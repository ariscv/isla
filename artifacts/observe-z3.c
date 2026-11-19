/* 仅观察动态库调用。候选归属由受测二进制的调用栈判定。 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <execinfo.h>
#include <fcntl.h>
#include <inttypes.h>
#include <link.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <z3.h>

struct range {
    uintptr_t start;
    uintptr_t end;
    unsigned kind;
};
static const struct range scopes[] = {
#include "scope-ranges.h"
};

static uintptr_t main_base;
static Z3_context (*make_context)(Z3_config);
static Z3_context (*make_context_rc)(Z3_config);
static void (*delete_context)(Z3_context);
static Z3_lbool (*check)(Z3_context, Z3_solver);
static Z3_lbool (*check_assumptions)(Z3_context, Z3_solver, unsigned, Z3_ast const *);
static uint64_t (*allocated_bytes)(void);
static atomic_uint_fast64_t live_contexts;
static atomic_int initialized;
static _Thread_local unsigned context_depth;
static _Thread_local unsigned check_depth;
static pthread_mutex_t totals_lock = PTHREAD_MUTEX_INITIALIZER;
static uint64_t check_counts[4], check_ns[4];
static uint64_t unfinished_checks, short_backtraces;
static pthread_t sampler;
static int log_fd = -1;

static uint64_t monotonic_ns(void) {
    struct timespec time;
    clock_gettime(CLOCK_MONOTONIC, &time);
    return (uint64_t)time.tv_sec * UINT64_C(1000000000) + time.tv_nsec;
}

static int find_main(struct dl_phdr_info *info, size_t size, void *unused) {
    (void)size;
    (void)unused;
    main_base = info->dlpi_addr;
    return 1;
}

static void sample(void) {
    uint64_t counts[4], ns[4], pending, short_stacks;
    pthread_mutex_lock(&totals_lock);
    for (unsigned i = 0; i < 4; ++i) {
        counts[i] = check_counts[i];
        ns[i] = check_ns[i];
    }
    pending = unfinished_checks;
    short_stacks = short_backtraces;
    pthread_mutex_unlock(&totals_lock);
    uint64_t contexts = atomic_load_explicit(&live_contexts, memory_order_relaxed);
    uint64_t bytes = atomic_load_explicit(&initialized, memory_order_acquire) ? allocated_bytes() : 0;
    char line[512];
    int length = snprintf(line, sizeof(line),
        "%" PRIu64 "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64
        "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64
        "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64 "\n",
        monotonic_ns(), contexts, bytes, pending, short_stacks,
        counts[0], ns[0], counts[1], ns[1], counts[2], ns[2], counts[3], ns[3]);
    if (length < 0 || (size_t)length >= sizeof(line) || write(log_fd, line, length) != length) {
        perror("observer write");
    }
}

static void *sample_loop(void *unused) {
    (void)unused;
    const struct timespec interval = { 5, 0 };
    for (;;) {
        sample();
        nanosleep(&interval, NULL);
    }
    return NULL;
}

__attribute__((constructor)) static void initialize(void) {
    make_context = dlsym(RTLD_NEXT, "Z3_mk_context");
    make_context_rc = dlsym(RTLD_NEXT, "Z3_mk_context_rc");
    delete_context = dlsym(RTLD_NEXT, "Z3_del_context");
    check = dlsym(RTLD_NEXT, "Z3_solver_check");
    check_assumptions = dlsym(RTLD_NEXT, "Z3_solver_check_assumptions");
    allocated_bytes = dlsym(RTLD_NEXT, "Z3_get_estimated_alloc_size");
    if (!make_context || !make_context_rc || !delete_context || !check || !check_assumptions || !allocated_bytes) {
        fputs("observer: Z3 library symbols are missing\n", stderr);
        _exit(125);
    }
    const char *path = getenv("ISARCH_OBSERVER_PATH");
    if (!path) return;
    log_fd = open(path, O_WRONLY | O_CREAT | O_EXCL | O_APPEND | O_CLOEXEC, 0600);
    dl_iterate_phdr(find_main, NULL);
    if (log_fd < 0 || pthread_create(&sampler, NULL, sample_loop, NULL) != 0) {
        fputs("observer: cannot start sampler\n", stderr);
        _exit(125);
    }
}

__attribute__((destructor)) static void finish(void) {
    if (log_fd < 0) return;
    pthread_cancel(sampler);
    pthread_join(sampler, NULL);
    sample();
    close(log_fd);
}

Z3_context Z3_mk_context(Z3_config config) {
    ++context_depth;
    Z3_context context = make_context(config);
    if (--context_depth == 0 && context) {
        atomic_fetch_add_explicit(&live_contexts, 1, memory_order_relaxed);
        atomic_store_explicit(&initialized, 1, memory_order_release);
    }
    return context;
}

Z3_context Z3_mk_context_rc(Z3_config config) {
    ++context_depth;
    Z3_context context = make_context_rc(config);
    if (--context_depth == 0 && context) {
        atomic_fetch_add_explicit(&live_contexts, 1, memory_order_relaxed);
        atomic_store_explicit(&initialized, 1, memory_order_release);
    }
    return context;
}

void Z3_del_context(Z3_context context) {
    delete_context(context);
    atomic_fetch_sub_explicit(&live_contexts, 1, memory_order_relaxed);
}

static unsigned check_scope(void) {
    void *frames[80];
    int length = backtrace(frames, (int)(sizeof(frames) / sizeof(frames[0])));
    unsigned scope = 0;
    for (int i = 1; i < length; ++i) {
        uintptr_t offset = (uintptr_t)frames[i] - main_base - 1;
        for (size_t j = 0; j < sizeof(scopes) / sizeof(scopes[0]); ++j) {
            if (offset >= scopes[j].start && offset < scopes[j].end) {
                scope |= scopes[j].kind;
            }
        }
    }
    pthread_mutex_lock(&totals_lock);
    ++unfinished_checks;
    if (length < 5 || length == (int)(sizeof(frames) / sizeof(frames[0]))) {
        ++short_backtraces;
    }
    pthread_mutex_unlock(&totals_lock);
    return scope;
}

static void check_finished(unsigned scope, uint64_t duration) {
    pthread_mutex_lock(&totals_lock);
    --unfinished_checks;
    ++check_counts[scope];
    check_ns[scope] += duration;
    pthread_mutex_unlock(&totals_lock);
}

Z3_lbool Z3_solver_check(Z3_context context, Z3_solver solver) {
    if (log_fd < 0 || check_depth) return check(context, solver);
    ++check_depth;
    unsigned scope = check_scope();
    uint64_t start = monotonic_ns();
    Z3_lbool result = check(context, solver);
    check_finished(scope, monotonic_ns() - start);
    --check_depth;
    return result;
}

Z3_lbool Z3_solver_check_assumptions(Z3_context context, Z3_solver solver, unsigned n, Z3_ast const *assumptions) {
    if (log_fd < 0 || check_depth) return check_assumptions(context, solver, n, assumptions);
    ++check_depth;
    unsigned scope = check_scope();
    uint64_t start = monotonic_ns();
    Z3_lbool result = check_assumptions(context, solver, n, assumptions);
    check_finished(scope, monotonic_ns() - start);
    --check_depth;
    return result;
}
