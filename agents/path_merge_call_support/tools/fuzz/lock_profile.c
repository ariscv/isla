/* 诊断专用：每 1024 次调用取样一次，保留锁地址及调用点，不改变锁协议。 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <signal.h>
#include <sys/time.h>
#include <ucontext.h>
#include <errno.h>
#include <sys/syscall.h>

#define THREADS 4096
#define SLOTS 128
struct row { void *caller; void *lock; uint64_t calls, samples, wall, cpu; };
struct thread { struct row locks[SLOTS]; struct row alloc[4]; unsigned contexts; };
static struct thread rows[THREADS];
static _Atomic unsigned next_thread;
#define MAX_SAMPLES 2000000
struct sample { uintptr_t pc; unsigned thread; };
static struct sample pcs[MAX_SAMPLES];
static _Atomic unsigned next_sample;

static __thread struct thread *current;
static __thread int entered;
static void sample_pc(int signal, siginfo_t *info, void *context) {
    (void)signal; (void)info;
    int saved_errno = errno;
    unsigned index = atomic_fetch_add(&next_sample, 1);
    if (index < MAX_SAMPLES) {
        pcs[index].pc = ((ucontext_t *)context)->uc_mcontext.gregs[REG_RIP];
        pcs[index].thread = current ? (unsigned)(current - rows) : THREADS;
    }
    errno = saved_errno;
}
static int (*real_lock)(pthread_mutex_t *);
static void *(*real_context)(void *);
extern void *__libc_malloc(size_t);
extern void *__libc_realloc(void *, size_t);
extern void __libc_free(void *);

static uint64_t now(clockid_t clock) {
    struct timespec t;
    if (clock_gettime(clock, &t)) abort();
    return (uint64_t)t.tv_sec * 1000000000 + t.tv_nsec;
}
static struct thread *thread_rows(void) {
    if (!current) {
        unsigned id = atomic_fetch_add(&next_thread, 1);
        if (id >= THREADS) abort();
        current = &rows[id];
    }
    return current;
}
__attribute__((constructor)) static void setup(void) {
    real_lock = dlsym(RTLD_NEXT, "pthread_mutex_lock");
    if (!real_lock) abort();
    real_context = dlsym(RTLD_NEXT, "Z3_mk_context_rc");
    struct sigaction action = {0};
    action.sa_sigaction = sample_pc;
    action.sa_flags = SA_SIGINFO | SA_RESTART;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGPROF, &action, NULL)) abort();
    struct itimerval interval = { .it_interval = {0, 1000}, .it_value = {0, 1000} };
    if (setitimer(ITIMER_PROF, &interval, NULL)) abort();
}
void *Z3_mk_context_rc(void *config) {
    if (!real_context) real_context = dlsym(RTLD_NEXT, "Z3_mk_context_rc");
    if (!real_context) abort();
    thread_rows()->contexts++;
    return real_context(config);
}
int pthread_mutex_lock(pthread_mutex_t *lock) {
    if (!real_lock) {
        real_lock = dlsym(RTLD_NEXT, "pthread_mutex_lock");
        if (!real_lock) abort();
    }
    if (entered) return real_lock(lock);
    entered = 1;
    struct thread *t = thread_rows();
    void *caller = __builtin_return_address(0);
    unsigned slot = ((uintptr_t)caller >> 4) % SLOTS;
    unsigned probes = 0;
    while (t->locks[slot].caller && t->locks[slot].caller != caller) {
        if (++probes == SLOTS) abort();
        slot = (slot + 1) % SLOTS;
    }
    struct row *r = &t->locks[slot];
    r->caller = caller; r->lock = lock;
    int sampled = (++r->calls % 1024 == 1);
    uint64_t wall = 0, cpu = 0;
    if (sampled) { wall = now(CLOCK_MONOTONIC); cpu = now(CLOCK_THREAD_CPUTIME_ID); }
    int result = real_lock(lock);
    if (sampled) { r->cpu += now(CLOCK_THREAD_CPUTIME_ID) - cpu; r->wall += now(CLOCK_MONOTONIC) - wall; r->samples++; }
    entered = 0;
    return result;
}
/* 分配器的内部锁不经过 pthread 接口，单独取样其调用成本。 */
void *malloc(size_t size) {
    if (entered) return __libc_malloc(size);
    entered = 1;
    struct row *r = &thread_rows()->alloc[0];
    int sampled = (++r->calls % 1024 == 1);
    uint64_t wall = 0, cpu = 0;
    if (sampled) { wall = now(CLOCK_MONOTONIC); cpu = now(CLOCK_THREAD_CPUTIME_ID); }
    void *result = __libc_malloc(size);
    if (sampled) { r->cpu += now(CLOCK_THREAD_CPUTIME_ID) - cpu; r->wall += now(CLOCK_MONOTONIC) - wall; r->samples++; }
    entered = 0;
    return result;
}
void free(void *ptr) {
    if (entered) { __libc_free(ptr); return; }
    entered = 1;
    struct row *r = &thread_rows()->alloc[1];
    int sampled = (++r->calls % 1024 == 1);
    uint64_t wall = 0, cpu = 0;
    if (sampled) { wall = now(CLOCK_MONOTONIC); cpu = now(CLOCK_THREAD_CPUTIME_ID); }
    __libc_free(ptr);
    if (sampled) { r->cpu += now(CLOCK_THREAD_CPUTIME_ID) - cpu; r->wall += now(CLOCK_MONOTONIC) - wall; r->samples++; }
    entered = 0;
}
void *realloc(void *ptr, size_t size) {
    if (entered) return __libc_realloc(ptr, size);
    entered = 1;
    struct row *r = &thread_rows()->alloc[2];
    int sampled = (++r->calls % 1024 == 1);
    uint64_t wall = 0, cpu = 0;
    if (sampled) { wall = now(CLOCK_MONOTONIC); cpu = now(CLOCK_THREAD_CPUTIME_ID); }
    void *result = __libc_realloc(ptr, size);
    if (sampled) { r->cpu += now(CLOCK_THREAD_CPUTIME_ID) - cpu; r->wall += now(CLOCK_MONOTONIC) - wall; r->samples++; }
    entered = 0;
    return result;
}
ssize_t write(int fd, const void *data, size_t size) {
    if (entered) return syscall(SYS_write, fd, data, size);
    entered = 1;
    struct row *r = &thread_rows()->alloc[3];
    int sampled = (++r->calls % 1024 == 1);
    uint64_t wall = 0, cpu = 0;
    if (sampled) { wall = now(CLOCK_MONOTONIC); cpu = now(CLOCK_THREAD_CPUTIME_ID); }
    ssize_t result = syscall(SYS_write, fd, data, size);
    if (sampled) { r->cpu += now(CLOCK_THREAD_CPUTIME_ID) - cpu; r->wall += now(CLOCK_MONOTONIC) - wall; r->samples++; }
    entered = 0;
    return result;
}
__attribute__((destructor)) static void finish(void) {
    entered = 1;
    struct itimerval interval = {0};
    setitimer(ITIMER_PROF, &interval, NULL);
    const char *path = getenv("ISLA_LOCK_LOG");
    if (!path) return;
    FILE *out = fopen(path, "a");
    if (!out) abort();
    const char *names[] = {"malloc", "free", "realloc", "write"};
    for (unsigned t = 0; t < next_thread; t++) {
        fprintf(out, "{\"thread\":%u,\"contexts\":%u}\n", t, rows[t].contexts);
        for (unsigned i = 0; i < SLOTS + 4; i++) {
            struct row *r = i < SLOTS ? &rows[t].locks[i] : &rows[t].alloc[i-SLOTS];
            if (!r->calls) continue;
            Dl_info info = {0};
            dladdr(r->caller, &info);
            fprintf(out, "{\"thread\":%u,\"kind\":\"%s\",\"caller\":\"%s+0x%lx\",\"lock\":\"%p\",\"calls\":%lu,\"samples\":%lu,\"wall_ns\":%lu,\"cpu_ns\":%lu}\n",
                    t, i < SLOTS ? "mutex" : names[i-SLOTS], info.dli_fname ? info.dli_fname : "", (uintptr_t)r->caller-(uintptr_t)info.dli_fbase,
                    r->lock, r->calls, r->samples, r->wall, r->cpu);
        }
    }
    for (unsigned index = 0; index < next_sample && index < MAX_SAMPLES; index++) {
        Dl_info info = {0};
        dladdr((void *)pcs[index].pc, &info);
        fprintf(out, "{\"sample_thread\":%u,\"object\":\"%s\",\"offset\":\"0x%lx\"}\n",
                pcs[index].thread, info.dli_fname ? info.dli_fname : "", pcs[index].pc-(uintptr_t)info.dli_fbase);
    }
    fclose(out);
}
