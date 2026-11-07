/* 只读观测：按日志路径签名，复制一级目录首次根查询的原始断言。 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <execinfo.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <z3.h>
static __thread char line[65536];
static __thread size_t used;
static __thread unsigned long long signature, saved;
ssize_t write(int fd, const void *data, size_t size) {
    ssize_t (*original)(int,const void*,size_t)=dlsym(RTLD_NEXT,"write");
    if(fd==2) {
        const char *p=data;
        for(size_t i=0;i<size;i++) {
            if(used+1>=sizeof(line)) used=0;
            line[used++]=p[i];
            if(p[i]=='\n') {
                line[used]=0;
                if(strstr(line,"[MERGE_PREDICT_START]")) {
                    char *key=strstr(line,"\"path_signature\":");
                    if(!key) abort();
                    signature=strtoull(key+17,NULL,10);
                }
                used=0;
            }
        }
    }
    return original(fd,data,size);
}
static void observe(Z3_context ctx,Z3_solver solver,unsigned n,Z3_ast const a[]) {
    if(!signature || saved==signature) return;
    void *frames[40]; int count=backtrace(frames,40),found=0;
    uintptr_t begin=strtoull(getenv("EXACT_ENUM_BEGIN"),NULL,0);
    uintptr_t end=strtoull(getenv("EXACT_ENUM_END"),NULL,0);
    for(int i=0;i<count;i++) {
        Dl_info info;
        if(dladdr(frames[i],&info)) {
            uintptr_t offset=(uintptr_t)frames[i]-(uintptr_t)info.dli_fbase;
            if(offset>=begin && offset<end) found=1;
        }
    }
    if(!found) return;
    /* 根查询必须没有守卫前缀；不误采后面的部分赋值。 */
    for(unsigned i=0;i<n;i++) if(Z3_get_bool_value(ctx,a[i])!=Z3_L_TRUE) abort();
    char path[4096];snprintf(path,sizeof(path),"%s/path-%llu.smt2",getenv("EXACT_DUMP"),signature);
    FILE *file=fopen(path,"wx");if(!file) abort();
    Z3_ast_vector v=Z3_solver_get_assertions(ctx,solver);Z3_ast_vector_inc_ref(ctx,v);
    Z3_solver copy=Z3_mk_solver(ctx);Z3_solver_inc_ref(ctx,copy);
    for(unsigned i=0;i<Z3_ast_vector_size(ctx,v);i++) Z3_solver_assert(ctx,copy,Z3_ast_vector_get(ctx,v,i));
    fprintf(file,"; 原路径首次根查询；额外假设全部为 true；signature=%llu\n",signature);
    fputs(Z3_solver_to_string(ctx,copy),file);fclose(file);
    Z3_solver_dec_ref(ctx,copy);Z3_ast_vector_dec_ref(ctx,v);saved=signature;
}
Z3_lbool Z3_solver_check(Z3_context c,Z3_solver s) {
    Z3_lbool (*f)(Z3_context,Z3_solver)=dlsym(RTLD_NEXT,"Z3_solver_check");
    Z3_lbool r=f(c,s);observe(c,s,0,NULL);return r;
}
Z3_lbool Z3_solver_check_assumptions(Z3_context c,Z3_solver s,unsigned n,Z3_ast const a[]) {
    Z3_lbool (*f)(Z3_context,Z3_solver,unsigned,Z3_ast const*)=dlsym(RTLD_NEXT,"Z3_solver_check_assumptions");
    Z3_lbool r=f(c,s,n,a);observe(c,s,n,a);return r;
}
