/* 原 SO 只读转发；在真实 emu 初始化后的 payload 前 fork，子进程独立执行 NEMU。 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <signal.h>
static int observed;
static void *original(void) {
 static void *h;
 if(!h){h=dlopen(getenv("XIANGSHAN_DIFF_SO"),RTLD_NOW|RTLD_LOCAL);if(!h)abort();}
 return h;
}
static void native(uint64_t *before) {
 uint64_t target=strtoull(getenv("PAYLOAD_PC"),0,0);
 if(observed || before[82]!=target)return;
 observed=1;fflush(NULL);pid_t child=fork();if(child<0)abort();
 if(child==0){
  alarm(15);
  void (*copy)(void *,bool,bool)=dlsym(original(),"difftest_regcpy");
  void (*mem)(uint64_t,void *,size_t,bool)=dlsym(original(),"difftest_memcpy");
  void (*exec)(uint64_t)=dlsym(original(),"difftest_exec");
  uint64_t state[175];copy(state,false,false);
  FILE *f=fopen("native-nemu-trace.jsonl","wx");if(!f)_exit(5);
  uint64_t *csr=dlsym(original(),"csr_array");if(csr)fprintf(f,"{\"event\":\"csr\",\"mnstatus\":%lu}\n",csr[0x744]);
  fprintf(f,"{\"event\":\"start\",\"pc\":%lu,\"mode\":%lu,\"mstatus\":%lu,\"satp\":%lu,\"guided_exec\":false}\n",state[82],state[64],state[65],state[75]);fflush(f);
  uint64_t low=strtoull(getenv("EXIT_LOW"),0,0), high=strtoull(getenv("EXIT_HIGH"),0,0);
  for(int step=0;step<2000;step++){
   copy(state,false,false);
   fprintf(f,"{\"event\":\"step\",\"step\":%d,\"pc\":%lu,\"mcause\":%lu,\"mtval\":%lu,\"mepc\":%lu,\"x2\":%lu}\n",step,state[82],state[73],state[69],state[67],state[2]);fflush(f);
   if(state[82]>=low && state[82]<=high){uint32_t ins;mem(state[82],&ins,4,false);if(ins==0x0005006b){fclose(f);_exit(0);}}
   exec(1);
  }
  fclose(f);_exit(6);
 }
 int status;waitpid(child,&status,0);fprintf(stderr,"ECFG3_NATIVE child_status=%d\n",status);
}
void difftest_regcpy(void *r,bool direction,bool restore){
 void (*call)(void *,bool,bool)=dlsym(original(),"difftest_regcpy");if(!call)abort();
 call(r,direction,restore);
 if(!direction){uint64_t *s=r;native(s);fprintf(stderr,"ECFG3_REF pc=0x%lx mcause=%lu mtval=0x%lx mepc=0x%lx x2=0x%lx\n",s[82],s[73],s[69],s[67],s[2]);}
}
void difftest_guided_exec(void *g){
 uint64_t *s=g;fprintf(stderr,"ECFG3_GUIDE force=%u cause=%lu mtval=0x%lx\n",*(unsigned char*)g,s[1],s[2]);
 uint64_t state[175];void (*copy)(void *,bool,bool)=dlsym(original(),"difftest_regcpy");copy(state,false,false);native(state);
 void (*call)(void *)=dlsym(original(),"difftest_guided_exec");if(!call)abort();call(g);
}

/* 同步器可能一次执行多条指令；在每条实际执行前检查起点，避免跨过 payload。 */
void difftest_exec(uint64_t count) {
 void (*copy)(void *,bool,bool)=dlsym(original(),"difftest_regcpy");
 void (*exec)(uint64_t)=dlsym(original(),"difftest_exec");
 if(!copy || !exec)abort();
 for(uint64_t i=0;i<count;i++){
  uint64_t before[175];copy(before,false,false);native(before);exec(1);
 }
}
