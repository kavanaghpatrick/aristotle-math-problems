#include <stdio.h>
#include <stdlib.h>
static int cmpl(const void*a,const void*b){long x=*(long*)a,y=*(long*)b;return (x>y)-(x<y);}
int main(int argc, char**argv){
    long N = atol(argv[1]);
    int r = argc-2;
    int ds[8]; for(int i=0;i<r;i++) ds[i]=atoi(argv[2+i]);
    unsigned char *cur = calloc(N+1,1);
    cur[0]=1;
    for(int di=0;di<r;di++){
        int d=ds[di];
        long pw[64]; int np=0; long p=1;
        while(p<=N){pw[np++]=p; if(p> N/d) break; p*=d;}
        long cap=2; for(int i=0;i<np;i++) cap*=2;
        long *Bd=malloc(sizeof(long)*cap); long nb=0; Bd[nb++]=0;
        for(int i=0;i<np;i++){ long cnt=nb; for(long j=0;j<cnt;j++){ long v=Bd[j]+pw[i]; if(v<=N) Bd[nb++]=v; } }
        qsort(Bd,nb,sizeof(long),cmpl);
        unsigned char *nxt=calloc(N+1,1);
        for(long n=0;n<=N;n++){ if(!cur[n]) continue; for(long j=0;j<nb;j++){ long v=n+Bd[j]; if(v>N) break; nxt[v]=1; } }
        free(cur); cur=nxt; free(Bd);
    }
    // print all missing > N/2, and analyze their structure mod powers of d_min
    printf("Missing integers > %ld:\n", N/2);
    int cnt=0;
    for(long n=N/2;n<=N;n++) if(!cur[n]){ printf("%ld ",n); if(++cnt>=60){printf("...");break;} }
    printf("\n");
    free(cur);
    return 0;
}
