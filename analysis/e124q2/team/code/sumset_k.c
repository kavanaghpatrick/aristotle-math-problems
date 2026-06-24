// Sumset of d^k * B_d over family, up to N. Tests k>=1 case.
#include <stdio.h>
#include <stdlib.h>
static int cmpl(const void*a,const void*b){long x=*(long*)a,y=*(long*)b;return (x>y)-(x<y);}
int main(int argc, char**argv){
    long N = atol(argv[1]);
    int K = atoi(argv[2]);
    int r = argc-3;
    int ds[8]; for(int i=0;i<r;i++) ds[i]=atoi(argv[3+i]);
    unsigned char *cur = calloc(N+1,1);
    cur[0]=1;
    for(int di=0;di<r;di++){
        int d=ds[di];
        // d^k * B_d: powers d^j for j>=K, value = sum of chosen d^j (j>=K), all <=N
        long pw[64]; int np=0; long p=1;
        for(int j=0;j<K;j++){ if(p> N/d){p=N+1;break;} p*=d; } // p = d^K
        while(p<=N){pw[np++]=p; if(p> N/d) break; p*=d;}
        long cap=2; for(int i=0;i<np;i++) cap*=2;
        long *Bd=malloc(sizeof(long)*cap); long nb=0; Bd[nb++]=0;
        for(int i=0;i<np;i++){ long cnt=nb; for(long j=0;j<cnt;j++){ long v=Bd[j]+pw[i]; if(v<=N) Bd[nb++]=v; } }
        qsort(Bd,nb,sizeof(long),cmpl);
        unsigned char *nxt=calloc(N+1,1);
        for(long n=0;n<=N;n++){ if(!cur[n]) continue; for(long j=0;j<nb;j++){ long v=n+Bd[j]; if(v>N) break; nxt[v]=1; } }
        free(cur); cur=nxt; free(Bd);
    }
    long misstot=0,last=-1,top=0; long lo=N*9/10;
    for(long n=0;n<=N;n++) if(!cur[n]){misstot++; last=n; if(n>=lo)top++;}
    printf("k=%d [",K);for(int i=0;i<r;i++)printf("%d%s",ds[i],i<r-1?",":"");
    printf("] N=%ld total_missing=%ld top10pct=%ld largest_missing=%ld\n",N,misstot,top,last);
    free(cur);
    return 0;
}
