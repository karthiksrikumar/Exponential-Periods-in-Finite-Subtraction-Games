// Scan families S = A ∪ {m-c : c in C}, A ⊆ [1..K], C ⊆ [0..K] with 0 in C, for m in [m0,m1].
// Output: A C m period preperiod (Brent). cap on steps.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int m; static u128 M, FULL;
static inline u128 step(u128 R){ u128 nb=((R&M)==0); return ((R<<1)|nb)&FULL; }
static int brent(unsigned long long cap, unsigned long long*lam_out, unsigned long long*mu_out){
  u128 x0=0, tort=x0, hare=step(x0); unsigned long long power=1, lam=1, steps=0;
  while(tort!=hare){ if(power==lam){tort=hare; power<<=1; lam=0;} hare=step(hare); lam++; if(++steps>cap) return 0;}
  tort=x0; hare=x0; for(unsigned long long i=0;i<lam;i++) hare=step(hare);
  unsigned long long mu=0; while(tort!=hare){tort=step(tort);hare=step(hare);mu++;}
  *lam_out=lam; *mu_out=mu; return 1;
}
int main(int argc,char**argv){
  int K=atoi(argv[1]), m0=atoi(argv[2]), m1=atoi(argv[3]), maxA=atoi(argv[4]), maxC=atoi(argv[5]);
  unsigned long long cap=strtoull(argv[6],0,10);
  for(int Am=0; Am<(1<<K); Am++){ if(__builtin_popcount(Am)>maxA) continue;
   for(int Cm=1; Cm<(1<<(K+1)); Cm+=2){ if(__builtin_popcount(Cm)>maxC) continue; // bit0 = c=0 always
    printf("A=%d C=%d :",Am,Cm);
    for(m=m0;m<=m1;m++){
      if(m-K<=K+1){printf(" -");continue;}
      FULL=(((u128)1)<<m)-1; M=0;
      for(int i=0;i<K;i++) if(Am>>i&1) M|=(u128)1<<(i);        // move i+1 -> bit i
      for(int c=0;c<=K;c++) if(Cm>>c&1) M|=(u128)1<<(m-c-1);   // move m-c -> bit m-c-1
      unsigned long long lam,mu; if(!brent(cap,&lam,&mu)){printf(" X");continue;}
      printf(" %llu",lam);
    }
    printf("\n"); fflush(stdout);
  }}
}
