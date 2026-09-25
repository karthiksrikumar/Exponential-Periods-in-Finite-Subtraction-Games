// Outcome period of subtraction game S (finite). o(n)=P iff all o(n-s)=N for s in S, s<=n.
// State R: bit i = o(n-1-i) (1 = P). next P iff (R & M)==0, M has bits s-1.
// For max-symmetric S the sequence is purely periodic: period = first t>0 with window(t)=window(0).
// General S: Brent cycle detection on state (m bits), gives preperiod & period.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int m; static u128 M, FULL;
static inline u128 step(u128 R){ u128 nb = ((R & M)==0) ? 1 : 0; return ((R<<1)|nb) & FULL; }
// initial state before position 0: positions <0 don't exist -> treat as "no move": moves to negative illegal.
// o(n) for n<min(S) is P. Equivalent: pretend o(k)=N for all k<0 (N positions never make parent P? no:)
// Parent P iff all options N; nonexistent options impose nothing -> treat as N. So R0 = 0 (all N).
int main(int argc,char**argv){
  int k=argc-1; int s[64]; m=0;
  if(k<1){fprintf(stderr,"usage: period s1 s2 ...\n");return 1;}
  for(int i=0;i<k;i++){s[i]=atoi(argv[i+1]); if(s[i]>m)m=s[i];}
  if(m>127){fprintf(stderr,"max S must be <=127\n");return 1;}
  FULL = (m==128)?~(u128)0:(((u128)1<<m)-1);
  M=0; for(int i=0;i<k;i++) M |= (u128)1<<(s[i]-1);
  // Brent's algorithm on sequence of states starting from R0=0
  u128 x0=0; u128 tort=x0, hare=step(x0); unsigned long long power=1, lam=1;
  while(tort!=hare){ if(power==lam){tort=hare; power<<=1; lam=0;} hare=step(hare); lam++; }
  // lam = period of states; find mu (preperiod)
  tort=x0; hare=x0; for(unsigned long long i=0;i<lam;i++) hare=step(hare);
  unsigned long long mu=0; while(tort!=hare){tort=step(tort);hare=step(hare);mu++;}
  printf("S={"); for(int i=0;i<k;i++) printf("%d%s",s[i],i<k-1?",":""); printf("} maxS=%d period=%llu preperiod=%llu\n",m,lam,mu);
  return 0;
}
