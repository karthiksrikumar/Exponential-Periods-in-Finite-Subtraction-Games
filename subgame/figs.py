import json, subprocess, numpy as np, matplotlib
matplotlib.use('Agg'); import matplotlib.pyplot as plt
from lay2 import taps_to_S
from lay import logical, WIRES
L=json.load(open('best26.json')); B=L['B']; res=L['res']; clocks=set(L['clocks'])
taps=[(tuple(q) if isinstance(q,list) else q, d) for q,d in L['taps']]
k=3; S=taps_to_S(B,taps,k); open('S_k.txt','w').write('\n'.join(map(str,S)))
per=k*2**k*B; N=2*per+B
subprocess.run(['./sim.exe','S_k.txt',str(N),'w.bin'],check=True)
w=np.fromfile('w.bin',dtype=np.uint8)
nb=N//B; img=w[:nb*B].reshape(nb,B)
# Figure 1: raw bitmap of first 2 periods (48 blocks), residues 0..B-1
fig,ax=plt.subplots(figsize=(11,4.2))
ax.imshow(img[:2*k*2**k],cmap='Greys',aspect='auto',interpolation='nearest')
for wname,r in res.items():
    ax.annotate(wname,(r,-0.8),ha='center',va='bottom',fontsize=7,rotation=60,color='tab:blue',annotation_clip=False)
ax.set_xlabel(r'residue $r$ within block (block length $B=%d$)'%B); ax.set_ylabel(r'block index $\tau$')
ax.set_title(r'P-positions (black) of the %d-move game $S_3$: position $n=\tau B+r$'%len(S),pad=28)
plt.tight_layout(); plt.savefig('../paper/figs/bitmap.pdf'); plt.savefig('../paper/figs/bitmap.png',dpi=160); plt.close()
# Figure 1b: logical view of wires
lg=logical(k,2*k*2**k)
M=np.array([lg[wn] for wn in WIRES])
fig,ax=plt.subplots(figsize=(11,2.6))
ax.imshow(M,cmap='Greys',aspect='auto',interpolation='nearest')
ax.set_yticks(range(8)); ax.set_yticklabels(WIRES); ax.set_xlabel(r'block index $\tau$')
for t in range(0,2*k*2**k+1,k): ax.axvline(t-0.5,color='tab:red',lw=0.6,alpha=0.6)
ax.set_title(r'Wire values per block ($k=3$): word $w$ occupies blocks $3w,3w+1,3w+2$; row u reads $w+1$ in binary (LSB first)')
plt.tight_layout(); plt.savefig('../paper/figs/wires.pdf'); plt.savefig('../paper/figs/wires.png',dpi=160); plt.close()
# Figure 2: growth
recs=[]
for line in open('p5.txt'):
    m,a,b,p=map(int,line.split()); recs.append((m,p))
best={}
for m,p in recs: best[m]=max(best.get(m,0),p)
ms=sorted(best)
fig,ax=plt.subplots(figsize=(6.5,4.2))
ax.semilogy(ms,[best[m] for m in ms],'o',ms=3,label=r'max-symmetric 5-move records (computed, $m\leq 66$)')
KK=np.arange(1,40); mx=[(K+1)*B+max(d for q,d in taps) for K in KK]
ax.semilogy([ (K+2)*B for K in KK],[B*(K+1)*2**(K+1) for K in KK],'-',label=r'our family $S_k$ (proved): $377\,k\,2^k$')
ax.set_xlabel(r'largest move $m=\max S$'); ax.set_ylabel('outcome period'); ax.legend(fontsize=8); ax.grid(alpha=0.3)
ax.set_title('Period growth')
plt.tight_layout(); plt.savefig('../paper/figs/growth.pdf'); plt.savefig('../paper/figs/growth.png',dpi=160); plt.close()
print('ok', len(S), per)
