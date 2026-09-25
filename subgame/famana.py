import math,sys
rows=[]
for line in open(sys.argv[1]):
    head,vals=line.split(':'); A,C=[int(x.split('=')[1]) for x in head.split()]
    v=vals.split(); ms=list(range(int(sys.argv[2]),int(sys.argv[2])+len(v)))
    pts=[(m,math.log2(int(x))) for m,x in zip(ms,v) if x not in('-','X') and int(x)>0]
    capped=sum(1 for x in v if x=='X')
    if len(pts)<8: continue
    # fit on last half
    pts2=pts[len(pts)//2:]
    n=len(pts2); mt=sum(a for a,_ in pts2)/n; ml=sum(b for _,b in pts2)/n
    sxx=sum((a-mt)**2 for a,_ in pts2); sl=sum((a-mt)*(b-ml) for a,b in pts2)/sxx
    res=max(abs(b-ml-sl*(a-mt)) for a,b in pts2)
    dec=lambda mask,off:[i+off for i in range(12) if mask>>i&1]
    rows.append((sl,res,capped,dec(A,1),dec(C,0),v[-6:]))
rows.sort(key=lambda r:-r[0])
for r in rows[:30]: print('slope=%.3f maxres=%.2f capped=%d A=%s C=%s last=%s'%r)
