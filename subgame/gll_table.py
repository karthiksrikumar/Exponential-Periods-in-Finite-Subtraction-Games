# Symbolic description of X-X by class (mod 13) as coarse sets (mod B'):
# tokens: 'Y-Y', 'Y-1', '-Y', '0', '-1'
XX={0:['Y-Y'],12:['Y-1','-Y'],8:['Y-1'],1:['Y-1','-Y'],5:['-Y'],4:['0'],11:['0'],7:['0'],9:['-1'],2:['-1'],6:['-1'],3:[],10:[]}
E=[1,5,12]
# For zero residue r=13z+rho with z>=1 and clock c: class, coarse shift
def cover_class(rho,c):
    if rho>=c: return (rho-c, 0)
    return (rho-c+13, -1)
print('Covering zero residues r = 13 z + rho, z >= 1 (all clocks lie below r):')
for rho in range(13):
    opts=[]
    for c in E:
        cl,sh=cover_class(rho,c)
        bad=XX[cl]
        # condition on z: coarse = z+sh must avoid the sets in 'bad'
        conds=[]
        for tok in bad:
            if tok=='Y-Y': conds.append('z%s in Y-Y'%('' if sh==0 else '-1'))
            if tok=='Y-1': conds.append('z%s in Y-1'%('' if sh==0 else '-1'))
            if tok=='-Y':  conds.append('z%s in -Y'%('' if sh==0 else '-1'))
            if tok=='0':   conds.append('z%s = 0'%('' if sh==0 else '-1'))
            if tok=='-1':  conds.append('z%s = -1'%('' if sh==0 else '-1'))
        opts.append((c,cl,sh,conds))
    print(' rho=%2d:'%rho, ' | '.join('c=%d->class %d%s bad iff %s'%(c,cl,'' if sh==0 else ' (coarse z-1)',' or '.join(cd) if cd else 'never') for c,cl,sh,cd in opts))
