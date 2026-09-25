bs=chr(92)
t=open('paper.tex',encoding='utf8').read()
anchor=bs+'begin{corollary}[Periods are hard to compute]'
thm=(bs+'begin{theorem}[Binary move sets]'+bs+'label{thm:exptime}\n'
'If the move set $S$ is given in binary (and $n$ in binary), deciding whether $n$ is a P-position of\n'
'$S$ is EXPTIME-complete.\n'
+bs+'end{theorem}\n\n'
+bs+'begin{proof}\n'
+bs+'emph{Membership.}  The simulation above uses space $O(\max S+\log n)$ and time $O(n|S|)$, both at\n'
'most exponential in the input length.\n\n'
+bs+'emph{Hardness.}  Repeat the reduction of Theorem~'+bs+'ref{thm:pspace} for a fixed machine $M$ deciding an\n'
'EXPTIME-complete language in time $T(N)=2^{N^c}$, on a tape of length $L=T(N)+2$ (so $M$ never\n'
'reaches the right marker).  The circuit and hence $B$ are unchanged.  The three long moves now have\n'
'size about $LB$, but in binary they need only $O(N^c)$ bits; the initial configuration is blank\n'
'except for the $N$ input cells and the two markers, so only $O(N)$ initialisation moves are needed.\n'
'The query position $n^*=(t^*L+1)B+13y_{'+bs+'mathrm{flag}}$ with $t^*=T(N)+L$ has $O(N^c)$ bits.  Hence\n'
'$(S_x,n^*)$ has polynomial size.\n'
+bs+'end{proof}\n\n'
'Thus the complexity of one-heap subtraction games is governed by the size of the largest move: they\n'
'are easy for every fixed game, PSPACE-complete when the moves are written in unary, and\n'
'EXPTIME-complete when they are written in binary.\n\n')
t=t.replace(anchor,thm+anchor,1)
old=(bs+'item '+bs+'textbf{Binary move sets.}  Is '+bs+'textsc{SubGame} still in PSPACE when $S$ is given in binary\n'
'(so that $'+bs+'max S$ may be exponential in the input length)?  Is it PSPACE-hard with a bounded number\n'
'of moves?')
new=(bs+'item '+bs+'textbf{Bounded number of moves.}  Our hardness reductions use $O(N)$ moves.  Is\n'
+bs+'textsc{SubGame} still PSPACE-hard (or EXPTIME-hard, in binary) when the number of moves is bounded?')
assert old in t, 'open problem text not found'
t=t.replace(old,new)
old2=('PSPACE-complete, whereas for every '+bs+'emph{fixed} one-heap game the question is easy.')
new2=('PSPACE-complete, and EXPTIME-complete when the moves are written in binary, whereas for every\n'
+bs+'emph{fixed} one-heap game the question is easy.')
assert old2 in t
t=t.replace(old2,new2)
open('paper.tex','w',encoding='utf8').write(t); print('ok')
