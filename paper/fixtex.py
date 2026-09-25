bs=chr(92)
t=open('paper.tex',encoding='utf8').read()
for name in [bs+'mathrm{marker}[-k])', bs+'mathrm{carry}[-1],'+bs+'mathrm{marker})', 'carry}[-1],'+bs+'mathrm{marker})']:
    pass
lines=t.split('\n')
out=[]
inalign=False
for ln in lines:
    if ln.startswith(bs+'mathrm{boot}&='+bs+'NOR') or ln.startswith(bs+'mathrm{marker}&=') or ln.startswith(bs+'mathrm{nb}&='):
        if ln.endswith(bs) and not ln.endswith(bs+bs):
            ln=ln+bs
    out.append(ln)
t='\n'.join(out)
old='S_3='+bs+'{2,5,7,8,9,10,12,13,15,16,20,21,22,28,29,35,41,42,47,50,53,55,58,66,69,70,71,79,80,81,'+bs+bs+'\n83,85,86,90,98,111,118,123,156,177,180,203,221,248,266,309,329,332,335,370,375,976,1013,1118'+bs+'}.'
new='S_3='+bs+'{2,5,7,8,9,10,12,13,15,16,20,21,22,28,29,35,41,42,47,50,53,55,58,'+bs+bs+'\n66,69,70,71,79,80,81,83,85,86,90,98,111,118,123,156,177,180,203,'+bs+bs+'\n221,248,266,309,329,332,335,370,375,976,1013,1118'+bs+'}.'
assert old in t, 'S3 not found'
t=t.replace(old,new)
oldfv=bs+'paragraph{Formal verification.}  Theorem~'
i=t.index(oldfv); j=t.index(bs+'subsection{Idea of the construction}')
newfv=(bs+'paragraph{Formal verification.}  Theorem~'+bs+'ref{thm:main}, Corollary~'+bs+'ref{cor:guy}, the nim-sequence statement\n'
 'and the General Layout Lemma are proved in Lean~4 with Mathlib (Section~'+bs+'ref{sec:lean}), with main statements\n'
 +bs+'begin{itemize}\n'+bs+'item '+bs+'texttt{SubGame.Concrete.exponential'+bs+'_period} (Theorem~'+bs+'ref{thm:main}),\n'
 +bs+'item '+bs+'texttt{SubGame.Concrete.guy'+bs+'_fails} and '+bs+'texttt{not'+bs+'_polynomially'+bs+'_bounded} (Corollary~'+bs+'ref{cor:guy}),\n'
 +bs+'item '+bs+'texttt{SubGame.Concrete.nim'+bs+'_period'+bs+'_dvd} (nim-sequences),\n'
 +bs+'item '+bs+'texttt{SubGame.GLL.simulate} (General Layout Lemma);\n'
 +bs+'end{itemize}\n'
 +bs+'texttt{'+bs+'#print axioms} reports only '+bs+'texttt{propext}, '+bs+'texttt{Classical.choice} and '+bs+'texttt{Quot.sound}.\n'
 'The PSPACE-completeness theorem is proved on paper; its game-theoretic core is part of the formal\n'
 'development, while the standard encoding of a linear-bounded automaton as a cellular automaton is not\nformalised.\n\n')
t=t[:i]+newfv+t[j:]
open('paper.tex','w',encoding='utf8').write(t)
print('ok')
