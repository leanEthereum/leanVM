import os, sys
# usage: python3 -I genpull.py  writes Tables/Vt/PullSels.lean (the pull side's selectors are the push side's).
# First run: python3 -I dump.py ../../LeanVM/Guest/Data/Core00.lean vt_ir.txt (from this directory).
import sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genforms import *
from mk import write
Dall=defs_window(0,WHI)
out=[]
for t in range(6):
    chP,_=chain(FV[str(t)][0],D); chQ,_=chain(D[FV[str(t)][1]][2][1],D)
    sp=[c[0] for c in chP]; sq=[c[0] for c in chQ]
    L=[f'theorem vtPullSels{t} {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) :']
    L.append('    ['+', '.join(f'σ (.n {v})' for v in sq)+'] =')
    L.append('      ['+', '.join(f'σ (.n {v})' for v in sp)+'] := by')
    names=[]
    for a,b in zip(sq,sp):
        p,op,args=Dall[a]; assert op=='copy' and args[0]==b,(t,a,b,op,args)
        L.append(f'  have a{p} := h.atomAt {p} {RAW[p][len(".atom "):]} (by decide +kernel)')
        names.append(f'a{p}')
    L.append('  simp only [Atom.Holds] at '+' '.join(names))
    L.append('  rw ['+', '.join(names)+']')
    out.append('\n'.join(wrapl(x,'      ',98) if False else x for x in L))
write('PullSels',"The pull side's table block selectors are the push side's, copied.",'LeanVM.Guest.B1.Tables.Vt.Base','\n\n'.join(out))
