import os, sys
# usage: python3 -I genair.py  writes Tables/Vt/Air.lean (each table's weight and form value; the final claim).
# First run: python3 -I dump.py ../../LeanVM/Guest/Data/Core00.lean vt_ir.txt (from this directory).
import sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genforms import *
from mk import write
# `verify_tables`' `air_acc += zc_cprod[g_zc_n / tau_g] * zc_peq[tau_g] * constraint_eval`, tau_g = kb[2 + t]
# (the kappa_base frame variable 27 + t): `g_zc_n = x·τ`.
GZN, CPROD, PEQ, CLAIM = 2544, 2630, 2651, 2648
out=[]
def at(p): return f'  have a{p} := h.atomAt {p} {RAW[p][len(".atom "):]} (by decide +kernel)'
airs=[]
for t in range(6):
    tau=27+t
    px=[q for q in range(WLO,WHI+1) if RAW[q]==f'.atom (.mul (.n {GZN}) (.n {RAW[q].split()[5].rstrip(")") if RAW[q].startswith(f".atom (.mul (.n {GZN})") else -1}) (.n {tau}))']
    assert len(px)==1,(t,px)
    pxx=px[0]; x=parse_atom(RAW[pxx])[1][1]
    pcpb=pxx+1; _,(cpb,c0,x1)=parse_atom(RAW[pcpb]); assert c0==CPROD and x1==x
    pcp=pxx+2; _,(cp,cpb1,o)=parse_atom(RAW[pcp]); assert cpb1==cpb and o==0
    ppeb=pxx+3; _,(peb,p0,t1)=parse_atom(RAW[ppeb]); assert p0==PEQ and t1==tau
    ppe=pxx+4; _,(pe,peb1,o)=parse_atom(RAW[ppe]); assert peb1==peb and o==0
    pw=pxx+5; _,(w,cp1,pe1)=parse_atom(RAW[pw]); assert (cp1,pe1)==(cp,pe)
    pa=pxx+6; _,(air,w1,CE)=parse_atom(RAW[pa]); assert w1==w
    airs.append((air,pa))
    stop=set(FV[str(t)][sd] for sd in range(3))|set(evvar)
    ceat=set(); deps_stop(CE,D,ceat,stop)
    def ex(v):
        if v in evvar: return f'ev {evvar[v]-BASE[t]}'
        if v in stop or v not in D or D[v][0] not in ceat: return f'σ (.n {v})'
        p,op,a=D[v]
        if op=='const': return f'word {a[0]} {a[1]}'
        if op=='copy': return ex(a[0])
        return f'({ex(a[0])} {"+" if op=="add" else "*"} {ex(a[1])})'
    ce=ex(CE)
    evs=sorted(set(v for q in ceat for v in (parse_atom(RAW[q])[1][1:] if parse_atom(RAW[q])[0] in ('add','mul') else []) if v in evvar))
    L=[]
    L.append(f'/-- Table {t}\'s air term: its weight `cprod[x]·peq[τ]` with `g^n = x·τ` (`τ = kb[{2+t}]`), times\nits form value. -/')
    L.append(f'theorem vtAir{t} {{rd : Reader}} {{σ : Val}} (h : VtH rd σ){" {ev : ℕ → E}" if evs else ""}')
    if evs: L.append(f'    (hev : ∀ c < {WIDTH[t]}, σ (.n (vtEvB ({BASE[t]} + c))) = ev c)')
    L.append(f'    : σ (.n {GZN}) = σ (.n {x}) * σ (.n {tau}) ∧')
    L.append(f'      LoadHolds rd (σ (.n {CPROD}) * σ (.n {x})) 0 (σ (.n {cp})) ∧')
    L.append(f'      LoadHolds rd (σ (.n {PEQ}) * σ (.n {tau})) 0 (σ (.n {pe})) ∧')
    L.append(f'      σ (.n {air}) = σ (.n {cp}) * σ (.n {pe}) *')
    L.append(f'        {ce} := by')
    poss=[pxx,pcpb,pcp,ppeb,ppe,pw,pa]+sorted(ceat)
    for q in poss: L.append(at(q))
    L.append('  simp only [Atom.Holds] at '+' '.join(f'a{q}' for q in poss))
    for v in evs:
        k=evvar[v]; c=k-BASE[t]
        L.append(f'  have v{v} : σ (.n {v}) = ev {c} := by')
        L.append(f'    rw [← hev {c} (by norm_num)]; exact (vt_eval h (k := {k}) (by norm_num)).2.2')
    L.append(f'  refine ⟨a{pxx}, by rw [← a{pcpb}]; exact a{pcp}, by rw [← a{ppeb}]; exact a{ppe}, ?_⟩')
    ceq=[f'a{q}' for q in sorted(ceat,reverse=True)]+[f'v{v}' for v in evs]
    L.append(f'  rw [a{pa}, a{pw}, '+wrapl(', '.join(ceq),'    ',90)+']')
    out.append('\n'.join(L))
# total: air_0, then `acc + air_t`, asserted equal to the sumcheck's final claim
pe_=[q for q in range(WLO,WHI+1) if RAW[q].startswith('.atom (.assertEq ') and f'(.n {CLAIM}))' in RAW[q]]
assert len(pe_)==1
tot=parse_atom(RAW[pe_[0]])
import re
tot=int(re.findall(r'\(\.n (\d+)\)',RAW[pe_[0]])[0])
chainp=[]
v=tot
while v!=airs[0][0]:
    p,op,a=D[v]; assert op=='add'; chainp.append(p); v=a[0]
assert [D[D[v][2][1]][0] if False else None for v in []]==[]
L=[]
L.append('/-- **The air check**: the sumcheck\'s final claim is the six tables\' air terms\' sum. -/')
L.append('theorem vt_air_total {rd : Reader} {σ : Val} (h : VtH rd σ) :')
L.append(f'    σ (.n {CLAIM}) = '+' + '.join(f'σ (.n {a})' for a,_ in airs)+' := by')
poss=chainp+[pe_[0]]
for q in poss: L.append(at(q))
L.append('  simp only [Atom.Holds] at '+' '.join(f'a{q}' for q in poss))
L.append(f'  rw [eq_neg_of_add_eq_zero_right a{pe_[0]}, CharTwo.neg_eq, '+', '.join(f'a{q}' for q in chainp)+']')
out.append('\n'.join(L))
write('Air',"`verify_tables`' air check: each table's weight and form value, and their sum the table\n  sumcheck's final claim.",'LeanVM.Guest.B1.Tables.Vt.FormsVal\npublic import LeanVM.Guest.B1.Tables.Vt.Pi','\n\n'.join('set_option maxRecDepth 10000 in\n'+x for x in out))
