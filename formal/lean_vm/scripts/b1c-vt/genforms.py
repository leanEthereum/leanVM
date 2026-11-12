import os, sys
# Library for mk.py: the per-block and per-side lemmas of Tables/Vt/FormsT*.lean from the body and FormsData.
# First run: python3 -I dump.py ../../LeanVM/Guest/Data/Core00.lean vt_ir.txt (from this directory).
import sys,re,json,ast
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symev import *
# vtEvalData (EvalsT.lean): evaluation k's first statement and its value (copied to value + 3).
_ed = open(os.path.join(VT_LEAN, 'EvalsT.lean')).read()
_ed = _ed[_ed.index('def vtEvalData'):]
_ed = _ed[_ed.index(':=') + 2:_ed.index('\n\n')]
EV = [(p, b, k) for k, (p, b) in enumerate(ast.literal_eval(' '.join(_ed.split())))]
evvar={}   # copy var -> k
for (p,b,k) in EV: evvar[b+3]=k
BASE=[0,13,26,33,47,61]; WIDTH=[13,13,7,14,14,92]
# The forms' window, the ξ powers multiplying the push/pull/count forms (G:2700), W's and β's variables.
WLO, WHI = 2685, 5524
XI = (2613, 2614, 2615)
WV, BV = 13, 14
# Each table's form values per side: the operands of its `ξ²·F0`, `ξ³·F1`, `ξ⁴·F2`, in table order.
def _formvals():
    res = {str(t): [] for t in range(6)}
    for sd, xi in enumerate(XI):
        ms = [parse_atom(IR[p])[1] for p in range(WLO, WHI + 1)
              if parse_atom(IR[p]) and parse_atom(IR[p])[0] == 'mul' and parse_atom(IR[p])[1][1] == xi]
        assert len(ms) == 6, (sd, ms)
        for t in range(6): res[str(t)].append(ms[t][2])
    return res
# defs over whole IR, first def wins but only for positions in a window
def defs_window(lo,hi):
    d={}
    for p in range(lo,hi+1):
        a=parse_atom(IR[p])
        if a is None: continue
        op,args=a
        if op in ('add','mul','copy'): d.setdefault(args[0],(p,op,args[1:]))
        elif op=='const': d.setdefault(args[0],(p,'const',args[1]))
        elif op=='load': d.setdefault(args[0],(p,'load',args[1:]))
    return d
def chain(F,d):
    """F = add(add(mul(s0,B0), mul(s1,B1)), ...) -> [(s,B,mulvar)]"""
    out=[]; adds=[]
    v=F
    while True:
        p,op,a=d[v]
        if op=='mul':
            out.append((a[0],a[1],v)); break
        assert op=='add',(v,op)
        adds.append(v)
        l,r=a
        pr,opr,ar=d[r]; assert opr=='mul'
        out.append((ar[0],ar[1],r))
        v=l
    out.reverse()
    return out,adds
def deps_stop(v,d,acc,stop):
    if v in stop or v not in d: return
    p,op,args=d[v]
    if p in acc: return
    acc.add(p)
    if op in ('add','mul','copy'):
        for a in args: deps_stop(a,d,acc,stop)

FV = _formvals()
RAW={}
for line in open(IRF).read().splitlines():
    k,_,s=line.partition(': ')
    s=s.strip()
    if s.endswith(' ::'): s=s[:-3]
    RAW[int(k)]=s
D=defs_window(WLO,WHI)
def bterms_lit(sd,t):
    src=open(os.path.join(VT_LEAN, 'FormsData.lean')).read()
    m=re.search(r'def vtBTerms%d%d : [^\n]*:=\n(.*?)\n\n'%(sd,t),src,re.S)
    lit=' '.join(x.strip() for x in m.group(1).split('\n'))
    return ast.literal_eval(lit.replace('(','(').replace('[','[')) , lit
def pylit(blk):
    # python data -> lean literal text
    def coord(c): return '['+', '.join('(['+', '.join(str(i) for i in m)+'], '+str(v)+')' for m,v in c)+']'
    return '['+', '.join(coord(c) for c in blk)+']'
def wrapl(text,ind='      ',width=98):
    # break a long comma list
    out=[];line=''
    for tok in text.split(', '):
        if len(line)+len(tok)+2>width: out.append(line+','); line=ind+tok
        else: line=(line+', '+tok) if line.strip() else (line+tok)
    out.append(line)
    return '\n'.join(out)
def runs(pos):
    """Maximal runs of consecutive positions."""
    out=[]
    for q in sorted(pos):
        if out and out[-1][-1]==q-1: out[-1].append(q)
        else: out.append([q])
    return out
def slices(pos):
    """A slice read per run of the positions, its atoms named `a<position>`."""
    L=[]
    for i,r in enumerate(runs(pos)):
        L.append(f'  obtain ⟨_, hs{i}⟩ := h.sliceAt {r[0]} [')
        L.append(',\n'.join('    '+RAW[q] for q in r)+'] (by decide +kernel)')
        L.append(f'  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hs{i}')
        L.append('  obtain ⟨'+wrapl(', '.join([f'a{q}' for q in r]+['-']),'    ',96)+f'⟩ := hs{i}')
    return L
def block_lemma(t,sd,bi,s,B,blk,ch,diff=False):
    acc=set(); deps_stop(B,D,acc,set(evvar))
    lo,hi0=min(acc),max(acc)
    mv=ch[bi][2]
    hi=hi0+1 if bi==0 else hi0+2
    accv=mv if bi==0 else parse_atom(RAW[hi])[1][0]
    prev=None
    if bi>=1:
        pb=ch[bi-1]; a2=set(); deps_stop(pb[1],D,a2,set(evvar)); ph=max(a2)
        prev=pb[2] if bi==1 else parse_atom(RAW[ph+2])[1][0]
    pos=sorted(acc|set(range(hi0+1,hi+1)))
    name=f'vtD{t}_{bi}' if diff else f'vtB{sd}{t}_{bi}'
    val=(lambda b: f'vtSlots W ev 0 {b}') if diff else (lambda b: f'vtBlockVal (σ (.n {BV})) W ev {b}')
    L=[]
    L.append(f'theorem {name} {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) {{W ev : ℕ → E}}')
    L.append(f'    (hw : ∀ i < 16, LoadHolds rd (σ (.n {WV})) i (W i))')
    L.append(f'    (hev : ∀ c < {WIDTH[t]}, σ (.n (vtEvB ({BASE[t]} + c))) = ev c) :')
    lhs=f'σ (.n {accv}) = ' + (f'σ (.n {prev}) + ' if bi>=1 else '') + f'σ (.n {s}) * '+val('').rstrip()
    L.append(f'    {lhs}')
    L.append(f'      {pylit(blk)} := by')
    L+=slices(pos)
    evs=set(); rws=[]
    for q in sorted(acc):
        o=parse_atom(RAW[q])
        if o[0]=='load':
            L.append(f'  have e{q} := tb_loadHolds_unique a{q} (hw {o[1][2]} (by norm_num))')
            rws.append(f'e{q}')
        else:
            rws.append(f'a{q}')
            for x in o[1][1:] if o[0] in ('add','mul','copy') else []:
                if x in evvar: evs.add(x)
    for x in sorted(evs):
        k=evvar[x]; c=k-BASE[t]
        assert 0<=c<WIDTH[t]
        L.append(f'  have v{x} : σ (.n {x}) = ev {c} := by')
        L.append(f'    rw [← hev {c} (by norm_num)]; exact (vt_eval h (k := {k}) (by norm_num)).2.2')
        rws.append(f'v{x}')
    L.append(f'  have hB : σ (.n {B}) = {val(pylit(blk))} := by')
    L.append('    simp only ['+wrapl(', '.join(reversed(rws)),'      ',94)+']')
    consts=set(parse_atom(RAW[q])[1][1][0] for q in acc if parse_atom(RAW[q])[0]=='const')
    coefs=set(v for c in blk for m,v in c)
    extra=(['vt_word_ofK'] if consts else [])+(['vt_ofK_ofBits_zero'] if (0 in consts or 0 in coefs) else [])+(['vt_ofK_ofBits_one'] if (1 in consts or 1 in coefs) else [])
    L.append('    simp only ['+('' if diff else 'vtBlockVal_eq, ')+'vtSlots, vtCoordVal_cons, vtCoordVal_nil, List.map_cons,')
    L.append('      List.map_nil, List.prod_cons, List.prod_nil'+''.join(', '+x for x in extra)+']')
    L.append('    ring')
    L.append(f'  rw [{"a"+str(hi)+", " if bi>=1 else ""}a{hi0+1}, hB]')
    return name,'\n'.join(L)
def side_lemma(t,sd,blocks_lits,ch,bnames):
    F=FV[str(t)][sd]
    name=f'vtSide{sd}{t}'
    L=[]
    sels='['+', '.join(f'σ (.n {s})' for s,B,mv in ch)+']'
    L.append(f'theorem {name} {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) {{'+('W ' if sd<2 else '')+'ev : ℕ → E}')
    if sd<2: L.append(f'    (hw : ∀ i < 16, LoadHolds rd (σ (.n {WV})) i (W i))')
    L.append(f'    (hev : ∀ c < {WIDTH[t]}, σ (.n (vtEvB ({BASE[t]} + c))) = ev c) :')
    beta=f'σ (.n {BV})' if sd<2 else '0'
    Wn='W' if sd<2 else '(fun _ ↦ 1)'
    L.append(f'    σ (.n {F}) =')
    L.append('      vtSideVal '+wrapl(sels,'        ',90)+f'\n        ({beta}) {Wn} ev vtBTerms{sd}{t} := by')
    assoc=', add_assoc' if len(ch)>=3 else ''
    if sd<2:
        L.append('  rw ['+wrapl(', '.join(f'{b} h hw hev' for b in reversed(bnames)),'    ',96)+']')
        L.append(f'  simp only [vtSideVal, vtBTerms{sd}{t}, List.zipWith_cons_cons, List.zipWith_nil_left,')
        L.append(f'    List.sum_cons, List.sum_nil, add_zero{assoc}]')
        return name,'\n'.join(L)
    acc=set(); deps_stop(F,D,acc,set(evvar))
    L+=slices(acc)
    evs=set(); rws=[]
    for q in sorted(acc):
        o=parse_atom(RAW[q]); rws.append(f'a{q}')
        for x in o[1][1:] if o[0] in ('add','mul','copy') else []:
            if x in evvar: evs.add(x)
    for x in sorted(evs):
        k=evvar[x]; c=k-BASE[t]
        assert 0<=c<WIDTH[t]
        L.append(f'  have v{x} : σ (.n {x}) = ev {c} := by')
        L.append(f'    rw [← hev {c} (by norm_num)]; exact (vt_eval h (k := {k}) (by norm_num)).2.2')
        rws.append(f'v{x}')
    L.append('  simp only ['+wrapl(', '.join(reversed(rws)),'    ',96)+']')
    L.append(f'  simp only [vtSideVal, vtBTerms{sd}{t}, List.zipWith_cons_cons, List.zipWith_nil_left,')
    L.append(f'    List.sum_cons, List.sum_nil, vtBlockVal_eq, vtSlots, vtCoordVal_cons, vtCoordVal_nil,')
    L.append(f'    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, vt_ofK_ofBits_one]')
    L.append('  ring')
    return name,'\n'.join(L)
HDR="""/-
  LeanVM.Guest.B1.Tables.Vt.%(mod)s

  %(doc)s
-/

module

public import %(imp)s

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

"""
FTR="""
end
end LeanVM.Guest.B1.Tables
"""
def gen_table(t,sides=(0,1,2),blocks=None,with_side=True):
    out=[]
    for sd in sides:
        data,lit=bterms_lit(sd,t)
        if sd==1:
            out.append(pull_side(t,with_side)); continue
        F=FV[str(t)][sd]; ch,_=chain(F,D)
        assert len(ch)==len(data)
        bn=[]
        for bi,(s,B,mv) in enumerate(ch):
            if sd<2:
                n=f'vtB{sd}{t}_{bi}'; bn.append(n)
                if blocks is None or bi in blocks:
                    n,txt=block_lemma(t,sd,bi,s,B,data[bi],ch)
                    out.append('set_option maxRecDepth 10000 in\n'+txt)
        if with_side:
            n,txt=side_lemma(t,sd,data,ch,bn); out.append('set_option maxRecDepth 10000 in\n'+txt)
    return '\n\n'.join(out)

import gendiff
def pull_side(t,with_side=True,blocks=None):
    """Table t's pull form: `F1 = F0 + Σ_b sel_b · Σ_i W_i · diff_i` (G:2645-2700)."""
    F0,F1=FV[str(t)][0],FV[str(t)][1]
    p1,op,a=D[F1]; assert op=='add' and a[0]==F0,(t,F1,op,a)
    Fd=a[1]; ch,_=chain(Fd,D); dt=gendiff.DT[t]
    assert len(ch)==len(dt) and all(any(c) for c in dt),(t,len(ch),len(dt))
    out=[]; bn=[]
    for bi,(s,B,mv) in enumerate(ch):
        n=f'vtD{t}_{bi}'; bn.append(n)
        if blocks is None or bi in blocks:
            n,txt=block_lemma(t,1,bi,s,B,dt[bi],ch,diff=True)
            out.append('set_option maxRecDepth 10000 in\n'+txt)
    if with_side:
        chP,_=chain(F0,D)
        sels='['+', '.join(f'σ (.n {s})' for s,B,mv in ch)+']'
        L=[f'theorem vtSide1{t} {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) {{W ev : ℕ → E}}']
        L.append(f'    (hw : ∀ i < 16, LoadHolds rd (σ (.n {WV})) i (W i))')
        L.append(f'    (hev : ∀ c < {WIDTH[t]}, σ (.n (vtEvB ({BASE[t]} + c))) = ev c) :')
        L.append(f'    σ (.n {F1}) =')
        L.append('      vtSideVal '+wrapl(sels,'        ',90)+f'\n        (σ (.n {BV})) W ev vtBTerms1{t} := by')
        L.append(f'  have hF0 : σ (.n {F0}) =')
        L.append('      vtSideVal '+wrapl(sels,'        ',90)+f'\n        (σ (.n {BV})) W ev vtBTerms0{t} := by')
        L.append(f'    rw [vtPullSels{t} h]; exact vtSide0{t} h hw hev')
        L.append(f'  have a{p1} := h.atomAt {p1} {RAW[p1][len(".atom "):]} (by decide +kernel)')
        L.append(f'  simp only [Atom.Holds] at a{p1}')
        L.append(f'  rw [vtSideVal_pull _ _ _ _ _ _ _ vtPull{t}, ← hF0, a{p1}, '+wrapl(', '.join(f'{b} h hw hev' for b in reversed(bn)),'    ',96)+']')
        assoc=', add_assoc' if len(ch)>=3 else ''
        L.append(f'  simp only [vtDiffSum, vtDTerms{t}, List.zipWith_cons_cons, List.zipWith_nil_left,')
        L.append(f'    List.sum_cons, List.sum_nil, add_zero{assoc}]')
        out.append('set_option maxRecDepth 10000 in\n'+'\n'.join(L))
    return '\n\n'.join(out)
