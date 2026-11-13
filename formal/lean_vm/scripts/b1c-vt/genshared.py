# usage: python3 -I genshared.py  — writes Tables/Vt/SharedT.lean (verify_tables' shared selector
# tables, G:2318-2325 at the commit in leanvm-rev: each table's `shared_len` and its `shared_selector_tables` call,
# the tables' pointers stepped one from another) from vt_ir.txt (dump.py).
import os, sys, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from symev import IR, parse_atom, VT_LEAN

def atom(p): return parse_atom(IR[p])

W288, W144 = 299140177199104, 21299200

def main():
    # find the six calls
    calls = [p for p in range(690, 800) if IR[p].startswith('.call "shared_selector_tables"')]
    assert len(calls) == 6, calls
    EQ0, G0 = 701, 702
    assert 'alloc (.n 701) 1728' in IR[695]
    out = []
    prev_end = 696
    val = {EQ0: ('EQ', 0), G0: ('G', 0)}   # var -> (table kind, exponent in units)
    for t, pc in enumerate(calls):
        args = [int(x) for x in re.findall(r'\.n (\d+)', IR[pc])]
        eqv, gv, zv, z1v, sqv, lenv = args
        L = []; hs = []
        facts = {}
        for p in range(prev_end + 1, pc):
            if not IR[p].startswith('.atom'): continue
            a = atom(p)
            nm = f'a{p}'
            L.append(f'  have {nm} := h.atomAt {p} _ (by decide +kernel)')
            hs.append((nm, p, a))
        # Lean atoms written out, from the IR text
        lines = []
        for nm, p, a in hs:
            if a and a[0] == 'hint': continue
            txt = IR[p]
            m = re.match(r'\.atom \((.*)\)$', txt)
            lines.append(f'  have {nm} := h.atomAt {p} ({m.group(1)}) (by decide +kernel)')
        # facts: mul 9 len (30+t); copy lenc len; const w33; rc lenc ...; eq/g pointer steps; z/z1/sq
        defs = {}
        for nm, p, a in hs:
            if a and a[0] in ('mul', 'copy', 'const'): defs[a[1][0]] = (nm, a)
        # pointer chains
        def ptr(v, base):
            # returns (rw list, exponent) with σ v = σ base * gen ^ e
            if v == base: return [], 0
            nm, a = defs[v] if v in defs else gdefs[v]
            assert a[0] == 'mul'
            src, c = a[1][1], a[1][2]
            cnm, ca = defs[c] if c in defs else gdefs[c]
            w = ca[1][1][0]
            e = 288 if w == W288 else 144 if w == W144 else None
            assert e is not None, w
            r, e0 = ptr(src, base)
            return [nm, cnm] + r, e0 + e
        for k, v in defs.items(): gdefs[k] = v
        eqr, eqe = ptr(eqv, EQ0); gr, ge = ptr(gv, G0)
        assert eqe == 288 * t and ge == 144 * t, (t, eqe, ge)
        lastc = calls[t - 1] if t else 696
        seg = [x for x in hs if x[1] > lastc]
        mlen = [a for nm, p, a in seg if a and a[0] == 'mul' and a[1][0] == 9]
        assert mlen and mlen[0][1][2] == 27 + t
        lenraw = mlen[0][1][1]
        cp = [(nm, a) for nm, p, a in seg if a and a[0] == 'copy']
        assert cp and cp[0][1][1] == [lenv, lenraw]
        rc = [(nm, a) for nm, p, a in seg if a and a[0] == 'rangeCheck']
        assert len(rc) == 1
        zm = [(nm, a) for nm, p, a in seg if a and a[0] == 'mul' and a[1][0] in (zv, z1v, sqv)]
        nmof = {a[1][0]: nm for nm, a in zm}
        assert [a[1][1] for nm, a in zm] == [8, 699, 12] and all(a[1][2] == 27 + t for nm, a in zm)
        mnm = [nm for nm, p, a in seg if a and a[0] == 'mul' and a[1][0] == 9][0]
        cnm = cp[0][0]
        rcnm = rc[0][0]
        rcidx = [p for nm, p, a in seg if nm == rcnm][0]
        wvar = int(re.findall(r'\.n (\d+)', IR[rcidx])[-1]); wnm = defs[wvar][0]
        simpl = ' '.join(nm for nm, p, a in hs if a and a[0] in ('mul', 'copy', 'const'))
        body = '\n'.join(lines)
        body += f'\n  have hc := h.callAt {pc} "shared_selector_tables" [.n {eqv}, .n {gv}, .n {zv}, .n {z1v}, .n {sqv}, .n {lenv}] []\n    (by decide +kernel)'
        # the call holds as a relation
        body += f'\n  simp only [Atom.Holds] at {simpl}'
        for nm, p, a in hs:
            if a and a[0] == 'const' and a[1][1][0] in (W288, W144):
                body += f'\n  rw [{"vtW288_eq" if a[1][1][0] == W288 else "vtW144_eq"}] at {nm}'
        def ptrproof(r, e, base):
            if not r: return 'by ring'
            rws = []
            for i in range(0, len(r), 2): rws += [r[i], r[i + 1]]
            return f'by rw [{", ".join(rws)}]' if len(r) == 2 else f'by rw [{", ".join(rws)}]; ring'
        out.append(f'''theorem vt_sh{t} {{rd : Reader}} {{σ : Val}} (h : VtH rd σ) :
    σ (.n 9) = σ (.n {lenv}) * σ (.n {27 + t}) ∧ (Atom.rangeCheck {rc[0][1][1]}).Holds rd σ ∧
      σ (.n {wvar}) = vtW33 ∧
      coreProgram.Rel rd "shared_selector_tables" [σ (.n {EQ0}) * gen ^ (288 * {t}),
        σ (.n {G0}) * gen ^ (144 * {t}), σ (.n 8) * σ (.n {27 + t}), σ (.n 699) * σ (.n {27 + t}),
        σ (.n 12) * σ (.n {27 + t}), σ (.n {lenv})] [] ∧
      σ (.n {eqv}) = σ (.n {EQ0}) * gen ^ (288 * {t}) ∧ σ (.n {gv}) = σ (.n {G0}) * gen ^ (144 * {t}) := by
{body}
  have e1 : σ (.n {eqv}) = σ (.n {EQ0}) * gen ^ (288 * {t}) := {ptrproof(eqr, eqe, EQ0)}
  have e2 : σ (.n {gv}) = σ (.n {G0}) * gen ^ (144 * {t}) := {ptrproof(gr, ge, G0)}
  refine ⟨by rw [{mnm}, ← {cnm}], {rcnm}, {wnm}, ?_, e1, e2⟩
  rw [← e1, ← e2, ← {nmof[zv]}, ← {nmof[z1v]}, ← {nmof[sqv]}]
  simpa using hc''')
    return out

gdefs = {}
HDR = '''/-
  LeanVM.Guest.B1.Tables.Vt.SharedT

  `verify_tables`' shared selector tables' statements, read off the body by kernel evaluation.
  Generated by `scripts/b1c-vt/genshared.py`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base
public import LeanVM.Guest.CoreData

/-!
# The shared tables' statements (G:2318-2325)

`vt_sh{t}`: table `t`'s `shared_len[t]` (`σ 9 = len · τ_g`, `τ_g = kb[2 + t]` the variable
`27 + t`), its range check below `g^34`, and its `shared_selector_tables` call at
`shared_eq·g^(288 t)`, `shared_g·g^(144 t)` (the compiler steps these pointers from one another).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `g^33`, `g^288`, `g^144`, as the data writes them. -/
abbrev vtW33 : E := word 8589934592 0
abbrev vtW288 : E := word 299140177199104 0
abbrev vtW144 : E := word 21299200 0

theorem vtW288_eq : word 299140177199104 0 = gen ^ 288 := by
  rw [tb_word_eOfNat, eOfNat, gen_pow_eq_ofK,
    show K.ofBits 299140177199104 = Parameters.addressOfIndex 288 by decide +kernel]

theorem vtW144_eq : word 21299200 0 = gen ^ 144 := by
  rw [tb_word_eOfNat, eOfNat, gen_pow_eq_ofK,
    show K.ofBits 21299200 = Parameters.addressOfIndex 144 by decide +kernel]
'''

if __name__ == '__main__':
    lemmas = main()
    open(os.path.join(VT_LEAN, 'SharedT.lean'), 'w').write(
        HDR + '\n' + '\n\n'.join(lemmas) + '\n\nend\nend LeanVM.Guest.B1.Tables\n')
