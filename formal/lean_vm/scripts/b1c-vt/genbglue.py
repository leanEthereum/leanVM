# usage: python3 -I genbglue.py > ../../LeanVM/Guest/B1/Tables/VtC/BGlueGen.lean
# verify_tables' bus sides outside the selectors (statements 765 ..< 2593 of the guest): one
# lemma per slice, the statements beyond evaluation by kind (reads of the cursor, fp_w, claim_pool,
# block_index_mle, bc_point and gkr_leaves; the KECCAKs), the others (stores, dispatches, calls, the
# bytecode share's value and its closing check) taken as hypotheses.
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vtflat
top, flat, ctr, cend = vtflat.load()
tctr = {}
for (k, s), c in zip(flat, ctr): tctr.setdefault(k, c)
SLICES = [(765, 766), (778, 781), (794, 811), (824, 842), (1332, 1479), (1912, 1926), (1926, 2021),
          (2021, 2593)]
READ = {13: ('hw', 16), 15: ('hpool', 4), 777: ('hidx', 3), 5: ('hcur', 7), 19: ('hpt', 4),
        17: ('hleaves', 3)}
HYP = {'hw': ('W', 13, 16), 'hpool': ('P', 15, 4), 'hidx': ('Q', 777, 3), 'hcur': ('C', 5, 7),
       'hpt': ('T', 19, 4), 'hleaves': ('G', 17, 3)}
def auto(s):
    m = re.match(r'\.atom \(\.(\w+)', s)
    if not m: return False
    op = m.group(1)
    if op in ('const', 'add', 'copy', 'hint'): return True
    if op == 'mul':
        v = [int(x) for x in re.findall(r'\.n (\d+)', s)]
        return v[1] < v[0] and v[2] < v[0]
    return False
out = []
for a, b in SLICES:
    rest = []; proofs = []; specials = []; used = set()
    for k in range(a, b):
        s = top[k]
        if auto(s): continue
        mi = re.match(r'\.dispatch \(\.n (\d+)\) \("index_mle__L0" :: .*\) \[\.n 8\] \[\.n (\d+)\]$', s)
        if mi:
            s = f'.dispatch (.n {mi.group(1)}) vtImNames [.n 8] [.n {mi.group(2)}]'
            top[k] = s
        rest.append(s)
        m = re.match(r'\.atom \(\.load \(\.n (\d+)\) \(\.n (\d+)\) (\d+)\)$', s)
        if m and int(m.group(1)) == tctr[k] and int(m.group(2)) in READ:
            d, p, off = map(int, m.groups())
            nm, lim = READ[p]
            assert off < lim, (k, s)
            proofs.append(f'(vt_readAt hl {k} (by decide +kernel) (by decide +kernel) ({nm} {off} (by norm_num))).2')
            used.add(nm)
            continue
        if s.startswith('.atom (.keccak '):
            proofs.append(f'vtB_keccakAt hl {k} (by decide +kernel)')
            continue
        specials.append(k)
        proofs.append(f'h{k}')
    name = f'vtB_glue_{a}'
    hyps = ''.join(f'\n    (h{k} : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) ({top[k]}))' for k in specials)
    restl = ',\n    '.join(rest)
    if rest:
        body = (f'  refine vt_blockR hl {a} {b - a} [\n    {restl}] (by decide +kernel) ?_\n'
                f'  intro s hs _\n'
                f'  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs\n'
                f'  rcases hs with {" | ".join(["rfl"] * len(rest))}\n' +
                ''.join(f'  · exact {p}\n' for p in proofs))
    else:
        body = f'  exact vt_blockR hl {a} {b - a} [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))\n'
    H = ''
    for nm in ['hw', 'hpool', 'hidx', 'hcur', 'hpt', 'hleaves']:
        if nm in used:
            f, p, n = HYP[nm]
            H += f'{{{f} : ℕ → E}}\n    ({nm} : ∀ i < {n}, LoadHolds rd (vtσ rd wo args (.n {p})) i ({f} i)) '
    sys.stderr.write(f'{name}: {sorted(used)} specials {specials}\n')
    out.append(f'''set_option maxRecDepth 100000 in
theorem {name} (hl : args.length = 20) {H}{hyps} :
    ∀ s ∈ (vtPre.drop {a}).take {b - a}, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
{body}''')
print('''/-
  LeanVM.Guest.B1.Tables.VtC.BGlueGen

  `verify_tables`' bus sides outside the selectors, slice by slice (generated:
  scripts/b1c-vt/genbglue.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BGlue
public import LeanVM.Guest.B1.Tables.Vt.SelFw

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}
''')
print('\n'.join(out))
print('''end

end
end LeanVM.Guest.B1.Tables''')
