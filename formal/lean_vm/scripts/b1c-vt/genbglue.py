# usage: python3 -I genbglue.py > ../../LeanVM/Guest/B1/Tables/VtC/BGlueGen.lean
# verify_tables' bus sides between the selectors and the stream reads (statements 769 ..< 2589 at
# main 40f877dc): one lemma per slice, the statements beyond evaluation by kind (fp_w, claim_pool and
# block_index_mle reads), the others (stores, dispatches, the KECCAK) taken as hypotheses.
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vtflat
top, flat, ctr, cend = vtflat.load()
tctr = {}
for (k, s), c in zip(flat, ctr): tctr.setdefault(k, c)
SLICES = [(769, 772), (784, 794), (807, 817), (826, 830), (839, 843), (852, 864), (877, 943),
          (1433, 1881), (1890, 1924), (1933, 2100), (2533, 2589)]
READ = {13: ('hw', 16), 15: ('hpool', 5), 781: ('hidx', 3)}
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
    if 'hw' in used: H += '{W : ℕ → E}\n    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) '
    if 'hpool' in used: H += '{P : ℕ → E}\n    (hpool : ∀ i < 5, LoadHolds rd (vtσ rd wo args (.n 15)) i (P i)) '
    if 'hidx' in used: H += '{Q : ℕ → E}\n    (hidx : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 781)) i (Q i)) '
    sys.stderr.write(f'{name}: {sorted(used)} specials {specials}\n')
    out.append(f'''set_option maxRecDepth 100000 in
theorem {name} (hl : args.length = 20) {H}{hyps} :
    ∀ s ∈ (vtPre.drop {a}).take {b - a}, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
{body}''')
print('''/-
  LeanVM.Guest.B1.Tables.VtC.BGlueGen

  `verify_tables`' bus sides between the selectors and the stream reads, slice by slice
  (generated: scripts/b1c-vt/genbglue.py).
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
