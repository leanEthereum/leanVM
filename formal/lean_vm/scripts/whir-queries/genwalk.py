"""Write B1/Opening/WalkBody{0,1,2}.lean and WalkFns.lean from the guest data."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
D = os.path.join(sys.argv[1], 'LeanVM') + '/' + 'Guest/B1/Opening/'
ws = sorted((tuple(map(int, n[len('walk_path__L'):].split('_L'))), n, i)
            for n, i in gen.fns.items() if n.startswith('walk_path__L'))
parts = [ws[k::3] for k in range(3)]
for k, part in enumerate(parts):
    out = ['''/-
  LeanVM.Guest.B1.Opening.WalkBody%d

  The bodies of a third of `walk_path`'s specializations are the template (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section
''' % k]
    for (pd, cd), n, i in part:
        out.append('''set_option maxRecDepth 100000 in
/-- `%s`. -/
theorem wpBody_L%d_L%d : Data.core%d.body = wpBodyT ⟨0, 0, %d, %d, 0, [], 0, 0⟩ :=
  stmtsEqb_sound (by decide +kernel)
''' % (n, pd, cd, i, pd, cd))
    out.append('end\nend LeanVM.Guest.B1\n')
    open(D + 'WalkBody%d.lean' % k, 'w').write('\n'.join(out))
import re
qt = open(D + 'QueriesT.lean').read()
blk = qt[qt.index('def walkPathNames'):]
blk = blk[:blk.index(']')]
order = [(int(a), int(b)) for a, b in re.findall(r'\((\d+), (\d+), "walk_path', blk)]
assert len(order) == len(ws)
src = open(D + 'WalkFns.lean').read()
head = src[:src.index('set_option maxRecDepth 100000 in')]
out = [head.rstrip() + '\n']
for (pd, cd), n, i in ws:
    out.append('''set_option maxRecDepth 100000 in
/-- `%s` is its template. -/
theorem wpFn_L%d_L%d : WalkFn "%s" %d %d :=
  ⟨_, coreProgram_find?_at (j := %d) rfl, rfl, wpBody_L%d_L%d⟩
''' % (n, pd, cd, n, pd, cd, i, pd, cd))
out.append('''/-- **Every deployed `walk_path` is its template.** -/
theorem walkFn_all : ∀ p ∈ walkPathNames, WalkFn p.2.2 p.1 p.2.1 := by
  intro p hp
  simp only [walkPathNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with %s
  exacts [%s]

end
end LeanVM.Guest.B1
''' % (' | '.join(['rfl'] * len(ws)),
       ', '.join('wpFn_L%d_L%d' % pc for pc in order)))
open(D + 'WalkFns.lean', 'w').write('\n'.join(out))
