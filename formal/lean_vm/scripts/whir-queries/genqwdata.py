"""Write B1/Bits/QueryWindowsData.lean from the guest data."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
P = os.path.join(sys.argv[1], 'LeanVM') + '/' + 'Guest/B1/Bits/QueryWindowsData.lean'
shapes = sorted((tuple(map(int, n[len('decode_query_windows__L'):].split('_L'))), n, i)
                for n, i in gen.fns.items() if n.startswith('decode_query_windows__L'))
N = len(shapes)
out = ['''/-
  LeanVM.Guest.B1.Bits.QueryWindowsData

  The %d specializations of `decode_query_windows` are their template, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsT
public import LeanVM.Guest.B1.Common.Find

/-!
# `decode_query_windows`' specializations

`queryWindowsShapes`: the deployed `(name, depth, cap depth)`; `queryWindows_data`: each is found
in the core IR with the parameters `0 .. 3` and the body `qwBody d cd` (`stmtsEqb_sound`, one
kernel evaluation each).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest

@[expose] public section
''' % N]
names = []
for (d, cd), n, i in shapes:
    t = 'qw_L%d_L%d' % (d, cd); names.append(t)
    out.append('''set_option maxRecDepth 100000 in
theorem %s : QwIs "%s" (qwBody %d %d) :=
  ⟨Data.core%d, coreProgram_find?_at (j := %d) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩
''' % (t, n, d, cd, i, i))
out.append('''/-- **Every deployed specialization is its template.** -/
theorem queryWindows_data : ∀ p ∈ queryWindowsShapes, QwIs p.1 (qwBody p.2.1 p.2.2) := by
  intro p hp
  simp only [queryWindowsShapes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with %s
  exacts [%s]

end
end LeanVM.Guest.B1
''' % (' | '.join(['rfl'] * N), ', '.join(names)))
open(P, 'w').write('\n'.join(out))
