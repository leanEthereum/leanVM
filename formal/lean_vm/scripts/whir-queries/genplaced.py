"""Write B1/Opening/QueriesPlacedS{0..3}.lean: each `opening_queries` specialization of
`QueriesBody{k}` (`genoq`'s quarters) is `CompleteAtB` (`OqCompleteDB`), from its body's and its
loop's templates and its `walk_path`'s (`WalkFns`)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
D = os.path.join(sys.argv[1], 'LeanVM') + '/' + 'Guest/B1/Opening/'
sp = gen.oq_specs()


def shape(d):
    return '⟨%d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, [%s]⟩' % (
        d['odd'], d['base'], d['folds'], d['leaf'], d['depth'], d['cd'], d['mu'], d['vanish'], d['nhs'],
        d['hsb'], d['final'], ', '.join(map(str, d['vs'])))


HEAD = '''/-
  LeanVM.Guest.B1.Opening.QueriesPlacedS%d

  A quarter of `opening_queries`' specializations, `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody%d
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section
'''
for k in range(4):
    out = [HEAD % (k, k)]
    for d in sp[k::4]:
        sh = shape(d)
        i = d['idx']
        wp = 'wpFn_L%d_L%d' % (d['depth'] - d['cd'], d['cd'])
        if d['base'] == 1:
            head = ('  oqCompleteDB1 fs cert (s := ((%s : OqShape).oq)) (by decide) (by decide) rfl (by decide)\n'
                    '    (by decide) (by decide : %d ≤ 1) (by decide +kernel) %s\n' % (sh, d['odd'], wp))
        else:
            head = ('  oqCompleteDB0 fs cert (s := ((%s : OqShape).oq)) (by decide) (by decide) rfl (by decide)\n'
                    '    (by decide) (by decide +kernel) %s\n' % (sh, wp))
        out.append('''
set_option maxRecDepth 100000 in
/-- `%s` is `CompleteAtB`. -/
theorem oqD_%d (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "%s" "%s" (%s : OqShape).oq %d :=
%s    (Program.find?_of_indexOf? (j := %d) (by decide +kernel) rfl) rfl oqBody_%d
    (Program.find?_of_indexOf? (j := %d) (by decide +kernel) rfl) rfl oqLoopBody_%d
''' % (d['name'], i, d['name'], d['loop'], sh, d['odd'], head, i, i, d['loopidx'], i))
    out.append('\nend\nend LeanVM.Guest.B1\n')
    open(D + 'QueriesPlacedS%d.lean' % k, 'w').write(''.join(out))

# QueriesPlacedAll.lean: the case split over `openingQueriesLoops` (in the order of `gen.oq_specs`).
p = D + 'QueriesPlacedAll.lean'
s = open(p).read()
i = s.index('  rcases hp with ')
s = s[:i] + '  rcases hp with ' + ' | '.join(['rfl'] * len(sp)) + '\n' + \
    ''.join('  · exact oqD_%d fs cert\n' % d['idx'] for d in sp) + '\nend\nend LeanVM.Guest.B1\n'
s = s.replace('each of the 73 deployed', 'each of the %d deployed' % len(sp))
open(p, 'w').write(s)
