"""Write B1/Opening/QueriesPlacedS{0..3}.lean: each `opening_queries` specialization of
`QueriesBody{k}` (`genoq`'s quarters) is `CompleteAtB` (`OqCompleteDB`), from its body's and its
loop's templates and its `walk_path`'s (`WalkFns`); and QueriesPlacedES{0..3}.lean,
QueriesPlacedEAll.lean: the same with the tree's size exact (`OqCompleteDE`, `QueriesPlacedE`)."""
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
  LeanVM.Guest.B1.Opening.QueriesPlaced%s%d

  A quarter of `opening_queries`' specializations, `CompleteAt%s`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody%d
public import LeanVM.Guest.B1.Opening.%s
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section
'''


def quarters(sfx, kind, pred, proof, thm, dep):
    """`QueriesPlaced{sfx}{k}`: each specialization `pred`, by `proof{1,0}`, named `thm_{idx}`."""
    for k in range(4):
        out = [HEAD % (sfx, k, kind, k, dep)]
        for d in sp[k::4]:
            sh = shape(d)
            i = d['idx']
            wp = 'wpFn_L%d_L%d' % (d['depth'] - d['cd'], d['cd'])
            if d['base'] == 1:
                head = ('  %s1 fs cert (s := ((%s : OqShape).oq)) (by decide) (by decide) rfl (by decide)\n'
                        '    (by decide) (by decide : %d ≤ 1) (by decide +kernel) %s\n' % (proof, sh, d['odd'], wp))
            else:
                head = ('  %s0 fs cert (s := ((%s : OqShape).oq)) (by decide) (by decide) rfl (by decide)\n'
                        '    (by decide) (by decide +kernel) %s\n' % (proof, sh, wp))
            out.append('''
set_option maxRecDepth 100000 in
/-- `%s` is `CompleteAt%s`. -/
theorem %s_%d (fs : String → ℕ) (cert : String → V → ℕ) :
    %s fs cert "%s" "%s" (%s : OqShape).oq %d :=
%s    (Program.find?_of_indexOf? (j := %d) (by decide +kernel) rfl) rfl oqBody_%d
    (Program.find?_of_indexOf? (j := %d) (by decide +kernel) rfl) rfl oqLoopBody_%d
''' % (d['name'], kind, thm, i, pred, d['name'], d['loop'], sh, d['odd'], head, i, i, d['loopidx'], i))
        out.append('\nend\nend LeanVM.Guest.B1\n')
        open(D + 'QueriesPlaced%s%d.lean' % (sfx, k), 'w').write(''.join(out))


def cases(thm):
    return ('  rcases hp with ' + ' | '.join(['rfl'] * len(sp)) + '\n' +
            ''.join('  · exact %s_%d fs cert\n' % (thm, d['idx']) for d in sp))


quarters('S', 'B', 'OqCompleteDB', 'oqCompleteDB', 'oqD', 'QueriesPlacedD2')
quarters('ES', 'E', 'OqCompleteDE', 'oqCompleteDE', 'oqDE', 'QueriesPlacedE')

# QueriesPlacedAll.lean: the case split over `openingQueriesLoops` (in the order of `gen.oq_specs`).
p = D + 'QueriesPlacedAll.lean'
s = open(p).read()
i = s.index('  rcases hp with ')
s = s[:i] + cases('oqD') + '\nend\nend LeanVM.Guest.B1\n'
s = s.replace('each of the 73 deployed', 'each of the %d deployed' % len(sp))
open(p, 'w').write(s)

# QueriesPlacedEAll.lean: the same, exact.
open(D + 'QueriesPlacedEAll.lean', 'w').write('''/-
  LeanVM.Guest.B1.Opening.QueriesPlacedEAll

  Every deployed specialization of `opening_queries` is `CompleteAtE`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedES0
public import LeanVM.Guest.B1.Opening.QueriesPlacedES1
public import LeanVM.Guest.B1.Opening.QueriesPlacedES2
public import LeanVM.Guest.B1.Opening.QueriesPlacedES3

/-!
# `opening_queries`, `CompleteAtE`, every specialization

`opening_queries_completeAtE`: each of the %d deployed specializations (`openingQueriesLoops`:
name, loop helper, shape) is `CompleteAtE` (`OqCompleteDE` at the shape's `Oq` and `odd`, by a tree
of exactly `oqBound fs name loop N` words) at every frame size `fs` and frame certificate `cert`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **Every deployed `opening_queries` is `CompleteAtE`.** -/
theorem opening_queries_completeAtE (fs : String → ℕ) (cert : String → V → ℕ) :
    ∀ p ∈ openingQueriesLoops, OqCompleteDE fs cert p.1 p.2.1 p.2.2.oq p.2.2.odd := by
  intro p hp
  simp only [openingQueriesLoops, List.mem_cons, List.not_mem_nil, or_false] at hp
%s
end
end LeanVM.Guest.B1
''' % (len(sp), cases('oqDE')))
