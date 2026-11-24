/-
  LeanVM.Protocol.EndToEnd.Sound.BusDepth

  The leanISA instance's push leaves and constraint count: size facts the bus and table phases'
  specifications take as hypotheses.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.BusLayout
import LeanVM.Protocol.EndToEnd.Front.LayoutStack

/-!
# The leanISA instance's push leaves and constraint count

Two size facts of the leanISA instance `leanIsaInstance prog s`, at every size, which the bus and
table phases' specification asks:

* `pushLeaves_leanIsa`: the push side's leaves are the three seeds' (state, memory, bytecode),
  then each opcode table's push flushes at its height;
* `B_leanIsa`: the sumcheck tables have two constraints, `JUMP`'s.

No hypothesis on the sizes is needed: the facts hold of the instance as built.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete

@[expose] public section

/-! ## The push side's leaves -/

/-- The instance's push leaves: the three seeds' (state, memory, bytecode), then each opcode
table's push flushes. -/
theorem pushLeaves_leanIsa (prog : LeanIsaProgram) (s : Sizes) :
    (leanIsaInstance prog s).pushLeaves = (1 + 2 ^ s.logMem + 2 ^ prog.logSize) +
      ∑ t : Fin 6, ((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = Side.push)).length *
        2 ^ s.τ t := by
  rw [M3Instance.pushLeaves, ← List.ofFn_eq_map, List.sum_ofFn]
  congr 1
  · show (((boundary prog s).filter fun b ↦ decide (b.side = .push)).map fun b ↦ 2 ^ b.κ).sum = _
    simp only [boundary, List.filter_cons, List.filter_nil, decide_true, decide_false,
      reduceCtorEq, ite_true, ite_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      pow_zero]
    omega
  · show ∑ j : Fin 9, ((LeanIsa.flushes j).filter fun f ↦ decide (f.1 = Side.push)).length *
        2 ^ height prog s j = _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h0 : LeanIsa.flushes (0 : Fin 9) = [] := rfl
    have h1 : LeanIsa.flushes (Fin.succ 0 : Fin 9) = [] := rfl
    have h2 : LeanIsa.flushes ((Fin.succ 0).succ : Fin 9) = [] := rfl
    simp only [h0, h1, h2, List.filter_nil, List.length_nil, zero_mul, zero_add]
    rfl

/-! ## The constraint count -/

/-- The instance's constraint counts: `JUMP` (table `7`) has two, the others none. -/
theorem length_constraints : ∀ j : Fin 9,
    (LeanIsa.constraints j).length = if j = opIdx 4 then 2 else 0 := by
  decide +kernel

/-- The sumcheck tables have two constraints, `JUMP`'s. -/
theorem B_leanIsa (prog : LeanIsaProgram) (s : Sizes) :
    (leanIsaInstance prog s).B = 2 := by
  let I := leanIsaInstance prog s
  have hsub : I.B = ∑ j ∈ Finset.univ.filter I.SumcheckTable, (I.constraints j).length :=
    (Finset.sum_subtype _ (by simp) (fun j ↦ (I.constraints j).length)).symm
  have hfil : ∑ j ∈ Finset.univ.filter I.SumcheckTable, (I.constraints j).length =
      ∑ j : Fin 9, (LeanIsa.constraints j).length :=
    Finset.sum_filter_of_ne fun _ _ hj ↦
      Or.inl (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hj))
  rw [show (leanIsaInstance prog s).B = I.B from rfl, hsub, hfil,
    Finset.sum_congr rfl fun j _ ↦ length_constraints j, Finset.sum_ite_eq']
  simp

end
end LeanVM.Protocol.EndToEnd.Sound
