/-
  LeanVM.Guest.EndExecYDeployed

  The witness streams' track on the deployed alignment: `hintWitness`, `KeepY` and `InitY` for
  `YCur alignA`.
-/

module

public import LeanVM.Guest.EndExecYKeep
public import LeanVM.Guest.EndExecYWit
public import LeanVM.Guest.EndExecYAl
public import LeanVM.Guest.EndExecJumpCells

/-!
# The witness streams' track on the deployed alignment

`hintWitness_alignA`: `ExecGaps.ofX`'s `hintWitness` for any `Y` implying `YCur alignA`, given the
witness atoms' destination cells (`WitCells`) and the honest pushes' independence of the bytecode
but its length (`PushShape`). `keepY_alignA`: each step keeps `YCur alignA`, given the `DEREF`
pointers (`DerefPow`). `InitY (YCur alignA)` is `initY_cur`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

public section

/-- **Each witness hint pops the next entry of its stream, the reference's words at its
destination**, on the deployed alignment. -/
theorem hintWitness_alignA (hW : WitCells alignA) (hSh : PushShape) {Y : Ref → St → Prop}
    (hY : ∀ r s, Y r s → YCur alignA r s) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isWitnessHint h = true → Mode.HintIn s1 h → HintOk C (refMem r.img) s1 h :=
  hintWitness_cur progAl advAl_alignA hW hSh hY

/-- **Each step keeps the witness streams' track**, on the deployed alignment. -/
theorem keepY_alignA {Y : Ref → St → Prop} (hD : DerefPow Y)
    (hY : ∀ r s, Y r s → YCur alignA r s) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op s1 s', OnRun (XOf Y) r s →
      C.ops[s.pc]? = some op → ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → runOp C s1 op = .ok s' → YCur alignA r { s' with steps := s'.steps + 1 } :=
  keepY_cur progAl alignA_main jumpCells_at alLayout_alignA advAl_alignA hD hY

end

end LeanVM.Guest.EndExec
