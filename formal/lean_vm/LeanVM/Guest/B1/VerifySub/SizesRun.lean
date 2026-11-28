/-
  LeanVM.Guest.B1.VerifySub.SizesRun

  `readAnnouncedSizes` on the carried sponge, from what its checks need of the eight words.
-/

module

public import LeanVM.Guest.B1.VerifySub.Phases

/-!
# The announced sizes' run

`runsTo_readAnnouncedSizes`: eight words whose high limbs are zero, the memory's log, the rows and
the rate exponent read off their low limbs (`vsLogMem`'s and `vsRows`' reading), a rate exponent
in `1 .. 4`, and a layout `buildLayout` returns for them with a stack of `16 .. 30` variables run
`readAnnouncedSizes` to that layout and rate, absorbing the words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem runsTo_require' {c : Prop} [Decidable c] (h : c) (s : Fs) :
    RunsTo (VerifierProgram.require c) s [] () s := by
  unfold VerifierProgram.require
  rw [ite_eq_left (by simp [h])]
  exact runsTo_ret () s

/-- **The announced sizes run.** -/
theorem runsTo_readAnnouncedSizes (bytecode : List K) (s : Fs) (xs : List E)
    (hlen : xs.length = 2 + nTables) (hhi : ∀ x ∈ xs, x.limb 1 = 0) {layout : Layout}
    (hb : buildLayout bytecode (kToNat ((xs.headD 0).limb 0))
      (((xs.drop 1).take nTables).map fun v ↦ kToNat (v.limb 0)) = some layout)
    (hl1 : 1 ≤ kToNat ((xs.getLastD 0).limb 0)) (hl4 : kToNat ((xs.getLastD 0).limb 0) ≤ 4)
    (hs1 : Whir.minLogStack ≤ layout.stackLog) (hs2 : layout.stackLog ≤ Whir.maxLogStack) :
    RunsTo (readAnnouncedSizes bytecode) s xs (layout, kToNat ((xs.getLastD 0).limb 0))
      (s.absorbAll xs dsObserve) := by
  have hr := runsTo_readN s xs
  rw [hlen] at hr
  unfold readAnnouncedSizes
  refine RunsTo.of_eq (hr.bind ((runsTo_require' (List.all_eq_true.mpr fun x hx ↦
    decide_eq_true (hhi x hx)) _).bind ((runsTo_require' ⟨hl1, hl4⟩ _).bind
      ((runsTo_liftOption' hb _).bind ((runsTo_require' ⟨hs1, hs2⟩ _).bind
        (runsTo_ret _ _)))))) rfl (by simp) rfl rfl
where
  runsTo_liftOption' {α : Type} {o : Option α} {a : α} (h : o = some a) (s : Fs) :
      RunsTo (liftOption o) s [] a s := by
    rw [h]; exact runsTo_ret a s

end
end LeanVM.Guest.B1.VerifySub
