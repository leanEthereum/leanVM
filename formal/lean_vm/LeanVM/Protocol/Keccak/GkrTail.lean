/-
  LeanVM.Protocol.Keccak.GkrTail

  The end of `verifyKeccak` as a specification: the instance and slot sumchecks on the claim at
  depth `12`, the `64` slices, and the final check.
-/

module

public import LeanVM.Protocol.Keccak.OpenIn

/-!
# The inputs' opening as a specification

`inputTail` is the end of `verify_keccak` (`crates/verifier/src/keccak.rs:279-293`): the instance
rounds, the slot rounds (`keccakOpen` with `first = 0, count = 2`), the `64` slices and the check
`μ̃(λ)·⟨W̃(ρ), s⟩ = value`. `inputSpec`: from doom of "the claim at depth `12` holds of the
committed inputs" to doom of "the `64` slice claims hold at `(λ, r_pack, ρ)`", each of the ten
challenges escaping at `L₀·2/|E|`; the carried predicate `R` rides along.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

@[expose] public section

/-- The end of `verify_keccak`, after the outputs' opening. -/
def inputTail (h : ℕ) (claim : KeccakClaim) (outputs : List ColumnClaim) :
    VerifierProgram (List ColumnClaim × List E × List E) :=
  sumcheck claim.value 3 (List.replicate 4 none) >>= fun y ↦
  keccakOpen h claim 0 keccakSegments y.2 >>= fun x ↦
  VerifierProgram.readScalars kBits >>= fun slices ↦
  VerifierProgram.require (multilinearEval claim.mu y.1 * dot x.2.1 slices = x.2.2) >>= fun _ ↦
  pure (outputs, y.1 ++ claim.point.take (h - 4) ++ x.1, slices)

theorem multilinearEval_mu {mu low : List E} (hmu : mu.length = 16) (hlow : low.length = 4) :
    multilinearEval mu low = MuT mu low := by
  rw [multilinearEval_eq low mu (by rw [hmu, hlow]; rfl), MuT, hlow]

/-- **The final check**: with true slices, the check gives the slot rounds' last claim. -/
theorem final_in (P : ℕ) (col : ℕ → K) (claim : KeccakClaim) (hshape : ClaimShape P claim)
    {low slot slices : List E} (hlow : low.length = 4) (hslot : slot.length = 6) (value : E)
    (hs : slicesTrue (P + 4) col (low ++ claim.point.take P ++ slot) slices)
    (hc : multilinearEval claim.mu low *
      dot ((foldAll slot (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD []) slices =
        value) :
    value = Fs P col claim low slot := by
  have ha : (low ++ claim.point.take P).length = P + 4 := by
    simp [hlow, hshape.2.1]; omega
  rw [← hc, Fs, cubeSum_full _ hslot, multilinearEval_mu hshape.1 hlow,
    dot_eq _ _ (by rw [fold_in_length P claim hslot, hs.2.1]), fold_in_length P claim hslot]
  refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun z hz ↦ ?_)
  have hz' := Finset.mem_range.1 hz
  rw [fold_in P claim hslot hz', hs.2.2 z hz', ← slices_eq P col ha hslot z]

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

open Classical in
/-- **The inputs' opening.** Lead `0`; the ten sumcheck challenges' groups `L₀·2/|E|`, the
follower's lead `T` after the slices. -/
noncomputable def inputSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (qk : β → ℕ → K) (P : ℕ) (claim : KeccakClaim) (hshape : ClaimShape P claim)
    (outs : List ColumnClaim) (hT : T ≤ εmax) (h2 : (L₀ : ℝ≥0∞) * errE 2 ≤ εmax) :
    Spec (inputTail (P + 4) claim outs)
      (Doomed C (fun q ↦ ClaimTrue (statesAt (P + 4) (qk q) 12) P claim ∧ R q))
      (fun res h ↦ res.1 = outs ∧
        Doomed C (fun q ↦ slicesTrue (P + 4) (qk q) res.2.1 res.2.2 ∧ R q) h) εmax 0 T :=
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  have he : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by rw [add_zero]; exact h2
  ((sumcheckSpec (T := 0) hst hcard R (Fl_plainFamily P qk claim) (count := 3) (by norm_num)
    (by norm_num) h0 he 4 [] claim.value (by simp)).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨by rw [ClaimTrue, ← Fl_nil, hv], hR⟩)
    (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun y ↦
  if hy : y.1.length = 4 then
    (Spec.congr (keccakOpen_eq (P + 4) claim 0 keccakSegments y.2).symm <|
      Spec.congr (p := sumcheck y.2 3 (List.replicate 6 none) >>= fun x ↦
        VerifierProgram.ret (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) claim 0
            keccakSegments)).headD [],
          x.2)) (by rw [qkeccakSlotBits_eq]) <|
      ((sumcheckSpec (T := 0) hst hcard R (Fs_plainFamily P qk claim y.1) (count := 3)
        (by norm_num) (by norm_num) h0 he 6 [] y.2 (by simp)).mono
        (fun _ (hd : y.1.length = 4 ∧ Doomed C _ _) ↦ Doomed.mono hd.2 fun q ⟨hv, hR⟩ ↦ ⟨by
          rw [List.nil_append, Fl, cubeSum_full _ hy, hv, Fs_nil P (qk q) claim hshape hy], hR⟩)
        (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl).bind' fun x ↦
      (Spec.ret (Post := fun (x' : List E × List E × E) h ↦ x'.1.length = 6 ∧
          x'.2.1 = (foldAll x'.1 (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD [] ∧
          Doomed C (fun q ↦ x'.2.2 = Fs P (qk q) claim y.1 x'.1 ∧ R q) h)
        (x.1, (foldAll x.1 (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD [], x.2)).mono
        (fun _ hd ↦ ⟨hd.1, rfl, by simpa using hd.2⟩) (fun _ _ h' ↦ h') le_rfl le_rfl
        le_rfl).bind' fun x ↦
    if hx : x.1.length = 6 ∧
        x.2.1 = (foldAll x.1 (keccakSlotWeights (P + 4) claim 0 keccakSegments)).headD [] then
      ((doomReadN (T := T) hst _ hT 63).mono (fun _ hd ↦ hd.2.2) (fun _ _ h' ↦ h') le_rfl
        le_rfl le_rfl).bind' fun slices ↦
      (Spec.require
        (Pre := fun h ↦ slices.length = 63 + 1 ∧
          Doomed C (fun q ↦ x.2.2 = Fs P (qk q) claim y.1 x.1 ∧ R q) h)
        (Post := fun _ h ↦ Doomed C (fun q ↦
          slicesTrue (P + 4) (qk q) (y.1 ++ claim.point.take (P + 4 - 4) ++ x.1) slices ∧ R q) h)
        fun _ hd hc ↦ Doomed.mono hd.2 fun q ⟨hs, hR⟩ ↦ ⟨by
          rw [show P + 4 - 4 = P by omega] at hs
          rw [hx.2] at hc
          exact final_in P (qk q) claim hshape hy hx.1 _ hs hc, hR⟩).bind' fun _ ↦
      (Spec.ret (outs, y.1 ++ claim.point.take (P + 4 - 4) ++ x.1, slices)).mono
        (fun _ hd ↦ ⟨rfl, hd⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hx ⟨hd.1, hd.2.1⟩) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hy hd.1) (fun _ _ h' ↦ h') le_rfl le_rfl le_rfl

end
end LeanVM.Protocol.KeccakGkr
