/-
  LeanVM.Guest.B1.Sig.SpWotsGroupComplete

  A digit group of `sp_wots` completes: its digit word `g^k` hinted, its range check on a memory of
  at least `64` words, the padding run the first group sets, its dispatch taking arm `k`, whose
  chains' starts are loaded.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsStepComplete
public import LeanVM.Guest.B1.Sig.SpWotsArms
public import LeanVM.Guest.B1.Sig.SpWotsCheck
public import LeanVM.Guest.B1.Sig.CodewordComplete

/-!
# A group, complete

A group of `sp_wots` is the shared group over `spW` (`groupD`), so it completes by the shared
`groupD_load`, its chain step in single-assignment form above `26` and reading `SpGood spPad`
(`spWp_shape`, `spWp_stable`).

* `SpArmPost`: arm `k`'s starts holding `vals`;
* `spGroupT_complete`: a group from base `B` completes on `B ..< end`, from any valuation where
  the padding run holds after what the group sets (`spPre`): its digit word `g^k` at `B`, `SpArmPost`;
* `spGroupP_complete`, `spGroupP_nb`: group `p` of the body.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- What arm `k` of the group from `B` leaves: its starts holding `vals`. -/
def SpArmPost (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) (vals : Nat → E)
    (σ : Val) : Prop :=
  ∀ t < n, σ (spStartOf first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k) t) = vals t

theorem padRun_seq (P : Nat) : SeqOK P (padRun P) (P + 5) := by
  simp [padRun, List.range_succ, SeqOK, ASeq, cst]

theorem spPre_seq (fold : Bool) (B : Nat) : SeqOK (B + 5) (spPre fold B) (spL fold B + 5) := by
  cases fold
  · rfl
  · exact padRun_seq (B + 5)

theorem spL_ge (fold : Bool) (B : Nat) : B ≤ spL fold B := by
  unfold spL; split <;> omega

theorem spW_shape {Bs : Nat} (h : 26 ≤ Bs) : StepShape spW Bs :=
  StepShape.mono (spWp_shape (b := spPad) (B := 26) (by simp [spPad]) (by norm_num)) h

theorem spW_stable {Bs : Nat} (h : 26 ≤ Bs) : GoodStable Bs (SpGood spPad) :=
  (spWp_stable (b := spPad) (B := 26) (by simp [spPad])).mono h

theorem spW_power_nb {Bs k n : Nat} (h : 26 ≤ Bs) (hn : n ≤ 3) : NBv Bs (spW.power (digitSum k n)) :=
  ⟨6 + digitSum k n, by have := digitSum_le_nine k n hn; omega, rfl⟩

/-- **A group completes**, its digit word `g^k` loaded at its base, its chain step above `Bs`. -/
theorem spGroupT_complete {first n : Nat} {fold : Bool} {B : Nat} {prodIn encIn : V} {k Bs : Nat}
    (hn : n ≤ 3) (hk : k < 4 ^ n) (hm : MemOK rd 64) (hBs : 26 ≤ Bs) (hB : Bs ≤ spL fold B + 5)
    (hpi : NBv Bs prodIn) (hei : NBv Bs encIn) (vals : Nat → E) (σ : Val) (hg : ∀ σ', AgreeBelow B σ σ' → AtomsHold rd σ' (spPre fold B) → SpGood spPad σ') :
    Completes C rd B (spGroupT first n fold prodIn encIn B).2 (spGroupT first n fold prodIn encIn B).1 σ
      (fun σ' => σ' (.n B) = ofK (addressOfIndex k) ∧ SpArmPost first n fold B prodIn encIn k vals σ' ∧
        SpGood spPad σ') :=
  (groupD_load (C := C) (rd := rd) (spW_shape hBs) (spW_stable hBs) hn hk hm (spL_ge fold B) hB
    (spPre_seq fold B) hpi hei (spW_power_nb hBs hn) vals σ hg).mono le_rfl le_rfl
    (fun _ h => ⟨h.1, h.2.1, h.2.2⟩)

theorem spArmB_ge (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) :
    spL fold B + 6 ≤ spArmB first n fold B prodIn encIn k := by
  rw [spArmB, ← armB_zero spW first n fold prodIn encIn (spL fold B)]
  exact armB_mono spW first n fold prodIn encIn (spL fold B) (Nat.zero_le _)

/-- A group's encoding (and product) lie below its end. -/
theorem spEnc_lt_end (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) :
    spEnc fold n B < spArmB first n fold B prodIn encIn (4 ^ n) := by
  have h1 := armB_one spW first n fold prodIn encIn (spL fold B)
  have h2 := armB_mono spW first n fold prodIn encIn (spL fold B)
    (Nat.one_le_pow n 4 (by norm_num))
  rw [spArmB]
  unfold spEnc spProd
  omega

/-- A group's tips and starts lie in its arms' range. -/
theorem spPost_bounds (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) {k t : Nat}
    (hk : k < 4 ^ n) (ht : t < n) :
    (spL fold B + 6 ≤ spSlot fold B t 2 ∧ spSlot fold B t 2 < spArmB first n fold B prodIn encIn (4 ^ n)) ∧
      ∃ j, spStartOf first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k) t = .n j ∧
        spL fold B + 6 ≤ j ∧ j < spArmB first n fold B prodIn encIn (4 ^ n) := by
  obtain ⟨j, ej, h1, h2, -⟩ := grpPos_spec spW first n fold prodIn encIn (spL fold B) k t hk ht
  refine ⟨?_, j, ej, h1, h2⟩
  have hs := slot_bounds spW fold (spL fold B) t 2 (by norm_num)
  have hc : groupStart fold (spL fold B) + chainStride spW * (t + 1) ≤
      groupStart fold (spL fold B) + chainStride spW * n :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _
  have he := spEnc_lt_end first n fold B prodIn encIn
  have hgs : spL fold B + 6 ≤ groupStart fold (spL fold B) := by rw [groupStart_eq]; split <;> omega
  unfold spEnc spProd at he
  exact ⟨by unfold spSlot; omega, by unfold spSlot; omega⟩

theorem spGroupT_nb {first n : Nat} {fold : Bool} {B : Nat} {prodIn encIn : V} (hn : n ≤ 3)
    (hB : 20 ≤ spL fold B) (hpi : NBv (spL fold B + 6) prodIn) (hei : NBv (spL fold B + 6) encIn) :
    NumBelow (spGroupT first n fold prodIn encIn B).2 (Stmt.valsList (spGroupT first n fold prodIn encIn B).1) :=
  groupD_numBelow (spW_shape (Bs := spL fold B + 6) (by omega)) le_rfl
    (spL_ge fold B) ((spPre_seq fold B).numBelow.mono (by omega)) hpi hei
    (fun k _ => spW_power_nb (by omega) hn)

end
end LeanVM.Guest.B1.Sig
