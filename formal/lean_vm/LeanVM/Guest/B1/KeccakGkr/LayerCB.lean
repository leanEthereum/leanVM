/-
  LeanVM.Guest.B1.KeccakGkr.LayerCB

  `keccak_layer`'s instance weights and Horner sections, completely.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerSecB
public import LeanVM.Guest.B1.KeccakGkr.LayerCA

/-!
# The instance weights and the product at `s`, completely

* `rmfe_vals`: on an evaluated valuation the values the block stores are the instance weights at
  `s` and their sum (the block's masks, `maskRun` on its statements but the loads);
  `rmfe_complete`: with those words in the next claim's record, the block holds.
* `horner_complete`: the Horner chain holds by its equations.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- A load statement. -/
def loadB : Stmt → Bool
  | .atom (.load ..) => true
  | _ => false

/-- The block but its stores. -/
def rmfePure : List Stmt := rmfeBlockT.filter fun s ↦ !loadB s

/-- The block's masks, checked on its statements but the loads. -/
def rmfeCheckP : Bool :=
  match maskRun (.n 877) [(.n 877, 2)] rmfePure with
  | some st => (List.range 16).all (fun i ↦ st.lookup (.n (rmfeStores.getD i 0)) ==
      some (embedLit.getD i 0)) && st.lookup (.n 958) == some embedXor
  | none => false

theorem rmfeCheckP_true : rmfeCheckP = true := by decide +kernel

theorem rmfePure_kernel : rmfePure.all isAtom = true ∧ canonChk [] (atomsL ([] ++ rmfePure)) = true ∧
    resid (atomsL rmfePure) = [] := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem rmfe_kernel : rmfeBlockT.all isAtom = true ∧ canonChk [] (atomsL ([] ++ rmfeBlockT)) = true ∧
    resid (atomsL rmfeBlockT) =
      (List.range 16).map (fun i ↦ .load (.n (rmfeStores.getD i 0)) (.n 12) (6 + i)) ++
        [.load (.n 958) (.n 12) 1] := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The values the block stores**: the instance weights at `s`, and their sum. -/
theorem rmfe_vals (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ s ∈ rmfeBlockT, GoodS rd S w σ s) :
    (∀ i < 16, σ (.n (rmfeStores.getD i 0)) = (keccakInstanceWeights (σ (.n 877))).getD i 0) ∧
      σ (.n 958) = sumE (keccakInstanceWeights (σ (.n 877))) := by
  obtain ⟨hall, hk, hr⟩ := rmfePure_kernel
  have h : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ rmfePure True (fun _ ↦ True) :=
    block_holdsP (P := []) hall hσ hk (fun s hs ↦ by
      have h' : s ∈ rmfePure := by simpa using hs
      exact hg s (List.mem_filter.mp h').1)
      (A := []) (by simp) (by rw [hr]; simp) trivial
  have hc := rmfeCheckP_true
  unfold rmfeCheckP at hc
  split at hc
  · rename_i st hst
    have hok0 : MaskOk σ (σ (.n 877)) [(.n 877, 2)] := by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact (pe_two _).symm
    obtain ⟨hok, -⟩ := maskRun_sound hst hok0 h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
    obtain ⟨hst16, hk⟩ := hc
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · rw [hok.lookup (hst16 i hi), ← keccakInstanceWeights_getD_pe _ hi]
    · rw [hok.lookup hk, ← sumE_keccakInstanceWeights]
  · cases hc

/-- **The instance weights, completely**: with the weights at `s` and their sum in the next
claim's record, the block holds. -/
theorem rmfe_complete (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ s ∈ rmfeBlockT, GoodS rd S w σ s)
    (hmu : ∀ i < 16, LoadHolds rd (σ (.n 12)) (6 + i)
      ((keccakInstanceWeights (σ (.n 877))).getD i 0))
    (hkap : LoadHolds rd (σ (.n 12)) 1 (sumE (keccakInstanceWeights (σ (.n 877))))) :
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ rmfeBlockT next kret := by
  obtain ⟨hall, hk, hr⟩ := rmfe_kernel
  obtain ⟨hv, hv958⟩ := rmfe_vals hσ hg
  refine block_holdsP (P := []) hall hσ hk (by simpa using hg) (A := []) (by simp) ?_
  rw [hr]
  intro a ha
  left
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    have hi' := List.mem_range.mp hi
    show LoadHolds rd _ _ _
    rw [hv i hi']; exact hmu i hi'
  · rw [List.mem_singleton] at ha
    subst ha
    show LoadHolds rd _ _ _
    rw [hv958]; exact hkap

/-- The Horner section of a specialization. -/
def hornerS (first : ℕ) : List Stmt := hornerT (fun k ↦ ((prodTab first).getD k default).a) 877 959

theorem horner_kernel {first : ℕ} (hf : first < 2) :
    (hornerS first).all isAtom = true ∧ canonChk [] (atomsL ([] ++ hornerS first)) = true ∧
      resid (atomsL (hornerS first)) = [] := by
  interval_cases first
  · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The product at `s`, completely**: the chain holds by its equations. -/
theorem horner_complete {first : ℕ} (hf : first < 2) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ hornerS first, GoodS rd S w σ s) :
    ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ (hornerS first) next kret := by
  obtain ⟨hall, hk, hr⟩ := horner_kernel hf
  exact block_holdsP (P := []) hall hσ hk (by simpa using hg) (A := []) (by simp) (by rw [hr]; simp)

end
end LeanVM.Guest.B1.VerifySub
