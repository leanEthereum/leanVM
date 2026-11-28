/-
  LeanVM.Guest.B1.VsC.KLSpec

  `keccak_layer`'s template, checked: its counter, its stores, and the loads that are not stores
  (the archive's `LayerCSpec`, `StoreFacts`, `LayerCG1`).
-/

module

public import LeanVM.Guest.B1.VsC.KLTail
public import LeanVM.Guest.B1.VsC.KLRmfe
public import LeanVM.Guest.B1.VsC.Fwd
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# A layer's template, checked

The checker accepts the two specializations (`layer_chk`), whose stores are `layerSt`
(`layer_stores`): the next claim's instance weights and `κ` at `out`, the local point, the next
claim's value, point, local point, lanes and flips. No store goes through the cursor, the claim or
the cursor after the pack rounds (`layer_noStore`); the loads of the lane weights, the weight
section, the slices' weights, the top coordinate and the flips are not stores, and the flips'
writes are (`layer_residOk`). `layerT_sections`: the body as the sections the completeness lemmas
take.
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## Stores -/

/-- No store goes through the pointers `ps`. -/
def noStoreVia (ps : List V) (S : List Atom) : Bool := S.all fun a ↦ match a with
  | .load _ p _ => !ps.contains p
  | _ => true

theorem not_mem_of_noStoreVia {ps : List V} {S : List Atom} (h : noStoreVia ps S = true) {p : V}
    (hp : p ∈ ps) (d : V) (off : ℕ) : Atom.load d p off ∉ S := by
  intro hm
  have h' := List.all_eq_true.mp h _ hm
  simp only at h'
  rw [List.contains_iff_mem.mpr hp] at h'
  exact absurd h' (by decide)

/-- None of the atoms `as` is a store. -/
def noneIn (as S : List Atom) : Bool := as.all fun a ↦ !S.contains a

theorem not_mem_of_noneIn {as S : List Atom} (h : noneIn as S = true) : ∀ a ∈ as, a ∉ S := by
  intro a ha hm
  have h' := List.all_eq_true.mp h a ha
  rw [List.contains_iff_mem.mpr hm] at h'
  exact absurd h' (by decide)

/-- The stores of `layerT first`: the next claim's instance weights and `κ`, the local point, the
next claim's value, point, local point, lanes and flips. -/
def layerSt (first : ℕ) : List Atom :=
  (List.range 16).map (fun i ↦ .load (.n (preOff first + rmfeStores.getD i 0)) (.n (valf% «keccak_layer» "out")) (6 + i)) ++
  [.load (.n (preOff first + 688)) (.n (valf% «keccak_layer» "out")) 1] ++
  (List.range 11).map (fun i ↦ .load (.n (layOff first + 821 + 32 * i)) (.n (layOff first + 809)) i) ++
  [.load (.n (tW first + 24)) (.n (valf% «keccak_layer» "out")) 0,
    .load (.n (layOff first + 781)) (.n (valf% «keccak_layer» "out")) 2,
    .load (.n (layOff first + 809)) (.n (valf% «keccak_layer» "out")) 4] ++
  (List.range 25).map (fun i ↦ .load (.n (tW first + 29 + 4 * i)) (.n (tW first + 25)) i) ++
  [.load (.n (tW first + 25)) (.n (valf% «keccak_layer» "out")) 3] ++
  (List.range 7).map (fun i ↦ .load (.n (topV (tW first) + 46 + 43 * i)) (.n (topV (tW first) + 3)) i) ++
  [.load (.n (topV (tW first) + 3)) (.n (valf% «keccak_layer» "out")) 5]

set_option maxRecDepth 100000 in
theorem layer_chk {first : ℕ} (hf : first < 2) : (chk 15 (layerT first)).isSome = true := by
  interval_cases first <;> decide +kernel

set_option maxRecDepth 100000 in
theorem layer_stores {first : ℕ} (hf : first < 2) : storesOf 15 (layerT first) = layerSt first := by
  interval_cases first <;> decide +kernel

/-- The stores load into none of the inlined `grind_check`'s values. -/
theorem layerSt_noGrind {first : ℕ} (hf : first < 2) :
    ∀ a ∈ layerSt first, loadInto (preOff first + 544) (preOff first + 544 + (gcLen 3 - 2)) a = false := by
  have h : (layerSt first).all
      (fun a ↦ !loadInto (preOff first + 544) (preOff first + 544 + (gcLen 3 - 2)) a) = true := by
    interval_cases first <;> decide +kernel
  intro a ha
  simpa using List.all_eq_true.mp h a ha

/-! ## Sections -/

/-- The position rounds. -/
def localS (o : ℕ) : List Stmt :=
  localRoundsT (.n (o + 802)) (.n (o + 809)) (.n (o + 803)) (cap5 (o + 804)) (o + 810) 11

theorem layerT_sections (first : ℕ) : layerT first =
    secA1 first ++ (secA2 first ++ (rmfeBlockT (preOff first) ++ (hornerS first ++
      (packT (preOff first) ++ (localS (layOff first) ++
        (tReadsT (layOff first) ++ (eqfS (layOff first) ++ (weightT first (layOff first) ++
          tailT (layOff first) (tW first) (tV first))))))))) := by
  simp only [layerT, secA1, secA2, hornerS, localS, eqfS, tW, tV, List.append_assoc]

theorem layer_noStore {first : ℕ} (hf : first < 2) :
    noStoreVia [.n (valf% «keccak_layer» "cursor@1"), .n (valf% «keccak_layer» "claim"),
      .n (layOff first + 802)] (layerSt first) = true := by
  interval_cases first <;> decide +kernel

theorem layer_residOk {first : ℕ} (hf : first < 2) :
    noneIn (resid (atomsL (eqfS (layOff first)))) (layerSt first) = true ∧
    noneIn (resid (atomsL (weightT first (layOff first)))) (layerSt first) = true ∧
    noneIn (resid (atomsL (tailEqf (layOff first) (tW first)))) (layerSt first) = true ∧
    noneIn [.load (.n (topV (tW first))) (.n (layOff first + 809)) 5] (layerSt first) = true ∧
    (∀ i < 7, noneIn (resid (atomsL (layerFlipT (tW first) i))) (layerSt first) = true) ∧
    (∀ i < 7, (layerSt first).contains (.load (.n (flipB (tW first) i + 42))
      (.n (topV (tW first) + 3)) i) = true) := by
  interval_cases first
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-! ## The honest valuation -/

/-- **A layer's valuation on a memory**: `layerT first` evaluated forward from the arguments, the
hints' and the dispatches' words from `w`. -/
noncomputable def layerσ (rd : Reader) (w : ℕ → E) (args : List E) (first : ℕ) : Val :=
  VsC.fwdVal rd w args (layerT first)

section
variable {rd : Reader} {w : ℕ → E} {args : List E} {first : ℕ}

set_option maxHeartbeats 1000000 in
theorem layer_good (hf : first < 2) (hl : args.length = 15) :
    ∀ s ∈ layerT first, GoodS rd (layerSt first) w (layerσ rd w args first) s := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (layer_chk hf)
  have h := (ev_spec rd w (layerT first) args (by rw [hl]; exact hc')).2.2
  rw [hl, layer_stores hf] at h
  exact h

set_option maxHeartbeats 1000000 in
theorem layer_param (hf : first < 2) (hl : args.length = 15) {i : ℕ}
    (hi : i < 15) : layerσ rd w args first (.n i) = args.getD i 0 := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (layer_chk hf)
  exact ev_params rd w (by rw [hl]; exact hc') (by rw [hl]; exact hi)

theorem layerσ_idx (v : V) : layerσ rd w args first v = layerσ rd w args first (.n v.idx) := by
  unfold layerσ VsC.fwdVal B1.Val.ofArgs; rfl

end

end
end LeanVM.Guest.B1.VerifySub.KL
