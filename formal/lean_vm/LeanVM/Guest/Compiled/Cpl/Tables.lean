/-
  LeanVM.Guest.Compiled.Cpl.Tables

  The back end's tables of the guest are its placement's: frame sizes, path maxima, the counted
  arms and the decoder's place codes, from the per-function test passing for every entry.
-/

module

public import LeanVM.Guest.Compiled.Cpl.Eval.All
public import LeanVM.Guest.Compiled.Cpl.Placed
public import LeanVM.Compiler.Sound.Pool
public import LeanVM.Guest.Compiled.Places
public import LeanVM.Compiler.Complete.ProgPlace
public import LeanVM.Guest.PlaceCode
public import LeanVM.Guest.Deployed
public meta import LeanVM.Guest.KernelLit

/-!
# The back end's tables, from the per-function test

`CplEval.cplOkAll` decides the per-function test (`cplOkWith`) for every entry; what it compares
with the back end's generated tables (`Deployed.Data`, `Cost.Decoder.guestPlaces`) becomes, for
the guest's world `W0`:

* `fsB_eq`, `fs_eq`: the layout's frame size of each function is `Deployed.Data`'s (`main`'s with
  the jump tables' slots), `Deployed.fs`;
* `pmax_eq`, `arms_eq`: the counts of each placed function are `Deployed.Data.pmax`, and the arms
  of function `Deployed.Data.armFn` counted apart are `Deployed.Data.arms`;
* `places_val`: reading a value through the decoder's place codes (`placeVal`) is the valuation by
  the back end's places (`valP`, `gLocs`), for every value.
-/

namespace LeanVM.Guest.Compiled.Cpl

open LeanVM.Compiler LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core GuestPiece

/-- The guest's jump tables have `Deployed.Data.jtSlots` slots. -/
kernel_rfl slotsG_size_deployed : slotsG.size = Deployed.Data.jtSlots

@[expose] public section

/-- The back end's input has an entry per core function. -/
theorem traced_length : guestTraced.length = coreProgram.length := _root_.LeanVM.Guest.guestTraced_length

/-- **What the per-function test says of entry `i`**, placed. -/
theorem factsG {i : ℕ} (hi : i < coreProgram.length) : CplFacts i (placedG i) := by
  have hi' : i < guestTraced.length := lt_of_lt_of_eq hi traced_length.symm
  obtain ⟨hat, -, -⟩ := guest_placed hi'
  exact cplOkWith_spec (cplOkWith_of hat (CplEval.cplOkAll i (coreProgram_length ▸ hi)))

theorem coreProgram_getElem {i : ℕ} (hi : i < coreProgram.length) :
    coreProgram[i] = coreOf (i + 1) := by
  rw [coreOf_eq (j := i + 1) (by omega) (by have := coreProgram_length_succ; omega)]
  simp only [Nat.add_sub_cancel]

theorem traced_core {i : ℕ} (hi : i < coreProgram.length) :
    (guestTraced.getD i default).core = coreProgram[i] := by
  have hi' : i < guestTraced.length := lt_of_lt_of_eq hi traced_length.symm
  rw [List.getD_eq_getElem _ _ hi', guestTraced_getElem hi', coreProgram_getElem hi]

theorem coreOf_one_main : (coreOf 1).name = "main" := by
  rw [coreOf_one]
  exact core0_main.1

theorem name_main_iff {i : ℕ} (hi : i < coreProgram.length) : coreProgram[i].name = "main" ↔ i = 0 := by
  rw [coreProgram_getElem hi]
  have hn := coreProgram_length_succ
  constructor
  · intro h
    have := coreOf_name_inj (j := i + 1) (j' := 1) (by omega) (by omega) le_rfl (by omega)
      (h.trans coreOf_one_main.symm)
    omega
  · rintro rfl
    exact coreOf_one_main

/-- **The layout's frame sizes are the back end's table's**: `main`'s frame and the jump tables'
slots, another function's frame, at least `2`. -/
theorem fsB_eq {i : ℕ} (hi : i < coreProgram.length) :
    W0.fsB coreProgram[i].name =
      if i = 0 then Deployed.Data.mainCells + Deployed.Data.jtSlots
      else max 2 (Deployed.Data.frameSizes.getD (i + 1) 0) := by
  have hi' : i < guestTraced.length := lt_of_lt_of_eq hi traced_length.symm
  obtain ⟨-, hpa, -⟩ := guest_placed hi'
  have hframe := (factsG hi).sfacts.frame
  rw [← traced_core hi]
  by_cases h0 : i = 0
  · subst h0
    have hm : (guestTraced.getD 0 default).core.name = "main" := by
      rw [traced_core hi]; exact (name_main_iff hi).mpr rfl
    rw [hm, (Complete.fsB_main W0_compiled hpa hm).2, hframe,
      show W0.slots = slotsG from rfl, slotsG_size_deployed]
    rfl
  · have hm : (guestTraced.getD i default).core.name ≠ "main" := by
      rw [traced_core hi]; exact fun h => h0 ((name_main_iff hi).mp h)
    rw [Complete.fsB_fn W0_compiled (tf_mem hi') hpa hm, hframe]
    simp only [fsWant, h0, ↓reduceIte]

/-- **The deployed frame sizes are the layout's** (`Deployed.fs`, the budget's). -/
theorem fs_eq : ∀ i (hi : i < coreProgram.length), Deployed.fs coreProgram[i].name = W0.fsB coreProgram[i].name := by
  intro i hi
  rw [fsB_eq hi, Deployed.fs, Deployed.indexOf?_getElem hi]
  rcases i with _ | i
  · rfl
  · rw [ite_eq_right (show ¬(i + 1 = 0) by omega)]
    rfl

/-- **Each placed function's path maxima are the back end's table's** (`Deployed.Data.pmax`). -/
theorem pmax_eq : ∀ i < coreProgram.length,
    Complete.ofCnt (Complete.pmaxP (keyedOf i) (placedG i)) = Deployed.Data.pmax.getD (i + 1) [] :=
  fun _ hi => (factsG hi).pmax

/-- The entry of function `Deployed.Data.armFn`, whose `match`es count their arms apart. -/
abbrev armIdx : ℕ := Deployed.Data.armFn - 1

theorem led_getD {α : Type} : ∀ (l : List α) (n : ℕ) (d : α), listElementOrDefault l n d = l.getD n d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, n + 1, d => led_getD as n d

/-- **The arms counted apart are the back end's table's** (`Deployed.Data.arms`). -/
theorem arms_eq :
    Complete.armsP true (guestTraced.getD armIdx default) (placedG armIdx) =
      Deployed.Data.arms.getD Deployed.Data.armFn [] := by
  have h := (factsG (i := armIdx) (by rw [coreProgram_length]; decide)).arms
  have hk : keyedOf armIdx = true := by decide
  have ha : armsOf armIdx = Deployed.Data.arms.getD Deployed.Data.armFn [] := by
    rw [armsOf, led_getD, show armIdx + 1 = Deployed.Data.armFn by decide]
  rw [hk, ha] at h
  exact h

/-! ## The places -/

theorem gLocs_eq {i : ℕ} (hi : i < coreProgram.length) :
    gLocs (coreOf (i + 1)).name = (placedG i).locs := by
  have hi' : i < guestTraced.length := lt_of_lt_of_eq hi traced_length.symm
  obtain ⟨-, hpa, -⟩ := guest_placed hi'
  obtain ⟨pf, hfo, hpa'⟩ := Complete.fnOf_of_mem W0_compiled (tf_mem hi')
  obtain ⟨hn, hnd⟩ := Complete.placed_names W0_compiled
  have hnd' : (W0.placed.map (·.fn.name)).Nodup := by rw [hn]; exact hnd
  have he : pf = placedG i := List.inj_on_of_nodup_map hnd' hpa'.1 hpa.1 (hpa'.2.trans hpa.2.symm)
  rw [← coreProgram_getElem hi, ← traced_core hi, gLocs,
    ← locs_of_p (W := W0) (W' := gWorld) (W0_p.trans gWorld_p.symm), (Complete.fnOf_spec hfo).2.2.2, he]

theorem shift_code {n e : ℕ} (hn : n < 1048576) :
    ¬(n + 1048576 * (e + 1) = 0) ∧ ¬(n + 1048576 * (e + 1) < 1048576) ∧
      (n + 1048576 * (e + 1)) % 1048576 = n ∧ (n + 1048576 * (e + 1)) / 1048576 - 1 = e :=
  ⟨by omega, by omega, by omega, by omega⟩

theorem placeWith_code {κ : ℕ} (L : MemoryImage κ) (fp : K) {l : Loc} {c : ℕ}
    (h : codeOf (some l) = some c) : placeWith L.read fp c = locVal L fp l := by
  cases l with
  | cell n =>
    rw [codeOf] at h
    split at h
    · next hn =>
      obtain rfl := Option.some.inj h
      have h0 : ¬((n : ℕ) = 0) := Nat.pos_iff_ne_zero.mp hn.1
      rw [placeWith, ite_eq_right h0, ite_eq_left hn.2]
      rfl
    · cases h
  | shifted n e =>
    rw [codeOf] at h
    split at h
    · next hn =>
      obtain rfl := Option.some.inj h
      have h20 : (2 : ℕ) ^ 20 = 1048576 := rfl
      obtain ⟨h0, hlt, h1, h2⟩ := shift_code (n := n) (e := e) (by rw [← h20]; exact hn)
      rw [placeWith, h20, ite_eq_right h0, ite_eq_right hlt, h1, h2]
      rfl
    · cases h

/-- **Reading through the place codes is the valuation by places**, for every value below the
row, on a function whose places are the codes (`PlacesAre`). -/
theorem placeVal_eq {κ : ℕ} (L : MemoryImage κ) (fp : K) {f : Fn} {locs : VMap Loc} {row : List ℕ}
    (hp : PlacesAre f locs row) (v : V) (hn : v.idx < row.length) :
    placeVal L.read fp row.toArray v = valP L fp locs v := by
  have hkeys := hp.keys v
  unfold placeVal valP
  by_cases hv : (v.path.isEmpty && v.tag == 0) = true
  · rw [ite_eq_left hv]
    obtain ⟨p, t, n⟩ := v
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    change n < row.length at hn
    have hg : row.toArray.getD n 0 = row.getD n 0 := by
      rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_toArray]
    have hc := hp.codes n hn
    rw [hg, List.getD_eq_getElem _ _ hn]
    cases hl : locs[(⟨[], 0, n⟩ : V)]? with
    | none =>
      rw [hl] at hc
      simp only [codeOf, Option.some.injEq] at hc
      rw [← hc]
      rfl
    | some l =>
      rw [hl] at hc
      exact placeWith_code L fp hc
  · rw [ite_eq_right hv]
    cases hl : locs[v]? with
    | none => rfl
    | some l =>
      exfalso
      apply hv
      rw [hkeys l hl]
      rfl

theorem guestPlaces_getD (j : ℕ) :
    Cost.Decoder.guestPlaces.getD j #[] = (Cost.Decoder.guestPlacesList.getD j []).toArray := by
  rw [Cost.Decoder.guestPlaces, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  simp only [Cost.Decoder.guestPlacesLit, List.getElem?_toArray, List.getElem?_map]
  cases Cost.Decoder.guestPlacesList[j]? <;> rfl

theorem row_size (j : ℕ) :
    (Cost.Decoder.guestPlaces.getD j #[]).size = (Cost.Decoder.guestPlacesList.getD j []).length := by
  rw [guestPlaces_getD, List.size_toArray]

theorem core_places {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    ∃ i, j = i + 1 ∧ i < coreProgram.length ∧
      PlacesAre (coreOf j) (gLocs (coreOf j).name) (Cost.Decoder.guestPlacesList.getD j []) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < coreProgram.length := by have := coreProgram_length_succ; omega
  have hp := (factsG hi).places
  rw [traced_core hi, coreProgram_getElem hi] at hp
  rw [gLocs_eq hi]
  exact ⟨i, rfl, hi, hp⟩

/-- **The decoder's place codes are the back end's places**: reading value `v` of function `j`
through its codes is the valuation by `gLocs`, for every value below the row (every value the core
function names, `core_vals`). -/
theorem places_val : ∀ j, 1 ≤ j → j < nFns → ∀ {κ : ℕ} (L : MemoryImage κ) (fp : K) (v : V),
    v.idx < (Cost.Decoder.guestPlaces.getD j #[]).size →
    placeVal L.read fp (Cost.Decoder.guestPlaces.getD j #[]) v = valP L fp (gLocs (coreOf j).name) v := by
  intro j h1 h2 κ L fp v hv
  obtain ⟨-, -, -, hp⟩ := core_places h1 h2
  rw [row_size] at hv
  rw [guestPlaces_getD]
  exact placeVal_eq L fp hp v hv

/-- **Every value a core function names has a place code**: it is `⟨[], 0, k⟩`, `k` below its
row. -/
theorem core_vals : ∀ j, 1 ≤ j → j < nFns → ∀ v ∈ (coreOf j).params ++ Stmt.valsList (coreOf j).body,
    v = ⟨[], 0, v.idx⟩ ∧ v.idx < (Cost.Decoder.guestPlaces.getD j #[]).size := by
  intro j h1 h2 v hv
  obtain ⟨-, -, -, hp⟩ := core_places h1 h2
  rw [row_size]
  exact hp.core v hv

end
end LeanVM.Guest.Compiled.Cpl
