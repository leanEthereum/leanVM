/-
  LeanVM.Guest.B1.Place.LqMem

  A memory built from a run of words, and the words of a leaf's valid trees.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.Memory.Size

/-!
# A memory from words, a leaf's words

* `cellRd S v`: the memory holding `v i` at `g^i` for `i < S`, `0` elsewhere; below `ordG` it
  reads `v i` there (`cellRd_at`), and it is defined everywhere (`cellRd_low`).
* `loadHolds_addr`: a load through `g^b` at offset `k` is the word at `g^(b + k)`;
  `addressOfIndex_ordG`: the indices wrap at `ordG`.
* `leaf_total`: a function whose body is a leaf placing nothing has trees of its frame alone.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The memory holding `v i` at `g^i` for `i < S`, `0` elsewhere. -/
noncomputable def cellRd (S : ℕ) (v : ℕ → E) : Reader := fun A ↦ by
  classical
  exact some (if h : ∃ i, i < S ∧ A = addressOfIndex i then v (Classical.choose h) else 0)

theorem cellRd_at {S : ℕ} (v : ℕ → E) (hS : S ≤ ordG) {i : ℕ} (hi : i < S) :
    cellRd S v (addressOfIndex i) = some (v i) := by
  have hS' : S ≤ 2 ^ 64 - 1 := hS
  unfold cellRd
  simp only [Option.some.injEq]
  split
  · next h =>
    obtain ⟨hj, he⟩ := Classical.choose_spec h
    have : Classical.choose h = i :=
      gpow_injOn (show Classical.choose h < 2 ^ 64 - 1 by omega) (show i < 2 ^ 64 - 1 by omega)
        he.symm
    rw [this]
  · next h => exact absurd ⟨i, hi, rfl⟩ h

theorem cellRd_low (S : ℕ) (v : ℕ → E) (k : ℕ) : LowDef k (cellRd S v) := fun _ _ ↦ by
  simp [cellRd]

/-- **A load through `g^b` at offset `k`** is the word at `g^(b + k)`. -/
theorem loadHolds_addr {rd : Reader} {b k : ℕ} {x : E} :
    LoadHolds rd (ofK (addressOfIndex b)) k x ↔ rd (addressOfIndex (b + k)) = some x := by
  unfold LoadHolds
  rw [Main.addr_ofK]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨(isInK_iff _).mpr ⟨_, rfl⟩, h⟩⟩

/-- **The indices wrap at `ordG`.** -/
theorem addressOfIndex_ordG (c m : ℕ) : addressOfIndex (c + ordG * m) = addressOfIndex c := by
  simp only [addressOfIndex, pow_add, pow_mul]
  have h1 : g ^ ordG = 1 := by
    have := pow_orderOf_eq_one g
    rwa [orderOf_g] at this
  rw [h1, one_pow, mul_one]

/-- `ReadsAt` of a run from `g^b`, word by word. -/
theorem readsAt_of_at {rd : Reader} {b : ℕ} {xs : List E}
    (h : ∀ k < xs.length, rd (addressOfIndex (b + k)) = some (xs.getD k 0)) :
    ReadsAt rd (ofK (addressOfIndex b)) xs := fun k hk ↦ by
  rw [loadHolds_addr, h k hk, List.getD_eq_getElem _ _ hk]

/-- The words of a run from `g^b`, read back. -/
theorem at_of_readsAt {rd : Reader} {b : ℕ} {xs : List E}
    (h : ReadsAt rd (ofK (addressOfIndex b)) xs) {k : ℕ} (hk : k < xs.length) :
    rd (addressOfIndex (b + k)) = some (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk, ← loadHolds_addr]
  exact h k hk

/-! ## A leaf's trees -/

/-- **A leaf placing nothing** has valid trees of its frame alone. -/
theorem leaf_total {fs : String → ℕ} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : Lift.Stmt.leafOkList atomUnplaced fn.body = true) :
    TotalLe coreProgram fs f (fun _ ↦ fs f) := by
  intro rd t args rets hn hv hb
  match t, hv with
  | .node g σ bufs kids, ⟨fn', hf', _, es, vs, hw, _, _, hk⟩ =>
    simp only [Tree.name] at hn
    subst hn
    rw [hf] at hf'
    cases Option.some.inj hf'
    have hall := Lift.walk_leafOk (σ := σ) fn.body hl
    rw [hw] at hall
    have hc := Lift.calls_nil_of_leafOk hall
    rw [hc] at hk
    have hkids : kids = [] := by
      cases kids with
      | nil => rfl
      | cons _ _ => exact hk.elim
    subst hkids
    have hal : allocs σ es = [] := by
      rw [allocs, List.filterMap_eq_nil_iff]
      intro e he
      have := hall e he
      match e, this with
      | .atom a, h =>
        simp only [Lift.EvLeafOk] at h
        cases a with
        | hint x => cases x <;> simp_all [Ev.alloc?, atomUnplaced]
        | _ => rfl
      | .inK _, _ => rfl
    have hb1 := hb.1
    rw [events_node hf hw, hal] at hb1
    subst hb1
    simp [total_node, Tree.totalKids]

end
end LeanVM.Guest.B1
