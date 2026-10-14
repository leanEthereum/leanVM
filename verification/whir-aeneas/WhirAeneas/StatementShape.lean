import Whir.SuccinctRingWeight
import WhirAeneas.ClaimShape

/-! Metadata-level statement check of the source `Statement::check`, and its
relation to the proof model's native shape premises. A region keeps its
offset, variable count and, per claim, the point and the transmitted slices.
The model's flattened family lists claims in region order, then claim order. -/
namespace WhirAeneas.StatementShape
open Whir

structure Region where
  offset : Nat
  vars : Nat
  claims : List (Array Concrete.E × List Concrete.E)

/-- Every claim's point spans the region and carries 64 slices. -/
def Region.Spans (r : Region) : Prop :=
  ∀ c ∈ r.claims, c.1.size = r.vars ∧ c.2.length = 64

/-- The source region guard: the region fits the cube, every claim spans it,
and it is an aligned slice of the occupied prefix. -/
def Region.Valid (logN committed : Nat) (r : Region) : Prop :=
  r.vars ≤ logN ∧ r.Spans ∧ r.vars < 64 ∧ r.offset % 2 ^ r.vars = 0 ∧
    r.offset + 2 ^ r.vars ≤ committed

instance (r : Region) : Decidable r.Spans := by
  unfold Region.Spans; infer_instance

instance (logN committed : Nat) (r : Region) : Decidable (r.Valid logN committed) := by
  unfold Region.Valid; infer_instance

def regionClaims (r : Region) : List RingPCSGame.FamilyClaim :=
  r.claims.map fun c => ⟨r.offset, c.1, fun i => c.2.getD i.val 0⟩

/-- The model's flattened family. -/
def family (rings : List Region) : List RingPCSGame.FamilyClaim :=
  rings.flatMap regionClaims

def familyFn (rings : List Region) : Fin (family rings).length → RingPCSGame.FamilyClaim :=
  fun j => (family rings)[j]

inductive Error where
  | noRingClaim
  | region (index : Nat)
  | pointClaim (index : Nat)
  deriving DecidableEq, Repr

/-- The source check, with errors in source order: no ring claim, then the
first invalid region, then the first ill-formed point claim. -/
def check (logN committed : Nat) (rings : List Region)
    (points : List RingPCSGame.PointClaim) : Except Error Unit :=
  if rings.all (fun r => r.claims.isEmpty) then .error .noRingClaim
  else match rings.findIdx? (fun r => !decide (r.Valid logN committed)) with
    | some index => .error (.region index)
    | none =>
      match points.findIdx? (fun p => !ClaimShape.checkOccupied logN committed p) with
      | some index => .error (.pointClaim index)
      | none => .ok ()

theorem findIdx?_eq_none_iff' {α : Type} (p : α → Bool) (l : List α) :
    l.findIdx? p = none ↔ ∀ x ∈ l, p x = false := by
  rw [List.findIdx?_eq_none_iff]

/-- Exact acceptance of the source check. -/
theorem check_ok_iff (logN committed : Nat) (rings : List Region)
    (points : List RingPCSGame.PointClaim) :
    check logN committed rings points = .ok () ↔
      (∃ r ∈ rings, r.claims ≠ []) ∧ (∀ r ∈ rings, r.Valid logN committed) ∧
        ∀ p ∈ points, ClaimShape.checkOccupied logN committed p = true := by
  unfold check
  split
  · rename_i hempty
    simp only [List.all_eq_true, List.isEmpty_iff] at hempty
    constructor
    · intro h; cases h
    · rintro ⟨⟨r, hr, hne⟩, _⟩
      exact absurd (hempty r hr) hne
  · rename_i hempty
    have hne : ∃ r ∈ rings, r.claims ≠ [] := by
      simp only [List.all_eq_true, List.isEmpty_iff, not_forall] at hempty
      obtain ⟨r, hr, h⟩ := hempty
      exact ⟨r, hr, h⟩
    cases hreg : rings.findIdx? (fun r => !decide (r.Valid logN committed)) with
    | some index =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ hall
      obtain ⟨hlt, hbad, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hreg
      have := hall _ (List.getElem_mem hlt)
      simp [this] at hbad
    | none =>
      have hall := (findIdx?_eq_none_iff' _ rings).mp hreg
      simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hall
      cases hpt : points.findIdx? (fun p => !ClaimShape.checkOccupied logN committed p) with
      | some index =>
        simp only [reduceCtorEq, false_iff, not_and]
        intro _ _ hpts
        obtain ⟨hlt, hbad, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hpt
        have := hpts _ (List.getElem_mem hlt)
        simp [this] at hbad
      | none =>
        have hpts := (findIdx?_eq_none_iff' _ points).mp hpt
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at hpts
        simp only [true_iff]
        exact ⟨hne, hall, hpts⟩

theorem mem_family {rings : List Region} {claim : RingPCSGame.FamilyClaim}
    (h : claim ∈ family rings) :
    ∃ r ∈ rings, ∃ c ∈ r.claims, claim = ⟨r.offset, c.1, fun i => c.2.getD i.val 0⟩ := by
  simp only [family, List.mem_flatMap, regionClaims, List.mem_map] at h
  obtain ⟨r, hr, c, hc, rfl⟩ := h
  exact ⟨r, hr, c, hc, rfl⟩

/-- Valid source regions give the model's family shape. -/
theorem familyShape_of_valid (logN committed : Nat) (rings : List Region)
    (hcomm : committed ≤ 2 ^ logN) (hvalid : ∀ r ∈ rings, r.Valid logN committed) :
    SuccinctRingWeight.FamilyShape logN (familyFn rings) := by
  intro j
  have hmem : (familyFn rings j) ∈ family rings := List.getElem_mem _
  obtain ⟨r, hr, c, hc, heq⟩ := mem_family hmem
  rw [heq]
  obtain ⟨hvars, hspans, _, haligned, hend⟩ := hvalid r hr
  have hsize : c.1.size = r.vars := (hspans c hc).1
  simp only [hsize]
  exact ⟨hvars, haligned, hend.trans hcomm⟩

/-- Source acceptance implies the model's native shape premises for the
flattened family and every point claim, plus a nonempty family. -/
theorem check_ok_model (logN committed : Nat) (rings : List Region)
    (points : List RingPCSGame.PointClaim) (hcomm : committed ≤ 2 ^ logN)
    (h : check logN committed rings points = .ok ()) :
    family rings ≠ [] ∧ SuccinctRingWeight.FamilyShape logN (familyFn rings) ∧
      ∀ p ∈ points, SuccinctPointWeight.Shape logN p := by
  obtain ⟨⟨r, hr, hne⟩, hvalid, hpts⟩ := (check_ok_iff logN committed rings points).mp h
  refine ⟨?_, familyShape_of_valid logN committed rings hcomm hvalid, ?_⟩
  · intro hnil
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    have : (⟨r.offset, c.1, fun i => c.2.getD i.val 0⟩ : RingPCSGame.FamilyClaim) ∈ family rings := by
      simp only [family, List.mem_flatMap, regionClaims, List.mem_map]
      exact ⟨r, hr, c, by simp [hcs], rfl⟩
    simp [hnil] at this
  · intro p hp
    exact ((ClaimShape.checkOccupied_true_iff logN committed p hcomm).mp (hpts p hp)).1

/-- Full-cube converse: every model-shaped statement whose regions each carry
at least one claim, whose claims span their regions with 64 slices, and whose
cube fits a machine word is accepted. -/
theorem check_ok_of_model (logN : Nat) (rings : List Region)
    (points : List RingPCSGame.PointClaim) (hn : logN < 64)
    (hclaims : ∀ r ∈ rings, r.claims ≠ []) (hspans : ∀ r ∈ rings, r.Spans)
    (hnonempty : rings ≠ [])
    (hfamily : SuccinctRingWeight.FamilyShape logN (familyFn rings))
    (hpoints : ∀ p ∈ points, SuccinctPointWeight.Shape logN p) :
    check logN (2 ^ logN) rings points = .ok () := by
  rw [check_ok_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨r, rs, hrs⟩ := List.exists_cons_of_ne_nil hnonempty
    exact ⟨r, by simp [hrs], hclaims r (by simp [hrs])⟩
  · intro r hr
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (hclaims r hr)
    have hc : c ∈ r.claims := by simp [hcs]
    have hmem : (⟨r.offset, c.1, fun i => c.2.getD i.val 0⟩ : RingPCSGame.FamilyClaim) ∈ family rings := by
      simp only [family, List.mem_flatMap, regionClaims, List.mem_map]
      exact ⟨r, hr, c, hc, rfl⟩
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hmem
    have hshape := hfamily ⟨j, hj⟩
    have hsize : c.1.size = r.vars := (hspans r hr c hc).1
    simp only [familyFn, Fin.getElem_fin, hget, hsize] at hshape
    exact ⟨hshape.1, hspans r hr, hshape.1.trans_lt hn, hshape.2.1, hshape.2.2⟩
  · intro p hp
    rw [ClaimShape.checkOccupied_full_cube, SuccinctPointWeight.check_iff]
    exact hpoints p hp

end WhirAeneas.StatementShape
