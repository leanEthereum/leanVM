/-
  LeanVM.Guest.B1.Merkle.CapLinks

  The deployed `verify_merkle_cap` specializations are their reference function, and so their
  meaning, in any program that finds them.
-/

module

public import LeanVM.Guest.B1.Merkle.CapRef
public import LeanVM.Guest.Pack.P4.Core
public import LeanVM.Guest.Pack.P6.Core
public import LeanVM.Guest.Pack.P11.Core
public import LeanVM.Guest.Pack.P23.Core
public import LeanVM.Guest.Pack.P42.Core
public import LeanVM.Guest.Pack.P56.Core
public import LeanVM.Guest.Pack.P61.Core

/-!
# `verify_merkle_cap__L2 .. L8`, linked

`capSpecs_linked` is one kernel evaluation of the link check (`LeanVM.Guest.Ref.Link`) per
deployed depth; with `capRef_sem` it gives `verify_merkle_cap_SpecP` in every program that finds
the functions.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Ref

@[expose] public section

/-- The deployed specializations: name, core function, cap depth. -/
noncomputable def capSpecs : List (String × Fn × ℕ) :=
  [("verify_merkle_cap__L2", Fn.«verify_merkle_cap__L2».core, 2),
    ("verify_merkle_cap__L3", Fn.«verify_merkle_cap__L3».core, 3),
    ("verify_merkle_cap__L4", Fn.«verify_merkle_cap__L4».core, 4),
    ("verify_merkle_cap__L5", Fn.«verify_merkle_cap__L5».core, 5),
    ("verify_merkle_cap__L6", Fn.«verify_merkle_cap__L6».core, 6),
    ("verify_merkle_cap__L7", Fn.«verify_merkle_cap__L7».core, 7),
    ("verify_merkle_cap__L8", Fn.«verify_merkle_cap__L8».core, 8)]

/-- Every deployed specialization is linked to the reference function at its depth. -/
theorem capSpecs_linked : (capSpecs.all fun s ↦ Linked s.2.1 (capRef s.2.2)) = true := by
  decide +kernel

/-- **`verify_merkle_cap`'s functions are their meaning**, at the deployed cap depths, in every
program that finds them. -/
theorem verify_merkle_cap_of_linked (P : Program)
    (hfind : ∀ s ∈ capSpecs, P.find? s.1 = some s.2.1) : verify_merkle_cap_SpecP P := by
  intro p hp rd args rets
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (show p ∈ capSpecs.map fun s ↦ (s.1, s.2.2) from hp)
  rw [rel_iff_sem (hfind s hs)]
  exact (Linked.sem_iff (List.all_eq_true.mp capSpecs_linked s hs) args rets).trans
    (capRef_sem _ rd args rets)

end
end LeanVM.Guest.B1
