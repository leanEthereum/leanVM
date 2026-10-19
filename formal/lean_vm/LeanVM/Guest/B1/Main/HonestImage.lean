/-
  LeanVM.Guest.B1.Main.HonestImage

  A memory image holding a consistent layout and `main`'s header, and the parts of the honest
  discharge (`DischargeHyps`) a placed tree of `main` valid on it gives.
-/

module

public import LeanVM.Guest.B1.Main.HonestAll
public import LeanVM.Guest.Memory.Discharge

/-!
# The memory image

`LConsistent L`: two entries of `L` covering one word give it the same value. `imageOf κ L hdr`
holds `hdr` at words `0`, `1` and each entry's words elsewhere (`memL_imageOf`, `imageOf_hdr`),
when the entries lie in `[2, 2^κ)`. On it, a tree of `main` placed at `0` by `RelAtIn` with the
header as its region gives `DischargeHyps`' memory-side fields (`dischargeMem`); the address
field follows from validity (`Tree.Valid.eqns_read`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **A consistent layout**: two entries covering one word give it the same value. -/
def LConsistent (L : Layout) : Prop :=
  ∀ q ∈ L, ∀ q' ∈ L, ∀ i, q.1 ≤ i → i < q.1 + q.2.length → q'.1 ≤ i → i < q'.1 + q'.2.length →
    q.2.getD (i - q.1) 0 = q'.2.getD (i - q'.1) 0

open Classical in
/-- **The image of a layout**: `hdr` at words `0` and `1`, an entry's word where one covers. -/
noncomputable def imageOf (κ : ℕ) (L : Layout) (hdr : E × E) : MemImage κ := fun i =>
  if (i : ℕ) = 0 then hdr.1 else if (i : ℕ) = 1 then hdr.2 else
    match L.find? (fun q => decide (q.1 ≤ (i : ℕ) ∧ (i : ℕ) < q.1 + q.2.length)) with
    | some q => q.2.getD ((i : ℕ) - q.1) 0
    | none => 0

theorem imageOf_hdr {κ : ℕ} (hκ : κ < 64) (h1 : 1 ≤ κ) (L : Layout) (hdr : E × E) :
    (imageOf κ L hdr).read (gpow 0) = some hdr.1 ∧ (imageOf κ L hdr).read (gpow 1) = some hdr.2 := by
  have h2 : 1 < 2 ^ κ := Nat.one_lt_two_pow (by omega)
  refine ⟨?_, ?_⟩
  · have := MemImage.read_gpow hκ (imageOf κ L hdr) ⟨0, by omega⟩
    simpa [imageOf] using this
  · have := MemImage.read_gpow hκ (imageOf κ L hdr) ⟨1, h2⟩
    simpa [imageOf] using this

theorem memL_imageOf {κ : ℕ} (hκ : κ < 64) {L : Layout} (hc : LConsistent L)
    (hin : ∀ q ∈ L, 2 ≤ q.1 ∧ q.1 + q.2.length ≤ 2 ^ κ) (hdr : E × E) :
    MemL (imageOf κ L hdr).read L := by
  intro q hq k hk
  obtain ⟨h2, hle⟩ := hin q hq
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [addr_ofK]
  have hi : q.1 + k < 2 ^ κ := by omega
  rw [MemImage.read_gpow hκ (imageOf κ L hdr) ⟨q.1 + k, hi⟩]
  congr 1
  simp only [imageOf, show q.1 + k ≠ 0 by omega, show q.1 + k ≠ 1 by omega, ↓reduceIte]
  have hex : (L.find? fun q' => decide (q'.1 ≤ q.1 + k ∧ q.1 + k < q'.1 + q'.2.length)).isSome := by
    rw [List.find?_isSome]
    exact ⟨q, hq, by simp; omega⟩
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp hex
  simp only [hq']
  have hm := List.mem_of_find?_eq_some hq'
  have hp := List.find?_some hq'
  simp only [decide_eq_true_eq] at hp
  rw [← hc q hq q' hm (q.1 + k) (by omega) (by omega) hp.1 hp.2, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ hk]

end
end LeanVM.Guest.B1.Main
