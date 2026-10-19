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

theorem pairwise_mem_ne {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b
  | [], _, a, ha, _, _, _ => by simp at ha
  | x :: l, h, a, ha, b, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hab
    · rw [h1]; exact h.1 b h2
    · rw [h2]; exact hs _ _ (h.1 a h1)
    · exact pairwise_mem_ne hs h.2 a h1 b h2 hab

/-- **Pairwise disjoint entries are consistent.** -/
theorem lConsistent_of_pairwise {L : Layout}
    (h : L.Pairwise fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1) : LConsistent L := by
  intro q hq q' hq' i h1 h2 h3 h4
  by_cases he : q = q'
  · subst he; rfl
  · have := pairwise_mem_ne (fun a b hab => hab.symm) h q hq q' hq' he
    omega

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

/-! ## `main`'s own words are disjoint -/

/-- Entries in disjoint slots. -/
def PwDisj (L : Layout) : Prop :=
  L.Pairwise fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1

theorem pwDisj_bufL : ∀ (b : ℕ) (sizes : List ℕ) (cs : List (List E)),
    List.Forall₂ (fun c s => c.length ≤ s) cs sizes → PwDisj (LeanVM.Guest.B1.bufL b sizes cs)
  | _, [], _, _ => by simp [LeanVM.Guest.B1.bufL, bases, PwDisj]
  | b, s :: sizes, [], h => by cases h
  | b, s :: sizes, c :: cs, h => by
    obtain ⟨hc, h⟩ := List.forall₂_cons.mp h
    simp only [LeanVM.Guest.B1.bufL, bases, List.zip_cons_cons, PwDisj, List.pairwise_cons]
    exact ⟨fun q hq => Or.inl (by
      have := LeanVM.Guest.B1.bufL_within (b + s) sizes cs h q hq; show b + c.length ≤ q.1; omega),
      pwDisj_bufL (b + s) sizes cs h⟩

theorem pwDisj_append {L L' : Layout} {b n b' n' : ℕ} (h : PwDisj L) (h' : PwDisj L')
    (hw : LeanVM.Guest.B1.Within L b n) (hw' : LeanVM.Guest.B1.Within L' b' n') (hb : b + n ≤ b') :
    PwDisj (L ++ L') :=
  List.pairwise_append.mpr ⟨h, h', fun q hq q' hq' => by
    have := hw q hq; have := hw' q' hq'; omega⟩

theorem pwDisj_mainIn (fs : String → ℕ) (fp : ℕ) (W : MainWords) (hl : W.bufs.map List.length = W.sizes) :
    PwDisj (mainIn fs fp W) := by
  have hf := forall₂_of_map_length _ _ hl
  refine pwDisj_append (pwDisj_bufL _ _ _ hf) ?_ (LeanVM.Guest.B1.bufL_within _ _ _ hf)
    (b' := mainExpBase fs fp W) (n' := 68) (fun q hq => ?_) (by unfold mainExpBase; omega)
  · simp only [mainLexp, PwDisj, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    left; simp [expTbl1]
  · simp only [mainLexp, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simp [expTbl1]
    · simp [expTbl2]

end
end LeanVM.Guest.B1.Main
