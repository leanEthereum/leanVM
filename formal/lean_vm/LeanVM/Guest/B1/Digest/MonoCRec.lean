/-
  LeanVM.Guest.B1.Digest.MonoCRec

  The claims of the gap walk, completely: on an evaluated valuation whose hints are the honest gaps,
  the walk's pointers, its cells, and its side atoms hold at honest slots.
-/

module

public import LeanVM.Guest.B1.Digest.MonoCChk
public import LeanVM.Guest.B1.Digest.ChildListCRec

/-!
# The gap walk, completely

The honest walk over slots `o` (strictly increasing) stands at `mStart o j` before claim `j` (`0`,
then one past the previous slot) and hints the gap `mGap o j = o j - mStart o j`. `MRec`: claim
`j < K` (of a frame from claim `s`, slots `o (s + j)`) below `L`, the mark at the region's slot,
its cells at the table. `mRecs_core`: on a valuation evaluated (`Fwd.Good`) with the gaps hinted,
claims evaluated by `mRecW` have their coverage pointer `region · g^(o (s + j) - j)`, their table
pointer `entries · g^(4 (o (s + j) - j))` and their cells, and their side atoms hold.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The slot the walk stands at before claim `j`: `0`, then one past the previous claim's. -/
def mStart (o : ℕ → ℕ) (j : ℕ) : ℕ := if j = 0 then 0 else o (j - 1) + 1

/-- Claim `j`'s gap. -/
def mGap (o : ℕ → ℕ) (j : ℕ) : ℕ := o j - mStart o j

theorem mStart_succ (o : ℕ → ℕ) (j : ℕ) : mStart o (j + 1) = o j + 1 := by simp [mStart]

/-- **The honest claims of a walk**: claim `j < K` at slot `os j` below `L`, the mark at the
region's slot, its four cells at the table. -/
def MRec (rd : Reader) (region : E) (L : ℕ) (entries mark : E) (K : ℕ) (os : ℕ → ℕ)
    (cells : List E) : Prop :=
  ∀ j < K, os j < L ∧ LoadHolds rd (region * gen ^ os j) 0 mark ∧
    ∀ c < 4, LoadHolds rd entries (4 * os j + c) (cells.getD (4 * j + c) 0)

variable {rd : Reader} {A S : List Atom} {w : ℕ → E} {σ : Val}

/-! ## The atoms' parts -/

theorem mem_monoWin {A : List Atom} {p0 j : ℕ} {a : Atom} (h : a ∈ monoWin A p0 j) : a ∈ A :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- **A block's atoms**: before its claims, a claim's own, or after them. -/
theorem mem_mParts {A : List Atom} {p0 K : ℕ} {a : Atom} (ha : a ∈ A) :
    a ∈ A.take p0 ∨ (∃ j < K, a ∈ monoWin A p0 j) ∨ a ∈ A.drop (p0 + 11 * K) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  rcases Nat.lt_or_ge i p0 with h1 | h1
  · exact Or.inl (List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩)
  rcases Nat.lt_or_ge i (p0 + 11 * K) with h2 | h2
  · refine Or.inr (Or.inl ⟨(i - p0) / 11, by omega,
      List.mem_iff_getElem.mpr ⟨(i - p0) % 11, ?_, ?_⟩⟩)
    · simp only [monoWin, List.length_take, List.length_drop]; omega
    · simp only [monoWin, List.getElem_take, List.getElem_drop]
      congr 1; omega
  · exact Or.inr (Or.inr (List.mem_iff_getElem.mpr ⟨i - (p0 + 11 * K), by simp; omega,
      by simp only [List.getElem_drop]; congr 1; omega⟩))

/-- **The claims from windows** of `w` claims covering the `K`. -/
theorem mRecs_of_wins {A : List Atom} {p0 g0 cov0 ent0 : ℕ} {mark : V} {K w W : ℕ}
    (hn : K ≤ w * W) (h : ∀ i < W, mRecsC A p0 g0 cov0 ent0 mark K (w * i) w = true) :
    mRecsC A p0 g0 cov0 ent0 mark K 0 K = true := by
  simp only [mRecsC, List.all_eq_true, List.mem_range', Bool.or_eq_true, decide_eq_true_eq]
  rintro k ⟨i, hi, rfl⟩
  right
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hk : i / w < W := by
    rw [Nat.div_lt_iff_lt_mul hw]; rw [Nat.mul_comm] at hn; omega
  have := h (i / w) hk
  simp only [mRecsC, List.all_eq_true, List.mem_range', Bool.or_eq_true,
    decide_eq_true_eq] at this
  rcases this (0 + 1 * i) ⟨i % w, Nat.mod_lt _ hw, by have := Nat.div_add_mod i w; omega⟩
    with h' | h'
  · omega
  · exact h'

theorem mRecsC_at {A : List Atom} {p0 g0 cov0 ent0 : ℕ} {mark : V} {K : ℕ}
    (h : mRecsC A p0 g0 cov0 ent0 mark K 0 K = true) {j : ℕ} (hj : j < K) :
    mRecW (monoWin A p0 j) j (g0 + 10 * j) (mCov g0 cov0 j) (mEnt g0 ent0 j) mark = true := by
  simp only [mRecsC, List.all_eq_true, List.mem_range', Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h j ⟨j, hj, by omega⟩ with h' | h'
  · omega
  · exact h'

theorem mRecW_parts {W : List Atom} {j gap pc pe : ℕ} {mark : V}
    (h : mRecW W j gap pc pe mark = true) :
    W.any (isWitO (.n gap)) = true ∧ mPtrOk (W.filter pureB) gap pc pe = true ∧
      (∀ c < 4, W.any (isLoadAt (.n (gap + 6 + c)) (.n (gap + 5)) (4 * j + c)) = true) ∧
      ∀ a ∈ W, needsSide a = true → mSide j gap mark a = true := by
  simp only [mRecW, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun a ha hn => (h4 a ha).resolve_left (by simp [hn])⟩

theorem mPtr_vals {F : List Atom} {gap pc pe : ℕ} (h : mPtrOk F gap pc pe = true)
    (hF : ∀ a ∈ F, a.Holds rd σ) :
    σ (.n (gap + 2)) = σ (.n pc) * σ (.n gap) ∧
      σ (.n (gap + 5)) = σ (.n pe) * (σ (.n gap) ^ 2) ^ 2 := by
  simp only [mPtrOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := h
  refine ⟨mulOf_sound h2 hF, ?_⟩
  rw [mulOf_sound h5 hF, mulOf_sound h4 hF, mulOf_sound h3 hF]
  ring

/-- A store through a coverage pointer or the record pointer `stp < g0` from `15`: a load
through a table pointer, or through `stp` below `15`, is none. -/
theorem notS_of_mStores {g0 stp : ℕ} (hS : ∀ a ∈ S, mStoresOk g0 stp a = true) {d p : V} {off : ℕ}
    (hp : covPtrB g0 p.idx = false) (h : p.idx ≠ stp ∨ off < 15) : Atom.load d p off ∉ S := by
  intro hm
  have := hS _ hm
  simp only [mStoresOk, hp, Bool.or_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  omega

theorem covPtrB_ent {g0 j : ℕ} : covPtrB g0 (g0 + 10 * j + 5) = false := by
  simp only [covPtrB, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  right; omega

theorem covPtrB_below {g0 q : ℕ} (h : q < g0 + 2) : covPtrB g0 q = false := by
  simp only [covPtrB, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  left; omega

/-! ## The claims' values -/

theorem mStart_le {o : ℕ → ℕ} {s K : ℕ} (hinc : ∀ j < K, mStart o (s + j) ≤ o (s + j)) :
    ∀ j < K, j + mStart o s ≤ o (s + j) := by
  intro j
  induction j with
  | zero => intro h; simpa using hinc 0 h
  | succ j ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hinc (j + 1) h
    rw [← Nat.add_assoc, mStart_succ] at h2
    rw [← Nat.add_assoc]
    omega

set_option maxRecDepth 20000 in
/-- **The claims of a block, evaluated, hold**: with the honest gaps hinted and the pointers from
`region · g^(mStart o s)`, `entries · g^(4 mStart o s)`, claim `j`'s pointers stand at
`o (s + j) - j`, its cells are the honest ones, and its side atoms hold. -/
theorem mRecs_core {p0 g0 cov0 ent0 stp K s L : ℕ} {markV : V} {o : ℕ → ℕ}
    {region entries : E} {cells : List E}
    (hrecs : ∀ j < K, mRecW (monoWin A p0 j) j (g0 + 10 * j) (mCov g0 cov0 j) (mEnt g0 ent0 j)
      markV = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) (hS : ∀ a ∈ S, mStoresOk g0 stp a = true) (hstp : stp < g0)
    (hw : ∀ j < K, w (g0 + 10 * j) = gen ^ mGap o (s + j))
    (hc0 : σ (.n cov0) = region * gen ^ mStart o s)
    (he0 : σ (.n ent0) = entries * gen ^ (4 * mStart o s))
    (hinc : ∀ j < K, mStart o (s + j) ≤ o (s + j))
    (hrec : MRec rd region L entries (σ markV) K (fun j => o (s + j)) cells)
    (hdef : BoundMem rd L) :
    (∀ j < K, σ (.n (g0 + 10 * j + 2)) = region * gen ^ (o (s + j) - j)) ∧
      (∀ j < K, σ (.n (g0 + 10 * j + 5)) = entries * gen ^ (4 * (o (s + j) - j))) ∧
      (∀ j < K, ∀ c < 4, σ (.n (g0 + 10 * j + 6 + c)) = cells.getD (4 * j + c) 0) ∧
      ∀ j < K, ∀ a ∈ monoWin A p0 j, needsSide a = true → a.Holds rd σ := by
  have hle := mStart_le hinc
  have hgW : ∀ j, ∀ a ∈ monoWin A p0 j, Good rd S w σ a := fun j a ha => hg a (mem_monoWin ha)
  have hFW : ∀ j, ∀ a ∈ (monoWin A p0 j).filter pureB, a.Holds rd σ := fun j => pure_holds (hgW j)
  have hgap : ∀ j < K, σ (.n (g0 + 10 * j)) = gen ^ mGap o (s + j) := fun j hj =>
    (wit_val (mRecW_parts (hrecs j hj)).1 (hgW j)).trans (hw j hj)
  have hptr : ∀ j < K, σ (.n (g0 + 10 * j + 2)) = region * gen ^ (o (s + j) - j) ∧
      σ (.n (g0 + 10 * j + 5)) = entries * gen ^ (4 * (o (s + j) - j)) := by
    intro j
    induction j with
    | zero =>
      intro hj
      obtain ⟨h2, h5⟩ := mPtr_vals (mRecW_parts (hrecs 0 hj)).2.1 (hFW 0)
      have hg0 := hgap 0 hj
      have hs := hle 0 hj
      have e : o (s + 0) - 0 = mStart o s + mGap o (s + 0) := by
        unfold mGap; simp only [Nat.add_zero] at hs ⊢; omega
      simp only [mCov, mEnt, ↓reduceIte] at h2 h5
      rw [e]
      exact ⟨by rw [h2, hc0, hg0, pow_add, mul_assoc], by rw [h5, he0, hg0]; ring⟩
    | succ j ih =>
      intro hj
      obtain ⟨i2, i5⟩ := ih (by omega)
      obtain ⟨h2, h5⟩ := mPtr_vals (mRecW_parts (hrecs (j + 1) hj)).2.1 (hFW (j + 1))
      have hg1 := hgap (j + 1) hj
      have hc : mCov g0 cov0 (j + 1) = g0 + 10 * j + 2 := by simp [mCov]
      have he : mEnt g0 ent0 (j + 1) = g0 + 10 * j + 5 := by simp [mEnt]
      rw [hc] at h2
      rw [he] at h5
      have hs := hle j (by omega)
      have hs1 := hinc (j + 1) hj
      rw [← Nat.add_assoc, mStart_succ] at hs1
      have e : o (s + j) - j + mGap o (s + (j + 1)) = o (s + (j + 1)) - (j + 1) := by
        unfold mGap; rw [← Nat.add_assoc, mStart_succ]; omega
      exact ⟨by rw [h2, i2, hg1, mul_assoc, ← pow_add, e], by rw [h5, i5, hg1, ← e]; ring⟩
  have hcell : ∀ j < K, ∀ c < 4,
      LoadHolds rd (σ (.n (g0 + 10 * j + 5))) (4 * j + c) (cells.getD (4 * j + c) 0) := by
    intro j hj c hc
    rw [(hptr j hj).2, loadHolds_mul_gen_pow]
    rw [show 4 * (o (s + j) - j) + (4 * j + c) = 4 * o (s + j) + c by
      have := hle j hj; omega]
    exact (hrec j hj).2.2 c hc
  have hnS5 : ∀ j < K, ∀ {d : V} {off : ℕ}, Atom.load d (.n (g0 + 10 * j + 5)) off ∉ S :=
    fun j _ _ _ => notS_of_mStores hS covPtrB_ent (Or.inl (by simp; omega))
  refine ⟨fun j hj => (hptr j hj).1, fun j hj => (hptr j hj).2, fun j hj c hc => ?_,
    fun j hj a ha hn => ?_⟩
  · have hl := (mRecW_parts (hrecs j hj)).2.2.1 c hc
    rw [load_val hl (hgW j) (hnS5 j hj), rdAt_of_load (hcell j hj c hc)]
  · have hs := (mRecW_parts (hrecs j hj)).2.2.2 a ha hn
    cases a with
    | touch t p =>
      simp only [mSide, decide_eq_true_eq] at hs
      subst hs
      have h1 : o (s + j) < L := (hrec j hj).1
      obtain ⟨v, hv⟩ := hdef (mGap o (s + j)) (by unfold mGap; omega)
      exact touch_holds_of (hgW j _ ha) (by rw [hgap j hj]; exact hv)
    | load d p off =>
      simp only [mSide, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
      rcases hs with ⟨⟨hp, hoff⟩, hd⟩ | ⟨⟨rfl, h1⟩, h2⟩
      · subst hp
        rw [hoff, hd]
        show LoadHolds rd (σ (.n (g0 + 10 * j + 2))) j (σ markV)
        rw [(hptr j hj).1, loadHolds_mul_gen_pow,
          show o (s + j) - j + j = o (s + j) + 0 by have := hle j hj; omega,
          ← loadHolds_mul_gen_pow]
        exact (hrec j hj).2.1
      · obtain ⟨c, rfl⟩ : ∃ c, off = 4 * j + c := ⟨off - 4 * j, by omega⟩
        exact load_holds_of (hnS5 j hj) (hgW j _ ha) (hcell j hj c (by omega))
    | _ => simp [mSide] at hs

end
end LeanVM.Guest.B1.Digest
