module

public import LeanVM.Guest.Mode.SoundCall

/-!
# What a frame's entry and return give

`RetHolds`: a function's guarantees at its return. Covered cells and runs (`Abs.covered_val`,
`Abs.coveredHR_val`), a run's first point (`Rng.first_val`), and the facts the domain assumes at an
entry, sound when they hold (`Holds.assume`, `Holds.pinR`, `Holds.extR`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- What a function guarantees at a return, over its frame. -/
def RetHolds (s : St) (G : Sig) : Prop :=
  (∀ o ∈ G.ret, s.mem.written (s.fp + o) = true) ∧ (∀ m ∈ G.post, HW s m) ∧
    (∀ r ∈ G.postR, RW s r) ∧ (∀ q ∈ G.postP, PW s q.1 q.2) ∧
    (∀ p ∈ G.retV, ∃ u, s.mem.get (s.fp + p.1) = some u ∧ MonoVal s p.2 u) ∧
    (∀ p ∈ G.postT, LTF s p.1 p.2) ∧ ∀ q ∈ G.postC, CndHolds s ⟨q.1, q.2.1, [], [], [], q.2.2, []⟩

/-- The heap cell `k` names holds a pointer with the cells `os` past it written. -/
def HP (s : St) (k : Mono) (os : List ℕ) : Prop :=
  ∃ v x, MonoVal s k v ∧ Names v x ∧ PtrW s.mem x os

/-! ## A cell the walk knows written has a word -/

theorem Abs.coveredHR_val {s : St} {A : Abs} (hA : Holds s A) {k : Mono} (h : A.coveredHR k = true) :
    ∃ vk, MonoVal s k vk := by
  unfold Abs.coveredHR at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨k', hm, hb⟩ := List.any_eq_true.mp (any_of_anyB h)
    obtain rfl := Mono.beq_eq hb
    obtain ⟨v, -, h1, -⟩ := hA.h _ hm
    exact ⟨v, h1⟩
  · obtain ⟨r, hm, hb⟩ := List.any_eq_true.mp (Abs.inRuns_any h)
    exact inRng_valR hA (hA.r r hm) hb

/-- **A heap cell the walk knows written has a word.** -/
theorem Abs.covered_val {s : St} {A : Abs} (hA : Holds s A) {k : Mono} (h : A.covered k = true) :
    ∃ vk, MonoVal s k vk := by
  unfold Abs.covered at h
  split at h
  · rename_i d hd
    obtain ⟨rfl, -⟩ := Mono.ownCell_eq hd
    exact ⟨_, MonoVal.own d⟩
  · simp only [Bool.or_eq_true] at h
    rcases h with (((h | h) | h) | h) | h
    · exact Abs.coveredHR_val hA h
    · obtain ⟨v, hv⟩ := Abs.coveredHR_val hA h
      exact Abs.pinned_ex hA hv
    · obtain ⟨⟨r, os⟩, hm, hb⟩ := List.any_eq_true.mp h
      obtain ⟨vq, xlo, xhi, h1, -, h3, -⟩ := hA.p _ hm
      exact inRng_val' hA h1 h3 hb
    · split at h
      · exact (Abs.ptrHp_sound hA h).1
      · cases h
    · exact (Abs.tabCovered_sound hA h).1

/-- A heap cell the walk knows written: its word, and the written cell it names. -/
theorem Abs.covered_cell {s : St} {A : Abs} (hA : Holds s A) (hwf : s.mem.WF)
    (hu : s.mem.used ≤ maxCells) {k : Mono} (h : A.covered k = true) :
    ∃ vk x, MonoVal s k vk ∧ Names vk x ∧ s.mem.written x = true := by
  obtain ⟨vk, hk⟩ := Abs.covered_val hA h
  obtain ⟨x, hx, hw⟩ := Abs.covered_ex hA hwf hu h hk
  exact ⟨vk, x, hk, hx, hw⟩

/-- A run's point at its counter's start names its cell at the counter's exponent. -/
theorem Rng.first_val {s : St} {r : Rng} {y : ℕ} (hy : IdxVal s r.lo y) {vq : E}
    (hq : MonoVal s r.q vq) : MonoVal s r.first (vq * ofK (g ^ (r.S * y + r.d))) := by
  unfold Rng.first
  split
  · rename_i c hc
    rw [hc] at hy
    rw [show y = c from hy]
    exact hq.shift _
  · rename_i x c hc
    rw [hc] at hy
    obtain ⟨u, e, hu, rfl, -, rfl⟩ := hy
    have hx : MonoVal s ⟨0, 0, [(x, r.S)]⟩ (ofK (g ^ e) ^ r.S) :=
      ⟨_, ⟨_, 1, hu, rfl, rfl⟩, by simp⟩
    have := (hq.mul hx).shift (r.S * c + r.d)
    rw [show r.S * (e + c) + r.d = e * r.S + (r.S * c + r.d) by ring, pow_add, ofK_mul, pow_mul,
      ofK_pow]
    rw [← mul_assoc]
    exact this

theorem Rng.first_q {s : St} {r : Rng} {v : E} (h : MonoVal s r.first v) : ∃ vq, MonoVal s r.q vq := by
  unfold Rng.first at h
  split at h
  · obtain ⟨u, hu, -⟩ := h.unshift
    exact ⟨u, hu⟩
  · obtain ⟨u, hu, -⟩ := h.unshift
    obtain ⟨va, -, ha, -, -⟩ := MonoVal.mul_inv hu
    exact ⟨va, ha⟩

theorem PtrW.sub {m : Mem} {x : ℕ} {os os' : List ℕ} (h : PtrW m x os') (hs : ∀ o ∈ os, o ∈ os') :
    PtrW m x os := by
  obtain ⟨p, h1, h2⟩ := h
  exact ⟨p, h1, fun o ho ↦ h2 o (hs o ho)⟩

/-! ## Entry -/

theorem entry_w {l : List ℕ} : ∀ {t : Exec.Trie Unit} {o : ℕ},
    (l.foldl (fun t o ↦ t.set () Exec.envDepth o) t).get o = some () → o ∈ l ∨ t.get o = some () := by
  induction l with
  | nil => intro t o h; exact Or.inr h
  | cons a l ih =>
    intro t o h
    rcases ih h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases Exec.Trie.get_set h with ⟨rfl, -⟩ | h
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr h

/-- **What holds when a selector's exponent is `j`**: the facts under that condition, and its bounds. -/
theorem Holds.assume {s : St} {A : Abs} (hA : Holds s A) {sel : Option Base} {j : ℕ}
    (hsel : ∀ x, sel = some x → IdxVal s (.ex x 0) j) : Holds s (A.assume sel j) := by
  cases sel with
  | none => exact hA
  | some x =>
    have hi := hsel x rfl
    have h1 := (hA.addLt (a := .ex x 0) (b := .num (j + 1)) ⟨j, j + 1, hi, rfl, by omega⟩).addLt
      (a := .num j) (b := .ex x 1) ⟨j, j + 1, rfl, Idx.succ_val' hi, by omega⟩
    unfold Abs.assume
    dsimp only
    split
    · rename_i c hc
      have hm := List.mem_of_find?_eq_some hc
      have hk := List.find?_some hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨-, hf⟩ := hA.c c hm
      obtain ⟨hh, hr, hp, hlt, hhv⟩ := hf (by rw [Base.beq_eq hk.1, hk.2]; exact hi)
      exact { h1 with
        h := fun k hk' ↦ (List.mem_append.mp hk').elim (hh k) (h1.h k)
        r := fun r hr' ↦ (List.mem_append.mp hr').elim (hr r) (h1.r r)
        p := fun q hq ↦ (List.mem_append.mp hq).elim (hp q) (h1.p q)
        lt := fun q hq ↦ (List.mem_append.mp hq).elim (hlt q) (h1.lt q)
        hv := fun q hq ↦ (List.mem_append.mp hq).elim (h1.hv q) (fun hq ↦ hhv q (List.mem_filter.mp hq).1) }
    · exact h1

/-- Runs with their products' bases of known exponent made powers of `g`. -/
theorem Holds.pinR {s : St} {A : Abs} (hA : Holds s A) (x : Base) : Holds s (A.pinR x) := by
  unfold Abs.pinR
  exact { hA with
    r := fun r hr ↦ by
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨r0, hm, hr0⟩ := List.mem_filterMap.mp hr
        split_ifs at hr0
        cases hr0
        obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := hA.r r0 hm
        exact ⟨vq, xlo, xhi, Abs.pinned_val hA h1, h2, h3, h4⟩
      · exact hA.r r hr }

/-! ## Calls and returns -/

/-- A run from one stride further, and the point at its start. -/
theorem RW.ext {s : St} {r : Rng} (hS : r.S ≤ r.d) (hn : RW s r) (hp : HW s (⟨r.q, r.lo, r.hi.succ, r.S, r.d - r.S⟩ : Rng).first) :
    RW s ⟨r.q, r.lo, r.hi.succ, r.S, r.d - r.S⟩ := by
  obtain ⟨vq, xlo, xhi, h1, h2, h3, h4⟩ := hn
  refine ⟨vq, xlo, xhi + 1, h1, h2, Idx.succ_val' h3, fun j hj1 hj2 ↦ ?_⟩
  rcases Nat.eq_or_lt_of_le hj1 with rfl | hj1
  · obtain ⟨v, x, hv, hx, hw⟩ := hp
    rw [hv.unique (Rng.first_val (r := ⟨r.q, r.lo, r.hi.succ, r.S, r.d - r.S⟩) h2 h1)] at hx
    exact ⟨x, hx, hw⟩
  · obtain ⟨x, hx, hw⟩ := h4 (j - 1) (by omega) (by omega)
    refine ⟨x, ?_, hw⟩
    rwa [show r.S * (j - 1) + r.d = r.S * j + (r.d - r.S) by
      rw [Nat.mul_sub, Nat.mul_one]
      have : r.S ≤ r.S * j := Nat.le_mul_of_pos_right _ (by omega)
      omega] at hx

theorem Holds.extR {s : St} {A : Abs} (hA : Holds s A) (hwf : s.mem.WF) (hu : s.mem.used ≤ maxCells)
    {r : Rng} (hr : RW s r) : Holds s (A.extR r) := by
  unfold Abs.extR
  split_ifs with h1
  · dsimp only
    split_ifs with h2
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      obtain ⟨v, x, hv, hx, hw⟩ := Abs.covered_cell hA hwf hu h2
      have hrw := RW.ext h1.2 hr ⟨v, x, hv, hx, hw⟩
      exact { hA with
        r := fun r' hm ↦ by
          rcases List.mem_cons.mp hm with rfl | hm
          exacts [hrw, hA.r r' hm] }
    · exact hA
  · exact hA

end

end LeanVM.Guest.Mode
