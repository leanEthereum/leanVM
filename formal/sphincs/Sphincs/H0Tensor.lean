import Sphincs.H0Grid

/-! **Grid tensors for the kernel.** Integer functions on the grid `{0..4}^d` stored as nested
five-tuples, with the operations the moment tables need: point increments, prefix sums along every
axis, forward differences along every axis, pointwise maps and sums. Each operation is proved to
compute its mathematical counterpart, so the codeword CDF counts `K(m) = 256 H(m)` and the
numerators of `f(u)` and `f2(u)` are evaluated by the kernel. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-- Five values. -/
structure Five (α : Type) where
  c0 : α
  c1 : α
  c2 : α
  c3 : α
  c4 : α

/-- The value at a grid coordinate. -/
def Five.sel {α : Type} (t : Five α) (y : FPos) : α :=
  match y.val with
  | 0 => t.c0
  | 1 => t.c1
  | 2 => t.c2
  | 3 => t.c3
  | _ => t.c4

/-- Integer tensors on the grid `{0..4}^d`. -/
def NT : ℕ → Type
  | 0 => ℤ
  | d + 1 => Five (NT d)

/-- The value of a tensor at a grid point. -/
def getT : (d : ℕ) → NT d → (Fin d → FPos) → ℤ
  | 0, x, _ => (show ℤ from x)
  | d + 1, t, m => getT d ((show Five (NT d) from t).sel (m 0)) (Fin.tail m)

def zeroT : (d : ℕ) → NT d
  | 0 => (0 : ℤ)
  | d + 1 => (⟨zeroT d, zeroT d, zeroT d, zeroT d, zeroT d⟩ : Five (NT d))

def zipT : (d : ℕ) → (ℤ → ℤ → ℤ) → NT d → NT d → NT d
  | 0, f, a, b => f (show ℤ from a) (show ℤ from b)
  | d + 1, f, a, b =>
      let a' := (show Five (NT d) from a)
      let b' := (show Five (NT d) from b)
      (⟨zipT d f a'.c0 b'.c0, zipT d f a'.c1 b'.c1, zipT d f a'.c2 b'.c2, zipT d f a'.c3 b'.c3,
        zipT d f a'.c4 b'.c4⟩ : Five (NT d))

def mapT : (d : ℕ) → (ℤ → ℤ) → NT d → NT d
  | 0, f, a => f (show ℤ from a)
  | d + 1, f, a =>
      let a' := (show Five (NT d) from a)
      (⟨mapT d f a'.c0, mapT d f a'.c1, mapT d f a'.c2, mapT d f a'.c3, mapT d f a'.c4⟩ : Five (NT d))

/-- Forward differences along every axis. -/
def deltaT : (d : ℕ) → NT d → NT d
  | 0, a => a
  | d + 1, a =>
      let a' := (show Five (NT d) from a)
      let b0 := deltaT d a'.c0
      let b1 := deltaT d a'.c1
      let b2 := deltaT d a'.c2
      let b3 := deltaT d a'.c3
      let b4 := deltaT d a'.c4
      (⟨zipT d (· - ·) b0 b1, zipT d (· - ·) b1 b2, zipT d (· - ·) b2 b3, zipT d (· - ·) b3 b4, b4⟩ :
        Five (NT d))

/-- Prefix sums along every axis. -/
def cumT : (d : ℕ) → NT d → NT d
  | 0, a => a
  | d + 1, a =>
      let a' := (show Five (NT d) from a)
      let b0 := cumT d a'.c0
      let s1 := zipT d (· + ·) b0 (cumT d a'.c1)
      let s2 := zipT d (· + ·) s1 (cumT d a'.c2)
      let s3 := zipT d (· + ·) s2 (cumT d a'.c3)
      let s4 := zipT d (· + ·) s3 (cumT d a'.c4)
      (⟨b0, s1, s2, s3, s4⟩ : Five (NT d))

/-- Add one at a grid point. -/
def incT : (d : ℕ) → NT d → (Fin d → FPos) → NT d
  | 0, a, _ => (show ℤ from a) + 1
  | d + 1, a, c =>
      let a' := (show Five (NT d) from a)
      match (c 0).val with
      | 0 => (⟨incT d a'.c0 (Fin.tail c), a'.c1, a'.c2, a'.c3, a'.c4⟩ : Five (NT d))
      | 1 => (⟨a'.c0, incT d a'.c1 (Fin.tail c), a'.c2, a'.c3, a'.c4⟩ : Five (NT d))
      | 2 => (⟨a'.c0, a'.c1, incT d a'.c2 (Fin.tail c), a'.c3, a'.c4⟩ : Five (NT d))
      | 3 => (⟨a'.c0, a'.c1, a'.c2, incT d a'.c3 (Fin.tail c), a'.c4⟩ : Five (NT d))
      | _ => (⟨a'.c0, a'.c1, a'.c2, a'.c3, incT d a'.c4 (Fin.tail c)⟩ : Five (NT d))

/-- The sum over the grid of a function of two tensors' values. -/
def sumT2 : (d : ℕ) → (ℤ → ℤ → ℤ) → NT d → NT d → ℤ
  | 0, f, a, b => f (show ℤ from a) (show ℤ from b)
  | d + 1, f, a, b =>
      let a' := (show Five (NT d) from a)
      let b' := (show Five (NT d) from b)
      sumT2 d f a'.c0 b'.c0 + sumT2 d f a'.c1 b'.c1 + sumT2 d f a'.c2 b'.c2 + sumT2 d f a'.c3 b'.c3 +
        sumT2 d f a'.c4 b'.c4

/-! ### Correctness -/

theorem fpos_val_cases (y : FPos) : y.val = 0 ∨ y.val = 1 ∨ y.val = 2 ∨ y.val = 3 ∨ y.val = 4 := by
  have := y.isLt
  simp only [chainTop] at this
  omega

theorem getT_succ (d : ℕ) (t : NT (d + 1)) (m : Fin (d + 1) → FPos) :
    getT (d + 1) t m = getT d ((show Five (NT d) from t).sel (m 0)) (Fin.tail m) := rfl

theorem getT_cons (d : ℕ) (t : NT (d + 1)) (y : FPos) (m' : Fin d → FPos) :
    getT (d + 1) t (Fin.cons y m') = getT d ((show Five (NT d) from t).sel y) m' := by
  rw [getT_succ, Fin.cons_zero, Fin.tail_cons]

theorem sel_of_val {α : Type} (t : Five α) (y : FPos) :
    t.sel y = if y.val = 0 then t.c0 else if y.val = 1 then t.c1 else if y.val = 2 then t.c2
      else if y.val = 3 then t.c3 else t.c4 := by
  unfold Five.sel
  rcases fpos_val_cases y with h | h | h | h | h <;> simp [h]

theorem getT_zeroT : ∀ (d : ℕ) (m : Fin d → FPos), getT d (zeroT d) m = 0
  | 0, _ => rfl
  | d + 1, m => by
      rw [getT_succ, sel_of_val]
      rcases fpos_val_cases (m 0) with h | h | h | h | h <;> simp only [h] <;> simp <;> exact getT_zeroT d _

theorem getT_zipT (f : ℤ → ℤ → ℤ) : ∀ (d : ℕ) (a b : NT d) (m : Fin d → FPos),
    getT d (zipT d f a b) m = f (getT d a m) (getT d b m)
  | 0, _, _, _ => rfl
  | d + 1, a, b, m => by
      rw [getT_succ, getT_succ, getT_succ, sel_of_val, sel_of_val, sel_of_val]
      rcases fpos_val_cases (m 0) with h | h | h | h | h <;> simp only [h] <;> simp <;> exact getT_zipT f d _ _ _

theorem getT_mapT (f : ℤ → ℤ) : ∀ (d : ℕ) (a : NT d) (m : Fin d → FPos),
    getT d (mapT d f a) m = f (getT d a m)
  | 0, _, _ => rfl
  | d + 1, a, m => by
      rw [getT_succ, getT_succ, sel_of_val, sel_of_val]
      rcases fpos_val_cases (m 0) with h | h | h | h | h <;> simp only [h] <;> simp <;> exact getT_mapT f d _ _

theorem getT_deltaT : ∀ (d : ℕ) (a : NT d) (m : Fin d → FPos),
    (getT d (deltaT d a) m : ℝ) = deltaF d (fun m => (getT d a m : ℝ)) m
  | 0, _, _ => rfl
  | d + 1, a, m => by
      rw [getT_succ]
      simp only [deltaF, D1]
      have hcons : ∀ y : FPos, (fun m' => (getT (d + 1) a (Fin.cons y m') : ℝ)) =
          fun m' => (getT d ((show Five (NT d) from a).sel y) m' : ℝ) := fun y => funext fun m' => by
        rw [getT_cons]
      simp only [hcons, sel_of_val]
      rcases fpos_val_cases (m 0) with h | h | h | h | h <;> simp only [h, chainTop] <;>
        simp [deltaT, getT_zipT, getT_deltaT d]

/-- The prefix sum over the grid points below `m`. -/
noncomputable def cumF (d : ℕ) (g : (Fin d → FPos) → ℝ) (m : Fin d → FPos) : ℝ :=
  ∑ y : Fin d → FPos, (if ∀ i, y i ≤ m i then g y else 0)

theorem cumF_succ (d : ℕ) (g : (Fin (d + 1) → FPos) → ℝ) (y0 : FPos) (m' : Fin d → FPos) :
    cumF (d + 1) g (Fin.cons y0 m') =
      ∑ y : FPos, if y ≤ y0 then cumF d (fun m'' => g (Fin.cons y m'')) m' else 0 := by
  unfold cumF
  rw [sum_fin_succ_fun]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ≤ y0
  · rw [if_pos hy]
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    apply propext
    constructor
    · intro h i
      simpa using h i.succ
    · intro h i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hy
      · simpa using h j
  · rw [if_neg hy]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [if_neg]
    intro h
    exact hy (by simpa using h 0)

/-- A sum over the five grid coordinates. -/
theorem sum_fpos (F : FPos → ℝ) :
    ∑ y : FPos, F y = F ⟨0, by decide⟩ + F ⟨1, by decide⟩ + F ⟨2, by decide⟩ + F ⟨3, by decide⟩ +
      F ⟨4, by decide⟩ := by
  have key : ∀ F : Fin 5 → ℝ, ∑ y : Fin 5, F y = F 0 + F 1 + F 2 + F 3 + F 4 := fun F => Fin.sum_univ_five F
  exact key F

theorem getT_cumT : ∀ (d : ℕ) (a : NT d) (m : Fin d → FPos),
    (getT d (cumT d a) m : ℝ) = cumF d (fun m => (getT d a m : ℝ)) m
  | 0, _, m => by
      unfold cumF
      rw [Fintype.sum_unique, if_pos (fun i => i.elim0)]
      congr 2
      funext i
      exact i.elim0
  | d + 1, a, m => by
      have hm : m = Fin.cons (m 0) (Fin.tail m) := (Fin.cons_self_tail m).symm
      rw [hm, cumF_succ, getT_cons]
      have hcons : ∀ y : FPos, (fun m'' => (getT (d + 1) a (Fin.cons y m'') : ℝ)) =
          fun m'' => (getT d ((show Five (NT d) from a).sel y) m'' : ℝ) := fun y => funext fun m' => by
        rw [getT_cons]
      simp only [hcons, sum_fpos, sel_of_val, Fin.le_iff_val_le_val]
      rcases fpos_val_cases (m 0) with h | h | h | h | h <;> simp only [h] <;>
        simp [cumT, getT_zipT, getT_cumT d] <;> ring

theorem getT_incT : ∀ (d : ℕ) (a : NT d) (c m : Fin d → FPos),
    getT d (incT d a c) m = getT d a m + if m = c then 1 else 0
  | 0, _, c, m => by
      rw [if_pos (funext fun i => i.elim0)]
      rfl
  | d + 1, a, c, m => by
      have hm : m = Fin.cons (m 0) (Fin.tail m) := (Fin.cons_self_tail m).symm
      have hc : c = Fin.cons (c 0) (Fin.tail c) := (Fin.cons_self_tail c).symm
      have heq : (m = c) ↔ ((m 0).val = (c 0).val ∧ Fin.tail m = Fin.tail c) := by
        constructor
        · rintro rfl; exact ⟨rfl, rfl⟩
        · rintro ⟨h0, ht⟩
          rw [hm, hc, Fin.ext h0, ht]
      rw [getT_succ, getT_succ, sel_of_val, sel_of_val]
      have hinc : incT (d + 1) a c = (if (c 0).val = 0 then
          (⟨incT d (show Five (NT d) from a).c0 (Fin.tail c), (show Five (NT d) from a).c1,
            (show Five (NT d) from a).c2, (show Five (NT d) from a).c3, (show Five (NT d) from a).c4⟩ : Five (NT d))
        else if (c 0).val = 1 then
          ⟨(show Five (NT d) from a).c0, incT d (show Five (NT d) from a).c1 (Fin.tail c),
            (show Five (NT d) from a).c2, (show Five (NT d) from a).c3, (show Five (NT d) from a).c4⟩
        else if (c 0).val = 2 then
          ⟨(show Five (NT d) from a).c0, (show Five (NT d) from a).c1,
            incT d (show Five (NT d) from a).c2 (Fin.tail c), (show Five (NT d) from a).c3,
            (show Five (NT d) from a).c4⟩
        else if (c 0).val = 3 then
          ⟨(show Five (NT d) from a).c0, (show Five (NT d) from a).c1, (show Five (NT d) from a).c2,
            incT d (show Five (NT d) from a).c3 (Fin.tail c), (show Five (NT d) from a).c4⟩
        else
          ⟨(show Five (NT d) from a).c0, (show Five (NT d) from a).c1, (show Five (NT d) from a).c2,
            (show Five (NT d) from a).c3, incT d (show Five (NT d) from a).c4 (Fin.tail c)⟩) := by
        simp only [incT]
        rcases fpos_val_cases (c 0) with h | h | h | h | h <;> simp [h]
      rw [hinc]
      have ih := getT_incT d
      rcases fpos_val_cases (c 0) with hc0 | hc0 | hc0 | hc0 | hc0 <;>
        rcases fpos_val_cases (m 0) with hm0 | hm0 | hm0 | hm0 | hm0 <;>
        simp only [hc0, hm0, heq, ih] <;> simp [ih]

theorem sumT2_eq (f : ℤ → ℤ → ℤ) : ∀ (d : ℕ) (a b : NT d),
    (sumT2 d f a b : ℝ) = ∑ m : Fin d → FPos, (f (getT d a m) (getT d b m) : ℝ)
  | 0, _, _ => by rw [Fintype.sum_unique]; rfl
  | d + 1, a, b => by
      rw [sum_fin_succ_fun]
      simp only [getT_cons, sum_fpos, sel_of_val]
      simp only [sumT2, Int.cast_add, sumT2_eq f d]
      simp

end Sphincs.Security.H0
