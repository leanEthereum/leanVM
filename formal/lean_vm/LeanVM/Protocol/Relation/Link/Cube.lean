/-
  LeanVM.Protocol.Relation.Link.Cube

  Tables of partial sums over the Boolean cube, and polynomials in one variable: a function of
  bounded degree in each coordinate gives a sum-check's table of partial sums.
-/

module

public import LeanVM.Protocol.Relation.Link.Rounds

/-!
# Partial sums over the cube

`cube f n p = Σ_{b ∈ {0,1}^{n − |p|}} f (p ++ b)`, the partial sums a sum-check over `n` variables
walks, from the full sum at `[]` to `f` itself at `n` challenges. `roundPolys_cube`: if `f` is a
polynomial of degree at most `deg i` in each coordinate `i` (`PerVarDegAt`), `cube f n` is a table of
partial sums of round degrees `deg` (`RoundPolys`). `PolyIn g d` says `g : E → E` is a polynomial of
degree at most `d`, with its closure under the ring's operations.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Link Finset

@[expose] public section

/-! ## One variable -/

/-- `g` is a polynomial of degree at most `d`. -/
def PolyIn (g : E → E) (d : ℕ) : Prop :=
  ∃ p : Polynomial E, p.natDegree ≤ d ∧ ∀ c, p.eval c = g c

namespace PolyIn

theorem const (a : E) : PolyIn (fun _ ↦ a) 0 := ⟨Polynomial.C a, by simp, fun _ ↦ by simp⟩

theorem var : PolyIn (fun c ↦ c) 1 := ⟨Polynomial.X, by simp, fun _ ↦ by simp⟩

theorem mono {g : E → E} {d e : ℕ} (h : PolyIn g d) (hde : d ≤ e) : PolyIn g e := by
  obtain ⟨p, hp, hv⟩ := h
  exact ⟨p, hp.trans hde, hv⟩

theorem congr {g g' : E → E} {d : ℕ} (h : PolyIn g d) (hg : ∀ c, g c = g' c) : PolyIn g' d := by
  obtain ⟨p, hp, hv⟩ := h
  exact ⟨p, hp, fun c ↦ (hv c).trans (hg c)⟩

theorem add {f g : E → E} {d e : ℕ} (hf : PolyIn f d) (hg : PolyIn g e) :
    PolyIn (fun c ↦ f c + g c) (max d e) := by
  obtain ⟨p, hp, hpv⟩ := hf
  obtain ⟨q, hq, hqv⟩ := hg
  refine ⟨p + q, (Polynomial.natDegree_add_le _ _).trans (max_le_max hp hq), fun c ↦ ?_⟩
  simp [hpv, hqv]

theorem neg {f : E → E} {d : ℕ} (hf : PolyIn f d) : PolyIn (fun c ↦ -f c) d := by
  obtain ⟨p, hp, hpv⟩ := hf
  exact ⟨-p, by rwa [Polynomial.natDegree_neg], fun c ↦ by simp [hpv]⟩

theorem sub {f g : E → E} {d e : ℕ} (hf : PolyIn f d) (hg : PolyIn g e) :
    PolyIn (fun c ↦ f c - g c) (max d e) :=
  (hf.add hg.neg).congr fun _ ↦ (sub_eq_add_neg _ _).symm

theorem mul {f g : E → E} {d e : ℕ} (hf : PolyIn f d) (hg : PolyIn g e) :
    PolyIn (fun c ↦ f c * g c) (d + e) := by
  obtain ⟨p, hp, hpv⟩ := hf
  obtain ⟨q, hq, hqv⟩ := hg
  refine ⟨p * q, Polynomial.natDegree_mul_le.trans (add_le_add hp hq), fun c ↦ ?_⟩
  simp [hpv, hqv]

theorem add_le {f g : E → E} {d : ℕ} (hf : PolyIn f d) (hg : PolyIn g d) :
    PolyIn (fun c ↦ f c + g c) d :=
  (hf.add hg).mono (max_le le_rfl le_rfl)

theorem mul_le {f g : E → E} {d e n : ℕ} (hf : PolyIn f d) (hg : PolyIn g e) (h : d + e ≤ n) :
    PolyIn (fun c ↦ f c * g c) n :=
  (hf.mul hg).mono h

theorem finsetSum {ι : Type} (s : Finset ι) {f : ι → E → E} {d : ℕ}
    (h : ∀ i ∈ s, PolyIn (f i) d) : PolyIn (fun c ↦ ∑ i ∈ s, f i c) d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ((const 0).mono (Nat.zero_le _)).congr fun c ↦ by simp
  | insert a s ha ih =>
    refine ((h a (mem_insert_self a s)).add_le (ih fun i hi ↦ h i (mem_insert_of_mem hi))).congr
      fun c ↦ ?_
    rw [sum_insert ha]

theorem listSum {ι : Type} (l : List ι) {f : ι → E → E} {d : ℕ}
    (h : ∀ i ∈ l, PolyIn (f i) d) : PolyIn (fun c ↦ (l.map fun i ↦ f i c).sum) d := by
  induction l with
  | nil => exact ((const 0).mono (Nat.zero_le _)).congr fun c ↦ by simp
  | cons a l ih =>
    exact ((h a (by simp)).add_le (ih fun i hi ↦ h i (by simp [hi]))).congr fun c ↦ by simp

end PolyIn

/-! ## Partial sums over the cube -/

/-- `Σ_{b ∈ {0,1}^k} f (p ++ b)`. -/
def sumTail (f : List E → E) : ℕ → List E → E
  | 0, p => f p
  | k + 1, p => sumTail f k (p ++ [0]) + sumTail f k (p ++ [1])

/-- **The table of partial sums** of `f` over `n` variables: at `p`, the sum over the cube of the
coordinates after `p`. -/
def cube (f : List E → E) (n : ℕ) (p : List E) : E := sumTail f (n - p.length) p

/-- At all `n` challenges, the table is `f`. -/
theorem cube_full {f : List E → E} {n : ℕ} {p : List E} (h : n ≤ p.length) : cube f n p = f p := by
  simp [cube, Nat.sub_eq_zero_of_le h, sumTail]

/-- `sumTail` is linear in `f`. -/
theorem sumTail_add (f g : List E → E) : ∀ (k : ℕ) (p : List E),
    sumTail (fun x ↦ f x + g x) k p = sumTail f k p + sumTail g k p
  | 0, _ => rfl
  | k + 1, p => by simp only [sumTail, sumTail_add f g k]; ring

theorem sumTail_smul (a : E) (f : List E → E) : ∀ (k : ℕ) (p : List E),
    sumTail (fun x ↦ a * f x) k p = a * sumTail f k p
  | 0, _ => rfl
  | k + 1, p => by simp only [sumTail, sumTail_smul a f k]; ring

theorem sumTail_finsetSum {ι : Type} (s : Finset ι) (f : ι → List E → E) (k : ℕ) (p : List E) :
    sumTail (fun x ↦ ∑ i ∈ s, f i x) k p = ∑ i ∈ s, sumTail (f i) k p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    induction k generalizing p with
    | zero => rfl
    | succ k ih => simp [sumTail, ih]
  | insert a s ha ih =>
    simp only [sum_insert ha]
    rw [sumTail_add (f a) (fun x ↦ ∑ i ∈ s, f i x) k p, ih]

theorem sumTail_congr {f g : List E → E} : ∀ (k : ℕ) (p : List E),
    (∀ b : List E, b.length = k → f (p ++ b) = g (p ++ b)) → sumTail f k p = sumTail g k p
  | 0, p, h => by simpa [sumTail] using h [] rfl
  | k + 1, p, h => by
    simp only [sumTail]
    rw [sumTail_congr k (p ++ [0]) fun b hb ↦ by simpa using h (0 :: b) (by simp [hb]),
      sumTail_congr k (p ++ [1]) fun b hb ↦ by simpa using h (1 :: b) (by simp [hb])]

/-- `f` is, in each coordinate `i < n`, a polynomial of degree at most `deg i`. -/
def PerVarDegAt (f : List E → E) (n : ℕ) (deg : ℕ → ℕ) : Prop :=
  ∀ pre rest : List E, pre.length + 1 + rest.length = n →
    PolyIn (fun c ↦ f (pre ++ c :: rest)) (deg pre.length)

theorem perVarDeg_of_at {f : List E → E} {n d : ℕ} (h : PerVarDegAt f n fun _ ↦ d) :
    PerVarDeg f n d := fun pre rest hl ↦ h pre rest hl

theorem sumTail_polyIn {f : List E → E} {n : ℕ} {deg : ℕ → ℕ} (hf : PerVarDegAt f n deg)
    (pre : List E) : ∀ (k : ℕ) (mid : List E), pre.length + 1 + mid.length + k = n →
      PolyIn (fun c ↦ sumTail f k (pre ++ c :: mid)) (deg pre.length)
  | 0, mid, hl => hf pre mid (by simpa using hl)
  | k + 1, mid, hl => by
    have h0 := sumTail_polyIn hf pre k (mid ++ [0]) (by simp; omega)
    have h1 := sumTail_polyIn hf pre k (mid ++ [1]) (by simp; omega)
    exact (h0.add_le h1).congr fun c ↦ by simp [sumTail]

/-- **A function of bounded degree in each coordinate gives a table of partial sums.** -/
theorem roundPolys_cube {f : List E → E} {n : ℕ} {deg : ℕ → ℕ} (hf : PerVarDegAt f n deg) :
    RoundPolys (cube f n) n deg := by
  intro p hp
  obtain ⟨q, hq, hv⟩ := sumTail_polyIn hf p (n - p.length - 1) [] (by simp; omega)
  refine ⟨q, hq, ?_, fun c ↦ ?_⟩
  · rw [hv, hv, cube, show n - p.length = (n - p.length - 1) + 1 by omega]
    rfl
  · rw [hv, cube, List.length_append, List.length_singleton,
      show n - (p.length + 1) = n - p.length - 1 by omega]

end

end LeanVM.Protocol.Relation
