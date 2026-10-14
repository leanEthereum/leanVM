import Whir.TerminalRefinement
import Whir.OODBounds

/-! OOD separation for the executable array evaluator. Boolean coordinates are
mapped to physical coefficient indices with the first coordinate as the low bit.
Candidate arrays are fixed before the sampled `Array.ofFn` challenge point. -/
namespace Whir.ExecutableOOD
open Concrete ArrayLayout TerminalRefinement
open scoped BigOperators

/-- Physical little-endian index of a Boolean vertex. -/
def cubeIndex : {n : Nat} → Cube n → Nat
  | 0, _ => 0
  | n + 1, u => 2 * cubeIndex (fun i : Fin n => u i.succ) + if u 0 then 1 else 0

@[simp] theorem cubeIndex_cons {n : Nat} (b : Bool) (u : Cube n) :
    cubeIndex (Fin.cons b u) = 2 * cubeIndex u + if b then 1 else 0 := rfl

theorem cubeIndex_lt {n : Nat} (u : Cube n) : cubeIndex u < 2 ^ n := by
  induction n with
  | zero => simp [cubeIndex]
  | succ n ih =>
    have h := ih (fun i => u i.succ)
    simp only [cubeIndex, pow_succ]
    split <;> omega

theorem cubeIndex_surjective {n : Nat} (i : Nat) (hi : i < 2 ^ n) :
    ∃ u : Cube n, cubeIndex u = i := by
  induction n generalizing i with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    simp only [pow_zero] at hi
    simp [cubeIndex, show i = 0 by omega]
  | succ n ih =>
    have hq : i / 2 < 2 ^ n := by
      rw [pow_succ] at hi
      omega
    obtain ⟨u, hu⟩ := ih (i / 2) hq
    by_cases hb : i % 2 = 0
    · refine ⟨Fin.cons false u, ?_⟩
      simp only [cubeIndex_cons, Bool.false_eq_true, ↓reduceIte, hu, Nat.add_zero]
      omega
    · refine ⟨Fin.cons true u, ?_⟩
      simp only [cubeIndex_cons, ↓reduceIte, hu]
      omega

variable {R : Type*} [Inhabited R]

/-- The actual array coefficient at the explicitly specified Boolean index. -/
def decode (n : Nat) (a : Array R) : Cube n → R := fun u => a[cubeIndex u]!

theorem decode_injective (n : Nat) :
    Function.Injective (fun a : {a : Array R // a.size = 2 ^ n} => decode n a.val) := by
  intro a b h
  apply Subtype.ext
  apply Array.ext
  · exact a.property.trans b.property.symm
  · intro i hi hj
    obtain ⟨u, hu⟩ := cubeIndex_surjective i (by simpa [a.property] using hi)
    have he := congrFun h u
    simpa only [decode, hu, getElem!_pos, hi, hj] using he

variable [CommRing R] [CharP R 2]

theorem decode_foldLow {n : Nat} (a : Array R) (r : R)
    (ha : a.size = 2 ^ (n + 1)) :
    decode n (foldLow a r) = foldFirst (decode (n + 1) a) r := by
  funext u
  have hi : cubeIndex u < a.size / 2 := by
    simpa [ha, pow_succ] using cubeIndex_lt u
  simp only [decode, foldLow, getElem!_tab _ _ _ hi, foldFirst, cubeIndex_cons,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero, CharTwo.sub_eq_add, foldPair]
  ring

/-- Exact bridge: the executable MLE uses the same coordinate order as `Cube`.
No executable/abstract-evaluator equality is an assumption. -/
theorem mle_eq_cube {n : Nat} (a : Array R) (r : Fin n → R)
    (ha : a.size = 2 ^ n) :
    Concrete.mle a (Array.ofFn r) = Whir.mle (decode n a) r := by
  induction n generalizing a with
  | zero =>
    have he : Array.ofFn r = #[] := by apply Array.eq_empty_of_size_eq_zero; simp
    rw [he, mle_empty a (by simpa using ha)]
    simp [Whir.mle, innerProduct, eqWeight, decode, cubeIndex, Cube]
  | succ n ih =>
    rw [Array.ofFn_succ', mle_cons a _ _ (by simpa using ha)]
    rw [ih (foldLow a (r 0)) (fun i => r i.succ) (by simp [ha, pow_succ])]
    rw [decode_foldLow a (r 0) ha, mle_foldFirst]
    congr 1
    ext i
    exact Fin.cases rfl (fun _ => rfl) i

variable {F : Type*} [Field F] [CharP F 2] [Inhabited F]

/-- The executable evaluator itself, run on symbolic coordinates. -/
noncomputable def arrayPolynomial {n : Nat} (a : Array F) :
    MvPolynomial (Fin n) F :=
  Concrete.mle (a.map MvPolynomial.C) (Array.ofFn MvPolynomial.X)

theorem arrayPolynomial_eq {n : Nat} (a : Array F) (ha : a.size = 2 ^ n) :
    arrayPolynomial (n := n) a = OODBounds.mlePolynomial (decode n a) := by
  unfold arrayPolynomial
  rw [mle_eq_cube _ _ (by simpa using ha)]
  unfold OODBounds.mlePolynomial
  congr 1
  funext u
  have hi : cubeIndex u < a.size := by simpa [ha] using cubeIndex_lt u
  simp [decode, getElem!_pos, hi]

theorem eval_arrayPolynomial {n : Nat} (a : Array F) (ha : a.size = 2 ^ n)
    (r : Fin n → F) :
    MvPolynomial.eval r (arrayPolynomial a) = Concrete.mle a (Array.ofFn r) := by
  rw [arrayPolynomial_eq a ha, OODBounds.eval_mlePolynomial, mle_eq_cube a r ha]

theorem arrayPolynomial_degree {n : Nat} (a : Array F) (ha : a.size = 2 ^ n) :
    (arrayPolynomial (n := n) a).totalDegree ≤ n := by
  rw [arrayPolynomial_eq a ha]
  exact OODBounds.mlePolynomial_degree _

theorem arrayPolynomial_injective (n : Nat) :
    Function.Injective
      (fun a : {a : Array F // a.size = 2 ^ n} => arrayPolynomial (n := n) a.val) := by
  intro a b h
  change arrayPolynomial (n := n) a.val = arrayPolynomial (n := n) b.val at h
  rw [arrayPolynomial_eq a.val a.property, arrayPolynomial_eq b.val b.property] at h
  exact decode_injective n (OODBounds.mlePolynomial_injective n h)

variable [Fintype F] [DecidableEq F]

/-- Uniform coordinates sampled in array order collide with probability at most
`n / |F|`. The two arrays are fixed, distinct, and have the required exact size. -/
theorem mle_collision_probability {n : Nat} (a b : Array F)
    (ha : a.size = 2 ^ n) (hb : b.size = 2 ^ n) (hne : a ≠ b) :
    Soundness.uniformProb (Finset.univ.filter fun r : Fin n → F =>
      Concrete.mle a (Array.ofFn r) = Concrete.mle b (Array.ofFn r)) ≤
        (n : ℚ) / Fintype.card F := by
  classical
  simp_rw [mle_eq_cube a _ ha, mle_eq_cube b _ hb]
  apply OODBounds.mle_collision_probability
  intro h
  exact hne (congrArg Subtype.val (decode_injective n (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h))

/-- Commitment-fixed executable candidate arrays are separated except with
probability `choose L 2 * n / |F|`, with unordered pairs charged once.
The valid-size premise is local to the list and does not alter malformed-input
semantics of the executable evaluator. -/
theorem candidate_separation {n : Nat} (list : Finset (Array F))
    (valid : ∀ a ∈ list, a.size = 2 ^ n) :
    Soundness.uniformProb (Finset.univ.filter fun r : Fin n → F =>
      ∃ a ∈ list, ∃ b ∈ list, a ≠ b ∧
        Concrete.mle a (Array.ofFn r) = Concrete.mle b (Array.ofFn r)) ≤
      (list.card.choose 2 : ℚ) * ((n : ℚ) / Fintype.card F) := by
  classical
  have hinj : Set.InjOn (decode n) (↑list : Set (Array F)) := by
    intro a ha b hb he
    exact congrArg Subtype.val
      (decode_injective n (a₁ := ⟨a, valid a ha⟩) (a₂ := ⟨b, valid b hb⟩) he)
  have h := OODBounds.candidate_separation (list.image (decode n))
  have he : (Finset.univ.filter fun r : Fin n → F =>
      ∃ f ∈ list.image (decode n), ∃ g ∈ list.image (decode n),
        f ≠ g ∧ Whir.mle f r = Whir.mle g r) =
      (Finset.univ.filter fun r : Fin n → F =>
        ∃ a ∈ list, ∃ b ∈ list, a ≠ b ∧
          Concrete.mle a (Array.ofFn r) = Concrete.mle b (Array.ofFn r)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hne, he⟩
      exact ⟨a, ha, b, hb, fun h => hne (congrArg (decode n) h),
        by simpa only [mle_eq_cube a r (valid a ha), mle_eq_cube b r (valid b hb)] using he⟩
    · rintro ⟨a, ha, b, hb, hne, he⟩
      exact ⟨decode n a, ⟨a, ha, rfl⟩, decode n b, ⟨b, hb, rfl⟩,
        fun h => hne (hinj ha hb h),
        by simpa only [mle_eq_cube a r (valid a ha), mle_eq_cube b r (valid b hb)] using he⟩
  rw [Finset.card_image_of_injOn hinj] at h
  convert h using 1
  apply congrArg Soundness.uniformProb
  ext r
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using Finset.ext_iff.mp he.symm r

end Whir.ExecutableOOD
