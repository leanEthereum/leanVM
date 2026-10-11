import Whir.RingPCSGame
import Whir.ExecutableOOD

/-! Source stack selectors, with explicit alignment and slot guards.  These
are stronger than the original verifier's range-only point checks. -/
namespace Whir.SuccinctPointWeight
open scoped BigOperators
open ExecutableOOD
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

variable {R : Type*} [CommRing R]

def natMle (n : Nat) (f : Nat → R) (x : Fin n → R) : R :=
  Whir.mle (fun u => f (cubeIndex u)) x

def eqBits {n : Nat} (q : Nat) (x : Fin n → R) : R :=
  ∏ i, if q.testBit i.val then x i else 1 - x i

lemma natMle_succ {n : Nat} (f : Nat → R) (x : Fin (n+1) → R) :
    natMle (n+1) f x =
      (1-x 0) * natMle n (fun v => f (2*v)) (fun i => x i.succ) +
      x 0 * natMle n (fun v => f (2*v+1)) (fun i => x i.succ) := by
  have hx : x = Fin.cons (x 0) (fun i => x i.succ) := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  rw [hx]
  simp only [natMle, Whir.mle, innerProduct, sum_cube_succ, Whir.eqWeight_cons,
    cubeIndex_cons, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Fin.cons_zero, Fin.cons_succ, mul_assoc, ← Finset.mul_sum]

lemma cubeIndex_sum {n : Nat} (u : Cube n) :
    cubeIndex u = ∑ i : Fin n, 2^i.val * (if u i then 1 else 0) := by
  induction n with
  | zero => simp [cubeIndex]
  | succ n ih =>
    rw [cubeIndex, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    simp only [mul_right_comm (2^_) 2, ← Finset.sum_mul]
    omega

lemma cubeIndex_append {d h : Nat} (a : Cube d) (b : Cube h) :
    cubeIndex (Fin.addCases a b) = cubeIndex a + 2^d * cubeIndex b := by
  simp only [cubeIndex_sum, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    Fin.val_castAdd, Fin.val_natAdd, pow_add, mul_assoc, Finset.mul_sum]

lemma eqWeight_append {d h : Nat} (x : Fin d → R) (y : Fin h → R)
    (a : Cube d) (b : Cube h) :
    Whir.eqWeight (Fin.addCases x y) (Fin.addCases a b) =
      Whir.eqWeight x a * Whir.eqWeight y b := by
  simp [Whir.eqWeight, Fin.prod_univ_add]

def cubeAppendEquiv (d h : Nat) : Cube d × Cube h ≃ Cube (d+h) where
  toFun p := Fin.addCases p.1 p.2
  invFun u := (fun i => u (Fin.castAdd h i), fun i => u (Fin.natAdd d i))
  left_inv p := by rcases p with ⟨a,b⟩; simp
  right_inv u := by ext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp

lemma natMle_split {d h : Nat} (f : Nat → R) (x : Fin d → R) (y : Fin h → R) :
    natMle (d+h) f (Fin.addCases x y) =
      ∑ b : Cube h, Whir.eqWeight y b *
        natMle d (fun v => f (v + 2^d*cubeIndex b)) x := by
  unfold natMle Whir.mle innerProduct
  rw [← Equiv.sum_comp (cubeAppendEquiv d h)]
  simp only [Fintype.sum_prod_type, cubeAppendEquiv, Equiv.coe_fn_mk,
    eqWeight_append, cubeIndex_append]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma cubeIndex_testBit {n : Nat} (u : Cube n) (i : Fin n) :
    (cubeIndex u).testBit i.val = u i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have bits : cubeIndex u = Nat.bit (u 0) (cubeIndex (fun j : Fin n => u j.succ)) := by
      cases h : u 0 <;>
        simp only [cubeIndex, h, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
          Nat.bit_false_apply, Nat.bit_true_apply]
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [bits, Fin.val_zero] using Nat.testBit_bit_zero (u 0) (cubeIndex (fun j : Fin n => u j.succ))
    · simpa only [bits, Fin.val_succ, Nat.testBit_bit_succ] using ih (fun j : Fin n => u j.succ) j

lemma cubeIndex_injective (n : Nat) : Function.Injective (@cubeIndex n) := by
  intro a b equal
  funext i
  have h := congrArg (fun k => k.testBit i.val) equal
  simpa only [cubeIndex_testBit] using h

lemma eqBits_cubeIndex {n : Nat} (u : Cube n) (x : Fin n → R) :
    eqBits (cubeIndex u) x = Whir.eqWeight x u := by
  simp only [eqBits, cubeIndex_testBit, Whir.eqWeight]

def region (offset d : Nat) (f : Nat → R) (v : Nat) : R :=
  if offset ≤ v ∧ v < offset + 2^d then f (v-offset) else 0

lemma region_block {d : Nat} (q b a : Nat) (low : a < 2^d) (f : Nat → R) :
    region (2^d*q) d f (a+2^d*b) = if b=q then f a else 0 := by
  have positive : 0 < 2^d := by positivity
  have selected : 2^d*q ≤ a+2^d*b ∧ a+2^d*b < 2^d*q+2^d ↔ b=q := by
    constructor
    · intro selected
      rcases lt_trichotomy b q with below | equal | above
      · have h := Nat.mul_le_mul_left (2^d) (Nat.succ_le_of_lt below)
        nlinarith
      · exact equal
      · have h := Nat.mul_le_mul_left (2^d) (Nat.succ_le_of_lt above)
        nlinarith
    · rintro rfl
      omega
  simp only [region, selected]
  split
  · rename_i equal
    subst b
    simp
  · rfl

lemma alignedRegion_mle {d h : Nat} (q : Nat) (bound : q < 2^h)
    (f : Nat → R) (lo : Fin d → R) (hi : Fin h → R) :
    natMle (d+h) (region (2^d*q) d f) (Fin.addCases lo hi) =
      natMle d f lo * eqBits q hi := by
  obtain ⟨chosen,hchosen⟩ := cubeIndex_surjective q bound
  rw [natMle_split]
  have inner (b : Cube h) :
      natMle d (fun v => region (2^d*q) d f (v+2^d*cubeIndex b)) lo =
        if b=chosen then natMle d f lo else 0 := by
    unfold natMle
    by_cases equal : b=chosen
    · subst b
      simp only [hchosen, region_block _ _ _ (cubeIndex_lt _) _, ↓reduceIte]
    · have different : cubeIndex b ≠ q := by
        intro same
        exact equal (cubeIndex_injective h (same.trans hchosen.symm))
      simp only [region_block _ _ _ (cubeIndex_lt _) _, different, equal, ↓reduceIte,
        Whir.mle_const]
  simp_rw [inner]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← hchosen, eqBits_cubeIndex]
  exact mul_comm _ _

/-- No coordinate-length assumption is needed: a complete block fitting inside
the cube cannot have more coordinates than the cube. This uses unbounded natural
arithmetic, not unchecked Rust `usize` shifts or additions. -/
theorem dimension_le_of_block_bound (offset d n : Nat)
    (bounded : offset + 2^d ≤ 2^n) : d ≤ n := by
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    ((Nat.le_add_left (2^d) offset).trans bounded)

/-- The high selector fits in precisely the suffix coordinates consumed by
`eq_bits`; no high bits are silently discarded. -/
theorem selector_lt_of_block_bound (offset d n : Nat)
    (aligned : offset % 2^d = 0) (bounded : offset + 2^d ≤ 2^n) :
    offset >>> d < 2^(n-d) := by
  have dimension := dimension_le_of_block_bound offset d n bounded
  have positive : 0 < 2^d := by positivity
  have offset_eq : offset = 2^d*(offset/2^d) := by
    have h := Nat.mod_add_div offset (2^d)
    omega
  rw [show n = d + (n-d) by omega, pow_add, offset_eq] at bounded
  rw [Nat.shiftRight_eq_div_pow]
  nlinarith

/-- Arbitrary low-dimensional weights scatter onto an aligned dyadic region.
The arithmetic selector and full cube bound are proved, not bridge premises. -/
theorem region_mle {d h : Nat} (offset : Nat) (f : Nat → R)
    (lo : Fin d → R) (hi : Fin h → R)
    (aligned : offset % 2^d = 0) (bounded : offset+2^d ≤ 2^(d+h)) :
    natMle (d+h) (region offset d f) (Fin.addCases lo hi) =
      natMle d f lo * eqBits (offset/2^d) hi := by
  have offset_eq : offset = 2^d*(offset/2^d) := by
    have h := Nat.mod_add_div offset (2^d)
    omega
  have bound : offset/2^d < 2^h := by
    simpa only [Nat.shiftRight_eq_div_pow, Nat.add_sub_cancel_left] using
      selector_lt_of_block_bound offset d (d+h) aligned bounded
  conv_lhs => rw [offset_eq]
  exact alignedRegion_mle _ bound _ _ _

lemma mle_eqWeight [CharP R 2] {n : Nat} (point x : Fin n → R) :
    Whir.mle (Whir.eqWeight point) x = ∏ i, (1 + point i + x i) := by
  induction n with
  | zero => simp [Whir.mle, innerProduct, Whir.eqWeight, Cube]
  | succ n ih =>
    have hp : point = Fin.cons (point 0) (fun i => point i.succ) := by
      ext i; exact Fin.cases rfl (fun _ => rfl) i
    have hx : x = Fin.cons (x 0) (fun i => x i.succ) := by
      ext i; exact Fin.cases rfl (fun _ => rfl) i
    rw [hp, hx]
    unfold Whir.mle innerProduct
    rw [sum_cube_succ, Fin.prod_univ_succ]
    simp only [Whir.eqWeight_cons, Bool.false_eq_true, ↓reduceIte, Fin.cons_zero, Fin.cons_succ]
    have scalar (a b : R) :
        (∑ u : Cube n, (a * Whir.eqWeight (fun i => x i.succ) u) *
          (b * Whir.eqWeight (fun i => point i.succ) u)) =
        a*b*Whir.mle (Whir.eqWeight (fun i => point i.succ)) (fun i => x i.succ) := by
      unfold Whir.mle innerProduct
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [scalar, scalar, ← add_mul, ih]
    have coordinate : (1-x 0)*(1-point 0)+x 0*point 0 = 1+point 0+x 0 := by
      rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
      ring_nf
      simp [CharTwo.two_eq_zero]
    rw [coordinate]

theorem eqWeight_mle (point : Array Concrete.E) (lo : Fin point.size → Concrete.E) :
    natMle point.size (RingPCSGame.eqWeight point) lo = ∏ i, (1+point[i]+lo i) := by
  have decoded : (fun u : Cube point.size => RingPCSGame.eqWeight point (cubeIndex u)) =
      Whir.eqWeight (fun i => point[i]) := by
    funext u
    simp only [RingPCSGame.eqWeight, cubeIndex_testBit, Whir.eqWeight, CharTwo.sub_eq_add]
  unfold natMle
  rw [decoded, mle_eqWeight]
  simp

theorem mle_tab [Inhabited R] [CharP R 2] (n : Nat) (f : Nat → R) (x : Fin n → R) :
    Concrete.mle (Concrete.tab (2^n) f) (Array.ofFn x) = natMle n f x := by
  rw [mle_eq_cube _ _ (ArrayLayout.size_tab _ _)]
  unfold natMle
  congr 1
  funext u
  exact ArrayLayout.getElem!_tab _ _ _ (cubeIndex_lt u)

lemma natMle_delta {n : Nat} (q : Nat) (bound : q < 2^n) (value : R) (x : Fin n → R) :
    natMle n (fun v => if v=q then value else 0) x = eqBits q x * value := by
  obtain ⟨chosen,hchosen⟩ := cubeIndex_surjective q bound
  have select (u : Cube n) : cubeIndex u=q ↔ u=chosen :=
    ⟨fun h => cubeIndex_injective n (h.trans hchosen.symm),fun h => h ▸ hchosen⟩
  simp only [natMle, Whir.mle, innerProduct, select, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← hchosen, eqBits_cubeIndex]

def strideWeight (stride slot : Nat) (f : Nat → R) (v : Nat) : R :=
  if v % 2^stride = slot then f (v/2^stride) else 0

lemma strideWeight_block {s : Nat} (slot a b : Nat) (low : a < 2^s) (f : Nat → R) :
    strideWeight s slot f (a+2^s*b) = if a=slot then f b else 0 := by
  simp [strideWeight, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt low,
    Nat.add_mul_div_left, Nat.div_eq_of_lt low]

theorem strideWeight_mle {s d : Nat} (slot : Nat) (valid : slot < 2^s)
    (f : Nat → R) (low : Fin s → R) (point : Fin d → R) :
    natMle (s+d) (strideWeight s slot f) (Fin.addCases low point) =
      eqBits slot low * natMle d f point := by
  rw [natMle_split]
  have inner (b : Cube d) :
      natMle s (fun v => strideWeight s slot f (v+2^s*cubeIndex b)) low =
        eqBits slot low * f (cubeIndex b) := by
    have same : (fun u : Cube s => strideWeight s slot f (cubeIndex u+2^s*cubeIndex b)) =
        (fun u : Cube s => if cubeIndex u=slot then f (cubeIndex b) else 0) := by
      funext u
      exact strideWeight_block _ _ _ (cubeIndex_lt u) _
    unfold natMle
    rw [same]
    exact natMle_delta slot valid _ low
  simp_rw [inner]
  unfold natMle Whir.mle innerProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

lemma strided_region (offset slot stride : Nat) (point : Array Concrete.E) (value : Concrete.E) :
    RingPCSGame.pointWeight (.strided offset slot stride point value) =
      region offset (stride+point.size) (strideWeight stride slot (RingPCSGame.eqWeight point)) := by
  funext v
  have mod_le : (v-offset) % 2^stride ≤ v-offset := Nat.mod_le _ _
  unfold RingPCSGame.pointWeight region strideWeight
  by_cases bounds : offset ≤ v ∧ v < offset+2^(stride+point.size)
  · by_cases slotEq : (v-offset) % 2^stride = slot
    · have lower : offset+slot ≤ v := by omega
      simp only [bounds, slotEq, lower, and_self, ↓reduceIte]
    · simp [bounds, slotEq]
  · have impossible : ¬(offset+slot ≤ v ∧ v < offset+2^(stride+point.size) ∧
        (v-offset)%2^stride=slot) := by omega
    simp only [bounds, impossible, ↓reduceIte]

/-- Source `Arith::eq_eval` on one contiguous coordinate segment. -/
def eqEval (point x : Array Concrete.E) (start : Nat) : Concrete.E :=
  ∏ i : Fin point.size, (1+point[i]+x[start+i.val]!)

/-- Source `Arith::eq_bits`; coordinates are little-endian. -/
def eqBitsAt (selector : Nat) (x : Array Concrete.E) (start count : Nat) : Concrete.E :=
  ∏ i : Fin count, if selector.testBit i.val then x[start+i.val]! else 1+x[start+i.val]!

/-- The two products in `StackClaim::eq_at`, not a dense-table evaluator.
The shape predicate below rules out out-of-range coordinate slices. -/
def eqAt : RingPCSGame.PointClaim → Array Concrete.E → Concrete.E
  | .point offset point _, x =>
      eqEval point x 0 * eqBitsAt (offset >>> point.size) x point.size (x.size-point.size)
  | .strided offset slot stride point _, x =>
      (eqBitsAt slot x 0 stride * eqEval point x stride) *
        eqBitsAt (offset >>> (stride+point.size)) x (stride+point.size) (x.size-(stride+point.size))

/-- Exact dyadic selector guards. The block range already implies that every
coordinate slice used by `eqAt` is in bounds; dimension is not a separate premise. -/
def Shape (n : Nat) : RingPCSGame.PointClaim → Prop
  | .point offset point _ =>
      offset % 2^point.size = 0 ∧ offset+2^point.size ≤ 2^n
  | .strided offset slot stride point _ =>
      offset % 2^(stride+point.size) = 0 ∧
        offset+2^(stride+point.size) ≤ 2^n ∧ slot < 2^stride

theorem Shape.point_iff (n offset : Nat) (point : Array Concrete.E) (value : Concrete.E) :
    Shape n (.point offset point value) ↔
      point.size ≤ n ∧ offset % 2^point.size = 0 ∧ offset+2^point.size ≤ 2^n := by
  constructor
  · intro shape
    exact ⟨dimension_le_of_block_bound offset point.size n shape.2, shape⟩
  · exact fun shape => shape.2

theorem Shape.strided_iff (n offset slot stride : Nat)
    (point : Array Concrete.E) (value : Concrete.E) :
    Shape n (.strided offset slot stride point value) ↔
      stride+point.size ≤ n ∧ offset % 2^(stride+point.size) = 0 ∧
        offset+2^(stride+point.size) ≤ 2^n ∧ slot < 2^stride := by
  constructor
  · intro shape
    exact ⟨dimension_le_of_block_bound offset (stride+point.size) n shape.2.1, shape⟩
  · exact fun shape => shape.2

instance (n : Nat) (claim : RingPCSGame.PointClaim) : Decidable (Shape n claim) := by
  cases claim <;> unfold Shape <;> infer_instance

/-- Explicit additional source guards; the old range-only `check_statement`
does not imply this predicate. No occupied-lane count changes these selectors. -/
def check (n : Nat) (claim : RingPCSGame.PointClaim) : Bool := decide (Shape n claim)

theorem check_iff (n : Nat) (claim : RingPCSGame.PointClaim) :
    check n claim = true ↔ Shape n claim := by simp [check]

omit [CommRing R] in
lemma array_split_left [Inhabited R] {d h : Nat} (a : Fin d → R) (b : Fin h → R) (i : Fin d) :
    (Array.ofFn (Fin.addCases a b))[i.val]! = a i := by
  rw [getElem!_pos _ _ (by simp only [Array.size_ofFn]; omega), Array.getElem_ofFn]
  change Fin.addCases a b (Fin.castAdd h i) = a i
  exact Fin.addCases_left i

omit [CommRing R] in
lemma array_split_right [Inhabited R] {d h : Nat} (a : Fin d → R) (b : Fin h → R) (i : Fin h) :
    (Array.ofFn (Fin.addCases a b))[d+i.val]! = b i := by
  rw [getElem!_pos _ _ (by simp only [Array.size_ofFn]; omega), Array.getElem_ofFn]
  change Fin.addCases a b (Fin.natAdd d i) = b i
  exact Fin.addCases_right i

theorem eqAt_point_split {h : Nat} (offset : Nat) (point : Array Concrete.E) (value : Concrete.E)
    (lo : Fin point.size → Concrete.E) (hi : Fin h → Concrete.E) :
    eqAt (.point offset point value) (Array.ofFn (Fin.addCases lo hi)) =
      (∏ i, (1+point[i]+lo i)) * eqBits (offset/2^point.size) hi := by
  simp only [eqAt, Nat.shiftRight_eq_div_pow, Array.size_ofFn, Nat.add_sub_cancel_left]
  simp only [eqEval, eqBitsAt, Nat.zero_add, array_split_left, array_split_right,
    eqBits, CharTwo.sub_eq_add]
  simp

theorem eqAt_strided_split {s h : Nat} (offset slot : Nat) (point : Array Concrete.E)
    (value : Concrete.E) (low : Fin s → Concrete.E) (middle : Fin point.size → Concrete.E)
    (hi : Fin h → Concrete.E) :
    eqAt (.strided offset slot s point value) (Array.ofFn (Fin.addCases (Fin.addCases low middle) hi)) =
      (eqBits slot low * (∏ i, (1+point[i]+middle i))) * eqBits (offset/2^(s+point.size)) hi := by
  have getLow (i : Fin s) :
      (Array.ofFn (Fin.addCases (Fin.addCases low middle) hi))[i.val]! = low i := by
    have h := array_split_left (Fin.addCases low middle) hi (Fin.castAdd point.size i)
    simpa only [Fin.val_castAdd, Fin.addCases_left] using h
  have getMiddle (i : Fin point.size) :
      (Array.ofFn (Fin.addCases (Fin.addCases low middle) hi))[s+i.val]! = middle i := by
    have h := array_split_left (Fin.addCases low middle) hi (Fin.natAdd s i)
    simpa only [Fin.val_natAdd, Fin.addCases_right] using h
  simp only [eqAt, Nat.shiftRight_eq_div_pow, Array.size_ofFn, Nat.add_sub_cancel_left]
  simp only [eqEval, eqBitsAt, Nat.zero_add, getLow, getMiddle, array_split_right,
    eqBits, CharTwo.sub_eq_add]
  simp

theorem point_mle {h : Nat} (offset : Nat) (point : Array Concrete.E) (value : Concrete.E)
    (lo : Fin point.size → Concrete.E) (hi : Fin h → Concrete.E)
    (aligned : offset % 2^point.size = 0)
    (bounded : offset+2^point.size ≤ 2^(point.size+h)) :
    natMle (point.size+h) (RingPCSGame.pointWeight (.point offset point value)) (Fin.addCases lo hi) =
      eqAt (.point offset point value) (Array.ofFn (Fin.addCases lo hi)) := by
  change natMle _ (region offset point.size (RingPCSGame.eqWeight point)) _ = _
  rw [region_mle offset _ lo hi aligned bounded, eqWeight_mle, eqAt_point_split]

theorem strided_mle {s h : Nat} (offset slot : Nat) (point : Array Concrete.E) (value : Concrete.E)
    (low : Fin s → Concrete.E) (middle : Fin point.size → Concrete.E) (hi : Fin h → Concrete.E)
    (aligned : offset % 2^(s+point.size) = 0)
    (bounded : offset+2^(s+point.size) ≤ 2^(s+point.size+h)) (valid : slot < 2^s) :
    natMle (s+point.size+h) (RingPCSGame.pointWeight (.strided offset slot s point value))
      (Fin.addCases (Fin.addCases low middle) hi) =
      eqAt (.strided offset slot s point value) (Array.ofFn (Fin.addCases (Fin.addCases low middle) hi)) := by
  rw [strided_region, region_mle offset _ _ hi aligned bounded,
    strideWeight_mle slot valid, eqWeight_mle, eqAt_strided_split]

theorem eqAt_eq_natMle (n : Nat) (claim : RingPCSGame.PointClaim) (x : Fin n → Concrete.E)
    (shape : Shape n claim) :
    eqAt claim (Array.ofFn x) = natMle n (RingPCSGame.pointWeight claim) x := by
  cases claim with
  | point offset point value =>
    obtain ⟨dimension,aligned,bounded⟩ := (Shape.point_iff n offset point value).mp shape
    obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le dimension
    have split : x = Fin.addCases (fun i => x (Fin.castAdd h i)) (fun i => x (Fin.natAdd point.size i)) := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    rw [split]
    exact (point_mle offset point value _ _ aligned bounded).symm
  | strided offset slot stride point value =>
    obtain ⟨dimension,aligned,bounded,valid⟩ := (Shape.strided_iff n offset slot stride point value).mp shape
    obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le dimension
    let low : Fin stride → Concrete.E := fun i => x (Fin.castAdd h (Fin.castAdd point.size i))
    let middle : Fin point.size → Concrete.E := fun i => x (Fin.castAdd h (Fin.natAdd stride i))
    let hi : Fin h → Concrete.E := fun i => x (Fin.natAdd (stride+point.size) i)
    have split : x = Fin.addCases (Fin.addCases low middle) hi := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp [low,middle]
      · simp [hi]
    rw [split]
    exact (strided_mle offset slot point value low middle hi aligned bounded valid).symm

/-- Exact source selector versus the existing dense public claim evaluator. -/
theorem eqAt_eq_mle (claim : RingPCSGame.PointClaim) (x : Array Concrete.E)
    (shape : Shape x.size claim) :
    eqAt claim x = Concrete.mle (RingPCSGame.publicPoint (2^x.size) claim).weight x := by
  have h := eqAt_eq_natMle x.size claim (fun i => x[i]) shape
  rw [← mle_tab] at h
  have copied : (Array.ofFn (fun i : Fin x.size => x[i])) = x := by
    apply Array.ext
    · simp
    · intro i hi hj
      simp
  rw [copied] at h
  exact h

lemma dense_dot_comm (a b : Array Concrete.E) : Concrete.dot a b = Concrete.dot b a := by
  simp only [ArrayAlgebra.dot_eq_sum]
  rw [Nat.min_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma dense_dot_zero (width : Nat) (a : Array Concrete.E) :
    Concrete.dot (Concrete.tab width (fun _ => 0)) a = 0 := by
  simp only [ArrayAlgebra.dot_eq_sum, ArrayLayout.size_tab]
  apply Finset.sum_eq_zero
  intro i member
  have hi : i < width := lt_of_lt_of_le (Finset.mem_range.mp member) (Nat.min_le_left _ _)
  rw [ArrayLayout.getElem!_tab _ _ _ hi, zero_mul]

/-- Linearity of the actual imperative initial accumulator, derived from its
existing discrepancy refinement rather than replacing the accumulator. -/
theorem mle_batchClaims (claims : Array CausalGame.Claim) (lambda : Concrete.E) (x : Array Concrete.E)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2^x.size) :
    Concrete.mle (CausalGame.batchClaims (2^x.size) claims lambda).weight x =
      ∑ j ∈ Finset.range claims.size, lambda^j * Concrete.mle claims[j]!.weight x := by
  have hz := InitialBatching.batchClaims_discrepancy (Concrete.tab (2^x.size) (fun _ => 0)) claims lambda
    (by simpa only [ArrayLayout.size_tab] using shape)
  have hx := InitialBatching.batchClaims_discrepancy (Concrete.eqTable x) claims lambda
    (by simpa only [TerminalRefinement.size_eqTable] using shape)
  simp only [ArrayLayout.size_tab, InitialBatching.errorPolynomial_eval, InitialBatching.claimError,
    dense_dot_zero, zero_sub, mul_neg, Finset.sum_neg_distrib, neg_inj] at hz
  simp only [TerminalRefinement.size_eqTable, InitialBatching.errorPolynomial_eval,
    InitialBatching.claimError, mul_sub, Finset.sum_sub_distrib, hz] at hx
  have linear := congrArg (fun z => z + ∑ j ∈ Finset.range claims.size, lambda^j*claims[j]!.value) hx
  simp only [sub_add_cancel] at linear
  simpa only [Concrete.mle, dense_dot_comm] using linear

theorem mle_transformedClaims {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix)
    (lambda : Concrete.E) (x : Array Concrete.E) :
    Concrete.mle (CausalGame.batchClaims (2^x.size)
      (RingPCSGame.transformedClaims (2^x.size) family points seed) lambda).weight x =
      Concrete.mle (RingPCSGame.familyPublic (2^x.size) family seed).weight x +
        ∑ i : Fin points.size,
          lambda^(i.val+1)*Concrete.mle (RingPCSGame.publicPoint (2^x.size) points[i]).weight x := by
  rw [mle_batchClaims]
  · have size : (RingPCSGame.transformedClaims (2^x.size) family points seed).size = points.size+1 := by
      simp [Nat.add_comm]
    rw [size, Finset.sum_range_succ']
    have head : (RingPCSGame.transformedClaims (2^x.size) family points seed)[0]! =
        RingPCSGame.familyPublic (2^x.size) family seed := by
      simp [RingPCSGame.transformedClaims]
    rw [head, pow_zero, one_mul, add_comm, ← Fin.sum_univ_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have tail : (RingPCSGame.transformedClaims (2^x.size) family points seed)[i.val+1]! =
        RingPCSGame.publicPoint (2^x.size) points[i] := by
      rw [getElem!_pos _ _ (by simp; omega)]
      unfold RingPCSGame.transformedClaims
      rw [Array.getElem_append_right (by simp)]
      simp
    rw [tail]
  · intro j
    have member : (RingPCSGame.transformedClaims (2^x.size) family points seed)[j] ∈
        RingPCSGame.transformedClaims (2^x.size) family points seed := Array.getElem_mem j.isLt
    simp only [RingPCSGame.transformedClaims, Array.mem_append, Array.mem_singleton, Array.mem_map] at member
    rcases member with head | ⟨point,_,head⟩
    · have equal : (RingPCSGame.transformedClaims (2^x.size) family points seed)[j] =
          RingPCSGame.familyPublic (2^x.size) family seed := head
      rw [equal]
      simp [RingPCSGame.familyPublic]
    · have equal : (RingPCSGame.transformedClaims (2^x.size) family points seed)[j] =
          RingPCSGame.publicPoint (2^x.size) point := head.symm
      rw [equal]
      simp [RingPCSGame.publicPoint]

end Whir.SuccinctPointWeight
