import Whir.RingPCSGame
import Whir.RingMapSoundness
import Whir.SuccinctPointWeight

namespace Whir.SuccinctRingWeight
open Concrete RingPCSGame
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Repeated squaring, with the exact 192-bit extension-field period. -/
def inverseFrobenius (v : E) (k : Nat) : E :=
  if k = 0 then v else squareIter v (192 - k)

theorem squareIter_add (v : E) (a b : Nat) :
    squareIter (squareIter v a) b = squareIter v (a + b) := by
  simp only [squareIter_eq, ← pow_mul, ← Nat.pow_add]

theorem squareIter_period (v : E) : squareIter v 192 = v := by
  rw [squareIter_eq, ← FieldModel.card_E]
  exact FiniteField.pow_card v

theorem inverseFrobenius_cancel (v : E) (k : Nat) (hk : k ≤ 192) :
    squareIter (inverseFrobenius v k) k = v := by
  unfold inverseFrobenius
  split_ifs with h
  · subst k; rfl
  · rw [squareIter_add, Nat.sub_add_cancel hk, squareIter_period]

/-- The source initializes every slot with v, and overwrites slots 63 down to
max(lowest,1), starting at v^(2^128). This recursive loop keeps that order. -/
def ladderLoop (v : E) (lowest : Nat) : Nat → E → List E
  | 0, _ => []
  | n + 1, power =>
    if lowest ≤ n then
      let next := power * power
      ladderLoop v lowest n next ++ [next]
    else List.replicate (n + 1) v

def inverseFrobeniusLadder (v : E) (lowest : Nat) : List E :=
  ladderLoop v (max lowest 1) 64 (squareIter v 128)

/-- Linearized Horner closure; unlike a field-linear dot product its squarings
also apply to the claim's gamma scaling. -/
def close : List E → E
  | [] => 0
  | t :: ts => t + squareIter (close ts) 1

theorem close_eq (ts : List E) :
    close ts = (ts.zipIdx.map fun (t, k) => squareIter t k).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [close, List.zipIdx_cons', List.map_cons, List.sum_cons, ih]
    congr 1
    simp only [squareIter_eq, List.map_map, list_sum_pow_char_pow]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ⟨a,k⟩ _
    simp only [Function.comp_apply, Prod.map, id_eq, Nat.pow_add, pow_mul, pow_one]

def prefixTerm (coefficients : Fin 64 → E) (z q : List E) (k : Fin 64) : E :=
  coefficients k * ((z.zip q).map fun (zn, qn) =>
    1 + zn + inverseFrobenius qn k.val).prod

/-- Unshared prefix evaluator, the semantic value of each source take slot. -/
def prefixTerms (coefficients : Fin 64 → E) (z q : List E)
    (lengths : List Nat) : List (Fin 64 → E) :=
  lengths.map fun n => prefixTerm coefficients (z.take n) (q.take n)

/-- Six-stage coefficient prefix extension, in the source append order. -/
def extendCoefficients (f : E) (shift : Nat) (prefixes : List (Nat × E)) : List (Nat × E) :=
  prefixes ++ prefixes.map fun (k, c) =>
    (k + shift, c * inverseFrobenius f (k + shift))

def newCoefficients (challenges : Fin 6 → E) : List (Nat × E) :=
  (List.finRange 6).foldl (fun ps p =>
    extendCoefficients (challenges p) (2 ^ (5 - p.val)) ps) [(0, 1)]

def evaluateCoefficients (ps : List (Nat × E)) (a : E) : E :=
  (ps.map fun (k, c) => squareIter (c * a) k).sum

theorem evaluate_extend (ps : List (Nat × E)) (f a : E) (s : Nat)
    (bound : ∀ t ∈ ps, t.1 + s ≤ 192) :
    evaluateCoefficients (extendCoefficients f s ps) a =
      mapStage f s (evaluateCoefficients ps a) := by
  simp only [evaluateCoefficients, extendCoefficients, List.map_append,
    List.sum_append, List.map_map, mapStage, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1
  simp only [squareIter_eq, list_sum_pow_char_pow, List.map_map]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  obtain ⟨k, c⟩ := t
  have hc := inverseFrobenius_cancel f (k + s) (bound (k, c) ht)
  simp only [squareIter_eq] at hc
  simp only [Function.comp_apply,mul_pow]
  rw [hc]
  simp only [Nat.pow_add,pow_mul]
  ring

theorem extend_bound (ps : List (Nat × E)) (f : E) (s b : Nat)
    (bound : ∀ t ∈ ps, t.1 ≤ b) :
    ∀ t ∈ extendCoefficients f s ps, t.1 ≤ b + s := by
  intro t ht
  simp only [extendCoefficients, List.mem_append, List.mem_map] at ht
  rcases ht with ht | ⟨u, hu, rfl⟩
  · exact (bound t ht).trans (Nat.le_add_right b s)
  · exact Nat.add_le_add_right (bound u hu) s

private theorem fold_evaluate (stages : List (E × Nat)) (ps : List (Nat × E))
    (a : E) (b : Nat) (bound : ∀ t ∈ ps, t.1 ≤ b)
    (budget : b + (stages.map Prod.snd).sum ≤ 192) :
    evaluateCoefficients
      (stages.foldl (fun acc fs => extendCoefficients fs.1 fs.2 acc) ps) a =
    stages.foldl (fun acc fs => mapStage fs.1 fs.2 acc) (evaluateCoefficients ps a) := by
  induction stages generalizing ps b with
  | nil => rfl
  | cons fs stages ih =>
    simp only [List.map_cons, List.sum_cons] at budget
    simp only [List.foldl_cons]
    rw [ih _ (b + fs.2) (extend_bound ps fs.1 fs.2 b bound) (by omega)]
    rw [evaluate_extend ps fs.1 a fs.2 (by intro t ht; have := bound t ht; omega)]

theorem newCoefficients_evaluate (f : Fin 6 → E) (a : E) :
    evaluateCoefficients (newCoefficients f) a = executableMap f a := by
  let stages := (List.finRange 6).map fun p => (f p, 2 ^ (5 - p.val))
  have h := fold_evaluate stages [(0, 1)] a 0 (by simp)
    (by
      change 0 + ((List.finRange 6).map (fun p => 2 ^ (5-p.val))).sum ≤ 192
      decide +kernel)
  simp only [stages, List.foldl_map, evaluateCoefficients, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, squareIter, one_mul, add_zero] at h
  rw [executableMap_eq, RingSwitch.composedMap, RingMapSoundness.fold_apply]
  simpa only [newCoefficients,evaluateCoefficients,AddMonoidHom.id_apply,mapStage_eq] using h

theorem ladderLoop_eq (v : E) (lowest n : Nat) (power : E) :
    ladderLoop v lowest n power =
      (List.range n).map (fun k => if lowest ≤ k then squareIter power (n-k) else v) := by
  induction n generalizing power with
  | zero => rfl
  | succ n ih =>
    by_cases reaches : lowest ≤ n
    · simp only [ladderLoop,reaches,↓reduceIte]
      rw [ih,List.range_succ,List.map_append,List.map_singleton]
      have last : (if lowest ≤ n then squareIter power (n+1-n) else v) = power * power := by
        simp [reaches,squareIter]
      rw [last]
      congr 1
      apply List.map_congr_left
      intro k member
      have hk : k < n := List.mem_range.mp member
      by_cases active : lowest ≤ k
      · simp only [active,↓reduceIte]
        change squareIter (squareIter power 1) (n-k) = squareIter power (n+1-k)
        rw [squareIter_add]
        congr 1
        omega
      · simp only [active,↓reduceIte]
    · rw [ladderLoop,ite_eq_right reaches]
      calc
        List.replicate (n+1) v = (List.range (n+1)).map (fun _ => v) := by simp
        _ = _ := by
          apply List.map_congr_left
          intro k member
          have hk := List.mem_range.mp member
          have inactive : ¬ lowest ≤ k := by omega
          simp [inactive]

theorem inverseFrobeniusLadder_length (v : E) (lowest : Nat) :
    (inverseFrobeniusLadder v lowest).length = 64 := by
  simp [inverseFrobeniusLadder,ladderLoop_eq]

theorem inverseFrobeniusLadder_get (v : E) (lowest : Nat) (k : Fin 64) :
    (inverseFrobeniusLadder v lowest)[k.val]'(by
      simpa only [inverseFrobeniusLadder_length] using k.isLt) =
      if max lowest 1 ≤ k.val then inverseFrobenius v k.val else v := by
  simp only [inverseFrobeniusLadder,ladderLoop_eq,List.getElem_map,List.getElem_range]
  split_ifs with active
  · have positive : k.val ≠ 0 := by omega
    rw [squareIter_add,inverseFrobenius,ite_eq_right positive]
    congr 1
    omega
  · rfl

/-- The source stores each generated term at its Frobenius index. -/
def coefficientArray (f : Fin 6 → E) : Array E :=
  (newCoefficients f).foldl (fun out term => out.set! term.1 term.2) (Array.replicate 64 1)


def reverseIndexFn (k : Fin 64) : Fin 64 :=
  ⟨k.val % 2 * 32 + k.val / 2 % 2 * 16 + k.val / 4 % 2 * 8 +
    k.val / 8 % 2 * 4 + k.val / 16 % 2 * 2 + k.val / 32, by omega⟩

theorem reverseIndex_involutive : Function.Involutive reverseIndexFn := by
  change ∀ k : Fin 64, reverseIndexFn (reverseIndexFn k) = k
  decide +kernel

def reverseIndex : Fin 64 ≃ Fin 64 where
  toFun := reverseIndexFn
  invFun := reverseIndexFn
  left_inv := reverseIndex_involutive
  right_inv := reverseIndex_involutive
def coefficientIndices : List Nat :=
  (List.finRange 6).foldl (fun ps p => ps ++ ps.map (fun k => k + 2 ^ (5-p.val))) [0]

theorem coefficientIndices_eq :
    coefficientIndices = List.ofFn (fun i : Fin 64 => (reverseIndex i).val) := by decide +kernel

theorem newCoefficients_keys (f : Fin 6 → E) :
    (newCoefficients f).map Prod.fst = coefficientIndices := by
  have foldKeys (stages : List (Fin 6)) (ps : List (Nat × E)) :
      (stages.foldl (fun acc p => extendCoefficients (f p) (2^(5-p.val)) acc) ps).map Prod.fst =
      stages.foldl (fun acc p => acc ++ acc.map (fun k => k + 2^(5-p.val))) (ps.map Prod.fst) := by
    induction stages generalizing ps with
    | nil => rfl
    | cons p stages ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [extendCoefficients,List.map_append,List.map_map]
      rfl
  exact foldKeys _ _

theorem newCoefficients_length (f : Fin 6 → E) : (newCoefficients f).length = 64 := by
  have h := congrArg List.length (newCoefficients_keys f)
  simpa only [List.length_map,coefficientIndices_eq,List.length_ofFn] using h

/-- Bit reversal is the generated append order, not a different coefficient map. -/
def coefficients (f : Fin 6 → E) (k : Fin 64) : E :=
  ((newCoefficients f)[(reverseIndex k).val]'(by
    simpa only [newCoefficients_length] using (reverseIndex k).isLt)).2

theorem newCoefficients_key (f : Fin 6 → E) (i : Fin 64) :
    ((newCoefficients f)[i.val]'(by simpa only [newCoefficients_length] using i.isLt)).1 =
      (reverseIndex i).val := by
  have h := congrArg (fun xs : List Nat => xs[i.val]!) (newCoefficients_keys f)
  have hi : i.val < (newCoefficients f).length := by
    simpa only [newCoefficients_length] using i.isLt
  simpa only [coefficientIndices_eq,getElem!_pos, List.length_map,
    List.length_ofFn,List.getElem_map,List.getElem_ofFn,hi,i.isLt] using h


theorem newCoefficients_ofFn (f : Fin 6 → E) :
    newCoefficients f =
      List.ofFn (fun i : Fin 64 => ((reverseIndex i).val,coefficients f (reverseIndex i))) := by
  apply List.ext_getElem
  · simp only [newCoefficients_length,List.length_ofFn]
  · intro i hi _
    have bound : i < 64 := by simpa only [newCoefficients_length] using hi
    simp only [List.getElem_ofFn]
    apply Prod.ext
    · exact newCoefficients_key f ⟨i,bound⟩
    · have rev (k : Fin 64) : reverseIndex (reverseIndex k) = k := reverseIndex_involutive k
      simp only [coefficients,rev]

theorem coefficients_evaluate (f : Fin 6 → E) (a : E) :
    (∑ k : Fin 64, squareIter (coefficients f k * a) k.val) = executableMap f a := by
  rw [← newCoefficients_evaluate,newCoefficients_ofFn,evaluateCoefficients]
  simp only [List.map_ofFn,List.sum_ofFn]
  exact (Equiv.sum_comp reverseIndex (fun k => squareIter (coefficients f k * a) k.val)).symm

theorem squareIter_eqWeight {n : Nat} (z : Fin n → E) (u : Cube n) (k : Nat) :
    squareIter (Whir.eqWeight z u) k = Whir.eqWeight (fun i => squareIter (z i) k) u := by
  simp only [squareIter_eq,Whir.eqWeight,← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp [sub_pow_char_pow]

theorem squareIter_prefix {n : Nat} (a : E) (z q : Fin n → E) (k : Nat) (hk : k ≤ 192) :
    squareIter (a * ∏ i, (1 + z i + inverseFrobenius (q i) k)) k =
      squareIter a k * ∏ i, (1 + squareIter (z i) k + q i) := by
  have cancel (i : Fin n) := inverseFrobenius_cancel (q i) k hk
  simp only [squareIter_eq] at cancel ⊢
  simp only [mul_pow,← Finset.prod_pow,add_pow_char_pow,one_pow,cancel]

theorem mle_square_eqWeight {n : Nat} (a : E) (z q : Fin n → E) (k : Nat) (hk : k ≤ 192) :
    Whir.mle (fun u => squareIter (a * Whir.eqWeight z u) k) q =
      squareIter (a * ∏ i, (1 + z i + inverseFrobenius (q i) k)) k := by
  rw [squareIter_prefix a z q k hk]
  simp only [Whir.mle,innerProduct,squareIter_eq,mul_pow]
  have eqw (u : Cube n) := squareIter_eqWeight z u k
  simp only [squareIter_eq] at eqw
  simp_rw [eqw]
  have value := SuccinctPointWeight.mle_eqWeight (fun i => (z i) ^ (2^k)) q
  change (∑ u, Whir.eqWeight q u * (a ^ (2^k) *
      Whir.eqWeight (fun i => (z i) ^ (2^k)) u)) = _
  rw [show (∑ u, Whir.eqWeight q u * (a ^ (2^k) *
      Whir.eqWeight (fun i => (z i) ^ (2^k)) u)) =
      a ^ (2^k) * Whir.mle (Whir.eqWeight (fun i => (z i) ^ (2^k))) q by
    simp only [Whir.mle,innerProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring]
  rw [value]

theorem prefixTerm_ofFn {n : Nat} (cs : Fin 64 → E) (z q : Fin n → E) (k : Fin 64) :
    prefixTerm cs (List.ofFn z) (List.ofFn q) k =
      cs k * ∏ i, (1 + z i + inverseFrobenius (q i) k.val) := by
  have zipped : (List.ofFn z).zip (List.ofFn q) = List.ofFn (fun i => (z i,q i)) := by
    apply List.ext_getElem <;> simp
  simp only [prefixTerm,zipped,List.map_ofFn,List.prod_ofFn,Function.comp_apply]

/-- Every gamma power remains inside the Frobenius closure. -/
theorem map_eqWeight_mle {n : Nat} (f : Fin 6 → E) (gamma : E) (z q : Fin n → E) :
    Whir.mle (fun u => executableMap f (gamma * Whir.eqWeight z u)) q =
      ∑ k : Fin 64, squareIter
        (gamma * prefixTerm (coefficients f) (List.ofFn z) (List.ofFn q) k) k.val := by
  simp_rw [← coefficients_evaluate]
  simp only [Whir.mle,innerProduct,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have h := mle_square_eqWeight (coefficients f k * gamma) z q k.val (by omega)
  rw [prefixTerm_ofFn]
  simpa only [Whir.mle,innerProduct,mul_assoc,mul_left_comm,mul_comm] using h

theorem ring_eqWeight_cube (point : Array E) (u : Cube point.size) :
    RingPCSGame.eqWeight point (ExecutableOOD.cubeIndex u) = Whir.eqWeight (fun i => point[i]) u := by
  simp only [RingPCSGame.eqWeight,Whir.eqWeight,SuccinctPointWeight.cubeIndex_testBit,
    CharTwo.sub_eq_add]

theorem map_region_low_mle (f : Fin 6 → E) (gamma : E) (point : Array E)
    (q : Fin point.size → E) :
    SuccinctPointWeight.natMle point.size
        (fun v => executableMap f (gamma * RingPCSGame.eqWeight point v)) q =
      ∑ k : Fin 64, squareIter
        (gamma * prefixTerm (coefficients f) point.toList (List.ofFn q) k) k.val := by
  unfold SuccinctPointWeight.natMle
  simp_rw [ring_eqWeight_cube]
  have pointList : point.toList = List.ofFn (fun i : Fin point.size => point[i]) := by
    apply List.ext_getElem <;> simp
  rw [pointList]
  exact map_eqWeight_mle f gamma _ q

theorem close_ofFn {n : Nat} (terms : Fin n → E) :
    close (List.ofFn terms) = ∑ k : Fin n, squareIter (terms k) k.val := by
  rw [close_eq]
  have zipped : (List.ofFn terms).zipIdx = List.ofFn (fun i => (terms i,i.val)) := by
    apply List.ext_getElem <;> simp
  simp only [zipped,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

def claimWeightAt (cs : Fin 64 → E) (gamma : E) (claim : FamilyClaim) (x : Array E) : E :=
  SuccinctPointWeight.eqBitsAt (claim.offset / 2^claim.point.size) x
      claim.point.size (x.size-claim.point.size) *
    close (List.ofFn (fun k : Fin 64 => gamma *
      prefixTerm cs claim.point.toList (List.ofFn (fun i : Fin claim.point.size => x[i.val]!)) k))

def FamilyShape (n : Nat) {m : Nat} (family : Fin m → FamilyClaim) : Prop :=
  ∀ j, (family j).point.size ≤ n ∧
    (family j).offset % 2^(family j).point.size = 0 ∧
    (family j).offset + 2^(family j).point.size ≤ 2^n

theorem mapped_region (f : Fin 6 → E) (gamma : E) (claim : FamilyClaim) :
    (fun v => executableMap f (gamma * regionWeight claim.offset claim.point v)) =
      SuccinctPointWeight.region claim.offset claim.point.size
        (fun v => executableMap f (gamma * RingPCSGame.eqWeight claim.point v)) := by
  funext v
  simp only [regionWeight,SuccinctPointWeight.region]
  split_ifs <;> simp

theorem claimWeightAt_split (f : Fin 6 → E) (gamma : E) (claim : FamilyClaim)
    {h : Nat} (lo : Fin claim.point.size → E) (hi : Fin h → E)
    (aligned : claim.offset % 2^claim.point.size = 0)
    (bounded : claim.offset + 2^claim.point.size ≤ 2^(claim.point.size+h)) :
    claimWeightAt (coefficients f) gamma claim (Array.ofFn (Fin.addCases lo hi)) =
      SuccinctPointWeight.natMle (claim.point.size+h)
        (fun v => executableMap f (gamma * regionWeight claim.offset claim.point v))
        (Fin.addCases lo hi) := by
  rw [mapped_region,SuccinctPointWeight.region_mle _ _ _ _ aligned bounded,
    map_region_low_mle]
  simp only [claimWeightAt,Array.size_ofFn,Nat.add_sub_cancel_left]
  simp only [SuccinctPointWeight.eqBitsAt,SuccinctPointWeight.array_split_right,
    SuccinctPointWeight.array_split_left,close_ofFn,SuccinctPointWeight.eqBits,CharTwo.sub_eq_add]
  exact mul_comm _ _

theorem claimWeightAt_eq_natMle (n : Nat) (f : Fin 6 → E) (gamma : E) (claim : FamilyClaim)
    (x : Fin n → E) (dimension : claim.point.size ≤ n)
    (aligned : claim.offset % 2^claim.point.size = 0)
    (bounded : claim.offset + 2^claim.point.size ≤ 2^n) :
    claimWeightAt (coefficients f) gamma claim (Array.ofFn x) =
      SuccinctPointWeight.natMle n
        (fun v => executableMap f (gamma * regionWeight claim.offset claim.point v)) x := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_add_of_le dimension
  have split : x = Fin.addCases (fun i => x (Fin.castAdd h i))
      (fun i => x (Fin.natAdd claim.point.size i)) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [split]
  exact claimWeightAt_split _ _ _ _ _ aligned bounded

def ringWeightAt {m : Nat} (family : Fin m → FamilyClaim) (seed : Prefix) (x : Array E) : E :=
  ∑ j, claimWeightAt (coefficients seed.2) (seed.1 ^ j.val) (family j) x

theorem ringWeightAt_eq_natMle {m n : Nat} (family : Fin m → FamilyClaim) (seed : Prefix)
    (x : Fin n → E) (shape : FamilyShape n family) :
    ringWeightAt family seed (Array.ofFn x) = SuccinctPointWeight.natMle n (transparentWeight family seed) x := by
  unfold ringWeightAt
  simp_rw [claimWeightAt_eq_natMle n _ _ _ x (shape _).1 (shape _).2.1 (shape _).2.2]
  simp only [SuccinctPointWeight.natMle,transparentWeight,Whir.mle,innerProduct,Finset.mul_sum]
  exact Finset.sum_comm

theorem ringWeightAt_eq_mle {m : Nat} (family : Fin m → FamilyClaim) (seed : Prefix)
    (x : Array E) (shape : FamilyShape x.size family) :
    ringWeightAt family seed x = Concrete.mle (familyPublic (2^x.size) family seed).weight x := by
  have h := ringWeightAt_eq_natMle family seed (fun i => x[i]) shape
  rw [← SuccinctPointWeight.mle_tab] at h
  have copied : Array.ofFn (fun i : Fin x.size => x[i]) = x := by
    apply Array.ext <;> simp
  rw [copied] at h
  exact h

def stackWeightAt {m : Nat} (family : Fin m → FamilyClaim) (points : Array PointClaim)
    (seed : Prefix) (lambda : E) (x : Array E) : E :=
  ringWeightAt family seed x +
    ∑ i : Fin points.size, lambda^(i.val+1) * SuccinctPointWeight.eqAt points[i] x

/-- The original source terminal caller formula, including family power zero
and every subsequent point power, equals the actual dense initial batch MLE. -/
theorem stackWeightAt_eq_batch_mle {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (seed : Prefix) (lambda : E) (x : Array E)
    (familyShape : FamilyShape x.size family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape x.size points[i]) :
    stackWeightAt family points seed lambda x =
      Concrete.mle (CausalGame.batchClaims (2^x.size)
        (transformedClaims (2^x.size) family points seed) lambda).weight x := by
  rw [SuccinctPointWeight.mle_transformedClaims]
  unfold stackWeightAt
  rw [ringWeightAt_eq_mle family seed x familyShape]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [SuccinctPointWeight.eqAt_eq_mle _ x (pointShapes i)]

end Whir.SuccinctRingWeight
