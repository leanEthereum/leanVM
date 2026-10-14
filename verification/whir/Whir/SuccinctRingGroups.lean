import Whir.SuccinctRingCoefficients

namespace Whir.SuccinctRingGroups
open Concrete RingPCSGame SuccinctRingWeight
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

/-- One multiplication per coordinate and Frobenius slot. Retaining every
prefix is equivalent to the source's take slots, including duplicate lengths. -/
def prefixScan (cs : Fin 64 → E) : List (E × E) → List (Fin 64 → E)
  | [] => [cs]
  | pair :: rest => cs :: prefixScan (fun k => cs k * (1+pair.1+inverseFrobenius pair.2 k.val)) rest

theorem prefixScan_length (cs : Fin 64 → E) (pairs : List (E × E)) :
    (prefixScan cs pairs).length = pairs.length+1 := by
  induction pairs generalizing cs with
  | nil => rfl
  | cons pair rest ih => simp [prefixScan,ih]

theorem prefixScan_get (cs : Fin 64 → E) (pairs : List (E × E)) (n : Nat)
    (bound : n ≤ pairs.length) :
    (prefixScan cs pairs)[n]'(by rw [prefixScan_length]; omega) =
      fun k => cs k * ((pairs.take n).map (fun pair => 1+pair.1+inverseFrobenius pair.2 k.val)).prod := by
  induction n generalizing cs pairs with
  | zero => cases pairs <;> simp [prefixScan]
  | succ n ih =>
    cases pairs with
    | nil => simp at bound
    | cons pair rest =>
      simp only [prefixScan,List.getElem_cons_succ,List.take_succ_cons,List.map_cons,List.prod_cons]
      rw [ih _ rest (by simpa using bound)]
      funext k
      exact mul_assoc _ _ _

theorem prefixScan_lookup (cs : Fin 64 → E) (z q : List E) (n : Nat)
    (hz : n ≤ z.length) (hq : n ≤ q.length) :
    (prefixScan cs (z.zip q))[n]! = prefixTerm cs (z.take n) (q.take n) := by
  have bound : n ≤ (z.zip q).length := by simp; omega
  rw [getElem!_pos _ _ (by rw [prefixScan_length]; omega),prefixScan_get cs _ n bound]
  have zipped : (z.zip q).take n = (z.take n).zip (q.take n) := by
    clear hz hq bound
    induction n generalizing z q with
    | zero => simp
    | succ n ih => cases z <;> cases q <;> simp [ih]
  funext k
  simp only [zipped,prefixTerm]

/-- Actual source prefix compatibility, established by the insertion test.
No coverage or membership correctness premise is supplied by a caller. -/
structure PrefixGroup {m : Nat} (family : Fin m → FamilyClaim) where
  lead : List E
  members : List (Fin m)
  compatible : ∀ j ∈ members, (family j).point.toList = lead.take (family j).point.size

def insertGroup {m : Nat} (family : Fin m → FamilyClaim) (j : Fin m) :
    List (PrefixGroup family) → List (PrefixGroup family)
  | [] => [⟨(family j).point.toList,[j],by
      intro i member
      have same : i=j := by simpa using member
      subst i
      simp⟩]
  | g :: rest =>
    if fits : (family j).point.toList = g.lead.take (family j).point.size then
      ⟨g.lead,g.members++[j],by
        intro i member
        rcases List.mem_append.mp member with old | fresh
        · exact g.compatible i old
        · have same : i=j := by simpa using fresh
          subst i
          exact fits⟩ :: rest
    else g :: insertGroup family j rest

/-- Longest first, as in PrefixGroup::of. Equal-length ties do not affect the
proved semantics or the original claim indices used for gamma powers. -/
def prefixGroups {m : Nat} (family : Fin m → FamilyClaim) : List (PrefixGroup family) :=
  ((List.finRange m).mergeSort (fun i j => decide ((family j).point.size ≤ (family i).point.size))).foldl
    (fun groups j => insertGroup family j groups) []

def memberSum {m : Nat} {family : Fin m → FamilyClaim} (weight : Fin m → E)
    (groups : List (PrefixGroup family)) : E :=
  (groups.map (fun g => (g.members.map weight).sum)).sum

theorem insertGroup_sum {m : Nat} (family : Fin m → FamilyClaim) (weight : Fin m → E)
    (j : Fin m) (groups : List (PrefixGroup family)) :
    memberSum weight (insertGroup family j groups) = weight j + memberSum weight groups := by
  induction groups with
  | nil => simp [insertGroup,memberSum]
  | cons g rest ih =>
    simp only [insertGroup]
    split
    · simp only [memberSum,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
        List.map_nil,List.sum_nil,add_zero]
      abel
    · change (g.members.map weight).sum + memberSum weight (insertGroup family j rest) = _
      rw [ih]
      simp only [memberSum,List.map_cons,List.sum_cons]
      abel

theorem prefixGroups_sum {m : Nat} (family : Fin m → FamilyClaim) (weight : Fin m → E) :
    memberSum weight (prefixGroups family) = ∑ j, weight j := by
  have foldSum (js : List (Fin m)) (groups : List (PrefixGroup family)) :
      memberSum weight (js.foldl (fun groups j => insertGroup family j groups) groups) =
        (js.map weight).sum + memberSum weight groups := by
    induction js generalizing groups with
    | nil => simp
    | cons j js ih =>
      rw [List.foldl_cons,ih,insertGroup_sum]
      simp only [List.map_cons,List.sum_cons]
      abel
  unfold prefixGroups
  rw [foldSum]
  simp only [memberSum,List.map_nil,List.sum_nil,add_zero]
  rw [((List.mergeSort_perm (List.finRange m)
    (fun i j => decide ((family j).point.size ≤ (family i).point.size))).map weight).sum_eq]
  simp [List.finRange,List.sum_ofFn]

def groupWeight {m : Nat} {family : Fin m → FamilyClaim} (cs : Fin 64 → E)
    (gamma : E) (x : Array E) (group : PrefixGroup family) : E :=
  let cached := prefixScan cs (group.lead.zip x.toList)
  (group.members.map (fun j =>
    SuccinctPointWeight.eqBitsAt ((family j).offset / 2^(family j).point.size) x
        (family j).point.size (x.size-(family j).point.size) *
      close (List.ofFn (fun k : Fin 64 => gamma^j.val * (cached[(family j).point.size]!) k)))).sum

theorem take_query (x : Array E) (n : Nat) (bound : n ≤ x.size) :
    x.toList.take n = List.ofFn (fun i : Fin n => x[i.val]!) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left bound]
  · intro i hi hj
    have hn : i < n := by simpa using hj
    have hx : i < x.size := lt_of_lt_of_le hn bound
    simp [getElem!_pos,hx]

theorem groupWeight_eq {m : Nat} (family : Fin m → FamilyClaim) (cs : Fin 64 → E)
    (gamma : E) (x : Array E) (shape : ∀ j, (family j).point.size ≤ x.size)
    (group : PrefixGroup family) :
    groupWeight cs gamma x group =
      (group.members.map (fun j => claimWeightAt cs (gamma^j.val) (family j) x)).sum := by
  unfold groupWeight
  apply congrArg List.sum
  apply List.map_congr_left
  intro j member
  have fits := group.compatible j member
  have length := congrArg List.length fits
  have hz : (family j).point.size ≤ group.lead.length := by
    simp only [Array.length_toList,List.length_take] at length
    omega
  have hq : (family j).point.size ≤ x.toList.length := by simpa using shape j
  rw [prefixScan_lookup cs _ _ _ hz hq,← fits,take_query x _ (shape j)]
  rfl

/-- Executable grouping covers every original claim exactly once in every
additive observation. Its shared-prefix cache then computes the same terms. -/
def sourceRingWeightAt {m : Nat} (family : Fin m → FamilyClaim) (seed : Prefix) (x : Array E) : E :=
  let cs := SuccinctRingCoefficients.sourceCoefficientArray seed.2
  ((prefixGroups family).map (groupWeight (fun k => cs[k.val]!) seed.1 x)).sum

theorem sourceRingWeightAt_eq {m : Nat} (family : Fin m → FamilyClaim) (seed : Prefix)
    (x : Array E) (shape : ∀ j, (family j).point.size ≤ x.size) :
    sourceRingWeightAt family seed x = ringWeightAt family seed x := by
  unfold sourceRingWeightAt
  have stored : (fun k : Fin 64 => (SuccinctRingCoefficients.sourceCoefficientArray seed.2)[k.val]!) =
      coefficients seed.2 := funext (SuccinctRingCoefficients.sourceCoefficientArray_get seed.2)
  dsimp only
  rw [stored]
  calc
    _ = memberSum (fun j => claimWeightAt (coefficients seed.2) (seed.1^j.val) (family j) x)
        (prefixGroups family) := by
      unfold memberSum
      apply congrArg List.sum
      apply List.map_congr_left
      intro group _
      exact groupWeight_eq family _ _ x shape group
    _ = _ := prefixGroups_sum family _

/-- The source may add all terms of one region before a single close. -/
theorem close_sum {m : Nat} (terms : Fin m → Fin 64 → E) :
    close (List.ofFn (fun k => ∑ j, terms j k)) =
      ∑ j, close (List.ofFn (terms j)) := by
  simp only [close_ofFn,squareIter_eq,sum_pow_char_pow]
  exact Finset.sum_comm

/-- Per-region source accumulation and one close per region. The owner is the
literal original claim's region index, so every claim has exactly one owner. -/
theorem region_closes {m r : Nat} (owner : Fin m → Fin r) (selector : Fin r → E)
    (terms : Fin m → Fin 64 → E) :
    (∑ region, selector region * close (List.ofFn (fun k =>
      ∑ j, if owner j=region then terms j k else 0))) =
      ∑ j, selector (owner j) * close (List.ofFn (terms j)) := by
  simp_rw [close_sum]
  have selected (j : Fin m) (region : Fin r) :
      close (List.ofFn (fun k => if owner j=region then terms j k else 0)) =
        if owner j=region then close (List.ofFn (terms j)) else 0 := by
    split_ifs
    · rfl
    · rw [close_ofFn]
      simp [squareIter_eq]
  simp_rw [selected]
  simp only [Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp

/-- The source query ladders, rather than inverse powers supplied by a caller. -/
def sourcePrefixScan (cs : Fin 64 → E) : List (E × List E) → List (Fin 64 → E)
  | [] => [cs]
  | pair :: rest => cs :: sourcePrefixScan (fun k => cs k*(1+pair.1+pair.2[k.val]!)) rest

theorem sourcePrefixScan_eq (cs : Fin 64 → E) (pairs : List (E × E)) :
    sourcePrefixScan cs (pairs.map (fun pair => (pair.1,inverseFrobeniusLadder pair.2 1))) =
      prefixScan cs pairs := by
  induction pairs generalizing cs with
  | nil => rfl
  | cons pair pairs ih =>
    simp only [List.map_cons,sourcePrefixScan,prefixScan]
    rw [show (fun k : Fin 64 => cs k*(1+pair.1+(inverseFrobeniusLadder pair.2 1)[k.val]!)) =
        (fun k => cs k*(1+pair.1+inverseFrobenius pair.2 k.val)) by
      funext k
      rw [SuccinctRingCoefficients.queryLadder_get]]
    rw [ih]

def sourcePrefixTerms (cs : Fin 64 → E) (z q : List E) (lengths : List Nat) :
    List (Fin 64 → E) :=
  let cached := sourcePrefixScan cs ((z.zip q).map (fun pair => (pair.1,inverseFrobeniusLadder pair.2 1)))
  lengths.map (fun n => cached[n]!)

theorem sourcePrefixTerms_eq (cs : Fin 64 → E) (z q : List E) (lengths : List Nat)
    (bounds : ∀ n ∈ lengths, n ≤ z.length ∧ n ≤ q.length) :
    sourcePrefixTerms cs z q lengths = prefixTerms cs z q lengths := by
  simp only [sourcePrefixTerms,sourcePrefixScan_eq,prefixTerms]
  apply List.map_congr_left
  intro n member
  exact prefixScan_lookup cs z q n (bounds n member).1 (bounds n member).2

def sourceGroupWeight {m : Nat} {family : Fin m → FamilyClaim} (cs : Fin 64 → E)
    (gamma : E) (x : Array E) (ladders : List (List E)) (group : PrefixGroup family) : E :=
  let cached := sourcePrefixScan cs (group.lead.zip ladders)
  (group.members.map (fun j =>
    SuccinctPointWeight.eqBitsAt ((family j).offset / 2^(family j).point.size) x
        (family j).point.size (x.size-(family j).point.size) *
      close (List.ofFn (fun k : Fin 64 => gamma^j.val * (cached[(family j).point.size]!) k)))).sum

theorem sourceGroupWeight_eq {m : Nat} {family : Fin m → FamilyClaim}
    (cs : Fin 64 → E) (gamma : E) (x : Array E) (group : PrefixGroup family) :
    sourceGroupWeight cs gamma x (x.toList.map (fun q => inverseFrobeniusLadder q 1)) group =
      groupWeight cs gamma x group := by
  have zipped (z q : List E) :
      z.zip (q.map (fun q => inverseFrobeniusLadder q 1)) =
        (z.zip q).map (fun pair => (pair.1,inverseFrobeniusLadder pair.2 1)) := by
    induction z generalizing q with
    | nil => simp
    | cons z zs ih => cases q <;> simp [ih]
  simp only [sourceGroupWeight,zipped,sourcePrefixScan_eq,groupWeight]

/-- Coefficient construction and all query ladders are materialized once,
then each longest prefix is scanned once for every member of its group. -/
def sourceSharedRingWeightAt {m : Nat} (family : Fin m → FamilyClaim)
    (seed : Prefix) (x : Array E) : E :=
  let cs := SuccinctRingCoefficients.sourceCoefficientArray seed.2
  let ladders := x.toList.map (fun q => inverseFrobeniusLadder q 1)
  ((prefixGroups family).map (sourceGroupWeight (fun k => cs[k.val]!) seed.1 x ladders)).sum

theorem sourceSharedRingWeightAt_eq {m : Nat} (family : Fin m → FamilyClaim)
    (seed : Prefix) (x : Array E) :
    sourceSharedRingWeightAt family seed x = sourceRingWeightAt family seed x := by
  unfold sourceSharedRingWeightAt sourceRingWeightAt
  apply congrArg List.sum
  apply List.map_congr_left
  intro group _
  exact sourceGroupWeight_eq _ _ x group

def sourceStackWeightAt {m : Nat} (family : Fin m → FamilyClaim) (points : Array PointClaim)
    (seed : Prefix) (lambda : E) (x : Array E) : E :=
  sourceSharedRingWeightAt family seed x +
    ∑ i : Fin points.size, lambda^(i.val+1)*SuccinctPointWeight.eqAt points[i] x

theorem sourceStackWeightAt_eq_batch_mle {m : Nat} (family : Fin m → FamilyClaim)
    (points : Array PointClaim) (seed : Prefix) (lambda : E) (x : Array E)
    (familyShape : FamilyShape x.size family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape x.size points[i]) :
    sourceStackWeightAt family points seed lambda x =
      Concrete.mle (CausalGame.batchClaims (2^x.size)
        (transformedClaims (2^x.size) family points seed) lambda).weight x := by
  unfold sourceStackWeightAt
  rw [sourceSharedRingWeightAt_eq]
  rw [sourceRingWeightAt_eq family seed x (fun j => (familyShape j).1)]
  exact stackWeightAt_eq_batch_mle family points seed lambda x familyShape pointShapes

end Whir.SuccinctRingGroups
