import Whir.SupportedCandidateProtocolProbability

/-! Causal first-collapse localization of the fixed Root0 row cancellation event.
Each stage charges one fresh scalar, not the marginal six-coordinate loss. -/
namespace Whir.PCSRoundByRoundCancellation
open Concrete Protocol CausalGame CausalProbability ExecutionShapes ParameterBounds
open InitialKnowledgeSchedule SupportedCandidateExtraction SupportedCandidateProtocol
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
attribute [local irreducible] ParameterBounds.config

variable {F : Type*} [Field F] [Inhabited F] [CharP F 2]

def partialRow (row : Array F) (seed : Nat → F) (k : Nat) : Array F :=
  (List.range k).foldl (fun a i => foldLow a (seed i)) row

omit [CharP F 2] in
@[simp] theorem partialRow_zero (row : Array F) (seed : Nat → F) :
    partialRow row seed 0 = row := rfl

omit [CharP F 2] in
 theorem partialRow_succ (row : Array F) (seed : Nat → F) (k : Nat) :
    partialRow row seed (k+1) = foldLow (partialRow row seed k) (seed k) := by
  simp [partialRow, List.range_succ, List.foldl_append]

omit [CharP F 2] in
 theorem partialRow_congr (row : Array F) (a b : Nat → F) (k : Nat)
    (h : ∀ i < k, a i = b i) : partialRow row a k = partialRow row b k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [partialRow_succ, partialRow_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

omit [CharP F 2] in
 theorem partialRow_size (row : Array F) (seed : Nat → F) (n k : Nat)
    (shape : row.size = 2^n) (hk : k ≤ n) :
    (partialRow row seed k).size = 2^(n-k) := by
  induction k with
  | zero => simpa using shape
  | succ k ih =>
    rw [partialRow_succ, ArrayLayout.size_foldLow, ih (by omega)]
    rw [show n-k = (n-(k+1))+1 by omega, pow_succ]
    simp

omit [CharP F 2] in
 theorem partialRow_terminal (row point : Array F) (shape : row.size = 2^point.size) :
    partialRow row (fun i => point[i]!) point.size = #[Concrete.mle row point] := by
  have mapped : (List.range point.size).map (fun i => point[i]!) = point.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      simp only [getElem!_pos point i (by simpa using hi')]
  unfold partialRow
  rw [← List.foldl_map, mapped, Array.foldl_toList]
  exact TerminalRefinement.foldLow_terminal row point shape

omit [Inhabited F] [CharP F 2] in
private theorem pair_recover (a b c d r s : F) (different : r ≠ s)
    (hr : foldPair a b r = foldPair c d r)
    (hs : foldPair a b s = foldPair c d s) : a = c ∧ b = d := by
  have product : (r-s) * ((a+b)-(c+d)) = 0 := by
    unfold foldPair at hr hs
    linear_combination hr - hs
  have sums : a+b = c+d := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr different))
  have ac : a = c := by
    unfold foldPair at hr
    rw [sums] at hr
    exact add_right_cancel hr
  exact ⟨ac, by simpa [ac] using sums⟩

/-- A nonzero incoming row difference has at most one collapsing scalar. -/
 theorem foldLow_collision_unique {n : Nat} (a b : Array F)
    (ha : a.size = 2^(n+1)) (hb : b.size = 2^(n+1)) (hne : a ≠ b)
    (r s : F) (hr : foldLow a r = foldLow b r) (hs : foldLow a s = foldLow b s) : r = s := by
  by_contra different
  apply hne
  apply congrArg Subtype.val (ExecutableOOD.decode_injective (n+1) (a₁ := ⟨a,ha⟩) (a₂ := ⟨b,hb⟩) ?_)
  have hrf := congrArg (ExecutableOOD.decode n) hr
  have hsf := congrArg (ExecutableOOD.decode n) hs
  rw [ExecutableOOD.decode_foldLow a r ha, ExecutableOOD.decode_foldLow b r hb] at hrf
  rw [ExecutableOOD.decode_foldLow a s ha, ExecutableOOD.decode_foldLow b s hb] at hsf
  funext u
  let tail : Cube n := fun i => u i.succ
  have pair := pair_recover (ExecutableOOD.decode (n+1) a (Fin.cons false tail))
    (ExecutableOOD.decode (n+1) a (Fin.cons true tail))
    (ExecutableOOD.decode (n+1) b (Fin.cons false tail))
    (ExecutableOOD.decode (n+1) b (Fin.cons true tail)) r s different
    (by simpa only [foldFirst_charTwo, foldPair] using congrFun hrf tail)
    (by simpa only [foldFirst_charTwo, foldPair] using congrFun hsf tail)
  have cons : Fin.cons (u 0) tail = u := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  rw [← cons]
  cases u 0
  · exact pair.1
  · exact pair.2

noncomputable def Stage {W Q : Type*} (list : Finset W) (committed : Q → Array F)
    (encoded : W → Q → Array F) (seed : Nat → F) (j : Nat) : Prop :=
  ∃ w ∈ list, ∃ q,
    partialRow (committed q) seed j ≠ partialRow (encoded w q) seed j ∧
    partialRow (committed q) seed (j+1) = partialRow (encoded w q) seed (j+1)

omit [CharP F 2] in
/-- The first equality cannot be stage zero when the committed row differs. -/
 theorem first_collapse {n : Nat} (a b : Array F) (seed : Nat → F)
    (different : a ≠ b) (terminal : partialRow a seed n = partialRow b seed n) :
    ∃ j < n, partialRow a seed j ≠ partialRow b seed j ∧
      partialRow a seed (j+1) = partialRow b seed (j+1) := by
  induction n with
  | zero => exact False.elim (different terminal)
  | succ n ih =>
    by_cases previous : partialRow a seed n = partialRow b seed n
    · obtain ⟨j,hj,hn,he⟩ := ih previous
      exact ⟨j, by omega, hn, he⟩
    · exact ⟨n, by omega, previous, terminal⟩

omit [CharP F 2] in
/-- Equality persists under the actual linear folds; a nonzero incoming
difference therefore certifies every earlier partial row was nonzero too. -/
theorem partialRow_equal_mono (a b : Array F) (seed : Nat → F) (j k : Nat)
    (hjk : j ≤ k) (equal : partialRow a seed j = partialRow b seed j) :
    partialRow a seed k = partialRow b seed k := by
  induction k with
  | zero =>
    have hj : j = 0 := by omega
    simpa [hj] using equal
  | succ k ih =>
    by_cases same : j = k+1
    · simpa [same] using equal
    · rw [partialRow_succ, partialRow_succ, ih (by omega)]

omit [CharP F 2] in
theorem stage_is_first {W Q : Type*} (list : Finset W)
    (committed : Q → Array F) (encoded : W → Q → Array F) (seed : Nat → F)
    (j : Nat) (event : Stage list committed encoded seed j) :
    ∃ w ∈ list, ∃ q, (∀ k ≤ j,
      partialRow (committed q) seed k ≠ partialRow (encoded w q) seed k) ∧
      partialRow (committed q) seed (j+1) = partialRow (encoded w q) seed (j+1) := by
  obtain ⟨w,hw,q,different,collapse⟩ := event
  exact ⟨w,hw,q,fun k hk equal => different
    (partialRow_equal_mono _ _ _ k j hk equal),collapse⟩

variable [Fintype F] [DecidableEq F]

open Classical in
 theorem stage_fiber_bound {W Q : Type*} [Fintype Q] [DecidableEq W] [DecidableEq Q]
    (n : Nat) (list : Finset W) (committed : Q → Array F) (encoded : W → Q → Array F)
    (committedShape : ∀ q, (committed q).size = 2^n)
    (encodedShape : ∀ w ∈ list, ∀ q, (encoded w q).size = 2^n)
    (seed : Nat → F) (j : Nat) (hj : j < n) :
    Soundness.uniformProb (Finset.univ.filter fun r : F =>
      Stage list committed encoded (Function.update seed j r) j) ≤
      (list.card : ℚ) * Fintype.card Q / Fintype.card F := by
  let events (i : list × Q) : Finset F := Finset.univ.filter fun r =>
    partialRow (committed i.2) seed j ≠ partialRow (encoded i.1 i.2) seed j ∧
    foldLow (partialRow (committed i.2) seed j) r =
      foldLow (partialRow (encoded i.1 i.2) seed j) r
  have fixed (row : Array F) (r : F) :
      partialRow row (Function.update seed j r) j = partialRow row seed j :=
    partialRow_congr _ _ _ _ (fun i hi => Function.update_of_ne (by omega) _ _)
  have equal : (Finset.univ.filter fun r : F =>
      Stage list committed encoded (Function.update seed j r) j) = Finset.univ.biUnion events := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Stage, partialRow_succ, fixed, Function.update_self]
    simp [events]
  have each (i : list × Q) : Soundness.uniformProb (events i) ≤ 1 / Fintype.card F := by
    have card : (events i).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro r hr s hs
      have rmem := (Finset.mem_filter.mp hr).2
      have smem := (Finset.mem_filter.mp hs).2
      apply foldLow_collision_unique (n := n-(j+1)) _ _ _ _ rmem.1 r s rmem.2 smem.2
      · simpa [show n-j = (n-(j+1))+1 by omega] using
          partialRow_size (committed i.2) seed n j (committedShape i.2) hj.le
      · simpa [show n-j = (n-(j+1))+1 by omega] using
          partialRow_size (encoded i.1 i.2) seed n j (encodedShape i.1 i.1.2 i.2) hj.le
    unfold Soundness.uniformProb
    exact div_le_div_of_nonneg_right (by exact_mod_cast card) (by positivity)
  rw [equal]
  calc
    _ ≤ ∑ i, Soundness.uniformProb (events i) := Soundness.union_bound events
    _ ≤ ∑ _i : list × Q, (1 / Fintype.card F : ℚ) := Finset.sum_le_sum (fun i _ => each i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_coe, Nat.cast_mul, nsmul_eq_mul]; ring

def initialSeed (p : Profile) (t : Tape (config p)) (k : Nat) : E :=
  (Array.ofFn (t.2.1 (initialLevel p)).1)[k]!

noncomputable def Event (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (j : Fin (config p).folds[0]!) (t : Tape (config p)) : Prop :=
  Stage (InitialCandidates.witnesses (config p) lanes root)
    (committedRow (Input p lanes root claims)) (witnessRow (Input p lanes root claims))
    (initialSeed p t) j.val

theorem initialSeed_get (p : Profile) (t : Tape (config p)) (k : Nat)
    (hk : k < (config p).folds[0]!) :
    initialSeed p t k = get (.fold (initialLevel p) ⟨k,hk⟩) t := by
  simp [initialSeed, CausalProbability.get, initialLevel, hk]

theorem initialSeed_set (p : Profile) (t : Tape (config p))
    (j : Fin (config p).folds[0]!) (r : E) (k : Nat) (hk : k < (config p).folds[0]!) :
    initialSeed p (set (.fold (initialLevel p) j) t r) k =
      Function.update (initialSeed p t) j.val r k := by
  rw [initialSeed_get _ _ _ hk]
  by_cases equal : k = j.val
  · subst k
    rw [show (⟨j.val,hk⟩ : Fin (config p).folds[0]!) = j from Fin.ext rfl, get_set]
    simp
  · rw [get_set_ne _ _ _ _ (by intro h; cases h; exact equal rfl),
      ← initialSeed_get _ _ _ hk, Function.update_of_ne equal]

open Classical in
/-- Any fixed previous history, including malformed execution histories, has the
same one-scalar bound. Both row sizes are unconditional `Array.ofFn` sizes:
no input-validity, no-wrap, or lane-cap assumption is hidden in this fiber. -/
theorem fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (j : Fin (config p).folds[0]!) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter fun r : Sample (.fold (initialLevel p) j) =>
      Event p lanes root claims j (set (.fold (initialLevel p) j) t r)) ≤
      (2^32 : ℚ) * blockLength (config p) / 2^192 := by
  let input := Input p lanes root claims
  have equal (r : E) : Event p lanes root claims j (set (.fold (initialLevel p) j) t r) ↔
      Stage (InitialCandidates.witnesses (config p) lanes root) (committedRow input)
        (witnessRow input) (Function.update (initialSeed p t) j.val r) j.val := by
    unfold Event Stage
    have fixed (row : Array E) (k : Nat) (hk : k ≤ j.val+1) :
        partialRow row (initialSeed p (set (.fold (initialLevel p) j) t r)) k =
          partialRow row (Function.update (initialSeed p t) j.val r) k :=
      partialRow_congr _ _ _ _ (fun i hi => initialSeed_set p t j r i (by omega))
    simp only [fixed _ j.val (by omega), fixed _ (j.val+1) le_rfl, input]
  simp_rw [equal]
  have bound := stage_fiber_bound (config p).folds[0]!
    (InitialCandidates.witnesses (config p) lanes root) (committedRow input) (witnessRow input)
    (by intro q; simp [committedRow, input, Input, laneCount])
    (by intro w hw q; simp [witnessRow, input, Input, laneCount])
    (initialSeed p t) j.val j.isLt
  rw [FieldModel.card_E] at bound
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at bound
  dsimp only [input, Input] at bound
  simp only [blockLength, Nat.cast_pow, Nat.cast_ofNat]
  apply bound.trans
  gcongr
  exact_mod_cast InitialCandidates.production_witnesses_card p lanes root

theorem cover (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (t : Tape (config p)) (bad : CancellationEvent p lanes root claims t) :
    ∃ j : Fin (config p).folds[0]!, Event p lanes root claims j t := by
  obtain ⟨w,hw,q,different,collision⟩ := bad
  let input := Input p lanes root claims
  have terminal : partialRow (committedRow input q) (initialSeed p t) (config p).folds[0]! =
      partialRow (witnessRow input w q) (initialSeed p t) (config p).folds[0]! := by
    have shapeA : (committedRow input q).size = 2^(config p).folds[0]! := by
      simp [committedRow, input, Input, laneCount]
    have shapeB : (witnessRow input w q).size = 2^(config p).folds[0]! := by
      simp [witnessRow, input, Input, laneCount]
    change partialRow _ (fun i => (Array.ofFn (t.2.1 (initialLevel p)).1)[i]!) _ =
      partialRow _ (fun i => (Array.ofFn (t.2.1 (initialLevel p)).1)[i]!) _
    simpa only [Array.size_ofFn] using
      (partialRow_terminal (committedRow input q) (Array.ofFn (t.2.1 (initialLevel p)).1)
        (by simpa using shapeA)).trans
      ((congrArg (fun x : E => #[x]) collision).trans
        (partialRow_terminal (witnessRow input w q) (Array.ofFn (t.2.1 (initialLevel p)).1)
          (by simpa using shapeB)).symm)
  obtain ⟨j,hj,hn,he⟩ := first_collapse _ _ _ different terminal
  exact ⟨⟨j,hj⟩,w,hw,q,hn,he⟩

/-- Dependence stops at the current initial-fold coordinate, inclusive. -/
theorem prefix_invariant (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (j : Fin (config p).folds[0]!) (t u : Tape (config p))
    (same : ∀ k ≤ j.val, initialSeed p t k = initialSeed p u k) :
    Event p lanes root claims j t ↔ Event p lanes root claims j u := by
  unfold Event Stage
  have fixed (row : Array E) (k : Nat) (hk : k ≤ j.val+1) :
      partialRow row (initialSeed p t) k = partialRow row (initialSeed p u) k :=
    partialRow_congr _ _ _ _ (fun i hi => same i (by omega))
  simp only [fixed _ j.val (by omega), fixed _ (j.val+1) le_rfl]

theorem future_invariant (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (j : Fin (config p).folds[0]!) (q : Coordinate (config p))
    (t : Tape (config p)) (x : Sample q)
    (later : position (.fold (initialLevel p) j) < position q) :
    Event p lanes root claims j (set q t x) ↔ Event p lanes root claims j t := by
  apply prefix_invariant
  intro k hk
  have hkn : k < (config p).folds[0]! := by omega
  rw [initialSeed_get _ _ _ hkn, initialSeed_get _ _ _ hkn]
  apply get_set_ne
  intro equal
  have bound : position (.fold (initialLevel p) (⟨k,hkn⟩ : Fin (config p).folds[0]!)) ≤
      position (.fold (initialLevel p) j) := by
    rw [CausalPositions.position_fold _ _ t, CausalPositions.position_fold _ _ t]
    change levelStart (challenges (config p) t) (initialLevel p).val + k ≤
      levelStart (challenges (config p) t) (initialLevel p).val + j.val
    exact Nat.add_le_add_left hk _
  rw [equal] at bound
  omega

#print axioms fiber_bound
#print axioms cover
#print axioms future_invariant

end Whir.PCSRoundByRoundCancellation
