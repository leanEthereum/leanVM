/-
  LeanVM.Guest.B1.Whir.CPrim

  The completeness direction's small blocks: explicit valuations by segments, the
  square-and-multiply chain, a squeeze with nothing waiting, a materialized pointer.
-/

module

public import LeanVM.Guest.B1.Whir.CVal
public import LeanVM.Guest.B1.Whir.CLoop
public import LeanVM.Guest.B1.Common.Run

/-!
# Small blocks, honestly

`segVal`: the valuation of consecutive segments of values. `osPowSteps_complete`: the template's
square-and-multiply chain at its honest values (`powVals`). `osSqueeze0_complete`: a squeeze with
nothing waiting, its permutation's cells and its challenge's values. `osMat_complete`: a
materialized pointer `base·g^off`. `sqCaps`: the capacities a run of squezes from nothing waiting
leaves.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- Two blocks in sequence, the second's outcome kept. -/
theorem BlkF.then {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA Out : Val → Prop}
    {fA : ℕ → E} {fB : Val → ℕ → E}
    (h1 : k ≤ k1) (h2 : k1 ≤ k2) (hA : BlkF C rd σ k k1 fA A OutA)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → OutA σ1 → BlkF C rd σ1 k1 k2 (fB σ1) B Out) :
    BlkF C rd σ k k2 (seqF σ k k1 fA fB) (A ++ B) Out :=
  BlkF.mono (BlkF.seq h1 h2 hA hB) fun _ h ↦ h.2

/-! ## Valuations by segments -/

/-- The valuation of the segments, at the values `.n i`. -/
def segVal (segs : List (ℕ × (ℕ → E))) : Val := fun v ↦
  if v.path = [] ∧ v.tag = 0 then segLookup segs v.idx else 0

theorem segVal_n (segs : List (ℕ × (ℕ → E))) (i : ℕ) : segVal segs (.n i) = segLookup segs i := by
  simp [segVal]

/-! ## Square and multiply -/

/-- The values of the square-and-multiply chain on `X` from `X^a`. -/
def powVals (X : E) : List Bool → ℕ → List E
  | [], _ => []
  | true :: ds, a => [X ^ (2 * a), X ^ (2 * a + 1)] ++ powVals X ds (2 * a + 1)
  | false :: ds, a => [X ^ (2 * a)] ++ powVals X ds (2 * a)

theorem powVals_length (X : E) : ∀ (ds : List Bool) (a : ℕ),
    (powVals X ds a).length = ds.length + (ds.filter id).length
  | [], _ => rfl
  | true :: ds, a => by simp [powVals, powVals_length X ds]; omega
  | false :: ds, a => by simp [powVals, powVals_length X ds]; omega

/-- **The square-and-multiply chain, honestly.** -/
theorem osPowSteps_complete {σ : Val} (x : ℕ) : ∀ (ds : List Bool) (acc k a : ℕ),
    σ (.n acc) = σ (.n x) ^ a →
    (∀ j < (powVals (σ (.n x)) ds a).length,
      σ (.n (k + j)) = (powVals (σ (.n x)) ds a).getD j 0) →
    AllOk C rd σ (osPowSteps x ds acc k).1 ∧
      σ (.n (osPowSteps x ds acc k).2) = σ (.n x) ^ digitsVal ds a
  | [], _, _, _, ha, _ => ⟨allOk_nil, ha⟩
  | true :: ds, acc, k, a, ha, hv => by
    have v0 := hv 0 (by simp [powVals])
    have v1 := hv 1 (by simp [powVals])
    simp only [powVals, List.cons_append, List.nil_append, List.getD_cons_zero,
      List.getD_cons_succ, Nat.add_zero] at v0 v1
    have := osPowSteps_complete x ds (k + 1) (k + 2) (2 * a + 1) v1 (fun j hj ↦ by
      have := hv (j + 2) (by simp [powVals]; omega)
      simp only [powVals, List.cons_append, List.nil_append, List.getD_cons_succ] at this
      rw [show k + 2 + j = k + (j + 2) by ring, this])
    simp only [osPowSteps, ↓reduceIte, allOk_cons, StmtOk, Atom.Holds]
    refine ⟨⟨by rw [v0, ha, ← pow_add]; ring_nf, by rw [v1, v0]; ring, this.1⟩, ?_⟩
    rw [this.2]; rfl
  | false :: ds, acc, k, a, ha, hv => by
    have v0 := hv 0 (by simp [powVals])
    simp only [powVals, List.cons_append, List.nil_append, List.getD_cons_zero, Nat.add_zero] at v0
    have := osPowSteps_complete x ds k (k + 1) (2 * a) v0 (fun j hj ↦ by
      have := hv (j + 1) (by simp [powVals]; omega)
      simp only [powVals, List.cons_append, List.nil_append, List.getD_cons_succ] at this
      rw [show k + 1 + j = k + (j + 1) by ring, this])
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, allOk_cons, StmtOk, Atom.Holds]
    refine ⟨⟨by rw [v0, ha, ← pow_add]; ring_nf, this.1⟩, ?_⟩
    rw [this.2]; simp [digitsVal]

theorem osPowSteps_all_flat (x : ℕ) : ∀ ds acc k, (osPowSteps x ds acc k).1.all Stmt.flat = true
  | [], _, _ => rfl
  | d :: ds, acc, k => by
    cases d <;> simp [osPowSteps, osPowSteps_all_flat x ds, Stmt.flat]

/-! ## Canonical cells -/

/-- Cell `c` of a state, `0` past the thirteen. -/
def cells13F (S : KeccakState) (c : ℕ) : E := if h : c < 13 then cellsOfState S false ⟨c, h⟩ else 0

theorem capOf_canonical (S : KeccakState) : AllCanonical (capOf S) := by
  intro c hc
  simp only [capOf, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact cellsOfState_canonical _ _ _

theorem pendCells_canonical (pend : List (E × ℕ)) : AllCanonical (pendCells pend) := by
  intro c hc
  simp only [pendCells, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hc
  obtain ⟨p, -, hp | hp⟩ := hc
  · rw [hp]; exact (scalarCells_canonical _ _).1
  · rw [hp]; exact (scalarCells_canonical _ _).2

theorem squeezeN_cap_canonical : ∀ (n : ℕ) (F : Fs), AllCanonical F.cap →
    AllCanonical (F.squeezeN n).2.cap
  | 0, _, h => h
  | n + 1, _, _ => squeezeN_cap_canonical n _ (capOf_canonical _)

/-! ## A squeeze with nothing waiting -/

/-- **A squeeze with nothing waiting, honestly**: the zero run, the capacity canonical, the
permutation's cells and the challenge's values. -/
theorem osSqueeze0_complete {σ : Val} {p : ℕ} {cap : List ℕ} (hcl : cap.length = 5) {j : ℕ}
    (hz : σ (.n (p + 1)) = 0 ∧ σ (.n (p + 2)) = 0 ∧ σ (.n (p + 3)) = 0 ∧ σ (.n (p + 4)) = 0)
    (hcan : AllCanonical (cap.map fun i ↦ σ (.n i)))
    (hv : ∀ c < 13, σ (.n (j + c)) = cells13F (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm c)
    (hc : ∀ i < 7, σ (.n (j + 13 + i)) = challengeVals (σ (.n j)) (σ (.n (j + 1))) i) :
    AllOk C rd σ (osSqueeze0 p cap j) ∧
      σ (.n (j + 19)) = challengeOf (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm := by
  obtain ⟨z1, z2, z3, z4⟩ := hz
  set S := (⟨cap.map fun i ↦ σ (.n i), []⟩ : Fs).perm with hS
  have h0 : σ (.n j) = cellsOfState S false 0 := by
    have := hv 0 (by omega); simpa [cells13F] using this
  have h1 : σ (.n (j + 1)) = cellsOfState S false 1 := by
    have := hv 1 (by omega); simpa [cells13F] using this
  have hins : (([p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4] ++ cap).map V.n).map σ =
      pendCells [] ++ List.replicate 8 0 ++ cap.map fun i ↦ σ (.n i) := by
    simp [z1, z2, z3, z4, pendCells, List.replicate]
  have hch : AllOk C rd σ (challengeT (.n j) (.n (j + 1)) (j + 13)) := by
    have h := holdsList_flat (C := C) (rd := rd) (σ := σ) (challengeT (.n j) (.n (j + 1)) (j + 13))
      rfl True (fun _ ↦ True)
    rw [holds_challengeT] at h
    exact (h.mp ⟨challengeOk_of_vals (by rw [h1]; exact cellsOfState_canonical _ _ _)
      (fun i hi ↦ hc i hi), trivial⟩).1
  refine ⟨?_, ?_⟩
  · simp only [osSqueeze0, allOk_cons]
    refine ⟨?_, hch⟩
    show (Atom.keccak _ _ false false).Holds rd σ
    apply keccakA_of (by simp [hcl]) (by simp [osRun])
    · rw [hins]
      intro x hx
      simp only [List.mem_append, List.mem_replicate] at hx
      rcases hx with (hx | hx) | hx
      · simp [pendCells] at hx
      · rw [hx.2, zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
      · exact hcan x hx
    · rw [hins, show permOf (pendCells [] ++ List.replicate 8 0 ++ cap.map fun i ↦ σ (.n i)) = S
        from by rw [hS, perm_eq_cells _ (by simp)]; rfl]
      funext c
      simp only [cells13, osRun, List.map_map, Function.comp_def]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range c.isLt,
        Option.map_some, Option.getD_some]
      have := hv c.val c.isLt
      simp only [cells13F, c.isLt, ↓reduceDIte] at this
      exact this
  · have := hc 6 (by omega)
    rw [show j + 13 + 6 = j + 19 by ring, h0, h1] at this
    rw [this, challengeVals_six]

/-! ## `fs_pack` -/

theorem allOk_fsPackT_iff {σ : Val} (x : V) (b t : ℕ) :
    AllOk C rd σ (fsPackT x b t) ↔ FsPackOk σ x b t := by
  have h := holdsList_flat (C := C) (rd := rd) (σ := σ) (fsPackT x b t) rfl True (fun _ ↦ True)
  rw [holds_fsPackT] at h
  simpa using h.symm

/-- `fs_pack` at its honest values. -/
theorem fsPackT_complete {σ : Val} {x : V} {b t : ℕ} (h : ∀ i < 9, σ (.n (b + i)) = fsPackVals (σ x) t i) :
    AllOk C rd σ (fsPackT x b t) ∧ σ (.n (b + 6)) = (Keccak.scalarCells (σ x) t).1 ∧
      σ (.n (b + 8)) = (Keccak.scalarCells (σ x) t).2 := by
  have c := fsPackVals_cells (σ x) t
  simp only [Prod.ext_iff] at c
  exact ⟨(allOk_fsPackT_iff x b t).mpr (fsPackOk_of_vals h), by rw [h 6 (by omega), c.1],
    by rw [h 8 (by omega), c.2]⟩

/-! ## A materialized pointer -/

/-- The values of `osMat base off k`. -/
def matVal (σ : Val) (base off k i : ℕ) : E :=
  if i = k then gw off else σ (.n base) * gw off

/-- **The materialized pointer.** -/
theorem osMat_complete {base off k : ℕ} (hoff : off < u128Bound) (hb : base < k) {σ σ' : Val}
    (ha : AgreeBelow k σ σ') (hv : RangeVals σ' k (osMat base off k).2.2 (matVal σ base off k)) :
    AllOk C rd σ' (osMat base off k).1 ∧
      σ' (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off := by
  by_cases h0 : off = 0
  · subst h0
    simp only [osMat, ↓reduceIte, pow_zero, mul_one]
    exact ⟨allOk_nil, ha base hb⟩
  · simp only [osMat, h0, ↓reduceIte] at hv ⊢
    have e0 := hv k le_rfl (by omega)
    have e1 := hv (k + 1) (by omega) (by omega)
    simp only [matVal, ↓reduceIte, show k + 1 ≠ k by omega] at e0 e1
    refine ⟨?_, by rw [e1, gw_eq hoff]⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact ⟨e0, by rw [e1, e0, ha base hb]⟩

/-! ## A run of squeezes from nothing waiting -/

/-- The capacities `j` squeezes from the capacity `cap`, nothing waiting, leave. -/
def sqCaps (cap : List E) : ℕ → List E
  | 0 => cap
  | j + 1 => capOf (⟨sqCaps cap j, []⟩ : Fs).perm

/-- The challenge of squeeze `j`. -/
def sqChal (cap : List E) (j : ℕ) : E := challengeOf (⟨sqCaps cap j, []⟩ : Fs).perm

theorem sqCaps_length (cap : List E) (h : cap.length = 5) : ∀ j, (sqCaps cap j).length = 5
  | 0 => h
  | _ + 1 => by simp [sqCaps, capOf]

theorem sqCaps_canonical (cap : List E) (h : AllCanonical cap) : ∀ j, AllCanonical (sqCaps cap j)
  | 0 => h
  | _ + 1 => capOf_canonical _

/-- The chain is the Spec's squeezes. -/
theorem squeezeN_sqCaps : ∀ (j : ℕ) (cap : List E),
    ((⟨cap, []⟩ : Fs).squeezeN j).2 = ⟨sqCaps cap j, []⟩ ∧
      ∀ i < j, ((⟨cap, []⟩ : Fs).squeezeN j).1.getD i 0 = sqChal cap i
  | 0, _ => ⟨rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | j + 1, cap => by
    obtain ⟨h1, h2⟩ := squeezeN_sqCaps j (capOf (⟨cap, []⟩ : Fs).perm)
    have hs : (⟨cap, []⟩ : Fs).squeeze = (sqChal cap 0, ⟨capOf (⟨cap, []⟩ : Fs).perm, []⟩) := rfl
    have hc : ∀ i, sqCaps (capOf (⟨cap, []⟩ : Fs).perm) i = sqCaps cap (i + 1) := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => simp only [sqCaps, ih]
    refine ⟨?_, fun i hi ↦ ?_⟩
    · simp only [Fs.squeezeN, hs, h1, hc]
    · simp only [Fs.squeezeN, hs]
      rcases i with _ | i
      · rfl
      · rw [List.getD_cons_succ, h2 i (by omega)]
        simp only [sqChal, hc]

/-! ## A function's body from its arguments -/

/-- The valuation holding the words `args` at the values `0 ..`. -/
def argVal (args : List E) : Val := fun v ↦
  if v.path = [] ∧ v.tag = 0 then args.getD v.idx 0 else 0

theorem argVal_n (args : List E) (i : ℕ) : argVal args (.n i) = args.getD i 0 := by
  simp [argVal]

theorem params_argVal {σ : Val} {args : List E} (h : AgreeBelow args.length (argVal args) σ) :
    (osParams args.length).map σ = args := by
  refine List.ext_getElem (by simp [osParams]) fun j h1 h2 ↦ ?_
  simp only [osParams, List.getElem_map, List.getElem_range]
  rw [h j h2, argVal_n, List.getD_eq_getElem _ _ h2]

/-- **A function's body from a block**: a function of the parameters `0 .. n - 1`, its body a
flat block then a `ret`, holds of `args` and `rets` when the block, from the arguments, holds with
the returned words `rets`. -/
theorem sem_of_blkF {fn : Fn} {K : ℕ} {f : ℕ → E} {A : List Stmt} {vs : List V}
    {args rets : List E} (hps : fn.params = osParams args.length) (hb : fn.body = A ++ [.ret vs])
    (hflat : A.all Stmt.flat = true)
    (h : BlkF C rd (argVal args) args.length K f A (fun σ' ↦ vs.map σ' = rets)) :
    Fn.Sem C rd fn args rets := by
  set σ := fill (argVal args) args.length K f
  obtain ⟨hok, hr⟩ := h σ (agree_fill _ _ _ _) (range_fill _ _ _ _)
  refine ⟨σ, by rw [hps]; exact params_argVal (agree_fill _ _ _ _), ?_⟩
  rw [hb, holdsList_flat_ret _ hflat]
  exact ⟨hok, hr⟩

/-- **A function's relation from a block.** -/
theorem rel_of_blkF {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn) {K : ℕ}
    {f : ℕ → E} {A : List Stmt} {vs : List V} {args rets : List E}
    (hps : fn.params = osParams args.length) (hb : fn.body = A ++ [.ret vs])
    (hflat : A.all Stmt.flat = true)
    (h : BlkF (coreProgram.Rel rd) rd (argVal args) args.length K f A (fun σ' ↦ vs.map σ' = rets)) :
    coreProgram.Rel rd name args rets := by
  rw [rel_iff_sem hf]
  exact sem_of_blkF hps hb hflat h

/-- The loop tail's values. -/
def loopTailVals (X N : E) : List E :=
  [word 2 0 0, X * word 2 0 0, X * word 2 0 0 + N, word 2 0 0, X * word 2 0 0]

/-- **The loop tail, honestly.** -/
theorem osLoopTailA_complete {σ : Val} {k : ℕ} (hk : 2 ≤ k) :
    BlkF C rd σ k (k + 5) (fun i ↦ (loopTailVals (σ (.n 0)) (σ (.n 1))).getD (i - k) 0)
      (osLoopTailA k) (fun σ' ↦ σ' (.n (k + 2)) = σ' (.n 0) * gen + σ' (.n 1) ∧
        σ' (.n (k + 4)) = σ' (.n 0) * gen) := by
  intro σ' ha hr
  have v : ∀ i < 5, σ' (.n (k + i)) = (loopTailVals (σ (.n 0)) (σ (.n 1))).getD i 0 :=
    fun i hi ↦ by rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
  have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
  have v3 := v 3 (by omega); have v4 := v 4 (by omega)
  simp only [loopTailVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4
  have a0 := ha 0 (by omega); have a1 := ha 1 (by omega)
  refine ⟨?_, by rw [v2, word_gen, a0, a1], by rw [v4, word_gen, a0]⟩
  simp only [osLoopTailA, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  exact ⟨v0, by rw [v1, a0, v0], by rw [v2, v1, a1], v3, by rw [v4, a0, v3]⟩

/-- **A loop's iteration from a block**: its body before the tail holding from the arguments
`x :: N :: rest` (`n` of them, `2 ≤ n`), the iteration holds with the guard and the next
arguments. -/
theorem iter_of_blkF {n K : ℕ} {f : ℕ → E} {A : List Stmt} {X N : E} {rest : List E}
    (hn : (X :: N :: rest).length = n) (hK : n ≤ K)
    (h : BlkF C rd (argVal (X :: N :: rest)) n K f A (fun _ ↦ True)) :
    ∃ σ : Val, (osParams n).map σ = X :: N :: rest ∧ AllOk C rd σ (A ++ osLoopTailA K) ∧
      σ (.n (K + 2)) = X * gen + N ∧
      (.n (K + 4) :: (List.range (n - 1)).map fun i ↦ V.n (i + 1)).map σ = X * gen :: N :: rest := by
  have hn2 : 2 ≤ n := by rw [← hn]; simp
  have hT := BlkF.then (C := C) (rd := rd) hK (Nat.le_add_right K 5) h fun σ1 _ _ ↦
    osLoopTailA_complete (σ := σ1) (k := K) (by omega)
  set σ := fill (argVal (X :: N :: rest)) n (K + 5) (seqF (argVal (X :: N :: rest)) n K f
    (fun σ1 i ↦ (loopTailVals (σ1 (.n 0)) (σ1 (.n 1))).getD (i - K) 0)) with hσ
  obtain ⟨hok, h2, h4⟩ := hT σ (agree_fill _ _ _ _) (range_fill _ _ _ _)
  have hab : AgreeBelow n (argVal (X :: N :: rest)) σ := agree_fill _ _ _ _
  have e0 : σ (.n 0) = X := by rw [hab 0 (by omega), argVal_n]; rfl
  have e1 : σ (.n 1) = N := by rw [hab 1 (by omega), argVal_n]; rfl
  rw [e0, e1] at h2
  rw [e0] at h4
  refine ⟨σ, ?_, hok, h2, ?_⟩
  · rw [← hn]; exact params_argVal (by rw [hn]; exact hab)
  · rw [List.map_cons, h4]
    congr 1
    refine List.ext_getElem (by simp [← hn]) fun j h1 h2 ↦ ?_
    simp only [List.getElem_map, List.getElem_range]
    have hj : j + 1 < n := by simp at h1; omega
    rw [hab (j + 1) hj, argVal_n, List.getD_eq_getElem _ _ (by rw [hn]; exact hj)]
    simp

/-! ## Materializations from earlier ones -/

theorem rangeVals_sub {σ : Val} {k k' a b : ℕ} {f g : ℕ → E} (h : RangeVals σ k k' f)
    (ha : k ≤ a) (hb : b ≤ k') (hfg : ∀ i, a ≤ i → i < b → f i = g i) : RangeVals σ a b g :=
  fun i h1 h2 ↦ (h i (by omega) (by omega)).trans (hfg i h1 h2)

theorem matsBelow_mono {K K' : ℕ} {mats : List OsMat} (h : MatsBelow K mats) (hK : K ≤ K') :
    MatsBelow K' mats := fun m hm ↦ by
  obtain ⟨h1, h2, h3⟩ := h m hm; exact ⟨by omega, by omega, by omega⟩

/-- The values of `osMatP plan mats base off k`: the distance's power, then the pointer. -/
def matPVal (σ : Val) (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k i : ℕ) : E :=
  if i = k then gw (osMatSD plan mats base off).2 else σ (.n base) * gw off

/-- **A materialized pointer, from earlier ones.** -/
theorem osMatP_complete {plan : List (ℕ × ℕ × ℕ)} {mats : List OsMat} {base off k : ℕ}
    (hoff : off < u128Bound) {σ σ' : Val} (hm : MatsOk σ' mats) (hbase : σ' (.n base) = σ (.n base))
    (hv : RangeVals σ' k (osMatP plan mats base off k).2.2 (matPVal σ plan mats base off k)) :
    AllOk C rd σ' (osMatP plan mats base off k).1 ∧
      σ' (.n (osMatP plan mats base off k).2.1) = σ (.n base) * gen ^ off := by
  by_cases h0 : off = 0
  · subst h0
    simp only [osMatP, ↓reduceIte, pow_zero, mul_one]
    exact ⟨allOk_nil, hbase⟩
  · rw [osMatP_eq k h0] at hv ⊢
    have e0 := hv k le_rfl (by simp)
    have e1 := hv (k + 1) (by omega) (by simp)
    simp only [matPVal, ↓reduceIte, show k + 1 ≠ k by omega] at e0 e1
    obtain ⟨hd, hs⟩ := osMatSD_ok (plan := plan) hm (base := base) hoff
    refine ⟨?_, by rw [e1, gw_eq hoff]⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    exact ⟨e0, by rw [e1, e0, gw_eq hd, hs, hbase, gw_eq hoff]⟩

theorem osMatP_k (plan : List (ℕ × ℕ × ℕ)) (mats : List OsMat) (base off k : ℕ) :
    (osMatP plan mats base off k).2.2 = if off = 0 then k else k + 2 := by
  unfold osMatP; split_ifs <;> rfl


/-! ## Dispatches -/

/-- **A dispatch on the rate's selector `R` holds** at every valuation giving its arguments and
returns the words `argsv`, `retsv`. -/
def DispC (C : CallRel) (rd : Reader) (R : E) (names : List String) (argsv retsv : List E) : Prop :=
  ∀ σ : Val, σ (.n osRate) = R → ∀ args rets : List V, args.map σ = argsv → rets.map σ = retsv →
    StmtOk C rd σ (.dispatch (.n osRate) names args rets)

/-- A dispatch at the selector `g^ri` holds when its `ri`-th function relates the words. -/
theorem dispC_of {names : List String} {ri : ℕ} (hri : ri < names.length) {R : E}
    (hR : R = ofK (addressOfIndex ri)) {argsv retsv : List E} (h : C names[ri] argsv retsv) :
    DispC C rd R names argsv retsv := fun σ hσ args rets ha hr ↦
  ⟨ri, hri, by rw [hσ, hR], by rw [ha, hr]; exact h⟩

end
end LeanVM.Guest.B1.Whir
