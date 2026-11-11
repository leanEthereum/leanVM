/-
  LeanVM.Guest.B1.Place.HonestProof

  The honest trace's facts that open_stacked's helpers' placed statements take: the proof.
-/

module

public import LeanVM.Guest.B1.Place.HonestSpec
public import LeanVM.Guest.B1.Place.HonestSizes
public import LeanVM.Guest.B1.Whir.FactsAll
public import LeanVM.Guest.B1.Merkle.CapAll
public import LeanVM.Guest.B1.Whir.BrFin2
public import LeanVM.Guest.B1.Whir.QueriesBlk
public import LeanVM.Guest.B1.Opening.QueriesRun

/-!
# The helpers' honest data, proved

Level by level on the honest trace (`lvHelperFacts_of`, at a configuration whose buffers fit its
rows, `OsSizes`, and whose cap checks are `verify_merkle_cap`'s specializations):

* `level_positions`: the sponge `F2` the queries start from is a permutation's capacity with
  nothing waiting (`hon_F2_cap`), so its squeezes are `sqChal` (`hon_sq_getD`) and the decoded
  positions `posAt` those of `qwPosOf` (`hon_pos`);
* `level_queries`: the hinted cap and flags are the honest ones (`capsL`, `flagsL`), checked to
  the level's root (`cap_meaning_at`, `verify_merkle_cap_holds`), each opening's cap leaf holding
  its climb's digest and its parent flagged (`hon_cap_cells`, `hon_cap_flag`, by `CapsAgree`); the
  positions are the decoders' (`hon_qs`); the chain of the rows' dot products with the row weights
  `wpC`, times `λ^q`, is the enforced sum (`hon_q_ret`: `oqChain_powers`, `enforcedSum_eq`,
  `rowDot_level0`, `rowDot_deeper`);
* `level_residual`: `finH` is the chain `lrAcc` over the positions in `query_positions`
  (`hon_qposC`) and the row of `basis_d` (`hon_bdC`), the residual products reading the row's
  first `logCols` words alone (`residualProd_congr`).

**`os_helper_facts`**: every arm and rate, its sizes by `osSizesB_all`, its cap checks' names by
`candB_all`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## The squeezes -/

theorem hon_F2_pend (L : SpLv) : L.F2.pend = [] := by
  unfold SpLv.F2; split <;> rfl

theorem hon_F2_cap (L : SpLv) : ∃ S : KeccakState, L.F2.cap = capOf S := by
  unfold SpLv.F2; split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

variable {c : OsCfg} {tr : OsTr}

/-- The queries' squeezes are the chain's challenges. -/
theorem hon_sq_getD (h : TrFit c tr) {i : ℕ} (hi : i < c.levels.length) {j : ℕ}
    (hj : j < (lvAt c i).squeezes) :
    ((tr.L i).F2.squeezeN (tr.L i).nsq).1.getD j 0 = sqChal (tr.L i).F2.cap j := by
  have hF2 : (tr.L i).F2 = ⟨(tr.L i).F2.cap, []⟩ := fs_of_pend_nil (hon_F2_pend _)
  have := (squeezeN_sqCaps (tr.L i).nsq (tr.L i).F2.cap).2 j (by rw [(h.fit i hi).nsq]; exact hj)
  rw [← hF2] at this
  exact this

/-- **The decoded positions** of squeeze `j`. -/
theorem hon_pos (h : TrFit c tr) {i : ℕ} (hi : i < c.levels.length) {j : ℕ}
    (hj : j < (lvAt c i).squeezes) {t : ℕ} (ht : t < 192 / (lvAt c i).depth) :
    posAt c tr i (j * (192 / (lvAt c i).depth) + t) =
      eOfNat (qwPosOf (lvAt c i).depth (sqChal (tr.L i).F2.cap j) t) := by
  have hdiv : (j * (192 / (lvAt c i).depth) + t) / (192 / (lvAt c i).depth) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]
  have hmod : (j * (192 / (lvAt c i).depth) + t) % (192 / (lvAt c i).depth) = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  unfold posAt qwPosOf
  rw [hdiv, hmod, hon_sq_getD h hi hj]

/-- **The query positions** are the decoders'. -/
theorem hon_qs (h : TrFit c tr) {i : ℕ} (hi : i < c.levels.length) {k : ℕ}
    (hk : k < (lvAt c i).queries) :
    (tr.L i).qs.getD k 0 = qwPosOf (lvAt c i).depth
      (sqChal (tr.L i).F2.cap (k / (192 / (lvAt c i).depth))) (k % (192 / (lvAt c i).depth)) := by
  have hb := h.lvb i hi
  have hD : (tr.L i).D = (lvAt c i).depth := by rw [SpLv.D, (h.fit i hi).ml, hb.depth]
  have hper := hb.per
  have hspan : (lvAt c i).queries ≤ (lvAt c i).squeezes * (192 / (lvAt c i).depth) := by
    rw [hb.squeezes]; exact ceilDiv_mul_ge hper
  have hj : k / (192 / (lvAt c i).depth) < (lvAt c i).squeezes :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
  have hq : (tr.L i).level.queries = (lvAt c i).queries := hb.queries
  rw [← hon_sq_getD h hi hj]
  unfold SpLv.qs queriesOf
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range, hq]; exact hk),
    List.getElem_map, List.getElem_range, hD]
  rfl

/-! ## The cap -/

theorem hon_capsL_getD {i k : ℕ} (hk : k < 4 * 2 ^ (lvAt c i).capDepth) :
    (capsL c tr i).getD k 0 = capCell (tr.L i).height (SpLv.batch' (tr.L i)) k := by
  rw [capsL, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hk),
    List.getElem_map, List.getElem_range]

theorem hon_flagsL_getD {i k : ℕ} (hk : k < 2 ^ (lvAt c i).capDepth) :
    (flagsL c tr i).getD k 0 =
      capFl (tr.L i).height (SpLv.batch' (tr.L i)) (lvAt c i).capDepth k := by
  rw [flagsL, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hk),
    List.getElem_map, List.getElem_range]

/-- **An opening's cap leaf** holds its climb's digest in the honest cap. -/
theorem hon_cap_cells {depth cd : ℕ} {batch : List (ℕ × Opening)} (hcdd : cd ≤ depth)
    (hag : BatchAgrees depth batch) {a : ℕ × Opening} (ha : a ∈ batch) :
    capCell depth batch (2 * (2 ^ cd + a.1 / 2 ^ (depth - cd))) =
        (digestHalves (climbD (merkleLeafDigest a.2.leaf) a.1 (a.2.path.take (depth - cd)))).1 ∧
      capCell depth batch (2 * (2 ^ cd + a.1 / 2 ^ (depth - cd)) + 1) =
        (digestHalves (climbD (merkleLeafDigest a.2.leaf) a.1 (a.2.path.take (depth - cd)))).2 := by
  have hv : 2 ^ cd + a.1 / 2 ^ (depth - cd) = heapNode depth a.1 (depth - cd) := by
    unfold heapNode; rw [show depth - (depth - cd) = cd by omega]
  have hnd := nodeD_eq hag ha (nodeIs_climb (a := a) (l := depth - cd) (by omega))
  rw [hv, capCell_even, capCell_odd, hnd]
  exact ⟨rfl, rfl⟩

/-- **An opening's cap leaf's parent** is flagged in the honest cap. -/
theorem hon_cap_flag {depth cd : ℕ} {batch : List (ℕ × Opening)} (hcd : 2 ≤ cd)
    (hcdd : cd ≤ depth) {a : ℕ × Opening} (ha : a ∈ batch) :
    capFl depth batch cd (2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1)) = 1 := by
  have hw : 2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1) = heapNode depth a.1 (depth - cd + 1) := by
    unfold heapNode; rw [show depth - (depth - cd + 1) = cd - 1 by omega]
  rcases capFl_cases (depth := depth) (batch := batch) cd
      (2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1)) with ⟨e, -⟩ | ⟨-, hn⟩
  · exact e
  · exact absurd ⟨a, ha, depth - cd + 1, le_rfl, by omega, hw⟩ hn

/-! ## The queries' value -/

theorem hon_wp_val {l k : ℕ} (hk : k < c.maxIl) :
    (wpC c tr l).getD k 0 =
      if k < 2 ^ rwLo (lvAt c l).folds then
        (eqKernel ((tr.L l).chs.take (rwLo (lvAt c l).folds))).getD
          (rwSlot (rwLo (lvAt c l).folds) (if l = 0 then 1 else 0) k) 0
      else if k < 2 ^ rwLo (lvAt c l).folds + 2 ^ ((lvAt c l).folds - rwLo (lvAt c l).folds) then
        (eqKernel ((tr.L l).chs.drop (rwLo (lvAt c l).folds))).getD
          (rwSlot ((lvAt c l).folds - rwLo (lvAt c l).folds) (if l = 0 then 1 else 0)
            (k - 2 ^ rwLo (lvAt c l).folds)) 0
      else 0 := by
  rw [wpC, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

/-- **The queries' chain on level `l`'s honest openings is its enforced sum.** -/
theorem hon_q_ret {l : ℕ} (hrow : RowShape l (lvAt c l))
    (hil : rowLo (lvAt c l).interleave + (lvAt c l).interleave / rowLo (lvAt c l).interleave ≤
      c.maxIl)
    (hidx : (tr.L l).index = l) (hch : (tr.L l).chs.length = (lvAt c l).folds)
    (hql : (tr.L l).qs.length = (lvAt c l).queries) (hos : (tr.L l).os.length = (tr.L l).qs.length)
    (hlam : (tr.L l).lam ≠ 0)
    (hleaf : ∀ k < (lvAt c l).queries, ((tr.L l).os.getD k default).leaf.length =
      lvWidth l (lvAt c l)) :
    oqChain ((lvAt c l).queries % 2 * (if l = 0 then 1 else 0)) (if l = 0 then 1 else 0)
        (tr.L l).lam⁻¹
        (fun k ↦ rowDot (if l = 0 then 1 else 0) (lvAt c l).interleave
          ((tr.L l).os.getD k default).leaf fun i ↦ (wpC c tr l).getD i 0)
        ((lvAt c l).queries / (1 + if l = 0 then 1 else 0)) * (tr.L l).lam ^ (lvAt c l).queries =
      (tr.L l).enforced := by
  have hodd : (lvAt c l).queries % 2 * (if l = 0 then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  have hb : (if l = 0 then 1 else 0) = 1 ∨
      ((if l = 0 then 1 else 0) = 0 ∧ (lvAt c l).queries % 2 * (if l = 0 then 1 else 0) = 0) := by
    split_ifs <;> simp
  have h1 := oqChain_powers hlam hodd hb (fun k ↦ rowDot (if l = 0 then 1 else 0)
    (lvAt c l).interleave ((tr.L l).os.getD k default).leaf fun i ↦ (wpC c tr l).getD i 0)
    ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))
  rw [oqCount_q] at h1
  rw [h1]
  have hrl : (tr.L l).rows.length = (tr.L l).qs.length := by
    unfold SpLv.rows; split_ifs <;> simp [hos]
  unfold SpLv.enforced
  rw [← hrl, enforcedSum_eq, hrl, hql]
  unfold powSum
  refine congrArg (List.foldl _ 0) (List.map_congr_left fun k hk ↦ ?_)
  have hk' : k < (lvAt c l).queries := List.mem_range.mp hk
  refine congrArg ((tr.L l).lam ^ k * ·) ?_
  have hko : k < (tr.L l).os.length := by omega
  have hrowk : (tr.L l).rows.getD k [] = specRow l ((tr.L l).os.getD k default).leaf := by
    have e : (tr.L l).rows = ((tr.L l).os.map (·.leaf)).map (specRow l) := by
      unfold SpLv.rows specRow
      rw [hidx]
      by_cases h0 : l = 0
      · simp only [h0, ↓reduceIte]
      · simp only [h0, ↓reduceIte]
    rw [e, List.getD_eq_getElem _ _ (by simpa using hko), List.getElem_map, List.getElem_map,
      List.getD_eq_getElem _ _ hko]
  beta_reduce
  rw [hrowk]
  have hlen := hleaf k hk'
  obtain ⟨hf, hI⟩ := hrow
  unfold lvWidth at hlen
  by_cases h0 : l = 0
  · subst h0
    simp only [↓reduceIte] at hf hI hlen ⊢
    rw [hI] at hlen hil ⊢
    rw [hf] at hch
    rw [rowLo_64] at hil
    simp only [specRow, ↓reduceIte]
    refine rowDot_level0 hlen hch (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · rw [hon_wp_val (by omega), hf]
      simp [rwSlot, hi, show rwLo 6 = 3 from rfl]
    · rw [hon_wp_val (by omega), hf]
      simp only [rwSlot, show rwLo 6 = 3 from rfl] at *
      have p3 : (2 : ℕ) ^ 3 = 8 := rfl
      simp only [↓reduceIte, p3, show ¬ 8 + i < 8 by omega, show 8 + i < 8 + 8 by omega]
      congr 1
      omega
  · simp only [h0, ↓reduceIte] at hf hI hlen ⊢
    rw [hI] at hlen hil ⊢
    rw [hf] at hch
    rw [rowLo_16] at hil
    simp only [specRow, h0, ↓reduceIte]
    refine rowDot_deeper (by simpa using hlen) hch (fun i hi ↦ ?_) (fun i hi ↦ ?_)
    · rw [hon_wp_val (by omega), hf]
      simp [rwSlot, hi, h0, show rwLo 4 = 3 from rfl]
    · rw [hon_wp_val (by omega), hf]
      simp only [rwSlot, show rwLo 4 = 3 from rfl] at *
      have p3 : (2 : ℕ) ^ 3 = 8 := rfl
      have p1 : (2 : ℕ) ^ (4 - 3) = 2 := rfl
      simp only [h0, ↓reduceIte, p3, p1, show ¬ 8 + i < 8 by omega, show 8 + i < 8 + 2 by omega,
        zero_ne_one, Nat.add_sub_cancel_left]

theorem lqIters_lvBase (q i : ℕ) : lqIters q (lvBase i) = q / (1 + if i = 0 then 1 else 0) := by
  unfold lqIters lvBase
  by_cases h0 : i = 0 <;> simp [h0]

/-! ## The residual -/

theorem residualProd_congr (vals : List E) (x : E) {d d' : ℕ → E} :
    ∀ n, (∀ t < n, d t = d' t) → residualProd vals x d n = residualProd vals x d' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [residualProd]
    rw [residualProd_congr vals x n (fun t ht ↦ h t (by omega)), h n (by omega)]

/-- `query_positions` holds level `i`'s decoded positions from its offset. -/
theorem hon_qposC (hs : OsSizes c) {i : ℕ} (hi : i < c.levels.length) {j : ℕ}
    (hj : j < (lvAt c i).squeezes * (192 / (lvAt c i).depth)) :
    (qposC c tr).getD ((lvAt c i).posOff + j) 0 = posAt c tr i j := by
  have hend := off_end (off := fun i ↦ (lvAt c i).posOff)
    (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hs.pos
    (c.levels.length - 1 - i) i (by omega)
  have hend' : (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth) ≤
      c.levels.length * ligPosCap := hend
  have hown : ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length ((lvAt c i).posOff + j) = i := by
    have := ownerOf_eq (off := fun i ↦ (lvAt c i).posOff)
      (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hs.pos (i := i)
      (k := (lvAt c i).posOff + j) (by omega) (by
      show (lvAt c i).posOff + j < (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth)
      omega) (c.levels.length - 1 - i) (by omega)
    rwa [show i + 1 + (c.levels.length - 1 - i) = c.levels.length by omega] at this
  rw [qposC, List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range]
  simp only [hown, Nat.add_sub_cancel_left, hj, ↓reduceIte]

/-- `basis_d` holds level `i`'s coefficients from `i · ligColsCap`. -/
theorem hon_bdC {i s : ℕ} (hi : i < c.levels.length) (hs : s < ligColsCap) :
    (bdC c tr).getD (i * ligColsCap + s) 0 = finD c tr i s := by
  have hlt : i * ligColsCap + s < c.levels.length * ligColsCap := by
    have := Nat.mul_le_mul_right ligColsCap (show i + 1 ≤ c.levels.length by omega)
    rw [Nat.add_mul, one_mul] at this; omega
  rw [bdC, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_range,
    Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt hs, Nat.mod_eq_of_lt hs, Nat.zero_add]

/-- **Level `i`'s residual** is the chain over its positions and its row of `basis_d`. -/
theorem hon_res {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    (hs : OsSizes c) {i : ℕ} (hi : i < c.levels.length) :
    finH c tr i = lrAcc (fun s ↦ (bdC c tr).getD (i * ligColsCap + s) 0) (lvAt c i).logCols
      (finM tr i) (fun k ↦ (qposC c tr).getD ((lvAt c i).posOff + k) 0) (lvAt c i).queries := by
  have hb := h.lvb i hi
  have hspan : (lvAt c i).queries ≤ (lvAt c i).squeezes * (192 / (lvAt c i).depth) := by
    rw [hb.squeezes]; exact ceilDiv_mul_ge hb.per
  have hv : (lvAt c i).vanish = vanishOfCols (lvAt c i).logCols := (hF.lv i hi).van
  have hcols : (lvAt c i).logCols ≤ ligColsCap := hs.cols i hi
  have hp : (List.range (lvAt c i).queries).map (Pof tr.rs i) =
      (List.range (lvAt c i).queries).map fun k ↦ (qposC c tr).getD ((lvAt c i).posOff + k) 0 :=
    List.map_congr_left fun k hk ↦ by
      have hk' := List.mem_range.mp hk
      rw [hon_qposC hs hi (by omega), posAt_eq h hi hk']
  unfold finH lrAcc resFold resFoldC
  rw [hv, hp]
  refine congrArg (fun F ↦ List.foldl F 0 _) (funext fun a ↦ funext fun p ↦ ?_)
  rw [residualProd_congr _ _ (lvAt c i).logCols fun t ht ↦ (hon_bdC hi (by omega)).symm]

/-! ## A level -/

/-- **Level `i`'s honest data**, at a configuration whose buffers fit its rows and whose cap
checks are `verify_merkle_cap`'s. -/
theorem lvHelperFacts_of {μ r : ℕ} {cfg : List Whir.Level} {target : E} {S : KeccakState}
    {xs : List E} {os : List (List Opening)} {root : Digest} (hF : CandFacts c μ r cfg)
    (hs : OsSizes c)
    (hil : ∀ i < c.levels.length,
      rowLo (lvAt c i).interleave + (lvAt c i).interleave / rowLo (lvAt c i).interleave ≤ c.maxIl)
    (hmc : ∀ i < c.levels.length,
      ("verify_merkle_cap__L" ++ natStr (lvAt c i).capDepth, (lvAt c i).capDepth) ∈ merkleCapNames)
    (h : TrFit c tr) (hR : TrRun c μ r target S xs os root tr)
    (hcaps : CapsAgree μ r target S xs os root) {i : ℕ} (hi : i < c.levels.length) :
    LvHelperFacts c tr i := by
  have hil' : i < tr.Ls.length := by rw [h.len]; exact hi
  obtain ⟨R, d, hOk⟩ := h.ok i hi
  have hb := h.lvb i hi
  have hfit := h.fit i hi
  have hD : (tr.L i).D = (lvAt c i).depth := by rw [SpLv.D, hfit.ml, hb.depth]
  have hh : (tr.L i).height = (lvAt c i).depth := by rw [hR.height i hil', hD]
  have hwd : (tr.L i).width = lvWidth i (lvAt c i) := hR.width i hil'
  have hcdd := hb.cdd
  have hcd2 := hb.cd
  have hql : (tr.L i).qs.length = (lvAt c i).queries := by rw [SpLv.qs_length, hb.queries]
  have hos : (tr.L i).os.length = (tr.L i).qs.length := hOk.osLen
  have hch : (tr.L i).chs.length = (lvAt c i).folds := by rw [SpLv.chs_length, hfit.fold]
  have hmem : tr.L i ∈ tr.Ls := by
    rw [OsTr.L, List.getD_eq_getElem _ _ hil']; exact List.getElem_mem hil'
  have hag := SpLv.batchAgrees (tr.L i) hcaps (hR.qs _ hmem)
  have hopen : ∀ k < (lvAt c i).queries,
      ((tr.L i).os.getD k default).leaf.length = lvWidth i (lvAt c i) ∧
        ((tr.L i).os.getD k default).path.length = (lvAt c i).depth := by
    intro k hk
    obtain ⟨e1, e2, -⟩ := openOne_facts (hOk.opens k (by omega) (by omega))
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact ⟨by rw [e1, hwd], by rw [e2, hh]⟩
  obtain ⟨S2, hS2⟩ := hon_F2_cap (tr.L i)
  refine ⟨by rw [hS2]; rfl, by rw [hS2]; exact Whir.capOf_canonical S2,
    fun j hj t ht ↦ hon_pos h hi hj ht, hOk.lam, ?_, hon_res hF h hs hi⟩
  refine ⟨capsL c tr i, flagsL c tr i, fun k ↦ (tr.L i).qs.getD k 0,
    fun k ↦ ((tr.L i).os.getD k default).leaf,
    fun k ↦ ((tr.L i).os.getD k default).path.take ((lvAt c i).depth - (lvAt c i).capDepth),
    ?_, fun k hk ↦ hon_qs h hi hk, ?_⟩
  · -- the cap, the flags and the openings
    dsimp only [LqCaps, lqShape]
    refine ⟨by simp [capsL], by simp [flagsL], fun rd CAP FL hC hFl ↦ ?_, fun k hk ↦ ?_⟩
    · exact (verify_merkle_cap_holds _ (hmc i hi) rd _ _).mpr
        (cap_meaning_at h hR hcaps hC hFl hi hcdd)
    · have hk1 : k < (tr.L i).qs.length := by omega
      have hk2 : k < (tr.L i).os.length := by omega
      have ha : ((tr.L i).qs.getD k 0, (tr.L i).os.getD k default) ∈ SpLv.batch' (tr.L i) := by
        rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2, SpLv.batch']
        exact List.mem_iff_getElem.mpr ⟨k, by simp; omega, by simp⟩
      have hq : (tr.L i).qs.getD k 0 < 2 ^ (lvAt c i).depth := by
        rw [List.getD_eq_getElem _ _ hk1, ← hD]; exact SpLv.qs_lt _ _ (List.getElem_mem _)
      have hcddH : (lvAt c i).capDepth ≤ (tr.L i).height := by rw [hh]; exact hcdd
      obtain ⟨hc1, hc2⟩ := hon_cap_cells (batch := SpLv.batch' (tr.L i)) hcddH hag ha
      have hfl := hon_cap_flag (batch := SpLv.batch' (tr.L i)) hcd2 hcddH ha
      dsimp only at hc1 hc2 hfl
      -- the bounds of the cells and the flag
      have hd1 : (tr.L i).qs.getD k 0 / 2 ^ ((lvAt c i).depth - (lvAt c i).capDepth) <
          2 ^ (lvAt c i).capDepth :=
        Nat.div_lt_of_lt_mul (by rw [← pow_add, Nat.sub_add_cancel hcdd]; exact hq)
      have hd2 : (tr.L i).qs.getD k 0 / 2 ^ ((lvAt c i).depth - (lvAt c i).capDepth + 1) <
          2 ^ ((lvAt c i).capDepth - 1) :=
        Nat.div_lt_of_lt_mul (by
          rw [← pow_add, show (lvAt c i).depth - (lvAt c i).capDepth + 1 +
            ((lvAt c i).capDepth - 1) = (lvAt c i).depth by omega]; exact hq)
      have e2 : 2 ^ (lvAt c i).capDepth = 2 * 2 ^ ((lvAt c i).capDepth - 1) := by
        rw [← pow_succ']; congr 1; omega
      refine ⟨by rw [Nat.sub_add_cancel hcdd]; exact hq, ?_, ?_, ?_, ?_, ?_⟩
      · rw [(hopen k hk).1]
        unfold Oq.R lvWidth lvBase
        by_cases h0 : i = 0 <;> simp [h0]
      · rw [List.length_take, (hopen k hk).2]; omega
      · rw [hon_capsL_getD (by omega), ← hh]; exact hc1
      · rw [hon_capsL_getD (by omega), ← hh]; exact hc2
      · rw [hon_flagsL_getD (by omega), ← hh]; exact hfl
  · -- the enforced sum
    rw [lqIters_lvBase]
    exact (hon_q_ret hb.row (hil i hi) (hR.index i hil') hch hql hos hOk.lam
      fun k hk ↦ (hopen k hk).1).symm

/-! ## Every arm -/

/-- **The honest trace has the helpers' data**, at every arm and rate. -/
theorem os_helper_facts : os_helper_facts_Spec := by
  intro m hm ri hri cfg hF S root target xs os w s' roots' _ _ hcaps tr h hR i hi
  obtain ⟨hs, hil⟩ := osSizesB_sound (osSizesB_all m hm ri hri)
  obtain ⟨-, -, hnm, -⟩ := candB_sound (candB_all m ri hm hri)
  exact lvHelperFacts_of hF hs hil (fun i hi ↦ (hnm i hi).1.2.2.2.2.1) h hR hcaps hi

end
end LeanVM.Guest.B1
