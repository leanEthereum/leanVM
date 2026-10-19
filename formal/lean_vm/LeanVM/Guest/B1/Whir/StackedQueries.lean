/-
  LeanVM.Guest.B1.Whir.StackedQueries

  A level's queries in `open_stacked`: the row weights, the cap's root, `opening_queries`, and the
  intro message, as the openings `queryP` reads and the enforced sum.
-/

module

public import LeanVM.Guest.B1.Whir.StackedLoops

/-!
# A level's queries (TRIAGE #36, through #28-30, #34, #35)

`osQueries` (G:1176-1193): `opening_row_weights` of the level's fold challenges, the cap's root
(`verify_merkle_cap`) stored at the level's root slot, `opening_queries` over the positions, then
the intro message. In the specification's terms (`osQueries_sound`): one opening per position
(the leaf, the path's siblings, then the cap's siblings) climbing to the root, and the query sum
is `enforcedSum` (V:1622) of the rows `queryP` gives.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The rows and the climb -/

/-- The rows `whirLevelsOpen` reads from the words of commitment `index` (V:1740-1741). -/
def osRowsOf (index : ℕ) (words : List (List K)) : List (List E) :=
  if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow

private theorem climb_append_list (D : Digest) (q : ℕ) : ∀ ss ts : List Digest,
    climb (m := Id) blake2sBytes D q (ss ++ ts) =
      climb (m := Id) blake2sBytes (climb (m := Id) blake2sBytes D q ss) (q / 2 ^ ss.length) ts
  | [], ts => by simp; rfl
  | s :: ss, ts => by
    rw [List.cons_append, climb_cons, climb_cons, climb_append_list _ _ ss ts, List.length_cons,
      Nat.div_div_eq_div_mul, pow_succ']

theorem leafRowWord_one (leaf : List K) (jw : ℕ) : leafRowWord 1 leaf jw = ofK (leaf.getD jw 0) := by
  simp [leafRowWord, oqRowWord]

theorem leafRowWord_zero (leaf : List K) (jw : ℕ) :
    leafRowWord 0 leaf jw = E.ofLimbs (leaf.getD (3 * jw) 0) (leaf.getD (3 * jw + 1) 0)
      (leaf.getD (3 * jw + 2) 0) := by
  simp [leafRowWord, oqRowWord]

/-- Level 0's row: the leaf read from the top down against the reversed weights. -/
theorem os_dot_row0 {f : ℕ} {leaf : List K} (hl : leaf.length = 2 ^ f) {lf : List E}
    (hlf : lf.length = f) :
    dot (leaf.reverse.map ofK) (eqKernel lf) =
      ∑ jw ∈ Finset.range (2 ^ f), leafRowWord 1 leaf jw * (eqKernel lf).getD (orwSlot f 1 jw) 0 := by
  rw [os_dot_eq_sum' _ _ (by simp [hl, length_eqKernel, hlf]), List.length_map, List.length_reverse, hl,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun jw hjw => ?_
  have hj := Finset.mem_range.mp hjw
  rw [leafRowWord_one, orwSlot, ite_pos' rfl, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_reverse (by rw [hl]; omega)]
  simp only [hl, show 2 ^ f - 1 - (2 ^ f - 1 - jw) = jw by omega]
  simp only [List.getD_eq_getElem?_getD, mul_eq_mul_right_iff]
  left
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-- A deeper level's row: its words regrouped by three. -/
theorem os_dot_rowExt {f : ℕ} {leaf : List K} (hl : leaf.length = 3 * 2 ^ f) {lf : List E}
    (hlf : lf.length = f) :
    dot (extRow leaf) (eqKernel lf) =
      ∑ jw ∈ Finset.range (2 ^ f), leafRowWord 0 leaf jw * (eqKernel lf).getD (orwSlot f 0 jw) 0 := by
  rw [os_dot_eq_sum' _ _ (by rw [os_extRow_length _ _ hl, length_eqKernel, hlf]), os_extRow_length _ _ hl]
  refine Finset.sum_congr rfl fun jw hjw => ?_
  rw [os_extRow_getD _ _ hl jw (Finset.mem_range.mp hjw), leafRowWord_zero, orwSlot, ite_neg' (by decide)]

/-! ## A query as an opening -/

/-- **A query's opening** (V:543-552): the leaf `QueryOk` gives and its path, the siblings below
the cap then the cap's own (`capSibs`), climb to the cap's root, which the refutation argument
(`cap_climb`) reaches from the cap leaf. -/
private theorem queryOk_opening {base I depth cd : ℕ} {rew qsc qw qbp flags cap : E} {i q : ℕ}
    {root : Digest} (hcd : 1 ≤ cd) (hcdd : cd ≤ depth) (hq : q < 2 ^ depth)
    (hroot : CapHashed rd cap 1) (hint : ∀ c, 2 ≤ c → c < 2 ^ cd → CapFlagged rd flags cap c)
    (hcell : CapCell rd cap 1 root)
    (h : QueryOk base I depth cd rd rew qsc qw qbp flags cap i q) :
    ∃ o : Opening, o.leaf.length = oqR base I ∧ o.path.length = depth ∧
      climb (m := Id) blake2sBytes (hashWords o.leaf) q o.path = root ∧
      ∃ s w, LoadHolds rd qsc i s ∧ LoadHolds rd qw i w ∧ LoadHolds rd qsc (i + 1)
        (s + w * ∑ jw ∈ Finset.range I, leafRowWord base o.leaf jw * memAt rd rew jw) := by
  obtain ⟨-, -, -, leaf, hlen, -, hsum, sibs, hsl, -, -, hcc, hfl⟩ := h
  set x := q / 2 ^ (depth - cd)
  have hx : x < 2 ^ cd := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show cd + (depth - cd) = depth by omega]
    exact hq
  have hc1 : 2 ^ cd ≤ 2 ^ cd + x := Nat.le_add_right _ _
  have hc2 : 2 ^ cd + x < 2 ^ (cd + 1) := by rw [pow_succ]; omega
  have hhalf : (2 ^ cd + x) / 2 = 2 ^ (cd - 1) + q / 2 ^ (depth - cd + 1) := by
    obtain ⟨c, rfl⟩ : ∃ c, cd = c + 1 := ⟨cd - 1, by omega⟩
    rw [pow_succ, Nat.add_sub_cancel, pow_succ, ← Nat.div_div_eq_div_mul]
    omega
  have htop := cap_climb hroot hint cd (2 ^ cd + x) hcd le_rfl hc1 hc2 (by rw [hhalf]; exact hfl)
  rw [capNode_eq hcc, capNode_eq hcell, Nat.add_sub_cancel_left] at htop
  refine ⟨⟨leaf, sibs ++ capSibs rd cap cd (2 ^ cd + x)⟩, hlen, ?_, ?_, hsum⟩
  · simp only [List.length_append, length_capSibs, hsl]; omega
  · simp only
    rw [climb_append_list, hsl]
    exact htop

private theorem rowsOf_getD (lvl : ℕ) (f : ℕ → Opening) (n i : ℕ) (hi : i < n) :
    (osRowsOf lvl (((List.range n).map f).map (·.leaf))).getD i [] =
      if lvl = 0 then (f i).leaf.reverse.map ofK else extRow (f i).leaf := by
  unfold osRowsOf
  split <;> simp [List.getD_eq_getElem?_getD, hi]

private theorem length_rowsOf (lvl : ℕ) (words : List (List K)) : (osRowsOf lvl words).length = words.length := by
  unfold osRowsOf; split <;> simp

theorem osMat_eq {base off k : ℕ} {m : List Stmt × ℕ × ℕ} (hm : osMat base off k = m)
    (hoff : off < 2 ^ 128) {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ m.1 True kret) : σ (.n m.2.1) = σ (.n base) * gen ^ off := by
  subst hm; exact osMat_sound hoff h

/-- **A level's queries** (G:1176-1193), in the specification's terms: the cap's root `root` at
the level's root slot, one opening per position climbing to it (what `queryP` reads), the query
sum `enforcedSum` (V:1622) of their rows, and the intro message's `c0, c2` read. -/
theorem osQueries_sound {cfg : OsCfg} {lv : OsLvl} {lvl rev : ℕ} (hrev : rev = if lvl = 0 then 1 else 0)
    (hrw : ∀ a r, coreProgram.Rel rd lv.rowWeights a r → MeaningOpeningRowWeights lv.folds rev rd a r)
    (hcapM : ∀ a r, coreProgram.Rel rd lv.verifyCap a r → MeaningVerifyMerkleCap lv.capDepth rd a r)
    (hqM : ∀ (n : ℕ) (pos : ℕ → ℕ) (cap flags qw qbp rew : E) (rets : List E), n < ordG →
      QueryBits rd qbp n lv.depth pos →
      coreProgram.Rel rd lv.queriesFn [cap, flags, qw, qbp, rew, gen ^ n] rets →
      ∃ qsc, MeaningOpeningQueries rev (2 ^ lv.folds) lv.depth lv.capDepth n pos rd qsc
        [cap, flags, qw, qbp, rew, gen ^ n] rets)
    (hcd : 1 ≤ lv.capDepth) (hcdd : lv.capDepth ≤ lv.depth)
    (hb1 : lv.foldsOff < 2 ^ 128) (hb2 : 4 * lv.capOff < 2 ^ 128) (hb4 : lvl * cfg.maxQ < 2 ^ 128)
    (hb5 : lv.posOff < 2 ^ 128) (hnq : lv.queries < 2 ^ 63)
    {lf : List E} (hlfl : lf.length = lv.folds)
    (hlf : ∀ j < lv.folds, LoadHolds rd (σ (.n osFch)) (lv.foldsOff + j) (lf.getD j 0))
    {lam : E} (hqw : ∀ i < lv.queries, LoadHolds rd (σ (.n osQw)) (lvl * cfg.maxQ + i) (lam ^ i))
    {pos : ℕ → ℕ} (hbits : QueryBits rd (σ (.n osQbp) * gen ^ lv.posOff) lv.queries lv.depth pos)
    {cur : E} {s : OsSt} {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs)
    {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osQueries cfg lv lvl s).1 True kret) :
    ∃ (root : Digest) (os : List Opening) (c0 c2 : E),
      LoadHolds rd (σ (.n osRoots)) (2 * lvl) (digestScalars root).1 ∧
      LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) (digestScalars root).2 ∧
      os.length = lv.queries ∧
      (∀ j (hj : j < os.length), (os[j]).leaf.length = oqR rev (2 ^ lv.folds) ∧
        (os[j]).path.length = lv.depth ∧
        climb (m := Id) blake2sBytes (hashWords (os[j]).leaf) (pos j) (os[j]).path = root) ∧
      σ (.n (osQueries cfg lv lvl s).2.2.1) =
        enforcedSum (osRowsOf lvl (os.map (·.leaf))) lf (powers lam lv.queries) ∧
      OsCur rd σ cur (osQueries cfg lv lvl s).2.1 (obsCv (obsCv cv c0) c2) (xs ++ [c0, c2]) ∧
      (osQueries cfg lv lvl s).2.1.co = s.co + 2 ∧
      σ (.n (osQueries cfg lv lvl s).2.2.2.1) = c0 ∧
      σ (.n (osQueries cfg lv lvl s).2.2.2.2.1) = σ (.n (osQueries cfg lv lvl s).2.2.1) + c2 ∧
      σ (.n (osQueries cfg lv lvl s).2.2.2.2.2) = c2 := by
  unfold osQueries at h ⊢
  simp only at h ⊢
  generalize hp : osMat osFch lv.foldsOff (s.k + 2) = p at h ⊢
  generalize hcp : osMat osCaps (4 * lv.capOff) p.2.2 = cp at h ⊢
  generalize hfp : osMat osFlags lv.capOff cp.2.2 = fp at h ⊢
  generalize hcp2 : osMat osCaps (4 * lv.capOff) (fp.2.2 + 2) = cp2 at h ⊢
  generalize hfp2 : osMat osFlags lv.capOff cp2.2.2 = fp2 at h ⊢
  generalize hqp : osMat osQw (lvl * cfg.maxQ) fp2.2.2 = qp at h ⊢
  generalize hbp : osMat osQbp lv.posOff qp.2.2 = bp at h ⊢
  simp only [holdsList_append] at h
  obtain ⟨-, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hP, h⟩ := holdsList_true_of (by rw [← hp]; exact osMat_noRet _ _ _) h
  obtain ⟨hW, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hCP, h⟩ := holdsList_true_of (by rw [← hcp]; exact osMat_noRet _ _ _) h
  obtain ⟨hFP, h⟩ := holdsList_true_of (by rw [← hfp]; exact osMat_noRet _ _ _) h
  obtain ⟨hCap, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hCP2, h⟩ := holdsList_true_of (by rw [← hcp2]; exact osMat_noRet _ _ _) h
  obtain ⟨hFP2, h⟩ := holdsList_true_of (by rw [← hfp2]; exact osMat_noRet _ _ _) h
  obtain ⟨hQP, h⟩ := holdsList_true_of (by rw [← hqp]; exact osMat_noRet _ _ _) h
  obtain ⟨hBP, h⟩ := holdsList_true_of (by rw [← hbp]; exact osMat_noRet _ _ _) h
  obtain ⟨hQS, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hI0, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hI2, h⟩ := holdsList_true_of (by rfl) h
  have ep := osMat_eq hp hb1 hP
  have ecp := osMat_eq hcp hb2 hCP
  have efp := osMat_eq hfp (by omega) hFP
  have ecp2 := osMat_eq hcp2 hb2 hCP2
  have efp2 := osMat_eq hfp2 (by omega) hFP2
  have eqp := osMat_eq hqp hb4 hQP
  have ebp := osMat_eq hbp hb5 hBP
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    and_true] at hW hCap hQS h
  -- the row weights are the level's fold challenges'
  obtain ⟨-, rs, hrsl, hrsr, hrew⟩ := hrw _ _ hW
  have hrs : rs = lf := List.ext_getElem (by rw [hrsl, hlfl]) fun j h1 h2 => by
    have := hrsr j h1
    rw [ep, loadHolds_mul_gen_pow] at this
    have h' := hlf j (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at h'
    exact loadHolds_unique this h'
  rw [hrs] at hrew
  -- the cap's root
  obtain ⟨hcapC, lr0, lr1⟩ := hCap
  obtain ⟨-, hroot, hint, root, hcell, hret⟩ := hcapM _ _ hcapC
  simp only [List.cons.injEq] at hret
  obtain ⟨r0, r1, -⟩ := hret
  -- the queries
  obtain ⟨eg, hqcall⟩ := hQS
  rw [eg, os_gw_eq (by omega), ecp2, ← ecp, efp2, ← efp, eqp, ebp] at hqcall
  obtain ⟨qsc, -, l0, hok, sN, lN, hsN⟩ := hqM _ pos _ _ _ _ _ _ (by simp only [ordG]; omega) hbits hqcall
  simp only [List.cons.injEq, and_true] at hsN
  have : Nonempty Opening := ⟨⟨[], []⟩⟩
  have hop := fun i (hi : i < lv.queries) =>
    queryOk_opening (rd := rd) hcd hcdd (hbits i hi).1 hroot hint hcell (hok i hi)
  choose! oOf hlen hplen hclimb hsum using hop
  set D : ℕ → E := fun i => ∑ jw ∈ Finset.range (2 ^ lv.folds), leafRowWord rev (oOf i).leaf jw *
    memAt rd (σ (.n (s.k + 1))) jw
  have hchain : ∀ i ≤ lv.queries, LoadHolds rd qsc i (∑ i' ∈ Finset.range i, lam ^ i' * D i') := by
    intro i hi
    induction i with
    | zero => simpa using l0
    | succ i ih =>
      obtain ⟨s', w, ls, lw, ls1⟩ := hsum i (by omega)
      rw [loadHolds_mul_gen_pow] at lw
      have hw := loadHolds_unique lw (hqw i (by omega))
      have hs := loadHolds_unique ls (ih (by omega))
      rw [hw, hs] at ls1
      rw [Finset.sum_range_succ]
      exact ls1
  have hsum' := loadHolds_unique lN (hchain _ le_rfl)
  -- the intro message
  have hat1 : OsCur rd σ cur { s with k := bp.2.2 + 2 } cv xs := ⟨hat.fs, hat.reads, hat.cursor⟩
  have hat2 := osFsNext_sound hat1 hI0
  have hat3 := osFsNext_sound hat2 hI2
  rw [List.append_assoc, List.singleton_append] at hat3
  refine ⟨root, (List.range lv.queries).map oOf, _, _, ?_, ?_, by simp, fun j hj => ?_, ?_,
    ⟨hat3.fs, hat3.reads, hat3.cursor⟩, rfl, rfl, h, rfl⟩
  · rw [← r0]; exact lr0
  · rw [← r1]; exact lr1
  · simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range]
    exact ⟨hlen j hj, hplen j hj, hclimb j hj⟩
  · rw [hsN, hsum', os_enforcedSum_eq _ _ _ (by simp [os_length_powersFrom, length_rowsOf, powers]),
      length_rowsOf, List.length_map, List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [os_powers_getD hi', rowsOf_getD _ _ _ _ hi']
    congr 1
    have hmem : ∀ jw < 2 ^ lv.folds, memAt rd (σ (.n (s.k + 1))) jw =
        (eqKernel lf).getD (orwSlot lv.folds rev jw) 0 := fun jw hjw => memAt_of_load (hrew jw hjw)
    simp only [D]
    rw [Finset.sum_congr rfl fun jw hjw => by rw [hmem jw (Finset.mem_range.mp hjw)]]
    by_cases h0 : lvl = 0
    · simp only [h0, ↓reduceIte] at hrev ⊢
      subst hrev
      exact (os_dot_row0 (by rw [hlen i hi']; simp [oqR]) hlfl).symm
    · simp only [h0, ↓reduceIte] at hrev ⊢
      subst hrev
      exact (os_dot_rowExt (by rw [hlen i hi']; simp [oqR]) hlfl).symm

end
end LeanVM.Guest.B1
