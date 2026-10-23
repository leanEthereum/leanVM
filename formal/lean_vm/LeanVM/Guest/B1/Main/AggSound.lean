/-
  LeanVM.Guest.B1.Main.AggSound

  B1 for `aggregate_claims` (G:3319-3486; TRIAGE #77), soundness: the claim it stores is
  `Node.batch`'s, the same values in the same order.
-/

module

public import LeanVM.Guest.B1.Main.AggLoop99
public import LeanVM.Guest.B1.Main.FreshWeight

/-!
# `aggregate_claims`, soundly

The body's transcript (`obs` of the count, `__loop95`), its lambdas (`__loop96`, `__loop98`), its
two sumchecks (`batch_sumcheck`), its weights (`__loop97`, `eqtree`, `__loop99`) and its two checks
are `Node.batch`'s, run on the chain (`batch_spec`), on the claims the buffers hold
(`ChildClaimsAt`); the bytecode sumcheck's hints are `bc_sumcheck_msgs` and `bc_star_hint`, the
matrices' `mat_sumcheck_msgs` and `mat_stars_hint`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-! ## The lambdas -/

/-- The state after `c` children's double squeeze. -/
def sqIt2 (cv : Digest) (c : ℕ) : Digest := (fun d => sqCv (sqCv d))^[c] cv

/-- The state after `c` children's triple squeeze. -/
def sqIt3 (cv : Digest) (c : ℕ) : Digest := (fun d => sqCv (sqCv (sqCv d)))^[c] cv

theorem sq2_spec : ∀ (n : ℕ) (cv : Digest), (sq2 n cv).2 = sqIt2 cv n ∧ (sq2 n cv).1.length = n ∧
    ∀ c (h : c < (sq2 n cv).1.length), (sq2 n cv).1[c] =
      (challengeOf (sqCv (sqIt2 cv c)), challengeOf (sqCv (sqCv (sqIt2 cv c))))
  | 0, cv => ⟨rfl, rfl, fun c h => absurd h (by simp [sq2])⟩
  | n + 1, cv => by
    obtain ⟨h1, h2, h3⟩ := sq2_spec n (sqCv (sqCv cv))
    refine ⟨by rw [sq2, h1]; rfl, by simp [sq2, h2], fun c hc => ?_⟩
    cases c with
    | zero => rfl
    | succ c =>
      simp only [sq2, List.getElem_cons_succ]
      rw [h3 c (by simpa [sq2] using hc)]
      rfl

theorem sq3_spec : ∀ (n : ℕ) (cv : Digest), (sq3 n cv).2 = sqIt3 cv n ∧ (sq3 n cv).1.length = n ∧
    ∀ c (h : c < (sq3 n cv).1.length), (sq3 n cv).1[c] =
      (challengeOf (sqCv (sqIt3 cv c)), challengeOf (sqCv (sqCv (sqIt3 cv c))),
        challengeOf (sqCv (sqCv (sqCv (sqIt3 cv c)))))
  | 0, cv => ⟨rfl, rfl, fun c h => absurd h (by simp [sq3])⟩
  | n + 1, cv => by
    obtain ⟨h1, h2, h3⟩ := sq3_spec n (sqCv (sqCv (sqCv cv)))
    refine ⟨by rw [sq3, h1]; rfl, by simp [sq3, h2], fun c hc => ?_⟩
    cases c with
    | zero => rfl
    | succ c =>
      simp only [sq3, List.getElem_cons_succ]
      rw [h3 c (by simpa [sq3] using hc)]
      rfl

theorem sqIt2_succ (cv : Digest) (c : ℕ) : sqIt2 cv (c + 1) = sqCv (sqCv (sqIt2 cv c)) :=
  Function.iterate_succ_apply' _ _ _

theorem sqIt3_succ (cv : Digest) (c : ℕ) : sqIt3 cv (c + 1) = sqCv (sqCv (sqCv (sqIt3 cv c))) :=
  Function.iterate_succ_apply' _ _ _

/-! ## Sums over children -/

theorem sumE_append_one (l : List E) (x : E) : sumE (l ++ [x]) = sumE l + x := by
  simp [sumE, List.foldl_append]

theorem sumE_zipWith_take_succ {α β : Type} (g : α → β → E) (cs : List α) (l : List β) (c : ℕ)
    (h1 : c < cs.length) (h2 : c < l.length) :
    sumE (List.zipWith g (cs.take (c + 1)) (l.take (c + 1))) =
      sumE (List.zipWith g (cs.take c) (l.take c)) + g cs[c] l[c] := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.toList_some, Option.toList_some,
    List.zipWith_append (by simp; omega), List.zipWith_cons_cons, List.zipWith_nil_left,
    sumE_append_one]

/-! ## Cells -/

theorem batchRounds_length (claim : E) (rounds : List (E × E)) (cv : Digest) :
    ((batchRounds claim rounds).run cv).1.1.length = rounds.length := by
  rw [batchRounds_run, bsRun_eq]; simp

/-- The cells of a deferred claim of the guest's shape, by their `DEFER_STMT_*` offsets. -/
theorem deferCells_getD {d : DeferredClaim} (h1 : d.bytecodePoint.length = 22)
    (h2 : d.matrixPoint.length = 28) :
    d.cells.length = 53 ∧ (∀ k < 22, d.cells.getD k 0 = d.bytecodePoint.getD k 0) ∧
      d.cells.getD 22 0 = d.bytecodeValue ∧
      (∀ k < 28, d.cells.getD (23 + k) 0 = d.matrixPoint.getD k 0) ∧
      d.cells.getD 51 0 = d.matrixA ∧ d.cells.getD 52 0 = d.matrixB := by
  have key : ∀ i, d.cells.getD i 0 =
      if i < 22 then d.bytecodePoint.getD i 0 else if i = 22 then d.bytecodeValue else
      if i < 51 then d.matrixPoint.getD (i - 23) 0 else if i = 51 then d.matrixA else
      if i = 52 then d.matrixB else 0 := by
    intro i
    simp only [DeferredClaim.cells, List.getD_eq_getElem?_getD, List.getElem?_append,
      List.length_append, List.length_cons, List.length_nil, h1, h2]
    split_ifs <;> first | omega | (simp_all; done) |
      (rw [List.getElem?_eq_none (by simp; omega)]; rfl)
  refine ⟨by simp [DeferredClaim.cells, h1, h2], fun k hk => ?_, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [key]; simp [hk]
  · rw [key]; simp
  · rw [key, ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel_left]
  · rw [key]; simp
  · rw [key]; simp

theorem readsAt_getD {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem readsAt_eq_of_getD {p : E} {f xs l : List E} {n : ℕ} (hf : ReadsAt rd p f)
    (hx : ReadsAt rd p xs) (hfl : f.length = n) (hl : l.length = n) (hxl : n ≤ xs.length)
    (h : ∀ k < n, xs.getD k 0 = l.getD k 0) : f = l := by
  apply List.ext_getElem (by rw [hfl, hl])
  intro k h1 h2
  have := loadHolds_unique (hf k h1) (readsAt_getD hx (by omega))
  rw [this, h k (by omega), List.getD_eq_getElem _ _ h2]

/-! ## The body -/

theorem noRetList_eqtreeT (pt : V) (off : ℕ) (out : V) (b : ℕ) :
    Stmt.noRetList (eqtreeT pt off out b) = true := by
  rw [eqtreeT, noRetList_append, noRetList_flatten _ (by
    simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun t _ => noRetList_etLayer ..)]
  rfl

theorem noRetList_agStores : Stmt.noRetList agStores = true := by
  rw [agStores, noRetList_append, noRetList_append, noRetList_append, noRetList_flatten _ (by
    simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun t _ => rfl), noRetList_flatten _ (by
    simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun t _ => rfl)]
  rfl

theorem find_aggregate_claims : coreProgram.find? "aggregate_claims" = some Data.core29 :=
  Program.find?_of_indexOf? (j := 29) (by decide +kernel) rfl

theorem fsCompress_out {σ : Val} {s0 s1 x : V} {b : ℕ} {cv : Digest}
    (h : ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      ∀ k, 2 ≤ k → k < 14 → σ (.n (b + k)) = fsVals (σ x) cv 1 k)
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    (σ (.n (b + 12)), σ (.n (b + 13))) = digestScalars (obsCv cv (σ x)) := by
  obtain ⟨cv', hcv', e⟩ := h
  have := digestScalars_injective (hcv'.symm.trans hcv)
  subst this
  rw [e 12 (by omega) (by omega), e 13 (by omega) (by omega)]
  rfl

theorem guestU_congr {z z' : E} {zchi lrr zp er ec rr zchi' lrr' zp' er' ec' rr' : ℕ → E}
    (hz : z = z') (h1 : ∀ k < 8, zchi k = zchi' k) (h2 : ∀ k < 8, lrr k = lrr' k)
    (h3 : ∀ i < 64, zp i = zp' i) (h4 : ∀ i < 64, er i = er' i) (h5 : ∀ i < 64, ec i = ec' i)
    (h6 : ∀ k < 28, rr k = rr' k) :
    guestU z zchi lrr zp er ec rr = guestU z' zchi' lrr' zp' er' ec' rr' := by
  subst hz
  have e1 : ∑ i ∈ Finset.range 64, lagNum z i * er i = ∑ i ∈ Finset.range 64, lagNum z i * er' i :=
    Finset.sum_congr rfl fun i hi => by rw [h4 i (Finset.mem_range.mp hi)]
  have e2 : ∏ k ∈ Finset.range 8, (1 + zchi k + rr (6 + k)) =
      ∏ k ∈ Finset.range 8, (1 + zchi' k + rr' (6 + k)) :=
    Finset.prod_congr rfl fun k hk => by
      have := Finset.mem_range.mp hk; rw [h1 k this, h6 (6 + k) (by omega)]
  have e3 : ∑ i ∈ Finset.range 64, zp i * ec i = ∑ i ∈ Finset.range 64, zp' i * ec' i :=
    Finset.sum_congr rfl fun i hi => by
      have := Finset.mem_range.mp hi; rw [h3 i this, h5 i this]
  have e4 : ∏ j ∈ Finset.range 8, (1 + lrr j + rr (27 - j)) =
      ∏ j ∈ Finset.range 8, (1 + lrr' j + rr' (27 - j)) :=
    Finset.prod_congr rfl fun j hj => by
      have := Finset.mem_range.mp hj; rw [h2 j this, h6 (27 - j) (by omega)]
  rw [guestU, guestU, e1, e2, e3, e4]

/-- **`aggregate_claims`, soundly** (G:3319-3486; TRIAGE #77). -/
theorem aggregate_claims_sound (args rets : List E)
    (h : coreProgram.Rel rd "aggregate_claims" args rets) : Meaning_aggregate_claims rd args rets := by
  rw [rel_iff_sem find_aggregate_claims] at h
  obtain ⟨σ, hp, h⟩ := h
  rw [show Fn.params Data.core29 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl] at hp
  rw [core29_body, agBody] at h
  simp only [holdsList_append, holds_fsCompressT (.n 12) (.n 13) (.n 0) 14 (by decide : 1 < 256)] at h
  rw [holdsList_noRet (eqtreeT (.n 90) 0 (.n 96) 97) (noRetList_eqtreeT ..),
    holdsList_noRet (eqtreeT (.n 90) 14 (.n 301) 302) (noRetList_eqtreeT ..),
    holdsList_noRet agStores noRetList_agStores] at h
  generalize hE1 : Stmt.HoldsList (coreProgram.Rel rd) rd σ (eqtreeT (.n 90) 0 (.n 96) 97) True
    (fun rs => rs = rets) = E1 at h
  generalize hE2 : Stmt.HoldsList (coreProgram.Rel rd) rd σ (eqtreeT (.n 90) 14 (.n 301) 302) True
    (fun rs => rs = rets) = E2 at h
  generalize hSt : Stmt.HoldsList (coreProgram.Rel rd) rd σ agStores True (fun rs => rs = rets) = St
    at h
  simp only [agP1, agP2, agP3, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gen, word_one, word_zero] at h
  obtain ⟨-, -, -, -, -, -, -, -, c12, c13, hfs,
    c28, h29, h30, -, l26, l27, c32, h33, c34, -, hl95,
    h35, h36, h37, -, c39, h40, h41, h42, -, l44a, l44b, l45a, l45b, c46, l46, c47, h48, c49, -, hl96,
    h50, h51, h52, l53, l54, l55, -, hbs22, h60, h61, c62, h63, -, c65, l65, c66, h67, c68, -, hl97,
    h69, l70, h71, he59, h72, h73, -, c75, h76, h77, h78, -, l60, l61, c80, l80, c81, h82, c83, -, hl98,
    h84, h85, h86, l87, l88, l89, -, hbs28, h94, h95, -,
    hE1', -, hE2', c506, h507, h508, -, c510, l510, c511, l511, c512, h513, c514, -, hl99,
    h515, h516, l517, h518, l519, h520, h521, he93, hSt', hret⟩ := h
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), by rw [← hp]; rfl, hret.symm,
    fun cs hne hlen hng hCC => ?_⟩
  have hn0 : 0 < cs.length := List.length_pos_iff.mpr hne
  -- the claims at the buffers
  have hC : ∀ c (hc : c < cs.length),
      LoadHolds rd (σ (.n 1)) (2 * c) (digestScalars cs[c].publicInput).1 ∧
      LoadHolds rd (σ (.n 1)) (2 * c + 1) (digestScalars cs[c].publicInput).2 ∧
      FreshShaped cs[c].fresh ∧ ReadsAt rd (σ (.n 2) * gen ^ (106 * c)) (fixedCells cs[c].fresh) ∧
      cs[c].carried.bytecodePoint.length = 22 ∧ cs[c].carried.matrixPoint.length = 28 ∧
      ReadsAt rd (σ (.n 3) * gen ^ (53 * c)) cs[c].carried.cells := hCC
  -- the transcript's start
  have hseed0 : (σ (.n 12), σ (.n 13)) = digestScalars (blake2sBytes batchLabel) := by
    rw [c12, c13]; exact aggSeed_eq
  have hcv1 := fsCompress_out hfs hseed0
  rw [hng, gen_pow_eq_ofK] at hcv1
  simp only [Nat.reduceAdd] at hcv1
  obtain ⟨cv1, ecv1⟩ : ∃ x, x = obsCv (blake2sBytes batchLabel) (ofK (Parameters.gpow cs.length)) :=
    ⟨_, rfl⟩
  rw [← ecv1] at hcv1
  -- the transcript, child by child
  have r95 := loop_sound (rd := rd) (f := "__loop95")
    (ps := [σ (.n 0), σ (.n 31), σ (.n 1), σ (.n 2), σ (.n 10), σ (.n 3), σ (.n 11)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop95_step x hx)
    (by rw [h33, c32, c34] at hl95; exact hl95)
  have hAbs : ∀ c ≤ cs.length,
      LoadHolds rd (σ (.n 31)) (2 * c) (digestScalars (obsAll cv1 ((cs.take c).flatMap childCells))).1 ∧
      LoadHolds rd (σ (.n 31)) (2 * c + 1)
        (digestScalars (obsAll cv1 ((cs.take c).flatMap childCells))).2 ∧
      ∀ c' < c, LoadHolds rd (σ (.n 10)) c' (σ (.n 2) * gen ^ (106 * c')) ∧
        LoadHolds rd (σ (.n 11)) c' (σ (.n 3) * gen ^ (53 * c')) := by
    intro c hc
    induction c with
    | zero =>
      refine ⟨?_, ?_, fun _ h => absurd h (by omega)⟩
      · rw [show σ (.n 26) = _ from congrArg Prod.fst hcv1] at l26; simpa [obsAll] using l26
      · rw [show σ (.n 27) = _ from congrArg Prod.snd hcv1] at l27; simpa [obsAll] using l27
    | succ c ih =>
      obtain ⟨a0, a1, arows⟩ := ih (by omega)
      obtain ⟨s0, s1, q0, q1, hall⟩ := r95 c (by omega) c rfl
      obtain ⟨p0, p1, fs, cs', w0, w1, hfl, hfr, hcl, hcr, wf, wc, o0, o1⟩ :=
        hall _ (Prod.ext (loadHolds_unique q0 a0) (loadHolds_unique q1 a1))
      obtain ⟨g0, g1, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      have e0 := loadHolds_unique w0 g0
      have e1 := loadHolds_unique w1 g1
      have efs : fs = fixedCells cs[c].fresh := readsAt_unique hfr gfr (by rw [hfl, (fixedCells_getD gsh).1])
      have ecs : cs' = cs[c].carried.cells := readsAt_unique hcr gcr (by rw [hcl, (deferCells_getD gb gm).1])
      have htk : (cs.take (c + 1)).flatMap childCells =
          (cs.take c).flatMap childCells ++ childCells cs[c] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.flatMap_append, List.flatMap_singleton]
      have hob : obsAll cv1 ((cs.take (c + 1)).flatMap childCells) =
          obsAll (obsAll cv1 ((cs.take c).flatMap childCells)) (p0 :: p1 :: (fs ++ cs')) := by
        rw [htk, e0, e1, efs, ecs, obsAll, obsAll, obsAll, List.foldl_append]
        rfl
      refine ⟨by rw [hob, show 2 * (c + 1) = 2 * c + 2 by ring]; exact o0,
        by rw [hob, show 2 * (c + 1) + 1 = 2 * c + 3 by ring]; exact o1, fun c' hc' => ?_⟩
      rcases Nat.lt_or_ge c' c with h' | h'
      · exact arows c' h'
      · rw [show c' = c by omega]; exact ⟨wf, wc⟩
  obtain ⟨cvA, ecvA⟩ : ∃ x, x = obsAll cv1 (cs.flatMap childCells) := ⟨_, rfl⟩
  obtain ⟨a0, a1, hRows⟩ := hAbs cs.length le_rfl
  rw [List.take_length, ← ecvA] at a0 a1
  -- the bytecode lambdas
  obtain ⟨lB, elB⟩ : ∃ l, l = (sq2 cs.length cvA).1 := ⟨_, rfl⟩
  obtain ⟨hsq2a, hsq2b, hsq2c⟩ := sq2_spec cs.length cvA
  rw [← elB] at hsq2b hsq2c
  have e35 : σ (.n 35) = gen ^ (2 * cs.length) := by rw [h35, hng]; ring
  rw [h36, e35, loadHolds_mul_gen_pow, Nat.add_zero] at l44a
  rw [h36, e35, loadHolds_mul_gen_pow] at l45a
  rw [← loadHolds_unique a0 l44a] at l44b
  rw [← loadHolds_unique a1 l45a] at l45b
  rw [c46] at l46
  have r96 := loop_sound (rd := rd) (f := "__loop96")
    (ps := [σ (.n 0), σ (.n 43), σ (.n 38), σ (.n 10), σ (.n 11)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop96_step x hx)
    (by rw [h48, c47, c49] at hl96; exact hl96)
  have hBC : ∀ c ≤ cs.length,
      LoadHolds rd (σ (.n 43)) (3 * c) (digestScalars (sqIt2 cvA c)).1 ∧
      LoadHolds rd (σ (.n 43)) (3 * c + 1) (digestScalars (sqIt2 cvA c)).2 ∧
      LoadHolds rd (σ (.n 43)) (3 * c + 2) (sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue) (cs.take c) (lB.take c))) ∧
      ∀ c' < c, LoadHolds rd (σ (.n 38)) (2 * c') (lB.getD c' (0, 0)).1 ∧
        LoadHolds rd (σ (.n 38)) (2 * c' + 1) (lB.getD c' (0, 0)).2 := by
    intro c hc
    induction c with
    | zero => exact ⟨l44b, l45b, by simpa [sumE] using l46, fun _ h => absurd h (by omega)⟩
    | succ c ih =>
      obtain ⟨b0, b1, b2, blam⟩ := ih (by omega)
      obtain ⟨s0, s1, q0, q1, hall⟩ := r96 c (by omega) c rfl
      obtain ⟨wl0, wl1, ws0, ws1, fp, cp, acc, fv, cv', wfp, wcp, wacc, wfv, wcv, wnew⟩ :=
        hall _ (Prod.ext (loadHolds_unique q0 b0) (loadHolds_unique q1 b1))
      obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      obtain ⟨wr, wc'⟩ := hRows c (by omega)
      have efp := loadHolds_unique wfp wr
      have ecp := loadHolds_unique wcp wc'
      subst efp ecp
      have efv := loadHolds_unique wfv (readsAt_getD gfr (by rw [(fixedCells_getD gsh).1]; omega))
      have ecv := loadHolds_unique wcv (readsAt_getD gcr (by rw [(deferCells_getD gb gm).1]; omega))
      rw [(fixedCells_getD gsh).2.2.1] at efv
      rw [(deferCells_getD gb gm).2.2.1] at ecv
      have eacc := loadHolds_unique wacc b2
      have hl : lB.getD c (0, 0) = (challengeOf (sqCv (sqIt2 cvA c)),
          challengeOf (sqCv (sqCv (sqIt2 cvA c)))) := by
        rw [List.getD_eq_getElem _ _ (by omega), hsq2c c (by omega)]
      refine ⟨?_, ?_, ?_, fun c' hc' => ?_⟩
      · rw [sqIt2_succ, show 3 * (c + 1) = 3 * c + 3 by ring]; exact ws0
      · rw [sqIt2_succ, show 3 * (c + 1) + 1 = 3 * c + 4 by ring]; exact ws1
      · rw [show 3 * (c + 1) + 2 = 3 * c + 5 by ring, sumE_zipWith_take_succ _ _ _ _ (by omega)
          (by omega), ← List.getD_eq_getElem _ (0, 0) (by omega), hl, ← eacc, ← efv, ← ecv, ← add_assoc]
        exact wnew
      · rcases Nat.lt_or_ge c' c with h' | h'
        · exact blam c' h'
        · rw [show c' = c by omega, hl]; exact ⟨wl0, wl1⟩
  obtain ⟨b0, b1, b2, hLB⟩ := hBC cs.length le_rfl
  rw [List.take_length, show lB.take cs.length = lB by rw [← hsq2b, List.take_length]] at b2
  -- the bytecode sumcheck
  have e51 : σ (.n 51) = gen ^ (3 * cs.length) := by rw [h51, h50, hng]; ring
  rw [h52, e51, loadHolds_mul_gen_pow, Nat.add_zero] at l53
  rw [h52, e51, loadHolds_mul_gen_pow] at l54 l55
  have hbs := (batch_sumcheck_L22_iff rd _ _).mp hbs22
  obtain ⟨cvB, rounds, rs, final, cvC, hcvB, hrl, hmsg, hrun, hrs, hrets⟩ := hbs
  rw [← loadHolds_unique b0 l53, ← loadHolds_unique b1 l54] at hcvB
  have ecvB : cvB = sqIt2 cvA cs.length := (digestScalars_injective hcvB).symm
  subst ecvB
  rw [← loadHolds_unique b2 l55] at hrun
  simp only [List.cons.injEq, and_true] at hrets
  obtain ⟨r57, r58, r59⟩ := hrets
  have hrsl : rs.length = 22 := by
    have := congrArg (fun x => x.1.1.length) hrun
    simp only at this
    rw [batchRounds_length] at this
    rw [← this, hrl]
  -- the bytecode weight
  rw [c65] at l65
  have r97 := loop_sound (rd := rd) (f := "__loop97")
    (ps := [σ (.n 0), σ (.n 10), σ (.n 11), σ (.n 56), σ (.n 64), σ (.n 38)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop97_step x hx)
    (by rw [h67, c66, c68] at hl97; exact hl97)
  have hW : ∀ c ≤ cs.length, LoadHolds rd (σ (.n 64)) c (sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint rs + l.2 * eqEval c.carried.bytecodePoint rs)
      (cs.take c) (lB.take c))) := by
    intro c hc
    induction c with
    | zero => simpa [sumE] using l65
    | succ c ih =>
      obtain ⟨fp, cp, wfp, wcp, r, f, g, hrl', hfl, hgl, hr, hf, hg, w, lf, lc, ww, wlf, wlc, wnew⟩ :=
        r97 c (by omega) c rfl
      obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      obtain ⟨wr, wc'⟩ := hRows c (by omega)
      have efp := loadHolds_unique wfp wr
      have ecp := loadHolds_unique wcp wc'
      subst efp ecp
      have er : r = rs := readsAt_unique hr hrs (by rw [hrl', hrsl])
      have ef : f = cs[c].fresh.bytecodePoint := readsAt_eq_of_getD hf gfr hfl gsh.1
        (by rw [(fixedCells_getD gsh).1]; omega) (fixedCells_getD gsh).2.1
      have eg : g = cs[c].carried.bytecodePoint := readsAt_eq_of_getD hg gcr hgl gb
        (by rw [(deferCells_getD gb gm).1]; omega) (deferCells_getD gb gm).2.1
      obtain ⟨l0, l1⟩ := hLB c (by omega)
      rw [loadHolds_unique wlf l0, loadHolds_unique wlc l1, loadHolds_unique ww (ih (by omega)),
        er, ef, eg] at wnew
      rw [sumE_zipWith_take_succ _ _ _ _ (by omega) (by omega), ← List.getD_eq_getElem _ (0, 0)
        (by omega), ← add_assoc]
      exact wnew
  have hWn := hW cs.length le_rfl
  rw [List.take_length, show lB.take cs.length = lB by rw [← hsq2b, List.take_length]] at hWn
  rw [h69, hng, loadHolds_mul_gen_pow, Nat.add_zero] at l70
  have hbcF : final = σ (.n 7) * sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.fresh.bytecodePoint rs + l.2 * eqEval c.carried.bytecodePoint rs) cs lB) := by
    rw [← r59, e_add_eq_zero_iff.mp he59, h71, loadHolds_unique l70 hWn]
  -- the matrix lambdas
  obtain ⟨lM, elM⟩ : ∃ l, l = (sq3 cs.length cvC).1 := ⟨_, rfl⟩
  obtain ⟨hsq3a, hsq3b, hsq3c⟩ := sq3_spec cs.length cvC
  rw [← elM] at hsq3b hsq3c
  rw [h60, r57] at l60
  rw [h61, r58] at l61
  rw [c80] at l80
  have r98 := loop_sound (rd := rd) (f := "__loop98")
    (ps := [σ (.n 0), σ (.n 79), σ (.n 74), σ (.n 10), σ (.n 11)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop98_step x hx)
    (by rw [h82, c81, c83] at hl98; exact hl98)
  have hMC : ∀ c ≤ cs.length,
      LoadHolds rd (σ (.n 79)) (3 * c) (digestScalars (sqIt3 cvC c)).1 ∧
      LoadHolds rd (σ (.n 79)) (3 * c + 1) (digestScalars (sqIt3 cvC c)).2 ∧
      LoadHolds rd (σ (.n 79)) (3 * c + 2) (sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.matrixValue + l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB)
        (cs.take c) (lM.take c))) ∧
      ∀ c' < c, LoadHolds rd (σ (.n 74)) (3 * c') (lM.getD c' (0, 0, 0)).1 ∧
        LoadHolds rd (σ (.n 74)) (3 * c' + 1) (lM.getD c' (0, 0, 0)).2.1 ∧
        LoadHolds rd (σ (.n 74)) (3 * c' + 2) (lM.getD c' (0, 0, 0)).2.2 := by
    intro c hc
    induction c with
    | zero => exact ⟨l60, l61, by simpa [sumE] using l80, fun _ h => absurd h (by omega)⟩
    | succ c ih =>
      obtain ⟨b0, b1, b2, blam⟩ := ih (by omega)
      obtain ⟨s0, s1, q0, q1, hall⟩ := r98 c (by omega) c rfl
      obtain ⟨wl0, wl1, wl2, ws0, ws1, fp, cp, acc, fv, ca, cb, wfp, wcp, wacc, wfv, wca, wcb, wnew⟩ :=
        hall _ (Prod.ext (loadHolds_unique q0 b0) (loadHolds_unique q1 b1))
      obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      obtain ⟨wr, wc'⟩ := hRows c (by omega)
      have efp := loadHolds_unique wfp wr
      have ecp := loadHolds_unique wcp wc'
      subst efp ecp
      have efv := loadHolds_unique wfv (readsAt_getD gfr (by rw [(fixedCells_getD gsh).1]; omega))
      have eca := loadHolds_unique wca (readsAt_getD gcr (by rw [(deferCells_getD gb gm).1]; omega))
      have ecb := loadHolds_unique wcb (readsAt_getD gcr (by rw [(deferCells_getD gb gm).1]; omega))
      rw [(fixedCells_getD gsh).2.2.2.2.2.2.2.2] at efv
      rw [(deferCells_getD gb gm).2.2.2.2.1] at eca
      rw [(deferCells_getD gb gm).2.2.2.2.2] at ecb
      have eacc := loadHolds_unique wacc b2
      have hl : lM.getD c (0, 0, 0) = (challengeOf (sqCv (sqIt3 cvC c)),
          challengeOf (sqCv (sqCv (sqIt3 cvC c))), challengeOf (sqCv (sqCv (sqCv (sqIt3 cvC c))))) := by
        rw [List.getD_eq_getElem _ _ (by omega), hsq3c c (by omega)]
      refine ⟨?_, ?_, ?_, fun c' hc' => ?_⟩
      · rw [sqIt3_succ, show 3 * (c + 1) = 3 * c + 3 by ring]; exact ws0
      · rw [sqIt3_succ, show 3 * (c + 1) + 1 = 3 * c + 4 by ring]; exact ws1
      · rw [show 3 * (c + 1) + 2 = 3 * c + 5 by ring, sumE_zipWith_take_succ _ _ _ _ (by omega)
          (by omega), ← List.getD_eq_getElem _ (0, 0, 0) (by omega), hl, ← eacc, ← efv, ← eca, ← ecb,
          ← add_assoc, ← add_assoc]
        exact wnew
      · rcases Nat.lt_or_ge c' c with h' | h'
        · exact blam c' h'
        · rw [show c' = c by omega, hl]; exact ⟨wl0, wl1, wl2⟩
  obtain ⟨m0, m1, m2, hLM⟩ := hMC cs.length le_rfl
  rw [List.take_length, show lM.take cs.length = lM by rw [← hsq3b, List.take_length]] at m2
  -- the matrix sumcheck
  have e85 : σ (.n 85) = gen ^ (3 * cs.length) := by rw [h85, h84, hng]; ring
  rw [h86, e85, loadHolds_mul_gen_pow, Nat.add_zero] at l87
  rw [h86, e85, loadHolds_mul_gen_pow] at l88 l89
  have hbsM := (batch_sumcheck_L28_iff rd _ _).mp hbs28
  obtain ⟨cvD, roundsM, rM, finalM, cvE, hcvD, hrlM, hmsgM, hrunM, hrM, hretsM⟩ := hbsM
  rw [← loadHolds_unique m0 l87, ← loadHolds_unique m1 l88] at hcvD
  have ecvD : cvD = sqIt3 cvC cs.length := (digestScalars_injective hcvD).symm
  subst ecvD
  rw [← loadHolds_unique m2 l89] at hrunM
  simp only [List.cons.injEq, and_true] at hretsM
  obtain ⟨-, -, r93⟩ := hretsM
  have hrMl : rM.length = 28 := by
    have := congrArg (fun x => x.1.1.length) hrunM
    simp only at this
    rw [batchRounds_length] at this
    rw [← this, hrlM]
  -- the two `eqtree`s: the equality kernels of the matrix point's row and column halves
  obtain ⟨hR1, hK1⟩ := eqtree_sound (.n 90) (.n 96) 0 97 _ (hE1 ▸ hE1')
  obtain ⟨hR2, hK2⟩ := eqtree_sound (.n 90) (.n 301) 14 302 _ (hE2 ▸ hE2')
  have eR1 : etRs σ 97 = rM.take 6 := by
    apply List.ext_getElem (by rw [length_etRs, List.length_take, hrMl]; rfl)
    intro t h1 h2
    rw [length_etRs] at h1
    have a := hR1 t h1
    rw [Nat.zero_add, List.getD_eq_getElem _ _ (by rw [length_etRs]; exact h1)] at a
    rw [loadHolds_unique a (hrM t (by omega)), List.getElem_take]
  have eR2 : etRs σ 302 = (rM.drop 14).take 6 := by
    apply List.ext_getElem (by rw [length_etRs, List.length_take, List.length_drop, hrMl]; rfl)
    intro t h1 h2
    rw [length_etRs] at h1
    have a := hR2 t h1
    rw [List.getD_eq_getElem _ _ (by rw [length_etRs]; exact h1)] at a
    rw [loadHolds_unique a (hrM (14 + t) (by omega)), List.getElem_take, List.getElem_drop]
  have cEqR : ∀ i < 64, cellAt rd (σ (.n 96)) (62 + i) = (eqKernel (rM.take 6)).getD i 0 :=
    fun i hi => by rw [← eR1]; exact cellAt_of_load (hK1 i hi)
  have cEqC : ∀ i < 64, cellAt rd (σ (.n 301)) (62 + i) = (eqKernel ((rM.drop 14).take 6)).getD i 0 :=
    fun i hi => by rw [← eR2]; exact cellAt_of_load (hK2 i hi)
  have cMp : ∀ k < 28, cellAt rd (σ (.n 90)) k = rM.getD k 0 := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact cellAt_of_load (hrM k (by omega))
  -- the matrix weights, child by child
  rw [c510] at l510
  rw [c511] at l511
  have r99 := loop_sound (rd := rd) (f := "__loop99")
    (ps := [σ (.n 0), σ (.n 10), σ (.n 96), σ (.n 90), σ (.n 301), σ (.n 11), σ (.n 74), σ (.n 509)])
    (m := cs.length) (N := σ (.n 0)) (by unfold ordG; omega) hng (fun x hx => loop99_step x hx)
    (by rw [h513, c512, c514] at hl99; exact hl99)
  have hWS : ∀ c ≤ cs.length,
      LoadHolds rd (σ (.n 509)) (2 * c) (sumE (List.zipWith (fun c l ↦
        l.1 * freshWeight c.fresh rM + l.2.1 * eqEval c.carried.matrixPoint rM)
        (cs.take c) (lM.take c))) ∧
      LoadHolds rd (σ (.n 509)) (2 * c + 1) (sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.alpha * freshWeight c.fresh rM + l.2.2 * eqEval c.carried.matrixPoint rM)
        (cs.take c) (lM.take c))) := by
    intro c hc
    induction c with
    | zero => exact ⟨by simpa [sumE] using l510, by simpa [sumE] using l511⟩
    | succ c ih =>
      obtain ⟨w0, w1⟩ := ih (by omega)
      obtain ⟨fp, cp, wfp, wcp, wn0, wn1⟩ := r99 c (by omega) c rfl
      obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC c (by omega)
      obtain ⟨wr, wc'⟩ := hRows c (by omega)
      have efp := loadHolds_unique wfp wr
      have ecp := loadHolds_unique wcp wc'
      subst efp ecp
      have cF : ∀ k < 106, cellAt rd (σ (.n 2) * gen ^ (106 * c)) k =
          (fixedCells cs[c].fresh).getD k 0 :=
        fun k hk => cellAt_of_load (readsAt_getD gfr (by rw [(fixedCells_getD gsh).1]; exact hk))
      have cC : ∀ k < 53, cellAt rd (σ (.n 3) * gen ^ (53 * c)) k = cs[c].carried.cells.getD k 0 :=
        fun k hk => cellAt_of_load (readsAt_getD gcr (by rw [(deferCells_getD gb gm).1]; exact hk))
      have hP : ∏ k ∈ Finset.range 28, (1 + cellAt rd (σ (.n 3) * gen ^ (53 * c)) (23 + k) +
          cellAt rd (σ (.n 90)) k) = eqEval cs[c].carried.matrixPoint rM := by
        rw [eqEval_prod _ _ 28 gm hrMl]
        exact Finset.prod_congr rfl fun k hk => by
          have := Finset.mem_range.mp hk
          rw [cC (23 + k) (by omega), (deferCells_getD gb gm).2.2.2.1 k this, cMp k this]
      have hU := guestU_congr (cF 24 (by omega)) (fun k hk => cF (25 + k) (by omega))
        (fun j hj => cF (33 + j) (by omega)) (fun i hi => cF (41 + i) (by omega)) cEqR cEqC cMp
      rw [guestU_eq gsh hrMl] at hU
      obtain ⟨l0, l1, l2⟩ := hLM c (by omega)
      rw [hU, hP, cellAt_of_load w0, cellAt_of_load l0, cellAt_of_load l1] at wn0
      rw [hU, hP, cellAt_of_load w1, cellAt_of_load l0, cellAt_of_load l2, cF 23 (by omega),
        (fixedCells_getD gsh).2.2.2.1] at wn1
      refine ⟨?_, ?_⟩
      · rw [show 2 * (c + 1) = 2 * c + 2 by ring, sumE_zipWith_take_succ _ _ _ _ (by omega)
          (by omega), ← List.getD_eq_getElem _ (0, 0, 0) (by omega), ← add_assoc]
        exact wn0
      · rw [show 2 * (c + 1) + 1 = 2 * c + 3 by ring, sumE_zipWith_take_succ _ _ _ _ (by omega)
          (by omega), ← List.getD_eq_getElem _ (0, 0, 0) (by omega), ← add_assoc]
        exact wn1
  obtain ⟨n0, n1⟩ := hWS cs.length le_rfl
  rw [List.take_length, show lM.take cs.length = lM by rw [← hsq3b, List.take_length]] at n0 n1
  -- the final check
  have e515 : σ (.n 515) = gen ^ (2 * cs.length) := by rw [h515, hng]; ring
  rw [h516, e515, loadHolds_mul_gen_pow, Nat.add_zero] at l517
  rw [h516, e515, loadHolds_mul_gen_pow] at l519
  have hmF : finalM = σ (.n 8) * sumE (List.zipWith (fun c l ↦
        l.1 * freshWeight c.fresh rM + l.2.1 * eqEval c.carried.matrixPoint rM) cs lM) +
      σ (.n 9) * sumE (List.zipWith (fun c l ↦
        l.1 * c.fresh.alpha * freshWeight c.fresh rM + l.2.2 * eqEval c.carried.matrixPoint rM)
        cs lM) := by
    rw [← r93, e_add_eq_zero_iff.mp he93, h521, h518, h520, loadHolds_unique l517 n0,
      loadHolds_unique l519 n1]
  -- the stores
  have hSt2 := hSt ▸ hSt'
  rw [agStores] at hSt2
  simp only [holdsList_append] at hSt2
  rw [holdsList_range_flatten 22 (fun k => [Stmt.atom (.load (.n (522 + k)) (.n 56) k),
      .atom (.load (.n (522 + k)) (.n 4) k)]) (fun _ => rfl),
    holdsList_range_flatten 28 (fun k => [Stmt.atom (.load (.n (544 + k)) (.n 90) k),
      .atom (.load (.n (544 + k)) (.n 4) (23 + k))]) (fun _ => rfl)] at hSt2
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hSt2
  obtain ⟨hA, l7, hB, l8, l9, -⟩ := hSt2
  have hD : ReadsAt rd (σ (.n 4)) (⟨rs, σ (.n 7), rM, σ (.n 8), σ (.n 9)⟩ : DeferredClaim).cells := by
    obtain ⟨dl, d1, d2, d3, d4, d5⟩ :=
      deferCells_getD (d := ⟨rs, σ (.n 7), rM, σ (.n 8), σ (.n 9)⟩) hrsl hrMl
    intro k hk
    rw [← List.getD_eq_getElem _ 0 hk]
    rw [dl] at hk
    rcases Nat.lt_or_ge k 22 with h1 | h1
    · obtain ⟨a, b, -⟩ := hA k h1
      rw [d1 k h1]
      show LoadHolds rd _ k (rs.getD k 0)
      rw [List.getD_eq_getElem _ _ (by omega), ← loadHolds_unique a (hrs k (by omega))]
      exact b
    rcases Nat.lt_or_ge k 23 with h2 | h2
    · rw [show k = 22 by omega, d2]; exact l7
    rcases Nat.lt_or_ge k 51 with h3 | h3
    · obtain ⟨a, b, -⟩ := hB (k - 23) (by omega)
      rw [show k = 23 + (k - 23) by omega, d3 _ (by omega)]
      show LoadHolds rd _ _ (rM.getD (k - 23) 0)
      rw [List.getD_eq_getElem _ _ (by omega), ← loadHolds_unique a (hrM (k - 23) (by omega))]
      exact b
    rcases Nat.lt_or_ge k 52 with h4 | h4
    · rw [show k = 51 by omega, d4]; exact l8
    · rw [show k = 52 by omega, d5]; exact l9
  -- the batching
  refine ⟨⟨rounds, roundsM, σ (.n 7), σ (.n 8), σ (.n 9)⟩, ⟨rs, σ (.n 7), rM, σ (.n 8), σ (.n 9)⟩,
    ?_, hrsl, hrMl, hD⟩
  rw [batch_spec]
  simp only [← ecv1, ← ecvA, ← elB, hsq2a, hrun, ← elM, hsq3a, hrunM, hbcF, hmF, and_self,
    ↓reduceIte]

end
end LeanVM.Guest.B1.Main
