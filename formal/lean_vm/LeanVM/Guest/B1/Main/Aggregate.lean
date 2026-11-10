/-
  LeanVM.Guest.B1.Main.Aggregate

  `aggregate_claims`' soundness: its core IR writes the batching (`Node.batch`) of the children
  whose words the memory holds.
-/

module

public import LeanVM.Guest.B1.Main.AggBody
public import LeanVM.Guest.Batch.Def
public import LeanVM.Guest.B1.Sumcheck.Batch
public import LeanVM.Guest.B1.Bits.Grind

/-!
# `aggregate_claims` (TRIAGE G #97)

`aggregate_claims_holds : aggregate_claims_sound_Spec`, from `batch_sumcheck__L23`'s meaning
(`batch_sumcheck_holds`) and `grind_check__L2`'s (`grind_check_holds`, on the memory image). For
`n_children_g = g^m`, the hints are the nonce `bc_sumcheck_msgs[0]`, the rounds after it and
`bc_star_hint` (`aggHints`), and the claim written at `defer_stmt` is the sumcheck's point and
the hint. For `m` children whose words the memory holds (`ChildWordsAt`), `batch_fs` reads
`Node.batch` on the carried sponge:

* the absorbing rows (`__loop33`, `l25_step`) carry the sponge after the count and the first `c`
  children's words (`absorb_rows`);
* the last absorbing row is permuted, the nonce absorbed with the tag `4` and permuted
  (`aggN`, `nonce_ins`), `grind_check__L2` on that permutation's cell `1` is its proof of work,
  `λ` its cell `0`, and its capacity the sponge `batch_sumcheck__L23` starts from (`aggLam`);
* the records of `bc_chain` (`__loop34`, `l26_step`) hold `λ^(2c)` and the lambdas' combination
  of the first `c` children's values (`chain_rows`); the last one's feeds `batch_sumcheck__L23`;
* the weights (`__loop35`, `l27_step`) are the lambdas' combination of the claims' equality
  weights at the sumcheck's point (`weight_rows`), and the body checks that the final claim is
  the hint times the last.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-! ## Bookkeeping -/

theorem pend_absorbAll : ∀ (xs : List E) (s : Fs) (t : ℕ), 1 ≤ s.pend.length →
    s.pend.length ≤ 4 → (s.absorbAll xs t).pend.length = (s.pend.length - 1 + xs.length) % 4 + 1
  | [], s, t, h1, h4 => by
    show s.pend.length = _
    simp only [List.length_nil]
    omega
  | x :: xs, s, t, h1, h4 => by
    show ((s.absorb x t).absorbAll xs t).pend.length = _
    by_cases hf : s.pend.length = 4
    · have e : s.absorb x t = ⟨capOf s.perm, [(x, t)]⟩ := by simp [Fs.absorb, hf, rateScalars]
      rw [e, pend_absorbAll xs _ t (by simp) (by simp)]
      simp only [List.length_cons, List.length_nil]
      omega
    · have e : s.absorb x t = ⟨s.cap, s.pend ++ [(x, t)]⟩ := by
        simp [Fs.absorb, hf, rateScalars]
      rw [e, pend_absorbAll xs _ t (by simp) (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_cons]
      omega

/-- The lambdas of `λ`, child `c`'s pair. -/
theorem lambdaPowers_eq (lam : E) (n : ℕ) :
    Batch.lambdaPowers lam n = (List.range n).map fun i ↦ (lam ^ (2 * i), lam ^ (2 * i + 1)) :=
  rfl

/-- A running sum over the first `c + 1` children. -/
theorem zip_prefix {α : Type} (F : α → E × E → E) (cs : List α) (L : ℕ → E × E) {c : ℕ}
    (hc : c < cs.length) :
    sumE (List.zipWith F (cs.take (c + 1)) ((List.range (c + 1)).map L)) =
      sumE (List.zipWith F (cs.take c) ((List.range c).map L)) + F cs[c] (L c) := by
  rw [List.take_succ_eq_append_getElem hc, List.range_succ, List.map_append,
    List.zipWith_append (by simp; omega)]
  simp [sumE, List.foldl_append]

theorem memAt_of_reads {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    memAt rd p k = xs.getD k 0 := by
  rw [memAt_of_load (h k hk), List.getD_eq_getElem _ _ hk]

/-! ## A child's words -/

theorem childCells_eq (cc : ChildClaims) (h1 : cc.freshClaim.bytecodePoint.length = 23)
    (h2 : cc.carriedClaim.bytecodePoint.length = 23) :
    Batch.childCells cc = cc.words ++ [0, 0] := by
  have hl : cc.words.length = 50 := by
    simp [ChildClaims.words, DeferredClaim.cells, h1, h2]
  rw [Batch.childCells, padToRate, hl]
  rfl

/-- **A child's words, as the absorbing loop reads them.** -/
theorem kid_words {cpi cfresh ccarried : E} {c : ℕ} {cc : ChildClaims}
    (h : ChildWordsAt rd cpi cfresh ccarried c cc) :
    memAt rd (cfresh * (gen ^ c) ^ 24) 23 = cc.freshClaim.bytecodeValue ∧
    memAt rd (ccarried * (gen ^ c) ^ 24) 23 = cc.carriedClaim.bytecodeValue ∧
    memRun rd (cfresh * (gen ^ c) ^ 24) 23 = cc.freshClaim.bytecodePoint ∧
    memRun rd (ccarried * (gen ^ c) ^ 24) 23 = cc.carriedClaim.bytecodePoint ∧
    l25Words rd cpi cfresh ccarried (gen ^ c) = Batch.childCells cc := by
  obtain ⟨h1, h2, hp0, hp1, hf, hc⟩ := h
  have e24 : (gen ^ c) ^ 24 = gen ^ (24 * c) := by rw [← pow_mul, mul_comm]
  have e2 : (gen ^ c) ^ 2 = gen ^ (2 * c) := by rw [← pow_mul, mul_comm]
  have b23 : bytecodeVars = 23 := rfl
  rw [b23] at h1 h2
  rw [e24]
  have hfl : (DeferredClaim.cells cc.freshClaim).length = 24 := by simp [DeferredClaim.cells, h1]
  have hcl : cc.carriedClaim.cells.length = 24 := by simp [DeferredClaim.cells, h2]
  have pf := (readsAt_append.mp (show ReadsAt rd _ (cc.freshClaim.bytecodePoint ++
    [cc.freshClaim.bytecodeValue]) from hf)).1
  have pc := (readsAt_append.mp (show ReadsAt rd _ (cc.carriedClaim.bytecodePoint ++
    [cc.carriedClaim.bytecodeValue]) from hc)).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [memAt_of_reads hf (by omega)]
    simp [DeferredClaim.cells, List.getD_eq_getElem?_getD, h1]
  · rw [memAt_of_reads hc (by omega)]
    simp [DeferredClaim.cells, List.getD_eq_getElem?_getD, h2]
  · rw [readsAt_memRun pf, h1]
  · rw [readsAt_memRun pc, h2]
  · rw [childCells_eq cc h1 h2]
    have hwl : (cc.words ++ [0, 0]).length = 52 := by
      simp [ChildClaims.words, DeferredClaim.cells, h1, h2]
    refine list_eq_of_getD (n := 52) (by simp [l25Words]) hwl fun w hw => ?_
    have lhs : (l25Words rd cpi cfresh ccarried (gen ^ c)).getD w 0 =
        l25Word rd cpi cfresh ccarried (gen ^ c) w := by
      simp [l25Words, List.getD_eq_getElem?_getD, hw]
    rw [lhs, l25Word, ChildClaims.words, e2, e24]
    generalize hA2 : ([(digestHalves cc.publicInput).1, (digestHalves cc.publicInput).2] :
      List E) = A2
    have hA : A2.length = 2 := by rw [← hA2]; rfl
    have hAF : (A2 ++ DeferredClaim.cells cc.freshClaim).length = 26 := by simp [hA, hfl]
    have hAFC : (A2 ++ DeferredClaim.cells cc.freshClaim ++ cc.carriedClaim.cells).length = 50 := by
      simp [hA, hfl, hcl]
    by_cases ha : w < 50
    · rw [List.getD_append (A2 ++ DeferredClaim.cells cc.freshClaim ++ cc.carriedClaim.cells) [0, 0] 0 w
        (by rw [hAFC]; exact ha)]
      by_cases hb : w < 26
      · rw [List.getD_append (A2 ++ DeferredClaim.cells cc.freshClaim) cc.carriedClaim.cells 0 w
          (by rw [hAF]; exact hb)]
        by_cases hc2 : w < 2
        · rw [ite_pos' hc2, List.getD_append A2 (DeferredClaim.cells cc.freshClaim) 0 w (by rw [hA]; exact hc2),
            ← hA2]
          rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
          · exact memAt_of_load ((loadHolds_mul_gen_pow rd _ _ _ _).mpr hp0)
          · exact memAt_of_load ((loadHolds_mul_gen_pow rd _ _ _ _).mpr hp1)
        · rw [ite_neg' hc2, ite_pos' hb,
            List.getD_append_right A2 (DeferredClaim.cells cc.freshClaim) 0 w (by rw [hA]; omega), hA,
            memAt_of_reads hf (by omega)]
      · rw [ite_neg' (show ¬ w < 2 by omega), ite_neg' hb, ite_pos' ha,
          List.getD_append_right (A2 ++ DeferredClaim.cells cc.freshClaim) cc.carriedClaim.cells 0 w
            (by rw [hAF]; omega), hAF, memAt_of_reads hc (by omega)]
    · rw [ite_neg' (show ¬ w < 2 by omega), ite_neg' (show ¬ w < 26 by omega), ite_neg' ha,
        List.getD_append_right (A2 ++ DeferredClaim.cells cc.freshClaim ++ cc.carriedClaim.cells) [0, 0] 0 w
          (by rw [hAFC]; omega), hAFC]
      rcases (show w = 50 ∨ w = 51 by omega) with rfl | rfl <;> rfl

/-! ## The rows -/

/-- **The absorbing rows**: row `c` carries the sponge after the count and the first `c`
children's words. -/
theorem absorb_rows {absorb cpi cfresh lfT ccarried lcT : E} {m : ℕ} {cs : List ChildClaims}
    (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (L25 : ∀ c < m, L25Step rd absorb cfresh lfT ccarried lcT cpi (gen ^ c))
    (h0 : RowRel rd absorb (aggS0.absorbAll (Batch.childCountCells m) dsObserve))
    (hp0 : (aggS0.absorbAll (Batch.childCountCells m) dsObserve).pend.length = 4) :
    ∀ c ≤ m, RowRel rd (absorb * (gen ^ c) ^ 13)
      (aggS0.absorbAll (Batch.childCountCells m ++ (cs.take c).flatMap Batch.childCells) dsObserve) ∧
      (aggS0.absorbAll (Batch.childCountCells m ++ (cs.take c).flatMap Batch.childCells)
        dsObserve).pend.length = 4 := by
  intro c
  induction c with
  | zero => intro _; simpa using ⟨h0, hp0⟩
  | succ c ih =>
    intro hc
    obtain ⟨hr, hp⟩ := ih (by omega)
    have hcc : c < cs.length := by omega
    obtain ⟨-, -, -, -, hw⟩ := kid_words (hcw c hcc)
    obtain ⟨-, -, hstep⟩ := L25 c (by omega)
    rw [List.take_succ_eq_append_getElem hcc, List.flatMap_append, List.flatMap_singleton,
      ← List.append_assoc, absorbAll_append, ← hw]
    refine ⟨?_, ?_⟩
    · have := hstep _ hp hr
      rwa [show absorb * (gen ^ c) ^ 13 * gen ^ 13 = absorb * (gen ^ (c + 1)) ^ 13 by ring]
        at this
    · rw [pend_absorbAll, hp]
      · simp [l25Words]
      · omega
      · omega

/-- **The records of `bc_chain`**: record `c` holds `λ^(2c)` and the lambdas' combination of the
first `c` children's values. -/
theorem chain_rows {absorb cpi cfresh lfT ccarried lcT chainT lam : E} {m : ℕ}
    {cs : List ChildClaims} (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (L25 : ∀ c < m, L25Step rd absorb cfresh lfT ccarried lcT cpi (gen ^ c))
    (L26 : ∀ c < m, L26Step rd chainT lfT lcT (lam * lam) lam (gen ^ c))
    (h0 : memAt rd chainT 0 = 1) (hz : memAt rd chainT 1 = 0) :
    ∀ c ≤ m, memAt rd (chainT * (gen ^ c) ^ 2) 0 = lam ^ (2 * c) ∧
      memAt rd (chainT * (gen ^ c) ^ 2) 1 = sumE (List.zipWith (fun c l ↦
        l.1 * c.freshClaim.bytecodeValue + l.2 * c.carriedClaim.bytecodeValue) (cs.take c)
        (Batch.lambdaPowers lam c)) := by
  intro c
  induction c with
  | zero => intro _; simpa [Batch.lambdaPowers, sumE] using ⟨h0, hz⟩
  | succ c ih =>
    intro hc
    obtain ⟨hpow, hacc⟩ := ih (by omega)
    have hcc : c < cs.length := by omega
    obtain ⟨s2, s3⟩ := L26 c (by omega)
    obtain ⟨hp1, hp2, -⟩ := L25 c (by omega)
    obtain ⟨fv, cv, -, -, -⟩ := kid_words (hcw c hcc)
    have e2 : chainT * (gen ^ (c + 1)) ^ 2 = chainT * (gen ^ c) ^ 2 * gen ^ 2 := by ring
    refine ⟨?_, ?_⟩
    · rw [e2, memAt_of_load ((loadHolds_mul_gen_pow rd _ 2 0 _).mpr s2), hpow]
      ring
    · rw [e2, memAt_of_load ((loadHolds_mul_gen_pow rd _ 2 1 _).mpr s3), lambdaPowers_eq,
        zip_prefix _ _ _ hcc, ← lambdaPowers_eq, ← hacc, hpow, memAt_of_load hp1,
        memAt_of_load hp2, fv, cv]
      ring

/-- **The weights**: `w[c]` is the lambdas' combination of the first `c` children's equality
weights at `r`. -/
theorem weight_rows {absorb cpi cfresh lfT ccarried lcT wT chainT pt1 lam : E} {r : List E} {m : ℕ}
    {cs : List ChildClaims} (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (L25 : ∀ c < m, L25Step rd absorb cfresh lfT ccarried lcT cpi (gen ^ c))
    (L27 : ∀ c < m, L27Step rd lfT lcT pt1 chainT wT lam (gen ^ c))
    (hpow : ∀ c < m, memAt rd (chainT * (gen ^ c) ^ 2) 0 = lam ^ (2 * c))
    (hpt : (memRun rd pt1 23).map (1 + ·) = r) (hz : memAt rd wT 0 = 0) :
    ∀ c ≤ m, memAt rd (wT * gen ^ c) 0 = sumE (List.zipWith (fun c l ↦
      l.1 * eqEval c.freshClaim.bytecodePoint r + l.2 * eqEval c.carriedClaim.bytecodePoint r) (cs.take c)
      (Batch.lambdaPowers lam c)) := by
  intro c
  induction c with
  | zero => intro _; simpa [Batch.lambdaPowers, sumE] using hz
  | succ c ih =>
    intro hc
    have hcc : c < cs.length := by omega
    have hst := L27 c (by omega)
    obtain ⟨hp1, hp2, -⟩ := L25 c (by omega)
    obtain ⟨-, -, fp, cp, -⟩ := kid_words (hcw c hcc)
    rw [show wT * gen ^ (c + 1) = wT * gen ^ c * gen ^ 1 by ring,
      memAt_of_load ((loadHolds_mul_gen_pow rd _ 1 0 _).mpr hst), lambdaPowers_eq,
      zip_prefix _ _ _ hcc, ← lambdaPowers_eq, ih (by omega), hpow c (by omega),
      memAt_of_load hp1, memAt_of_load hp2, fp, cp, hpt]
    ring

/-! ## `aggregate_claims` -/

theorem headCells_eq (m : ℕ) : Batch.childCountCells m = [gen ^ m, 0, 0, 0] := rfl

theorem absorb_head (m : ℕ) : aggS0.absorbAll (Batch.childCountCells m) dsObserve =
    ⟨capOf batchSeed, [gen ^ m, 0, 0, 0].map (·, dsObserve)⟩ := by
  rw [headCells_eq, absorbAll_short aggS0 _ dsObserve (by simp [aggS0])]
  rfl

/-- The sumcheck's rounds `aggregate_claims` hints, read off the memory at `bc_sumcheck_msgs`. -/
noncomputable def aggRounds (rd : Reader) (σ : Val) : List (E × E) :=
  (List.range 23).map fun k => (memAt rd (σ (.n 6)) (1 + 2 * k), memAt rd (σ (.n 6)) (2 + 2 * k))

/-- **`aggregate_claims`' hints**, read off its valuation and the memory: the proof of work's nonce,
`bc_sumcheck_msgs`' first word, the rounds after it, the bytecode's value `bc_star_hint`. -/
noncomputable def aggHints (rd : Reader) (σ : Val) : BatchingHints :=
  ⟨memAt rd (σ (.n 6)) 0, aggRounds rd σ, σ (.n 7)⟩

theorem pairs_getD : ∀ (l : List (E × E)) (i : ℕ),
    (l.flatMap fun g => [g.1, g.2]).getD (2 * i) 0 = (l.getD i 0).1 ∧
      (l.flatMap fun g => [g.1, g.2]).getD (2 * i + 1) 0 = (l.getD i 0).2
  | [], _ => by simp
  | p :: l, 0 => by simp
  | p :: l, i + 1 => by
    have ih := pairs_getD l i
    simp only [List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact ih

/-- Rounds read from memory one word past `p` are the memory's at `1 + 2k`, `2 + 2k`. -/
theorem rounds_of_reads {rd : Reader} {p : E} {rounds : List (E × E)} {n : ℕ}
    (hl : rounds.length = n) (h : ReadsAt rd (p * gen) (rounds.flatMap fun g => [g.1, g.2])) :
    rounds = (List.range n).map fun k => (memAt rd p (1 + 2 * k), memAt rd p (2 + 2 * k)) := by
  have hlen : (rounds.flatMap fun g => [g.1, g.2]).length = 2 * n := by
    simp [List.length_flatMap, hl, mul_comm]
  refine List.ext_getElem (by simp [hl]) fun k h1 h2 => ?_
  have hk : k < n := by omega
  obtain ⟨e0, e1⟩ := pairs_getD rounds k
  have l0 := h (2 * k) (by omega)
  have l1 := h (2 * k + 1) (by omega)
  rw [← List.getD_eq_getElem _ 0, e0, ← pow_one gen, loadHolds_mul_gen_pow] at l0
  rw [← List.getD_eq_getElem _ 0, e1, ← pow_one gen, loadHolds_mul_gen_pow,
    show 1 + (2 * k + 1) = 2 + 2 * k by omega] at l1
  simp only [List.getElem_map, List.getElem_range]
  rw [memAt_of_load l0, memAt_of_load l1, List.getD_eq_getElem _ _ h1]

/-! ## The callees' meanings this proof takes -/

/-- `grind_check__L2`'s core IR gives its meaning on a memory image whose `tabs` holds the bit
windows. -/
theorem agg_grind {rd : Reader} (hm : MemOk rd) {w tabs : E} {rets : List E} (hW : WinTabs rd tabs)
    (h : coreProgram.Rel rd "grind_check__L2" [w, tabs] rets) : MeaningGrindCheck 2 [w, tabs] rets := by
  obtain ⟨κ, h16, hκ, L, rfl⟩ := hm
  exact (grind_check_holds 2 (by decide) hκ (by unfold winTabBits; omega) L w tabs hW rets).mp h

/-- **`aggregate_claims`, its hints named**: on a valuation of its body (its calls under a
relation below `coreProgram.Rel`), the meaning holds with the hints `aggHints rd σ`. -/
def MeaningAggregateClaimsW (rd : Reader) (h : BatchingHints) : List E → List E → Prop
  | [ncg, cpi, cfresh, ccarried, dst, tabs], rets => WinTabs rd tabs →
      ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      rets = [] ∧ ∃ out : DeferredClaim,
        out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batch cs h = some out
  | _, _ => False

/-- The cells of a nonce's permutation: the nonce's two cells, six zeros, the capacity of the
permutation of four waiting scalars. -/
theorem nonce_ins {s : Fs} (hs : s.pend.length = 4) (n : E) :
    s.nonceState n = permOf ([n, word 0 dsPowNonce, 0, 0, 0, 0, 0, 0] ++ capOf s.perm) := by
  have e : s.absorb n dsPowNonce = ⟨capOf s.perm, [(n, dsPowNonce)]⟩ := by
    simp [Fs.absorb, hs, rateScalars]
  rw [Fs.nonceState, e, perm_eq_cells _ (by simp)]
  rfl

/-- **`aggregate_claims` at a valuation** writes the batching, with the hints `aggHints rd σ`, of
the children whose words the memory holds. -/
theorem aggregate_claims_val {C : CallRel} {rd : Reader} (hm : MemOk rd)
    (hle : CallRel.Le C (coreProgram.Rel rd))
    {σ : Val} {args rets : List E} (hpar : Data.core33.params.map σ = args)
    (hbC : Stmt.HoldsList C rd σ (Fn.body Data.core33) False (fun rs => rs = rets)) :
    MeaningAggregateClaimsW rd (aggHints rd σ) args rets := by
  have hb := holdsList_mono hle _ id (fun _ h => h) hbC
  have hok := agg_ok
  simp only [aggOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hflat, hparams⟩, hseed⟩, hp0⟩, hz3⟩, hrate⟩,
    hg33⟩, hm42⟩, hk⟩, hrin⟩, hnA⟩, hkn⟩, hgr⟩, hm94⟩, hc99⟩, hl99⟩, hc100⟩, hl100⟩, hg34⟩,
    hm105⟩, hl106⟩, hg109⟩, hbs⟩, hpt1⟩, hc189⟩, hl189⟩, hg35⟩, hm193⟩, hl194⟩, hm195⟩, hae⟩,
    hout⟩, hl7⟩ := hok
  rw [hparams] at hpar
  subst hpar
  rw [agg_shape, holdsList_append] at hb
  obtain ⟨hall, hret⟩ := holdsList_flat aggP hflat _ _ hb
  have hr : rets = [] := by
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at hret
    exact hret.symm
  subst hr
  have hat := atoms_of_flat hall
  simp only [List.map_cons, List.map_nil, MeaningAggregateClaimsW]
  intro hW m hm1 hm16 hN
  refine ⟨trivial, ?_⟩
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hseed hz3 hrate hpt1 hout
  -- the absorbing loop
  have L25 : ∀ c < m, L25Step rd (σ (.n 33)) (σ (.n 2)) (σ (.n 8)) (σ (.n 3)) (σ (.n 9))
      (σ (.n 1)) (gen ^ c) :=
    loop_sound (f := "__loop33")
      (ps := [σ (.n 0), σ (.n 33), σ (.n 2), σ (.n 8), σ (.n 3), σ (.n 9), σ (.n 1)])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l25_step hy
        exact ⟨h1 _ _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg33 hall hne)
  -- the sumcheck
  have hbsm := (batch_sumcheck_holds rd _ _).mp (call_of_flat hall hbs)
  simp only [List.map_cons, List.map_nil, MeaningBatchSumcheck] at hbsm
  obtain ⟨rounds, hrl, hrd, hpt, hrets⟩ := hbsm
  rw [genMul_sound hg109 hat] at hrd
  have hrnd : rounds = aggRounds rd σ := rounds_of_reads hrl hrd
  have h115 : σ (.n 115) = (bsRun rounds (σ (.n 106)) ⟨[σ (.n 89), σ (.n 90), σ (.n 91),
      σ (.n 92), σ (.n 93)], []⟩).1.2 := by
    have := congrArg List.getLast? hrets
    simpa using this
  have hptl : (bsRun rounds (σ (.n 106)) ⟨[σ (.n 89), σ (.n 90), σ (.n 91), σ (.n 92),
      σ (.n 93)], []⟩).1.1.length = 23 := by rw [bsRun_len, hrl]
  refine ⟨⟨(bsRun rounds (σ (.n 106)) ⟨[σ (.n 89), σ (.n 90), σ (.n 91),
    σ (.n 92), σ (.n 93)], []⟩).1.1, σ (.n 7)⟩, hptl, ?_, ?_⟩
  · -- the claim written
    intro k hk
    simp only [DeferredClaim.cells, List.length_append, List.length_cons, List.length_nil,
      hptl] at hk
    by_cases hk23 : k < 23
    · rw [show (DeferredClaim.cells ⟨(bsRun rounds (σ (.n 106)) ⟨[σ (.n 89), σ (.n 90),
        σ (.n 91), σ (.n 92), σ (.n 93)], []⟩).1.1, σ (.n 7)⟩)[k] = _ from
        List.getElem_append_left (by rw [hptl]; exact hk23)]
      obtain ⟨h1, h2⟩ := hout k hk23
      have e := loadHolds_unique (load_sound h1 hat) (hpt k (by rw [hptl]; exact hk23))
      rw [← e]
      exact load_sound h2 hat
    · have hk' : k = 23 := by omega
      subst hk'
      rw [show (DeferredClaim.cells ⟨(bsRun rounds (σ (.n 106)) ⟨[σ (.n 89), σ (.n 90),
        σ (.n 91), σ (.n 92), σ (.n 93)], []⟩).1.1, σ (.n 7)⟩)[23] = σ (.n 7) by
          simp [DeferredClaim.cells, List.getElem_append_right, hptl]]
      exact load_sound hl7 hat
  -- the batching
  intro cs hcl hcw
  -- row 0
  have hcap0 : rowCap rd (σ (.n 33)) = capOf batchSeed := by
    refine list_eq_of_getD (n := 5) (by simp [rowCap]) (by simp [capOf]) fun i hi => ?_
    obtain ⟨hcst, hld⟩ := hseed i hi
    rw [← seed_cells i hi, ← const_sound hcst hat, ← memAt_of_load (load_sound hld hat)]
    simp [rowCap, List.getD_eq_getElem?_getD, hi]
  have hrow0 : RowRel rd (σ (.n 33)) (aggS0.absorbAll (Batch.childCountCells m) dsObserve) := by
    rw [absorb_head, ← hcap0]
    refine rowRel_full (by simp) fun j hj => ?_
    obtain ⟨r1, r2⟩ := hrate j hj
    rw [memAt_of_load (load_sound r1 hat), memAt_of_load (load_sound r2 hat)]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · have := packOf_of (packIn_sound hp0 hat)
      rw [hN] at this
      exact this
    · obtain ⟨hc, hp⟩ := hz3 0 (by omega)
      have := packOf_of (packIn_sound hp hat)
      rw [const_sound hc hat, word_zero] at this
      exact this
    · obtain ⟨hc, hp⟩ := hz3 1 (by omega)
      have := packOf_of (packIn_sound hp hat)
      rw [const_sound hc hat, word_zero] at this
      exact this
    · obtain ⟨hc, hp⟩ := hz3 2 (by omega)
      have := packOf_of (packIn_sound hp hat)
      rw [const_sound hc hat, word_zero] at this
      exact this
  have hpend0 : (aggS0.absorbAll (Batch.childCountCells m) dsObserve).pend.length = 4 := by
    rw [absorb_head]; rfl
  -- the absorbing rows
  obtain ⟨hrowm, hpendm⟩ := absorb_rows hcl hcw L25 hrow0 hpend0 m le_rfl
  rw [List.take_of_length_le (by omega), show Batch.childCountCells m ++ cs.flatMap Batch.childCells =
    Batch.cellsBeforeChallenge cs by rw [Batch.cellsBeforeChallenge, hcl]] at hrowm hpendm
  have hrow42 : RowRel rd (σ (.n 42)) (aggAbs cs) := by
    rw [monoIs_sound hm42 hat, hN]
    exact hrowm
  -- the last row's permutation
  have hin := rowIn_sound hrin hat
  have hout1 := DupSpec.keccak_facts (keccak_sound hk hat)
  rw [hin, ← rowRel_perm hrow42] at hout1
  have o : ∀ c (hc : c < 13), σ (.n (60 + c)) = cellsOfState (aggAbs cs).perm false ⟨c, hc⟩ :=
    fun c hc => by
      have := hout1 c hc
      rwa [show aggKo.getD c default = .n (60 + c) by
        simp [aggKo, List.getD_eq_getElem?_getD, hc]] at this
  -- the nonce's permutation
  have hnh := allIn_holds hnA hat C (fun _ => True)
  rw [aggNonceA_eq, holdsList_append, holds_fsNonceT, holds_padRunT] at hnh
  obtain ⟨⟨hl73, hpk⟩, ⟨-, h77, h78, h79, h80⟩, -⟩ := hnh
  obtain ⟨h74, h75⟩ := hpk
  have h73 : σ (.n 73) = (aggHints rd σ).lambdaGrindNonce := (memAt_of_load hl73).symm
  have hnin : aggNi.map σ = [σ (.n 73), word 0 dsPowNonce, 0, 0, 0, 0, 0, 0] ++
      capOf (aggAbs cs).perm := by
    simp only [aggNi, permIns, List.take, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, h74, h75, h77, h78, h79, h80, capOf, o 8 (by omega), o 9 (by omega),
      o 10 (by omega), o 11 (by omega), o 12 (by omega)]
    rfl
  have hnout := DupSpec.keccak_facts (keccak_sound hkn hat)
  rw [hnin, ← nonce_ins (s := aggAbs cs) hpendm, h73, ← aggN] at hnout
  have q : ∀ c (hc : c < 13), σ (.n (81 + c)) =
      cellsOfState (aggN cs (aggHints rd σ).lambdaGrindNonce) false ⟨c, hc⟩ :=
    fun c hc => by
      have := hnout c hc
      rwa [show aggNo.getD c default = .n (81 + c) by
        simp [aggNo, List.getD_eq_getElem?_getD, hc]] at this
  -- the proof of work and `λ`
  have hg := agg_grind hm hW (by simpa using call_of_flat hall hgr)
  obtain ⟨-, hpow⟩ := hg
  have q1 : σ (.n 82) = cellsOfState (aggN cs (aggHints rd σ).lambdaGrindNonce) false 1 :=
    q 1 (by omega)
  have hpowOk : powOk Batch.batchLambdaGrindBits
      (Keccak.lane (aggN cs (aggHints rd σ).lambdaGrindNonce) 2) = true := by
    have := (grindOk_iff (s := aggAbs cs) (bits := 2) (by omega)
      (aggHints rd σ).lambdaGrindNonce).mpr (by rw [← aggN, ← q1]; exact hpow)
    exact this.resolve_left (by omega)
  have hlam : σ (.n 81) = challengeOf (aggN cs (aggHints rd σ).lambdaGrindNonce) := by
    rw [q 0 (by omega), Keccak.challengeOf_cells]
    rfl
  have hcapN : (⟨[σ (.n 89), σ (.n 90), σ (.n 91), σ (.n 92), σ (.n 93)], []⟩ : Fs) =
      (aggLam cs (aggHints rd σ).lambdaGrindNonce).2 := by
    simp only [aggLam, capOf, Fs.mk.injEq, and_true]
    rw [q 8 (by omega), q 9 (by omega), q 10 (by omega), q 11 (by omega), q 12 (by omega)]
    rfl
  have hagg : (aggLam cs (aggHints rd σ).lambdaGrindNonce).1 = Batch.lambdaPowers (σ (.n 81)) m := by
    simp only [aggLam, hcl, hlam]
  -- the records
  have L26 : ∀ c < m, L26Step rd (σ (.n 98)) (σ (.n 8)) (σ (.n 9)) (σ (.n 81) * σ (.n 81))
      (σ (.n 81)) (gen ^ c) := by
    have h := loop_sound (f := "__loop34")
      (ps := [σ (.n 0), σ (.n 98), σ (.n 8), σ (.n 9), σ (.n 94), σ (.n 81)])
      (B := fun x => L26Step rd (σ (.n 98)) (σ (.n 8)) (σ (.n 9)) (σ (.n 94)) (σ (.n 81)) x)
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l26_step hy
        exact ⟨h1 _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg34 hall hne)
    rwa [isMul_sound hm94 hat] at h
  have h98 : memAt rd (σ (.n 98)) 0 = 1 := by
    rw [memAt_of_load (load_sound hl99 hat), const_sound hc99 hat, word_one]
  have h98z : memAt rd (σ (.n 98)) 1 = 0 := by
    rw [memAt_of_load (load_sound hl100 hat), const_sound hc100 hat, word_zero]
  have CH := chain_rows hcl hcw L25 L26 h98 h98z
  have p105 : σ (.n 105) = σ (.n 98) * (gen ^ m) ^ 2 := by
    rw [monoIs_sound hm105 hat, hN]
  have hclaim : Batch.batchedClaim cs (aggLam cs (aggHints rd σ).lambdaGrindNonce).1 = σ (.n 106) := by
    obtain ⟨-, hacc⟩ := CH m le_rfl
    rw [List.take_of_length_le (by omega)] at hacc
    rw [hagg, ← memAt_of_load (load_sound hl106 hat), p105, hacc]
    rfl
  have hrun : aggRun cs (aggHints rd σ) = bsRun rounds (σ (.n 106))
      ⟨[σ (.n 89), σ (.n 90), σ (.n 91), σ (.n 92), σ (.n 93)], []⟩ := by
    rw [aggRun, hclaim, ← hcapN, hrnd]
    rfl
  -- the weight
  have L27 : ∀ c < m, L27Step rd (σ (.n 8)) (σ (.n 9)) (σ (.n 116)) (σ (.n 98)) (σ (.n 188))
      (σ (.n 81)) (gen ^ c) :=
    loop_sound (f := "__loop35")
      (ps := [σ (.n 0), σ (.n 8), σ (.n 9), σ (.n 116), σ (.n 98), σ (.n 188), σ (.n 81)])
      (by unfold ordG; omega) hN
      (fun y hy => by
        obtain ⟨h1, h2⟩ := l27_step hy
        exact ⟨h1 _ _ _ _ _ _ _ rfl, h2⟩)
      (fun hne => by simpa using guard_sound hg35 hall hne)
  have hptr : (memRun rd (σ (.n 116)) 23).map (1 + ·) = (bsRun rounds (σ (.n 106))
      ⟨[σ (.n 89), σ (.n 90), σ (.n 91), σ (.n 92), σ (.n 93)], []⟩).1.1 := by
    rw [readsAt_memRun hpt, hptl]
    refine map_one_add_memRun fun k hk => ?_
    obtain ⟨⟨⟨c1, l1⟩, a1⟩, s1⟩ := hpt1 k hk
    rw [memAt_of_load (load_sound s1 hat), add_sound a1 hat, const_sound c1 hat, word_one,
      memAt_of_load (load_sound l1 hat)]
  have hz188 : memAt rd (σ (.n 188)) 0 = 0 := by
    rw [memAt_of_load (load_sound hl189 hat), const_sound hc189 hat, word_zero]
  have W := weight_rows hcl hcw L25 L27 (fun c hc => (CH c hc.le).1) hptr hz188 m le_rfl
  rw [List.take_of_length_le (by omega)] at W
  have hw : Batch.batchedBytecodeWeight cs (aggLam cs (aggHints rd σ).lambdaGrindNonce).1
      (bsRun rounds (σ (.n 106))
      ⟨[σ (.n 89), σ (.n 90), σ (.n 91), σ (.n 92), σ (.n 93)], []⟩).1.1 = σ (.n 194) := by
    rw [hagg, ← memAt_of_load (load_sound hl194 hat), isMul_sound hm193 hat, hN, W]
    rfl
  -- the check
  rw [batch_fs, ite_pos' hpowOk, hrun, hw, ← h115, assertEq_sound hae hat, isMul_sound hm195 hat]
  exact ite_pos' rfl

/-- **`aggregate_claims`' core IR writes the batching of the children whose words the memory
holds**, on a memory image. -/
theorem aggregate_claims_holds : aggregate_claims_sound_Spec := by
  intro rd hm args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_aggregate_claims _ _).mp hrel
  have h := aggregate_claims_val hm (fun _ _ _ h => h) hpar hb
  match args, h with
  | [ncg, cpi, cfresh, ccarried, dst, tabs], h =>
    intro hW m hm1 hm16 hN
    obtain ⟨hr, out, hl, hrd, hb⟩ := h hW m hm1 hm16 hN
    exact ⟨hr, aggHints rd σ, out, hl, hrd, hb⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h => exact h.elim
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => exact h.elim

end
end LeanVM.Guest.B1.Main
