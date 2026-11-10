/-
  LeanVM.Guest.B1.Whir.CHonLvP

  A level of the honest run: the guest's sponges and samples are the Spec's.
-/

module

public import LeanVM.Guest.B1.Whir.CHonLv
public import LeanVM.Guest.B1.Whir.LastRun
public import LeanVM.Guest.B1.Whir.LevelSpec
public import LeanVM.Guest.B1.Whir.Finish
public import LeanVM.Guest.B1.Whir.CTail
public import LeanVM.Guest.B1.Whir.CInvLast

/-!
# The guest's sponges are the Spec's

On a level `L : LvAt` of the honest run and the guest's data of it (`LvAt.midW`, `LvAt.finWD`),
with the level's row `lv` of the tables matching the Spec's level: the capacity after the folds
(`cap1`), the query grind's permutation (`S2` = `qS`), the capacity after the squeezes (`cap3` =
`F3`), `λ` and the batching nonce's permutation, the out-of-domain points (`MidEqs`); the
samples and the squeezes' capacities (`lvAt_words`); the rounds' challenges in memory
(`roundsMem_of`); a non-final level's claim, the next level's less the deficit (`midClaim`,
`hbat_of`); the final level's sponges (`FinEqs`), its terminal (`finEnd`) and closing rounds'
calls (`tailC_of`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Value

@[expose] public section

/-- Squeezes from a capacity, the first split off. -/
theorem squeezeN_first (cap : List E) (n : ℕ) (hn : 1 ≤ n) :
    ((⟨cap, []⟩ : Fs).squeezeN n) =
      (challengeOf (⟨cap, []⟩ : Fs).perm :: ((⟨capOf (⟨cap, []⟩ : Fs).perm, []⟩ : Fs).squeezeN (n - 1)).1,
        ((⟨capOf (⟨cap, []⟩ : Fs).perm, []⟩ : Fs).squeezeN (n - 1)).2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem rdCell_zero (S : KeccakState) : rdCell S 0 = challengeOf S := by
  rw [Keccak.challengeOf_cells]; rfl

/-- What a non-final level's guest data and the Spec agree on. -/
structure MidEqs (logN : ℕ) (L L' : LvAt) (lv : OsLv) (cl : E) (M : MidW) : Prop where
  cap1 : M.cap1 lv L.cap cl = L.cap1
  S2 : M.S2 lv L.cap cl = L.qS logN
  cap3 : M.cap3 lv L.cap cl = (L.F3 logN).cap
  F3pend : (L.F3 logN).pend = []
  SL : M.SL lv L.cap cl = (L.F3 logN).nonceState M.n2
  lam : M.lam lv L.cap cl = L.lam logN
  cap' : L'.cap = capOf (M.SL lv L.cap cl)
  z0 : cellsOfState (omState L.cap1 M.msg none) false 0 ::
      ((⟨capOf (omState L.cap1 M.msg none), []⟩ : Fs).squeezeN (lv.logCols - 1)).1 = (L.osRec logN).z0
  z1 : ((⟨spfRets L.cap1 M.msg lv.logCols, []⟩ : Fs).squeezeN lv.logCols).1 = (L.osRec logN).z1

/-- **A non-final level: the guest's sponges are the Spec's.** -/
theorem midEqs {logN index : ℕ} {L L' : LvAt} (hN : LvAt.NextStep logN index L L') {lv : OsLv}
    (hfold : L.level.fold = lv.folds) (hmu : L.mu logN = lv.logCols) (hdep : lv.depth = L.dp logN)
    (hq : L.level.queries = lv.queries) (hsq : lv.squeezes = sqCount (128 / lv.depth) lv.queries)
    (hcols : 1 ≤ lv.logCols) (r0 r1 batched pS pZ cl : E) :
    MidEqs logN L L' lv cl (L.midW r0 r1 batched pS pZ) := by
  obtain ⟨rw, W, hd, -, -, -, -, -, -, hcap', -⟩ := hN
  have hrw : L.rw = rw := by simp [LvAt.rw, hd]
  have hnw : L.nw = W := by simp [LvAt.nw, hd]
  set M := L.midW r0 r1 batched pS pZ with hM
  have hc1 : M.cap1 lv L.cap cl = L.cap1 := by
    simp only [hM, MidW.cap1, LvAt.midW, LvAt.cap1, roundsTr_cap, hfold]
  have hF : L.F = ⟨L.cap1, []⟩ := by simp [LvAt.F, LvAt.cap1]
  have hmsg : M.msg = W.x0 :: W.x1 :: W.high := by simp [hM, MidW.msg, LvAt.midW, hnw]
  -- the message's permutation and the out-of-domain points
  have hF1 : W.F1 L.F = (⟨L.cap1, []⟩ : Fs).absorbAll M.msg dsObserve := by
    rw [hF, hmsg]; rfl
  have hsq1 : ((W.F1 L.F).squeezeN (L.mu logN)) =
      (challengeOf (omState L.cap1 M.msg none) ::
        ((⟨capOf (omState L.cap1 M.msg none), []⟩ : Fs).squeezeN (lv.logCols - 1)).1,
        ⟨spfRets L.cap1 M.msg lv.logCols, []⟩) := by
    rw [hF1, hmu]
    obtain ⟨m, hm⟩ : ∃ m, lv.logCols = m + 1 := ⟨lv.logCols - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    simp only [Fs.squeezeN, Fs.squeeze, spfRets, omState, Nat.add_sub_cancel, Prod.mk.injEq, true_and]
    exact squeezeN_mk _ _
  have hsq2 : (((W.F1 L.F).squeezeN (L.mu logN)).2.squeezeN (L.mu logN)) =
      (((⟨spfRets L.cap1 M.msg lv.logCols, []⟩ : Fs).squeezeN lv.logCols).1,
        ⟨spRets L.cap1 M.msg lv.logCols, []⟩) := by
    rw [hsq1, hmu]
    rw [Prod.mk.injEq]
    exact ⟨rfl, squeezeN_mk _ _⟩
  have hS2 : M.S2 lv L.cap cl = L.qS logN := by
    simp only [MidW.S2, hc1, commitS, LvAt.qS, hd, NextW.qS]
    rw [hsq2]
    simp [hM, LvAt.midW, hnw]
  have hqS : L.qS logN = W.qS L.F (L.mu logN) := by simp [LvAt.qS, hd]
  have hF3 : L.F3 logN = ⟨M.cap3 lv L.cap cl, []⟩ := by
    simp only [LvAt.F3, hd, NextW.F3, MidW.cap3, sqCap]
    rw [← hqS, ← hS2, hsq, hdep, hq]
    exact squeezeN_mk _ _
  have hSL : M.SL lv L.cap cl = (L.F3 logN).nonceState M.n2 := by
    rw [hF3]; rfl
  have hF3' : L.F3 logN = W.F3 L.F (L.mu logN) (L.dp logN) L.level.queries := by simp [LvAt.F3, hd]
  have hn2 : M.n2 = W.n2 := by simp [hM, LvAt.midW, hnw]
  have hood : W.ood L.F (L.mu logN) = [((W.F1 L.F).squeezeN (L.mu logN)).1,
      (((W.F1 L.F).squeezeN (L.mu logN)).2.squeezeN (L.mu logN)).1] := rfl
  have hrec : L.osRec logN = W.osRec logN L.level L.s1 L.F := by simp [LvAt.osRec, hd]
  refine ⟨hc1, hS2, by rw [hF3], by rw [hF3], hSL, ?_, ?_, ?_, ?_⟩
  · simp only [MidW.lam, LvAt.lam, hd, NextW.lam]
    rw [rdCell_zero, hSL, hF3', hn2]
  · rw [hcap', hSL, hF3', hn2]
    simp only [LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hrw]
  · rw [hrec]
    simp only [NextW.osRec]
    rw [hood, hsq1]
    simp only [List.getD_cons_zero, Keccak.challengeOf_cells]
  · rw [hrec]
    simp only [NextW.osRec]
    rw [hood, hsq2]
    simp only [List.getD_cons_succ, List.getD_cons_zero]

/-- **A level's samples and the squeezes' capacities**: sample `0` is the query grind's
challenge, sample `j ≥ 1` the next squeeze from `capSq j`; `capSq 1` is the grind's capacity and
`capSq S` the capacity after the positions' squeezes. -/
theorem lvAt_words (L : LvAt) (logN : ℕ) {lv : OsLv} (hdep : lv.depth = L.dp logN)
    (hq : L.level.queries = lv.queries) (hsq : lv.squeezes = sqCount (128 / lv.depth) lv.queries) :
    L.word logN 0 = rdCell (L.qS logN) 0 ∧
      (∀ j, 1 ≤ j → (⟨L.capSq logN j, []⟩ : Fs).squeeze.1 = L.word logN j) ∧
      L.capSq logN 1 = capOf (L.qS logN) ∧ L.capSq logN lv.squeezes = (L.F3 logN).cap := by
  refine ⟨?_, fun j hj ↦ ?_, rfl, ?_⟩
  · rw [rdCell_zero]; rfl
  · simp only [LvAt.word, LvAt.capSq, sqSample, show j ≠ 0 by omega, ↓reduceIte, sqCap]
    rw [← squeezeN_mk]
  · simp only [LvAt.capSq, sqCap, LvAt.F3]
    rcases hd : L.d with ⟨rw, W⟩ | ⟨rw, W⟩
    · simp only [NextW.F3, LvAt.qS, hd, hsq, hdep, hq]
    · simp only [FinW.F3, LvAt.qS, hd, hsq, hdep, hq]

/-! ## The rounds' challenges -/

/-- The rounds only append their `γ`s. -/
theorem roundsSpec_gammas : ∀ (n : ℕ) (s : WhirState) (fs xs : List E),
    ∃ gs : List E, (roundsSpec n s fs xs).1.gammas = s.gammas ++ gs ∧ gs.length = n
  | 0, s, _, _ => ⟨[], by simp [roundsSpec], rfl⟩
  | n + 1, s, fs, xs => by
    obtain ⟨gs, h1, h2⟩ := roundsSpec_gammas n (roundSpec s fs (xs.take 7)).1
      (roundSponge fs (xs.take 7)).cap (xs.drop 7)
    refine ⟨(roundChs fs (xs.take 7)).1 :: gs, ?_, by simp [h2]⟩
    show (roundsSpec n _ _ _).1.gammas = _
    rw [h1, show (roundSpec s fs (List.take 7 xs)).1.gammas = s.gammas ++ [(roundChs fs (List.take 7 xs)).1]
      from rfl, List.append_assoc]
    rfl

theorem roundsSpec_gammas_length (n : ℕ) (s : WhirState) (fs xs : List E) :
    (roundsSpec n s fs xs).1.gammas.length = s.gammas.length + n := by
  obtain ⟨gs, h1, h2⟩ := roundsSpec_gammas n s fs xs
  rw [h1, List.length_append, h2]

theorem roundsSpec_rounds_length : ∀ (n : ℕ) (s : WhirState) (fs xs : List E),
    (roundsSpec n s fs xs).2.length = n
  | 0, _, _, _ => rfl
  | n + 1, s, fs, xs => by
    simp only [roundsSpec, List.length_cons, roundsSpec_rounds_length n]

/-- **The rounds' challenges in memory**: from the Spec's `γ`s at `fch·g^i` on and its rounds'
`α, β, θ` at `coefs·g^(3i)` on, every round's grinds passing, `RoundsMem`. -/
theorem roundsMem_of {rd : Reader} {fch coefs : E} : ∀ (n i : ℕ) (s : WhirState) (fs : List E)
    (cl : E) (xs : List E), RoundsOk n fs xs →
    (∀ j < n, LoadHolds rd fch (i + j) ((roundsSpec n s fs xs).1.gammas.getD (s.gammas.length + j) 0)) →
    (∀ j < n, LoadHolds rd coefs (3 * (i + j)) ((roundsSpec n s fs xs).2.getD j ⟨0, 0, 0⟩).alpha ∧
      LoadHolds rd coefs (3 * (i + j) + 1) ((roundsSpec n s fs xs).2.getD j ⟨0, 0, 0⟩).beta ∧
      LoadHolds rd coefs (3 * (i + j) + 2) ((roundsSpec n s fs xs).2.getD j ⟨0, 0, 0⟩).theta) →
    RoundsMem rd fch coefs n i fs cl xs
  | 0, _, _, _, _, _, _, _, _ => trivial
  | n + 1, i, s, fs, cl, xs, hok, hg, hc => by
    obtain ⟨hgr, -, hok'⟩ := hok
    set w := xs.take 7 with hw
    set s1 := (roundSpec s fs w).1 with hs1
    obtain ⟨gs, hgs, -⟩ := roundsSpec_gammas n s1 (roundSponge fs w).cap (xs.drop 7)
    have hspec : roundsSpec (n + 1) s fs xs =
        ((roundsSpec n s1 (roundSponge fs w).cap (xs.drop 7)).1,
          (roundSpec s fs w).2 :: (roundsSpec n s1 (roundSponge fs w).cap (xs.drop 7)).2) := rfl
    have hs1g : s1.gammas = s.gammas ++ [(roundChs fs w).1] := rfl
    have hG : (roundsSpec (n + 1) s fs xs).1.gammas = s.gammas ++ (roundChs fs w).1 :: gs := by
      rw [hspec]
      show (roundsSpec n s1 (roundSponge fs w).cap (xs.drop 7)).1.gammas = _
      rw [hgs, hs1g, List.append_assoc]
      rfl
    have g0 := hg 0 (by omega)
    rw [hG, show (s.gammas ++ (roundChs fs w).1 :: gs).getD (s.gammas.length + 0) 0 = (roundChs fs w).1 by
      simp [List.getD_eq_getElem?_getD]] at g0
    have hR : (roundsSpec (n + 1) s fs xs).2.getD 0 ⟨0, 0, 0⟩ =
        ⟨(roundChs fs w).2.2.2, (roundChs fs w).2.1, (roundChs fs w).2.2.1⟩ := by
      rw [hspec]; rfl
    obtain ⟨c0, c1, c2⟩ := hc 0 (by omega)
    rw [hR] at c0 c1 c2
    simp only [Nat.add_zero] at c0 c1 c2
    refine ⟨hgr, by rw [loadHolds_mul_gen_pow]; simpa using g0, ?_, ?_, ?_, ?_⟩
    · rw [loadHolds_mul_gen_pow]; simpa using c0
    · rw [loadHolds_mul_gen_pow]; exact c1
    · rw [loadHolds_mul_gen_pow]; exact c2
    · rw [roundRets_take5]
      refine roundsMem_of n (i + 1) s1 _ _ _ hok' (fun j hj ↦ ?_) (fun j hj ↦ ?_)
      · have := hg (j + 1) (by omega)
        rw [hspec] at this
        rw [show s1.gammas.length = s.gammas.length + 1 by simp [hs1g],
          show i + 1 + j = i + (j + 1) by ring, show s.gammas.length + 1 + j = s.gammas.length + (j + 1) by ring]
        exact this
      · have := hc (j + 1) (by omega)
        rw [hspec] at this
        simp only [List.getD_cons_succ] at this
        rw [show i + 1 + j = i + (j + 1) by ring]
        exact this

/-! ## The claims -/

theorem roundsSpec_glued : ∀ (n : ℕ) (s : WhirState) (fs xs : List E),
    (roundsSpec n s fs xs).1.glued = s.glued
  | 0, _, _, _ => rfl
  | n + 1, _, _, _ => roundsSpec_glued n _ _ _

/-- **The guest's rounds' claim is the Spec's** but for the deficit `D` times the rounds' `γ`s. -/
theorem roundsTr_claim : ∀ (n : ℕ) (s : WhirState) (fs xs : List E) (D : E),
    (roundsTr n fs (s.claim + D) xs).2 = (roundsSpec n s fs xs).1.claim +
      ((roundsSpec n s fs xs).1.gammas.drop s.gammas.length).prod * D
  | 0, s, _, _, D => by simp [roundsTr, roundsSpec]
  | n + 1, s, fs, xs, D => by
    set w := xs.take 7 with hw
    set s1 := (roundSpec s fs w).1 with hs1
    have hcl : (roundRets fs 0 (s.claim + D) w).getD 6 0 = s1.claim + (roundChs fs w).1 * D := by
      simp only [roundRets, hs1, roundSpec, roundChs, List.cons_append, List.nil_append,
        List.getD_cons_succ, List.getD_cons_zero, Fs.squeeze, capOf]
      rw [roundClaim_add]
    have ih := roundsTr_claim n s1 (roundSponge fs w).cap (xs.drop 7) ((roundChs fs w).1 * D)
    obtain ⟨gs, hgs, -⟩ := roundsSpec_gammas n s1 (roundSponge fs w).cap (xs.drop 7)
    have hs1g : s1.gammas = s.gammas ++ [(roundChs fs w).1] := rfl
    show (roundsTr n ((roundRets fs 0 (s.claim + D) w).take 5) ((roundRets fs 0 (s.claim + D) w).getD 6 0)
      (xs.drop 7)).2 = (roundsSpec n s1 (roundSponge fs w).cap (xs.drop 7)).1.claim +
        ((roundsSpec n s1 (roundSponge fs w).cap (xs.drop 7)).1.gammas.drop s.gammas.length).prod * D
    rw [roundRets_take5, hcl, ih, hgs, hs1g]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.length_append, List.length_singleton, List.drop_append_of_le_length le_rfl, List.drop_length,
      List.nil_append, List.prod_cons]
    have e : List.drop (s.gammas.length + 1) (s.gammas ++ (roundChs fs w).1 :: gs) = gs := by
      rw [show s.gammas ++ (roundChs fs w).1 :: gs = (s.gammas ++ [(roundChs fs w).1]) ++ gs by simp,
        show s.gammas.length + 1 = (s.gammas ++ [(roundChs fs w).1]).length by simp, List.drop_left]
    rw [e]
    ring

/-- **A non-final level's claim**: the guest's claim after the glue is the next level's, the
Spec's less the deficit with the level's record appended; the next state's `γ`s and glued claims. -/
theorem midClaim {logN index : ℕ} {L L' : LvAt} (hN : LvAt.NextStep logN index L L') {lv : OsLv}
    (hfold : L.level.fold = lv.folds) (hmu : L.mu logN = lv.logCols) (hdep : lv.depth = L.dp logN)
    (hq : L.level.queries = lv.queries) (hsq : lv.squeezes = sqCount (128 / lv.depth) lv.queries)
    (hcols : 1 ≤ lv.logCols) {recs : List OsRec} (hrecF : ∀ r ∈ recs, r.F ≤ L.s.gammas.length)
    (r0 r1 batched pS pZ : E)
    (hbat : (L.lam logN) ^ L.level.queries * batched = ∑ k ∈ Finset.range (L.qs logN).length,
      (L.lam logN) ^ k * foldRow (specLanes index ((L.phase.map (·.leaf)).getD k []))
        (K.ofBits ((L.qs logN).getD k 0)) L.rounds) :
    (L.midW r0 r1 batched pS pZ).claimOut lv L.cap (L.gcl recs) = L'.gcl (recs ++ [L.osRec logN]) ∧
      L'.s.gammas = L.s1.gammas ∧ L'.s.glued = L.s.glued ++ recGlued (L.osRec logN) ∧
      (L.osRec logN).F = L.s1.gammas.length := by
  have hE := midEqs hN hfold hmu hdep hq hsq hcols r0 r1 batched pS pZ (L.gcl recs)
  obtain ⟨rw, W, hd, -, -, -, -, hok, hs', -, -⟩ := hN
  have hrw : L.rw = rw := by simp [LvAt.rw, hd]
  have hnw : L.nw = W := by simp [LvAt.nw, hd]
  have hrec : L.osRec logN = W.osRec logN L.level L.s1 L.F := by simp [LvAt.osRec, hd]
  have hlam : L.lam logN = W.lam L.F (L.mu logN) (L.dp logN) L.level.queries := by simp [LvAt.lam, hd]
  have hqs : L.qs logN = W.qs L.F (L.mu logN) (L.dp logN) L.level.queries := by simp [LvAt.qs, hd]
  have hph : L.phase = W.phase := by simp [LvAt.phase, hd]
  have hs1 : L.s1 = rsSt L.level L.s L.cap rw := by simp only [LvAt.s1, hrw]
  have hF : L.F = rsF L.level L.cap rw := by simp only [LvAt.F, hrw]
  have hrd : L.rounds = rsRounds L.level L.s L.cap rw := by simp only [LvAt.rounds, hrw]
  -- the next state
  have hs'' : L'.s = W.glued logN index L.level L.s1 L.F L.rounds := by rw [hs', hs1, hF, hrd]
  have hglue := glueLevel_two L.s1 (L.lam logN) (L.mu logN)
    ((W.ood L.F (L.mu logN)).getD 0 []) ((W.ood L.F (L.mu logN)).getD 1 []) W.y0 W.y1
    (L.qs logN) (powers (L.lam logN) (L.qs logN).length)
    (levelBatched (L.mu logN) index L.rounds W.high (L.qs logN) (W.phase.map (·.leaf)) (L.lam logN))
  have hgl : W.glued logN index L.level L.s1 L.F L.rounds = glueLevel L.s1 (L.lam logN) (L.mu logN)
      [(W.ood L.F (L.mu logN)).getD 0 [], (W.ood L.F (L.mu logN)).getD 1 []] [W.y0, W.y1] (L.qs logN)
      (powers (L.lam logN) (L.qs logN).length)
      (levelBatched (L.mu logN) index L.rounds W.high (L.qs logN) (W.phase.map (·.leaf)) (L.lam logN)) := by
    rw [hlam, hqs]; rfl
  rw [hgl, hglue] at hs''
  have hrecF' : (L.osRec logN).F = L.s1.gammas.length := by rw [hrec]; rfl
  have hrlam : (L.osRec logN).lam = L.lam logN := by rw [hrec, hlam]; rfl
  have hrecGl : recGlued (L.osRec logN) = [⟨1 * L.lam logN, L.s1.gammas.length,
      fun x ↦ eqEval ((W.ood L.F (L.mu logN)).getD 0 []) x⟩,
      ⟨1 * L.lam logN * L.lam logN, L.s1.gammas.length, fun x ↦ eqEval ((W.ood L.F (L.mu logN)).getD 1 []) x⟩,
      ⟨1 * L.lam logN * L.lam logN * L.lam logN, L.s1.gammas.length,
        inducedWeight (L.mu logN) (L.qs logN) (powers (L.lam logN) (L.qs logN).length)⟩] := by
    rw [hrec, hlam, hqs]; rfl
  have hgam : L'.s.gammas = L.s1.gammas := by rw [hs'']
  have hglued : L'.s.glued = L.s.glued ++ recGlued (L.osRec logN) := by
    rw [hs'', hrecGl, hs1, roundsSpec_glued]
  refine ⟨?_, hgam, hglued, hrecF'⟩
  -- the claims
  obtain ⟨gs, hgs, -⟩ := roundsSpec_gammas L.level.fold L.s L.cap rw
  have hs1g : L.s1.gammas = L.s.gammas ++ gs := by rw [hs1]; exact hgs
  have hcl1 : (L.midW r0 r1 batched pS pZ).cl1 lv L.cap (L.gcl recs) =
      L.s1.claim + gs.prod * recsDeficit recs L.s.gammas := by
    simp only [MidW.cl1, LvAt.midW, LvAt.gcl, hrw, ← hfold]
    have hs1' : L.s1 = (roundsSpec L.level.fold L.s L.cap rw).1 := hs1
    rw [roundsTr_claim, ← hs1', hs1g, List.drop_left]
  have hB := levelBatched_eq (L.mu logN) index L.rounds W.high (L.qs logN) (W.phase.map (·.leaf))
    (by have hpl := hok.plen; rw [← hrw] at hpl; rw [List.length_map, hqs]; exact hpl) (L.lam logN)
  have hH : recH (L.osRec logN) = ∑ k ∈ Finset.range (L.qs logN).length,
      L.lam logN ^ k * highTerm (L.mu logN) W.high ((L.qs logN).getD k 0) := by
    rw [recH, hrlam, hrec, hqs]; rfl
  have hdef : recsDeficit (recs ++ [L.osRec logN]) L'.s.gammas =
      gs.prod * recsDeficit recs L.s.gammas + L.lam logN ^ 3 * recH (L.osRec logN) := by
    rw [hgam, recsDeficit_snoc _ _ _ hrecF', hs1g, recsDeficit_append_gammas _ _ _ hrecF, hrlam]
  show _ = L'.s.claim + recsDeficit (recs ++ [L.osRec logN]) L'.s.gammas
  rw [hdef, hs'']
  rw [MidW.claimOut, hcl1, hE.lam]
  simp only [LvAt.midW, hnw]
  rw [hB, ← hph, ← hbat, ← hH, ← hq]
  have h2 : ∀ x : E, x + x = 0 := fun x ↦ CharTwo.add_self_eq_zero x
  linear_combination -(L.lam logN ^ 3) * h2 (recH (L.osRec logN))

/-- **The guest's queries' chain** times `λ^Q` is the batched sum `hbat` asks for. -/
theorem hbat_of {lam : E} (hlam : lam ≠ 0) {odd base N Q : ℕ} (hodd : odd ≤ 1) (hob : base = 1 ∨ odd = 0)
    (hQ : oqCount odd base N = Q) {ds es : ℕ → E} (hds : ∀ k < Q, ds k = es k) :
    lam ^ Q * oqChain odd base lam⁻¹ ds N = ∑ k ∈ Finset.range Q, lam ^ k * es k := by
  subst hQ
  rw [oqChain_mul_pow (mul_inv_cancel₀ hlam) hodd hob ds N, powSum]
  exact Finset.sum_congr rfl fun k hk ↦ by rw [hds k (Finset.mem_range.mp hk)]

/-! ## The final level -/

/-- What the final level's guest data and the Spec agree on. -/
structure FinEqs (logN : ℕ) (L : LvAt) (lv : OsLv) (cl : E) (M : FinWD) : Prop where
  cap1 : M.cap1 lv L.cap cl = L.cap1
  S2 : M.S2 lv L.cap cl = L.qS logN
  cap3 : M.cap3 lv L.cap cl = (L.F3 logN).cap
  F3pend : (L.F3 logN).pend = []

/-- **The final level: the guest's sponges are the Spec's.** -/
theorem finEqs {logN lane index : ℕ} {L : LvAt} {w : WhirEnd} (hF : LvAt.FinStep logN lane index L w)
    {lv : OsLv} (hfold : L.level.fold = lv.folds) (hdep : lv.depth = L.dp logN)
    (hq : L.level.queries = lv.queries) (hsq : lv.squeezes = sqCount (128 / lv.depth) lv.queries)
    (r0 r1 batched pZ pH cl : E) : FinEqs logN L lv cl (L.finWD r0 r1 batched pZ pH) := by
  obtain ⟨rw, W, hd, -⟩ := hF
  have hfw : L.fw = W := by simp [LvAt.fw, hd]
  set M := L.finWD r0 r1 batched pZ pH with hM
  have hc1 : M.cap1 lv L.cap cl = L.cap1 := by
    simp only [hM, FinWD.cap1, LvAt.finWD, LvAt.cap1, roundsTr_cap, hfold]
  have hF : L.F = ⟨L.cap1, []⟩ := by simp [LvAt.F, LvAt.cap1]
  have hqS : L.qS logN = W.qS L.F := by simp [LvAt.qS, hd]
  have hS2 : M.S2 lv L.cap cl = L.qS logN := by
    rw [hqS, FinWD.S2, hc1, hF]
    simp [hM, LvAt.finWD, hfw, omState, FinW.qS]
  have hF3 : L.F3 logN = ⟨M.cap3 lv L.cap cl, []⟩ := by
    simp only [LvAt.F3, hd, FinW.F3, FinWD.cap3, sqCap]
    rw [← hqS, ← hS2, hsq, hdep, hq]
    exact squeezeN_mk _ _
  exact ⟨hc1, hS2, by rw [hF3], by rw [hF3]⟩

theorem tailRun_length : ∀ (pairs : List (E × E)) (cap : List E) (cl : E),
    (tailRun pairs cap cl).1.length = pairs.length
  | [], _, _ => rfl
  | (_, _) :: rest, _, _ => by simp only [tailRun, List.length_cons, tailRun_length rest]

/-- **The final level's end**: with `tr` the guest's closing rounds from its capacity and claim
after the folds, the terminal's target, inner sum, residual and point. -/
theorem finEnd {logN lane index : ℕ} {L : LvAt} {w : WhirEnd} (hF : LvAt.FinStep logN lane index L w)
    {lv : OsLv} (hfold : L.level.fold = lv.folds) (hdep : lv.depth = L.dp logN)
    (hq : L.level.queries = lv.queries) (hsq : lv.squeezes = sqCount (128 / lv.depth) lv.queries)
    {recs : List OsRec} (hrecF : ∀ r ∈ recs, r.F ≤ L.s.gammas.length)
    (hglued : L.s.glued = recs.flatMap recGlued) (r0 r1 batched pZ pH : E) :
    w.target = (tailRun L.fw.pairs ((L.finWD r0 r1 batched pZ pH).cap3 lv L.cap (L.gcl recs))
        ((L.finWD r0 r1 batched pZ pH).cl1 lv L.cap (L.gcl recs))).2.1 +
      (tailRun L.fw.pairs ((L.finWD r0 r1 batched pZ pH).cap3 lv L.cap (L.gcl recs))
        ((L.finWD r0 r1 batched pZ pH).cl1 lv L.cap (L.gcl recs))).1.prod * recsDeficit recs L.s1.gammas ∧
    w.inner = (recs.flatMap recGlued).foldl (fun x g ↦ x + g.scalar * g.weightAt ((L.s1.gammas ++
      (tailRun L.fw.pairs ((L.finWD r0 r1 batched pZ pH).cap3 lv L.cap (L.gcl recs))
        ((L.finWD r0 r1 batched pZ pH).cl1 lv L.cap (L.gcl recs))).1).drop g.foldStart)) 0 ∧
    w.residual = multilinearEval (L.fw.fold.take (2 ^ L.mu logN))
      (tailRun L.fw.pairs ((L.finWD r0 r1 batched pZ pH).cap3 lv L.cap (L.gcl recs))
        ((L.finWD r0 r1 batched pZ pH).cl1 lv L.cap (L.gcl recs))).1 ∧
    w.point = rotPt L.s1.gammas
      (tailRun L.fw.pairs ((L.finWD r0 r1 batched pZ pH).cap3 lv L.cap (L.gcl recs))
        ((L.finWD r0 r1 batched pZ pH).cl1 lv L.cap (L.gcl recs))).1 lane ∧
    (tailRun L.fw.pairs ((L.finWD r0 r1 batched pZ pH).cap3 lv L.cap (L.gcl recs))
        ((L.finWD r0 r1 batched pZ pH).cl1 lv L.cap (L.gcl recs))).1.length = L.mu logN := by
  have hE := finEqs hF hfold hdep hq hsq r0 r1 batched pZ pH (L.gcl recs)
  obtain ⟨rw, W, hd, -, -, -, -, hok, hw⟩ := hF
  have hrw : L.rw = rw := by simp [LvAt.rw, hd]
  have hfw : L.fw = W := by simp [LvAt.fw, hd]
  rw [← hrw] at hw
  have hF3 : L.F3 logN = W.F3 L.F (L.dp logN) L.level.queries := by simp [LvAt.F3, hd]
  obtain ⟨gs, hgs, -⟩ := roundsSpec_gammas L.level.fold L.s L.cap L.rw
  have hs1g : L.s1.gammas = L.s.gammas ++ gs := hgs
  have hcl1 : (L.finWD r0 r1 batched pZ pH).cl1 lv L.cap (L.gcl recs) =
      L.s1.claim + recsDeficit recs L.s1.gammas := by
    simp only [FinWD.cl1, LvAt.finWD, LvAt.gcl, ← hfold]
    rw [roundsTr_claim, hs1g, List.drop_left, recsDeficit_append_gammas _ _ _ hrecF]
  rw [hE.cap3, hcl1, hfw]
  obtain ⟨t1, t2, -⟩ := tailRun_add W.pairs (L.F3 logN).cap L.s1.claim (recsDeficit recs L.s1.gammas)
  have hT : W.tail L.F (L.dp logN) L.level.queries L.s1.claim = tailRun W.pairs (L.F3 logN).cap L.s1.claim := by
    rw [hF3]; rfl
  have hgl : L.s1.glued = recs.flatMap recGlued := by
    rw [← hglued]; exact roundsSpec_glued _ _ _ _
  have hpl := hok.plen2
  rw [← hrw] at hpl
  subst hw
  simp only [FinW.wend]
  rw [hT, t1, t2, hgl]
  refine ⟨?_, rfl, rfl, rfl, by rw [tailRun_length, hpl]⟩
  have h2 : ∀ x : E, x + x = 0 := fun x ↦ CharTwo.add_self_eq_zero x
  linear_combination -h2 ((tailRun W.pairs (L.F3 logN).cap L.s1.claim).1.prod * recsDeficit recs L.s1.gammas)

/-- **The closing rounds' calls**, from each round's call at the state `tailRun` reaches before
it and the challenges' loads. -/
theorem tailC_of {C : CallRel} {rd : Reader} {pT tabs : E} : ∀ (pairs : List (E × E)) (j0 : ℕ)
    (cap : List E) (cl cur : E),
    (∀ j < pairs.length, C "opening_tail_round" ((tailRun (pairs.take j) cap cl).2.2 ++
      [cur * gen ^ (2 * j), (tailRun (pairs.take j) cap cl).2.1, tabs])
      (tailRets (tailRun (pairs.take j) cap cl).2.2 (cur * gen ^ (2 * j)) (tailRun (pairs.take j) cap cl).2.1
        (pairs.getD j (0, 0)))) →
    (∀ j < pairs.length, LoadHolds rd pT (j0 + j) ((tailRun pairs cap cl).1.getD j 0)) →
    TailC C rd pT tabs j0 pairs cap cl cur
  | [], _, _, _, _, _, _ => trivial
  | (c0, c2) :: rest, j0, cap, cl, cur, hc, hl => by
    have h0 := hc 0 (by simp)
    simp only [List.take_zero, tailRun, Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero] at h0
    have l0 := hl 0 (by simp)
    simp only [tailRun_cons, List.getD_cons_zero, Nat.add_zero] at l0
    have e7 : (tailRets cap cur cl (c0, c2)).getD 7 0 =
        ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1 := by
      simp [tailRets, Fs.squeeze, capOf]
    refine ⟨h0, by rw [e7]; exact l0, ?_⟩
    have e5 : (tailRets cap cur cl (c0, c2)).take 5 =
        ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.2.cap := by
      simp [tailRets, Fs.squeeze, capOf]
    have e6 : (tailRets cap cur cl (c0, c2)).getD 6 0 =
        c0 + ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1 *
          (cl + (1 + ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1) * c2) := by
      simp [tailRets, Fs.squeeze, capOf]
    rw [e5, e6]
    refine tailC_of rest (j0 + 1) _ _ _ (fun j hj ↦ ?_) (fun j hj ↦ ?_)
    · have := hc (j + 1) (by simp; omega)
      simp only [List.take_succ_cons, tailRun_cons, List.getD_cons_succ] at this
      rw [show cur * gen ^ (2 * (j + 1)) = cur * gen ^ 2 * gen ^ (2 * j) by ring] at this
      exact this
    · have := hl (j + 1) (by simp; omega)
      simp only [tailRun_cons, List.getD_cons_succ] at this
      rw [show j0 + 1 + j = j0 + (j + 1) by ring]
      exact this

end
end LeanVM.Guest.B1.Whir
