/-
  LeanVM.Guest.B1.Whir.CHonLvP

  A level of the honest run: the guest's sponges and samples are the Spec's.
-/

module

public import LeanVM.Guest.B1.Whir.CHonLv
public import LeanVM.Guest.B1.Whir.LastRun

/-!
# The guest's sponges are the Spec's

On a level `L : LvAt` of the honest run and the guest's data of it (`LvAt.midW`, `LvAt.finWD`),
with the level's row `lv` of the tables matching the Spec's level: the capacity after the folds
(`cap1`), the query grind's permutation (`S2` = `qS`), the capacity after the squeezes (`cap3` =
`F3`), `λ` and the batching nonce's permutation, the out-of-domain points (`MidEqs`); the
samples and the squeezes' capacities (`lvAt_words`).
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

end
end LeanVM.Guest.B1.Whir
