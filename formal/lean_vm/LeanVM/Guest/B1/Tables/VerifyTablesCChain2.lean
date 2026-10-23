/-
  LeanVM.Guest.B1.Tables.VerifyTablesCChain2

  `verify_tables`' completeness: the column evaluations and the constraint windows chained.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCChain

/-!
# The evaluations and the tables' terms

`vt_ev_run`: a run of one table's column evaluations, the state absorbing each word in turn
(`cvE`). `vt_phaseD`: statements `4374 ..< 7854`, the first table's `g^τ`, then per table its
evaluations and its constraint window.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- The evaluations' first indices and counts, per table. -/
def evFirst : List ℕ := [0, 15, 30, 38, 53, 67]
def evCnt : List ℕ := [15, 15, 8, 15, 14, 37]

/-- The state before evaluation `j`: the words before it absorbed. -/
def cvE (cv0 : Digest) (ws : ℕ → E) (j : ℕ) : Digest := obsAll cv0 ((List.range j).map ws)

theorem cvE_succ (cv0 : Digest) (ws : ℕ → E) (j : ℕ) : cvE cv0 ws (j + 1) = obsCv (cvE cv0 ws j) (ws j) := by
  rw [cvE, cvE, List.range_succ, List.map_append, List.map_cons, List.map_nil, obsAll_append_one']

/-- The cell holding the state before evaluation `j`. -/
def evSt (j : ℕ) : ℕ := if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13

set_option maxRecDepth 100000 in
theorem ev_nb0 : ∀ j < 26, numBelowB (evVal.getD (0 + j) 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD (0 + j) 0)).take 16)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ev_nb1 : ∀ j < 26, numBelowB (evVal.getD (26 + j) 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD (26 + j) 0)).take 16)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ev_nb2 : ∀ j < 26, numBelowB (evVal.getD (52 + j) 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD (52 + j) 0)).take 16)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ev_nb3 : ∀ j < 26, numBelowB (evVal.getD (78 + j) 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD (78 + j) 0)).take 16)) = true := by decide +kernel

theorem ev_nb (j : ℕ) (hj : j < 104) : numBelowB (evVal.getD j 0 + 16)
    (Stmt.valsList ((vtPre.drop (evStmt.getD j 0)).take 16)) = true := by
  rcases (show j < 26 ∨ (26 ≤ j ∧ j < 52) ∨ (52 ≤ j ∧ j < 78) ∨ 78 ≤ j by omega) with h | h | h | h
  · simpa using ev_nb0 j h
  · simpa [show 26 + (j - 26) = j by omega] using ev_nb1 (j - 26) (by omega)
  · simpa [show 52 + (j - 52) = j by omega] using ev_nb2 (j - 52) (by omega)
  · simpa [show 78 + (j - 78) = j by omega] using ev_nb3 (j - 78) (by omega)

theorem ev_tau_lt : ∀ j < 104, evTau.getD j 0 < evVal.getD j 0 ∧ 13 < evTau.getD j 0 ∧
    evSt j + 1 < evVal.getD j 0 ∧ 4651 < evVal.getD j 0 := by decide +kernel

section
variable {rd : Reader}

/-- **A run of one table's evaluations**, from evaluation `j0`, its `g^τ` at `evTau j0`. -/
theorem vt_ev_run (hEv : VtEvComplete) {cur pool cplen g : E} {ws : ℕ → E} {cv0 : Digest}
    (hmem : ∀ j < 104, LoadHolds rd cur j (ws j) ∧ LoadHolds rd pool (5 + j) (ws j)) :
    ∀ (d j0 : ℕ), j0 + d ≤ 104 → (∀ j < d, evStmt.getD (j0 + j) 0 = evStmt.getD j0 0 + 16 * j ∧
      evVal.getD (j0 + j) 0 = evVal.getD j0 0 + 16 * j ∧ evTau.getD (j0 + j) 0 = evTau.getD j0 0) →
    (∀ j < d, LoadHolds rd cplen (5 + (j0 + j)) g) →
    ∀ σ : Val, σ (.n 4651) = cur → σ (.n 13) = pool → σ (.n 14) = cplen → σ (.n (evTau.getD j0 0)) = g →
      (σ (.n (evSt j0)), σ (.n (evSt j0 + 1))) = digestScalars (cvE cv0 ws j0) →
      Completes (coreProgram.Rel rd) rd (evVal.getD j0 0) (evVal.getD j0 0 + 16 * d)
        ((vtPre.drop (evStmt.getD j0 0)).take (16 * d)) σ (fun σ' =>
          (∀ j < d, σ' (.n (evVal.getD (j0 + j) 0)) = ws (j0 + j)) ∧
            (0 < d → (σ' (.n (evVal.getD (j0 + d - 1) 0 + 13)), σ' (.n (evVal.getD (j0 + d - 1) 0 + 14))) =
              digestScalars (cvE cv0 ws (j0 + d))))
  | 0, j0, _, _, _, σ, _, _, _, _, _ => by
    simp only [Nat.mul_zero, Nat.add_zero, List.take_zero]
    exact completes_nil _ _ σ ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | d + 1, j0, hjd, hcon, hcpl, σ, h4651, h13, h14, htau, hst => by
    have hj0 : j0 < 104 := by omega
    obtain ⟨ht0, -, hst0, hc0⟩ := ev_tau_lt j0 hj0
    have hc1 := hcon 1
    have hs : ∀ j < d, evStmt.getD (j0 + 1 + j) 0 = evStmt.getD (j0 + 1) 0 + 16 * j ∧
        evVal.getD (j0 + 1 + j) 0 = evVal.getD (j0 + 1) 0 + 16 * j ∧
        evTau.getD (j0 + 1 + j) 0 = evTau.getD (j0 + 1) 0 := fun j hj => by
      obtain ⟨a1, b1, c1⟩ := hcon 1 (by omega)
      obtain ⟨a2, b2, c2⟩ := hcon (1 + j) (by omega)
      rw [show j0 + 1 + j = j0 + (1 + j) by omega, a2, b2, c2, a1, b1, c1]
      exact ⟨by omega, by omega, rfl⟩
    have hunit : Completes (coreProgram.Rel rd) rd (evVal.getD j0 0) (evVal.getD j0 0 + 16)
        ((vtPre.drop (evStmt.getD j0 0)).take 16) σ (fun σ' =>
          σ' (.n (evVal.getD j0 0)) = ws j0 ∧ σ' (.n (evVal.getD j0 0 + 15)) = ws j0 ∧
            (σ' (.n (evVal.getD j0 0 + 13)), σ' (.n (evVal.getD j0 0 + 14))) =
              digestScalars (obsCv (cvE cv0 ws j0) (ws j0))) :=
      hEv j0 hj0 rd σ cur pool cplen (ws j0) g (cvE cv0 ws j0) h4651 h13 h14 htau hst (hmem j0 hj0).1
        (hmem j0 hj0).2 (by simpa using hcpl 0 (by omega))
    have IH := vt_ev_run (cplen := cplen) (g := g) (cv0 := cv0) hEv hmem d (j0 + 1)
    rcases d with _ | d
    · rw [show 16 * (0 + 1) = 16 from rfl]
      refine hunit.mono le_rfl le_rfl fun σ' q => ⟨fun j hj => ?_, fun _ => ?_⟩
      · obtain rfl : j = 0 := by omega
        simpa using q.1
      · simpa [cvE_succ] using q.2.2
    obtain ⟨a1, b1, c1⟩ := hc1 (by omega)
    simp only [Nat.mul_one] at a1 b1
    rw [show 16 * (d + 1 + 1) = 16 + 16 * (d + 1) by ring]
    refine (vt_cons (Q := fun σ'' => (∀ j < d + 1, σ'' (.n (evVal.getD (j0 + 1 + j) 0)) = ws (j0 + 1 + j)) ∧
        (0 < d + 1 → (σ'' (.n (evVal.getD (j0 + 1 + (d + 1) - 1) 0 + 13)),
          σ'' (.n (evVal.getD (j0 + 1 + (d + 1) - 1) 0 + 14))) = digestScalars (cvE cv0 ws (j0 + 1 + (d + 1)))))
      (by omega) (by omega) (numBelow_of_B (ev_nb j0 hj0)) hunit
      (fun σ1 σ2 hag hp => by simp +contextual (disch := omega) only [hag]; exact hp)
      fun σ' e p => ?_).mono le_rfl le_rfl ?_
    · rw [← a1, ← b1]
      have hr := IH (by omega) hs
        (fun j hj => by rw [show j0 + 1 + j = j0 + (j + 1) by omega]; exact hcpl (j + 1) (by omega)) σ'
        (by rw [Ext.app' e _ (by omega), h4651]) (by rw [Ext.app' e _ (by omega), h13])
        (by rw [Ext.app' e _ (by omega), h14])
        (by rw [c1, Ext.app' e _ (by omega), htau])
        (by
          simp only [evSt, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, cvE_succ]
          rw [show evVal.getD j0 0 + 13 + 1 = evVal.getD j0 0 + 14 by omega]
          exact p.2.2)
      rw [show evVal.getD (j0 + 1) 0 + 16 * (d + 1) = evVal.getD j0 0 + (16 + 16 * (d + 1)) by omega] at hr
      exact hr
    · rintro σ'' ⟨⟨q0, -⟩, qr, qs⟩
      refine ⟨fun j hj => ?_, fun _ => ?_⟩
      · rcases j with _ | j
        · simpa using q0
        · rw [show j0 + (j + 1) = j0 + 1 + j by omega]; exact qr j (by omega)
      · rw [show j0 + (d + 1 + 1) - 1 = j0 + 1 + (d + 1) - 1 by omega,
          show j0 + (d + 1 + 1) = j0 + 1 + (d + 1) by omega]
        exact qs (by omega)

end

section
variable {rd : Reader}

/-- `vt_ev_run` at literal positions. -/
theorem vt_ev_run' (hEv : VtEvComplete) {cur pool cplen g : E} {ws : ℕ → E} {cv0 : Digest}
    (hmem : ∀ j < 104, LoadHolds rd cur j (ws j) ∧ LoadHolds rd pool (5 + j) (ws j)) (d j0 : ℕ) (hd : 0 < d)
    (hjd : j0 + d ≤ 104) (hcon : ∀ j < d, evStmt.getD (j0 + j) 0 = evStmt.getD j0 0 + 16 * j ∧
      evVal.getD (j0 + j) 0 = evVal.getD j0 0 + 16 * j ∧ evTau.getD (j0 + j) 0 = evTau.getD j0 0)
    (hcpl : ∀ j < d, LoadHolds rd cplen (5 + (j0 + j)) g) {lo st s so tv : ℕ} (hlo : evVal.getD j0 0 = lo)
    (hst : evStmt.getD j0 0 = st) (hs : evSt j0 = s) (hso : evVal.getD (j0 + d - 1) 0 + 13 = so)
    (htv : evTau.getD j0 0 = tv) {σ : Val} (h4651 : σ (.n 4651) = cur) (h13 : σ (.n 13) = pool)
    (h14 : σ (.n 14) = cplen) (htau : σ (.n tv) = g)
    (hcv : (σ (.n s), σ (.n (s + 1))) = digestScalars (cvE cv0 ws j0)) :
    Completes (coreProgram.Rel rd) rd lo (lo + 16 * d) ((vtPre.drop st).take (16 * d)) σ (fun σ' =>
      (∀ j < d, σ' (.n (lo + 16 * j)) = ws (j0 + j)) ∧
        (σ' (.n so), σ' (.n (so + 1))) = digestScalars (cvE cv0 ws (j0 + d))) := by
  subst hlo hst hs hso htv
  refine (vt_ev_run hEv hmem d j0 hjd hcon hcpl σ h4651 h13 h14 htau hcv).mono le_rfl le_rfl
    fun σ' ⟨q1, q2⟩ => ⟨fun j hj => by rw [← (hcon j hj).2.1]; exact q1 j hj, ?_⟩
  rw [show evVal.getD (j0 + d - 1) 0 + 13 + 1 = evVal.getD (j0 + d - 1) 0 + 14 by omega]
  exact q2 hd

/-- `VtAirComplete` at literal positions, the next table's `g^τ` read. -/
theorem vt_air' (hAir : VtAirComplete) (t : ℕ) (ht : t < 6) {lo hi a b tv tvn : ℕ} {τn : ℕ}
    (hlo : airLo.getD t 0 = lo) (hhi : airHi.getD t 0 = hi) (ha : airA.getD t 0 = a) (hb : airB.getD t 0 = b)
    (htv : tauV.getD t 0 = tv) (htvn : t < 5 → tauV.getD (t + 1) 0 = tvn) {σ : Val} {fpw dims pC pP : E}
    {n τ : ℕ} (h11 : σ (.n 11) = fpw) (h7 : σ (.n 7) = dims) (h4639 : σ (.n 4639) = pC)
    (h4655 : σ (.n 4655) = pP) (h4554 : σ (.n 4554) = gen ^ n) (htau : σ (.n tv) = gen ^ τ) (hτ : τ ≤ n)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) (hpC : ∃ v, LoadHolds rd pC (n - τ) v)
    (hpP : ∃ v, LoadHolds rd pP τ v) (hdn : t < 5 → LoadHolds rd dims (t + 2) (gen ^ τn)) :
    Completes (coreProgram.Rel rd) rd lo hi ((vtPre.drop a).take (b - a)) σ (fun σ' =>
      t < 5 → σ' (.n tvn) = gen ^ τn) := by
  subst hlo hhi ha hb htv
  refine (hAir t ht rd σ fpw dims pC pP n τ h11 h7 h4639 h4655 h4554 htau hτ hfpw hpC hpP
    fun h => ⟨_, hdn h⟩).mono le_rfl le_rfl fun σ' q h => ?_
  rw [← htvn h]; exact q h _ (hdn h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- **Statements `4374 ..< 7854`**: the first table's `g^τ`, then per table its evaluations and its
constraint window, which reads the next table's `g^τ`. -/
theorem vt_phaseD (hEv : VtEvComplete) (hAir : VtAirComplete) {σ : Val}
    {cur pool cplen fpw dims pC pP : E} {n : ℕ} {τ : ℕ → ℕ} {ws : ℕ → E} {cv0 : Digest}
    (h7 : σ (.n 7) = dims) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool) (h14 : σ (.n 14) = cplen)
    (h4554 : σ (.n 4554) = gen ^ n) (h4639 : σ (.n 4639) = pC) (h4655 : σ (.n 4655) = pP)
    (h4651 : σ (.n 4651) = cur) (hcv0 : (σ (.n 4649), σ (.n (4649 + 1))) = digestScalars (cvE cv0 ws 0))
    (hdims : ∀ t < 6, LoadHolds rd dims (t + 1) (gen ^ τ t)) (hτn : ∀ t < 6, τ t ≤ n)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) (hpC : ∀ t < 6, ∃ v, LoadHolds rd pC (n - τ t) v)
    (hpP : ∀ t < 6, ∃ v, LoadHolds rd pP (τ t) v)
    (hmem : ∀ j < 104, LoadHolds rd cur j (ws j) ∧ LoadHolds rd pool (5 + j) (ws j))
    (hcpl : ∀ t < 6, ∀ j < evCnt.getD t 0, LoadHolds rd cplen (5 + (evFirst.getD t 0 + j)) (gen ^ τ t)) :
    Completes (coreProgram.Rel rd) rd 4660 8140
      ((vtPre.drop 4374).take (1 + (16 * 15 + ((4863 - 4615) + (16 * 15 + ((5392 - 5103) + (16 * 8 + ((5669 - 5520) + (16 * 15 + ((6192 - 5909) + (16 * 14 + ((6694 - 6416) + (16 * 37 + ((7854 - 7286))))))))))))))) σ (fun σ' =>
        (∀ j < 104, σ' (.n (evVal.getD j 0)) = ws j) ∧
          (σ' (.n 7569), σ' (.n (7569 + 1))) = digestScalars (cvE cv0 ws 104)) := by
  refine (vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
    (vt_c_tau h7 (hdims 0 (by norm_num))) (by vt_stable) fun σ1 e1 p1 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_run' hEv hmem 15 0 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 0 (by norm_num) j hj) (lo := 4661) (st := 4375) (s := 4649) (so := 4898) (tv := 4660)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e1]; exact h14)
        p1
        (by simp (disch := omega) only [Ext.app' e1]; exact hcv0))
      (by vt_stable) fun σ2 e2 p2 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_air' hAir 0 (by norm_num) (lo := 4901) (hi := 5149) (a := 4615) (b := 4863) (tv := 4660)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 5148) (τn := τ 1) (by decide) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e2, Ext.app' e1]; exact p1) (hτn 0 (by norm_num)) hfpw (hpC 0 (by norm_num)) (hpP 0 (by norm_num)) (fun h => hdims 1 (by norm_num)))
      (by vt_stable) fun σ3 e3 p3 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_run' hEv hmem 15 15 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 1 (by norm_num) j hj) (lo := 5149) (st := 4863) (s := 4898) (so := 5386) (tv := 5148)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p3 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p2.2)))
      (by vt_stable) fun σ4 e4 p4 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_air' hAir 1 (by norm_num) (lo := 5389) (hi := 5678) (a := 5103) (b := 5392) (tv := 5148)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 5677) (τn := τ 2) (by decide) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p3 (by norm_num))) (hτn 1 (by norm_num)) hfpw (hpC 1 (by norm_num)) (hpP 1 (by norm_num)) (fun h => hdims 2 (by norm_num)))
      (by vt_stable) fun σ5 e5 p5 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_run' hEv hmem 8 30 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 2 (by norm_num) j hj) (lo := 5678) (st := 5392) (s := 5386) (so := 5803) (tv := 5677)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p5 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p4.2)))
      (by vt_stable) fun σ6 e6 p6 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_air' hAir 2 (by norm_num) (lo := 5806) (hi := 5955) (a := 5520) (b := 5669) (tv := 5677)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 5954) (τn := τ 3) (by decide) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p5 (by norm_num))) (hτn 2 (by norm_num)) hfpw (hpC 2 (by norm_num)) (hpP 2 (by norm_num)) (fun h => hdims 3 (by norm_num)))
      (by vt_stable) fun σ7 e7 p7 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_run' hEv hmem 15 38 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 3 (by norm_num) j hj) (lo := 5955) (st := 5669) (s := 5803) (so := 6192) (tv := 5954)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p7 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p6.2)))
      (by vt_stable) fun σ8 e8 p8 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_air' hAir 3 (by norm_num) (lo := 6195) (hi := 6478) (a := 5909) (b := 6192) (tv := 5954)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 6477) (τn := τ 4) (by decide) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p7 (by norm_num))) (hτn 3 (by norm_num)) hfpw (hpC 3 (by norm_num)) (hpP 3 (by norm_num)) (fun h => hdims 4 (by norm_num)))
      (by vt_stable) fun σ9 e9 p9 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_run' hEv hmem 14 53 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 4 (by norm_num) j hj) (lo := 6478) (st := 6192) (s := 6192) (so := 6699) (tv := 6477)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p9 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p8.2)))
      (by vt_stable) fun σ10 e10 p10 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_air' hAir 4 (by norm_num) (lo := 6702) (hi := 6980) (a := 6416) (b := 6694) (tv := 6477)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 6979) (τn := τ 5) (by decide) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p9 (by norm_num))) (hτn 4 (by norm_num)) hfpw (hpC 4 (by norm_num)) (hpP 4 (by norm_num)) (fun h => hdims 5 (by norm_num)))
      (by vt_stable) fun σ11 e11 p11 =>
    vt_cons (by norm_num) (by norm_num) (numBelow_of_B (by decide +kernel))
      (vt_ev_run' hEv hmem 37 67 (by norm_num) (by norm_num) (by decide +kernel)
        (fun j hj => hcpl 5 (by norm_num) j hj) (lo := 6980) (st := 6694) (s := 6699) (so := 7569) (tv := 6979)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp (disch := omega) only [Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4651) (by simp (disch := omega) only [Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h13) (by simp (disch := omega) only [Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h14)
        (p11 (by norm_num))
        (by simp (disch := omega) only [Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p10.2)))
      (by vt_stable) fun σ12 e12 p12 =>
    (vt_air' hAir 5 (by norm_num) (lo := 7572) (hi := 8140) (a := 7286) (b := 7854) (tv := 6979)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (tvn := 0) (τn := 0) (by decide) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h11) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h7) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4639) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4655) (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact h4554)
        (by simp (disch := omega) only [Ext.app' e12, Ext.app' e11, Ext.app' e10, Ext.app' e9, Ext.app' e8, Ext.app' e7, Ext.app' e6, Ext.app' e5, Ext.app' e4, Ext.app' e3, Ext.app' e2, Ext.app' e1]; exact (p11 (by norm_num))) (hτn 5 (by norm_num)) hfpw (hpC 5 (by norm_num)) (hpP 5 (by norm_num)) (fun h => absurd h (by norm_num)))).mono le_rfl le_rfl ?_
  rintro σ' ⟨-, ⟨v0, -⟩, -, ⟨v1, -⟩, -, ⟨v2, -⟩, -, ⟨v3, -⟩, -, ⟨v4, -⟩, -, ⟨v5, s5⟩, -⟩
  refine ⟨fun j hj => ?_, s5⟩
  have hv : ∀ j < 104, evVal.getD j 0 =
      if j < 15 then 4661 + 16 * j else if j < 30 then 5149 + 16 * (j - 15) else if j < 38 then
        5678 + 16 * (j - 30) else if j < 53 then 5955 + 16 * (j - 38) else if j < 67 then
          6478 + 16 * (j - 53) else 6980 + 16 * (j - 67) := by decide +kernel
  rw [hv j hj]
  by_cases c0 : j < 15
  · simpa [c0] using v0 j c0
  by_cases c1 : j < 30
  · simpa [c0, c1, show 15 + (j - 15) = j by omega] using v1 (j - 15) (by omega)
  by_cases c2 : j < 38
  · simpa [c0, c1, c2, show 30 + (j - 30) = j by omega] using v2 (j - 30) (by omega)
  by_cases c3 : j < 53
  · simpa [c0, c1, c2, c3, show 38 + (j - 38) = j by omega] using v3 (j - 38) (by omega)
  by_cases c4 : j < 67
  · simpa [c0, c1, c2, c3, c4, show 53 + (j - 53) = j by omega] using v4 (j - 53) (by omega)
  · simpa [c0, c1, c2, c3, c4, show 67 + (j - 67) = j by omega] using v5 (j - 67) (by omega)
end

end
end LeanVM.Guest.B1.VerifySub
