module

public import Quantum.Qrom.Xmss.End
public import Quantum.Qrom.Xmss.Multi.GameTFacts
public import Quantum.Qrom.Xmss.Multi.GameTCalls

@[expose] public section

/-!
# The end of leanXMSS's multi-user QROM chain: runtime 2's win

The `n`-user analog of `Quantum.Qrom.Xmss.End`: the win of runtime 2 at the hidden values `θ`
(the canonical game `muGameQN`) against an event `E` of the register that contains the
projection of `BadQN` (Events), at the end of the game.

* **The game's shape** (`muGameQN_eq`): the challenge prefix, the logging reads of the forged
  user's verification (`wReadsQN`, single-user `readsProgramV`) and the winning condition.
* **The decompressed reads** (`htQ₂N_readsProgramV`): from registers without empty cell, the
  logging reads keep the register and return the honest evaluation against the view.
* **The winning runs** (`winDecompQN`): for a good table, in the decompressed basis the prefix's
  facts hold for every user (`prefixFactsQN`), and in the compressed basis a view holding the log
  is in `BadQN` (`win_imp_badQN` at the forged user). EndReads' `win_le_of_winDecomp`: the win is
  at most the event weight at the end of the game plus `readErrQ`
  (`evalDistMap_muGameQN_le_eventWeight`).
* **The event bound** (`ewMuGameQN_le`): from a bound `(advTermQ q + √tw)²` at the end of the
  prefix, the verification reads graded like sponge calls:
  `(advTermQ q + verTermQ + √(tw + verLinQ))²`.
* **Averaged** (`uavg_ite_le_of_forall`): the win masked to good tables against the averaged
  costs, Jensen for `(a + √f)²`.
-/

open Matrix IPFunctor OracleSpec
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT readLift readLiftQ liftRead decR
  NoBot NoBotDb initU initU_posSemidef runSig runSig_of_not runSig_posSemidef
  conj_runSig_of ofReal_trace_conj_runSig trace_conj_branch_true_le_eventWeight
  ofReal_trace_branch_le_one evalDistMap_winBit querySupportedOn_of_conj_compressReg WinDecomp
  win_le_of_winDecomp readLift_bind₂ realizeT_bind₂ extCls noBot_runtimeR
  querySupportedOn_runtimeR_step' rpow_inv_two_eventWeight_keepReads_le keepCost nonKeep
  nonKeep_le_one chg_map chg_act tmplLens readLens isChargeBound_mono_charge eventWeight_bind₂
  eventWeight_eq_tsum_run₂ tsum_rpow_inv_two_ite rpow_inv_two_add_le_of_le_sq uavg_const
  uavg_sq_rpow_add_le)
open Quantum.Qrom.SufCma.Multi (MuSignLog cmdCharge hashCharge signCharge)
open Quantum.SufCma (QueriesSatisfy trace queries trace_query_bind trace_pure)

attribute [local irreducible] xmssRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-! ## The game's shape -/

section shape

/-- The winning condition of a prefix outcome: the forged user's transcript does not contain the
forgery, and every user's transcript is valid. -/
noncomputable def winCondQN (valid : SignLog → Bool) (pre : (Fin n → PublicKey) × MuRun n) :
    Bool :=
  xmssRom.winningCondition (pre.2.2.user pre.2.1.1) pre.2.1.2 && pre.2.2.allValid valid

/-- **The verification's logging reads** of a prefix outcome under the forged user's key,
realized at `θ`. -/
noncomputable def wReadsQN (θ : HPosN n → Digest) (pre : (Fin n → PublicKey) × MuRun n) :
    QComp (recHwSpec HashOutput HashDomain (HPosN n) (SelMemN n)) (QReg.of Unit) (QReg.of Unit)
      (Bool × List (HashDomain × HashOutput)) :=
  realizeT θ (readLiftQ goodQN
    (readsProgramV (SelMemN n) (QReg.of Unit) (xmssRom.verify (pre.1 pre.2.1.1) pre.2.1.2)))

theorem realizeT_verifyTN (valid : SignLog → Bool) (θ : HPosN n → Digest)
    (pre : (Fin n → PublicKey) × MuRun n) :
    realizeT θ (verifyTN (SelMemN n) valid pre) =
      (wReadsQN θ pre).bind fun a ↦ QuantumComp₂.pure (winCondQN valid pre && a.1) := by
  rw [verifyTN, readsProgram_eq_map, QuantumComp₂.map_eq]
  simp only [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rw [readLift_bind₂, QuantumComp₂.bind_assoc, realizeT_bind₂]
  rfl

/-- **The game is its prefix, the logging reads and the winning condition.** -/
theorem muGameQN_eq (valid : SignLog → Bool) (A : MuAdversary n) (θ : HPosN n → Digest) :
    muGameQN valid A θ = (prefixQN A θ).bind fun pre ↦
      (wReadsQN θ pre).bind fun a ↦ QuantumComp₂.pure (winCondQN valid pre && a.1) := by
  rw [muGameQN, muGameT_eq_prefixTN_bind, realizeT_bind₂]
  simp only [realizeT_verifyTN]
  rfl

/-- The game is its prefix and the realized verification. -/
theorem muGameQN_eq_verify (valid : SignLog → Bool) (A : MuAdversary n) (θ : HPosN n → Digest) :
    muGameQN valid A θ = (prefixQN A θ).bind fun pre ↦
      realizeT θ (verifyTN (SelMemN n) valid pre) := by
  rw [muGameQN, muGameT_eq_prefixTN_bind, realizeT_bind₂]
  rfl

end shape

/-! ## The logging reads in the decompressed basis -/

section reads

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (HPosN n) × M)
  (θ : HPosN n → Digest)

/-- A program from no register is supported anywhere. -/
theorem htQ₂N_of_empty {A B : QReg} {α : Type} (y : QComp (RSpecN n M) A B α)
    (Q : α → Set (RRegN n M)) : HTQ₂N m₀ y ∅ Q := by
  intro ρ hρ a
  have h0 : ρ = 0 := by
    ext m m'
    by_contra h
    exact (hρ m m' h).1
  rw [h0, map_zero]
  exact querySupportedOn_zero _ _

/-- **The logging reads in the decompressed basis**: from registers with no empty cell whose
views only hash along `x`, they keep the register and return the honest evaluation against the
view, with the view's answers appended to the log. -/
theorem htQ₂N_run_romReadImplV (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    ∀ (P : Set (RRegN n M)) (log : List (HashDomain × HashOutput)), (∀ s ∈ P, NoBot s) →
      (∀ s ∈ P, QueriesSatisfy (romAnswers (hvwN s)) IsHash x) →
      HTQ₂N m₀ (realizeT θ (readLiftQ goodQN ((simulateQ (romReadImplV M B) x).run log))) P
        fun a ↦ {s | s ∈ P ∧ a = (evalWithAnswerFn (romAnswers (hvwN s)) x,
          log ++ trace (romAnswers (hvwN s)) (hashReadV (hvwN s)) x)} := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro P log _ _
    rw [simulateQ_pure, StateT.run_pure]
    exact htQ₂N_pure (a, log) fun s hs ↦
      ⟨hs, by rw [evalWithAnswerFn_pure, trace_pure, List.append_nil]⟩
  | query_bind t k ih =>
    intro P log hP hx
    rcases P.eq_empty_or_nonempty with hP0 | ⟨s₀, hs₀⟩
    · subst hP0
      exact htQ₂N_of_empty m₀ _ _
    have hq : ∀ s ∈ P, QueriesSatisfy (romAnswers (hvwN s)) IsHash
        (k (romAnswers (hvwN s) t)) := fun s hs q hq ↦ hx s hs q (by
      rw [queries, trace_query_bind]
      exact List.mem_append_right _ hq)
    obtain ⟨c, rfl⟩ : IsHash t := hx s₀ hs₀ t (by
      rw [queries, trace_query_bind]
      exact List.mem_append_left _ (List.mem_singleton_self t))
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change HTQ₂N m₀ (realizeT θ (readLiftQ goodQN (QuantumComp₂.bind
      ((readCall (.readH c keepMem) B).bind fun r ↦
        QuantumComp₂.pure (r.1.getD 0, log ++ [(c, r.1.getD 0)]))
      fun p ↦ (simulateQ (romReadImplV M B) (k p.1)).run p.2))) P _
    rw [readLift_bind₂, realizeT_bind₂]
    have h1 := ((detQN_readH (m₀ := m₀) (θ := θ) c keepMem B).bind fun r ↦
      detQN_pure (m₀ := m₀) (θ := θ) (B := B)
        (r.1.getD 0, log ++ [(c, r.1.getD 0)])) P hP
    refine HTQ₂N.bind (h1.mono subset_rfl fun p ↦ ?_) fun p ↦
      ((ih p.1 {s | s ∈ P ∧ p = (hvwN s c, log ++ [(c, hvwN s c)])} p.2
        (fun s hs ↦ hP s hs.1) fun s hs ↦ ?_).mono subset_rfl fun b ↦ ?_)
    · rintro s' ⟨s, hs, rfl, rfl⟩
      exact ⟨hs, rfl⟩
    · obtain ⟨hs, rfl⟩ := hs
      exact hq s hs
    · rintro s ⟨⟨hs, rfl⟩, rfl⟩
      refine ⟨hs, ?_⟩
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, trace_query_bind,
        List.append_assoc]
      rfl

/-- **The logging reads of a computation that only hashes**, in the decompressed basis. -/
theorem htQ₂N_readsProgramV (B : QReg) {α : Type} (x : OracleComp RomOracles α)
    (hx : ∀ H, QueriesSatisfy (romAnswers H) IsHash x) (P : Set (RRegN n M))
    (hP : ∀ s ∈ P, NoBot s) :
    HTQ₂N m₀ (realizeT θ (readLiftQ goodQN (readsProgramV M B x))) P
      fun a ↦ {s | s ∈ P ∧ a = honestEvalV (hvwN s) x} :=
  (htQ₂N_run_romReadImplV m₀ θ B x P [] hP fun s _ ↦ hx (hvwN s)).mono subset_rfl fun _ ↦
    fun _ hs ↦ ⟨hs.1, hs.2.trans (by rw [List.nil_append]; rfl)⟩

end reads

/-! ## The winning runs -/

section decomp

/-- A run of the game: a prefix outcome and a run of the logging reads. -/
abbrev RunQN (n : ℕ) : Type :=
  ((Fin n → PublicKey) × MuRun n) × (Bool × List (HashDomain × HashOutput))

/-- **The classical facts of a winning run** `i` on the hardwired cells and the memory `b`: the
run wins, its reads number at most `verifyCalls`, any function answering its reads as logged
verifies as it did, and some function `H` gives the public keys, and per user the transcript's
signatures, the records and the known inputs of the hardwired cells (`win_imp_badQN`'s
hypotheses). -/
def RunFactsN (S0 : Fin n → MasterSeed) (w : QTableN n) (valid : SignLog → Bool) (i : RunQN n)
    (b : Hw HashOutput HashDomain × (Finset (HPosN n) × SelMemN n)) : Prop :=
  (winCondQN valid i.1 && i.2.1) = true ∧ i.2.2.length ≤ verifyCalls ∧
    (∀ H' : HashDomain → HashOutput, (∀ p ∈ i.2.2, H' p.1 = p.2) →
      honestEval H' (xmssRom.verify (i.1.1 i.1.2.1.1) i.1.2.1.2) =
        (i.2.1, i.2.2.map Prod.fst)) ∧
    ∃ H : HashDomain → HashOutput, (∀ j, i.1.1 j = (w.user j).publicKey) ∧ ∀ j,
      (∀ r ∈ i.1.2.2.user j, r.2 = (w.user j).signature H r.1) ∧
      (SigningTranscript.NoLeafIndexReused (i.1.2.2.user j) →
        ∀ r ∈ i.1.2.2.user j, Records (w.user j) H (b.2.2 j) r.1) ∧
      ∀ D : DbReg HashOutput HashDomain,
        HwKnown (S0 j) (w.user j) H (projU j (D, b.1, b.2.2)) ((i.1.2.2.user j).map Sigma.fst)

/-- **A view holding the log of a run with its facts is in the event** (`win_imp_badQN` at the
forged user). -/
theorem mem_badQN_of_runFactsN (S0 : Fin n → MasterSeed) (w : QTableN n) (hP : PDistinct w)
    (valid : SignLog → Bool) (i : RunQN n) {s : RRegN n (SelMemN n)}
    (hf : RunFactsN S0 w valid i s.2) (ha : DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1)) :
    (s.1, s.2.1, s.2.2.2) ∈ BadQN (honN S0 w) w.params := by
  obtain ⟨hw, hl, hev, H, hpk, hj⟩ := hf
  obtain ⟨hlog, hM, hEx⟩ := hj i.1.2.1.1
  have hU : ∀ p ∈ i.2.2, unionH (s.1, s.2.1, s.2.2.2) p.1 = some p.2 := of_agrees_wLogQ hl ha
  have hE := hev (viewH (unionH (s.1, s.2.1, s.2.2.2))) fun p hp ↦ by
    rw [viewH, hU p hp, Option.getD_some]
  obtain ⟨hwv, hver⟩ := (Bool.and_eq_true _ _).mp hw
  rw [winCondQN] at hwv
  obtain ⟨hwc, -⟩ := (Bool.and_eq_true _ _).mp hwv
  have hwin : SigningTranscript.NoLeafIndexReused (i.1.2.2.user i.1.2.1.1) ∧
      ¬Common.SufCma.SignerReturnedForgery SigningRequest.message (i.1.2.2.user i.1.2.1.1)
        i.1.2.1.2.message i.1.2.1.2.signature := by
    have h := hwc
    rw [winningCondition_xmssRom] at h
    simpa only [LeanXmss.RandomPermutationModel.sufCmaScheme, decide_eq_true_eq] using h
  refine win_imp_badQN S0 w hP H (s.1, s.2.1, s.2.2.2) i.1.2.1.1 (i.1.2.2.user i.1.2.1.1)
    i.1.2.1.2 hlog (hM hwin.1) (hEx s.1) hwin ?_ ?_
  · rw [← hpk i.1.2.1.1, hE]
    exact hver
  · rw [← hpk i.1.2.1.1, hE]
    intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    rw [hU p hp]
    rfl

variable (valid : SignLog → Bool) (A : MuAdversary n) (θ : HPosN n → Digest)

/-- **A winning run**: the branch of the logging reads at the run after the prefix's, when the
game wins on it; `0` otherwise. -/
noncomputable def σQN (i : RunQN n) :
    Matrix (Unit × RRegN n (SelMemN n)) (Unit × RRegN n (SelMemN n)) ℂ :=
  runSig m0N (prefixQN A θ) (wReadsQN θ) (fun pre a ↦ winCondQN valid pre && a.1) i

/-- **A winning run in the decompressed basis**, for a good table: the prefix's facts, and the run
is the honest verification against the view, with its answers. -/
theorem dec_σQN (hw : (tableN (seedsOf θ)).good (tabOfN θ)) (i : RunQN n) :
    QuerySupportedOn (fun p : Unit × RRegN n (SelMemN n) ↦ p.2)
      {s | (winCondQN valid i.1 && i.2.1) = true ∧ PreFactsQN (seedsOf θ) (tabOfN θ) i.1 s ∧
        i.2 = honestEvalV (hvwN s) (xmssRom.verify (i.1.1 i.1.2.1.1) i.1.2.1.2)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset (HPosN n) × SelMemN n)) (σQN valid A θ i)) := by
  by_cases h : (winCondQN valid i.1 && i.2.1) = true
  · rw [σQN, conj_runSig_of m0N _ _ _ i h]
    have hpre := prefixFactsQN (seedsOf θ) (tabOfN θ) hw A m0N rfl i.1
    rw [thetaOfN_seedsOf_tabOfN] at hpre
    exact (htQ₂N_readsProgramV m0N θ (QReg.of Unit) _ (fun _ ↦ isHash_verify _ _)
      {s | PreFactsQN (seedsOf θ) (tabOfN θ) i.1 s} (fun s hs ↦ hs.2.1) _ hpre i.2).mono
        fun s hs ↦ ⟨h, hs⟩
  · rw [σQN, runSig_of_not m0N _ _ _ i h, map_zero]
    exact querySupportedOn_zero _ _

/-- **Recorded**: in the decompressed basis, no empty cell, and the view holds the log. -/
theorem recorded_σQN (hw : (tableN (seedsOf θ)).good (tabOfN θ)) (i : RunQN n) :
    QuerySupportedOn (fun y : Unit × RRegN n (SelMemN n) ↦ y.2)
      {s | NoBotDb s.1 ∧ DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset (HPosN n) × SelMemN n)) (σQN valid A θ i)) :=
  (dec_σQN valid A θ hw i).mono fun s hs ↦ by
    obtain ⟨-, ⟨-, hnb, -⟩, he⟩ := hs
    have e2 := congrArg Prod.snd he
    refine ⟨hnb, agrees_wLogQ fun p hp ↦ ?_⟩
    rw [e2] at hp
    rw [snd_eq_of_mem_trace_hashReadV hp]
    exact hwView_eq_some_hvwN hnb p.1

/-- **The run's classical facts**, in the decompressed basis. -/
theorem facts_σQN (hw : (tableN (seedsOf θ)).good (tabOfN θ)) (i : RunQN n) :
    QuerySupportedOn (fun y : Unit × RRegN n (SelMemN n) ↦ y.2)
      {s | RunFactsN (seedsOf θ) (tabOfN θ) valid i s.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset (HPosN n) × SelMemN n)) (σQN valid A θ i)) :=
  (dec_σQN valid A θ hw i).mono fun s hs ↦ by
    obtain ⟨hwin, ⟨hpk, -, hj⟩, he⟩ := hs
    have e1 := congrArg Prod.fst he
    have e2 := congrArg Prod.snd he
    refine ⟨hwin, ?_, fun H' hH' ↦ ?_, viewH (unionH (s.1, s.2.1, s.2.2.2)), hpk,
      fun j ↦ ⟨(hj j).1, (hj j).2.1, fun _ ↦ (hj j).2.2⟩⟩
    · rw [e2]
      exact length_trace_hashReadV_le _ (verify_cost _ _)
    · simp only [honestEvalV] at e1 e2
      rw [e1, e2, map_fst_trace_hashReadV]
      exact honestEval_eq_of_agree _ fun p hp ↦ hH' p (e2 ▸ hp)

variable (E : Set (RRegN n (SelMemN n))) [DecidablePred (· ∈ E)]
  (hE : ∀ s : RRegN n (SelMemN n),
    (s.1, s.2.1, s.2.2.2) ∈ BadQN (honN (seedsOf θ) (tabOfN θ)) (tabOfN θ).params → s ∈ E)

omit [DecidablePred (· ∈ E)] in
include hE in
/-- **In the event**: in the compressed basis, a view holding the log is in `E`. -/
theorem bad_σQN (hw : (tableN (seedsOf θ)).good (tabOfN θ)) (i : RunQN n) :
    QuerySupportedOn (fun y : Unit × RRegN n (SelMemN n) ↦ y.2)
      {s | DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1) → s ∈ E} (σQN valid A θ i) :=
  (querySupportedOn_of_conj_compressReg (P := RunFactsN (seedsOf θ) (tabOfN θ) valid i)
    (facts_σQN valid A θ hw i)).mono fun _ hf ha ↦
      hE _ (mem_badQN_of_runFactsN (seedsOf θ) (tabOfN θ) hw.2 valid i hf ha)

include hE in
/-- **The decomposition of runtime 2's winning runs along the verification's reads**, for a good
table. -/
noncomputable def winDecompQN (hw : (tableN (seedsOf θ)).good (tabOfN θ)) :
    WinDecomp m0N (muGameQN valid A θ) (muGameQN valid A θ) E verifyCalls 0 0 where
  ι := RunQN n
  σ := σQN valid A θ
  log i := wLogQ i.2.2
  psd i := runSig_posSemidef m0N _ _ _ i
  countH i := readCount_wLogQ_le _
  countK i := (readCount_wLogQ_eq_zero _ (by decide)).le
  countK' i := (readCount_wLogQ_eq_zero _ (by decide)).le
  recorded i := recorded_σQN valid A θ hw i
  bad i := bad_σQN valid A θ E hE hw i
  win := by
    rw [evalDistMap_winBit, muGameQN_eq]
    have h := ofReal_trace_conj_runSig m0N (prefixQN A θ) (wReadsQN θ)
      (fun pre a ↦ winCondQN valid pre && a.1) 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.le
  event := by
    have h := ofReal_trace_conj_runSig m0N (prefixQN A θ) (wReadsQN θ)
      (fun pre a ↦ winCondQN valid pre && a.1) ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector E)
    rw [← muGameQN_eq] at h
    exact h.symm.le.trans (trace_conj_branch_true_le_eventWeight m0N (muGameQN valid A θ) _)
  mass := by
    have h := ofReal_trace_conj_runSig m0N (prefixQN A θ) (wReadsQN θ)
      (fun pre a ↦ winCondQN valid pre && a.1) 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    rw [← muGameQN_eq] at h
    exact h.symm.le.trans (ofReal_trace_branch_le_one m0N (muGameQN valid A θ) true)

include hE in
/-- **Runtime 2's win is at most the event at the end of the game and the read error**, for a
good table. -/
theorem evalDistMap_muGameQN_le_eventWeight (hw : (tableN (seedsOf θ)).good (tabOfN θ)) :
    (runtimeR m0N).evalDistMap .instruments (muGameQN valid A θ) (SubState.basis ()) winObsQ
        {true} ≤
      (runtimeR m0N).eventWeight .instruments (hwProjector E) (muGameQN valid A θ)
        (initU m0N) + readErrQ :=
  win_le_of_winDecomp (winDecompQN valid A θ E hE hw)

end decomp

/-! ## The verification's calls -/

section verifyCalls

/-- A lifted read that keeps the memory keeps the memory with the label. -/
theorem keepUpd_liftReadQN {M : Type} (c : HwRead HashOutput HashDomain M) (hc : c.KeepsMem) :
    KeepUpd (liftRead (S := HPosN n) c) := by
  cases c with
  | readH z upd =>
    change upd = keepMem at hc
    subst hc
    exact fun _ _ ↦ rfl
  | readK x upd =>
    change upd = keepMem at hc
    subst hc
    exact fun _ _ ↦ rfl
  | readK' x upd =>
    change upd = keepMem at hc
    subst hc
    exact fun _ _ ↦ rfl

/-- **The verification calls only reads that keep the memory.** -/
theorem chg_verifyTN_nonKeep (θ : HPosN n → Digest) (valid : SignLog → Bool)
    (x : (Fin n → PublicKey) × MuRun n) :
    IFreeM.IsChargeBound (realizeT θ (verifyTN (SelMemN n) valid x))
      (portCharge (nonKeep HashOutput HashDomain (HPosN n) (SelMemN n))) 0 := by
  unfold verifyTN
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ ↦ trivial
  refine IFreeM.IsChargeBound.mapLens (readLens (goodQN (n := n))) ?_
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    (chg_map _ Prod.fst (sChg_simulateQ_romReadImpl_keep (M := SelMemN n) (QReg.of Unit) _ []))
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show nonKeep HashOutput HashDomain (HPosN n) (SelMemN n) (.inl (.inl (.inr (liftRead c)))) ≤
      nonKeepRdQ (SelMemN n) (.inr c)
    by_cases hc : c.KeepsMem
    · have h0 : nonKeep HashOutput HashDomain (HPosN n) (SelMemN n)
          (.inl (.inl (.inr (liftRead c)))) = 0 := by
        simp only [nonKeep, keepUpd_liftReadQN c hc, ↓reduceIte]
      omega
    · have h1 : nonKeepRdQ (SelMemN n) (.inr c) = 1 := by
        simp only [nonKeepRdQ, hc, ↓reduceIte]
      have h2 := nonKeep_le_one (X := HashOutput) (Z := HashDomain) (S := HPosN n)
        (M := SelMemN n) (.inl (.inl (.inr (liftRead c))))
      omega

/-- **The verification's calls**: at most `verifyCalls`. -/
theorem chg_verifyTN_one (θ : HPosN n → Digest) (valid : SignLog → Bool)
    (x : (Fin n → PublicKey) × MuRun n) :
    IFreeM.IsChargeBound (realizeT θ (verifyTN (SelMemN n) valid x)) (portCharge fun _ ↦ 1)
      verifyCalls := by
  have he : rChargeQN (n := n) (SelMemN n) 1 1 1 1 1 = fun _ ↦ 1 := by
    funext i
    rcases i with ((i | c) | c) | T
    · rfl
    · simp only [rChargeQN, ite_self]
    · rfl
    · rfl
  have h := isChargeBound_realizeTN (M := SelMemN n) 1 1 1 1 1 θ
    (chg_verifyTN (M := SelMemN n) 1 1 1 1 1 valid x)
  rw [he] at h
  simpa using h

end verifyCalls

/-! ## The event bound over the game -/

section event

/-- The initial state has empty databases. -/
theorem querySupportedOn_dbGrade_initQN :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := HashOutput) (Z := HashDomain)
      (m0N (n := n))).D ↦ dbGrade m.2.1) (Set.Iic 0) (initU (X := HashOutput)
        (Z := HashDomain) (m0N (n := n))) := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty HashOutput HashDomain, m0N) : RRegN n (SelMemN n))).matrix) m m' ≠
      0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact absurd rfl h

variable (valid : SignLog → Bool) (A : MuAdversary n) {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)

include hhash hsign in
/-- **The prefix's calls**: at most `q + clsCapN n total`. -/
theorem calls_prefixQN (θ : HPosN n → Digest) :
    IFreeM.IsChargeBound (prefixQN A θ) (portCharge fun _ ↦ 1) (q + clsCapN n total) := by
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    ((advCalls_prefixQN cwUpdN A hhash hsign θ).add (clsCalls_prefixQN cwUpdN A hhash hsign θ))
  rcases a with o | ⟨i, E, ℓ⟩
  · exact le_rfl
  · show 1 ≤ (if extCls HashOutput HashDomain (Finset (HPosN n) × SelMemN n)
        (recSpec (HPosN n) (SelMemN n)) i then 0 else 1) +
      (if extCls HashOutput HashDomain (Finset (HPosN n) × SelMemN n)
        (recSpec (HPosN n) (SelMemN n)) i then 1 else 0)
    split_ifs <;> omega

include hhash hsign in
/-- **The event bound over the whole game**: from a bound `(advTermQ q + √tw)²` on the event
weight at the end of the challenge prefix, each of the `verifyCalls` verification reads costs
`√(2^-128)` in the square root and its linear terms `verLinQ`:
`ew ≤ (advTermQ q + verTermQ + √(tw + verLinQ))²`. -/
theorem ewMuGameQN_le (B : Set (RRegN n (SelMemN n))) [DecidablePred (· ∈ B)]
    (hup : ∀ W m, UpClosed (slice B W m))
    (hfresh : ∀ W m t, FreshBound (slice B W m) t (2 ^ 128 : ℝ≥0∞)⁻¹)
    (θ : HPosN n → Digest) (tw : ℝ≥0∞)
    (hpreT : (runtimeR m0N).eventWeight .instruments (hwProjector B) (prefixQN A θ)
      (initU m0N) ≤ (advTermQ q + tw ^ (2⁻¹ : ℝ)) ^ 2) :
    (runtimeR m0N).eventWeight .instruments (hwProjector B) (muGameQN valid A θ) (initU m0N) ≤
      (advTermQ q + verTermQ + (tw + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hε : (2 ^ 128 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by positivity)
  have hρa := fun a ↦ ((runtimeR m0N).run₂ .instruments (prefixQN A θ)).posSemidef_branch_apply a
    (initU_posSemidef (X := HashOutput) (Z := HashDomain) m0N)
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step
    (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))) (fun s ↦ dbGrade s.1)
    (fun _ ↦ 1) (querySupportedOn_runtimeR_step' (X := HashOutput) (Z := HashDomain) m0N)
    .instruments (calls_prefixQN A hhash hsign θ) querySupportedOn_dbGrade_initQN
    ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))
    .instruments (prefixQN A θ) (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le B hup m0N
    (N := q + clsCapN n total + verifyCalls) hε (fun W m ↦ hfresh W m _) .instruments
    (realizeT θ (verifyTN (SelMemN n) valid a)) (chg_verifyTN_one θ valid a)
    (chg_verifyTN_nonKeep θ valid a) (t := 0 + (q + clsCapN n total)) (by omega) (hρa a)
    (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0N).run₂ .instruments (prefixQN A θ)).branch a
      (initU m0N)).trace.re ≤ 1 :=
    (((runtimeR m0N).run₂ .instruments (prefixQN A θ)).isCPTNIFamily.tsum_ofReal_trace_re_le
      (initU_posSemidef (X := HashOutput) (Z := HashDomain) m0N)).trans
        (ENNReal.ofReal_le_one.mpr ((SubState.basis ()).prod
          (runtimeR (X := HashOutput) (Z := HashDomain) (m0N (n := n))).init).trace_re_le_one)
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0N) .instruments
    (hwProjector B) (prefixQN A θ) (initU m0N)
  have hm : ∑' j, (∑' a, (if j < verifyCalls then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) *
      ENNReal.ofReal (((runtimeR m0N).run₂ .instruments (prefixQN A θ)).branch a
        (initU m0N)).trace.re) ^ (2⁻¹ : ℝ) ≤ verTermQ := by
    calc _ ≤ ∑' j, ((if j < verifyCalls then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTermQ := by
          unfold verTermQ
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector B)
      (((runtimeR m0N).run₂ .instruments (prefixQN A θ)).branch a (initU m0N)) +
      (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (((runtimeR m0N).run₂ .instruments (prefixQN A θ)).branch a
          (initU m0N)).trace.re) ≤
      (runtimeR m0N).eventWeight .instruments (hwProjector B) (prefixQN A θ) (initU m0N) +
        verLinQ := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹ * _
        ≤ (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹ * 1 := by
          gcongr
      _ = verLinQ := mul_one _
  have hpre' : ((runtimeR m0N).eventWeight .instruments (hwProjector B)
      (prefixQN A θ) (initU m0N) + verLinQ) ^ (2⁻¹ : ℝ) ≤
      advTermQ q + (tw + verLinQ) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := advTermQ q ^ 2) (δ := 0) (C := verLinQ)
      (b := tw) (a := (runtimeR m0N).eventWeight .instruments
        (hwProjector B) (prefixQN A θ) (initU m0N)) (by
          rw [sq_rpow_inv_two_eq, add_zero]
          exact hpreT.trans_eq (by rw [add_comm (advTermQ q)]))
    rwa [sq_rpow_inv_two_eq, zero_add] at h
  have hew : (runtimeR m0N).eventWeight .instruments (hwProjector B) (muGameQN valid A θ)
      (initU m0N) = ∑' a, (runtimeR m0N).eventWeight .instruments (hwProjector B)
        (realizeT θ (verifyTN (SelMemN n) valid a))
        (((runtimeR m0N).run₂ .instruments (prefixQN A θ)).branch a (initU m0N)) := by
    rw [muGameQN_eq_verify]
    exact eventWeight_bind₂ (runtimeR m0N) .instruments (hwProjector B)
      (prefixQN A θ) _ (initU_posSemidef (X := HashOutput) (Z := HashDomain) m0N)
  have hfin : (runtimeR m0N).eventWeight .instruments (hwProjector B) (muGameQN valid A θ)
      (initU m0N) ^ (2⁻¹ : ℝ) ≤ advTermQ q + verTermQ + (tw + verLinQ) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0N).eventWeight .instruments (hwProjector B)
          (prefixQN A θ) (initU m0N) + verLinQ) ^ (2⁻¹ : ℝ) + verTermQ :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ advTermQ q + (tw + verLinQ) ^ (2⁻¹ : ℝ) + verTermQ :=
          add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

end event

/-! ## Averaged -/

section average

/-- **The masked average of runtime 2's win** (Jensen for `(a + √f)²`): if `p θ` is at most
`(c + √(tw θ + verLinQ))² + readErrQ` on the tables of a mask `G`, and the costs `tw` average to
at most `T`, the average of `p` under `G` is at most `(c + √(T + verLinQ))² + readErrQ`. -/
theorem uavg_ite_le_of_forall {Θ : Type} [Fintype Θ] [Nonempty Θ] (G : Θ → Prop)
    [DecidablePred G] (p tw : Θ → ℝ≥0∞) (c : ℝ≥0∞)
    (hp : ∀ θ, G θ → p θ ≤ (c + (tw θ + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ)
    {T : ℝ≥0∞} (hcost : uavg tw ≤ T) :
    uavg (fun θ ↦ if G θ then p θ else 0) ≤ (c + (T + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ := by
  have hpt : ∀ θ, (if G θ then p θ else 0) ≤
      (c + (tw θ + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ := fun θ ↦ by
    by_cases hg : G θ
    · simp only [hg, ↓reduceIte]
      exact hp θ hg
    · simp only [hg, ↓reduceIte]
      exact zero_le
  refine (uavg_mono hpt).trans ?_
  rw [uavg_add, uavg_const]
  refine add_le_add ?_ le_rfl
  have h := uavg_sq_rpow_add_le (fun _ : Θ ↦ c ^ 2) (fun θ ↦ tw θ + verLinQ)
  simp only [sq_rpow_inv_two_eq, uavg_const, uavg_add] at h
  exact h.trans (pow_le_pow_left₀ zero_le (add_le_add le_rfl
    (ENNReal.rpow_le_rpow (add_le_add hcost le_rfl) (by norm_num))) 2)

end average

end Quantum.Qrom.Xmss.Multi

end
