module

public import Quantum.Qrom.Xmss.Hybrid
public import Quantum.Qrom.Xmss.Costs.Bound
public import Quantum.Xmss.Assembly.WinDecomp
public import Quantum.Xmss.Assembly.EventSqrt

@[expose] public section

/-!
# The end of leanXMSS's QROM chain: runtime 2's win

The win of runtime 2 at the hidden values `θ` (`p2Q A θ`, Hybrid) against the event `BadRQ`
(Events' `BadQ` read through the template's label) at the end of the game.

* **The verification's reads with their answers** (`romReadImplV`, `readsProgramV`): the
  game's read program logs each hashed cell with its answer (`readsProgram_eq_map`), so the
  game is its challenge prefix, a run of the logging reads and the winning condition
  (`gameQ_eq`).
* **The decompressed reads** (`htQ₂_run_romReadImplV`): from registers without empty cell whose
  views only hash along the computation, the logging reads keep the register and return the
  honest evaluation against the view, with the view's answers.
* **The winning runs** (`winDecompQ`): one run per prefix outcome and accepting run of the
  reads; recorded in the decompressed basis (no empty cell, the view holds the log), and in the
  compressed basis a view holding the log is in the event (`win_imp_badQ` on the prefix's facts
  `prefixFactsQ`, which bear on the hardwired cells and the memory only through some function
  `H`, and an accepting honest verification held by the view). EndReads' `win_le_of_winDecomp`:
  the win is at most the event weight at the end of the game plus the read error
  `readErrQ = 2 · verifyCalls / |Y|` (`p2Q_le_eventWeight`).
* **The event bound** (`ewGameQ_le`): from the bound `(advTermQ q + √twPQ)²` at the end of the
  challenge prefix (Costs' `ewPrefixQ_le`), the verification's reads graded like sponge calls
  (EventSqrt's `rpow_inv_two_eventWeight_keepReads_le`, fresh fraction `2^-128`):
  `(advTermQ q + verTermQ + √(twPQ + verLinQ))²`.
* **Averaged** (`uavg_p2Q_le`): with the prefix's averaged classical cost at most `T`,
  `E p2Q ≤ (advTermQ q + verTermQ + √(T + verLinQ))² + readErrQ`.
-/

open Matrix IPFunctor OracleSpec
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid Quantum.SufCma
open LeanXmss HashSig
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT readLift readLiftQ liftRead decR
  NoBot NoBotDb initU initU_posSemidef runSig runSig_of runSig_of_not runSig_posSemidef
  conj_runSig_of ofReal_trace_conj_runSig trace_conj_branch_true_le_eventWeight
  ofReal_trace_branch_le_one evalDistMap_winBit winBit querySupportedOn_inter
  querySupportedOn_of_conj_compressReg WinDecomp win_le_of_winDecomp readLift_bind₂
  realizeT_bind₂ extCls noBot_runtimeR querySupportedOn_runtimeR_step'
  rpow_inv_two_eventWeight_keepReads_le keepCost nonKeep nonKeep_le_one
  SChg sChg_pure sChg_bind chg_map chg_act tmplLens readLens
  isChargeBound_mono_charge eventWeight_bind₂ eventWeight_eq_tsum_run₂
  tsum_rpow_inv_two_ite rpow_inv_two_add_le_of_le_sq uavg_const uavg_sq_rpow_add_le)

/-- The winning condition of the QROM copy is the statement's. -/
theorem winningCondition_xmssRom :
    xmssRom.winningCondition = LeanXmss.RandomPermutationModel.sufCmaScheme.winningCondition :=
  rfl

attribute [local irreducible] xmssRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The read programs with their answers -/

section values

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The model's oracles by read ports, logging the answers**: GameReads' `romReadImpl` with each
hashed cell logged beside its answer. -/
noncomputable def romReadImplV (B : QReg) :
    QueryImpl RomOracles (StateT (List (HashDomain × HashOutput))
      (QComp (hwReadSpec HashOutput HashDomain M) B B))
  | .inl n => liftM (QComp.coinImpl (hwReadSpec HashOutput HashDomain M) B n)
  | .inr x => fun log ↦ (readCall (.readH x keepMem) B).bind fun r ↦
      QuantumComp₂.pure (r.1.getD 0, log ++ [(x, r.1.getD 0)])

/-- **A computation as a program of read ports, with the answers**: its result and the hashed
cells with their answers. -/
noncomputable def readsProgramV (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    QComp (hwReadSpec HashOutput HashDomain M) B B (α × List (HashDomain × HashOutput)) :=
  (simulateQ (romReadImplV M B) x).run []

variable {M}

omit [Fintype M] [DecidableEq M] in
/-- The logging reads forget their answers to `romReadImpl`'s. -/
theorem run_simulateQ_romReadImpl (B : QReg) {α : Type} (x : OracleComp RomOracles α)
    (log : List (HashDomain × HashOutput)) :
    (simulateQ (romReadImpl M B) x).run (log.map Prod.fst) =
      (fun p ↦ (p.1, p.2.map Prod.fst)) <$> (simulateQ (romReadImplV M B) x).run log := by
  induction x using OracleComp.inductionOn generalizing log with
  | pure a => simp [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.pure_bind]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
      StateT.run_bind, StateT.run_bind]
    rcases t with n | x
    · simp only [romReadImpl, romReadImplV, StateT.run_monadLift, map_bind, bind_assoc,
        pure_bind, ih]
    · change ((readCall (.readH x keepMem) B).bind fun r ↦
          QuantumComp₂.pure (r.1.getD 0, log.map Prod.fst ++ [x])) >>= _ =
        _ <$> (((readCall (.readH x keepMem) B).bind fun r ↦
          QuantumComp₂.pure (r.1.getD 0, log ++ [(x, r.1.getD 0)])) >>= _)
      simp only [QuantumComp₂.bind_eq, QuantumComp₂.map_eq, QuantumComp₂.bind_assoc,
        QuantumComp₂.pure_bind, QuantumComp₂.map_eq_bind_pure]
      refine congrArg _ (funext fun r ↦ ?_)
      have h := ih (r.1.getD 0) (log ++ [(x, r.1.getD 0)])
      rw [List.map_append, List.map_singleton] at h
      rw [h, QuantumComp₂.map_eq, QuantumComp₂.map_eq_bind_pure]

omit [Fintype M] [DecidableEq M] in
/-- **`readsProgram` is the logging reads with the answers forgotten.** -/
theorem readsProgram_eq_map (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    readsProgram M B x = (fun p ↦ (p.1, p.2.map Prod.fst)) <$> readsProgramV M B x :=
  run_simulateQ_romReadImpl B x []

end values

/-! ## The game's shape -/

section shape

/-- The winning condition of a prefix outcome. -/
noncomputable def winCondQ (pre : PublicKey × (Forgery × SignLog)) : Bool :=
  xmssRom.winningCondition pre.2.2 pre.2.1

/-- **The verification's logging reads** of a prefix outcome, realized at `θ`. -/
noncomputable def wReadsQ (θ : HPos → Digest) (pre : PublicKey × (Forgery × SignLog)) :
    QComp (recHwSpec HashOutput HashDomain HPos SelMem) (QReg.of Unit) (QReg.of Unit)
      (Bool × List (HashDomain × HashOutput)) :=
  realizeT θ (readLiftQ goodQ (readsProgramV SelMem (QReg.of Unit) (xmssRom.verify pre.1 pre.2.1)))

theorem realizeT_verifyT (θ : HPos → Digest) (pre : PublicKey × (Forgery × SignLog)) :
    realizeT θ (verifyT SelMem pre) =
      (wReadsQ θ pre).bind fun a ↦ QuantumComp₂.pure (winCondQ pre && a.1) := by
  rw [verifyT, readsProgram_eq_map, QuantumComp₂.map_eq]
  simp only [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rw [readLift_bind₂, QuantumComp₂.bind_assoc, realizeT_bind₂]
  rfl

/-- **The game is its prefix, the logging reads and the winning condition.** -/
theorem gameQ_eq (A : Adversary) (θ : HPos → Digest) :
    gameQ A θ = (prefixQ A θ).bind fun pre ↦
      (wReadsQ θ pre).bind fun a ↦ QuantumComp₂.pure (winCondQ pre && a.1) := by
  rw [gameQ, gameT_eq_prefixT_bind, realizeT_bind₂]
  simp only [realizeT_verifyT]
  rfl

/-- The game is its prefix and the realized verification. -/
theorem gameQ_eq_verify (A : Adversary) (θ : HPos → Digest) :
    gameQ A θ = (prefixQ A θ).bind fun pre ↦ realizeT θ (verifyT SelMem pre) := by
  rw [gameQ, gameT_eq_prefixT_bind, realizeT_bind₂]
  rfl

end shape

/-! ## The logging reads in the decompressed basis -/

section reads

/-- A hash query's cell with the answer of `H`. -/
def hashReadV (H : HashDomain → HashOutput) : RomOracles.Domain → List (HashDomain × HashOutput)
  | .inl _ => []
  | .inr x => [(x, H x)]

/-- **The honest evaluation with the answers**: the result and the hashed cells with `H`'s
answers. -/
def honestEvalV {α : Type} (H : HashDomain → HashOutput) (x : OracleComp RomOracles α) :
    α × List (HashDomain × HashOutput) :=
  (evalWithAnswerFn (romAnswers H) x, trace (romAnswers H) (hashReadV H) x)

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset HPos × M) (θ : HPos → Digest)

/-- A program from no register is supported anywhere. -/
theorem htQ₂_of_empty {A B : QReg} {α : Type} (y : QComp (RSpec M) A B α)
    (Q : α → Set (RReg M)) : HTQ₂ m₀ y ∅ Q := by
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
theorem htQ₂_run_romReadImplV (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    ∀ (P : Set (RReg M)) (log : List (HashDomain × HashOutput)), (∀ s ∈ P, NoBot s) →
      (∀ s ∈ P, QueriesSatisfy (romAnswers (hvw s)) IsHash x) →
      HTQ₂ m₀ (realizeT θ (readLiftQ goodQ ((simulateQ (romReadImplV M B) x).run log))) P
        fun a ↦ {s | s ∈ P ∧ a = (evalWithAnswerFn (romAnswers (hvw s)) x,
          log ++ trace (romAnswers (hvw s)) (hashReadV (hvw s)) x)} := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro P log _ _
    rw [simulateQ_pure, StateT.run_pure]
    exact htQ₂_pure (a, log) fun s hs ↦
      ⟨hs, by rw [evalWithAnswerFn_pure, trace_pure, List.append_nil]⟩
  | query_bind t k ih =>
    intro P log hP hx
    rcases P.eq_empty_or_nonempty with hP0 | ⟨s₀, hs₀⟩
    · subst hP0
      exact htQ₂_of_empty m₀ _ _
    have hq : ∀ s ∈ P, QueriesSatisfy (romAnswers (hvw s)) IsHash
        (k (romAnswers (hvw s) t)) := fun s hs q hq ↦ hx s hs q (by
      rw [queries, trace_query_bind]
      exact List.mem_append_right _ hq)
    obtain ⟨c, rfl⟩ : IsHash t := hx s₀ hs₀ t (by
      rw [queries, trace_query_bind]
      exact List.mem_append_left _ (List.mem_singleton_self t))
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change HTQ₂ m₀ (realizeT θ (readLiftQ goodQ (QuantumComp₂.bind
      ((readCall (.readH c keepMem) B).bind fun r ↦
        QuantumComp₂.pure (r.1.getD 0, log ++ [(c, r.1.getD 0)]))
      fun p ↦ (simulateQ (romReadImplV M B) (k p.1)).run p.2))) P _
    rw [readLift_bind₂, realizeT_bind₂]
    have h1 := ((detQ_readH (m₀ := m₀) (θ := θ) c keepMem B).bind fun r ↦
      detQ_pure (m₀ := m₀) (θ := θ) (B := B)
        (r.1.getD 0, log ++ [(c, r.1.getD 0)])) P hP
    refine HTQ₂.bind (h1.mono subset_rfl fun p ↦ ?_) fun p ↦
      ((ih p.1 {s | s ∈ P ∧ p = (hvw s c, log ++ [(c, hvw s c)])} p.2
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
theorem htQ₂_readsProgramV (B : QReg) {α : Type} (x : OracleComp RomOracles α)
    (hx : ∀ H, QueriesSatisfy (romAnswers H) IsHash x) (P : Set (RReg M))
    (hP : ∀ s ∈ P, NoBot s) :
    HTQ₂ m₀ (realizeT θ (readLiftQ goodQ (readsProgramV M B x))) P
      fun a ↦ {s | s ∈ P ∧ a = honestEvalV (hvw s) x} :=
  (htQ₂_run_romReadImplV m₀ θ B x P [] hP fun s _ ↦ hx (hvw s)).mono subset_rfl fun _ ↦
    fun _ hs ↦ ⟨hs.1, hs.2.trans (by rw [List.nil_append]; rfl)⟩

end reads

/-! ## Honest evaluations and their logs -/

section honest

theorem snd_eq_of_mem_trace_hashReadV {H : HashDomain → HashOutput} {α : Type}
    {x : OracleComp RomOracles α} {p : HashDomain × HashOutput}
    (hp : p ∈ trace (romAnswers H) (hashReadV H) x) : p.2 = H p.1 := by
  rw [trace_eq_flatMap] at hp
  obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 hp
  rcases q with n | c
  · exact absurd hq List.not_mem_nil
  · rw [hashReadV, List.mem_singleton] at hq
    rw [hq]

theorem map_fst_trace_hashReadV (H : HashDomain → HashOutput) {α : Type}
    (x : OracleComp RomOracles α) :
    (trace (romAnswers H) (hashReadV H) x).map Prod.fst = trace (romAnswers H) hashRead x := by
  rw [trace_eq_flatMap, trace_eq_flatMap, List.map_flatMap]
  congr 1
  funext q
  rcases q <;> rfl

/-- **The logged reads number at most the hash calls of a path bound.** -/
theorem length_trace_hashReadV_le (H : HashDomain → HashOutput) {α : Type}
    {x : OracleComp RomOracles α} {n : ℕ} (h : Common.QueryCostAtMost x hashCallCost n) :
    (trace (romAnswers H) (hashReadV H) x).length ≤ n := by
  rw [trace_eq_flatMap, List.length_flatMap]
  refine le_of_eq_of_le (congrArg List.sum (List.map_congr_left fun q _ ↦ ?_))
    (Quantum.Xmss.sum_map_queries_le (romAnswers H) hashCallCost h)
  rcases q <;> rfl

/-- **The honest evaluation depends on `H` only through what it reads**: a function answering
every logged read of the evaluation against `H` as `H` does gives the same result and reads. -/
theorem honestEval_eq_of_agree {H H' : HashDomain → HashOutput} {α : Type}
    (x : OracleComp RomOracles α) (h : ∀ p ∈ trace (romAnswers H) (hashReadV H) x, H' p.1 = p.2) :
    honestEval H' x = (evalWithAnswerFn (romAnswers H) x, trace (romAnswers H) hashRead x) := by
  induction x using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    have hk := ih (romAnswers H t) fun p hp ↦ h p (by
      rw [trace_query_bind]
      exact List.mem_append_right _ hp)
    have ht : romAnswers H' t = romAnswers H t := by
      rcases t with n | c
      · rfl
      · exact h (c, H c) (by
          rw [trace_query_bind]
          exact List.mem_append_left _ (List.mem_singleton_self _))
    obtain ⟨h1, h2⟩ := Prod.mk.inj hk
    simp only [honestEval] at h1 h2 ⊢
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_liftM_query, trace_query_bind, trace_query_bind, ht, h1, h2]

end honest

/-! ## The winning runs -/

section decomp

/-- A run of the game: a prefix outcome and a run of the logging reads. -/
abbrev RunQ : Type :=
  (PublicKey × (Forgery × SignLog)) × (Bool × List (HashDomain × HashOutput))

/-- **The log of a run of the reads**, as a log of `h`-reads (empty beyond `verifyCalls` reads,
which no honest verification makes). -/
def wLogQ (l : List (HashDomain × HashOutput)) : QueryLog (spongeOSpec HashOutput HashDomain) :=
  if l.length ≤ verifyCalls then l.map fun p ↦ ⟨.h p.1, p.2⟩ else []

theorem readCount_wLogQ_le (l : List (HashDomain × HashOutput)) :
    readCount .h (wLogQ l) ≤ verifyCalls := by
  unfold wLogQ
  split_ifs with hl
  · exact List.countP_le_length.trans (by rw [List.length_map]; exact hl)
  · exact Nat.zero_le _

theorem readCount_wLogQ_eq_zero (l : List (HashDomain × HashOutput)) {p : SpongePort}
    (hp : p ≠ .h) : readCount p (wLogQ l) = 0 := by
  unfold wLogQ readCount
  split_ifs
  · rw [List.countP_eq_zero]
    intro e he
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 he
    exact fun h ↦ hp (of_decide_eq_true h).symm
  · rfl

theorem agrees_wLogQ {l : List (HashDomain × HashOutput)} {D : DbReg HashOutput HashDomain}
    (h : ∀ p ∈ l, D.1 p.1 = some p.2) : DbReg.Agrees (wLogQ l) D := by
  intro e he
  unfold wLogQ at he
  split_ifs at he
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact h p hp
  · exact absurd he List.not_mem_nil

theorem of_agrees_wLogQ {l : List (HashDomain × HashOutput)} (hl : l.length ≤ verifyCalls)
    {D : DbReg HashOutput HashDomain} (h : DbReg.Agrees (wLogQ l) D) :
    ∀ p ∈ l, D.1 p.1 = some p.2 := fun p hp ↦
  h ⟨.h p.1, p.2⟩ (by
    unfold wLogQ
    split_ifs
    exact List.mem_map.2 ⟨p, hp, rfl⟩)

/-- **The classical facts of a winning run** `i` on the hardwired cells and the memory `b`: the
run wins, its reads number at most `verifyCalls`, any function answering its reads as logged
verifies as it did, and some function `H` gives the transcript's signatures, the records and the
known inputs of the hardwired cells (`win_imp_badQ`'s hypotheses). -/
def RunFacts (θ : HPos → Digest) (i : RunQ) (b : Hw HashOutput HashDomain × QMem) : Prop :=
  (winCondQ i.1 && i.2.1) = true ∧ i.2.2.length ≤ verifyCalls ∧
    (∀ H' : HashDomain → HashOutput, (∀ p ∈ i.2.2, H' p.1 = p.2) →
      honestEval H' (xmssRom.verify i.1.1 i.1.2.1) = (i.2.1, i.2.2.map Prod.fst)) ∧
    ∃ H : HashDomain → HashOutput, i.1.1 = (tabOf θ).publicKey ∧
      (∀ r ∈ i.1.2.2, r.2 = (tabOf θ).signature H r.1) ∧
      (SigningTranscript.NoLeafIndexReused i.1.2.2 →
        ∀ r ∈ i.1.2.2, Records (tabOf θ) H b.2.2 r.1) ∧
      ∀ D : DbReg HashOutput HashDomain,
        HwKnown (seedOf θ) (tabOf θ) H (D, b.1, b.2.2) (i.1.2.2.map Sigma.fst)

/-- **A view holding the log of a run with its facts is in the event** (`win_imp_badQ`). -/
theorem mem_badRQ_of_runFacts (θ : HPos → Digest) (i : RunQ) {s : RReg SelMem}
    (hf : RunFacts θ i s.2) (ha : DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1)) :
    s ∈ BadRQ (honQ θ) := by
  obtain ⟨hw, hl, hev, H, hpk, hlog, hM, hEx⟩ := hf
  have hU : ∀ p ∈ i.2.2, unionH (projQ s) p.1 = some p.2 := of_agrees_wLogQ hl ha
  have hE := hev (viewH (unionH (projQ s))) fun p hp ↦ by
    rw [viewH, hU p hp, Option.getD_some]
  obtain ⟨hwc, hver⟩ := (Bool.and_eq_true _ _).mp hw
  have hwin : SigningTranscript.NoLeafIndexReused i.1.2.2 ∧
      ¬Common.SufCma.SignerReturnedForgery SigningRequest.message i.1.2.2 i.1.2.1.message
        i.1.2.1.signature := by
    have h := hwc
    rw [winCondQ, winningCondition_xmssRom] at h
    simpa only [LeanXmss.RandomPermutationModel.sufCmaScheme, decide_eq_true_eq] using h
  refine mem_badRQ_iff.mpr (win_imp_badQ (seedOf θ) (tabOf θ) H (projQ s) i.1.2.2 i.1.2.1 hlog
    (hM hwin.1) (hEx s.1) hwin ?_ ?_)
  · rw [← hpk, hE]
    exact hver
  · rw [← hpk, hE]
    intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    rw [hU p hp]
    rfl

variable (A : Adversary) (θ : HPos → Digest)

/-- **A winning run**: the branch of the logging reads at the run after the prefix's, when the
game wins on it; `0` otherwise. -/
noncomputable def σQ (i : RunQ) : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ :=
  runSig m0H (prefixQ A θ) (wReadsQ θ) (fun pre a ↦ winCondQ pre && a.1) i

/-- **A winning run in the decompressed basis**: the prefix's facts, and the run is the honest
verification against the view, with its answers. -/
theorem dec_σQ (i : RunQ) :
    QuerySupportedOn (fun p : Unit × RReg SelMem ↦ p.2)
      {s | (winCondQ i.1 && i.2.1) = true ∧ PreFactsQ (seedOf θ) (tabOf θ) i.1 s ∧
        i.2 = honestEvalV (hvw s) (xmssRom.verify i.1.1 i.1.2.1)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset HPos × SelMem)) (σQ A θ i)) := by
  by_cases h : (winCondQ i.1 && i.2.1) = true
  · rw [σQ, conj_runSig_of m0H _ _ _ i h]
    have hpre := prefixFactsQ (seedOf θ) (tabOf θ) A m0H rfl i.1
    rw [thetaOf_seedOf_tabOf] at hpre
    exact (htQ₂_readsProgramV m0H θ (QReg.of Unit) _ (fun _ ↦ isHash_verify _ _)
      {s | PreFactsQ (seedOf θ) (tabOf θ) i.1 s} (fun s hs ↦ hs.2.1) _ hpre i.2).mono
        fun s hs ↦ ⟨h, hs⟩
  · rw [σQ, runSig_of_not m0H _ _ _ i h, map_zero]
    exact querySupportedOn_zero _ _

/-- **Recorded**: in the decompressed basis, no empty cell, and the view holds the log. -/
theorem recorded_σQ (i : RunQ) :
    QuerySupportedOn (fun y : Unit × RReg SelMem ↦ y.2)
      {s | NoBotDb s.1 ∧ DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset HPos × SelMem)) (σQ A θ i)) :=
  (dec_σQ A θ i).mono fun s hs ↦ by
    obtain ⟨-, ⟨-, hnb, -⟩, he⟩ := hs
    have e2 := congrArg Prod.snd he
    refine ⟨hnb, agrees_wLogQ fun p hp ↦ ?_⟩
    rw [e2] at hp
    rw [snd_eq_of_mem_trace_hashReadV hp]
    exact hwView_eq_some_hvw hnb p.1

/-- **The run's classical facts**, in the decompressed basis. -/
theorem facts_σQ (i : RunQ) :
    QuerySupportedOn (fun y : Unit × RReg SelMem ↦ y.2) {s | RunFacts θ i s.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset HPos × SelMem)) (σQ A θ i)) :=
  (dec_σQ A θ i).mono fun s hs ↦ by
    obtain ⟨hw, ⟨hpk, -, hlog, hrec, hEx⟩, he⟩ := hs
    have e1 := congrArg Prod.fst he
    have e2 := congrArg Prod.snd he
    refine ⟨hw, ?_, fun H' hH' ↦ ?_, viewH (unionH (s.1, s.2.1, s.2.2.2)), hpk, hlog, hrec,
      fun _ ↦ hEx⟩
    · rw [e2]
      exact length_trace_hashReadV_le _ (verify_cost _ _)
    · simp only [honestEvalV] at e1 e2
      rw [e1, e2, map_fst_trace_hashReadV]
      exact honestEval_eq_of_agree _ fun p hp ↦ hH' p (e2 ▸ hp)

/-- **In the event**: in the compressed basis, a view holding the log is in `BadRQ`. -/
theorem bad_σQ (i : RunQ) :
    QuerySupportedOn (fun y : Unit × RReg SelMem ↦ y.2)
      {s | DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1) → s ∈ BadRQ (honQ θ)} (σQ A θ i) :=
  (querySupportedOn_of_conj_compressReg (P := RunFacts θ i) (facts_σQ A θ i)).mono
    fun _ hf ha ↦ mem_badRQ_of_runFacts θ i hf ha

/-- **The decomposition of runtime 2's winning runs along the verification's reads.** -/
noncomputable def winDecompQ :
    WinDecomp m0H (gameQ A θ) (gameQ A θ) (BadRQ (honQ θ)) verifyCalls 0 0 where
  ι := RunQ
  σ := σQ A θ
  log i := wLogQ i.2.2
  psd i := runSig_posSemidef m0H _ _ _ i
  countH i := readCount_wLogQ_le _
  countK i := (readCount_wLogQ_eq_zero _ (by decide)).le
  countK' i := (readCount_wLogQ_eq_zero _ (by decide)).le
  recorded i := recorded_σQ A θ i
  bad i := bad_σQ A θ i
  win := by
    rw [evalDistMap_winBit, gameQ_eq]
    have h := ofReal_trace_conj_runSig m0H (prefixQ A θ) (wReadsQ θ)
      (fun pre a ↦ winCondQ pre && a.1) 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.le
  event := by
    have h := ofReal_trace_conj_runSig m0H (prefixQ A θ) (wReadsQ θ)
      (fun pre a ↦ winCondQ pre && a.1)
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector (BadRQ (honQ θ)))
    rw [← gameQ_eq] at h
    exact h.symm.le.trans (trace_conj_branch_true_le_eventWeight m0H (gameQ A θ) _)
  mass := by
    have h := ofReal_trace_conj_runSig m0H (prefixQ A θ) (wReadsQ θ)
      (fun pre a ↦ winCondQ pre && a.1) 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    rw [← gameQ_eq] at h
    exact h.symm.le.trans (ofReal_trace_branch_le_one m0H (gameQ A θ) true)

/-- The read error of the verification's reads: `2 · verifyCalls / |Y|`. -/
noncomputable def readErrQ : ℝ≥0∞ :=
  ENNReal.ofReal (readError HashOutput HashDomain verifyCalls 0 0)

/-- **Runtime 2's win is at most the event at the end of the game and the read error.** -/
theorem p2Q_le_eventWeight :
    p2Q A θ ≤ (runtimeR m0H).eventWeight .instruments (hwProjector (BadRQ (honQ θ))) (gameQ A θ)
      initH + readErrQ :=
  win_le_of_winDecomp (winDecompQ A θ)

end decomp

/-! ## The verification's calls -/

section verifyCalls

variable {M : Type} [Fintype M] [DecidableEq M]

open scoped Classical in
variable (M) in
/-- The charge of the read program's calls other than the reads that keep the memory. -/
noncomputable def nonKeepRdQ : (hwReadSpec HashOutput HashDomain M).Port → ℕ
  | .inl _ => 1
  | .inr c => if c.KeepsMem then 0 else 1

omit [Fintype M] [DecidableEq M] in
/-- A lifted read that keeps the memory keeps the memory with the label. -/
theorem keepUpd_liftReadQ (c : HwRead HashOutput HashDomain M) (hc : c.KeepsMem) :
    KeepUpd (liftRead (S := HPos) c) := by
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

omit [Fintype M] [DecidableEq M] in
/-- A read that keeps the memory has charge `0`. -/
theorem chg_readCall_keepQ (c : HwRead HashOutput HashDomain M) (hc : c.KeepsMem) (B : QReg) :
    IFreeM.IsChargeBound (readCall c B) (portCharge (nonKeepRdQ M)) 0 := by
  have h0 : nonKeepRdQ M (.inr c) = 0 := by simp only [nonKeepRdQ, hc, ↓reduceIte]
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_of_eq h0, fun _ ↦ trivial⟩) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem sChg_romReadImpl_keep (B : QReg) (t : RomOracles.Domain) :
    SChg (nonKeepRdQ M) (romReadImpl M B t) 0 := by
  rcases t with n | x
  · intro s
    show IFreeM.IsChargeBound ((StateT.lift (QComp.coinImpl (hwReadSpec HashOutput HashDomain M)
      B n) : StateT (List HashDomain) (QComp (hwReadSpec HashOutput HashDomain M) B B) _).run s)
      _ _
    rw [StateT.run_lift]
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0)
      fun a' ↦ sChg_pure (σ := List HashDomain) (B := B) (nonKeepRdQ M) a' 0 s
  · intro log
    show IFreeM.IsChargeBound ((readCall (.readH x keepMem) B).bind fun r ↦
      QuantumComp₂.pure (r.1.getD 0, log ++ [x])) _ _
    exact FreeM₂.isChargeBound_bind (n₂ := 0)
      (chg_readCall_keepQ (.readH x keepMem) rfl B) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem sChg_simulateQ_romReadImpl_keep (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    SChg (nonKeepRdQ M) (simulateQ (romReadImpl M B) x) 0 := by
  induction x using OracleComp.inductionOn with
  | pure x => rw [simulateQ_pure]; exact sChg_pure _ x _
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact sChg_bind _ (sChg_romReadImpl_keep B t) fun u ↦ ih u

omit [Fintype M] [DecidableEq M] in
/-- **The verification calls only reads that keep the memory.** -/
theorem chg_verifyT_nonKeepQ (θ : HPos → Digest) (x : PublicKey × (Forgery × SignLog)) :
    IFreeM.IsChargeBound (realizeT θ (verifyT M x))
      (portCharge (nonKeep HashOutput HashDomain HPos M)) 0 := by
  unfold verifyT
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ ↦ trivial
  refine IFreeM.IsChargeBound.mapLens (readLens goodQ) ?_
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    (chg_map _ Prod.fst (sChg_simulateQ_romReadImpl_keep (M := M) (QReg.of Unit) _ []))
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show nonKeep HashOutput HashDomain HPos M (.inl (.inl (.inr (liftRead c)))) ≤
      nonKeepRdQ M (.inr c)
    by_cases hc : c.KeepsMem
    · have h0 : nonKeep HashOutput HashDomain HPos M (.inl (.inl (.inr (liftRead c)))) = 0 := by
        simp only [nonKeep, keepUpd_liftReadQ c hc, ↓reduceIte]
      omega
    · have h1 : nonKeepRdQ M (.inr c) = 1 := by simp only [nonKeepRdQ, hc, ↓reduceIte]
      have h2 := nonKeep_le_one (X := HashOutput) (Z := HashDomain) (S := HPos) (M := M)
        (.inl (.inl (.inr (liftRead c))))
      omega

omit [Fintype M] [DecidableEq M] in
/-- **The verification's calls**: at most `verifyCalls`. -/
theorem chg_verifyT_oneQ (θ : HPos → Digest) (x : PublicKey × (Forgery × SignLog)) :
    IFreeM.IsChargeBound (realizeT θ (verifyT M x)) (portCharge fun _ ↦ 1) verifyCalls := by
  have he : rChargeQ M 1 1 1 1 1 = fun _ ↦ 1 := by
    funext i
    rcases i with ((i | c) | c) | T
    · rfl
    · simp only [rChargeQ, ite_self]
    · rfl
    · rfl
  have h := isChargeBound_realizeT (M := M) 1 1 1 1 1 θ (chg_verifyT (M := M) 1 1 1 1 1 x)
  rw [he] at h
  simpa using h

end verifyCalls

/-! ## The event bound over the game -/

section event

/-- **The verification term**: `verifyCalls · √(2^-128)`, its reads graded like sponge calls. -/
noncomputable def verTermQ : ℝ≥0∞ :=
  (verifyCalls : ℝ≥0∞) * ((2 ^ 128 : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)

/-- **The verification's linear term**: `verifyCalls (2^-128 + 2/|Y| + 2/|D|)`. -/
noncomputable def verLinQ : ℝ≥0∞ :=
  (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹

/-- The initial state has empty databases. -/
theorem querySupportedOn_dbGrade_initQ :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := HashOutput) (Z := HashDomain)
      m0Q).D ↦ dbGrade m.2.1) (Set.Iic 0) initQ := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty HashOutput HashDomain, m0Q) : RReg SelMem)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact absurd rfl h

variable (A : Adversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) lifetime)
include hhash hsign

/-- **The prefix's calls**: at most `q + clsCapQ`. -/
theorem calls_prefixQ (θ : HPos → Digest) :
    IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun _ ↦ 1) (q + clsCapQ) := by
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    ((advCalls_prefixQ cwUpd A hhash hsign θ).add (clsCalls_prefixQ cwUpd A hhash hsign θ))
  rcases a with o | ⟨i, E, ℓ⟩
  · exact le_rfl
  · show 1 ≤ (if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) +
      (if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0)
    split_ifs <;> omega

/-- **The event bound over the whole game**: from Costs' bound at the end of the challenge prefix,
each of the `verifyCalls` verification reads costs `√(2^-128)` in the square root and its linear
terms `keepE + recW` (`verLinQ`):
`ew ≤ (advTermQ q + verTermQ + √(twPQ hon A θ + verLinQ))²`. -/
theorem ewGameQ_le (hon : HonestCells) (θ : HPos → Digest) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (gameQ A θ) initQ ≤
      (advTermQ q + verTermQ + (twPQ hon A θ + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hpreT := ewPrefixQ_le hon A θ (advCalls_prefixQ cwUpd A hhash hsign θ)
    (clsCalls_prefixQ cwUpd A hhash hsign θ)
  have hε : (2 ^ 128 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by positivity)
  have hρa := fun a ↦ ((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).posSemidef_branch_apply a
    initQ_posSemidef
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step
    (runtimeR (X := HashOutput) (Z := HashDomain) m0Q) (fun s ↦ dbGrade s.1) (fun _ ↦ 1)
    (querySupportedOn_runtimeR_step' (X := HashOutput) (Z := HashDomain) m0Q) .instruments
    (calls_prefixQ A hhash hsign θ) querySupportedOn_dbGrade_initQ ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR (X := HashOutput) (Z := HashDomain) m0Q .instruments
    (prefixQ A θ) (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le (BadRQ hon)
    (fun W m ↦ upClosed_slice_badRQ W m) m0Q (N := q + clsCapQ + verifyCalls) hε
    (fun W m ↦ freshBound_slice_badRQ W m _) .instruments
    (realizeT θ (verifyT SelMem a)) (chg_verifyT_oneQ θ a) (chg_verifyT_nonKeepQ θ a)
    (t := 0 + (q + clsCapQ)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a
      initQ).trace.re ≤ 1 :=
    (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).isCPTNIFamily.tsum_ofReal_trace_re_le
      initQ_posSemidef).trans ofReal_trace_initQ_le_one
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0Q) .instruments
    (hwProjector (BadRQ hon)) (prefixQ A θ) initQ
  have hm : ∑' j, (∑' a, (if j < verifyCalls then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) *
      ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a
        initQ).trace.re) ^ (2⁻¹ : ℝ) ≤ verTermQ := by
    calc _ ≤ ∑' j, ((if j < verifyCalls then (2 ^ 128 : ℝ≥0∞)⁻¹ else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTermQ := by
          unfold verTermQ
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector (BadRQ hon))
      (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a initQ) +
      (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a
          initQ).trace.re) ≤
      (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (prefixQ A θ) initQ +
        verLinQ := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹ * _
        ≤ (verifyCalls : ℝ≥0∞) * keepCost HashOutput HashDomain (2 ^ 128 : ℝ≥0∞)⁻¹ * 1 := by
          gcongr
      _ = verLinQ := mul_one _
  have hpre' : ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon))
      (prefixQ A θ) initQ + verLinQ) ^ (2⁻¹ : ℝ) ≤
      advTermQ q + (twPQ hon A θ + verLinQ) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := advTermQ q ^ 2) (δ := 0) (C := verLinQ)
      (b := twPQ hon A θ) (a := (runtimeR m0Q).eventWeight .instruments
        (hwProjector (BadRQ hon)) (prefixQ A θ) initQ) (by
          rw [sq_rpow_inv_two_eq, add_zero]
          exact hpreT.trans_eq (by rw [add_comm (advTermQ q)]))
    rwa [sq_rpow_inv_two_eq, zero_add] at h
  have hew : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (gameQ A θ)
      initQ = ∑' a, (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon))
        (realizeT θ (verifyT SelMem a))
        (((runtimeR m0Q).run₂ .instruments (prefixQ A θ)).branch a initQ) := by
    rw [gameQ_eq_verify]
    exact eventWeight_bind₂ (runtimeR m0Q) .instruments (hwProjector (BadRQ hon))
      (prefixQ A θ) _ initQ_posSemidef
  have hfin : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon)) (gameQ A θ)
      initQ ^ (2⁻¹ : ℝ) ≤ advTermQ q + verTermQ + (twPQ hon A θ + verLinQ) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ hon))
          (prefixQ A θ) initQ + verLinQ) ^ (2⁻¹ : ℝ) + verTermQ :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ advTermQ q + (twPQ hon A θ + verLinQ) ^ (2⁻¹ : ℝ) + verTermQ :=
          add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

/-- **Runtime 2's win at `θ`**: `p2Q ≤ (advTermQ q + verTermQ + √(twPQ + verLinQ))² + readErrQ`. -/
theorem p2Q_le (θ : HPos → Digest) :
    p2Q A θ ≤ (advTermQ q + verTermQ + (twPQ (honQ θ) A θ + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 +
      readErrQ :=
  (p2Q_le_eventWeight A θ).trans (add_le_add (ewGameQ_le A hhash hsign (honQ θ) θ) le_rfl)

/-- **Runtime 2's win, averaged** (Jensen for `(a + √f)²`): with the prefix's averaged classical
cost at most `T`, `E p2Q ≤ (advTermQ q + verTermQ + √(T + verLinQ))² + readErrQ`. -/
theorem uavg_p2Q_le {T : ℝ≥0∞} (hcost : uavg (fun θ : HPos → Digest ↦ twPQ (honQ θ) A θ) ≤ T) :
    uavg (p2Q A) ≤ (advTermQ q + verTermQ + (T + verLinQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ := by
  set c := advTermQ q + verTermQ
  refine (uavg_mono (p2Q_le A hhash hsign)).trans ?_
  rw [uavg_add, uavg_const]
  refine add_le_add ?_ le_rfl
  have h := uavg_sq_rpow_add_le (fun _ : HPos → Digest ↦ c ^ 2)
    (fun θ ↦ twPQ (honQ θ) A θ + verLinQ)
  simp only [sq_rpow_inv_two_eq, uavg_const, uavg_add] at h
  refine h.trans (pow_le_pow_left₀ zero_le (add_le_add le_rfl
    (ENNReal.rpow_le_rpow (add_le_add hcost le_rfl) (by norm_num))) 2)

end event

end Quantum.Qrom.Xmss

end
