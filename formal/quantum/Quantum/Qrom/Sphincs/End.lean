module

public import Quantum.Qrom.Sphincs.Hybrid
public import Quantum.Qrom.Sphincs.GameTFactsPre
public import Quantum.Qrom.Sphincs.Classify
public import Quantum.Qrom.Sphincs.Costs.Bound
public import Quantum.Xmss.Assembly.WinDecomp
public import Quantum.Xmss.Assembly.EventSqrt
public import Quantum.Xmss.Assembly.EndReads

@[expose] public section

/-!
# The end of leanSPHINCS's QROM chain: runtime 2's win

The win of runtime 2 at the policy `strPol` and the hidden values `θ` (`p2Q strPol A θ`, Hybrid)
against the event `BadRQ (pkQ θ) (honQ θ) (starCover (streamOf θ))` (Events' `BadQ` read
through the template's label, with the static stream cover `S★` of `θ`) at the end of the game.

* **The verification's reads with their answers** (`romReadImplV`, `readsProgramV`): the
  game's read program logs each hashed input with the pair read at its regrouped cell
  (`readsProgram_eq_map`), so the game is its challenge prefix, a run of the logging reads and the
  winning condition (`gameQ_eq`).
* **The decompressed reads** (`htS₂_run_romReadImplV`): from registers without empty cell, the
  logging reads keep the register and return the honest evaluation against the regrouped view.
* **The winning runs** (`winDecompQ`): one run per prefix outcome and accepting run of the
  reads; recorded in the decompressed basis, and in the compressed basis a view holding the log
  is in the event (`win_imp_badQ` on GameTFactsPre's `prefixFactsS`, at the table `runTab` of the
  run, whose public key and honest cells are the canonical table's). EndReads'
  `win_le_of_winDecomp`: the win is at most the event weight at the end of the game plus the read
  error `readErrQ = 2 · verifyCalls / |Y|` (`p2Q_le_eventWeight`).
* **The event bound** (`ewGameQ_le`): from Costs' bound `(advTermQ q S + √twPQ)²` at the end of
  the challenge prefix, the verification's reads graded like adversary calls (EventSqrt's
  `rpow_inv_two_eventWeight_keepReads_le`, fresh fraction `epsQ S = 2^-128 + price S`).
* **Averaged** (`uavg_p2Q_le`): Minkowski over the hidden values, with the mean fresh fraction
  `epsBarQ = 2^-128 + rhoCov · 2^-128` over the uniform stream (`uavg_epsQ_le`) and the prefix's
  averaged classical cost at most `T`:
  `E p2Q ≤ (advBarQ q + verBarQ + √(T + verLinBarQ))² + readErrQ`.
-/

open Matrix IPFunctor OracleSpec
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.SufCma (QueriesSatisfy queries trace trace_eq_flatMap trace_query_bind trace_pure)
open Quantum.Qrom.Xmss (romAnswers hashRead honestEval IsHash)
open Quantum.Sphincs (Disclosures Covered rhoCov price)
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
theorem winningCondition_sphincsRom :
    sphincsRom.winningCondition = RandomPermutationModel.sufCmaScheme.winningCondition :=
  rfl

attribute [local irreducible] sphincsRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The read programs with their answers -/

section values

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The model's oracles by read ports, logging the answers**: GameReads' `romReadImpl` with each
hashed input logged beside the pair read at its regrouped cell. -/
noncomputable def romReadImplV (B : QReg) :
    QueryImpl RomOracles (StateT (List (Qrom.HashDomain × PairOut))
      (QComp (hwReadSpec PairOut Qrom.HashDomain M) B B))
  | .inl n => liftM (QComp.coinImpl (hwReadSpec PairOut Qrom.HashDomain M) B n)
  | .inr x => fun log ↦ (readCall (.readH (hmsgRoute (x, false)).1 keepMem) B).bind fun r ↦
      QuantumComp₂.pure (pairPart (hmsgRoute (x, false)).2 (r.1.getD 0), log ++ [(x, r.1.getD 0)])

/-- **A computation as a program of read ports, with the answers**: its result and the hashed
inputs with the pairs read. -/
noncomputable def readsProgramV (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    QComp (hwReadSpec PairOut Qrom.HashDomain M) B B (α × List (Qrom.HashDomain × PairOut)) :=
  (simulateQ (romReadImplV M B) x).run []

variable {M}

omit [Fintype M] [DecidableEq M] in
/-- The logging reads forget their answers to `romReadImpl`'s. -/
theorem run_simulateQ_romReadImpl (B : QReg) {α : Type} (x : OracleComp RomOracles α)
    (log : List (Qrom.HashDomain × PairOut)) :
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
    · change ((readCall (.readH (hmsgRoute (x, false)).1 keepMem) B).bind fun r ↦
          QuantumComp₂.pure (pairPart (hmsgRoute (x, false)).2 (r.1.getD 0),
            log.map Prod.fst ++ [x])) >>= _ =
        _ <$> (((readCall (.readH (hmsgRoute (x, false)).1 keepMem) B).bind fun r ↦
          QuantumComp₂.pure (pairPart (hmsgRoute (x, false)).2 (r.1.getD 0),
            log ++ [(x, r.1.getD 0)])) >>= _)
      simp only [QuantumComp₂.bind_eq, QuantumComp₂.map_eq, QuantumComp₂.bind_assoc,
        QuantumComp₂.pure_bind, QuantumComp₂.map_eq_bind_pure]
      refine congrArg _ (funext fun r ↦ ?_)
      have h := ih (pairPart (hmsgRoute (x, false)).2 (r.1.getD 0)) (log ++ [(x, r.1.getD 0)])
      rw [List.map_append, List.map_singleton] at h
      rw [h, QuantumComp₂.map_eq, QuantumComp₂.map_eq_bind_pure]

omit [Fintype M] [DecidableEq M] in
/-- **`readsProgram` is the logging reads with the answers forgotten.** -/
theorem readsProgram_eq_map (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    readsProgram M B x = (fun p ↦ (p.1, p.2.map Prod.fst)) <$> readsProgramV M B x :=
  run_simulateQ_romReadImpl B x []

end values

/-- An outcome of the logging reads: the verifier's result and the hashed inputs with pairs. -/
abbrev ReadsOut : Type :=
  Bool × List (Qrom.HashDomain × PairOut)

/-- **The verification's logging reads** of a prefix outcome `pre`, realized at `θ`. Inline: the
kernel recurses checking against such a program wrapped in a definition. -/
local macro "wReadsQ " θ:term:max ppSpace pre:term:max : term =>
  `((realizeT $θ (readLiftQ goodQ (readsProgramV SelMem (QReg.of Unit)
    (sphincsRom.verify (Prod.fst $pre) (Prod.fst (Prod.snd $pre))))) :
      QComp (recHwSpec PairOut Qrom.HashDomain TPos SelMem) (QReg.of Unit) (QReg.of Unit)
        ReadsOut))

/-- The signing transcript of the game (a notation: an `abbrev` here made the kernel recurse
comparing it with the prefix's result type). -/
local notation "SLogQ" => SufCma.SignLog Message (Option Signature)

/-! ## The game's shape -/

section shape

/-- The winning condition of a prefix outcome. -/
noncomputable def winCondQ (pre : PublicKey × (Forgery × SLogQ)) : Bool :=
  sphincsRom.winningCondition pre.2.2 pre.2.1

theorem realizeT_verifyT (θ : TVals) (pre : PublicKey × (Forgery × SLogQ)) :
    realizeT θ (verifyT SelMem pre) =
      QuantumComp₂.bind (wReadsQ θ pre) fun (a : ReadsOut) ↦
        QuantumComp₂.pure (winCondQ pre && a.1) := by
  rw [verifyT, readsThenT_eq, readsProgram_eq_map, QuantumComp₂.map_eq]
  simp only [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rw [readLift_bind₂, QuantumComp₂.bind_assoc, realizeT_bind₂]
  rfl

/-- The game is its prefix and the realized verification. -/
theorem gameQ_eq_verify (pol : DigestPolicy) (A : SAdversary) (θ : TVals) :
    gameQ pol A θ = (prefixQ pol A θ).bind fun pre ↦ realizeT θ (verifyT SelMem pre) := by
  rw [gameQ, gameT_eq_prefixT_bind, realizeT_bind₂]
  rfl

/-- **The game is its prefix, the logging reads and the winning condition.** -/
theorem gameQ_eq (pol : DigestPolicy) (A : SAdversary) (θ : TVals) :
    gameQ pol A θ = (prefixQ pol A θ).bind fun pre ↦
      QuantumComp₂.bind (wReadsQ θ pre) fun (a : ReadsOut) ↦
        QuantumComp₂.pure (winCondQ pre && a.1) :=
  (gameQ_eq_verify pol A θ).trans (congrArg _ (funext fun pre ↦ realizeT_verifyT θ pre))

end shape

/-! ## The logging reads in the decompressed basis -/

section reads

/-- A hash query's input with the pair of `F` at its regrouped cell. -/
def hashReadV (F : Qrom.HashDomain → PairOut) :
    RomOracles.Domain → List (Qrom.HashDomain × PairOut)
  | .inl _ => []
  | .inr x => [(x, F (hmsgRoute (x, false)).1)]

/-- **The honest evaluation with the answers**: against `regroup hmsgRoute F`, the result and the
hashed inputs with the pairs of `F` at their cells. -/
def honestEvalV {α : Type} (F : Qrom.HashDomain → PairOut) (x : OracleComp RomOracles α) :
    α × List (Qrom.HashDomain × PairOut) :=
  (evalWithAnswerFn (romAnswers (regroup hmsgRoute F)) x,
    trace (romAnswers (regroup hmsgRoute F)) (hashReadV F) x)

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset TPos × M) (θ : TVals)

/-- A program from no register is supported anywhere. -/
theorem htS₂_of_empty {A B : QReg} {α : Type} (y : QComp (RSpecS M) A B α)
    (Q : α → Set (RRegS M)) : HTS₂ m₀ y ∅ Q := by
  intro ρ hρ a
  have h0 : ρ = 0 := by
    ext m m'
    by_contra h
    exact (hρ m m' h).1
  rw [h0, map_zero]
  exact querySupportedOn_zero _ _

/-- **The logging reads in the decompressed basis**: from registers with no empty cell whose
regrouped views only hash along `x`, they keep the register and return the honest evaluation
against the view, with the view's pairs appended to the log. -/
theorem htS₂_run_romReadImplV (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    ∀ (P : Set (RRegS M)) (log : List (Qrom.HashDomain × PairOut)), (∀ s ∈ P, NoBot s) →
      (∀ s ∈ P, QueriesSatisfy (romAnswers (regroup hmsgRoute (hvwS s))) IsHash x) →
      HTS₂ m₀ (realizeT θ (readLiftQ goodQ ((simulateQ (romReadImplV M B) x).run log))) P
        fun a ↦ {s | s ∈ P ∧ a =
          (evalWithAnswerFn (romAnswers (regroup hmsgRoute (hvwS s))) x,
            log ++ trace (romAnswers (regroup hmsgRoute (hvwS s))) (hashReadV (hvwS s)) x)} := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro P log _ _
    rw [simulateQ_pure, StateT.run_pure]
    exact htS₂_pure (a, log) fun s hs ↦
      ⟨hs, by rw [evalWithAnswerFn_pure, trace_pure, List.append_nil]⟩
  | query_bind t k ih =>
    intro P log hP hx
    rcases P.eq_empty_or_nonempty with hP0 | ⟨s₀, hs₀⟩
    · subst hP0
      exact htS₂_of_empty m₀ _ _
    have hq : ∀ s ∈ P, QueriesSatisfy (romAnswers (regroup hmsgRoute (hvwS s))) IsHash
        (k (romAnswers (regroup hmsgRoute (hvwS s)) t)) := fun s hs q hq ↦ hx s hs q (by
      rw [queries, trace_query_bind]
      exact List.mem_append_right _ hq)
    obtain ⟨c, rfl⟩ : IsHash t := hx s₀ hs₀ t (by
      rw [queries, trace_query_bind]
      exact List.mem_append_left _ (List.mem_singleton_self t))
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change HTS₂ m₀ (realizeT θ (readLiftQ goodQ (QuantumComp₂.bind
      ((readCall (.readH (hmsgRoute (c, false)).1 keepMem) B).bind fun r ↦
        QuantumComp₂.pure (pairPart (hmsgRoute (c, false)).2 (r.1.getD 0),
          log ++ [(c, r.1.getD 0)]))
      fun p ↦ (simulateQ (romReadImplV M B) (k p.1)).run p.2))) P _
    rw [readLift_bind₂, realizeT_bind₂]
    have h1 := ((detS_readH (m₀ := m₀) (θ := θ) (hmsgRoute (c, false)).1 keepMem B).bind
      fun r ↦ detS_pure (m₀ := m₀) (θ := θ) (B := B)
        (pairPart (hmsgRoute (c, false)).2 (r.1.getD 0), log ++ [(c, r.1.getD 0)])) P hP
    refine HTS₂.bind (h1.mono subset_rfl fun p ↦ ?_) fun p ↦
      ((ih p.1 {s | s ∈ P ∧ p = (regroup hmsgRoute (hvwS s) c,
          log ++ [(c, hvwS s (hmsgRoute (c, false)).1)])} p.2
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
theorem htS₂_readsProgramV (B : QReg) {α : Type} (x : OracleComp RomOracles α)
    (hx : ∀ H, QueriesSatisfy (romAnswers H) IsHash x) (P : Set (RRegS M))
    (hP : ∀ s ∈ P, NoBot s) :
    HTS₂ m₀ (realizeT θ (readLiftQ goodQ (readsProgramV M B x))) P
      fun a ↦ {s | s ∈ P ∧ a = honestEvalV (hvwS s) x} :=
  (htS₂_run_romReadImplV m₀ θ B x P [] hP fun s _ ↦ hx _).mono subset_rfl fun _ ↦
    fun _ hs ↦ ⟨hs.1, hs.2.trans (by rw [List.nil_append]; rfl)⟩

end reads

/-! ## Honest evaluations and their logs -/

section honest

theorem snd_eq_of_mem_trace_hashReadV {F : Qrom.HashDomain → PairOut} {α : Type}
    {x : OracleComp RomOracles α} {p : Qrom.HashDomain × PairOut}
    (hp : p ∈ trace (romAnswers (regroup hmsgRoute F)) (hashReadV F) x) :
    p.2 = F (hmsgRoute (p.1, false)).1 := by
  rw [trace_eq_flatMap] at hp
  obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 hp
  rcases q with n | c
  · exact absurd hq List.not_mem_nil
  · rw [hashReadV, List.mem_singleton] at hq
    rw [hq]

theorem map_fst_trace_hashReadV (F : Qrom.HashDomain → PairOut) {α : Type}
    (x : OracleComp RomOracles α) :
    (trace (romAnswers (regroup hmsgRoute F)) (hashReadV F) x).map Prod.fst =
      trace (romAnswers (regroup hmsgRoute F)) hashRead x := by
  rw [trace_eq_flatMap, trace_eq_flatMap, List.map_flatMap]
  congr 1
  funext q
  rcases q <;> rfl

/-- **The logged reads number at most the hash calls of a path bound.** -/
theorem length_trace_hashReadV_le (F : Qrom.HashDomain → PairOut) {α : Type}
    {x : OracleComp RomOracles α} {n : ℕ} (h : Common.QueryCostAtMost x hashCallCost n) :
    (trace (romAnswers (regroup hmsgRoute F)) (hashReadV F) x).length ≤ n := by
  rw [trace_eq_flatMap, List.length_flatMap]
  refine le_of_eq_of_le (congrArg List.sum (List.map_congr_left fun q _ ↦ ?_))
    (Quantum.Xmss.sum_map_queries_le (romAnswers (regroup hmsgRoute F)) hashCallCost h)
  rcases q <;> rfl

/-- **The honest evaluation depends on `F` only through the cells it reads**: a function holding
the logged pair at the cell of every logged input gives the same result and inputs. -/
theorem honestEval_eq_of_agree {F F' : Qrom.HashDomain → PairOut} {α : Type}
    (x : OracleComp RomOracles α)
    (h : ∀ p ∈ trace (romAnswers (regroup hmsgRoute F)) (hashReadV F) x,
      F' (hmsgRoute (p.1, false)).1 = p.2) :
    honestEval (regroup hmsgRoute F') x =
      (evalWithAnswerFn (romAnswers (regroup hmsgRoute F)) x,
        trace (romAnswers (regroup hmsgRoute F)) hashRead x) := by
  induction x using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    have hk := ih (romAnswers (regroup hmsgRoute F) t) fun p hp ↦ h p (by
      rw [trace_query_bind]
      exact List.mem_append_right _ hp)
    have ht : romAnswers (regroup hmsgRoute F') t = romAnswers (regroup hmsgRoute F) t := by
      rcases t with n | c
      · rfl
      · have hc := h (c, F (hmsgRoute (c, false)).1) (by
          rw [trace_query_bind]
          exact List.mem_append_left _ (List.mem_singleton_self _))
        change pairPart (hmsgRoute (c, false)).2 (F' (hmsgRoute (c, false)).1) =
          pairPart (hmsgRoute (c, false)).2 (F (hmsgRoute (c, false)).1)
        rw [hc]
    obtain ⟨h1, h2⟩ := Prod.mk.inj hk
    simp only [honestEval] at h1 h2 ⊢
    rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_liftM_query, trace_query_bind, trace_query_bind, ht, h1, h2]

end honest

/-! ## The winning runs -/

section decomp

/-- A run of the game: a prefix outcome and a run of the logging reads. -/
abbrev RunQ : Type :=
  (PublicKey × (Forgery × SLogQ)) × (Bool × List (Qrom.HashDomain × PairOut))

/-- **The log of a run of the reads**, as a log of `h`-reads at the regrouped cells (empty beyond
`verifyCalls` reads, which no honest verification makes). -/
def wLogQ (l : List (Qrom.HashDomain × PairOut)) : QueryLog (spongeOSpec PairOut Qrom.HashDomain) :=
  if l.length ≤ verifyCalls then l.map fun p ↦ ⟨.h (hmsgRoute (p.1, false)).1, p.2⟩ else []

theorem readCount_wLogQ_le (l : List (Qrom.HashDomain × PairOut)) :
    readCount .h (wLogQ l) ≤ verifyCalls := by
  unfold wLogQ
  split_ifs with hl
  · exact List.countP_le_length.trans (by rw [List.length_map]; exact hl)
  · exact Nat.zero_le _

theorem readCount_wLogQ_eq_zero (l : List (Qrom.HashDomain × PairOut)) {p : SpongePort}
    (hp : p ≠ .h) : readCount p (wLogQ l) = 0 := by
  unfold wLogQ readCount
  split_ifs
  · rw [List.countP_eq_zero]
    intro e he
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 he
    exact fun h ↦ hp (of_decide_eq_true h).symm
  · rfl

theorem agrees_wLogQ {l : List (Qrom.HashDomain × PairOut)} {D : DbReg PairOut Qrom.HashDomain}
    (h : ∀ p ∈ l, D.1 (hmsgRoute (p.1, false)).1 = some p.2) : DbReg.Agrees (wLogQ l) D := by
  intro e he
  unfold wLogQ at he
  split_ifs at he
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact h p hp
  · exact absurd he List.not_mem_nil

theorem of_agrees_wLogQ {l : List (Qrom.HashDomain × PairOut)} (hl : l.length ≤ verifyCalls)
    {D : DbReg PairOut Qrom.HashDomain} (h : DbReg.Agrees (wLogQ l) D) :
    ∀ p ∈ l, D.1 (hmsgRoute (p.1, false)).1 = some p.2 := fun p hp ↦
  h ⟨.h (hmsgRoute (p.1, false)).1, p.2⟩ (by
    unfold wLogQ
    split_ifs
    exact List.mem_map.2 ⟨p, hp, rfl⟩)

/-- The cover of the static stream of `θ`. -/
noncomputable def starQ (θ : TVals) : Disclosures :=
  starCover (streamOf θ)

/-- **The classical facts of a winning run** `i` on the hardwired cells and the memory `b`: the
run wins, its reads number at most `verifyCalls`, any function holding the logged pairs verifies
as it did, and some function `H` gives the transcript's signatures, the records, the known inputs
and the digests of the hardwired cells and the coverage of the signed digests at the run's table
(`win_imp_badQ`'s hypotheses). -/
def RunFacts (θ : TVals) (i : RunQ) (b : Hw PairOut Qrom.HashDomain × (Finset TPos × SelMem)) :
    Prop :=
  (winCondQ i.1 && i.2.1) = true ∧ i.2.2.length ≤ verifyCalls ∧
    (∀ F' : Qrom.HashDomain → PairOut, (∀ p ∈ i.2.2, F' (hmsgRoute (p.1, false)).1 = p.2) →
      honestEval (regroup hmsgRoute F') (sphincsRom.verify i.1.1 i.1.2.1) =
        (i.2.1, i.2.2.map Prod.fst)) ∧
    ∃ H : Qrom.HashDomain → HashOutput, i.1.1 = (tabOf θ).publicKey ∧
      (∀ r ∈ i.1.2.2, r.2 = (runTab θ b.2.1).signature H r.1) ∧
      (∀ r ∈ i.1.2.2, Records (runTab θ b.2.1) H b.2.2 r.1) ∧
      (∀ D : DbReg PairOut Qrom.HashDomain,
        HwKnown (seedOf θ) (runTab θ b.2.1) H (D, b.1, b.2.2) (i.1.2.2.map Sigma.fst)) ∧
      (∀ D : DbReg PairOut Qrom.HashDomain,
        HwDigests (seedOf θ) (runTab θ b.2.1) (D, b.1, b.2.2) (i.1.2.2.map Sigma.fst)) ∧
      ∀ r ∈ i.1.2.2, Covered (starQ θ) (pairView (runTab θ b.2.1 (digPos r.1)))

/-- **A view holding the log of a run with its facts is in the event** (`win_imp_badQ`). -/
theorem mem_badRQ_of_runFacts (θ : TVals) (i : RunQ) {s : RRegS SelMem}
    (hf : RunFacts θ i s.2) (ha : DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1)) :
    s ∈ BadRQ (pkQ θ) (honQ θ) (starQ θ) := by
  obtain ⟨hw, hl, hev, H, hpk, hlog, hM, hEx, hD, hcov⟩ := hf
  have hU : ∀ p ∈ i.2.2, unionH (projQ s) (hmsgRoute (p.1, false)).1 = some p.2 :=
    of_agrees_wLogQ hl ha
  have hE := hev (viewP (unionH (projQ s))) fun p hp ↦ by
    rw [viewP, hU p hp, Option.getD_some]
  obtain ⟨hwc, hver⟩ := (Bool.and_eq_true _ _).mp hw
  have hfresh : ¬Common.SufCma.SignerReturnedForgery id i.1.2.2 i.1.2.1.message
      i.1.2.1.signature := by
    have h := hwc
    rw [winCondQ, winningCondition_sphincsRom] at h
    exact (of_decide_eq_true h).2
  have hb := win_imp_badQ (seedOf θ) (runTab θ s.2.2.1) H (starQ θ) (projQ s) i.1.2.2 i.1.2.1
    hlog hM (hEx s.1) (hD s.1) hcov hfresh (by
      rw [runTab_publicKey θ s.2.2.1, ← hpk, hE]
      exact hver) (by
      rw [runTab_publicKey θ s.2.2.1, ← hpk, hE]
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
      rw [hU p hp]
      rfl)
  rw [runTab_publicKey θ s.2.2.1, honCell_runTab θ s.2.2.1] at hb
  exact mem_badRQ_iff.mpr hb

/-- **A winning run's support**, abstract over the prefix and the reads (the kernel recursed
checking the concrete instance directly). -/
theorem querySupportedOn_conj_runSig {α β : Type}
    (x : QComp (RSpecS SelMem) (QReg.of Unit) (QReg.of Unit) α)
    (y : α → QComp (RSpecS SelMem) (QReg.of Unit) (QReg.of Unit) β) (f : α → β → Bool)
    (P : α → Set (RRegS SelMem)) (Q : α → β → Set (RRegS SelMem))
    (hx : ∀ a, QuerySupportedOn (fun p : Unit × RRegS SelMem ↦ p.2) (P a)
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem))
        (((runtimeR m0H).run₂ .instruments x).branch a (initU m0H))))
    (hy : ∀ a, HTS₂ m0H (y a) (P a) (Q a)) (i : α × β) :
    QuerySupportedOn (fun p : Unit × RRegS SelMem ↦ p.2) {s | f i.1 i.2 = true ∧ s ∈ Q i.1 i.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem)) (runSig m0H x y f i)) := by
  by_cases h : f i.1 i.2 = true
  · rw [conj_runSig_of m0H x y f i h]
    exact (hy i.1 _ (hx i.1) i.2).mono fun s hs ↦ ⟨h, hs⟩
  · rw [runSig_of_not m0H x y f i h, map_zero]
    exact querySupportedOn_zero _ _

variable (A : SAdversary)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) signatureLimit)
  (θ : TVals)

/-- **A winning run**: the branch of the logging reads at the run after the prefix's, when the
game wins on it; `0` otherwise. -/
noncomputable def σQ (i : RunQ) : Matrix (Unit × RRegS SelMem) (Unit × RRegS SelMem) ℂ :=
  runSig m0H (prefixQ strPol A θ) (fun pre ↦ wReadsQ θ pre)
    (fun pre (a : ReadsOut) ↦ winCondQ pre && a.1) i

include hsign in
/-- **A winning run in the decompressed basis**: the prefix's facts, and the run is the honest
verification against the view, with its answers. -/
theorem dec_σQ (i : RunQ) :
    QuerySupportedOn (fun p : Unit × RRegS SelMem ↦ p.2)
      {s | (winCondQ i.1 && i.2.1) = true ∧ PreFactsS θ i.1 s ∧
        i.2 = honestEvalV (hvwS s) (sphincsRom.verify i.1.1 i.1.2.1)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem)) (σQ A θ i)) := by
  exact querySupportedOn_conj_runSig (prefixQ strPol A θ) (fun pre ↦ wReadsQ θ pre)
    (fun pre (a : ReadsOut) ↦ winCondQ pre && a.1) (fun pre ↦ {s | PreFactsS θ pre s})
    (fun pre a ↦ {s | PreFactsS θ pre s ∧
      a = honestEvalV (hvwS s) (sphincsRom.verify pre.1 pre.2.1)})
    (fun pre ↦ prefixFactsS A hsign m0H rfl θ pre)
    (fun pre ↦ htS₂_readsProgramV m0H θ (QReg.of Unit) _ (fun _ ↦ isHash_verify _ _)
      {s | PreFactsS θ pre s} (fun s hs ↦ hs.2.1)) i

include hsign in
/-- **Recorded**: in the decompressed basis, no empty cell, and the view holds the log. -/
theorem recorded_σQ (i : RunQ) :
    QuerySupportedOn (fun y : Unit × RRegS SelMem ↦ y.2)
      {s | NoBotDb s.1 ∧ DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem)) (σQ A θ i)) :=
  (dec_σQ A hsign θ i).mono fun s hs ↦ by
    obtain ⟨-, ⟨-, hnb, -⟩, he⟩ := hs
    have e2 := congrArg Prod.snd he
    refine ⟨hnb, agrees_wLogQ fun p hp ↦ ?_⟩
    rw [e2] at hp
    rw [snd_eq_of_mem_trace_hashReadV hp]
    exact hwView_eq_some_hvwS hnb _

include hsign in
/-- **The run's classical facts**, in the decompressed basis. -/
theorem facts_σQ (i : RunQ) :
    QuerySupportedOn (fun y : Unit × RRegS SelMem ↦ y.2) {s | RunFacts θ i s.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem)) (σQ A θ i)) :=
  (dec_σQ A hsign θ i).mono fun s hs ↦ by
    obtain ⟨hw, ⟨hpk, -, hlog, hrec, hEx, hD, hcov⟩, he⟩ := hs
    have e1 := congrArg Prod.fst he
    have e2 := congrArg Prod.snd he
    refine ⟨hw, ?_, fun F' hF' ↦ ?_, hHS s, hpk, hlog, hrec, fun _ ↦ hEx, fun _ ↦ hD, hcov⟩
    · rw [e2]
      exact length_trace_hashReadV_le _ (verify_hashCalls _ _)
    · simp only [honestEvalV] at e1 e2
      rw [e1, e2, map_fst_trace_hashReadV]
      exact honestEval_eq_of_agree _ fun p hp ↦ hF' p (e2 ▸ hp)

include hsign in
/-- **In the event**: in the compressed basis, a view holding the log is in `BadRQ`. -/
theorem bad_σQ (i : RunQ) :
    QuerySupportedOn (fun y : Unit × RRegS SelMem ↦ y.2)
      {s | DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1) →
        s ∈ BadRQ (pkQ θ) (honQ θ) (starQ θ)} (σQ A θ i) :=
  (querySupportedOn_of_conj_compressReg (P := RunFacts θ i) (facts_σQ A hsign θ i)).mono
    fun _ hf ha ↦ mem_badRQ_of_runFacts θ i hf ha

/-- The weight of the game's winning branch, run by run. -/
theorem ofReal_trace_conj_gameQ
    (K : Matrix (Unit × RRegS SelMem) (Unit × RRegS SelMem) ℂ) :
    ENNReal.ofReal (MatrixMap.conj K (((runtimeR m0H).run₂ .instruments
      (gameQ strPol A θ)).branch true (initU m0H))).trace.re =
      ∑' p, ENNReal.ofReal (MatrixMap.conj K (σQ A θ p)).trace.re := by
  rw [gameQ_eq]
  exact ofReal_trace_conj_runSig m0H (prefixQ strPol A θ) (fun pre ↦ wReadsQ θ pre)
    (fun pre (a : ReadsOut) ↦ winCondQ pre && a.1) K

open Classical in
/-- **The decomposition of runtime 2's winning runs along the verification's reads.** -/
noncomputable def winDecompQ :
    WinDecomp m0H (gameQ strPol A θ) (gameQ strPol A θ) (BadRQ (pkQ θ) (honQ θ) (starQ θ))
      verifyCalls 0 0 where
  ι := RunQ
  σ := σQ A θ
  log i := wLogQ i.2.2
  psd i := runSig_posSemidef m0H _ _ _ i
  countH i := readCount_wLogQ_le _
  countK i := (readCount_wLogQ_eq_zero _ (by decide)).le
  countK' i := (readCount_wLogQ_eq_zero _ (by decide)).le
  recorded i := recorded_σQ A hsign θ i
  bad i := bad_σQ A hsign θ i
  win := by
    rw [evalDistMap_winBit]
    have h := ofReal_trace_conj_gameQ A θ 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.le
  event := (ofReal_trace_conj_gameQ A θ _).symm.le.trans
    (trace_conj_branch_true_le_eventWeight m0H (gameQ strPol A θ) _)
  mass := by
    have h := ofReal_trace_conj_gameQ A θ 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.symm.le.trans (ofReal_trace_branch_le_one m0H (gameQ strPol A θ) true)

/-- The read error of the verification's reads: `2 · verifyCalls / |Y|`. -/
noncomputable def readErrQ : ℝ≥0∞ :=
  ENNReal.ofReal (readError PairOut Qrom.HashDomain verifyCalls 0 0)

include hsign in
open Classical in
/-- **Runtime 2's win is at most the event at the end of the game and the read error.** -/
theorem p2Q_le_eventWeight :
    p2Q strPol A θ ≤ (runtimeR m0Q).eventWeight .instruments
      (hwProjector (BadRQ (pkQ θ) (honQ θ) (starQ θ))) (gameQ strPol A θ) initQ + readErrQ :=
  win_le_of_winDecomp (winDecompQ A hsign θ)

end decomp

/-! ## The verification's calls -/

section verifyCalls

variable {M : Type} [Fintype M] [DecidableEq M]

open scoped Classical in
variable (M) in
/-- The charge of the read program's calls other than the reads that keep the memory. -/
noncomputable def nonKeepRdQ : (hwReadSpec PairOut Qrom.HashDomain M).Port → ℕ
  | .inl _ => 1
  | .inr c => if c.KeepsMem then 0 else 1

omit [Fintype M] [DecidableEq M] in
/-- A lifted read that keeps the memory keeps the memory with the label. -/
theorem keepUpd_liftReadQ (c : HwRead PairOut Qrom.HashDomain M) (hc : c.KeepsMem) :
    KeepUpd (liftRead (S := TPos) c) := by
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
theorem chg_readCall_keepQ (c : HwRead PairOut Qrom.HashDomain M) (hc : c.KeepsMem) (B : QReg) :
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
    show IFreeM.IsChargeBound ((StateT.lift (QComp.coinImpl
      (hwReadSpec PairOut Qrom.HashDomain M) B n) : StateT (List Qrom.HashDomain)
        (QComp (hwReadSpec PairOut Qrom.HashDomain M) B B) _).run s) _ _
    rw [StateT.run_lift]
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0)
      fun a' ↦ sChg_pure (σ := List Qrom.HashDomain) (B := B) (nonKeepRdQ M) a' 0 s
  · intro log
    show IFreeM.IsChargeBound ((readCall (.readH (hmsgRoute (x, false)).1 keepMem) B).bind
      fun r ↦ QuantumComp₂.pure (pairPart (hmsgRoute (x, false)).2 (r.1.getD 0), log ++ [x]))
        _ _
    exact FreeM₂.isChargeBound_bind (n₂ := 0)
      (chg_readCall_keepQ (.readH (hmsgRoute (x, false)).1 keepMem) rfl B) fun _ ↦ trivial

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
theorem chg_verifyT_nonKeepQ (θ : TVals) (x : PublicKey × (Forgery × SLogQ)) :
    IFreeM.IsChargeBound (realizeT θ (verifyT M x))
      (portCharge (nonKeep PairOut Qrom.HashDomain TPos M)) 0 := by
  rw [verifyT, readsThenT_eq]
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ ↦ trivial
  refine IFreeM.IsChargeBound.mapLens (readLens goodQ) ?_
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    (chg_map _ Prod.fst (sChg_simulateQ_romReadImpl_keep (M := M) (QReg.of Unit) _ []))
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show nonKeep PairOut Qrom.HashDomain TPos M (.inl (.inl (.inr (liftRead c)))) ≤
      nonKeepRdQ M (.inr c)
    by_cases hc : c.KeepsMem
    · have h0 : nonKeep PairOut Qrom.HashDomain TPos M (.inl (.inl (.inr (liftRead c)))) = 0 := by
        simp only [nonKeep, keepUpd_liftReadQ c hc, ↓reduceIte]
      omega
    · have h1 : nonKeepRdQ M (.inr c) = 1 := by simp only [nonKeepRdQ, hc, ↓reduceIte]
      have h2 := nonKeep_le_one (X := PairOut) (Z := Qrom.HashDomain) (S := TPos) (M := M)
        (.inl (.inl (.inr (liftRead c))))
      omega

omit [Fintype M] [DecidableEq M] in
/-- **The verification's calls**: at most `verifyCalls`. -/
theorem chg_verifyT_oneQ (θ : TVals) (x : PublicKey × (Forgery × SLogQ)) :
    IFreeM.IsChargeBound (realizeT θ (verifyT M x)) (portCharge fun _ ↦ 1) verifyCalls := by
  have he : rChargeQ M 1 1 1 1 = fun _ ↦ 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  have h := isChargeBound_realizeT (M := M) 1 1 1 1 θ (chg_verifyT (M := M) 1 1 1 1 x)
  rw [he] at h
  simpa using h

end verifyCalls

/-! ## The event bound over the game -/

section event

/-- **The verification term**: `verifyCalls · √(2^-128 + price S)`, its reads graded like
adversary calls. -/
noncomputable def verTermQ (S : Disclosures) : ℝ≥0∞ :=
  (verifyCalls : ℝ≥0∞) * epsQ S ^ (2⁻¹ : ℝ)

/-- **The verification's linear term**: `verifyCalls (ε + 2/|Y| + 2/|D|)`. -/
noncomputable def verLinQ (S : Disclosures) : ℝ≥0∞ :=
  (verifyCalls : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S)

/-- The initial state has empty databases. -/
theorem querySupportedOn_dbGrade_initQ :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := PairOut) (Z := Qrom.HashDomain)
      m0Q).D ↦ dbGrade m.2.1) (Set.Iic 0) initQ := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty PairOut Qrom.HashDomain, m0Q) : RegQ)).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact absurd rfl h

variable (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) signatureLimit)
include hhash hsign

/-- **The prefix's calls**: at most `q + clsCapQ`. -/
theorem calls_prefixQ (θ : TVals) :
    IFreeM.IsChargeBound (prefixQ strPol A θ) (portCharge fun _ ↦ 1) (q + clsCapQ) := by
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    ((advCalls_prefixQ strPol A hhash hsign θ).add
      (clsCalls_prefixT cwUpd strPol A hhash hsign θ))
  rcases a with o | ⟨i, E, ℓ⟩
  · exact le_rfl
  · show 1 ≤ (if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 0 else 1) +
      (if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0)
    split_ifs <;> omega

/-- **The event bound over the whole game**: from Costs' bound at the end of the challenge prefix,
each of the `verifyCalls` verification reads costs `√(epsQ S)` in the square root and its linear
terms `keepE + recW` (`verLinQ`):
`ew ≤ (advTermQ q S + verTermQ S + √(twPQ pk hon S strPol A θ + verLinQ S))²`. -/
theorem ewGameQ_le (pk : PublicKey) (hon : HonestCells) (S : Disclosures) (θ : TVals) :
    (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S)) (gameQ strPol A θ)
        initQ ≤
      (advTermQ q S + verTermQ S + (twPQ pk hon S strPol A θ + verLinQ S) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hpreT := ewPrefixQ_le pk hon S strPol A θ (advCalls_prefixQ strPol A hhash hsign θ)
    (clsCalls_prefixT cwUpd strPol A hhash hsign θ)
  have hρa := fun a ↦ ((runtimeR m0Q).run₂ .instruments
    (prefixQ strPol A θ)).posSemidef_branch_apply a initQ_posSemidef
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step
    (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q) (fun s ↦ dbGrade s.1) (fun _ ↦ 1)
    (querySupportedOn_runtimeR_step' (X := PairOut) (Z := Qrom.HashDomain) m0Q) .instruments
    (calls_prefixQ A hhash hsign θ) querySupportedOn_dbGrade_initQ ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0Q .instruments
    (prefixQ strPol A θ) (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le (BadRQ pk hon S)
    (fun W m ↦ upClosed_slice_badRQ W m) m0Q (N := q + clsCapQ + verifyCalls) (ε := epsQ S)
    (epsQ_ne_top S) (fun W m ↦ freshBound_slice_badRQ W m _) .instruments
    (realizeT θ (verifyT SelMem a)) (chg_verifyT_oneQ θ a) (chg_verifyT_nonKeepQ θ a)
    (t := 0 + (q + clsCapQ)) (by omega) (hρa a) (hga a) (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments
      (prefixQ strPol A θ)).branch a initQ).trace.re ≤ 1 :=
    (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).isCPTNIFamily.tsum_ofReal_trace_re_le
      initQ_posSemidef).trans ofReal_trace_initQ_le_one
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0Q) .instruments
    (hwProjector (BadRQ pk hon S)) (prefixQ strPol A θ) initQ
  have hm : ∑' j, (∑' a, (if j < verifyCalls then epsQ S else 0) *
      ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).branch a
        initQ).trace.re) ^ (2⁻¹ : ℝ) ≤ verTermQ S := by
    calc _ ≤ ∑' j, ((if j < verifyCalls then epsQ S else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTermQ S := by
          unfold verTermQ
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector (BadRQ pk hon S))
      (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).branch a initQ) +
      (verifyCalls : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S) *
        ENNReal.ofReal (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).branch a
          initQ).trace.re) ≤
      (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
        (prefixQ strPol A θ) initQ + verLinQ S := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc (verifyCalls : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S) * _
        ≤ (verifyCalls : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain (epsQ S) * 1 := by
          gcongr
      _ = verLinQ S := mul_one _
  have hpre' : ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (prefixQ strPol A θ) initQ + verLinQ S) ^ (2⁻¹ : ℝ) ≤
      advTermQ q S + (twPQ pk hon S strPol A θ + verLinQ S) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := advTermQ q S ^ 2) (δ := 0) (C := verLinQ S)
      (b := twPQ pk hon S strPol A θ) (a := (runtimeR m0Q).eventWeight .instruments
        (hwProjector (BadRQ pk hon S)) (prefixQ strPol A θ) initQ) (by
          rw [Quantum.Qrom.Xmss.sq_rpow_inv_two_eq, add_zero]
          exact hpreT.trans_eq (by rw [add_comm (advTermQ q S)]))
    rwa [Quantum.Qrom.Xmss.sq_rpow_inv_two_eq, zero_add] at h
  have hew : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (gameQ strPol A θ) initQ = ∑' a, (runtimeR m0Q).eventWeight .instruments
        (hwProjector (BadRQ pk hon S)) (realizeT θ (verifyT SelMem a))
        (((runtimeR m0Q).run₂ .instruments (prefixQ strPol A θ)).branch a initQ) := by
    rw [gameQ_eq_verify]
    exact eventWeight_bind₂ (runtimeR m0Q) .instruments (hwProjector (BadRQ pk hon S))
      (prefixQ strPol A θ) _ initQ_posSemidef
  have hfin : (runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
      (gameQ strPol A θ) initQ ^ (2⁻¹ : ℝ) ≤
      advTermQ q S + verTermQ S + (twPQ pk hon S strPol A θ + verLinQ S) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0Q).eventWeight .instruments (hwProjector (BadRQ pk hon S))
          (prefixQ strPol A θ) initQ + verLinQ S) ^ (2⁻¹ : ℝ) + verTermQ S :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ advTermQ q S + (twPQ pk hon S strPol A θ + verLinQ S) ^ (2⁻¹ : ℝ) + verTermQ S :=
          add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

/-- **Runtime 2's win at `θ`**:
`p2Q ≤ (advTermQ q S★ + verTermQ S★ + √(twPQ + verLinQ S★))² + readErrQ`, `S★ = starQ θ`. -/
theorem p2Q_le (θ : TVals) :
    p2Q strPol A θ ≤ (advTermQ q (starQ θ) + verTermQ (starQ θ) +
      (twPQ (pkQ θ) (honQ θ) (starQ θ) strPol A θ + verLinQ (starQ θ)) ^ (2⁻¹ : ℝ)) ^ 2 +
        readErrQ :=
  (p2Q_le_eventWeight A hsign θ).trans
    (add_le_add (ewGameQ_le A hhash hsign (pkQ θ) (honQ θ) (starQ θ) θ) le_rfl)

end event

/-! ## Averaged over the hidden values -/

section average

/-- **The mean fresh fraction**: `2^-128 + rhoCov · 2^-128`. -/
noncomputable def epsBarQ : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (rhoCov / 2 ^ 128)

/-- **The mean fresh fraction over the hidden values** (the stream of `θ` is uniform). -/
theorem uavg_epsQ_le : uavg (fun θ : TVals ↦ epsQ (starQ θ)) ≤ epsBarQ := by
  unfold epsQ starQ epsBarQ
  rw [uavg_add, uavg_const]
  refine add_le_add le_rfl ?_
  exact (uavg_streamOf fun d ↦ ENNReal.ofReal (price (starCover d))).trans_le
    uavg_price_starCover_le

/-- **The averaged adversary term**: `√(6 q² epsBarQ)`. -/
noncomputable def advBarQ (q : ℕ) : ℝ≥0∞ :=
  ((q : ℝ≥0∞) ^ 2 * (6 * epsBarQ)) ^ (2⁻¹ : ℝ)

/-- **The averaged verification term**: `√(verifyCalls² epsBarQ)`. -/
noncomputable def verBarQ : ℝ≥0∞ :=
  ((verifyCalls : ℝ≥0∞) ^ 2 * epsBarQ) ^ (2⁻¹ : ℝ)

/-- **The averaged verification's linear term**: `verifyCalls (epsBarQ + 2/|Y| + 2/|D|)`. -/
noncomputable def verLinBarQ : ℝ≥0∞ :=
  (verifyCalls : ℝ≥0∞) * keepCost PairOut Qrom.HashDomain epsBarQ

/-- `n · √x = √(n² x)`. -/
theorem natCast_mul_rpow_inv_two (n : ℕ) (x : ℝ≥0∞) :
    (n : ℝ≥0∞) * x ^ (2⁻¹ : ℝ) = ((n : ℝ≥0∞) ^ 2 * x) ^ (2⁻¹ : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), Quantum.Qrom.Xmss.sq_rpow_inv_two_eq]

theorem advTermQ_eq (q : ℕ) (S : Disclosures) :
    advTermQ q S = ((q : ℝ≥0∞) ^ 2 * (6 * epsQ S)) ^ (2⁻¹ : ℝ) := by
  unfold advTermQ
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, natCast_mul_rpow_inv_two]

theorem verTermQ_eq (S : Disclosures) :
    verTermQ S = ((verifyCalls : ℝ≥0∞) ^ 2 * epsQ S) ^ (2⁻¹ : ℝ) :=
  natCast_mul_rpow_inv_two _ _

/-- **Minkowski for three square roots**, averaged. -/
theorem uavg_sq_rpow_add3_le {Θ : Type*} [Fintype Θ] [Nonempty Θ] (f g h : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ (f θ ^ (2⁻¹ : ℝ) + g θ ^ (2⁻¹ : ℝ) + h θ ^ (2⁻¹ : ℝ)) ^ 2) ≤
      (uavg f ^ (2⁻¹ : ℝ) + uavg g ^ (2⁻¹ : ℝ) + uavg h ^ (2⁻¹ : ℝ)) ^ 2 := by
  have e : ∀ θ, f θ ^ (2⁻¹ : ℝ) + g θ ^ (2⁻¹ : ℝ) =
      ((f θ ^ (2⁻¹ : ℝ) + g θ ^ (2⁻¹ : ℝ)) ^ 2) ^ (2⁻¹ : ℝ) := fun θ ↦
    (Quantum.Qrom.Xmss.sq_rpow_inv_two_eq _).symm
  have h1 := uavg_sq_rpow_add_le (fun θ ↦ (f θ ^ (2⁻¹ : ℝ) + g θ ^ (2⁻¹ : ℝ)) ^ 2) h
  simp only [← e] at h1
  refine h1.trans (pow_le_pow_left₀ zero_le (add_le_add ?_ le_rfl) 2)
  calc uavg (fun θ ↦ (f θ ^ (2⁻¹ : ℝ) + g θ ^ (2⁻¹ : ℝ)) ^ 2) ^ (2⁻¹ : ℝ)
      ≤ ((uavg f ^ (2⁻¹ : ℝ) + uavg g ^ (2⁻¹ : ℝ)) ^ 2) ^ (2⁻¹ : ℝ) :=
        ENNReal.rpow_le_rpow (uavg_sq_rpow_add_le f g) (by norm_num)
    _ = _ := Quantum.Qrom.Xmss.sq_rpow_inv_two_eq _

variable (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) signatureLimit)
include hhash hsign

/-- **Runtime 2's win, averaged** (Minkowski over the hidden values): with the prefix's averaged
classical cost at most `T`, `E p2Q ≤ (advBarQ q + verBarQ + √(T + verLinBarQ))² + readErrQ`. -/
theorem uavg_p2Q_le {T : ℝ≥0∞}
    (hcost : uavg (fun θ : TVals ↦ twPQ (pkQ θ) (honQ θ) (starQ θ) strPol A θ) ≤ T) :
    uavg (p2Q strPol A) ≤ (advBarQ q + verBarQ + (T + verLinBarQ) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ := by
  refine (uavg_mono (p2Q_le A hhash hsign)).trans ?_
  rw [uavg_add, uavg_const]
  refine add_le_add ?_ le_rfl
  simp only [advTermQ_eq, verTermQ_eq]
  refine (uavg_sq_rpow_add3_le _ _ _).trans (pow_le_pow_left₀ zero_le
    (add_le_add (add_le_add ?_ ?_) ?_) 2)
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_const_mul, uavg_const_mul]
    gcongr
    exact uavg_epsQ_le
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_const_mul]
    gcongr
    exact uavg_epsQ_le
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_add]
    refine add_le_add hcost ?_
    unfold verLinQ verLinBarQ keepCost
    rw [uavg_const_mul, uavg_add, uavg_add, uavg_const, uavg_const]
    gcongr
    exact uavg_epsQ_le

end average

end Quantum.Qrom.Sphincs

end
