module

public import Quantum.Qrom.Sphincs.End
public import Quantum.Qrom.Sphincs.Multi.GameTFacts
public import Quantum.Qrom.Sphincs.Multi.Hybrid
public import Quantum.Qrom.Sphincs.Multi.Costs.Bound
public import Quantum.Qrom.Sphincs.Multi.CovMax

@[expose] public section

/-!
# The end of leanSPHINCS's multi-user QROM chain: runtime 2's win

The `n`-user analog of `Quantum.Qrom.Sphincs.End`: the win of runtime 2 at the policies
`strPolN n` and the hidden values `θ` (`p2SN`, Hybrid) against the event
`BadRQN (pkQN θ) (honQN θ) (starQN θ)` (Costs' `BadRQN`, every user's static stream cover) at the
end of the game.

* **The game's shape** (`muGameQSN_eq`): the challenge prefix, the logging reads of the forged
  user's verification (single-user `readsProgramV`) and the winning condition `winCondQSN`.
* **The decompressed reads** (`htQ₂SN_readsProgramV`): from registers without empty cell, the
  logging reads keep the register and return the honest evaluation against the regrouped view.
* **The winning runs** (`winDecompQSN`): in the decompressed basis the prefix's facts hold for
  every user (`prefixFactsQSN`); a win has distinct `PK.seed`s (`pdOK`), so in the compressed
  basis a view holding the log is in the event (`win_imp_badQP` at the forged user,
  `mem_badQN_of_badQP`). EndReads' `win_le_of_winDecomp`: the win is at most the event weight at
  the end of the game plus `readErrQ`.
* **The event bound** (`ewMuGameQSN_le`): from a bound `(c + √tw)²` at the end of the prefix, the
  verification's reads graded like adversary calls at the fresh fraction `epsQN S`.
* **Per hidden values** (`p2SN_le`): `0` off `GoodSN`; on `GoodSN` the decomposition and Costs'
  `ewPrefixQSN_le`.
* **Averaged** (`uavg_p2SN_le`): Minkowski over the hidden values with the mean fresh fraction
  `epsBarN n = 2^-128 + rhoMaxQ n` over the users' uniform streams (`uavg_epsQN_le`).
-/

open Matrix IPFunctor OracleSpec
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.SufCma (QueriesSatisfy queries trace trace_query_bind trace_pure)
open Quantum.Qrom.Xmss (romAnswers honestEval IsHash)
open Quantum.Sphincs (Disclosures Covered price)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT readLiftQ liftRead NoBot
  NoBotDb initU initU_posSemidef runSig runSig_of_not runSig_posSemidef conj_runSig_of
  ofReal_trace_conj_runSig trace_conj_branch_true_le_eventWeight ofReal_trace_branch_le_one
  evalDistMap_winBit querySupportedOn_of_conj_compressReg WinDecomp win_le_of_winDecomp
  readLift_bind₂ realizeT_bind₂ extCls noBot_runtimeR querySupportedOn_runtimeR_step'
  rpow_inv_two_eventWeight_keepReads_le keepCost nonKeep nonKeep_le_one chg_map tmplLens
  readLens isChargeBound_mono_charge eventWeight_bind₂ eventWeight_eq_tsum_run₂
  tsum_rpow_inv_two_ite rpow_inv_two_add_le_of_le_sq uavg_const uavg_sq_rpow_add_le)
open Quantum.Qrom.SufCma.Multi (cmdCharge hashCharge signCharge signChargeAt)

attribute [local irreducible] sphincsRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

/-- **The forged user's verification's logging reads** of a prefix outcome, realized at `θ`.
Inline: the kernel recurses checking against such a program wrapped in a definition. -/
local macro "wReadsQSN " θ:term:max ppSpace pre:term:max : term =>
  `((realizeT $θ (readLiftQ goodQN (readsProgramV (SelMemN _) (QReg.of Unit)
    (sphincsRom.verify (Prod.fst $pre (Prod.fst (Prod.fst (Prod.snd $pre))))
      (Prod.snd (Prod.fst (Prod.snd $pre)))))) :
      QComp (recHwSpec PairOut HashDomain (TPosN _) (SelMemN _)) (QReg.of Unit) (QReg.of Unit)
        ReadsOut))

/-! ## The game's shape -/

section shape

/-- The winning condition of a prefix outcome: distinct `PK.seed`s, the forged user's transcript
does not contain the forgery, and every user's transcript is valid. -/
noncomputable def winCondQSN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (pre : (Fin n → PublicKey) × MuRunS n) : Bool :=
  pdOK pre.1 && sphincsRom.winningCondition (pre.2.2.user pre.2.1.1) pre.2.1.2 &&
    pre.2.2.allValid valid

theorem realizeT_verifyTN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (θ : TValsN n) (pre : (Fin n → PublicKey) × MuRunS n) :
    realizeT θ (verifyTN (SelMemN n) valid pre) =
      QuantumComp₂.bind (wReadsQSN θ pre) fun (a : ReadsOut) ↦
        QuantumComp₂.pure (winCondQSN valid pre && a.1) := by
  rw [verifyTN, readsThenTN_eq, readsProgram_eq_map, QuantumComp₂.map_eq]
  simp only [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rw [readLift_bind₂, QuantumComp₂.bind_assoc, realizeT_bind₂]
  rfl

/-- The game is its prefix and the realized verification. -/
theorem muGameQSN_eq_verify (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (θ : TValsN n) :
    muGameQSN pols valid A θ = (prefixQSN pols A θ).bind fun pre ↦
      realizeT θ (verifyTN (SelMemN n) valid pre) := by
  rw [muGameQSN, muGameT_eq_prefixTN_bind, realizeT_bind₂]
  rfl

/-- **The game is its prefix, the logging reads and the winning condition.** -/
theorem muGameQSN_eq (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (θ : TValsN n) :
    muGameQSN pols valid A θ = (prefixQSN pols A θ).bind fun pre ↦
      QuantumComp₂.bind (wReadsQSN θ pre) fun (a : ReadsOut) ↦
        QuantumComp₂.pure (winCondQSN valid pre && a.1) :=
  (muGameQSN_eq_verify pols valid A θ).trans
    (congrArg _ (funext fun pre ↦ realizeT_verifyTN valid θ pre))

end shape

/-! ## The logging reads in the decompressed basis -/

section reads

variable {M : Type} [Fintype M] [DecidableEq M] (m₀ : Finset (TPosN n) × M) (θ : TValsN n)

/-- A program from no register is supported anywhere. -/
theorem htQ₂SN_of_empty {A B : QReg} {α : Type} (y : QComp (RSpecSN n M) A B α)
    (Q : α → Set (RRegSN n M)) : HTQ₂SN m₀ y ∅ Q := by
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
theorem htQ₂SN_run_romReadImplV (B : QReg) {α : Type} (x : OracleComp RomOracles α) :
    ∀ (P : Set (RRegSN n M)) (log : List (HashDomain × PairOut)), (∀ s ∈ P, NoBot s) →
      (∀ s ∈ P, QueriesSatisfy (romAnswers (regroup hmsgRoute (hvwSN s))) IsHash x) →
      HTQ₂SN m₀ (realizeT θ (readLiftQ goodQN ((simulateQ (romReadImplV M B) x).run log))) P
        fun a ↦ {s | s ∈ P ∧ a =
          (evalWithAnswerFn (romAnswers (regroup hmsgRoute (hvwSN s))) x,
            log ++ trace (romAnswers (regroup hmsgRoute (hvwSN s))) (hashReadV (hvwSN s)) x)} := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro P log _ _
    rw [simulateQ_pure, StateT.run_pure]
    exact htQ₂SN_pure (a, log) fun s hs ↦
      ⟨hs, by rw [evalWithAnswerFn_pure, trace_pure, List.append_nil]⟩
  | query_bind t k ih =>
    intro P log hP hx
    rcases P.eq_empty_or_nonempty with hP0 | ⟨s₀, hs₀⟩
    · subst hP0
      exact htQ₂SN_of_empty m₀ _ _
    have hq : ∀ s ∈ P, QueriesSatisfy (romAnswers (regroup hmsgRoute (hvwSN s))) IsHash
        (k (romAnswers (regroup hmsgRoute (hvwSN s)) t)) := fun s hs q hq ↦ hx s hs q (by
      rw [queries, trace_query_bind]
      exact List.mem_append_right _ hq)
    obtain ⟨c, rfl⟩ : IsHash t := hx s₀ hs₀ t (by
      rw [queries, trace_query_bind]
      exact List.mem_append_left _ (List.mem_singleton_self t))
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change HTQ₂SN m₀ (realizeT θ (readLiftQ goodQN (QuantumComp₂.bind
      ((readCall (.readH (hmsgRoute (c, false)).1 keepMem) B).bind fun r ↦
        QuantumComp₂.pure (pairPart (hmsgRoute (c, false)).2 (r.1.getD 0),
          log ++ [(c, r.1.getD 0)]))
      fun p ↦ (simulateQ (romReadImplV M B) (k p.1)).run p.2))) P _
    rw [readLift_bind₂, realizeT_bind₂]
    have h1 := ((detQSN_readH (m₀ := m₀) (θ := θ) (hmsgRoute (c, false)).1 keepMem B).bind
      fun r ↦ detQSN_pure (m₀ := m₀) (θ := θ) (B := B)
        (pairPart (hmsgRoute (c, false)).2 (r.1.getD 0), log ++ [(c, r.1.getD 0)])) P hP
    refine HTQ₂SN.bind (h1.mono subset_rfl fun p ↦ ?_) fun p ↦
      ((ih p.1 {s | s ∈ P ∧ p = (regroup hmsgRoute (hvwSN s) c,
          log ++ [(c, hvwSN s (hmsgRoute (c, false)).1)])} p.2
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
theorem htQ₂SN_readsProgramV (B : QReg) {α : Type} (x : OracleComp RomOracles α)
    (hx : ∀ H, QueriesSatisfy (romAnswers H) IsHash x) (P : Set (RRegSN n M))
    (hP : ∀ s ∈ P, NoBot s) :
    HTQ₂SN m₀ (realizeT θ (readLiftQ goodQN (readsProgramV M B x))) P
      fun a ↦ {s | s ∈ P ∧ a = honestEvalV (hvwSN s) x} :=
  (htQ₂SN_run_romReadImplV m₀ θ B x P [] hP fun s _ ↦ hx _).mono subset_rfl fun _ ↦
    fun _ hs ↦ ⟨hs.1, hs.2.trans (by rw [List.nil_append]; rfl)⟩

end reads

/-! ## The winning runs -/

section decomp

/-- A run of the game: a prefix outcome and a run of the logging reads. -/
abbrev RunQSN (n : ℕ) : Type :=
  ((Fin n → PublicKey) × MuRunS n) × (Bool × List (HashDomain × PairOut))

/-- **The classical facts of a winning run** `i` on the hardwired cells and the memory `b`: the
run wins, its reads number at most `verifyCalls`, any function holding the logged pairs verifies
as it did, and some function `H` gives the public keys and, per user, the transcript's
signatures, the records, the coverage of the signed digests at the run's table, and for distinct
`PK.seed`s the known inputs and digests of the hardwired cells (`win_imp_badQP`'s hypotheses). -/
def RunFactsSN (θ : TValsN n) (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (i : RunQSN n) (b : Hw PairOut HashDomain × (Finset (TPosN n) × SelMemN n)) : Prop :=
  (winCondQSN valid i.1 && i.2.1) = true ∧ i.2.2.length ≤ verifyCalls ∧
    (∀ F' : HashDomain → PairOut, (∀ p ∈ i.2.2, F' (hmsgRoute (p.1, false)).1 = p.2) →
      honestEval (regroup hmsgRoute F') (sphincsRom.verify (i.1.1 i.1.2.1.1) i.1.2.1.2) =
        (i.2.1, i.2.2.map Prod.fst)) ∧
    ∃ H : HashDomain → HashOutput, (∀ j, i.1.1 j = (tabOf (userOf θ j)).publicKey) ∧ ∀ j,
      (∀ r ∈ i.1.2.2.user j, r.2 = (runTab (userOf θ j) (labU b.2.1 j)).signature H r.1) ∧
      (∀ r ∈ i.1.2.2.user j, Records (runTab (userOf θ j) (labU b.2.1 j)) H (b.2.2 j) r.1) ∧
      (PDistinct (tabOfN θ) →
        (∀ D : DbReg PairOut HashDomain, HwKnown (seedsOf θ j) (runTab (userOf θ j)
          (labU b.2.1 j)) H (projU j (D, b.1, b.2.2)) ((i.1.2.2.user j).map Sigma.fst)) ∧
        ∀ D : DbReg PairOut HashDomain, HwDigestsP (seedsOf θ j) (runTab (userOf θ j)
          (labU b.2.1 j)) (projU j (D, b.1, b.2.2)) ((i.1.2.2.user j).map Sigma.fst)) ∧
      ∀ r ∈ i.1.2.2.user j,
        Covered (starQN θ j) (pairView (runTab (userOf θ j) (labU b.2.1 j) (digPos r.1)))

/-- **A view holding the log of a run with its facts is in the event** (`win_imp_badQP` at the
forged user; a win has distinct `PK.seed`s). -/
theorem mem_badRQN_of_runFactsSN (θ : TValsN n)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (i : RunQSN n)
    {s : RRegSN n (SelMemN n)} (hf : RunFactsSN θ valid i s.2)
    (ha : DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1)) :
    s ∈ BadRQN (pkQN θ) (honQN θ) (starQN θ) := by
  obtain ⟨hw, hl, hev, H, hpk, hj⟩ := hf
  obtain ⟨hlog, hM, hED, hcov⟩ := hj i.1.2.1.1
  have hU : ∀ p ∈ i.2.2, unionH (s.1, s.2.1, s.2.2.2) (hmsgRoute (p.1, false)).1 = some p.2 :=
    of_agrees_wLogQ hl ha
  have hE := hev (viewP (unionH (s.1, s.2.1, s.2.2.2))) fun p hp ↦ by
    rw [viewP, hU p hp, Option.getD_some]
  obtain ⟨hwc, hver⟩ := (Bool.and_eq_true _ _).mp hw
  rw [winCondQSN, Bool.and_eq_true, Bool.and_eq_true] at hwc
  obtain ⟨⟨hpd, hwin⟩, -⟩ := hwc
  have hinj : Function.Injective fun j ↦ (i.1.1 j).publicSeed :=
    @of_decide_eq_true _ (Classical.propDecidable _) hpd
  have hPD : PDistinct (tabOfN θ) := fun a b hab ↦ hinj (by
    change (i.1.1 a).publicSeed = (i.1.1 b).publicSeed
    rw [hpk, hpk, QTable.publicKey_publicSeed, QTable.publicKey_publicSeed]
    exact hab)
  have hP : Function.Injective fun j ↦ (pkQN θ j).publicSeed := fun a b hab ↦ hinj (by
    change (i.1.1 a).publicSeed = (i.1.1 b).publicSeed
    rw [hpk, hpk]
    exact hab)
  have hfresh : ¬Common.SufCma.SignerReturnedForgery id (i.1.2.2.user i.1.2.1.1)
      i.1.2.1.2.message i.1.2.1.2.signature := by
    have h := hwin
    rw [winningCondition_sphincsRom] at h
    exact (of_decide_eq_true h).2
  have hb := win_imp_badQP (seedsOf θ i.1.2.1.1)
    (runTab (userOf θ i.1.2.1.1) (labU s.2.2.1 i.1.2.1.1)) H (starQN θ i.1.2.1.1)
    (projU i.1.2.1.1 (s.1, s.2.1, s.2.2.2)) (i.1.2.2.user i.1.2.1.1) i.1.2.1.2 hlog hM
    ((hED hPD).1 s.1) ((hED hPD).2 s.1) hcov hfresh (by
      rw [unionH_projU, runTab_publicKey, ← hpk, hE]
      exact hver) (by
      rw [unionH_projU, runTab_publicKey, ← hpk, hE]
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
      rw [hU p hp]
      rfl)
  rw [runTab_publicKey, honCell_runTab] at hb
  exact mem_badRQN_iff.mpr (mem_badQN_of_badQP (pk := pkQN θ) (hon := honQN θ) (S := starQN θ)
    (i := i.1.2.1.1) hP (fun j ↦ prefixedSlot_of_honCell (seedsOf θ j) (tabOf (userOf θ j))) hb)

/-- **A winning run's support**, abstract over the prefix and the reads (the kernel recursed
checking the concrete instance directly). -/
theorem querySupportedOn_conj_runSigSN {α β : Type}
    (x : QComp (RSpecSN n (SelMemN n)) (QReg.of Unit) (QReg.of Unit) α)
    (y : α → QComp (RSpecSN n (SelMemN n)) (QReg.of Unit) (QReg.of Unit) β)
    (f : α → β → Bool) (P : α → Set (RRegSN n (SelMemN n)))
    (Q : α → β → Set (RRegSN n (SelMemN n)))
    (hx : ∀ a, QuerySupportedOn (fun p : Unit × RRegSN n (SelMemN n) ↦ p.2) (P a)
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut HashDomain (Finset (TPosN n) × SelMemN n))
        (((runtimeR m0SN).run₂ .instruments x).branch a (initU m0SN))))
    (hy : ∀ a, HTQ₂SN m0SN (y a) (P a) (Q a)) (i : α × β) :
    QuerySupportedOn (fun p : Unit × RRegSN n (SelMemN n) ↦ p.2)
      {s | f i.1 i.2 = true ∧ s ∈ Q i.1 i.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut HashDomain (Finset (TPosN n) × SelMemN n))
        (runSig m0SN x y f i)) := by
  by_cases h : f i.1 i.2 = true
  · rw [conj_runSig_of m0SN x y f i h]
    exact (hy i.1 _ (hx i.1) i.2).mono fun s hs ↦ ⟨h, hs⟩
  · rw [runSig_of_not m0SN x y f i h, map_zero]
    exact querySupportedOn_zero _ _

variable (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
  (hsignAt : ∀ pks i, IFreeM.IsChargeBound (A pks) (cmdCharge (signChargeAt i)) signatureLimit)
  (θ : TValsN n)

/-- **A winning run**: the branch of the logging reads at the run after the prefix's, when the
game wins on it; `0` otherwise. -/
noncomputable def σQSN (i : RunQSN n) :
    Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ :=
  runSig m0SN (prefixQSN (strPolN n) A θ) (fun pre ↦ wReadsQSN θ pre)
    (fun pre (a : ReadsOut) ↦ winCondQSN valid pre && a.1) i

include hsignAt in
/-- **A winning run in the decompressed basis**: the prefix's facts, and the run is the honest
verification against the view, with its answers. -/
theorem dec_σQSN (i : RunQSN n) :
    QuerySupportedOn (fun p : Unit × RRegSN n (SelMemN n) ↦ p.2)
      {s | (winCondQSN valid i.1 && i.2.1) = true ∧ PreFactsQSN θ i.1 s ∧
        i.2 = honestEvalV (hvwSN s) (sphincsRom.verify (i.1.1 i.1.2.1.1) i.1.2.1.2)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut HashDomain (Finset (TPosN n) × SelMemN n)) (σQSN valid A θ i)) :=
  querySupportedOn_conj_runSigSN (prefixQSN (strPolN n) A θ) (fun pre ↦ wReadsQSN θ pre)
    (fun pre (a : ReadsOut) ↦ winCondQSN valid pre && a.1) (fun pre ↦ {s | PreFactsQSN θ pre s})
    (fun pre a ↦ {s | PreFactsQSN θ pre s ∧
      a = honestEvalV (hvwSN s) (sphincsRom.verify (pre.1 pre.2.1.1) pre.2.1.2)})
    (fun pre ↦ prefixFactsQSN A hsignAt m0SN rfl θ pre)
    (fun pre ↦ htQ₂SN_readsProgramV m0SN θ (QReg.of Unit) _ (fun _ ↦ isHash_verify _ _)
      {s | PreFactsQSN θ pre s} (fun _ hs ↦ hs.2.1)) i

include hsignAt in
/-- **Recorded**: in the decompressed basis, no empty cell, and the view holds the log. -/
theorem recorded_σQSN (i : RunQSN n) :
    QuerySupportedOn (fun y : Unit × RRegSN n (SelMemN n) ↦ y.2)
      {s | NoBotDb s.1 ∧ DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut HashDomain (Finset (TPosN n) × SelMemN n)) (σQSN valid A θ i)) :=
  (dec_σQSN valid A hsignAt θ i).mono fun s hs ↦ by
    obtain ⟨-, ⟨-, hnb, -⟩, he⟩ := hs
    have e2 := congrArg Prod.snd he
    refine ⟨hnb, agrees_wLogQ fun p hp ↦ ?_⟩
    rw [e2] at hp
    rw [snd_eq_of_mem_trace_hashReadV hp]
    exact hwView_eq_some_hvwSN hnb _

include hsignAt in
/-- **The run's classical facts**, in the decompressed basis. -/
theorem facts_σQSN (i : RunQSN n) :
    QuerySupportedOn (fun y : Unit × RRegSN n (SelMemN n) ↦ y.2) {s | RunFactsSN θ valid i s.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut HashDomain (Finset (TPosN n) × SelMemN n)) (σQSN valid A θ i)) :=
  (dec_σQSN valid A hsignAt θ i).mono fun s hs ↦ by
    obtain ⟨hw, ⟨hpk, -, hj⟩, he⟩ := hs
    have e1 := congrArg Prod.fst he
    have e2 := congrArg Prod.snd he
    refine ⟨hw, ?_, fun F' hF' ↦ ?_, hHSN s, hpk, fun j ↦ ⟨(hj j).1, (hj j).2.1,
      fun hP ↦ ⟨fun _ ↦ ((hj j).2.2.1 hP).1, fun _ ↦ ((hj j).2.2.1 hP).2⟩, (hj j).2.2.2⟩⟩
    · rw [e2]
      exact length_trace_hashReadV_le _ (verify_hashCalls _ _)
    · simp only [honestEvalV] at e1 e2
      rw [e1, e2, map_fst_trace_hashReadV]
      exact honestEval_eq_of_agree _ fun p hp ↦ hF' p (e2 ▸ hp)

include hsignAt in
/-- **In the event**: in the compressed basis, a view holding the log is in `BadRQN`. -/
theorem bad_σQSN (i : RunQSN n) :
    QuerySupportedOn (fun y : Unit × RRegSN n (SelMemN n) ↦ y.2)
      {s | DbReg.Agrees (wLogQ i.2.2) (hwView s.2.1 s.1) →
        s ∈ BadRQN (pkQN θ) (honQN θ) (starQN θ)} (σQSN valid A θ i) :=
  (querySupportedOn_of_conj_compressReg (P := RunFactsSN θ valid i)
    (facts_σQSN valid A hsignAt θ i)).mono
    fun _ hf ha ↦ mem_badRQN_of_runFactsSN θ valid i hf ha

/-- The weight of the game's winning branch, run by run. -/
theorem ofReal_trace_conj_muGameQSN
    (K : Matrix (Unit × RRegSN n (SelMemN n)) (Unit × RRegSN n (SelMemN n)) ℂ) :
    ENNReal.ofReal (MatrixMap.conj K (((runtimeR m0SN).run₂ .instruments
      (muGameQSN (strPolN n) valid A θ)).branch true (initU m0SN))).trace.re =
      ∑' p, ENNReal.ofReal (MatrixMap.conj K (σQSN valid A θ p)).trace.re := by
  rw [muGameQSN_eq]
  exact ofReal_trace_conj_runSig m0SN (prefixQSN (strPolN n) A θ) (fun pre ↦ wReadsQSN θ pre)
    (fun pre (a : ReadsOut) ↦ winCondQSN valid pre && a.1) K

open Classical in
/-- **The decomposition of runtime 2's winning runs along the verification's reads.** -/
noncomputable def winDecompQSN :
    WinDecomp m0SN (muGameQSN (strPolN n) valid A θ) (muGameQSN (strPolN n) valid A θ)
      (BadRQN (pkQN θ) (honQN θ) (starQN θ)) verifyCalls 0 0 where
  ι := RunQSN n
  σ := σQSN valid A θ
  log i := wLogQ i.2.2
  psd i := runSig_posSemidef m0SN _ _ _ i
  countH i := readCount_wLogQ_le _
  countK i := (readCount_wLogQ_eq_zero _ (by decide)).le
  countK' i := (readCount_wLogQ_eq_zero _ (by decide)).le
  recorded i := recorded_σQSN valid A hsignAt θ i
  bad i := bad_σQSN valid A hsignAt θ i
  win := by
    rw [evalDistMap_winBit]
    have h := ofReal_trace_conj_muGameQSN valid A θ 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.le
  event := (ofReal_trace_conj_muGameQSN valid A θ _).symm.le.trans
    (trace_conj_branch_true_le_eventWeight m0SN (muGameQSN (strPolN n) valid A θ) _)
  mass := by
    have h := ofReal_trace_conj_muGameQSN valid A θ 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.symm.le.trans
      (ofReal_trace_branch_le_one m0SN (muGameQSN (strPolN n) valid A θ) true)

include hsignAt in
open Classical in
/-- **Runtime 2's win is at most the event at the end of the game and the read error.** -/
theorem p2SN_le_eventWeight :
    p2SN (strPolN n) valid A θ ≤ (runtimeR m0SN).eventWeight .instruments
      (hwProjector (BadRQN (pkQN θ) (honQN θ) (starQN θ))) (muGameQSN (strPolN n) valid A θ)
        (initU m0SN) + readErrQ :=
  win_le_of_winDecomp (winDecompQSN valid A hsignAt θ)

end decomp

/-! ## The verification's calls -/

section verifyCalls

/-- A lifted read that keeps the memory keeps the memory with the label. -/
theorem keepUpd_liftReadSN {M : Type} (c : HwRead PairOut HashDomain M) (hc : c.KeepsMem) :
    KeepUpd (liftRead (S := TPosN n) c) := by
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
theorem nonKeep_verifyTN (θ : TValsN n) (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (x : (Fin n → PublicKey) × MuRunS n) :
    IFreeM.IsChargeBound (realizeT θ (verifyTN (SelMemN n) valid x))
      (portCharge (nonKeep PairOut HashDomain (TPosN n) (SelMemN n))) 0 := by
  rw [verifyTN, readsThenTN_eq]
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) ?_ fun _ ↦ trivial
  refine IFreeM.IsChargeBound.mapLens (readLens (goodQN (n := n))) ?_
  refine isChargeBound_mono_charge (fun s a ↦ ?_)
    (chg_map _ Prod.fst (sChg_simulateQ_romReadImpl_keep (M := SelMemN n) (QReg.of Unit) _ []))
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · show nonKeep PairOut HashDomain (TPosN n) (SelMemN n) (.inl (.inl (.inr (liftRead c)))) ≤
      nonKeepRdQ (SelMemN n) (.inr c)
    by_cases hc : c.KeepsMem
    · have h0 : nonKeep PairOut HashDomain (TPosN n) (SelMemN n)
          (.inl (.inl (.inr (liftRead c)))) = 0 := by
        simp only [nonKeep, keepUpd_liftReadSN c hc, ↓reduceIte]
      omega
    · have h1 : nonKeepRdQ (SelMemN n) (.inr c) = 1 := by
        simp only [nonKeepRdQ, hc, ↓reduceIte]
      have h2 := nonKeep_le_one (X := PairOut) (Z := HashDomain) (S := TPosN n) (M := SelMemN n)
        (.inl (.inl (.inr (liftRead c))))
      omega

/-- **The verification's calls**: at most `verifyCalls`. -/
theorem calls_verifyTN (θ : TValsN n) (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (x : (Fin n → PublicKey) × MuRunS n) :
    IFreeM.IsChargeBound (realizeT θ (verifyTN (SelMemN n) valid x)) (portCharge fun _ ↦ 1)
      verifyCalls := by
  rw [verifyTN, readsThenTN_eq]
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0) ?_ fun _ ↦ trivial)
    (Nat.add_zero verifyCalls).le
  refine IFreeM.IsChargeBound.mapLens (readLens (goodQN (n := n))) ?_
  refine isChargeBound_mono_charge (fun s a ↦ ?_) (IFreeM.IsChargeBound.mono
    (chg_map _ Prod.fst (chg_readsProgram (M := SelMemN n) 1 1 (QReg.of Unit)
      (verify_hashCalls _ _))) (one_mul verifyCalls).le)
  rcases a with o | ⟨i | c, E, ℓ⟩
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

end verifyCalls

/-! ## The event bound over the game -/

section event

/-- **The verification term**: `verifyCalls · √(epsQN S)`, its reads graded like adversary
calls. -/
noncomputable def verTermQN (S : Fin n → Disclosures) : ℝ≥0∞ :=
  (verifyCalls : ℝ≥0∞) * epsQN S ^ (2⁻¹ : ℝ)

/-- **The verification's linear term**: `verifyCalls (epsQN S + 2/|Y| + 2/|D|)`. -/
noncomputable def verLinQN (S : Fin n → Disclosures) : ℝ≥0∞ :=
  (verifyCalls : ℝ≥0∞) * keepCost PairOut HashDomain (epsQN S)

/-- The initial state has empty databases. -/
theorem querySupportedOn_dbGrade_initSN :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := PairOut) (Z := HashDomain)
      (m0SN (n := n))).D ↦ dbGrade m.2.1) (Set.Iic 0) (initU (X := PairOut)
        (Z := HashDomain) (m0SN (n := n))) := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty PairOut HashDomain, m0SN) : RRegSN n (SelMemN n))).matrix) m m' ≠
      0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · constructor <;> simp [← he.1, ← he.2, dbGrade, Database.size_empty]
  · exact absurd rfl h

/-- **The event bound over the whole game**: from a bound `(c + √tw)²` on the event weight at the
end of the challenge prefix, each of the `verifyCalls` verification reads costs `√(epsQN S)` in
the square root and its linear terms `verLinQN S`:
`ew ≤ (c + verTermQN S + √(tw + verLinQN S))²`. -/
theorem ewMuGameQSN_le (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (B : Set (RRegSN n (SelMemN n))) [DecidablePred (· ∈ B)]
    (hup : ∀ W m, UpClosed (slice B W m)) (S : Fin n → Disclosures)
    (hfresh : ∀ W m t, FreshBound (slice B W m) t (epsQN S)) (θ : TValsN n) {q K : ℕ}
    (hadv : IFreeM.IsChargeBound (prefixQSN pols A θ)
      (portCharge fun i ↦ if extCls PairOut HashDomain (Finset (TPosN n) × SelMemN n)
        (recSpec (TPosN n) (SelMemN n)) i then 0 else 1) q)
    (hcls : IFreeM.IsChargeBound (prefixQSN pols A θ)
      (portCharge fun i ↦ if extCls PairOut HashDomain (Finset (TPosN n) × SelMemN n)
        (recSpec (TPosN n) (SelMemN n)) i then 1 else 0) K) (c tw : ℝ≥0∞)
    (hpreT : (runtimeR m0SN).eventWeight .instruments (hwProjector B) (prefixQSN pols A θ)
      (initU m0SN) ≤ (c + tw ^ (2⁻¹ : ℝ)) ^ 2) :
    (runtimeR m0SN).eventWeight .instruments (hwProjector B) (muGameQSN pols valid A θ)
        (initU m0SN) ≤
      (c + verTermQN S + (tw + verLinQN S) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have hε : epsQN S ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 (by positivity), ?_⟩
    refine ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ ↦ ENNReal.ofReal_ne_top)
      (iSup_le fun i ↦ Finset.single_le_sum
        (f := fun i ↦ ENNReal.ofReal (price (S i))) (fun _ _ ↦ zero_le) (Finset.mem_univ i))
  have hcalls : IFreeM.IsChargeBound (prefixQSN pols A θ) (portCharge fun _ ↦ 1) (q + K) := by
    refine isChargeBound_mono_charge (fun s a ↦ ?_) (hadv.add hcls)
    rcases a with o | ⟨i, E, ℓ⟩
    · exact le_rfl
    · show 1 ≤ (if extCls PairOut HashDomain (Finset (TPosN n) × SelMemN n)
          (recSpec (TPosN n) (SelMemN n)) i then 0 else 1) +
        (if extCls PairOut HashDomain (Finset (TPosN n) × SelMemN n)
          (recSpec (TPosN n) (SelMemN n)) i then 1 else 0)
      split_ifs <;> omega
  have hρa := fun a ↦ ((runtimeR m0SN).run₂ .instruments
    (prefixQSN pols A θ)).posSemidef_branch_apply a
      (initU_posSemidef (X := PairOut) (Z := HashDomain) m0SN)
  have hga := fun a ↦ QuerySupportedOn.run_of_charge_step
    (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))) (fun s ↦ dbGrade s.1)
    (fun _ ↦ 1) (querySupportedOn_runtimeR_step' (X := PairOut) (Z := HashDomain) m0SN)
    .instruments hcalls querySupportedOn_dbGrade_initSN ⟨QReg.of Unit, rfl, a⟩
  have hnba := fun a ↦ noBot_runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))
    .instruments (prefixQSN pols A θ) (SubState.basis ()).matrix ⟨QReg.of Unit, rfl, a⟩
  have h2 := fun a ↦ (rpow_inv_two_eventWeight_keepReads_le B hup m0SN
    (N := q + K + verifyCalls) hε (fun W m ↦ hfresh W m _) .instruments
    (realizeT θ (verifyTN (SelMemN n) valid a)) (calls_verifyTN θ valid a)
    (nonKeep_verifyTN θ valid a) (t := 0 + (q + K)) (by omega) (hρa a) (hga a)
    (hnba a)).trans_eq (add_comm _ _)
  have hmink := rpow_inv_two_tsum_le_of_le_add_tsum h2
  have htr : ∑' a, ENNReal.ofReal (((runtimeR m0SN).run₂ .instruments
      (prefixQSN pols A θ)).branch a (initU m0SN)).trace.re ≤ 1 :=
    (((runtimeR m0SN).run₂ .instruments (prefixQSN pols A θ)).isCPTNIFamily.tsum_ofReal_trace_re_le
      (initU_posSemidef (X := PairOut) (Z := HashDomain) m0SN)).trans
        (ENNReal.ofReal_le_one.mpr ((SubState.basis ()).prod
          (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).init).trace_re_le_one)
  have hpre := eventWeight_eq_tsum_run₂ (runtimeR m0SN) .instruments
    (hwProjector B) (prefixQSN pols A θ) (initU m0SN)
  have hm : ∑' j, (∑' a, (if j < verifyCalls then epsQN S else 0) *
      ENNReal.ofReal (((runtimeR m0SN).run₂ .instruments (prefixQSN pols A θ)).branch a
        (initU m0SN)).trace.re) ^ (2⁻¹ : ℝ) ≤ verTermQN S := by
    calc _ ≤ ∑' j, ((if j < verifyCalls then epsQN S else 0) * 1) ^ (2⁻¹ : ℝ) := by
          refine ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [ENNReal.tsum_mul_left]
          gcongr
      _ = verTermQN S := by
          unfold verTermQN
          rw [tsum_rpow_inv_two_ite, mul_one]
  have ht : ∑' a, (potential (hwProjector B)
      (((runtimeR m0SN).run₂ .instruments (prefixQSN pols A θ)).branch a (initU m0SN)) +
      (verifyCalls : ℝ≥0∞) * keepCost PairOut HashDomain (epsQN S) *
        ENNReal.ofReal (((runtimeR m0SN).run₂ .instruments (prefixQSN pols A θ)).branch a
          (initU m0SN)).trace.re) ≤
      (runtimeR m0SN).eventWeight .instruments (hwProjector B) (prefixQSN pols A θ)
        (initU m0SN) + verLinQN S := by
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    refine add_le_add (le_of_eq hpre.symm) ?_
    calc (verifyCalls : ℝ≥0∞) * keepCost PairOut HashDomain (epsQN S) * _
        ≤ (verifyCalls : ℝ≥0∞) * keepCost PairOut HashDomain (epsQN S) * 1 := by
          gcongr
      _ = verLinQN S := mul_one _
  have hpre' : ((runtimeR m0SN).eventWeight .instruments (hwProjector B)
      (prefixQSN pols A θ) (initU m0SN) + verLinQN S) ^ (2⁻¹ : ℝ) ≤
      c + (tw + verLinQN S) ^ (2⁻¹ : ℝ) := by
    have h := rpow_inv_two_add_le_of_le_sq (c := c ^ 2) (δ := 0) (C := verLinQN S)
      (b := tw) (a := (runtimeR m0SN).eventWeight .instruments
        (hwProjector B) (prefixQSN pols A θ) (initU m0SN)) (by
          rw [Quantum.Qrom.Xmss.sq_rpow_inv_two_eq, add_zero]
          exact hpreT.trans_eq (by rw [add_comm c]))
    rwa [Quantum.Qrom.Xmss.sq_rpow_inv_two_eq, zero_add] at h
  have hew : (runtimeR m0SN).eventWeight .instruments (hwProjector B) (muGameQSN pols valid A θ)
      (initU m0SN) = ∑' a, (runtimeR m0SN).eventWeight .instruments (hwProjector B)
        (realizeT θ (verifyTN (SelMemN n) valid a))
        (((runtimeR m0SN).run₂ .instruments (prefixQSN pols A θ)).branch a (initU m0SN)) := by
    rw [muGameQSN_eq_verify]
    exact eventWeight_bind₂ (runtimeR m0SN) .instruments (hwProjector B)
      (prefixQSN pols A θ) _ (initU_posSemidef (X := PairOut) (Z := HashDomain) m0SN)
  have hfin : (runtimeR m0SN).eventWeight .instruments (hwProjector B) (muGameQSN pols valid A θ)
      (initU m0SN) ^ (2⁻¹ : ℝ) ≤ c + verTermQN S + (tw + verLinQN S) ^ (2⁻¹ : ℝ) := by
    rw [hew]
    refine hmink.trans ?_
    calc _ ≤ ((runtimeR m0SN).eventWeight .instruments (hwProjector B)
          (prefixQSN pols A θ) (initU m0SN) + verLinQN S) ^ (2⁻¹ : ℝ) + verTermQN S :=
          add_le_add (ENNReal.rpow_le_rpow ht (by norm_num)) hm
      _ ≤ c + (tw + verLinQN S) ^ (2⁻¹ : ℝ) + verTermQN S :=
          add_le_add hpre' le_rfl
      _ = _ := by ring
  have h := ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

variable (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
  {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
  (hsignAt : ∀ pks i, IFreeM.IsChargeBound (A pks) (cmdCharge (signChargeAt i)) signatureLimit)
include hhash hsign hsignAt

/-- **Runtime 2's win at `θ`**: `0` off `GoodSN`; on `GoodSN` the event at the end of the game,
bounded through Costs' `ewPrefixQSN_le`:
`p2SN ≤ (advTermQN q S★ + verTermQN S★ + √(twMaskSN + verLinQN S★))² + readErrQ`,
`S★ = starQN θ`. -/
theorem p2SN_le (θ : TValsN n) :
    p2SN (strPolN n) valid A θ ≤ (advTermQN q (starQN θ) + verTermQN (starQN θ) +
      (twMaskSN A θ + verLinQN (starQN θ)) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ := by
  by_cases hG : GoodSN θ
  · rw [twMaskSN_of_pDistinct A hG]
    have hadv := advCalls_prefixQS cwUpdN (strPolN n) A hhash hsign θ
    have hcls := clsCalls_prefixQS cwUpdN (strPolN n) A hhash hsign θ
    exact (p2SN_le_eventWeight valid A hsignAt θ).trans (add_le_add
      (ewMuGameQSN_le (strPolN n) valid A _ (fun W m ↦ upClosed_slice_badRQN W m) (starQN θ)
        (fun W m t ↦ freshBound_slice_badRQN W m t) θ hadv hcls _ _
        (ewPrefixQSN_le (pkQN θ) (honQN θ) (starQN θ) A θ hadv hcls)) le_rfl)
  · rw [p2SN_eq_zero_of_not hG]
    exact zero_le

end event

/-! ## Averaged over the hidden values -/

section average

/-- **The mean fresh fraction**: `2^-128` plus the mean worst user's price. -/
noncomputable def epsBarN (n : ℕ) : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ + rhoMaxQ n

/-- **The mean fresh fraction over the hidden values** (the users' streams are uniform). -/
theorem uavg_epsQN_le : uavg (fun θ : TValsN n ↦ epsQN (starQN θ)) ≤ epsBarN n := by
  unfold epsQN starQN epsBarN
  rw [uavg_add, uavg_const]
  refine add_le_add le_rfl (le_of_eq ?_)
  exact uavg_streamsOf (P := Option Pos) (J := Message) (N := signatureLimit) (Ω := PairOut)
    fun d ↦ ⨆ i, ENNReal.ofReal (price (starCover (d i)))

/-- **The averaged adversary term**: `√(6 q² epsBarN n)`. -/
noncomputable def advBarN (n q : ℕ) : ℝ≥0∞ :=
  ((q : ℝ≥0∞) ^ 2 * (6 * epsBarN n)) ^ (2⁻¹ : ℝ)

/-- **The averaged verification term**: `√(verifyCalls² epsBarN n)`. -/
noncomputable def verBarN (n : ℕ) : ℝ≥0∞ :=
  ((verifyCalls : ℝ≥0∞) ^ 2 * epsBarN n) ^ (2⁻¹ : ℝ)

/-- **The averaged verification's linear term**: `verifyCalls (epsBarN n + 2/|Y| + 2/|D|)`. -/
noncomputable def verLinBarN (n : ℕ) : ℝ≥0∞ :=
  (verifyCalls : ℝ≥0∞) * keepCost PairOut HashDomain (epsBarN n)

theorem advTermQN_eq_rpow (q : ℕ) (S : Fin n → Disclosures) :
    advTermQN q S = ((q : ℝ≥0∞) ^ 2 * (6 * epsQN S)) ^ (2⁻¹ : ℝ) := by
  unfold advTermQN
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, natCast_mul_rpow_inv_two]

theorem verTermQN_eq_rpow (S : Fin n → Disclosures) :
    verTermQN S = ((verifyCalls : ℝ≥0∞) ^ 2 * epsQN S) ^ (2⁻¹ : ℝ) :=
  natCast_mul_rpow_inv_two _ _

variable (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
  {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
  (hsignAt : ∀ pks i, IFreeM.IsChargeBound (A pks) (cmdCharge (signChargeAt i)) signatureLimit)
include hhash hsign hsignAt

/-- **Runtime 2's win, averaged** (Minkowski over the hidden values): with the prefix's masked
averaged classical cost at most `T`,
`E p2SN ≤ (advBarN n q + verBarN n + √(T + verLinBarN n))² + readErrQ`. -/
theorem uavg_p2SN_le {T : ℝ≥0∞} (hcost : uavg (twMaskSN A) ≤ T) :
    uavg (p2SN (strPolN n) valid A) ≤
      (advBarN n q + verBarN n + (T + verLinBarN n) ^ (2⁻¹ : ℝ)) ^ 2 + readErrQ := by
  refine (uavg_mono (p2SN_le valid A hhash hsign hsignAt)).trans ?_
  rw [uavg_add, uavg_const]
  refine add_le_add ?_ le_rfl
  simp only [advTermQN_eq_rpow, verTermQN_eq_rpow]
  refine (uavg_sq_rpow_add3_le _ _ _).trans (pow_le_pow_left₀ zero_le
    (add_le_add (add_le_add ?_ ?_) ?_) 2)
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_const_mul, uavg_const_mul]
    gcongr
    exact uavg_epsQN_le
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_const_mul]
    gcongr
    exact uavg_epsQN_le
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [uavg_add]
    refine add_le_add hcost ?_
    unfold verLinQN verLinBarN keepCost
    rw [uavg_const_mul, uavg_add, uavg_add, uavg_const, uavg_const]
    gcongr
    exact uavg_epsQN_le

end average

end Quantum.Qrom.Sphincs.Multi

end
