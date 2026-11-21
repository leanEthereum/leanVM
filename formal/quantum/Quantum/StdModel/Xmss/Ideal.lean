module

public import Quantum.StdModel.Decide
public import Quantum.StdModel.Xmss.Extract

@[expose] public section

/-!
# The ideal leanXMSS game at a fixed table and its three events

At a fixed table `tab` of a world, with `h := W.hashOf tab`, the ideal game of an ideal secret
`k : IdealKey` (a parameter, chain starts and randomizer bases, see `Xmss.Gen`) runs the adversary
on the public key `idealPk h k` with each signing request answered by the abstract signer at the
ideal operations (`idealKernel`), then decides. `idealProb W tab A d` is the average over a uniform
ideal secret of the probability of the decision `d`.

* `idealWin`: the forgery verifies and the transcript is a win.
* `encDec`, `tcrDec`, `cpreDec`: the events of the reduction on an honest transcript without
  repeated leaf indices.
* `idealProb_win_le`: **the union bound**: the ideal game is won at most with the sum of the
  probabilities of the three events (`extract`).
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props

/-- leanXMSS over the world's Keccak-256. -/
noncomputable abbrev xmssScheme (W : OracleWorld) :=
  Qrom.Xmss.xmssOver W.hash

section Ideal

variable (h : HashInput → HashOutput) (k : IdealKey)

/-- The ideal signer's answer to a request. -/
def idealSign (r : SigningRequest) : Option Signature :=
  Gen.sign (m := Id) (k.ops h) r.leafIndex r.message

/-- The ideal public key. -/
def idealPk : PublicKey :=
  ⟨Gen.root (k.ops h), k.1⟩

/-- **The ideal signer as a kernel**: its answer, logged. -/
noncomputable def idealKernel : Kernel SigningOracleSpec (QueryLog SigningOracleSpec) :=
  fun log r ↦ pure (idealSign h k r, log ++ [⟨r, idealSign h k r⟩])

/-- Every answer of the transcript is the ideal signer's. -/
def LogHonest (log : QueryLog SigningOracleSpec) : Prop :=
  ∀ x ∈ log, x.2 = idealSign h k x.1

/-- **The ideal win**: the forgery verifies under the ideal public key and the transcript makes
it a win. -/
noncomputable def idealWin (run : Forgery × QueryLog SigningOracleSpec) : Bool :=
  RandomPermutationModel.sufCmaScheme.winningCondition run.2 run.1 &&
    Qrom.Xmss.Over.verify (m := Id) h (idealPk h k) run.1.message run.1.signature

/-- An event on an honest transcript without repeated leaf indices, as a decision. -/
noncomputable def evDec (ev : QueryLog SigningOracleSpec → Forgery → Prop)
    (run : Forgery × QueryLog SigningOracleSpec) : Bool :=
  holds (SigningTranscript.NoLeafIndexReused run.2 ∧ LogHonest h k run.2 ∧ ev run.2 run.1)

/-- **The EncTCR$ event** as a decision. -/
noncomputable def encDec : Forgery × QueryLog SigningOracleSpec → Bool :=
  evDec h k fun log F ↦ EncEv h k.1 (k.ops h) log F

/-- **The SM-TCR-C event** as a decision. -/
noncomputable def tcrDec : Forgery × QueryLog SigningOracleSpec → Bool :=
  evDec h k fun _ F ↦ TcrEv h k.1 (k.ops h) F

/-- **The CPRE event** as a decision. -/
noncomputable def cpreDec : Forgery × QueryLog SigningOracleSpec → Bool :=
  evDec h k fun log F ↦ CpreEv h k.1 (k.ops h) log F

end Ideal

variable (W : OracleWorld) (tab : W.Tab)

/-- **The ideal run** at the table `tab`: the adversary on the ideal public key, against the ideal
signer, returning its forgery and transcript. -/
noncomputable def idealRun (k : IdealKey)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    QComp W.spec (QReg.of Unit) (QReg.of Unit) (Forgery × QueryLog SigningOracleSpec) :=
  kRunQ W (idealKernel (W.hashOf tab) k) (A (idealPk (W.hashOf tab) k)) []

/-- **The average over a uniform ideal secret** of the probability of the decision `d` of the
ideal run. -/
noncomputable def idealProb (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery)
    (d : IdealKey → Forgery × QueryLog SigningOracleSpec → Bool) : ℝ≥0∞ :=
  ∑ k : IdealKey, (Fintype.card IdealKey : ℝ≥0∞)⁻¹ * W.probAt tab ((idealRun W tab k A).map (d k))

/-- The ideal signer keeps the transcript honest. -/
theorem logHonest_idealKernel (h : HashInput → HashOutput) (k : IdealKey)
    (log : QueryLog SigningOracleSpec) (hl : LogHonest h k log) (r : SigningRequest) :
    ∀ p ∈ support (idealKernel h k log r), LogHonest h k p.2 := by
  intro p hp
  simp only [idealKernel, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hl x hx
  · rw [List.mem_singleton] at hx
    subst hx
    rfl

/-- On the ideal run the win is the win on an honest transcript. -/
theorem probAt_idealWin_eq (k : IdealKey)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    W.probAt tab ((idealRun W tab k A).map (idealWin (W.hashOf tab) k)) =
      W.probAt tab ((idealRun W tab k A).map fun run ↦
        holds (idealWin (W.hashOf tab) k run = true ∧ LogHonest (W.hashOf tab) k run.2)) := by
  refine probAt_eq_of_run₂ W tab ?_
  refine run₂_map_kRunQ_sim (W.runtime tab) (idealKernel (W.hashOf tab) k)
    (idealKernel (W.hashOf tab) k) (LogHonest (W.hashOf tab) k) id
    (fun _ _ _ ↦ by simp) (fun s hs r ↦ logHonest_idealKernel _ k s hs r)
    _ [] (fun _ h ↦ (List.not_mem_nil h).elim) _ _ fun a s hs ↦ ?_
  change idealWin (W.hashOf tab) k (a, s) =
    holds (idealWin (W.hashOf tab) k (a, s) = true ∧ LogHonest (W.hashOf tab) k s)
  cases hw : idealWin (W.hashOf tab) k (a, s)
  · cases hh : holds (false = true ∧ LogHonest (W.hashOf tab) k s)
    · rfl
    · exact absurd (holds_eq_true.mp hh).1 (by simp)
  · exact (holds_eq_true.mpr ⟨rfl, hs⟩).symm

/-- A win on an honest transcript is one of the three events. -/
theorem win_imp_events (h : HashInput → HashOutput) (k : IdealKey)
    (run : Forgery × QueryLog SigningOracleSpec)
    (hw : holds (idealWin h k run = true ∧ LogHonest h k run.2) = true) :
    encDec h k run = true ∨ tcrDec h k run = true ∨ cpreDec h k run = true := by
  obtain ⟨hw, hl⟩ := holds_eq_true.mp hw
  simp only [idealWin, Bool.and_eq_true] at hw
  obtain ⟨hwin, hver⟩ := hw
  simp only [RandomPermutationModel.sufCmaScheme, decide_eq_true_eq] at hwin
  obtain ⟨hreuse, hnew⟩ := hwin
  rcases extract h k run.2 run.1 hl hreuse hver hnew with he | he | he
  · exact .inl (holds_eq_true.mpr ⟨hreuse, hl, he⟩)
  · exact .inr (.inl (holds_eq_true.mpr ⟨hreuse, hl, he⟩))
  · exact .inr (.inr (holds_eq_true.mpr ⟨hreuse, hl, he⟩))

/-- **The union bound of the ideal game**: the ideal win is at most the sum of the averaged
probabilities of the EncTCR$, SM-TCR-C and CPRE events. -/
theorem idealProb_win_le
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) :
    idealProb W tab A (fun k ↦ idealWin (W.hashOf tab) k) ≤
      idealProb W tab A (fun k ↦ encDec (W.hashOf tab) k) +
        idealProb W tab A (fun k ↦ tcrDec (W.hashOf tab) k) +
          idealProb W tab A (fun k ↦ cpreDec (W.hashOf tab) k) := by
  simp only [idealProb, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_le_sum fun k _ ↦ mul_le_mul' le_rfl ?_
  rw [probAt_idealWin_eq]
  have hu := probAt_map_le_sum W tab (idealRun W tab k A) _ (Finset.univ : Finset (Fin 3))
    (fun i ↦ ![encDec (W.hashOf tab) k, tcrDec (W.hashOf tab) k, cpreDec (W.hashOf tab) k] i)
    fun run hr ↦ by
      rcases win_imp_events _ k run hr with he | he | he
      · exact ⟨0, Finset.mem_univ _, he⟩
      · exact ⟨1, Finset.mem_univ _, he⟩
      · exact ⟨2, Finset.mem_univ _, he⟩
  refine hu.trans (le_of_eq ?_)
  rw [Fin.sum_univ_three]
  rfl

end Quantum.StdModel.Xmss

end
