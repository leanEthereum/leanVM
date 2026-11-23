module

public import Quantum.StdModel.Qrom.SphincsItsrRt1Game
public import Quantum.StdModel.Sphincs.ItsrHop

@[expose] public section

/-!
# B3's ITSR success in the QROM is at most runtime 1 on the template game

Step 1 of the ITSR bound at leanSPHINCS's B3 (`SphItsr`). B3's ITSR success over a uniform table
is the average over `H` of the ideal game read through the ITSR decision (`ideal_itsr_eq`). The
template's decision (`dI`: `true` past `signatureLimit` signed messages, the ITSR event of the
data of the first `signatureLimit` ones otherwise) dominates the ITSR decision
(`itsrDec_imp_dI`). The ideal game at the table of given digests, read through `dI`, is a
program of the random oracle with a pure signer (`gameAt_dI_eq`, `gameL`), which at a function
holding the non-secret values of `tabOf θ` has the law of the ITSR read game (`phiI_eq`), the read
program of runtime 1 on the template (`p1I_eq`). Averaging (`uavg_hwI_eq`):

* `probAvg_itsrRed_le_uavg`: B3's ITSR success in the QROM is at most the uniform average over
  the hidden values `θ` of runtime 1 with record ports, the non-secret cells `hwI θ` hardwired,
  running the template game `gameIQ msgPol A θ`.
-/

open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open OracleComp OracleSpec

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime Quantum.Qrom.Sphincs
open Quantum.Qrom (regroup)
open Quantum.Sponge (spongeFnReadRuntime overwrite read_port_eq_classical_read)
open Quantum.Xmss.Hybrid (uavg)
open Quantum.Xmss.Assembly (runtime1R)

attribute [local irreducible] Quantum.Qrom.hashQ LeanSphincsOver.messageDigest

/-! ## The template's decision on the game's run -/

/-- The ITSR data of the signed messages `msgs` at the table `v` under `h`. -/
def dataL (h : HashInput → HashOutput) (v : QTable) (msgs : List Message) : List ItsrDatum :=
  msgs.map fun M ↦ (M, v.randomizer M, digestOf h v.publicKey (v.randomizer M) M)

/-- **The template's ITSR decision on a run** at the table `v` under `h`. -/
noncomputable def dI (h : HashInput → HashOutput) (v : QTable) (r : Forgery × SignLog) : Bool :=
  itsrDecT r.2.length r.1 (dataL h v (logMsgsT r.2))
    (digestOf h v.publicKey r.1.signature.randomizer r.1.message)

theorem logMsgsT_eq_logMsgs {log : SignLog} (hl : log.length ≤ signatureLimit) :
    logMsgsT log = logMsgs log := by
  unfold logMsgsT logMsgs logPairs
  rw [List.map_map, List.take_of_length_le (by rw [List.length_map]; exact hl)]
  rfl

/-- **The template's decision dominates the ITSR decision.** -/
theorem itsrDec_imp_dI (h : HashInput → HashOutput) (v : QTable) (r : Forgery × SignLog)
    (hr : itsrDec h v r = true) : dI h v r = true := by
  unfold dI itsrDecT
  by_cases hn : signatureLimit < r.2.length
  · rw [decide_eq_true hn, Bool.true_or]
  · rw [decide_eq_false hn, Bool.false_or, Props.holds_eq_true]
    have hE := Props.holds_eq_true.mp hr
    rw [logMsgsT_eq_logMsgs (Nat.le_of_not_lt hn)]
    unfold ItsrHolds
    refine ⟨?_, ?_⟩
    · rw [dataL, List.map_map]
      exact hE.1
    · rw [dataL, List.map_map]
      exact hE.2

/-- Uniform averages are monotone. -/
theorem unifAvg_le_of_le {X : Type} [Fintype X] {Φ Ψ : X → ℝ≥0∞} (h : ∀ x, Φ x ≤ Ψ x) :
    unifAvg X Φ ≤ unifAvg X Ψ :=
  mul_le_mul' le_rfl (Finset.sum_le_sum fun x _ ↦ h x)

/-- **The game read through the template's decision dominates the ITSR game.** -/
theorem gameAt_itsrDec_le (A' : SAdv romWorld) (H : romWorld.Tab) (v : QTable) :
    gameAt romWorld H A' v (itsrDec (romWorld.hashOf H) v) ≤
      gameAt romWorld H A' v (dI (romWorld.hashOf H) v) := by
  unfold gameAt
  refine (probAt_map_le_sum romWorld H _ _ Finset.univ (fun _ : Unit ↦ dI (romWorld.hashOf H) v)
    fun r hr ↦ ⟨(), Finset.mem_univ _, itsrDec_imp_dI _ v r hr⟩).trans_eq ?_
  exact Fintype.sum_unique _

/-! ## The game at a table as the game with a pure signer -/

/-- **The forgery's digest at a fixed function** is `digestOf`. -/
theorem simulateQ_messageDigest_rom (H : romWorld.Tab) (pk : PublicKey) (R : Randomizer)
    (M : Message) :
    simulateQ (romWorld.eager H) (LeanSphincsOver.messageDigest Qrom.hashQ pk R M) =
      pure (digestOf (romWorld.hashOf H) pk R M) := by
  refine (Over.simulateQ_messageDigest (romWorld.eager H) romWorld.hash pk R M).trans ?_
  simp only [romWorld.simulateQ_hash H]
  rw [LeanSphincsOver.messageDigest]
  simp only [LeanSphincsOver.messageDigestCall, sequenceFin_pure, pure_bind]
  rfl

/-- The encoding cells of the hash `cellHash` of a table's hash are the table's. -/
theorem encAgree_cellHash (H : Qrom.HashDomain → HashOutput) (seed : PublicParameter) :
    EncAgree seed (cellHash (romWorld.hashOf H)) H := fun l τ e msg c ↦ by
  have he := encodeInput_encCell seed l τ e msg c
  change romWorld.hashOf H (Qrom.decodeInput (encCell seed l τ e msg c)) =
    H (encCell seed l τ e msg c)
  rw [Qrom.decodeInput_of_encodeInput_eq_some he,
    show ∀ l', romWorld.hashOf H l' = (Qrom.encodeInput l').elim 0 H from fun _ ↦ rfl, he,
    Option.elim_some]

/-- **The game at the table `v`, read through the template's decision**, is the game with the
pure signer of `v`'s signatures, `v`'s public key and `v`'s data. -/
theorem gameAt_dI_eq (H : romWorld.Tab) (v : QTable) (A : SAdversary) :
    gameAt romWorld H (ofQrom A) v (dI (romWorld.hashOf H) v) =
      romWorld.probAt H (gameL (fun M ↦ v.signature (cellHash (romWorld.hashOf H)) M)
        v.publicKey (dataL (romWorld.hashOf H) v) A) := by
  have hK : signKernel romWorld sigSch (fun M ↦ v.signature (cellHash (romWorld.hashOf H)) M) H =
      detKernel (romWorld.hashOf H) v := by
    funext log M
    rfl
  have hX : (romWorld.runtime H).run₂ .instruments
      (kRunQ romWorld (detKernel (romWorld.hashOf H) v) (ofQrom A v.publicKey) []) =
      (romWorld.runtime H).run₂ .instruments (Quantum.Qrom.SufCma.challenged sigSch
        (fun M ↦ v.signature (cellHash (romWorld.hashOf H)) M)
        (Quantum.Qrom.SufCma.withSignLog (A v.publicKey))) := by
    rw [← hK, ← run₂_challenged_withCallLog (W := romWorld) sigSch
      (fun M ↦ v.signature (cellHash (romWorld.hashOf H)) M) H (ofQrom A v.publicKey)]
    exact congrArg ((romWorld.runtime H).run₂ .instruments)
      (substitute_logSigns_ofQrom sigSch _ _ (A v.publicKey) []).symm
  have hL : gameL (fun M ↦ v.signature (cellHash (romWorld.hashOf H)) M) v.publicKey
      (dataL (romWorld.hashOf H) v) A =
      (Quantum.Qrom.SufCma.challenged sigSch (fun M ↦ v.signature (cellHash (romWorld.hashOf H)) M)
        (Quantum.Qrom.SufCma.withSignLog (A v.publicKey))).bind fun run ↦
          tailL (v.publicKey, run, dataL (romWorld.hashOf H) v (logMsgsT run.2)) := by
    simp only [gameL, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  unfold gameAt
  refine probAt_eq_of_run₂ romWorld H ?_
  rw [QuantumComp₂.map_eq_bind_pure, hL]
  refine run₂_bind_congr hX fun run ↦ ?_
  rw [tailL]
  have hc := (romWorld.classicalOn_toQuantumAt H (QReg.of Unit)
    (LeanSphincsOver.messageDigest romWorld.hash v.publicKey run.1.signature.randomizer
      run.1.message)).congr (simulateQ_messageDigest_rom H _ _ _) rfl
  exact (run₂_bind_of_classicalOn_pure (romWorld.runtime H) hc fun dF ↦
    QuantumComp₂.pure (itsrDecT run.2.length run.1
      (dataL (romWorld.hashOf H) v (logMsgsT run.2)) dF)).symm

/-! ## The ideal game against runtime 1's reads -/

/-- **The ideal game's statistic**: the game at the table of the digests `x` under `H`, read
through the template's decision. -/
noncomputable def phiI (A : SAdversary) (H : Qrom.HashDomain → HashOutput)
    (x : PublicParameter × (KeygenDomain → Digest) × (Message → Digest)) : ℝ≥0∞ :=
  gameAt romWorld H (ofQrom A) (digTable (romWorld.hashOf H) x.1 x.2.1 x.2.2)
    (dI (romWorld.hashOf H) (digTable (romWorld.hashOf H) x.1 x.2.1 x.2.2))

/-- **At a function holding the non-secret values of `tabOf θ`**, the ideal game at the digests of
its secrets has the law of the ITSR read game against runtime 1's classical reads. -/
theorem phiI_eq (A : SAdversary) (θ : TVals) (t : TFun) :
    phiI A (regroup hmsgRoute (overwrite (hwI θ) t).1) (digsOf (tabOf θ)) =
      (spongeFnReadRuntime PairOut Qrom.HashDomain t (hwI θ) ()).evalDistMap .instruments
        (gameReadsI θ A) (SubState.basis ()) winObsQ {true} := by
  have hon : Honest (romWorld.hashOf (regroup hmsgRoute (overwrite (hwI θ) t).1)) (tabOf θ) :=
    honest_tabOf θ fun p hp ↦ overwrite_hwI θ t p hp
  have hpk : (digTable (romWorld.hashOf (regroup hmsgRoute (overwrite (hwI θ) t).1))
      (tabOf θ).publicSeed (secDig (tabOf θ)) (tabOf θ).randomizer).publicKey =
        (tabOf θ).publicKey :=
    (publicKey_eq_digTable_of_honest hon).symm
  have hs : ∀ msg, (digTable (romWorld.hashOf (regroup hmsgRoute (overwrite (hwI θ) t).1))
      (tabOf θ).publicSeed (secDig (tabOf θ)) (tabOf θ).randomizer).signature
        (cellHash (romWorld.hashOf (regroup hmsgRoute (overwrite (hwI θ) t).1))) msg =
      (tabOf θ).signature (regroup hmsgRoute (overwrite (hwI θ) t).1) msg := fun msg ↦
    (signature_eq_digTable_of_honest hon _ msg).symm.trans
      (signature_congrH (encAgree_cellHash _ _) msg)
  have hd : ∀ msgs, dataL (romWorld.hashOf (regroup hmsgRoute (overwrite (hwI θ) t).1))
      (digTable (romWorld.hashOf (regroup hmsgRoute (overwrite (hwI θ) t).1))
        (tabOf θ).publicSeed (secDig (tabOf θ)) (tabOf θ).randomizer) msgs =
      msgs.map (datumD θ) := fun msgs ↦ List.map_congr_left fun M _ ↦ by
    rw [randomizer_digTable, hpk, datumD, sigTabD_randomizer, dgD_eq,
      Extract.messageDigest_eq hon M]
  unfold phiI
  refine (gameAt_dI_eq (regroup hmsgRoute (overwrite (hwI θ) t).1) _ A).trans ?_
  exact congrArg (fun μ ↦ μ {true}) (evalDistMap_gameL_eq t (hwI θ) θ hs (hpk.trans pkD_eq.symm)
    hd A (SubState.basis ()) winObsQ)

/-- **Runtime 1 on the template game is the average over runtime 1's functions** of the ideal
game at the digests of the secrets of `tabOf θ`. -/
theorem p1I_eq (A : SAdversary) (θ : TVals) :
    (runtime1R PairOut Qrom.HashDomain (hwI θ) m0H).evalDistMap .instruments
        (gameIQ msgPol A θ) (SubState.basis ()) winObsQ {true} =
      ∑ t : TFun, (Fintype.card TFun : ℝ≥0∞)⁻¹ *
        phiI A (regroup hmsgRoute (overwrite (hwI θ) t).1) (digsOf (tabOf θ)) := by
  rw [evalDistMap_runtime1R_gameIQ]
  have e := congrArg (fun μ ↦ μ {true}) (read_port_eq_classical_read (hwI θ) ()
    LocalSig.Interp.instruments (gameReadsI θ A) (SubState.basis ()) winObsQ)
  simp only [MeasureTheory.Measure.coe_finsetSum, Finset.sum_apply,
    MeasureTheory.Measure.smul_apply, smul_eq_mul] at e
  convert e using 3 with t
  exact phiI_eq A θ t

/-! ## The bound -/

/-- **B3's ITSR success in the QROM is at most runtime 1 on the template game**: the average over
the hidden values `θ` of runtime 1 with record ports, the non-secret cells `hwI θ` hardwired,
running `gameIQ msgPol A θ`. -/
theorem probAvg_itsrRed_le_uavg (A : SAdversary) :
    romWorld.probAvg ((Props.itsr romWorld itsrMap).game (itsrRed romWorld (ofQrom A))) ≤
      uavg (fun θ : TVals ↦ (runtime1R PairOut Qrom.HashDomain (hwI θ) m0H).evalDistMap
        .instruments (gameIQ msgPol A θ) (SubState.basis ()) winObsQ {true}) := by
  have hΦ : ∀ H P s s' r, (∀ d, KDIn d → s d = s' d) →
      phiI A H (P, s, r) = phiI A H (P, s', r) := fun H P s s' r hs ↦ by
    unfold phiI
    dsimp only
    rw [digTable_congr_sec _ P r hs]
  calc romWorld.probAvg ((Props.itsr romWorld itsrMap).game (itsrRed romWorld (ofQrom A)))
      = unifAvg romWorld.Tab fun H ↦
          ideal romWorld H (ofQrom A) (itsrDec (romWorld.hashOf H)) := by
        rw [OracleWorld.probAvg_eq_sum]
        unfold unifAvg
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun H _ ↦ congrArg _
          (ideal_itsr_eq romWorld H (ofQrom A) romWorld_coinsFair).symm
    _ ≤ unifAvg (Qrom.HashDomain → HashOutput) fun H ↦ unifAvg PublicParameter fun P ↦
          unifAvg (KeygenDomain → Digest) fun s ↦ unifAvg (Message → Digest) fun r ↦
            phiI A H (P, s, r) :=
        unifAvg_le_of_le fun H ↦ unifAvg_le_of_le fun P ↦ unifAvg_le_of_le fun s ↦
          unifAvg_le_of_le fun r ↦ gameAt_itsrDec_le _ H _
    _ = uavg (fun θ : TVals ↦ ∑ t : TFun, (Fintype.card TFun : ℝ≥0∞)⁻¹ *
          phiI A (regroup hmsgRoute (overwrite (hwI θ) t).1) (digsOf (tabOf θ))) :=
        (uavg_hwI_eq (phiI A) hΦ).symm
    _ = _ := congrArg uavg (funext fun θ ↦ (p1I_eq A θ).symm)

end Quantum.StdModel.Sphincs.SphItsr

end
