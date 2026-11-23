module

public import Quantum.StdModel.Qrom.SphincsItsrEndWinFold

@[expose] public section

/-!
# The end of the ITSR game: runtime 2's win against the event

Runtime 2's ITSR win at the policy `strPol` and the hidden values `θ` (`p2I strPol A θ`,
`SphincsItsrGame`) is at most the weight of `BadRQ (pkQ θ) (honQ θ) S★` (`S★ = starQ θ`) at the
end of the game plus the read error of the tail's two reads, as for the SUF-CMA game
(`Quantum.Qrom.Sphincs.End`).

* **The game's shape** (`realizeT_tailIT`, `gameIQ_eq`): the prefix with the data, the logging
  reads of the forgery's digest (End's `readsProgramV`) and the ITSR decision.
* **A winning run is in the event** (`mem_badRQ_of_runFactsI`): the forgery's call-0 `H_msg` cell
  is read, so a view holding the log holds its pair `ω`, the forgery's digest is
  `digestOfPair ω`; it is not hardwired, else it is a signed message's digest cell (`HwDigests`)
  and cell injectivity makes the forgery's pair that message's pair, a datum's; and the decision's
  coverage of its cells covers its view by `S★` (`covered_of_cells`): a Cov hit.
* **The decomposition** (`winDecompI`) and EndReads' `win_le_of_winDecomp`:
  `p2I ≤ ew + readErrI`, `readErrI` the read error of two reads (`p2I_le_eventWeight`).
-/

open Matrix IPFunctor OracleSpec
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Qrom (regroup RomOracles unionH)
open Quantum.Qrom.Sphincs
open Quantum.SufCma (queries)
open Quantum.Qrom.Xmss (romAnswers honestEval)
open Quantum.Sphincs (Covered)
open Quantum.Xmss.Assembly (recHwSpec runtimeR realizeT readLiftQ NoBotDb initU runSig
  runSig_posSemidef ofReal_trace_conj_runSig trace_conj_branch_true_le_eventWeight
  ofReal_trace_branch_le_one evalDistMap_winBit querySupportedOn_of_conj_compressReg WinDecomp
  win_le_of_winDecomp readLift_bind₂ realizeT_bind₂)

local notation "signChargeQ" => Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-- An outcome of the forgery's logging reads: its digest and the hashed inputs with pairs. -/
abbrev ReadsOutI : Type :=
  MessageDigest × List (Qrom.HashDomain × PairOut)

/-- The forgery's digest computation of a prefix outcome with the data. -/
noncomputable def mdI (y : PreI) : OracleComp RomOracles MessageDigest :=
  LeanSphincsOver.messageDigest Qrom.hashQ y.1 y.2.1.1.signature.randomizer y.2.1.1.message

/-- **The forgery's logging reads** of a prefix outcome `y`, realized at `θ`. Inline: the kernel
recurses checking against such a program wrapped in a definition. -/
local macro "wReadsI " θ:term:max ppSpace y:term:max : term =>
  `((realizeT $θ (readLiftQ goodQ (readsProgramV SelMem (QReg.of Unit) (mdI $y))) :
      QComp (recHwSpec PairOut Qrom.HashDomain TPos SelMem) (QReg.of Unit) (QReg.of Unit)
        ReadsOutI))

/-- The ITSR decision of a prefix outcome with the data and an outcome of the reads. -/
noncomputable def winI (y : PreI) (a : ReadsOutI) : Bool :=
  itsrDecT y.2.1.2.length y.2.1.1 y.2.2 a.1

attribute [local irreducible] Quantum.Qrom.hashQ LeanSphincsOver.messageDigest

/-! ## The game's shape -/

section shape

theorem realizeT_tailIT (θ : TVals) (y : PreI) :
    realizeT θ (tailIT SelMem y) =
      QuantumComp₂.bind (wReadsI θ y) fun (a : ReadsOutI) ↦ QuantumComp₂.pure (winI y a) := by
  rw [tailIT, readsThenT_eq, readsProgram_eq_map, QuantumComp₂.map_eq]
  simp only [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc, QuantumComp₂.pure_bind]
  rw [readLift_bind₂, QuantumComp₂.bind_assoc, realizeT_bind₂]
  rfl

/-- **The game is its prefix with the data, the forgery's logging reads and the decision.** -/
theorem gameIQ_eq (pol : DigestPolicy) (A : SAdversary) (θ : TVals) :
    gameIQ pol A θ = (prefixIQ pol A θ).bind fun y ↦
      QuantumComp₂.bind (wReadsI θ y) fun (a : ReadsOutI) ↦ QuantumComp₂.pure (winI y a) := by
  rw [gameIQ, gameIT_eq, realizeT_bind₂]
  exact congrArg _ (funext fun y ↦ realizeT_tailIT θ y)

end shape

/-! ## The winning runs -/

section decomp

/-- A run of the game: a prefix outcome with the data and a run of the logging reads. -/
abbrev RunI : Type :=
  PreI × ReadsOutI

/-- **The log of a run of the reads**, as a log of `h`-reads at the regrouped cells (empty beyond
two reads, which the forgery's digest does not make). -/
def wLogI (l : List (Qrom.HashDomain × PairOut)) : QueryLog (spongeOSpec PairOut Qrom.HashDomain) :=
  if l.length ≤ 2 then l.map fun p ↦ ⟨.h (hmsgRoute (p.1, false)).1, p.2⟩ else []

theorem readCount_wLogI_le (l : List (Qrom.HashDomain × PairOut)) :
    readCount .h (wLogI l) ≤ 2 := by
  unfold wLogI
  split_ifs with hl
  · exact List.countP_le_length.trans (by rw [List.length_map]; exact hl)
  · exact Nat.zero_le _

theorem readCount_wLogI_eq_zero (l : List (Qrom.HashDomain × PairOut)) {p : SpongePort}
    (hp : p ≠ .h) : readCount p (wLogI l) = 0 := by
  unfold wLogI readCount
  split_ifs
  · rw [List.countP_eq_zero]
    intro e he
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 he
    exact fun h ↦ hp (of_decide_eq_true h).symm
  · rfl

theorem agrees_wLogI {l : List (Qrom.HashDomain × PairOut)} {D : DbReg PairOut Qrom.HashDomain}
    (h : ∀ p ∈ l, D.1 (hmsgRoute (p.1, false)).1 = some p.2) : DbReg.Agrees (wLogI l) D := by
  intro e he
  unfold wLogI at he
  split_ifs at he
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact h p hp
  · exact absurd he List.not_mem_nil

theorem of_agrees_wLogI {l : List (Qrom.HashDomain × PairOut)} (hl : l.length ≤ 2)
    {D : DbReg PairOut Qrom.HashDomain} (h : DbReg.Agrees (wLogI l) D) :
    ∀ p ∈ l, D.1 (hmsgRoute (p.1, false)).1 = some p.2 := fun p hp ↦
  h ⟨.h (hmsgRoute (p.1, false)).1, p.2⟩ (by
    unfold wLogI
    split_ifs
    exact List.mem_map.2 ⟨p, hp, rfl⟩)

/-- **The classical facts of a winning run** `i` on the hardwired cells and the memory `b`: the
run wins, its reads number at most two, any function holding the logged pairs gives the digest
and inputs it did, the public key is the template's, the transcript is within the signing
budget, the data's messages are the transcript's, each datum is honest, and the hardwired call-0
`H_msg` cells are signed digests at the run's table. -/
def RunFactsI (θ : TVals) (i : RunI)
    (b : Hw PairOut Qrom.HashDomain × (Finset TPos × SelMem)) : Prop :=
  winI i.1 i.2 = true ∧ i.2.2.length ≤ 2 ∧
    (∀ F' : Qrom.HashDomain → PairOut, (∀ p ∈ i.2.2, F' (hmsgRoute (p.1, false)).1 = p.2) →
      honestEval (regroup hmsgRoute F') (mdI i.1) = (i.2.1, i.2.2.map Prod.fst)) ∧
    i.1.1 = (tabOf θ).publicKey ∧ i.1.2.1.2.length ≤ signatureLimit ∧
    i.1.2.2.map Prod.fst = logMsgsT i.1.2.1.2 ∧ (∀ d ∈ i.1.2.2, DatumOk θ d) ∧
    ∀ D : DbReg PairOut Qrom.HashDomain,
      HwDigests (seedOf θ) (runTab θ b.2.1) (D, b.1, b.2.2) (i.1.2.1.2.map Sigma.fst)

/-- **A view holding the log of a run with its facts is in the event**: a Cov hit at the
forgery's call-0 `H_msg` cell. -/
theorem mem_badRQ_of_runFactsI (θ : TVals) (i : RunI) {s : RRegS SelMem}
    (hf : RunFactsI θ i s.2) (ha : DbReg.Agrees (wLogI i.2.2) (hwView s.2.1 s.1)) :
    s ∈ BadRQ (pkQ θ) (honQ θ) (starQ θ) := by
  obtain ⟨hw, hl, hev, hpk, hlen, hmsgs, hdat, hD⟩ := hf
  have hU : ∀ p ∈ i.2.2, unionH (projQ s) (hmsgRoute (p.1, false)).1 = some p.2 :=
    of_agrees_wLogI hl ha
  have hE := hev (viewP (unionH (projQ s))) fun p hp ↦ by
    rw [viewP, hU p hp, Option.getD_some]
  -- The forgery's call-0 cell, read with the pair `ω`.
  have hc0 := encodeInput_digestCell i.1.1.publicSeed i.1.1.root
    i.1.2.1.1.signature.randomizer i.1.2.1.1.message 0
  have hx0 : hmsgCall (digestCell i.1.1.publicSeed i.1.1.root i.1.2.1.1.signature.randomizer
      i.1.2.1.1.message 0) = some 0 := by
    rw [hmsgCall_of_encodeInput_eq_some hc0, hmsgCallOf_messageDigestInput]
  have hmem : digestCell i.1.1.publicSeed i.1.1.root i.1.2.1.1.signature.randomizer
      i.1.2.1.1.message 0 ∈ i.2.2.map Prod.fst := by
    have e : (honestEval (regroup hmsgRoute (viewP (unionH (projQ s)))) (mdI i.1)).2 =
        i.2.2.map Prod.fst :=
      congrArg Prod.snd hE
    rw [← e]
    exact mem_honestEval_snd (mem_queries_messageDigest _ _ _ _)
  obtain ⟨p, hp, hp1⟩ := List.mem_map.1 hmem
  have hroute : hmsgRoute (p.1, false) = (p.1, false) :=
    hmsgRoute_of_ne (by rw [hp1, hx0]; exact fun h ↦ by cases h)
  have hω := hU p hp
  rw [hroute, hp1] at hω
  have hdF : i.2.1 = digestOfPair p.2 := by
    have e : (honestEval (regroup hmsgRoute (viewP (unionH (projQ s)))) (mdI i.1)).1 = i.2.1 :=
      congrArg Prod.fst hE
    rw [← e]
    change (honestEval (regroup hmsgRoute (viewP (unionH (projQ s))))
      (LeanSphincsOver.messageDigest Qrom.hashQ i.1.1 i.1.2.1.1.signature.randomizer
        i.1.2.1.1.message)).1 = _
    rw [fst_honestEval_messageDigest, viewP, hω, Option.getD_some]
  -- The ITSR event on the data.
  have hI : ItsrHolds i.2.1 i.1.2.1.1.signature.randomizer i.1.2.1.1.message i.1.2.2 := by
    have h := hw
    unfold winI itsrDecT at h
    rw [Bool.or_eq_true, decide_eq_true_iff] at h
    exact Props.holds_eq_true.mp (h.resolve_left (by omega))
  obtain ⟨hfresh, hcov⟩ := hI
  -- The cell is not hardwired.
  have hnw : s.2.1.1 (digestCell i.1.1.publicSeed i.1.1.root i.1.2.1.1.signature.randomizer
      i.1.2.1.1.message 0) = none := by
    cases hw0 : s.2.1.1 (digestCell i.1.1.publicSeed i.1.1.root
      i.1.2.1.1.signature.randomizer i.1.2.1.1.message 0) with
    | none => rfl
    | some y =>
      exfalso
      obtain ⟨m, hm, hxm, -⟩ := hD s.1 _ y hx0 hw0
      have hpkw : i.1.1 = (runTab θ s.2.2.1).publicKey :=
        hpk.trans (runTab_publicKey θ s.2.2.1).symm
      rw [hpkw] at hxm
      have hsl := cell_injective ((runTab θ s.2.2.1).expandedKey (seedOf θ))
        (runTab θ s.2.2.1).root (s := .hmsg i.1.2.1.1.signature.randomizer i.1.2.1.1.message 0)
        (s' := .hmsg ((runTab θ s.2.2.1).randomizer m) m 0) trivial trivial (p := ()) (p' := ())
        hxm
      obtain ⟨hR, hMr, -⟩ := Quantum.Sphincs.Slot.hmsg.inj (congrArg Sigma.fst hsl)
      have hm' : m ∈ i.1.2.2.map Prod.fst := by
        rw [hmsgs, logMsgsT, List.take_of_length_le (by rw [List.length_map]; exact hlen)]
        exact hm
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hm'
      refine hfresh (List.mem_map.2 ⟨d, hd, ?_⟩)
      rw [hR, hMr, (hdat d hd).1, (runTab_offDig θ s.2.2.1).randomizer]
  refine mem_badRQ_iff.mpr (mem_badQ_of_cov hω hx0 hnw ?_)
  rw [hdF] at hcov
  exact covered_of_cells (fun d hd ↦ (hdat d hd).2) hcov

variable (A : SAdversary) (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) signChargeQ signatureLimit)
  (θ : TVals)

/-- **A winning run**: the branch of the logging reads at the run after the prefix's, when the
game wins on it; `0` otherwise. -/
noncomputable def σI (i : RunI) : Matrix (Unit × RRegS SelMem) (Unit × RRegS SelMem) ℂ :=
  runSig m0H (prefixIQ strPol A θ) (fun y ↦ wReadsI θ y) (fun y (a : ReadsOutI) ↦ winI y a) i

include hsign in
/-- **A winning run in the decompressed basis**: the prefix's facts, and the run is the honest
digest against the view, with its answers. -/
theorem dec_σI (i : RunI) :
    QuerySupportedOn (fun p : Unit × RRegS SelMem ↦ p.2)
      {s | winI i.1 i.2 = true ∧ PreFactsI θ i.1 s ∧ i.2 = honestEvalV (hvwS s) (mdI i.1)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem)) (σI A θ i)) :=
  querySupportedOn_conj_runSig (prefixIQ strPol A θ) (fun y ↦ wReadsI θ y)
    (fun y (a : ReadsOutI) ↦ winI y a) (fun y ↦ {s | PreFactsI θ y s})
    (fun y a ↦ {s | PreFactsI θ y s ∧ a = honestEvalV (hvwS s) (mdI y)})
    (fun y ↦ prefixFactsI θ A hsign y)
    (fun y ↦ htS₂_readsProgramV m0H θ (QReg.of Unit) _ (fun _ ↦ isHash_messageDigest _ _ _)
      {s | PreFactsI θ y s} (fun _ hs ↦ hs.1.2.1)) i

include hsign in
/-- **Recorded**: in the decompressed basis, no empty cell, and the view holds the log. -/
theorem recorded_σI (i : RunI) :
    QuerySupportedOn (fun y : Unit × RRegS SelMem ↦ y.2)
      {s | NoBotDb s.1 ∧ DbReg.Agrees (wLogI i.2.2) (hwView s.2.1 s.1)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem)) (σI A θ i)) :=
  (dec_σI A hsign θ i).mono fun s hs ↦ by
    obtain ⟨-, ⟨⟨-, hnb, -⟩, -⟩, he⟩ := hs
    have e2 := congrArg Prod.snd he
    refine ⟨hnb, agrees_wLogI fun p hp ↦ ?_⟩
    rw [e2] at hp
    rw [snd_eq_of_mem_trace_hashReadV hp]
    exact hwView_eq_some_hvwS hnb _

include hsign in
/-- **The run's classical facts**, in the decompressed basis. -/
theorem facts_σI (i : RunI) :
    QuerySupportedOn (fun y : Unit × RRegS SelMem ↦ y.2) {s | RunFactsI θ i s.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem)) (σI A θ i)) :=
  (dec_σI A hsign θ i).mono fun s hs ↦ by
    obtain ⟨hw, ⟨⟨hpk, -, -, -, -, hD, -⟩, hlen, hmsgs, hdat⟩, he⟩ := hs
    have e1 := congrArg Prod.fst he
    have e2 := congrArg Prod.snd he
    refine ⟨hw, ?_, fun F' hF' ↦ ?_, hpk, hlen, hmsgs, hdat, fun _ ↦ hD⟩
    · rw [e2]
      exact length_trace_hashReadV_le _ (messageDigest_cost _ _ _)
    · simp only [honestEvalV] at e1 e2
      rw [e1, e2, map_fst_trace_hashReadV]
      exact honestEval_eq_of_agree _ fun p hp ↦ hF' p (e2 ▸ hp)

include hsign in
/-- **In the event**: in the compressed basis, a view holding the log is in `BadRQ`. -/
theorem bad_σI (i : RunI) :
    QuerySupportedOn (fun y : Unit × RRegS SelMem ↦ y.2)
      {s | DbReg.Agrees (wLogI i.2.2) (hwView s.2.1 s.1) →
        s ∈ BadRQ (pkQ θ) (honQ θ) (starQ θ)} (σI A θ i) :=
  (querySupportedOn_of_conj_compressReg (P := RunFactsI θ i) (facts_σI A hsign θ i)).mono
    fun _ hf ha ↦ mem_badRQ_of_runFactsI θ i hf ha

/-- The weight of the game's winning branch, run by run. -/
theorem ofReal_trace_conj_gameIQ
    (K : Matrix (Unit × RRegS SelMem) (Unit × RRegS SelMem) ℂ) :
    ENNReal.ofReal (MatrixMap.conj K (((runtimeR m0H).run₂ .instruments
      (gameIQ strPol A θ)).branch true (initU m0H))).trace.re =
      ∑' p, ENNReal.ofReal (MatrixMap.conj K (σI A θ p)).trace.re := by
  rw [gameIQ_eq]
  exact ofReal_trace_conj_runSig m0H (prefixIQ strPol A θ) (fun y ↦ wReadsI θ y)
    (fun y (a : ReadsOutI) ↦ winI y a) K

open Classical in
/-- **The decomposition of runtime 2's winning runs along the forgery's two digest reads.** -/
noncomputable def winDecompI :
    WinDecomp m0H (gameIQ strPol A θ) (gameIQ strPol A θ) (BadRQ (pkQ θ) (honQ θ) (starQ θ))
      2 0 0 where
  ι := RunI
  σ := σI A θ
  log i := wLogI i.2.2
  psd i := runSig_posSemidef m0H _ _ _ i
  countH i := readCount_wLogI_le _
  countK i := (readCount_wLogI_eq_zero _ (by decide)).le
  countK' i := (readCount_wLogI_eq_zero _ (by decide)).le
  recorded i := recorded_σI A hsign θ i
  bad i := bad_σI A hsign θ i
  win := by
    rw [evalDistMap_winBit]
    have h := ofReal_trace_conj_gameIQ A θ 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.le
  event := (ofReal_trace_conj_gameIQ A θ _).symm.le.trans
    (trace_conj_branch_true_le_eventWeight m0H (gameIQ strPol A θ) _)
  mass := by
    have h := ofReal_trace_conj_gameIQ A θ 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.symm.le.trans (ofReal_trace_branch_le_one m0H (gameIQ strPol A θ) true)

/-- The read error of the forgery's two digest reads. -/
noncomputable def readErrI : ℝ≥0∞ :=
  ENNReal.ofReal (readError PairOut Qrom.HashDomain 2 0 0)

include hsign in
open Classical in
/-- **Runtime 2's ITSR win is at most the event at the end of the game and the read error.** -/
theorem p2I_le_eventWeight :
    p2I strPol A θ ≤ (runtimeR m0Q).eventWeight .instruments
      (hwProjector (BadRQ (pkQ θ) (honQ θ) (starQ θ))) (gameIQ strPol A θ) initQ + readErrI :=
  win_le_of_winDecomp (winDecompI A hsign θ)

end decomp

end Quantum.StdModel.Sphincs.SphItsr

end
