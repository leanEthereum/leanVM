module

public import Quantum.StdModel.Qrom.SphincsItsrGame
public import Quantum.Qrom.Sphincs.End

@[expose] public section

/-!
# The facts of the ITSR game's prefix with the data, at the event side's policy

On every branch of the ITSR game's prefix with the data (`prefixIQ strPol A θ`, `SphincsItsrGame`),
in the decompressed basis, the register satisfies the challenge prefix's facts (`PreFactsS`,
GameTFactsPre) and each signed message's datum is the honest one.

* **One datum** (`invS_fold`, `htS₂_foldS`): the data's step reveals `PK.seed`, `PK.root`, `R(M)`
  and the digest policy's coordinates of a signed message and hardwires its digest cell. Within
  the signing budget a signed message is marked, so the digest cell gets the stream pair already
  at its digest coordinate: the invariant `InvS` of the transcript is kept. Its datum is
  `(M, R(M), digestOfPair ω)` with `ω` the marked stream pair, whose view `S★` covers
  (`DatumOk`, `datumOk_of_invS`).
* **The prefix with the data** (`PreFactsI`, `htS₂_prefixI`, `prefixFactsI`): the prefix's facts,
  a transcript within the signing budget, the data's messages the transcript's and each datum
  `DatumOk`.
* **The forgery's digest** (`fst_honestEval_messageDigest`, `mem_queries_messageDigest`): against
  a regrouped function `F` it is `digestOfPair (F x₀)`, `x₀` the call-0 cell, which it hashes.
* **Coverage** (`covered_of_cells`): a digest of a pair whose cells the data's digests cover has
  a view covered by `S★`.
-/

open OracleComp OracleSpec
open Matrix IPFunctor
open scoped Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Qrom.Sphincs
open Quantum.SufCma (QueriesSatisfy queries trace_query_bind)
open Quantum.Qrom.Xmss (romAnswers honestEval)
open Quantum.Qrom (regroup RomOracles)
open Quantum.Xmss.Hybrid (progUpdate restrictTo)
open Quantum.Sphincs (Covered Disclosures)
open Quantum.Xmss.Assembly (recHwSpec realizeT revealThen progThen runtimeR NoBot initU)

local notation "signChargeQ" => Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## One datum -/

section fold

/-- **The facts of a signed message's datum**: the table's randomizer of its message, and the
digest of a pair whose view `S★` covers. -/
def DatumOk (θ : TVals) (d : ItsrDatum) : Prop :=
  d.2.1 = (tabOf θ).randomizer d.1 ∧ ∃ ω, d.2.2 = digestOfPair ω ∧ Covered (starQ θ) (pairView ω)

variable {θ : TVals} {log : SLogS} {msg : Message}

/-- **A signed message is marked** within the signing budget: its stream entry is its mark. -/
theorem streamIdx_of_logged {s : RRegS SelMem} (hs : s ∈ InvS θ log)
    (hlen : log.length ≤ signatureLimit) (hm : msg ∈ log.map Sigma.fst) :
    ∃ j, streamIdx s.2.2.1 msg = some j ∧ SPos.asg msg j ∈ s.2.2.1 := by
  obtain ⟨-, hok, -⟩ := hs
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
  obtain ⟨j₀, hj₀⟩ : ∃ j, SPos.asg q.1 j ∈ s.2.2.1 := by
    rcases hok.2.2.2 q hq with h | ⟨-, hlt⟩
    · exact h
    · omega
  rcases h : streamIdx s.2.2.1 q.1 with _ | j
  · exact absurd hj₀ ((streamIdx_none_facts' h).1 j₀)
  · rcases streamIdx_some_facts' h with hj | ⟨hf, -⟩
    · exact ⟨j, rfl, hj⟩
    · exact absurd hj₀ (hf j₀)

/-- **The datum of a signed message** at a register of the invariant is honest. -/
theorem datumOk_of_invS {s : RRegS SelMem} (hs : s ∈ InvS θ log)
    (hlen : log.length ≤ signatureLimit) (hm : msg ∈ log.map Sigma.fst) :
    DatumOk θ (msg, (tabOf θ).randomizer msg, digestOfPair (dgS θ s.2.2.1 msg)) := by
  obtain ⟨j, hj, -⟩ := streamIdx_of_logged hs hlen hm
  refine ⟨rfl, dgS θ s.2.2.1 msg, rfl, ?_⟩
  unfold dgS
  rw [strOut_some hj]
  exact covered_starCover (streamOf θ) j

/-- **One datum keeps the invariant**: the reveals and the digest cell's program of a signed
message, within the signing budget. -/
theorem invS_fold {s s' : RRegS SelMem} (hs : s ∈ InvS θ log)
    (hlen : log.length ≤ signatureLimit) (hm : msg ∈ log.map Sigma.fst)
    (hp : ProgRelS (cellQ θ (digPos msg)) (dgS θ s.2.2.1 msg)
      (s.1, s.2.1, (s.2.2.1 ∪ {seedC, rootC, rndC msg} ∪ strNeed s.2.2.1 msg, s.2.2.2)) s') :
    s' ∈ InvS θ log := by
  obtain ⟨j, hj, hasg⟩ := streamIdx_of_logged hs hlen hm
  obtain ⟨hnb, hok, hF⟩ := hs
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hW : s'.2.1 = progUpdate (.programH (cellQ θ (digPos msg)) (dgS θ s.2.2.1 msg)) s.2.1 :=
    congrArg Prod.fst hp1
  have hL : s'.2.2.1 = s.2.2.1 ∪ {seedC, rootC, rndC msg} ∪ strNeed s.2.2.1 msg :=
    congrArg (·.2.1) hp1
  have hmem : s'.2.2.2 = s.2.2.2 := congrArg (·.2.2) hp1
  have hnew : ∀ t ∈ s'.2.2.1, t ∈ s.2.2.1 ∨ t.IsVal ∨ t = .str j := by
    intro t ht
    rw [hL] at ht
    rcases Finset.mem_union.1 ht with ht | ht
    · rcases Finset.mem_union.1 ht with ht | ht
      · exact .inl ht
      · exact .inr (.inl (valOnly_sigReveal msg t ht))
    · rcases (mem_strNeed_some hj t).1 ht with rfl | rfl
      · exact .inr (.inr rfl)
      · exact .inl hasg
  have hsub : s.2.2.1 ⊆ s'.2.2.1 := by
    rw [hL]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  have hasg' : ∀ m j', SPos.asg m j' ∈ s'.2.2.1 → SPos.asg m j' ∈ s.2.2.1 := fun m j' h ↦ by
    rcases hnew _ h with h | h | h
    · exact h
    · exact h.elim
    · cases h
  have hdig' : ∀ m, SPos.dig m ∈ s'.2.2.1 → SPos.dig m ∈ s.2.2.1 := fun m h ↦ by
    rcases hnew _ h with h | h | h
    · exact h
    · exact h.elim
    · cases h
  obtain ⟨h1, h2, h3, h4⟩ := hok
  have hok' : StrOk s'.2.2.1 log :=
    ⟨fun m j₁ j₂ a b ↦ h1 m j₁ j₂ (hasg' _ _ a) (hasg' _ _ b),
      fun m j₁ a ↦ h2 m j₁ (hasg' _ _ a),
      fun m hd ↦ ⟨(h3 m (hdig' m hd)).1.trans (asgCount_mono hsub),
        fun j₁ a ↦ (h3 m (hdig' m hd)).2 j₁ (hasg' _ _ a)⟩,
      fun q hq ↦ (h4 q hq).imp (fun ⟨j₁, a⟩ ↦ ⟨j₁, hsub a⟩) fun ⟨a, b⟩ ↦ ⟨hsub a, b⟩⟩
  refine ⟨hp2 hnb, hok', fun w hw ↦ ?_⟩
  obtain ⟨hlog, hrec, hmok, hhw⟩ := hF w (compatS_anti hw hok' hsub)
  have hea : EncAgree w.publicSeed (hHS s) (hHS s') := fun l τ e m c ↦ by
    rw [hw.1.publicSeed]
    have hz : encCell (tabOf θ).publicSeed l τ e m c ≠ cellQ θ (digPos msg) :=
      fun h ↦ cellQ_ne_encCell θ _ l τ e m c h.symm
    refine congrArg Prod.fst (hvwS_congr (s := s) (s' := s') ?_ (hp3 _ hz)).symm
    rw [hW, progUpdate_programH_fst, Function.update_of_ne hz]
  refine ⟨fun q hq ↦ (hlog q hq).trans (signature_congrH hea q.1), fun q hq ↦ ?_, ?_,
    fun z ω hz ↦ ?_⟩
  · rw [hmem]
    exact records_congrH hea (hrec q hq)
  · rw [hmem]
    exact memOkS_congrH hea hmok
  · by_cases hzd : z = cellQ θ (digPos msg)
    · subst hzd
      rw [hW, progUpdate_programH_fst, Function.update_self] at hz
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
      refine .inl ⟨q, hq, (hw.1.cellOf (seedOf θ) (digPos q.1)).symm, ?_⟩
      rw [← Option.some.inj hz, hw.2 q.1 (.inl ⟨j, hsub hasg⟩), markC_of_asg hok'.1 (hsub hasg)]
      unfold dgS
      rw [strOut_some hj]
    · rw [hW, progUpdate_programH_fst, Function.update_of_ne hzd] at hz
      rcases hhw z ω hz with h | ⟨q, hq, p, hp, e⟩
      · exact .inl h
      · exact .inr ⟨q, hq, p, pubBy_congrH hea hp, e⟩

variable (θ) {m₀ : Finset TPos × SelMem}

/-- **The data of signed messages** at the event side's policy, within the signing budget, keep
the invariant of the transcript; the data's messages are the given ones, each datum honest. -/
theorem htS₂_foldS (B : QReg) (log : SLogS) (hlen : log.length ≤ signatureLimit) :
    ∀ msgs : List Message, (∀ m ∈ msgs, m ∈ log.map Sigma.fst) →
      HTS₂ m₀ (realizeT θ (foldT SelMem strPol B msgs)) (InvS θ log)
        fun ds ↦ {s | s ∈ InvS θ log ∧ ds.map Prod.fst = msgs ∧ ∀ d ∈ ds, DatumOk θ d}
  | [], _ => htS₂_pure [] fun s hs ↦ ⟨hs, rfl, fun _ h ↦ absurd h List.not_mem_nil⟩
  | msg :: ms, hms => by
    have hm := hms msg List.mem_cons_self
    have ih := htS₂_foldS B log hlen ms fun m h ↦ hms m (List.mem_cons_of_mem _ h)
    rw [foldT]
    refine htS₂_revealThen m₀ θ _ _ _ _ fun mem₁ ↦ ?_
    refine htS₂_revealThen m₀ θ _ _ _ _ fun mem₂ ↦ ?_
    have hd : digestT strPol mem₁.1 msg (restrictTo (strPol.need mem₁.1 msg) θ) =
        digestOfPair (dgS θ mem₁.1 msg) :=
      congrArg digestOfPair (pairR_restrictTo (strPol.out_mem mem₁.1 msg) θ)
    have hr : (digPort strPol mem₁.1 msg).realize θ =
        .programH (cellQ θ (digPos msg)) (dgS θ mem₁.1 msg) := by
      rw [realize_digPort, ← cellOf_digPos (seedOf θ)]
      rfl
    have hR₀ : (tabR (restrictTo {seedC, rootC, rndC msg} θ)).randomizer msg =
        (tabOf θ).randomizer msg :=
      sigTabD_randomizer msg
    dsimp only
    rw [hR₀, hd]
    refine htS₂_progThen m₀ θ _ hr _ _ _ ?_
    by_cases hok : DatumOk θ (msg, (tabOf θ).randomizer msg, digestOfPair (dgS θ mem₁.1 msg))
    · refine htS₂_realizeT_bind m₀ θ (ih.mono ?_ fun _ ↦ subset_rfl) fun ds ↦ htS₂_pure _ ?_
      · rintro s₃ ⟨s₂, ⟨s₁, ⟨s, hs, hmem, rfl⟩, -, rfl⟩, hpr⟩
        subst hmem
        exact invS_fold hs hlen hm hpr
      · rintro s ⟨hs, hds, hdk⟩
        exact ⟨hs, by rw [List.map_cons, hds], List.forall_mem_cons.2 ⟨hok, hdk⟩⟩
    · refine (htS₂_of_empty m₀ _ _).mono ?_ fun _ ↦ subset_rfl
      rintro s₃ ⟨s₂, ⟨s₁, ⟨s, hs, hmem, rfl⟩, -, rfl⟩, -⟩
      subst hmem
      exact absurd (datumOk_of_invS hs hlen hm) hok

end fold

/-! ## The prefix with the data -/

section prefixRun

/-- **The facts of a prefix outcome with the data** `y` on a register `s`: the challenge prefix's
facts (`PreFactsS`), a transcript within the signing budget, the data's messages the
transcript's (`logMsgsT`), each datum honest. -/
def PreFactsI (θ : TVals) (y : PreI) (s : RRegS SelMem) : Prop :=
  PreFactsS θ (y.1, y.2.1) s ∧ y.2.1.2.length ≤ signatureLimit ∧
    y.2.2.map Prod.fst = logMsgsT y.2.1.2 ∧ ∀ d ∈ y.2.2, DatumOk θ d

variable (θ : TVals) {m₀ : Finset TPos × SelMem}

/-- **The prefix with the data**: from registers whose public key reveal gives the invariant, on
every branch the facts `PreFactsI` hold. -/
theorem htS₂_prefixI (A : SAdversary)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) signChargeQ signatureLimit)
    (P₀ : Set (RRegS SelMem))
    (hroot : ∀ s ∈ P₀, (s.1, s.2.1, (s.2.2.1 ∪ pkReveal, s.2.2.2)) ∈ InvS θ []) :
    HTS₂ m₀ (realizeT θ (prefixIT SelMem cwUpd strPol A)) P₀ fun y ↦ {s | PreFactsI θ y s} := by
  unfold prefixIT
  refine htS₂_realizeT_bind m₀ θ (htS₂_prefixS θ A signatureLimit hsign (InvS θ)
    (fun B msg log ↦ htS₂_signInv θ B msg log) P₀ hroot) fun x ↦ ?_
  by_cases hx : x.2.2.length ≤ signatureLimit ∧ x.1 = (tabOf θ).publicKey
  · obtain ⟨hlen, hpk⟩ := hx
    have hall : logMsgsT x.2.2 = x.2.2.map Sigma.fst :=
      List.take_of_length_le (by rw [List.length_map]; exact hlen)
    refine htS₂_realizeT_bind m₀ θ ((htS₂_foldS θ (QReg.of Unit) x.2.2 hlen (logMsgsT x.2.2)
      fun m hm ↦ hall ▸ hm).mono (fun s hs ↦ hs.1) fun _ ↦ subset_rfl) fun ds ↦ htS₂_pure _ ?_
    rintro s ⟨hs, hds, hdk⟩
    exact ⟨preFactsS_of hs hlen hpk, hlen, hds, hdk⟩
  · exact (htS₂_of_empty m₀ _ _).mono (fun s hs ↦ absurd ⟨hs.2.1, hs.2.2⟩ hx)
      fun _ ↦ subset_rfl

/-- **The facts of the canonical prefix with the data**: on every branch `y` of
`prefixIQ strPol A θ`, run against `runtimeR m0H` by an adversary making at most `signatureLimit`
signing requests, in the decompressed basis, the register is supported where `PreFactsI θ y`
holds. -/
theorem prefixFactsI (A : SAdversary)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) signChargeQ signatureLimit) (y : PreI) :
    QuerySupportedOn (fun p : Unit × RRegS SelMem ↦ p.2) {s | PreFactsI θ y s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem))
        (((runtimeR m0H).run₂ .instruments (prefixIQ strPol A θ)).branch y (initU m0H))) := by
  rw [Quantum.Xmss.Assembly.conj_branch₂ m0H (prefixIQ strPol A θ) y (initU m0H)]
  have H := htS₂_prefixI θ (m₀ := m0H) A hsign
    {s | NoBot s ∧ s.2 = (hwEmpty PairOut Qrom.HashDomain, m0H)} fun _ hs ↦ invS_init θ rfl hs
  exact H _ (init_decS m0H) y

end prefixRun

/-! ## The forgery's digest -/

section digest

/-- **The forgery's digest against a regrouped function** `F`: the digest of the pair at its
call-0 cell. -/
theorem fst_honestEval_messageDigest (F : Qrom.HashDomain → PairOut) (pk : PublicKey)
    (R : Randomizer) (msg : Message) :
    (honestEval (regroup hmsgRoute F) (LeanSphincsOver.messageDigest Qrom.hashQ pk R msg)).1 =
      digestOfPair (F (digestCell pk.publicSeed pk.root R msg 0)) := by
  rw [fst_honestEval]
  unfold LeanSphincsOver.messageDigest
  rw [evalWithAnswerFn_bind, Quantum.Xmss.evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure]
  refine congrArg truncateMessageDigest (funext fun c ↦ ?_)
  change evalWithAnswerFn (romAnswers (regroup hmsgRoute F))
    (Qrom.hashQ (Quantum.Sphincs.messageDigestInput R pk.publicSeed pk.root msg c)) = _
  rw [Qrom.hashQ_of_encodeInput_eq_some (encodeInput_digestCell _ _ _ _ c),
    evalWithAnswerFn_liftM_query]
  exact regroup_messageDigestInput F R pk.publicSeed pk.root msg
    (fun i ↦ encodeInput_digestCell _ _ _ _ i) c

/-- **The forgery's digest hashes its call-0 cell.** -/
theorem mem_queries_messageDigest (f : QueryImpl RomOracles Id) (pk : PublicKey)
    (R : Randomizer) (msg : Message) :
    (.inr (digestCell pk.publicSeed pk.root R msg 0) : RomOracles.Domain) ∈
      queries f (LeanSphincsOver.messageDigest Qrom.hashQ pk R msg) := by
  by_contra h
  have hs : QueriesSatisfy f (· ≠ .inr (digestCell pk.publicSeed pk.root R msg 0))
      (LeanSphincsOver.messageDigest Qrom.hashQ pk R msg) := fun q hq he ↦ h (he ▸ hq)
  unfold LeanSphincsOver.messageDigest at hs
  have h0 := Quantum.Xmss.QueriesSatisfy.of_sequenceFin
    (Quantum.Xmss.queriesSatisfy_bind_iff.1 hs).1 0
  change QueriesSatisfy f _
    (Qrom.hashQ (Quantum.Sphincs.messageDigestInput R pk.publicSeed pk.root msg 0)) at h0
  rw [Qrom.hashQ_of_encodeInput_eq_some (encodeInput_digestCell _ _ _ _ 0)] at h0
  have hq := trace_query_bind f (fun t ↦ [t])
    (.inr (digestCell pk.publicSeed pk.root R msg 0) : RomOracles.Domain) pure
  rw [bind_pure] at hq
  exact h0 _ (by rw [queries, hq]; exact List.mem_cons_self) rfl

end digest

/-! ## Coverage -/

section cover

theorem mem_foldr_union {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List (Finset α)}, a ∈ l.foldr (· ∪ ·) ∅ → ∃ t ∈ l, a ∈ t
  | [], h => absurd h (Finset.notMem_empty a)
  | t :: l, h => by
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨t, List.mem_cons_self, h⟩
    · obtain ⟨u, hu, hau⟩ := mem_foldr_union h
      exact ⟨u, List.mem_cons_of_mem _ hu, hau⟩

/-- **Covered cells, covered view**: a pair whose digest's cells the data's digests cover, each
the digest of a pair whose view `S` covers, has a view `S` covers. -/
theorem covered_of_cells {S : Disclosures} {ω : PairOut} {ds : List ItsrDatum}
    (hds : ∀ d ∈ ds, ∃ ω', d.2.2 = digestOfPair ω' ∧ Covered S (pairView ω'))
    (h : digestCells (digestOfPair ω) ⊆ (ds.map fun d ↦ digestCells d.2.2).foldr (· ∪ ·) ∅) :
    Covered S (pairView ω) := fun κ ↦ by
  have hm : (digestIndex (digestOfPair ω), κ, digestForsLeaves (digestOfPair ω) κ) ∈
      digestCells (digestOfPair ω) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ κ)
  obtain ⟨t, ht, hat⟩ := mem_foldr_union (h hm)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ht
  obtain ⟨ω', he, hc⟩ := hds d hd
  rw [he] at hat
  obtain ⟨κ', -, hκ⟩ := Finset.mem_image.1 hat
  simp only [Prod.mk.injEq] at hκ
  obtain ⟨h1, rfl, h3⟩ := hκ
  change digestForsLeaves (digestOfPair ω) κ' ∈ S (digestIndex (digestOfPair ω)) κ'
  rw [← h1, ← h3]
  exact hc κ'

end cover

end Quantum.StdModel.Sphincs.SphItsr

end
