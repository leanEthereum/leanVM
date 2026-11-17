module

public import Quantum.Qrom.Sphincs.GameTFacts

@[expose] public section

/-!
# The classification facts of leanSPHINCS's challenge prefix in the QROM

On every branch of the challenge prefix at the event side's digest policy (`prefixQ strPol`), in
the decompressed basis, the register satisfies the hypotheses of `win_imp_badQ` against the run's
table `runTab θ L` (`L` the register's label) and the view's hash.

* **One signature** (`invS_step`, `htS₂_signInv`): a signature's effect (`SignEff`) keeps the
  invariant `InvS` with the transcript grown by the request.
* **The prefix** (`htS_logSigns`, `htS₂_prefixS`): the substituted adversary moves the invariant
  along its signing transcript, within its signing budget; `invS_init`, `init_decS` start it.
* **The run's table** (`runTab`): the template's table off the digest cells, and at the digest
  cell of `m` the pair at `m`'s digest coordinate (`markC`). It agrees with the template's table
  off the digest cells (`runTab_offDig`), so it has the same public key and honest cells
  (`runTab_publicKey`, `honCell_runTab`).
* **The facts** (`PreFactsS`, `preFactsS_of`, `prefixFactsS`): the transcript's signatures and
  records, the hardwired chain steps and FORS leaves known (`HwKnown`), the hardwired call-0
  `H_msg` cells signed digests (`HwDigests`), and, within the signing budget, every signed view
  covered by `starCover (streamOf θ)`.
-/

open Matrix IPFunctor
open scoped Kronecker
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Slot Key keyOf ValPos cpos Known layerDisclosed forsDisclosed Covered
  treeBits)
open Quantum.Xmss.Hybrid (restrictTo)
open Quantum.Xmss.Assembly (recHwSpec realizeT revealThen runtimeR NoBot initU noBot_init
  querySupportedOn_conj_compressReg querySupportedOn_inter realizeT_substitute decR)

attribute [local irreducible] sphincsRom

/- Instance search for the run families over the register exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The run's table -/

section runTab

/-- The coordinate of a position's value in the run at the label `L`: the digest coordinate
`markC L m` for the digest cell of `m`, the position's own otherwise. -/
noncomputable def runC (L : Finset TPos) (p : Pos) : TPos :=
  match p.1 with
  | .hmsg m => markC L m
  | _ => .val (some p)

/-- **The table of a run at the label `L`**: the template's table off the digest cells, and at the
digest cell of `m` the pair at `m`'s digest coordinate. -/
noncomputable def runTab (θ : TVals) (L : Finset TPos) : QTable :=
  fun p ↦ pairAt θ (runC L p)

variable (θ : TVals) (L : Finset TPos)

theorem runTab_digPos (m : Message) : runTab θ L (digPos m) = pairAt θ (markC L m) :=
  rfl

theorem runTab_offDig : OffDig (runTab θ L) (tabOf θ) := by
  rintro ⟨q, hq⟩ hm
  cases q with
  | hmsg m => exact absurd rfl (hm m)
  | _ => rfl

theorem compatS_runTab : CompatS θ L (runTab θ L) :=
  ⟨runTab_offDig θ L, fun m _ ↦ runTab_digPos θ L m⟩

theorem runTab_publicKey : (runTab θ L).publicKey = (tabOf θ).publicKey :=
  (runTab_offDig θ L).publicKey

theorem slotPos_isStruct {s : Slot} {p : RawPos} (h : slotPos s = some p) : p.IsStruct := by
  unfold slotPos at h
  split at h <;> (try split_ifs at h) <;> (try cases h) <;> trivial

/-- **The run's table has the template's honest cells.** -/
theorem honCell_runTab (S0 : MasterSeed) :
    QTable.honCell S0 (runTab θ L) = QTable.honCell S0 (tabOf θ) := by
  funext s
  unfold QTable.honCell
  rcases h : slotPos s with _ | p
  · rfl
  · have hp : ∀ m, p ≠ .hmsg m := fun m hm ↦ by
      have := slotPos_isStruct h
      rw [hm] at this
      exact this
    simp only [Option.bind_some]
    split_ifs
    · rw [(runTab_offDig θ L).cellOf, (runTab_offDig θ L).dig hp]
    · rfl

end runTab

/-! ## One signature keeps the invariant -/

section step

/-- **One signature keeps the invariant**, from its effect on the decompressed register. -/
theorem invS_step {θ : TVals} {log : SLogS} {msg : Message} {s s' : RRegS SelMem}
    {sig : Option Signature} (hs : s ∈ InvS θ log) (he : SignEff θ msg s sig s') :
    s' ∈ InvS θ (log ++ [⟨msg, sig⟩]) := by
  obtain ⟨-, hok, hF⟩ := hs
  obtain ⟨hnb, henc, hsub, hnew, hstr, hmem, hsig, hW⟩ := he
  have hok' : StrOk s'.2.2.1 (log ++ [⟨msg, sig⟩]) := strOk_step hnew hok hsub hstr
  refine ⟨hnb, hok', fun w hw ↦ ?_⟩
  obtain ⟨hlog, hrec, hmok, hhw⟩ := hF w (compatS_anti hw hok' hsub)
  have hea : EncAgree w.publicSeed (hHS s) (hHS s') := fun l τ e m c ↦ by
    rw [hw.1.publicSeed]
    exact congrArg Prod.fst (henc l τ e m c).symm
  have hdig : w (digPos msg) = dgS θ s.2.2.1 msg := by
    obtain ⟨hm, hp⟩ := pairAt_markC_step hok' hstr
    exact (hw.2 msg hm).trans hp
  have hidx : w.index msg = idxS θ s.2.2.1 msg :=
    congrArg (fun y ↦ digestIndex (digestOfPair y)) hdig
  have hlv : w.leaves msg = lvS θ s.2.2.1 msg :=
    congrArg (fun y ↦ digestForsLeaves (digestOfPair y)) hdig
  rw [← hidx] at hmem
  have hsigN : sig = w.signature (hHS s) msg := by
    rw [signature_eq_sigOf3, hidx, hlv, hw.1.randomizer, hw.1.forsOpening, hw.1.layerSig,
      hw.1.layerSig, hw.1.layerSig]
    exact hsig
  have hrecN : Records w (hHS s) s'.2.2.2 msg := by
    intro l sel hls
    rw [hmem]
    have e1 : (tabOf θ).layerSelect (hHS s) (w.index msg) l = some sel :=
      (hw.1.layerSelect _ _ _).symm.trans hls
    rcases hk : s.2.2.2 (keyOf l (w.index msg)) with _ | c
    · rw [grind3_key θ _ _ l hk]
      exact (congrArg (Option.map _) e1).trans
        (congrArg some (recOfS_offDig hw.1 (hHS s) l (w.index msg) sel).symm)
    · obtain ⟨l', idx', sel', hK, hs', rfl⟩ := hmok _ c hk
      obtain rfl : l' = l := congrArg Prod.fst hK
      rw [layerSelect_congr hK, hls] at hs'
      obtain rfl := Option.some.inj hs'
      rw [grind3_of_ne_none θ _ _ (by rw [hk]; exact Option.some_ne_none _), hk]
      exact congrArg some (recOfS_key hK sel)
  have hmokN : MemOkS w (hHS s) s'.2.2.2 := by
    intro K c hc
    rw [hmem] at hc
    by_cases hK0 : s.2.2.2 K = none
    · by_cases hK : ∃ l, K = keyOf l (w.index msg)
      · obtain ⟨l, rfl⟩ := hK
        rw [grind3_key θ _ _ l hK0] at hc
        obtain ⟨sel, hsel, rfl⟩ := Option.map_eq_some_iff.1 hc
        exact ⟨l, w.index msg, sel, rfl, (hw.1.layerSelect _ _ _).trans hsel,
          (recOfS_offDig hw.1 (hHS s) l (w.index msg) sel).symm⟩
      · rw [grind3_of_ne θ _ _ (fun l h ↦ hK ⟨l, h⟩), hK0] at hc
        cases hc
    · rw [grind3_of_ne_none θ _ _ hK0] at hc
      exact hmok K c hc
  have hmem' : ∀ q, q ∈ log ++ [⟨msg, sig⟩] → q ∈ log ∨ q = ⟨msg, sig⟩ := fun q hq ↦
    (List.mem_append.1 hq).imp_right List.mem_singleton.1
  have hlast : (⟨msg, sig⟩ : (_ : Message) × Option Signature) ∈ log ++ [⟨msg, sig⟩] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨fun q hq ↦ ?_, fun q hq ↦ ?_, memOkS_congrH hea hmokN, fun z ω hz ↦ ?_⟩
  · rcases hmem' q hq with hq | rfl
    · rw [hlog q hq, signature_congrH hea]
    · exact hsigN.trans (signature_congrH hea msg)
  · refine records_congrH hea ?_
    rcases hmem' q hq with hq | rfl
    · intro l sel hls
      have h0 := hrec q hq l sel hls
      rw [hmem, grind3_of_ne_none θ _ _ (by rw [h0]; exact Option.some_ne_none _), h0]
    · exact hrecN
  · rcases hW z ω hz with h | ⟨rfl, rfl⟩ | ⟨sel₀, sel₁, sel₂, h0, h1, h2, p, hp, rfl⟩
    · rcases hhw z ω h with ⟨q, hq, e1, e2⟩ | ⟨q, hq, p, hp, e1⟩
      · exact .inl ⟨q, List.mem_append_left _ hq, e1, e2⟩
      · exact .inr ⟨q, List.mem_append_left _ hq, p, pubBy_congrH hea hp, e1⟩
    · exact .inl ⟨⟨msg, sig⟩, hlast, (hw.1.cellOf (seedOf θ) (digPos msg)).symm, hdig.symm⟩
    · have hpub : PubBy w (hHS s) msg p := by
        unfold PubBy
        rw [hidx, hlv, hw.1.layerSelect, hw.1.layerSelect, hw.1.layerSelect]
        exact ⟨sel₀, sel₁, sel₂, h0, h1, h2, hp⟩
      exact .inr ⟨⟨msg, sig⟩, hlast, p, pubBy_congrH hea hpub,
        (hw.1.cellOf (seedOf θ) p).symm⟩

variable (θ : TVals) {m₀ : Finset TPos × SelMem}

/-- **A signature at the event side's policy keeps the invariant `InvS`.** -/
theorem htS₂_signInv (B : QReg) (msg : Message) (log : SLogS) :
    HTS₂ m₀ (realizeT θ (signT SelMem cwUpd strPol B msg)) (InvS θ log)
      fun sig ↦ InvS θ (log ++ [⟨msg, sig⟩]) :=
  (htS₂_signS θ B msg (InvS θ log) fun _ hs ↦ hs.1).mono subset_rfl fun _ ↦ by
    rintro s' ⟨s, hs, he⟩
    exact invS_step hs he

end step

/-! ## The challenge prefix -/

section prefixRun

variable (θ : TVals) {m₀ : Finset TPos × SelMem}

-- The adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "AdvP" => QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec

theorem length_logAfter_le {A : QReg} (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A)
    (b : c.Resp) (log : SLogS) :
    (SufCma.logAfter c b log).length ≤ log.length + SufCma.cmdCharge SufCma.signCharge A c := by
  rcases c with o | ⟨_ | r, E, ℓ⟩ <;>
    simp [SufCma.logAfter, SufCma.cmdCharge, SufCma.signCharge]

/-- **The substituted adversary with its signing log**, within a signing budget: from a log of
length at most `K` less the remaining budget `n`, sponge-only steps keep `Inv log`, a signing
request moves it to the extended log. -/
theorem htS_logSigns (K : ℕ) (Inv : SLogS → Set (RRegS SelMem))
    (hsign : ∀ (B : QReg) (msg : Message) (log : SLogS),
      HTS₂ m₀ (realizeT θ (signT SelMem cwUpd strPol B msg)) (Inv log)
        (fun sig ↦ Inv (log ++ [⟨msg, sig⟩])))
    {Ω Y : QReg → Type} (leaf : ∀ u, Ω u → SLogS → Y u) (Q : (Σ u, Y u) → Set (RRegS SelMem))
    (hleaf : ∀ u y log, log.length ≤ K → Inv log ⊆ Q ⟨u, leaf u y log⟩) {A : QReg}
    (x : IPFunctor.IFreeM AdvP Ω A) (n : ℕ)
    (hx : IFreeM.IsChargeBound x (SufCma.cmdCharge SufCma.signCharge) n) (log : SLogS)
    (hn : log.length + n ≤ K) :
    HTS m₀ ((SufCma.logSigns leaf x log).substitute fun A c ↦
      realizeT θ (challengeT SelMem cwUpd strPol A c)) (Inv log) Q := by
  induction x using IPFunctor.IFreeM.inductionOn generalizing n log with
  | pure u y => exact htS_pure (leaf u y log) (hleaf u y log (by omega))
  | liftBind s c next ih =>
    obtain ⟨hc, hnext⟩ := (IFreeM.isChargeBound_liftBind_iff _ _ _).1 hx
    refine HTS.bind (x := realizeT θ (challengeT SelMem cwUpd strPol s c))
      (Q := fun p ↦ Inv (SufCma.logAfter c p.2.1 log)) ?_ fun u ans ↦ ?_
    · rcases c with o | ⟨_ | r, E, ℓ⟩
      · exact htS_sponge m₀ θ _ (Inv log)
      · exact htS_sponge m₀ θ _ (Inv log)
      · have hs : HTS₂ m₀ (realizeT θ (signAt SelMem cwUpd strPol r E ℓ))
            (Inv log) fun sig ↦ Inv (log ++ [⟨r, sig⟩]) :=
          htS₂_realizeT_bind m₀ θ (htS₂_act _ _) fun _ ↦ hsign _ r log
        exact htS_realizeT_bind m₀ θ (htS_of_htS₂ hs) fun _ l ↦ htS_pure _ subset_rfl
    · obtain ⟨b, hb⟩ := ans
      subst hb
      have hl := length_logAfter_le c b log
      exact ih b _ (hnext b) (SufCma.logAfter c b log) (by omega)

/-- **The challenge prefix**: the public key revealed, then the adversary, within its signing
budget `K`, against the challenger with its signing log, moving `Inv log` along the log; it
returns the template's public key and a log of at most `K` requests. -/
theorem htS₂_prefixS (A : SAdversary) (K : ℕ)
    (hA : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) K)
    (Inv : SLogS → Set (RRegS SelMem))
    (hsign : ∀ (B : QReg) (msg : Message) (log : SLogS),
      HTS₂ m₀ (realizeT θ (signT SelMem cwUpd strPol B msg)) (Inv log)
        (fun sig ↦ Inv (log ++ [⟨msg, sig⟩])))
    (P₀ : Set (RRegS SelMem))
    (hroot : ∀ s ∈ P₀, (s.1, s.2.1, (s.2.2.1 ∪ pkReveal, s.2.2.2)) ∈ Inv []) :
    HTS₂ m₀ (realizeT θ (prefixT SelMem cwUpd strPol A)) P₀
      (fun pre ↦ {s | s ∈ Inv pre.2.2 ∧ pre.2.2.length ≤ K ∧ pre.1 = (tabOf θ).publicKey}) := by
  unfold prefixT
  refine htS₂_revealThen m₀ θ _ _ P₀ _ fun mem ↦ ?_
  dsimp only
  refine htS₂_realizeT_bind m₀ θ (Q := fun run ↦ {s | s ∈ Inv run.2 ∧ run.2.length ≤ K}) ?_
    fun run ↦ htS₂_pure _ fun s hs ↦ ⟨hs.1, hs.2, pkD_eq (θ := θ)⟩
  refine htS₂_of_htS (HTS.mono (P := Inv []) ?_ ?_ fun _ ↦ subset_rfl)
  · have e := realizeT_substitute (good := goodQ) (M := SelMem) θ
      (challengeT SelMem cwUpd strPol)
      (SufCma.withSignLog (A (tabR (restrictTo pkReveal θ)).publicKey))
    refine (congrArg (fun y ↦ HTS m₀ y (Inv [])
      fun p ↦ {s | s ∈ Inv p.2.2.2 ∧ p.2.2.2.length ≤ K}) e).mpr ?_
    exact htS_logSigns θ K Inv hsign (Ω := QuantumComp₂.Leaf (QReg.of Unit) Forgery)
      (fun _ l log ↦ ⟨l.1, (l.2, log)⟩)
      (fun q : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) (Forgery × SLogS) u) ↦
        {s | s ∈ Inv q.2.2.2 ∧ q.2.2.2.length ≤ K})
      (fun _ _ _ hl _ hs ↦ ⟨hs, hl⟩) _ K (hA _) []
      (Nat.zero_add K).le
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hroot s₀ hs₀

/-- A label of value coordinates keeps the stream bookkeeping of the empty transcript. -/
theorem strOk_nil {L : Finset TPos} (hL : ValOnly L) : StrOk L [] :=
  ⟨fun m j _ hj _ ↦ absurd hj (hL.asg m j), fun m j hj ↦ absurd hj (hL.asg m j),
    fun m hd ↦ absurd hd (hL.dig m), fun _ hq ↦ absurd hq List.not_mem_nil⟩

/-- **The invariant after the public key's reveal**, from no empty cell, no hardwired cell, an
empty label and no selection. -/
theorem invS_init (hm₀ : m₀ = (∅, fun _ ↦ none)) {s : RRegS SelMem}
    (hs : NoBot s ∧ s.2 = (hwEmpty PairOut Qrom.HashDomain, m₀)) :
    (s.1, s.2.1, (s.2.2.1 ∪ pkReveal, s.2.2.2)) ∈ InvS θ [] := by
  obtain ⟨hnb, hs2⟩ := hs
  subst hm₀
  have hW : s.2.1 = hwEmpty PairOut Qrom.HashDomain := congrArg Prod.fst hs2
  have hL : s.2.2.1 = ∅ := congrArg (·.2.1) hs2
  have hM : s.2.2.2 = fun _ ↦ none := congrArg (·.2.2) hs2
  refine ⟨noBot_of_fst_eq rfl hnb, strOk_nil ?_, fun w _ ↦ ⟨fun _ hq ↦ absurd hq List.not_mem_nil,
    fun _ hq ↦ absurd hq List.not_mem_nil, fun K c hc ↦ ?_, fun z ω hz ↦ ?_⟩⟩
  · show ValOnly (s.2.2.1 ∪ pkReveal)
    rw [hL, Finset.empty_union]
    exact valOnly_pkReveal
  · change s.2.2.2 K = some c at hc
    rw [hM] at hc
    cases hc
  · change s.2.1.1 z = some ω at hz
    rw [hW] at hz
    exact absurd hz (by simp [hwEmpty, Database.empty])

/-- **The initial operator in the decompressed basis**: no empty cell, no hardwired cell, memory
`m₀`. -/
theorem init_decS (m₀ : Finset TPos × SelMem) :
    QuerySupportedOn (fun p : Unit × RRegS SelMem ↦ p.2)
      {s | NoBot s ∧ s.2 = (hwEmpty PairOut Qrom.HashDomain, m₀)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem)) (initU m₀)) := by
  have h0 : QuerySupportedOn (fun p : Unit × RRegS SelMem ↦ p.2)
      {s | s.2 = (hwEmpty PairOut Qrom.HashDomain, m₀)} (initU m₀) := by
    intro m m' hm
    change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty PairOut Qrom.HashDomain, m₀) : RRegS SelMem)).matrix) m m' ≠ 0
      at hm
    simp only [SubState.matrix_basis] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨congrArg Prod.snd he.1.symm, congrArg Prod.snd he.2.symm⟩
    · exact absurd rfl h
  exact querySupportedOn_inter (noBot_init m₀ (A := Unit) (SubState.basis ()).matrix)
    (querySupportedOn_conj_compressReg
      (P := fun b ↦ b = (hwEmpty PairOut Qrom.HashDomain, m₀)) h0)

end prefixRun

/-! ## The facts of the prefix -/

section facts

/-- A chain value known at `j` is known at every later position of the chain. -/
theorem known_cpos_le {D : Set ValPos} {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    {i : ChainIndex} {j : ℕ} (hin : τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l)
    (h : Known D (cpos l τ e i j)) : ∀ k, j + k < chainLength → Known D (cpos l τ e i (j + k))
  | 0, _ => h
  | k + 1, hk => Known.chain l τ e i ⟨j + k, by omega⟩ hin (known_cpos_le hin h k (by omega))

/-- **A chain step published by a layer signature is known** from the layer's disclosures. -/
theorem known_of_layerPos {D : Set ValPos} {l : Layer} {idx : Index} {x : Encoding}
    (hD : layerDisclosed l (treeOfIndex l idx) (leafOfIndex l idx) x ⊆ D) {l' : Layer}
    {τ : TreeIndex} {e : TreeLeafIndex} {i : ChainIndex} {step : ChainStep}
    (hp : (RawPos.chain l' τ e i step).InRange) (hm : (⟨_, hp⟩ : Pos) ∈ layerPos (keyOf l idx) x) :
    Known D (cpos l' τ e i step.val) := by
  rcases mem_layerPos_cases hm with ⟨i', s', hle, h⟩ | h | ⟨k, j, h, -⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := RawPos.chain.inj h
    have hin : τ.val < 2 ^ treeBits l' ∧ e.val < 2 ^ layerHeight l' := hp
    rw [h1, h2, h3] at hin ⊢
    rw [h4, h5]
    have h0 : Known D (cpos l (treeOfIndex l idx) (leafOfIndex l idx) i' (x i').val) :=
      Known.disclosed _ (hD (Or.inl ⟨i', rfl⟩))
    have hC : chainLength - 1 + 1 = chainLength := rfl
    have hk := known_cpos_le hin h0 (s'.val - (x i').val) (by have := s'.isLt; omega)
    rwa [Nat.add_sub_cancel' hle] at hk
  · cases h
  · cases h

variable {S0 : MasterSeed} {w : QTable} {H : Qrom.HashDomain → HashOutput}

/-- The disclosures of a message all of whose searches succeed. -/
theorem disclosedBy_of_select {M : Message} {sel₀ sel₁ sel₂ : EncodingCounter × Encoding}
    (h0 : w.layerSelect H (w.index M) 0 = some sel₀)
    (h1 : w.layerSelect H (w.index M) 1 = some sel₁)
    (h2 : w.layerSelect H (w.index M) 2 = some sel₂) :
    w.disclosedBy H M = forsDisclosed (w.index M) (w.leaves M) ∪
      layerDisclosed 0 (treeOfIndex 0 (w.index M)) (leafOfIndex 0 (w.index M)) sel₀.2 ∪
      layerDisclosed 1 (treeOfIndex 1 (w.index M)) (leafOfIndex 1 (w.index M)) sel₁.2 ∪
      layerDisclosed 2 (treeOfIndex 2 (w.index M)) (leafOfIndex 2 (w.index M)) sel₂.2 := by
  simp only [QTable.disclosedBy, h0, h1, h2]

theorem isStruct_of_pubBy {M : Message} {p : Pos} (hp : PubBy w H M p) : p.1.IsStruct := by
  obtain ⟨s₀, s₁, s₂, -, -, -, hp | hp | hp | hp⟩ := hp
  · exact isStruct_of_mem_forsPos hp
  · exact isStruct_of_mem_layerPos hp
  · exact isStruct_of_mem_layerPos hp
  · exact isStruct_of_mem_layerPos hp

variable {log : SLogS} {s : RRegS SelMem}
  (hhw : ∀ z ω, s.2.1.1 z = some ω →
    (∃ q ∈ log, z = cellOf S0 (digPos q.1) w ∧ ω = w (digPos q.1)) ∨
      ∃ q ∈ log, ∃ p, PubBy w H q.1 p ∧ z = cellOf S0 p w)
include hhw

/-- **The hardwired call-0 `H_msg` cells are signed digests.** -/
theorem hwDigests_of : HwDigests S0 w (s.1, s.2.1, s.2.2.2) (log.map Sigma.fst) := by
  intro x ω hx hz
  rcases hhw x ω hz with ⟨q, hq, e1, e2⟩ | ⟨q, hq, p, hp, rfl⟩
  · exact ⟨q.1, List.mem_map_of_mem hq, e1, e2⟩
  · refine absurd hx (hmsgCall_cellOf_ne_zero S0 w fun m hm ↦ ?_)
    have h := isStruct_of_pubBy hp
    rw [hm] at h
    exact h

-- The linter's `whnf` of the disclosure memberships runs the counter search.
set_option linter.constructorNameAsVariable false in
/-- **Every hardwired chain step and FORS leaf has a known input.** -/
theorem hwKnown_of : HwKnown S0 w H (s.1, s.2.1, s.2.2.2) (log.map Sigma.fst) := by
  have hD : ∀ q ∈ log, w.disclosedBy H q.1 ⊆ w.disclosures H (log.map Sigma.fst) := fun q hq ↦ by
    unfold QTable.disclosures
    exact Set.subset_union_of_subset_right (Set.subset_iUnion₂
      (s := fun m (_ : m ∈ log.map Sigma.fst) ↦ w.disclosedBy H m) q.1
      (List.mem_map_of_mem hq)) _
  refine ⟨fun l τ e i step hp hz ↦ ?_, fun idx κ t hz ↦ ?_⟩
  · obtain ⟨ω, hω⟩ := Option.isSome_iff_exists.1 hz
    rcases hhw _ ω hω with ⟨q, -, e1, -⟩ | ⟨q, hq, p, hpb, e1⟩
    · have h := congrArg Subtype.val ((table S0).inj w e1)
      cases h
    · obtain rfl := (table S0).inj w e1
      obtain ⟨sel₀, sel₁, sel₂, h0, h1, h2, hc⟩ := hpb
      have hd := hD q hq
      rw [disclosedBy_of_select h0 h1 h2] at hd
      rcases hc with hc | hc | hc | hc
      · rcases mem_forsPos_cases hc with ⟨_, h⟩ | ⟨_, _, _, h, -⟩ | h <;> cases h
      · exact known_of_layerPos (fun _ hx ↦ hd (Set.mem_union_left _ (Set.mem_union_left _
          (Set.mem_union_right _ hx)))) hp hc
      · exact known_of_layerPos (fun _ hx ↦ hd (Set.mem_union_left _ (Set.mem_union_right _ hx)))
          hp hc
      · exact known_of_layerPos (fun _ hx ↦ hd (Set.mem_union_right _ hx)) hp hc
  · obtain ⟨ω, hω⟩ := Option.isSome_iff_exists.1 hz
    rcases hhw _ ω hω with ⟨q, -, e1, -⟩ | ⟨q, hq, p, hpb, e1⟩
    · have h := congrArg Subtype.val ((table S0).inj w e1)
      cases h
    · obtain rfl := (table S0).inj w e1
      obtain ⟨sel₀, sel₁, sel₂, h0, h1, h2, hc⟩ := hpb
      have hd := hD q hq
      rw [disclosedBy_of_select h0 h1 h2] at hd
      rcases hc with hc | hc | hc | hc
      · rcases mem_forsPos_cases hc with ⟨_, h⟩ | ⟨_, _, _, h, -⟩ | h
        · obtain ⟨rfl, rfl, rfl⟩ := RawPos.forsLeaf.inj h
          exact Known.disclosed _ (hd (Set.mem_union_left _ (Set.mem_union_left _
            (Set.mem_union_left _ ⟨_, Or.inl rfl⟩))))
        · cases h
        · cases h
      all_goals
        rcases mem_layerPos_cases hc with ⟨_, _, -, h⟩ | h | ⟨_, _, h, -⟩ <;> cases h

end facts

/-- **The facts of a prefix outcome `pre`** on a register `s` (`win_imp_badQ`'s hypotheses on the
projected register `(s.1, s.2.1, s.2.2.2)`, against the run's table `runTab θ s.2.2.1`, the hash
`hHS s` of the register's view, and the stream's disclosures `starCover (streamOf θ)`): the
public key is the template's, no empty cell, the transcript's signatures are the table's, the
memory records every request's selections, every hardwired chain step and FORS leaf has a known
input, every hardwired call-0 `H_msg` cell is a signed digest, and every signed view is covered. -/
def PreFactsS (θ : TVals) (pre : PublicKey × (Forgery × SLogS)) (s : RRegS SelMem) : Prop :=
  pre.1 = (tabOf θ).publicKey ∧ NoBot s ∧
    (∀ q ∈ pre.2.2, q.2 = (runTab θ s.2.2.1).signature (hHS s) q.1) ∧
    (∀ q ∈ pre.2.2, Records (runTab θ s.2.2.1) (hHS s) s.2.2.2 q.1) ∧
    HwKnown (seedOf θ) (runTab θ s.2.2.1) (hHS s) (s.1, s.2.1, s.2.2.2) (pre.2.2.map Sigma.fst) ∧
    HwDigests (seedOf θ) (runTab θ s.2.2.1) (s.1, s.2.1, s.2.2.2) (pre.2.2.map Sigma.fst) ∧
    ∀ q ∈ pre.2.2, Covered (starCover (streamOf θ)) (pairView (runTab θ s.2.2.1 (digPos q.1)))

/-- **The facts from the invariant**, within the signing budget. -/
theorem preFactsS_of {θ : TVals} {pre : PublicKey × (Forgery × SLogS)} {s : RRegS SelMem}
    (hs : s ∈ InvS θ pre.2.2) (hlen : pre.2.2.length ≤ signatureLimit)
    (hpk : pre.1 = (tabOf θ).publicKey) : PreFactsS θ pre s := by
  obtain ⟨hnb, hok, hF⟩ := hs
  obtain ⟨hlog, hrec, -, hhw⟩ := hF _ (compatS_runTab θ s.2.2.1)
  refine ⟨hpk, hnb, hlog, hrec, hwKnown_of hhw, hwDigests_of hhw, fun q hq ↦ ?_⟩
  rcases hok.2.2.2 q hq with ⟨j, hj⟩ | ⟨-, hlt⟩
  · rw [runTab_digPos, markC_of_asg hok.1 hj]
    exact covered_starCover (streamOf θ) j
  · omega

/-- **The classification facts of the canonical prefix**: on every branch `pre` of the challenge
prefix `prefixQ strPol A θ`, run against `runtimeR m₀` from an empty label and no selection by an
adversary making at most `signatureLimit` signing requests, in the decompressed basis, the
register is supported where `PreFactsS θ pre` holds. -/
theorem prefixFactsS (A : SAdversary)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge)
      signatureLimit)
    (m₀ : Finset TPos × SelMem) (hm₀ : m₀ = (∅, fun _ ↦ none)) (θ : TVals)
    (pre : PublicKey × (Forgery × SLogS)) :
    QuerySupportedOn (fun p : Unit × RRegS SelMem ↦ p.2) {s | PreFactsS θ pre s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        compressReg PairOut Qrom.HashDomain (Finset TPos × SelMem))
        (((runtimeR m₀).run₂ .instruments (prefixQ strPol A θ)).branch pre (initU m₀))) := by
  rw [Quantum.Xmss.Assembly.conj_branch₂ m₀ (prefixQ strPol A θ) pre (initU m₀)]
  have H := htS₂_prefixS θ (m₀ := m₀) A signatureLimit hsign (InvS θ)
    (fun B msg log ↦ htS₂_signInv θ B msg log)
    {s | NoBot s ∧ s.2 = (hwEmpty PairOut Qrom.HashDomain, m₀)} fun _ hs ↦ invS_init θ hm₀ hs
  refine (H _ (init_decS m₀) pre).mono ?_
  rintro s ⟨hinv, hlen, hpk⟩
  exact preFactsS_of hinv hlen hpk

end Quantum.Qrom.Sphincs

end
