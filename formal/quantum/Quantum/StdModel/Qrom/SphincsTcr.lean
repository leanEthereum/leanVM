module

public import Quantum.StdModel.Qrom.Tcr2
public import Quantum.StdModel.Qrom.SphincsInst
public import Quantum.StdModel.Qrom.XmssTcr

@[expose] public section

/-!
# The leanSPHINCS SM-TCR-C bound of B6, with free answers and re-reads

`Quantum.StdModel.Qrom.Tcr2.probAvg_smTcrIn_slRed_le_count` at leanSPHINCS's restricted SM-TCR-C
game `smTcrIn romWorld tcrColl slotColl TcrTwIn` played by B6 (`tcrRed`).

* **Its setup** asks every leaf, node and FORS node and key of the key as a target (the
  challenger's answers, free), then reads at most `11264` cells of target slots itself (its key
  generation, `isG_tcr_pre`). After it, at every table consistent with the log, every target
  position's cell is a record (`signOK_pre`: the live run is a run at that table,
  `mem_support_logImpl_of_liveRedRun`, where the setup's transcript is `tcrLog` of the routed
  table's digests, `run_tcrRest`, and the poison answers recorded each target).
* **Its signer** reads no charged cell (`ju_signer`): at every table consistent with the log the
  routed signer answered by the failing semantics (`failImpl`, failing at the charged cells)
  returns the routed table's signature (`simulateQ_failImpl_tcrSigner`, by `sign_eq_pure`: every
  position's cell is a record or off the target kinds), so its live runs make no charged read
  (`liveRedRun_of_fail`).
* **Its output** reads at most `548` cells of target slots (`isG_tcr_post`).

With the judge's read, `n = 11264 + 548 + 1 = 11813`, whatever the number of signing requests:
`probAvg ≤ (q + 11813)² · gradeEta (2^128)` (`probAvg_smTcrIn_tcrRed_le`).
-/

open OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (ExpandedKey keyDerivationInput)
open Quantum.Sphincs (Slot messageDigestInput)
open Quantum.Qrom.Sphincs (QTable RawPos Pos posSlot posInput cellOf slotInput SlotPayload
  encodeInput_posInput slotInRange_posSlot AnswersTable AnswersDigest AnswersEnc encCell
  encodeInput_encCell)

namespace Quantum.StdModel.Sphincs

open Quantum.StdModel Props Common
open Quantum.StdModel.Qrom (gradeEta LiveRedRun)
open Quantum.StdModel.Qrom.Tcr (GSep IsG Mem mem₀ ChalFirst chalW chalCan chalCost
  isQueryBound_of_noChal RecInv LiveInv TVal tcell)
open Quantum.StdModel.Qrom.Tcr2 (MemK rlK updK cnt Consistent failImpl Chg gWR
  liveRedRun_of_fail consistent_of_liveRedRun mem_support_logImpl_of_liveRedRun cnt_liveRedRun
  liveInv_liveRedRunK probAvg_smTcrIn_slRed_le_count consistent_logD liveRedRun_none)
open Quantum.StdModel.Qrom.SphInst (tcrColl_param_tweak_eq tcrColl_layout_injective
  tcrColl_layout_slot)

/-! ## Layout obligations and the cells of the targets -/

theorem sphincs_gSep : GSep tcrColl TcrTwIn :=
  fun _ P _ m _ _ _ _ hG h ↦ tcrColl_param_tweak_eq hG P m h

/-- `2^128` digests per truncation, with the classical decision of the fibers. -/
theorem card_truncateHash_fiber_le_cl (o : Digest) :
    (@Finset.filter HashOutput (fun y ↦ tcrColl.trunc y = o)
      (fun _ ↦ Classical.propDecidable _) Finset.univ).card ≤ 2 ^ 128 := by
  convert Quantum.StdModel.Xmss.card_truncateHash_fiber_le o
  rfl

/-- **A `G`-cell is the cell of a slot input of a target kind.** -/
theorem isG_kindCell {z : Quantum.Qrom.HashDomain} (h : IsG tcrColl TcrTwIn z) :
    KindCell tcrTwKinds z := by
  obtain ⟨P', t, l, mm, ht, hz⟩ := h
  obtain ⟨-, d, hd⟩ := tcrColl_layout_slot ht P' mm
  refine ⟨pubKey P', 0, t, d, ?_, hd ▸ hz⟩
  cases l <;> cases t <;> first | exact (ht : False).elim | exact le_rfl

/-- **The cell of a slot input off the target kinds is no `G`-cell.** -/
theorem not_isG_of_kind {key : ExpandedKey} {root : Digest} {s : Slot} {d : SlotPayload s}
    (h0 : tcrTwKinds.of s = 0) {z : Quantum.Qrom.HashDomain}
    (hz : Quantum.Qrom.encodeInput (slotInput key root s d) = some z) :
    ¬ IsG tcrColl TcrTwIn z := fun h ↦ by
  obtain ⟨key', root', s', d', h1, hz'⟩ := isG_kindCell h
  have hk := kindsOf_eq_of_slotInput_eq (Quantum.Qrom.encodeInput_injective hz hz') tcrTwKinds
  omega

/-- The positions that are no target have slots off the target kinds. -/
theorem kind_posSlot_of_not_target (v : QTable) {p : RawPos} (hp : ¬ IsTarget p) :
    tcrTwKinds.of (posSlot v p) = 0 := by
  cases p <;> first | exact absurd trivial hp | rfl

/-! ## The reduction's own reads of `G`-cells -/

theorem tcr_le_isG (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    twInputCost (IsG tcrColl TcrTwIn) (slotInput key root s p) ≤ tcrTwKinds.of s :=
  twInputCost_le (fun _ h ↦ isG_kindCell h) key root s p

theorem tcrHash_kinds_isG :
    HashKinds (tcrHash romWorld) (hcallCostOn (IsG tcrColl TcrTwIn) (R' := TcrPorts))
      tcrTwKinds :=
  hashKinds_liftW_on tcr_le_isG

/-- **B6's setup reads at most `11264` `G`-cells itself.** -/
theorem isG_tcr_pre :
    QueryCostAtMost (tcrPre romWorld) (hcallCostOn (IsG tcrColl TcrTwIn) (R' := TcrPorts))
      11264 := by
  unfold tcrPre tcrRest
  exact ((liftW_sample_on _).bind fun s ↦ (liftW_sample_on _).bind fun _ ↦
    (buildDig_zero (tcrAsk_on s)).bind fun _ ↦ (portQ_on _).bind fun _ ↦
      (keygenFromSeed_cost (routeHash_pure_kinds tcrHash_kinds_isG) 0).bind fun _ ↦
        isWeightBound_pure _ _ 0).mono (by simp [keygenW_tcrTwKinds])

/-- **B6's output reads at most `548` `G`-cells.** -/
theorem isG_tcr_post (a : TcrData) (f : Forgery) (st : TcrSt) :
    QueryCostAtMost (tcrPost romWorld a f st)
      (hcallCostOn (IsG tcrColl TcrTwIn) (R' := TcrPorts)) 548 := by
  unfold tcrPost
  exact (recVerify_bind_tw (fun l ↦ liftW_hash_on (R' := TcrPorts) (P := IsG tcrColl TcrTwIn) l)
    (hashKinds_hashQuery_on tcr_le_isG)
    (fun rv ↦ tcrHashAll romWorld rv.2 >>= fun ps ↦ pure (tcrPick a.P a.t (tcrLook ps)))
    (fun rv ↦ ((tcrHashAll_on (P := IsG tcrColl TcrTwIn) rv.2).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono le_rfl) a.pk f.message f.signature).mono
    (by simp [verifyW_tcrTwKinds])

theorem gWR_le_isG (t : (romWorld.Oracles + TcrPorts).Domain) :
    gWR tcrColl TcrTwIn (R' := TcrPorts) t ≤ hcallCostOn (IsG tcrColl TcrTwIn) t := by
  rcases t with (n | z) | q
  · exact le_rfl
  · simp only [gWR, hcallCostOn, twCellCost]
    exact le_rfl
  · exact le_rfl

theorem chalW_le_portCost (t : (romWorld.Oracles + TcrPorts).Domain) :
    chalW t ≤ portCost romWorld (R' := TcrPorts) t := by
  rcases t with t | q <;> exact le_rfl

/-- **A reduction's program with no own hash, then a program whose challenger queries come
first**, makes every challenger query first. -/
theorem chalFirst_bind {Q' : Type} {R' : OracleSpec.{0, 0} Q'} {α β : Type}
    (oa : OracleComp (romWorld.Oracles + R') α) (f : α → OracleComp (romWorld.Oracles + R') β)
    (h1 : QueryCostAtMost oa (hcallCostOn (fun _ ↦ True) (R' := R')) 0)
    (h2 : ∀ a, ChalFirst (f a)) : ChalFirst (oa >>= f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rw [pure_bind]; exact h2 a
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h1
    unfold ChalFirst
    rw [bind_assoc, isQueryBound_query_bind_iff]
    rcases t with (n | z) | q'
    · exact ⟨trivial, fun u ↦ ih u (by have h := h1.2 u; rwa [Nat.zero_sub] at h)⟩
    · exact absurd h1.1 (by simp [hcallCostOn, twCellCost])
    · exact ⟨rfl, fun u ↦ ih u (by have h := h1.2 u; rwa [Nat.zero_sub] at h)⟩

/-- **B6's setup makes every challenger query first**: the build and the reveal hash nothing
of their own, the key generation queries no challenger. -/
theorem chalFirst_tcrPre : ChalFirst (tcrPre romWorld) := by
  unfold tcrPre tcrRest
  exact chalFirst_bind _ _ (liftW_sample_on _) fun s ↦ chalFirst_bind _ _ (liftW_sample_on _)
    fun r ↦ chalFirst_bind _ _ (buildDig_zero (tcrAsk_on s)) fun _ ↦
      chalFirst_bind _ _ (portQ_on _) fun P ↦ isQueryBound_of_noChal _
        ((QueryCostAtMost.bind (a := 0) (b := 0) (tcr_queryCostAtMost_keygen romWorld P s r)
          fun _ ↦ isWeightBound_pure _ _ 0).mono_weight chalW_le_portCost) false

/-! ## The routed signer at the failing semantics -/

/-- **The records of the targets**: at every table consistent with the log, every target
position's cell of the routed table of `a` is a record. -/
def SignOK (a : TcrData) (m : Mem) : Prop :=
  ∀ H : Quantum.Qrom.HashDomain → HashOutput, Consistent H m → ∀ p : Pos,
    IsTarget p.1 → m.recs (cellOf 0 p (digTable (romWorld.hashOf H) a.P a.s a.r)) ≠ none

open scoped Classical in
/-- The world's hash at a cell that does not fail. -/
theorem simulateQ_failImpl_tcrHash {H : Quantum.Qrom.HashDomain → HashOutput}
    {B : Quantum.Qrom.HashDomain → Prop} {l : HashInput} {x : Quantum.Qrom.HashDomain}
    (hx : Quantum.Qrom.encodeInput l = some x) (hB : ¬ B x) :
    simulateQ (failImpl (R' := TcrPorts) H B) (tcrHash romWorld l) =
      pure (romWorld.hashOf H l) := by
  simp [tcrHash, liftW, romWorld, Quantum.Qrom.hashQ, hx]
  erw [simulateQ_spec_query]
  change (if B x then none else some (H x)) = some (H x)
  rw [ite_eq_right hB]

theorem not_chg_posInput {a : TcrData} {m : Mem} (hok : SignOK a m)
    {H : Quantum.Qrom.HashDomain → HashOutput} (hH : Consistent H m) (p : Pos) :
    ¬ Chg tcrColl TcrTwIn m (cellOf 0 p (digTable (romWorld.hashOf H) a.P a.s a.r)) := by
  rintro ⟨hG, hr⟩
  by_cases ht : IsTarget p.1
  · exact hok H hH p ht hr
  · exact not_isG_of_kind (kind_posSlot_of_not_target _ ht) (encodeInput_posInput 0 _ p) hG

/-- The routed hash answered by the failing semantics. -/
noncomputable abbrev routedF (H : Quantum.Qrom.HashDomain → HashOutput) (m : Mem)
    (a : TcrData) : HashInput → Option HashOutput :=
  routeHash a.P (fun d ↦ pure (a.s d)) (fun M ↦ pure (a.r M))
    fun l ↦ simulateQ (failImpl (R' := TcrPorts) H (Chg tcrColl TcrTwIn m)) (tcrHash romWorld l)

theorem answersTable_fail {a : TcrData} {m : Mem} (hok : SignOK a m)
    {H : Quantum.Qrom.HashDomain → HashOutput} (hH : Consistent H m) :
    AnswersTable 0 (digTable (romWorld.hashOf H) a.P a.s a.r) (routedF H m a) := by
  intro p hp
  by_cases hs : IsSecret p
  · exact answersSecrets_routeHash (h := romWorld.hashOf H) (fun _ ↦ rfl) (fun _ ↦ rfl) ⟨p, hp⟩
      hs
  · have hne : ¬ ∃ q : Pos, IsSecret q.1 ∧
        secInput a.P q.1 = posInput 0 (digTable (romWorld.hashOf H) a.P a.s a.r) p := by
      rintro ⟨q, hq, e⟩
      have e' := (posInput_eq_secInput (digTable (romWorld.hashOf H) a.P a.s a.r)
        (publicSeed_digTable _ _ _ _) (prfKey_digTable _ _ _ _) hq).trans e
      obtain rfl := posInput_inj (p := q) (q := ⟨p, hp⟩) e'
      exact hs hq
    unfold routedF routeHash
    rw [dite_eq_right hne]
    dsimp only
    rw [simulateQ_failImpl_tcrHash
      (encodeInput_posInput 0 _ ⟨p, hp⟩ : Quantum.Qrom.encodeInput (posInput 0 _ p) = _)
      (not_chg_posInput hok hH ⟨p, hp⟩)]
    exact congrArg pure ((honest_digTable _ _ _ _).out ⟨p, hp⟩ hs).symm

theorem answersDigest_fail {a : TcrData} {m : Mem}
    {H : Quantum.Qrom.HashDomain → HashOutput} :
    AnswersDigest (digTable (romWorld.hashOf H) a.P a.s a.r) (routedF H m a) := fun M ↦ by
  set v := digTable (romWorld.hashOf H) a.P a.s a.r
  have hne : ¬ ∃ q : Pos, IsSecret q.1 ∧
      secInput a.P q.1 = messageDigestInput (v.randomizer M) v.publicSeed v.root M 1 := by
    rintro ⟨q, hq, e⟩
    exact sphincs_slotInput_ne (v.expandedKey 0) v.root (slotInRange_posSlot v q)
      (s' := .hmsg (v.randomizer M) M 1) trivial
      (posSlot_ne_of_secret v hq (fun _ e'' ↦ by cases e'') (fun _ e'' ↦ by cases e'')
        fun _ e'' ↦ by cases e'') _ ()
      ((posInput_eq_secInput v (publicSeed_digTable _ _ _ _) (prfKey_digTable _ _ _ _) hq).trans e)
  have hx : Quantum.Qrom.encodeInput (messageDigestInput (v.randomizer M) v.publicSeed v.root M 1)
      = some (Quantum.Qrom.Sphincs.cell (v.expandedKey 0) v.root (.hmsg (v.randomizer M) M 1) ()) :=
    Quantum.Qrom.Sphincs.encodeInput_slotInput (v.expandedKey 0) v.root
      (.hmsg (v.randomizer M) M 1) ()
  unfold routedF routeHash
  rw [dite_eq_right hne]
  dsimp only
  rw [simulateQ_failImpl_tcrHash hx fun h ↦ not_isG_of_kind (key := v.expandedKey 0)
    (root := v.root) (s := .hmsg (v.randomizer M) M 1) (d := ()) rfl hx h.1]
  exact congrArg pure ((honest_digTable _ _ _ _).call1 M).symm

theorem answersEnc_fail {a : TcrData} {m : Mem}
    {H : Quantum.Qrom.HashDomain → HashOutput} :
    AnswersEnc (digTable (romWorld.hashOf H) a.P a.s a.r) (cellHash (romWorld.hashOf H))
      (routedF H m a) := fun l τ e message counter ↦ by
  set v := digTable (romWorld.hashOf H) a.P a.s a.r
  have hne : ¬ ∃ q : Pos, IsSecret q.1 ∧ secInput a.P q.1 =
      addressedHashInput v.publicSeed (hashDomainFields (.encoding l τ e))
        (littleEndianBytes 16 message ++ bigEndianBytes 4 counter) := by
    rintro ⟨q, hq, e'⟩
    exact sphincs_slotInput_ne (v.expandedKey 0) v.root (slotInRange_posSlot v q)
      (s' := .enc l τ e) trivial
      (posSlot_ne_of_secret v hq (fun _ e'' ↦ by cases e'') (fun _ e'' ↦ by cases e'')
        fun _ e'' ↦ by cases e'') _ (message, counter)
      ((posInput_eq_secInput v (publicSeed_digTable _ _ _ _) (prfKey_digTable _ _ _ _) hq).trans
        e')
  have hx := encodeInput_encCell v.publicSeed l τ e message counter
  have hx' : Quantum.Qrom.encodeInput (slotInput (v.expandedKey 0) v.root (.enc l τ e)
      (message, counter)) = some (encCell v.publicSeed l τ e message counter) := hx
  unfold routedF routeHash
  rw [dite_eq_right hne]
  dsimp only
  rw [simulateQ_failImpl_tcrHash hx fun h ↦ not_isG_of_kind rfl hx' h.1]
  exact congrArg (fun x ↦ (pure (romWorld.hashOf H x) : Option HashOutput))
    (Quantum.Qrom.decodeInput_of_encodeInput_eq_some hx).symm

/-- **The routed signer at the failing semantics** returns the routed table's signature, at
every table consistent with the log when the targets are records. -/
theorem simulateQ_failImpl_tcrSigner {a : TcrData} {m : Mem} (hok : SignOK a m)
    {H : Quantum.Qrom.HashDomain → HashOutput} (hH : Consistent H m)
    (slog : SignLog) (M : Message) :
    simulateQ (failImpl (R' := TcrPorts) H (Chg tcrColl TcrTwIn m))
        (tcrSigner romWorld (a, slog) M) =
      some ((digTable (romWorld.hashOf H) a.P a.s a.r).signature (cellHash (romWorld.hashOf H)) M,
        (a, slog ++ [⟨M, (digTable (romWorld.hashOf H) a.P a.s a.r).signature
          (cellHash (romWorld.hashOf H)) M⟩])) := by
  unfold tcrSigner
  rw [simulateQ_bind, Over.simulateQ_sign]
  simp only [simulateQ_routeHash, simulateQ_pure]
  rw [Quantum.Qrom.Sphincs.sign_eq_pure (answersTable_fail hok hH) answersDigest_fail
    answersEnc_fail]
  rfl

/-! ## The invariant of the live runs -/

/-- **The invariant of B6's live runs**: at most `11264` charged reads, and on a live memory the
handler's data `a` with every target position's cell a record. -/
def Ju (a : TcrData) (s : TcrSt × QueryLog TcrPorts) (μ : Option MemK) : Prop :=
  cnt μ ≤ 11264 ∧ ∀ m k, μ = some (m, k) → s.1.1 = a ∧ SignOK a m

/-- **The signer keeps the invariant**: it makes no charged read and keeps the records. -/
theorem ju_signer {P : PublicParameter} {a : TcrData} {st : TcrSt} {log : QueryLog TcrPorts}
    {μ : Option MemK} (M : Message) (hJ : Ju a (st, log) μ)
    {r : (Option Signature × TcrSt) × QueryLog TcrPorts} {μ' : Option MemK}
    (hrun : LiveRedRun rlK (updK tcrColl TcrTwIn)
      ((smTcrIn romWorld tcrColl slotColl TcrTwIn).answer P) (tcrSigner romWorld st M) log μ r
        μ') :
    Ju a (r.1.2, r.2) μ' := by
  obtain ⟨hc, hok⟩ := hJ
  rcases μ with _ | ⟨m, k⟩
  · rw [liveRedRun_none _ _ hrun]
    exact ⟨Nat.zero_le _, fun _ _ h ↦ by cases h⟩
  obtain ⟨hst, hsign⟩ := hok m k rfl
  rcases μ' with _ | ⟨m', k'⟩
  · exact ⟨Nat.zero_le _, fun _ _ h ↦ by cases h⟩
  obtain ⟨st₁, slog⟩ := st
  change st₁ = a at hst
  subst hst
  have hf : ∀ H, Consistent H m → simulateQ (failImpl H (Chg tcrColl TcrTwIn m))
      (tcrSigner romWorld (st₁, slog) M) ≠ none := fun H hH ↦ by
    rw [simulateQ_failImpl_tcrSigner hsign hH]
    exact Option.some_ne_none _
  obtain ⟨hk, hrecs, -, hval⟩ := liveRedRun_of_fail _ _ hrun hf
  refine ⟨?_, fun m'' k'' h ↦ ?_⟩
  · have hk' : k' = k := hk
    change k ≤ 11264 at hc
    change k' ≤ 11264
    omega
  · cases h
    refine ⟨?_, fun H hH p hp ↦ ?_⟩
    · have e := (hval _ (consistent_logD m')).symm.trans (simulateQ_failImpl_tcrSigner hsign
        (consistent_of_liveRedRun _ _ hrun (consistent_logD m') (m, k) rfl) slog M)
      exact congrArg (fun x ↦ x.2.1) (Option.some.inj e)
    · rw [hrecs]
      exact hsign H (consistent_of_liveRedRun _ _ hrun hH (m, k) rfl) p hp

/-- **After the setup the targets are records**: the live run is a run at every table consistent
with the log, where the transcript is `tcrLog` of the routed table's digests, each target recorded
by the poison answers. -/
theorem signOK_pre (P : PublicParameter) {a : TcrData × QueryLog TcrPorts} {m : Mem} {k : ℕ}
    (hrun : LiveRedRun rlK (updK tcrColl TcrTwIn)
      ((smTcrIn romWorld tcrColl slotColl TcrTwIn).answer P) (tcrPre romWorld) []
        (some (mem₀, 0)) a (some (m, k))) :
    SignOK a.1 m := by
  have hI0 : LiveInv tcrColl slotColl TcrTwIn P [] ((some ((mem₀, 0) : MemK)).map Prod.fst) := by
    intro m₀ hm₀
    cases hm₀
    refine ⟨rfl, fun _ _ hv ↦ absurd hv (by simp [mem₀, Quantum.StdModel.Qrom.Tcr.Mem.recs]),
      fun _ e he ↦ ?_⟩
    simp [tcrTargets] at he
  have hI := liveInv_liveRedRunK sphincs_gSep tcrColl_tweakSeparated tcrColl_lengthLe _ hrun hI0
    m rfl
  intro H hH p hp
  have hsup := mem_support_logImpl_of_liveRedRun _ _ hrun hH
  rw [run_tcrPre romWorld H romWorld_coinsFair] at hsup
  simp only [mem_support_bind_iff] at hsup
  obtain ⟨s, -, r, -, hsr⟩ := hsup
  obtain ⟨tf, -, hrest⟩ := run_tcrRest romWorld H P s r
  have hrest' : (simulateQ (logImpl (W := romWorld) H
      ((smTcrIn romWorld tcrColl slotColl TcrTwIn).answer P)) (tcrRest romWorld s r)).run [] =
      pure (⟨P, s, r, tf, (digTable (romWorld.hashOf H) P s r).publicKey⟩,
        tcrLog (digTable (romWorld.hashOf H) P s r).dig P) := hrest
  rw [hrest', support_pure, Set.mem_singleton_iff] at hsr
  subst hsr
  set v := digTable (romWorld.hashOf H) P s r
  have he := mem_tcrTargets_tcrLog v.dig P p hp
  have hval := tcrValid_tcrLog v.dig P
  obtain ⟨w, hw, -⟩ := hI.2.2 ⟨hval.1, hval.2.2⟩ _ he (tcrTwIn_keySlot p hp)
  have hlay : tcrColl.layout (tcrFnOf p.1) P (keySlot p.1) (tcrKeyMsg p.1 (keyPayload p.1 v.dig)) =
      posInput 0 v p.1 := by
    rw [tcrColl_layout_key P p hp, posInput_eq_keyInput 0 v (tcr_keyPart_of_isTarget hp)
      (tcr_not_secret_of_isTarget hp), publicSeed_digTable]
  have hcell : tcell tcrColl P (⟨tcrFnOf p.1, keySlot p.1, tcrKeyMsg p.1 (keyPayload p.1 v.dig)⟩ :
      TcrOut) = cellOf 0 p v := by
    change (Quantum.Qrom.encodeInput (tcrColl.layout _ P _ _)).getD 0 = _
    rw [hlay, encodeInput_posInput]
    rfl
  change m.recs (cellOf 0 p v) ≠ none
  rw [← hcell, hw]
  exact Option.some_ne_none _

/-! ## The bound -/

/-- B6's output's own reads of `G`-cells. -/
theorem isG_tcr_post_gWR (a : TcrData) (f : Forgery) (st : TcrSt) :
    QueryCostAtMost (tcrPost romWorld a f st) (gWR tcrColl TcrTwIn (R' := TcrPorts)) 548 :=
  QueryCostAtMost.mono_weight (isG_tcr_post a f st) gWR_le_isG

-- The output's program is otherwise unfolded by `whnf` when matching its live runs.
attribute [local irreducible] tcrPost

/-- **The output adds at most `548` charged reads.** -/
theorem cnt_post_le {P : PublicParameter} {a : TcrData} {f : Forgery} {st : TcrSt}
    {log : QueryLog TcrPorts} {μ : Option MemK} {r : TcrOut × QueryLog TcrPorts}
    {μ' : Option MemK}
    (hrun : LiveRedRun rlK (updK tcrColl TcrTwIn)
      ((smTcrIn romWorld tcrColl slotColl TcrTwIn).answer P) (tcrPost romWorld a f st) log μ r
        μ') :
    cnt μ' ≤ cnt μ + 548 :=
  cnt_liveRedRun (C := tcrColl) (G := TcrTwIn) _ (tcrPost romWorld a f st)
    (isG_tcr_post_gWR a f st) hrun

open scoped Classical in
/-- **The QROM bound of leanSPHINCS's restricted SM-TCR-C game played by B6**, the challenger's
answers and B6's re-reads of its targets free (its key generation and signer recompute the targets
from the table its answers recorded): with `q` adversary calls and any number of signing requests,
`probAvg ≤ (q + 11813)² (2 √(2^128/N) + √((2^128 + 2)/N))²`, `N = 2^256`. -/
theorem probAvg_smTcrIn_tcrRed_le (A : SAdv romWorld) {q : ℕ}
    (hq : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q) :
    romWorld.probAvg ((smTcrIn romWorld tcrColl slotColl TcrTwIn).game (tcrRed romWorld A)) ≤
      ((q + 11813 : ℕ) : ℝ≥0∞) ^ 2 *
        ENNReal.ofReal (gradeEta HashOutput (2 ^ 128)) :=
  probAvg_smTcrIn_slRed_le_count sphincs_gSep tcrColl_layout_injective tcrColl_tweakSeparated
    tcrColl_lengthLe card_truncateHash_fiber_le_cl (fun _ ↦ tcrPre romWorld) (fun _ a ↦ A a.pk)
    (fun _ a ↦ (a, [])) (fun _ ↦ tcrSigner romWorld) (fun _ ↦ tcrPost romWorld)
    (fun _ ↦ chalFirst_tcrPre)
    (fun _ st M ↦ (queryCostAtMost_tcrSigner romWorld st M).mono_weight chalW_le_portCost)
    (fun _ a f st ↦ (queryCostAtMost_tcrPost romWorld a f st).mono_weight chalW_le_portCost)
    (fun _ ↦ hq _) 11813 (fun _ a s μ ↦ Ju a s μ)
    (fun P a μ hrun ↦ by
      have hw : QueryCostAtMost (tcrPre romWorld) (gWR tcrColl TcrTwIn (R' := TcrPorts)) 11264 :=
        isG_tcr_pre.mono_weight gWR_le_isG
      refine ⟨(cnt_liveRedRun _ _ hw hrun).trans (by simp [cnt]), fun m k hμ ↦ ⟨rfl, ?_⟩⟩
      subst hμ
      exact signOK_pre P hrun)
    (fun _ _ _ _ _ qq hJ _ _ hrun ↦ ju_signer qq hJ hrun)
    (fun _ a f st _ _ hJ _ _ hrun ↦ by
      have h := cnt_post_le hrun
      have := hJ.1
      omega)

end Quantum.StdModel.Sphincs

end
