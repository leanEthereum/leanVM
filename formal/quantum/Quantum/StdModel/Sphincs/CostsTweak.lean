module

public import Quantum.StdModel.Sphincs.Costs

@[expose] public section

/-!
# leanSPHINCS's reductions: their own queries at the challenge tweaks (design R3)

In the QROM (`romWorld`) the reduction's classical hash of `l` is one query of the random
function at the cell `encodeInput l`. `hcallCostOn P` counts the queries at cells satisfying `P`
(coins and challenger queries count nothing). Per property, `P` is the set of its challenge
tweaks' cells:

* B1, `KimCell`: the inputs keyed by `SK.seed` (the formats `kimFmt` around any key);
* B2, `PrfMsgCell`: the inputs keyed by `SK.prf` (`prfMsgInput_eq`, any key);
* B3, `HmsgCell`: the `H_msg` inputs (`itsrMap.inputs`);
* B4, `EncCell`: the encoding slots of the keys in use (`encKeys`), under any `PK.seed`;
* B5, `CpreCell`: the chain steps and the FORS leaves, under any `PK.seed`;
* B6, `TcrCell`: the target slots (`keySlot p` for `IsTarget p`), under any `PK.seed`.

Each set lies in the cells of slot inputs of some kinds (`KindCell`): inputs of slots of different
kinds differ (`kindsOf_eq_of_slotInput_eq`, by length and address type), so a hash call of a kind
outside the set never queries it, and the scheme's per-kind bounds (`keygenW`, `signW`,
`verifyW`) at the kinds' indicator count the queries. A recorded verification counts its queries
in the set, and so do its recorded inputs hashed again (`recVerify_mapM_tw`).

| | setup | handler (per request) | output |
|---|---|---|---|
| B1 (`B1`) | 65538 | 286914 | 0 |
| B2 (`B2`) | 0 | 1 | 0 |
| B3 (`itsrRed`) | 0 | 2 | 0 |
| B4 (`encRed`) | 0 | 12884901888 = 3 · 2^32 | 6 = 3 + 3 |
| B5 (`cpreRed`) | 0 | 0 | 1200 = 600 + 600 |
| B6 (`tcrRed`) | 11264 | 290817 | 548 = 274 + 274 |

B1 and B2 count every expansion, secret `PRF` call and `PRF_msg` call at one: the per-kind
bounds hold for every key, while only the calls under the reduction's own key are routed to the
challenger. B4's signer grinds every encoding at its cap; B6's key generation and signer hash the
trees' leaves and nodes at the crude height `10` of `treeLevelsW`.
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (ExpandedKey keyDerivationInput)
open Quantum.Sphincs (Slot Key msgPos messageDigestInput prfMessageInput)
open Quantum.Qrom.Sphincs (RawPos Pos slotInput SlotPayload)
open Common (QueryCostAtMost QueryCostAtMost.bind QueryCostAtMost.mono isWeightBound_pure
  isWeightBound_query isWeightBound_map QueryCostAtMost.bind_of_support)
open Common.SufCma (SchemeHashSpec)

namespace Quantum.StdModel.Sphincs

/-! ## Counting the queries at a set of cells -/

section Count

variable (P : Quantum.Qrom.HashDomain → Prop)

open Classical in
/-- One for a query of the random function at a cell satisfying `P`, nothing for a coin. -/
noncomputable def twCellCost : Quantum.Qrom.RomOracles.Domain → ℕ
  | .inl _ => 0
  | .inr x => if P x then 1 else 0

/-- **A reduction's queries at the cells `P`**: one for a query of the random function at a cell
satisfying `P`, nothing for a coin or a challenger query. -/
noncomputable def hcallCostOn {Q' : Type} {R' : OracleSpec.{0, 0} Q'} :
    (romWorld.Oracles + R').Domain → ℕ
  | .inl t => twCellCost P t
  | .inr _ => 0

open Classical in
/-- The queries at the cells `P` of the hash of `l`: one when `l` codes a cell satisfying `P`. -/
noncomputable def twInputCost (l : HashInput) : ℕ :=
  match Quantum.Qrom.encodeInput l with
  | some x => if P x then 1 else 0
  | none => 0

/-- The hash of `l` queries the cells `P` `twInputCost P l` times. -/
theorem hashQ_twCellCost (l : HashInput) :
    QueryCostAtMost (Quantum.Qrom.hashQ l) (twCellCost P) (twInputCost P l) := by
  rcases h : Quantum.Qrom.encodeInput l with _ | x
  · have e : Quantum.Qrom.hashQ l = pure 0 := by rw [Quantum.Qrom.hashQ, h]
    rw [e]
    exact isWeightBound_pure _ _ _
  · rw [Quantum.Qrom.hashQ_of_encodeInput_eq_some h, twInputCost, h]
    exact isWeightBound_query (twCellCost P) (.inr x)

variable {P} {Q' : Type} {R' : OracleSpec.{0, 0} Q'}

/-- A challenger query counts nothing. -/
theorem portQ_on (q : Q') : QueryCostAtMost (portQ romWorld R' q) (hcallCostOn P (R' := R')) 0 :=
  queryCostAtMost_portQ romWorld (fun _ ↦ le_rfl) q

/-- A sample counts nothing. -/
theorem sample_on (α : Type) [SampleableType α] :
    QueryCostAtMost (Props.sample romWorld α) (twCellCost P) 0 :=
  Common.isWeightBound_liftM_probComp (twCellCost P) (fun _ ↦ rfl) ($ᵗ α)

theorem liftW_sample_on (α : Type) [SampleableType α] :
    QueryCostAtMost (liftW R' (Props.sample romWorld α)) (hcallCostOn P (R' := R')) 0 :=
  queryCostAtMost_liftW_of romWorld (c := twCellCost P) (fun _ ↦ le_rfl) (sample_on α)

theorem liftLeft_sample_on (α : Type) [SampleableType α] :
    QueryCostAtMost (liftLeft (spec₂ := R') (Props.sample romWorld α)) (hcallCostOn P (R' := R'))
      0 :=
  queryCostAtMost_liftLeft_of romWorld (c := twCellCost P) (fun _ ↦ le_rfl) (sample_on α)

/-- The world's hash in a reduction queries the cells `P` `twInputCost P l` times. -/
theorem liftW_hash_on (l : HashInput) :
    QueryCostAtMost (liftW R' (romWorld.hash l)) (hcallCostOn P (R' := R')) (twInputCost P l) :=
  queryCostAtMost_liftW_of romWorld (c := twCellCost P) (fun _ ↦ le_rfl) (hashQ_twCellCost P l)

end Count

/-! ## Kinds of slots -/

/-- The address type of a secret's `PRF` call. -/
theorem addressType_keygenDomainFields (d : KeygenDomain) :
    (keygenDomainFields d).addressType = .wotsPrf ∨
      (keygenDomainFields d).addressType = .forsPrf := by
  cases d <;> simp [keygenDomainFields, makeAddress]

/-- **Inputs of slots of different kinds differ**: two equal honest inputs, under any keys and
roots, have slots of one kind (by their lengths, else by their address types). -/
theorem kindsOf_eq_of_slotInput_eq {key key' : ExpandedKey} {root root' : Digest} {s s' : Slot}
    {p : SlotPayload s} {p' : SlotPayload s'}
    (h : slotInput key root s p = slotInput key' root' s' p') (c : Kinds) : c.of s = c.of s' := by
  have hl : slotLen s = slotLen s' := (length_slotInput key root s p).symm.trans
    ((congrArg List.length h).trans (length_slotInput key' root' s' p'))
  cases s <;> cases s' <;> dsimp only [slotInput] at h <;> first
    | rfl
    | (exfalso; simp [slotLen] at hl; done)
    | (exfalso
       have ha := congrArg Address.addressType (addressedHashInput_inj h).1
       simp [hashDomainFields, makeAddress] at ha
       done)
    | (exfalso
       have ha := congrArg Address.addressType (addressedHashInput_inj h).1
       obtain e | e := addressType_keygenDomainFields ‹KeygenDomain› <;>
         simp [hashDomainFields, makeAddress, e] at ha)

/-- The cells of the honest inputs, under any key and root, of the slots of the kinds `c` bounds
by at least one. -/
def KindCell (c : Kinds) (x : Quantum.Qrom.HashDomain) : Prop :=
  ∃ (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s), 1 ≤ c.of s ∧
    Quantum.Qrom.encodeInput (slotInput key root s p) = some x

section Kinds

variable {P : Quantum.Qrom.HashDomain → Prop} {c : Kinds}

/-- **The queries at cells of the kinds of `c`**: a slot input queries such a cell only when `c`
bounds its kind by at least one. -/
theorem twInputCost_le (hP : ∀ x, P x → KindCell c x) (key : ExpandedKey) (root : Digest)
    (s : Slot) (p : SlotPayload s) : twInputCost P (slotInput key root s p) ≤ c.of s := by
  unfold twInputCost
  split
  · rename_i x hx
    split_ifs with hPx
    · obtain ⟨key', root', s', p', hs', hx'⟩ := hP x hPx
      rw [kindsOf_eq_of_slotInput_eq (Quantum.Qrom.encodeInput_injective hx hx') c]
      exact hs'
    · exact Nat.zero_le _
  · exact Nat.zero_le _

variable (hle : ∀ key root s p, twInputCost P (slotInput key root s p) ≤ c.of s)
include hle

theorem hashKinds_hashQ_on : HashKinds Quantum.Qrom.hashQ (twCellCost P) c :=
  fun key root s p ↦ (hashQ_twCellCost P _).mono (hle key root s p)

theorem hashKinds_hashL_on {Q' : Type} {R' : OracleSpec.{0, 0} Q'} :
    HashKinds (hashL romWorld R') (hcallCostOn P (R' := R')) c :=
  fun key root s p ↦ queryCostAtMost_liftLeft_of romWorld (c := twCellCost P) (fun _ ↦ le_rfl)
    (hashKinds_hashQ_on hle key root s p)

theorem hashKinds_liftW_on {Q' : Type} {R' : OracleSpec.{0, 0} Q'} :
    HashKinds (fun l ↦ liftW R' (romWorld.hash l)) (hcallCostOn P (R' := R')) c :=
  fun key root s p ↦ queryCostAtMost_liftW_of romWorld (c := twCellCost P) (fun _ ↦ le_rfl)
    (hashKinds_hashQ_on hle key root s p)

theorem hashKinds_hashQuery_on :
    HashKinds Quantum.Sphincs.WithHash.hashQuery (twInputCost P) c := fun key root s p ↦ by
  rw [Quantum.Sphincs.WithHash.hashQuery, HasQuery.instOfMonadLift_query]
  exact (isWeightBound_query _ _).mono (hle key root s p)

end Kinds

/-- The routed hash with pure secrets and randomizers keeps the bounds per kind. -/
theorem routeHash_pure_kinds {ι : Type} {O : OracleSpec.{0, 0} ι} {Q : PublicParameter}
    {s : KeygenDomain → Digest} {r : Message → Digest} {h : HashInput → OracleComp O HashOutput}
    {cost : ι → ℕ} {c : Kinds} (hh : HashKinds h cost c) :
    HashKinds (routeHash Q (fun d ↦ (pure (s d) : OracleComp O Digest)) (fun M ↦ pure (r M)) h)
      cost c :=
  routeHash_kinds hh (fun _ ↦ isWeightBound_pure _ _ _) (fun _ ↦ isWeightBound_pure _ _ _)

/-! ## The recorded verification -/

section Rec

variable {ι : Type} {O : OracleSpec.{0, 0} ι} {h : HashInput → OracleComp O HashOutput}
  {cost : ι → ℕ} {w : HashInput → ℕ} (hh : ∀ l, QueryCostAtMost (h l) cost (w l))
include hh

/-- **A recorded computation** within `n` under `w` costs at most `n` and records inputs of total
weight at most `n`. -/
theorem recTw_cost {α : Type} (x : OracleComp SchemeHashSpec α) :
    ∀ n : ℕ, QueryCostAtMost x w n → ∀ l0 : List HashInput,
      QueryCostAtMost ((simulateQ (recImpl h) x).run l0) cost n ∧
        ∀ r ∈ support ((simulateQ (recImpl h) x).run l0), ∃ new : List HashInput,
          r.2 = l0 ++ new ∧ (new.map w).sum ≤ n := by
  induction x using OracleComp.inductionOn with
  | pure a =>
    intro n _ l0
    rw [simulateQ_pure, StateT.run_pure]
    refine ⟨isWeightBound_pure _ _ _, fun r hr ↦ ⟨[], ?_, by simp⟩⟩
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr, List.append_nil]
  | query_bind t k ih =>
    intro n hx l0
    rw [Common.isWeightBound_query_bind_iff] at hx
    have h1 := hx.1
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hq : (recImpl h t).run l0 = (fun o ↦ (o, l0 ++ [t])) <$> h t := by
      simp [recImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_modify]
    rw [hq, bind_map_left]
    refine ⟨((hh t).bind fun o ↦ (ih o (n - w t) (hx.2 o) (l0 ++ [t])).1).mono (by omega),
      fun r hr ↦ ?_⟩
    rw [mem_support_bind_iff] at hr
    obtain ⟨o, -, hr⟩ := hr
    obtain ⟨new, e, hs⟩ := (ih o (n - w t) (hx.2 o) (l0 ++ [t])).2 r hr
    refine ⟨t :: new, by rw [e, List.append_assoc]; rfl, ?_⟩
    rw [List.map_cons, List.sum_cons]
    omega

/-- **The recorded verification** costs at most `verifyW c` and records inputs of total weight
at most `verifyW c`, when the hash query weighs at most `c` per kind. -/
theorem recVerify_tw {c : Kinds} (hv : HashKinds Quantum.Sphincs.WithHash.hashQuery w c)
    (pk : PublicKey) (M : Message) (σ : Signature) :
    QueryCostAtMost (recVerify h pk M σ) cost (verifyW c) ∧
      ∀ r ∈ support (recVerify h pk M σ), (r.2.map w).sum ≤ verifyW c := by
  have hx : QueryCostAtMost (Quantum.Sphincs.WithHash.verify Quantum.Sphincs.WithHash.hashQuery
      pk M σ) w (verifyW c) := by
    rw [← Quantum.Qrom.Sphincs.verify_eq_withHash]
    exact verify_cost hv pk M σ
  have := recTw_cost hh _ _ hx []
  refine ⟨this.1, fun r hr ↦ ?_⟩
  obtain ⟨new, e, hs⟩ := this.2 r hr
  rw [List.nil_append] at e
  rw [e]
  exact hs

omit hh in
/-- `mapM` costs the sum of its steps' bounds. -/
theorem mapM_cost_sum {α β : Type} {f : α → OracleComp O β} {b : α → ℕ}
    (hf : ∀ x, QueryCostAtMost (f x) cost (b x)) :
    ∀ xs : List α, QueryCostAtMost (xs.mapM f) cost (xs.map b).sum
  | [] => by
    rw [List.mapM_nil]
    exact isWeightBound_pure _ _ _
  | x :: xs => by
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    exact (hf x).bind fun _ ↦ ((mapM_cost_sum hf xs).bind fun _ ↦
      isWeightBound_pure _ cost 0).mono le_rfl

/-- **The recorded verification, then a continuation costing at most the recorded inputs'
weight**: at most `verifyW c` each. -/
theorem recVerify_bind_tw {c : Kinds} (hv : HashKinds Quantum.Sphincs.WithHash.hashQuery w c)
    {γ : Type} (k : Bool × List HashInput → OracleComp O γ)
    (hk : ∀ rv, QueryCostAtMost (k rv) cost (rv.2.map w).sum) (pk : PublicKey) (M : Message)
    (σ : Signature) :
    QueryCostAtMost (recVerify h pk M σ >>= k) cost (verifyW c + verifyW c) :=
  QueryCostAtMost.bind_of_support (recVerify_tw hh hv pk M σ).1 fun rv hrv ↦
    (hk rv).mono ((recVerify_tw hh hv pk M σ).2 rv hrv)

/-- **The recorded verification, then the recorded inputs hashed again**: at most `verifyW c`
each. -/
theorem recVerify_mapM_tw {c : Kinds} (hv : HashKinds Quantum.Sphincs.WithHash.hashQuery w c)
    {γ : Type} (F : Bool × List HashInput → List HashOutput → γ) (pk : PublicKey) (M : Message)
    (σ : Signature) :
    QueryCostAtMost (do
        let rv ← recVerify h pk M σ
        let os ← rv.2.mapM h
        pure (F rv os)) cost (verifyW c + verifyW c) :=
  recVerify_bind_tw hh hv _ (fun rv ↦ ((mapM_cost_sum hh rv.2).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono le_rfl) pk M σ

end Rec

section Zero

variable {ι : Type} {O : OracleSpec.{0, 0} ι} {w : ι → ℕ}

/-- A build of asks costing nothing costs nothing. -/
theorem buildDig_zero {ask : RawPos → (RawPos → Digest) → OracleComp O Digest}
    (hask : ∀ p t, QueryCostAtMost (ask p t) w 0) : QueryCostAtMost (buildDig ask) w 0 :=
  (buildDig_cost hask).mono (Nat.mul_zero _).le

/-- A table of steps costing nothing costs nothing. -/
theorem cpreTab_zero {α β : Type} [DecidableEq α] (L : List α) (x : β)
    {f : α → OracleComp O β} (hf : ∀ a, QueryCostAtMost (f a) w 0) :
    QueryCostAtMost (cpreTab L x f) w 0 :=
  (cpreTab_cost L x hf).mono (Nat.mul_zero _).le

end Zero

/-! ## B1: the calls keyed by `SK.seed` -/

/-- **B1's challenge tweaks (KIM-PRF)**: the cells of the calls keyed by `SK.seed`, the formats
`kimFmt` around any key `S0` (`kimInput_*`). -/
def KimCell (x : Quantum.Qrom.HashDomain) : Prop :=
  ∃ (y : KimDom) (S0 : MasterSeed),
    Quantum.Qrom.encodeInput ((kimFmt y).1 ++ littleEndianBytes 32 S0 ++ (kimFmt y).2) = some x

/-- The kinds of B1's challenge tweaks: the key expansion and the secrets' `PRF`. -/
def kimTwKinds : Kinds :=
  { Kinds.const 0 with expand := 1, prf := 1 }

theorem kimCell_kind {x : Quantum.Qrom.HashDomain} (h : KimCell x) : KindCell kimTwKinds x := by
  obtain ⟨y, S0, hx⟩ := h
  cases y with
  | publicSeed =>
    rw [kimInput_publicSeed] at hx
    exact ⟨⟨S0, 0, 0⟩, 0, .expand 0, (), le_rfl, hx⟩
  | prfKey =>
    rw [kimInput_prfKey] at hx
    exact ⟨⟨S0, 0, 0⟩, 0, .expand 1, (), le_rfl, hx⟩
  | prf Q d =>
    rw [kimInput_prf] at hx
    exact ⟨⟨S0, 0, Q⟩, 0, .prf d, (), le_rfl, hx⟩

theorem kim_le (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    twInputCost KimCell (slotInput key root s p) ≤ kimTwKinds.of s :=
  twInputCost_le (fun _ ↦ kimCell_kind) key root s p

theorem keygenW_kimTwKinds : keygenW kimTwKinds = 65538 := by
  norm_num [keygenW, treeLevelsW, otsPublicLeafW, kimTwKinds, Kinds.const, chainCount]

theorem signW_kimTwKinds : signW kimTwKinds = 286914 := by
  norm_num [signW, treeLevelsW, otsPublicLeafW, forsOpenW, forsTreeOpenW, signLayerW, otsSignW,
    openW, kimTwKinds, Kinds.const, chainCount, forsTreeCount, forsTreeHeight,
    encodingAttemptLimit]

theorem verifyW_kimTwKinds : verifyW kimTwKinds = 0 := by
  norm_num [verifyW, forsRecoverW, forsTreeRecoverW, layerW, otsLeafW, kimTwKinds, Kinds.const,
    chainCount, forsTreeCount, forsTreeHeight, layerCount]

section B1

theorem b1Sec_on (x : PublicParameter × HashOutput) (d : KeygenDomain) :
    QueryCostAtMost (b1Sec romWorld x d) (hcallCostOn KimCell (R' := KimSpec)) kimTwKinds.prf :=
  (isWeightBound_map _ (portQ_on _)).mono (Nat.zero_le _)

theorem b1Rnd_on (x : PublicParameter × HashOutput) (M : Message) :
    QueryCostAtMost (b1Rnd romWorld x M) (hcallCostOn KimCell (R' := KimSpec))
      kimTwKinds.prfMsg :=
  isWeightBound_map _ (hashKinds_hashL_on kim_le ⟨0, x.2, x.1⟩ 0 (.prfMsg M) ())

/-- **B1's setup** queries the cells keyed by `SK.seed` at most `65538` times. -/
theorem twCalls_B1_pre :
    QueryCostAtMost (rPre romWorld KimSpec Prod.fst (b1Sec romWorld) (b1Rnd romWorld)
      (b1Ctx romWorld)) (hcallCostOn KimCell (R' := KimSpec)) 65538 := by
  have hctx : QueryCostAtMost (b1Ctx romWorld) (hcallCostOn KimCell (R' := KimSpec)) 0 := by
    unfold b1Ctx
    exact (portQ_on _).bind fun _ ↦ (portQ_on _).bind fun _ ↦ isWeightBound_pure _ _ 0
  exact (rPre_cost romWorld KimSpec Prod.fst (b1Sec romWorld) (b1Rnd romWorld)
    (hashKinds_hashL_on kim_le) b1Sec_on b1Rnd_on _ hctx).mono
      (by simp [keygenW_kimTwKinds])

/-- **B1's signer** queries the cells keyed by `SK.seed` at most `286914` times per request. -/
theorem twCalls_B1_sign (st : (PublicParameter × HashOutput) × SignLog) (M : Message) :
    QueryCostAtMost (rSign romWorld KimSpec Prod.fst (b1Sec romWorld) (b1Rnd romWorld) st M)
      (hcallCostOn KimCell (R' := KimSpec)) 286914 :=
  (rSign_cost romWorld KimSpec Prod.fst (b1Sec romWorld) (b1Rnd romWorld)
    (hashKinds_hashL_on kim_le) b1Sec_on b1Rnd_on st M).mono (by simp [signW_kimTwKinds])

/-- **B1's output** queries no cell keyed by `SK.seed`. -/
theorem twCalls_B1_post (a : (PublicParameter × HashOutput) × PublicKey) (f : Forgery)
    (st : (PublicParameter × HashOutput) × SignLog) :
    QueryCostAtMost (rPost romWorld KimSpec a f st) (hcallCostOn KimCell (R' := KimSpec)) 0 :=
  (rPost_cost romWorld KimSpec (hashKinds_hashL_on kim_le) a f st).mono
    (by simp [verifyW_kimTwKinds])

end B1

/-! ## B2: the calls keyed by `SK.prf` -/

/-- **B2's challenge tweaks (PRF_msg)**: the cells of the inputs keyed by `SK.prf`, the
prefix-keyed format under any key `K` (`prfMsgInput_eq`). -/
def PrfMsgCell (x : Quantum.Qrom.HashDomain) : Prop :=
  ∃ (K : HashOutput) (y : MsgDom),
    Quantum.Qrom.encodeInput (([] : HashInput) ++ littleEndianBytes 32 K ++ msgBytes y) = some x

theorem prfMsgCell_kind {x : Quantum.Qrom.HashDomain} (h : PrfMsgCell x) :
    KindCell prfMsgKinds x := by
  obtain ⟨K, y, hx⟩ := h
  rw [prfMsgInput_eq] at hx
  exact ⟨⟨0, K, y.1⟩, 0, .prfMsg y.2, (), le_rfl, hx⟩

theorem prfMsg_le (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    twInputCost PrfMsgCell (slotInput key root s p) ≤ prfMsgKinds.of s :=
  twInputCost_le (fun _ ↦ prfMsgCell_kind) key root s p

section B2

theorem b2Sec_on (x : PublicParameter × (KeygenDomain → Digest)) (d : KeygenDomain) :
    QueryCostAtMost (b2Sec romWorld x d) (hcallCostOn PrfMsgCell (R' := MsgSpec))
      prfMsgKinds.prf :=
  isWeightBound_pure _ _ _

theorem b2Rnd_on (x : PublicParameter × (KeygenDomain → Digest)) (M : Message) :
    QueryCostAtMost (b2Rnd romWorld x M) (hcallCostOn PrfMsgCell (R' := MsgSpec))
      prfMsgKinds.prfMsg :=
  (portQ_on _).mono (Nat.zero_le _)

/-- **B2's setup** queries no cell keyed by `SK.prf`. -/
theorem twCalls_B2_pre :
    QueryCostAtMost (rPre romWorld MsgSpec Prod.fst (b2Sec romWorld) (b2Rnd romWorld)
      (b2Ctx romWorld)) (hcallCostOn PrfMsgCell (R' := MsgSpec)) 0 := by
  have hctx : QueryCostAtMost (b2Ctx romWorld) (hcallCostOn PrfMsgCell (R' := MsgSpec)) 0 := by
    unfold b2Ctx
    exact (liftLeft_sample_on _).bind fun _ ↦ (liftLeft_sample_on _).bind fun _ ↦
      isWeightBound_pure _ _ 0
  exact (rPre_cost romWorld MsgSpec Prod.fst (b2Sec romWorld) (b2Rnd romWorld)
    (hashKinds_hashL_on prfMsg_le) b2Sec_on b2Rnd_on _ hctx).mono
      (by simp [keygenW_prfMsgKinds])

/-- **B2's signer** queries the cells keyed by `SK.prf` at most once per request. -/
theorem twCalls_B2_sign (st : (PublicParameter × (KeygenDomain → Digest)) × SignLog)
    (M : Message) :
    QueryCostAtMost (rSign romWorld MsgSpec Prod.fst (b2Sec romWorld) (b2Rnd romWorld) st M)
      (hcallCostOn PrfMsgCell (R' := MsgSpec)) 1 :=
  (rSign_cost romWorld MsgSpec Prod.fst (b2Sec romWorld) (b2Rnd romWorld)
    (hashKinds_hashL_on prfMsg_le) b2Sec_on b2Rnd_on st M).mono (by simp [signW_prfMsgKinds])

/-- **B2's output** queries no cell keyed by `SK.prf`. -/
theorem twCalls_B2_post (a : (PublicParameter × (KeygenDomain → Digest)) × PublicKey)
    (f : Forgery) (st : (PublicParameter × (KeygenDomain → Digest)) × SignLog) :
    QueryCostAtMost (rPost romWorld MsgSpec a f st) (hcallCostOn PrfMsgCell (R' := MsgSpec)) 0 :=
  (rPost_cost romWorld MsgSpec (hashKinds_hashL_on prfMsg_le) a f st).mono
    (by simp [verifyW_prfMsgKinds])

end B2

/-! ## B3: the message hash -/

/-- **B3's challenge tweaks (ITSR)**: the cells of the `H_msg` inputs (`itsrMap.inputs`). -/
def HmsgCell (x : Quantum.Qrom.HashDomain) : Prop :=
  ∃ (R : Randomizer) (y : ItsrMsg), ∃ l ∈ itsrMap.inputs R y, Quantum.Qrom.encodeInput l = some x

/-- The kinds of B3's challenge tweaks: `H_msg`. -/
def hmsgTwKinds : Kinds :=
  { Kinds.const 0 with hmsg := 1 }

theorem hmsgCell_kind {x : Quantum.Qrom.HashDomain} (h : HmsgCell x) :
    KindCell hmsgTwKinds x := by
  obtain ⟨R, y, l, hl, hx⟩ := h
  simp only [itsrMap, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact ⟨⟨0, 0, y.1⟩, y.2.1, .hmsg R y.2.2 0, (), le_rfl, hx⟩
  · exact ⟨⟨0, 0, y.1⟩, y.2.1, .hmsg R y.2.2 1, (), le_rfl, hx⟩

theorem hmsg_le (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    twInputCost HmsgCell (slotInput key root s p) ≤ hmsgTwKinds.of s :=
  twInputCost_le (fun _ ↦ hmsgCell_kind) key root s p

theorem keygenW_hmsgTwKinds : keygenW hmsgTwKinds = 0 := by
  norm_num [keygenW, treeLevelsW, otsPublicLeafW, hmsgTwKinds, Kinds.const, chainCount]

theorem signW_hmsgTwKinds : signW hmsgTwKinds = 2 := by
  norm_num [signW, treeLevelsW, otsPublicLeafW, forsOpenW, forsTreeOpenW, signLayerW, otsSignW,
    openW, hmsgTwKinds, Kinds.const, chainCount, forsTreeCount, forsTreeHeight,
    encodingAttemptLimit]

section B3

attribute [local instance] secretsSampleable

theorem itsrHash_kinds :
    HashKinds (itsrHash romWorld) (hcallCostOn HmsgCell (R' := ItsrSpec)) hmsgTwKinds :=
  hashKinds_liftW_on hmsg_le

/-- **B3's setup** queries no `H_msg` cell. -/
theorem twCalls_itsr_pre :
    QueryCostAtMost (itsrPre romWorld) (hcallCostOn HmsgCell (R' := ItsrSpec)) 0 := by
  unfold itsrPre
  exact ((liftW_sample_on _).bind fun _ ↦ (liftW_sample_on _).bind fun _ ↦
    (keygenFromSeed_cost (routeHash_pure_kinds itsrHash_kinds) 0).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono (by simp [keygenW_hmsgTwKinds])

/-- **B3's signer** queries the `H_msg` cells at most twice per request. -/
theorem twCalls_itsr_sign (st : ItsrState) (M : Message) :
    QueryCostAtMost (itsrHandler romWorld st M) (hcallCostOn HmsgCell (R' := ItsrSpec)) 2 := by
  have hr : QueryCostAtMost (itsrRnd romWorld st.1.2.2 st.2.2 M)
      (hcallCostOn HmsgCell (R' := ItsrSpec)) 0 := by
    unfold itsrRnd
    split
    · exact isWeightBound_pure _ _ _
    · exact isWeightBound_map _ (isWeightBound_query _ _)
  unfold itsrHandler
  exact (hr.bind fun _ ↦ (sign_cost (routeHash_pure_kinds itsrHash_kinds) 0 M).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by simp [signW_hmsgTwKinds])

/-- **B3's output** queries nothing. -/
theorem twCalls_itsr_post (a : ItsrSetup) (f : Forgery) (st : ItsrState) :
    QueryCostAtMost (itsrPost romWorld a f st) (hcallCostOn HmsgCell (R' := ItsrSpec)) 0 :=
  isWeightBound_pure _ _ _

end B3

/-! ## B4: the encodings of the keys in use -/

/-- **B4's challenge tweaks (EncTCR+C)**: the cells of the encoding slots of the keys in use
(`encKeys`), under any `PK.seed`. -/
def EncCell (x : Quantum.Qrom.HashDomain) : Prop :=
  ∃ K ∈ encKeys, ∃ (Q : PublicParameter) (d : SlotPayload (encTw K)),
    Quantum.Qrom.encodeInput (slotInput (pubKey Q) 0 (encTw K) d) = some x

/-- The kinds of B4's challenge tweaks: the encodings. -/
def encTwKinds : Kinds :=
  { Kinds.const 0 with enc := 1 }

theorem encCell_kind {x : Quantum.Qrom.HashDomain} (h : EncCell x) : KindCell encTwKinds x := by
  obtain ⟨K, -, Q, d, hx⟩ := h
  exact ⟨pubKey Q, 0, encTw K, d, le_rfl, hx⟩

theorem enc_le (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    twInputCost EncCell (slotInput key root s p) ≤ encTwKinds.of s :=
  twInputCost_le (fun _ ↦ encCell_kind) key root s p

theorem signW_encTwKinds : signW encTwKinds = 12884901888 := by
  norm_num [signW, treeLevelsW, otsPublicLeafW, forsOpenW, forsTreeOpenW, signLayerW, otsSignW,
    openW, encTwKinds, Kinds.const, chainCount, forsTreeCount, forsTreeHeight,
    encodingAttemptLimit]

theorem verifyW_encTwKinds : verifyW encTwKinds = 3 := by
  norm_num [verifyW, forsRecoverW, forsTreeRecoverW, layerW, otsLeafW, encTwKinds, Kinds.const,
    chainCount, forsTreeCount, forsTreeHeight, layerCount]

section B4

attribute [local instance] secretsSampleable encRndSampleable

variable {P : Quantum.Qrom.HashDomain → Prop}

theorem encAsk_on (s : KeygenDomain → Digest) (p : RawPos) (t : RawPos → Digest) :
    QueryCostAtMost (encAsk romWorld s p t) (hcallCostOn P (R' := EncCtrPorts)) 0 := by
  unfold encAsk
  split
  · exact isWeightBound_pure _ _ _
  · exact portQ_on _

theorem encTargets_on (msg : Key → Digest) :
    ∀ L, QueryCostAtMost (encTargets romWorld msg L) (hcallCostOn P (R' := EncCtrPorts)) 0
  | [] => by
    simp only [encTargets]
    exact isWeightBound_pure _ _ _
  | K :: Ks => by
    simp only [encTargets]
    exact ((portQ_on _).bind fun _ ↦ (encTargets_on msg Ks).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono le_rfl

/-- **B4's setup** queries no encoding cell. -/
theorem twCalls_enc_pre :
    QueryCostAtMost (encRedPre romWorld) (hcallCostOn EncCell (R' := EncCtrPorts)) 0 := by
  unfold encRedPre encCore
  exact ((liftW_sample_on _).bind fun s ↦ (liftW_sample_on _).bind fun _ ↦
    (buildDig_zero (encAsk_on s)).bind fun _ ↦ (encTargets_on _ _).bind fun _ ↦
      (portQ_on _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono le_rfl

theorem encH_kinds :
    HashKinds (encH romWorld) (hcallCostOn EncCell (R' := EncCtrPorts)) encTwKinds :=
  hashKinds_liftW_on enc_le

/-- **B4's signer** queries the encoding cells at most `3 · 2^32` times per request (the counter
search of each layer at its cap). -/
theorem twCalls_enc_sign (st : EncData × SignLog) (M : Message) :
    QueryCostAtMost (encRedSign romWorld st M) (hcallCostOn EncCell (R' := EncCtrPorts))
      12884901888 := by
  unfold encRedSign
  exact ((sign_cost (routeHash_pure_kinds encH_kinds) 0 M).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by simp [signW_encTwKinds])

/-- **B4's output** queries the encoding cells at most `6` times: one trial per layer in the
recorded verification, and again in its recorded inputs. -/
theorem twCalls_enc_post (a : EncData) (f : Forgery) (st : EncData × SignLog) :
    QueryCostAtMost (encRedPost romWorld a f st) (hcallCostOn EncCell (R' := EncCtrPorts)) 6 := by
  unfold encRedPost
  exact (recVerify_mapM_tw (fun l ↦ liftW_hash_on (P := EncCell) l)
    (hashKinds_hashQuery_on enc_le)
    (fun rv os ↦ encPick a.P a.tg (rv.2.zip os)) a.pk f.message f.signature).mono
      (by simp [verifyW_encTwKinds])

end B4

/-! ## B5: the chain steps and the FORS leaves -/

/-- The slots of the CPRE chains: the chain steps and the FORS leaves. -/
def CpreSlot : Slot → Prop
  | .chain .. | .forsLeaf .. => True
  | _ => False

/-- **B5's challenge tweaks (CPRE)**: the cells of the chain steps and the FORS leaves, under any
`PK.seed`. -/
def CpreCell (x : Quantum.Qrom.HashDomain) : Prop :=
  ∃ (Q : PublicParameter) (s : Slot) (d : SlotPayload s), CpreSlot s ∧
    Quantum.Qrom.encodeInput (slotInput (pubKey Q) 0 s d) = some x

/-- The kinds of B5's challenge tweaks: the chain steps and the FORS leaves. -/
def cpreTwKinds : Kinds :=
  { Kinds.const 0 with chain := 1, forsLeaf := 1 }

theorem cpreCell_kind {x : Quantum.Qrom.HashDomain} (h : CpreCell x) :
    KindCell cpreTwKinds x := by
  obtain ⟨Q, s, d, hs, hx⟩ := h
  refine ⟨pubKey Q, 0, s, d, ?_, hx⟩
  cases s <;> first | exact False.elim hs | exact le_rfl

theorem cpre_le (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    twInputCost CpreCell (slotInput key root s p) ≤ cpreTwKinds.of s :=
  twInputCost_le (fun _ ↦ cpreCell_kind) key root s p

theorem verifyW_cpreTwKinds : verifyW cpreTwKinds = 600 := by
  norm_num [verifyW, forsRecoverW, forsTreeRecoverW, layerW, otsLeafW, cpreTwKinds, Kinds.const,
    chainCount, forsTreeCount, forsTreeHeight, layerCount]

section B5

variable {P : Quantum.Qrom.HashDomain → Prop}

theorem cpreValQ_on (j : CpreJ) (μ : ℕ) :
    QueryCostAtMost (cpreValQ romWorld j μ) (hcallCostOn P (R' := CpreS)) 0 :=
  portQ_on _

theorem cpreEvQ_on (l t : Slot) (m : SlotPayload l) :
    QueryCostAtMost (cpreEvQ romWorld l t m) (hcallCostOn P (R' := CpreS)) 0 :=
  portQ_on _

theorem cpreAsk_on (p : RawPos) (t : RawPos → Digest) :
    QueryCostAtMost (cpreAsk romWorld p t) (hcallCostOn P (R' := CpreS)) 0 := by
  cases p with
  | chain l τ e i step =>
    show QueryCostAtMost (cpreChainAsk romWorld l τ e i step) _ 0
    unfold cpreChainAsk
    split
    · exact cpreValQ_on _ _
    · exact isWeightBound_pure _ _ _
  | leaf => exact cpreEvQ_on _ _ _
  | node => exact cpreEvQ_on _ _ _
  | forsLeaf => exact cpreValQ_on _ _
  | forsNode => exact cpreEvQ_on _ _ _
  | forsRoots => exact cpreEvQ_on _ _ _
  | _ => exact isWeightBound_pure _ _ _

theorem cpreSelFrom_on (K : Key) (m : Digest) :
    ∀ n c, QueryCostAtMost (cpreSelFrom romWorld K m n c) (hcallCostOn P (R' := CpreS)) 0
  | 0, _ => by
    simp only [cpreSelFrom]
    exact isWeightBound_pure _ _ _
  | n + 1, c => by
    simp only [cpreSelFrom]
    refine ((cpreEvQ_on _ _ _).bind (b := 0) fun d ↦ ?_).mono le_rfl
    split
    · exact isWeightBound_pure _ _ _
    · exact cpreSelFrom_on K m n (c + 1)

theorem cpreOpenQ_on (sel : Key → Option (EncodingCounter × Encoding))
    (x : Key × ChainIndex × Fin chainLength) :
    QueryCostAtMost (cpreOpenQ romWorld sel x) (hcallCostOn P (R' := CpreS)) 0 := by
  unfold cpreOpenQ
  split
  · split
    · exact cpreValQ_on _ _
    · exact isWeightBound_pure _ _ _
  · exact isWeightBound_pure _ _ _

theorem cpreStage_on : QueryCostAtMost (cpreStage romWorld) (hcallCostOn P (R' := CpreS)) 0 := by
  unfold cpreStage cpreSelAll cpreOpenAll
  exact ((buildDig_zero cpreAsk_on).bind fun tf ↦
    (cpreTab_zero cpreKeys none fun K ↦ cpreSelFrom_on K
      ((ofDig tf).valuePos (msgPos K)) encodingAttemptLimit 0).bind fun sel ↦
    (cpreTab_zero cprePositions 0 (cpreOpenQ_on sel)).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono le_rfl

/-- **B5's setup** queries no chain step or FORS leaf. -/
theorem twCalls_cpre_pre :
    QueryCostAtMost (cprePre romWorld) (hcallCostOn CpreCell (R' := CpreS)) 0 := by
  unfold cprePre cpreRevQ
  exact ((liftW_sample_on _).bind fun _ ↦ cpreStage_on.bind fun _ ↦ (portQ_on _).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono le_rfl

theorem cpreSignIdx_on (a : CpreData) (sl : SignLog) (fl : List (CpreFJ × Digest))
    (M : Message) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    QueryCostAtMost (cpreSignIdx romWorld a sl fl M idx lv) (hcallCostOn P (R' := CpreS)) 0 := by
  unfold cpreSignIdx
  split
  · exact isWeightBound_pure _ _ _
  · unfold cpreForsQ
    exact ((cpreTab_zero (List.finRange forsTreeCount) 0 fun κ ↦
      cpreValQ_on (.inr (idx, κ, lv κ)) 0).bind fun _ ↦ isWeightBound_pure _ _ 0).mono le_rfl

theorem cpreHash_kinds :
    HashKinds (cpreHash romWorld) (hcallCostOn CpreCell (R' := CpreS)) cpreTwKinds :=
  hashKinds_liftW_on cpre_le

/-- **B5's signer** queries no chain step or FORS leaf: it hashes only the digest's two `H_msg`
calls and reads every chain value and FORS secret from the challenger. -/
theorem twCalls_cpre_sign (st : CpreSt) (M : Message) :
    QueryCostAtMost (cpreHandler romWorld st M) (hcallCostOn CpreCell (R' := CpreS)) 0 := by
  unfold cpreHandler
  exact ((cpreHash_kinds ⟨0, 0, st.1.par⟩ (ofDig st.1.tf).root (.hmsg (st.1.rnd M) M 0) ()).bind
    fun _ ↦ (cpreHash_kinds ⟨0, 0, st.1.par⟩ (ofDig st.1.tf).root (.hmsg (st.1.rnd M) M 1)
      ()).bind fun _ ↦ cpreSignIdx_on _ _ _ _ _ _).mono le_rfl

/-- **B5's output** queries the chain steps and FORS leaves at most `1200` times: `600` in the
recorded verification (`3 · 64 · 3` chain steps, `24` FORS leaves), and again in its recorded
inputs. -/
theorem twCalls_cpre_post (a : CpreData) (f : Forgery) (st : CpreSt) :
    QueryCostAtMost (cprePost romWorld a f st) (hcallCostOn CpreCell (R' := CpreS)) 1200 := by
  unfold cprePost
  exact (recVerify_mapM_tw (fun l ↦ liftW_hash_on (P := CpreCell) l)
    (hashKinds_hashQuery_on cpre_le)
    (fun rv os ↦ cpreOut a st.2.2 (cpreLookup rv.2 os)) a.pk f.message f.signature).mono
      (by simp [verifyW_cpreTwKinds])

end B5

/-! ## B6: the targets -/

/-- **B6's challenge tweaks (SM-TCR)**: the cells of the target slots, `keySlot p` for a target
position `p` (`IsTarget`: WOTS leaves, hypertree and FORS nodes, FORS keys), under any
`PK.seed`. -/
def TcrCell (x : Quantum.Qrom.HashDomain) : Prop :=
  ∃ (Q : PublicParameter) (p : Pos), IsTarget p.1 ∧ ∃ d : SlotPayload (keySlot p.1),
    Quantum.Qrom.encodeInput (slotInput (pubKey Q) 0 (keySlot p.1) d) = some x

/-- The kinds of B6's challenge tweaks: the leaves, the nodes, the FORS nodes, the FORS keys. -/
def tcrTwKinds : Kinds :=
  { Kinds.const 0 with leaf := 1, node := 1, forsNode := 1, forsRoots := 1 }

theorem tcrCell_kind {x : Quantum.Qrom.HashDomain} (h : TcrCell x) : KindCell tcrTwKinds x := by
  obtain ⟨Q, p, hp, d, hx⟩ := h
  refine ⟨pubKey Q, 0, keySlot p.1, d, ?_, hx⟩
  obtain ⟨p, hin⟩ := p
  revert hp
  cases p <;> intro hp <;> first | exact (hp : False).elim | exact le_rfl

theorem tcr_le (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    twInputCost TcrCell (slotInput key root s p) ≤ tcrTwKinds.of s :=
  twInputCost_le (fun _ ↦ tcrCell_kind) key root s p

theorem keygenW_tcrTwKinds : keygenW tcrTwKinds = 11264 := by
  norm_num [keygenW, treeLevelsW, otsPublicLeafW, tcrTwKinds, Kinds.const, chainCount]

theorem signW_tcrTwKinds : signW tcrTwKinds = 290817 := by
  norm_num [signW, treeLevelsW, otsPublicLeafW, forsOpenW, forsTreeOpenW, signLayerW, otsSignW,
    openW, tcrTwKinds, Kinds.const, chainCount, forsTreeCount, forsTreeHeight,
    encodingAttemptLimit]

theorem verifyW_tcrTwKinds : verifyW tcrTwKinds = 274 := by
  norm_num [verifyW, forsRecoverW, forsTreeRecoverW, layerW, otsLeafW, tcrTwKinds, Kinds.const,
    chainCount, forsTreeCount, forsTreeHeight, layerCount]

section B6

variable {P : Quantum.Qrom.HashDomain → Prop}

theorem tcrAsk_on (s : KeygenDomain → Digest) (p : RawPos) (t : RawPos → Digest) :
    QueryCostAtMost (tcrAsk romWorld s p t) (hcallCostOn P (R' := TcrPorts)) 0 := by
  unfold tcrAsk
  cases p <;> first | exact portQ_on _ | exact isWeightBound_pure _ _ _

theorem tcrHashAll_on : ∀ xs : List HashInput, QueryCostAtMost (tcrHashAll romWorld xs)
    (hcallCostOn P (R' := TcrPorts)) (xs.map (twInputCost P)).sum
  | [] => by
    simp only [tcrHashAll]
    exact isWeightBound_pure _ _ _
  | x :: xs => by
    simp only [tcrHashAll, List.map_cons, List.sum_cons]
    exact (liftW_hash_on x).bind fun _ ↦ ((tcrHashAll_on xs).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono le_rfl

theorem tcrHash_kinds :
    HashKinds (tcrHash romWorld) (hcallCostOn TcrCell (R' := TcrPorts)) tcrTwKinds :=
  hashKinds_liftW_on tcr_le

/-- **B6's setup** queries the target cells at most `11264` times: its routed key generation's
top tree (`2^10` leaves and `10 · 2^10` nodes at the crude height `10`). -/
theorem twCalls_tcr_pre :
    QueryCostAtMost (tcrPre romWorld) (hcallCostOn TcrCell (R' := TcrPorts)) 11264 := by
  unfold tcrPre tcrRest
  exact ((liftW_sample_on _).bind fun s ↦ (liftW_sample_on _).bind fun _ ↦
    (buildDig_zero (tcrAsk_on s)).bind fun _ ↦ (portQ_on _).bind fun _ ↦
      (keygenFromSeed_cost (routeHash_pure_kinds tcrHash_kinds) 0).bind fun _ ↦
        isWeightBound_pure _ _ 0).mono (by simp [keygenW_tcrTwKinds])

/-- **B6's signer** queries the target cells at most `290817` times per request. -/
theorem twCalls_tcr_sign (st : TcrSt) (M : Message) :
    QueryCostAtMost (tcrSigner romWorld st M) (hcallCostOn TcrCell (R' := TcrPorts)) 290817 := by
  unfold tcrSigner
  exact ((sign_cost (routeHash_pure_kinds tcrHash_kinds) 0 M).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by simp [signW_tcrTwKinds])

/-- **B6's output** queries the target cells at most `548` times: `274` in the recorded
verification, and again in its recorded inputs. -/
theorem twCalls_tcr_post (a : TcrData) (f : Forgery) (st : TcrSt) :
    QueryCostAtMost (tcrPost romWorld a f st) (hcallCostOn TcrCell (R' := TcrPorts)) 548 := by
  unfold tcrPost
  exact (recVerify_bind_tw (fun l ↦ liftW_hash_on (R' := TcrPorts) (P := TcrCell) l)
    (hashKinds_hashQuery_on tcr_le)
    (fun rv ↦ tcrHashAll romWorld rv.2 >>= fun ps ↦ pure (tcrPick a.P a.t (tcrLook ps)))
    (fun rv ↦ ((tcrHashAll_on (P := TcrCell) rv.2).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono le_rfl) a.pk f.message f.signature).mono
    (by simp [verifyW_tcrTwKinds])

end B6

end Quantum.StdModel.Sphincs

end
