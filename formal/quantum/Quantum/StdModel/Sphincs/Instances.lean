module

public import Quantum.StdModel.Sphincs.Events
public import Quantum.StdModel.Props
public import Quantum.StdModel.Formats

@[expose] public section

/-!
# leanSPHINCS instances of the property games

The collections, chains, encodings, keyed functions and message maps of the property games
(`Quantum.StdModel.Props`) for leanSPHINCS, every tweak a slot (`Quantum.Sphincs.Slot`), every
public parameter `PK.seed`, every tweakable hash truncated by `truncateHash`.

* `slotColl`: the evaluation collection of the two-phase games, function `l` at tweak `t` the honest
  input of the slot `t` when `l = t` and `t` is in range (`slotColl_layout`).
* `tcrColl` (SM-TCR): the targets `T_v`, `H` (hypertree and FORS) and `T_k` at their slots;
  `tcrColl_layout_tcrMsg`: a target position's slot and payload as a target input.
* `cpreChains` (CPRE): the WOTS chains (`len = chainLength - 1`, selective) and the FORS leaves
  (`len = 1`, adaptive); `simulateQ_cpre_walk_wots` (the walk is `walkH`),
  `simulateQ_cpre_walk_fors` (the FORS leaf `thSlot`), `cpreChains_distinctTweaks`.
* `encCtr` (EncTCR+C): the WOTS+C encoding; `simulateQ_encCtr_grind`: grinding is `QTable.select`.
* `kimFmt`, `kimTrunc` (KIM-PRF): the `SK.seed`-keyed calls S1 to S3 (`kimInput_*`).
* `msgBytes` (PRF_msg): `prfMsgInput_eq`.
* `itsrMap` (ITSR): the two `H_msg` calls; `simulateQ_itsr_select`: the cells `digestCells`.
* Obligations (`Props.Basic`): `LengthLe` of every collection, `TweakSeparated` of `slotColl`
  against each challenge collection, `KimFmtInjective`, `KimLengthLe`.

The challenge collections hash, at a tweak of another kind or out of range, `PK.seed` followed by
the message bytes (`SlotShaped`): such an input is no slot input (by its length), the bytes still
determine the message, and `PK.seed` stays hidden; an empty input there would make the targets at
such tweaks collide for every message.
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open HashSig.OverPermutation (nodePayload walkChain)
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (ExpandedKey keyDerivationInput)
open Quantum.Sphincs (Slot Key length_addressedHashInput length_digestsPayload
  length_bigEndianBytes littleEndianBytes_injective toBytes_injective
  slotOfAddress_keygenDomainFields messageDigestInput length_messageDigestInput prfMessageInput
  length_prfMessageInput length_keyDerivationInput)
open Quantum.Xmss (length_littleEndianBytes)
open Quantum.Qrom.Sphincs (QTable RawPos Pos posPayload posSlot slotInput SlotPayload SlotInRange
  slotInRange_posSlot length_slotInput_le)
open Quantum.StdModel.Props (TwColl TwHash Chains CtrEnc MsgMap KimFmtInjective KimLengthLe)

namespace Quantum.StdModel.Sphincs

/-! ## Tweakable hashes at a fixed table -/

/-- A tweakable hash of a collection, answered by a fixed table. -/
theorem simulateQ_eval (W : OracleWorld) (tab : W.Tab) {Par Tw Fn Out : Type} {Msg : Fn → Type}
    (C : TwColl Par Tw Fn Msg Out) (l : Fn) (P : Par) (t : Tw) (m : Msg l) :
    simulateQ (W.eager tab) (C.eval W l P t m) =
      pure (C.trunc (W.hashOf tab (C.layout l P t m))) := by
  rw [TwColl.eval, simulateQ_map, W.simulateQ_hash, map_pure]

/-! ## Inputs of no slot -/

/-- The lengths of the honest slot inputs. -/
def slotLengths : List ℕ :=
  [44, 64, 68, 80, 84, 93, 432, 1072]

/-- The lengths of the challenge collections' inputs at tweaks of no slot of their kind:
`PK.seed` and the message bytes. -/
def junkLengths : List ℕ :=
  [32, 36, 48, 400, 1040]

theorem length_slotInput_mem (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s) :
    (slotInput key root s p).length ∈ slotLengths := by
  cases s with
  | chain | forsLeaf | prf =>
    simp [slotInput, length_addressedHashInput, littleEndianBytes, slotLengths]
  | node | forsNode =>
    simp [slotInput, length_addressedHashInput, nodePayload, littleEndianBytes, slotLengths]
  | enc =>
    simp [slotInput, length_addressedHashInput, littleEndianBytes, bigEndianBytes, slotLengths]
  | leaf =>
    rw [slotInput, length_addressedHashInput, length_digestsPayload (n := chainCount) p]
    decide
  | forsRoots =>
    rw [slotInput, length_addressedHashInput, length_digestsPayload (n := forsTreeCount) p]
    decide
  | hmsg => rw [slotInput, length_messageDigestInput]; decide
  | prfMsg message =>
    rw [slotInput, length_prfMessageInput key.secretPrfKey key.publicSeed message]
    decide
  | expand => rw [slotInput, length_keyDerivationInput]; decide

theorem slotInput_ne_of_length {key : ExpandedKey} {root : Digest} {s : Slot} {p : SlotPayload s}
    {x : HashInput} (hx : x.length ∉ slotLengths) : slotInput key root s p ≠ x :=
  fun h ↦ hx (h ▸ length_slotInput_mem key root s p)

/-- **The shape of a challenge collection's input** at the tweak `t`: the honest input of `t`,
in range, or an input of no slot (nonempty, of no slot input's length) within `maxLen`. -/
def SlotShaped (P : PublicParameter) (t : Slot) (x : HashInput) : Prop :=
  (∃ d, SlotInRange t ∧ x = slotInput (pubKey P) 0 t d) ∨
    (x.length ∉ 0 :: slotLengths ∧ x.length ≤ Qrom.maxLen)

theorem slotShaped_junk {P : PublicParameter} {t : Slot} {x : HashInput}
    (hx : x.length ∈ junkLengths) : SlotShaped P t x := by
  have h : ∀ n ∈ junkLengths, n ∉ 0 :: slotLengths ∧ n ≤ Qrom.maxLen := by decide
  exact Or.inr (h _ hx)

theorem SlotShaped.length_le {P : PublicParameter} {t : Slot} {x : HashInput}
    (h : SlotShaped P t x) : x.length ≤ Qrom.maxLen := by
  rcases h with ⟨d, -, rfl⟩ | ⟨-, h⟩
  · exact length_slotInput_le _ _ _ _
  · exact h

/-- Every input of a collection of shaped inputs has at most `maxLen` bytes. -/
theorem lengthLe_of_shaped {Fn : Type} {Msg : Fn → Type} (C : TwColl PublicParameter Slot Fn Msg
    Digest) (h : ∀ l P t m, SlotShaped P t (C.layout l P t m)) : C.LengthLe Qrom.maxLen :=
  fun l P t m ↦ (h l P t m).length_le

/-! ## The evaluation collection -/

instance instDecidablePredSlotInRange : DecidablePred SlotInRange := fun s ↦ by
  cases s <;> unfold SlotInRange <;> infer_instance

/-- The layout of `slotColl`: the honest input of the slot `t` when the function is `t` and `t` is
in range, else empty. -/
def slotLayout (l : Slot) (P : PublicParameter) (t : Slot) (m : SlotPayload l) : HashInput :=
  if l = t ∧ SlotInRange l then slotInput (pubKey P) 0 l m else []

/-- **The evaluation collection** of the two-phase games: every slot's tweakable hash (`F`, `H`,
`T_v`, `T_k`, the encoding, the secrets and the digest calls), the function being the slot. -/
def slotColl : TwColl PublicParameter Slot Slot SlotPayload Digest where
  layout := slotLayout
  trunc := truncateHash

theorem slotColl_layout (P : PublicParameter) {t : Slot} (ht : SlotInRange t)
    (m : SlotPayload t) : slotColl.layout t P t m = slotInput (pubKey P) 0 t m :=
  ite_eq_left ⟨rfl, ht⟩

/-- An evaluation of `slotColl` at a fixed table is `thSlot`. -/
theorem simulateQ_slotColl_eval (W : OracleWorld) (tab : W.Tab) (P : PublicParameter) {t : Slot}
    (ht : SlotInRange t) (m : SlotPayload t) :
    simulateQ (W.eager tab) (slotColl.eval W t P t m) = pure (thSlot (W.hashOf tab) P t m) := by
  rw [simulateQ_eval, slotColl_layout P ht]
  rfl

theorem slotColl_lengthLe : slotColl.LengthLe Qrom.maxLen := by
  intro l P t m
  show (slotLayout l P t m).length ≤ _
  unfold slotLayout
  split_ifs
  · exact length_slotInput_le _ _ _ _
  · exact Nat.zero_le _

/-- **Obligation (c) from DIST**: `slotColl` never produces a shaped input under another tweak. -/
theorem tweakSeparated_of_shaped {Fn : Type} {Msg : Fn → Type}
    (C : TwColl PublicParameter Slot Fn Msg Digest)
    (h : ∀ l P t m, SlotShaped P t (C.layout l P t m)) : slotColl.TweakSeparated C := by
  intro l P t m l' t' m' he
  change slotLayout l' P t' m' = _ at he
  unfold slotLayout at he
  split_ifs at he with hl
  · obtain ⟨rfl, hr⟩ := hl
    rcases h l P t m with ⟨d, ht, hd⟩ | ⟨hn, -⟩
    · exact congrArg Sigma.fst (sphincs_slotInput_inj (pubKey P) 0 hr ht (he.trans hd))
    · exact absurd he (slotInput_ne_of_length fun hm ↦ hn (List.mem_cons_of_mem _ hm))
  · rcases h l P t m with ⟨d, -, hd⟩ | ⟨hn, -⟩
    · exact absurd (he.trans hd).symm
        (slotInput_ne_of_length (by decide : ([] : HashInput).length ∉ slotLengths))
    · exact absurd (List.mem_cons_self ..) (he ▸ hn)

/-! ## SM-TCR: the targets -/

/-- The target functions of SM-TCR: `T_v` (WOTS leaves), `H` in the hypertree, `H` in FORS, `T_k`
(FORS keys). -/
inductive TcrFn where
  | leaf
  | node
  | forsNode
  | forsRoots
  deriving DecidableEq

/-- The messages of the target functions: the payloads of their slots. -/
def TcrMsg : TcrFn → Type
  | .leaf => ChainIndex → Digest
  | .node => Digest × Digest
  | .forsNode => Digest × Digest
  | .forsRoots => ForsTreeIndex → Digest

/-- The bytes of a target message, as its slot hashes them. -/
def tcrBytes : (l : TcrFn) → TcrMsg l → HashInput
  | .leaf, m => digestsPayload m
  | .node, m => nodePayload m.1 m.2
  | .forsNode, m => nodePayload m.1 m.2
  | .forsRoots, m => digestsPayload m

/-- The layout of `tcrColl`: the honest input of the slot `t` when `t` is in range and of the
function's kind, else `PK.seed` and the message bytes. -/
def tcrLayout (P : PublicParameter) : (l : TcrFn) → Slot → TcrMsg l → HashInput
  | .leaf, .leaf a b c, m => slotInput (pubKey P) 0 (.leaf a b c) m
  | .node, .node a b c d, m =>
      if SlotInRange (.node a b c d) then slotInput (pubKey P) 0 (.node a b c d) m
      else littleEndianBytes 16 P ++ tcrBytes .node m
  | .forsNode, .forsNode a b c d, m =>
      if SlotInRange (.forsNode a b c d) then slotInput (pubKey P) 0 (.forsNode a b c d) m
      else littleEndianBytes 16 P ++ tcrBytes .forsNode m
  | .forsRoots, .forsRoots a, m => slotInput (pubKey P) 0 (.forsRoots a) m
  | l, _, m => littleEndianBytes 16 P ++ tcrBytes l m

/-- **The SM-TCR target collection**: `T_v`, `H` (hypertree, FORS) and `T_k` at their slots. -/
def tcrColl : TwColl PublicParameter Slot TcrFn TcrMsg Digest where
  layout l P t m := tcrLayout P l t m
  trunc := truncateHash

theorem length_tcrJunk (P : PublicParameter) (l : TcrFn) (m : TcrMsg l) :
    (littleEndianBytes 16 P ++ tcrBytes l m).length ∈ junkLengths := by
  cases l with
  | leaf =>
    have hm : (digestsPayload (n := chainCount) m).length = 16 * chainCount :=
      length_digestsPayload _
    show (littleEndianBytes 16 P ++ digestsPayload (n := chainCount) m).length ∈ _
    rw [List.length_append, length_littleEndianBytes, hm]
    decide
  | node => simp [tcrBytes, nodePayload, littleEndianBytes, junkLengths]
  | forsNode => simp [tcrBytes, nodePayload, littleEndianBytes, junkLengths]
  | forsRoots =>
    have hm : (digestsPayload (n := forsTreeCount) m).length = 16 * forsTreeCount :=
      length_digestsPayload _
    show (littleEndianBytes 16 P ++ digestsPayload (n := forsTreeCount) m).length ∈ _
    rw [List.length_append, length_littleEndianBytes, hm]
    decide

theorem tcrLayout_shaped (P : PublicParameter) (l : TcrFn) (t : Slot) (m : TcrMsg l) :
    SlotShaped P t (tcrLayout P l t m) := by
  have hj : SlotShaped P t (littleEndianBytes 16 P ++ tcrBytes l m) :=
    slotShaped_junk (length_tcrJunk P l m)
  cases l
  case leaf =>
    cases t
    case leaf a b c => exact Or.inl ⟨m, trivial, rfl⟩
    all_goals exact hj
  case node =>
    cases t
    case node a b c d =>
      by_cases h : SlotInRange (.node a b c d)
      · exact Or.inl ⟨m, h, ite_eq_left h⟩
      · have e : tcrLayout P .node (.node a b c d) m = littleEndianBytes 16 P ++ tcrBytes .node m :=
          ite_eq_right h
        rw [e]
        exact hj
    all_goals exact hj
  case forsNode =>
    cases t
    case forsNode a b c d =>
      by_cases h : SlotInRange (.forsNode a b c d)
      · exact Or.inl ⟨m, h, ite_eq_left h⟩
      · have e : tcrLayout P .forsNode (.forsNode a b c d) m =
            littleEndianBytes 16 P ++ tcrBytes .forsNode m := ite_eq_right h
        rw [e]
        exact hj
    all_goals exact hj
  case forsRoots =>
    cases t
    case forsRoots a => exact Or.inl ⟨m, trivial, rfl⟩
    all_goals exact hj

theorem tcrColl_lengthLe : tcrColl.LengthLe Qrom.maxLen :=
  lengthLe_of_shaped tcrColl fun l P t m ↦ tcrLayout_shaped P l t m

theorem tcrColl_tweakSeparated : slotColl.TweakSeparated tcrColl :=
  tweakSeparated_of_shaped tcrColl fun l P t m ↦ tcrLayout_shaped P l t m

/-- The target function of a position (`T_v` for the positions that are no target). -/
def tcrFnOf : RawPos → TcrFn
  | .node .. => .node
  | .forsNode .. => .forsNode
  | .forsRoots _ => .forsRoots
  | _ => .leaf

/-- A payload of a position's slot as a message of its target function (`0` for the positions
that are no target). -/
def tcrMsg (v : QTable) : (p : RawPos) → SlotPayload (posSlot v p) → TcrMsg (tcrFnOf p)
  | .leaf .., d => d
  | .node .., d => d
  | .forsNode .., d => d
  | .forsRoots _, d => d
  | .prfKey, _ => fun _ ↦ 0
  | .publicSeed, _ => fun _ ↦ 0
  | .chainStart .., _ => fun _ ↦ 0
  | .chain .., _ => fun _ ↦ 0
  | .forsSecret .., _ => fun _ ↦ 0
  | .forsLeaf .., _ => fun _ ↦ 0
  | .prfMsg _, _ => fun _ ↦ 0
  | .hmsg _, _ => fun _ ↦ 0

/-- The honest message of a target position. -/
def tcrMsgOf (v : QTable) (p : RawPos) : TcrMsg (tcrFnOf p) :=
  tcrMsg v p (posPayload v p)

theorem tcrMsg_injective (v : QTable) {p : RawPos} (hp : IsTarget p) :
    Function.Injective (tcrMsg v p) := by
  cases p with
  | leaf | node | forsNode | forsRoots => exact fun _ _ h ↦ h
  | _ => exact False.elim hp

/-- **A target position as a target input**: its slot as the tweak, a payload of the slot as the
message of its target function; the input is the slot's honest input. -/
theorem tcrColl_layout_tcrMsg (v : QTable) (P : PublicParameter) (p : Pos) (hp : IsTarget p.1)
    (d : SlotPayload (posSlot v p.1)) :
    tcrColl.layout (tcrFnOf p.1) P (posSlot v p.1) (tcrMsg v p.1 d) =
      slotInput (pubKey P) 0 (posSlot v p.1) d := by
  obtain ⟨p, hin⟩ := p
  have hr := slotInRange_posSlot v ⟨p, hin⟩
  cases p with
  | leaf => rfl
  | node => exact ite_eq_left hr
  | forsNode => exact ite_eq_left hr
  | forsRoots => rfl
  | _ => exact False.elim hp

/-- The honest message of a target position gives its honest input. -/
theorem tcrColl_layout_tcrMsgOf (v : QTable) (P : PublicParameter) (p : Pos) (hp : IsTarget p.1) :
    tcrColl.layout (tcrFnOf p.1) P (posSlot v p.1) (tcrMsgOf v p.1) =
      slotInput (pubKey P) 0 (posSlot v p.1) (posPayload v p.1) :=
  tcrColl_layout_tcrMsg v P p hp _

/-- A target input at a fixed table is `thSlot`. -/
theorem simulateQ_tcrColl_eval (W : OracleWorld) (tab : W.Tab) (v : QTable) (P : PublicParameter)
    (p : Pos) (hp : IsTarget p.1) (d : SlotPayload (posSlot v p.1)) :
    simulateQ (W.eager tab) (tcrColl.eval W (tcrFnOf p.1) P (posSlot v p.1) (tcrMsg v p.1 d)) =
      pure (thSlot (W.hashOf tab) P (posSlot v p.1) d) := by
  rw [simulateQ_eval, tcrColl_layout_tcrMsg v P p hp d]
  rfl

/-! ## CPRE: the WOTS chains and the FORS leaves -/

/-- The chains of CPRE: chain `i` of the WOTS key `K`, or the FORS leaf `(idx, κ, s)`. -/
abbrev CpreJ : Type :=
  (Key × ChainIndex) ⊕ (Index × ForsTreeIndex × ForsLeafIndex)

instance instFintypeCpreJ : Fintype CpreJ :=
  inferInstanceAs (Fintype ((Key × ChainIndex) ⊕ (Index × ForsTreeIndex × ForsLeafIndex)))

instance instDecidableEqCpreJ : DecidableEq CpreJ :=
  inferInstanceAs (DecidableEq ((Key × ChainIndex) ⊕ (Index × ForsTreeIndex × ForsLeafIndex)))

/-- The step layout: the honest input of a chain or FORS-leaf slot with the value as payload, else
`PK.seed` and the value. -/
def stepLayout (P : PublicParameter) : Slot → Digest → HashInput
  | .chain a b c d e, m => slotInput (pubKey P) 0 (.chain a b c d e) m
  | .forsLeaf a b c, m => slotInput (pubKey P) 0 (.forsLeaf a b c) m
  | _, m => littleEndianBytes 16 P ++ littleEndianBytes 16 m

/-- The chain step: `F` at a chain slot, the FORS leaf hash at a FORS-leaf slot. -/
def cpreStep : TwHash PublicParameter Slot Digest Digest where
  layout _ P t m := stepLayout P t m
  trunc := truncateHash

/-- The step tweaks: step `μ` of WOTS chain `(K, i)` (`μ` below `chainLength - 1`), the FORS leaf
slot. -/
def cpreTweak : CpreJ → ℕ → Slot
  | Sum.inl (K, i), μ => .chain K.1 K.2.1 K.2.2 i ⟨μ % (chainLength - 1), Nat.mod_lt _ (by decide)⟩
  | Sum.inr (idx, κ, s), _ => .forsLeaf idx κ s

/-- The chain lengths: `chainLength - 1` steps for a WOTS chain, one for a FORS leaf. -/
def cpreLen : CpreJ → ℕ
  | Sum.inl _ => chainLength - 1
  | Sum.inr _ => 1

/-- WOTS chains are opened selectively, FORS leaves adaptively. -/
def cpreAdaptive : CpreJ → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

/-- **The CPRE chains of leanSPHINCS.** -/
def cpreChains : Chains PublicParameter Slot CpreJ Digest where
  step := cpreStep
  len := cpreLen
  tweak := cpreTweak
  adaptive := cpreAdaptive

theorem stepLayout_shaped (P : PublicParameter) (t : Slot) (m : Digest) :
    SlotShaped P t (stepLayout P t m) := by
  have hj : SlotShaped P t (littleEndianBytes 16 P ++ littleEndianBytes 16 m) :=
    slotShaped_junk (by simp [littleEndianBytes, junkLengths])
  cases t
  case chain => exact Or.inl ⟨m, trivial, rfl⟩
  case forsLeaf => exact Or.inl ⟨m, trivial, rfl⟩
  all_goals exact hj

theorem cpreStep_lengthLe : cpreChains.step.LengthLe Qrom.maxLen :=
  lengthLe_of_shaped cpreChains.step fun _ P t m ↦ stepLayout_shaped P t m

theorem cpreStep_tweakSeparated : slotColl.TweakSeparated cpreChains.step :=
  tweakSeparated_of_shaped cpreChains.step fun _ P t m ↦ stepLayout_shaped P t m

/-- **The CPRE step tweaks are pairwise distinct.** -/
theorem cpreChains_distinctTweaks : cpreChains.DistinctTweaks := by
  rintro (⟨K, i⟩ | ⟨idx, κ, s⟩) μ (⟨K', i'⟩ | ⟨idx', κ', s'⟩) μ' hμ hμ' h
  · change μ < chainLength - 1 at hμ
    change μ' < chainLength - 1 at hμ'
    obtain ⟨h1, h2, h3, h4, h5⟩ := Slot.chain.inj h
    have h6 := congrArg Fin.val h5
    simp only [Nat.mod_eq_of_lt hμ, Nat.mod_eq_of_lt hμ'] at h6
    exact ⟨congrArg Sum.inl (Prod.ext (Prod.ext h1 (Prod.ext h2 h3)) h4), h6⟩
  · cases h
  · cases h
  · change μ < 1 at hμ
    change μ' < 1 at hμ'
    obtain ⟨rfl, rfl, rfl⟩ := Slot.forsLeaf.inj h
    exact ⟨rfl, by omega⟩

/-- The chain walk with the step `g μ` leaving position `μ`, as the CPRE game runs it. -/
def walkFwd {α : Type} (g : ℕ → α → α) : ℕ → ℕ → α → α
  | _, 0, x => x
  | μ, n + 1, x => walkFwd g (μ + 1) n (g μ x)

theorem walkFwd_succ {α : Type} (g : ℕ → α → α) :
    ∀ μ n x, walkFwd g μ (n + 1) x = g (μ + n) (walkFwd g μ n x)
  | _, 0, _ => rfl
  | μ, n + 1, x => by
    rw [walkFwd, walkFwd_succ g (μ + 1) n, show μ + 1 + n = μ + (n + 1) by omega]
    rfl

/-- A chain walk at a fixed table. -/
theorem simulateQ_walk (W : OracleWorld) (tab : W.Tab) {Par Tw J Val : Type}
    (ch : Chains Par Tw J Val) (P : Par) (j : J) :
    ∀ μ n x, simulateQ (W.eager tab) (ch.walk W P j μ n x) =
      pure (walkFwd (fun μ y ↦ ch.step.trunc (W.hashOf tab (ch.step.layout () P (ch.tweak j μ) y)))
        μ n x)
  | _, 0, _ => by rw [Chains.walk, simulateQ_pure]; rfl
  | μ, n + 1, x => by
    rw [Chains.walk, simulateQ_bind, simulateQ_eval, pure_bind]
    exact simulateQ_walk W tab ch P j (μ + 1) n _

/-- `walkChain` (the scheme's walk, built from the end) is `walkFwd` within the chain. -/
theorem walkChain_eq_walkFwd {c : ℕ} (s : Fin c → Digest → Id Digest) (g : ℕ → Digest → Digest)
    (hg : ∀ μ (h : μ < c) x, g μ x = s ⟨μ, h⟩ x) (μ : ℕ) :
    ∀ n x, μ + n ≤ c → walkChain s μ n x = walkFwd g μ n x
  | 0, _, _ => rfl
  | n + 1, x, h => by
    rw [walkFwd_succ, ← walkChain_eq_walkFwd s g hg μ n x (by omega), hg (μ + n) (by omega)]
    show (if h' : μ + n < c then s ⟨μ + n, h'⟩ (walkChain s μ n x) else pure 0) = _
    rw [dite_eq_left (by omega)]

/-- **The CPRE walk of a WOTS chain at a fixed table is `walkH`**, within the chain. -/
theorem simulateQ_cpre_walk_wots (W : OracleWorld) (tab : W.Tab) (P : PublicParameter) (K : Key)
    (i : ChainIndex) {μ n : ℕ} (h : μ + n ≤ chainLength - 1) (z : Digest) :
    simulateQ (W.eager tab) (cpreChains.walk W P (Sum.inl (K, i)) μ n z) =
      pure (walkH (W.hashOf tab) P K i μ n z) := by
  rw [simulateQ_walk]
  refine congrArg pure (walkChain_eq_walkFwd _ _ ?_ μ n z h).symm
  intro ν hν x
  have hf : (⟨ν % (chainLength - 1), Nat.mod_lt _ (by decide)⟩ : ChainStep) = ⟨ν, hν⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hν)
  show truncateHash (W.hashOf tab (slotInput (pubKey P) 0
    (.chain K.1 K.2.1 K.2.2 i ⟨ν % (chainLength - 1), Nat.mod_lt _ (by decide)⟩) x)) = _
  rw [hf]
  rfl

/-- **The CPRE walk of a FORS leaf at a fixed table is the FORS leaf hash.** -/
theorem simulateQ_cpre_walk_fors (W : OracleWorld) (tab : W.Tab) (P : PublicParameter)
    (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) (μ : ℕ) (z : Digest) :
    simulateQ (W.eager tab) (cpreChains.walk W P (Sum.inr (idx, κ, s)) μ 1 z) =
      pure (thSlot (W.hashOf tab) P (.forsLeaf idx κ s) z) := by
  rw [simulateQ_walk]
  rfl

/-! ## EncTCR+C: the WOTS+C encoding -/

/-- The encoding layout: the honest input of an encoding slot with the message and the counter's
32-bit encoding, else `PK.seed`, the message and the counter's encoding. -/
def encLayout (P : PublicParameter) : Slot → Digest × ℕ → HashInput
  | .enc a b c, x => slotInput (pubKey P) 0 (.enc a b c) (x.1, BitVec.ofNat counterBits x.2)
  | _, x =>
      littleEndianBytes 16 P ++ littleEndianBytes 16 x.1 ++
        bigEndianBytes 4 (BitVec.ofNat counterBits x.2)

/-- The encoding digest `T_e`. -/
def encHash : TwHash PublicParameter Slot (Digest × ℕ) Digest where
  layout _ P t x := encLayout P t x
  trunc := truncateHash

/-- The codeword test of the encoding: the digest decodes (digit sum `T`). Irreducible, so that
unification never evaluates the decoding. -/
@[irreducible] def encIsCode (d : Digest) : Bool :=
  (TargetSum.decodeDigest d).isSome

/-- **The WOTS+C encoding of leanSPHINCS**: codewords are the digests of digit sum `T`, counters
below `2^32`. -/
def encCtr : CtrEnc PublicParameter Slot Digest Digest where
  hash := encHash
  isCode := encIsCode
  limit := encodingAttemptLimit

theorem encLayout_shaped (P : PublicParameter) (t : Slot) (x : Digest × ℕ) :
    SlotShaped P t (encLayout P t x) := by
  have hj : SlotShaped P t (littleEndianBytes 16 P ++ littleEndianBytes 16 x.1 ++
      bigEndianBytes 4 (BitVec.ofNat counterBits x.2)) :=
    slotShaped_junk (by simp [littleEndianBytes, bigEndianBytes, junkLengths])
  cases t
  case enc => exact Or.inl ⟨_, trivial, rfl⟩
  all_goals exact hj

theorem encHash_lengthLe : encCtr.hash.LengthLe Qrom.maxLen :=
  lengthLe_of_shaped encCtr.hash fun _ P t x ↦ encLayout_shaped P t x

theorem encHash_tweakSeparated : slotColl.TweakSeparated encCtr.hash :=
  tweakSeparated_of_shaped encCtr.hash fun _ P t x ↦ encLayout_shaped P t x

/-- Grinding answered by the digests `dig c`. -/
def grindWith {Dig : Type} (dig : ℕ → Dig) (isCode : Dig → Bool) : ℕ → ℕ → Option (ℕ × Dig)
  | _, 0 => none
  | c, n + 1 => if isCode (dig c) then some (c, dig c) else grindWith dig isCode (c + 1) n

/-- Grinding at a fixed table. -/
theorem simulateQ_grind (W : OracleWorld) (tab : W.Tab) {Par Tw Msg Dig : Type}
    (e : CtrEnc Par Tw Msg Dig) (P : Par) (t : Tw) (m : Msg) :
    ∀ c n, simulateQ (W.eager tab) (e.grind W P t m c n) =
      pure (grindWith (fun c ↦ e.hash.trunc (W.hashOf tab (e.hash.layout () P t (m, c)))) e.isCode
        c n)
  | _, 0 => by rw [CtrEnc.grind, simulateQ_pure]; rfl
  | c, n + 1 => by
    simp only [CtrEnc.grind, simulateQ_bind, simulateQ_eval, pure_bind, grindWith]
    split_ifs
    · exact simulateQ_pure _ _
    · exact simulateQ_grind W tab e P t m (c + 1) n

theorem encDigest_cellHash (h : HashInput → HashOutput) (v : QTable) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (m : Digest) (c : EncodingCounter) :
    v.encDigest (cellHash h) l τ e m c = thSlot h v.publicSeed (.enc l τ e) (m, c) := by
  show truncateHash (h (Qrom.decodeInput (Quantum.Qrom.Sphincs.encCell v.publicSeed l τ e m c))) = _
  rw [Qrom.decodeInput_of_encodeInput_eq_some
    (Quantum.Qrom.Sphincs.encodeInput_encCell v.publicSeed l τ e m c)]
  rfl

theorem selectFrom_succ_of_some {H : Qrom.HashDomain → HashOutput} {v : QTable} {l : Layer}
    {τ : TreeIndex} {e : TreeLeafIndex} {m : Digest} {n c : ℕ} {x : Encoding}
    (hx : TargetSum.decodeDigest (v.encDigest H l τ e m (BitVec.ofNat counterBits c)) = some x) :
    v.selectFrom H l τ e m (n + 1) c = some (BitVec.ofNat counterBits c, x) := by
  rw [QTable.selectFrom, hx]

theorem selectFrom_succ_of_none {H : Qrom.HashDomain → HashOutput} {v : QTable} {l : Layer}
    {τ : TreeIndex} {e : TreeLeafIndex} {m : Digest} {n c : ℕ}
    (hx : TargetSum.decodeDigest (v.encDigest H l τ e m (BitVec.ofNat counterBits c)) = none) :
    v.selectFrom H l τ e m (n + 1) c = v.selectFrom H l τ e m n (c + 1) := by
  rw [QTable.selectFrom, hx]

theorem encCtr_isCode : encCtr.isCode = encIsCode :=
  rfl

/-- Grinding from counter `c` with the encoding digests `D` is the counter search of the table. -/
theorem grindWith_eq_selectFrom (H : Qrom.HashDomain → HashOutput) (v : QTable) (l : Layer)
    (τ : TreeIndex) (e : TreeLeafIndex) (m : Digest) (dig : ℕ → Digest)
    (D : EncodingCounter → Digest) (hD : ∀ k, v.encDigest H l τ e m k = D k)
    (hdig : ∀ c, dig c = D (BitVec.ofNat counterBits c)) :
    ∀ n c, c + n ≤ 2 ^ counterBits →
      grindWith dig encIsCode c n =
        (v.selectFrom H l τ e m n c).map fun sel ↦ (sel.1.toNat, D sel.1)
  | 0, _, _ => rfl
  | n + 1, c, hc => by
    have ih := grindWith_eq_selectFrom H v l τ e m dig D hD hdig n (c + 1) (by omega)
    rw [grindWith, hdig c, encIsCode]
    cases hx : TargetSum.decodeDigest (D (BitVec.ofNat counterBits c)) with
    | none =>
      rw [selectFrom_succ_of_none ((congrArg TargetSum.decodeDigest (hD _)).trans hx)]
      exact ih
    | some x =>
      have hc' : (BitVec.ofNat counterBits c).toNat = c := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [selectFrom_succ_of_some ((congrArg TargetSum.decodeDigest (hD _)).trans hx)]
      exact congrArg some (Prod.ext hc'.symm rfl)

/-- **Grinding at a fixed table is the table's counter search**: the target `(T_e, m)` of the key
`(l, τ, e)` is answered with the selected counter (as a number) and its encoding digest. -/
theorem simulateQ_encCtr_grind (W : OracleWorld) (tab : W.Tab) (v : QTable) {P : PublicParameter}
    (hP : v.publicSeed = P) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (m : Digest) :
    simulateQ (W.eager tab) (encCtr.grind W P (.enc l τ e) m 0 encCtr.limit) =
      pure ((v.select (cellHash (W.hashOf tab)) l τ e m).map fun sel ↦
        (sel.1.toNat, thSlot (W.hashOf tab) P (.enc l τ e) (m, sel.1))) := by
  rw [simulateQ_grind, encCtr_isCode]
  refine congrArg pure (grindWith_eq_selectFrom _ v l τ e m _
    (fun k ↦ thSlot (W.hashOf tab) P (.enc l τ e) (m, k)) (fun k ↦ ?_) (fun _ ↦ rfl)
    encodingAttemptLimit 0 (Nat.zero_add _).le)
  rw [encDigest_cellHash, hP]

/-! ## KIM-PRF: the `SK.seed`-keyed calls -/

/-- The calls keyed by `SK.seed` (D1). -/
inductive KimDom where
  /-- S1: `PK.seed = Trunc_16(H(leanSPHINCS ‖ SK.seed ‖ 0))`. -/
  | publicSeed
  /-- S2: `SK.prf = H(leanSPHINCS ‖ SK.seed ‖ 1)`. -/
  | prfKey
  /-- S3: a secret `PRF(P, SK.seed, ADRS_d)`, for every public seed `P`. -/
  | prf (P : PublicParameter) (d : KeygenDomain)
  deriving DecidableEq

/-- `KimDom` as a sum of products of finite types. -/
def kimDomEquiv : KimDom ≃ Bool ⊕ (PublicParameter ×
    ((Layer × TreeIndex × TreeLeafIndex × ChainIndex) ⊕ (Index × ForsTreeIndex × ForsLeafIndex)))
    where
  toFun
    | .publicSeed => .inl false
    | .prfKey => .inl true
    | .prf P (.oneTimeChain l τ e i) => .inr (P, .inl (l, τ, e, i))
    | .prf P (.forsSecret idx κ s) => .inr (P, .inr (idx, κ, s))
  invFun
    | .inl false => .publicSeed
    | .inl true => .prfKey
    | .inr (P, .inl (l, τ, e, i)) => .prf P (.oneTimeChain l τ e i)
    | .inr (P, .inr (idx, κ, s)) => .prf P (.forsSecret idx κ s)
  left_inv x := by rcases x with _ | _ | ⟨P, _ | _⟩ <;> rfl
  right_inv y := by rcases y with (_ | _) | ⟨P, ⟨l, τ, e, i⟩ | ⟨idx, κ, s⟩⟩ <;> rfl

instance instFintypeKimDom : Fintype KimDom :=
  Fintype.ofEquiv _ kimDomEquiv.symm

/-- The formats: the bytes before and after the key `SK.seed`. -/
def kimFmt : KimDom → HashInput × HashInput
  | .publicSeed => (seedTag, [0])
  | .prfKey => (seedTag, [1])
  | .prf P d => (littleEndianBytes 16 P ++ (keygenDomainFields d).toBytes, [])

/-- The truncations: `SK.prf` whole; `PK.seed` and the secrets their first 16 bytes. -/
def kimTrunc : KimDom → HashOutput → HashOutput
  | .prfKey, o => o
  | _, o => (truncateHash o).setWidth 256

theorem truncateHash_setWidth (o : HashOutput) :
    truncateHash ((truncateHash o).setWidth 256) = truncateHash o := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [truncateHash, digestBits] at hi ⊢
  simp [hi, show i < 256 by omega]

theorem truncateHash_kimTrunc (x : KimDom) (o : HashOutput) :
    truncateHash (kimTrunc x o) = truncateHash o := by
  cases x with
  | prfKey => rfl
  | publicSeed => exact truncateHash_setWidth o
  | prf => exact truncateHash_setWidth o

/-- S1: the format of `PK.seed` keyed by `S0` is the key-expansion input of domain `0`. -/
theorem kimInput_publicSeed (S0 : MasterSeed) :
    (kimFmt .publicSeed).1 ++ littleEndianBytes 32 S0 ++ (kimFmt .publicSeed).2 =
      keyDerivationInput S0 0 :=
  rfl

/-- S2: the format of `SK.prf` keyed by `S0` is the key-expansion input of domain `1`. -/
theorem kimInput_prfKey (S0 : MasterSeed) :
    (kimFmt .prfKey).1 ++ littleEndianBytes 32 S0 ++ (kimFmt .prfKey).2 =
      keyDerivationInput S0 1 :=
  rfl

/-- S3: the format of the secret `d` under `P` keyed by `S0` is the `PRF` input. -/
theorem kimInput_prf (S0 : MasterSeed) (P : PublicParameter) (d : KeygenDomain) :
    (kimFmt (.prf P d)).1 ++ littleEndianBytes 32 S0 ++ (kimFmt (.prf P d)).2 =
      addressedHashInput P (keygenDomainFields d) (littleEndianBytes 32 S0) :=
  List.append_nil _

/-- S3 under the key's public seed is the honest input of the slot `.prf d`. -/
theorem kimInput_prf_slotInput (key : ExpandedKey) (root : Digest) (d : KeygenDomain) :
    (kimFmt (.prf key.publicSeed d)).1 ++ littleEndianBytes 32 key.secretSeed ++
        (kimFmt (.prf key.publicSeed d)).2 = slotInput key root (.prf d) () :=
  List.append_nil _

theorem kimFmt_injective : Function.Injective kimFmt := by
  have hne : ∀ P d, (kimFmt (.prf P d)).2 = [] := fun _ _ ↦ rfl
  intro x y h
  cases x with
  | publicSeed =>
    cases y with
    | publicSeed => rfl
    | prfKey => exact absurd (congrArg (fun p ↦ p.2.head?) h) (by decide)
    | prf P d => exact absurd ((congrArg Prod.snd h).trans (hne P d)) (by simp [kimFmt])
  | prfKey =>
    cases y with
    | publicSeed => exact absurd (congrArg (fun p ↦ p.2.head?) h) (by decide)
    | prfKey => rfl
    | prf P d => exact absurd ((congrArg Prod.snd h).trans (hne P d)) (by simp [kimFmt])
  | prf P d =>
    cases y with
    | publicSeed => exact absurd ((congrArg Prod.snd h).symm.trans (hne P d)) (by simp [kimFmt])
    | prfKey => exact absurd ((congrArg Prod.snd h).symm.trans (hne P d)) (by simp [kimFmt])
    | prf P' d' =>
      obtain ⟨hP, ha⟩ := List.append_inj (congrArg Prod.fst h)
        (by rw [length_littleEndianBytes, length_littleEndianBytes])
      have hd := congrArg Quantum.Sphincs.slotOfAddress (toBytes_injective ha)
      rw [slotOfAddress_keygenDomainFields, slotOfAddress_keygenDomainFields] at hd
      rw [littleEndianBytes_injective 16 hP, Slot.prf.inj (Option.some.inj hd)]

/-- **Obligation (b)**: distinct calls have distinct formats. -/
theorem kim_fmtInjective : KimFmtInjective kimFmt kimTrunc :=
  fun _ _ h ↦ kimFmt_injective (congrArg Prod.fst h)

/-- **Obligation (a) for KIM-PRF.** -/
theorem kim_lengthLe : KimLengthLe kimFmt (littleEndianBytes 32) Qrom.maxLen := by
  intro x K
  cases x with
  | publicSeed => simp [kimFmt, seedTag, length_littleEndianBytes, Qrom.maxLen]
  | prfKey => simp [kimFmt, seedTag, length_littleEndianBytes, Qrom.maxLen]
  | prf P d =>
    simp [kimFmt, length_littleEndianBytes, Quantum.Sphincs.length_toBytes, Qrom.maxLen]

/-! ## PRF_msg -/

/-- The domain of `PRF_msg`: the optional randomness (`PK.seed`) and the message. -/
abbrev MsgDom : Type :=
  PublicParameter × Message

/-- The bytes after the key `SK.prf`: the optional randomness and the framed message. -/
def msgBytes (x : MsgDom) : HashInput :=
  littleEndianBytes 16 x.1 ++ framedMessage x.2

/-- `SK.prf = K` followed by `msgBytes (P, M)` is the `PRF_msg` input with randomness `P`. -/
theorem msgInput_eq (K : HashOutput) (x : MsgDom) :
    littleEndianBytes 32 K ++ msgBytes x = prfMessageInput K x.1 x.2 :=
  (List.append_assoc _ _ _).symm

/-- The input of the prefix-keyed function under `SK.prf = K` is the `PRF_msg` input. -/
theorem prfMsgInput_eq (K : HashOutput) (x : MsgDom) :
    ([] : HashInput) ++ littleEndianBytes 32 K ++ msgBytes x = prfMessageInput K x.1 x.2 :=
  (List.append_assoc _ _ _).symm

/-- Under the key's `SK.prf` and `PK.seed`, the honest input of the slot `.prfMsg M`. -/
theorem prfMsgInput_slotInput (key : ExpandedKey) (root : Digest) (M : Message) :
    ([] : HashInput) ++ littleEndianBytes 32 key.secretPrfKey ++ msgBytes (key.publicSeed, M) =
      slotInput key root (.prfMsg M) () :=
  prfMsgInput_eq key.secretPrfKey (key.publicSeed, M)

/-- **Obligation (a) for PRF_msg.** -/
theorem prfMsg_lengthLe :
    KimLengthLe (fun x : MsgDom ↦ (([] : HashInput), msgBytes x)) (littleEndianBytes 32)
      Qrom.maxLen := by
  intro x K
  show (([] : HashInput) ++ littleEndianBytes 32 K ++ msgBytes x).length ≤ _
  rw [prfMsgInput_eq K x]
  exact (length_prfMessageInput K x.1 x.2).trans_le (by decide)

/-! ## ITSR: the message hash -/

/-- **The message hash of leanSPHINCS**: the two `H_msg` calls on `R ‖ PK.seed ‖ PK.root ‖ M`,
their outputs truncated to the digest, the FORS instance and one leaf per tree. -/
def itsrMap :
    MsgMap Randomizer (PublicParameter × Digest × Message) (Index × ForsTreeIndex × ForsLeafIndex)
    where
  inputs R x := [messageDigestInput R x.1 x.2.1 x.2.2 0, messageDigestInput R x.1 x.2.1 x.2.2 1]
  cells outs := digestCells (truncateMessageDigest fun c ↦ outs.getD c.val 0)

theorem simulateQ_mapM_hash (W : OracleWorld) (tab : W.Tab) :
    ∀ l : List HashInput, simulateQ (W.eager tab) (l.mapM W.hash) = pure (l.map (W.hashOf tab))
  | [] => by rw [List.mapM_nil, simulateQ_pure]; rfl
  | a :: l => by
    rw [List.mapM_cons, simulateQ_bind, W.simulateQ_hash, pure_bind, simulateQ_bind,
      simulateQ_mapM_hash W tab l, pure_bind, simulateQ_pure]
    rfl

/-- **The selected cells at a fixed table** are those of `digestOf`. -/
theorem simulateQ_itsr_select (W : OracleWorld) (tab : W.Tab) (R : Randomizer) (pk : PublicKey)
    (M : Message) :
    simulateQ (W.eager tab) (itsrMap.select W R (pk.publicSeed, pk.root, M)) =
      pure (digestCells (digestOf (W.hashOf tab) pk R M)) := by
  rw [MsgMap.select, simulateQ_map, simulateQ_mapM_hash, map_pure]
  refine congrArg pure (congrArg digestCells (congrArg truncateMessageDigest (funext fun c ↦ ?_)))
  obtain ⟨c, hc⟩ := c
  have hc2 : c < 2 := hc
  interval_cases c <;> rfl

/-- **The length obligation of ITSR**: both `H_msg` inputs have 84 bytes. -/
theorem itsr_lengthLe (R : Randomizer) (x : PublicParameter × Digest × Message) :
    ∀ y ∈ itsrMap.inputs R x, y.length ≤ Qrom.maxLen := by
  intro y hy
  simp only [itsrMap, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> rw [length_messageDigestInput] <;> decide

end Quantum.StdModel.Sphincs

end
