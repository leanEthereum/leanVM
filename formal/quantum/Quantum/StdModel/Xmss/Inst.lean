module

public import Quantum.StdModel.Xmss.Gen
public import Quantum.StdModel.Formats
public import Quantum.StdModel.Props.EncTcr
public import Quantum.StdModel.Props.Cpre
public import Quantum.StdModel.Props.Tcr

@[expose] public section

/-!
# leanXMSS instances of EncTCR$, CPRE and SM-TCR-C

The tweaks of the chain and tree games are the addressable slots of leanXMSS (`XTw`); the public
parameter is `P` and every tweakable hash truncates by `truncateHash`.

* `xmssEnc` (EncTCR$): the message digest at the tweak `(l, e)`, input `slotInput P (.msg l e)`;
  grinding at a fixed table is `grind` (`simulateQ_xmssEnc_grind`, `simulateQ_xmssEnc_encode`),
  the digest `Over.messageDigest` (`simulateQ_xmssEnc_hash`).
* `xmssStep`: the chain step, the honest input of a chain slot and empty at any other slot.
* `xmssChains` (CPRE): chain `(l, e, i)` of length `chainLength - 1`, step `μ` at the tweak
  `.chain l e μ i`, all adaptive; no evaluation collection (`noEval`). The walk at a fixed table
  is `Over.chainWalk` (`simulateQ_xmssChains_walk`).
* `xmssTcrC` (SM-TCR-C targets): the leaf and the node, at a tweak of their own kind the honest
  input of the slot, else `P` followed by the message bytes (so that the targets at such tweaks
  still determine their messages); `xmssTcrD`: the chain step.
* Obligations (`Props.Basic`): `LengthLe` of every collection, `xmssChains_distinctTweaks`,
  `noEval_tweakSeparated`, `xmssTcrD_tweakSeparated` (DIST, `xmss_slotInput_inj`, and the
  lengths of the other inputs).
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open Quantum.Xmss (Slot length_littleEndianBytes)
open Quantum.Qrom.Xmss (Payload slotInput Addressable MsgBytes length_slotInput length_thInput_eq
  length_digestsPayload)

namespace Quantum.StdModel.Xmss

/-- A tweakable hash of a collection, answered by a fixed table. -/
theorem simulateQ_eval (W : OracleWorld) (tab : W.Tab) {Par Tw Fn Out : Type} {Msg : Fn → Type}
    (C : Props.TwColl Par Tw Fn Msg Out) (l : Fn) (P : Par) (t : Tw) (m : Msg l) :
    simulateQ (W.eager tab) (C.eval W l P t m) =
      pure (C.trunc (W.hashOf tab (C.layout l P t m))) := by
  rw [Props.TwColl.eval, simulateQ_map, W.simulateQ_hash, map_pure]

/-! ## Tweaks -/

/-- **The tweaks** of the chain and tree games: the addressable slots. -/
abbrev XTw := {s : Slot // Addressable s}

theorem addressable_chain (l : Layer) (e : KeyIndex) (s : ChainStep) (i : ChainIndex) :
    Addressable (.chain l e s i) :=
  trivial

theorem addressable_leaf (l : Layer) (e : KeyIndex) : Addressable (.leaf l e) :=
  trivial

/-- A node of a layer's tree, level `k + 1 ≤ layerHeight`, index below `2^32`, is addressable. -/
theorem addressable_node (l : Layer) {k j : ℕ} (hk : k < layerHeight) (hj : j < 2 ^ 32) :
    Addressable (.node l (k + 1) j) := by
  have h : layerHeight < 2 ^ 23 := by norm_num [layerHeight]
  exact ⟨by omega, hj⟩

theorem length_slotInput_pos (P : PublicParameter) (s : Slot) (d : Payload s) :
    0 < (slotInput P s d).length := by
  cases s
  case seed =>
    rw [slotInput, List.length_append]
    exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
  all_goals (rw [slotInput, length_thInput_eq]; omega)

/-! ## EncTCR$ -/

/-- **The EncTCR$ instance**: the message digest of key `(l, e)`, `M ‖ ρ` at the address of
`.message l e`; codewords by `Codeword.decode`; `randomizerAttemptLimit` trials `ρ = R_0 + c`. -/
def xmssEnc : Props.SaltEnc PublicParameter (Layer × KeyIndex) MsgBytes Randomizer Digest where
  hash := { layout := fun _ P t d ↦ slotInput P (.msg t.1 t.2) d, trunc := truncateHash }
  isCode d := (Codeword.decode d).isSome
  limit := randomizerAttemptLimit
  shift r0 c := r0 + BitVec.ofNat digestBits c

theorem xmssEnc_lengthLe : xmssEnc.hash.LengthLe Qrom.maxLen :=
  fun _ P t d ↦ length_slotInput P (.msg t.1 t.2) d

theorem xmssEnc_isCode (d : Digest) : xmssEnc.isCode d = (Codeword.decode d).isSome :=
  rfl

theorem xmssEnc_shift (r0 : Randomizer) (c : ℕ) :
    xmssEnc.shift r0 c = r0 + BitVec.ofNat digestBits c :=
  rfl

/-- The EncTCR$ digest at a fixed table is the message digest. -/
theorem simulateQ_xmssEnc_hash (W : OracleWorld) (tab : W.Tab) (P : PublicParameter) (l : Layer)
    (e : KeyIndex) (M : MsgBytes) (ρ : Randomizer) :
    simulateQ (W.eager tab) (xmssEnc.hash.eval W () P (l, e) (M, ρ)) =
      pure (Qrom.Xmss.Over.messageDigest (m := Id) (W.hashOf tab) P l e M.1 ρ) := by
  rw [simulateQ_eval]
  rfl

theorem grind_succ_id (h : HashInput → HashOutput) (P : PublicParameter) (l : Layer)
    (e : KeyIndex) (M : HashInput) (r0 : Randomizer) (n t : ℕ) :
    grind (m := Id) h P l e M r0 (n + 1) t =
      if (Codeword.decode (Qrom.Xmss.Over.messageDigest (m := Id) h P l e M
          (r0 + BitVec.ofNat digestBits t))).isSome then
        pure (some (r0 + BitVec.ofNat digestBits t, Qrom.Xmss.Over.messageDigest (m := Id) h P l
          e M (r0 + BitVec.ofNat digestBits t)))
      else grind (m := Id) h P l e M r0 n (t + 1) :=
  rfl

/-- **EncTCR$ grinding at a fixed table** (trial `c`, `n` trials left) is `grind`. -/
theorem simulateQ_xmssEnc_grind (W : OracleWorld) (tab : W.Tab) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (M : MsgBytes) (r0 : Randomizer) :
    ∀ c n : ℕ, simulateQ (W.eager tab) (xmssEnc.grind W P (l, e) M r0 c n) =
      pure (grind (m := Id) (W.hashOf tab) P l e M.1 r0 n c)
  | c, 0 => by
    rw [Props.SaltEnc.grind, simulateQ_pure]
    rfl
  | c, n + 1 => by
    rw [Props.SaltEnc.grind, simulateQ_bind, simulateQ_xmssEnc_hash, pure_bind, grind_succ_id,
      xmssEnc_shift, xmssEnc_isCode]
    split_ifs
    · rw [simulateQ_pure]
      rfl
    · exact simulateQ_xmssEnc_grind W tab P l e M r0 (c + 1) n

/-- The EncTCR$ answer at a fixed table is the ideal signer's encoding by `grind`. -/
theorem simulateQ_xmssEnc_encode (W : OracleWorld) (tab : W.Tab) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (M : MsgBytes) (r0 : Randomizer) :
    simulateQ (W.eager tab) (xmssEnc.grind W P (l, e) M r0 0 xmssEnc.limit) =
      pure (grind (m := Id) (W.hashOf tab) P l e M.1 r0 randomizerAttemptLimit 0) :=
  simulateQ_xmssEnc_grind W tab P l e M r0 0 randomizerAttemptLimit

/-! ## The chain step -/

/-- The chain step's input at a slot: the honest input of a chain slot, empty at any other. -/
def stepLayout (P : PublicParameter) : Slot → Digest → HashInput
  | .chain l e s i, x => slotInput P (.chain l e s i) x
  | _, _ => []

/-- **The chain step** `F(P, T, x)` at the tweak `T`. -/
def xmssStep : Props.TwHash PublicParameter XTw Digest Digest where
  layout _ P t x := stepLayout P t.1 x
  trunc := truncateHash

theorem length_stepLayout_chain (P : PublicParameter) (l : Layer) (e : KeyIndex) (s : ChainStep)
    (i : ChainIndex) (x : Digest) : (stepLayout P (.chain l e s i) x).length = 64 := by
  show (thInput P (hashDomainFields (.chain l e s)) (Verification.chainPayload i x)).length = 64
  simp only [length_thInput_eq, Verification.chainPayload, littleEndianBytes, List.length_append,
    List.length_ofFn]

theorem xmssStep_lengthLe : xmssStep.LengthLe Qrom.maxLen := by
  rintro _ P ⟨t, -⟩ x
  show (stepLayout P t x).length ≤ _
  cases t with
  | chain l e s i => exact length_slotInput P (.chain l e s i) x
  | leaf | node | msg | prf | rnd | param | seed => exact Nat.zero_le _

/-- The chain step at a chain slot, at a fixed table, is the scheme's chain step. -/
theorem simulateQ_xmssStep_eval (W : OracleWorld) (tab : W.Tab) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (s : ChainStep) (i : ChainIndex) (hs : Addressable (.chain l e s i))
    (x : Digest) :
    simulateQ (W.eager tab) (xmssStep.eval W () P ⟨.chain l e s i, hs⟩ x) =
      pure (Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P (.chain l e s)
        (Verification.chainPayload i x)) := by
  rw [simulateQ_eval]
  rfl

/-! ## CPRE -/

/-- **The CPRE instance**: chain `i` of key `(l, e)`, of length `chainLength - 1`, step `μ` at
the tweak `.chain l e μ i`, openings adaptive. -/
def xmssChains : Props.Chains PublicParameter XTw (Layer × KeyIndex × ChainIndex) Digest where
  step := xmssStep
  len _ := chainLength - 1
  tweak j μ :=
    ⟨.chain j.1 j.2.1 ⟨μ % (chainLength - 1), Nat.mod_lt _ (by decide)⟩ j.2.2, trivial⟩
  adaptive _ := true

/-- **The empty evaluation collection** of the CPRE game. -/
def noEval : Props.TwColl PublicParameter XTw Empty (fun _ ↦ Unit) Digest where
  layout l := l.elim
  trunc := truncateHash

theorem xmssChains_tweak (l : Layer) (e : KeyIndex) (i : ChainIndex) {μ : ℕ}
    (hμ : μ < chainLength - 1) :
    xmssChains.tweak (l, e, i) μ = ⟨.chain l e ⟨μ, hμ⟩ i, trivial⟩ :=
  Subtype.ext (congrArg (fun s : ChainStep ↦ Slot.chain l e s i) (Fin.ext (Nat.mod_eq_of_lt hμ)))

theorem xmssChains_distinctTweaks : xmssChains.DistinctTweaks := by
  rintro ⟨l, e, i⟩ μ ⟨l', e', i'⟩ μ' hμ hμ' h
  rw [xmssChains_tweak l e i hμ, xmssChains_tweak l' e' i' hμ'] at h
  have hv := congrArg Subtype.val h
  injection hv with h1 h2 h3 h4
  subst h1 h2 h4
  exact ⟨rfl, congrArg Fin.val h3⟩

theorem xmssChains_step_lengthLe : xmssChains.step.LengthLe Qrom.maxLen :=
  xmssStep_lengthLe

theorem noEval_lengthLe : noEval.LengthLe Qrom.maxLen :=
  fun l ↦ l.elim

theorem noEval_tweakSeparated : noEval.TweakSeparated xmssChains.step :=
  fun _ _ _ _ l ↦ l.elim

/-- Step `μ < chainLength - 1` of chain `(l, e, i)` at a fixed table is the scheme's step. -/
theorem simulateQ_xmssChains_step (W : OracleWorld) (tab : W.Tab) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (i : ChainIndex) {μ : ℕ} (hμ : μ < chainLength - 1) (x : Digest) :
    simulateQ (W.eager tab) (xmssChains.step.eval W () P (xmssChains.tweak (l, e, i) μ) x) =
      pure (Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P (.chain l e ⟨μ, hμ⟩)
        (Verification.chainPayload i x)) := by
  rw [xmssChains_tweak l e i hμ]
  exact simulateQ_xmssStep_eval W tab P l e _ i trivial x

theorem walkChain_succ_id {K : ℕ} (step : Fin K → Digest → Id Digest) (μ n : ℕ) (x : Digest) :
    walkChain step μ (n + 1) x =
      if h : μ + n < K then step ⟨μ + n, h⟩ (walkChain step μ n x) else pure 0 :=
  rfl

/-- A chain walk in `Id`, below the end, starts with its first step. -/
theorem walkChain_shift_id {K : ℕ} (step : Fin K → Digest → Id Digest) :
    ∀ (n μ : ℕ) (x : Digest) (h : μ + n < K),
      walkChain step μ (n + 1) x = walkChain step (μ + 1) n (step ⟨μ, by omega⟩ x)
  | 0, μ, x, h => by
    rw [walkChain_succ_id, dite_eq_left h]
    rfl
  | n + 1, μ, x, h => by
    rw [walkChain_succ_id, dite_eq_left h, walkChain_shift_id step n μ x (by omega),
      walkChain_succ_id, dite_eq_left (show μ + 1 + n < K by omega)]
    congr 1
    exact Fin.ext (show μ + (n + 1) = μ + 1 + n by omega)

theorem chainWalk_succ_id (h : HashInput → HashOutput) (P : PublicParameter) (l : Layer)
    (e : KeyIndex) (i : ChainIndex) (μ n : ℕ) (x : Digest) (hμ : μ + n < chainLength - 1) :
    Qrom.Xmss.Over.chainWalk (m := Id) h P l e i μ (n + 1) x =
      Qrom.Xmss.Over.chainWalk (m := Id) h P l e i (μ + 1) n
        (Qrom.Xmss.Over.tweakableHash (m := Id) h P (.chain l e ⟨μ, by omega⟩)
          (Verification.chainPayload i x)) :=
  walkChain_shift_id _ n μ x hμ

/-- **The CPRE walk at a fixed table**, within the chain, is the scheme's chain walk. -/
theorem simulateQ_xmssChains_walk (W : OracleWorld) (tab : W.Tab) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (i : ChainIndex) :
    ∀ (μ n : ℕ) (x : Digest), μ + n ≤ chainLength - 1 →
      simulateQ (W.eager tab) (xmssChains.walk W P (l, e, i) μ n x) =
        pure (Qrom.Xmss.Over.chainWalk (m := Id) (W.hashOf tab) P l e i μ n x)
  | μ, 0, x, _ => by
    rw [Props.Chains.walk, simulateQ_pure]
    rfl
  | μ, n + 1, x, h => by
    rw [Props.Chains.walk, simulateQ_bind,
      simulateQ_xmssChains_step W tab P l e i (show μ < chainLength - 1 by omega), pure_bind,
      simulateQ_xmssChains_walk W tab P l e i (μ + 1) n _ (by omega),
      chainWalk_succ_id _ P l e i μ n x (by omega)]

/-! ## SM-TCR-C -/

/-- The SM-TCR-C target functions: the leaf and the tree node. -/
inductive TcrFn where
  | leaf
  | node
  deriving DecidableEq

/-- The messages of the target functions: the payloads of their slots. -/
abbrev TcrMsg : TcrFn → Type
  | .leaf => ChainIndex → Digest
  | .node => Digest × Digest

/-- The bytes of a target message, as its slot hashes them. -/
def tcrBytes : (f : TcrFn) → TcrMsg f → HashInput
  | .leaf, m => digestsPayload m
  | .node, m => nodePayload m.1 m.2

/-- The layout of `xmssTcrC`: the honest input of the slot at a tweak of the function's kind,
else `P` followed by the message bytes. -/
def tcrLayout (P : PublicParameter) : (f : TcrFn) → Slot → TcrMsg f → HashInput
  | .leaf, .leaf l e, m => slotInput P (.leaf l e) m
  | .node, .node l k j, m => slotInput P (.node l k j) m
  | f, _, m => littleEndianBytes 16 P ++ tcrBytes f m

/-- **The SM-TCR-C target collection**: the leaf and the node at their slots. -/
def xmssTcrC : Props.TwColl PublicParameter XTw TcrFn TcrMsg Digest where
  layout f P t m := tcrLayout P f t.1 m
  trunc := truncateHash

/-- **The SM-TCR-C evaluation collection**: the chain step. -/
abbrev xmssTcrD : Props.TwHash PublicParameter XTw Digest Digest :=
  xmssStep

theorem length_tcrJunk (P : PublicParameter) (f : TcrFn) (m : TcrMsg f) :
    (littleEndianBytes 16 P ++ tcrBytes f m).length = 48 ∨
      (littleEndianBytes 16 P ++ tcrBytes f m).length = 944 := by
  rw [List.length_append, length_littleEndianBytes]
  cases f with
  | leaf =>
    right
    show 16 + (digestsPayload (n := chainCount) m).length = 944
    rw [length_digestsPayload (n := chainCount) m]
    rfl
  | node =>
    left
    show 16 + (nodePayload m.1 m.2).length = 48
    simp only [nodePayload, littleEndianBytes, List.length_append, List.length_ofFn]

theorem tcrLayout_shape (P : PublicParameter) (f : TcrFn) (t : Slot) (m : TcrMsg f) :
    (∃ d, tcrLayout P f t m = slotInput P t d) ∨
      tcrLayout P f t m = littleEndianBytes 16 P ++ tcrBytes f m := by
  cases f
  case leaf =>
    cases t
    case leaf l e => exact Or.inl ⟨m, rfl⟩
    all_goals exact Or.inr rfl
  case node =>
    cases t
    case node l k j => exact Or.inl ⟨m, rfl⟩
    all_goals exact Or.inr rfl

theorem xmssTcrC_lengthLe : xmssTcrC.LengthLe Qrom.maxLen := by
  rintro f P ⟨t, -⟩ m
  show (tcrLayout P f t m).length ≤ _
  rcases tcrLayout_shape P f t m with ⟨d, hd⟩ | hd
  · rw [hd]
    exact length_slotInput P t d
  · rw [hd]
    rcases length_tcrJunk P f m with h | h <;> rw [h] <;> decide

theorem xmssTcrD_lengthLe : xmssTcrD.LengthLe Qrom.maxLen :=
  xmssStep_lengthLe

/-- **Obligation (c)**: the chain step never produces a target input under another tweak. -/
theorem xmssTcrD_tweakSeparated : xmssTcrD.TweakSeparated xmssTcrC := by
  rintro f P ⟨t, ht⟩ m _ ⟨t', ht'⟩ m' h
  change stepLayout P t' m' = tcrLayout P f t m at h
  apply Subtype.ext
  show t' = t
  cases t' with
  | chain l e s i =>
    rcases tcrLayout_shape P f t m with ⟨d, hd⟩ | hd
    · exact congrArg Sigma.fst (xmss_slotInput_inj P ht' ht (h.trans hd))
    · have hl := congrArg List.length (h.trans hd)
      rw [length_stepLayout_chain] at hl
      rcases length_tcrJunk P f m with h' | h' <;> omega
  | leaf | node | msg | prf | rnd | param | seed =>
    exfalso
    have hl : 0 = (tcrLayout P f t m).length := congrArg List.length h
    rcases tcrLayout_shape P f t m with ⟨d, hd⟩ | hd
    · have := length_slotInput_pos P t d
      rw [hd] at hl
      omega
    · rw [hd] at hl
      rcases length_tcrJunk P f m with h' | h' <;> omega

/-- The leaf target at its slot, at a fixed table, is the scheme's leaf. -/
theorem simulateQ_xmssTcrC_leaf (W : OracleWorld) (tab : W.Tab) (P : PublicParameter) (l : Layer)
    (e : KeyIndex) (hs : Addressable (.leaf l e)) (ends : ChainIndex → Digest) :
    simulateQ (W.eager tab) (xmssTcrC.eval W .leaf P ⟨.leaf l e, hs⟩ ends) =
      pure (Qrom.Xmss.Over.leafHash (m := Id) (W.hashOf tab) P l e ends) := by
  rw [simulateQ_eval]
  rfl

/-- The node target at its slot, at a fixed table, is the scheme's node. -/
theorem simulateQ_xmssTcrC_node (W : OracleWorld) (tab : W.Tab) (P : PublicParameter) (l : Layer)
    (k j : ℕ) (hs : Addressable (.node l k j)) (a b : Digest) :
    simulateQ (W.eager tab) (xmssTcrC.eval W .node P ⟨.node l k j, hs⟩ (a, b)) =
      pure (Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P (.node l k j)
        (nodePayload a b)) := by
  rw [simulateQ_eval]
  rfl

/-- The SM-TCR-C evaluation at a chain slot, at a fixed table, is the scheme's chain step. -/
theorem simulateQ_xmssTcrD_eval (W : OracleWorld) (tab : W.Tab) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (s : ChainStep) (i : ChainIndex) (hs : Addressable (.chain l e s i))
    (x : Digest) :
    simulateQ (W.eager tab) (xmssTcrD.eval W () P ⟨.chain l e s i, hs⟩ x) =
      pure (Qrom.Xmss.Over.tweakableHash (m := Id) (W.hashOf tab) P (.chain l e s)
        (Verification.chainPayload i x)) :=
  simulateQ_xmssStep_eval W tab P l e s i hs x

end Quantum.StdModel.Xmss

end
