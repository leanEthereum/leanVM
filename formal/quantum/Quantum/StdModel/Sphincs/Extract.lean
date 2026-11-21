module

public import Quantum.StdModel.Sphincs.Events
public import Quantum.Qrom.Sphincs.Classify

@[expose] public section

/-!
# leanSPHINCS at a fixed hash: a fresh forgery is in an event

The classical extraction of the standard-model reduction (design, Theorem 2): a forgery that
verifies under `h` against the honest structure `v`, and that the signer did not return, is in one
of the four events `EvItsr`, `EvEnc`, `EvTcr`, `EvCpre` (`win_imp_events`).

The reductions compute their outputs from the forgery's verification only, so the extraction is
relative to a partial sound hash `H : HashInput → Option HashOutput` (`H x = some o` implies
`o = h x`) under which the forgery verifies: the trace-local events `EvTcrT`, `EvEncT`, `EvCpreT`
have their witnesses' inputs answered by `H` and imply the events (`EvTcrT.evTcr`, ...).
`Extract.extractT` and `win_imp_eventsT` are the extraction into them; the total hash `h` answers
in `Option` as `Extract.optH h` (`Extract.verify_optH`), and the forgery's own verification trace
as `Extract.traceH` (`h` on the verifier's queries `Extract.verifyQueries`, `Extract.verify_traceH`,
`win_imp_eventsT'`). The QRPM's `verify_spec` and its companions read off the verifier's calls.
Under the negated trace-local events:

* `Extract.tree_meet`, `Extract.leaf_meet`, `Extract.forsTree_meet`, `Extract.forsRoots_meet`: a
  fold, a one-time leaf, a FORS tree or a FORS key reaching its honest value has the honest
  payloads (else SM-TCR at the first divergence, `foldPath_meet`).
* `Extract.layer_meet`: a layer reaching the honest root of its tree signs the value its key signs
  and is the key's honest layer signature. Each forged chain walks to the honest end, so its value
  is honest and its key's selection opens it at or below the forged digit (else CPRE); the selected
  word is then pointwise below the forged one, equal by incomparability, and the forged pair of
  message and counter is the selected one (else EncTCR+C).
* `Extract.extract_core`: the FORS key and openings are honest and every opened FORS leaf is
  disclosed by a signed message (else CPRE), so the forgery's cells are covered; a fresh pair is an
  ITSR win, a signed pair makes the forgery that message's honest signature.
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open HashSig.OverPermutation (foldPath walkChain)
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (layerSignatures)
open Common.SufCma (SchemeHashSpec)
open Quantum.Sphincs (Key keyOf msgPos LayerOk treeBits)
open Quantum.Qrom.Sphincs (QTable Pos posPayload posSlot SlotPayload slotInput digPos)

namespace Quantum.StdModel.Sphincs

/-! ## The trace-local events -/

/-- **SM-TCR, trace-local**: a target position and a different payload at its slot whose input
`H` answers with the honest digest. -/
def EvTcrT (_h : HashInput → HashOutput) (v : QTable) (H : HashInput → Option HashOutput) :
    Prop :=
  ∃ p : Pos, IsTarget p.1 ∧ ∃ d : SlotPayload (posSlot v p.1), d ≠ posPayload v p.1 ∧
    ∃ o, H (slotInput (pubKey v.publicSeed) 0 (posSlot v p.1) d) = some o ∧
      truncateHash o = v.dig p.1

/-- **EncTCR+C, trace-local**: a key in use, selected at counter `c` on its message `m`, and a
pair `(m', c') ≠ (m, c)` whose trial input `H` answers with the selected encoding digest. -/
def EvEncT (h : HashInput → HashOutput) (v : QTable) (H : HashInput → Option HashOutput) :
    Prop :=
  ∃ K, KeyIn K ∧ ∃ sel, keySelect h v K = some sel ∧ ∃ (m' : Digest) (c' : EncodingCounter),
    (m', c') ≠ (keyMessage v K, sel.1) ∧
      ∃ o, H (slotInput (pubKey v.publicSeed) 0 (.enc K.1 K.2.1 K.2.2) (m', c')) = some o ∧
        truncateHash o = thSlot h v.publicSeed (.enc K.1 K.2.1 K.2.2) (keyMessage v K, sel.1)

/-- **CPRE, trace-local**: as `EvCpre`, with the WOTS walk answered by `H` and the FORS leaf's
input answered by `H`. -/
def EvCpreT (h : HashInput → HashOutput) (v : QTable) (H : HashInput → Option HashOutput)
    (log : List Message) : Prop :=
  (∃ K, KeyIn K ∧ ∃ (i : ChainIndex) (μ : ℕ), μ < chainLength - 1 ∧ ∃ z,
    Quantum.Sphincs.WithHash.chainWalk H v.publicSeed K.1 K.2.1 K.2.2 i μ (chainLength - 1 - μ)
        z = some (v.endpoints K.1 K.2.1 K.2.2 i) ∧
      (z ≠ v.chainValue K.1 K.2.1 K.2.2 i μ ∨
        ¬∃ sel, keySelect h v K = some sel ∧ (sel.2 i).val ≤ μ)) ∨
  ∃ (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) (z : Digest) (o : HashOutput),
    H (slotInput (pubKey v.publicSeed) 0 (.forsLeaf idx κ s) z) = some o ∧
      truncateHash o = v.forsValue idx κ 0 s.val ∧
      (z ≠ v.forsSecret idx κ s ∨ ¬ForsOpened h v log idx κ s)

namespace Extract

/-! ## The verifier answered by `h` -/

/-- The hash `h` as answers in `Id`. -/
def idH (h : HashInput → HashOutput) : QueryImpl SchemeHashSpec Id :=
  fun x ↦ h x

/-- The hash `h` as answers in `Option`, never failing. -/
def optH (h : HashInput → HashOutput) : QueryImpl SchemeHashSpec Option :=
  fun x ↦ some (h x)

variable {h : HashInput → HashOutput} {v : QTable} {H : HashInput → Option HashOutput}

theorem optH_sound : ∀ x o, optH h x = some o → o = h x :=
  fun _ _ hx ↦ (Option.some.inj hx).symm

theorem simulateQ_optH {α : Type} (x : OracleComp SchemeHashSpec α) :
    simulateQ (optH h) x = some (simulateQ (idH h) x) := by
  rw [Quantum.SufCma.simulateQ_eq_pure_evalWithAnswerFn (optH h) (idH h) (fun _ ↦ rfl),
    Quantum.SufCma.simulateQ_eq_pure_evalWithAnswerFn (idH h) (idH h) (fun _ ↦ rfl)]
  rfl

/-- **The verifier in `Option`**: accepting under `h`, it accepts with every hash answered by
`h`. -/
theorem verify_optH {pk : PublicKey} {M : Message} {σ : Signature}
    (hver : Quantum.Qrom.Sphincs.LeanSphincsOver.verify (m := Id) (fun l ↦ h l) pk M σ = true) :
    Quantum.Sphincs.WithHash.verify (optH h) pk M σ = some true := by
  rw [← Quantum.Sphincs.WithHash.simulateQ_verify, simulateQ_optH,
    Quantum.Sphincs.WithHash.simulateQ_verify]
  exact congrArg some ((Quantum.Qrom.Sphincs.verify_eq_withHash (idH h) pk M σ).symm.trans hver)

/-- A chain walk whose steps a partial sound hash answers is the total walk. -/
theorem walkChain_sound {k : ℕ} {stepO : Fin k → Digest → Option Digest}
    {step : Fin k → Digest → Id Digest} (hs : ∀ j d r, stepO j d = some r → r = step j d) :
    ∀ (a n : ℕ) (z r : Digest), walkChain stepO a n z = some r → r = walkChain step a n z
  | _, 0, _, _, hw => (Option.some.inj hw).symm
  | a, n + 1, z, r, hw => by
    obtain ⟨prev, hp, hw⟩ := Option.bind_eq_some_iff.1 hw
    have ih := walkChain_sound hs a n z prev hp
    show r = (if hk' : a + n < k then step ⟨a + n, hk'⟩ (walkChain step a n z)
      else (pure 0 : Id Digest))
    by_cases hk : a + n < k
    · have e : stepO ⟨a + n, hk⟩ prev = some r := (dite_eq_left hk).symm.trans hw
      rw [dite_eq_left hk, ← ih]
      exact hs _ _ _ e
    · have e : (pure 0 : Option Digest) = some r := (dite_eq_right hk).symm.trans hw
      rw [dite_eq_right hk]
      exact (Option.some.inj e).symm

/-- A WOTS walk answered by a partial sound hash is `walkH`. -/
theorem chainWalk_sound (hH : ∀ x o, H x = some o → o = h x) {Q : PublicParameter} {l : Layer}
    {τ : TreeIndex} {e : TreeLeafIndex} {i : ChainIndex} {a n : ℕ} {z r : Digest}
    (hw : Quantum.Sphincs.WithHash.chainWalk H Q l τ e i a n z = some r) :
    walkH h Q (l, τ, e) i a n z = r :=
  (walkChain_sound (stepO := fun j d ↦ Quantum.Sphincs.WithHash.tweakableHash H Q
      (.chain l τ e i j) (littleEndianBytes 16 d))
    (step := fun j d ↦ Quantum.Qrom.Sphincs.LeanSphincsOver.tweakableHash (m := Id)
      (fun x ↦ h x) Q (.chain l τ e i j) (littleEndianBytes 16 d))
    (fun _ _ _ hr ↦ by
      obtain ⟨o, ho, rfl⟩ := Quantum.Sphincs.addressedHash_option hr
      obtain rfl := hH _ _ ho
      rfl) a n z r hw).symm

/-! ## The forgery's verification trace -/

/-- The hash inputs the verifier queries on `(M, σ)` under `pk`, answered by `h`, in order. -/
def verifyQueries (h : HashInput → HashOutput) (pk : PublicKey) (M : Message) (σ : Signature) :
    List HashInput :=
  Quantum.SufCma.queries (idH h)
    (Quantum.Sphincs.WithHash.verify Quantum.Sphincs.WithHash.hashQuery pk M σ)

/-- **The verification trace as a partial hash**: `h` on the inputs the verifier queries, failing
elsewhere. -/
def traceH (h : HashInput → HashOutput) (pk : PublicKey) (M : Message) (σ : Signature) :
    HashInput → Option HashOutput :=
  fun x ↦ if x ∈ verifyQueries h pk M σ then some (h x) else none

theorem traceH_sound {pk : PublicKey} {M : Message} {σ : Signature} :
    ∀ x o, traceH h pk M σ x = some o → o = h x := by
  intro x o hx
  unfold traceH at hx
  split_ifs at hx
  exact (Option.some.inj hx).symm

/-- **The verifier on its own trace**: accepting under `h`, it accepts with every hash answered by
the trace. -/
theorem verify_traceH {pk : PublicKey} {M : Message} {σ : Signature}
    (hver : Quantum.Qrom.Sphincs.LeanSphincsOver.verify (m := Id) (fun l ↦ h l) pk M σ = true) :
    Quantum.Sphincs.WithHash.verify (traceH h pk M σ) pk M σ = some true := by
  have hq := Quantum.Sphincs.simulateQ_option_eq_some (traceH h pk M σ) (idH h)
    (Quantum.Sphincs.WithHash.verify Quantum.Sphincs.WithHash.hashQuery pk M σ)
    (fun q hq ↦ ite_eq_left hq)
  rw [Quantum.Sphincs.WithHash.simulateQ_verify] at hq
  rw [hq]
  have he := Quantum.SufCma.simulateQ_eq_pure_evalWithAnswerFn (idH h) (idH h) (fun _ ↦ rfl)
    (Quantum.Sphincs.WithHash.verify Quantum.Sphincs.WithHash.hashQuery pk M σ)
  rw [Quantum.Sphincs.WithHash.simulateQ_verify] at he
  refine congrArg some (Eq.trans ?_ hver)
  exact he.symm.trans (Quantum.Qrom.Sphincs.verify_eq_withHash (idH h) pk M σ).symm

end Extract

/-! ## The trace-local events are events -/

section Events

variable {h : HashInput → HashOutput} {v : QTable} {H : HashInput → Option HashOutput}

theorem EvTcrT.evTcr (hH : ∀ x o, H x = some o → o = h x) (hT : EvTcrT h v H) : EvTcr h v := by
  obtain ⟨p, hp, d, hne, o, ho, hd⟩ := hT
  obtain rfl := hH _ _ ho
  exact ⟨p, hp, d, hne, hd⟩

theorem EvEncT.evEnc (hH : ∀ x o, H x = some o → o = h x) (hE : EvEncT h v H) : EvEnc h v := by
  obtain ⟨K, hK, sel, hS, m', c', hne, o, ho, hd⟩ := hE
  obtain rfl := hH _ _ ho
  exact ⟨K, hK, sel, hS, m', c', hne, hd⟩

theorem EvCpreT.evCpre (hH : ∀ x o, H x = some o → o = h x) {log : List Message}
    (hC : EvCpreT h v H log) : EvCpre h v log := by
  rcases hC with ⟨K, hK, i, μ, hμ, z, hw, hz⟩ | ⟨idx, κ, s, z, o, ho, hd, hz⟩
  · exact Or.inl ⟨K, hK, i, μ, hμ, z, Extract.chainWalk_sound hH hw, hz⟩
  · obtain rfl := hH _ _ ho
    exact Or.inr ⟨idx, κ, s, z, hd, hz⟩

end Events

namespace Extract

variable {h : HashInput → HashOutput} {v : QTable} {H : HashInput → Option HashOutput}

/-! ## The honest structure -/

/-- The encoding digest of the honest table is `Th` at the trial's slot. -/
theorem encDigest_eq_thSlot (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (m : Digest)
    (c : EncodingCounter) :
    v.encDigest (cellHash h) l τ e m c = thSlot h v.publicSeed (.enc l τ e) (m, c) := by
  change truncateHash (h (Qrom.decodeInput (Quantum.Qrom.Sphincs.codeOf
    (slotInput (pubKey v.publicSeed) 0 (.enc l τ e) (m, c))
    (Quantum.Qrom.Sphincs.length_slotInput_le _ _ _ _)))) = _
  rw [Quantum.Qrom.Sphincs.decodeInput_codeOf]
  rfl

/-- The honest digest of a message is the digest of its honest randomizer under `h`. -/
theorem messageDigest_eq (hv : Honest h v) (M : Message) :
    v.messageDigest M = digestOf h v.publicKey (v.randomizer M) M := by
  refine congrArg truncateMessageDigest (funext fun c ↦ ?_)
  rcases Quantum.Sphincs.digestCall_cases c with rfl | rfl
  · rw [Quantum.Qrom.Sphincs.QTable.digestOutput_zero,
      hv.out (digPos M) (by simp [IsSecret, digPos])]
    rfl
  · rw [Quantum.Qrom.Sphincs.QTable.digestOutput_one, hv.call1]
    rfl

/-- A cell is in the union of the cells of a list when one of them has it. -/
theorem mem_foldr_union {α β : Type} [DecidableEq β] {f : α → Finset β} {x : β} :
    ∀ {L : List α}, (∃ a ∈ L, x ∈ f a) → x ∈ (L.map f).foldr (· ∪ ·) ∅
  | [], ⟨_, ha, _⟩ => by simp at ha
  | _ :: L, ⟨a, ha, hx⟩ => by
    rw [List.map_cons, List.foldr_cons, Finset.mem_union]
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Or.inl hx
    · exact Or.inr (mem_foldr_union ⟨a, ha, hx⟩)

/-! ## No SM-TCR win: the honest payloads -/

/-- **No SM-TCR win**: a payload at a target position's slot whose input `H` answers with the
honest digest is the honest payload. -/
theorem payload_eq (hT : ¬EvTcrT h v H) {p : Pos} (hp : IsTarget p.1)
    {q : SlotPayload (posSlot v p.1)} {o : HashOutput}
    (ho : H (slotInput (pubKey v.publicSeed) 0 (posSlot v p.1) q) = some o)
    (hq : truncateHash o = v.dig p.1) :
    q = posPayload v p.1 := by
  by_contra hne
  exact hT ⟨p, hp, q, hne, o, ho, hq⟩

/-- **A Merkle path of the hypertree ending at its tree's root**: it starts at the honest one-time
leaf and its siblings are the honest ones. -/
theorem tree_meet (hT : ¬EvTcrT h v H) {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    (hτ : τ.val < 2 ^ treeBits l) (he : e.val < 2 ^ layerHeight l) {path : ℕ → Digest}
    {w : Digest}
    (hf : Quantum.Sphincs.WithHash.treeFold H v.publicSeed l τ e path (layerHeight l) w =
      some (v.treeValue l τ (layerHeight l) 0)) :
    w = v.treeValue l τ 0 e.val ∧
      ∀ k < layerHeight l, path k = v.treeValue l τ k (e.val / 2 ^ k ^^^ 1) := by
  have h0 : e.val / 2 ^ layerHeight l = 0 := Nat.div_eq_of_lt he
  have hl := Quantum.Sphincs.layerHeight_le l
  have ht : layerHeight topLayer = 10 := rfl
  refine Quantum.Sphincs.foldPath_meet (node := fun level nodeIndex ↦
      Quantum.Sphincs.WithHash.tweakableHash H v.publicSeed (.node l τ (level + 1) nodeIndex))
    (val := fun k j ↦ v.treeValue l τ k j) (fun k hk a b hab ↦ ?_) (by rw [h0]; exact hf)
  have hj : e.val / 2 ^ (k + 1) < 2 ^ (layerHeight l - (k + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
    exact he
  have hj' : e.val / 2 ^ (k + 1) < 2 ^ layerHeight topLayer :=
    lt_of_lt_of_le (Quantum.Sphincs.lt_two_pow_of_lt hj)
      (Quantum.Sphincs.two_pow_layerHeight_le l)
  have hk' : k < layerHeight topLayer := by omega
  obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option hab
  have hp := payload_eq hT
    (p := ⟨.node l τ ⟨k, hk'⟩ ⟨e.val / 2 ^ (k + 1), hj'⟩, hτ, hk, hj⟩) trivial
    (q := (a, b)) ho (hr.trans (dite_eq_left ⟨hk', hj'⟩))
  exact Prod.mk.inj hp

/-- **A one-time leaf at its honest value**: the chain ends are the honest ones. -/
theorem leaf_meet (hT : ¬EvTcrT h v H) {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    (hk : τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l) {E : ChainIndex → Digest}
    (hE : Quantum.Sphincs.WithHash.leafHash H v.publicSeed l τ e E =
      some (v.treeValue l τ 0 e.val)) :
    E = v.endpoints l τ e := by
  have hd : v.treeValue l τ 0 e.val = v.dig (.leaf l τ e) := by
    change v.dig (.leaf l τ (leafOfNat e.val)) = _
    rw [Quantum.Sphincs.leafOfNat_val]
  obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option hE
  exact payload_eq hT (p := ⟨.leaf l τ e, hk⟩) trivial (q := E) ho (hr.trans hd)

/-- **A FORS tree ending at its honest root**: `H` maps the forged secret to the honest FORS leaf
and the path is the honest one. -/
theorem forsTree_meet (hT : ¬EvTcrT h v H) {idx : Index} {κ : ForsTreeIndex}
    {t : ForsLeafIndex} {op : ForsTreeOpening} {lf : Digest}
    (hlf : Quantum.Sphincs.WithHash.forsLeafHash H v.publicSeed idx κ t op.secret = some lf)
    (hf : foldPath (fun level node ↦ Quantum.Sphincs.WithHash.tweakableHash H
        v.publicSeed (.forsNode idx κ (level + 1) node)) t.val
      (fun level ↦ if hl : level < forsTreeHeight then op.path ⟨level, hl⟩ else 0)
        forsTreeHeight lf = some (v.forsValue idx κ forsTreeHeight 0)) :
    (∃ o, H (slotInput (pubKey v.publicSeed) 0 (.forsLeaf idx κ t) op.secret) = some o ∧
      truncateHash o = v.forsValue idx κ 0 t.val) ∧
      ∀ z : Fin forsTreeHeight, op.path z = v.forsValue idx κ z.val ((t.val >>> z.val) ^^^ 1) := by
  have hs : t.val < 2 ^ forsTreeHeight := t.isLt
  have h0 : t.val / 2 ^ forsTreeHeight = 0 := Nat.div_eq_of_lt hs
  have key := Quantum.Sphincs.foldPath_meet (node := fun level node ↦
      Quantum.Sphincs.WithHash.tweakableHash H v.publicSeed (.forsNode idx κ (level + 1) node))
    (val := fun k j ↦ v.forsValue idx κ k j) (n := forsTreeHeight) (leaf := t.val)
    (fun k hk a b hab ↦ by
      have hj : t.val / 2 ^ (k + 1) < 2 ^ (forsTreeHeight - (k + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
        exact hs
      have hj' : t.val / 2 ^ (k + 1) < 2 ^ forsTreeHeight := Quantum.Sphincs.lt_two_pow_of_lt hj
      obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option hab
      have hp := payload_eq hT
        (p := ⟨.forsNode idx κ ⟨k, hk⟩ ⟨t.val / 2 ^ (k + 1), hj'⟩, hj⟩) trivial
        (q := (a, b)) ho (hr.trans (dite_eq_left ⟨hk, hj'⟩))
      exact Prod.mk.inj hp)
    (by rw [h0]; exact hf)
  obtain ⟨o, ho, hr⟩ := Quantum.Sphincs.addressedHash_option hlf
  refine ⟨⟨o, ho, hr.trans key.1⟩, fun z ↦ ?_⟩
  have hz := key.2 z.val z.isLt
  simp only [z.isLt, dite_true] at hz
  rw [Nat.shiftRight_eq_div_pow]
  exact hz

/-- **A FORS key at its honest value**: the roots are the honest ones. -/
theorem forsRoots_meet (hT : ¬EvTcrT h v H) {idx : Index} {roots : ForsTreeIndex → Digest}
    (hr : Quantum.Sphincs.WithHash.forsPublicKey H v.publicSeed idx roots =
      some (v.forsKey idx)) :
    roots = v.forsRoot idx := by
  obtain ⟨o, ho, hd⟩ := Quantum.Sphincs.addressedHash_option hr
  exact payload_eq hT (p := ⟨.forsRoots idx, trivial⟩) trivial (q := roots) ho hd

/-! ## No CPRE win -/

/-- **No CPRE win on a WOTS chain**: a value walking under `H` to the honest end of a chain of a
key in use is the honest value, and the key's selection opens the chain at or below its
position. -/
theorem chain_of_not_cpre {log : List Message} (hC : ¬EvCpreT h v H log) {K : Key}
    (hK : KeyIn K) {i : ChainIndex} {μ : ℕ} (hμ : μ < chainLength - 1) {z : Digest}
    (hz : Quantum.Sphincs.WithHash.chainWalk H v.publicSeed K.1 K.2.1 K.2.2 i μ
      (chainLength - 1 - μ) z = some (v.endpoints K.1 K.2.1 K.2.2 i)) :
    z = v.chainValue K.1 K.2.1 K.2.2 i μ ∧
      ∃ sel, keySelect h v K = some sel ∧ (sel.2 i).val ≤ μ := by
  by_contra hn
  refine hC (Or.inl ⟨K, hK, i, μ, hμ, z, hz, ?_⟩)
  by_cases h1 : z = v.chainValue K.1 K.2.1 K.2.2 i μ
  · exact Or.inr fun h2 ↦ hn ⟨h1, h2⟩
  · exact Or.inl h1

/-- **No CPRE win on a FORS leaf**: a secret that `H` maps to the honest FORS leaf is the honest
secret, and the leaf is disclosed by a returned signature. -/
theorem fors_of_not_cpre {log : List Message} (hC : ¬EvCpreT h v H log) {idx : Index}
    {κ : ForsTreeIndex} {s : ForsLeafIndex} {z : Digest}
    (hz : ∃ o, H (slotInput (pubKey v.publicSeed) 0 (.forsLeaf idx κ s) z) = some o ∧
      truncateHash o = v.forsValue idx κ 0 s.val) :
    z = v.forsSecret idx κ s ∧ ForsOpened h v log idx κ s := by
  obtain ⟨o, ho, hd⟩ := hz
  by_contra hn
  refine hC (Or.inr ⟨idx, κ, s, z, o, ho, hd, ?_⟩)
  by_cases h1 : z = v.forsSecret idx κ s
  · exact Or.inr fun h2 ↦ hn ⟨h1, h2⟩
  · exact Or.inl h1

/-! ## The layers -/

/-- **A layer reaching the honest root of its tree**: it signs the value its key signs, and it is
the key's honest layer signature. -/
theorem layer_meet {log : List Message} (hT : ¬EvTcrT h v H) (hE : ¬EvEncT h v H)
    (hC : ¬EvCpreT h v H log) {l : Layer} {idx : Index} {σ : Signature} {msg root : Digest}
    (hok : LayerOk H v.publicSeed idx σ l msg root)
    (hroot : root = v.treeRoot l (treeOfIndex l idx)) :
    msg = v.layerMessage idx l ∧ v.layerSig (cellHash h) idx l = some (σ.layers l) := by
  subst hroot
  have hτ := Quantum.Qrom.Sphincs.treeOfIndex_lt l idx
  have he := Quantum.Sphincs.leafOfIndex_lt l idx
  have hK : KeyIn (keyOf l idx) := ⟨hτ, he⟩
  obtain ⟨w, hots, hfold⟩ := hok
  obtain ⟨hw, hpath⟩ := tree_meet hT hτ he hfold
  obtain ⟨o, x, ho, hx, E, hEc, hleaf⟩ := Quantum.Sphincs.otsLeaf_spec hots
  rw [hw] at hleaf
  have hEh := leaf_meet hT ⟨hτ, he⟩ hleaf
  -- Each forged value walks to the honest end: it is honest, and opened by the selection.
  have hchain : ∀ i, (σ.layers l).chainValues i =
      v.chainValue l (treeOfIndex l idx) (leafOfIndex l idx) i (x i).val ∧
      ((x i).val < chainLength - 1 →
        ∃ sel, keySelect h v (keyOf l idx) = some sel ∧ sel.2 i ≤ x i) := by
    intro i
    have hi := (x i).isLt
    have hwalk : Quantum.Sphincs.WithHash.chainWalk H v.publicSeed l (treeOfIndex l idx)
        (leafOfIndex l idx) i (x i).val (chainLength - 1 - (x i).val)
        ((σ.layers l).chainValues i) =
          some (v.endpoints l (treeOfIndex l idx) (leafOfIndex l idx) i) :=
      (hEc i).trans (congrArg some (congrFun hEh i))
    by_cases hlt : (x i).val < chainLength - 1
    · obtain ⟨hz, sel, hs, hle⟩ := chain_of_not_cpre (K := keyOf l idx) hC hK hlt hwalk
      exact ⟨hz, fun _ ↦ ⟨sel, hs, Fin.le_def.2 hle⟩⟩
    · have hxe : (x i).val = chainLength - 1 := by omega
      refine ⟨?_, fun h' ↦ absurd h' hlt⟩
      rw [hxe, Nat.sub_self] at hwalk
      have h0 : some ((σ.layers l).chainValues i) =
          some (v.endpoints l (treeOfIndex l idx) (leafOfIndex l idx) i) := hwalk
      rw [hxe]
      exact Option.some.inj h0
  have hvx := Quantum.Sphincs.Codeword.sum_eq_of_decode hx
  obtain ⟨i0, hi0⟩ := Quantum.Sphincs.Codeword.exists_lt_of_sum hvx
  obtain ⟨sel, hS, -⟩ := (hchain i0).2 hi0
  have hle : ∀ i, sel.2 i ≤ x i := by
    intro i
    by_cases hlt : (x i).val < chainLength - 1
    · obtain ⟨sel', hS', hle⟩ := (hchain i).2 hlt
      rw [hS] at hS'
      obtain rfl := Option.some.inj hS'
      exact hle
    · rw [Fin.le_def]
      have := (sel.2 i).isLt
      have := (x i).isLt
      omega
  -- Incomparability: the forged word is the selected one; then the forged trial is.
  have hS' : v.select (cellHash h) l (treeOfIndex l idx) (leafOfIndex l idx)
      (keyMessage v (keyOf l idx)) = some sel := hS
  have hdec := Quantum.Qrom.Sphincs.decode_of_select (v := v) (H := cellHash h) hS'
  have hxs : sel.2 = x := Quantum.Sphincs.Codeword.eq_of_le
    (Quantum.Sphincs.Codeword.sum_eq_of_decode hdec) hvx hle
  have hd2 : TargetSum.decodeDigest (thSlot h v.publicSeed
      (.enc l (treeOfIndex l idx) (leafOfIndex l idx)) (keyMessage v (keyOf l idx), sel.1)) =
        some x := by
    rw [← encDigest_eq_thSlot, ← hxs]
    exact hdec
  have hpair : (msg, (σ.layers l).counter) = (keyMessage v (keyOf l idx), sel.1) := by
    by_contra hne
    exact hE ⟨keyOf l idx, hK, sel, hS, msg, (σ.layers l).counter, hne, o, ho,
      Quantum.Sphincs.Codeword.eq_of_decode hx hd2⟩
  obtain ⟨hmsg, hc⟩ := Prod.mk.inj hpair
  refine ⟨hmsg.trans (v.msgPos_eq l idx), ?_⟩
  have h2 : (fun i ↦ v.chainValue l (treeOfIndex l idx) (leafOfIndex l idx) i (sel.2 i).val) =
      (σ.layers l).chainValues := by
    funext i
    rw [(hchain i).1, hxs]
  have h3 : v.authPath l (treeOfIndex l idx) (leafOfIndex l idx) =
      (σ.layers l).authenticationPath := by
    funext z
    have hz := hpath z.val z.isLt
    rw [Verification.layerPath, dite_eq_left z.isLt] at hz
    rw [Quantum.Qrom.Sphincs.QTable.authPath, Nat.shiftRight_eq_div_pow]
    exact hz.symm
  rw [Quantum.Qrom.Sphincs.QTable.layerSig_eq, Quantum.Qrom.Sphincs.QTable.layerSignature]
  change Option.map _ (v.select (cellHash h) l (treeOfIndex l idx) (leafOfIndex l idx)
    (keyMessage v (keyOf l idx))) = _
  rw [hS']
  simp only [Option.map_some, Option.some.injEq]
  exact Quantum.Sphincs.layerSignature_ext hc.symm h2 h3

/-! ## The extraction -/

/-- **The extraction under the negated trace-local events**: an accepted forgery under a partial
sound hash is an ITSR win or the honest signature of a signed message. -/
theorem extract_core (hv : Honest h v) (hH : ∀ x o, H x = some o → o = h x)
    {msgs : List Message} (hT : ¬EvTcrT h v H) (hE : ¬EvEncT h v H) (hC : ¬EvCpreT h v H msgs)
    {M : Message} {σ : Signature}
    (hver : Quantum.Sphincs.WithHash.verify H v.publicKey M σ = some true) :
    EvItsr h v msgs σ.randomizer M ∨
      ∃ M' ∈ msgs, M' = M ∧ v.signature (cellHash h) M' = some σ := by
  obtain ⟨o, ho, fk, hfk, hlay⟩ := Quantum.Sphincs.verify_spec hver
  have hoe : o = fun c ↦
      h (Quantum.Sphincs.messageDigestInput σ.randomizer v.publicKey.publicSeed v.publicKey.root
        M c) :=
    funext fun c ↦ hH _ _ (ho c)
  subst hoe
  obtain ⟨D, hD⟩ : ∃ D, digestOf h v.publicKey σ.randomizer M = D := ⟨_, rfl⟩
  have hfk' : Quantum.Sphincs.WithHash.forsRecover H v.publicSeed (digestIndex D)
      (digestForsLeaves D) σ.forsOpening = some fk := by
    rw [← hD]
    exact hfk
  have hlay' : Quantum.Sphincs.WithHash.verifyLayers H v.publicSeed (digestIndex D) σ
      layerCount fk = some (some v.root) := by
    rw [← hD]
    exact hlay
  -- The layers, from the top.
  obtain ⟨r0, r1, h0, h1, h2⟩ := Quantum.Sphincs.verifyLayers_spec hlay'
  have ht : treeOfIndex 2 (digestIndex D) = 0 := Quantum.Sphincs.treeOfIndex_topLayer _
  obtain ⟨hm2, hs2⟩ := layer_meet hT hE hC h2 (by rw [ht]; rfl)
  obtain ⟨hm1, hs1⟩ := layer_meet hT hE hC h1 (hm2.trans (v.layerMessage_two _))
  obtain ⟨hm0, hs0⟩ := layer_meet hT hE hC h0 (hm1.trans (v.layerMessage_one _))
  -- FORS: the roots and the openings are honest, the opened leaves disclosed.
  obtain ⟨roots, hroots, hpk⟩ := Quantum.Sphincs.forsRecover_spec hfk'
  rw [hm0, Quantum.Qrom.Sphincs.QTable.layerMessage_zero] at hpk
  have hr := forsRoots_meet hT hpk
  have hfors : ∀ κ, (σ.forsOpening κ).secret = v.forsSecret (digestIndex D) κ
      (digestForsLeaves D κ) ∧ ForsOpened h v msgs (digestIndex D) κ (digestForsLeaves D κ) ∧
      ∀ z : Fin forsTreeHeight, (σ.forsOpening κ).path z = v.forsValue (digestIndex D) κ z.val
        (((digestForsLeaves D κ).val >>> z.val) ^^^ 1) := fun κ ↦ by
    obtain ⟨lf, hlf, hfold⟩ := hroots κ
    rw [hr] at hfold
    obtain ⟨hleaf, hpath⟩ := forsTree_meet hT hlf hfold
    obtain ⟨hs, hop⟩ := fors_of_not_cpre hC hleaf
    exact ⟨hs, hop, hpath⟩
  by_cases hm : (σ.randomizer, M) ∈ msgs.map (fun M' ↦ (v.randomizer M', M'))
  · -- A signed pair: the forgery is that message's honest signature.
    right
    obtain ⟨M', hM', hpair⟩ := List.mem_map.1 hm
    obtain ⟨hR, hMM⟩ := Prod.mk.inj hpair
    refine ⟨M', hM', hMM, ?_⟩
    have hdig : v.messageDigest M' = D := by
      rw [messageDigest_eq hv, hR, hMM, hD]
    have hidx : v.index M' = digestIndex D := congrArg digestIndex hdig
    have hlv : v.leaves M' = digestForsLeaves D := congrArg digestForsLeaves hdig
    unfold Quantum.Qrom.Sphincs.QTable.signature
    rw [hidx, hs0, hs1, hs2]
    change some ⟨v.randomizer M', v.forsOpening (digestIndex D) (v.leaves M'),
      layerSignatures (σ.layers 0) (σ.layers 1) (σ.layers 2)⟩ = some σ
    rw [hlv, Quantum.Sphincs.layerSignatures_layers, hR]
    have hop : v.forsOpening (digestIndex D) (digestForsLeaves D) = σ.forsOpening :=
      funext fun κ ↦ Quantum.Sphincs.forsTreeOpening_ext (hfors κ).1.symm
        (funext fun z ↦ ((hfors κ).2.2 z).symm)
    rw [hop]
  · -- A fresh pair whose cells the signed messages' cells cover: ITSR.
    left
    refine ⟨hm, ?_⟩
    rw [hD]
    intro c hc
    obtain ⟨κ, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨M', hM', -, hi, hl⟩ := (hfors κ).2.1
    refine mem_foldr_union ⟨M', hM', ?_⟩
    rw [← messageDigest_eq hv]
    refine Finset.mem_image.2 ⟨κ, Finset.mem_univ κ, ?_⟩
    change (v.index M', κ, v.leaves M' κ) = _
    rw [hi, hl]

/-- **The extraction into the trace-local events**: a forgery accepted under a partial sound hash
`H` is an ITSR win, a trace-local EncTCR+C, SM-TCR or CPRE win, or the honest signature of a
signed message. -/
theorem extractT (hv : Honest h v) (hH : ∀ x o, H x = some o → o = h x) {msgs : List Message}
    {M : Message} {σ : Signature}
    (hver : Quantum.Sphincs.WithHash.verify H v.publicKey M σ = some true) :
    EvItsr h v msgs σ.randomizer M ∨ EvEncT h v H ∨ EvTcrT h v H ∨ EvCpreT h v H msgs ∨
      ∃ M' ∈ msgs, M' = M ∧ v.signature (cellHash h) M' = some σ := by
  by_contra hno
  rcases extract_core hv hH (fun e ↦ hno (Or.inr (Or.inr (Or.inl e))))
      (fun e ↦ hno (Or.inr (Or.inl e))) (fun e ↦ hno (Or.inr (Or.inr (Or.inr (Or.inl e)))))
      hver with hI | hs
  · exact hno (Or.inl hI)
  · exact hno (Or.inr (Or.inr (Or.inr (Or.inr hs))))

/-- **The extraction, verification in `Option`**: without an EncTCR+C, SM-TCR or CPRE win, a
forgery accepted under a partial sound hash is an ITSR win or the honest signature of a signed
message. -/
theorem extract (hv : Honest h v) (hH : ∀ x o, H x = some o → o = h x) {msgs : List Message}
    (hT : ¬EvTcr h v) (hE : ¬EvEnc h v) (hC : ¬EvCpre h v msgs) {M : Message} {σ : Signature}
    (hver : Quantum.Sphincs.WithHash.verify H v.publicKey M σ = some true) :
    EvItsr h v msgs σ.randomizer M ∨
      ∃ M' ∈ msgs, M' = M ∧ v.signature (cellHash h) M' = some σ :=
  extract_core hv hH (fun e ↦ hT (e.evTcr hH)) (fun e ↦ hE (e.evEnc hH))
    (fun e ↦ hC (e.evCpre hH)) hver

end Extract

/-- **The extraction into the trace-local events** (design, Theorem 2): a forgery accepted under a
partial sound hash `H`, against a transcript of honest signatures that does not contain it, is an
ITSR win or a trace-local EncTCR+C, SM-TCR or CPRE win. -/
theorem win_imp_eventsT {h : HashInput → HashOutput} {v : QTable}
    {H : HashInput → Option HashOutput} (hv : Honest h v) (hH : ∀ x o, H x = some o → o = h x)
    {log : List (Message × Option Signature)}
    (hlog : ∀ e ∈ log, e.2 = v.signature (cellHash h) e.1) {forg : Forgery}
    (hver : Quantum.Sphincs.WithHash.verify H v.publicKey forg.message forg.signature =
      some true)
    (hfresh : ¬∃ e ∈ log, e.1 = forg.message ∧ e.2 = some forg.signature) :
    EvItsr h v (log.map Prod.fst) forg.signature.randomizer forg.message ∨ EvEncT h v H ∨
      EvTcrT h v H ∨ EvCpreT h v H (log.map Prod.fst) := by
  rcases Extract.extractT (msgs := log.map Prod.fst) hv hH hver with
    hI | hE | hT | hC | ⟨M', hM', hMM, hs⟩
  · exact Or.inl hI
  · exact Or.inr (Or.inl hE)
  · exact Or.inr (Or.inr (Or.inl hT))
  · exact Or.inr (Or.inr (Or.inr hC))
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM'
    exact absurd ⟨e, he, hMM, (hlog e he).trans hs⟩ hfresh

/-- **The extraction** (design, Theorem 2): a forgery that verifies under `h` against the honest
structure `v`, against a transcript of honest signatures that does not contain it, is an ITSR,
EncTCR+C, SM-TCR or CPRE win. -/
theorem win_imp_events {h : HashInput → HashOutput} {v : QTable} (hv : Honest h v)
    {log : List (Message × Option Signature)}
    (hlog : ∀ e ∈ log, e.2 = v.signature (cellHash h) e.1) {forg : Forgery}
    (hver : Quantum.Qrom.Sphincs.LeanSphincsOver.verify (m := Id) (fun l ↦ h l) v.publicKey
      forg.message forg.signature = true)
    (hfresh : ¬∃ e ∈ log, e.1 = forg.message ∧ e.2 = some forg.signature) :
    EvItsr h v (log.map Prod.fst) forg.signature.randomizer forg.message ∨ EvEnc h v ∨
      EvTcr h v ∨ EvCpre h v (log.map Prod.fst) := by
  rcases win_imp_eventsT hv Extract.optH_sound hlog (Extract.verify_optH hver) hfresh with
    hI | hE | hT | hC
  · exact Or.inl hI
  · exact Or.inr (Or.inl (hE.evEnc Extract.optH_sound))
  · exact Or.inr (Or.inr (Or.inl (hT.evTcr Extract.optH_sound)))
  · exact Or.inr (Or.inr (Or.inr (hC.evCpre Extract.optH_sound)))

/-- **The extraction into the trace-local events on the forgery's own trace**: the events are
decided by the hash on the verifier's queries alone. -/
theorem win_imp_eventsT' {h : HashInput → HashOutput} {v : QTable} (hv : Honest h v)
    {log : List (Message × Option Signature)}
    (hlog : ∀ e ∈ log, e.2 = v.signature (cellHash h) e.1) {forg : Forgery}
    (hver : Quantum.Qrom.Sphincs.LeanSphincsOver.verify (m := Id) (fun l ↦ h l) v.publicKey
      forg.message forg.signature = true)
    (hfresh : ¬∃ e ∈ log, e.1 = forg.message ∧ e.2 = some forg.signature) :
    EvItsr h v (log.map Prod.fst) forg.signature.randomizer forg.message ∨
      EvEncT h v (Extract.traceH h v.publicKey forg.message forg.signature) ∨
      EvTcrT h v (Extract.traceH h v.publicKey forg.message forg.signature) ∨
      EvCpreT h v (Extract.traceH h v.publicKey forg.message forg.signature)
        (log.map Prod.fst) :=
  win_imp_eventsT hv Extract.traceH_sound hlog (Extract.verify_traceH hver) hfresh

end Quantum.StdModel.Sphincs

end
