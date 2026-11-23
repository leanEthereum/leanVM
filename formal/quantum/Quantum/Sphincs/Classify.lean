module

public import Quantum.Sphincs.Events
public import Quantum.Sphincs.CoverStream
public import Quantum.Xmss.Classify
public import Quantum.Sponge.Reads.Log

@[expose] public section

/-!
# The deterministic core of leanSPHINCS's QRPM proof: a win is in the event

The event side (contract C4) over the template data `d : EvData`, the hardwired cells `W`, the
databases `D` and the memory `m`. The union `union W D` answers a hash call when the sponge
evaluation of its blocks is a path of the union (`Quantum.Xmss.OnPath`), with the digest of its
view (`Quantum.Xmss.viewHash`, a hash in `Option`).

* **Verification in `Option`** (`verify_viewHash_of_honestEval`): an accepting honest evaluation
  whose reads the union holds is an accepting verification with every hash answered by
  `viewHash` (`simulateQ_option_eq_some`); `verify_spec`, `verifyLayers_spec`, `otsLeaf_spec`,
  `forsRecover_spec` read off its calls.
* **No hit, honest** (`honest_of_view`): a call at a structural slot whose view digest is the
  value at the slot's output is the honest input of an exempted slot, or the register is in
  `Bad d N` (a Struct hit). By last divergence along the verifier's walks: `chain_meet`,
  `tree_meet` (`foldPath_meet` for any fold), `leaf_meet`, `forsTree_meet`, `forsRoots_meet`.
  `enc_meet`: a trial of a selected key at the recorded digest is the selected trial (else an Enc
  hit).
* **Selections** (`SelFn`): each key's selected counter and word. A key signs the one value at
  `msgPos`, so a selection does not depend on the message and no reuse hypothesis is needed.
  `EvData.selSig S R w`: the signature with randomizer `R` on the digest view `w`;
  `selDisclosures`: the positions the signed messages disclose; `EvData.RecordsSel`: the memory
  records the selected trial blocks with digests decoding to the selected words.
* `layer_meet`: a forged layer reaching the honest root of its tree signs the value at its key's
  `msgPos` and is the selection's layer signature. An exempted chain step is public, hence opened
  by the key's selection at or below the forged word, which incomparability makes equal
  (`Codeword.eq_of_le`).
* `WinFacts`: the classical facts of a win, with **the exemptions public**: the exempted
  structural slots are public for the signed messages' disclosures (`exempt`, the role of
  leanXMSS's `Ex ⊆ Public`), and the exempted `H_msg` pairs are signed pairs (`covEx`), whose two
  calls the hardwired cells hold with the signed digests (`digests`).
* **The classification** (`win_imp_bad_sel`, `mem_bad_of_agrees`): a win is in `Bad d N`. The
  layers meet the honest trees from the top, then the FORS key, roots and openings are honest and
  each opened leaf's slot is exempted. An exempted forged pair is a signed pair with the signed
  digests, so the forgery is the returned signature; otherwise the opened secrets are disclosed,
  so their leaves are covered by `S★` (`cover`), and the forged call-0 tail is a coverage hit
  (`HalfCov` with the low index bits of call 1).
-/

open OracleComp OracleSpec
open Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput ChainStep
  chainLength littleEndianBytes truncateHash digestsPayload)
open HashSig.OverPermutation (sequenceFin walkChain foldPath nodePayload)
open Quantum.Xmss (X Z blocks trunc128 out256 viewPerm viewHash OnPath viewHash_eq_some_iff
  heldBy_union blocks_injective)
open Common.SufCma (SignerReturnedForgery)
open Quantum.SufCma (honestEval queries trace_query_bind fst_honestEval snd_honestEval spongeOut
  inputReads)

namespace Quantum.Sphincs

/-! ## Verification answered by the union view -/

section OptionEval

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}

/-- **Answers in `Option`**: a computation whose queries `impl` answers as `f` returns, answered by
`impl`, its evaluation with `f`. -/
theorem simulateQ_option_eq_some (impl : QueryImpl spec Option) (f : QueryImpl spec Id) :
    ∀ x : OracleComp spec α, (∀ q ∈ queries f x, impl q = some (f q)) →
      simulateQ impl x = some (evalWithAnswerFn f x) := by
  intro x
  induction x using OracleComp.inductionOn with
  | pure a => intro _; rfl
  | query_bind t k ih =>
    intro h
    have hq : queries f ((liftM (spec.query t) : OracleComp spec _) >>= k) =
        [t] ++ queries f (k (f t)) := trace_query_bind f (fun t ↦ [t]) t k
    rw [hq] at h
    rw [simulateQ_bind, simulateQ_spec_query,
      h t (List.mem_append_left _ (List.mem_singleton_self t)), evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query]
    exact ih (f t) fun q hq ↦ h q (List.mem_append_right _ hq)

/-- `sequenceFin` in `Option` returns every component. -/
theorem sequenceFin_option {β : Type} :
    ∀ {n : ℕ} {c : Fin n → Option β} {g : Fin n → β}, sequenceFin c = some g →
      ∀ i, c i = some (g i)
  | 0, _, _, _, i => i.elim0
  | n + 1, c, g, h, i => by
    simp only [sequenceFin, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, tl, htl, rfl⟩ := h
    refine Fin.cases ha (fun j ↦ ?_) i
    exact sequenceFin_option htl j

end OptionEval

/-! ## The verifier's hash calls in `Option` -/

section Calls

variable {H : HashInput → Option HashOutput}

theorem addressedHash_option {Q : PublicParameter} {a : Address} {p : HashInput} {r : Digest}
    (h : WithHash.addressedHash H Q a p = some r) :
    ∃ o, H (addressedHashInput Q a p) = some o ∧ truncateHash o = r := by
  unfold WithHash.addressedHash at h
  obtain ⟨o, ho, h⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨o, ho, Option.some.inj h⟩

/-- **An accepted forgery**: the digest calls, the FORS key, and the layers up to `PK.root`. -/
theorem verify_spec {pk : PublicKey} {M : Message} {σ : Signature}
    (h : WithHash.verify H pk M σ = some true) :
    ∃ o : DigestCall → HashOutput,
      (∀ c, H (messageDigestInput σ.randomizer pk.publicSeed pk.root M c) = some (o c)) ∧
      ∃ fk, WithHash.forsRecover H pk.publicSeed (digestView o).1 (digestView o).2
          σ.forsOpening = some fk ∧
        WithHash.verifyLayers H pk.publicSeed (digestView o).1 σ layerCount fk =
          some (some pk.root) := by
  unfold WithHash.verify at h
  obtain ⟨dg, hdg, h⟩ := Option.bind_eq_some_iff.1 h
  unfold WithHash.messageDigest at hdg
  obtain ⟨o, ho, hdg⟩ := Option.bind_eq_some_iff.1 hdg
  obtain rfl := Option.some.inj hdg
  obtain ⟨fk, hfk, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨o, fun c ↦ sequenceFin_option ho c, fk, hfk, ?_⟩
  rcases x with _ | root
  · cases h
  · have hr : root = pk.root := of_decide_eq_true (Option.some.inj h)
    rw [← hr]
    exact hx

/-- A layer of an accepted signature: the one-time leaf of key `K_l(idx)` on `msg` and the fold of
the layer's path to `root`. -/
def LayerOk (H : HashInput → Option HashOutput) (Q : PublicParameter) (idx : Index)
    (σ : Signature) (l : Layer) (msg root : Digest) : Prop :=
  ∃ v, WithHash.otsLeaf H Q l (treeOfIndex l idx) (leafOfIndex l idx) msg (σ.layers l).counter
      (σ.layers l).chainValues = some (some v) ∧
    WithHash.treeFold H Q l (treeOfIndex l idx) (leafOfIndex l idx)
      (Verification.layerPath σ l) (layerHeight l) v = some root

/-- One layer of the walk up the hypertree. -/
theorem verifyLayers_succ {Q : PublicParameter} {idx : Index} {σ : Signature} {n : ℕ}
    {msg r : Digest} (hn : n < layerCount)
    (h : WithHash.verifyLayers H Q idx σ (n + 1) msg = some (some r)) :
    ∃ root, LayerOk H Q idx σ ⟨layerCount - 1 - n, by omega⟩ msg root ∧
      (if n = 0 then (pure (some root) : Option (Option Digest))
        else WithHash.verifyLayers H Q idx σ n root) = some (some r) := by
  rw [WithHash.verifyLayers, dite_eq_left hn] at h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
  rcases x with _ | v
  · cases h
  obtain ⟨root, hroot, h⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨root, ⟨v, hx, hroot⟩, h⟩

/-- **The three layers of an accepted signature**, from the FORS key up to the top root. -/
theorem verifyLayers_spec {Q : PublicParameter} {idx : Index} {σ : Signature} {fk r : Digest}
    (h : WithHash.verifyLayers H Q idx σ layerCount fk = some (some r)) :
    ∃ r0 r1, LayerOk H Q idx σ 0 fk r0 ∧ LayerOk H Q idx σ 1 r0 r1 ∧ LayerOk H Q idx σ 2 r1 r := by
  obtain ⟨r0, h0, h⟩ := verifyLayers_succ (n := 2) (by decide) h
  rw [ite_eq_right (by decide)] at h
  obtain ⟨r1, h1, h⟩ := verifyLayers_succ (n := 1) (by decide) h
  rw [ite_eq_right (by decide)] at h
  obtain ⟨r2, h2, h⟩ := verifyLayers_succ (n := 0) (by decide) h
  rw [ite_eq_left rfl] at h
  obtain rfl : r2 = r := Option.some.inj (Option.some.inj h)
  exact ⟨r0, r1, h0, h1, h2⟩

/-- **A one-time leaf**: the encoding decodes to a word, the chains are walked from the signed
values to their ends `E`, and the leaf compresses `E`. -/
theorem otsLeaf_spec {Q : PublicParameter} {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    {msg : Digest} {c : EncodingCounter} {vals : ChainIndex → Digest} {v : Digest}
    (h : WithHash.otsLeaf H Q l τ e msg c vals = some (some v)) :
    ∃ o x, H (addressedHashInput Q (hashDomainFields (.encoding l τ e))
        (littleEndianBytes 16 msg ++ bigEndianBytes 4 c)) = some o ∧
      TargetSum.decodeDigest (truncateHash o) = some x ∧
      ∃ E : ChainIndex → Digest,
        (∀ i, WithHash.recoverChain H Q l τ e i (x i) (vals i) = some (E i)) ∧
        WithHash.leafHash H Q l τ e E = some v := by
  unfold WithHash.otsLeaf at h
  obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.1 h
  rcases y with _ | x
  · cases h
  unfold WithHash.encode at hy
  obtain ⟨dg, hdg, hy⟩ := Option.bind_eq_some_iff.1 hy
  obtain ⟨o, ho, rfl⟩ := addressedHash_option hdg
  obtain ⟨E, hE, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨v', hv', h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl : v' = v := Option.some.inj (Option.some.inj h)
  exact ⟨o, x, ho, Option.some.inj hy, E, sequenceFin_option hE, hv'⟩

/-- **A FORS key**: each tree's opening recovers a root, and the roots compress to the key. -/
theorem forsRecover_spec {Q : PublicParameter} {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex}
    {op : ForsTreeIndex → ForsTreeOpening} {fk : Digest}
    (h : WithHash.forsRecover H Q idx lv op = some fk) :
    ∃ roots : ForsTreeIndex → Digest,
      (∀ κ, ∃ lf, WithHash.forsLeafHash H Q idx κ (lv κ) (op κ).secret = some lf ∧
        foldPath (fun level node ↦ WithHash.tweakableHash H Q (.forsNode idx κ (level + 1) node))
          (lv κ).val (fun level ↦ if h : level < forsTreeHeight then (op κ).path ⟨level, h⟩ else 0)
          forsTreeHeight lf = some (roots κ)) ∧
      WithHash.forsPublicKey H Q idx roots = some fk := by
  unfold WithHash.forsRecover at h
  obtain ⟨roots, hroots, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨roots, fun κ ↦ ?_, h⟩
  have hκ := sequenceFin_option hroots κ
  unfold WithHash.forsTreeRecover at hκ
  exact Option.bind_eq_some_iff.1 hκ

/-- One more step of a chain walk. -/
theorem walkChain_succ_option {k : ℕ} {step : Fin k → Digest → Option Digest} {a n : ℕ}
    {v r : Digest} (hk : a + n < k) (h : walkChain step a (n + 1) v = some r) :
    ∃ prev, walkChain step a n v = some prev ∧ step ⟨a + n, hk⟩ prev = some r := by
  obtain ⟨prev, hp, h⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨prev, hp, (dite_eq_left hk).symm.trans h⟩

/-- One more level of a fold. -/
theorem foldPath_succ_option {node : ℕ → ℕ → HashInput → Option Digest} {leaf : ℕ}
    {sib : ℕ → Digest} {n : ℕ} {v r : Digest} (h : foldPath node leaf sib (n + 1) v = some r) :
    ∃ cur, foldPath node leaf sib n v = some cur ∧
      node n (leaf / 2 ^ (n + 1)) (if leaf.testBit n then nodePayload (sib n) cur
        else nodePayload cur (sib n)) = some r :=
  Option.bind_eq_some_iff.1 h

/-- **A fold ending at the honest value** (`Quantum.Xmss.path_meet` for any fold): when every node
reaching its honest value from a payload of two children has the honest children, the fold starts
at the honest leaf and its siblings are honest. -/
theorem foldPath_meet {node : ℕ → ℕ → HashInput → Option Digest} {leaf : ℕ} {sib : ℕ → Digest}
    {val : ℕ → ℕ → Digest} :
    ∀ {n : ℕ} {v : Digest},
      (∀ k < n, ∀ a b, node k (leaf / 2 ^ (k + 1)) (nodePayload a b) =
          some (val (k + 1) (leaf / 2 ^ (k + 1))) →
        a = val k (2 * (leaf / 2 ^ (k + 1))) ∧ b = val k (2 * (leaf / 2 ^ (k + 1)) + 1)) →
      foldPath node leaf sib n v = some (val n (leaf / 2 ^ n)) →
      v = val 0 leaf ∧ ∀ k < n, sib k = val k (leaf / 2 ^ k ^^^ 1)
  | 0, v, _, h => by
    refine ⟨?_, fun k hk ↦ absurd hk (Nat.not_lt_zero k)⟩
    have hv : v = val 0 (leaf / 2 ^ 0) := Option.some.inj h
    rwa [pow_zero, Nat.div_one] at hv
  | n + 1, v, hnode, h => by
    obtain ⟨cur, hcur, hn⟩ := foldPath_succ_option h
    have hj : leaf / 2 ^ (n + 1) = leaf / 2 ^ n / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have hcs : cur = val n (leaf / 2 ^ n) ∧ sib n = val n (leaf / 2 ^ n ^^^ 1) := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hn
      rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ n) with h2 | h2
      · have hx : leaf / 2 ^ n ^^^ 1 = leaf / 2 ^ n + 1 := Nat.xor_one_of_even (Nat.even_iff.2 h2)
        simp only [h2, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte] at hn
        obtain ⟨ha, hb⟩ := hnode n (Nat.lt_succ_self n) _ _ hn
        refine ⟨ha.trans (congrArg _ ?_), hb.trans (congrArg _ ?_)⟩
        · rw [hj]
          omega
        · rw [hx, hj]
          omega
      · have hx : leaf / 2 ^ n ^^^ 1 = leaf / 2 ^ n - 1 := Nat.xor_one_of_odd (Nat.odd_iff.2 h2)
        simp only [h2, decide_true, ↓reduceIte] at hn
        obtain ⟨ha, hb⟩ := hnode n (Nat.lt_succ_self n) _ _ hn
        refine ⟨hb.trans (congrArg _ ?_), ha.trans (congrArg _ ?_)⟩
        · rw [hj]
          omega
        · rw [hx, hj]
          omega
    obtain ⟨hv, hs⟩ := foldPath_meet (n := n) (fun k hk ↦ hnode k (Nat.lt_succ_of_lt hk))
      (hcs.1 ▸ hcur)
    exact ⟨hv, fun k hk ↦ (Nat.lt_succ_iff_lt_or_eq.1 hk).elim (hs k) fun h ↦ h ▸ hcs.2⟩

/-- Digests of a payload determine its digests. -/
theorem digestsPayload_inj {n : ℕ} {E E' : Fin n → Digest}
    (h : digestsPayload E = digestsPayload E') : E = E' :=
  List.ofFn_injective (Quantum.Xmss.flatMap_littleEndianBytes_injective
    (List.length_ofFn.trans List.length_ofFn.symm) h)

end Calls

/-! ## Target hits -/

/-- The input of a structural slot is its addressed input. -/
theorem slotInput_of_inTable {s : Slot} (hT : InTable s) (Q : PublicParameter)
    (f : ValPos → Digest) :
    slotInput Q s f = addressedHashInput Q (hashDomainFields (slotDomain s)) (slotPayload f s) := by
  cases s <;> first | rfl | exact hT.elim

/-- An `out` output of a path of the union view. -/
theorem reaches_of_onPath_out {Y : Type} (out : X → Y) {π : Equiv.Perm (X × Z)} {U : Dbs X Z}
    {u : HashInput} (h : OnPath π U u) :
    Reaches π U out (absorbTail (viewPerm π U) (blocks u))
      (out (spongeHash (viewPerm π U) (blocks u))) :=
  reaches_of_agrees π U.fill.1 U.fill.2.1 U.fill.2.2 (Quantum.Xmss.blocks_ne_nil u)
    (agreesRounds_of_heldBy π U.fill.1 U.fill.2.1 U.fill.2.2 h).1
    ((agreesRounds_of_heldBy π U.fill.1 U.fill.2.1 U.fill.2.2 h).2 (Quantum.Xmss.blocks_ne_nil u))

/-- **The selected trial input** of key `K` at counter `c`: `PK.seed ‖ ADRS_enc(K) ‖ M_K ‖ BE32(c)`
with `M_K` the value at `msgPos K`. -/
def EvData.encInput (d : EvData) (K : Key) (c : EncodingCounter) : HashInput :=
  addressedHashInput d.seed (hashDomainFields (.encoding K.1 K.2.1 K.2.2))
    (littleEndianBytes 16 (d.value (msgPos K)) ++ bigEndianBytes 4 c)

section Hits

variable {Lb : Type} {d : EvData} {N : ℕ} {D : DbReg X Z} {W : Hw X Z} {m : Mem Lb}

/-- **A structural call without a hit is honest and exempted**: an input on a path of the union at
a structural slot, of the honest input's length, whose view digest is the value at the slot's
output, is the honest input of an exempted slot, unless the register is in the event. -/
theorem honest_of_view (hN : dbGrade W ≤ N) (hnb : (D, W, m) ∉ Bad d N) {s : Slot}
    (hT : InTable s) {u : HashInput} {o : HashOutput}
    (hv : viewHash d.perm (union W D) u = some o)
    (hs : slotOf d.pk (absorbTail (viewPerm d.perm (union W D)) (blocks u)) = some s)
    (hlen : u.length = (slotInput d.seed s d.value).length)
    (ho : truncateHash o = d.value (slotOutPos s)) :
    u = slotInput d.seed s d.value ∧ s ∈ d.exS W := by
  obtain ⟨hon, rfl⟩ := viewHash_eq_some_iff.1 hv
  by_contra hne
  have hr := Quantum.Xmss.reaches_of_onPath hon
  rw [ho] at hr
  refine hnb (mem_bad_of_tgt hN (sphTgt_struct hs hT ?_ ?_) hr)
  · rw [EvData.honTail, length_absorbTail, length_absorbTail, EvData.blocksOf,
      Quantum.Xmss.length_blocks, Quantum.Xmss.length_blocks, hlen]
  · rintro ⟨ht, hex⟩
    obtain ⟨h', hrd, htail, -⟩ := EvData.heldIn_union_of_mem_exS D hex
    have hc := Quantum.Xmss.absorbTail_congr (π := d.perm) (t := (h', d.keys.2.1, d.keys.2.2))
      (t' := (union W D).fill) (d.blocksOf s) fun e he ↦ SpongeRead.answeredBy_fill (hrd e he)
    exact hne ⟨blocks_injective (absorbTail_injective _ (ht.trans (htail.symm.trans hc.symm))),
      hex⟩

/-- **`honest_of_view` for an addressed call**: the payload is the slot's honest payload. -/
theorem honest_of_addressed (hN : dbGrade W ≤ N) (hnb : (D, W, m) ∉ Bad d N) {s : Slot}
    (hT : InTable s) {p : HashInput} {r : Digest}
    (hv : WithHash.addressedHash (viewHash d.perm (union W D)) d.seed
      (hashDomainFields (slotDomain s)) p = some r)
    (hs : slotOf d.pk (absorbTail (viewPerm d.perm (union W D))
      (blocks (addressedHashInput d.seed (hashDomainFields (slotDomain s)) p))) = some s)
    (hlen : p.length = (slotPayload d.value s).length) (hr : r = d.value (slotOutPos s)) :
    p = slotPayload d.value s ∧ s ∈ d.exS W := by
  obtain ⟨o, ho, rfl⟩ := addressedHash_option hv
  have h := honest_of_view hN hnb hT ho hs
    (by rw [slotInput_of_inTable hT, length_addressedHashInput, length_addressedHashInput, hlen]) hr
  rw [slotInput_of_inTable hT] at h
  exact ⟨(addressedHashInput_injective d.seed h.1).2, h.2⟩

/-- **A chain walk ending at the honest chain** (no hit): it starts at the honest value, and the
slot of its first step is exempted. -/
theorem chain_meet (hN : dbGrade W ≤ N) (hnb : (D, W, m) ∉ Bad d N) {l : Layer} {τ : TreeIndex}
    {e : TreeLeafIndex} {i : ChainIndex}
    (hk : τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l) :
    ∀ (n a : ℕ) (v : Digest), a + n ≤ chainLength - 1 →
      WithHash.chainWalk (viewHash d.perm (union W D)) d.seed l τ e i a n v =
        some (d.value (cpos l τ e i (a + n))) →
      v = d.value (cpos l τ e i a) ∧
        ∀ h : a < chainLength - 1, 0 < n → Slot.chain l τ e i ⟨a, h⟩ ∈ d.exS W
  | 0, _, _, _, h => ⟨Option.some.inj h, fun _ h0 ↦ absurd h0 (lt_irrefl 0)⟩
  | n + 1, a, v, han, h => by
    have hlt : a + n < chainLength - 1 := by omega
    obtain ⟨prev, hprev, hstep⟩ := walkChain_succ_option hlt h
    obtain ⟨hp, hex⟩ := honest_of_addressed hN hnb (s := .chain l τ e i ⟨a + n, hlt⟩) hk hstep
      (slotOf_chain _ d.pk l τ e i ⟨a + n, hlt⟩ prev)
      ((Quantum.Xmss.length_littleEndianBytes 16 _).trans
        (Quantum.Xmss.length_littleEndianBytes 16 _).symm) rfl
    have hprev' : prev = d.value (cpos l τ e i (a + n)) := littleEndianBytes_injective 16 hp
    obtain ⟨hv, hex'⟩ := chain_meet hN hnb hk n a v (by omega) (hprev' ▸ hprev)
    refine ⟨hv, fun ha _ ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hex
    · exact hex' ha hn

/-- **A Merkle path of the hypertree ending at its tree's root** (no hit): it starts at the honest
one-time leaf, and its siblings are the honest ones. -/
theorem tree_meet (hN : dbGrade W ≤ N) (hnb : (D, W, m) ∉ Bad d N) {l : Layer} {τ : TreeIndex}
    {e : TreeLeafIndex} (hτ : τ.val < 2 ^ treeBits l) (he : e.val < 2 ^ layerHeight l)
    {path : ℕ → Digest} {v : Digest}
    (h : WithHash.treeFold (viewHash d.perm (union W D)) d.seed l τ e path (layerHeight l) v =
      some (d.value (tpos l τ (layerHeight l) 0))) :
    v = d.value (tpos l τ 0 e.val) ∧
      ∀ k < layerHeight l, path k = d.value (tpos l τ k (e.val / 2 ^ k ^^^ 1)) := by
  have h0 : e.val / 2 ^ layerHeight l = 0 := Nat.div_eq_of_lt he
  have hl := layerHeight_le l
  refine foldPath_meet (node := fun level nodeIndex ↦ WithHash.tweakableHash
      (viewHash d.perm (union W D)) d.seed (.node l τ (level + 1) nodeIndex))
    (val := fun k j ↦ d.value (tpos l τ k j)) (fun k hk a b hab ↦ ?_) (by rw [h0]; exact h)
  have hj : e.val / 2 ^ (k + 1) < 2 ^ (layerHeight l - (k + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
    exact he
  have hT : InTable (.node l τ (k + 1) (e.val / 2 ^ (k + 1))) := ⟨hτ, by omega, by omega, hj⟩
  have hidx : e.val / 2 ^ (k + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _)
    (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by omega)))
  obtain ⟨hp, -⟩ := honest_of_addressed hN hnb hT hab
    (slotOf_node _ d.pk l τ _ _ (by omega) hidx a b)
    (by simp [slotPayload, nodePayload, littleEndianBytes]) rfl
  exact Quantum.Xmss.nodePayload_injective hp

/-- **A one-time leaf at its honest value** (no hit): the chain ends are the honest ones. -/
theorem leaf_meet (hN : dbGrade W ≤ N) (hnb : (D, W, m) ∉ Bad d N) {l : Layer} {τ : TreeIndex}
    {e : TreeLeafIndex} (hk : InTable (.leaf l τ e)) {E : ChainIndex → Digest}
    (h : WithHash.leafHash (viewHash d.perm (union W D)) d.seed l τ e E =
      some (d.value (tpos l τ 0 e.val))) :
    ∀ i, E i = d.value (cpos l τ e i (chainLength - 1)) := by
  obtain ⟨hp, -⟩ := honest_of_addressed hN hnb hk h (slotOf_leaf _ d.pk l τ e E)
    ((length_digestsPayload _).trans (length_digestsPayload _).symm) rfl
  exact congrFun (digestsPayload_inj hp)

/-- **A FORS tree ending at its honest root** (no hit): the opening is the honest secret and path,
and the leaf's slot is exempted. -/
theorem forsTree_meet (hN : dbGrade W ≤ N) (hnb : (D, W, m) ∉ Bad d N) {idx : Index}
    {κ : ForsTreeIndex} {s : ForsLeafIndex} {op : ForsTreeOpening} {lf : Digest}
    (hlf : WithHash.forsLeafHash (viewHash d.perm (union W D)) d.seed idx κ s op.secret = some lf)
    (h : foldPath (fun level node ↦ WithHash.tweakableHash (viewHash d.perm (union W D)) d.seed
        (.forsNode idx κ (level + 1) node)) s.val
      (fun level ↦ if h : level < forsTreeHeight then op.path ⟨level, h⟩ else 0) forsTreeHeight lf =
        some (d.value (fpos idx κ forsTreeHeight 0))) :
    op.secret = d.value (.forsSecret idx κ s) ∧
      (∀ z : Fin forsTreeHeight,
        op.path z = d.value (fpos idx κ z.val ((s.val >>> z.val) ^^^ 1))) ∧
      Slot.forsLeaf idx κ s ∈ d.exS W := by
  have hs : s.val < 2 ^ forsTreeHeight := s.isLt
  have h0 : s.val / 2 ^ forsTreeHeight = 0 := Nat.div_eq_of_lt hs
  have key := foldPath_meet (node := fun level node ↦ WithHash.tweakableHash
      (viewHash d.perm (union W D)) d.seed (.forsNode idx κ (level + 1) node))
    (val := fun k j ↦ d.value (fpos idx κ k j)) (n := forsTreeHeight) (leaf := s.val)
    (fun k hk a b hab ↦ by
      have hk' : k < 10 := hk
      have hj : s.val / 2 ^ (k + 1) < 2 ^ (forsTreeHeight - (k + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
        exact hs
      have hT : InTable (.forsNode idx κ (k + 1) (s.val / 2 ^ (k + 1))) :=
        ⟨by omega, by omega, hj⟩
      obtain ⟨hp, -⟩ := honest_of_addressed hN hnb hT hab
        (slotOf_forsNode _ d.pk idx κ _ _ (by omega) hk hj a b)
        (by simp [slotPayload, nodePayload, littleEndianBytes]) rfl
      exact Quantum.Xmss.nodePayload_injective hp)
    (by rw [h0]; exact h)
  obtain ⟨hp, hex⟩ := honest_of_addressed hN hnb (s := .forsLeaf idx κ s) trivial hlf
    (slotOf_forsLeaf _ d.pk idx κ s op.secret)
    ((Quantum.Xmss.length_littleEndianBytes 16 _).trans
      (Quantum.Xmss.length_littleEndianBytes 16 _).symm) key.1
  refine ⟨littleEndianBytes_injective 16 hp, fun z ↦ ?_, hex⟩
  have hz := key.2 z.val z.isLt
  simp only [z.isLt, dite_true] at hz
  rw [Nat.shiftRight_eq_div_pow]
  exact hz

/-- **A FORS key at its honest value** (no hit): the roots are the honest ones. -/
theorem forsRoots_meet (hN : dbGrade W ≤ N) (hnb : (D, W, m) ∉ Bad d N) {idx : Index}
    {roots : ForsTreeIndex → Digest}
    (h : WithHash.forsPublicKey (viewHash d.perm (union W D)) d.seed idx roots =
      some (d.value (.forsKey idx))) :
    ∀ κ, roots κ = d.value (fpos idx κ forsTreeHeight 0) := by
  obtain ⟨hp, -⟩ := honest_of_addressed hN hnb (s := .forsRoots idx) trivial h
    (slotOf_forsRoots _ d.pk idx roots)
    ((length_digestsPayload _).trans (length_digestsPayload _).symm) rfl
  exact congrFun (digestsPayload_inj hp)

/-- **An encoding at a selected key's digest** (no hit): a trial of key `K` whose view digest is
the recorded digest `y` of the selected block `x` is the selected trial, on the value `K` signs. -/
theorem enc_meet (hN : dbGrade W ≤ N) (hnb : (D, W, m) ∉ Bad d N) {K : Key} {c : EncodingCounter}
    {x : X} {y : Digest} (hsel : m.2 K = some (x, y)) (hx : blocks (d.encInput K c) = [x])
    {msg : Digest} {c' : EncodingCounter} {o : HashOutput}
    (hv : viewHash d.perm (union W D) (addressedHashInput d.seed
      (hashDomainFields (.encoding K.1 K.2.1 K.2.2))
      (littleEndianBytes 16 msg ++ bigEndianBytes 4 c')) = some o)
    (hy : truncateHash o = y) : msg = d.value (msgPos K) ∧ c' = c := by
  obtain ⟨hon, rfl⟩ := viewHash_eq_some_iff.1 hv
  set u := addressedHashInput d.seed (hashDomainFields (.encoding K.1 K.2.1 K.2.2))
    (littleEndianBytes 16 msg ++ bigEndianBytes 4 c') with hu
  have hlen : u.length < 136 := by
    have hp : (littleEndianBytes 16 msg ++ bigEndianBytes 4 c').length = 20 := by
      simp [littleEndianBytes, bigEndianBytes]
    rw [hu, length_addressedHashInput, hp]
    norm_num
  have ht : absorbTail (viewPerm d.perm (union W D)) (blocks u) = blocks u :=
    Quantum.Xmss.absorbTail_blocks_of_lt _ hlen
  by_cases he : blocks u = [x]
  · have hx' : blocks (addressedHashInput d.seed (hashDomainFields (.encoding K.1 K.2.1 K.2.2))
        (littleEndianBytes 16 (d.value (msgPos K)) ++ bigEndianBytes 4 c)) = [x] := hx
    have hp := (addressedHashInput_injective d.seed (blocks_injective (he.trans hx'.symm))).2
    obtain ⟨h1, h2⟩ := List.append_inj hp (by simp [littleEndianBytes])
    exact ⟨littleEndianBytes_injective 16 h1, bigEndianBytes_injective 4 h2⟩
  · exfalso
    have hslot : slotOf d.pk (blocks u) = some (.enc K.1 K.2.1 K.2.2) := by
      rw [← ht]
      exact slotOf_encoding _ d.pk K.1 K.2.1 K.2.2 msg c'
    have hr := Quantum.Xmss.reaches_of_onPath hon
    rw [ht, hy] at hr
    exact hnb (mem_bad_of_tgt hN (sphTgt_enc hslot hsel he) hr)

end Hits

/-! ## Indices and the values the keys sign -/

theorem treeOfIndex_lt_treeBits (l : Layer) (idx : Index) :
    (treeOfIndex l idx).val < 2 ^ treeBits l := by
  have hi : idx.val < 2 ^ 26 := idx.isLt
  fin_cases l <;>
    simp only [treeOfIndex, treeBits, indexBits, bitsBelowLayer, layerHeight] <;> norm_num <;> omega

theorem msgPos_keyOf_zero (idx : Index) : msgPos (keyOf 0 idx) = .forsKey idx := by
  change ValPos.forsKey (indexBelow 0 (treeOfIndex 0 idx) (leafOfIndex 0 idx)) = .forsKey idx
  refine congrArg ValPos.forsKey (Fin.ext ?_)
  have hi : idx.val < 67108864 := idx.isLt
  change ((treeOfIndex 0 idx).val * 2 ^ 8 + (leafOfIndex 0 idx).val) % 2 ^ 26 = idx.val
  rw [treeOfIndex_zero, leafOfIndex_zero]
  change (idx.val / 256 * 256 + idx.val % 256) % 67108864 = idx.val
  omega

theorem msgPos_keyOf_one (idx : Index) :
    msgPos (keyOf 1 idx) = tpos 0 (treeOfIndex 0 idx) (layerHeight 0) 0 := by
  change tpos 0 (indexBelow 1 (treeOfIndex 1 idx) (leafOfIndex 1 idx)) 8 0 =
    tpos 0 (treeOfIndex 0 idx) 8 0
  refine congrArg (fun τ ↦ tpos 0 τ 8 0) (Fin.ext ?_)
  have hi : idx.val < 67108864 := idx.isLt
  change (idx.val / 65536 * 256 + idx.val / 256 % 256) % 67108864 = idx.val / 256
  omega

theorem msgPos_keyOf_two (idx : Index) :
    msgPos (keyOf 2 idx) = tpos 1 (treeOfIndex 1 idx) (layerHeight 1) 0 := by
  change tpos 1 (indexBelow 2 (treeOfIndex 2 idx) (leafOfIndex 2 idx)) 8 0 =
    tpos 1 (treeOfIndex 1 idx) 8 0
  refine congrArg (fun τ ↦ tpos 1 τ 8 0) (Fin.ext ?_)
  have hi : idx.val < 67108864 := idx.isLt
  change (idx.val / 67108864 * 1024 + idx.val / 65536 % 1024) % 67108864 = idx.val / 65536
  omega

/-! ## Signatures of a selection function -/

/-- **A selection function**: for each WOTS+C key, the selected counter and word (none when the
key has no selection). A key signs one fixed value (`msgPos`), so its selection does not depend on
the message. -/
abbrev SelFn : Type :=
  Key → Option (EncodingCounter × Encoding)

/-- **The positions the signature on the view `w` with the selection `S` discloses**: the FORS
secrets at the view's leaves and their paths, and for each layer whose key has a selection its
opened chain positions and its path (a layer is disclosed as soon as its key is selected, even when
a layer above it has no selection). -/
def selDisclosedBy (S : SelFn) (w : View) : Set ValPos :=
  forsDisclosed w.1 w.2 ∪ {p | ∃ l sel, S (keyOf l w.1) = some sel ∧
    p ∈ layerDisclosed l (treeOfIndex l w.1) (leafOfIndex l w.1) sel.2}

/-- **The positions disclosed after signing the messages `msgs`**: the root, and the signature of
each message `M` on the view of its digest outputs `dig M`. -/
def selDisclosures (S : SelFn) (dig : Message → DigestCall → HashOutput) (msgs : List Message) :
    Set ValPos :=
  {rootPos} ∪ {p | ∃ M ∈ msgs, p ∈ selDisclosedBy S (digestView (dig M))}

namespace EvData

variable (d : EvData)

/-- The signature of layer `l` in a signature of index `idx` with the selection `S`: the selected
counter, the chains opened to the selected word, and the key's path, at the values. -/
def selLayerSig (S : SelFn) (l : Layer) (idx : Index) : Option (LayerSignature l) :=
  (S (keyOf l idx)).map fun sel ↦ ⟨sel.1,
    fun i ↦ d.value (cpos l (treeOfIndex l idx) (leafOfIndex l idx) i (sel.2 i).val),
    fun z ↦ d.value (tpos l (treeOfIndex l idx) z.val
      (((leafOfIndex l idx).val >>> z.val) ^^^ 1))⟩

/-- The FORS opening of the view `w` at the values: the secrets at its leaves and their paths. -/
def forsOpen (w : View) : ForsTreeIndex → ForsTreeOpening :=
  fun κ ↦ ⟨d.value (.forsSecret w.1 κ (w.2 κ)),
    fun z ↦ d.value (fpos w.1 κ z.val (((w.2 κ).val >>> z.val) ^^^ 1))⟩

/-- **The signature with the selection `S`** of a message with randomizer `R` and digest view `w`:
none unless every layer's key has a selection. -/
def selSig (S : SelFn) (R : Randomizer) (w : View) : Option Signature :=
  match d.selLayerSig S 0 w.1, d.selLayerSig S 1 w.1, d.selLayerSig S 2 w.1 with
  | some b, some m, some t =>
      some ⟨R, d.forsOpen w, KeyGenerationAndSigning.layerSignatures b m t⟩
  | _, _, _ => none

/-- **The selections record `S`**: each selected key's selected trial block and a digest decoding
to the selected word. -/
def RecordsSel (S : SelFn) (sel : Selections) : Prop :=
  ∀ K c, S K = some c → ∃ x y, sel K = some (x, y) ∧ blocks (d.encInput K c.1) = [x] ∧
    TargetSum.decodeDigest y = some c.2

/-- The input of call `c` of `H_msg` at the randomizer `R` and the message `M`, under the public
key. -/
def hmsgInput (R : Randomizer) (M : Message) (c : DigestCall) : HashInput :=
  messageDigestInput R d.seed (d.value rootPos) M c

/-- **`U` holds a hash of `u` with output `y`**: every read of `u` under some keys, which output
`y`. -/
def HashHeld (U : Dbs X Z) (u : HashInput) (y : HashOutput) : Prop :=
  ∃ t : SpongeKeys X Z, (∀ e ∈ spongeReads d.perm t.1 t.2.1 t.2.2 (blocks u), e.HeldBy U) ∧
    out256 (spongeHash (spongePerm t d.perm) (blocks u)) = y

end EvData

/-! ## Disclosed positions -/

section Disclosed

variable {S : SelFn} {dig : Message → DigestCall → HashOutput} {msgs : List Message}

/-- A computable chain position lies above a disclosed position of its chain. -/
theorem known_chain_pos {Dp : Set ValPos} {p : ValPos} (h : Known Dp p) :
    ∀ l τ e i (j : Fin chainLength), p = .chain l τ e i j →
      ∃ j' : Fin chainLength, j' ≤ j ∧ ValPos.chain l τ e i j' ∈ Dp := by
  induction h with
  | disclosed p hp =>
    rintro l τ e i j rfl
    exact ⟨j, le_rfl, hp⟩
  | chain l τ e i step _ _ ih =>
    intro l' τ' e' i' j' hp
    simp only [cpos, ValPos.chain.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hp
    obtain ⟨j'', hj'', hm⟩ := ih l τ e i _ rfl
    refine ⟨j'', ?_, hm⟩
    have hs : step.val < 3 := step.isLt
    rw [Fin.le_def] at hj'' ⊢
    simp only [chainLength, HashSig.winternitzBits, Nat.reducePow] at hj'' ⊢
    omega
  | leaf => intro _ _ _ _ _ hp; simp [tpos] at hp
  | node => intro _ _ _ _ _ hp; simp [tpos] at hp
  | forsLeaf => intro _ _ _ _ _ hp; simp [fpos] at hp
  | forsNode => intro _ _ _ _ _ hp; simp [fpos] at hp
  | forsRoots => intro _ _ _ _ _ hp; cases hp

/-- **A disclosed chain position is opened by a selection of its key.** -/
theorem sel_of_chain_mem {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {i : ChainIndex}
    {j : Fin chainLength} (h : ValPos.chain l τ e i j ∈ selDisclosures S dig msgs) :
    ∃ sel, S (l, τ, e) = some sel ∧ sel.2 i = j := by
  rcases h with h | ⟨M, -, h⟩
  · simp [rootPos, tpos] at h
  rcases h with ⟨κ, h | ⟨z, h⟩⟩ | ⟨l', sel, hS, ⟨i', h⟩ | ⟨z, h⟩⟩
  · cases h
  · simp [fpos] at h
  · simp only [cpos, ValPos.chain.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨sel, hS, Fin.ext (Nat.mod_eq_of_lt (sel.2 _).isLt).symm⟩
  · simp [tpos] at h

/-- A computable FORS secret is disclosed. -/
theorem known_forsSecret {Dp : Set ValPos} {idx : Index} {κ : ForsTreeIndex} {s : ForsLeafIndex}
    (h : Known Dp (.forsSecret idx κ s)) : ValPos.forsSecret idx κ s ∈ Dp := by
  rcases known_iff.1 h with h | ⟨s', hs, hout, -⟩
  · exact h
  · exfalso
    cases s' <;> simp [slotOutPos, cpos, tpos, fpos, InTable] at hout hs

/-- **A disclosed FORS secret is a signed view's leaf.** -/
theorem view_of_forsSecret_mem {idx : Index} {κ : ForsTreeIndex} {s : ForsLeafIndex}
    (h : ValPos.forsSecret idx κ s ∈ selDisclosures S dig msgs) :
    ∃ M ∈ msgs, (digestView (dig M)).1 = idx ∧ (digestView (dig M)).2 κ = s := by
  rcases h with h | ⟨M, hM, h⟩
  · simp [rootPos, tpos] at h
  rcases h with ⟨κ', h | ⟨z, h⟩⟩ | ⟨l', sel, -, ⟨i', h⟩ | ⟨z, h⟩⟩
  · simp only [ValPos.forsSecret.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨M, hM, rfl, rfl⟩
  · simp [fpos] at h
  · simp [cpos] at h
  · simp [tpos] at h

end Disclosed

/-! ## The classification -/

/-- **The classical facts of a winning run** at the hardwired cells `W` and the memory `m`, for a
selection `S`, randomizers `rnd` and digest outputs `dig` of the signed messages:

* `grade`: few hardwired cells;
* `sigs`: the transcript's signatures are those of `S` (`selSig`), message `M` on the view of
  `dig M` with randomizer `rnd M`;
* `records`: the memory's selections record `S` (`RecordsSel`);
* `exempt`: **the exempted structural slots are public** (`exS W ⊆ Public`) for the disclosures of
  the signed messages (`selDisclosures`);
* `cover`: the static coverage set covers the view of every signed message;
* `covEx`: **the exempted `H_msg` pairs are signed pairs** `(rnd M, M)`;
* `digests`: the hardwired cells hold both `H_msg` calls of every signed pair with the outputs
  `dig M`;
* `fresh`: the forgery is not a returned signature. -/
structure WinFacts {Lb : Type} (d : EvData) (N : ℕ) (S : SelFn) (rnd : Message → Randomizer)
    (dig : Message → DigestCall → HashOutput) (log : QueryLog SigningOracleSpec)
    (forgery : Forgery) (W : Hw X Z) (m : Mem Lb) : Prop where
  grade : dbGrade W ≤ N
  sigs : ∀ r ∈ log, r.2 = d.selSig S (rnd r.1) (digestView (dig r.1))
  records : d.RecordsSel S m.2
  exempt : d.exS W ⊆ Public (selDisclosures S dig (log.map Sigma.fst))
  cover : ∀ r ∈ log, Covered d.cover (digestView (dig r.1))
  covEx : ∀ p ∈ d.covEx W, ∃ r ∈ log, r.1 = p.2 ∧ p.1 = rnd r.1
  digests : ∀ r ∈ log, ∀ c, d.HashHeld W.toDbs (d.hmsgInput (rnd r.1) r.1 c) (dig r.1 c)
  fresh : ¬SignerReturnedForgery id log forgery.message forgery.signature

/-- A signature is its three layers. -/
theorem layerSignatures_layers (σ : Signature) :
    KeyGenerationAndSigning.layerSignatures (σ.layers 0) (σ.layers 1) (σ.layers 2) = σ.layers := by
  funext l
  fin_cases l <;> rfl

/-- A signature whose layers are the selection's and whose opening is the view's is the selection's
signature. -/
theorem EvData.selSig_eq_some {d : EvData} {S : SelFn} {R : Randomizer} {w : View}
    {σ : Signature} (h0 : d.selLayerSig S 0 w.1 = some (σ.layers 0))
    (h1 : d.selLayerSig S 1 w.1 = some (σ.layers 1))
    (h2 : d.selLayerSig S 2 w.1 = some (σ.layers 2)) (hR : σ.randomizer = R)
    (hf : d.forsOpen w = σ.forsOpening) : d.selSig S R w = some σ := by
  unfold EvData.selSig
  rw [h0, h1, h2]
  change some ⟨R, d.forsOpen w,
    KeyGenerationAndSigning.layerSignatures (σ.layers 0) (σ.layers 1) (σ.layers 2)⟩ = some σ
  rw [hf, layerSignatures_layers, ← hR]

/-- **A hardwired hash is the view's**: the union view of an input whose hash the hardwired cells
hold outputs that hash. -/
theorem eq_of_hashHeld {d : EvData} {W : Hw X Z} (D : DbReg X Z) {u : HashInput}
    {y o : HashOutput} (hh : d.HashHeld W.toDbs u y) (hv : viewHash d.perm (union W D) u = some o) :
    o = y := by
  obtain ⟨t, hr, rfl⟩ := hh
  obtain ⟨-, rfl⟩ := viewHash_eq_some_iff.1 hv
  have hc := (Quantum.SufCma.spongeReads_congr d.perm (blocks u)
    fun e he ↦ SpongeRead.answeredBy_fill (heldBy_union D (hr e he))).2
  change out256 (spongeHash (spongePerm (union W D).fill d.perm) (blocks u)) = _
  rw [spongeHash, spongeHash, hc]

theorem layerSignature_ext {l : Layer} {a b : LayerSignature l} (h1 : a.counter = b.counter)
    (h2 : a.chainValues = b.chainValues) (h3 : a.authenticationPath = b.authenticationPath) :
    a = b := by
  cases a
  cases b
  cases h1
  cases h2
  cases h3
  rfl

theorem forsTreeOpening_ext {a b : ForsTreeOpening} (h1 : a.secret = b.secret)
    (h2 : a.path = b.path) : a = b := by
  cases a
  cases b
  cases h1
  cases h2
  rfl

section Layers

variable {Lb : Type} {d : EvData} {N : ℕ} {S : SelFn} {dig : Message → DigestCall → HashOutput}
  {msgs : List Message} {D : DbReg X Z} {W : Hw X Z} {m : Mem Lb}

/-- **A layer reaching the honest root of its tree** (no hit, `Quantum.Xmss.layer_meet_sel`): it
signs the value its key signs, and it is the layer signature of the selection. The forged word is
opened at a chain below its end (a codeword), whose first step is then exempted, hence public,
hence opened by the selection of the same key at or below the forged position; so the selected word
is pointwise below the forged one, equal to it by incomparability, and the forged encoding input is
the selected one, or an encoding hit. -/
theorem layer_meet (hN : dbGrade W ≤ N) (hnb : (D, W, m) ∉ Bad d N) (hrec : d.RecordsSel S m.2)
    (hEx : d.exS W ⊆ Public (selDisclosures S dig msgs)) {l : Layer} {idx : Index}
    {σ : Signature} {msg root : Digest}
    (hok : LayerOk (viewHash d.perm (union W D)) d.seed idx σ l msg root)
    (hroot : root = d.value (tpos l (treeOfIndex l idx) (layerHeight l) 0)) :
    msg = d.value (msgPos (keyOf l idx)) ∧ d.selLayerSig S l idx = some (σ.layers l) := by
  subst hroot
  have hτ := treeOfIndex_lt_treeBits l idx
  have he := leafOfIndex_lt l idx
  obtain ⟨v, hots, hfold⟩ := hok
  obtain ⟨hv, hpath⟩ := tree_meet hN hnb hτ he hfold
  obtain ⟨o, x, ho, hx, E, hE, hleaf⟩ := otsLeaf_spec hots
  rw [hv] at hleaf
  have hEh := leaf_meet hN hnb ⟨hτ, he⟩ hleaf
  -- The chains: the forged values are honest, and the steps leaving them exempted.
  have hchain : ∀ i, (σ.layers l).chainValues i =
      d.value (cpos l (treeOfIndex l idx) (leafOfIndex l idx) i (x i).val) ∧
      ∀ h : (x i).val < chainLength - 1,
        Slot.chain l (treeOfIndex l idx) (leafOfIndex l idx) i ⟨(x i).val, h⟩ ∈ d.exS W := by
    intro i
    have hi := (x i).isLt
    have hEi : WithHash.chainWalk (viewHash d.perm (union W D)) d.seed l (treeOfIndex l idx)
        (leafOfIndex l idx) i (x i).val (chainLength - 1 - (x i).val)
        ((σ.layers l).chainValues i) = some (d.value (cpos l (treeOfIndex l idx)
          (leafOfIndex l idx) i ((x i).val + (chainLength - 1 - (x i).val)))) := by
      rw [show (x i).val + (chainLength - 1 - (x i).val) = chainLength - 1 by omega]
      exact (hE i).trans (congrArg some (hEh i))
    obtain ⟨hval, hex⟩ := chain_meet hN hnb ⟨hτ, he⟩ _ _ _ (by omega) hEi
    exact ⟨hval, fun h ↦ hex h (by omega)⟩
  -- An exempted step is public: a selection of the same key opened its chain at or below it.
  have hknown : ∀ i, (x i).val < chainLength - 1 →
      ∃ sel, S (keyOf l idx) = some sel ∧ sel.2 i ≤ x i := by
    intro i hi
    have hpub := hEx ((hchain i).2 hi)
    obtain ⟨j', hj', hm⟩ := known_chain_pos hpub.2 l (treeOfIndex l idx) (leafOfIndex l idx) i
      (x i) (congrArg (ValPos.chain l _ _ i) (Fin.ext (Nat.mod_eq_of_lt (x i).isLt)))
    obtain ⟨sel, hS, hsel⟩ := sel_of_chain_mem hm
    exact ⟨sel, hS, hsel ▸ hj'⟩
  have hvx := Codeword.sum_eq_of_decode hx
  obtain ⟨i0, hi0⟩ := Codeword.exists_lt_of_sum hvx
  obtain ⟨sel, hS, -⟩ := hknown i0 hi0
  have hle : ∀ i, sel.2 i ≤ x i := by
    intro i
    by_cases h : (x i).val < chainLength - 1
    · obtain ⟨sel', hS', hle⟩ := hknown i h
      rw [hS] at hS'
      obtain rfl := Option.some.inj hS'
      exact hle
    · rw [Fin.le_def]
      have := (sel.2 i).isLt
      omega
  -- Incomparability: the forged word is the selected one; then the encoding input is.
  obtain ⟨xb, y, hm2, hxb, hy⟩ := hrec _ sel hS
  have hxs : sel.2 = x := Codeword.eq_of_le (Codeword.sum_eq_of_decode hy) hvx hle
  obtain ⟨hmsg, hc⟩ := enc_meet hN hnb hm2 hxb ho (Codeword.eq_of_decode hx (hxs ▸ hy))
  refine ⟨hmsg, ?_⟩
  have h2 : (fun i ↦ d.value (cpos l (treeOfIndex l idx) (leafOfIndex l idx) i (sel.2 i).val)) =
      (σ.layers l).chainValues := by
    funext i
    rw [(hchain i).1, hxs]
  have h3 : (fun z : Fin (layerHeight l) ↦ d.value (tpos l (treeOfIndex l idx) z.val
      (((leafOfIndex l idx).val >>> z.val) ^^^ 1))) = (σ.layers l).authenticationPath := by
    funext z
    have hz := hpath z.val z.isLt
    rw [Verification.layerPath, dite_eq_left z.isLt] at hz
    rw [Nat.shiftRight_eq_div_pow]
    exact hz.symm
  change Option.map _ (S (keyOf l idx)) = _
  rw [hS]
  exact congrArg some (layerSignature_ext hc.symm h2 h3)

end Layers

section Win

variable {Lb : Type} {d : EvData} {N : ℕ} {S : SelFn} {rnd : Message → Randomizer}
  {dig : Message → DigestCall → HashOutput} {log : QueryLog SigningOracleSpec} {forgery : Forgery}
  {D : DbReg X Z} {W : Hw X Z} {m : Mem Lb}

/-- **A win is in the event** (`Quantum.Xmss.win_imp_bad_sel` for leanSPHINCS): a forgery that
verifies under the union view, with the classical facts of a winning run (`WinFacts`), puts the
register in `Bad d N`. The three layers meet the honest trees from the top (`layer_meet`), so the
FORS key is the honest key of the forged index, the roots and the openings are honest
(`forsRoots_meet`, `forsTree_meet`) and every opened leaf's slot is exempted. If the forged pair is
an exempted one, it is a signed pair, whose digests the hardwired cells fix, so the forgery is the
signature returned for its message; otherwise the opened secrets are disclosed, their leaves are
covered, and the forged call-0 tail is a coverage hit. -/
theorem win_imp_bad_sel (hf : WinFacts d N S rnd dig log forgery W m)
    (hver : WithHash.verify (viewHash d.perm (union W D)) d.pk forgery.message
      forgery.signature = some true) :
    (D, W, m) ∈ Bad d N := by
  by_contra hnb
  have hN := hf.grade
  obtain ⟨o, ho, fk, hfk, hlay⟩ := verify_spec hver
  obtain ⟨r0, r1, h0, h1, h2⟩ := verifyLayers_spec hlay
  -- The layers, from the top.
  have ht : treeOfIndex 2 (digestView o).1 = 0 := treeOfIndex_topLayer _
  obtain ⟨hm2, hs2⟩ := layer_meet hN hnb hf.records hf.exempt h2 (by
    change d.value (tpos topLayer 0 (layerHeight topLayer) 0) = _
    rw [ht]
    rfl)
  rw [msgPos_keyOf_two] at hm2
  obtain ⟨hm1, hs1⟩ := layer_meet hN hnb hf.records hf.exempt h1 hm2
  rw [msgPos_keyOf_one] at hm1
  obtain ⟨hm0, hs0⟩ := layer_meet hN hnb hf.records hf.exempt h0 hm1
  rw [msgPos_keyOf_zero] at hm0
  -- FORS: the roots and the openings are honest, the opened leaves exempted.
  obtain ⟨roots, hroots, hpk⟩ := forsRecover_spec hfk
  rw [hm0] at hpk
  have hr := forsRoots_meet hN hnb hpk
  have hfors : ∀ κ,
      (forgery.signature.forsOpening κ).secret =
        d.value (.forsSecret (digestView o).1 κ ((digestView o).2 κ)) ∧
      (∀ z : Fin forsTreeHeight, (forgery.signature.forsOpening κ).path z =
        d.value (fpos (digestView o).1 κ z.val ((((digestView o).2 κ).val >>> z.val) ^^^ 1))) ∧
      Slot.forsLeaf (digestView o).1 κ ((digestView o).2 κ) ∈ d.exS W := fun κ ↦ by
    obtain ⟨lf, hlf, hfold⟩ := hroots κ
    rw [hr κ] at hfold
    exact forsTree_meet hN hnb hlf hfold
  by_cases hcov : (forgery.signature.randomizer, forgery.message) ∈ d.covEx W
  · -- A signed pair: the digests are the signed ones, and the forgery the returned signature.
    obtain ⟨r, hrl, hrM, hrR⟩ := hf.covEx (forgery.signature.randomizer, forgery.message) hcov
    dsimp only at hrM hrR
    have hdo : o = dig r.1 := funext fun c ↦ eq_of_hashHeld D (hf.digests r hrl c) (by
      have h := ho c
      rw [hrR, ← hrM] at h
      exact h)
    apply hf.fresh
    refine ⟨r, hrl, hrM, ?_⟩
    rw [hf.sigs r hrl, ← hdo]
    refine EvData.selSig_eq_some hs0 hs1 hs2 hrR (funext fun κ ↦ ?_)
    exact forsTreeOpening_ext (hfors κ).1.symm (funext fun z ↦ ((hfors κ).2.1 z).symm)
  · -- Otherwise the opened leaves are covered, and the call-0 tail is a coverage hit.
    apply hnb
    have hcovd : Covered d.cover (digestView o) := fun κ ↦ by
      have hk := known_forsSecret (hf.exempt (hfors κ).2.2).2
      obtain ⟨M, hM, hi, hl⟩ := view_of_forsSecret_mem hk
      obtain ⟨r, hrl, rfl⟩ := List.mem_map.1 hM
      have hc := hf.cover r hrl κ
      rw [hi, hl] at hc
      exact hc
    rw [digestView_eq] at hcovd
    have hhalf : HalfCov d.cover (hiOf (o 0), leavesOf (o 0)) :=
      (halfCov_iff _ _ _).2 ⟨loOf (o 1), (joinIndex _ _).isLt, hcovd⟩
    obtain ⟨hon, hoo⟩ := viewHash_eq_some_iff.1 (ho 0)
    have hreach := reaches_of_onPath_out out256 hon
    have hy : out256 (spongeHash (viewPerm d.perm (union W D)) (blocks
        (messageDigestInput forgery.signature.randomizer d.pk.publicSeed d.pk.root
          forgery.message 0))) = o 0 := hoo
    rw [hy] at hreach
    exact mem_bad_of_cov hN (slotOf_messageDigestInput_self _ d.pk _ _ 0) hcov hreach hhalf

/-- **Verification through the union view**: an honest evaluation of the verifier that accepts with
its reads held by `U` accepts with every hash answered by `viewHash π U`. -/
theorem verify_viewHash_of_honestEval {π : Equiv.Perm (X × Z)} {U : Dbs X Z} {pk : PublicKey}
    {f : Forgery} (hv : (honestEval U.fill π (schemeWithHash.verify pk f)).1 = true)
    (hr : ∀ e ∈ (honestEval U.fill π (schemeWithHash.verify pk f)).2, e.HeldBy U) :
    WithHash.verify (viewHash π U) pk f.message f.signature = some true := by
  refine (WithHash.simulateQ_verify (n := Option) (viewHash π U) pk f.message
    f.signature).symm.trans ?_
  rw [simulateQ_option_eq_some _ (spongeOut (spongePerm U.fill π)) _ fun q hq ↦
    viewHash_eq_some_iff.2 ⟨fun e he ↦ hr e (by
      rw [snd_honestEval]
      exact List.mem_flatMap.2 ⟨q, hq, he⟩), rfl⟩]
  rw [← fst_honestEval]
  exact congrArg some hv

/-- **A win with recorded reads is in the event** (`Quantum.Xmss.mem_bad_of_agrees` for
leanSPHINCS): if the view `hwView W D` holds the log of the verification's reads, whose honest
evaluation on any database holding them accepts the forgery with its reads held, and the run has
the classical facts of a win, then the register is in `Bad d N`. -/
theorem mem_bad_of_agrees (hf : WinFacts d N S rnd dig log forgery W m)
    (rlog : QueryLog (spongeOSpec X Z))
    (hverify : ∀ U : Dbs X Z, (∀ e ∈ rlog.map toSpongeRead, e.HeldBy U) →
      (honestEval U.fill d.perm (schemeWithHash.verify d.pk forgery)).1 = true ∧
        ∀ e ∈ (honestEval U.fill d.perm (schemeWithHash.verify d.pk forgery)).2, e.HeldBy U)
    (hag : DbReg.Agrees rlog (hwView W D)) : (D, W, m) ∈ Bad d N := by
  have hU := hverify (union W D) ((agrees_iff_forall_heldBy rlog (hwView W D)).1 hag)
  exact win_imp_bad_sel hf (verify_viewHash_of_honestEval hU.1 hU.2)

end Win

end Quantum.Sphincs

end
