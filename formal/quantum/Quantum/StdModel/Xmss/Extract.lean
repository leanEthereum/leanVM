module

public import Quantum.StdModel.Xmss.Gen
public import Quantum.Xmss.Classify

@[expose] public section

/-!
# leanXMSS's standard-model reduction: a forgery yields an event

`extract`: a forgery that verifies under the hash `h` against the root of the ideal signer
`k.ops h`, for a transcript of that signer's answers with no leaf index reused, and that the signer
did not return, puts the reduction in `EncEv`, `TcrEv` or `CpreEv`. `extract_ops` proves it for
any operations whose leaf and node operations are the scheme's hashes.

The proof is by last divergence on each layer, top first. The forged Merkle path reaches the
honest root of its tree, so a node input differs from the honest children with the honest output
(`TcrEv`), or the forged leaf and path are honest; then the forged chain ends differ from the
honest ones with the honest leaf (`TcrEv`), or are honest. A forged chain value at a position below
its end is the honest value there and opened at or below it by a request with the key (else
`CpreEv`). A codeword has such a position, so the key encodes a request's message; all those
requests have the same message, hence the same codeword, which lies pointwise below the forged one
and so equals it (incomparability). The forged digest is then the honest one, and the forged message
and randomizer differ from the honest ones (`EncEv`) or the layer is the signer's. A signer's top
layer fixes the forged bottom root to the honest one, and with both layers the signer's, the
forgery is the signer's answer to the request at its leaf index.
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma

namespace Quantum.StdModel.Xmss

namespace Extract

/-! ## Computations in `Id` -/

theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x :=
  rfl

theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a :=
  rfl

theorem sequenceFin_id {β : Type} : ∀ {n : ℕ} (c : Fin n → Id β), sequenceFin c = c
  | 0, _ => funext fun i ↦ i.elim0
  | n + 1, c => by
    simp only [sequenceFin, id_bind, sequenceFin_id, id_pure]
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i

theorem keyAt_val (e : KeyIndex) : keyAt e.val = e :=
  Fin.ext (Nat.mod_eq_of_lt e.isLt)

/-! ## The honest signer -/

section Honest

variable (o : Ops Id)

theorem otsPublicKey_eq (l : Layer) (e : KeyIndex) :
    Gen.otsPublicKey o l e = fun i ↦ o.chain l e i (chainLength - 1) :=
  sequenceFin_id _

theorem treePath_eq (l : Layer) (e : KeyIndex) :
    Gen.treePath o l e =
      fun level ↦ Gen.treeNode o l level.val (Nat.xor (e.val / 2 ^ level.val) 1) :=
  sequenceFin_id _

theorem treeNode_zero (l : Layer) (e : KeyIndex) :
    Gen.treeNode o l 0 e.val = Gen.keyLeaf o l e := by
  change Gen.keyLeaf o l (keyAt e.val) = _
  rw [keyAt_val]

variable {o}

theorem signLayer_of {e : KeyIndex} {M : LayerMsg} {ρ : Randomizer} {D : Digest} {x : Encoding}
    (henc : o.encode e M = some (ρ, D)) (hdec : Codeword.decode D = some x) :
    Gen.signLayer o e M =
      some ⟨ρ, fun i ↦ o.chain M.layer e i (x i).val, Gen.treePath o M.layer e⟩ := by
  simp only [Gen.signLayer, id_bind, henc, hdec, sequenceFin_id, id_pure]

theorem sign_of {idx : LeafIndex} {M : Message} {sb st : LayerSignature}
    (hb : Gen.signLayer o (keyIndexOnLayer idx bottomLayer) (.inl M) = some sb)
    (ht : Gen.signLayer o (keyIndexOnLayer idx topLayer)
      (.inr (Gen.treeNode o bottomLayer layerHeight (keyIndexOnLayer idx topLayer).val)) =
        some st) :
    Gen.sign o idx M = some ⟨idx, fun l ↦ if l = bottomLayer then sb else st⟩ := by
  simp only [Gen.sign, id_bind, hb, ht, id_pure]

end Honest

/-! ## Messages and requests -/

theorem bytes_inj {M M' : LayerMsg} (hl : M.layer = M'.layer) (hb : M.bytes = M'.bytes) :
    M = M' := by
  rcases M with m | r <;> rcases M' with m' | r' <;>
    simp only [LayerMsg.layer, LayerMsg.bytes] at hl hb
  · rw [Quantum.Xmss.littleEndianBytes_injective 32 hb]
  · exact absurd hl (by decide)
  · exact absurd hl (by decide)
  · rw [Quantum.Xmss.littleEndianBytes_injective 16 hb]

variable {o : Ops Id}

theorem requestMsg_bottom {r : SigningRequest} {M : LayerMsg}
    (hM : requestMsg o r bottomLayer = some M) : M = .inl r.message := by
  have hb : requestMsg o r bottomLayer = some (.inl r.message) := ite_eq_left rfl
  exact (Option.some.inj (hb.symm.trans hM)).symm

theorem requestMsg_top {r : SigningRequest} {M : LayerMsg}
    (hM : requestMsg o r topLayer = some M) :
    M = .inr (Gen.treeNode o bottomLayer layerHeight
      (keyIndexOnLayer r.leafIndex topLayer).val) := by
  simp only [requestMsg, show topLayer ≠ bottomLayer by decide, ↓reduceIte,
    Option.ite_none_right_eq_some] at hM
  exact (Option.some.inj hM.2).symm

theorem requestMsg_layer {r : SigningRequest} {l : Layer} {M : LayerMsg}
    (hM : requestMsg o r l = some M) : M.layer = l := by
  by_cases hl : l = bottomLayer
  · subst hl
    rw [requestMsg_bottom hM]
    rfl
  · obtain rfl := Quantum.Xmss.eq_topLayer hl
    rw [requestMsg_top hM]
    rfl

/-- Two requests with the same key of a layer have it sign the same message. -/
theorem requestMsg_unique {log : QueryLog SigningOracleSpec}
    (hreuse : SigningTranscript.NoLeafIndexReused log)
    {r r' : (_ : SigningRequest) × Option Signature} (hr : r ∈ log) (hr' : r' ∈ log) {l : Layer}
    (hk : keyIndexOnLayer r.1.leafIndex l = keyIndexOnLayer r'.1.leafIndex l) {M M' : LayerMsg}
    (hM : requestMsg o r.1 l = some M) (hM' : requestMsg o r'.1 l = some M') : M = M' := by
  by_cases hl : l = bottomLayer
  · subst hl
    have hidx : r.1.leafIndex = r'.1.leafIndex := Fin.ext (by
      have := congrArg Fin.val hk
      simpa [keyIndexOnLayer, bottomLayer] using this)
    obtain rfl := List.inj_on_of_nodup_map hreuse hr hr' hidx
    exact Option.some.inj (hM.symm.trans hM')
  · obtain rfl := Quantum.Xmss.eq_topLayer hl
    rw [requestMsg_top hM, requestMsg_top hM', hk]

theorem honestMsg_of {log : QueryLog SigningOracleSpec}
    {r : (_ : SigningRequest) × Option Signature} (hr : r ∈ log) {l : Layer} {e : KeyIndex}
    (hk : keyIndexOnLayer r.1.leafIndex l = e) {M : LayerMsg} (hM : requestMsg o r.1 l = some M) :
    HonestMsg o log l e M :=
  ⟨r, hr, hk, hM⟩

/-! ## The forged layers -/

variable {h : HashInput → HashOutput} {P : PublicParameter}

theorem forgedMsg_layer {F : Forgery} {l : Layer} {M : LayerMsg}
    (hM : forgedMsg h P F l = some M) : M.layer = l := by
  unfold forgedMsg at hM
  split_ifs at hM with hl
  · obtain rfl := Option.some.inj hM
    exact hl.symm
  · obtain ⟨R, -, rfl⟩ := Option.map_eq_some_iff.1 hM
    exact (Quantum.Xmss.eq_topLayer hl).symm

/-- An accepted layer: its digest decodes to a word, and its root is the fold of the leaf of the
chain ends it recovers. -/
theorem layerRoot_some {l : Layer} {e : KeyIndex} {msg : HashInput} {ls : LayerSignature}
    {r : Digest} (hr : Qrom.Xmss.Over.layerRoot (m := Id) h P l e msg ls = some r) :
    ∃ x, Codeword.decode (Qrom.Xmss.Over.messageDigest (m := Id) h P l e msg ls.randomizer) =
      some x ∧
      Qrom.Xmss.Over.treeFold (m := Id) h P l e ls.authenticationPath layerHeight
        (Qrom.Xmss.Over.leafHash (m := Id) h P l e fun i ↦
          Qrom.Xmss.Over.recoverChain (m := Id) h P l e i (x i) (ls.chainValues i)) = r := by
  rcases hd : Codeword.decode (Qrom.Xmss.Over.messageDigest (m := Id) h P l e msg ls.randomizer)
    with _ | x
  · simp only [Qrom.Xmss.Over.layerRoot, Qrom.Xmss.Over.otsLeaf, id_bind, hd, id_pure] at hr
    cases hr
  · simp only [Qrom.Xmss.Over.layerRoot, Qrom.Xmss.Over.otsLeaf, id_bind, hd, id_pure,
      sequenceFin_id] at hr
    exact ⟨x, rfl, Option.some.inj hr⟩

/-- An accepted signature: its bottom layer reaches a root `R`, from which its top layer reaches
the public root. -/
theorem verify_true {root : Digest} {M : Message} {σ : Signature}
    (hv : Qrom.Xmss.Over.verify (m := Id) h ⟨root, P⟩ M σ = true) :
    ∃ R, Qrom.Xmss.Over.layerRoot (m := Id) h P bottomLayer
        (keyIndexOnLayer σ.leafIndex bottomLayer) (littleEndianBytes 32 M)
        (σ.layers bottomLayer) = some R ∧
      Qrom.Xmss.Over.layerRoot (m := Id) h P topLayer
        (keyIndexOnLayer σ.leafIndex topLayer) (littleEndianBytes 16 R)
        (σ.layers topLayer) = some root := by
  simp only [Qrom.Xmss.Over.verify, id_bind] at hv
  split at hv
  · next R hb =>
    split at hv
    · next r ht =>
      simp only [id_pure] at hv
      exact ⟨R, hb, ht.trans (congrArg some (of_decide_eq_true hv))⟩
    · simp only [id_pure] at hv
      cases hv
  · simp only [id_pure] at hv
    cases hv

theorem forgedFold_succ
    (hnode : ∀ l k j a b, o.node l k j a b =
      Qrom.Xmss.Over.tweakableHash (m := Id) h P (.node l (k + 1) j) (nodePayload a b))
    (F : Forgery) (l : Layer) (leaf : Digest) (k : ℕ) :
    forgedFold h P F l leaf (k + 1) =
      o.node l k ((forgedKey F l).val / 2 ^ (k + 1))
        (forgedKids F l k (forgedFold h P F l leaf k)).1
        (forgedKids F l k (forgedFold h P F l leaf k)).2 := by
  rw [hnode]
  unfold forgedKids
  simp only [forgedFold, Qrom.Xmss.Over.treeFold, foldPath, id_bind]
  by_cases hb : (forgedKey F l).val.testBit k <;>
    simp only [hb, ↓reduceIte, Bool.false_eq_true]

/-- Children equal to the honest children of the node above position `e / 2^k` at level `k`: the
value is the honest node there and the sibling is the honest sibling. -/
theorem kids_eq (o : Ops Id) (l : Layer) (e k : ℕ) (s v : Digest)
    (h : (if e.testBit k then (s, v) else (v, s)) =
      (Gen.treeNode o l k (2 * (e / 2 ^ (k + 1))),
        Gen.treeNode o l k (2 * (e / 2 ^ (k + 1)) + 1))) :
    v = Gen.treeNode o l k (e / 2 ^ k) ∧ s = Gen.treeNode o l k (Nat.xor (e / 2 ^ k) 1) := by
  have hj : e / 2 ^ (k + 1) = e / 2 ^ k / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hj, Nat.testBit_eq_decide_div_mod_eq] at h
  change _ ∧ s = Gen.treeNode o l k (e / 2 ^ k ^^^ 1)
  generalize e / 2 ^ k = y at h ⊢
  rcases Nat.mod_two_eq_zero_or_one y with hm | hm
  · have hx : y ^^^ 1 = y + 1 := Nat.xor_one_of_even (Nat.even_iff.2 hm)
    simp only [hm, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte,
      Prod.mk.injEq] at h
    rw [hx]
    exact ⟨h.1.trans (congrArg (Gen.treeNode o l k) (by omega)),
      h.2.trans (congrArg (Gen.treeNode o l k) (by omega))⟩
  · have hx : y ^^^ 1 = y - 1 := Nat.xor_one_of_odd (Nat.odd_iff.2 hm)
    simp only [hm, decide_true, ↓reduceIte, Prod.mk.injEq] at h
    rw [hx]
    exact ⟨h.2.trans (congrArg (Gen.treeNode o l k) (by omega)),
      h.1.trans (congrArg (Gen.treeNode o l k) (by omega))⟩

/-- **A forged Merkle path reaching the honest root**: a forged node input differs from the
honest children with the honest output, or the forged leaf and path are the honest ones. -/
theorem path_meet
    (hnode : ∀ l k j a b, o.node l k j a b =
      Qrom.Xmss.Over.tweakableHash (m := Id) h P (.node l (k + 1) j) (nodePayload a b))
    (F : Forgery) (l : Layer) (leaf : Digest)
    (hroot : forgedFold h P F l leaf layerHeight =
      Gen.treeNode o l layerHeight ((forgedKey F l).val / 2 ^ layerHeight)) :
    (∃ k < layerHeight,
      forgedKids F l k (forgedFold h P F l leaf k) ≠
        (Gen.treeNode o l k (2 * ((forgedKey F l).val / 2 ^ (k + 1))),
          Gen.treeNode o l k (2 * ((forgedKey F l).val / 2 ^ (k + 1)) + 1)) ∧
      o.node l k ((forgedKey F l).val / 2 ^ (k + 1))
          (forgedKids F l k (forgedFold h P F l leaf k)).1
          (forgedKids F l k (forgedFold h P F l leaf k)).2 =
        Gen.treeNode o l (k + 1) ((forgedKey F l).val / 2 ^ (k + 1))) ∨
    (leaf = Gen.keyLeaf o l (forgedKey F l) ∧
      (F.signature.layers l).authenticationPath = Gen.treePath o l (forgedKey F l)) := by
  let f : ℕ → Digest := fun k ↦ forgedFold h P F l leaf k
  let g : ℕ → Digest := fun k ↦ Gen.treeNode o l k ((forgedKey F l).val / 2 ^ k)
  let u : ℕ → Digest × Digest := fun k ↦ forgedKids F l k (f k)
  let w : ℕ → Digest × Digest := fun k ↦
    (Gen.treeNode o l k (2 * ((forgedKey F l).val / 2 ^ (k + 1))),
      Gen.treeNode o l k (2 * ((forgedKey F l).val / 2 ^ (k + 1)) + 1))
  have hkids : ∀ k, u k = w k → f k = g k ∧
      (if hk : k < layerHeight then (F.signature.layers l).authenticationPath ⟨k, hk⟩ else 0) =
        Gen.treeNode o l k (Nat.xor ((forgedKey F l).val / 2 ^ k) 1) :=
    fun k hk ↦ kids_eq o l (forgedKey F l).val k _ (f k) hk
  have hstep : ∀ k, k + 1 < layerHeight → u (k + 1) = w (k + 1) → f (k + 1) = g (k + 1) :=
    fun k _ hk ↦ (hkids (k + 1) hk).1
  rcases Quantum.Xmss.last_divergence u w f g layerHeight hroot hstep with
    ⟨k, hk, hne, hfg⟩ | hall
  · exact Or.inl ⟨k, hk, hne, (forgedFold_succ hnode F l leaf k).symm.trans hfg⟩
  · refine Or.inr ⟨?_, ?_⟩
    · have h0 : f 0 = g 0 := (hkids 0 (hall 0 (by decide))).1
      change leaf = Gen.treeNode o l 0 ((forgedKey F l).val / 2 ^ 0) at h0
      rw [pow_zero, Nat.div_one, treeNode_zero] at h0
      exact h0
    · rw [treePath_eq]
      funext k
      have hk := (hkids k.val (hall k.val k.isLt)).2
      simp only [k.isLt, ↓reduceDIte] at hk
      exact hk

/-- **One layer of a forgery reaching the honest root of its tree**: an event, or the layer is the
signer's signature of the forged message by a request with the forged key. -/
theorem layer_meet
    (hnode : ∀ l k j a b, o.node l k j a b =
      Qrom.Xmss.Over.tweakableHash (m := Id) h P (.node l (k + 1) j) (nodePayload a b))
    (hleaf : ∀ l e ends, o.leaf l e ends = Qrom.Xmss.Over.leafHash (m := Id) h P l e ends)
    {log : QueryLog SigningOracleSpec} (hreuse : SigningTranscript.NoLeafIndexReused log)
    (F : Forgery) (l : Layer) {M' : LayerMsg} (hM' : forgedMsg h P F l = some M') {x : Encoding}
    (hx : Codeword.decode (forgedDigest h P F l M') = some x)
    (hroot : forgedFold h P F l
        (Qrom.Xmss.Over.leafHash (m := Id) h P l (forgedKey F l) (forgedEnds h P F l x))
        layerHeight =
      Gen.treeNode o l layerHeight ((forgedKey F l).val / 2 ^ layerHeight)) :
    EncEv h P o log F ∨ TcrEv h P o F ∨ CpreEv h P o log F ∨
      ∃ r ∈ log, keyIndexOnLayer r.1.leafIndex l = forgedKey F l ∧ requestMsg o r.1 l = some M' ∧
        Gen.signLayer o (forgedKey F l) M' = some (F.signature.layers l) := by
  rcases path_meet hnode F l _ hroot with hnd | ⟨hlf, hpath⟩
  · exact Or.inr (Or.inl ⟨l, M', hM', x, hx, Or.inr hnd⟩)
  by_cases hE : forgedEnds h P F l x = Gen.otsPublicKey o l (forgedKey F l)
  swap
  · refine Or.inr (Or.inl ⟨l, M', hM', x, hx, Or.inl ⟨hE, ?_⟩⟩)
    rw [hlf, Gen.keyLeaf, id_bind, hleaf]
  by_cases hC : CpreEv h P o log F
  · exact Or.inr (Or.inr (Or.inl hC))
  have hend : ∀ i, Qrom.Xmss.Over.chainWalk (m := Id) h P l (forgedKey F l) i (x i).val
      (chainLength - 1 - (x i).val) ((F.signature.layers l).chainValues i) =
      o.chain l (forgedKey F l) i (chainLength - 1) := fun i ↦ by
    have := congrFun hE i
    rw [otsPublicKey_eq] at this
    exact this
  have hchain : ∀ i, (x i).val < chainLength - 1 →
      (F.signature.layers l).chainValues i = o.chain l (forgedKey F l) i (x i).val ∧
        Opened o log l (forgedKey F l) i (x i).val := fun i hi ↦ by
    by_contra hn
    exact hC ⟨l, M', hM', x, hx, i, hi, hend i, not_and_or.1 hn⟩
  have hz : ∀ i, (F.signature.layers l).chainValues i = o.chain l (forgedKey F l) i (x i).val := by
    intro i
    by_cases hi : (x i).val < chainLength - 1
    · exact (hchain i hi).1
    · have h3 : (x i).val = chainLength - 1 := by have := (x i).isLt; omega
      have := hend i
      rw [h3, Nat.sub_self] at this
      rw [h3]
      exact this
  -- A request opens the key; its codeword is the forged one.
  have hsum := Quantum.Xmss.Codeword.sum_eq_of_decode hx
  obtain ⟨i0, hi0⟩ := Quantum.Xmss.Codeword.exists_lt_of_sum hsum
  obtain ⟨-, r0, hr0, hk0, M0, hM0, ρ0, D0, xx0, henc0, hdec0, -⟩ := hchain i0 hi0
  have hle : ∀ i, xx0 i ≤ x i := by
    intro i
    by_cases hi : (x i).val < chainLength - 1
    · obtain ⟨-, r, hr, hk, M, hM, ρ, D, xx, henc, hdec, hxi⟩ := hchain i hi
      obtain rfl := requestMsg_unique hreuse hr0 hr (hk0.trans hk.symm) hM0 hM
      rw [henc0] at henc
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj henc)
      rw [hdec0] at hdec
      obtain rfl := Option.some.inj hdec
      exact hxi
    · change (xx0 i).val ≤ (x i).val
      have := (xx0 i).isLt
      omega
  have hxx : xx0 = x :=
    Quantum.Xmss.Codeword.eq_of_le (Quantum.Xmss.Codeword.sum_eq_of_decode hdec0) hsum hle
  have hdecx : Codeword.decode D0 = some x := hxx ▸ hdec0
  have hD : forgedDigest h P F l M' = D0 := Quantum.Xmss.Codeword.eq_of_decode hx hdecx
  by_cases hne : (M'.bytes, (F.signature.layers l).randomizer) = (M0.bytes, ρ0)
  swap
  · exact Or.inl ⟨l, M', hM', M0, ρ0, D0, honestMsg_of hr0 hk0 hM0, henc0, hne, hD⟩
  obtain ⟨hbytes, hρ⟩ := Prod.mk.inj hne
  obtain rfl := bytes_inj ((forgedMsg_layer hM').trans (requestMsg_layer hM0).symm) hbytes
  refine Or.inr (Or.inr (Or.inr ⟨r0, hr0, hk0, hM0, ?_⟩))
  have hcv : (fun i ↦ o.chain l (forgedKey F l) i (x i).val) =
      (F.signature.layers l).chainValues := funext fun i ↦ (hz i).symm
  rw [signLayer_of henc0 hdecx, requestMsg_layer hM0, ← hρ, ← hpath, hcv]

end Extract

open Extract

/-- **Extraction over any operations** whose leaf and node operations are the scheme's hashes. -/
theorem extract_ops (h : HashInput → HashOutput) (P : PublicParameter) (o : Ops Id)
    (hleaf : ∀ l e ends, o.leaf l e ends = Qrom.Xmss.Over.leafHash (m := Id) h P l e ends)
    (hnode : ∀ l k j a b, o.node l k j a b =
      Qrom.Xmss.Over.tweakableHash (m := Id) h P (.node l (k + 1) j) (nodePayload a b))
    (log : QueryLog SigningOracleSpec) (F : Forgery)
    (hlog : ∀ x ∈ log, x.2 = Gen.sign o x.1.leafIndex x.1.message)
    (hreuse : SigningTranscript.NoLeafIndexReused log)
    (hver : Qrom.Xmss.Over.verify (m := Id) h ⟨Gen.root o, P⟩ F.message F.signature = true)
    (hnew : ¬ SignerReturnedForgery SigningRequest.message log F.message F.signature) :
    EncEv h P o log F ∨ TcrEv h P o F ∨ CpreEv h P o log F := by
  obtain ⟨R, hb, ht⟩ := verify_true hver
  set idx := F.signature.leafIndex
  -- The top layer, on the forged bottom root `R`.
  have hMt : forgedMsg h P F topLayer = some (.inr R) := by
    simp only [forgedMsg, show topLayer ≠ bottomLayer by decide, ↓reduceIte]
    rw [hb, Option.map_some]
  obtain ⟨xt, hxt, hrt⟩ := layerRoot_some ht
  have hdiv1 : (keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight = 0 :=
    Nat.div_eq_of_lt (Quantum.Xmss.keyIndexOnLayer_lt idx topLayer)
  rcases layer_meet hnode hleaf hreuse F topLayer hMt (x := xt) hxt
      (hrt.trans (by
        change Gen.root o = Gen.treeNode o topLayer layerHeight
          ((keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight)
        rw [hdiv1]
        rfl)) with hev | hev | hev | ⟨r1, -, hk1, hm1, hs1⟩
  · exact Or.inl hev
  · exact Or.inr (Or.inl hev)
  · exact Or.inr (Or.inr hev)
  have hR : R = Gen.treeNode o bottomLayer layerHeight (keyIndexOnLayer idx topLayer).val := by
    have := requestMsg_top hm1
    rw [hk1] at this
    exact Sum.inr.inj this
  -- The bottom layer, on the forged message.
  have hMb : forgedMsg h P F bottomLayer = some (.inl F.message) := ite_eq_left rfl
  obtain ⟨xb, hxb, hrb⟩ := layerRoot_some hb
  have hdiv0 : (keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight =
      (keyIndexOnLayer idx topLayer).val := by
    simp [keyIndexOnLayer, bottomLayer, topLayer, layerHeight]
  rcases layer_meet hnode hleaf hreuse F bottomLayer hMb (x := xb) hxb
      (hrb.trans (by
        change R = Gen.treeNode o bottomLayer layerHeight
          ((keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight)
        rw [hR, hdiv0])) with hev | hev | hev | ⟨r0, hr0, hk0, hm0, hs0⟩
  · exact Or.inl hev
  · exact Or.inr (Or.inl hev)
  · exact Or.inr (Or.inr hev)
  -- Both layers are the signer's: the forgery is its answer to the request at `idx`.
  exfalso
  have hi0 : r0.1.leafIndex = idx := Fin.ext (by
    have := congrArg Fin.val hk0
    simpa [forgedKey, keyIndexOnLayer, bottomLayer] using this)
  have hm : r0.1.message = F.message := (Sum.inl.inj (requestMsg_bottom hm0)).symm
  have hsig : Gen.sign o r0.1.leafIndex r0.1.message = some F.signature := by
    rw [hi0, hm, sign_of hs0 (hR ▸ hs1), Quantum.Xmss.signature_eq_layers]
  exact hnew ⟨r0, hr0, hm, (hlog r0 hr0).trans hsig⟩

/-- **The deterministic extraction of the reduction**: a forgery that verifies against the root of
the ideal signer, for a transcript of its answers with no leaf index reused, and that the signer
did not return, yields an encoding, a tree or a chain event. -/
theorem extract (h : HashInput → HashOutput) (k : IdealKey) (log : QueryLog SigningOracleSpec)
    (F : Forgery)
    (hlog : ∀ x ∈ log, x.2 = Gen.sign (m := Id) (k.ops h) x.1.leafIndex x.1.message)
    (hreuse : SigningTranscript.NoLeafIndexReused log)
    (hver : Qrom.Xmss.Over.verify (m := Id) h ⟨Gen.root (k.ops h), k.1⟩ F.message F.signature =
      true)
    (hnew : ¬ Common.SufCma.SignerReturnedForgery SigningRequest.message log F.message
      F.signature) :
    EncEv h k.1 (k.ops h) log F ∨ TcrEv h k.1 (k.ops h) F ∨ CpreEv h k.1 (k.ops h) log F :=
  extract_ops h k.1 (k.ops h) (fun _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl) log F hlog hreuse hver hnew

end Quantum.StdModel.Xmss

end
