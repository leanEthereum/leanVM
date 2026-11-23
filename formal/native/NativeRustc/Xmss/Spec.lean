module

public import NativeRustc.Xmss.Codeword

/-!
# The Rust functions are the statement's

Each function of `NativeRustc.Xmss.Model` on the bytes of the statement's values (a digest `d` as
`le16 d`, the public parameter `P` as `littleEndianBytes 16 P`) is the statement's function of
`LeanXmss.Verification` over Keccak-f[1600]: the address (`address_eq`), `th` (`th_eq`,
`th_tweak`, and its streaming form through the `Hasher`, `th_hasher`), a chain (`chain_eq`), the
message digest (`messageDigest_eq`, `messageDigest_hasher`), the one-time leaf (`wotsLeaf_eq`),
the fold up the path (`pathFold_eq`), a layer (`layerRoot_eq`) and verification (`verify_spec`).
-/

@[expose] public section

namespace NativeRustc.Xmss

open HashSig HashSig.OverPermutation LeanXmss LeanXmss.Verification LeanVM.Semantics
  LeanVM.Protocol.KeccakHash Native Native.Keccak NativeRustc.Keccak

/-! ## Bytes -/

/-- `(i as u128).to_le_bytes()`. -/
theorem u128Bytes_eq (i : Nat) (hi : i < 2 ^ 64) : u128Bytes i = le16 (BitVec.ofNat 128 i) := by
  have hlo : digestLo (BitVec.ofNat 128 i) = i.toUInt64 := by
    rw [digestLo, BitVec.toNat_ofNat, Nat.toUInt64_eq, Nat.mod_eq_of_lt (by omega)]
  have hhi : digestHi (BitVec.ofNat 128 i) = 0 := by
    rw [digestHi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt hi]
    rfl
  show _ = littleEndianBytes 16 (BitVec.ofNat 128 i)
  rw [littleEndianBytes_16, hlo, hhi]
  rfl

/-! ## The address and the tweakable hash -/

/-- `layer_hi` as a number. -/
theorem layerHi_toNat {layer : Nat} (hl : layer < 2) {field : UInt32} (hf : field.toNat < 2 ^ 23) :
    (layerHi layer field).toNat = field.toNat + 2 ^ 23 * layer := by
  rw [layerHi, UInt32.toNat_or]
  obtain _ | _ | _ := layer
  · simp
  · rw [show (Nat.toUInt32 (0 + 1) * top).toNat = 2 ^ 23 from rfl, lor_eq_add hf (dvd_refl _)]
    omega
  · omega

/-- The statement's `hi` fits in 24 bits. -/
theorem layerHi_lt (layer : Layer) {field : Nat} (hf : field < 2 ^ 23) :
    LeanXmss.layerHi layer field < 2 ^ 24 := by
  have : layer.val < 2 := layer.isLt
  unfold LeanXmss.layerHi
  omega

/-- `layer_hi` is the statement's. -/
theorem layerHi_eq (layer : Layer) {field : UInt32} (hf : field.toNat < 2 ^ 23) :
    (layerHi layer.val field).toNat = LeanXmss.layerHi layer field.toNat := by
  rw [layerHi_toNat layer.isLt hf, LeanXmss.layerHi]

/-- **`address` is `addressBytes`** of the fields as numbers. -/
theorem address_eq (tw : Tweak) (ht : tw.t.toNat < 32) (hs : tw.step.toNat < 8)
    (hh : tw.hi.toNat < 2 ^ 24) :
    address tw = addressBytes (tweakFields tw.t.toNat tw.step.toNat tw.hi.toNat tw.lo.toNat) := by
  have hb : (BitVec.ofNat 3 tw.step.toNat ++ BitVec.ofNat 5 tw.t.toNat).toNat =
      tw.t.toNat + 32 * tw.step.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hbyte : tw.t ||| tw.step <<< 5 = UInt8.ofNat (tw.t.toNat + 32 * tw.step.toNat) := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_or, UInt8.toNat_shiftLeft, UInt8.toNat_ofNat']
    simp only [UInt8.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), lor_eq_add (n := 5) (by omega) (Dvd.intro_left _ rfl)]
    omega
  have hhi : (u32Bytes tw.hi).take 3 = XmssVerifier.bytes tw.hi.toNat 3 := by
    rw [u32Bytes, show (4 : Nat) = 3 + 1 from rfl, XmssVerifier.bytes_add,
      List.take_left' (by simp [XmssVerifier.bytes])]
  have h1 : XmssVerifier.bytes (tw.t.toNat + 32 * tw.step.toNat) 1 =
      [UInt8.ofNat (tw.t.toNat + 32 * tw.step.toNat)] := by
    simp [XmssVerifier.bytes]
  simp only [addressBytes, tweakFields, XmssVerifier.littleEndianBytes_eq_bytes, hb,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt tw.lo.toNat_lt, Nat.mod_eq_of_lt hh, address, hhi, hbyte, u32Bytes, h1]
  rfl

/-- **`th` is the statement's `Th`** on the parameter's bytes, at the address of the fields. -/
theorem th_eq (P : PublicParameter) (tw : Tweak) (fields : TweakFields) (payload : HashInput)
    (ha : address tw = addressBytes fields) :
    th (littleEndianBytes 16 P) tw payload =
      le16 (Id.run (LeanXmss.th (m := Id) keccakF1600 P fields payload)) := by
  rw [LeanXmss.th, Id.run_bind, Id.run_pure, truncate_keccakHash, le16_ofWords, th, hashBytes, ha,
    take16_digestBytes]
  rfl

/-- `th` at a tweak whose fields are the numbers `tag`, `step`, `hi`, `lo`. -/
theorem th_tweak (P : PublicParameter) (tw : Tweak) (payload : HashInput) {tag step hi lo : Nat}
    (ht : tw.t.toNat = tag) (htag : tag < 32) (hs : tw.step.toNat = step) (hstep : step < 8)
    (hh : tw.hi.toNat = hi) (hhi : hi < 2 ^ 24) (hl : tw.lo.toNat = lo) :
    th (littleEndianBytes 16 P) tw payload =
      le16 (Id.run (LeanXmss.th (m := Id) keccakF1600 P (tweakFields tag step hi lo) payload)) := by
  subst ht hs hh hl
  exact th_eq P tw _ payload (address_eq tw htag hstep hhi)

/-- **`th` through the `Hasher`**: new, updated with `P`, the address and the payload,
finalized, truncated. -/
theorem th_hasher (pp : List UInt8) (tw : Tweak) (payload : List UInt8) :
    th pp tw payload = (finalize (update (update (update new pp) (address tw)) payload)).take 16 := by
  rw [finalize_eq (holds_update (holds_update (holds_update holds_new pp) _) payload), th, hashBytes,
    List.nil_append]

/-- **`message_digest` through the `Hasher`**: new, updated with `P`, the address, the message
and the randomizer. -/
theorem messageDigest_hasher (pp : List UInt8) (layer : Nat) (e : UInt32)
    (randomizer message : List UInt8) :
    messageDigest pp layer e randomizer message =
      (finalize (update (update (update (update new pp)
        (address (tweak 12 (layerHi layer 0) e))) message) randomizer)).take 16 := by
  rw [finalize_eq (holds_update (holds_update (holds_update (holds_update holds_new pp) _) _) _),
    messageDigest, hashBytes, List.nil_append]

/-! ## WOTS+C -/

/-- **`chain` is the statement's chain walk.** -/
theorem chain_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) (i : ChainIndex)
    {e : UInt32} (he : e.toNat = key.val) (start : Nat) :
    ∀ steps, start + steps ≤ 3 → ∀ v : Digest,
      chain (littleEndianBytes 16 P) layer.val e i.val start steps (le16 v) =
        le16 (Id.run (chainWalk (m := Id) keccakF1600 P layer key i start steps v))
  | 0, _, _ => rfl
  | steps + 1, hs, v => by
    have ih := chain_eq P layer key i he start steps (by omega) v
    rw [chain, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, ← chain, ih]
    unfold chainWalk
    rw [walkChain, Id.run_bind, dite_eq_left (by unfold chainLength winternitzBits; omega)]
    have hi : i.val < 58 := i.isLt
    have hstep : (start + 1 * steps).toUInt8.toNat = start + steps := by
      rw [Nat.toUInt8_eq, UInt8.toNat_ofNat']
      omega
    rw [u128Bytes_eq _ (by omega), th_tweak P _ _ (tag := 1) rfl (by decide) hstep (by omega)
      (layerHi_eq layer (by decide)) (layerHi_lt layer (by decide)) he]
    rfl

/-- **`message_digest` is the statement's.** -/
theorem messageDigest_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) {e : UInt32}
    (he : e.toNat = key.val) (R : Randomizer) (message : HashInput) :
    messageDigest (littleEndianBytes 16 P) layer.val e (le16 R) message =
      le16 (Id.run (Verification.messageDigest (m := Id) keccakF1600 P layer key message R)) := by
  rw [messageDigest, List.append_assoc _ message, ← th,
    th_tweak P _ _ (tag := 12) (step := 0) rfl (by decide) rfl (by decide)
      (layerHi_eq layer (by decide)) (layerHi_lt layer (by decide)) he]
  rfl

/-- **`wots_leaf`'s leaf is the statement's one-time leaf.** -/
theorem wotsLeaf_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) {e : UInt32}
    (he : e.toNat = key.val) (message : HashInput) (R : Randomizer) (values : ChainIndex → Digest) :
    (wotsLeaf (littleEndianBytes 16 P) layer.val e message (le16 R)
        (List.ofFn fun i ↦ le16 (values i))).map Prod.snd =
      (Id.run (otsLeaf (m := Id) keccakF1600 P layer key message R values)).map le16 := by
  unfold wotsLeaf otsLeaf
  rw [messageDigest_eq P layer key he R message, Id.run_bind]
  generalize Id.run (Verification.messageDigest (m := Id) keccakF1600 P layer key message R) = D
  rw [codeword_eq]
  unfold Codeword.decode
  by_cases hc : Codeword.Valid D
  · rw [ite_eq_left hc, ite_eq_left hc]
    have hends : ((List.range 58).map fun i ↦ chain (littleEndianBytes 16 P) layer.val e i
        ((digits D.toNat).getD i 0).toNat (3 - ((digits D.toNat).getD i 0).toNat)
        ((List.ofFn fun i ↦ le16 (values i)).getD i [])) =
        List.ofFn fun i : ChainIndex ↦ le16 (Id.run (recoverChain (m := Id) keccakF1600 P layer
          key i (digestDigits D i) (values i))) := by
      apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn]; rfl)
      intro i h1 h2
      have hi : i < 58 := by simpa using h1
      rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      have hv : (List.ofFn fun i ↦ le16 (values i)).getD i [] = le16 (values ⟨i, hi⟩) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi),
          Option.getD_some, List.getElem_ofFn]
      have hd3 : (digestDigits (n := chainCount) D ⟨i, hi⟩).val ≤ 3 :=
        Nat.le_of_lt_succ (digestDigits (n := chainCount) D ⟨i, hi⟩).isLt
      rw [hv, getD_digits D hi]
      exact chain_eq P layer key ⟨i, hi⟩ he _ _ (by omega) _
    dsimp only
    rw [hends, Id.run_bind, XmssVerifier.sequenceFin_id, Id.run_bind, Id.run_pure, Option.map_some,
      Option.map_some]
    unfold leafHash wotsLeafHash
    rw [th_tweak P _ _ (tag := 2) (step := 0) rfl (by decide) rfl (by decide)
      (layerHi_eq layer (by decide)) (layerHi_lt layer (by decide)) he, flatten_ofFn]
    rfl
  · rw [ite_eq_right hc, ite_eq_right hc]
    rfl

/-! ## The tree -/

/-- The node's side: bit `j` of the key. -/
theorem and_one_iff {key j : Nat} : key >>> j &&& 1 = 0 ↔ key.testBit j = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
    decide_eq_false_iff_not]
  omega

/-- **`path_fold` with `node` is the statement's fold up the tree.** -/
theorem pathFold_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) (leaf : Digest) :
    pathFold (le16 leaf) key.val (List.ofFn fun j ↦ le16 (path j))
        (fun level j children ↦ node (littleEndianBytes 16 P) layer.val level j.toUInt32 children) =
      le16 (Id.run (treeFold (m := Id) keccakF1600 P layer key path layerHeight leaf)) := by
  have hk : key.val < 2 ^ 32 := key.isLt
  suffices key' : ∀ j, j ≤ 16 →
      (List.range j).foldl (fun current z ↦
        node (littleEndianBytes 16 P) layer.val (z + 1) (key.val >>> (z + 1)).toUInt32
          (if key.val >>> z &&& 1 = 0
            then current ++ (List.ofFn fun j ↦ le16 (path j)).getD z []
            else (List.ofFn fun j ↦ le16 (path j)).getD z [] ++ current))
        (le16 leaf) =
      le16 (Id.run (treeFold (m := Id) keccakF1600 P layer key path j leaf)) by
    rw [pathFold, List.length_ofFn]
    exact key' 16 le_rfl
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
    unfold treeFold
    rw [foldPath, Id.run_bind]
    have hjh : j < layerHeight := by unfold layerHeight; omega
    have hsib : (List.ofFn fun j ↦ le16 (path j)).getD j [] = le16 (path ⟨j, hjh⟩) := by
      simp [List.getD_eq_getElem?_getD, hjh]
    rw [hsib, dite_eq_left hjh]
    have hj1 : (j + 1).toUInt32.toNat = j + 1 := by
      rw [Nat.toUInt32_eq, UInt32.toNat_ofNat']
      omega
    have hlo : (key.val >>> (j + 1)).toUInt32.toNat = key.val / 2 ^ (j + 1) := by
      rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hk)]
    unfold node
    rw [th_tweak P _ _ (tag := 3) (step := 0) rfl (by decide) rfl (by decide)
      ((layerHi_eq layer (by omega)).trans (by rw [hj1])) (layerHi_lt layer (by omega)) hlo]
    cases hb : key.val.testBit j
    · rw [ite_eq_left (and_one_iff.mpr hb), ite_eq_right Bool.false_ne_true]
      rfl
    · rw [ite_eq_right (fun h ↦ absurd (and_one_iff.mp h) (by rw [hb]; decide)),
        ite_eq_left (rfl : true = true)]
      rfl

/-! ## A layer and verification -/

/-- A layer's signature as the Rust code holds it: the randomizer, chain values and path nodes as
their bytes. -/
def layerBytes (ls : LeanXmss.LayerSignature) : LayerSignature :=
  ⟨le16 ls.randomizer, List.ofFn fun i ↦ le16 (ls.chainValues i),
    List.ofFn fun j ↦ le16 (ls.authenticationPath j)⟩

/-- **`layer_root`'s root is the statement's.** -/
theorem layerRoot_eq (P : PublicParameter) (layer : Layer) (key : KeyIndex) {e : UInt32}
    (he : e.toNat = key.val) (message : HashInput) (ls : LeanXmss.LayerSignature) :
    (layerRoot (littleEndianBytes 16 P) layer.val e message (layerBytes ls)).map Prod.snd =
      (Id.run (Verification.layerRoot (m := Id) keccakF1600 P layer key message ls)).map le16 := by
  have hw := wotsLeaf_eq P layer key he message ls.randomizer ls.chainValues
  unfold layerRoot Verification.layerRoot
  rw [Id.run_bind]
  simp only [layerBytes]
  revert hw
  generalize wotsLeaf (littleEndianBytes 16 P) layer.val e message (le16 ls.randomizer)
    (List.ofFn fun i ↦ le16 (ls.chainValues i)) = r
  generalize Id.run (otsLeaf (m := Id) keccakF1600 P layer key message ls.randomizer
    ls.chainValues) = s
  intro hw
  cases r with
  | none =>
    cases s with
    | none => rfl
    | some _ => simp at hw
  | some p =>
    obtain ⟨x, leaf⟩ := p
    cases s with
    | none => simp at hw
    | some leafS =>
      simp only [Option.map_some, Option.some.injEq] at hw
      subst hw
      rw [Id.run_bind, Id.run_pure, Option.map_some, Option.map_some, he, pathFold_eq]

/-- The key of the leaf index on a layer. -/
theorem layerIndex_toNat (leafIndex : LeafIndex) {li : UInt32} (hli : li.toNat = leafIndex.val)
    (layer : Layer) :
    (layerIndex li layer.val).toNat = (keyIndexOnLayer leafIndex layer).val := by
  have h : leafIndex.val < 2 ^ 32 := leafIndex.isLt
  have hl : layer.val < 2 := layer.isLt
  rw [show (keyIndexOnLayer leafIndex layer).val = leafIndex.val / 2 ^ (16 * layer.val) from rfl,
    layerIndex, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', UInt32.toNat_toUInt64, hli, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : layer.val * 16 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : layer.val * 16 < 64),
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)), mul_comm]

/-- **`verify` is `LeanXmss.verifyWithKeccak`** on the bytes of the key, the message and the
signature. -/
theorem verify_spec (pk : HashSig.PublicKey) (msg : Message) (sig : LeanXmss.Signature)
    {li : UInt32}
    (hli : li.toNat = sig.leafIndex.val) :
    verify ⟨le16 pk.root, littleEndianBytes 16 pk.parameter⟩ (littleEndianBytes 32 msg)
        ⟨li, layerBytes (sig.layers bottomLayer), layerBytes (sig.layers topLayer)⟩ =
      verifyWithKeccak pk msg sig := by
  have h0 := layerRoot_eq pk.parameter bottomLayer _
    (layerIndex_toNat sig.leafIndex hli bottomLayer) (littleEndianBytes 32 msg)
    (sig.layers bottomLayer)
  change Option.map Prod.snd (layerRoot (littleEndianBytes 16 pk.parameter) 0 (layerIndex li 0)
    (littleEndianBytes 32 msg) (layerBytes (sig.layers bottomLayer))) = _ at h0
  unfold verify verifyWithKeccak Verification.verify
  dsimp only
  rw [Id.run_bind]
  revert h0
  generalize layerRoot (littleEndianBytes 16 pk.parameter) 0 (layerIndex li 0)
    (littleEndianBytes 32 msg) (layerBytes (sig.layers bottomLayer)) = r
  generalize Id.run (Verification.layerRoot (m := Id) keccakF1600 pk.parameter bottomLayer
    (keyIndexOnLayer sig.leafIndex bottomLayer) (littleEndianBytes 32 msg)
    (sig.layers bottomLayer)) = s
  intro h0
  cases r with
  | none =>
    cases s with
    | none => rfl
    | some _ => simp at h0
  | some p =>
    obtain ⟨x, bottomRoot⟩ := p
    cases s with
    | none => simp at h0
    | some bottomRootS =>
      simp only [Option.map_some, Option.some.injEq] at h0
      subst h0
      have h1 := layerRoot_eq pk.parameter topLayer _
        (layerIndex_toNat sig.leafIndex hli topLayer) (littleEndianBytes 16 bottomRootS)
        (sig.layers topLayer)
      change Option.map Prod.snd (layerRoot (littleEndianBytes 16 pk.parameter) 1
        (layerIndex li 1) (littleEndianBytes 16 bottomRootS) (layerBytes (sig.layers topLayer))) =
        _ at h1
      dsimp only
      rw [Id.run_bind, show le16 bottomRootS = littleEndianBytes 16 bottomRootS from rfl]
      revert h1
      generalize layerRoot (littleEndianBytes 16 pk.parameter) 1 (layerIndex li 1)
        (littleEndianBytes 16 bottomRootS) (layerBytes (sig.layers topLayer)) = r
      generalize Id.run (Verification.layerRoot (m := Id) keccakF1600 pk.parameter topLayer
        (keyIndexOnLayer sig.leafIndex topLayer) (littleEndianBytes 16 bottomRootS)
        (sig.layers topLayer)) = s
      intro h1
      cases r with
      | none =>
        cases s with
        | none => rfl
        | some _ => simp at h1
      | some p =>
        obtain ⟨y, root⟩ := p
        cases s with
        | none => simp at h1
        | some rootS =>
          simp only [Option.map_some, Option.some.injEq] at h1
          subst h1
          rw [Id.run_pure, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, le16_inj]

end NativeRustc.Xmss
