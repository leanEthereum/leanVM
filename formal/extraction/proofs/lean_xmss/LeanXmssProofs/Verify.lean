import LeanXmssProofs.Wots

/-!
# `tree.rs` and `scheme.rs`: a node, a layer's root, and `verify`

`tree::node` is the statement's hash at a tree node, `scheme::layer_root_unwatched` (the leaf of
`wots_leaf`, folded up the path by `keccak256::path_root`) its `Verification.layerRoot`,
`wots::layer_index` its `keyIndexOnLayer`, and `scheme::verify` its `Verification.verify`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation LeanXmss
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open lean_xmss
open Keccak256Proofs

namespace LeanXmssProofs

section
variable {π : KeccakState → KeccakState}

/-! ## The trees -/

/-- **`node`**: node `j` at `level` of a layer, the statement's hash at that node. -/
theorem node_spec (H : HasherSpec π) (pp : Array Std.U8 16#usize) (layer level : Std.Usize)
    (j : Std.U32) (ch : Array (Array Std.U8 16#usize) 2#usize) (l : Layer)
    (hl : layer.val = l.val) (hz : level.val < 2 ^ 23) :
    ∃ r, tree.node pp layer level j ch = ok r ∧
      toDigest r = Id.run (Verification.tweakableHash (inId π) (toDigest pp)
        (.node l level.val j.val) (bytes ((ch.val.map Array.val).flatten))) := by
  have hl1 : layer.val ≤ 1 := by have := l.isLt; simp only [layerCount] at this; omega
  have hc : (UScalar.cast .U32 level).val = level.val := by
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (by simp only [UScalarTy.numBits]; omega)
  obtain ⟨hi, hhi, hhiv⟩ := layer_hi_eq layer (UScalar.cast .U32 level) hl1 (by rw [hc]; exact hz)
  have htw := tweak_eq hash.TWEAK_NODE hi j (by simp [hash.TWEAK_NODE])
    (by rw [hhiv, hc]; omega)
  obtain ⟨d, hd, hdv⟩ := th_digests_spec H pp { t := hash.TWEAK_NODE, step := 0#u8, hi, lo := j }
    ch.to_slice (by simp [hash.TWEAK_NODE]) (by simp [Slice.length]; scalar_tac)
  refine ⟨d, ?_, ?_⟩
  · simp [tree.node, tree.node_tweak, lift, hhi, htw, core.array.Array.as_slice,
      rust_primitives.slice.array_as_slice, hd]
  · rw [hdv]
    simp only [Verification.tweakableHash, hashDomainFields]
    have hs : ch.to_slice.val = ch.val := by simp [Array.to_slice]
    rw [hs]
    congr 2
    exact toFields_eq _ _ _ _ _ (by simp [hash.TWEAK_NODE]) rfl
      (by rw [hhiv, hc, layerHi, hl]) rfl

/-- **`layer_root_unwatched`** is the statement's `layerRoot`. -/
theorem layer_root_spec (H : HasherSpec π) (pp : Array Std.U8 16#usize) (layer : Std.Usize)
    (e : Std.U32) (message : Slice Std.U8) (sig : scheme.LayerSignature) (l : Layer)
    (key : KeyIndex) (hl : layer.val = l.val) (he : e.val = key.val) :
    ∃ o, scheme.layer_root_unwatched pp layer e message sig = ok o ∧
      (ofOption o).map (fun p ↦ toDigest p.2) =
        Id.run (Verification.layerRoot (inId π) (toDigest pp) l key (bytes message.val)
          (toLayerSignature sig)) := by
  obtain ⟨o, ho, hov⟩ := wots_leaf_spec H pp layer e message sig.randomizer sig.chain_values l key
    hl he
  have hroot : ∀ O : Option Digest, Id.run (Verification.otsLeaf (inId π) (toDigest pp) l key
        (bytes message.val) (toDigest sig.randomizer) (fun i ↦ toDigest sig.chain_values.val[i.val]!)) = O →
      Id.run (Verification.layerRoot (inId π) (toDigest pp) l key (bytes message.val)
        (toLayerSignature sig)) = O.map (fun leaf => Id.run (Verification.treeFold (inId π)
          (toDigest pp) l key (toLayerSignature sig).authenticationPath layerHeight leaf)) := by
    intro O hO
    have hO' : Verification.otsLeaf (inId π) (toDigest pp) l key (bytes message.val)
        (toLayerSignature sig).randomizer (toLayerSignature sig).chainValues = (pure O : Id _) := hO
    simp only [Verification.layerRoot, hO']
    cases O <;> rfl
  generalize Id.run (Verification.otsLeaf (inId π) (toDigest pp) l key
        (bytes message.val) (toDigest sig.randomizer) (fun i ↦ toDigest sig.chain_values.val[i.val]!)) = O at hov hroot
  rw [hroot O rfl]
  match o, ho, hov with
  | .None, ho, hov =>
    refine ⟨.None, ?_, ?_⟩
    · simp [scheme.layer_root_unwatched, ho, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
    · cases O with
      | none => rfl
      | some v => simp [ofOption] at hov
  | .Some (x, leaf), ho, hov =>
    have hecast : (UScalar.cast .Usize e).val = e.val :=
      UScalar.cast_val_mod_pow_greater_numBits_eq .Usize e
        (by simp only [UScalarTy.numBits]; exact numBits_ge)
    obtain ⟨r, hr, hv⟩ := path_root_fold
      scheme.layer_root_unwatched.closure.Insts.CoreOpsFunctionFnTupleUsizeUsizeShared2ArrayArrayU8162ArrayU816
      (pp, layer)
      (fun z j p => Id.run (Verification.tweakableHash (inId π) (toDigest pp) (.node l (z + 1) j) p))
      leaf (UScalar.cast .Usize e) sig.path.to_slice
      (by
        intro z j ch hz hz' hj
        have hplen : sig.path.to_slice.length = 16 := by simp
        have hj32 : j.val < 2 ^ 32 := by
          have := e.hBounds
          simp only [UScalarTy.numBits] at this
          omega
        have hjc : (UScalar.cast .U32 j).val = j.val := by
          rw [UScalar.cast_val_eq]
          exact Nat.mod_eq_of_lt hj32
        obtain ⟨r, hr, hv⟩ := node_spec H pp layer z (UScalar.cast .U32 j) ch l hl (by omega)
        refine ⟨r, ?_, ?_⟩
        · simp [scheme.layer_root_unwatched.closure.Insts.CoreOpsFunctionFnTupleUsizeUsizeShared2ArrayArrayU8162ArrayU816.call,
            lift, hr]
        · have : z.val - 1 + 1 = z.val := by omega
          rw [hv, this, hjc])
      (by simp)
    refine ⟨.Some (x, r), ?_, ?_⟩
    · simp [scheme.layer_root_unwatched, ho, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, lift,
        core.array.Array.as_slice, rust_primitives.slice.array_as_slice, hr]
    · cases O with
      | none => simp [ofOption] at hov
      | some v =>
        simp only [ofOption, Option.map_some, Option.some.injEq] at hov
        simp only [ofOption, Option.map_some]
        refine congrArg some ?_
        have hplen : sig.path.to_slice.length = 16 := by simp
        rw [hv, hplen, hecast, he, hov]
        rw [foldId_congr _ _ _ (fun level =>
          if h : level < layerHeight then (toLayerSignature sig).authenticationPath ⟨level, h⟩ else 0)]
        · rw [foldId_eq_foldPath
            (fun z j => Verification.tweakableHash (inId π) (toDigest pp) (.node l (z + 1) j))]
          rfl
        · intro z hz
          have hz' : z < layerHeight := hz
          simp [hz', toLayerSignature]

/-! ## `verify` -/

/-- **`layer_index`**: the statement's key of a layer, the leaf index or its high half. -/
theorem layer_index_spec (leaf : Std.U32) (layer : Std.Usize) (l : Layer)
    (hl : layer.val = l.val) :
    ∃ r, wots.layer_index leaf layer = ok r ∧
      r.val = (keyIndexOnLayer (toLeafIndex leaf) l).val := by
  have hl1 : layer.val ≤ 1 := by have := l.isLt; simp only [layerCount] at this; omega
  have h : wots.layer_index leaf layer ⦃ r => r.val = leaf.val / 2 ^ (16 * layer.val) ⦄ := by
    unfold wots.layer_index
    simp only [internals.LAYER_HEIGHT, lift, Aeneas.Std.bind_ok]
    step*
    have hb := leaf.hBounds
    simp only [UScalarTy.numBits] at hb
    have hc : (UScalar.cast .U64 leaf).val = leaf.val := by
      rw [UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt (by simp only [UScalarTy.numBits]; omega)
    rw [UScalar.cast_val_eq, i2_post, hc, i1_post, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb)
  obtain ⟨r, hr, hv⟩ := WP.spec_imp_exists h
  refine ⟨r, hr, ?_⟩
  rw [hv, hl]
  rfl

/-- Two computations that may each give nothing, then a comparison: `verify`'s shape. -/
theorem two_layers (x : Option Digest) (f : Digest → Option Digest) (root : Digest) :
    Id.run (do
      let some b ← (pure x : Id (Option Digest)) | return false
      let some r ← (pure (f b) : Id (Option Digest)) | return false
      return decide (r = root)) =
      match x with
      | none => false
      | some b =>
        match f b with
        | none => false
        | some r => decide (r = root) := by
  cases x with
  | none => rfl
  | some b =>
    simp only [pure_bind]
    cases f b <;> rfl

/-- The statement's `verify`, by what its two layers recover. -/
theorem verify_run (PK : HashSig.PublicKey) (M : Message) (S : LeanXmss.Signature) :
    Id.run (Verification.verify (inId π) PK M S) =
      match Id.run (Verification.layerRoot (inId π) PK.parameter bottomLayer
        (keyIndexOnLayer S.leafIndex bottomLayer) (littleEndianBytes 32 M) (S.layers bottomLayer)) with
      | none => false
      | some b =>
        match Id.run (Verification.layerRoot (inId π) PK.parameter topLayer
          (keyIndexOnLayer S.leafIndex topLayer) (littleEndianBytes 16 b) (S.layers topLayer)) with
        | none => false
        | some root => decide (root = PK.root) :=
  two_layers _ (fun b => Id.run (Verification.layerRoot (inId π) PK.parameter topLayer
    (keyIndexOnLayer S.leafIndex topLayer) (littleEndianBytes 16 b) (S.layers topLayer))) _

/-- **`verify`**: the extracted Rust verifier returns, and returns the statement's verdict. -/
theorem verify_spec (H : HasherSpec π) (pk : scheme.LeanXmssPublicKey)
    (m : Array Std.U8 32#usize) (sig : scheme.LeanXmssSignature) :
    scheme.verify pk m sig = ok (Id.run (Verification.verify (inId π) (toPublicKey pk)
      (toMessage m) (toSignature sig))) := by
  obtain ⟨i, hi, hiv⟩ := layer_index_spec sig.leaf_index 0#usize bottomLayer rfl
  obtain ⟨i1, hi1, hi1v⟩ := layer_index_spec sig.leaf_index 1#usize topLayer rfl
  obtain ⟨o, ho, hov⟩ := layer_root_spec H pk.public_param 0#usize i m.to_slice sig.bottom
    bottomLayer (keyIndexOnLayer (toLeafIndex sig.leaf_index) bottomLayer) rfl hiv
  have htop := fun b : Array Std.U8 16#usize => layer_root_spec H pk.public_param 1#usize i1
    b.to_slice sig.top topLayer (keyIndexOnLayer (toLeafIndex sig.leaf_index) topLayer) rfl hi1v
  have hm : bytes m.to_slice.val = littleEndianBytes 32 (toMessage m) := by
    rw [littleEndianBytes_toMessage]; simp [Array.to_slice]
  have hb16 : ∀ b : Array Std.U8 16#usize,
      bytes b.to_slice.val = littleEndianBytes 16 (toDigest b) := by
    intro b; rw [littleEndianBytes_toDigest]; simp [Array.to_slice]
  rw [hm] at hov
  simp only [hb16] at htop
  rw [verify_run (toPublicKey pk) (toMessage m) (toSignature sig)]
  show _ = ok (match Id.run (Verification.layerRoot (inId π) (toDigest pk.public_param) bottomLayer
      (keyIndexOnLayer (toLeafIndex sig.leaf_index) bottomLayer) (littleEndianBytes 32 (toMessage m))
      (toLayerSignature sig.bottom)) with
    | none => false
    | some b =>
      match Id.run (Verification.layerRoot (inId π) (toDigest pk.public_param) topLayer
        (keyIndexOnLayer (toLeafIndex sig.leaf_index) topLayer) (littleEndianBytes 16 b)
        (toLayerSignature sig.top)) with
      | none => false
      | some root => decide (root = toDigest pk.merkle_root))
  rw [← hov]
  match o, ho with
  | .None, ho =>
    simp [scheme.verify, hi, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, ho,
      ofOption]
  | .Some (x, b), ho =>
    obtain ⟨o1, ho1, ho1v⟩ := htop b
    simp only [ofOption, Option.map_some]
    rw [← ho1v]
    match o1, ho1 with
    | .None, ho1 =>
      simp [scheme.verify, hi, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, ho,
        hi1, ho1, ofOption]
    | .Some (x1, root), ho1 =>
      have heq : decide (root = pk.merkle_root) = decide (toDigest root = toDigest pk.merkle_root) :=
        decide_eq_decide.mpr ⟨fun h => congrArg toDigest h, toDigest_inj⟩
      simp [scheme.verify, hi, core.array.Array.as_slice, rust_primitives.slice.array_as_slice, ho,
        hi1, ho1, ofOption, array_eq, heq]

end

end LeanXmssProofs
