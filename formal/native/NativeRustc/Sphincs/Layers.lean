module

public import NativeRustc.Sphincs.Spec

/-!
# `verify` is leanSPHINCS verification

On a signature whose bytes are the statement signature's (`randomizer`, FORS openings, each layer's
counter, chain values and path: the hypotheses of `verify_spec`), a layer of `verify`'s loop is the
statement's `layerRoot` (`layersFrom_cons`), the loop is the statement's three layers
(`layersFrom_three`), and `verify` is `Sphincs.verifyWithKeccak` (`verify_spec`).
-/

@[expose] public section

namespace NativeRustc.Sphincs

open _root_.Sphincs HashSig HashSig.OverPermutation LeanVM.Protocol.KeccakHash NativeRustc.Keccak
  Native.Keccak

/-- What a parsed signature holds for layer `l`: the statement's counter, chain values and path, as
bytes. -/
def LayerHolds (sig : _root_.Sphincs.Signature) (sigB : Signature) (l : Layer) : Prop :=
  (sigB.layers.getD l.val ⟨0, []⟩).counter.toNat = (sig.layers l).counter.toNat ∧
    (sigB.layers.getD l.val ⟨0, []⟩).wots = List.ofFn (fun i ↦ le16 ((sig.layers l).chainValues i)) ∧
    sigB.path l.val = List.ofFn (fun j ↦ le16 ((sig.layers l).authenticationPath j))

theorem layerHeight_le (l : Layer) : layerHeight l ≤ 10 := by
  unfold layerHeight; split <;> omega

/-- **A layer of `verify`'s loop** is the statement's `layerRoot`, then the rest of the loop. -/
theorem layersFrom_cons (seed : PublicParameter) (sig : _root_.Sphincs.Signature) (sigB : Signature)
    {idx : UInt64} {index : Index} (h : idx.toNat = index.val) (l : Layer)
    (hl : LayerHolds sig sigB l) (rest : List Nat) (d : Digest) :
    layersFrom (littleEndianBytes 16 seed) idx sigB (l.val :: rest) (le16 d) =
      (Native.SphincsVerifier.layerRoot seed index sig l d).bind fun r ↦
        layersFrom (littleEndianBytes 16 seed) idx sigB rest (le16 r) := by
  obtain ⟨hc, hw, hp⟩ := hl
  have hwl := wotsLeaf_eq seed l (treeOfIndex l index) (leafOfIndex l index) (ofIndex_layer _ _)
    (ofIndex_tree l h) (ofIndex_leaf l h) d hc (sig.layers l).chainValues
  rw [← hw] at hwl
  rw [layersFrom]
  unfold Native.SphincsVerifier.layerRoot
  revert hwl
  generalize wotsLeaf (littleEndianBytes 16 seed) (OtsKey.ofIndex l.val idx) (le16 d)
    (sigB.layers.getD l.val ⟨0, []⟩).counter (sigB.layers.getD l.val ⟨0, []⟩).wots = r
  generalize Id.run (Verification.otsLeaf (m := Id) LeanVM.Semantics.keccakF1600 seed l
    (treeOfIndex l index) (leafOfIndex l index) d (sig.layers l).counter
    (sig.layers l).chainValues) = s
  intro hwl
  cases r with
  | none =>
    cases s with
    | none => rfl
    | some _ => simp at hwl
  | some p =>
    obtain ⟨x, leaf⟩ := p
    cases s with
    | none => simp at hwl
    | some leafS =>
      simp only [Option.map_some, Option.some.injEq] at hwl
      subst hwl
      rw [Option.map_some, Option.bind_some, hp]
      dsimp only
      rw [treeFold_eq seed l (treeOfIndex l index) (leafOfIndex l index) (ofIndex_layer _ _)
          (ofIndex_tree l h) (ofIndex_leaf l h) (layerHeight_le l)]
      rfl

/-- **`verify`'s loop is the statement's three layers.** -/
theorem layersFrom_three (seed : PublicParameter) (sig : _root_.Sphincs.Signature)
    (sigB : Signature) {idx : UInt64} {index : Index} (h : idx.toNat = index.val)
    (hL : ∀ l, LayerHolds sig sigB l) (d : Digest) :
    layersFrom (littleEndianBytes 16 seed) idx sigB [0, 1, 2] (le16 d) =
      (((Native.SphincsVerifier.layerRoot seed index sig 0 d).bind
        (Native.SphincsVerifier.layerRoot seed index sig 1)).bind
        (Native.SphincsVerifier.layerRoot seed index sig 2)).map le16 := by
  show layersFrom (littleEndianBytes 16 seed) idx sigB
    [(0 : Layer).val, (1 : Layer).val, (2 : Layer).val] (le16 d) = _
  rw [layersFrom_cons seed sig sigB h 0 (hL 0)]
  cases Native.SphincsVerifier.layerRoot seed index sig 0 d with
  | none => rfl
  | some r0 =>
    rw [Option.bind_some, Option.bind_some, layersFrom_cons seed sig sigB h 1 (hL 1)]
    cases Native.SphincsVerifier.layerRoot seed index sig 1 r0 with
    | none => rfl
    | some r1 =>
      rw [Option.bind_some, Option.bind_some, layersFrom_cons seed sig sigB h 2 (hL 2)]
      cases Native.SphincsVerifier.layerRoot seed index sig 2 r1 with
      | none => rfl
      | some r2 => rfl

/-- **`verify` is `Sphincs.verifyWithKeccak`** on the bytes of the key and the message and a
signature whose bytes are the statement signature's. -/
theorem verify_spec (pk : _root_.Sphincs.PublicKey) (msg : Message) (sig : _root_.Sphincs.Signature)
    (sigB : Signature) (hR : sigB.randomizer = le16 sig.randomizer)
    (hF : sigB.fors = List.ofFn fun c ↦
      ⟨le16 (sig.forsOpening c).secret, List.ofFn fun z ↦ le16 ((sig.forsOpening c).path z)⟩)
    (hL : ∀ l, LayerHolds sig sigB l) :
    verify ⟨littleEndianBytes 16 pk.publicSeed, le16 pk.root⟩ (littleEndianBytes 32 msg) sigB =
      verifyWithKeccak pk msg sig := by
  rw [Native.SphincsVerifier.verifyWithKeccak_eq]
  have hi := digestFields_index pk sig.randomizer msg
  have hlv := digestFields_leaves pk sig.randomizer msg
  unfold verify messageDigest
  dsimp only
  rw [hR, hlv, hF, forsRecover_eq pk.publicSeed hi, layersFrom_three pk.publicSeed sig sigB hi hL]
  generalize (((Native.SphincsVerifier.layerRoot pk.publicSeed _ sig 0 _).bind
    (Native.SphincsVerifier.layerRoot pk.publicSeed _ sig 1)).bind
    (Native.SphincsVerifier.layerRoot pk.publicSeed _ sig 2)) = o
  cases o with
  | none => rfl
  | some r =>
    rw [Option.map_some]
    exact Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, decide_eq_true_iff, le16_inj])

end NativeRustc.Sphincs
