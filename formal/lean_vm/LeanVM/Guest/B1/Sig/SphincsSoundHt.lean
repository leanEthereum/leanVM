/-
  LeanVM.Guest.B1.Sig.SphincsSoundHt

  A hypertree layer of `verify_sig_lean_sphincs` (`sp_layer`, `lean_ethereum.py:3926-3937` at
  leanVM main 40f877dc) against the statement: its counter and encoding, the call of `sp_wots` and the
  path reach the statement's layer root (`LayerReaches`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundWots
public import LeanVM.Guest.B1.Sig.SphincsSoundPath
public import LeanVM.Guest.B1.Sig.SphincsSoundBlocks
public import LeanVM.Guest.B1.Sig.SphincsSoundDigest
public import LeanVM.Guest.B1.Sig.SphincsBridge

/-!
# A layer, sound

The statement's side:

* `otsLeaf_of_valid`: a counter whose encoding's digits reach the target sum recovers
  `wotsLeafOf`;
* `pathAdr_eq`, `htTreeFold_cells`: a path of the hypertree over cells, at the tree's first address
  cell, is `SphincsSoundPath`'s `pFold` of `pNodeE` (`addressedHash_node`);
* `layerReaches_of_cells`: the encoding's digest, `sp_wots`'s leaf and the fold reach the root.

The guest's side, layer `l` at `sLayerBase l`:

* `sLayerPre_sound`: the counter read is a number `N < 2^32` (`sFromMarks_sound`), `enc_at = a1 +
  WOTS_ENC` the encoding's address cell (`adrsCell1_add_type`), and the encoding `KECCAK` of 68
  bytes the statement's encoding hash of the message and the counter `beWordAt 0 N`
  (`addressedHash_encodingDigest`: the guest reads `BE_32(c)` lowest byte first, so its counter is
  `c`'s byte reversal);
* `sLayerPath_sound`, `sPathSib_eq`, `sPathPos_layer`: the path, its siblings at `sPathKid l j`
  (`SphincsSig`'s positions);
* `layer_sound`: the layer reaches the statement's root, the signature `sphincsSigOf σ V`'s layer.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)
open HashSig HashSig.OverPermutation
open Sphincs Sphincs.Verification

@[expose] public section

/-! ## The statement's layer over cells -/

/-- **A counter whose encoding is a codeword recovers the leaf of its digits.** -/
theorem otsLeaf_of_valid {P : PublicParameter} {layer : Layer} {tree : TreeIndex}
    {lf : TreeLeafIndex} {msg : HashSig.Digest} {ctr : EncodingCounter}
    {values : ChainIndex → HashSig.Digest} {d : HashSig.Digest}
    (hd : Id.run (tweakableHash (m := Id) keccakF1600 P (.encoding layer tree lf)
      (littleEndianBytes 16 msg ++ Sphincs.bigEndianBytes 4 ctr)) = d)
    (hv : TargetSum.Valid (TargetSum.base2bDigits d)) :
    Id.run (otsLeaf (m := Id) keccakF1600 P layer tree lf msg ctr values) =
      some (wotsLeafOf P layer tree lf d values) := by
  unfold otsLeaf encode
  simp only [Id.run_bind, Id.run_pure] at hd ⊢
  have hdec : TargetSum.decodeDigest d = some (TargetSum.base2bDigits d) := ite_eq_left hv
  rw [hd, hdec]
  rfl

/-- A path node's address cell is the statement's (type `TREE`, no key pair). -/
theorem pathAdr_eq {h i : Nat} (hh : h < 256) (hi : i < 2 ^ 16) : pathAdr h i = adrsCell1 2 0 h i := by
  have ha : a1Hi h i < 2 ^ 64 := by unfold a1Hi; omega
  rw [pathAdr, word_eq128 (by norm_num), adrsCell1_eq]
  congr 1
  simp only [adrsNat1, beWordAt, a1Hi]
  omega

/-- **The statement's path over cells**: folding a cell's value up `k ≤ 16` levels with siblings
that are cells' values is `pFold` of `pNodeE` at the tree's first address cell. -/
theorem htTreeFold_cells (pp : E) (layer : Layer) (tree : TreeIndex) (lf : TreeLeafIndex)
    (sib : Nat → E) (path : Nat → HashSig.Digest) (v : E) :
    ∀ k, k ≤ 16 → (∀ j < k, path j = cellVal (sib j)) →
      Id.run (treeFold (m := Id) keccakF1600 (cellVal pp) layer tree lf path k (cellVal v)) =
        cellVal (pFold (pNodeE pp (adrsCell0 layer.val tree.val) lf.val sib) k v)
  | 0, _, _ => rfl
  | k + 1, hk, hp => by
      have ih := htTreeFold_cells pp layer tree lf sib path v k (by omega) fun j hj => hp j (by omega)
      have he : lf.val >>> (k + 1) < 2 ^ 16 := by
        have := lf.isLt
        rw [Nat.shiftRight_eq_div_pow]
        exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le this (by decide))
      unfold treeFold at ih ⊢
      simp only [foldPath, Id.run_bind] at ih ⊢
      rw [ih, hp k (by omega), pFold, pNodeE, pathAdr_eq (by omega) he, Nat.shiftRight_eq_div_pow]
      by_cases hb : lf.val.testBit k
      · simp only [hb, ↓reduceIte, mPair]
        rw [nodePayload_cellVal, tweakableHash_sphincsCells]
        rfl
      · simp only [hb, ↓reduceIte, mPair, Bool.false_eq_true]
        rw [nodePayload_cellVal, tweakableHash_sphincsCells]
        rfl

/-- **A layer over cells reaches its root**: the encoding's digest is the statement's of the
message and the layer's counter, the leaf is the one the layer's chain values recover at its
digits (which reach the target sum), and the root is the statement's fold of the leaf. -/
theorem layerReaches_of_cells {P : PublicParameter} {idx : Index} {sig : Sphincs.Signature}
    {l : Layer} {msg root : HashSig.Digest} {enc leaf : HashSig.Digest}
    (henc : Id.run (tweakableHash (m := Id) keccakF1600 P
      (.encoding l (treeOfIndex l idx) (leafOfIndex l idx))
      (littleEndianBytes 16 msg ++ Sphincs.bigEndianBytes 4 (sig.layers l).counter)) = enc)
    (hv : TargetSum.Valid (TargetSum.base2bDigits enc))
    (hleaf : leaf = wotsLeafOf P l (treeOfIndex l idx) (leafOfIndex l idx) enc
      (sig.layers l).chainValues)
    (hroot : Id.run (treeFold (m := Id) keccakF1600 P l (treeOfIndex l idx) (leafOfIndex l idx)
      (layerPath sig l) (layerHeight l) leaf) = root) :
    LayerReaches P idx sig l msg root := by
  rw [layerReaches_iff]
  exact ⟨leaf, by rw [otsLeaf_of_valid henc hv, hleaf], hroot⟩

/-! ## The counter's bytes -/

/-- A 32-bit word's bytes reversed, digit by digit. -/
theorem beWordAt_zero_digits {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (hd : d < 256) :
    beWordAt 0 (a + 256 * b + 65536 * c + 16777216 * d) = d + 256 * c + 65536 * b + 16777216 * a := by
  simp only [beWordAt, Nat.mul_zero, pow_zero, one_mul, Nat.reducePow]
  omega

/-- A 32-bit word's bytes reversed twice. -/
theorem beWordAt_zero_beWordAt_zero {N : Nat} (h : N < 2 ^ 32) : beWordAt 0 (beWordAt 0 N) = N := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ : ∃ a b c d, a < 256 ∧ b < 256 ∧ c < 256 ∧ d < 256 ∧
      N = a + 256 * b + 65536 * c + 16777216 * d :=
    ⟨N % 256, N / 256 % 256, N / 65536 % 256, N / 16777216, by omega, by omega, by omega, by omega,
      by omega⟩
  rw [beWordAt_zero_digits ha hb hc hd, beWordAt_zero_digits hd hc hb ha]

/-- The layer's counter, as the signature reads it off its cell. -/
theorem counter_of_cell {N : Nat} (h : N < 2 ^ 32) :
    (BitVec.ofNat 32 (beWordAt 0 (cellNat (eOfNat N))) : EncodingCounter).toNat = beWordAt 0 N := by
  rw [cellNat_eOfNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (beWordAt_zero_lt N)]

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The layer's counter and encoding -/

/-- **A layer before its call, over cells**: the counter read is a number `N < 2^32` at
`sCtrOf l`, `enc_at` is `a1 + WOTS_ENC`, and the encoding digest at `sEncOf l` is the hash of the 68
bytes of `[P, a0, enc_at, signed, counter]`. -/
theorem sLayerPre_cells {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ}
    (hbb : ByteBits L.read (σ (.n 1))) (hp : PadOK σ sPad) {l : Nat} {a0 a1 signed : V}
    (h : AtomsHold L.read σ (sLayerPre l a0 a1 signed)) :
    ∃ N < 2 ^ 32, σ (sCtrOf l) = eOfNat N ∧
      σ (sEncOf l) = (digestHalves (keccak256 ((cellsBytes [σ sPP, σ a0,
        σ a1 + lit (7 * 2 ^ 24), σ signed, eOfNat N]).take 68))).1 := by
  have hC : AtomsHold L.read σ (sLayerCtr l).1 := h.left.left.right
  obtain ⟨N, hN, hlt⟩ := sFromMarks_sound hκ hbb (b := sLayerBase l) (n := 4) (x := sLayerBase l + 4)
    (by norm_num) (by norm_num) hC
  have hlt' : N < 2 ^ 32 := by simpa using hlt
  have hctr : σ (sLayerCtr l).2.2 = eOfNat N := hN
  refine ⟨N, hlt', by rw [← (sLayerCtr_out l).1]; exact hctr, ?_⟩
  have hA : AtomsHold L.read σ [cst (sLayerCtr l).2.1 (lit (7 * 2 ^ 24)),
      addS (.n ((sLayerCtr l).2.1 + 1)) a1 (.n (sLayerCtr l).2.1)] := h.left.right
  have c0 : σ (.n (sLayerCtr l).2.1) = lit (7 * 2 ^ 24) := hA.atom (a := .const _ _) (by simp [cst])
  have c1 : σ (.n ((sLayerCtr l).2.1 + 1)) = σ a1 + σ (.n (sLayerCtr l).2.1) :=
    hA.atom (a := .add _ _ _) (by simp [addS])
  have hK : AtomsHold L.read σ (sLayerK l a0 signed).1 := h.right
  have hrev : eOfNat N = eOfNat (beWordAt 0 (beWordAt 0 N)) := by
    rw [beWordAt_zero_beWordAt_zero hlt']
  have hz := cellsBytes_counterCell_zero [σ sPP, σ a0, σ (.n ((sLayerCtr l).2.1 + 1)), σ signed]
    (beWordAt 0 N)
  rw [← hrev] at hz
  have k := kMsg_sound (cells := [.cell sPP, .cell a0, .cell (.n ((sLayerCtr l).2.1 + 1)), .cell signed,
      .cell (sLayerCtr l).2.2]) (len := 68) (tailRun := false) (out := none) hp
    (fun h => absurd h (by simp)) hK (by simp) (fun j hj => by
      simp only [List.map_cons, List.map_nil, KC.val, hctr]
      exact hz j (by simpa using hj))
  have e : sEncOf l = .n (sLayerK l a0 signed).2.2 := by rw [(sLayerK_out l a0 signed).1]; rfl
  have k1 := k
  simp only [List.map_cons, List.map_nil, KC.val, hctr, c1, c0] at k1
  rw [e]
  exact k1

/-- **A layer before its call, sound**: the counter read is a number `N < 2^32` at `sCtrOf l`, and
the encoding digest at `sEncOf l` is the statement's encoding hash of the message `signed` and the
counter `beWordAt 0 N` (`BE_32` of it is the bytes hinted), at the one-time key whose address cells
are `a0`, `a1`. -/
theorem sLayerPre_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ}
    (hbb : ByteBits L.read (σ (.n 1))) (hp : PadOK σ sPad) {l : Nat} {a0 a1 signed : V}
    (h : AtomsHold L.read σ (sLayerPre l a0 a1 signed)) {layer : Layer} {tree : TreeIndex}
    {lf : TreeLeafIndex} (hl : layer.val = l) (ha0 : σ a0 = adrsCell0 l tree.val)
    (ha1 : σ a1 = adrsCell1 0 lf.val 0 0) :
    ∃ N < 2 ^ 32, σ (sCtrOf l) = eOfNat N ∧
      Id.run (tweakableHash (m := Id) keccakF1600 (cellVal (σ sPP)) (.encoding layer tree lf)
        (littleEndianBytes 16 (cellVal (σ signed)) ++
          Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 (beWordAt 0 N)))) = cellVal (σ (sEncOf l)) := by
  obtain ⟨N, hN, hctr, hE⟩ := sLayerPre_cells hκ hbb hp h
  refine ⟨N, hN, hctr, ?_⟩
  have hEA : σ a1 + lit (7 * 2 ^ 24) = adrsCell1 7 lf.val 0 0 := by
    rw [ha1, lit_of_lt (by norm_num)]
    exact adrsCell1_add_type (by norm_num)
  have hA := addressedHash_encodingDigest (σ sPP) (σ signed) layer.val tree.val .wotsEncoding lf.val 0 0
    (BitVec.ofNat 32 (beWordAt 0 N))
  have hcell : eOfNat (beWordAt 0 (@BitVec.toNat Sphincs.counterBits
      (BitVec.ofNat 32 (beWordAt 0 N)))) = eOfNat N := by
    show eOfNat (beWordAt 0 (BitVec.ofNat 32 (beWordAt 0 N)).toNat) = eOfNat N
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (beWordAt_zero_lt N), beWordAt_zero_beWordAt_zero hN]
  rw [hcell] at hA
  rw [hE, hEA, ha0, ← hl]
  exact hA

/-! ## The layer's path -/

/-- Where `sPath … m z x` hints its level `j`'s children. -/
def sPathPos : Nat → Nat → Nat → Nat → Nat
  | 0, _, x, _ => x
  | m + 1, z, x, j => if j = z then x else sPathPos m (z + 1) (x + pathWidth m) j

/-- `sPathSib`'s siblings, at `sPathPos`. -/
theorem sPathSib_eq (bit : Nat → V) (off : Nat) :
    ∀ (m z x j : Nat), z ≤ j → j < z + m →
      sPathSib σ bit off m z x j = siblingOf σ (bit (off + j)) (sPathPos m z x j)
  | 0, _, _, _, _, h => absurd h (by omega)
  | m + 1, z, x, j, h1, h2 => by
      by_cases hj : j = z
      · subst hj; simp [sPathSib, sPathPos]
      · simp only [sPathSib, sPathPos, hj, ↓reduceIte]
        exact sPathSib_eq bit off m (z + 1) (x + pathWidth m) j (by omega) (by omega)

/-- The layers' siblings at `SphincsSig`'s positions. -/
theorem sPathPos_layer : ∀ l < 3, ∀ j < sHeightOf l,
    sPathPos (sHeightOf l) 0 (sLayerBase l + 48) j = sPathKid l j := by decide +kernel

/-- **A layer's path, sound**: the bits of the layer's leaf `layerLeafN T l` and its shifts as the
digest block gives them, the root is `pFold` of `pNodeE` from the leaf `sp_wots` returns. -/
theorem sLayerPath_sound (hp : PadOK σ sPad) {T : Nat} (hD : DigestAt σ T) {l : Nat} (hl : l < 3)
    {a0 signed : V} (h : AtomsHold rd σ (sLayerPath l a0 signed).1) :
    σ (sLayerPath l a0 signed).2.2 = pFold (pNodeE (σ sPP) (σ a0) (layerLeafN T l)
      (sPathSib σ sLeafBit (sOffOf l) (sHeightOf l) 0 ((sLayerK l a0 signed).2.1 + 1)))
        (sHeightOf l) (σ (.n (sLayerK l a0 signed).2.1)) := by
  have hlen : sLeafLen l ≤ 10 := sLeafLen_le.2
  have hb := sPath_sound (rd := rd) (σ := σ) (pad := sPad) (pp := sPP) (a0 := a0) (bit := sLeafBit)
    (val := sLVal) (off := sOffOf l) (e := layerLeafN T l) (height := sHeightOf l) hp
    (by unfold sHeightOf; omega) (layerLeafN_lt T l)
    (fun z hz => by
      have hb26 : sLeafOff l + z < 26 := by
        unfold sHeightOf at hz; unfold sLeafOff; unfold sLeafLen at hz; split_ifs at hz <;> omega
      rw [sOffOf, hD.leafBit hb26, testBit_layerLeafN]
      simp only [show z < sLeafLen l from hz, decide_true, Bool.true_and]
      rfl)
    (fun z hz => hD.2.2.2.1 l hl z hz)
    (sHeightOf l) 0 (.n (sLayerK l a0 signed).2.1) ((sLayerK l a0 signed).2.1 + 1) (by omega) h
  rw [← nIter_zero]
  exact hb

/-! ## A layer -/

/-- **A layer, sound**: under a call relation that unfolds at `V`, its counter and encoding, its
call of `sp_wots` at the key `K_l(idx)`'s address cells (`a0 = sA0Of l`, `a1 = sA1Of l`) and its
path reach, from the message `signed`, the root the path computes, with the layer's signature
`sphincsSigOf σ Vm`'s, when the digest `T` gives the leaf. -/
theorem layer_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} {Vm : FrameMap}
    (hV : UnfoldsV L.read C Vm) (hbb : ByteBits L.read (σ (.n 1))) (hp : PadOK σ sPad) {T : Nat}
    (hD : DigestAt σ T) (l : Layer) {signed : V}
    (hpre : AtomsHold L.read σ (sLayerPre l.val (sA0Of l.val) (sA1Of l.val) signed))
    (hcall : C "sp_wots" ([sPP, sA0Of l.val, sA1Of l.val,
      .n (sLayerK l.val (sA0Of l.val) signed).2.2].map σ)
      ([.n (sLayerK l.val (sA0Of l.val) signed).2.1].map σ))
    (hpath : AtomsHold L.read σ (sLayerPath l.val (sA0Of l.val) signed).1) {idx : Index}
    (ha0 : σ (sA0Of l.val) = adrsCell0 l.val (treeOfIndex l idx).val)
    (ha1 : σ (sA1Of l.val) = adrsCell1 0 (leafOfIndex l idx).val 0 0)
    (hleaf : (leafOfIndex l idx).val = layerLeafN T l.val) :
    LayerReaches (cellVal (σ sPP)) idx (sphincsSigOf σ Vm) l (cellVal (σ signed))
      (cellVal (σ (sLayerPath l.val (sA0Of l.val) signed).2.2)) := by
  obtain ⟨N, hN, hctr, henc⟩ := sLayerPre_sound hκ hbb hp hpre rfl ha0 ha1
  have eK := sLayerK_out l.val (sA0Of l.val) signed
  simp only [List.map_cons, List.map_nil] at hcall
  obtain ⟨hv, hw⟩ := wots_call_sound hV hcall l (treeOfIndex l idx) (leafOfIndex l idx)
    (by rw [ha0, ha1]; rfl)
  have hc : ((sphincsSigOf σ Vm).layers l).counter = BitVec.ofNat 32 (beWordAt 0 N) := by
    simp only [sphincsSigOf, sLayerOf, hctr, cellNat_eOfNat (show N < 2 ^ 64 by omega)]
    rfl
  have hvals : ((sphincsSigOf σ Vm).layers l).chainValues =
      sChainValuesOf (Vm "sp_wots" [σ sPP, σ (sA0Of l.val), σ (sA1Of l.val),
        σ (.n (sLayerK l.val (sA0Of l.val) signed).2.2)]
        [σ (.n (sLayerK l.val (sA0Of l.val) signed).2.1)]) := by
    rw [eK.1, eK.2]
    rfl
  have hl3 := l.isLt
  have hpth := sLayerPath_sound (rd := L.read) hp hD hl3 hpath
  refine layerReaches_of_cells (enc := cellVal (σ (sEncOf l.val))) ?_ ?_ (hw.trans ?_) ?_
  · rw [hc]; exact henc
  · rw [show sEncOf l.val = .n (sLayerK l.val (sA0Of l.val) signed).2.2 by rw [eK.1]; rfl]
    exact hv
  · rw [hvals, show sEncOf l.val = .n (sLayerK l.val (sA0Of l.val) signed).2.2 by rw [eK.1]; rfl]
  · rw [hpth, ha0, ← hleaf]
    have hh : layerHeight l = sHeightOf l.val := by
      unfold layerHeight sHeightOf sLeafLen; rfl
    rw [hh]
    refine htTreeFold_cells _ _ _ _ _ _ _ _ (by unfold sHeightOf; have := sLeafLen_le (l := l.val); omega)
      fun j hj => ?_
    rw [sPathSib_eq sLeafBit _ _ 0 _ j (by omega) (by omega), eK.2,
      show sLayerBase l.val + 47 + 1 = sLayerBase l.val + 48 by omega,
      sPathPos_layer l.val hl3 j hj]
    simp only [layerPath, show j < layerHeight l by rw [hh]; exact hj, ↓reduceDIte, sphincsSigOf,
      sLayerOf]
    rfl

end
end LeanVM.Guest.B1.Sig
