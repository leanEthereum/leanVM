/-
  LeanVM.Guest.B1.Sig.SphincsStagesComplete

  The statement's leanSPHINCS verification (`Statement/LeanSphincs.lean`) of
  an honest signature, stage by stage over the cells `verify_sig_lean_sphincs`'s completeness
  computes: the digest's number, the FORS key's cell, each layer's encoding, leaf and root.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBridge
public import LeanVM.Guest.B1.Sig.SphincsCompleteBlocks

/-!
# An honest signature's stages over cells

For a public key `pk`, a message `m` and a signature `sig`:

* `msgLo m`, `msgHi m`: the claim's two message cells; `digestT pk m sig`: the digest's number,
  `sDigestOf_eq`: the statement's digest is `digestOf` of it;
* `forsSecretCell`, `forsSibCell`, `layerSibCell`: the signature's openings and paths as cells;
  `forsKeyCell`, `sForsKeyOf_eq`: the FORS key is the value of `T_k` of the roots' cells;
* `layer_cells`: a layer reaching `r` from the value of a cell `S` has its encoding's digits reach
  the target sum, and `r` is the value of `pFold` of `pNodeE` from the leaf's cell
  (`wotsLeafOf`); `layer_call`: the call relation holds of that layer's `sp_wots` call under
  `SpWotsCalls`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)
open HashSig HashSig.OverPermutation

@[expose] public section

/-! ## The digest -/

/-- `cellVal_cellOf128` at a digest. -/
theorem cellVal_cellOf128_digest (v : HashSig.Digest) : cellVal (cellOf128 v) = v := cellVal_cellOf128 v

/-- The claim's low message cell. -/
def msgLo (m : HashSig.Message) : E := cellOf128 (m.extractLsb' 0 128)
/-- The claim's high message cell. -/
def msgHi (m : HashSig.Message) : E := cellOf128 (m.extractLsb' 128 128)

/-- **The digest's number** of an honest signature: the statement's `H_msg` output. -/
def digestT (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) : Nat :=
  (sDigestOf pk m sig).toNat

theorem digestT_lt (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    digestT pk m sig < 2 ^ 272 := by
  have := (sDigestOf pk m sig).isLt
  rw [two_pow_digestBits] at this
  exact this

/-- **The statement's message digest is `digestOf` of the digest's number.** -/
theorem sDigestOf_eq (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    sDigestOf pk m sig = digestOf (digestT pk m sig) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, digestT, Nat.mod_eq_of_lt (sDigestOf pk m sig).isLt]

/-- The digest's index, as the statement reads it. -/
abbrev digestIdx (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    Sphincs.Index :=
  Sphincs.digestIndex (sDigestOf pk m sig)

theorem treeOf_idx (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (l : Sphincs.Layer) :
    (Sphincs.treeOfIndex l (digestIdx pk m sig)).val = layerTreeN (digestT pk m sig) l.val := by
  rw [digestIdx, sDigestOf_eq]; exact treeOfIndex_digest (digestT_lt pk m sig) l

theorem leafOf_idx (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (l : Sphincs.Layer) :
    (Sphincs.leafOfIndex l (digestIdx pk m sig)).val = layerLeafN (digestT pk m sig) l.val := by
  rw [digestIdx, sDigestOf_eq]; exact leafOfIndex_digest (digestT_lt pk m sig) l

/-! ## FORS -/

/-- FORS tree `c`'s opened secret, as a cell. -/
def forsSecretCell (sig : Sphincs.Signature) (c : Nat) : E :=
  cellOf128 (if h : c < 24 then (sig.forsOpening ⟨c, h⟩).secret else 0)

/-- FORS tree `c`'s sibling at height `z`, as a cell. -/
def forsSibCell (sig : Sphincs.Signature) (c z : Nat) : E :=
  cellOf128 (if h : c < 24 then (if hz : z < 10 then (sig.forsOpening ⟨c, h⟩).path ⟨z, hz⟩ else 0)
    else 0)

/-- **The FORS key's cell**: `T_k` of `PK.seed`, the bottom key's `A0`, `FORS_ROOTS` and the roots
the openings reach at the digest's leaves. -/
def forsKeyCell (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) : E :=
  (hcell ([cellOf128 pk.publicSeed, adrsCell0 0 (layerTreeN (digestT pk m sig) 0),
    adrsCell1 4 (layerLeafN (digestT pk m sig) 0) 0 0] ++
    List.ofFn fun c : Sphincs.ForsTreeIndex =>
      forsRootCell (cellOf128 pk.publicSeed) (adrsCell0 0 (layerTreeN (digestT pk m sig) 0))
        (layerLeafN (digestT pk m sig) 0) c.val (forsLeafN (digestT pk m sig) c.val)
        (forsSecretCell sig c.val) (forsSibCell sig c.val))).1

/-- **The statement's FORS key is the FORS key cell's value.** -/
theorem sForsKeyOf_eq (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    sForsKeyOf pk m sig = cellVal (forsKeyCell pk m sig) := by
  have hT := digestT_lt pk m sig
  have h := forsRecover_cells (cellOf128 pk.publicSeed) (digestIdx pk m sig)
    (Sphincs.digestForsLeaves (sDigestOf pk m sig)) sig.forsOpening
    (secret := forsSecretCell sig) (sib := forsSibCell sig)
    (fun c => by
      have hc : c.val < 24 := c.isLt
      simp only [forsSecretCell, hc, ↓reduceDIte]
      exact cellVal_cellOf128_digest _)
    (fun c z hz => by
      have hc : c.val < 24 := c.isLt
      simp only [forsSibCell, hc, hz, ↓reduceDIte]
      exact cellVal_cellOf128_digest _)
  rw [cellVal_cellOf128] at h
  rw [sForsKeyOf, h, forsKeyCell]
  have e0 := treeOf_idx pk m sig 0
  have e1 := leafOf_idx pk m sig 0
  simp only [Fin.val_zero] at e0 e1
  rw [e0, e1]
  simp only [sDigestOf_eq, digestForsLeaves_val hT]
  rfl

/-! ## The layers -/

/-- Layer `l`'s path, as cells. -/
def layerSibCell (sig : Sphincs.Signature) (l : Sphincs.Layer) (z : Nat) : E :=
  cellOf128 (Sphincs.Verification.layerPath sig l z)

/-- The encoding's digest cell of layer `l`'s key, signing the value of `S`. -/
def layerEnc (pk : Sphincs.PublicKey) (idx : Sphincs.Index) (sig : Sphincs.Signature)
    (l : Sphincs.Layer) (S : E) : E :=
  encDigestCell (cellOf128 pk.publicSeed) (adrsCell0 l.val (Sphincs.treeOfIndex l idx).val)
    (adrsCell1 7 (Sphincs.leafOfIndex l idx).val 0 0) S
    (eOfNat (beWordAt 0 (sig.layers l).counter.toNat))

/-- The leaf layer `l`'s key recovers, signing the value of `S`. -/
def layerLeaf (pk : Sphincs.PublicKey) (idx : Sphincs.Index) (sig : Sphincs.Signature)
    (l : Sphincs.Layer) (S : E) : HashSig.Digest :=
  wotsLeafOf pk.publicSeed l (Sphincs.treeOfIndex l idx) (Sphincs.leafOfIndex l idx)
    (cellVal (layerEnc pk idx sig l S)) (sig.layers l).chainValues

/-- The root layer `l` reaches, signing the value of `S`, as a cell. -/
def layerRootCell (pk : Sphincs.PublicKey) (idx : Sphincs.Index) (sig : Sphincs.Signature)
    (l : Sphincs.Layer) (S : E) : E :=
  pFold (pNodeE (cellOf128 pk.publicSeed) (adrsCell0 l.val (Sphincs.treeOfIndex l idx).val)
    (Sphincs.leafOfIndex l idx).val (layerSibCell sig l)) (Sphincs.layerHeight l)
    (cellOf128 (layerLeaf pk idx sig l S))

theorem layerHeight_le (l : Sphincs.Layer) : Sphincs.layerHeight l ≤ 10 := by
  unfold Sphincs.layerHeight; split <;> omega

/-- **A layer over cells**: reaching `r` from the value of `S`, its encoding's digits reach the
target sum, and `r` is the value of its root cell. -/
theorem layer_cells {pk : Sphincs.PublicKey} {idx : Sphincs.Index} {sig : Sphincs.Signature}
    {l : Sphincs.Layer} {S : E} {r : HashSig.Digest}
    (h : LayerReaches pk.publicSeed idx sig l (cellVal S) r) :
    Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits (cellVal (layerEnc pk idx sig l S))) ∧
      r = cellVal (layerRootCell pk idx sig l S) := by
  obtain ⟨v, hot, hfold⟩ := (layerReaches_iff _ _ _ _ _ _).mp h
  have ho := otsLeaf_cells (cellOf128 pk.publicSeed) S l (Sphincs.treeOfIndex l idx)
    (Sphincs.leafOfIndex l idx) (sig.layers l).counter (sig.layers l).chainValues
  rw [cellVal_cellOf128] at ho
  rw [ho] at hot
  split_ifs at hot with hV
  have hv : v = layerLeaf pk idx sig l S := (Option.some.inj hot).symm
  refine ⟨hV, ?_⟩
  have hf := htFold_cells (cellOf128 pk.publicSeed) l (Sphincs.treeOfIndex l idx)
    (Sphincs.leafOfIndex l idx) (sib := layerSibCell sig l)
    (path := Sphincs.Verification.layerPath sig l) (layerHeight_le l)
    (fun z _ => cellVal_cellOf128 _) (cellOf128 v)
  rw [cellVal_cellOf128, cellVal_cellOf128_digest] at hf
  rw [← hfold, hf, hv]
  rfl

/-- **Layer `l`'s call of `sp_wots` holds** under `SpWotsCalls`: on `PK.seed`, the key's address
cells and its encoding's digest cell, returning its leaf's cell. -/
theorem layer_call {C : CallRel} (hC : SpWotsCalls C) {pk : Sphincs.PublicKey}
    {idx : Sphincs.Index} {sig : Sphincs.Signature} {l : Sphincs.Layer} {S : E}
    (hV : Sphincs.TargetSum.Valid
      (Sphincs.TargetSum.base2bDigits (cellVal (layerEnc pk idx sig l S)))) :
    C "sp_wots" [cellOf128 pk.publicSeed, adrsCell0 l.val (Sphincs.treeOfIndex l idx).val,
      adrsCell1 0 (Sphincs.leafOfIndex l idx).val 0 0, layerEnc pk idx sig l S]
      [cellOf128 (layerLeaf pk idx sig l S)] := by
  have := hC pk.publicSeed l (Sphincs.treeOfIndex l idx) (Sphincs.leafOfIndex l idx)
    (cellVal (layerEnc pk idx sig l S)) (sig.layers l).chainValues hV
  have hc : cellOf128 (cellVal (layerEnc pk idx sig l S)) = layerEnc pk idx sig l S :=
    cellOf128_cellVal _
  rw [hc] at this
  exact this

/-- `WOTS_ENC` added to a key pair's `A1`. -/
theorem adrsCell1_enc (kp : Nat) : adrsCell1 0 kp 0 0 + lit (7 * 2 ^ 24) = adrsCell1 7 kp 0 0 := by
  rw [lit_of_lt (by norm_num)]
  exact adrsCell1_add_type (by norm_num)

end
end LeanVM.Guest.B1.Sig
