/-
  LeanVM.Guest.B1.Sig.SphincsBridgeCells

  leanSPHINCS's verification stages (`Statement/LeanSphincs.lean` at leanVM main `40f877dc`) over the
  guest's cells: a tree's fold, a FORS tree's root, the FORS key and a one-time leaf.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsHash
public import LeanVM.Guest.B1.Sig.SphincsSoundPath
public import LeanVM.Guest.B1.Sig.SphincsCompleteSpec

/-!
# leanSPHINCS's stages over cells

The statement's hashes of digests that are cells' values are the first cells of the guest's
`hcell`s (`tweakableHash_sphincsCells`), so its folds are folds of cells:

* `pathAdr_eqC`: a path node's address cell (`pathAdr`, type `TREE`) is `adrsCell1 2 0 h i`;
* `foldPath_cells`: `foldPath` of a tweakable hash whose address cells at level `l` are `a0` and
  `adr l` is the value of `pFold` of the cells' nodes;
* `htFold_cells`: a tree's fold is `pFold` of `pNodeE` at the tree's `A0`;
* `forsAdrCell`, `forsLeafCell`, `forsNodeCell`, `forsRootCell`: FORS tree `c`'s addresses
  (`FORS_TREE`, at the bottom key's leaf `kp`, height `z`, index `c·2^(10-z) + s >>> z`), its leaf
  hashed from its secret and its nodes; `forsTreeRecover_cellsC`, `forsRecover_cells`: a FORS tree's
  root and the FORS key (`FORS_ROOTS`) over cells;
* `encDigestCell`, `encode_cells`, `otsLeaf_cells`: the encoding's digest is the first cell of the hash of
  the 68 bytes of `[P, A0, A1_enc, M, counter]`, and the one-time leaf is `wotsLeafOf` when its
  digits reach the target sum, nothing otherwise.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open HashSig HashSig.OverPermutation

@[expose] public section

/-! ## Folds -/

/-- **A path node's address cell**: type `TREE`, height `h`, index `i`. -/
theorem pathAdr_eqC {h i : Nat} (hh : h < 256) (hi : i < 2 ^ 16) : pathAdr h i = adrsCell1 2 0 h i := by
  have ha : a1Hi h i < 2 ^ 64 := by unfold a1Hi; omega
  have e : pathAdr h i = lit (2 * 2 ^ 24 + 2 ^ 64 * a1Hi h i) := by
    rw [pathAdr, lit]; congr 1 <;> omega
  rw [e, lit_eq _ (by omega), adrsCell1_eq]
  congr 1
  simp only [adrsNat1, beWordAt_zero_of_lt (show 2 < 256 by norm_num), beWordAt_of_zero,
    beWordAt_two_of_lt hh, beWordAt_three_of_lt_pow16 hi, a1Hi]
  omega

/-- Folds agree when their nodes agree on the levels folded. -/
theorem pFold_congr_lt (f g : Nat → E → E) : ∀ (n : Nat) (x : E), (∀ l < n, f l = g l) →
    pFold f n x = pFold g n x
  | 0, _, _ => rfl
  | n + 1, x, h => by
      rw [pFold, pFold, h n (by omega), pFold_congr_lt f g n x fun l hl => h l (by omega)]

theorem nodePayload_mPair (b : Bool) (v s : E) :
    (if b then nodePayload (cellVal s) (cellVal v) else nodePayload (cellVal v) (cellVal s)) =
      [(mPair b v s).1, (mPair b v s).2].flatMap cellBytes := by
  cases b <;> simp [mPair, nodePayload_cellVal]

/-- **A fold of tweakable hashes over cells**: when the hash domain of level `l`'s node `q`
(`q = e / 2^(l + 1)`) has the address cells `a0`, `adr l`, `foldPath` from the value of `x`, the
siblings the values of `sib`, is the value of `pFold` of the cells' nodes. -/
theorem foldPath_cells (pp a0 : E) (dom : Nat → Nat → Sphincs.HashDomain) (adr : Nat → E) (e : Nat)
    {sib : Nat → E} {path : Nat → HashSig.Digest} :
    ∀ (n : Nat), (∀ l < n, hashDomainCells (dom l (e / 2 ^ (l + 1))) = (a0, adr l)) →
      (∀ l < n, cellVal (sib l) = path l) → ∀ x : E,
      Id.run (foldPath (m := Id) (fun level q =>
          Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp) (dom level q))
        e path n (cellVal x)) =
        cellVal (pFold (fun l v => (hcell [pp, a0, adr l, (mPair (e.testBit l) v (sib l)).1,
          (mPair (e.testBit l) v (sib l)).2]).1) n x)
  | 0, _, _, _ => rfl
  | n + 1, hd, hs, x => by
      have ih := foldPath_cells pp a0 dom adr e n (fun l hl => hd l (by omega))
        (fun l hl => hs l (by omega)) x
      show Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp)
        (dom n (e / 2 ^ (n + 1)))
        (if e.testBit n then nodePayload (path n) (Id.run (foldPath (m := Id) (fun level q =>
            Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp) (dom level q))
            e path n (cellVal x)))
          else nodePayload (Id.run (foldPath (m := Id) (fun level q =>
            Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp) (dom level q))
            e path n (cellVal x))) (path n)) = _
      rw [ih, ← hs n (by omega), nodePayload_mPair, tweakableHash_sphincsCells, hd n (by omega)]
      rfl

/-- **A tree's fold over cells**: from the value of `x`, the siblings the values of `sib`, the fold
of tree `tree` of layer `layer` from leaf `leaf` is the value of `pFold` of `pNodeE` at the tree's
`A0`. -/
theorem htFold_cells (pp : E) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (leaf : Sphincs.TreeLeafIndex) {sib : Nat → E} {path : Nat → HashSig.Digest} {h : Nat} (hh : h ≤ 10)
    (hsib : ∀ l < h, cellVal (sib l) = path l) (x : E) :
    Id.run (Sphincs.Verification.treeFold (m := Id) keccakF1600 (cellVal pp) layer tree leaf path h
        (cellVal x)) =
      cellVal (pFold (pNodeE pp (adrsCell0 layer.val tree.val) leaf.val sib) h x) := by
  have hl' : leaf.val < 2 ^ 10 := leaf.isLt
  refine (foldPath_cells pp (adrsCell0 layer.val tree.val)
    (fun level q => .node layer tree (level + 1) q)
    (fun l => adrsCell1 2 0 (l + 1) (leaf.val / 2 ^ (l + 1))) leaf.val h
    (fun l _ => rfl) hsib x).trans ?_
  refine congrArg cellVal (pFold_congr_lt _ _ h x fun l hl => funext fun v => ?_)
  rw [pNodeE, pathAdr_eqC (by omega) (by
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hl' (by norm_num))),
    Nat.shiftRight_eq_div_pow]

/-! ## FORS -/

/-- FORS tree `c`'s address cell at height `z` on the path of leaf `s`, at the bottom key's leaf
`kp`: `FORS_TREE`, the height, the tree index `c·2^(10-z) + s >>> z`. -/
def forsAdrCell (kp c z s : Nat) : E := adrsCell1 3 kp z (c * 2 ^ (10 - z) + s >>> z)

/-- FORS tree `c`'s leaf `s` hashed from its secret's cell. -/
def forsLeafCell (pp a0 : E) (kp c s : Nat) (secret : E) : E :=
  (hcell [pp, a0, forsAdrCell kp c 0 s, secret]).1

/-- FORS tree `c`'s node at height `z + 1` on the path of leaf `s`, from the one at `z` and its
sibling. -/
def forsNodeCell (pp a0 : E) (kp c s : Nat) (sib : Nat → E) (z : Nat) (v : E) : E :=
  (hcell [pp, a0, forsAdrCell kp c (z + 1) s, (mPair (s.testBit z) v (sib z)).1,
    (mPair (s.testBit z) v (sib z)).2]).1

/-- FORS tree `c`'s root reached from leaf `s`'s secret and its siblings. -/
def forsRootCell (pp a0 : E) (kp c s : Nat) (secret : E) (sib : Nat → E) : E :=
  pFold (forsNodeCell pp a0 kp c s sib) 10 (forsLeafCell pp a0 kp c s secret)

/-- **A FORS tree's root over cells**: the secret and the path the values of `secret`, `sib`. -/
theorem forsTreeRecover_cellsC (pp : E) (idx : Sphincs.Index) (c : Sphincs.ForsTreeIndex)
    (s : Sphincs.ForsLeafIndex) (op : Sphincs.ForsTreeOpening) {secret : E} {sib : Nat → E}
    (hsec : cellVal secret = op.secret)
    (hsib : ∀ z (hz : z < 10), cellVal (sib z) = op.path ⟨z, hz⟩) :
    Id.run (Sphincs.Verification.forsTreeRecover (m := Id) keccakF1600 (cellVal pp) idx c s op) =
      cellVal (forsRootCell pp (adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val)
        (Sphincs.leafOfIndex 0 idx).val c.val s.val secret sib) := by
  have hleaf : Id.run (Sphincs.Verification.forsLeafHash (m := Id) keccakF1600 (cellVal pp) idx c s
      op.secret) = cellVal (forsLeafCell pp (adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val)
        (Sphincs.leafOfIndex 0 idx).val c.val s.val secret) := by
    rw [← hsec]
    show Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp)
      (.forsLeaf idx c s) (littleEndianBytes 16 (cellVal secret)) = _
    rw [digest_cells, tweakableHash_sphincsCells]
    simp only [forsLeafCell, forsAdrCell, hashDomainCells, Sphincs.forsTreeIndex,
      Sphincs.forsTreeHeight, Nat.shiftRight_zero]
    rfl
  show Id.run (foldPath (m := Id) (fun level node => Sphincs.Verification.tweakableHash (m := Id)
      keccakF1600 (cellVal pp) (.forsNode idx c (level + 1) node)) s.val
      (fun level => if h : level < Sphincs.forsTreeHeight then op.path ⟨level, h⟩ else 0)
      Sphincs.forsTreeHeight (Id.run (Sphincs.Verification.forsLeafHash (m := Id) keccakF1600
        (cellVal pp) idx c s op.secret))) = _
  rw [hleaf]
  refine (foldPath_cells pp (adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val)
    (fun level q => .forsNode idx c (level + 1) q)
    (fun l => forsAdrCell (Sphincs.leafOfIndex 0 idx).val c.val (l + 1) s.val) s.val 10
    (fun l _ => by
      simp only [hashDomainCells, forsAdrCell, Sphincs.forsTreeIndex, Sphincs.forsTreeHeight,
        Nat.shiftRight_eq_div_pow])
    (fun l hl => by
      show cellVal (sib l) = if h : l < 10 then op.path ⟨l, h⟩ else 0
      simp only [hl, ↓reduceDIte]; exact hsib l hl) _).trans ?_
  rfl

/-- **The FORS key over cells**: `T_k` (`FORS_ROOTS`) of the roots the openings reach, their
secrets and paths the values of `secret c`, `sib c`. -/
theorem forsRecover_cells (pp : E) (idx : Sphincs.Index)
    (leaves : Sphincs.ForsTreeIndex → Sphincs.ForsLeafIndex)
    (op : Sphincs.ForsTreeIndex → Sphincs.ForsTreeOpening) {secret : Nat → E} {sib : Nat → Nat → E}
    (hsec : ∀ c : Sphincs.ForsTreeIndex, cellVal (secret c.val) = (op c).secret)
    (hsib : ∀ (c : Sphincs.ForsTreeIndex) z (hz : z < 10), cellVal (sib c.val z) = (op c).path ⟨z, hz⟩) :
    Id.run (Sphincs.Verification.forsRecover (m := Id) keccakF1600 (cellVal pp) idx leaves op) =
      cellVal (hcell ([pp, adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val,
        adrsCell1 4 (Sphincs.leafOfIndex 0 idx).val 0 0] ++
        List.ofFn fun c : Sphincs.ForsTreeIndex =>
          forsRootCell pp (adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val)
            (Sphincs.leafOfIndex 0 idx).val c.val (leaves c).val (secret c.val) (sib c.val))).1 := by
  have hr : (fun c : Sphincs.ForsTreeIndex => Id.run (Sphincs.Verification.forsTreeRecover (m := Id)
      keccakF1600 (cellVal pp) idx c (leaves c) (op c))) = fun c =>
      cellVal (forsRootCell pp (adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val)
        (Sphincs.leafOfIndex 0 idx).val c.val (leaves c).val (secret c.val) (sib c.val)) :=
    funext fun c => forsTreeRecover_cellsC pp idx c (leaves c) (op c) (hsec c) (hsib c)
  show Sphincs.Verification.forsPublicKey (m := Id) keccakF1600 (cellVal pp) idx
    (sequenceFin (m := Id) fun c => Sphincs.Verification.forsTreeRecover (m := Id) keccakF1600
      (cellVal pp) idx c (leaves c) (op c)) = _
  rw [sequenceFin_id]
  show Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp) (.forsRoots idx)
    (digestsPayload fun c => Id.run (Sphincs.Verification.forsTreeRecover (m := Id) keccakF1600
      (cellVal pp) idx c (leaves c) (op c))) = _
  rw [hr, digestsPayload_cells, tweakableHash_sphincsCells]
  rfl

/-! ## The one-time leaf -/

/-- **The encoding's digest cell**: the first cell of the hash of the 68 bytes of `[P, A0, A1,
M, counter]`. -/
def encDigestCell (pp a0 a1 msg ctr : E) : E :=
  (digestHalves (keccak256 ((cellsBytes [pp, a0, a1, msg, ctr]).take 68))).1

/-- **The encoding over cells**: the counter's cell holds `BE_32(c)` reversed. -/
theorem encode_cells (pp msg : E) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (leaf : Sphincs.TreeLeafIndex) (ctr : Sphincs.EncodingCounter) :
    Id.run (Sphincs.Verification.encode (m := Id) keccakF1600 (cellVal pp) layer tree leaf
        (cellVal msg) ctr) =
      Sphincs.TargetSum.decodeDigest (cellVal (encDigestCell pp (adrsCell0 layer.val tree.val)
        (adrsCell1 7 leaf.val 0 0) msg (eOfNat (beWordAt 0 ctr.toNat)))) := by
  have := addressedHash_encodingDigest pp msg layer.val tree.val .wotsEncoding leaf.val 0 0 ctr
  simp only [Sphincs.Verification.encode, Id.run, bind, pure]
  exact congrArg Sphincs.TargetSum.decodeDigest this

/-- **The one-time leaf over cells**: the leaf `wotsLeafOf` the chain values recover when the
encoding's digits reach the target sum, nothing otherwise. -/
theorem otsLeaf_cells (pp msg : E) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (leaf : Sphincs.TreeLeafIndex) (ctr : Sphincs.EncodingCounter)
    (values : Sphincs.ChainIndex → HashSig.Digest) :
    Id.run (Sphincs.Verification.otsLeaf (m := Id) keccakF1600 (cellVal pp) layer tree leaf
        (cellVal msg) ctr values) =
      if Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits (cellVal (encDigestCell pp
          (adrsCell0 layer.val tree.val) (adrsCell1 7 leaf.val 0 0) msg
          (eOfNat (beWordAt 0 ctr.toNat))))) then
        some (wotsLeafOf (cellVal pp) layer tree leaf (cellVal (encDigestCell pp
          (adrsCell0 layer.val tree.val) (adrsCell1 7 leaf.val 0 0) msg
          (eOfNat (beWordAt 0 ctr.toNat)))) values)
      else none := by
  have he : Sphincs.Verification.encode (m := Id) keccakF1600 (cellVal pp) layer tree leaf
      (cellVal msg) ctr = Sphincs.TargetSum.decodeDigest (cellVal (encDigestCell pp
        (adrsCell0 layer.val tree.val) (adrsCell1 7 leaf.val 0 0) msg
        (eOfNat (beWordAt 0 ctr.toNat)))) := encode_cells pp msg layer tree leaf ctr
  unfold Sphincs.Verification.otsLeaf
  rw [he]
  unfold Sphincs.TargetSum.decodeDigest
  split_ifs <;> rfl

end
end LeanVM.Guest.B1.Sig
