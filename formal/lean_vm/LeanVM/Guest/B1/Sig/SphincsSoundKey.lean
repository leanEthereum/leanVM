/-
  LeanVM.Guest.B1.Sig.SphincsSoundKey

  The FORS block of `verify_sig_lean_sphincs` (`lean_ethereum.py:4031-4036` at leanVM main 40f877dc)
  against the statement: the FORS key the guest computes is the statement's `fors_pkFromSig` of the
  openings `sphincsSigOf` reads, at the digest's index and leaves.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundFors
public import LeanVM.Guest.B1.Sig.SphincsSoundAddrs
public import LeanVM.Guest.B1.Sig.SphincsSig

/-!
# The FORS key, sound

`SphincsSoundFors.sForsBlock_sound` gives the FORS key as the `hcell` of `P`, `A0`,
`key + FORS_ROOTS` and the roots `fRootE` (leaf `fLeafE`, nodes `fNodeE` at `fAdrE`). Here:

* `fAdrE_eq`: `fAdrE` at `A1 = key + FORS_TREE` is the statement's address cell of the FORS node
  (`adrsCell1_add_words23`);
* `forsTreeRecover_cells`: the statement's FORS tree root of an opening whose secret and path are
  cells' values is `fRootE`'s;
* `forsSib_eq`, `forsTreeBase_eq`: the siblings and secrets at `SphincsSig`'s positions;
* `forsKey_sound`: the FORS key is `forsRecover` of `sForsOpeningOf`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)
open HashSig HashSig.OverPermutation
open Sphincs Sphincs.Verification

@[expose] public section

/-! ## Addresses -/

/-- **A FORS node's address cell** (`sp_fors_at`), at the key pair's `A1 + FORS_TREE`: height `z`,
its index across the trees. -/
theorem fAdrE_eq {kp c z s : Nat} (hc : c < 24) (hz : z ≤ 10) (hs : s < 2 ^ 10) :
    fAdrE (adrsCell1 3 kp 0 0) c z s =
      adrsCell1 3 kp z (forsTreeIndex ⟨c, by simp [forsTreeCount]; omega⟩ z (s >>> z)) := by
  have hi := fIdx_lt hc hz hs
  have hA := a1Hi_lt (h := z) (i := fIdx c z s) (by omega) hi
  have hF : forsTreeIndex ⟨c, by simp [forsTreeCount]; omega⟩ z (s >>> z) = fIdx c z s := by
    simp only [Sphincs.forsTreeIndex, fIdx, forsTreeHeight]
    ring
  rw [hF, fAdrE, ← lit_hi hA, ← adrsCell1_add_words23 3 kp z (fIdx c z s)]
  congr 2
  rw [beWordAt_three_of_lt_pow16 hi, beWordAt_two_of_lt (by omega)]
  unfold a1Hi
  omega

/-! ## A FORS tree -/

/-- **The statement's FORS tree over cells**: an opening whose secret and siblings are cells'
values reaches `fRootE`'s root, at the address cells of `K_0(idx)`. -/
theorem forsTreeRecover_cells (pp a0 secret : E) (idx : Index) (c : ForsTreeIndex)
    (leaf : ForsLeafIndex) (opening : ForsTreeOpening) (sib : Nat → E)
    (ha0 : a0 = adrsCell0 0 (treeOfIndex 0 idx).val)
    (hsec : opening.secret = cellVal secret)
    (hsib : ∀ z : Fin forsTreeHeight, opening.path z = cellVal (sib z.val)) :
    Id.run (forsTreeRecover (m := Id) keccakF1600 (cellVal pp) idx c leaf opening) =
      cellVal (fRootE pp a0 (adrsCell1 3 (leafOfIndex 0 idx).val 0 0) c.val leaf.val secret sib) := by
  have hc : c.val < 24 := c.isLt
  have hs : leaf.val < 2 ^ 10 := leaf.isLt
  have hfold : ∀ k ≤ 10,
      Id.run (foldPath (fun level node => tweakableHash (m := Id) keccakF1600 (cellVal pp)
          (.forsNode idx c (level + 1) node)) leaf.val
          (fun level => if h : level < forsTreeHeight then opening.path ⟨level, h⟩ else 0) k
          (cellVal (fLeafE pp a0 (adrsCell1 3 (leafOfIndex 0 idx).val 0 0) c.val leaf.val secret))) =
        cellVal (pFold (fNodeE pp a0 (adrsCell1 3 (leafOfIndex 0 idx).val 0 0) c.val leaf.val sib) k
          (fLeafE pp a0 (adrsCell1 3 (leafOfIndex 0 idx).val 0 0) c.val leaf.val secret)) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      simp only [foldPath, Id.run_bind] at ih ⊢
      rw [ih (by omega), pFold, fNodeE, fAdrE_eq hc (by omega) hs]
      have hp : (if h : k < forsTreeHeight then opening.path ⟨k, h⟩ else 0) = cellVal (sib k) := by
        rw [dite_eq_left (show k < forsTreeHeight by simp [forsTreeHeight]; omega)]
        exact hsib ⟨k, by simp [forsTreeHeight]; omega⟩
      rw [hp, Nat.shiftRight_eq_div_pow]
      by_cases hb : leaf.val.testBit k
      · simp only [hb, ↓reduceIte, mPair]
        rw [nodePayload_cellVal, tweakableHash_sphincsCells, ha0]
        rfl
      · simp only [hb, ↓reduceIte, mPair, Bool.false_eq_true]
        rw [nodePayload_cellVal, tweakableHash_sphincsCells, ha0]
        rfl
  unfold forsTreeRecover forsLeafHash
  simp only [Id.run_bind]
  rw [hsec, digest_cells, tweakableHash_sphincsCells]
  have hl : (hcell ([pp, (hashDomainCells (.forsLeaf idx c leaf)).1,
      (hashDomainCells (.forsLeaf idx c leaf)).2] ++ [secret])).1 =
      fLeafE pp a0 (adrsCell1 3 (leafOfIndex 0 idx).val 0 0) c.val leaf.val secret := by
    rw [fLeafE, fAdrE_eq hc (by norm_num) hs, ha0]
    rfl
  rw [hl]
  exact hfold 10 le_rfl

/-! ## Positions -/

/-- Where `sForsLevels … c m z x` hints level `j`'s children. -/
def sForsPos (c : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, x, _ => x
  | m + 1, z, x, j => if j = z then x else sForsPos c m (z + 1) (x + forsLevelWidth c z) j

variable {rd : Reader} {σ : Val}

/-- `sForsSib`'s siblings, at `sForsPos`. -/
theorem sForsSib_eq (bit : Nat → V) (c : Nat) :
    ∀ (m z x j : Nat), z ≤ j → j < z + m →
      sForsSib σ bit c m z x j = siblingOf σ (bit (10 * c + j)) (sForsPos c m z x j)
  | 0, _, _, _, _, h => absurd h (by omega)
  | m + 1, z, x, j, h1, h2 => by
      by_cases hj : j = z
      · subst hj; simp [sForsSib, sForsPos]
      · simp only [sForsSib, sForsPos, hj, ↓reduceIte]
        exact sForsSib_eq bit c m (z + 1) (x + forsLevelWidth c z) j (by omega) (by omega)

/-- The FORS siblings at `SphincsSig`'s positions. -/
theorem sForsPos_kid : ∀ c < 24, ∀ z < 10,
    sForsPos c 10 0 (forsTreeBase 1382 c + forsLeafWidth c) z = sForsKid c z := by decide +kernel

/-- The FORS secrets at `SphincsSig`'s positions. -/
theorem forsTreeBase_eq : ∀ c < 24, forsTreeBase 1382 c = sForsBase c := by decide +kernel

/-- The FORS key's output. -/
theorem sForsB_out : sForsB.2.2 = 5248 := by decide +kernel

/-! ## The FORS key -/

/-- **The FORS key over cells**: at the digest `T`'s leaves, the FORS key is the `hcell` of `P`,
`A0`, `key + FORS_ROOTS` and the trees' roots `fRootE`. -/
theorem forsKey_cells (hp : PadOK σ sPad) {T : Nat} (hD : DigestAt σ T) (h : AtomsHold rd σ sForsB.1) :
    σ sForsPk = (hcell ([σ sPP, σ sA0B, σ sKeyB + lit (4 * 2 ^ 24)] ++ (List.range 24).map fun c =>
      fRootE (σ sPP) (σ sA0B) (σ sKeyB + lit (3 * 2 ^ 24)) c (forsLeafN T c)
        (σ (.n (forsTreeBase 1382 c))) (forsSib σ sForsBit 1382 c))).1 := by
  have hbit : ∀ c < 24, ∀ z < 10,
      σ (sForsBit (10 * c + z)) = if (forsLeafN T c).testBit z then 1 else 0 := by
    intro c hc z hz
    have e : sForsBit (10 * c + z) = sMdBit (10 * c + 9 - z) := by
      unfold sForsBit; congr 1; omega
    rw [e, hD.mdBit (by omega), testBit_forsLeafN]
    simp only [hz, decide_true, Bool.true_and]
    rfl
  have hval : ∀ c < 24, ∀ j < 10, σ (sVals (10 * c + j)) = eOfNat (fIdx c j (forsLeafN T c)) := by
    intro c hc j hj
    have e : sVals (10 * c + j) = sFVal c j := by
      unfold sVals; congr 1 <;> omega
    rw [e]
    exact hD.2.2.1 c hc j hj
  have hout : sForsPk = .n (sForsBlock sPad sPP sA0B sKeyB sForsBit sVals 1382).2.2 := by
    rw [show (sForsBlock sPad sPP sA0B sKeyB sForsBit sVals 1382).2.2 = sForsB.2.2 from rfl, sForsB_out]
    rfl
  rw [hout]
  exact sForsBlock_sound (rd := rd) hp (pp := sPP) (a0 := sA0B) (key := sKeyB) (bit := sForsBit)
    (val := sVals) (b0 := 1382) (s := fun c => forsLeafN T c) (fun c _ => forsLeafN_lt T c) hbit hval h

/-- `fors_pkFromSig` in `Id`: `T_k` of the trees' roots. -/
theorem forsRecover_id (P : PublicParameter) (idx : Index) (leaves : ForsTreeIndex → ForsLeafIndex)
    (opening : ForsTreeIndex → ForsTreeOpening) :
    Id.run (forsRecover (m := Id) keccakF1600 P idx leaves opening) =
      Id.run (forsPublicKey (m := Id) keccakF1600 P idx fun c =>
        Id.run (forsTreeRecover (m := Id) keccakF1600 P idx c (leaves c) (opening c))) := by
  unfold forsRecover
  rw [Id.run_bind, sequenceFin_id]
  rfl

/-- **The FORS key, sound**: at the digest `T`'s index and leaves, with the bottom key's address
cells, the FORS key at `fors_pk` is the statement's `fors_pkFromSig` of the openings
`sForsOpeningOf` reads. -/
theorem forsKey_sound (hp : PadOK σ sPad) {T : Nat} (hD : DigestAt σ T)
    (hA0 : σ sA0B = adrsCell0 0 (layerTreeN T 0))
    (hK : σ sKeyB = adrsCell1 0 (layerLeafN T 0) 0 0) (h : AtomsHold rd σ sForsB.1) :
    cellVal (σ sForsPk) = Id.run (forsRecover (m := Id) keccakF1600 (cellVal (σ sPP))
      (digestIndex (digestOf T)) (digestForsLeaves (digestOf T)) fun c => sForsOpeningOf σ c.val) := by
  have hT := hD.1
  have h0 : (treeOfIndex 0 (digestIndex (digestOf T))).val = layerTreeN T 0 := treeOfIndex_digest hT 0
  have h1 : (leafOfIndex 0 (digestIndex (digestOf T))).val = layerLeafN T 0 := leafOfIndex_digest hT 0
  have hA3 : σ sKeyB + lit (3 * 2 ^ 24) =
      adrsCell1 3 (leafOfIndex 0 (digestIndex (digestOf T))).val 0 0 := by
    rw [hK, h1, lit_of_lt (by norm_num)]
    exact adrsCell1_add_type (by norm_num)
  have hA4 : σ sKeyB + lit (4 * 2 ^ 24) =
      adrsCell1 4 (leafOfIndex 0 (digestIndex (digestOf T))).val 0 0 := by
    rw [hK, h1, lit_of_lt (by norm_num)]
    exact adrsCell1_add_type (by norm_num)
  have hroot : ∀ c : ForsTreeIndex,
      Id.run (forsTreeRecover (m := Id) keccakF1600 (cellVal (σ sPP)) (digestIndex (digestOf T)) c
          (digestForsLeaves (digestOf T) c) (sForsOpeningOf σ c.val)) =
        cellVal (fRootE (σ sPP) (σ sA0B) (σ sKeyB + lit (3 * 2 ^ 24)) c.val (forsLeafN T c.val)
          (σ (.n (forsTreeBase 1382 c.val))) (forsSib σ sForsBit 1382 c.val)) := by
    intro c
    have hc : c.val < 24 := c.isLt
    rw [forsTreeRecover_cells (σ sPP) (σ sA0B) (σ (.n (forsTreeBase 1382 c.val)))
      (digestIndex (digestOf T)) c (digestForsLeaves (digestOf T) c) (sForsOpeningOf σ c.val)
      (forsSib σ sForsBit 1382 c.val) (by rw [hA0, h0])
      (by rw [forsTreeBase_eq c.val hc]; rfl)
      (fun z => by
        have hz : z.val < 10 := z.isLt
        rw [forsSib, sForsSib_eq sForsBit c.val 10 0 _ z.val (by omega) (by omega),
          sForsPos_kid c.val hc z.val hz]
        rfl), ← hA3, digestForsLeaves_val hT c]
  rw [forsRecover_id]
  simp only [hroot]
  unfold forsPublicKey
  rw [digestsPayload_cells, tweakableHash_sphincsCells, forsKey_cells hp hD h]
  have hcells : hashDomainCells (.forsRoots (digestIndex (digestOf T))) =
      (σ sA0B, σ sKeyB + lit (4 * 2 ^ 24)) := by
    rw [hA4, hA0, ← h0]
    rfl
  rw [hcells, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

end
end LeanVM.Guest.B1.Sig
