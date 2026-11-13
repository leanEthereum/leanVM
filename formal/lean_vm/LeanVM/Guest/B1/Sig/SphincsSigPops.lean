/-
  LeanVM.Guest.B1.Sig.SphincsSigPops

  The witness-stream entries `verify_sig_lean_sphincs` (`lean_ethereum.py:4143-4244`) pops, its three `sp_wots` calls' spliced in, are the honest hint generator's pushes for the signature (`Hints.sphincsHints`), stream by stream.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsComplete
public import LeanVM.Guest.B1.Sig.SphincsCompleteConv
public import LeanVM.Guest.B1.Sig.SpWotsPops
public import LeanVM.Guest.Hints
import LeanVM.Protocol.Verifier.Load

/-!
# A leanSPHINCS signature's pops are its hints

* `sphincsHints_eq`, `unusedEntry_eq`: the hint generator's digest is the statement's, its unused bytes `spUnusedN`'s;
* `forsPops_sameStreams`: FORS's entries are the secrets' then the climbs' pushes, stream by stream;
* `layerPops_sameStreams`: a layer's entries, its `sp_wots` call's spliced in, are `sphincsLayer`'s pushes, stream by stream;
* `spSegPops`, `spSegPops_sameStreams`: the body's entries are `sphincsHints`';
* `verify_lean_sphincs_complete_pops`: the statements before the root's check complete popping, on every valuation agreeing below their end, `spSegPops pk m sig` with the three `sp_wots` calls' entries `spKids pk m sig` spliced in, which are `sphincsHints pk m sig`, stream by stream.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (eOfNat kToNat)
open HashSig HashSig.OverPermutation

@[expose] public section

/-! ## Cells and words -/

theorem spCellOfBytes_cellBytes (x : E) : Hints.cellOfBytes (cellBytes x) = x := by
  have hl : ∀ a : K, (K.toBytes a).length = 8 := fun a => by
    simp [K.toBytes, LeanVM.Protocol.KeccakHash.wordBytes]
  conv_rhs => rw [eq_ofLimbs x]
  rw [Hints.cellOfBytes, cellBytes, LeanVM.Protocol.Verifier.kOfBytes_kBytes_append, List.drop_left' (hl _),
    ← List.append_nil (K.toBytes (x.limb 1)), LeanVM.Protocol.Verifier.kOfBytes_kBytes_append]

/-- The hint generator's cell of a 128-bit value is the guest's. -/
theorem spCell128_eq (v : BitVec 128) : Hints.cell128 v = cellOf128 v := by
  conv_lhs => rw [← cellVal_cellOf128 v]
  rw [Hints.cell128, bytesLE_cellVal, spCellOfBytes_cellBytes]

theorem spCount_eq {n : Nat} (h : n < 2 ^ 64) : Hints.count n = ofK (addressOfIndex n) := by
  rw [Hints.count, gpowE, gpowK_eq (by unfold u128Bound; omega)]

/-! ## The digest -/

/-- The hint generator's `H_msg` outputs. -/
abbrev spOutputs (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    Sphincs.DigestCall → HashSig.HashOutput :=
  fun call => Id.run (Sphincs.Verification.messageDigestCall (m := Id) keccakF1600 sig.randomizer
    pk.publicSeed pk.root m call)

theorem sDigestOf_eq_outputs (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    sDigestOf pk m sig = Sphincs.truncateMessageDigest (spOutputs pk m sig) := by
  simp only [sDigestOf, Sphincs.Verification.messageDigest, Id.run, bind, pure, sequenceFin_id]
  rfl

theorem messageDigestCall_toNat (R seed root : E) (msg : HashSig.Message) (c : Sphincs.DigestCall) :
    (Id.run (Sphincs.Verification.messageDigestCall (m := Id) keccakF1600 (cellVal R) (cellVal seed)
        (cellVal root) msg c)).toNat =
      cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c.val))).1 +
        2 ^ 128 * cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c.val))).2 := by
  simp only [Sphincs.Verification.messageDigestCall, keccakHash_keccakF1600, Id.run]
  rw [hmsgBytes_eq, keccakBits_toNat]

/-- **The unused bytes' entry** is `spUnusedN`'s bytes, each in the exponent. -/
theorem unusedEntry_eq (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    Hints.sphincsUnusedEntry (spOutputs pk m sig) =
      (List.range 6).map fun j => ofK (addressOfIndex (spUnusedN pk m sig.randomizer / 256 ^ j % 256)) := by
  have hc : ∀ c : Sphincs.DigestCall, (spOutputs pk m sig c).toNat =
      cellNat (digestHalves (keccak256 (hmsgBytes (cellOf128 sig.randomizer) (cellOf128 pk.publicSeed)
        (cellOf128 pk.root) m.toNat c.val))).1 +
      2 ^ 128 * cellNat (digestHalves (keccak256 (hmsgBytes (cellOf128 sig.randomizer)
        (cellOf128 pk.publicSeed) (cellOf128 pk.root) m.toNat c.val))).2 := fun c => by
    have := messageDigestCall_toNat (cellOf128 sig.randomizer) (cellOf128 pk.publicSeed) (cellOf128 pk.root) m c
    have e1 : cellVal (cellOf128 sig.randomizer) = sig.randomizer := cellVal_cellOf128 _
    have e2 : cellVal (cellOf128 pk.publicSeed) = pk.publicSeed := cellVal_cellOf128 _
    have e3 : cellVal (cellOf128 pk.root) = pk.root := cellVal_cellOf128 _
    rw [e1, e2, e3] at this
    exact this
  generalize spOutputs pk m sig = O at hc ⊢
  have hv : Sphincs.digestValue O = (O 0).toNat * 2 ^ (256 * 0) + (O 1).toNat * 2 ^ (256 * 1) := by
    unfold Sphincs.digestValue
    exact Fin.sum_univ_two (f := fun c : Fin 2 => (O c).toNat * 2 ^ (256 * c.val))
  have h0 := hc 0
  have h1 := hc 1
  rw [show (0 : Sphincs.DigestCall).val = 0 from rfl] at h0
  rw [show (1 : Sphincs.DigestCall).val = 1 from rfl] at h1
  unfold Hints.sphincsUnusedEntry
  refine List.map_congr_left fun j hj => ?_
  have hj6 := List.mem_range.mp hj
  rw [spCount_eq (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))]
  suffices h : Sphincs.digestValue O / 2 ^ (8 * (34 + j)) % 256 = spUnusedN pk m sig.randomizer / 256 ^ j % 256 by
    rw [h]
  rw [hv, spUnusedN, unusedOf]
  generalize digestHalves (keccak256 (hmsgBytes (cellOf128 sig.randomizer) (cellOf128 pk.publicSeed)
    (cellOf128 pk.root) m.toNat 1)) = d1 at h1 ⊢
  generalize digestHalves (keccak256 (hmsgBytes (cellOf128 sig.randomizer) (cellOf128 pk.publicSeed)
    (cellOf128 pk.root) m.toNat 0)) = d0 at h0 ⊢
  have a0 := cellNat_lt d0.1
  have b0 := cellNat_lt d0.2
  have b1 := cellNat_lt d1.2
  have l0 := kToNat_lt (d1.1.limb 0)
  have l1 := kToNat_lt (d1.1.limb 1)
  have e1 : cellNat d1.1 = kToNat (d1.1.limb 0) + 2 ^ 64 * kToNat (d1.1.limb 1) := rfl
  rw [h0, h1, e1]
  have hX : ∀ x y : Nat, x < 2 ^ 256 → (x * 2 ^ (256 * 0) + y * 2 ^ (256 * 1)) / 2 ^ (8 * (34 + j)) =
      y / 2 ^ (16 + 8 * j) := by
    intro x y hx
    rw [show 8 * (34 + j) = 256 + (16 + 8 * j) by omega, pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_zero,
      pow_zero, Nat.mul_one, Nat.mul_one, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hx,
      Nat.zero_add]
  rw [hX _ _ (by
    have : cellNat d0.1 + 2 ^ 128 * cellNat d0.2 < 2 ^ 128 + 2 ^ 128 * (2 ^ 128 - 1) := by omega
    calc cellNat d0.1 + 2 ^ 128 * cellNat d0.2 < 2 ^ 128 + 2 ^ 128 * (2 ^ 128 - 1) := this
      _ = 2 ^ 256 := by norm_num)]
  generalize cellNat d0.1 = A0 at *
  generalize cellNat d0.2 = B0 at *
  generalize cellNat d1.2 = B1 at *
  generalize kToNat (d1.1.limb 0) = L0 at *
  generalize kToNat (d1.1.limb 1) = L1 at *
  interval_cases j <;> norm_num <;> omega

/-! ## FORS -/

theorem pairPop_ordered (name : String) (b : Bool) (v w : BitVec 128) :
    pairPop name b (cellOf128 v) (cellOf128 w) = (name, Hints.ordered b v w) := by
  cases b <;> simp [pairPop, mPair, Hints.ordered, spCell128_eq]

/-- **A FORS tree's fold over cells**, `j ≤ 10` levels: the value of `pFold` of `fNodeE` from `fLeafE`. -/
theorem forsFold_cells (pp : E) (idx : Sphincs.Index) (c : Sphincs.ForsTreeIndex) (s : Sphincs.ForsLeafIndex)
    (op : Sphincs.ForsTreeOpening) {secret : E} {sib : Nat → E} (hsec : cellVal secret = op.secret)
    (hsib : ∀ z (hz : z < 10), cellVal (sib z) = op.path ⟨z, hz⟩) {j : Nat} (hj : j ≤ 10) :
    Id.run (foldPath (m := Id) (fun level node => Sphincs.Verification.tweakableHash (m := Id) keccakF1600
        (cellVal pp) (.forsNode idx c (level + 1) node)) s.val
      (fun level => if h : level < Sphincs.forsTreeHeight then op.path ⟨level, h⟩ else 0) j
      (Id.run (Sphincs.Verification.forsLeafHash (m := Id) keccakF1600 (cellVal pp) idx c s op.secret))) =
    cellVal (pFold (fNodeE pp (adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val)
        (adrsCell1 3 (Sphincs.leafOfIndex 0 idx).val 0 0) c.val s.val sib) j
      (fLeafE pp (adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val) (adrsCell1 3 (Sphincs.leafOfIndex 0 idx).val 0 0)
        c.val s.val secret)) := by
  have hc : c.val < 24 := c.isLt
  have hs : s.val < 2 ^ 10 := s.isLt
  have hleaf : Id.run (Sphincs.Verification.forsLeafHash (m := Id) keccakF1600 (cellVal pp) idx c s
      op.secret) = cellVal (fLeafE pp (adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val)
        (adrsCell1 3 (Sphincs.leafOfIndex 0 idx).val 0 0) c.val s.val secret) := by
    rw [fLeafE, fAdrE_eqC hc (by norm_num) hs, ← hsec]
    show Sphincs.Verification.tweakableHash (m := Id) keccakF1600 (cellVal pp)
      (.forsLeaf idx c s) (littleEndianBytes 16 (cellVal secret)) = _
    rw [digest_cells, tweakableHash_sphincsCells]
    simp only [forsAdrCell, hashDomainCells, Sphincs.forsTreeIndex, Sphincs.forsTreeHeight,
      Nat.shiftRight_zero]
    rfl
  rw [hleaf]
  refine (foldPath_cells pp (adrsCell0 0 (Sphincs.treeOfIndex 0 idx).val)
    (fun level q => .forsNode idx c (level + 1) q)
    (fun l => forsAdrCell (Sphincs.leafOfIndex 0 idx).val c.val (l + 1) s.val) s.val j
    (fun l _ => by
      simp only [hashDomainCells, forsAdrCell, Sphincs.forsTreeIndex, Sphincs.forsTreeHeight,
        Nat.shiftRight_eq_div_pow])
    (fun l hl => by
      show cellVal (sib l) = if h : l < 10 then op.path ⟨l, h⟩ else 0
      simp only [show l < 10 by omega, ↓reduceDIte]; exact hsib l (by omega)) _).trans ?_
  refine congrArg cellVal (pFold_congr_lt _ _ j _ fun z hz => funext fun v => ?_)
  rw [fNodeE, fAdrE_eqC hc (by omega) hs]

/-- The hint generator's digest. -/
abbrev spDigest (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) : Sphincs.MessageDigest :=
  Sphincs.truncateMessageDigest (spOutputs pk m sig)

theorem forsSecretCell_val (sig : Sphincs.Signature) (c : Sphincs.ForsTreeIndex) :
    forsSecretCell sig c.val = cellOf128 (sig.forsOpening c).secret := by
  have hc : c.val < 24 := c.isLt
  simp only [forsSecretCell, hc, ↓reduceDIte]

theorem forsSibCell_val (sig : Sphincs.Signature) (c : Sphincs.ForsTreeIndex) (z : Nat) :
    forsSibCell sig c.val z = cellOf128 (if h : z < Sphincs.forsTreeHeight then (sig.forsOpening c).path ⟨z, h⟩
      else 0) := by
  have hc : c.val < 24 := c.isLt
  simp only [forsSibCell, hc, ↓reduceDIte]
  rfl

/-- **A FORS tree's climb** is the hint generator's. -/
theorem forsClimb_eq (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (c : Sphincs.ForsTreeIndex) :
    climbPops "sp_fors_nodes" (fNodeE (cellOf128 pk.publicSeed) (adrsCell0 0 (layerTreeN (digestT pk m sig) 0))
        (adrsCell1 3 (layerLeafN (digestT pk m sig) 0) 0 0) c.val (forsLeafN (digestT pk m sig) c.val)
        (forsSibCell sig c.val)) (forsLeafN (digestT pk m sig) c.val).testBit (forsSibCell sig c.val) 10 0
      (fLeafE (cellOf128 pk.publicSeed) (adrsCell0 0 (layerTreeN (digestT pk m sig) 0))
        (adrsCell1 3 (layerLeafN (digestT pk m sig) 0) 0 0) c.val (forsLeafN (digestT pk m sig) c.val)
        (forsSecretCell sig c.val)) =
    Hints.sphincsForsNodes pk.publicSeed (Sphincs.digestIndex (spDigest pk m sig)) c
      (Sphincs.digestForsLeaves (spDigest pk m sig) c) (sig.forsOpening c) := by
  have hT := digestT_lt pk m sig
  have hD : spDigest pk m sig = digestOf (digestT pk m sig) := by
    show Sphincs.truncateMessageDigest (spOutputs pk m sig) = _
    rw [← sDigestOf_eq_outputs, sDigestOf_eq]
  have hl : (Sphincs.digestForsLeaves (spDigest pk m sig) c).val = forsLeafN (digestT pk m sig) c.val := by
    rw [hD]; exact digestForsLeaves_val hT c
  have hi : Sphincs.digestIndex (spDigest pk m sig) = digestIdx pk m sig := by
    show _ = Sphincs.digestIndex (sDigestOf pk m sig)
    rw [sDigestOf_eq_outputs]
  have e0 : (Sphincs.treeOfIndex 0 (Sphincs.digestIndex (spDigest pk m sig))).val = layerTreeN (digestT pk m sig) 0 := by
    rw [hi]; exact treeOf_idx pk m sig 0
  have e1 : (Sphincs.leafOfIndex 0 (Sphincs.digestIndex (spDigest pk m sig))).val = layerLeafN (digestT pk m sig) 0 := by
    rw [hi]; exact leafOf_idx pk m sig 0
  have hsec : cellVal (forsSecretCell sig c.val) = (sig.forsOpening c).secret := by
    rw [forsSecretCell_val]; exact cellVal_cellOf128 _
  have hsib : ∀ z (hz : z < 10), cellVal (forsSibCell sig c.val z) = (sig.forsOpening c).path ⟨z, hz⟩ := by
    intro z hz
    rw [forsSibCell_val]
    simp only [show z < Sphincs.forsTreeHeight from hz, ↓reduceDIte]
    exact cellVal_cellOf128 _
  rw [climbPops_eq]
  unfold Hints.sphincsForsNodes
  refine List.map_congr_left fun j hj => ?_
  dsimp only
  have hj10 := List.mem_range.mp hj
  have hf := forsFold_cells (cellOf128 pk.publicSeed) (Sphincs.digestIndex (spDigest pk m sig)) c
    (Sphincs.digestForsLeaves (spDigest pk m sig) c) (sig.forsOpening c) hsec hsib (j := j) (by omega)
  have ep : cellVal (cellOf128 pk.publicSeed) = pk.publicSeed := cellVal_cellOf128 _
  rw [ep, hl, e0, e1] at hf
  rw [Nat.zero_add, nIter_zero, ← cellOf128_cellVal (pFold _ _ _), ← hf, forsSibCell_val, hl]
  exact pairPop_ordered _ _ _ _

/-! ## Lists -/

theorem mem_climbPops {name : String} {node : Nat → E → E} {bt : Nat → Bool} {sib : Nat → E} {m z : Nat} {v : E}
    {q : Pop} (h : q ∈ climbPops name node bt sib m z v) : q.1 = name := by
  rw [climbPops_eq] at h
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
  rfl

theorem flatMap_range_finRange {α : Type} (n : Nat) (f : Nat → List α) :
    (List.range n).flatMap f = (List.finRange n).flatMap fun c => f c.val := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]

theorem append_eq_append_left {α : Type} {a b c : List α} (h : b = c) : a ++ b = a ++ c := h ▸ rfl

theorem flatMap_singleton' {α β : Type} (l : List α) (f : α → β) : l.flatMap (fun x => [f x]) = l.map f := by
  induction l <;> simp_all

/-- **FORS's entries are the secrets' then the climbs' pushes**, stream by stream. -/
theorem forsPops_sameStreams (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    SameStreams (forsPops (cellOf128 pk.publicSeed) (adrsCell0 0 (layerTreeN (digestT pk m sig) 0))
        (layerLeafN (digestT pk m sig) 0) (forsLeafN (digestT pk m sig)) (forsSecretCell sig) (forsSibCell sig))
      ((List.finRange Sphincs.forsTreeCount).map (fun c => ("sp_fors_secrets", [Hints.cell128 (sig.forsOpening c).secret])) ++
        (List.finRange Sphincs.forsTreeCount).flatMap fun c => Hints.sphincsForsNodes pk.publicSeed
          (Sphincs.digestIndex (spDigest pk m sig)) c (Sphincs.digestForsLeaves (spDigest pk m sig) c)
          (sig.forsOpening c)) := by
  have hs := sameStreams_flatMap_split
    (fun c => [(("sp_fors_secrets" : String), [forsSecretCell sig c])])
    (fun c => climbPops "sp_fors_nodes" (fNodeE (cellOf128 pk.publicSeed)
        (adrsCell0 0 (layerTreeN (digestT pk m sig) 0)) (adrsCell1 3 (layerLeafN (digestT pk m sig) 0) 0 0) c
        (forsLeafN (digestT pk m sig) c) (forsSibCell sig c)) (forsLeafN (digestT pk m sig) c).testBit
      (forsSibCell sig c) 10 0 (fLeafE (cellOf128 pk.publicSeed) (adrsCell0 0 (layerTreeN (digestT pk m sig) 0))
        (adrsCell1 3 (layerLeafN (digestT pk m sig) 0) 0 0) c (forsLeafN (digestT pk m sig) c) (forsSecretCell sig c)))
    (fun x y p hp q hq => by
      rw [List.mem_singleton] at hp
      rw [hp, mem_climbPops hq]
      exact (by decide : ("sp_fors_secrets" : String) ≠ "sp_fors_nodes")) (List.range 24)
  have e1 : ((List.range 24).flatMap fun c => [(("sp_fors_secrets" : String), [forsSecretCell sig c])]) =
      (List.finRange Sphincs.forsTreeCount).map
        (fun c => ("sp_fors_secrets", [Hints.cell128 (sig.forsOpening c).secret])) := by
    rw [flatMap_range_finRange, flatMap_singleton']
    exact List.map_congr_left fun c _ =>
      congrArg (fun x => (("sp_fors_secrets" : String), [x])) ((forsSecretCell_val sig c).trans (spCell128_eq _).symm)
  have e2 := flatMap_range_finRange 24 (fun c => climbPops "sp_fors_nodes" (fNodeE (cellOf128 pk.publicSeed)
        (adrsCell0 0 (layerTreeN (digestT pk m sig) 0)) (adrsCell1 3 (layerLeafN (digestT pk m sig) 0) 0 0) c
        (forsLeafN (digestT pk m sig) c) (forsSibCell sig c)) (forsLeafN (digestT pk m sig) c).testBit
      (forsSibCell sig c) 10 0 (fLeafE (cellOf128 pk.publicSeed) (adrsCell0 0 (layerTreeN (digestT pk m sig) 0))
        (adrsCell1 3 (layerLeafN (digestT pk m sig) 0) 0 0) c (forsLeafN (digestT pk m sig) c) (forsSecretCell sig c)))
  rw [e1, e2] at hs
  refine hs.trans (SameStreams.of_eq (append_eq_append_left ?_))
  exact List.flatMap_congr fun c _ => forsClimb_eq pk m sig c


/-! ## A layer -/

theorem counterPop_eq (ctr : Sphincs.EncodingCounter) :
    counterPop ctr.toNat = ("sp_counter", Hints.sphincsCounterEntry ctr) := by
  have hl : (Sphincs.bigEndianBytes 4 ctr).length = 4 := length_bigEndianBytes 4 ctr
  unfold counterPop Hints.sphincsCounterEntry Hints.exponentBytes
  refine congrArg (fun x => (("sp_counter" : String), x)) (List.ext_getElem
    (by rw [List.length_map, List.length_map, List.length_range, hl]) fun k h1 h2 => ?_)
  have hk : k < 4 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  have hb := toNat_getElem_bigEndianBytes 4 ctr k (by rw [hl]; exact hk)
  rw [spCount_eq (lt_of_lt_of_le (UInt8.toNat_lt _) (by norm_num)), hb, beDigit _ _ hk]
  rfl

theorem sp_take_drop_map_range {α : Type} (d : Nat → α) (a j n : Nat) :
    (((List.range n).map d).drop a).take j = (List.range' a (min j (n - a))).map d := by
  have ht : ∀ m, List.take j (List.range' a m) = List.range' a (min j m) := fun m =>
    List.ext_getElem (by simp) (fun _ _ _ => by simp [List.getElem_range'])
  rw [← List.map_drop, List.range_eq_range', List.drop_range', Nat.zero_add, Nat.mul_one, ← List.map_take, ht]

theorem sp_foldr_digits (N : Nat) : ∀ j a, ((List.range' a j).map fun i => N / 4 ^ i % 4).foldr (· + 4 * ·) 0 =
    N / 4 ^ a % 4 ^ j
  | 0, a => by simp [Nat.mod_one]
  | j + 1, a => by
      rw [List.range'_succ, List.map_cons, List.foldr_cons, sp_foldr_digits N j (a + 1),
        show N / 4 ^ (a + 1) = N / 4 ^ a / 4 by rw [pow_succ, Nat.div_div_eq_div_mul],
        show (4 : Nat) ^ (j + 1) = 4 * 4 ^ j from pow_succ' 4 j, Nat.mod_mul]

/-- **The digit words' pushes** are the groups' words of the digits. -/
theorem digitGroups_eq {d : Nat → Nat} (hd : ∀ i, d i < 4) :
    Hints.digitGroups ((List.range 64).map d) =
      (List.range 22).map fun q => ("digits", [ofK (addressOfIndex (spK d q))]) := by
  unfold Hints.digitGroups Hints.digitHints
  simp only [List.length_map, List.length_range, List.map_map]
  refine List.map_congr_left fun q hq => ?_
  have hq' : q < 22 := List.mem_range.mp hq
  simp only [Function.comp_apply, Hints.digitGroup]
  rw [sp_take_drop_map_range]
  have hm : ∀ i ∈ List.range' (3 * q) (min 3 (64 - 3 * q)), d i = spDn d / 4 ^ i % 4 := fun i hi => by
    rw [List.mem_range'] at hi
    exact (spDn_digit hd (by omega)).symm
  rw [List.map_congr_left hm, sp_foldr_digits, show min 3 (64 - 3 * q) = spN q by unfold spN; split <;> omega]
  have hk := spK_lt d q
  rw [show spDn d / 4 ^ (3 * q) % 4 ^ spN q = spK d q from rfl,
    spCount_eq (lt_of_lt_of_le hk (by unfold spN; split <;> norm_num))]

theorem chainIdx_flatMap {α : Type} (F : Nat → α) :
    (List.range 22).flatMap (fun q => (List.range (spN q)).map fun t => F (3 * q + t)) = (List.range 64).map F := by
  have h : (List.range 22).flatMap (fun q => (List.range (spN q)).map fun t => 3 * q + t) = List.range 64 := by
    decide
  rw [← h, List.map_flatMap]
  simp only [List.map_map, Function.comp_def]

/-- **`sp_wots`'s entries are its digit words' pushes, then its starts'**, stream by stream. -/
theorem spWotsPops_sameStreams (digest : HashSig.Digest) (values : Sphincs.ChainIndex → HashSig.Digest) :
    SameStreams (spWotsPops digest values)
      (Hints.digitGroups ((List.range 64).map (spDigitsOf digest)) ++
        (List.range 64).map fun i => startPop (spValsOf values i)) := by
  have hs := sameStreams_flatMap_split
    (fun q => [(("digits" : String), [ofK (addressOfIndex (spK (spDigitsOf digest) q))])])
    (fun q => (List.range (spN q)).map fun t => startPop (spValsOf values (3 * q + t)))
    (fun x y p hp q hq => by
      rw [List.mem_singleton] at hp
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hq
      rw [hp]
      exact (by decide : ("digits" : String) ≠ "chain_starts")) (List.range 22)
  rw [flatMap_singleton', chainIdx_flatMap (fun i => startPop (spValsOf values i)),
    ← digitGroups_eq (spDigitsOf_lt digest)] at hs
  exact hs

theorem finRange_map_val {α : Type} (n : Nat) (f : Nat → α) :
    (List.finRange n).map (fun i => f i.val) = (List.range n).map f := by
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-- The hint generator's layer, its parts named. -/
theorem sphincsLayer_eq (pp : HashSig.PublicParameter) (idx : Sphincs.Index) (sig : Sphincs.Signature)
    (L : Sphincs.Layer) (signed : HashSig.Digest) :
    Hints.sphincsLayer pp idx sig L signed =
      ([("sp_counter", Hints.sphincsCounterEntry (sig.layers L).counter)] ++
        Hints.digitGroups ((List.finRange Sphincs.chainCount).map fun i =>
          ((Id.run (Sphincs.Verification.encode (m := Id) keccakF1600 pp L (Sphincs.treeOfIndex L idx)
            (Sphincs.leafOfIndex L idx) signed (sig.layers L).counter)).map (· i |>.val)).getD 0) ++
        (List.finRange Sphincs.chainCount).map (fun i => ("chain_starts", [Hints.cell128 ((sig.layers L).chainValues i)])) ++
        (List.range (Sphincs.layerHeight L)).map (fun l => ("siblings", Hints.ordered
          ((Sphincs.leafOfIndex L idx).val.testBit l)
          (Id.run (Sphincs.Verification.treeFold (m := Id) keccakF1600 pp L (Sphincs.treeOfIndex L idx)
            (Sphincs.leafOfIndex L idx) (Sphincs.Verification.layerPath sig L) l
            ((Id.run (Sphincs.Verification.otsLeaf (m := Id) keccakF1600 pp L (Sphincs.treeOfIndex L idx)
              (Sphincs.leafOfIndex L idx) signed (sig.layers L).counter (sig.layers L).chainValues)).getD 0)))
          (Sphincs.Verification.layerPath sig L l))),
        Id.run (Sphincs.Verification.treeFold (m := Id) keccakF1600 pp L (Sphincs.treeOfIndex L idx)
          (Sphincs.leafOfIndex L idx) (Sphincs.Verification.layerPath sig L) (Sphincs.layerHeight L)
          ((Id.run (Sphincs.Verification.otsLeaf (m := Id) keccakF1600 pp L (Sphincs.treeOfIndex L idx)
            (Sphincs.leafOfIndex L idx) signed (sig.layers L).counter (sig.layers L).chainValues)).getD 0))) :=
  rfl

theorem sHeightOf_val (L : Sphincs.Layer) : sHeightOf L.val = Sphincs.layerHeight L := sHeightOf_eq L.isLt

/-- **A layer's entries, its `sp_wots` call's spliced in, are `sphincsLayer`'s pushes**, stream by stream, and the root it passes up is its root cell's value. -/
theorem layerPops_sameStreams (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (L : Sphincs.Layer) (S : E)
    (hV : Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits
      (cellVal (layerEnc pk (digestIdx pk m sig) sig L S)))) :
    SameStreams (layerPops pk m sig L S (spWotsPops (cellVal (layerEnc pk (digestIdx pk m sig) sig L S))
        (sig.layers L).chainValues))
      (Hints.sphincsLayer pk.publicSeed (digestIdx pk m sig) sig L (cellVal S)).1 ∧
    (Hints.sphincsLayer pk.publicSeed (digestIdx pk m sig) sig L (cellVal S)).2 =
      cellVal (layerRootCell pk (digestIdx pk m sig) sig L S) := by
  have ep : cellVal (cellOf128 pk.publicSeed) = pk.publicSeed := cellVal_cellOf128 _
  -- the encoding and the leaf
  have he := encode_cells (cellOf128 pk.publicSeed) S L (Sphincs.treeOfIndex L (digestIdx pk m sig))
    (Sphincs.leafOfIndex L (digestIdx pk m sig)) (sig.layers L).counter
  have ho := otsLeaf_cells (cellOf128 pk.publicSeed) S L (Sphincs.treeOfIndex L (digestIdx pk m sig))
    (Sphincs.leafOfIndex L (digestIdx pk m sig)) (sig.layers L).counter (sig.layers L).chainValues
  rw [ep] at he ho
  have hE : layerEnc pk (digestIdx pk m sig) sig L S = encDigestCell (cellOf128 pk.publicSeed)
      (adrsCell0 L.val (Sphincs.treeOfIndex L (digestIdx pk m sig)).val)
      (adrsCell1 7 (Sphincs.leafOfIndex L (digestIdx pk m sig)).val 0 0) S
      (eOfNat (beWordAt 0 (sig.layers L).counter.toNat)) := rfl
  rw [← hE] at he ho
  unfold Sphincs.TargetSum.decodeDigest at he
  rw [ite_eq_left hV] at he ho
  have hleaf : wotsLeafOf pk.publicSeed L (Sphincs.treeOfIndex L (digestIdx pk m sig))
      (Sphincs.leafOfIndex L (digestIdx pk m sig)) (cellVal (layerEnc pk (digestIdx pk m sig) sig L S))
      (sig.layers L).chainValues = layerLeaf pk (digestIdx pk m sig) sig L S := rfl
  rw [hleaf] at ho
  -- the folds
  have hfold : ∀ j ≤ 10, Id.run (Sphincs.Verification.treeFold (m := Id) keccakF1600 pk.publicSeed L
      (Sphincs.treeOfIndex L (digestIdx pk m sig)) (Sphincs.leafOfIndex L (digestIdx pk m sig))
      (Sphincs.Verification.layerPath sig L) j (layerLeaf pk (digestIdx pk m sig) sig L S)) =
      cellVal (pFold (pNodeE (cellOf128 pk.publicSeed)
        (adrsCell0 L.val (Sphincs.treeOfIndex L (digestIdx pk m sig)).val)
        (Sphincs.leafOfIndex L (digestIdx pk m sig)).val (layerSibCell sig L)) j
        (cellOf128 (layerLeaf pk (digestIdx pk m sig) sig L S))) := fun j hj => by
    have h := htFold_cells (cellOf128 pk.publicSeed) L (Sphincs.treeOfIndex L (digestIdx pk m sig))
      (Sphincs.leafOfIndex L (digestIdx pk m sig)) (sib := layerSibCell sig L)
      (path := Sphincs.Verification.layerPath sig L) hj (fun z _ => cellVal_cellOf128 _)
      (cellOf128 (layerLeaf pk (digestIdx pk m sig) sig L S))
    have ev : cellVal (cellOf128 (layerLeaf pk (digestIdx pk m sig) sig L S)) =
      layerLeaf pk (digestIdx pk m sig) sig L S := cellVal_cellOf128 _
    rw [ep, ev] at h
    exact h
  have et := treeOf_idx pk m sig L
  have el := leafOf_idx pk m sig L
  rw [sphincsLayer_eq pk.publicSeed (digestIdx pk m sig) sig L (cellVal S), he, ho]
  simp only [Option.getD_some, Option.map_some]
  refine ⟨?_, ?_⟩
  · -- the entries
    have hd : ((List.finRange Sphincs.chainCount).map fun i =>
        (Sphincs.TargetSum.base2bDigits (cellVal (layerEnc pk (digestIdx pk m sig) sig L S)) i).val) =
        (List.range 64).map (spDigitsOf (cellVal (layerEnc pk (digestIdx pk m sig) sig L S))) := by
      rw [← finRange_map_val]
      exact List.map_congr_left fun i _ => spDigitsOf_eq _ i
    have hst : ((List.finRange Sphincs.chainCount).map fun i =>
        (("chain_starts" : String), [Hints.cell128 ((sig.layers L).chainValues i)])) =
        (List.range 64).map fun i => startPop (spValsOf (sig.layers L).chainValues i) := by
      rw [← finRange_map_val]
      refine List.map_congr_left fun i _ => ?_
      have hi : i.val < 64 := i.isLt
      simp only [spValsOf, hi, ↓reduceDIte, startPop]
      exact congrArg (fun x => (("chain_starts" : String), [x])) (spCell128_eq _)
    have hsib : climbPops "siblings" (pNodeE (cellOf128 pk.publicSeed)
        (adrsCell0 L.val (layerTreeN (digestT pk m sig) L.val)) (layerLeafN (digestT pk m sig) L.val)
        (layerSibCell sig L)) (layerLeafN (digestT pk m sig) L.val).testBit (layerSibCell sig L) (sHeightOf L.val) 0
        (cellOf128 (layerLeaf pk (digestIdx pk m sig) sig L S)) =
        (List.range (Sphincs.layerHeight L)).map (fun l => ("siblings", Hints.ordered
          ((Sphincs.leafOfIndex L (digestIdx pk m sig)).val.testBit l)
          (Id.run (Sphincs.Verification.treeFold (m := Id) keccakF1600 pk.publicSeed L
            (Sphincs.treeOfIndex L (digestIdx pk m sig)) (Sphincs.leafOfIndex L (digestIdx pk m sig))
            (Sphincs.Verification.layerPath sig L) l (layerLeaf pk (digestIdx pk m sig) sig L S)))
          (Sphincs.Verification.layerPath sig L l))) := by
      rw [climbPops_eq, sHeightOf_val]
      refine List.map_congr_left fun j hj => ?_
      have hj' : j < Sphincs.layerHeight L := List.mem_range.mp hj
      have hj10 : j ≤ 10 := by have := layerHeight_le L; omega
      rw [Nat.zero_add, nIter_zero, ← et, ← el, ← cellOf128_cellVal (pFold _ _ _), ← hfold j hj10]
      exact pairPop_ordered _ _ _ _
    unfold layerPops
    rw [counterPop_eq, hd, hst, hsib]
    rw [show ∀ (a : Pop) (D St Sib : List Pop), [a] ++ D ++ St ++ Sib = [a] ++ ((D ++ St) ++ Sib) from
      fun _ _ _ _ => by simp only [List.append_assoc]]
    exact (SameStreams.refl [_]).append ((spWotsPops_sameStreams _ _).append (SameStreams.refl _))
  · rw [hfold _ (layerHeight_le L)]
    rfl


/-! ## The signature -/

/-- **`sp_wots`'s entries in layer `L`**, signing the value of `S`: its encoding's digit words and the layer's chain values. -/
def spKid (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) (L : Sphincs.Layer) (S : E) :
    List Pop :=
  spWotsPops (cellVal (layerEnc pk (digestIdx pk m sig) sig L S)) (sig.layers L).chainValues

/-- **The three `sp_wots` calls' entries**, bottom layer first, each signing the value below. -/
def spKids (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) : List (List Pop) :=
  [spKid pk m sig ⟨0, by decide⟩ (forsKeyCell pk m sig), spKid pk m sig ⟨1, by decide⟩ (sRoot0 pk m sig),
    spKid pk m sig ⟨2, by decide⟩ (sRoot1 pk m sig)]

/-- **The check's entries** for the signature `sig` of `m` under `pk`, its `sp_wots` calls' spliced in: the randomizer, the unused bytes, FORS's, then each layer's. -/
def spSegPops (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) : List Pop :=
  prePops pk m sig (spKid pk m sig ⟨0, by decide⟩ (forsKeyCell pk m sig))
    (spKid pk m sig ⟨1, by decide⟩ (sRoot0 pk m sig)) (spKid pk m sig ⟨2, by decide⟩ (sRoot1 pk m sig))

/-- The hint generator's FORS key. -/
abbrev spForsKey (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) : HashSig.Digest :=
  Id.run (Sphincs.Verification.forsRecover (m := Id) keccakF1600 pk.publicSeed
    (Sphincs.digestIndex (spDigest pk m sig)) (Sphincs.digestForsLeaves (spDigest pk m sig)) sig.forsOpening)

theorem sphincsHints_eq (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    Hints.sphincsHints pk m sig =
      [("sp_rand", [Hints.cell128 sig.randomizer]), ("sp_unused", Hints.sphincsUnusedEntry (spOutputs pk m sig))] ++
        (List.finRange Sphincs.forsTreeCount).map (fun c =>
          ("sp_fors_secrets", [Hints.cell128 (sig.forsOpening c).secret])) ++
        (List.finRange Sphincs.forsTreeCount).flatMap (fun c => Hints.sphincsForsNodes pk.publicSeed
          (Sphincs.digestIndex (spDigest pk m sig)) c (Sphincs.digestForsLeaves (spDigest pk m sig) c)
          (sig.forsOpening c)) ++
        (Hints.sphincsLayer pk.publicSeed (Sphincs.digestIndex (spDigest pk m sig)) sig ⟨0, by decide⟩ (spForsKey pk m sig)).1 ++
        (Hints.sphincsLayer pk.publicSeed (Sphincs.digestIndex (spDigest pk m sig)) sig ⟨1, by decide⟩
          (Hints.sphincsLayer pk.publicSeed (Sphincs.digestIndex (spDigest pk m sig)) sig ⟨0, by decide⟩
            (spForsKey pk m sig)).2).1 ++
        (Hints.sphincsLayer pk.publicSeed (Sphincs.digestIndex (spDigest pk m sig)) sig ⟨2, by decide⟩
          (Hints.sphincsLayer pk.publicSeed (Sphincs.digestIndex (spDigest pk m sig)) sig ⟨1, by decide⟩
            (Hints.sphincsLayer pk.publicSeed (Sphincs.digestIndex (spDigest pk m sig)) sig ⟨0, by decide⟩
              (spForsKey pk m sig)).2).2).1 :=
  rfl

/-- **The check's entries are `sphincsHints`'**, stream by stream. -/
theorem spSegPops_sameStreams (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (hv : Sphincs.verifyWithKeccak pk m sig = true) :
    SameStreams (spSegPops pk m sig) (Hints.sphincsHints pk m sig) := by
  obtain ⟨r0, r1, h0, h1, h2⟩ := (verifyWithKeccak_iff_stages pk m sig).mp hv
  rw [sForsKeyOf_eq] at h0
  obtain ⟨hV0, hr0⟩ := layer_cells h0
  rw [hr0] at h1
  obtain ⟨hV1, hr1⟩ := layer_cells h1
  rw [hr1] at h2
  obtain ⟨hV2, -⟩ := layer_cells h2
  have L0 := layerPops_sameStreams pk m sig ⟨0, by decide⟩ (forsKeyCell pk m sig) hV0
  have L1 := layerPops_sameStreams pk m sig ⟨1, by decide⟩
    (layerRootCell pk (digestIdx pk m sig) sig ⟨0, by decide⟩ (forsKeyCell pk m sig)) hV1
  have L2 := layerPops_sameStreams pk m sig ⟨2, by decide⟩
    (layerRootCell pk (digestIdx pk m sig) sig ⟨1, by decide⟩
      (layerRootCell pk (digestIdx pk m sig) sig ⟨0, by decide⟩ (forsKeyCell pk m sig))) hV2
  have hi : Sphincs.digestIndex (spDigest pk m sig) = digestIdx pk m sig := by
    show _ = Sphincs.digestIndex (sDigestOf pk m sig)
    rw [sDigestOf_eq_outputs]
  have hk : spForsKey pk m sig = cellVal (forsKeyCell pk m sig) := by
    rw [← sForsKeyOf_eq]
    show Id.run (Sphincs.Verification.forsRecover (m := Id) keccakF1600 pk.publicSeed
        (Sphincs.digestIndex (spDigest pk m sig)) (Sphincs.digestForsLeaves (spDigest pk m sig)) sig.forsOpening) =
      Id.run (Sphincs.Verification.forsRecover (m := Id) keccakF1600 pk.publicSeed
        (Sphincs.digestIndex (sDigestOf pk m sig)) (Sphincs.digestForsLeaves (sDigestOf pk m sig)) sig.forsOpening)
    rw [sDigestOf_eq_outputs]
  have hRU : [(("sp_rand" : String), [cellOf128 sig.randomizer]), ("sp_unused", (List.range 6).map fun j =>
      ofK (addressOfIndex (spUnusedN pk m sig.randomizer / 256 ^ j % 256)))] =
      [("sp_rand", [Hints.cell128 sig.randomizer]), ("sp_unused", Hints.sphincsUnusedEntry (spOutputs pk m sig))] := by
    rw [unusedEntry_eq, spCell128_eq sig.randomizer]
  have h := ((SameStreams.of_eq hRU).append (forsPops_sameStreams pk m sig)).append
    (L0.1.append (L1.1.append L2.1))
  refine h.trans (SameStreams.of_eq ?_)
  rw [sphincsHints_eq, hk, hi, L0.2, L1.2]
  simp only [List.append_assoc]

/-! ## The check, complete -/

theorem sLayerT_nb : NumBelow sLayerT.2.1 (Stmt.valsList sLayerT.1) := numBelow_of_all (by decide +kernel)

theorem sPre_nb : NumBelow sLayerT.2.1 (Stmt.valsList sPre) := by
  have hT := sLayerT_le
  have ap : ∀ {hi : Nat} {xs ys : List Stmt}, NumBelow hi (Stmt.valsList xs) → NumBelow hi (Stmt.valsList ys) →
      NumBelow hi (Stmt.valsList (xs ++ ys)) := fun h1 h2 => by rw [valsList_append]; exact h1.append h2
  exact ap (sBottom_nb.mono (by omega)) (ap (sLayerB_nb.mono (by omega))
    (ap (sMidAddrs_seq.numBelow.mono (by omega)) (ap (sLayerM_nb.mono (by omega))
      (ap (sTopAddrs_seq.numBelow.mono (by omega)) sLayerT_nb))))

/-- **`verify_sig_lean_sphincs`'s statements before the root's check complete popping its hints**: on every valuation agreeing below their end with the completing one, they pop `spSegPops`, the three `sp_wots` calls' entries `spKids` spliced in, which are `sphincsHints pk m sig`, stream by stream. -/
theorem verify_lean_sphincs_complete_pops (C : CallRel) (rd : Reader) (hC : SpWotsCalls C) (hm : MemOK rd 256)
    {bb : E} (hbb : ByteBits rd bb) (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature)
    (hv : Sphincs.verifyWithKeccak pk m sig = true) (σ : Val) (h1 : σ (.n 1) = bb)
    (hat : ClaimAt rd (σ (.n 0)) (cellOf128 pk.publicSeed) (cellOf128 pk.root) (msgLo m) (msgHi m)) :
    Completes C rd 2 sLayerT.2.1 sPre σ (fun σ' => ∀ σ'', AgreeBelow sLayerT.2.1 σ' σ'' →
      SplicePops rd σ'' sPre (spKids pk m sig) (spSegPops pk m sig) ∧
        SameStreams (spSegPops pk m sig) (Hints.sphincsHints pk m sig)) :=
  (sPre_complete sphincsBlocksComplete hC hm hbb pk m sig hv σ h1 hat).mono le_rfl le_rfl
    fun _ h _ hag => ⟨(h.2.2.2 _ _ _).agree sPre_nb hag, spSegPops_sameStreams pk m sig hv⟩

/-- **`verify_sig_lean_sphincs` is complete, popping its hints**: `verify_sig_lean_sphincs_complete_loads_Spec`'s valuation, and a call instance of it on that valuation whose callees pop `spKids` pops `spSegPops`, which are `sphincsHints pk m sig`, stream by stream. -/
theorem verify_sig_lean_sphincs_complete_pops (C : CallRel) (rd : Reader) (p bb : E) (pk : Sphincs.PublicKey)
    (m : HashSig.Message) (sig : Sphincs.Signature) (hC : SpWotsCalls C) (hm : MemOK rd 256)
    (hbb : ByteBits rd bb)
    (hat : ClaimAt rd p (cellOf128 pk.publicSeed) (cellOf128 pk.root) (cellOf128 (m.extractLsb' 0 128))
      (cellOf128 (m.extractLsb' 128 128)))
    (hv : Sphincs.verifyWithKeccak pk m sig = true) :
    ∃ σ : Val, σ (.n 0) = p ∧ σ (.n 1) = bb ∧
      Stmt.HoldsList C rd σ (Fn.«verify_sig_lean_sphincs».core).body False (fun rs => rs = []) ∧
      (∀ (P : Core.Program) (bufs : List ℕ) (kids : List Memory.Tree),
        P.find? "verify_sig_lean_sphincs" = some Fn.«verify_sig_lean_sphincs».core →
        Memory.Tree.popsKids P rd kids = spKids pk m sig →
        (Memory.Tree.node "verify_sig_lean_sphincs" σ bufs kids).pops P rd = spSegPops pk m sig) ∧
      SameStreams (spSegPops pk m sig) (Hints.sphincsHints pk m sig) := by
  let σ0 : Val := Function.update (Function.update (fun _ => (0 : E)) (.n 0) p) (.n 1) bb
  have e0 : σ0 (.n 0) = p := by
    simp only [σ0]
    rw [Function.update_of_ne (by simp), Function.update_self]
  have e1 : σ0 (.n 1) = bb := Function.update_self ..
  obtain ⟨σf, hef, ⟨hroot, hrt, -, hsp⟩, hhf⟩ :=
    sPre_complete sphincsBlocksComplete hC hm hbb pk m sig hv σ0 e1 (by rw [e0]; exact hat)
  have f0 : σf (.n 0) = p := by rw [hef.apply (Or.inl (by norm_num))]; exact e0
  have f1 : σf (.n 1) = bb := by rw [hef.apply (Or.inl (by norm_num))]; exact e1
  refine ⟨σf, f0, f1, ?_, fun P bufs kids hf hk => ?_, spSegPops_sameStreams pk m sig hv⟩
  · rw [sBody_eq, sBody_splitC, holdsList_append]
    refine hhf _ _ ⟨?_, rfl⟩
    show σf sLayerT.2.2 + σf sRoot = 0
    rw [hroot, hrt]; exact e_add_self _
  · have hb : (Fn.«verify_sig_lean_sphincs».core).body = sPre ++ [.atom (.assertEq sLayerT.2.2 sRoot), .ret []] := by
      rw [sBody_eq, sBody_splitC]
    have hx : SplicePops rd σf sPre (Memory.Tree.popsKids P rd kids) (spSegPops pk m sig) := by
      rw [hk]
      exact hsp (spKid pk m sig ⟨0, by decide⟩ (forsKeyCell pk m sig))
        (spKid pk m sig ⟨1, by decide⟩ (sRoot0 pk m sig)) (spKid pk m sig ⟨2, by decide⟩ (sRoot1 pk m sig))
    have hy : ∀ a : Atom, walk σf [.atom a, .ret []] = .ret [.atom a] [] := fun a => by
      simp [walk, walk1, Out.seq, Out.pre]
    have hc : ∀ a : Atom, calls [.atom a] = [] := fun _ => rfl
    obtain ⟨es', -, he⟩ := Memory.Tree.pops_of_splice (bufs := bufs) hf hb hx (hy _) (hc _)
    rw [he]
    exact List.append_nil _


end
end LeanVM.Guest.B1.Sig
