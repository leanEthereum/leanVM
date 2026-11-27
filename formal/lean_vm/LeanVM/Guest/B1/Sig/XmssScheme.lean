/-
  LeanVM.Guest.B1.Sig.XmssScheme

  EthLib's leanXMSS verification with Keccak-256 (`LeanXmss.verifyWithKeccak`) as pure functions of
  the guest's cells.
-/

module

public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Guest.B1.Sig.Shapes
public import LeanVM.Guest.Value.KeccakEthLib
public import EthLib.Cryptography.Proofs.Xmss.Verify
public import EthLib.Cryptography.Proofs.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.Tree
public import EthLib.Cryptography.Proofs.Xmss.Encoding
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.Xmss.Address
public import EthLib.Cryptography.Proofs.Xmss.Words
public import EthLib.Cryptography.Proofs.Xmss.Constants
public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import Common.WithHash
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.WithHash
import Common.SequenceFin

/-!
# leanXMSS over cells

`LeanXmss.verifyWithKeccak` is EthLib's `verifyWith` over the hash `xF`, EthLib's Keccak-256 of
lanes over Keccak-f[1600]. The lemmas here are stated for any hash `f` with the hypothesis `XH f`
that it is Keccak-256 of the lanes' bytes: the kernel then never compares `f` with another term,
which would unfold the hash. A cell is the two lanes `xl x`, and a hash of cells' bytes is the
first cell of their `hcell` (`th_cells`).

* `xmssVerify_iff`: the bottom layer's root, then the top layer's from it, is the key's;
* `chainStep_cells`, `chainEnd_cells` (over `xChain`), `leafHash_cells`, `messageDigest_cells`,
  `fold_cells` (over `xFold`): the routines on cells whose address cells hold EthLib's address
  encodings;
* `codeword_lit`, `codeword_some`: a codeword is the literal of its base-4 digits, summing to
  `106`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open EthLib.Cryptography
open EthLib.Cryptography.Hash.Keccak (Lanes2 Lanes4 lanesBytes)

@[expose] public section

/-- The digest cells of the Keccak-256 hash of cells. -/
def hcell (cs : List E) : E × E := digestHalves (keccak256 (cs.flatMap cellBytes))

theorem cellsBytes_eq_flatMap (cs : List E) : cellsBytes cs = cs.flatMap cellBytes := rfl

theorem sequenceFin_id {α : Type} : ∀ {n : Nat} (f : Fin n → Id α),
    _root_.HashSig.OverPermutation.sequenceFin f = f
  | 0, f => funext fun i => i.elim0
  | n + 1, f => by
      simp only [Common.sequenceFin_succ]
      have := sequenceFin_id (fun i : Fin n => f i.succ)
      rw [this]
      funext i
      refine Fin.cases rfl (fun j => rfl) i

/-- A cell as a 128-bit value. -/
def xv (x : E) : BitVec 128 := cellVal x

/-! ## The hash -/

/-- leanXMSS's hash over Keccak-f[1600], as a function of lanes. -/
def xF (lanes : Array UInt64) : Lanes4 := Id.run (LeanXmss.xmssHash (m := Id) keccakF1600 lanes)

/-- The hash `f` is Keccak-256 of the lanes' bytes. -/
def XH (f : Array UInt64 → Lanes4) : Prop :=
  ∀ lanes, (f lanes).bytes = (keccak256 (lanesBytes lanes)).toBytes

theorem xh_keccak : XH xF := KeccakEthLib.xmssHash_keccakF1600

theorem xmssHash_eq_pureHash :
    LeanXmss.xmssHash (m := Id) keccakF1600 = Xmss.pureHash xF := rfl

/-- The layer of number `n`: the bottom for `0`, the top otherwise. -/
def lyr (n : Nat) : Xmss.Layer := if n = 0 then .bottom else .top

theorem toNat_lyr {n : Nat} (h : n < 2) : (lyr n).toNat = n := by
  interval_cases n <;> rfl

theorem lyr_zero : lyr 0 = .bottom := rfl

theorem lyr_one : lyr 1 = .top := rfl

variable {f : Array UInt64 → Lanes4}

/-! ## Verification -/

/-- **Verification**: the bottom layer's root, then the top layer's from it, is the key's. -/
theorem xmssVerify_iff (pk : Xmss.PublicKey) (msg : Xmss.Message) (σ : Xmss.Signature) :
    LeanXmss.verifyWithKeccak pk msg σ = true ↔
      ∃ r0, (Xmss.layerRoot (Xmss.pureHash xF) pk.publicParam .bottom σ.leafIndex.toNat
          msg.toArray σ.bottom).run = some r0 ∧
        (Xmss.layerRoot (Xmss.pureHash xF) pk.publicParam .top (Xmss.bottomTree σ.leafIndex)
          r0.toArray σ.top).run = some pk.root :=
  Xmss.verify_iff

/-! ## A hash of cells -/

theorem toBytes_toList (d : LeanVM.Protocol.Digest) :
    (LeanVM.Protocol.Digest.toBytes d).toList = digestBytes d := rfl

theorem bytes_halfOf_zero (w : Lanes4) :
    (Lanes2.mk w.w0 w.w1).bytes.toList = w.bytes.toList.take 16 := by
  simp [Lanes2.bytes, Lanes4.bytes]

/-- **A hash of cells**: a tweakable hash whose input is the bytes of cells is the lanes of the
first cell of their `hcell`. -/
theorem th_cells (hf : XH f) {P : Lanes2} {A : Xmss.Address} {M : Array UInt64} {cs : List E}
    (h : P.bytes.toList ++ A.encode.bytes.toList ++ lanesBytes M = cs.flatMap cellBytes) :
    (Xmss.th (Xmss.pureHash f) P A M).run = xl (hcell cs).1 := by
  apply Lanes2.bytes_injective
  apply Vector.toList_inj.mp
  rw [bytes_xl, Xmss.th_run, Xmss.halfOf_zero, bytes_halfOf_zero, hf (Xmss.thInput P A M),
    Xmss.lanesBytes_thInput, h,
    toBytes_toList, hcell, digestBytes_eq, List.take_left' (length_cellBytes _)]

/-- A digit is below `4`. -/
theorem hxlt (x : Vector (Fin Xmss.Constants.CHAIN_LENGTH) Xmss.Constants.V)
    (i : Fin Xmss.Constants.V) : (x[i] : Nat) < 4 := by
  have h := (x[i]).isLt
  have e : Xmss.Constants.CHAIN_LENGTH = 4 := Xmss.Constants.chain_length_eq
  omega

theorem index_lt (i : Fin Xmss.Constants.V) : i.val < 2 ^ 64 := by
  have := i.isLt
  simp only [Xmss.Constants.V] at this
  omega

/-! ## A chain -/

/-- **A chain step over cells**, its address's bytes those of the step's address. -/
theorem chainStep_cells (hf : XH f) {pp a x : E} {layer : Xmss.Layer} {e : UInt32}
    {i : Fin Xmss.Constants.V} {mu : Fin (Xmss.Constants.CHAIN_LENGTH - 1)}
    (ha : cellBytes a = (Xmss.Address.chain layer e mu).encode.bytes.toList) :
    (Xmss.chainStep (Xmss.pureHash f) (xl pp) layer e i mu (xl x)).run =
      xl (hcell [pp, a, x, eOfNat i.val]).1 := by
  rw [Xmss.chainStep_eq_th]
  apply th_cells hf
  rw [Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_lanes2,
    Xmss.lanesBytes_index _ (index_lt i), toList_toLE, ← ha]
  simp [bytes_xl, cellBytes_eOfNat (index_lt i)]

/-- `n` chain steps from position `s` on cells: the step leaving position `s` hashes `P`, its
address `adr s`, the value and the chain index. -/
def xChain (pp : E) (adr : Nat → E) (i : Nat) : Nat → Nat → E → E
  | 0, _, x => x
  | n + 1, s, x => xChain pp adr i n (s + 1) (hcell [pp, adr s, x, eOfNat i]).1

/-- **A chain walked over cells**, its addresses' bytes those of the steps'. -/
theorem chain_cells (hf : XH f) {pp : E} {adr : Nat → E} {layer : Xmss.Layer} {e : UInt32}
    (hadr : ∀ s : Fin (Xmss.Constants.CHAIN_LENGTH - 1),
      cellBytes (adr s.val) = (Xmss.Address.chain layer e s).encode.bytes.toList)
    (i : Fin Xmss.Constants.V) :
    ∀ (n start : Nat) (h : start + n < Xmss.Constants.CHAIN_LENGTH) (z : E),
      (Xmss.chain (Xmss.pureHash f) (xl pp) layer e i start n h (xl z)).run =
        xl (xChain pp adr i.val n start z)
  | 0, start, h, z => by simp [xChain]
  | n + 1, start, h, z => by
      rw [Xmss.chain_succ_run h, chainStep_cells hf (hadr ⟨start, by
        simp only [Xmss.Constants.CHAIN_LENGTH] at h ⊢; omega⟩)]
      exact chain_cells hf hadr i n (start + 1) (by omega) _

/-- **A chain end over cells**: chain `i` walked from the position its digit names to position
`3`, `3 - x_i` steps. -/
theorem chainEnd_cells (hf : XH f) {pp : E} {adr : Nat → E} {layer : Xmss.Layer} {e : UInt32}
    (hadr : ∀ s : Fin (Xmss.Constants.CHAIN_LENGTH - 1),
      cellBytes (adr s.val) = (Xmss.Address.chain layer e s).encode.bytes.toList)
    (x : Vector (Fin Xmss.Constants.CHAIN_LENGTH) Xmss.Constants.V)
    (y : Vector Lanes2 Xmss.Constants.V) (i : Fin Xmss.Constants.V) {z : E} (hy : y[i] = xl z) :
    Xmss.chainEnd f (xl pp) layer e x y i =
      xl (xChain pp adr i.val (3 - (x[i] : Nat)) (x[i] : Nat) z) := by
  have hk : (x[i] : Nat) + (3 - (x[i] : Nat)) = Xmss.Constants.CHAIN_LENGTH - 1 := by
    have := hxlt x i
    have e : Xmss.Constants.CHAIN_LENGTH = 4 := Xmss.Constants.chain_length_eq
    omega
  rw [Xmss.chainEnd_eq_chain hk, hy]
  exact chain_cells hf hadr i _ _ _ z

theorem ofFn_val_eq {α : Type} (n : Nat) (g : Nat → α) :
    (List.ofFn fun i : Fin n => g i.val) = (List.range n).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- **The one-time leaf over cells.** -/
theorem leafHash_cells (hf : XH f) {pp a : E} {layer : Xmss.Layer} {e : UInt32} (tips : Nat → E)
    (ha : cellBytes a = (Xmss.Address.leaf layer e).encode.bytes.toList) :
    (Xmss.otsLeafHash (Xmss.pureHash f) (xl pp) layer e
        (Vector.ofFn fun i : Fin Xmss.Constants.V => xl (tips i.val))).run =
      xl (hcell (pp :: a :: (List.range 58).map tips)).1 := by
  rw [Xmss.otsLeafHash_eq_th]
  apply th_cells hf
  rw [Xmss.lanesBytes_digestLanes, bytes_xl, ← ha, Vector.toList_ofFn, List.map_ofFn]
  have e1 : (List.ofFn ((fun d : Lanes2 => d.bytes.toList) ∘ fun i : Fin Xmss.Constants.V =>
      xl (tips i.val))) = List.ofFn fun i : Fin Xmss.Constants.V => cellBytes (tips i.val) :=
    List.ofFn_inj.mpr (funext fun i => bytes_xl _)
  rw [e1, ofFn_val_eq Xmss.Constants.V (fun j => cellBytes (tips j))]
  simp [List.flatMap, List.map_map, Function.comp_def, List.append_assoc]
  rfl

/-- **The message digest over cells.** -/
theorem messageDigest_cells (hf : XH f) {pp a rho : E} {layer : Xmss.Layer} {e : UInt32}
    {M : Array UInt64} {cs : List E}
    (ha : cellBytes a = (Xmss.Address.msg layer e).encode.bytes.toList)
    (hM : lanesBytes M = cs.flatMap cellBytes) :
    (Xmss.messageDigest (Xmss.pureHash f) (xl pp) layer e M (xl rho)).run =
      xl (hcell (pp :: a :: cs ++ [rho])).1 := by
  rw [Xmss.messageDigest_eq_th]
  apply th_cells hf
  rw [Hash.Keccak.lanesBytes_append, hM, Hash.Keccak.lanesBytes_lanes2, ← ha]
  simp [bytes_xl]

/-! ## A tree -/

/-- **A node over cells**, its address's bytes those of the node's. -/
theorem nodeHash_cells (hf : XH f) {pp a l r : E} {layer : Xmss.Layer}
    {p : EthLib.Cryptography.Merkle.Position} (hp : p.level ≤ Xmss.Constants.LAYER_HEIGHT)
    (ha : cellBytes a = (Xmss.Address.node layer ⟨p.level, Nat.lt_succ_of_le hp⟩
      (UInt32.ofNat p.index)).encode.bytes.toList) :
    (Xmss.nodeHash (Xmss.pureHash f) (xl pp) layer p (xl l) (xl r)).run =
      xl (hcell [pp, a, l, r]).1 := by
  rw [Xmss.nodeHash_of_le _ _ _ hp]
  apply th_cells hf
  have e1 : (#[(xl l).lo, (xl l).hi, (xl r).lo, (xl r).hi] : Array UInt64) =
      (xl l).toArray ++ (xl r).toArray := rfl
  rw [e1, Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_lanes2,
    Hash.Keccak.lanesBytes_lanes2, ← ha]
  simp [bytes_xl]

/-- `m` levels of a Merkle path on cells, the last level taken last: level `l` hashes `P`, its
address `A l` and the pair in the order of bit `l`. -/
def xFold (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) : Nat → E → E
  | 0, x => x
  | m + 1, x =>
      let y := xFold pp A bits sibs m x
      (hcell [pp, A m, if bits m then sibs m else y, if bits m then y else sibs m]).1

/-- **A layer's tree over cells**: the climb of a path whose addresses' bytes are the nodes'
addresses', its bits the key's. -/
theorem climb_cells (hf : XH f) {pp : E} {A : Nat → E} {layer : Xmss.Layer} {e : Nat}
    (hA : ∀ (l : Nat) (hl : l < Xmss.Constants.LAYER_HEIGHT), cellBytes (A l) =
      (Xmss.Address.node layer ⟨l + 1, by omega⟩ (UInt32.ofNat (e / 2 ^ (l +
          1)))).encode.bytes.toList)
    (sibs : Nat → E) :
    ∀ m ≤ Xmss.Constants.LAYER_HEIGHT, ∀ x : E,
      (EthLib.Cryptography.Merkle.climb (Xmss.nodeHash (Xmss.pureHash f) (xl pp) layer) ⟨0,
          e⟩ (xl x)
        (List.ofFn fun k : Fin m => xl (sibs k.val))).run =
        xl (xFold pp A (fun l => e.testBit l) sibs m x)
  | 0, _, x => by simp [xFold]
  | m + 1, hm, x => by
      rw [EthLib.Cryptography.Merkle.climb_ofFn_succ (hash := Xmss.nodeHash (Xmss.pureHash f) (xl
          pp) layer) e
        (fun k => xl (sibs k)) m (xl x), Id.run_bind, climb_cells hf hA sibs m (by omega) x]
      by_cases hb : e.testBit m = true
      · simp only [xFold, hb, ↓reduceIte]
        exact nodeHash_cells hf (p := ⟨m + 1, e / 2 ^ (m + 1)⟩) hm (hA m (by omega))
      · simp only [xFold, hb]
        exact nodeHash_cells hf (p := ⟨m + 1, e / 2 ^ (m + 1)⟩) hm (hA m (by omega))

/-- **A layer's tree over cells, in full**: the fold of its `16` siblings. -/
theorem fold_cells (hf : XH f) {pp : E} {A : Nat → E} {layer : Xmss.Layer} {e : Nat}
    (hA : ∀ (l : Nat) (hl : l < Xmss.Constants.LAYER_HEIGHT), cellBytes (A l) =
      (Xmss.Address.node layer ⟨l + 1, by omega⟩ (UInt32.ofNat (e / 2 ^ (l +
          1)))).encode.bytes.toList)
    (sibs : Nat → E) (x : E) :
    (Xmss.fold (Xmss.pureHash f) (xl pp) layer e (xl x)
        (Vector.ofFn fun k : Fin Xmss.Constants.LAYER_HEIGHT => xl (sibs k.val))).run =
      xl (xFold pp A (fun l => e.testBit l) sibs 16 x) := by
  refine (congrArg Id.run (Xmss.fold_ofFn (Xmss.pureHash f) (xl pp) layer e (xl x)
    (fun k => xl (sibs k)))).trans ?_
  exact climb_cells hf hA sibs 16 le_rfl x

/-! ## The codeword -/

theorem base4_lt {dig : Nat → Nat} (hd : ∀ j, dig j < 4) :
    ∀ n, ∑ j ∈ Finset.range n, dig j * 4 ^ j < 4 ^ n
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, pow_succ]
      have := base4_lt hd n
      have h3 : dig n * 4 ^ n ≤ 3 * 4 ^ n := Nat.mul_le_mul_right _ (by have := hd n; omega)
      omega

theorem base4_digit {dig : Nat → Nat} (hd : ∀ j, dig j < 4) :
    ∀ n i, i < n → (∑ j ∈ Finset.range n, dig j * 4 ^ j) / 4 ^ i % 4 = dig i
  | 0, _, h => absurd h (by omega)
  | n + 1, i, h => by
      rw [Finset.sum_range_succ]
      by_cases hi : i = n
      · subst hi
        rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (base4_lt hd i), Nat.zero_add,
          Nat.mod_eq_of_lt (hd i)]
      · have hlt : i < n := by omega
        rw [show dig n * 4 ^ n = 4 ^ i * (4 * (dig n * 4 ^ (n - i - 1))) by
          rw [show 4 ^ n = 4 ^ i * 4 * 4 ^ (n - i - 1) by
            rw [mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega]; ring,
          Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, base4_digit hd n i hlt]

theorem cellNat_lit (N : Nat) : cellNat (lit N) = N % 2 ^ 128 := by
  simp only [cellNat, lit, word, ofLimbs_limb0, ofLimbs_limb1, kToNat_ofBits, Nat.mod_mod]
  have h1 := Nat.mod_mul_right_div_self N (2 ^ 64) (2 ^ 64)
  have h2 : N % 2 ^ 128 % 2 ^ 64 = N % 2 ^ 64 := Nat.mod_mod_of_dvd _ (by norm_num)
  have h3 := Nat.mod_add_div (N % 2 ^ 128) (2 ^ 64)
  rw [show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 by norm_num] at h1
  omega

theorem cellVal_lit (N : Nat) : cellVal (lit N) = BitVec.ofNat 128 N := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_cellVal, cellNat_lit, BitVec.toNat_ofNat]

theorem xv_lit (N : Nat) : xv (lit N) = BitVec.ofNat 128 N := cellVal_lit N

theorem toNat_xl_lit {N : Nat} (h : N < 2 ^ 128) : (xl (lit N)).toNat = N := by
  rw [toNat_xl, cellNat_lit, Nat.mod_eq_of_lt h]

/-- A cell is the literal of its lanes' number. -/
theorem lit_toNat_xl (x : E) : lit (xl x).toNat = x := by
  apply xl_inj
  apply Lanes2.toNat_injective
  rw [toNat_xl_lit (Lanes2.toNat_lt _)]

/-- The digits `dig`, each below `4`, as a codeword's vector. -/
def codeVec (dig : Nat → Nat) (hd : ∀ j, dig j < 4) :
    Vector (Fin Xmss.Constants.CHAIN_LENGTH) Xmss.Constants.V :=
  Vector.ofFn fun i => ⟨dig i.val, by rw [Xmss.Constants.chain_length_eq]; exact hd i.val⟩

theorem codeVec_val (dig : Nat → Nat) (hd : ∀ j, dig j < 4) (i : Fin Xmss.Constants.V) :
    ((codeVec dig hd)[i] : Nat) = dig i.val := by
  simp [codeVec]

/-- **A codeword's digits**: the digest holding the literal of `58` digits below 4 summing to
106 is the codeword of them. -/
theorem codeword_lit {dig : Nat → Nat} (hd : ∀ j, dig j < 4)
    (hs : ∑ i ∈ Finset.range 58, dig i = 106) :
    Xmss.codeword? (xl (lit (∑ j ∈ Finset.range 58, dig j * 4 ^ j))) = some (codeVec dig hd) := by
  have hlt : ∑ j ∈ Finset.range 58, dig j * 4 ^ j < 2 ^ 128 :=
    lt_trans (base4_lt hd 58) (by norm_num)
  rw [Xmss.codeword?_eq_some_iff, toNat_xl_lit hlt]
  refine ⟨?_, ?_⟩
  · simp only [codeVec_val]
    exact (Fin.sum_univ_eq_sum_range (fun j => dig j * 4 ^ j) Xmss.Constants.V).symm
  · simp only [codeVec_val]
    exact (Fin.sum_univ_eq_sum_range (fun j => dig j) Xmss.Constants.V).trans hs

theorem base4_expand : ∀ n N, N < 4 ^ n → ∑ j ∈ Finset.range n, N / 4 ^ j % 4 * 4 ^ j = N
  | 0, N, h => by simp only [pow_zero, Nat.lt_one_iff] at h; simp [h]
  | n + 1, N, h => by
      rw [Finset.sum_range_succ']
      have ih := base4_expand n (N / 4) (by rw [pow_succ] at h; omega)
      have hs : ∑ j ∈ Finset.range n, N / 4 ^ (j + 1) % 4 * 4 ^ (j + 1) =
          4 * ∑ j ∈ Finset.range n, N / 4 / 4 ^ j % 4 * 4 ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ', Nat.div_div_eq_div_mul]
        ring
      rw [hs, ih]
      simp only [pow_zero, Nat.div_one, Nat.mul_one]
      omega

/-- **A codeword's digits, read back**: a digest that is a codeword holds the literal of its
base-4 digits, which sum to 106. -/
theorem codeword_some {d : Lanes2} {x : Vector (Fin Xmss.Constants.CHAIN_LENGTH) Xmss.Constants.V}
    (h : Xmss.codeword? d = some x) :
    (∀ i : Fin Xmss.Constants.V, (x[i] : Nat) = d.toNat / 4 ^ i.val % 4) ∧
      ∑ i ∈ Finset.range 58, d.toNat / 4 ^ i % 4 = 106 ∧
      d.toNat = ∑ j ∈ Finset.range 58, d.toNat / 4 ^ j % 4 * 4 ^ j := by
  obtain ⟨hdig, -, -⟩ := Xmss.codeword?_eq_some h
  have hsum := Xmss.sum_of_codeword h
  have htn := Xmss.toNat_of_codeword h
  have e1 : ∑ i : Fin Xmss.Constants.V, (x[i] : Nat) =
      ∑ i ∈ Finset.range 58, d.toNat / 4 ^ i % 4 := by
    rw [Finset.sum_congr rfl (fun i _ => hdig i)]
    exact Fin.sum_univ_eq_sum_range (fun j => d.toNat / 4 ^ j % 4) Xmss.Constants.V
  refine ⟨hdig, ?_, ?_⟩
  · rw [← e1, hsum, Xmss.Constants.target_sum_eq]
  · calc d.toNat = ∑ i : Fin Xmss.Constants.V, (x[i] : Nat) * 4 ^ i.val := htn
      _ = ∑ i : Fin Xmss.Constants.V, (d.toNat / 4 ^ i.val % 4) * 4 ^ i.val :=
          Finset.sum_congr rfl (fun i _ => by rw [hdig i])
      _ = _ := Fin.sum_univ_eq_sum_range (fun j => d.toNat / 4 ^ j % 4 * 4 ^ j)
          Xmss.Constants.V

end
end LeanVM.Guest.B1.Sig
