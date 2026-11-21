module

public import Quantum.Sponge.Keccak
public import Quantum.Sponge.Hash
public import Statement.LeanXmss

@[expose] public section

/-!
# leanXMSS's hash as a sponge

The statement's hash `H` (`keccakHash`, Keccak-256 over a permutation `π` of `KeccakState`) is the
sponge of `Quantum/Sponge/Hash.lean` on the rate `X = KeccakRate` (1088 bits) and the capacity
`Z = KeccakCapacity` (512 bits), both XOR groups:

* `keccakStateEquiv : KeccakState ≃ X × Z`: rate bit `j` is bit `j % 64` of lane `j / 64`
  (lanes `0` to `16`), capacity bit `j` is bit `j % 64` of lane `17 + j / 64`. XOR into a lane is
  addition, so Keccak's absorption is the sponge's (`keccakStateEquiv_absorbBlockWith`).
* `blocks`: the padded blocks of an input (`0x01 … 0x80`), each read as a rate; rate bit
  `8 k + r` is bit `r` of byte `k` (`blockOf_apply`).
* `keccakHash_eq_spongeHash`: `H` over `π` is `out256` of `spongeHash (spongeView π) (blocks input)`,
  where `out256` reads the first 256 rate bits in the statement's byte order; likewise in any lawful
  monad (`keccakHash_pure`) and for `queryPermutation` under any simulation answering `π`
  (`simulateQ_keccakHash`).
* `trunc128 = truncateHash ∘ out256` keeps the first 128 rate bits: `card_fiber_trunc128`.
* `Slot`, `slotOf`: the hash call a Msponge tail belongs to, read from its first block (prefix,
  address, and the chain index of a chain step's payload) and its length (the seed derivation);
  `slotOf_thInput` and its instances per hash call, `slotOf_seed`; tails determine the address and
  payload (`absorbTail_blocks_thInput_injective`).
-/

namespace Quantum.Xmss

open Finset Quantum.Sponge HashSig HashSig.OverPermutation LeanXmss
open LeanVM.Semantics
open LeanVM.Protocol.KeccakHash (littleEndianLane absorbBlockWith absorbWith padBlock
  keccak256With wordBytes digestBytes padFirst padLast)

/-- The rate of Keccak-256, 1088 bits. -/
abbrev X : Type := KeccakRate

/-- The capacity of Keccak-256, 512 bits. -/
abbrev Z : Type := KeccakCapacity

/-! ## Bits -/

/-- A bit as an element of `ZMod 2`. -/
def bitOf (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bitOf_xor (a b : Bool) : bitOf (a ^^ b) = bitOf a + bitOf b := by
  cases a <;> cases b <;> decide

@[simp]
theorem bitOf_eq_one_iff (b : Bool) : bitOf b = 1 ↔ b = true := by
  cases b <;> decide

@[simp]
theorem bitOf_false : bitOf false = 0 := rfl

@[simp]
theorem bitOf_true : bitOf true = 1 := rfl

theorem bitOf_injective : Function.Injective bitOf := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem bitOf_decide_eq_one (z : ZMod 2) : bitOf (decide (z = 1)) = z := by
  revert z
  decide

/-- The bit vector with the given `ZMod 2` digits, least significant first. -/
def ofBits {n : ℕ} (f : Fin n → ZMod 2) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn fun i ↦ decide (f i = 1))).cast List.length_ofFn

theorem getLsbD_ofBits {n : ℕ} (f : Fin n → ZMod 2) (i : ℕ) (hi : i < n) :
    (ofBits f).getLsbD i = decide (f ⟨i, hi⟩ = 1) := by
  rw [ofBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn]
  simp [hi]

/-- The bits of a bit vector as `ZMod 2` digits, least significant first. -/
def bitsEquiv (n : ℕ) : BitVec n ≃ (Fin n → ZMod 2) where
  toFun v i := bitOf (v.getLsbD i)
  invFun := ofBits
  left_inv v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_ofBits _ i hi]
    simp
  right_inv f := by
    funext i
    show bitOf ((ofBits f).getLsbD i) = f i
    rw [getLsbD_ofBits _ i i.isLt, bitOf_decide_eq_one]

theorem bitsEquiv_apply (n : ℕ) (v : BitVec n) (i : Fin n) : bitsEquiv n v i = bitOf (v.getLsbD i) :=
  rfl

theorem getLsbD_bitsEquiv_symm (n : ℕ) (f : Fin n → ZMod 2) (i : ℕ) (hi : i < n) :
    ((bitsEquiv n).symm f).getLsbD i = decide (f ⟨i, hi⟩ = 1) :=
  getLsbD_ofBits f i hi

/-- A lane's 64 bits, least significant first. -/
def laneEquiv : UInt64 ≃ (Fin 64 → ZMod 2) :=
  (⟨UInt64.toBitVec, UInt64.ofBitVec, fun _ ↦ rfl, fun _ ↦ rfl⟩ : UInt64 ≃ BitVec 64).trans
    (bitsEquiv 64)

theorem laneEquiv_apply (w : UInt64) (b : Fin 64) : laneEquiv w b = bitOf (w.toBitVec.getLsbD b) :=
  rfl

theorem laneEquiv_xor (a b : UInt64) : laneEquiv (a ^^^ b) = laneEquiv a + laneEquiv b := by
  funext i
  simp only [laneEquiv_apply, UInt64.toBitVec_xor, BitVec.getLsbD_xor, bitOf_xor, Pi.add_apply]

theorem laneEquiv_zero : laneEquiv 0 = 0 := by
  funext i
  simp [laneEquiv_apply]

/-! ## The state as rate and capacity -/

theorem lane_eq_getElem (s : KeccakState) (i : ℕ) (h : i < 25) : Keccak.lane s i = s[i] := by
  simp [Keccak.lane, h]

theorem lane_ofFn (g : Fin 25 → UInt64) (i : ℕ) (h : i < 25) :
    Keccak.lane (Vector.ofFn g) i = g ⟨i, h⟩ := by
  simp [Keccak.lane, h]

/-- **The Keccak state as rate and capacity.** Rate bit `j` is bit `j % 64` of lane `j / 64`, capacity
bit `j` is bit `j % 64` of lane `17 + j / 64`. -/
def keccakStateEquiv : KeccakState ≃ X × Z where
  toFun s := (fun j ↦ laneEquiv (Keccak.lane s (j / 64)) ⟨j % 64, Nat.mod_lt _ (by norm_num)⟩,
    fun j ↦ laneEquiv (Keccak.lane s (17 + j / 64)) ⟨j % 64, Nat.mod_lt _ (by norm_num)⟩)
  invFun p := Vector.ofFn fun i ↦ laneEquiv.symm fun b ↦
    if h : i.val < 17 then p.1 ⟨64 * i + b, by omega⟩ else p.2 ⟨64 * (i - 17) + b, by omega⟩
  left_inv s := by
    ext i hi
    simp only [Vector.getElem_ofFn]
    rw [Equiv.symm_apply_eq, ← lane_eq_getElem s i hi]
    funext b
    split_ifs with h
    · simp only [show (64 * i + b) / 64 = i by omega, show (64 * i + b) % 64 = b by omega]
    · simp only [show 17 + (64 * (i - 17) + b) / 64 = i by omega,
        show (64 * (i - 17) + b) % 64 = b by omega]
  right_inv p := by
    obtain ⟨x, z⟩ := p
    refine Prod.ext (funext fun j ↦ ?_) (funext fun j ↦ ?_)
    · simp only
      rw [lane_ofFn _ _ (by omega), Equiv.apply_symm_apply]
      split_ifs with h
      · congr 1
        ext
        simp only
        omega
      · exfalso
        simp only [not_lt] at h
        omega
    · simp only
      rw [lane_ofFn _ _ (by omega), Equiv.apply_symm_apply]
      split_ifs with h
      · exfalso
        simp only at h
        omega
      · congr 1
        ext
        simp only
        omega

theorem keccakStateEquiv_fst (s : KeccakState) (j : Fin 1088) :
    (keccakStateEquiv s).1 j =
      bitOf ((Keccak.lane s (j / 64)).toBitVec.getLsbD (j % 64)) :=
  rfl

theorem keccakStateEquiv_zero : keccakStateEquiv (Vector.replicate 25 0) = (0, 0) := by
  refine Prod.ext (funext fun j ↦ ?_) (funext fun j ↦ ?_)
  · simp [keccakStateEquiv, Keccak.lane, Vector.getElem?_replicate,
      show (j : ℕ) / 64 < 25 by omega, laneEquiv_zero]
  · simp [keccakStateEquiv, Keccak.lane, Vector.getElem?_replicate,
      show 17 + (j : ℕ) / 64 < 25 by omega, laneEquiv_zero]

/-- A permutation of the Keccak state, transported to `X × Z`. -/
def spongeView (π : Equiv.Perm KeccakState) : Equiv.Perm (X × Z) :=
  keccakStateEquiv.permCongr π

/-! ## Blocks -/

/-- A block of bytes as a rate: bit `j` is bit `j % 64` of the little-endian lane `j / 64`. -/
def blockOf (block : List UInt8) : X :=
  fun j ↦ laneEquiv (littleEndianLane block (j / 64)) ⟨j % 64, Nat.mod_lt _ (by norm_num)⟩

/-- XOR of a block into the rate lanes is addition into the rate. -/
theorem keccakStateEquiv_xorBlock (s : KeccakState) (block : List UInt8) :
    keccakStateEquiv (Vector.ofFn fun i : Fin 25 ↦
      if i.val < 17 then Keccak.lane s i ^^^ littleEndianLane block i else Keccak.lane s i) =
      ((keccakStateEquiv s).1 + blockOf block, (keccakStateEquiv s).2) := by
  refine Prod.ext (funext fun j ↦ ?_) (funext fun j ↦ ?_)
  · change laneEquiv (Keccak.lane (Vector.ofFn _) (j / 64)) _ = _
    rw [lane_ofFn _ _ (by omega)]
    split_ifs with h
    · rw [laneEquiv_xor]
      rfl
    · exfalso
      simp only [not_lt] at h
      omega
  · change laneEquiv (Keccak.lane (Vector.ofFn _) (17 + j / 64)) _ = _
    rw [lane_ofFn _ _ (by omega)]
    split_ifs with h
    · exfalso
      simp only at h
      omega
    · rfl

/-- One absorbed block of Keccak is one sponge step. -/
theorem keccakStateEquiv_absorbBlockWith (π : Equiv.Perm KeccakState) (s : KeccakState)
    (block : List UInt8) :
    keccakStateEquiv (absorbBlockWith (m := Id) (fun s ↦ pure (π s)) s block) =
      absorbStep (spongeView π) (keccakStateEquiv s) (blockOf block) := by
  rw [absorbStep, spongeView, Equiv.permCongr_apply, ← keccakStateEquiv_xorBlock,
    Equiv.symm_apply_apply]
  rfl

/-- The byte blocks `absorbWith n` absorbs: `n` whole blocks, then the padded rest. -/
def blockBytes : ℕ → List UInt8 → List (List UInt8)
  | 0, data => [padBlock data]
  | n + 1, data => data.take LeanVM.Protocol.KeccakHash.rate ::
      blockBytes n (data.drop LeanVM.Protocol.KeccakHash.rate)

/-- **The sponge blocks of a hash input**: whole blocks of 136 bytes, then the last one padded with
`0x01 … 0x80`, each as a rate. -/
def blocks (input : HashInput) : List X :=
  (blockBytes (input.length / LeanVM.Protocol.KeccakHash.rate) input).map blockOf

theorem length_blockBytes (n : ℕ) (data : List UInt8) : (blockBytes n data).length = n + 1 := by
  induction n generalizing data with
  | zero => rfl
  | succ n ih => simp [blockBytes, ih]

theorem length_blocks (input : HashInput) : (blocks input).length = input.length / 136 + 1 := by
  simp [blocks, length_blockBytes, LeanVM.Protocol.KeccakHash.rate]

theorem keccakStateEquiv_absorbWith (π : Equiv.Perm KeccakState) :
    ∀ (n : ℕ) (s : KeccakState) (data : List UInt8),
      keccakStateEquiv (absorbWith (m := Id) (fun s ↦ pure (π s)) n s data) =
        ((blockBytes n data).map blockOf).foldl (absorbStep (spongeView π)) (keccakStateEquiv s)
  | 0, s, data => keccakStateEquiv_absorbBlockWith π s (padBlock data)
  | n + 1, s, data => by
    rw [blockBytes, List.map_cons, List.foldl_cons, ← keccakStateEquiv_absorbBlockWith,
      ← keccakStateEquiv_absorbWith π n]
    rfl

theorem absorbWith_pure {m : Type → Type} [Monad m] [LawfulMonad m] (π : Equiv.Perm KeccakState) :
    ∀ (n : ℕ) (s : KeccakState) (data : List UInt8),
      absorbWith (m := m) (fun s ↦ pure (π s)) n s data =
        pure (absorbWith (m := Id) (fun s ↦ pure (π s)) n s data)
  | 0, _, _ => rfl
  | n + 1, s, data => by
    simp only [absorbWith, absorbBlockWith, pure_bind]
    exact absorbWith_pure π n _ _

/-! ## The output -/

/-- **The hash output of a rate**: its first 256 bits, as `keccakHash` reads its digest bytes. -/
def out256 (x : X) : HashOutput :=
  (bitsEquiv 256).symm fun j ↦ x (Fin.castAdd 832 j)

theorem getLsbD_out256 (x : X) (j : ℕ) (hj : j < 256) :
    (out256 x).getLsbD j = decide (x ⟨j, by omega⟩ = 1) :=
  getLsbD_bitsEquiv_symm 256 _ j hj

theorem wordBytes_foldr (w : UInt64) (acc : ℕ) :
    (wordBytes w).foldr (fun b acc ↦ b.toNat + 256 * acc) acc = w.toNat + 2 ^ 64 * acc := by
  have hw := w.toNat_lt
  rw [wordBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, UInt64.toNat_toUInt8,
    UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem digestBytes_foldr (a b c d : UInt64) :
    (digestBytes #v[a, b, c, d]).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      2 ^ 64 * (2 ^ 64 * (2 ^ 64 * d.toNat + c.toNat) + b.toNat) + a.toNat := by
  simp only [digestBytes, show (#v[a, b, c, d] : Vector UInt64 4).toList = [a, b, c, d] from rfl,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.foldr_append, wordBytes_foldr]
  ring

theorem digest_output_eq (s : KeccakState) :
    BitVec.ofNat 256 ((digestBytes #v[Keccak.lane s 0, Keccak.lane s 1, Keccak.lane s 2,
      Keccak.lane s 3]).foldr (fun b acc ↦ b.toNat + 256 * acc) 0) = out256 (keccakStateEquiv s).1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [digestBytes_foldr, BitVec.getLsbD_ofNat, getLsbD_out256 _ j hj, keccakStateEquiv_fst]
  simp only [hj, decide_true, Bool.true_and, bitOf_eq_one_iff, Bool.decide_eq_true]
  have h64 : ∀ w : UInt64, w.toNat < 2 ^ 64 := fun w ↦ w.toNat_lt
  rw [Nat.testBit_two_pow_mul_add _ (h64 _)]
  split_ifs with h0
  · rw [show j / 64 = 0 by omega, show j % 64 = j by omega]
    rfl
  rw [Nat.testBit_two_pow_mul_add _ (h64 _)]
  split_ifs with h1
  · rw [show j / 64 = 1 by omega, show j % 64 = j - 64 by omega]
    rfl
  rw [Nat.testBit_two_pow_mul_add _ (h64 _)]
  split_ifs with h2
  · rw [show j / 64 = 2 by omega, show j % 64 = j - 64 - 64 by omega]
    rfl
  · rw [show j / 64 = 3 by omega, show j % 64 = j - 64 - 64 - 64 by omega]
    rfl

/-- **Keccak-256 over a permutation is the sponge**, in any lawful monad. -/
theorem keccakHash_pure {m : Type → Type} [Monad m] [LawfulMonad m] (π : Equiv.Perm KeccakState)
    (input : HashInput) :
    keccakHash (fun s ↦ (pure (π s) : m KeccakState)) input =
      pure (out256 (spongeHash (spongeView π) (blocks input))) := by
  simp only [keccakHash, keccak256With]
  rw [absorbWith_pure]
  simp only [pure_bind, map_pure]
  rw [digest_output_eq, keccakStateEquiv_absorbWith, keccakStateEquiv_zero]
  rfl

/-- **Keccak-256 over a permutation is the sponge** (`keccakHash` in `Id`): `H` over `π` is the first
256 bits of the sponge hash under `π` transported to `X × Z`. -/
theorem keccakHash_eq_spongeHash (π : Equiv.Perm KeccakState) (input : HashInput) :
    Id.run (keccakHash (fun s ↦ (pure (π s) : Id KeccakState)) input) =
      out256 (spongeHash (spongeView π) (blocks input)) := by
  rw [keccakHash_pure]
  rfl

theorem simulateQ_absorbWith {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl Common.RandomPermutationOracles r) (π : Equiv.Perm KeccakState)
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (π s)) :
    ∀ (n : ℕ) (s : KeccakState) (data : List UInt8),
      simulateQ impl (absorbWith Common.queryPermutation n s data) =
        absorbWith (fun s ↦ (pure (π s) : r KeccakState)) n s data
  | 0, s, data => by
    simp only [absorbWith, absorbBlockWith, Common.queryPermutation, simulateQ_spec_query, himpl]
  | n + 1, s, data => by
    simp only [absorbWith, absorbBlockWith, simulateQ_bind, Common.queryPermutation,
      simulateQ_spec_query, himpl, pure_bind]
    exact simulateQ_absorbWith impl π himpl n _ _

/-- **Keccak-256 over `queryPermutation`** under any simulation that answers forward queries with
`π` is the sponge. -/
theorem simulateQ_keccakHash {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl Common.RandomPermutationOracles r) (π : Equiv.Perm KeccakState)
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (π s)) (input : HashInput) :
    simulateQ impl (keccakHash Common.queryPermutation input) =
      pure (out256 (spongeHash (spongeView π) (blocks input))) := by
  have h : simulateQ impl (keccakHash Common.queryPermutation input) =
      keccakHash (fun s ↦ (pure (π s) : r KeccakState)) input := by
    simp only [keccakHash, keccak256With, simulateQ_map, simulateQ_bind, simulateQ_pure,
      simulateQ_absorbWith impl π himpl]
  rw [h, keccakHash_pure]

/-! ## Digests -/

/-- **The digest of a rate**: `Truncate_16` of its hash output, its first 128 bits. -/
def trunc128 (x : X) : Digest :=
  truncateHash (out256 x)

theorem trunc128_eq (x : X) : trunc128 x = (bitsEquiv 128).symm fun j ↦ x (Fin.castAdd 960 j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj : j < 128 := hj
  change ((out256 x).extractLsb' 0 128).getLsbD j = ((bitsEquiv 128).symm _).getLsbD j
  rw [getLsbD_bitsEquiv_symm _ _ j hj, BitVec.getLsbD_extractLsb', getLsbD_out256 _ _ (by omega)]
  simp [hj]

/-- Each digest has `2^960` preimages under `trunc128`. -/
theorem card_fiber_trunc128 (d : Digest) :
    #(univ.filter fun x : X ↦ trunc128 x = d) = 2 ^ 960 := by
  calc #(univ.filter fun x : X ↦ trunc128 x = d)
      = #(univ.filter fun p : (Fin 128 → ZMod 2) × (Fin 960 → ZMod 2) ↦
          p.1 = bitsEquiv 128 d) :=
        card_equiv (Fin.appendEquiv (α := ZMod 2) 128 960).symm fun x ↦ by
          simp only [mem_filter, mem_univ, true_and, trunc128_eq]
          exact (bitsEquiv 128).symm_apply_eq
    _ = Fintype.card (Fin 960 → ZMod 2) := card_filter_fst_eq _
    _ = 2 ^ 960 := by simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-! ## The bytes of a block -/

/-- Bit `j` of a byte string: bit `j % 8` of byte `j / 8`, `0` past the end. -/
def inputBit (bytes : List UInt8) (j : ℕ) : ZMod 2 :=
  bitOf ((bytes.getD (j / 8) 0).toBitVec.getLsbD (j % 8))

private theorem getLsbD_laneFold (bytes : List UInt8) (i : ℕ) :
    ∀ K, K ≤ 8 → ∀ b, b < 64 →
      ((List.range K).foldl (fun acc k ↦ acc ||| ((bytes.getD (8 * i + k) 0).toUInt64 <<<
        (8 * k).toUInt64)) 0).toBitVec.getLsbD b =
        (decide (b < 8 * K) && (bytes.getD (8 * i + b / 8) 0).toBitVec.getLsbD (b % 8))
  | 0, _, b, _ => by simp
  | K + 1, hK, b, hb => by
    have hs : ((8 * K).toUInt64.toBitVec % 64).toNat = 8 * K := by
      simp [BitVec.toNat_umod]
      omega
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, UInt64.toBitVec_or,
      BitVec.getLsbD_or, getLsbD_laneFold bytes i K (by omega) b hb, UInt64.toBitVec_shiftLeft,
      BitVec.getLsbD_shiftLeft', hs, UInt8.toBitVec_toUInt64, BitVec.getLsbD_setWidth]
    by_cases h1 : b < 8 * K
    · simp [h1, show b < 8 * (K + 1) by omega]
    · by_cases h2 : b < 8 * (K + 1)
      · simp [h1, h2, hb, show b / 8 = K by omega, show b % 8 = b - 8 * K by omega,
          show b - 8 * K < 64 by omega]
      · have hge : ∀ c : UInt8, c.toBitVec.getLsbD (b - 8 * K) = false :=
          fun c ↦ BitVec.getLsbD_of_ge _ _ (by omega)
        simp [h1, h2, hge]

/-- Bit `b` of the little-endian lane `i` of a byte string is bit `b % 8` of byte `8 i + b / 8`. -/
theorem getLsbD_littleEndianLane (bytes : List UInt8) (i b : ℕ) (hb : b < 64) :
    (littleEndianLane bytes i).toBitVec.getLsbD b =
      (bytes.getD (8 * i + b / 8) 0).toBitVec.getLsbD (b % 8) := by
  rw [littleEndianLane, getLsbD_laneFold bytes i 8 le_rfl b hb]
  simp [show b < 8 * 8 by omega]

/-- Rate bit `j` of a block is bit `j` of its bytes. -/
theorem blockOf_apply (block : List UInt8) (j : Fin 1088) : blockOf block j = inputBit block j := by
  simp only [blockOf, laneEquiv_apply]
  rw [getLsbD_littleEndianLane _ _ _ (Nat.mod_lt _ (by norm_num)), inputBit,
    show 8 * ((j : ℕ) / 64) + (j : ℕ) % 64 / 8 = (j : ℕ) / 8 by omega,
    show (j : ℕ) % 64 % 8 = (j : ℕ) % 8 by omega]

/-- The padded last block: the remaining bytes, then `0x01`, zeros, and `0x80` XORed into byte
`135`. -/
theorem padBlock_getD (rem : List UInt8) (hr : rem.length < 136) (k : ℕ) (hk : k < 136) :
    (padBlock rem).getD k 0 =
      if k < rem.length then rem.getD k 0
      else (if rem.length = k then padFirst else 0) ^^^ (if 135 = k then padLast else 0) := by
  simp only [padBlock, LeanVM.Protocol.KeccakHash.rate, List.getD_eq_getElem?_getD,
    List.getElem?_modify, List.getElem?_append, List.getElem?_replicate]
  by_cases h1 : k < rem.length
  · have h2 : rem.length ≠ k := by omega
    have h3 : (135 : ℕ) ≠ k := by omega
    simp [h1, h2, h3]
  · have h4 : k - rem.length < 136 - rem.length := by omega
    by_cases h2 : rem.length = k <;> by_cases h3 : (135 : ℕ) = k <;>
      simp [h1, h2, h3, h4, hk]

/-- The first block `blocks` absorbs, as bytes: the first 136 bytes, or the padded input. -/
def firstBlock (input : HashInput) : List UInt8 :=
  if input.length < 136 then padBlock input else input.take 136

theorem firstBlock_of_lt (input : HashInput) (h : input.length < 136) :
    firstBlock input = padBlock input := by
  rw [firstBlock, ite_eq_left h]

theorem head?_blocks (input : HashInput) :
    (blocks input).head? = some (blockOf (firstBlock input)) := by
  rw [blocks, firstBlock]
  rcases h : input.length / LeanVM.Protocol.KeccakHash.rate with _ | n
  · simp only [LeanVM.Protocol.KeccakHash.rate] at h
    rw [ite_eq_left (by omega)]
    rfl
  · simp only [LeanVM.Protocol.KeccakHash.rate] at h
    rw [ite_eq_right (by omega)]
    rfl

theorem firstBlock_getD (input : HashInput) (k : ℕ) (hk : k < input.length) (hk' : k < 136) :
    (firstBlock input).getD k 0 = input.getD k 0 := by
  rw [firstBlock]
  split_ifs with h
  · rw [padBlock_getD input h k hk', ite_eq_left hk]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      ite_eq_left hk']

theorem blockOf_firstBlock (input : HashInput) (j : Fin 1088) (hj : (j : ℕ) < 8 * input.length) :
    blockOf (firstBlock input) j = inputBit input j := by
  rw [blockOf_apply, inputBit, inputBit, firstBlock_getD input _ (by omega) (by omega)]

theorem head?_absorbTail (φ : Equiv.Perm (X × Z)) (m : List X) :
    (absorbTail φ m).head? = m.head? := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m b ih =>
    rw [absorbTail_append_singleton]
    cases m with
    | nil => simp [absorb]
    | cons a m =>
      rw [List.head?_append, ih]
      rfl

/-- The Msponge tail of an input starts with its first block, and has one more block per whole
block of 136 bytes. -/
theorem absorbTail_blocks (φ : Equiv.Perm (X × Z)) (input : HashInput) :
    ∃ rest, absorbTail φ (blocks input) = blockOf (firstBlock input) :: rest ∧
      rest.length = input.length / 136 := by
  have hh := head?_absorbTail φ (blocks input)
  have hl := length_absorbTail φ (blocks input)
  rw [head?_blocks] at hh
  rw [length_blocks] at hl
  cases ht : absorbTail φ (blocks input) with
  | nil => rw [ht] at hl; simp at hl
  | cons x rest =>
    rw [ht] at hh hl
    simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    exact ⟨rest, by rw [hh], hl⟩

/-! ## The bytes of a tweakable-hash input -/

theorem length_littleEndianBytes (n : ℕ) (v : BitVec (8 * n)) :
    (littleEndianBytes n v).length = n :=
  List.length_ofFn

theorem inputBit_append_left (a b : List UInt8) (j : ℕ) (h : j < 8 * a.length) :
    inputBit (a ++ b) j = inputBit a j := by
  simp only [inputBit, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem inputBit_append_right (a b : List UInt8) (j : ℕ) :
    inputBit (a ++ b) (8 * a.length + j) = inputBit b j := by
  simp only [inputBit, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), show (8 * a.length + j) / 8 - a.length = j / 8 by omega,
    show (8 * a.length + j) % 8 = j % 8 by omega]

theorem inputBit_littleEndianBytes (n : ℕ) (v : BitVec (8 * n)) (j : ℕ) :
    inputBit (littleEndianBytes n v) j = bitOf (v.getLsbD j) := by
  rw [inputBit, littleEndianBytes, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with h
  · simp [Nat.div_add_mod, Nat.mod_lt j (show 8 > 0 by norm_num)]
  · rw [Option.getD_none, BitVec.getLsbD_of_ge v j (by omega)]
    simp

theorem length_addressBytes (fields : TweakFields) : (addressBytes fields).length = 16 := by
  simp only [addressBytes, List.length_append, length_littleEndianBytes]

theorem inputBit_addressBytes_lo (fields : TweakFields) (j : ℕ) (hj : j < 32) :
    inputBit (addressBytes fields) j = bitOf (fields.lo.getLsbD j) := by
  rw [addressBytes, inputBit_append_left _ _ _ (by simp [length_littleEndianBytes]; omega),
    inputBit_append_left _ _ _ (by simp [length_littleEndianBytes]; omega),
    inputBit_append_left _ _ _ (by simp [length_littleEndianBytes]; omega),
    inputBit_littleEndianBytes]

theorem inputBit_addressBytes_hi (fields : TweakFields) (j : ℕ) (hj : j < 24) :
    inputBit (addressBytes fields) (32 + j) = bitOf (fields.hi.getLsbD j) := by
  rw [addressBytes, inputBit_append_left _ _ _ (by simp [length_littleEndianBytes]; omega),
    inputBit_append_left _ _ _ (by simp [length_littleEndianBytes]; omega),
    show 32 + j = 8 * (littleEndianBytes 4 fields.lo).length + j by
      rw [length_littleEndianBytes],
    inputBit_append_right, inputBit_littleEndianBytes]

theorem inputBit_addressBytes_stepTag (fields : TweakFields) (j : ℕ) (hj : j < 8) :
    inputBit (addressBytes fields) (56 + j) = bitOf ((fields.step ++ fields.tag).getLsbD j) := by
  rw [addressBytes, inputBit_append_left _ _ _ (by simp [length_littleEndianBytes]; omega),
    show 56 + j = 8 * (littleEndianBytes 4 fields.lo ++ littleEndianBytes 3 fields.hi).length + j by
      rw [List.length_append, length_littleEndianBytes, length_littleEndianBytes],
    inputBit_append_right, inputBit_littleEndianBytes]

theorem length_thInput (Q : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    (thInput Q fields payload).length = 32 + payload.length := by
  simp only [thInput, hasherInput, List.length_append, length_littleEndianBytes,
    length_addressBytes]

theorem inputBit_thInput_prefix (Q : PublicParameter) (fields : TweakFields) (payload : HashInput)
    (j : ℕ) (hj : j < 128) : inputBit (thInput Q fields payload) j = bitOf (Q.getLsbD j) := by
  rw [thInput, hasherInput,
    inputBit_append_left _ _ _ (by simp [length_littleEndianBytes, length_addressBytes]; omega),
    inputBit_append_left _ _ _ (by simp [length_littleEndianBytes]; omega),
    inputBit_littleEndianBytes]

theorem inputBit_thInput_address (Q : PublicParameter) (fields : TweakFields)
    (payload : HashInput) (j : ℕ) (hj : j < 128) :
    inputBit (thInput Q fields payload) (128 + j) = inputBit (addressBytes fields) j := by
  rw [thInput, hasherInput,
    inputBit_append_left _ _ _ (by simp [length_littleEndianBytes, length_addressBytes]; omega),
    show 128 + j = 8 * (littleEndianBytes 16 Q).length + j by rw [length_littleEndianBytes],
    inputBit_append_right]

theorem inputBit_thInput_payload (Q : PublicParameter) (fields : TweakFields)
    (payload : HashInput) (j : ℕ) :
    inputBit (thInput Q fields payload) (256 + j) = inputBit payload j := by
  rw [thInput, hasherInput,
    show 256 + j = 8 * (littleEndianBytes 16 Q ++ addressBytes fields).length + j by
      rw [List.length_append, length_littleEndianBytes, length_addressBytes],
    inputBit_append_right]

/-! ## Slots -/

/-- Bits `a` to `a + n - 1` of a rate, as a bit vector. -/
def rateSlice (x : X) (a n : ℕ) (h : a + n ≤ 1088) : BitVec n :=
  ofBits fun j : Fin n ↦ x ⟨a + j, by omega⟩

theorem rateSlice_eq {x : X} {a n : ℕ} {h : a + n ≤ 1088} {v : BitVec n}
    (hv : ∀ j (hj : j < n), x ⟨a + j, by omega⟩ = bitOf (v.getLsbD j)) :
    rateSlice x a n h = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [rateSlice, getLsbD_ofBits _ j hj]
  simp only [hv j hj, bitOf_eq_one_iff, Bool.decide_eq_true]

/-- The hash call a Msponge tail belongs to: a chain step (its address and the chain index in its
payload), a leaf, a tree node, a message digest, a chain-start derivation, a randomizer base, the
public parameter, or the scheme seed. -/
inductive Slot where
  /-- Step `step` of chain `chain` of key `key` of layer `layer`. -/
  | chain (layer : Layer) (key : KeyIndex) (step : ChainStep) (chain : ChainIndex)
  /-- The leaf of key `key`. -/
  | leaf (layer : Layer) (key : KeyIndex)
  /-- The node at `level`, index `nodeIndex`. -/
  | node (layer : Layer) (level nodeIndex : ℕ)
  /-- The message digest of key `key`. -/
  | msg (layer : Layer) (key : KeyIndex)
  /-- The starts of chains `2 pair` and `2 pair + 1` of key `key`. -/
  | prf (layer : Layer) (key : KeyIndex) (pair : ChainPairIndex)
  /-- The randomizer base `R0` of key `key`. -/
  | rnd (layer : Layer) (key : KeyIndex)
  /-- The public parameter `P`. -/
  | param
  /-- The scheme seed `S = H("leanXMSS" ‖ S_0)`. -/
  | seed
  deriving DecidableEq

/-- The layer an address's `hi` field names: its bit 23. -/
def layerOf (hi : BitVec 24) : Layer :=
  ⟨hi.toNat / 2 ^ 23, by
    have := hi.isLt
    simp only [layerCount, Nat.reducePow] at this ⊢
    omega⟩

/-- The rest of an address's `hi` field: its low 23 bits. -/
def lowOf (hi : BitVec 24) : ℕ :=
  hi.toNat % 2 ^ 23

/-- The key an address's `lo` field names. -/
def keyOf (lo : BitVec 32) : KeyIndex :=
  ⟨lo.toNat, by
    have := lo.isLt
    simp only [lifetime, layerCount, layerHeight, Nat.reduceMul, Nat.reducePow] at this ⊢
    omega⟩

/-- The slot of a `P`-prefixed call at the address `fields`; `index` is the payload's second 16
bytes, a chain step's chain index. -/
def fieldsSlot (fields : TweakFields) (index : BitVec 128) : Option Slot :=
  match fields.tag.toNat with
  | 0 => if h : lowOf fields.hi < 29 then
      some (.prf (layerOf fields.hi) (keyOf fields.lo) ⟨_, h⟩) else none
  | 1 => if h : fields.step.toNat < 3 ∧ index.toNat < 58 then
      some (.chain (layerOf fields.hi) (keyOf fields.lo) ⟨_, h.1⟩ ⟨_, h.2⟩) else none
  | 2 => some (.leaf (layerOf fields.hi) (keyOf fields.lo))
  | 3 => some (.node (layerOf fields.hi) (lowOf fields.hi) fields.lo.toNat)
  | 7 => some (.rnd (layerOf fields.hi) (keyOf fields.lo))
  | 12 => some (.msg (layerOf fields.hi) (keyOf fields.lo))
  | _ => none

/-- The slot of a call with prefix `Q` at the address `fields`, for the public parameter `P`: the
parameter derivation (prefix `0`, type `5`), or a `P`-prefixed call (`fieldsSlot`). -/
def slotOfAddress (P Q : PublicParameter) (fields : TweakFields) (index : BitVec 128) :
    Option Slot :=
  if Q = 0 ∧ fields.tag = 5 then some .param else if Q = P then fieldsSlot fields index else none

/-- The slot a first block names: its prefix (bytes `0` to `15`), address (bytes `16` to `31`)
and the payload's second 16 bytes (bytes `48` to `63`). -/
def slotOfBlock (P : PublicParameter) (x : X) : Option Slot :=
  slotOfAddress P (rateSlice x 0 128 (by norm_num))
    ⟨rateSlice x 184 5 (by norm_num), rateSlice x 189 3 (by norm_num),
      rateSlice x 160 24 (by norm_num), rateSlice x 128 32 (by norm_num)⟩
    (rateSlice x 384 128 (by norm_num))

/-- A one-block tail of the seed derivation's shape: `leanXMSS`, 32 bytes, and the padding of a
40-byte input. -/
def SeedShaped (x : X) : Prop :=
  (∀ j : Fin 1088, (j : ℕ) < 64 → x j = inputBit seedTag j) ∧
    ∀ j : Fin 1088, 320 ≤ (j : ℕ) → x j = if (j : ℕ) = 320 ∨ (j : ℕ) = 1087 then 1 else 0

instance (x : X) : Decidable (SeedShaped x) := by
  unfold SeedShaped
  infer_instance

/-- **The slot of a Msponge tail** for the public parameter `P`: the seed derivation if it is one
block of that shape, else the slot its first block names. -/
def slotOf (P : PublicParameter) : List X → Option Slot
  | [] => none
  | x :: rest => if rest.isEmpty ∧ SeedShaped x then some .seed else slotOfBlock P x

/-- The payload's second 16 bytes, as a bit vector. -/
def payloadIndex (payload : HashInput) : BitVec 128 :=
  ofBits fun j : Fin 128 ↦ inputBit payload (128 + j)

theorem slotOfBlock_thInput (P Q : PublicParameter) (fields : TweakFields) (payload : HashInput)
    (hp : 32 ≤ payload.length) :
    slotOfBlock P (blockOf (firstBlock (thInput Q fields payload))) =
      slotOfAddress P Q fields (payloadIndex payload) := by
  set x := blockOf (firstBlock (thInput Q fields payload))
  have hx : ∀ j (hj : j < 512), x ⟨j, by omega⟩ = inputBit (thInput Q fields payload) j :=
    fun j hj ↦ blockOf_firstBlock _ _ (by rw [length_thInput]; simp only; omega)
  have hQ : rateSlice x 0 128 (by norm_num) = Q := rateSlice_eq fun j hj ↦ by
    rw [hx (0 + j) (by omega), zero_add, inputBit_thInput_prefix _ _ _ _ hj]
  have hlo : rateSlice x 128 32 (by norm_num) = fields.lo := rateSlice_eq fun j hj ↦ by
    rw [hx (128 + j) (by omega), inputBit_thInput_address _ _ _ _ (by omega),
      inputBit_addressBytes_lo _ _ hj]
  have hhi : rateSlice x 160 24 (by norm_num) = fields.hi := rateSlice_eq fun j hj ↦ by
    rw [hx (160 + j) (by omega), show 160 + j = 128 + (32 + j) by omega,
      inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_hi _ _ hj]
  have htag : rateSlice x 184 5 (by norm_num) = fields.tag := rateSlice_eq fun j hj ↦ by
    rw [hx (184 + j) (by omega), show 184 + j = 128 + (56 + j) by omega,
      inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_stepTag _ _ (by omega),
      BitVec.getLsbD_append, ite_eq_left hj]
  have hstep : rateSlice x 189 3 (by norm_num) = fields.step := rateSlice_eq fun j hj ↦ by
    rw [hx (189 + j) (by omega), show 189 + j = 128 + (56 + (5 + j)) by omega,
      inputBit_thInput_address _ _ _ _ (by omega), inputBit_addressBytes_stepTag _ _ (by omega),
      BitVec.getLsbD_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hidx : rateSlice x 384 128 (by norm_num) = payloadIndex payload := rateSlice_eq fun j hj ↦ by
    rw [hx (384 + j) (by omega), show 384 + j = 256 + (128 + j) by omega,
      inputBit_thInput_payload, payloadIndex, getLsbD_ofBits _ j hj, bitOf_decide_eq_one]
  rw [slotOfBlock, hQ, hlo, hhi, htag, hstep, hidx]

theorem not_seedShaped_padBlock (input : HashInput) (h1 : 40 < input.length)
    (h2 : input.length < 136) : ¬SeedShaped (blockOf (padBlock input)) := by
  intro hs
  have h := hs.2 ⟨8 * input.length, by omega⟩ (show 320 ≤ 8 * input.length by omega)
  rw [blockOf_apply, inputBit] at h
  simp only [show 8 * input.length / 8 = input.length by omega,
    show 8 * input.length % 8 = 0 by omega] at h
  rw [padBlock_getD input h2 _ h2, ite_eq_right (lt_irrefl _), ite_eq_left rfl,
    ite_eq_right (show ¬(8 * input.length = 320 ∨ 8 * input.length = 1087) by omega)] at h
  by_cases h3 : 135 = input.length
  · rw [ite_eq_left h3] at h
    exact absurd h (by decide)
  · rw [ite_eq_right h3] at h
    exact absurd h (by decide)

/-- **The slot of a tweakable-hash input's tail** (payload of at least 32 bytes): the slot its
prefix, address and payload name. -/
theorem slotOf_thInput (φ : Equiv.Perm (X × Z)) (P Q : PublicParameter) (fields : TweakFields)
    (payload : HashInput) (hp : 32 ≤ payload.length) :
    slotOf P (absorbTail φ (blocks (thInput Q fields payload))) =
      slotOfAddress P Q fields (payloadIndex payload) := by
  obtain ⟨rest, ht, hl⟩ := absorbTail_blocks φ (thInput Q fields payload)
  have hL := length_thInput Q fields payload
  rw [ht, slotOf, ite_eq_right, slotOfBlock_thInput P Q fields payload hp]
  rintro ⟨hr, hs⟩
  rw [List.isEmpty_iff] at hr
  subst hr
  have h136 : (thInput Q fields payload).length < 136 := by
    rw [List.length_nil] at hl
    omega
  rw [firstBlock, ite_eq_left h136] at hs
  exact not_seedShaped_padBlock _ (by omega) h136 hs

private theorem seedPad_bit (q r : ℕ) (hq : 40 ≤ q) (hr : r < 8) :
    bitOf (((if 40 = q then padFirst else 0) ^^^ (if 135 = q then padLast else 0)).toBitVec.getLsbD
      r) = if 8 * q + r = 320 ∨ 8 * q + r = 1087 then 1 else 0 := by
  by_cases h40 : 40 = q
  · subst h40
    interval_cases r <;> decide
  · by_cases h135 : 135 = q
    · subst h135
      interval_cases r <;> decide
    · rw [ite_eq_right h40, ite_eq_right h135, ite_eq_right (by omega),
        show (0 ^^^ 0 : UInt8) = 0 from rfl]
      simp

theorem seedShaped_seedInput (masterSeed : MasterSeed) :
    SeedShaped (blockOf (padBlock (seedTag ++ littleEndianBytes 32 masterSeed))) := by
  have hst : seedTag.length = 8 := rfl
  have hlen : (seedTag ++ littleEndianBytes 32 masterSeed).length = 40 := by
    rw [List.length_append, hst, length_littleEndianBytes]
  have hfb := firstBlock_of_lt (seedTag ++ littleEndianBytes 32 masterSeed)
    (by rw [hlen]; norm_num)
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · rw [← hfb, blockOf_firstBlock _ j (by rw [hlen]; omega),
      inputBit_append_left _ _ _ (by rw [hst]; omega)]
  · rw [blockOf_apply, inputBit, padBlock_getD _ (by rw [hlen]; norm_num) _ (by omega), hlen,
      ite_eq_right (by omega)]
    conv_rhs => rw [← Nat.div_add_mod (j : ℕ) 8]
    exact seedPad_bit _ _ (by omega) (Nat.mod_lt _ (by norm_num))

/-- The scheme seed's derivation `H("leanXMSS" ‖ S_0)` has the slot `seed`. -/
theorem slotOf_seed (φ : Equiv.Perm (X × Z)) (P : PublicParameter) (masterSeed : MasterSeed) :
    slotOf P (absorbTail φ (blocks (seedTag ++ littleEndianBytes 32 masterSeed))) = some .seed := by
  obtain ⟨rest, ht, hl⟩ := absorbTail_blocks φ (seedTag ++ littleEndianBytes 32 masterSeed)
  have hlen : (seedTag ++ littleEndianBytes 32 masterSeed).length = 40 := by
    rw [List.length_append, show seedTag.length = 8 from rfl, length_littleEndianBytes]
  rw [hlen] at hl
  have hr : rest = [] := List.eq_nil_of_length_eq_zero hl
  subst hr
  rw [ht, slotOf, firstBlock_of_lt _ (by rw [hlen]; norm_num)]
  exact ite_eq_left ⟨rfl, seedShaped_seedInput masterSeed⟩

/-! ### The slot of each honest call -/

theorem slotOfAddress_self (P : PublicParameter) (fields : TweakFields) (index : BitVec 128)
    (h : fields.tag ≠ 5) : slotOfAddress P P fields index = fieldsSlot fields index := by
  rw [slotOfAddress, ite_eq_right (fun h' ↦ h h'.2), ite_eq_left rfl]

theorem toNat_layerHi (layer : Layer) (v : ℕ) (hv : v < 2 ^ 23) :
    (BitVec.ofNat 24 (layerHi layer v)).toNat = v + 2 ^ 23 * layer.val := by
  have hl : layer.val < 2 := layer.isLt
  simp only [BitVec.toNat_ofNat, layerHi, Nat.reducePow] at hv ⊢
  omega

theorem layerOf_layerHi (layer : Layer) (v : ℕ) (hv : v < 2 ^ 23) :
    layerOf (BitVec.ofNat 24 (layerHi layer v)) = layer := by
  have hl : layer.val < 2 := layer.isLt
  apply Fin.ext
  simp only [layerOf, toNat_layerHi layer v hv]
  simp only [Nat.reducePow] at hv ⊢
  omega

theorem lowOf_layerHi (layer : Layer) (v : ℕ) (hv : v < 2 ^ 23) :
    lowOf (BitVec.ofNat 24 (layerHi layer v)) = v := by
  have hl : layer.val < 2 := layer.isLt
  simp only [lowOf, toNat_layerHi layer v hv]
  simp only [Nat.reducePow] at hv ⊢
  omega

theorem keyOf_ofNat (key : KeyIndex) : keyOf (BitVec.ofNat 32 key.val) = key := by
  have hk : key.val < 2 ^ 32 := key.isLt
  apply Fin.ext
  simp only [keyOf, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hk

theorem payloadIndex_pair (v : Digest) (w : BitVec 128) :
    payloadIndex (littleEndianBytes 16 v ++ littleEndianBytes 16 w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [payloadIndex, getLsbD_ofBits _ j hj,
    show 128 + j = 8 * (littleEndianBytes 16 v).length + j by simp [littleEndianBytes],
    inputBit_append_right, inputBit_littleEndianBytes]
  simp

theorem length_flatMap_littleEndianBytes (l : List (BitVec (8 * 16))) :
    (l.flatMap (littleEndianBytes 16)).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_littleEndianBytes, List.length_cons]
    ring

theorem slotOf_chain (φ : Equiv.Perm (X × Z)) (P : PublicParameter) (layer : Layer)
    (key : KeyIndex) (step : ChainStep) (chain : ChainIndex) (value : Digest) :
    slotOf P (absorbTail φ (blocks (thInput P (hashDomainFields (.chain layer key step))
      (Verification.chainPayload chain value)))) = some (.chain layer key step chain) := by
  have hs : (step : ℕ) % 2 ^ 3 = step := Nat.mod_eq_of_lt (lt_of_lt_of_le step.isLt (by decide))
  have hc : (chain : ℕ) % 2 ^ 128 = chain :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le chain.isLt (by decide))
  simp only [Nat.reducePow] at hs hc
  rw [slotOf_thInput _ _ _ _ _ (by simp [Verification.chainPayload, littleEndianBytes]),
    Verification.chainPayload, payloadIndex_pair,
    slotOfAddress_self _ _ _ (by show BitVec.ofNat 5 1 ≠ 5; decide)]
  simp [fieldsSlot, hashDomainFields, tweakFields, layerOf_layerHi layer 0 (by norm_num),
    keyOf_ofNat, hs, hc]
  exact ⟨step.isLt, chain.isLt⟩

theorem slotOf_leaf (φ : Equiv.Perm (X × Z)) (P : PublicParameter) (layer : Layer)
    (key : KeyIndex) (endpoints : ChainIndex → Digest) :
    slotOf P (absorbTail φ (blocks (thInput P (hashDomainFields (.leaf layer key))
      (digestsPayload endpoints)))) = some (.leaf layer key) := by
  have h : (digestsPayload endpoints).length = 16 * chainCount :=
    (length_flatMap_littleEndianBytes (List.ofFn endpoints)).trans
      (congrArg (16 * ·) (List.length_ofFn (f := endpoints)))
  rw [slotOf_thInput _ _ _ _ _ (by rw [h]; decide),
    slotOfAddress_self _ _ _ (by show BitVec.ofNat 5 2 ≠ 5; decide)]
  simp [fieldsSlot, hashDomainFields, tweakFields, layerOf_layerHi layer 0 (by norm_num),
    keyOf_ofNat]

theorem slotOf_node (φ : Equiv.Perm (X × Z)) (P : PublicParameter) (layer : Layer)
    (level nodeIndex : ℕ) (hlevel : level < 2 ^ 23) (hindex : nodeIndex < 2 ^ 32)
    (left right : Digest) :
    slotOf P (absorbTail φ (blocks (thInput P (hashDomainFields (.node layer level nodeIndex))
      (nodePayload left right)))) = some (.node layer level nodeIndex) := by
  rw [slotOf_thInput _ _ _ _ _ (by simp [nodePayload, littleEndianBytes]),
    slotOfAddress_self _ _ _ (by show BitVec.ofNat 5 3 ≠ 5; decide)]
  simp [fieldsSlot, hashDomainFields, tweakFields, layerOf_layerHi layer level hlevel,
    lowOf_layerHi layer level hlevel, show nodeIndex < 4294967296 from hindex]

theorem slotOf_msg (φ : Equiv.Perm (X × Z)) (P : PublicParameter) (layer : Layer)
    (key : KeyIndex) (message : HashInput) (hm : 16 ≤ message.length) (randomizer : Randomizer) :
    slotOf P (absorbTail φ (blocks (thInput P (hashDomainFields (.message layer key))
      (message ++ littleEndianBytes 16 randomizer)))) = some (.msg layer key) := by
  rw [slotOf_thInput _ _ _ _ _ (by simp [littleEndianBytes]; omega),
    slotOfAddress_self _ _ _ (by show BitVec.ofNat 5 12 ≠ 5; decide)]
  simp [fieldsSlot, hashDomainFields, tweakFields, layerOf_layerHi layer 0 (by norm_num),
    keyOf_ofNat]

theorem slotOf_prf (φ : Equiv.Perm (X × Z)) (P : PublicParameter) (layer : Layer)
    (key : KeyIndex) (pair : ChainPairIndex) (seed : MasterSeed) :
    slotOf P (absorbTail φ (blocks (thInput P (keygenDomainFields (.oneTimeChainPair layer key pair))
      (littleEndianBytes 32 seed)))) = some (.prf layer key pair) := by
  have hp : pair.val < 29 := pair.isLt
  rw [slotOf_thInput _ _ _ _ _ (by simp [length_littleEndianBytes]),
    slotOfAddress_self _ _ _ (by show BitVec.ofNat 5 0 ≠ 5; decide)]
  simp [fieldsSlot, keygenDomainFields, tweakFields, layerOf_layerHi layer pair (by omega),
    lowOf_layerHi layer pair (by omega), keyOf_ofNat, hp]

theorem slotOf_rnd (φ : Equiv.Perm (X × Z)) (P : PublicParameter) (layer : Layer)
    (key : KeyIndex) (seed : MasterSeed) (message : HashInput) :
    slotOf P (absorbTail φ (blocks (thInput P (tweakFields 7 0 (layerHi layer 0) key)
      (littleEndianBytes 32 seed ++ message)))) = some (.rnd layer key) := by
  rw [slotOf_thInput _ _ _ _ _ (by simp [length_littleEndianBytes]),
    slotOfAddress_self _ _ _ (by show BitVec.ofNat 5 7 ≠ 5; decide)]
  simp [fieldsSlot, tweakFields, layerOf_layerHi layer 0 (by norm_num), keyOf_ofNat]

theorem slotOf_param (φ : Equiv.Perm (X × Z)) (P : PublicParameter) (seed : MasterSeed) :
    slotOf P (absorbTail φ (blocks (thInput 0 (keygenDomainFields .parameter)
      (littleEndianBytes 32 seed)))) = some .param := by
  rw [slotOf_thInput _ _ _ _ _ (by simp [length_littleEndianBytes]), slotOfAddress,
    ite_eq_left ⟨rfl, rfl⟩]

/-! ## Tails determine inputs -/

theorem getD_eq_of_blockOf_eq {b b' : List UInt8} (h : blockOf b = blockOf b') (k : ℕ)
    (hk : k < 136) : b.getD k 0 = b'.getD k 0 := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  have := congrFun h ⟨8 * k + r, by omega⟩
  rw [blockOf_apply, blockOf_apply, inputBit, inputBit] at this
  simp only [show (8 * k + r) / 8 = k by omega, show (8 * k + r) % 8 = r by omega] at this
  exact bitOf_injective this

theorem eq_of_getD_eq {a b : List UInt8} (hl : a.length = b.length)
    (h : ∀ k < a.length, a.getD k 0 = b.getD k 0) : a = b := by
  apply List.ext_getElem hl
  intro k h1 h2
  have := h k h1
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

theorem padBlock_injective {a b : List UInt8} (ha : a.length < 136) (hb : b.length < 136)
    (h : blockOf (padBlock a) = blockOf (padBlock b)) : a = b := by
  have hg := getD_eq_of_blockOf_eq h
  have key : ∀ {a b : List UInt8}, a.length < 136 → b.length < 136 →
      (∀ k < 136, (padBlock a).getD k 0 = (padBlock b).getD k 0) → ¬a.length < b.length := by
    intro a b ha hb hg hlt
    have := hg b.length hb
    rw [padBlock_getD a ha _ hb, padBlock_getD b hb _ hb, ite_eq_right (by omega),
      ite_eq_right (lt_irrefl _), ite_eq_right (by omega), ite_eq_left rfl] at this
    by_cases h3 : 135 = b.length
    · rw [ite_eq_left h3] at this
      exact absurd this (by decide)
    · rw [ite_eq_right h3] at this
      exact absurd this (by decide)
  have hlen : a.length = b.length := by
    have h1 := key ha hb hg
    have h2 := key hb ha fun k hk ↦ (hg k hk).symm
    omega
  refine eq_of_getD_eq hlen fun k hk ↦ ?_
  have := hg k (by omega)
  rwa [padBlock_getD a ha _ (by omega), padBlock_getD b hb _ (by omega), ite_eq_left hk,
    ite_eq_left (hlen ▸ hk)] at this

theorem blockBytes_injective : ∀ (n : ℕ) (a b : List UInt8), a.length / 136 = n →
    b.length / 136 = n → (blockBytes n a).map blockOf = (blockBytes n b).map blockOf → a = b
  | 0, a, b, ha, hb, h => by
    simp only [blockBytes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact padBlock_injective (by omega) (by omega) h
  | n + 1, a, b, ha, hb, h => by
    simp only [blockBytes, LeanVM.Protocol.KeccakHash.rate, List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have htake : a.take 136 = b.take 136 :=
      eq_of_getD_eq (by simp only [List.length_take]; omega) fun k hk ↦
        getD_eq_of_blockOf_eq h1 k (by simp only [List.length_take] at hk; omega)
    have hdrop : a.drop 136 = b.drop 136 :=
      blockBytes_injective n _ _ (by simp only [List.length_drop]; omega)
        (by simp only [List.length_drop]; omega) h2
    rw [← List.take_append_drop 136 a, ← List.take_append_drop 136 b, htake, hdrop]

/-- Distinct inputs have distinct blocks: Keccak's padding is injective. -/
theorem blocks_injective : Function.Injective blocks := by
  intro a b h
  have hl := congrArg List.length h
  rw [length_blocks, length_blocks] at hl
  have hn : b.length / 136 = a.length / 136 := by omega
  simp only [blocks, LeanVM.Protocol.KeccakHash.rate] at h
  rw [hn] at h
  exact blockBytes_injective _ a b rfl hn h

theorem addressBytes_injective : Function.Injective addressBytes := by
  intro f f' h
  have hb : ∀ j, inputBit (addressBytes f) j = inputBit (addressBytes f') j := fun j ↦ by rw [h]
  have hlo : f.lo = f'.lo := BitVec.eq_of_getLsbD_eq fun j hj ↦ bitOf_injective (by
    have := hb j
    rwa [inputBit_addressBytes_lo _ _ hj, inputBit_addressBytes_lo _ _ hj] at this)
  have hhi : f.hi = f'.hi := BitVec.eq_of_getLsbD_eq fun j hj ↦ bitOf_injective (by
    have := hb (32 + j)
    rwa [inputBit_addressBytes_hi _ _ hj, inputBit_addressBytes_hi _ _ hj] at this)
  have hst : f.step ++ f.tag = f'.step ++ f'.tag := BitVec.eq_of_getLsbD_eq fun j hj ↦
    bitOf_injective (by
      have := hb (56 + j)
      rwa [inputBit_addressBytes_stepTag _ _ hj, inputBit_addressBytes_stepTag _ _ hj] at this)
  have htag : f.tag = f'.tag := BitVec.eq_of_getLsbD_eq fun j hj ↦ by
    have := congrArg (fun v ↦ v.getLsbD j) hst
    rw [BitVec.getLsbD_append, BitVec.getLsbD_append, ite_eq_left hj, ite_eq_left hj] at this
    exact this
  have hstep : f.step = f'.step := BitVec.eq_of_getLsbD_eq fun j hj ↦ by
    have := congrArg (fun v ↦ v.getLsbD (5 + j)) hst
    rw [BitVec.getLsbD_append, BitVec.getLsbD_append, ite_eq_right (show ¬(5 + j < 5) by omega),
      ite_eq_right (show ¬(5 + j < 5) by omega), Nat.add_sub_cancel_left] at this
    exact this
  cases f
  cases f'
  simp_all

/-- The prefix fixed, a tweakable-hash input determines its address and payload. -/
theorem thInput_injective (Q : PublicParameter) {f f' : TweakFields} {p p' : HashInput}
    (h : thInput Q f p = thInput Q f' p') : f = f' ∧ p = p' := by
  unfold thInput hasherInput at h
  obtain ⟨h1, h2⟩ := List.append_inj h
    (by simp only [List.length_append, length_littleEndianBytes, length_addressBytes])
  exact ⟨addressBytes_injective (List.append_cancel_left h1), h2⟩

/-- **Tails determine inputs**: two tweakable-hash inputs with the same prefix and the same Msponge
tail have the same address and payload. -/
theorem absorbTail_blocks_thInput_injective (φ : Equiv.Perm (X × Z)) (Q : PublicParameter)
    {f f' : TweakFields} {p p' : HashInput}
    (h : absorbTail φ (blocks (thInput Q f p)) = absorbTail φ (blocks (thInput Q f' p'))) :
    f = f' ∧ p = p' :=
  thInput_injective Q (blocks_injective (absorbTail_injective φ h))

end Quantum.Xmss

end
