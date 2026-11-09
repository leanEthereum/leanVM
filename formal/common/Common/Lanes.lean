module

public import Mathlib.Data.List.GetD
public import Common.Keccak
public import Common.HashOracle
public import Common.Lemmas

@[expose] public section

/-!
# Lanes and bytes

The statement holds a Keccak state as `25` lanes of `64` bits (`LeanVM.Semantics.KeccakState`) and
Keccak-256 as `keccak256With` over a permutation of the lanes; the proofs of `common` hold a state
as bytes (`Common.KState`: 32 digest bytes, 104 more bytes of the rate, 64 bytes of capacity) and
Keccak-256 as the sponge over a permutation of the bytes (`Common.keccak256With`). Byte `8i + k`
is byte `k` of lane `i`, little-endian (`KState.toRpm`, `Digest.ofRpm`).

* `stateEquiv`, `digestEquiv`: the two bijections.
* `keccak256With_rpm`: Keccak-256 over a permutation `π` of the lane states is `common`'s sponge
  over `π` read on bytes, in every monad; the deployed Keccak-256 is `common`'s sponge over the
  deployed Keccak-f[1600] read on bytes (`keccak256_eq_rpm`).
* `lazyPerm_relabel`: the lazily sampled permutation of the lane states is the one of the byte
  states read through `stateEquiv` (a fresh answer is uniform among the unused points on either
  side, `uniformAvoiding_map`).
* `Common.relabel`, `Common.runK_relabel`, `Common.isWeightBound_relabel`: a game of the model
  with the hash oracle (`KSpecH`, on lanes) is the game with its permutation queries read on
  bytes (`KSpecB`), with the same distribution against the lazily sampled permutation and the
  same permutation calls.
* `keccakNF_of_keep`: a state keeping lanes `16..24` of another keeps its capacity and its byte
  `135`, so the block that leads from one to the other is non-final (`Common.keccakNF`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace LeanVM

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- The 200 bytes of a Keccak state, as `common` splits them (32 digest bytes, 104 more bytes
of the rate, 64 bytes of capacity): byte `8i + k` is byte `k` of lane `i`, little-endian
(`keccak_hash`'s `u64::from_le_bytes`, `crates/verifier/src/hash.rs:71-75`). -/
def KState.toRpm (s : KeccakState) : Common.KState :=
  Common.KState.ofBytes (s.toList.flatMap wordBytes)

/-- A digest of 32 bytes as four little-endian words (`Digest::words`, `hash.rs:105-107`). -/
def Digest.ofRpm (d : Common.DigestBytes) : Digest :=
  #v[littleEndianLane d.toList 0, littleEndianLane d.toList 1, littleEndianLane d.toList 2,
      littleEndianLane d.toList 3]

/-- A query on the bytes of the states. -/
def permQueryToRpm : Common.PermutationQuery KeccakState → Common.PermutationQuery Common.KState
  | .forward x => .forward (KState.toRpm x)
  | .inverse y => .inverse (KState.toRpm y)

end LeanVM

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## A lane and its bytes -/

theorem or_mul_two_pow {a n : ℕ} (b : ℕ) (ha : a < 2 ^ n) : a ||| b * 2 ^ n = a + b * 2 ^ n := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ha]; ring

theorem bytes8_or {x0 x1 x2 x3 x4 x5 x6 x7 : ℕ} (h0 : x0 < 256) (h1 : x1 < 256) (h2 : x2 < 256)
    (h3 : x3 < 256) (h4 : x4 < 256) (h5 : x5 < 256) (h6 : x6 < 256) (h7 : x7 < 256) :
    (x0 % 18446744073709551616 ||| x1 * 256 % 18446744073709551616 |||
      x2 * 65536 % 18446744073709551616 ||| x3 * 16777216 % 18446744073709551616 |||
      x4 * 4294967296 % 18446744073709551616 ||| x5 * 1099511627776 % 18446744073709551616 |||
      x6 * 281474976710656 % 18446744073709551616 |||
      x7 * 72057594037927936 % 18446744073709551616) =
    (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * (x4 + 256 * (x5 + 256 * (x6 + 256 * x7))))))) %
      18446744073709551616 := by
  rw [Nat.mod_eq_of_lt (by omega : x0 < _), Nat.mod_eq_of_lt (by omega : x1 * 256 < _),
    Nat.mod_eq_of_lt (by omega : x2 * 65536 < _), Nat.mod_eq_of_lt (by omega : x3 * 16777216 < _),
    Nat.mod_eq_of_lt (by omega : x4 * 4294967296 < _),
    Nat.mod_eq_of_lt (by omega : x5 * 1099511627776 < _),
    Nat.mod_eq_of_lt (by omega : x6 * 281474976710656 < _),
    Nat.mod_eq_of_lt (by omega : x7 * 72057594037927936 < _), Nat.mod_eq_of_lt (by omega)]
  rw [show (256 : ℕ) = 2 ^ 8 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (65536 : ℕ) = 2 ^ 16 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (16777216 : ℕ) = 2 ^ 24 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (4294967296 : ℕ) = 2 ^ 32 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (281474976710656 : ℕ) = 2 ^ 48 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (72057594037927936 : ℕ) = 2 ^ 56 by rfl, or_mul_two_pow _ (by omega)]
  ring

/-- The 64-bit word of eight little-endian bytes. -/
def bytesLane (b : List UInt8) : UInt64 :=
  UInt64.ofNat ((List.range 8).foldr (fun i acc ↦ (b.getD i 0).toNat + 256 * acc) 0)

theorem wordBytes_len (w : UInt64) : (wordBytes w).length = 8 := rfl

/-- A lane is read back from the head of its eight bytes. -/
theorem bytesLane_wordBytes_append (w : UInt64) (rest : List UInt8) :
    bytesLane (wordBytes w ++ rest) = w := by
  apply UInt64.toNat_inj.mp
  have hw := w.toNat_lt
  simp only [bytesLane, wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.foldr_cons,
    List.foldr_nil, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  norm_num
  omega

/-- `littleEndianLane` reads the eight bytes from `8i` as `bytesLane` does. -/
theorem leLane_eq_bytesLane (bs : List UInt8) (i : ℕ) :
    littleEndianLane bs i = bytesLane (bs.drop (8 * i)) := by
  apply UInt64.toNat_inj.mp
  have hb : ∀ k, (bs[8 * i + k]?.getD 0).toNat < 256 := fun k ↦ UInt8.toNat_lt _
  have e : ∀ k, (bs.drop (8 * i)).getD k 0 = bs.getD (8 * i + k) 0 := fun k ↦ by
    simp [List.getD_eq_getElem?_getD]
  simp only [littleEndianLane, bytesLane, e, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldr_append, List.foldl_cons, List.foldl_nil, List.foldr_cons,
    List.foldr_nil, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    List.getD_eq_getElem?_getD, UInt64.zero_or]
  have h0 := hb 0
  simp only [Nat.add_zero] at h0
  have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4; have h5 := hb 5
  have h6 := hb 6; have h7 := hb 7
  generalize (bs[8 * i]?.getD 0).toNat = x0 at *
  generalize (bs[8 * i + 1]?.getD 0).toNat = x1 at *
  generalize (bs[8 * i + 2]?.getD 0).toNat = x2 at *
  generalize (bs[8 * i + 3]?.getD 0).toNat = x3 at *
  generalize (bs[8 * i + 4]?.getD 0).toNat = x4 at *
  generalize (bs[8 * i + 5]?.getD 0).toNat = x5 at *
  generalize (bs[8 * i + 6]?.getD 0).toNat = x6 at *
  generalize (bs[8 * i + 7]?.getD 0).toNat = x7 at *
  simp only [Nat.shiftLeft_eq, Nat.mul_zero, Nat.add_zero]
  norm_num
  exact bytes8_or h0 h1 h2 h3 h4 h5 h6 h7

/-- The bytes of `bytesLane b` are the first eight of `b`, missing ones `0`. -/
theorem wordBytes_bytesLane (b : List UInt8) :
    wordBytes (bytesLane b) = (List.range 8).map fun k ↦ b.getD k 0 := by
  have hb : ∀ k, (b.getD k 0).toNat < 256 := fun k ↦ UInt8.toNat_lt _
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4
  have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  simp only [wordBytes, bytesLane, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] <;>
    generalize (b.getD 0 0).toNat = x0 at * <;>
    generalize (b.getD 1 0).toNat = x1 at * <;>
    generalize (b.getD 2 0).toNat = x2 at * <;>
    generalize (b.getD 3 0).toNat = x3 at * <;>
    generalize (b.getD 4 0).toNat = x4 at * <;>
    generalize (b.getD 5 0).toNat = x5 at * <;>
    generalize (b.getD 6 0).toNat = x6 at * <;>
    generalize (b.getD 7 0).toNat = x7 at * <;>
    norm_num <;> omega

/-- The bytes of `littleEndianLane bs i` are bytes `8i` to `8i + 7` of `bs`, missing ones `0`. -/
theorem wordBytes_leLane (bs : List UInt8) (i : ℕ) :
    wordBytes (littleEndianLane bs i) = (List.range 8).map fun k ↦ bs.getD (8 * i + k) 0 := by
  rw [leLane_eq_bytesLane, wordBytes_bytesLane]
  refine List.map_congr_left fun k _ ↦ ?_
  simp [List.getD_eq_getElem?_getD]

/-! ## Lists of lanes and their bytes -/

/-- The bytes of a list of lanes, each little-endian. -/
def lanesBytes (l : List UInt64) : List UInt8 := l.flatMap wordBytes

@[simp] theorem lanesBytes_nil : lanesBytes [] = [] := rfl

@[simp] theorem lanesBytes_cons (a : UInt64) (l : List UInt64) :
    lanesBytes (a :: l) = wordBytes a ++ lanesBytes l := rfl

@[simp] theorem length_lanesBytes (l : List UInt64) : (lanesBytes l).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, wordBytes_len]; ring

theorem drop_lanesBytes (l : List UInt64) (i : ℕ) :
    (lanesBytes l).drop (8 * i) = lanesBytes (l.drop i) := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [lanesBytes_cons, show 8 * (i + 1) = 8 + 8 * i by ring, ← List.drop_drop,
        List.drop_left' (wordBytes_len a), ih, List.drop_succ_cons]

theorem leLane_lanesBytes (l : List UInt64) (i : ℕ) (hi : i < l.length) :
    littleEndianLane (lanesBytes l) i = l[i] := by
  rw [leLane_eq_bytesLane, drop_lanesBytes, List.drop_eq_getElem_cons hi, lanesBytes_cons,
    bytesLane_wordBytes_append]

theorem getD_lanesBytes (l : List UInt64) (j : ℕ) (hj : j < 8 * l.length) :
    (lanesBytes l).getD j 0 = (wordBytes (l[j / 8]'(by omega))).getD (j % 8) 0 := by
  have hj' : j / 8 < l.length := by omega
  conv_lhs => rw [show j = 8 * (j / 8) + j % 8 by omega]
  rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, drop_lanesBytes,
    List.drop_eq_getElem_cons hj', lanesBytes_cons,
    List.getElem?_append_left (by rw [wordBytes_len]; omega), ← List.getD_eq_getElem?_getD]

theorem lanesBytes_ofFn_leLane (bs : List UInt8) (n : ℕ) (h : bs.length = 8 * n) :
    lanesBytes (List.ofFn fun i : Fin n ↦ littleEndianLane bs i) = bs := by
  refine List.ext_getElem (by simp [h]) fun j h1 h2 ↦ ?_
  have hj : j < 8 * (List.ofFn fun i : Fin n ↦ littleEndianLane bs i).length :=
      by simp [h] at h2 ⊢; omega
  have e := getD_lanesBytes _ j hj
  rw [List.getD_eq_getElem _ _ h1] at e
  rw [e, List.getElem_ofFn, wordBytes_leLane, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by omega)]
  congr 1
  omega

/-! ## The state -/

@[simp] theorem length_toBytes (x : Common.KState) : x.toBytes.length = 200 := by
  simp [Common.KState.toBytes]

/-- Lengths of byte lists, for `omega`. -/
macro "len_omega" : tactic =>
  `(tactic| (simp only [List.length_append, List.length_ofFn, Vector.length_toList,
    Common.KState.toBytes] at *; omega))

theorem ofBytes_toBytes (x : Common.KState) : Common.KState.ofBytes x.toBytes = x := by
  obtain ⟨⟨a, b⟩, c⟩ := x
  simp only [Common.KState.ofBytes, Common.KState.toBytes, Prod.mk.injEq]
  refine ⟨⟨Vector.ext fun i hi ↦ ?_, Vector.ext fun i hi ↦ ?_⟩, Vector.ext fun i hi ↦ ?_⟩ <;>
    simp only [Vector.getElem_ofFn] <;>
    rw [List.getD_eq_getElem _ _ (by len_omega)]
  · rw [List.getElem_append_left (by len_omega), List.getElem_append_left (by len_omega),
      Vector.getElem_toList]
  · rw [List.getElem_append_left (by len_omega), List.getElem_append_right (by len_omega),
      Vector.getElem_toList]
    simp only [Vector.length_toList, Nat.add_sub_cancel_left]
  · rw [List.getElem_append_right (by len_omega), Vector.getElem_toList]
    simp only [List.length_append, Vector.length_toList, Nat.add_sub_cancel_left]

theorem toBytes_ofBytes (bs : List UInt8) (h : bs.length = 200) :
    (Common.KState.ofBytes bs).toBytes = bs := by
  refine List.ext_getElem (by len_omega) fun j h1 h2 ↦ ?_
  simp only [Common.KState.ofBytes, Common.KState.toBytes, Vector.toList_ofFn]
  by_cases j1 : j < 32
  · rw [List.getElem_append_left (by len_omega), List.getElem_append_left (by len_omega),
      List.getElem_ofFn, List.getD_eq_getElem _ _ (by omega)]
  · by_cases j2 : j < 136
    · rw [List.getElem_append_left (by len_omega), List.getElem_append_right (by len_omega),
        List.getElem_ofFn, List.getD_eq_getElem _ _ (by len_omega)]
      simp only [List.length_ofFn]
      congr 1; omega
    · rw [List.getElem_append_right (by len_omega), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by len_omega)]
      simp only [List.length_append, List.length_ofFn]
      have e : 136 + (j - (32 + 104)) = j := by omega
      simp only [e]

/-- The lane state of 200 bytes: lane `i` is bytes `8i` to `8i + 7`, little-endian. -/
def KState.ofRpm (x : Common.KState) : KeccakState := Vector.ofFn fun i : Fin 25 ↦ littleEndianLane x.toBytes i

theorem toBytes_toRpm (s : KeccakState) : (KState.toRpm s).toBytes = lanesBytes s.toList :=
  toBytes_ofBytes (lanesBytes s.toList) (by simp)

theorem ofRpm_toRpm (s : KeccakState) : KState.ofRpm (KState.toRpm s) = s := by
  refine Vector.ext fun i hi ↦ ?_
  rw [KState.ofRpm, Vector.getElem_ofFn, toBytes_toRpm, leLane_lanesBytes _ _ (by simpa)]
  simp

theorem toRpm_ofRpm (x : Common.KState) : KState.toRpm (KState.ofRpm x) = x := by
  show Common.KState.ofBytes (lanesBytes (KState.ofRpm x).toList) = x
  rw [KState.ofRpm, Vector.toList_ofFn, lanesBytes_ofFn_leLane _ 25 (by simp), ofBytes_toBytes]

/-- **The Keccak state as lanes and as bytes.** -/
def stateEquiv : KeccakState ≃ Common.KState where
  toFun := KState.toRpm
  invFun := KState.ofRpm
  left_inv := ofRpm_toRpm
  right_inv := toRpm_ofRpm

@[simp] theorem stateEquiv_apply (s : KeccakState) : stateEquiv s = KState.toRpm s := rfl

@[simp] theorem stateEquiv_symm_apply (x : Common.KState) :
    stateEquiv.symm x = KState.ofRpm x := rfl

/-- Byte `j` of a state is byte `j % 8` of lane `j / 8`. -/
theorem toBytes_toRpm_getElem (s : KeccakState) (j : ℕ) (hj : j < 200) :
    (KState.toRpm s).toBytes[j]'(by simp; omega) =
      (wordBytes (s[j / 8]'(by omega))).getD (j % 8) 0 := by
  have h := getD_lanesBytes s.toList j (by simp; omega)
  rw [← toBytes_toRpm, List.getD_eq_getElem _ _ (by simp; omega)] at h
  rw [h]
  simp

/-- The zero state. -/
theorem lanesBytes_replicate_zero (n : ℕ) :
    lanesBytes (List.replicate n 0) = List.replicate (8 * n) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, lanesBytes_cons, ih, show 8 * (n + 1) = 8 + 8 * n by ring,
      ← List.replicate_append_replicate]
    rfl

theorem toRpm_zero : KState.toRpm (Vector.replicate 25 0) = Common.KState.zero := by
  rw [← ofBytes_toBytes Common.KState.zero]
  show Common.KState.ofBytes (lanesBytes (Vector.replicate 25 0).toList) = _
  rw [Vector.toList_replicate, lanesBytes_replicate_zero]
  simp only [Common.KState.zero, Common.KState.toBytes, Vector.toList_replicate,
    List.replicate_append_replicate]

/-! ## The digest -/

/-- The 32 bytes of a digest. -/
def Digest.toRpm (d : Digest) : Common.DigestBytes :=
  Vector.ofFn fun i : Fin 32 ↦ (lanesBytes d.toList).getD i 0

theorem toList_digestToRpm (d : Digest) : (Digest.toRpm d).toList = lanesBytes d.toList := by
  refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
  simp only [Digest.toRpm, Vector.toList_ofFn, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ h2]

theorem digestOfRpm_toRpm (d : Digest) : Digest.ofRpm (Digest.toRpm d) = d := by
  have e : ∀ k (hk : k < 4), littleEndianLane (Digest.toRpm d).toList k = d[k] := fun k hk ↦ by
    rw [toList_digestToRpm, leLane_lanesBytes _ _ (by simpa)]
    simp
  refine Vector.ext fun i hi ↦ ?_
  interval_cases i
  · exact e 0 (by norm_num)
  · exact e 1 (by norm_num)
  · exact e 2 (by norm_num)
  · exact e 3 (by norm_num)

theorem digestToRpm_ofRpm (d : Common.DigestBytes) : Digest.toRpm (Digest.ofRpm d) = d := by
  apply Vector.toList_inj.mp
  rw [toList_digestToRpm]
  have e : (Digest.ofRpm d).toList = List.ofFn fun i : Fin 4 ↦ littleEndianLane d.toList i := by
    simp [Digest.ofRpm, List.ofFn_succ]
  rw [e, lanesBytes_ofFn_leLane _ 4 (by simp)]

/-- **The digest as lanes and as bytes.** -/
def digestEquiv : Digest ≃ Common.DigestBytes where
  toFun := Digest.toRpm
  invFun := Digest.ofRpm
  left_inv := digestOfRpm_toRpm
  right_inv := digestToRpm_ofRpm

@[simp] theorem digestEquiv_apply (d : Digest) : digestEquiv d = Digest.toRpm d := rfl

@[simp] theorem digestEquiv_symm_apply (d : Common.DigestBytes) :
    digestEquiv.symm d = Digest.ofRpm d := rfl

/-! ## Absorbing a block -/

theorem wordBytes_getD (w : UInt64) (k : ℕ) (hk : k < 8) :
    (wordBytes w).getD k 0 = (w >>> (8 * k).toUInt64).toUInt8 := by
  rw [wordBytes, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem wordBytes_xor_getD (a b : UInt64) (k : ℕ) (hk : k < 8) :
    (wordBytes (a ^^^ b)).getD k 0 = (wordBytes a).getD k 0 ^^^ (wordBytes b).getD k 0 := by
  rw [wordBytes_getD _ _ hk, wordBytes_getD _ _ hk, wordBytes_getD _ _ hk, UInt64.shiftRight_xor,
    UInt64.toUInt8_xor]

theorem wordBytes_leLane_getD (bs : List UInt8) (i k : ℕ) (hk : k < 8) :
    (wordBytes (littleEndianLane bs i)).getD k 0 = bs.getD (8 * i + k) 0 := by
  rw [wordBytes_leLane, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem lane_eq_getElem (s : KeccakState) (i : ℕ) (hi : i < 25) : Keccak.lane s i = s[i] := by
  simp [Keccak.lane, Array.getD_eq_getD_getElem?, hi]

/-- Byte `j` of a state, through `toRpm`. -/
theorem lanesBytes_getD (s : KeccakState) (j : ℕ) (hj : j < 200) :
    (lanesBytes s.toList).getD j 0 = (wordBytes (s[j / 8]'(by omega))).getD (j % 8) 0 := by
  rw [getD_lanesBytes _ _ (by simp; omega)]
  simp

theorem toRpm_fst_fst (s : KeccakState) (j : ℕ) (hj : j < 32) :
    (KState.toRpm s).1.1[j] = (wordBytes (s[j / 8]'(by omega))).getD (j % 8) 0 := by
  rw [← lanesBytes_getD s j (by omega)]
  simp [KState.toRpm, Common.KState.ofBytes, lanesBytes]

theorem toRpm_fst_snd (s : KeccakState) (j : ℕ) (hj : j < 104) :
    (KState.toRpm s).1.2[j] =
      (wordBytes (s[(32 + j) / 8]'(by omega))).getD ((32 + j) % 8) 0 := by
  rw [← lanesBytes_getD s (32 + j) (by omega)]
  simp [KState.toRpm, Common.KState.ofBytes, lanesBytes]

theorem toRpm_snd (s : KeccakState) (j : ℕ) (hj : j < 64) :
    (KState.toRpm s).2[j] =
      (wordBytes (s[(136 + j) / 8]'(by omega))).getD ((136 + j) % 8) 0 := by
  rw [← lanesBytes_getD s (136 + j) (by omega)]
  simp [KState.toRpm, Common.KState.ofBytes, lanesBytes]

/-- **XORing a block's lanes into the rate is XORing its bytes** (`absorbBlock`, `absorb`). -/
theorem toRpm_absorbInput (s : KeccakState) (block : List UInt8) :
    KState.toRpm (Vector.ofFn fun i : Fin 25 ↦
        if i.val < 17 then Keccak.lane s i ^^^ littleEndianLane block i else Keccak.lane s i) =
      Common.absorb (KState.toRpm s) (Common.KBlock.ofBytes block) := by
  set v : KeccakState := Vector.ofFn fun i : Fin 25 ↦
    if i.val < 17 then Keccak.lane s i ^^^ littleEndianLane block i else Keccak.lane s i with hv
  have hin : ∀ i (hi : i < 17), v[i]'(by omega) = s[i]'(by omega) ^^^ littleEndianLane block i := by
    intro i hi
    rw [hv, Vector.getElem_ofFn]
    simp only [hi, ↓reduceIte, lane_eq_getElem s i (by omega)]
  have hout : ∀ i (hi : 17 ≤ i) (hi' : i < 25), v[i] = s[i] := by
    intro i hi hi'
    rw [hv, Vector.getElem_ofFn]
    simp only [show ¬ i < 17 by omega, ↓reduceIte, lane_eq_getElem s i hi']
  have hblk : ∀ j (hj : j < 136), (wordBytes (v[j / 8]'(by omega))).getD (j % 8) 0 =
      (wordBytes (s[j / 8]'(by omega))).getD (j % 8) 0 ^^^ block.getD j 0 := by
    intro j hj
    rw [hin (j / 8) (by omega), wordBytes_xor_getD _ _ _ (by omega),
      wordBytes_leLane_getD _ _ _ (by omega)]
    congr 2
    omega
  refine Prod.ext (Prod.ext (Vector.ext fun j hj ↦ ?_) (Vector.ext fun j hj ↦ ?_))
    (Vector.ext fun j hj ↦ ?_)
  · change _ = (Vector.zipWith (· ^^^ ·) (KState.toRpm s).1.1 _)[j]
    rw [Vector.getElem_zipWith, toRpm_fst_fst _ _ hj, toRpm_fst_fst _ _ hj, hblk j (by omega),
      Common.KBlock.ofBytes, Vector.getElem_ofFn]
  · change _ = (Vector.zipWith (· ^^^ ·) (KState.toRpm s).1.2 _)[j]
    rw [Vector.getElem_zipWith, toRpm_fst_snd _ _ hj, toRpm_fst_snd _ _ hj,
      hblk (32 + j) (by omega), Common.KBlock.ofBytes, Vector.getElem_ofFn]
  · change (KState.toRpm v).2[j] = (KState.toRpm s).2[j]
    rw [toRpm_snd _ _ hj, toRpm_snd _ _ hj, hout _ (by omega) (by omega)]

/-! ## The padding -/

theorem length_padBlock (data : List UInt8) (h : data.length < 136) :
    (padBlock data).length = 136 := by
  simp only [padBlock, List.length_modify, List.length_append, List.length_replicate, rate]
  omega

/-- The last block: the padding of fewer than `136` bytes is `padBlock`. -/
theorem keccakPadBytes_eq_padBlock (data : List UInt8) (h : data.length < 136) :
    Common.keccakPadBytes data = padBlock data := by
  have hm : data.length % 136 = data.length := Nat.mod_eq_of_lt h
  unfold Common.keccakPadBytes
  simp only [hm]
  apply List.ext_getElem?
  intro j
  simp only [padBlock, rate, padFirst, padLast, List.getElem?_modify]
  by_cases hj : j < data.length
  · split_ifs <;> simp_all [List.getElem?_append_left hj]
    omega
  · split_ifs <;> simp_all [List.getElem?_append_right (Nat.le_of_not_lt hj),
      List.getElem?_replicate]
    · decide
    · rw [show j - 135 = (j - 136) + 1 by omega]; rfl
    · rw [show j - data.length = (134 - data.length) + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_append_right (by simp), List.length_replicate, Nat.sub_self]
      have e : 134 - data.length + 1 < 136 - data.length := by omega
      simp only [List.getElem?_cons_zero, e, ↓reduceIte]
    · rw [show j - data.length = (j - data.length - 1) + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_append]
      simp only [List.length_replicate, List.getElem?_replicate]
      split_ifs <;> simp_all <;> omega

/-- Long data: the padding of at least `136` bytes is the first block, then the padding of the
rest. -/
theorem keccakPadBytes_of_le (data : List UInt8) (h : 136 ≤ data.length) :
    Common.keccakPadBytes data = data.take 136 ++ Common.keccakPadBytes (data.drop 136) := by
  have hm : (data.drop 136).length % 136 = data.length % 136 := by
    rw [List.length_drop]; omega
  unfold Common.keccakPadBytes
  rw [hm]
  split_ifs <;> simp only [List.append_assoc, ← List.append_assoc (data.take 136),
    List.take_append_drop]

theorem toBlocks_of_le (l : List UInt8) (h : 136 ≤ l.length) :
    Common.toBlocks l = Common.KBlock.ofBytes (l.take 136) :: Common.toBlocks (l.drop 136) := by
  match l, h with
  | b :: bs, _ => rw [Common.toBlocks]

/-! ## Keccak-256 over a permutation -/

section Sponge

variable {m : Type → Type} [Monad m] [LawfulMonad m] (π : Common.KState → m Common.KState)

/-- A permutation of the byte states, read on lane states. -/
def lanePerm : KeccakState → m KeccakState := fun s ↦ KState.ofRpm <$> π (KState.toRpm s)

omit [LawfulMonad m] in
theorem absorbBlockWith_lanePerm (s : KeccakState) (block : List UInt8) :
    absorbBlockWith (lanePerm π) s block =
      KState.ofRpm <$> π (Common.absorb (KState.toRpm s) (Common.KBlock.ofBytes block)) := by
  rw [absorbBlockWith, lanePerm, toRpm_absorbInput]

theorem absorbWith_lanePerm : ∀ (n : ℕ) (s : KeccakState) (data : List UInt8), data.length / 136 = n →
    absorbWith (lanePerm π) n s data =
      KState.ofRpm <$> Common.absorbAll π (KState.toRpm s)
        (Common.toBlocks (Common.keccakPadBytes data))
  | 0, s, data, h => by
    have hl : data.length < 136 := by omega
    rw [keccakPadBytes_eq_padBlock data hl, toBlocks_of_le _ (by rw [length_padBlock _ hl]),
      List.take_of_length_le (by rw [length_padBlock _ hl]),
      List.drop_of_length_le (by rw [length_padBlock _ hl])]
    simp only [absorbWith, absorbBlockWith_lanePerm, Common.absorbAll_cons, Common.toBlocks,
      Common.absorbAll_nil, bind_pure]
  | n + 1, s, data, h => by
    have hl : 136 ≤ data.length := by omega
    have hd : (data.drop 136).length / 136 = n := by rw [List.length_drop]; omega
    have h136 : (data.take 136).length = 136 := by rw [List.length_take]; omega
    rw [keccakPadBytes_of_le data hl,
      toBlocks_of_le _ (by rw [List.length_append, h136]; omega),
      List.take_append_of_le_length (by rw [h136]), List.take_take, Nat.min_self,
      List.drop_append_of_le_length (by rw [h136]),
      List.drop_of_length_le (by rw [h136]), List.nil_append]
    simp only [absorbWith, absorbBlockWith_lanePerm, Common.absorbAll_cons, bind_map_left,
      map_bind, rate]
    refine bind_congr fun y ↦ ?_
    rw [absorbWith_lanePerm n _ _ hd, toRpm_ofRpm]

theorem leLane_append_left (l r : List UInt8) (i : ℕ) (h : 8 * i + 8 ≤ l.length) :
    littleEndianLane (l ++ r) i = littleEndianLane l i := by
  unfold littleEndianLane
  refine List.foldl_ext _ _ _ fun a k hk ↦ ?_
  simp only [List.mem_range] at hk
  rw [List.getD_append _ _ _ _ (by omega)]

/-- **Keccak-256 over a permutation is `common`'s Keccak-256 sponge over it**, in every
monad: the sponge of rate 136 bytes and capacity 512 bits, with the Keccak padding, from the zero
state, its first 32 bytes read as four little-endian lanes. -/
theorem keccak256With_rpm (data : List UInt8) :
    keccak256With (lanePerm π) data = Digest.ofRpm <$> Common.keccak256With π data := by
  rw [keccak256With, absorbWith_lanePerm π (data.length / rate) _ data rfl, toRpm_zero, Common.keccak256With,
    Common.spongeWith, bind_map_left, Functor.map_map, map_eq_bind_pure_comp]
  refine bind_congr fun y ↦ ?_
  have e : ∀ i (hi : i < 4), Keccak.lane (KState.ofRpm y) i = littleEndianLane y.1.1.toList i := by
    intro i hi
    rw [lane_eq_getElem _ _ (by omega), KState.ofRpm, Vector.getElem_ofFn]
    show littleEndianLane (y.1.1.toList ++ y.1.2.toList ++ y.2.toList) i = _
    rw [List.append_assoc, leLane_append_left _ _ _ (by simp only [Vector.length_toList]; omega)]
  have hv : (#v[Keccak.lane (KState.ofRpm y) 0, Keccak.lane (KState.ofRpm y) 1,
      Keccak.lane (KState.ofRpm y) 2, Keccak.lane (KState.ofRpm y) 3] : Digest) =
        Digest.ofRpm y.1.1 := by
    simp only [Digest.ofRpm, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
      e 3 (by norm_num)]
  rw [hv]
  rfl

end Sponge

/-- Keccak-256 over `keccakF` is the deployed Keccak-256. -/
theorem keccak256With_keccakF (data : List UInt8) :
    keccak256With (m := Id) keccakF1600 data = keccak256 data := rfl

/-- **The deployed Keccak-256 is `common`'s Keccak-256 sponge** (`Common.keccak256With`) over
the deployed Keccak-f[1600] read on bytes. -/
theorem keccak256_eq_rpm (data : List UInt8) :
    keccak256 data = Digest.ofRpm
      (Common.keccak256With (m := Id) (fun x ↦ KState.toRpm (keccakF1600 (KState.ofRpm x))) data) := by
  have h : lanePerm (m := Id) (fun x ↦ KState.toRpm (keccakF1600 (KState.ofRpm x))) =
      (keccakF1600 : KeccakState → Id KeccakState) := by
    funext s
    show KState.ofRpm (KState.toRpm (keccakF1600 (KState.ofRpm (KState.toRpm s)))) = keccakF1600 s
    rw [ofRpm_toRpm, ofRpm_toRpm]
  have e := keccak256With_rpm (m := Id) (fun x ↦ KState.toRpm (keccakF1600 (KState.ofRpm x))) data
  rw [h, keccak256With_keccakF] at e
  exact e.trans (Id.run_map _ _)

/-! ## Keeping the capacity -/

/-- A state keeping lanes `16..24` of another keeps its capacity (lanes `17..24`, bytes
`136..199`) and its byte `135` (the top byte of lane `16`). -/
theorem toRpm_keep (x y : KeccakState) (h : ∀ i : Fin 25, 16 ≤ i.val → x[i] = y[i]) :
    (KState.toRpm x).2 = (KState.toRpm y).2 ∧
      (KState.toRpm x).1.2[103] = (KState.toRpm y).1.2[103] := by
  have h' : ∀ i (hi : 16 ≤ i) (hi' : i < 25), x[i] = y[i] := fun i hi hi' ↦ by
    simpa only [Fin.getElem_fin] using h ⟨i, hi'⟩ hi
  refine ⟨Vector.ext fun j hj ↦ ?_, ?_⟩
  · rw [toRpm_snd _ _ hj, toRpm_snd _ _ hj, h' _ (by omega) (by omega)]
  · rw [toRpm_fst_snd _ _ (by norm_num), toRpm_fst_snd _ _ (by norm_num),
      h' _ (by norm_num) (by norm_num)]

/-- **A duplexing that keeps lanes `16..24` absorbs a non-final block**: from `y` to `x`, the
capacity is kept and the block's last byte is zero (`Common.keccakNF_blockTo`). -/
theorem keccakNF_of_keep (x y : KeccakState) (h : ∀ i : Fin 25, 16 ≤ i.val → x[i] = y[i]) :
    (KState.toRpm x).2 = (KState.toRpm y).2 ∧
      Common.keccakNF (Common.blockTo (KState.toRpm y) (KState.toRpm x)) :=
  ⟨(toRpm_keep x y h).1, Common.keccakNF_blockTo _ _ (toRpm_keep x y h).2⟩

/-! ## A fresh answer through a bijection -/

section Avoiding

variable {S₁ S₂ : Type} [Fintype S₁] [DecidableEq S₁] [SampleableType S₁]
  [Fintype S₂] [DecidableEq S₂] [SampleableType S₂]

omit [Fintype S₁] [DecidableEq S₁] [SampleableType S₁] [Fintype S₂] [DecidableEq S₂]
  [SampleableType S₂] in
theorem mem_map_equiv (e : S₁ ≃ S₂) (l : List S₁) (y : S₂) : y ∈ l.map e ↔ e.symm y ∈ l := by
  constructor
  · rintro hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    simpa using ha
  · intro hm
    exact List.mem_map.mpr ⟨e.symm y, hm, by simp⟩

/-- **A uniform draw avoiding a list, through a bijection**, is a uniform draw avoiding the
list's image. -/
theorem uniformAvoiding_map (e : S₁ ≃ S₂) (l : List S₁) :
    e <$> Common.uniformAvoiding l =ᵈ Common.uniformAvoiding (l.map e) := by
  by_cases h : ∃ y, y ∉ l
  · have h' : ∃ y, y ∉ l.map e := by
      obtain ⟨y, hy⟩ := h
      exact ⟨e y, fun hm ↦ hy (by simpa using hm)⟩
    have hcard : (Finset.univ.filter fun y ↦ y ∉ l.map e).card =
        (Finset.univ.filter fun y ↦ y ∉ l).card := by
      refine Finset.card_bij (fun y _ ↦ e.symm y) (fun y hy ↦ ?_) (fun _ _ _ _ h ↦ by simpa using h)
        (fun y hy ↦ ⟨e y, ?_, by simp⟩)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact fun hm ↦ hy (by simpa using List.mem_map_of_mem (f := e) hm)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        simpa using hy
    refine evalDistEq_iff_forall_prEvent_eq_output.mpr fun y ↦ ?_
    rw [prEvent_map]
    have e1 := Common.prEvent_uniformAvoiding h (fun x ↦ e x = y)
    have e2 := Common.prEvent_uniformAvoiding h' (fun x ↦ x = y)
    rw [e1, e2, hcard]
    congr 2
    by_cases hy : y ∈ l.map e
    · have hy' : e.symm y ∈ l := (mem_map_equiv e l y).mp hy
      rw [Finset.card_eq_zero.mpr, Finset.card_eq_zero.mpr] <;>
        refine Finset.eq_empty_of_forall_notMem fun x hx ↦ ?_ <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      · exact hx.1 (hx.2 ▸ hy)
      · exact hx.1 (by rw [← e.symm_apply_apply x, hx.2]; exact hy')
    · have hy' : e.symm y ∉ l := fun hm ↦ hy ((mem_map_equiv e l y).mpr hm)
      rw [Finset.card_eq_one.mpr ⟨y, ?_⟩, Finset.card_eq_one.mpr ⟨e.symm y, ?_⟩]
      · ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨-, rfl⟩; simp
        · rintro rfl; exact ⟨hy', by simp⟩
      · ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨-, rfl⟩; rfl
        · rintro rfl; exact ⟨hy, rfl⟩
  · have h' : ¬ ∃ y, y ∉ l.map e := by
      rintro ⟨y, hy⟩
      exact h ⟨e.symm y, fun hm ↦ hy (by simpa using List.mem_map_of_mem (f := e) hm)⟩
    simp only [Common.uniformAvoiding, h, h', ↓reduceDIte]
    exact SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective

end Avoiding

/-! ## The lazily sampled permutation through a bijection -/

section Perm

variable {S₁ S₂ : Type} [Fintype S₁] [DecidableEq S₁] [SampleableType S₁]
  [Fintype S₂] [DecidableEq S₂] [SampleableType S₂]

/-- The edges of a log, read through `f`. -/
def logMap (f : S₂ → S₁) (E : Common.PermutationEdges S₂) : Common.PermutationEdges S₁ :=
  E.map fun p ↦ (f p.1, f p.2)

/-- A query read through `e`. -/
def mapQ (e : S₁ ≃ S₂) : Common.PermutationQuery S₁ → Common.PermutationQuery S₂
  | .forward x => .forward (e x)
  | .inverse y => .inverse (e y)

omit [Fintype S₁] [SampleableType S₁] [Fintype S₂] [SampleableType S₂] in
theorem fwdLookup_logMap (e : S₁ ≃ S₂) (E : Common.PermutationEdges S₂) (x : S₁) :
    Common.forwardLookup (logMap e.symm E) x = (Common.forwardLookup E (e x)).map e.symm := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = e x
    · subst h; simp [logMap, Common.forwardLookup]
    · have h' : ¬ e.symm a = x := fun h' ↦ h (by rw [← h']; simp)
      simp only [logMap, List.map_cons, Common.forwardLookup, h, h', ↓reduceIte] at ih ⊢
      exact ih

omit [Fintype S₁] [SampleableType S₁] [Fintype S₂] [SampleableType S₂] in
theorem invLookup_logMap (e : S₁ ≃ S₂) (E : Common.PermutationEdges S₂) (y : S₁) :
    Common.inverseLookup (logMap e.symm E) y = (Common.inverseLookup E (e y)).map e.symm := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : b = e y
    · subst h; simp [logMap, Common.inverseLookup]
    · have h' : ¬ e.symm b = y := fun h' ↦ h (by rw [← h']; simp)
      simp only [logMap, List.map_cons, Common.inverseLookup, h, h', ↓reduceIte] at ih ⊢
      exact ih

/-- **The lazily sampled permutation through a bijection**: a query read through `e` against the
permutation on `S₂`, its answer and edges read back, is the query against the permutation on
`S₁` with the edges read back. -/
theorem lazyPerm_relabel (e : S₁ ≃ S₂) (q : Common.PermutationQuery S₁) (E : Common.PermutationEdges S₂) :
    Prod.map e.symm (logMap e.symm) <$> (Common.lazyRandomPermutation (mapQ e q)).run E =ᵈ
      (Common.lazyRandomPermutation q).run (logMap e.symm E) := by
  cases q with
  | forward x =>
    simp only [mapQ, Common.lazyRandomPermutation, StateT.run_mk, fwdLookup_logMap]
    rcases h : Common.forwardLookup E (e x) with _ | y
    · simp only [Option.map_none, Functor.map_map]
      have hl : (logMap e.symm E).map Prod.snd = (E.map Prod.snd).map e.symm := by
        simp [logMap, Function.comp_def]
      rw [hl]
      refine EvalDistEq.trans ?_ ((uniformAvoiding_map e.symm _).map
        fun y ↦ (y, (x, y) :: logMap e.symm E))
      rw [Functor.map_map]
      simp [logMap]
    · simp
  | inverse y =>
    simp only [mapQ, Common.lazyRandomPermutation, StateT.run_mk, invLookup_logMap]
    rcases h : Common.inverseLookup E (e y) with _ | x
    · simp only [Option.map_none, Functor.map_map]
      have hl : (logMap e.symm E).map Prod.fst = (E.map Prod.fst).map e.symm := by
        simp [logMap, Function.comp_def]
      rw [hl]
      refine EvalDistEq.trans ?_ ((uniformAvoiding_map e.symm _).map
        fun x ↦ (x, (x, y) :: logMap e.symm E))
      rw [Functor.map_map]
      simp [logMap]
    · simp

end Perm

/-! ## Stateful computations related through a projection of the state -/

section StRel

variable {σ₁ σ₂ α β : Type}

/-- Two stateful computations related through a projection of their states: run from any state
and its projection, they agree in distribution, the first's final state projected. -/
def StRel (proj : σ₁ → σ₂) (m₁ : StateT σ₁ ProbComp α) (m₂ : StateT σ₂ ProbComp α) : Prop :=
  ∀ s, Prod.map id proj <$> m₁.run s =ᵈ m₂.run (proj s)

theorem StRel.pure (proj : σ₁ → σ₂) (a : α) :
    StRel proj (pure a : StateT σ₁ ProbComp α) (pure a) := fun s ↦ by
  simp only [StateT.run_pure, map_pure, Prod.map_apply, id_eq]
  exact EvalDistEq.rfl

theorem StRel.bind {proj : σ₁ → σ₂} {m₁ : StateT σ₁ ProbComp α} {m₂ : StateT σ₂ ProbComp α}
    {k₁ : α → StateT σ₁ ProbComp β} {k₂ : α → StateT σ₂ ProbComp β} (h : StRel proj m₁ m₂)
    (hk : ∀ a, StRel proj (k₁ a) (k₂ a)) : StRel proj (m₁ >>= k₁) (m₂ >>= k₂) := fun s ↦ by
  simp only [StateT.run_bind, map_bind]
  calc (m₁.run s >>= fun z ↦ Prod.map id proj <$> (k₁ z.1).run z.2)
      =ᵈ (m₁.run s >>= fun z ↦ (k₂ z.1).run (proj z.2)) :=
        EvalDistEq.bind_right _ fun z ↦ hk z.1 z.2
    _ = ((Prod.map id proj <$> m₁.run s) >>= fun z ↦ (k₂ z.1).run z.2) := by
        rw [bind_map_left]; rfl
    _ =ᵈ (m₂.run (proj s) >>= fun z ↦ (k₂ z.1).run z.2) := EvalDistEq.bind_left (h s) _

theorem StRel.map {proj : σ₁ → σ₂} {m₁ : StateT σ₁ ProbComp α} {m₂ : StateT σ₂ ProbComp α}
    (h : StRel proj m₁ m₂) (f : α → β) : StRel proj (f <$> m₁) (f <$> m₂) := fun s ↦ by
  simp only [StateT.run_map, Functor.map_map]
  have := (h s).map (Prod.map f id)
  simp only [Functor.map_map] at this
  exact this

theorem absorbAll_rel {proj : σ₁ → σ₂} (π₁ : Common.KState → StateT σ₁ ProbComp Common.KState)
    (π₂ : Common.KState → StateT σ₂ ProbComp Common.KState) (h : ∀ x, StRel proj (π₁ x) (π₂ x)) :
    ∀ (st : Common.KState) (bs : List Common.KBlock),
      StRel proj (Common.absorbAll π₁ st bs) (Common.absorbAll π₂ st bs)
  | st, [] => StRel.pure proj st
  | st, B :: bs => by
    rw [Common.absorbAll_cons, Common.absorbAll_cons]
    exact StRel.bind (h _) fun y ↦ absorbAll_rel π₁ π₂ h y bs

end StRel

theorem ofRpm_zero : KState.ofRpm Common.KState.zero = Vector.replicate 25 0 := by
  rw [← toRpm_zero, ofRpm_toRpm]

/-! ## The model on lanes and on bytes -/

/-- The edges of a byte log, read on lanes. -/
abbrev projLog : Common.PermutationEdges Common.KState → Common.PermutationEdges KeccakState := logMap stateEquiv.symm

/-- A forward query on bytes is the forward query on lanes, read on bytes. -/
theorem fwd_rel (x : Common.KState) :
    StRel projLog (Common.lazyRandomPermutation (.forward x))
      (KState.toRpm <$> Common.lazyRandomPermutation (S := KeccakState) (.forward (KState.ofRpm x))) := by
  intro s
  have h := (lazyPerm_relabel stateEquiv (.forward (KState.ofRpm x)) s).map (Prod.map KState.toRpm id)
  simp only [mapQ, stateEquiv_apply, Functor.map_map] at h
  rw [toRpm_ofRpm] at h
  have e : (fun a ↦ Prod.map KState.toRpm id (Prod.map (⇑stateEquiv.symm)
      (logMap ⇑stateEquiv.symm) a)) = Prod.map id projLog := by
    funext p
    obtain ⟨a, b⟩ := p
    simp only [Prod.map_apply, stateEquiv_symm_apply, toRpm_ofRpm, id_eq]
  rw [e] at h
  rw [StateT.run_map]
  exact h

/-- The 32 bytes of a digest are `Digest.toRpm`'s. -/
theorem toBytes_eq_toRpm (d : Digest) : d.toBytes = Digest.toRpm d := by
  apply Vector.toList_inj.mp
  rw [toList_digestToRpm]
  simp [Digest.toBytes, digestBytes, lanesBytes]

theorem toBytes_ofRpm (d : Common.DigestBytes) : (Digest.ofRpm d).toBytes = d := by
  rw [toBytes_eq_toRpm, digestToRpm_ofRpm]

end LeanVM.Rpm

namespace Common

open LeanVM LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Rpm

/-- **A game of the model with its permutation queries read on bytes**: coins and Keccak-256 as
they are, a query `π x` or `π⁻¹ y` on lanes the query on the bytes of `x` or `y`, its answer read
back on lanes. -/
def relabel : QueryImpl KSpecH (OracleComp KSpecB)
  | .inl n => liftM (KSpecB.query (.inl n))
  | .inr (.inl m) => liftM (KSpecB.query (.inr (.inl m)))
  | .inr (.inr q) => KState.ofRpm <$> liftM (KSpecB.query (.inr (.inr (mapQ stateEquiv q))))

/-- The lanes' lazily sampled permutation, through the bytes. -/
theorem lazyPerm_eq_lanePerm :
    (fun x ↦ Common.lazyRandomPermutation (.forward x) : LeanVM.Semantics.KeccakState →
        StateT (PermutationEdges LeanVM.Semantics.KeccakState) ProbComp LeanVM.Semantics.KeccakState) =
      lanePerm (fun x ↦ KState.toRpm <$> Common.lazyRandomPermutation (S := LeanVM.Semantics.KeccakState)
        (.forward (KState.ofRpm x))) := by
  funext s
  simp only [lanePerm, Functor.map_map]
  rw [ofRpm_toRpm]
  simp only [ofRpm_toRpm, id_map']

/-- Each query of the model on lanes is its query on bytes, the edges read on lanes. -/
theorem relabel_step (t : KSpecH.Domain) (s : PermutationEdges KState) :
    Prod.map id projLog <$> ((realImpl keccakPadding KState.zero ∘ₛ relabel) t).run s =ᵈ
      (kImplH t).run (projLog s) := by
  rcases t with n | m | q
  · simp only [QueryImpl.apply_compose, relabel, simulateQ_spec_query, realImpl, kImplH]
    simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_lift, map_bind, map_pure,
      Prod.map_apply, id_eq]
    exact EvalDistEq.rfl
  · simp only [QueryImpl.apply_compose, relabel, simulateQ_spec_query, realImpl, kImplH]
    rw [lazyPerm_eq_lanePerm, keccak256With_rpm, Functor.map_map]
    simp only [toBytes_ofRpm, id_map']
    exact (StRel.map (absorbAll_rel _ _ fwd_rel _ _) _) s
  · simp only [QueryImpl.apply_compose, relabel, simulateQ_map, simulateQ_spec_query, realImpl,
      kImplH]
    have h := lazyPerm_relabel stateEquiv q s
    rw [StateT.run_map, Functor.map_map]
    exact h

/-- **A game of the model is the game on bytes**: against the lazily sampled permutations, the
game with its permutation queries on lanes and the game with them read on bytes have one
distribution. -/
theorem runK_relabel {α : Type} (G : OracleComp KSpecH α) :
    runKH G =ᵈ runKB (simulateQ relabel G) := by
  have h := map_run_simulateQ_evalDistEq_of_inv (realImpl keccakPadding KState.zero ∘ₛ relabel)
    kImplH (fun _ ↦ True) projLog (fun _ _ _ _ _ ↦ trivial) (fun t s _ ↦ relabel_step t s) G []
    trivial
  have h2 := h.map Prod.fst
  simp only [Functor.map_map] at h2
  rw [runKH, runKB, realGame, StateT.run'_eq, StateT.run'_eq, ← QueryImpl.simulateQ_compose]
  exact h2.symm

/-- **A game on bytes weighs what the game on lanes weighs**, for weights that give each query
on bytes at most the weight of the query on lanes it reads. -/
theorem isWeightBound_relabel' (w : KSpecH.Domain → ℕ) (w' : KSpecB.Domain → ℕ)
    (h0 : ∀ n, w' (.inl n) ≤ w (.inl n)) (h1 : ∀ m, w' (.inr (.inl m)) ≤ w (.inr (.inl m)))
    (h2 : ∀ q, w' (.inr (.inr (mapQ stateEquiv q))) ≤ w (.inr (.inr q))) {α : Type}
    {G : OracleComp KSpecH α} {Q : ℕ} (h : QueryCostAtMost G w Q) :
    QueryCostAtMost (simulateQ relabel G) w' Q := by
  induction G using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    rw [simulateQ_query_bind]
    rcases t with n | m | q
    · change QueryCostAtMost (liftM (KSpecB.query (.inl n)) >>= fun u ↦ simulateQ relabel (k u))
        w' Q
      exact (isWeightBound_query_bind_iff _ _ _ _).mpr
        ⟨(h0 n).trans h.1, fun u ↦ (ih u (h.2 u)).mono (by have := h0 n; omega)⟩
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inl m))) >>= fun u ↦
        simulateQ relabel (k u)) w' Q
      exact (isWeightBound_query_bind_iff _ _ _ _).mpr
        ⟨(h1 m).trans h.1, fun u ↦ (ih u (h.2 u)).mono (by have := h1 m; omega)⟩
    · change QueryCostAtMost ((KState.ofRpm <$>
        liftM (KSpecB.query (.inr (.inr (mapQ stateEquiv q))))) >>= fun u ↦
          simulateQ relabel (k u)) w' Q
      rw [bind_map_left]
      exact (isWeightBound_query_bind_iff _ _ _ _).mpr
        ⟨(h2 q).trans h.1, fun u ↦ (ih _ (h.2 _)).mono (by have := h2 q; omega)⟩

/-- **A game on bytes makes the permutation calls of the game on lanes.** -/
theorem isWeightBound_relabel {α : Type} {G : OracleComp KSpecH α} {Q : ℕ}
    (h : QueryCostAtMost G permCallsH Q) : QueryCostAtMost (simulateQ relabel G) permCallsB Q :=
  isWeightBound_relabel' permCallsH permCallsB (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)
    (fun q ↦ by cases q <;> exact le_rfl) h

/-- **A game on bytes read on lanes**: the inverse of `relabel`. -/
def unrelabel : QueryImpl KSpecB (OracleComp KSpecH)
  | .inl n => liftM (KSpecH.query (.inl n))
  | .inr (.inl m) => liftM (KSpecH.query (.inr (.inl m)))
  | .inr (.inr q) => KState.toRpm <$> liftM (KSpecH.query (.inr (.inr (mapQ stateEquiv.symm q))))

/-- An adversary with its queries read on bytes. -/
def relabelAdv {X β : Type} (A : X → OracleComp KSpecH β) : X → OracleComp KSpecB β :=
  fun x ↦ simulateQ relabel (A x)

/-- An adversary on bytes with its queries read on lanes. -/
def unrelabelAdv {X β : Type} (A : X → OracleComp KSpecB β) : X → OracleComp KSpecH β :=
  fun x ↦ simulateQ unrelabel (A x)

theorem mapQ_mapQ_symm (q : PermutationQuery KState) : mapQ stateEquiv (mapQ stateEquiv.symm q) = q := by
  cases q <;> simp [mapQ, toRpm_ofRpm]

/-- Reading on lanes, then on bytes, changes nothing. -/
theorem simulateQ_relabel_unrelabel {α : Type} (X : OracleComp KSpecB α) :
    simulateQ relabel (simulateQ unrelabel X) = X := by
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_id' X]
  congr 1
  funext t
  rcases t with n | m | q
  · simp [relabel, unrelabel]
  · simp [relabel, unrelabel]
  · simp only [QueryImpl.apply_compose, unrelabel, relabel, simulateQ_map, simulateQ_spec_query,
      Functor.map_map]
    rw [mapQ_mapQ_symm]
    simp [toRpm_ofRpm]

theorem relabelAdv_unrelabelAdv {X β : Type} (A : X → OracleComp KSpecB β) :
    relabelAdv (unrelabelAdv A) = A := by
  funext x
  exact simulateQ_relabel_unrelabel (A x)

/-- **A game on lanes weighs what it weighs on bytes**, in permutation calls. -/
theorem isWeightBound_relabel_iff {α : Type} (G : OracleComp KSpecH α) (Q : ℕ) :
    QueryCostAtMost (simulateQ relabel G) permCallsB Q ↔ QueryCostAtMost G permCallsH Q := by
  refine ⟨fun h ↦ ?_, isWeightBound_relabel⟩
  induction G using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [simulateQ_query_bind] at h
    rw [isWeightBound_query_bind_iff]
    rcases t with n | m | q
    · change QueryCostAtMost (liftM (KSpecB.query (.inl n)) >>= fun u ↦ simulateQ relabel (k u))
        permCallsB Q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · change QueryCostAtMost (liftM (KSpecB.query (.inr (.inl m))) >>= fun u ↦
        simulateQ relabel (k u)) permCallsB Q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩
    · change QueryCostAtMost ((KState.ofRpm <$>
        liftM (KSpecB.query (.inr (.inr (mapQ stateEquiv q))))) >>= fun u ↦
          simulateQ relabel (k u)) permCallsB Q at h
      rw [bind_map_left, isWeightBound_query_bind_iff] at h
      refine ⟨h.1, fun u ↦ ih u _ ?_⟩
      have := h.2 (KState.toRpm u)
      rwa [ofRpm_toRpm] at this

end Common
