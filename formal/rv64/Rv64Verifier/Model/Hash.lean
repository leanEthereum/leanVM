import Statement.Fast.Keccak

/-!
# Keccak-256 as the Rust computes it

`crates/verifier/src/hash.rs`, one mirror per function, following the Rust's loops as
`Model.Multilinear` does: a `u64` is a `BitVec 64`, a `u8` a `BitVec 8`, the state `[u64; 25]` and
the byte buffers are `List`s, and a loop over `0..n` is `(List.range n).foldl`. `keccakFRust` is
`keccak_f` (`keccakFRust_eq`: Keccak-f[1600], through `Statement.Fast.Keccak`'s `roundLanes`),
`xorBlockRust` is `xor_block`, `keccakHashRust` is `keccak_hash` and `digestWordsRust` is
`Digest::words` (`keccakHashRust_eq`, `digestWordsRust_keccakHashRust`: Keccak-256 over
Keccak-f[1600]).
-/

namespace Rv64Verifier.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## The tables -/

/-- `KECCAK_RC`. -/
def keccakRCRust : List (BitVec 64) := [
  0x0000000000000001#64, 0x0000000000008082#64, 0x800000000000808A#64, 0x8000000080008000#64,
  0x000000000000808B#64, 0x0000000080000001#64, 0x8000000080008081#64, 0x8000000000008009#64,
  0x000000000000008A#64, 0x0000000000000088#64, 0x0000000080008009#64, 0x000000008000000A#64,
  0x000000008000808B#64, 0x800000000000008B#64, 0x8000000000008089#64, 0x8000000000008003#64,
  0x8000000000008002#64, 0x8000000000000080#64, 0x000000000000800A#64, 0x800000008000000A#64,
  0x8000000080008081#64, 0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64]

/-- `KECCAK_RHO`. -/
def keccakRhoRust : List ℕ :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- `KECCAK_PI`, as the constant evaluates. -/
def keccakPiRust : List ℕ :=
  [0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9, 19, 4]

theorem keccakRCRust_eq : keccakRCRust = keccakRC.map UInt64.toBitVec := by decide +kernel

theorem keccakRhoRust_eq : keccakRhoRust = keccakRho := rfl

/-- The constant's loop, `pi[i] = i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)`. -/
theorem keccakPiRust_eq : keccakPiRust = (List.range 25).map keccakPi := by decide +kernel

/-! ## `keccak_f` -/

/-- One iteration of `keccak_f`'s loop, with the round constant `rc`: θ's `c` and `d`, `d` XORed
into the rows, ρ and π into `b`, χ row by row from `b`, then ι. -/
def keccakRoundRust (a : List (BitVec 64)) (rc : BitVec 64) : List (BitVec 64) :=
  let c := (List.range 5).map fun x ↦
    a.getD x 0 ^^^ a.getD (x + 5) 0 ^^^ a.getD (x + 10) 0 ^^^ a.getD (x + 15) 0 ^^^ a.getD (x + 20) 0
  let d := (List.range 5).map fun x ↦
    c.getD ((x + 4) % 5) 0 ^^^ (c.getD ((x + 1) % 5) 0).rotateLeft 1
  let a := (List.range 5).foldl (fun a y ↦ (List.range 5).foldl
    (fun a x ↦ a.set (5 * y + x) (a.getD (5 * y + x) 0 ^^^ d.getD x 0)) a) a
  let b := (List.range 25).foldl (fun b i ↦
    b.set (keccakPiRust.getD i 0) ((a.getD i 0).rotateLeft (keccakRhoRust.getD i 0)))
    (List.replicate 25 0)
  let a := (List.range 5).foldl (fun a y ↦ (List.range 5).foldl
    (fun a x ↦ a.set (5 * y + x) (b.getD (5 * y + x) 0 ^^^
      (~~~ b.getD (5 * y + (x + 1) % 5) 0 &&& b.getD (5 * y + (x + 2) % 5) 0))) a) a
  a.set 0 (a.getD 0 0 ^^^ rc)

/-- `keccak_f`: a round per constant of `KECCAK_RC`. -/
def keccakFRust (a : List (BitVec 64)) : List (BitVec 64) := keccakRCRust.foldl keccakRoundRust a

/-- The state as the Rust holds it. -/
def stateBits (a : KeccakState) : List (BitVec 64) := a.toList.map UInt64.toBitVec

theorem rot_toBitVec (x : UInt64) {n : ℕ} (hn : n < 64) :
    (Keccak.rot x n).toBitVec = x.toBitVec.rotateLeft n := by
  rw [BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn, Keccak.rot]
  split
  · next h =>
    subst h
    have : x.toBitVec >>> 64 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      rw [Nat.div_eq_of_lt x.toBitVec.isLt]
    simp [this]
  · next h =>
    have h1 : (n.toUInt64.toBitVec % 64).toNat = n := by
      simp [Nat.mod_eq_of_lt hn]
    have h2 : ((64 - n).toUInt64.toBitVec % 64).toNat = 64 - n := by
      simp [Nat.mod_eq_of_lt (show 64 - n < 64 by omega)]
    rw [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', h1, h2]

theorem round_toBitVec (a : KeccakState) (rc : UInt64) :
    keccakRoundRust (stateBits a) rc.toBitVec = stateBits (Keccak.round a rc) := by
  rw [LeanVM.Fast.Keccak.round_eq_roundLanes]
  obtain ⟨⟨l⟩, hl⟩ := a
  match l, hl with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
      a20, a21, a22, a23, a24], _ =>
    simp only [keccakRoundRust, LeanVM.Fast.Keccak.roundLanes, stateBits, Keccak.lane,
      keccakPiRust, keccakRhoRust,
      show List.range 5 = [0, 1, 2, 3, 4] from rfl,
      show List.range 25 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
        20, 21, 22, 23, 24] from rfl]
    simp [rot_toBitVec, UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not]

theorem keccakF_foldl (rcs : List UInt64) (a : KeccakState) :
    (rcs.map UInt64.toBitVec).foldl keccakRoundRust (stateBits a) =
      stateBits (rcs.foldl Keccak.round a) := by
  induction rcs generalizing a with
  | nil => rfl
  | cons rc rcs ih => simp only [List.map_cons, List.foldl_cons, round_toBitVec, ih]

/-- **`keccak_f` is Keccak-f[1600].** -/
theorem keccakFRust_eq (a : KeccakState) : keccakFRust (stateBits a) = stateBits (keccakF1600 a) := by
  rw [keccakFRust, keccakRCRust_eq, keccakF_foldl, keccakF1600]

/-! ## `xor_block`, `keccak_hash`, `Digest::words` -/

/-- `u64::from_le_bytes`. -/
def fromLeBytes (bytes : List (BitVec 8)) : BitVec 64 :=
  (List.range 8).foldl (fun acc k ↦ acc ||| (bytes.getD k 0).setWidth 64 <<< (8 * k)) 0

/-- `u64::to_le_bytes`. -/
def toLeBytes (w : BitVec 64) : List (BitVec 8) :=
  (List.range 8).map fun k ↦ (w >>> (8 * k)).setWidth 8

/-- `xor_block`: lane `i` XORed with the block's chunk `8i..8i+8`, for the `17` lanes the zip
reaches. -/
def xorBlockRust (state : List (BitVec 64)) (block : List (BitVec 8)) : List (BitVec 64) :=
  (List.range 17).foldl
    (fun s i ↦ s.set i (s.getD i 0 ^^^ fromLeBytes ((block.drop (8 * i)).take 8))) state

/-- `keccak_hash`'s last block: `[0; RATE]` with the tail copied in, `0x01` XORed after the tail and
`0x80` into the last byte. -/
def padBlockRust (tail : List (BitVec 8)) : List (BitVec 8) :=
  let block := tail ++ (List.replicate 136 0).drop tail.length
  let block := block.set tail.length (block.getD tail.length 0 ^^^ 0x01#8)
  block.set 135 (block.getD 135 0 ^^^ 0x80#8)

/-- `keccak_hash`: the whole blocks of `136` bytes, each XORed in and permuted, then the padded
tail, then the first four lanes' bytes. -/
def keccakHashRust (data : List (BitVec 8)) : List (BitVec 8) :=
  let blocks := data.length / 136
  let state := (List.range blocks).foldl (fun state j ↦
    keccakFRust (xorBlockRust state ((data.drop (136 * j)).take 136))) (List.replicate 25 0)
  let state := keccakFRust (xorBlockRust state (padBlockRust (data.drop (136 * blocks))))
  (List.range 4).flatMap fun i ↦ toLeBytes (state.getD i 0)

/-- `Digest::words`. -/
def digestWordsRust (value : List (BitVec 8)) : List (BitVec 64) :=
  (List.range 4).map fun i ↦ fromLeBytes ((value.drop (8 * i)).take 8)

/-- Bytes as the Rust holds them. -/
def byteBits (bytes : List UInt8) : List (BitVec 8) := bytes.map UInt8.toBitVec

theorem foldl_hom_mem {α β γ : Type} (h : α → β) (f : α → γ → α) (g : β → γ → β) (l : List γ)
    (H : ∀ a, ∀ x ∈ l, h (f a x) = g (h a) x) (a : α) : h (l.foldl f a) = l.foldl g (h a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [ih (fun b y hy ↦ H b y (by simp [hy])), H a x (by simp)]

theorem getD_byteBits_take_drop (bytes : List UInt8) (i k : ℕ) (hk : k < 8) :
    (((byteBits bytes).drop (8 * i)).take 8).getD k 0 = (bytes.getD (8 * i + k) 0).toBitVec := by
  simp only [byteBits, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, hk, ↓reduceIte]
  cases bytes[8 * i + k]? <;> rfl

theorem fromLeBytes_byteBits (bytes : List UInt8) (i : ℕ) :
    fromLeBytes (((byteBits bytes).drop (8 * i)).take 8) = (littleEndianLane bytes i).toBitVec := by
  rw [fromLeBytes, littleEndianLane]
  symm
  refine foldl_hom_mem UInt64.toBitVec _ _ _ (fun acc k hk ↦ ?_) 0
  have hk : k < 8 := List.mem_range.mp hk
  have hs : ((8 * k).toUInt64.toBitVec % 64).toNat = 8 * k := by
    rw [BitVec.toNat_umod]
    simp
    omega
  rw [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', hs,
    UInt8.toBitVec_toUInt64, getD_byteBits_take_drop _ _ _ hk]

theorem getElem?_foldl_xor (G : ℕ → BitVec 64) (l : List (BitVec 64)) :
    ∀ (n j : ℕ), ((List.range n).foldl (fun s i ↦ s.set i (s.getD i 0 ^^^ G i)) l)[j]? =
      l[j]?.map fun x ↦ if j < n then x ^^^ G j else x
  | 0, j => by simp
  | n + 1, j => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hj : j = n
    · subst hj
      rw [List.getElem?_set_self', List.getD_eq_getElem?_getD, getElem?_foldl_xor G l j j]
      cases l[j]? <;> simp
    · rw [List.getElem?_set_ne (Ne.symm hj), getElem?_foldl_xor G l n j]
      cases l[j]? with
      | none => rfl
      | some x =>
        simp only [Option.map_some]
        congr 1
        by_cases h : j < n
        · simp [h, show j < n + 1 by omega]
        · simp [h, show ¬ j < n + 1 by omega]

theorem xorBlockRust_eq (s : KeccakState) (block : List UInt8) :
    xorBlockRust (stateBits s) (byteBits block) = stateBits (Vector.ofFn fun i : Fin 25 ↦
      if i.val < 17 then Keccak.lane s i ^^^ littleEndianLane block i else Keccak.lane s i) := by
  apply List.ext_getElem?
  intro j
  rw [xorBlockRust, getElem?_foldl_xor]
  by_cases hj : j < 25
  · simp [stateBits, hj, Keccak.lane, fromLeBytes_byteBits]
    split_ifs <;> simp
  · simp [stateBits, hj]

theorem length_byteBits (bytes : List UInt8) : (byteBits bytes).length = bytes.length :=
  List.length_map _

theorem byteBits_set_xor (l : List UInt8) (i : ℕ) (c : UInt8) :
    (byteBits l).set i ((byteBits l).getD i 0 ^^^ c.toBitVec) =
      byteBits (l.set i (l[i]?.getD default ^^^ c)) := by
  rw [byteBits, byteBits, List.map_set, List.getD_eq_getElem?_getD, List.getElem?_map,
    UInt8.toBitVec_xor]
  cases l[i]? <;> rfl

theorem padBlockRust_eq (rem : List UInt8) :
    padBlockRust (byteBits rem) = byteBits (padBlock rem) := by
  have hb : byteBits rem ++ (List.replicate 136 (0 : BitVec 8)).drop (byteBits rem).length =
      byteBits (rem ++ List.replicate (rate - rem.length) 0) := by
    rw [List.drop_replicate]
    simp only [byteBits, List.map_append, List.map_replicate, List.length_map]
    rfl
  simp only [padBlockRust]
  rw [hb, length_byteBits, show (0x01#8) = padFirst.toBitVec from rfl, byteBits_set_xor,
    show (0x80#8) = padLast.toBitVec from rfl, byteBits_set_xor, padBlock, List.modify_eq_set,
    List.modify_eq_set]
  rfl

theorem absorbWith_succ (n : ℕ) (s : KeccakState) (data : List UInt8) :
    absorbWith (m := Id) keccakF1600 (n + 1) s data =
      absorbWith (m := Id) keccakF1600 n (absorbBlockWith (m := Id) keccakF1600 s (data.take rate))
        (data.drop rate) := rfl

theorem absorbBlock_eq (s : KeccakState) (block : List UInt8) :
    keccakFRust (xorBlockRust (stateBits s) (byteBits block)) =
      stateBits (absorbBlockWith (m := Id) keccakF1600 s block) := by
  rw [xorBlockRust_eq, keccakFRust_eq]
  rfl

theorem absorb_eq : ∀ (n : ℕ) (s : KeccakState) (data : List UInt8),
    keccakFRust (xorBlockRust ((List.range n).foldl (fun state j ↦
      keccakFRust (xorBlockRust state (((byteBits data).drop (136 * j)).take 136))) (stateBits s))
      (padBlockRust ((byteBits data).drop (136 * n)))) =
      stateBits (absorbWith (m := Id) keccakF1600 n s data)
  | 0, s, data => by
    rw [List.range_zero, List.foldl_nil, Nat.mul_zero, List.drop_zero, padBlockRust_eq,
      absorbBlock_eq]
    rfl
  | n + 1, s, data => by
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map, absorbWith_succ,
      ← absorb_eq n _ (data.drop rate), ← absorbBlock_eq]
    have hd : ∀ j, (byteBits data).drop (136 * Nat.succ j) = (byteBits (data.drop rate)).drop (136 * j) := by
      intro j
      rw [byteBits, byteBits, List.map_drop, List.drop_drop, Nat.mul_succ, Nat.add_comm]
      rfl
    simp only [hd, Nat.mul_zero, List.drop_zero, show 136 * (n + 1) = 136 * Nat.succ n from rfl]
    simp only [byteBits, List.map_take]
    rfl

theorem toLeBytes_toBitVec (w : UInt64) : toLeBytes w.toBitVec = byteBits (wordBytes w) := by
  rw [toLeBytes, byteBits, wordBytes, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hk : k < 8 := List.mem_range.mp hk
  have hs : ((8 * k).toUInt64.toBitVec % 64).toNat = 8 * k := by
    rw [BitVec.toNat_umod]
    simp
    omega
  simp only [Function.comp, UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight,
    BitVec.ushiftRight_eq', hs]

theorem getD_stateBits (s : KeccakState) {i : ℕ} (hi : i < 25) :
    (stateBits s).getD i 0 = (Keccak.lane s i).toBitVec := by
  simp [stateBits, Keccak.lane, hi]

/-- **`keccak_hash` is Keccak-256 over Keccak-f[1600]**, its 32 bytes the digest's. -/
theorem keccakHashRust_eq (data : List UInt8) :
    keccakHashRust (byteBits data) =
      byteBits (digestBytes (keccak256With (m := Id) keccakF1600 data)) := by
  have h0 : List.replicate 25 (0 : BitVec 64) = stateBits (Vector.replicate 25 0) := by
    simp [stateBits]
  simp only [keccakHashRust]
  rw [h0, length_byteBits, absorb_eq]
  simp only [keccak256With, digestBytes, show List.range 4 = [0, 1, 2, 3] from rfl,
    List.flatMap_cons, List.flatMap_nil, getD_stateBits _ (show 0 < 25 by omega),
    getD_stateBits _ (show 1 < 25 by omega), getD_stateBits _ (show 2 < 25 by omega),
    getD_stateBits _ (show 3 < 25 by omega), toLeBytes_toBitVec, byteBits]
  rfl

theorem fromLeBytes_toLeBytes (w : BitVec 64) : fromLeBytes (toLeBytes w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [fromLeBytes, toLeBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  interval_cases i <;> simp

theorem length_toLeBytes (w : BitVec 64) : (toLeBytes w).length = 8 := by simp [toLeBytes]

theorem digestWordsRust_digestBytes (d : Digest) :
    digestWordsRust (byteBits (digestBytes d)) = d.toList.map UInt64.toBitVec := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [w0, w1, w2, w3], _ =>
    simp only [digestBytes, byteBits, Vector.toList_mk, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append]
    have h : ∀ w, (wordBytes w).map UInt8.toBitVec = toLeBytes w.toBitVec := fun w ↦
      (toLeBytes_toBitVec w).symm
    simp [h, digestWordsRust, show List.range 4 = [0, 1, 2, 3] from rfl, List.drop_append,
      List.take_append, length_toLeBytes, List.take_of_length_le, List.drop_of_length_le,
      fromLeBytes_toLeBytes]

/-- **`Digest::words` of `keccak_hash` are the statement's digest.** -/
theorem digestWordsRust_keccakHashRust (data : List UInt8) :
    digestWordsRust (keccakHashRust (byteBits data)) =
      (keccak256With (m := Id) keccakF1600 data).toList.map UInt64.toBitVec := by
  rw [keccakHashRust_eq, digestWordsRust_digestBytes]

end Rv64Verifier.Model
