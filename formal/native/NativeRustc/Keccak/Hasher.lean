module

public import NativeRustc.Keccak.Sponge

/-!
# `keccak256::Hasher` on its bytes

The streaming Keccak-256 of `crates/keccak256/src/lib.rs`, `Hasher { state: [u64; 25], buf: [u8;
RATE], buf_len: usize }`, as its 344 bytes in memory, in rustc's layout (`Hasher::update` reads
`buf_len` at byte 336 and `buf` at 200): the state's lanes at `0`, the buffer at `200`, `buf_len`
at `336` (`hasherSize`, `bufOff`, `bufLenOff`). The Rust functions on those bytes: `Hasher::new`
(`new`, a `memset` to zero: `new_eq_memset`), one turn of `update`'s loop (`updateStep`) and the
loop (`update`), `final_block` (`finalBlock`) and `finalize` (`finalize`); `keccak256`'s free
functions `hash` (`hashBytes`) and `path_fold` (`pathFold`).

`HasherHolds h absorbed`: the bytes `h` are a hasher that has absorbed `absorbed`: the state is the
sponge after its whole blocks, the buffer starts with the rest and `buf_len` counts it. `new` holds
`[]` (`holds_new`), a turn of `update`'s loop absorbs the bytes it takes (`holds_updateStep`, its
bytes `updateStep_split`), `update` absorbs its input (`holds_update`), and `finalize` is the bytes
of `keccak256` of what was absorbed (`finalize_eq`).
-/

@[expose] public section

namespace NativeRustc.Keccak

open LeanVM.Semantics LeanVM.Protocol.KeccakHash Native.Keccak Native.Keccak.Proof

/-! ## The layout -/

/-- A hasher's bytes. -/
def hasherSize : Nat := 344

/-- `buf`'s offset. -/
def bufOff : Nat := 200

/-- `buf_len`'s offset. -/
def bufLenOff : Nat := 336

/-- `buf_len`: the `usize` at byte 336. -/
def bufLen (h : List UInt8) : Nat := (littleEndianLane (h.drop 336) 0).toNat

/-! ## The Rust functions -/

/-- `Hasher::new`: every byte zero. -/
def new : List UInt8 := List.replicate 344 0

/-- `Hasher::new` is `memset` of its 344 bytes to `0`, as rustc compiles it. -/
theorem new_eq_memset : new = memsetBytes 0 344 := rfl

/-- One turn of `update`'s loop on the hasher `h` and the remaining input `data`: copy as much of
`data` as fits into `buf`, advance `buf_len`, and absorb a full buffer, `buf_len` back to `0`;
the hasher and the input left. -/
def updateStep (h data : List UInt8) : List UInt8 × List UInt8 :=
  let len := bufLen h
  let take := min (136 - len) data.length
  let h := writeAt h (200 + len) (data.take take)
  let len := len + take
  let h := writeAt h 336 (wordBytes len.toUInt64)
  if len = 136 then
    let h := writeAt h 0 (absorb (h.take 200) ((h.drop 200).take 136))
    (writeAt h 336 (wordBytes 0), data.drop take)
  else (h, data.drop take)

/-- `update`'s loop, at most `fuel` turns, while input remains. -/
def updateLoop : Nat → List UInt8 → List UInt8 → List UInt8
  | 0, h, _ => h
  | fuel + 1, h, data =>
    if data.isEmpty then h else updateLoop fuel (updateStep h data).1 (updateStep h data).2

/-- **`Hasher::update`**: the loop's turns until the input is consumed (each takes a byte). -/
def update (h data : List UInt8) : List UInt8 := updateLoop data.length h data

/-- `final_block`: the remaining bytes, zeros to `RATE`, `PAD_FIRST` XORed after the bytes and
`PAD_LAST` into the last byte. -/
def finalBlock (tail : List UInt8) : List UInt8 :=
  ((tail ++ List.replicate (136 - tail.length) 0).modify tail.length (· ^^^ 0x01)).modify 135
    (· ^^^ 0x80)

/-- `final_block` is the statement's padded block. -/
theorem finalBlock_eq_padBlock : finalBlock = padBlock := rfl

/-- **`Hasher::finalize`**: absorb the final block into a copy of the state; its digest. -/
def finalize (h : List UInt8) : List UInt8 :=
  digestOf (absorb (h.take 200) (finalBlock ((h.drop 200).take (bufLen h))))

/-! ## What a hasher holds -/

/-- **The bytes `h` are a hasher that has absorbed `absorbed`**: the state is the sponge after the
whole blocks of `absorbed`, `buf` holds its last `absorbed.length % 136` bytes then anything, and
`buf_len` is that count. -/
def HasherHolds (h absorbed : List UInt8) : Prop :=
  ∃ rest : List UInt8, rest.length = 136 - absorbed.length % 136 ∧
    h = stateBytes (sponge absorbed) ++ (absorbed.drop (136 * (absorbed.length / 136)) ++
      (rest ++ wordBytes (absorbed.length % 136).toUInt64))

theorem length_of_holds {h a : List UInt8} (hh : HasherHolds h a) : h.length = 344 := by
  obtain ⟨rest, hr, rfl⟩ := hh
  simp only [List.length_append, length_stateBytes, List.length_drop, hr, length_wordBytes]
  omega

/-- `buf_len` is the count of the bytes past the whole blocks. -/
theorem bufLen_of_holds {h a : List UInt8} (hh : HasherHolds h a) : bufLen h = a.length % 136 := by
  obtain ⟨rest, hr, rfl⟩ := hh
  rw [bufLen, ← List.append_assoc, ← List.append_assoc,
    List.drop_left' (by simp only [List.length_append, length_stateBytes, List.length_drop, hr]; omega),
    littleEndianLane_wordBytes, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

/-- The bytes of zero words. -/
theorem wordsBytes_replicate_zero : ∀ n : Nat,
    wordsBytes (List.replicate n (0 : UInt64)) = List.replicate (8 * n) 0
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, wordsBytes, List.flatMap_cons, ← wordsBytes,
      wordsBytes_replicate_zero n, show wordBytes 0 = List.replicate 8 0 from rfl,
      List.replicate_append_replicate]
    congr 1
    omega

/-- **`Hasher::new` holds nothing.** -/
theorem holds_new : HasherHolds new [] := by
  refine ⟨List.replicate 136 0, by simp, ?_⟩
  rw [show sponge [] = Vector.replicate 25 0 from rfl, stateBytes, Vector.toList_replicate,
    wordsBytes_replicate_zero, show wordBytes (([] : List UInt8).length % 136).toUInt64 =
      List.replicate 8 0 from rfl, List.drop_nil, List.nil_append, List.replicate_append_replicate,
    List.replicate_append_replicate]
  rfl

/-- Writing `src` over all of `q`, after the prefix `p`. -/
theorem writeAt_append_end (p q src : List UInt8) {off : Nat} (hoff : off = p.length)
    (hq : src.length = q.length) : writeAt (p ++ q) off src = p ++ src := by
  rw [writeAt_append p q src hoff, hq, List.drop_length, List.append_nil]

/-- One turn of `update`'s loop on a hasher whose state, buffered bytes, rest of `buf` and
`buf_len` are `S`, `T`, `rest` and `r`: it copies `t` bytes of `data` after `T`, then absorbs a
full buffer. -/
theorem updateStep_split (S T rest data : List UInt8) {r : Nat} (hS : S.length = 200)
    (hT : T.length = r) (hr : rest.length = 136 - r) (hr136 : r < 136) :
    updateStep (S ++ (T ++ (rest ++ wordBytes r.toUInt64))) data =
      if r + min (136 - r) data.length = 136 then
        (absorb S (T ++ data.take (min (136 - r) data.length)) ++
          (T ++ (data.take (min (136 - r) data.length) ++
            (rest.drop (min (136 - r) data.length) ++ wordBytes 0))),
          data.drop (min (136 - r) data.length))
      else
        (S ++ (T ++ (data.take (min (136 - r) data.length) ++
          (rest.drop (min (136 - r) data.length) ++
            wordBytes (r + min (136 - r) data.length).toUInt64))),
          data.drop (min (136 - r) data.length)) := by
  have hbl : bufLen (S ++ (T ++ (rest ++ wordBytes r.toUInt64))) = r := by
    rw [bufLen, ← List.append_assoc, ← List.append_assoc,
      List.drop_left' (by simp only [List.length_append, hS, hT, hr]; omega),
      littleEndianLane_wordBytes, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  simp only [updateStep, hbl]
  have htr : min (136 - r) data.length ≤ rest.length := by omega
  have hDl : (data.take (min (136 - r) data.length)).length = min (136 - r) data.length := by
    simp
  generalize min (136 - r) data.length = t at htr hDl ⊢
  generalize data.take t = D at hDl ⊢
  have h1 : writeAt (S ++ (T ++ (rest ++ wordBytes r.toUInt64))) (200 + r) D =
      (S ++ (T ++ (D ++ rest.drop t))) ++ wordBytes r.toUInt64 := by
    rw [← List.append_assoc S T, writeAt_append _ _ _ (by simp [hS, hT]), hDl,
      List.drop_append_of_le_length htr]
    simp only [List.append_assoc]
  rw [h1, writeAt_append_end _ _ _ (by simp [hS, hT, hDl]; omega) (by simp [length_wordBytes])]
  by_cases hfull : r + t = 136
  · have hW : (wordBytes (r + t).toUInt64).length = 8 := length_wordBytes _
    generalize wordBytes (r + t).toUInt64 = W at hW ⊢
    have hab : (absorb S (T ++ D)).length = 200 := by
      rw [absorb, keccakF, length_stateBytes]
    have hTD : (T ++ D).length = 136 := by simp [hT, hDl]; omega
    rw [show S ++ (T ++ (D ++ rest.drop t)) ++ W = [] ++ S ++ ((T ++ D) ++ (rest.drop t ++ W)) by
      simp only [List.nil_append, List.append_assoc], List.nil_append, List.take_left' hS,
      List.drop_left' hS, List.take_left' hTD]
    simp only [hfull, ↓reduceIte]
    rw [← List.nil_append (S ++ _), ← List.append_assoc [],
      writeAt_append_append (off := 0) [] _ _ _ rfl (hab.trans hS.symm), List.nil_append,
      show absorb S (T ++ D) ++ ((T ++ D) ++ (rest.drop t ++ W)) =
        (absorb S (T ++ D) ++ ((T ++ D) ++ rest.drop t)) ++ W by simp only [List.append_assoc],
      writeAt_append_end _ _ _ (by simp [hab]; omega) (by rw [length_wordBytes, hW])]
    simp only [List.append_assoc]
  · simp only [hfull, ↓reduceIte, List.append_assoc]

/-- **A turn of `update`'s loop absorbs the `k > 0` bytes it takes.** -/
theorem holds_updateStep {h a data : List UInt8} (hh : HasherHolds h a) (hd : data ≠ []) :
    ∃ k, 0 < k ∧ k ≤ data.length ∧ (updateStep h data).2 = data.drop k ∧
      HasherHolds (updateStep h data).1 (a ++ data.take k) := by
  obtain ⟨rest, hr, rfl⟩ := hh
  have hlen : 0 < data.length := List.length_pos_iff.mpr hd
  have hr136 : a.length % 136 < 136 := Nat.mod_lt _ (by omega)
  have hT : (a.drop (136 * (a.length / 136))).length = a.length % 136 := by simp; omega
  rw [updateStep_split _ _ _ data (length_stateBytes _) hT hr hr136]
  generalize hn : a.length / 136 = n at *
  generalize hrr : a.length % 136 = r at *
  have ha : a.length = 136 * n + r := by omega
  have hkeep : ∀ rest', absorbBlocks n (Vector.replicate 25 0) (a ++ rest') = sponge a := by
    intro rest'
    rw [sponge, hn, absorbBlocks_append _ _ _ _ (by omega)]
  generalize ht : min (136 - r) data.length = t
  have ht1 : 0 < t := by omega
  have hD : (data.take t).length = t := by simp; omega
  refine ⟨t, ht1, by omega, by split <;> rfl, ?_⟩
  by_cases hfull : r + t = 136
  · -- The buffer is full: absorbed, and `buf_len` back to `0`.
    have hl' : (a ++ data.take t).length = 136 * (n + 1) := by simp only [List.length_append, hD]; omega
    have hsp : sponge (a ++ data.take t) =
        absorbBlock (sponge a) (a.drop (136 * n) ++ data.take t) := by
      rw [sponge, hl', Nat.mul_div_cancel_left _ (by omega), absorbBlocks_succ, hkeep,
        List.drop_append_of_le_length (by omega), List.take_of_length_le (by simp; omega)]
    simp only [hfull, ↓reduceIte, absorb_stateBytes]
    refine ⟨a.drop (136 * n) ++ (data.take t ++ rest.drop t), by simp [hD, hl']; omega, ?_⟩
    rw [hl', Nat.mul_div_cancel_left _ (by omega), Nat.mul_mod_right,
      List.drop_of_length_le (le_of_eq hl'), hsp]
    simp only [List.nil_append, List.append_assoc]
    rw [show Nat.toUInt64 0 = 0 from rfl]
  · -- Room is left: the input is consumed.
    have htd : t = data.length := by omega
    have hl' : (a ++ data.take t).length = 136 * n + (r + t) := by simp only [List.length_append, hD]; omega
    simp only [hfull, ↓reduceIte]
    refine ⟨rest.drop t, by simp [hl']; omega, ?_⟩
    have hdiv : (a ++ data.take t).length / 136 = n := by
      rw [hl', Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have hmod : (a ++ data.take t).length % 136 = r + t := by
      rw [hl', Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hsp : sponge (a ++ data.take t) = sponge a := by rw [sponge, hdiv, hkeep]
    rw [hdiv, hmod, hsp, List.drop_append_of_le_length (by omega)]
    simp only [List.append_assoc]

/-- **`Hasher::update` absorbs its input.** -/
theorem holds_update {h a : List UInt8} (hh : HasherHolds h a) (data : List UInt8) :
    HasherHolds (update h data) (a ++ data) := by
  suffices key : ∀ fuel h a data, data.length ≤ fuel → HasherHolds h a →
      HasherHolds (updateLoop fuel h data) (a ++ data) from key _ h a data le_rfl hh
  intro fuel
  induction fuel with
  | zero =>
    intro h a data hf hh
    rw [List.eq_nil_of_length_eq_zero (by omega : data.length = 0), List.append_nil]
    exact hh
  | succ fuel ih =>
    intro h a data hf hh
    by_cases hd : data = []
    · subst hd
      simpa [updateLoop] using hh
    obtain ⟨k, hk0, hkl, hrest, hh'⟩ := holds_updateStep hh hd
    have hne : data.isEmpty = false := by simpa using hd
    rw [updateLoop, hne, hrest]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have := ih _ _ (data.drop k) (by simp; omega) hh'
    rwa [List.append_assoc, List.take_append_drop] at this

/-- **`Hasher::finalize` is Keccak-256** of what the hasher absorbed, its digest's 32 bytes. -/
theorem finalize_eq {h a : List UInt8} (hh : HasherHolds h a) :
    finalize h = digestBytes (keccak256 a) := by
  have hbl := bufLen_of_holds hh
  obtain ⟨rest, hr, rfl⟩ := hh
  have hT : (a.drop (136 * (a.length / 136))).length = a.length % 136 := by simp; omega
  rw [finalize, hbl, List.take_left' (length_stateBytes _), List.drop_left' (length_stateBytes _),
    List.take_left' hT, finalBlock_eq_padBlock, absorb_stateBytes, digestOf_absorb_sponge]

/-! ## `keccak256`'s free functions -/

/-- `keccak256::hash`: Keccak-256's 32 bytes (what a `Hasher` that absorbed `data` finalizes,
`finalize_eq`). -/
def hashBytes (data : List UInt8) : List UInt8 := digestBytes (keccak256 data)

/-- `path_fold`: the root `leaf`, at index `e`, and its `path` reach; the node above level `z` is
`node (z + 1) (e >> (z + 1))` of the two children, bit `z` of `e` saying which is the sibling. -/
def pathFold (leaf : List UInt8) (e : Nat) (path : List (List UInt8))
    (node : Nat → Nat → List UInt8 → List UInt8) : List UInt8 :=
  (List.range path.length).foldl (fun current z ↦
    let sibling := path.getD z []
    node (z + 1) (e >>> (z + 1))
      (if e >>> z &&& 1 = 0 then current ++ sibling else sibling ++ current)) leaf

end NativeRustc.Keccak
