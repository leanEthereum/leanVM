module

public import NativeRustcVmArm.Code.Vm.StackOffsets.Names
public import NativeRustcVmArm.Layout.StackOffsets.Exec
public import NativeRustcVmArm.Layout.Frame
public import NativeRustcVmArm.Layout.InsertionSort
public import NativeVm.Math.Layout

/-!
# `stack_offsets` on AArch64: the model, the frame, the registers

- The model (`ord`, `P`): the order `insertion_sort` leaves in `order` (`ord`, a permutation of
  the indices, `ord_perm`), and the layout after its first `k` blocks (`P`, the model's fold
  `placeStep` along it); `stackOffsets` is `P` after all (`stackOffsets_eq`). `OffsetsFit` fails
  where the code fails: a size past `63` (`not_fit_size`), a sum past `u64` (`not_fit_sum`), and
  holds where the sum stays a `u64` (`fit_end`).
- Memory: the order array's first `j` words (`Ords`), the offsets placed so far (`OutAt`), each
  kept by the writes of the next block (`Ords.step`, `OutAt.step`) and complete at the end
  (`OutAt.words`).
- The frame (`Fr`: `Frame` with the offsets as output, `1328` bytes, all the stack): a block
  writing only into one region (`Frame.of_region`), a block of registers only (`run_regs`).
- The callee-saved registers the body reads (`Regs`).
-/

namespace NativeRustcVmArm.Layout.StackOffsets

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Layout
open NativeRustcVmArm.Arrays (calleeRegs inSlots keepsAll regs_eq_of mem_calleeRegs inSlots_false)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)
open NativeVm.Math.Layout (placeStep getD_set! stackOffsets_order)
open LeanVM.Protocol.Verifier (log2Ceil)

@[expose] public section

/-! ## The model -/

/-- The number of blocks. -/
abbrev n (m : MachineData) : Nat := m.regs.X1.toNat
/-- The sizes. -/
abbrev sizes (m : MachineData) : Array Nat := natsOf m m.regs.X0 m.regs.X1.toNat
/-- A block's log-size, `0` past the sizes. -/
abbrev size (m : MachineData) (i : Nat) : Nat := (sizes m).getD i 0
/-- The order `insertion_sort` leaves in `order`. -/
def ord (m : MachineData) : Array Nat :=
  insertionSort (sortLt (size m)) (Array.range m.regs.X1.toNat)
/-- The layout after the first `k` blocks of the order. -/
def P (m : MachineData) (k : Nat) : Array Nat × Nat :=
  ((ord m).toList.take k).foldl (placeStep (size m)) (Array.replicate m.regs.X1.toNat 0, 0)

theorem size_sizes (m : MachineData) : (sizes m).size = n m := by
  simp [sizes, natsOf, NativeRustcVm.wordsOf]

theorem ord_perm (m : MachineData) : (ord m).toList.Perm (List.range (n m)) := by
  have h : (insertionSort (fun i j ↦ decide (size m j < size m i) ||
      (decide (size m i = size m j) && decide (i < j))) (Array.range (sizes m).size)).toList.Perm
      (List.range (sizes m).size) := (stackOffsets_order (sizes m)).1
  rw [size_sizes] at h
  exact h

theorem ord_size (m : MachineData) : (ord m).size = n m := by
  simpa using (ord_perm m).length_eq

theorem ord_mem {m : MachineData} {i : Nat} (h : i ∈ (ord m).toList) : i < n m :=
  List.mem_range.mp ((ord_perm m).mem_iff.mp h)

theorem ord_lt {m : MachineData} {k : Nat} (hk : k < (ord m).size) : (ord m)[k] < n m :=
  ord_mem (Array.getElem_mem_toList hk)

theorem foldl_snd (sz : Nat → Nat) :
    ∀ (L : List Nat) (acc : Array Nat × Nat),
      (L.foldl (placeStep sz) acc).2 = acc.2 + (L.map (2 ^ sz ·)).sum
  | [], acc => by simp
  | x :: L, acc => by
    rw [List.foldl_cons, foldl_snd sz L, List.map_cons, List.sum_cons, placeStep]
    simp only
    omega

theorem foldl_size (sz : Nat → Nat) :
    ∀ (L : List Nat) (acc : Array Nat × Nat), (L.foldl (placeStep sz) acc).1.size = acc.1.size
  | [], acc => rfl
  | x :: L, acc => by
    rw [List.foldl_cons, foldl_size sz L, placeStep]
    simp

theorem P_snd (m : MachineData) (k : Nat) :
    (P m k).2 = (((ord m).toList.take k).map (2 ^ size m ·)).sum := by
  rw [P, foldl_snd, Nat.zero_add]

theorem P_size (m : MachineData) (k : Nat) : (P m k).1.size = n m := by
  rw [P, foldl_size]; simp

theorem P_zero (m : MachineData) : P m 0 = (Array.replicate (n m) 0, 0) := by
  simp [P]

theorem P_succ {m : MachineData} {k : Nat} (hk : k < (ord m).size) :
    P m (k + 1) = placeStep (size m) (P m k) (ord m)[k] := by
  simp [P, List.take_add_one, List.foldl_append, hk]

theorem P_succ_snd {m : MachineData} {k : Nat} (hk : k < (ord m).size) :
    (P m (k + 1)).2 = (P m k).2 + 2 ^ size m (ord m)[k] := by
  rw [P_succ hk, placeStep]

theorem P_succ_getD {m : MachineData} {k : Nat} (hk : k < (ord m).size) (i : Nat) :
    (P m (k + 1)).1.getD i 0 = if i = (ord m)[k] then (P m k).2 else (P m k).1.getD i 0 := by
  rw [P_succ hk, placeStep, getD_set!, P_size]
  have := ord_lt hk
  by_cases h : i = (ord m)[k] <;> simp [h, this]

theorem take_length_ord (m : MachineData) : (ord m).toList.take (n m) = (ord m).toList :=
  List.take_of_length_le (by simp [ord_size])

/-- **The model's `stackOffsets`** is `P` after every block. -/
theorem stackOffsets_eq (m : MachineData) :
    stackOffsets (sizes m) = ((P m (n m)).1, log2Ceil (P m (n m)).2) := by
  have e : stackOffsets (sizes m) =
      (((ord m).toList.foldl (placeStep (size m)) (Array.replicate (n m) 0, 0)).1,
        log2Ceil ((ord m).toList.foldl (placeStep (size m)) (Array.replicate (n m) 0, 0)).2) := by
    rw [Array.foldl_toList]
    unfold stackOffsets
    simp only [size_sizes]
    rfl
  rw [e, P, take_length_ord]

theorem le_sum_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by simp
  | y :: _, _, .tail _ h => by have := le_sum_of_mem h; simp; omega

theorem sum_take_le (f : Nat → Nat) (L : List Nat) (j : Nat) :
    ((L.take j).map f).sum ≤ (L.map f).sum := by
  conv_rhs => rw [← List.take_append_drop j L]
  rw [List.map_append, List.sum_append]
  omega

/-- The total of the sizes, along the order. -/
theorem total_eq (m : MachineData) :
    ((sizes m).toList.map (2 ^ ·)).sum = ((ord m).toList.map (2 ^ size m ·)).sum := by
  have e : (sizes m).toList.map (2 ^ ·) = (List.range (n m)).map (2 ^ size m ·) := by
    apply List.ext_getElem (by simp [size_sizes])
    intro i h1 h2
    have hi : i < (sizes m).size := by simpa using h1
    simp [size, Array.getD, hi]
  rw [e, ((ord_perm m).map _).sum_eq]

/-- A size past `63`: the blocks do not fit. -/
theorem not_fit_size {m : MachineData} {i : Nat} (hi : i < n m) (h : 64 ≤ size m i) :
    ¬OffsetsFit (sizes m) := fun hf ↦ by
  have hi' : i < (sizes m).size := by rw [size_sizes]; exact hi
  have := hf.1 _ (Array.getElem_mem hi')
  have e : size m i = (sizes m)[i] := by simp [size, Array.getD, hi']
  omega

/-- A sum past `u64`: the blocks do not fit. -/
theorem not_fit_sum {m : MachineData} {k : Nat} (hk : k < (ord m).size)
    (h : 2 ^ 64 ≤ (P m k).2 + 2 ^ size m (ord m)[k]) : ¬OffsetsFit (sizes m) := fun hf ↦ by
  have h1 := hf.2
  rw [total_eq] at h1
  have h2 := sum_take_le (2 ^ size m ·) (ord m).toList (k + 1)
  rw [← P_snd, P_succ_snd hk] at h2
  omega

/-- The sum a `u64`: the blocks fit. -/
theorem fit_end {m : MachineData} (h : (P m (n m)).2 < 2 ^ 64) : OffsetsFit (sizes m) := by
  have ht : ((sizes m).toList.map (2 ^ ·)).sum = (P m (n m)).2 := by
    rw [total_eq, P_snd, take_length_ord]
  refine ⟨fun s hs ↦ ?_, by rw [ht]; exact h⟩
  have h1 := le_sum_of_mem (List.mem_map_of_mem (f := (2 ^ ·)) (Array.mem_toList_iff.mpr hs))
  rw [ht] at h1
  by_contra hc
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.le_of_not_lt hc)
  omega

/-! ## Memory -/

/-- The frame's base: `order` at its byte `0`. -/
abbrev fb (m : MachineData) : BitVec 64 := fbase m 1328
/-- `offsets`. -/
abbrev out (m : MachineData) : BitVec 64 := m.regs.X2.toBitVec
/-- `offsets`' length. -/
abbrev cap (m : MachineData) : Nat := m.regs.X3.toNat

/-- **The order array's first `j` words**: `0`, …, `j - 1`. -/
def Ords (m0 : MachineData) (j : Nat) (d : Mem 64) : Prop :=
  ∀ t < j, WordAt d (fb m0 + BitVec.ofNat 64 (8 * t)) t.toUInt64

/-- **`c` more words of the order array**, written by a block into `8 c` bytes from word `j`. -/
theorem Ords.step {m0 : MachineData} {j c : Nat} {d d' : Mem 64} (h : Ords m0 j d)
    (hnw : NativeRustcVm.NoWrap (fb m0) 1328) (hle : 8 * (j + c) ≤ 1328)
    (hs : ∀ p, ¬InRange (fb m0 + BitVec.ofNat 64 (8 * j)) (8 * c) p → d'.get? p = d.get? p)
    (hnew : ∀ t, j ≤ t → t < j + c → WordAt d' (fb m0 + BitVec.ofNat 64 (8 * t)) t.toUInt64) :
    Ords m0 (j + c) d' := fun t ht ↦ by
  by_cases htj : t < j
  · refine Arrays.bytesAt_congr (h t htj) fun q hq ↦ hs _ ?_
    have hq8 : q < 8 := by simpa [NativeRustcVm.length_wordBytes] using hq
    rw [NativeRustcVm.addr_add]
    exact NativeRustcVm.not_inRange_sub hnw (by omega) (by omega) (by omega)
  · exact hnew t (by omega) ht

/-- The order array's words: `natsOf` reads the indices. -/
theorem natsOf_ords {m0 st : MachineData} {a : UInt64} (ha : a.toBitVec = fb m0) {j : Nat}
    (hj : j < 2 ^ 64) (h : Ords m0 j st.dmem) : natsOf st a j = Array.range j := by
  have hl : (wordsOf st.dmem a.toBitVec j).map UInt64.toNat = List.range j := by
    apply List.ext_getElem (by simp [NativeRustcVm.wordsOf])
    intro t h1 h2
    have ht : t < j := by simpa using h2
    simp only [NativeRustcVm.wordsOf, List.getElem_map, List.getElem_range]
    rw [ha, NativeRustcVm.wordOf_of_wordAt (h t ht)]
    exact InsertionSort.toNat_toUInt64 (by omega)
  rw [natsOf, hl]
  apply Array.ext'
  simp

/-- **The offsets placed after `k` blocks.** -/
def OutAt (m0 : MachineData) (k : Nat) (d : Mem 64) : Prop :=
  ∀ i ∈ (ord m0).toList.take k,
    WordAt d (out m0 + BitVec.ofNat 64 (8 * i)) ((P m0 k).1.getD i 0).toUInt64

theorem outAt_zero (m0 : MachineData) (d : Mem 64) : OutAt m0 0 d := by
  intro i hi; simp at hi

/-- **Block `k` placed**: `P k`'s sum stored at its offset, the others kept. -/
theorem OutAt.step {m0 : MachineData} {k : Nat} {d d' : Mem 64} (h : OutAt m0 k d)
    (hk : k < (ord m0).size) (hnw : NativeRustcVm.NoWrap (out m0) (8 * cap m0))
    (hcap : n m0 ≤ cap m0)
    (hw : WordAt d' (out m0 + BitVec.ofNat 64 (8 * (ord m0)[k])) (P m0 k).2.toUInt64)
    (hs : ∀ p, ¬InRange (out m0 + BitVec.ofNat 64 (8 * (ord m0)[k])) 8 p →
      d'.get? p = d.get? p) : OutAt m0 (k + 1) d' := by
  intro i hi
  rw [P_succ_getD hk]
  have hik := ord_lt hk
  rw [List.take_add_one, List.mem_append, Array.getElem?_toList, Array.getElem?_eq_getElem hk] at hi
  by_cases he : i = (ord m0)[k]
  · simp only [he, ↓reduceIte]; exact hw
  · simp only [he, ↓reduceIte]
    have hi' : i ∈ (ord m0).toList.take k := by
      rcases hi with hi | hi
      · exact hi
      · simp at hi; exact absurd hi he
    have hin : i < n m0 := ord_mem (List.mem_of_mem_take hi')
    refine Arrays.bytesAt_congr (h i hi') fun q hq ↦ hs _ ?_
    have hq8 : q < 8 := by simpa [NativeRustcVm.length_wordBytes] using hq
    rw [NativeRustcVm.addr_add]
    refine NativeRustcVm.not_inRange_sub hnw (by omega) (by omega) ?_
    omega

/-- **Every block placed**: the offsets are `P`'s. -/
theorem OutAt.words {m0 : MachineData} {d : Mem 64} (h : OutAt m0 (n m0) d) :
    WordsAt d (out m0) (natWords (P m0 (n m0)).1) := by
  rw [NativeRustcVm.wordsAt_iff]
  intro t ht
  have ht' : t < (P m0 (n m0)).1.size := by simpa [natWords] using ht
  have hmem : t ∈ (ord m0).toList.take (n m0) := by
    rw [take_length_ord]
    exact (ord_perm m0).mem_iff.mpr (List.mem_range.mpr (by rw [P_size] at ht'; exact ht'))
  have := h t hmem
  simp only [natWords, List.getElem_map, Array.getElem_toList]
  rw [show (P m0 (n m0)).1[t] = (P m0 (n m0)).1.getD t 0 by simp [Array.getD, ht']]
  exact this

/-! ## The frame -/

/-- **The body's frame**: `Frame` with the offsets as output, the 1328 bytes of stack. -/
abbrev Fr (m0 : MachineData) : MachineData → Prop :=
  Frame m0 1328 1328 slots (InRange (out m0) (8 * cap m0))

theorem stack_eq : stackOffsetsStack = 1328 := rfl

/-- **A block writing only into region 0** (`b`, `len`), inside the outputs or the stack and apart
from the slots, keeps a frame. -/
theorem Frame.of_region [Labels] {m0 st st' : MachineData} {F S : Nat} {sl : List (Nat × XReg)}
    {R : BitVec 64 → Prop} {b : BitVec 64} {len : Nat} {rs : List (BitVec 64 × Nat)}
    {S₀ S₁ : SState} (hb : Frame m0 F S sl R st)
    (hm₀ : Match (Env.ofMachine st ((b, len) :: rs)) S₀ st)
    (hm : Match (Env.ofMachine st ((b, len) :: rs)) S₁ st')
    (hwf : (Env.ofMachine st ((b, len) :: rs)).WF)
    (hk : keepsAll S₀ { S₁ with mem := [] } (calleeRegs.filter fun r ↦ !inSlots sl r) = true)
    (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ len)
    (hR : ∀ p, InRange b len p → R p ∨ InRange (stackBelow m0 S) S p)
    (hslot : ∀ q ∈ sl, ∀ i < 8,
      ¬InRange b len (fbase m0 F + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i)) :
    Frame m0 F S sl R st' := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, -⟩ := hk
  have hsame := same_of_region hm hwf (r := 0) rfl hw
  refine ⟨?_, fun q hq i hi ↦ ?_, fun r hr' hn ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ hm.kept hwf _ (hb.kept p hp)⟩
  · rw [Match.sp_eq hm₀ hm hsp]; exact hb.sp
  · simp only [List.length_map, List.length_range] at hi
    rw [hsame _ (hslot q hq i (by simpa using hi))]; exact hb.frame q hq i hi
  · obtain ⟨hs, he⟩ := hr r (List.mem_filter.mpr ⟨mem_calleeRegs hr', by
      rw [inSlots_false hn]; rfl⟩)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · rw [hsame p fun h ↦ hp (hR p h)]; exact hb.same p hp

theorem mem_nil_of_keepsAll {S₀ S₁ : SState} {rs : List XReg} (h : keepsAll S₀ S₁ rs = true) :
    S₁.mem = [] := by
  simp only [keepsAll, Bool.and_eq_true, List.isEmpty_iff] at h
  exact h.2

theorem with_mem_nil {S₁ : SState} (h : S₁.mem = []) : { S₁ with mem := [] } = S₁ := by
  cases S₁; cases h; rfl

theorem slots_bounds : ∀ q ∈ slots, 1264 ≤ q.1 ∧ q.1 + 8 ≤ 1328 := by decide

theorem fb_noWrap {m0 : MachineData} (hS : StackOk m0 1328) : NativeRustcVm.NoWrap (fb m0) 1328 :=
  (Arrays.frame_ok hS (Nat.le_refl _)).2.1

/-- **A block writing only into the order array** (`len` bytes from its byte `o`) keeps the
frame. -/
theorem Fr.of_ords [Labels] {m0 st st' : MachineData} (hS : StackOk m0 1328) {o len : Nat}
    (hol : o + len ≤ 1264) {S₀ S₁ : SState} (hb : Fr m0 st)
    (hm₀ : Match (Env.ofMachine st [(fb m0 + BitVec.ofNat 64 o, len)]) S₀ st)
    (hm : Match (Env.ofMachine st [(fb m0 + BitVec.ofNat 64 o, len)]) S₁ st')
    (hwf : (Env.ofMachine st [(fb m0 + BitVec.ofNat 64 o, len)]).WF)
    (hk : keepsAll S₀ { S₁ with mem := [] } keptRegs = true)
    (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ len) : Fr m0 st' := by
  have hnw := fb_noWrap hS
  refine Frame.of_region hb hm₀ hm hwf hk hw (fun p h ↦ Or.inr (frame_in_stack hS (Nat.le_refl _)
    (NativeRustcVm.InRange.of_sub h hnw (by omega)))) fun q hq i hi ↦ ?_
  obtain ⟨h1, h2⟩ := slots_bounds q hq
  rw [NativeRustcVm.addr_add]
  exact NativeRustcVm.not_inRange_sub hnw (by omega) (by omega) (by omega)

/-- A `Nat` value of a word. -/
theorem u64_eq {v : BitVec 64} {t : Nat} (h : v.toNat = t) : UInt64.ofBitVec v = t.toUInt64 := by
  have := v.isLt
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofBitVec, InsertionSort.toNat_toUInt64 (by omega), h]

theorem add_lit {x : BitVec 64} {a c : Nat} (h : x.toNat = a) (hc : a + c < 2 ^ 64) :
    (x + BitVec.ofNat 64 c).toNat = a + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h]; omega

theorem sub_lit {x : BitVec 64} {a c : Nat} (h : x.toNat = a) (hc : c ≤ a) :
    (x - BitVec.ofNat 64 c).toNat = a - c := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, h]
  rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
  omega

/-- A branch on a condition the executor evaluates to `decide P`. -/
theorem pc_of {pc a b : Int64} {c : Bool} {P : Prop} [Decidable P]
    (h : pc = if c = true then a else b) (hc : c = decide P) : (P → pc = a) ∧ (¬P → pc = b) := by
  subst hc
  exact ⟨fun hp ↦ by simpa [hp] using h, fun hp ↦ by simpa [hp] using h⟩

/-! ## The registers -/

/-- **The callee-saved registers the body reads**: `offsets`' length (X19), `offsets` (X20),
`n` (X21), `sizes` (X22), the order array (X24). -/
structure Regs (m0 st : MachineData) : Prop where
  x19 : st.regs.X19 = m0.regs.X3
  x20 : st.regs.X20 = m0.regs.X2
  x21 : st.regs.X21 = m0.regs.X1
  x22 : st.regs.X22 = m0.regs.X0
  x24 : st.regs.X24.toBitVec = fb m0

/-- The registers `Regs` reads. -/
def regsList : List XReg := [.X19, .X20, .X21, .X22, .X24]

theorem Regs.of {m0 st st' : MachineData} (h : Regs m0 st)
    (he : ∀ r ∈ regsList, st'.regs.getXReg r = st.regs.getXReg r) : Regs m0 st' where
  x19 := (he .X19 (by simp [regsList])).trans h.x19
  x20 := (he .X20 (by simp [regsList])).trans h.x20
  x21 := (he .X21 (by simp [regsList])).trans h.x21
  x22 := (he .X22 (by simp [regsList])).trans h.x22
  x24 := by rw [show st'.regs.X24 = st.regs.X24 from he .X24 (by simp [regsList])]; exact h.x24

theorem Regs.call {m0 st st' : MachineData} (h : Regs m0 st) (hs : Saved st st') : Regs m0 st' :=
  h.of fun r hr ↦ hs.1 r (by
    simp [regsList] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem fb_toNat {m0 : MachineData} (hS : StackOk m0 1328) :
    (fb m0).toNat + 1328 ≤ 2 ^ 64 := fb_noWrap hS

theorem fb_add {m0 : MachineData} (hS : StackOk m0 1328) {c : Nat} (hc : c < 1328) :
    (fb m0 + BitVec.ofNat 64 c).toNat = (fb m0).toNat + c := by
  have := fb_toNat hS
  exact Arrays.toNat_add_ofNat' (by omega)

theorem lit_toNat {c : Nat} (h : c < 2 ^ 64) : (BitVec.ofNat 64 c).toNat = c :=
  NativeRustcVm.toNat_ofNat_of_lt h

theorem beq_dec {x y : BitVec 64} {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b) :
    (x == y) = decide (a = b) := by
  rw [← hx, ← hy]
  by_cases h : x = y
  · subst h; simp
  · simp only [beq_eq_false_iff_ne.mpr h]
    exact (decide_eq_false fun h' ↦ h (BitVec.eq_of_toNat_eq h')).symm

theorem ult_dec {x y : BitVec 64} {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b) :
    x.ult y = decide (a < b) := by
  rw [← hx, ← hy]; rfl

theorem nbeq_dec {x y : BitVec 64} {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b) :
    (!(x == y)) = decide (a ≠ b) := by
  rw [beq_dec hx hy]
  by_cases h : a = b <;> simp [h]

/-- `lsl #3` of a shifted register operand. -/
theorem shl3 (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

variable [Host]

variable {k : Nat}

open NativeRustcVmArm.Vm.StackOffsets (code)

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.entryOffset) NativeRustcVmArm.Vm.StackOffsets.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b2Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b2Offset) NativeRustcVmArm.Vm.StackOffsets.label_2_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b6Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b6Offset) NativeRustcVmArm.Vm.StackOffsets.label_5_at
theorem lbl_6 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_6 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b7Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b7Offset) NativeRustcVmArm.Vm.StackOffsets.label_6_at
theorem lbl_7 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b8Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b8Offset) NativeRustcVmArm.Vm.StackOffsets.label_7_at
theorem lbl_9 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b10Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b10Offset) NativeRustcVmArm.Vm.StackOffsets.label_9_at
theorem lbl_10 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b11Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b11Offset) NativeRustcVmArm.Vm.StackOffsets.label_10_at
theorem lbl_11 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_11 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b12Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b12Offset) NativeRustcVmArm.Vm.StackOffsets.label_11_at
theorem lbl_12 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_12 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b13Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b13Offset) NativeRustcVmArm.Vm.StackOffsets.label_12_at
theorem lbl_13 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b15Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b15Offset) NativeRustcVmArm.Vm.StackOffsets.label_13_at
theorem lbl_14 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_14 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b16Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b16Offset) NativeRustcVmArm.Vm.StackOffsets.label_14_at
theorem lbl_15 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_15 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b17Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b17Offset) NativeRustcVmArm.Vm.StackOffsets.label_15_at
theorem lbl_19 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_19 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b21Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b21Offset) NativeRustcVmArm.Vm.StackOffsets.label_19_at
theorem lbl_20 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.StackOffsets.label_20 = Host.addrOf (k + NativeRustcVmArm.Vm.StackOffsets.b22Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.StackOffsets.b22Offset) NativeRustcVmArm.Vm.StackOffsets.label_20_at

/-- **A block of registers only** from a fresh state keeps the frame and memory. -/
theorem run_regs {m0 : MachineData} (hS : StackOk m0 1328) {ds : List Directive} {kk : Nat}
    {S1 : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds regsS = some (S1, x))
    (hkeep : keepsAll regsS S1 keptRegs = true) {st : MachineState} (hpc : st.pc = Host.addrOf kk)
    (hb : Fr m0 st.data) {R : MachineState → Prop}
    (cont : ∀ st', Match (Env.ofMachine st.data []) S1 st'.data →
      PcOk (Env.ofMachine st.data []) x (Host.addrOf (kk + ds.length)) st' →
      Fr m0 st'.data → st'.data.dmem = st.data.dmem → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at hk hx (Env.wf_nil _) hpc (match_nil _) fun st' hm hpc' ↦ by
    have hmem := mem_nil_of_keepsAll hkeep
    have hd : st'.data.dmem = st.data.dmem := hm.dmem_eq (Env.wf_nil _) hmem
    refine cont st' hm hpc' (Frame.of_block hb hS (by decide) (match_nil _) hm (Env.wf_nil _)
      (by rw [with_mem_nil hmem]; exact hkeep) (fun p _ ↦ by rw [hd])
      (fun q _ i _ ↦ by rw [hd])) hd

end

end NativeRustcVmArm.Layout.StackOffsets
