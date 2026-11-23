module

public import NativeRustcVmX64.Whir.InducedWeight.Exec
public import NativeRustcVmX64.Whir.SubspaceAtTable.Leaf
public import NativeRustcVm.Whir.MathInduced
public import NativeRustcVm.Whir.MathSubspace

/-!
# `induced_weight`'s states (x86-64)

The frame's base `fbOf m0` (the 1168 bytes below the entry's RSP). From the entry `m0` (`μ ≤ 30`):
the spills (`Spills`: the output pointer at 24, the table's pointer and count at 32, 40, the queries'
count at 48, the queries' and the weights' pointers at 56, 64, the table's copy, a
`Buf<(u64, u64), 31>` at 616), all in the frame's bytes 24 to 72 and 616 to 1120; the queries' loop
words (`Loop`: the query's index at 72, the sum at 80);
- `OInv j` at the queries' loop head (`b7`): `j` queries summed (`totOf`);
- `IInv j i` at the product's loop head (`b10`): `i` factors of query `j` (`prodOf`), its `What`s at
  104, `8 · len` at 16;
- `Acc j` at the sum (`b6`): query `j`'s product done;
- `Done` at the store (`b17`): the sum over every query.

Frame bytes kept between two memories (`FKeep`) by a block (`fkeep_block`) or a callee
(`fkeep_call`, `fkeep_stack`, `fkeep_range`).
-/

namespace NativeRustcVmX64.Whir.InducedWeight

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (Region InAny WordAt WordsAt wordOf ewOf EWAt BufWordsAt)
open NativeRustcVmX64.Whir.Leaf

@[expose] public section

/-- The frame's base. -/
def fbOf (m0 : MachineData) : BitVec 64 := stackBelow m0 1168
/-- `μ`. -/
def muOf (m0 : MachineData) : Nat := (reg m0 .rsi).toNat
/-- The table. -/
def tbOf (m0 : MachineData) : Array (UInt64 × UInt64) := subspaceTable (muOf m0)
/-- The queries. -/
def qsOf (m0 : MachineData) : Array UInt64 := wordSlice m0 (reg m0 .rdx) (reg m0 .rcx).toNat
/-- The weights. -/
def wsOf (m0 : MachineData) : Array EW := slice m0 (reg m0 .r8) (reg m0 .r9)
/-- The point. -/
def ptOf (m0 : MachineData) : Array EW := slice m0 (stackArg m0 0) (stackArg m0 1)
/-- The queries' count the loop runs. -/
def cntOf (m0 : MachineData) : Nat := min (reg m0 .r9).toNat (reg m0 .rcx).toNat
/-- Query `j`'s `What`s. -/
def whatOf (m0 : MachineData) (j : Nat) : Array UInt64 := subspaceAt (muOf m0) ((qsOf m0).getD j 0)
/-- Query `j`'s factors' count. -/
def lenOf (m0 : MachineData) (j : Nat) : Nat := min (ptOf m0).size (whatOf m0 j).size
/-- The sum over the first `j` queries. -/
def totOf (m0 : MachineData) (j : Nat) : EW := indTot (muOf m0) (qsOf m0) (wsOf m0) (ptOf m0) j
/-- Query `j`'s product after `i` factors. -/
def prodOf (m0 : MachineData) (j i : Nat) : EW :=
  indProd (ptOf m0) (whatOf m0 j) ((wsOf m0).getD j 0) i

/-- The body's frame: no output written. -/
abbrev Fr (m0 st : MachineData) : Prop := Frame m0 1168 inducedWeightStack slots [] st

/-- The spills and the table's copy. -/
structure Spills (m0 st : MachineData) : Prop where
  out : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofBitVec (reg m0 .rdi))
  ptrs : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 32)
    [.ofBitVec (fbOf m0 + BitVec.ofNat 64 624), (tbOf m0).size.toUInt64, (cntOf m0).toUInt64,
      .ofBitVec (reg m0 .rdx), .ofBitVec (reg m0 .r8)]
  table : BufPairsAt st.dmem (fbOf m0 + BitVec.ofNat 64 616) rootCap (tbOf m0).toList

/-- The queries' loop's words after `j` queries: `j` at 72, the sum at 80. -/
structure Loop (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  idx : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 72) j.toUInt64
  tot : EWAt st.dmem (fbOf m0 + BitVec.ofNat 64 80) (totOf m0 j)

/-- The queries' loop head after `j` queries. -/
structure OInv (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  hj : j < cntOf m0
  mu : muOf m0 ≤ stackCap
  rsi : reg st .rsi = BitVec.ofNat 64 j
  rcx : reg st .rcx = (totOf m0 j).c0.toBitVec
  rax : reg st .rax = (totOf m0 j).c1.toBitVec
  rdx : reg st .rdx = BitVec.ofNat 64 (tbOf m0).size
  r14 : reg st .r14 = stackArg m0 0

/-- The product's loop head: `i` factors of query `j`. -/
structure IInv (m0 : MachineData) (j i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  lp : Loop m0 j st
  hj : j < cntOf m0
  mu : muOf m0 ≤ stackCap
  what : BufWordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 104) rootCap (whatOf m0 j).toList
  len : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (8 * lenOf m0 j).toUInt64
  hi : i < lenOf m0 j
  rbx : reg st .rbx = (prodOf m0 j i).c0.toBitVec
  r12 : reg st .r12 = (prodOf m0 j i).c1.toBitVec
  r14 : reg st .r14 = stackArg m0 0
  r15 : reg st .r15 = BitVec.ofNat 64 (8 * i)

/-- Query `j`'s product done. -/
structure Acc (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  lp : Loop m0 j st
  hj : j < cntOf m0
  mu : muOf m0 ≤ stackCap
  rbx : reg st .rbx = (prodOf m0 j (lenOf m0 j)).c0.toBitVec
  r12 : reg st .r12 = (prodOf m0 j (lenOf m0 j)).c1.toBitVec
  r14 : reg st .r14 = stackArg m0 0

/-- Every query summed. -/
structure Done (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofBitVec (reg m0 .rdi))
  mu : muOf m0 ≤ stackCap
  rcx : reg st .rcx = (totOf m0 (cntOf m0)).c0.toBitVec
  rax : reg st .rax = (totOf m0 (cntOf m0)).c1.toBitVec

/-- Frame bytes `lo` to `hi` the same in `d` and `d'`. -/
def FKeep (m0 : MachineData) (d d' : DataMem) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi →
    d'.get? (fbOf m0 + BitVec.ofNat 64 i) = d.get? (fbOf m0 + BitVec.ofNat 64 i)

end

public section

theorem stack_eq : inducedWeightStack = 2112 := by decide

theorem stack_le : 1168 ≤ inducedWeightStack ∧ 1168 + subspaceTableStack ≤ inducedWeightStack ∧
    1168 + subspaceAtTableStack ≤ inducedWeightStack ∧ 1168 + kmulStack ≤ inducedWeightStack ∧
    1168 + ewMulStack ≤ inducedWeightStack ∧ 1168 + 0 ≤ inducedWeightStack := by decide

theorem whatOf_size (m0 : MachineData) (j : Nat) : (whatOf m0 j).size = (tbOf m0).size :=
  subspaceAtTable_size _ _

theorem qsOf_size (m0 : MachineData) : (qsOf m0).size = (reg m0 .rcx).toNat := by
  simp [qsOf, wordSlice]

theorem wsOf_size (m0 : MachineData) : (wsOf m0).size = (reg m0 .r9).toNat := by
  simp [wsOf, slice]

theorem ptOf_size (m0 : MachineData) : (ptOf m0).size = (stackArg m0 1).toNat := by
  simp [ptOf, slice]

theorem getD_eq {α : Type} (a : Array α) {i : Nat} (v : α) (h : i < a.size) :
    a.getD i v = a[i] := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- The result: the sum over every query. -/
theorem totOf_cnt (m0 : MachineData) :
    totOf m0 (cntOf m0) = inducedWeight (muOf m0) (qsOf m0) (wsOf m0) (ptOf m0) := by
  rw [inducedWeight_eq, wsOf_size, qsOf_size]
  rfl

theorem totOf_zero (m0 : MachineData) : totOf m0 0 = 0 := indTot_zero _ _ _ _

theorem totOf_succ (m0 : MachineData) {j : Nat} (hj : j < cntOf m0) :
    totOf m0 (j + 1) = totOf m0 j + prodOf m0 j (lenOf m0 j) := by
  have hjws : j < (wsOf m0).size := by rw [wsOf_size]; unfold cntOf at hj; omega
  have hjqs : j < (qsOf m0).size := by rw [qsOf_size]; unfold cntOf at hj; omega
  unfold totOf prodOf lenOf whatOf
  rw [indTot_succ _ _ _ _ hjws hjqs, getD_eq _ _ hjws, getD_eq _ _ hjqs]

theorem prodOf_zero (m0 : MachineData) (j : Nat) : prodOf m0 j 0 = (wsOf m0).getD j 0 :=
  indProd_zero _ _ _

theorem prodOf_succ (m0 : MachineData) {j i : Nat} (hi : i < lenOf m0 j) :
    prodOf m0 j (i + 1) = EW.mul (prodOf m0 j i)
      (indFactor ((ptOf m0)[i]'(by unfold lenOf at hi; omega))
        ((whatOf m0 j)[i]'(by unfold lenOf at hi; omega))) :=
  indProd_succ _ _ _ (by unfold lenOf at hi; omega) (by unfold lenOf at hi; omega)

/-! ## Frame bytes kept -/

section
variable {m0 : MachineData} {d d' d'' : DataMem} {lo hi : Nat}

theorem FKeep.trans (h1 : FKeep m0 d d' lo hi) (h2 : FKeep m0 d' d'' lo hi) :
    FKeep m0 d d'' lo hi := fun i a b ↦ (h2 i a b).trans (h1 i a b)

theorem FKeep.mono (h : FKeep m0 d d' lo hi) {lo' hi' : Nat} (h1 : lo ≤ lo') (h2 : hi' ≤ hi) :
    FKeep m0 d d' lo' hi' := fun i a b ↦ h i (by omega) (by omega)

theorem FKeep.of_eq (h : d' = d) : FKeep m0 d d' lo hi := fun _ _ _ ↦ by rw [h]

/-- Bytes of the frame kept. -/
theorem bytes_keep {o : Nat} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt d (fbOf m0 + BitVec.ofNat 64 o) bs) (hk : FKeep m0 d d' lo hi)
    (ho : lo ≤ o) (hl : o + bs.length ≤ hi) :
    NativeRustcVm.BytesAt d' (fbOf m0 + BitVec.ofNat 64 o) bs := fun i hi' ↦ by
  rw [addr_add, hk _ (by omega) (by omega), ← addr_add]
  exact h i hi'

theorem word_keep {o : Nat} {w : UInt64} (h : WordAt d (fbOf m0 + BitVec.ofNat 64 o) w)
    (hk : FKeep m0 d d' lo hi) (ho : lo ≤ o) (hl : o + 8 ≤ hi) :
    WordAt d' (fbOf m0 + BitVec.ofNat 64 o) w :=
  bytes_keep h hk ho (by rw [NativeRustcVm.length_wordBytes]; exact hl)

theorem ew_keep {o : Nat} {x : EW} (h : EWAt d (fbOf m0 + BitVec.ofNat 64 o) x)
    (hk : FKeep m0 d d' lo hi) (ho : lo ≤ o) (hl : o + 16 ≤ hi) :
    EWAt d' (fbOf m0 + BitVec.ofNat 64 o) x :=
  bytes_keep h hk ho (by rw [NativeRustcVm.length_ewBytes]; exact hl)

/-- A `Buf<u64, 31>` of the frame kept. -/
theorem bufWords_keep {o : Nat} {xs : List UInt64}
    (h : BufWordsAt d (fbOf m0 + BitVec.ofNat 64 o) 31 xs) (hk : FKeep m0 d d' lo hi)
    (ho : lo ≤ o) (hl : o + 256 ≤ hi) : BufWordsAt d' (fbOf m0 + BitVec.ofNat 64 o) 31 xs := by
  obtain ⟨hl', h1, h2⟩ := h
  refine ⟨hl', bytes_keep h1 hk ho (by rw [NativeRustcVm.length_wordBytes]; omega), ?_⟩
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add] at h2 ⊢
  exact bytes_keep h2 hk (by omega) (by rw [NativeRustcVm.length_wordsBytes]; omega)

/-- The length of a table's bytes. -/
theorem pairs_len (ps : List (UInt64 × UInt64)) :
    ((pairWords ps).flatMap NativeRustcVm.wordBytes).length = 16 * ps.length := by
  rw [NativeRustcVm.length_wordsBytes]
  simp [pairWords]
  omega

/-- A `Buf<(u64, u64), 31>` of the frame kept. -/
theorem bufPairs_keep {o : Nat} {ps : List (UInt64 × UInt64)}
    (h : BufPairsAt d (fbOf m0 + BitVec.ofNat 64 o) 31 ps) (hk : FKeep m0 d d' lo hi)
    (ho : lo ≤ o) (hl : o + 504 ≤ hi) : BufPairsAt d' (fbOf m0 + BitVec.ofNat 64 o) 31 ps := by
  obtain ⟨hl', h1, h2⟩ := h
  refine ⟨hl', bytes_keep h1 hk ho (by rw [NativeRustcVm.length_wordBytes]; omega), ?_⟩
  unfold PairsAt NativeRustcVm.Transcript.off NativeRustcVm.WordsAt at h2 ⊢
  rw [addr_add] at h2 ⊢
  exact bytes_keep h2 hk (by omega) (by rw [pairs_len]; omega)

theorem words_keep {o : Nat} {ws : List UInt64}
    (h : WordsAt d (fbOf m0 + BitVec.ofNat 64 o) ws) (hk : FKeep m0 d d' lo hi)
    (ho : lo ≤ o) (hl : o + 8 * ws.length ≤ hi) : WordsAt d' (fbOf m0 + BitVec.ofNat 64 o) ws :=
  bytes_keep (bs := ws.flatMap NativeRustcVm.wordBytes) h hk ho
    (by rw [NativeRustcVm.length_wordsBytes]; exact hl)

end

theorem Spills.mono {m0 st st' : MachineData} (h : Spills m0 st)
    (h1 : FKeep m0 st.dmem st'.dmem 24 72) (h2 : FKeep m0 st.dmem st'.dmem 616 1120) :
    Spills m0 st' :=
  ⟨word_keep h.out h1 (by omega) (by omega), words_keep h.ptrs h1 (by omega) (by simp),
    bufPairs_keep h.table h2 (by omega) (by omega)⟩

theorem Spills.of_dmem {m0 st st' : MachineData} (h : Spills m0 st) (hd : st'.dmem = st.dmem) :
    Spills m0 st' := h.mono (.of_eq hd) (.of_eq hd)

theorem Loop.mono {m0 st st' : MachineData} {j : Nat} (h : Loop m0 j st)
    (hk : FKeep m0 st.dmem st'.dmem 72 96) : Loop m0 j st' :=
  ⟨word_keep h.idx hk (by omega) (by omega), ew_keep h.tot hk (by omega) (by omega)⟩

theorem Loop.of_dmem {m0 st st' : MachineData} {j : Nat} (h : Loop m0 j st)
    (hd : st'.dmem = st.dmem) : Loop m0 j st' := h.mono (.of_eq hd)

/-- A block's write list. -/
theorem hall_of {mem : List Write} {l : List (Nat × Nat × Nat)} (h : mem.map wsig = l) {lo hi : Nat}
    (hl : ∀ x ∈ l, x.1 = 0 ∧ (x.2.1 + x.2.2 ≤ lo ∨ hi ≤ x.2.1)) :
    ∀ w ∈ mem, w.r = 0 ∧ (w.off + w.n ≤ lo ∨ hi ≤ w.off) := fun w hw ↦
  hl (wsig w) (h ▸ List.mem_map_of_mem hw)

/-- A block's writes, below `L`. -/
theorem hw_of {mem : List Write} {l : List (Nat × Nat × Nat)} (h : mem.map wsig = l) {L : Nat}
    (hl : ∀ x ∈ l, x.1 = 0 ∧ x.2.1 + x.2.2 ≤ L) : ∀ w ∈ mem, w.r = 0 ∧ w.off + w.n ≤ L :=
  fun w hw ↦ hl (wsig w) (h ▸ List.mem_map_of_mem hw)

/-- **Frame bytes a block kept**: no write of it in region 0 (the frame) between `lo` and
`hi`. -/
theorem fkeep_block [Labels] {m0 : MachineData} {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) (hwf : env.WF) {sz : Nat} (hb : env.regions[0]? = some (fbOf m0, sz))
    {lo hi : Nat} (hhi : hi ≤ sz)
    (hall : ∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ lo ∨ hi ≤ w.off)) :
    FKeep m0 env.mem0 m.dmem lo hi := by
  intro i h1 h2
  have h := Match.keep hm hwf hb (o := lo) (len := hi - lo) (by omega)
    (fun w hw ↦ by have := hall w hw; omega) (i - lo) (by omega)
  rwa [show lo + (i - lo) = i by omega] at h

section
variable {m0 d1 d2 : MachineData} {N : Nat}

/-- **Frame bytes a callee kept**, changing its stack below the frame. -/
theorem fkeep_stack (hS : StackOk m0 inducedWeightStack) (hsp : rspOf d1 = fbOf m0)
    (hle : 1168 + N ≤ inducedWeightStack)
    (hs : SameOutside d1.dmem d2.dmem (InRange (stackBelow d1 N) N)) {lo hi : Nat}
    (hhi : hi ≤ 1176) : FKeep m0 d1.dmem d2.dmem lo hi := fun i _ h2 ↦
  hs _ (not_inRange_callee hS hsp hle (by omega))

/-- **Frame bytes a callee kept**, changing its stack and the frame's bytes `c` to `c + n`. -/
theorem fkeep_call (hS : StackOk m0 inducedWeightStack) (hsp : rspOf d1 = fbOf m0)
    (hle : 1168 + N ≤ inducedWeightStack) {c n : Nat}
    (hs : SameOutside d1.dmem d2.dmem (fun p ↦
      InAny [⟨fbOf m0 + BitVec.ofNat 64 c, n⟩] p ∨ InRange (stackBelow d1 N) N p))
    (hc : c + n ≤ 1176) (hc0 : c < 1176) {lo hi : Nat} (hhi : hi ≤ 1176)
    (hap : hi ≤ c ∨ c + n ≤ lo) : FKeep m0 d1.dmem d2.dmem lo hi := fun i h1 h2 ↦
  hs _ fun h ↦ h.elim (fun ⟨r, hr, hp⟩ ↦ by
      rw [List.mem_singleton] at hr
      subst hr
      have := (inRange_fb_iff hS stack_le.1 (c := c) (n := n) (j := i) hc0 hc (by omega)).mp hp
      omega)
    (not_inRange_callee hS hsp hle (by omega))

/-- **Frame bytes `memcpy` kept**: those outside the copy, in the frame's bytes `c` to `c + n`. -/
theorem fkeep_range (hS : StackOk m0 inducedWeightStack) {c n : Nat}
    (hs : SameOutside d1.dmem d2.dmem (InRange (fbOf m0 + BitVec.ofNat 64 c) n))
    (hc : c + n ≤ 1176) (hc0 : c < 1176) {lo hi : Nat} (hhi : hi ≤ 1176)
    (hap : hi ≤ c ∨ c + n ≤ lo) : FKeep m0 d1.dmem d2.dmem lo hi := fun i h1 h2 ↦
  hs _ fun hp ↦ by
    have := (inRange_fb_iff hS stack_le.1 (c := c) (n := n) (j := i) hc0 hc (by omega)).mp hp
    omega

end

/-! ## Values -/

/-- **A tag word's low half loaded**: a tag `0` or `1`. -/
theorem load4_of_tag [Labels] {env : Env} {r o : Nat} {w : UInt64} (hw : w = 0 ∨ w = 1)
    (h : WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) w) :
    env.load r o 4 = BitVec.ofNat 64 w.toNat := by
  have h4 : NativeRustcVm.BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o)
      ((NativeRustcVm.wordBytes w).take 4) := fun i hi ↦ by
    rw [List.length_take, NativeRustcVm.length_wordBytes] at hi
    have := h i (by rw [NativeRustcVm.length_wordBytes]; omega)
    rw [List.getElem_take]
    exact this
  rw [Env.load_of_bytesAt (n := 4) (by rw [List.length_take, NativeRustcVm.length_wordBytes]; rfl)
    h4]
  rcases hw with rfl | rfl <;> decide

/-- A word loaded. -/
theorem load_word {env : Env} {r o : Nat} {w : UInt64}
    (h : WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) w) : env.load r o 8 = w.toBitVec := by
  rw [Arrays.load8_eq, NativeRustcVm.wordOf_of_wordAt h]

/-- Word `i` of words. -/
theorem word_at {d : DataMem} {a : BitVec 64} {o : Nat} {xs : List UInt64}
    (h : WordsAt d (a + BitVec.ofNat 64 o) xs) (i : Nat) (hi : i < xs.length) :
    WordAt d (a + BitVec.ofNat 64 (o + 8 * i)) xs[i] := by
  have := NativeRustcVm.WordsAt.getElem h hi
  rwa [addr_add] at this

/-- The unsigned minimum of an `ite`. -/
theorem ite_min (a b : BitVec 64) :
    (if a.ult b = true then a else b).toNat = min a.toNat b.toNat := by
  rw [bv_ult_toNat]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, ↓reduceIte]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

theorem shl4_eq (x : BitVec 64) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem shl3_eq (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem mul_lit (a c : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 c = BitVec.ofNat 64 (a * c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod]

end

end NativeRustcVmX64.Whir.InducedWeight
