module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVm.Arrays.Mle

/-!
# `multilinear_eval_by`'s frame

Both instances of `multilinear_eval_by` keep, `1232` bytes below the entry's SP (`fbOf`), their
arguments (`fb + 8` to `fb + 48`), the pending entries (`fb + 48 + 16 k`), the `full` flags
(`fb + 1072 + k`, `k < 64`) and the saved registers (from `fb + 1136`). The pending entries the
frame holds (`pendOf`, the flags `0` or `1`: `FlagsOk`); a flag cleared (`pendOf_clear`), an entry
pushed (`pendOf_set`), bytes kept (`pendOf_congr`). The frame's bytes: kept by a call of
`EW::mul` (`frame_call`); a block writing only entries and flags keeps the body
(`body_of_frame_write`).
-/

namespace NativeRustcVmArm.Arrays.MleFrame

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (setP)

@[expose] public section

/-- The frame's base: `1232` bytes below the entry's SP. -/
def fbOf (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 1232

/-- Level `k`'s pending entry: `full[k]` (the byte at `fb + 1072 + k`) is `1`, the entry the one
at `fb + 48 + 16 k`. -/
def pendOf (d : DataMem) (fb : BitVec 64) (k : Nat) : Option EW :=
  if k < 64 ∧ d.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 1 then
    some (ewOf d (fb + BitVec.ofNat 64 (48 + 16 * k)))
  else none

/-- Every flag is `0` or `1`. -/
def FlagsOk (d : DataMem) (fb : BitVec 64) : Prop :=
  ∀ k < 64, d.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 0 ∨
    d.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 1

end

public section

/-! ## Addresses -/

theorem ofNat_add_inj {a : BitVec 64} {i j : Nat} (h : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 j)
    (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) : i = j := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  have := a.isLt
  omega

theorem fb_ne {a : BitVec 64} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    a + BitVec.ofNat 64 i ≠ a + BitVec.ofNat 64 j := fun e ↦ h (ofNat_add_inj e hi hj)

theorem fb_toNat {m0 : MachineData} (hS : StackOk m0 mleStack) :
    (fbOf m0).toNat = m0.regs.SP.toBitVec.toNat - 1232 ∧ 1824 ≤ m0.regs.SP.toBitVec.toNat :=
  ⟨(frame_ok hS (by decide)).2.2, hS.2.1⟩

theorem fb_add_toNat {m0 : MachineData} (hS : StackOk m0 mleStack) {o : Nat} (ho : o ≤ 1232) :
    (fbOf m0 + BitVec.ofNat 64 o).toNat = (fbOf m0).toNat + o := by
  obtain ⟨h1, h2⟩ := fb_toNat hS
  have := m0.regs.SP.toBitVec.isLt
  exact toNat_add_ofNat' (by omega)

/-- The `n` bytes at `o` of the frame, `o + n ≤ 1232`: mapped while the entry's bytes are. -/
theorem frame_piece {m0 st : MachineData} (hS : StackOk m0 mleStack) (hk : Kept m0.dmem st.dmem)
    {o n : Nat} (h : o + n ≤ 1232) :
    Mapped st.dmem (fbOf m0 + BitVec.ofNat 64 o) n ∧ NoWrap (fbOf m0 + BitVec.ofNat 64 o) n := by
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS (show 1232 ≤ mleStack by decide)
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [NativeRustcVm.addr_add]
    exact hk _ (hmap _ (by omega))
  · unfold NoWrap at hnw ⊢
    rw [fb_add_toNat hS (by omega)]
    unfold fbOf
    omega

/-- Two pieces of the frame, the first below the second. -/
theorem frame_apart {m0 : MachineData} (hS : StackOk m0 mleStack) {o n o' n' : Nat}
    (h : o + n ≤ o') (h' : o' + n' ≤ 1232) :
    Apart (fbOf m0 + BitVec.ofNat 64 o) n (fbOf m0 + BitVec.ofNat 64 o') n' := by
  unfold Apart
  rw [fb_add_toNat hS (by omega), fb_add_toNat hS (by omega)]
  omega

/-- A region apart from the stack is apart from a piece of the frame. -/
theorem frame_offStack {m0 : MachineData} (hS : StackOk m0 mleStack) {a : BitVec 64} {len : Nat}
    (h : OffStack m0 a len mleStack) {o n : Nat} (ho : o + n ≤ 1232) :
    Apart a len (fbOf m0 + BitVec.ofNat 64 o) n := by
  have hsb : (stackBelow m0 mleStack).toNat = m0.regs.SP.toBitVec.toNat - 1824 :=
    toNat_sub_ofNat hS.2.1
  obtain ⟨h1, h2⟩ := fb_toNat hS
  unfold OffStack Apart at h
  unfold Apart
  rw [fb_add_toNat hS (by omega)]
  rw [hsb] at h
  have : mleStack = 1824 := rfl
  omega

/-- A piece of the frame is in the stack. -/
theorem frame_inStack {m0 : MachineData} (hS : StackOk m0 mleStack) {j : Nat} (hj : j < 1232) :
    InRange (stackBelow m0 mleStack) mleStack (fbOf m0 + BitVec.ofNat 64 j) := by
  have hsb : (stackBelow m0 mleStack).toNat = m0.regs.SP.toBitVec.toNat - 1824 :=
    toNat_sub_ofNat hS.2.1
  rw [inRange_iff (stack_noWrap hS), hsb, fb_add_toNat hS (by omega), (fb_toNat hS).1]
  have := (fb_toNat hS).2
  have : mleStack = 1824 := rfl
  omega

/-- Apart, the other way round. -/
theorem apart_comm {a b : BitVec 64} {n m : Nat} (h : Apart a n b m) : Apart b m a n := by
  unfold Apart at *; omega

/-- An address between offsets `lo` and `hi` of the frame. -/
theorem frame_addr {m0 : MachineData} (hS : StackOk m0 mleStack) {p : BitVec 64} {lo hi : Nat}
    (h1 : (fbOf m0).toNat + lo ≤ p.toNat) (h2 : p.toNat < (fbOf m0).toNat + hi) (hhi : hi ≤ 1232) :
    ∃ j, lo ≤ j ∧ j < hi ∧ p = fbOf m0 + BitVec.ofNat 64 j :=
  ⟨p.toNat - (fbOf m0).toNat, by omega, by omega, by
    apply BitVec.eq_of_toNat_eq; rw [fb_add_toNat hS (by omega)]; omega⟩

/-- A piece of a region apart from the stack is apart from a piece of the frame. -/
theorem piece_offStack {m0 : MachineData} (hS : StackOk m0 mleStack) {a : BitVec 64} {len : Nat}
    (h : OffStack m0 a len mleStack) (hnw : NoWrap a len) {j w o n : Nat} (hj : j + w ≤ len)
    (hw : 0 < w) (ho : o + n ≤ 1232) :
    Apart (a + BitVec.ofNat 64 j) w (fbOf m0 + BitVec.ofNat 64 o) n := by
  have h' := frame_offStack hS h ho
  unfold NoWrap at hnw
  unfold Apart at h' ⊢
  rw [toNat_add_ofNat' (by omega)]
  omega

/-- Two regions, mapped, not wrapping, apart: a well-formed environment. -/
theorem wf2 {st : MachineData} {a b : BitVec 64} {n n' : Nat} (ha : Mapped st.dmem a n ∧ NoWrap a n)
    (hb : Mapped st.dmem b n' ∧ NoWrap b n') (hab : Apart a n b n')
    (vars : Nat → BitVec 64 := fun _ ↦ 0) : (Env.ofMachine st [(a, n), (b, n')] vars).WF :=
  Env.wf_of ⟨ha, hb, trivial⟩ (List.pairwise_cons.mpr ⟨by simpa using hab,
    List.pairwise_singleton _ _⟩)

/-- Three regions, mapped, not wrapping, pairwise apart: a well-formed environment. -/
theorem wf3 {st : MachineData} {a b c : BitVec 64} {n n' n'' : Nat}
    (ha : Mapped st.dmem a n ∧ NoWrap a n) (hb : Mapped st.dmem b n' ∧ NoWrap b n')
    (hc : Mapped st.dmem c n'' ∧ NoWrap c n'') (hab : Apart a n b n') (hac : Apart a n c n'')
    (hbc : Apart b n' c n'') (vars : Nat → BitVec 64 := fun _ ↦ 0) :
    (Env.ofMachine st [(a, n), (b, n'), (c, n'')] vars).WF :=
  Env.wf_of ⟨ha, hb, hc, trivial⟩ (List.pairwise_cons.mpr ⟨by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hab
    · exact hac, List.pairwise_cons.mpr ⟨by simpa using hbc, List.pairwise_singleton _ _⟩⟩)

/-! ## Bodies -/

/-- **A call of `EW::mul`** keeps the frame's bytes. -/
theorem frame_call {m0 st st' : MachineData} {slots : List (Nat × XReg)}
    (hb : Body m0 1232 mleStack slots 0 0 st) (hpost : EWMulPost st st') {j : Nat} (hj : j < 1232) :
    st'.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) = st.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := by
  obtain ⟨-, -, hsame, -⟩ := hpost
  refine hsame _ ?_
  unfold stackBelow
  rw [hb.sp]
  have := m0.regs.SP.toNat_lt
  exact not_inRange_below (by unfold ewMulStack; omega)

/-- **A block writing only pending entries and flags** keeps a body. -/
theorem body_of_frame_write [Labels] {m0 st st' : MachineData} {slots : List (Nat × XReg)}
    {env : Env} {S₀ S₁ : SState} (hb : Body m0 1232 mleStack slots 0 0 st)
    (hS : StackOk m0 mleStack) (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF)
    (hd : env.mem0 = st.dmem)
    (hk : keepsAll S₀ { S₁ with mem := [] } (calleeRegs.filter fun r ↦ !inSlots slots r) = true)
    (hw : ∀ p, Written env S₁ p → ∃ j, 48 ≤ j ∧ j < 1136 ∧ p = fbOf m0 + BitVec.ofNat 64 j)
    (hslots : ∀ p ∈ slots, p.1 + 8 ≤ 48 ∨ (1136 ≤ p.1 ∧ p.1 + 8 ≤ 1232)) :
    Body m0 1232 mleStack slots 0 0 st' := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, -⟩ := hk
  have hsame : ∀ p, ¬Written env S₁ p → st'.dmem.get? p = st.dmem.get? p := fun p hp ↦ by
    rw [hm.get?_mem0 hwf hp, hd]
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r hr' hn ↦ ?_, fun p hp ↦ ?_, ?_⟩
  · rw [Match.sp_eq hm₀ hm hsp]; exact hb.sp
  · simp only [List.length_map, List.length_range] at hi
    rw [NativeRustcVm.addr_add, hsame _ fun hW ↦ ?_]
    · rw [← NativeRustcVm.addr_add]; exact hb.frame p hp i (by simpa using hi)
    · obtain ⟨j, hj1, hj2, he⟩ := hw _ hW
      have := ofNat_add_inj he (by rcases hslots p hp with h | h <;> omega) (by omega)
      rcases hslots p hp with h | h <;> omega
  · obtain ⟨hs, he⟩ := hr r (List.mem_filter.mpr ⟨mem_calleeRegs hr', by
      rw [inSlots_false hn]; rfl⟩)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · by_cases hW : Written env S₁ p
    · obtain ⟨j, -, hj2, rfl⟩ := hw _ hW
      exact absurd (Or.inr (frame_inStack hS (by omega))) hp
    · rw [hsame p hW]; exact hb.same p hp
  · intro p hp
    have := hm.kept hwf p
    rw [hd] at this
    exact this (hb.kept p hp)

/-! ## Pending entries -/

theorem pendOf_congr {d d' : DataMem} {fb : BitVec 64}
    (h : ∀ j, 48 ≤ j → j < 1136 → d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    pendOf d' fb = pendOf d fb := by
  funext k
  unfold pendOf
  by_cases hk : k < 64
  · rw [h (1072 + k) (by omega) (by omega), NativeRustcVm.ewOf_congr (d := d) fun i hi ↦ by
      rw [NativeRustcVm.addr_add]; exact h _ (by omega) (by omega)]
  · simp [hk]

theorem flagsOk_congr {d d' : DataMem} {fb : BitVec 64} (hf : FlagsOk d fb)
    (h : ∀ j, 48 ≤ j → j < 1136 → d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    FlagsOk d' fb := fun k hk ↦ by
  rw [h (1072 + k) (by omega) (by omega)]; exact hf k hk

/-- Every flag `0`: nothing pending. -/
theorem pendOf_zero {d : DataMem} {fb : BitVec 64}
    (h : ∀ k < 64, d.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 0) :
    pendOf d fb = fun _ ↦ none := by
  funext k
  unfold pendOf
  by_cases hk : k < 64
  · rw [h k hk]; simp
  · simp [hk]

/-- **A flag cleared**: level `k`'s entry gone. -/
theorem pendOf_clear {d d' : DataMem} {fb : BitVec 64} {k : Nat} (hk : k < 64)
    (hf : d'.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 0)
    (h : ∀ j, 48 ≤ j → j < 1136 → j ≠ 1072 + k →
      d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    pendOf d' fb = setP (pendOf d fb) k none := by
  funext j
  unfold setP
  by_cases hj : j = k
  · subst hj
    rw [ite_eq_left rfl]
    unfold pendOf
    rw [hf]
    simp
  · rw [ite_eq_right hj]
    unfold pendOf
    by_cases hj' : j < 64
    · rw [h (1072 + j) (by omega) (by omega) (by omega), NativeRustcVm.ewOf_congr (d := d) fun i hi ↦ by
        rw [NativeRustcVm.addr_add]; exact h _ (by omega) (by omega) (by omega)]
    · simp [hj']

theorem flagsOk_clear {d d' : DataMem} {fb : BitVec 64} {k : Nat} (hfl : FlagsOk d fb)
    (hf : d'.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 0)
    (h : ∀ j, 48 ≤ j → j < 1136 → j ≠ 1072 + k →
      d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    FlagsOk d' fb := fun j hj ↦ by
  by_cases hjk : j = k
  · subst hjk; exact Or.inl hf
  · rw [h (1072 + j) (by omega) (by omega) (by omega)]; exact hfl j hj

/-- **An entry pushed** at level `k`. -/
theorem pendOf_set {d d' : DataMem} {fb : BitVec 64} {k : Nat} {v : EW} (hk : k < 64)
    (hf : d'.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 1)
    (hv : ewOf d' (fb + BitVec.ofNat 64 (48 + 16 * k)) = v)
    (h : ∀ j, 48 ≤ j → j < 1136 → j ≠ 1072 + k → (j < 48 + 16 * k ∨ 64 + 16 * k ≤ j) →
      d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    pendOf d' fb = setP (pendOf d fb) k (some v) := by
  funext j
  unfold setP
  by_cases hj : j = k
  · subst hj
    rw [ite_eq_left rfl]
    unfold pendOf
    rw [hf, hv]
    simp [hk]
  · rw [ite_eq_right hj]
    unfold pendOf
    by_cases hj' : j < 64
    · rw [h (1072 + j) (by omega) (by omega) (by omega) (by omega),
        NativeRustcVm.ewOf_congr (d := d) fun i hi ↦ by
          rw [NativeRustcVm.addr_add]
          exact h _ (by omega) (by omega) (by omega) (by
            rcases Nat.lt_or_gt_of_ne hj with hl | hl <;> omega)]
    · simp [hj']

theorem flagsOk_set {d d' : DataMem} {fb : BitVec 64} {k : Nat} (hfl : FlagsOk d fb)
    (hf : d'.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 1) (hk : k < 64)
    (h : ∀ j, 48 ≤ j → j < 1136 → j ≠ 1072 + k → (j < 48 + 16 * k ∨ 64 + 16 * k ≤ j) →
      d'.get? (fb + BitVec.ofNat 64 j) = d.get? (fb + BitVec.ofNat 64 j)) :
    FlagsOk d' fb := fun j hj ↦ by
  by_cases hjk : j = k
  · subst hjk; exact Or.inr hf
  · rw [h (1072 + j) (by omega) (by omega) (by omega) (by omega)]; exact hfl j hj

/-- A flag's byte, `0` (nothing pending) or `1` (the entry pending). -/
theorem flag_cases {d : DataMem} {fb : BitVec 64} {k : Nat} (hk : k < 64) (hfl : FlagsOk d fb) :
    (d.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 0 ∧ pendOf d fb k = none) ∨
      (d.get? (fb + BitVec.ofNat 64 (1072 + k)) = some 1 ∧
        pendOf d fb k = some (ewOf d (fb + BitVec.ofNat 64 (48 + 16 * k)))) := by
  rcases hfl k hk with h | h
  · refine .inl ⟨h, ?_⟩
    unfold pendOf
    rw [h, ite_eq_right (fun hc ↦ absurd hc.2 (by decide))]
  · refine .inr ⟨h, ?_⟩
    unfold pendOf
    rw [h, ite_eq_left ⟨hk, rfl⟩]

/-- A byte at an address, as the executor loads it. -/
theorem load_byte [Labels] {env : Env} {r : Nat} {b : UInt8}
    (h : env.mem0.get? (env.base r) = some b) :
    env.load r 0 1 = BitVec.ofInt 64 (Int.ofBytes [b]) :=
  Env.load_of_bytesAt rfl fun i hi ↦ by
    obtain rfl : i = 0 := by simp at hi; omega
    rw [add_ofNat_zero, add_ofNat_zero]
    exact h

/-- A word of an argument slice, read in a body. -/
theorem word_of_apart {m0 st : MachineData} {S : Nat} {a : BitVec 64} {n i : Nat}
    (hc : Changes m0 st S 0 0) (hS : StackOk m0 S) (hna : NoWrap a (8 * n))
    (hst : OffStack m0 a (8 * n) S) (hi : i < n) :
    wordOf st.dmem (a + BitVec.ofNat 64 (8 * i)) =
      (NativeRustcVm.wordsOf m0.dmem a n)[i]'(by simp; exact hi) := by
  rw [NativeRustcVm.getElem_wordsOf]
  exact NativeRustcVm.wordOf_congr fun j hj ↦ by
    rw [NativeRustcVm.addr_add]
    exact same_of_apart hc hS hna hst (apart_zero _ _) noWrap_zero _ (by omega)

/-- The `8` bytes of word `i < n` of a readable slice are mapped in a state that kept them. -/
theorem word_mapped {m0 st : MachineData} {a : BitVec 64} {n i : Nat} (h : Readable m0 a (8 * n))
    (hk : Kept m0.dmem st.dmem) (hi : i < n) :
    Mapped st.dmem (a + BitVec.ofNat 64 (8 * i)) 8 ∧ NoWrap (a + BitVec.ofNat 64 (8 * i)) 8 := by
  obtain ⟨hm, hn⟩ := h
  unfold NoWrap at *
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [NativeRustcVm.addr_add]; exact hk _ (hm _ (by omega))
  · rw [toNat_add_ofNat' (by omega)]; omega

/-- An index scaled by `8` (`[xn, xm, lsl #3]`). -/
theorem memExtend3 (x : BitVec 64) :
    BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E3⟩) = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.apply_mem_extend, BitVec.unsigned]
  rw [Int.shiftLeft_eq, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  push_cast
  omega

end

end NativeRustcVmArm.Arrays.MleFrame
