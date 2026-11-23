module

public import NativeRustcVmArm.Whir.GlueLevel.Mem
public import NativeRustcVmArm.Whir.MathFrame
public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVmArm.Sumcheck.Common

/-!
# `each_row`'s frame

Both `each_row`s keep an `F`-byte frame below the entry's SP `m0` (`base m0 F`) and change no
memory but their stack (`N` bytes). Their bodies keep locals in the frame below offset `lo` and
the saved registers from `hi` on, and let the callees and the loop write the frame's bytes in
`[lo, hi)` (the lanes, the `What`s, `novel_eval`'s result) and the stack below the frame: `Hit`.
A step changing memory in `Hit` only keeps the frame (`fr_hit`) and the locals (`keep_low`); a
callee's change of a range in `[lo, hi)` and its stack (`hit_of_call`), a block's writes in that
range (`hit_of_block`) are such steps.
-/

namespace NativeRustcVmArm.Whir.EachRow

open NativeRustcArm NativeRustcArm.Sym
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- The bytes `each_row`'s steps may change: the frame's `[lo, hi)` and the stack below it. -/
def Hit (m0 : MachineData) (F N lo hi : Nat) (q : BitVec 64) : Prop :=
  InRange (base m0 F + BitVec.ofNat 64 lo) (hi - lo) q ∨ InRange (base m0 N) (N - F) q

end

public section

variable {m0 : MachineData} {F N lo hi : Nat}

/-- The layout's constraints. -/
structure Lay (m0 : MachineData) (F N lo hi : Nat) : Prop where
  lo_hi : lo ≤ hi
  hi_F : hi ≤ F
  F_N : F ≤ N
  N_sp : N ≤ m0.regs.SP.toNat

theorem Lay.base_F (h : Lay m0 F N lo hi) : (base m0 F).toNat = m0.regs.SP.toNat - F :=
  Ring.base_toNat (by have := h.F_N; have := h.N_sp; omega)

theorem Lay.base_N (h : Lay m0 F N lo hi) : (base m0 N).toNat = m0.regs.SP.toNat - N :=
  Ring.base_toNat h.N_sp

/-- `Hit` as numbers. -/
theorem Lay.hit_iff (h : Lay m0 F N lo hi) {q : BitVec 64} :
    Hit m0 F N lo hi q ↔ (m0.regs.SP.toNat - F + lo ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - F + hi) ∨
      (m0.regs.SP.toNat - N ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - F) := by
  have := h.lo_hi; have := h.hi_F; have := h.F_N; have := h.N_sp
  have hF := h.base_F; have hN := h.base_N
  have hlt := m0.regs.SP.toNat_lt
  have e1 : (base m0 F + BitVec.ofNat 64 lo).toNat = m0.regs.SP.toNat - F + lo := by
    rw [NativeRustcVm.toNat_add_ofNat (by omega), hF]
  unfold Hit
  rw [Sym.inRange_iff (by rw [e1]; omega), Sym.inRange_iff (by rw [hN]; omega), e1, hN]
  constructor <;> intro h' <;> omega

/-- The stack as numbers. -/
theorem Lay.stack_iff (h : Lay m0 F N lo hi) {q : BitVec 64} :
    InRange (base m0 N) N q ↔ m0.regs.SP.toNat - N ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat := by
  have := h.N_sp
  have hN := h.base_N
  have hlt := m0.regs.SP.toNat_lt
  rw [Sym.inRange_iff (by rw [hN]; omega), hN]
  constructor <;> intro h' <;> omega

/-- A byte of the frame at offset `o` as a number. -/
theorem Lay.frame_toNat (h : Lay m0 F N lo hi) {o : Nat} (ho : o < F) :
    (base m0 F + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - F + o := by
  have := h.F_N; have := h.N_sp
  have hlt := m0.regs.SP.toNat_lt
  rw [NativeRustcVm.toNat_add_ofNat (by rw [h.base_F]; omega), h.base_F]

theorem Lay.hit_stack (h : Lay m0 F N lo hi) {q : BitVec 64} (hq : Hit m0 F N lo hi q) :
    InRange (base m0 N) N q := by
  rw [h.hit_iff] at hq
  rw [h.stack_iff]
  have := h.lo_hi; have := h.hi_F; have := h.F_N; have := h.N_sp
  omega

/-- A byte of the frame outside `[lo, hi)` is not hit. -/
theorem Lay.not_hit (h : Lay m0 F N lo hi) {o : Nat} (ho : o < lo ∨ (hi ≤ o ∧ o < F)) :
    ¬ Hit m0 F N lo hi (base m0 F + BitVec.ofNat 64 o) := by
  have := h.lo_hi; have := h.hi_F; have := h.F_N; have := h.N_sp
  rw [h.hit_iff, h.frame_toNat (by omega)]
  omega

/-- **A step changing memory in `Hit`** keeps the frame, its slots outside `[lo, hi)`. -/
theorem fr_hit {slots : List (Nat × XReg)} {outs : BitVec 64 → Prop} {m m' : MachineData}
    (hl : Lay m0 F N lo hi) (h : Fr m0 F N slots [] outs m) (hsp : m'.regs.SP = m.regs.SP)
    (hk : Kept m.dmem m'.dmem) (hs : SameOutside m.dmem m'.dmem (Hit m0 F N lo hi))
    (hsl : ∀ p ∈ slots, p.1 + 8 ≤ lo ∨ (hi ≤ p.1 ∧ p.1 + 8 ≤ F)) :
    Fr m0 F N slots [] outs m' :=
  h.step hsp (by simp) hk hs (fun _ hq ↦ .inl (hl.hit_stack hq)) fun p hp i hi' hq ↦ by
    rw [NativeRustcVm.addr_add_add] at hq
    exact hl.not_hit (by have := hsl p hp; omega) hq

/-- **Bytes of the frame below `lo`** are kept by a step changing memory in `Hit`. -/
theorem keep_low {d d' : Mem 64} (hl : Lay m0 F N lo hi) (hs : SameOutside d d' (Hit m0 F N lo hi))
    {o : Nat} {bs : List UInt8} (hle : o + bs.length ≤ lo)
    (hb : NativeRustcVm.BytesAt d (base m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d' (base m0 F + BitVec.ofNat 64 o) bs :=
  hb.of_sameOutside hs fun i hi' ↦ by
    rw [NativeRustcVm.addr_add_add]
    exact hl.not_hit (by omega)

/-- **Bytes of the frame outside `[lo, hi)`** are kept by a step changing memory in `Hit`. -/
theorem keep_frame {d d' : Mem 64} (hl : Lay m0 F N lo hi)
    (hs : SameOutside d d' (Hit m0 F N lo hi)) {o : Nat} {bs : List UInt8}
    (hle : o + bs.length ≤ lo ∨ (hi ≤ o ∧ o + bs.length ≤ F))
    (hb : NativeRustcVm.BytesAt d (base m0 F + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d' (base m0 F + BitVec.ofNat 64 o) bs :=
  hb.of_sameOutside hs fun i hi' ↦ by
    rw [NativeRustcVm.addr_add_add]
    exact hl.not_hit (by omega)

/-- **A callee's change** of `n` bytes at offset `o ∈ [lo, hi)` of the frame and of its stack,
`N'` bytes below the frame. -/
theorem hit_of_call {m m' : MachineData} {N' o n : Nat} (hl : Lay m0 F N lo hi)
    (hsp : m.regs.SP.toBitVec = base m0 F) (hN' : F + N' ≤ N) (ho : lo ≤ o) (hon : o + n ≤ hi)
    (hs : SameOutside m.dmem m'.dmem (fun q ↦
      NativeRustcVm.InAny [⟨base m0 F + BitVec.ofNat 64 o, n⟩] q ∨
        InRange (stackBelow m N') N' q)) :
    SameOutside m.dmem m'.dmem (Hit m0 F N lo hi) := by
  intro q hq
  refine hs q fun h' ↦ hq ?_
  have := hl.lo_hi; have := hl.hi_F; have := hl.F_N; have := hl.N_sp
  have hlt := m0.regs.SP.toNat_lt
  rw [hl.hit_iff]
  rcases h' with ⟨r, hr, hq'⟩ | hq'
  · simp only [List.mem_singleton] at hr
    subst hr
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact absurd hq' (Nat.not_lt_zero _)
    have e := hl.frame_toNat (o := o) (by omega)
    have hq'' : InRange (base m0 F + BitVec.ofNat 64 o) n q := hq'
    rw [Sym.inRange_iff (by rw [e]; omega), e] at hq''
    omega
  · have hsb : (stackBelow m N').toNat = m0.regs.SP.toNat - F - N' := by
      unfold stackBelow
      rw [hsp, NativeRustcVm.toNat_sub_ofNat (by rw [hl.base_F]; omega), hl.base_F]
    rw [Sym.inRange_iff (by rw [hsb]; omega), hsb] at hq'
    omega

/-- **A block's writes** in region 0, the frame, within `[lo, hi)`. -/
theorem hit_of_block [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hl : Lay m0 F N lo hi) (hm : Match (Env.ofMachine m ((base m0 F, F) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 F, F) :: rs)).WF)
    (hS : S.mem.all (fun w ↦ w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) = true) :
    SameOutside m.dmem m'.dmem (Hit m0 F N lo hi) := by
  intro q hq
  refine hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ hq ?_
  have := List.all_eq_true.mp hS w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨⟨hr, hlo⟩, hhi⟩ := this
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [hl.base_F] at h1 h2
  rw [hl.hit_iff]
  omega

/-- A pointer into region 0 of a fresh environment. -/
theorem eval_ptr0 [Labels] (m : MachineData) (b : BitVec 64) (n : Nat) (rs : List (BitVec 64 × Nat))
    (o : Nat) : (Sym.ptr 0 (o : Int)).eval (Env.ofMachine m ((b, n) :: rs)) = b + BitVec.ofNat 64 o :=
  rfl

/-- Bytes `memcpy` copied: a prefix of the source's. -/
theorem bytesAt_copy {d d' : Mem 64} {a a' : BitVec 64} {n : Nat} {bs : List UInt8}
    (hc : NativeRustcVm.BytesAt d a (bytesOf d' a' n)) (hb : NativeRustcVm.BytesAt d' a' bs)
    (hle : bs.length ≤ n) : NativeRustcVm.BytesAt d a bs := by
  intro i hi
  rw [hc i (by simp [NativeRustcArm.bytesOf]; omega)]
  have := hb i hi
  simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range]
  rw [show (d'.get? (a' + BitVec.ofNat 64 i)) = some bs[i] from this]
  rfl

/-- `lsl #3` as rustc writes it (`ubfm #61, #60`): the product by `8`. -/
theorem lsl3 (x : BitVec 64) : UnOp.apply (.ubfm 61 60) .W64 x = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- **An input** apart from the stack: its bytes as at the entry. -/
theorem input_same {slots : List (Nat × XReg)} {outs : BitVec 64 → Prop} {m : MachineData}
    (h : Fr m0 F N slots [] outs m) (hN : N ≤ m0.regs.SP.toNat) {a : BitVec 64}
    {n : Nat} (hna : NoWrap a n) (hst : OffStack m0 a n N)
    (hout : ∀ i < n, ¬ outs (a + BitVec.ofNat 64 i)) :
    ∀ i < n, m.dmem.get? (a + BitVec.ofNat 64 i) = m0.dmem.get? (a + BitVec.ofNat 64 i) :=
  fun i hi ↦ h.same _ fun h' ↦ h'.elim
    (NativeRustcVm.Transcript.not_inRange_of_apart hst hna (Ring.base_noWrap hN)
      (NativeRustcVm.inRange_add hi (by unfold NoWrap at hna; omega))) (hout i hi)

end

end NativeRustcVmArm.Whir.EachRow
