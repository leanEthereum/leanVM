module

public import NativeRustcVmArm.Whir.VerifyStackedOpening.Exit
public import NativeRustcVmArm.Whir.FoldRounds.Basic

/-!
# `verify_stacked_opening`: the ladder

`ladder_b30`: `b30` reads the stack's log-size, writes the `BasisW`'s words (`basisWords`) to the
frame's bytes 56 to 111 and calls `ladder` into the frame's bytes 256 to 415; `b31` checks its tag:
`None` goes to `b36`, `Some` to `b32` (`AtB32`). Helpers: a window of the frame (`Parts.win`),
the frame's words and `Common` across a step writing such a window (`fw_win`, `Common.frame`),
the read-only data for a callee (`Parts.rodataAt`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening
open LeanVM.Parameters

@[expose] public section

/-- The `BasisW`'s words at the frame's bytes 56 to 111: the scales and their count, the layout,
the ring switch's output, the Keccak output, the column claims, the out-of-domain claim. -/
def basisWords (layout : LayoutW) (cs : Array ColumnClaimW) (m0 : MachineData) :
    List (Nat × UInt64) :=
  [(56, UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 8)), (64, (cntOf layout cs).toUInt64),
    (72, m0.regs.X1), (80, m0.regs.X3), (88, m0.regs.X4), (96, m0.regs.X5), (104, m0.regs.X6)]

/-- **At `b32`**: the ladder `ls` at the frame's byte 256 (its levels from 264, their count at
408), its address in X19, the `BasisW`'s words, the stack's log-size in X21, the batched target's
two parts in X28, X29 and X27, X26. -/
structure AtB32 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (ls : List Whir.Level) (m0 st : MachineData) :
    Prop where
  com : Common a s layout cs m0 st
  fwb : FW st.dmem m0 (basisWords layout cs m0)
  lad : Whir.ladder layout.stackLog m0.regs.X2.toNat = some ls
  len : ls.length ≤ 6
  lv : LevelsAt st.dmem (loc m0 264) ls
  cnt : NativeRustcVm.WordAt st.dmem (loc m0 408) ls.length.toUInt64
  x19 : (st.regs.getXReg .X19).toBitVec = loc m0 256
  x21 : st.regs.getXReg .X21 = layout.stackLog.toUInt64
  claim : (⟨st.regs.getXReg .X28, st.regs.getXReg .X29⟩ : EW) +
    ⟨st.regs.getXReg .X27, st.regs.getXReg .X26⟩ = claimOf s layout target cs value

end

public section

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

/-- The frame's byte `o`. -/
theorem Parts.loc_toNat {o : Nat} (ho : o ≤ 512) :
    (loc m0 o).toNat = m0.regs.SP.toNat - 512 + o := by
  have hS := h.hS
  have := base_toNat (m0 := m0) (F := 512) (by omega)
  rw [NativeRustcVm.toNat_add_ofNat (by have := m0.regs.SP.toNat_lt; omega), this]

/-- A window of the frame is in the frame. -/
theorem Parts.win {o n : Nat} (hon : o + n ≤ 512) {q : BitVec 64}
    (hq : InRange (loc m0 o) n q) : InRange (base m0 512) 512 q :=
  NativeRustcVm.InRange.of_sub hq (base_noWrap (by have := h.hS; omega)) hon

/-- A window of the frame, readable in a state of the frame. -/
theorem Parts.loc_readable {O : BitVec 64 → Prop} {st : MachineData} (hf : OFr m0 O st) {o n : Nat}
    (hon : o + n ≤ 512) :
    Readable st (loc m0 o) n := by
  have hS := h.hS
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [NativeRustcVm.addr_add_add]
    exact hf.kept _ (Ring.frame_mapped h.wt.1 (by rw [stack_eq]; decide) (o + i) (by omega))
  · show (loc m0 o).toNat + n ≤ 2 ^ 64
    rw [h.loc_toNat (by omega)]
    have := m0.regs.SP.toNat_lt
    omega

/-- The read-only data for a callee, from a frame with outputs among `outsF`. -/
theorem Parts.rodataAt {O : BitVec 64 → Prop} (hO : ∀ q, O q → outsF m0 q) {st : MachineData}
    (hf : OFr m0 O st) {N' : Nat} (hle : 512 + N' ≤ verifyStackedOpeningStack) :
    RodataAt st N' := by
  have hro := h.wt.2.2.1
  refine rodataAt_callee hro hf.same (fun q hq t ↦ ?_) hf.sp h.hN (by rw [stack_eq]; decide)
    (by omega)
  rcases hq with hq | hq
  · exact rodata_not_stack hro h.hN t hq
  rcases hO q hq with hq | hq | hq
  · exact rodata_not_out h.po.2 h.po.1.2.1 t hq (hro t).2.1
  · exact rodata_not_out h.so.2 h.so.1.2.1 t hq (hro t).2.1
  · exact rodata_not_out h.wt.2.2.2.2 h.ts.footprint.1.2 t hq (hro t).2.1

/-- A window of the frame is apart from the read-only data. -/
theorem Parts.loc_rodata {o n : Nat} (hon : o + n ≤ 512) :
    NativeRustcVm.RodataApart rodataAddr (loc m0 o) n := by
  have hS := h.hS
  have hN := h.hN
  refine rodataApart_stack h.wt.2.2.1 ?_ ?_
  all_goals rw [toNat_stackBelow hN, h.loc_toNat (by omega)]
  all_goals rw [stack_eq]; omega

/-- **The frame's words** across a step writing a window of the frame above them. -/
theorem fw_win {st : MachineData} (hf : VFr m0 st) {o' n' : Nat} (ho' : o' + n' ≤ 512)
    {d' : Mem 64} (hs : SameOutside st.dmem d' (InRange (loc m0 o') n'))
    {L : List (Nat × UInt64)} (hL : ∀ p ∈ L, p.1 + 8 ≤ o') (hw : FW st.dmem m0 L) :
    FW d' m0 L := fun o v hp ↦
  Fr.bytes_keep (N' := 0) hf h.hN h.ctx.frame_outs (by rw [stack_eq]; decide) ho'
    (NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr (.inl hq)) (o := o)
    (bs := NativeRustcVm.wordBytes v)
    (by rw [NativeRustcVm.length_wordBytes]; have := hL _ hp; omega)
    (.inl (by rw [NativeRustcVm.length_wordBytes]; exact hL _ hp)) (hw o v hp)

/-- **`Common`** across a step writing the frame only, its words given. -/
theorem Common.frame {st st' : MachineData} (hc : Common a s layout cs m0 st) (hf' : VFr m0 st')
    (hs : SameOutside st.dmem st'.dmem (InRange (base m0 512) 512))
    (hk : NativeRustcVm.Transcript.Keeps st.dmem st'.dmem)
    (hfw : FW st'.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (32, m0.regs.X5),
      (40, m0.regs.X6), (48, m0.regs.X2)])
    (hr : ∀ r ∈ [XReg.X22, .X23, .X24, .X25], st'.regs.getXReg r = st.regs.getXReg r) :
    Common a s layout cs m0 st' := by
  have hP : placedOf layout cs cs.size ≤ 160 := (placedOf_le_self _).trans h.cl.len_le
  have hscb : scalesBytes = 2600 := rfl
  refine ⟨hf', h.ts_frame hc.ts hk hs, hfw, ?_, ?_, (hr .X22 (by simp)).trans hc.x22,
    (hr .X23 (by simp)) ▸ hc.x23, (hr .X24 (by simp)).trans hc.x24,
    (hr .X25 (by simp)).trans hc.x25⟩
  · have := h.sc_keep hc.fr (N' := 0) (by rw [stack_eq]; decide) (o := 0)
      (bs := NativeRustcVm.wordBytes (cntOf layout cs).toUInt64)
      (NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr hq)
      (by rw [NativeRustcVm.length_wordBytes, hscb]; omega)
      (by rw [NativeRustcVm.length_wordBytes]; omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact hc.scw)
    rwa [NativeRustcVm.addr_add_zero] at this
  · exact h.sc_keep hc.fr (N' := 0) (by rw [stack_eq]; decide) (o := 8)
      (NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inr hq)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_scalesOf, hscb]; unfold cntOf
          omega)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_scalesOf]; unfold cntOf
          omega)
      hc.scs

/-- **`Common`** across a step writing a window of the frame from byte `56` on. -/
theorem Common.win {st st' : MachineData} (hc : Common a s layout cs m0 st) (hf' : VFr m0 st')
    {o' n' : Nat} (ho : 56 ≤ o') (ho' : o' + n' ≤ 512)
    (hs : SameOutside st.dmem st'.dmem (InRange (loc m0 o') n'))
    (hk : NativeRustcVm.Transcript.Keeps st.dmem st'.dmem)
    (hr : ∀ r ∈ [XReg.X22, .X23, .X24, .X25], st'.regs.getXReg r = st.regs.getXReg r) :
    Common a s layout cs m0 st' :=
  hc.frame h hf' (NativeRustcVm.SameOutside.mono hs fun _ hq ↦ h.win ho' hq) hk
    (fw_win h hc.fr ho' hs (fun p hp ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega) hc.fw) hr

end

/-- Bytes copied: what `memcpy` leaves at `dst` holds what was at `src`. -/
theorem bytesAt_copy {d d' : Mem 64} {src dst : BitVec 64} {n o : Nat} {bs : List UInt8}
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcArm.bytesOf d src n))
    (hb : NativeRustcVm.BytesAt d (src + BitVec.ofNat 64 o) bs) (hl : o + bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (dst + BitVec.ofNat 64 o) bs := by
  intro i hi
  have := hc (o + i) (by simp [NativeRustcArm.bytesOf]; omega)
  rw [NativeRustcVm.addr_add_add, this]
  simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range]
  rw [← NativeRustcVm.addr_add_add, hb i hi]
  rfl

/-- **Levels copied** by `memcpy`. -/
theorem levelsAt_copy {d d' : Mem 64} {src dst : BitVec 64} {ls : List Whir.Level}
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcArm.bytesOf d src 144)) (hl : LevelsAt d src ls)
    (hlen : ls.length ≤ 6) : LevelsAt d' dst ls := fun i hi ↦ by
  obtain ⟨h1, h2, h3, h4⟩ := hl i hi
  refine ⟨h1, h2, h3, bytesAt_copy hc h4 ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    NativeRustcVm.length_wordBytes, levelBytes]
  omega

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
