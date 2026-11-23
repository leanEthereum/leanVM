module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Ood

/-!
# `verify_stacked_opening`: windows of the frame (x86-64)

A window `[lo, lo + n)` of the frame (`win m0 lo`): its address as a number (`Parts.win_toNat`),
readable and off a callee's stack in a state of the frame (`Ok.win_in`), apart from an area apart
from the stack (`Parts.win_apart`) and from the outputs. The frame's words across a call writing
a window and its stack (`FW.callWin`). The `BasisW`'s words at the frame's `104` (`basisW`); the
levels copied (`levelsAt_copy`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

@[expose] public section

/-- The frame's byte `lo`. -/
abbrev win (m0 : MachineData) (lo : Nat) : BitVec 64 := off (stackBelow m0 512) lo

/-- The `BasisW`'s words at the frame's `104` to `159`: the scales and their count, the layout, the
ring switch's output, the Keccak output, the column claims, the out-of-domain claim. -/
def basisW (m0 : MachineData) (layout : LayoutW) (cs : Array ColumnClaimW) : List (Nat × UInt64) :=
  [(104, UInt64.ofBitVec (off (scA m0) 8)), (112, (cntOf layout cs).toUInt64),
    (120, UInt64.ofBitVec (layA m0)), (128, UInt64.ofBitVec (reg m0 .rcx)),
    (136, UInt64.ofBitVec (reg m0 .r8)), (144, UInt64.ofBitVec (clA m0)),
    (152, UInt64.ofBitVec (oA m0))]

end

public section

/-- A copy's bytes. -/
theorem bytesAt_copy {d d' : Mem 64} {src dst : BitVec 64} {n o : Nat} {bs : List UInt8}
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcX64.bytesOf d src n))
    (hb : NativeRustcVm.BytesAt d (src + BitVec.ofNat 64 o) bs) (hl : o + bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (dst + BitVec.ofNat 64 o) bs := by
  intro i hi
  have := hc (o + i) (by simp [NativeRustcX64.bytesOf]; omega)
  rw [NativeRustcVm.addr_add_add, this]
  simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range]
  rw [← NativeRustcVm.addr_add_add, hb i hi]
  rfl

/-- **The levels copied**: at most six, `144` bytes. -/
theorem levelsAt_copy {d d' : Mem 64} {src dst : BitVec 64} {ls : List LeanVM.Parameters.Whir.Level}
    (hc : NativeRustcVm.BytesAt d' dst (NativeRustcX64.bytesOf d src 144)) (hl : LevelsAt d src ls)
    (hlen : ls.length ≤ 6) : LevelsAt d' dst ls := fun i hi ↦ by
  obtain ⟨h1, h2, h3, h4⟩ := hl i hi
  refine ⟨h1, h2, h3, bytesAt_copy hc h4 ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    NativeRustcVm.length_wordBytes, levelBytes]
  omega

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

theorem Parts.win_toNat {lo : Nat} (hlo : lo ≤ 520) :
    (win m0 lo).toNat = (rspOf m0).toNat - 512 + lo := by
  have hf : (stackBelow m0 512).toNat = (rspOf m0).toNat - 512 := h.fbn
  have hr := h.rsp
  rw [toNat_off (by omega)]
  omega

/-- A window apart from an area apart from the stack. -/
theorem Parts.win_apart {lo n : Nat} (hlo : lo + n ≤ 520) {x : BitVec 64} {l : Nat}
    (hx : NativeRustcVm.Apart x l (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8)) : NativeRustcVm.Apart (win m0 lo) n x l := by
  have hw := h.win_toNat (lo := lo) (by omega)
  have hs : (stackBelow m0 verifyStackedOpeningStack).toNat = (rspOf m0).toNat - 11936 := h.sb
  have hr := h.rsp
  unfold NativeRustcVm.Apart at hx ⊢
  rw [hs, stack_eq] at hx
  omega

/-- A window apart from the `TState`. -/
theorem Parts.win_t {lo n : Nat} (hlo : lo + n ≤ 520) :
    NativeRustcVm.Apart (win m0 lo) n (tA m0) tstateBytes :=
  h.win_apart hlo h.wt.2.2.2.1.1

/-- A window apart from the `WhirW`. -/
theorem Parts.win_p {lo n : Nat} (hlo : lo + n ≤ 520) :
    NativeRustcVm.Apart (win m0 lo) n (pA m0) whirBytes :=
  h.win_apart hlo h.po.1.2.2.2.2.1

/-- A window, readable and off a callee's stack, in a state of the frame at a call. -/
theorem Ok.win_in {st : MachineData} (hok : Ok m0 st 0) {lo n : Nat} (hlo : 8 ≤ lo)
    (hn : lo + n ≤ 520) {N' : Nat} (hN' : 512 + N' ≤ verifyStackedOpeningStack) :
    WhirIn st (win m0 lo) n N' := by
  have hw := h.win_toNat (lo := lo) (by omega)
  have hR := h.rsp
  have hfb : (stackBelow m0 512).toNat = (rspOf m0).toNat - 512 := h.fbn
  refine ⟨⟨mapped_off (hok.frame_ok h).1 hn, ?_⟩, ?_⟩
  · show (win m0 lo).toNat + n ≤ 2 ^ 64
    omega
  · show NativeRustcVm.Apart _ _ _ _
    rw [stack_eq] at hN'
    have hsb : (stackBelow st N').toNat = (rspOf m0).toNat - 512 - N' := by
      rw [stackBelow_toNat (by rw [Ok.sp hok, hfb]; omega), Ok.sp hok, hfb]
    unfold NativeRustcVm.Apart
    rw [hsb, hw]
    omega

/-- **The frame's words** across a call writing a window and its stack below the frame. -/
theorem FW.callWin {st : MachineData} (hok : Ok m0 st 0) {d' : Mem 64} {N' lo n : Nat}
    (hN' : 512 + N' ≤ verifyStackedOpeningStack) (hn : lo + n ≤ 520)
    (hso : NativeRustcVm.SameOutside st.dmem d'
      (fun q ↦ NativeRustcVm.InRange (win m0 lo) n q ∨
        NativeRustcVm.InRange (stackBelow st N') N' q))
    {L : List (Nat × UInt64)} (hL : FW st.dmem m0 L)
    (hmiss : ∀ p ∈ L, p.1 + 8 ≤ lo ∨ lo + n ≤ p.1) (hle : ∀ p ∈ L, p.1 + 8 ≤ 520) :
    FW d' m0 L := fun p hp ↦ by
  have hR := h.rsp
  have hfb : (stackBelow m0 512).toNat = (rspOf m0).toNat - 512 := h.fbn
  have hfb' : (fb m0).toNat = (rspOf m0).toNat - 512 := h.fbn
  have hle' := hle p hp
  have hm := hmiss p hp
  refine NativeRustcVm.BytesAt.of_sameOutside (hL p hp) hso fun i hi hq ↦ ?_
  rw [NativeRustcVm.length_wordBytes] at hi
  rw [off_add] at hq
  rcases hq with hq | hq
  · have hw := h.win_toNat (lo := lo) (by omega)
    have hnw : NativeRustcVm.NoWrap (win m0 lo) n := by unfold NativeRustcVm.NoWrap; omega
    rw [inR hnw, hw, toNat_off (by omega)] at hq
    omega
  · exact (h.callee_stack (Ok.sp hok) hN' hq).2 (inRange_off_self (by omega) (by omega))

end

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
