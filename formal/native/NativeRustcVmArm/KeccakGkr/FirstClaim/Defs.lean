module

public import NativeRustcVmArm.KeccakGkr.Common
public import NativeRustcVmArm.KeccakGkr.FirstClaim.Exec
public import NativeRustcVmArm.Spec.Arrays

/-!
# `first_claim`: the body's context

The entry's arguments (`outA` the result, `wtsA` the bit weights, `fbA` the frame), the body
(`Body`: the 1408-byte frame, the result and the bit weights written), the bit weight `j`
(`wOf`), and the slices a call reads: an argument's elements (`arg_slice`), the frame's locals
(`local_readable`, `local_offStack`), the two apart (`arg_local_apart`).
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (claimBytes weightsBytes)

@[expose] public section

/-- The result. -/
abbrev outA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The bit weights. -/
abbrev wtsA (m0 : MachineData) : BitVec 64 := firstWeights m0
/-- The frame's base. -/
abbrev fbA (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 1408

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(1400, .X19), (1392, .X20), (1384, .X21), (1376, .X22), (1368, .X23), (1360, .X24),
    (1352, .X25), (1344, .X26), (1336, .X27), (1328, .X28), (1312, .X29), (1320, .X30)]

/-- The regions `first_claim` writes. -/
abbrev wsOf (m0 : MachineData) : List Region := [⟨outA m0, 8 + claimBytes⟩, ⟨wtsA m0, weightsBytes⟩]

/-- The regions `first_claim` reads. -/
abbrev rsOf (m0 : MachineData) (n : Nat) : List Region :=
  [ewsRegion m0.regs.X1.toBitVec n, ewsRegion m0.regs.X3.toBitVec 1,
    ewsRegion m0.regs.X4.toBitVec 5, ewsRegion m0.regs.X5.toBitVec 25, ⟨m0.regs.SP.toBitVec, 8⟩]

/-- The body: the 1408-byte frame, the result and the bit weights written. -/
abbrev Body (m0 st : MachineData) : Prop := Frame m0 1408 firstClaimStack slots (wsOf m0) st

/-- Bit weight `j` of the lanes' kernel. -/
def wOf (lanes : Array EW) (j : Nat) : EW :=
  lanes.getD (j / 64) 0 * EW.ofK ((1 : UInt64) <<< (j % 64).toUInt64)

end

public section

theorem slots_le : ∀ p ∈ slots, 1312 ≤ p.1 ∧ p.1 + 8 ≤ 1408 := by decide

theorem slots_le' : ∀ p ∈ slots, p.1 + 8 ≤ 1408 := fun p hp ↦ (slots_le p hp).2

theorem all_slots : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → r ∈ ([] : List XReg) := by
  intro r hr hn
  exfalso
  apply hn
  cases r <;> simp_all [calleeSaved, slots]

theorem stack_eq : firstClaimStack = 2112 := rfl

variable {inst segment lanePoint output : Array EW} {m0 st : MachineData}

theorem pre_areas (hpre : FirstClaimPre inst segment lanePoint output m0) :
    Areas m0 firstClaimStack (wsOf m0) (rsOf m0 inst.size) :=
  hpre.2.2.2.2.2.2.2.2.2.2

theorem wsOff (hpre : FirstClaimPre inst segment lanePoint output m0) :
    WsOff m0 firstClaimStack (wsOf m0) :=
  wsOff_of_areas (pre_areas hpre) hpre.1

/-- **An argument's elements** in a body: a slice a callee using `n` bytes of stack reads. -/
theorem arg_slice (hpre : FirstClaimPre inst segment lanePoint output m0) (hb : Body m0 st)
    {a : BitVec 64} {xs : Array EW} (hr : ewsRegion a xs.size ∈ rsOf m0 inst.size)
    (hx : NativeRustcVm.EWsAt m0.dmem a xs.toList) {n : Nat} (hn : 1408 + n ≤ firstClaimStack)
    {x l : UInt64} (hxa : x.toBitVec = a) (hl : l.toNat = xs.size) :
    SliceOk st x l n ∧ slice st x l = xs := by
  have hA := pre_areas hpre
  have hS := hpre.1
  have hok := Areas.ok hA (Or.inr hr)
  have hst := NativeRustcVm.Apart.symm (Areas.stack_rs hA hr)
  have hx' : NativeRustcVm.EWsAt st.dmem a xs.toList := by
    have := hb.bytesAt hA hS hr (o := 0) (bs := xs.toList.flatMap NativeRustcVm.ewBytes) (by
      rw [length_flatMap_ewBytes, Array.length_toList]; show 0 + 16 * xs.size ≤ 16 * xs.size; omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact hx)
    rwa [NativeRustcVm.addr_add_zero] at this
  refine ⟨⟨by rw [hxa, hl]; exact ⟨Mapped.kept' hok.1 hb.kept, hok.2⟩,
    by rw [hxa, hl]; exact hb.apart_callee hS hn hst⟩, ?_⟩
  unfold slice
  rw [hxa, hl]
  have := NativeRustcVm.ewsOf_of_ewsAt hx'
  rw [Array.length_toList] at this
  rw [this, Array.toArray_toList]

/-- **The frame's locals** below the slots are data memory and do not wrap. -/
theorem local_readable (hpre : FirstClaimPre inst segment lanePoint output m0) (hb : Body m0 st)
    {o n : Nat} (hon : o + n ≤ 1408) :
    Readable st (fbA m0 + BitVec.ofNat 64 o) n := by
  obtain ⟨hmap, hnw, -⟩ := frame_ok hpre.1 (show 1408 ≤ firstClaimStack by decide)
  have := sub_ok (show Region.Ok m0.dmem ⟨fbA m0, 1408⟩ from ⟨hmap, hnw⟩) hon
  exact ⟨Mapped.kept' this.1 hb.kept, this.2⟩

/-- **The frame's locals** are apart from a callee's stack. -/
theorem local_offStack (hpre : FirstClaimPre inst segment lanePoint output m0) (hb : Body m0 st)
    {o n s : Nat} (ho : o ≤ 1408) (hs : 1408 + s ≤ firstClaimStack) :
    OffStack st (fbA m0 + BitVec.ofNat 64 o) n s := by
  have hS := hpre.1
  have hN : firstClaimStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have hfb := (frame_ok hS (show 1408 ≤ firstClaimStack by decide)).2.2
  have hSP := m0.regs.SP.toBitVec.isLt
  unfold OffStack Apart stackBelow
  right
  rw [hb.sp, toNat_sub_ofNat (by rw [hfb]; omega),
    toNat_add_ofNat' (show (fbA m0).toNat + o < 2 ^ 64 by rw [hfb]; omega), hfb]
  omega

/-- **An argument's region and a frame local** are apart. -/
theorem arg_local_apart (hpre : FirstClaimPre inst segment lanePoint output m0) {r : Region}
    (hr : r ∈ rsOf m0 inst.size) {o n : Nat} (hon : o + n ≤ 1408) :
    Apart r.addr r.size (fbA m0 + BitVec.ofNat 64 o) n := by
  have hA := pre_areas hpre
  have hS := hpre.1
  have hN : firstClaimStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have hfb := (frame_ok hS (show 1408 ≤ firstClaimStack by decide)).2.2
  have hSP := m0.regs.SP.toBitVec.isLt
  have hap := Areas.stack_rs hA hr
  have hnw := (Areas.ok hA (Or.inr hr)).2
  unfold Apart stackBelow at hap
  unfold NativeRustcVm.NoWrap at hnw
  rw [toNat_sub_ofNat hN] at hap
  unfold Apart
  rw [toNat_add_ofNat' (show (fbA m0).toNat + o < 2 ^ 64 by rw [hfb]; omega), hfb]
  rw [stack_eq] at hap hN
  omega

/-- An argument's elements `o` to `o + l` in a body: readable, apart from a callee's stack, what
`ewsOf` reads there. -/
theorem arg_sub (hpre : FirstClaimPre inst segment lanePoint output m0) (hb : Body m0 st)
    {a : BitVec 64} {xs : Array EW} (hr : ewsRegion a xs.size ∈ rsOf m0 inst.size)
    (hx : NativeRustcVm.EWsAt m0.dmem a xs.toList) {o l : Nat} (hol : o + l ≤ xs.size) {n : Nat}
    (hn : 1408 + n ≤ firstClaimStack) :
    Readable st (a + BitVec.ofNat 64 (16 * o)) (16 * l) ∧
      OffStack st (a + BitVec.ofNat 64 (16 * o)) (16 * l) n ∧
      NativeRustcVm.ewsOf st.dmem (a + BitVec.ofNat 64 (16 * o)) l = (xs.toList.drop o).take l := by
  have hA := pre_areas hpre
  have hS := hpre.1
  have hok := Areas.ok hA (Or.inr hr)
  have hx' : NativeRustcVm.EWsAt st.dmem a xs.toList := by
    have := hb.bytesAt hA hS hr (o := 0) (bs := xs.toList.flatMap NativeRustcVm.ewBytes) (by
      rw [length_flatMap_ewBytes, Array.length_toList]; show 0 + 16 * xs.size ≤ 16 * xs.size; omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact hx)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hsub := sub_ok hok (o := 16 * o) (n := 16 * l) (by show _ ≤ 16 * xs.size; omega)
  refine ⟨⟨Mapped.kept' hsub.1 hb.kept, hsub.2⟩, ?_, ?_⟩
  · have hst : Apart (stackBelow m0 firstClaimStack) firstClaimStack a (16 * xs.size) :=
      Areas.stack_rs hA hr
    have hN : firstClaimStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
    have hnw : a.toNat + 16 * xs.size ≤ 2 ^ 64 := hok.2
    have hsp' : st.regs.SP.toBitVec.toNat = m0.regs.SP.toBitVec.toNat - 1408 :=
      hb.sp_toNat hS (by decide)
    unfold Apart stackBelow at hst
    rw [toNat_sub_ofNat hN] at hst
    unfold OffStack Apart stackBelow
    rw [stack_eq] at hst hN hn
    rw [toNat_sub_ofNat (by rw [hsp']; omega), hsp']
    rcases Nat.lt_or_ge (a.toNat + 16 * o) (2 ^ 64) with hlt | hge
    · rw [toNat_add_ofNat' hlt]; omega
    · have e : (a + BitVec.ofNat 64 (16 * o)).toNat = 0 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 * o < 2 ^ 64 by omega),
          show a.toNat + 16 * o = 2 ^ 64 by omega, Nat.mod_self]
      rw [e]; omega
  · have := NativeRustcVm.ewsOf_of_ewsAt ((hx'.drop o).take l)
    rwa [List.length_take, List.length_drop, Array.length_toList,
      Nat.min_eq_left (by omega)] at this

/-- **The frame and the word above it** (the bit weights' address) are data memory. -/
theorem frame_word_ok (hpre : FirstClaimPre inst segment lanePoint output m0) :
    Mapped m0.dmem (fbA m0) 1416 ∧ NoWrap (fbA m0) 1416 := by
  have hS := hpre.1
  obtain ⟨hmap, hnw, hfb⟩ := frame_ok hS (show 1408 ≤ firstClaimStack by decide)
  have hw := Areas.ok (pre_areas hpre) (r := ⟨m0.regs.SP.toBitVec, 8⟩) (Or.inr (by simp))
  have e : fbA m0 + BitVec.ofNat 64 1408 = m0.regs.SP.toBitVec := by
    unfold fbA; exact BitVec.sub_add_cancel _ _
  refine ⟨show Mapped m0.dmem (fbA m0) (1408 + 8) from
    NativeRustcVm.mapped_append_iff.mpr ⟨hmap, e ▸ hw.1⟩, ?_⟩
  have h8 : m0.regs.SP.toBitVec.toNat + 8 ≤ 2 ^ 64 := hw.2
  unfold NoWrap
  rw [hfb]
  have : 1408 ≤ m0.regs.SP.toBitVec.toNat := Nat.le_trans (by decide) hS.2.1
  omega


/-- **A frame local kept** by a change in a callee's stack below the body's SP, in the written
regions and in the frame's bytes `o'` to `o' + n'` apart from it. -/
theorem local_keep' (hpre : FirstClaimPre inst segment lanePoint output m0) (hb : Body m0 st)
    {st' : MachineData} {o n o' n' : Nat} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt st.dmem (fbA m0 + BitVec.ofNat 64 o) bs) (ho : o + bs.length ≤ 1408)
    (hn : n < 2 ^ 63) (ho' : o' + n' ≤ 1408) (hdis : o + bs.length ≤ o' ∨ o' + n' ≤ o)
    {R : BitVec 64 → Prop} (hs : SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → InRange (stackBelow st n) n p ∨ NativeRustcVm.InAny (wsOf m0) p ∨
      InRange (fbA m0 + BitVec.ofNat 64 o') n' p) :
    NativeRustcVm.BytesAt st'.dmem (fbA m0 + BitVec.ofNat 64 o) bs :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi hRp ↦ by
    rw [NativeRustcVm.addr_add_add] at hRp
    rcases hR _ hRp with h' | h' | h'
    · unfold stackBelow at h'
      rw [hb.sp] at h'
      exact not_inRange_below (by omega) h'
    · exact slot_not hpre.1 (by decide) (wsOff hpre) (show o + i < 1408 by omega) h'
    · unfold InRange at h'
      rw [show fbA m0 + BitVec.ofNat 64 (o + i) - (fbA m0 + BitVec.ofNat 64 o') =
        BitVec.ofNat 64 (o + i) - BitVec.ofNat 64 o' by bv_omega, BitVec.toNat_sub,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h'
      omega

/-- **A frame local kept** by a change in a callee's stack below the body's SP and in the
written regions. -/
theorem local_keep (hpre : FirstClaimPre inst segment lanePoint output m0) (hb : Body m0 st)
    {st' : MachineData} {o n : Nat} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt st.dmem (fbA m0 + BitVec.ofNat 64 o) bs) (ho : o + bs.length ≤ 1408)
    (hn : n < 2 ^ 63) {R : BitVec 64 → Prop} (hs : SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → InRange (stackBelow st n) n p ∨ NativeRustcVm.InAny (wsOf m0) p) :
    NativeRustcVm.BytesAt st'.dmem (fbA m0 + BitVec.ofNat 64 o) bs :=
  local_keep' hpre hb h ho hn (o' := 0) (n' := 0) (by decide) (Or.inr (Nat.zero_le _)) hs
    fun p hp ↦ (hR p hp).elim Or.inl fun h ↦ Or.inr (Or.inl h)

/-- **Elements of a written region kept** by a change in a callee's stack, `n` bytes below a
body's SP, and in the frame's bytes `o'` to `o' + n'`. -/
theorem ws_keep (hpre : FirstClaimPre inst segment lanePoint output m0) (hb : Body m0 st)
    {st' : MachineData} {w : Region} (hw : w ∈ wsOf m0) {n N o' n' : Nat}
    (hn : 1408 + n ≤ firstClaimStack) (ho' : o' + n' ≤ 1408) (hN : 16 * N ≤ w.size)
    {f : Nat → EW} (h : ElemsAt st.dmem w.addr f N) {R : BitVec 64 → Prop}
    (hs : SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → InRange (stackBelow st n) n p ∨ InRange (fbA m0 + BitVec.ofNat 64 o') n' p) :
    ElemsAt st'.dmem w.addr f N := by
  have hA := pre_areas hpre
  have hS := hpre.1
  have hok := Areas.ok hA (Or.inl hw)
  have hap := Areas.apart_stack hA hw
  refine h.keep hs (fun p hp hc ↦ NativeRustcVm.Apart.not_inRange hap hok.2 (noWrap_stackBelow hS)
    (show InRange w.addr w.size p by unfold InRange at hp ⊢; omega) ?_)
    (show w.addr.toNat + 16 * N ≤ 2 ^ 64 by
      have := hok.2; unfold NativeRustcVm.NoWrap at this; omega)
  rcases hR p hc with h' | h'
  · exact hb.stack_in hS hn h'
  · exact local_inStack hS (F := 1408) (by decide) (lo := 1408) (by decide) (inRange_mono h' ho')

/-- **Elements of a written region kept** by a callee using `n` bytes below a body's SP. -/
theorem ws_keep_call (hpre : FirstClaimPre inst segment lanePoint output m0) (hb : Body m0 st)
    {st' : MachineData} {w : Region} (hw : w ∈ wsOf m0) {n N : Nat}
    (hn : 1408 + n ≤ firstClaimStack) (hN : 16 * N ≤ w.size) {f : Nat → EW}
    (h : ElemsAt st.dmem w.addr f N)
    (hs : SameOutside st.dmem st'.dmem (InRange (stackBelow st n) n)) :
    ElemsAt st'.dmem w.addr f N :=
  ws_keep hpre hb hw hn (o' := 0) (n' := 0) (by decide) hN h hs fun _ h ↦ Or.inl h

end

end NativeRustcVmArm.KeccakGkr.FirstClaim
