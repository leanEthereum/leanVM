module

public import NativeRustcVmArm.Layout.Body
public import NativeRustcVmArm.Rodata

/-!
# Function bodies with a frame and several outputs

`Frame m0 F S slots R st`: as `Arrays.Body`, `F` bytes of frame below the entry's SP holding the
prologue's slots, the other callee-saved registers the entry's, every mapped byte kept, but memory
changed only where `R` holds (the outputs) or in the `S` bytes of stack. Made at the entry
(`Frame.of_entry`), kept by a block writing nothing or only in the frame (`Frame.of_block`), by a
call changing bytes of `R`, of the stack but the slots (`Frame.call`); the epilogue restores the
entry's registers (`Frame.saved`).
-/

namespace NativeRustcVmArm.Layout

open NativeRustcArm NativeRustcArm.Sym
open NativeRustcVmArm.Arrays (SlotsAt calleeRegs inSlots inSlots_false mem_calleeRegs keepsAll
  savedRegs restores slot_load find?_mem find?_none mem_savedRegs frame_ok slotsAt_of_writes
  stack_noWrap toNat_sub_ofNat inRange_stack)

public section

/-- The frame's base. -/
abbrev fbase (m0 : MachineData) (F : Nat) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 F

/-- **A function's body** with outputs `R`. -/
structure Frame (m0 : MachineData) (F S : Nat) (slots : List (Nat × XReg))
    (R : BitVec 64 → Prop) (st : MachineData) : Prop where
  sp : st.regs.SP.toBitVec = fbase m0 F
  frame : SlotsAt st.dmem (fbase m0 F) m0 slots
  regs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → st.regs.getXReg r = m0.regs.getXReg r
  same : SameOutside m0.dmem st.dmem (fun p ↦ R p ∨ InRange (stackBelow m0 S) S p)
  kept : Kept m0.dmem st.dmem

theorem fbase_toNat {m0 : MachineData} {F S : Nat} (hS : StackOk m0 S) (hF : F ≤ S) :
    (fbase m0 F).toNat = m0.regs.SP.toNat - F := (frame_ok hS hF).2.2

/-- Bytes of the frame are bytes of the stack. -/
theorem frame_in_stack {m0 : MachineData} {F S : Nat} (hS : StackOk m0 S) (hF : F ≤ S) {p : BitVec 64}
    (h : InRange (fbase m0 F) F p) : InRange (stackBelow m0 S) S p := by
  have hfn := (frame_ok hS hF).2.1
  have hsn : NoWrap (stackBelow m0 S) S := stack_noWrap hS
  have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  rw [inRange_iff hfn] at h
  rw [inRange_iff hsn]
  unfold stackBelow
  rw [toNat_sub_ofNat hSle]
  rw [fbase_toNat hS hF] at h
  have := m0.regs.SP.toNat_lt
  constructor <;> simp only [UInt64.toNat_toBitVec] at * <;> omega

/-- **The prologue**: its writes in the frame (region 0 of `rs`) make a body. -/
theorem Frame.of_entry [Labels] {m0 st : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {R : BitVec 64 → Prop} {rs : List (BitVec 64 × Nat)} {S' : SState} (hS : StackOk m0 S)
    (hF : F ≤ S) (hm : Match (Env.ofMachine m0 ((fbase m0 F, F) :: rs)) S' st)
    (hwf : (Env.ofMachine m0 ((fbase m0 F, F) :: rs)).WF) (hsp : S'.sp = .ptr 0 0)
    (hw : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.1 + i) S'.mem = some (.reg p.2, i))
    (hregs : ∀ r ∈ calleeRegs, inSlots slots r = false → S'.reg r = some (.reg r))
    (hmem : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F) : Frame m0 F S slots R st := by
  refine ⟨?_, slotsAt_of_writes hm hw, fun r hr hn ↦ ?_, fun p hp ↦ ?_, hm.kept hwf⟩
  · rw [hm.sp, hsp]; simp [Sym.eval]
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs r _ (hregs r (mem_calleeRegs hr) (inSlots_false hn))]
    rfl
  · exact same_of_region hm hwf (r := 0) rfl hmem p fun h ↦ hp (Or.inr (frame_in_stack hS hF h))

/-- **A block** keeping the registers and SP, changing memory only in the frame but the slots,
keeps a body. -/
theorem Frame.of_block [Labels] {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {R : BitVec 64 → Prop} {rs : List (BitVec 64 × Nat)} {S₀ S₁ : SState}
    (hb : Frame m0 F S slots R st) (hS : StackOk m0 S) (hF : F ≤ S)
    (hm₀ : Match (Env.ofMachine st rs) S₀ st) (hm : Match (Env.ofMachine st rs) S₁ st')
    (hwf : (Env.ofMachine st rs).WF)
    (hk : keepsAll S₀ { S₁ with mem := [] } (calleeRegs.filter fun r ↦ !inSlots slots r) = true)
    (hst : ∀ p, ¬InRange (fbase m0 F) F p → st'.dmem.get? p = st.dmem.get? p)
    (hslot : ∀ q ∈ slots, ∀ i < 8, st'.dmem.get? (fbase m0 F + BitVec.ofNat 64 q.1 +
      BitVec.ofNat 64 i) = st.dmem.get? (fbase m0 F + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i)) :
    Frame m0 F S slots R st' := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, -⟩ := hk
  refine ⟨?_, fun q hq i hi ↦ ?_, fun r hr' hn ↦ ?_, fun p hp ↦ ?_,
    fun p hp ↦ hm.kept hwf _ (hb.kept p hp)⟩
  · rw [Match.sp_eq hm₀ hm hsp]; exact hb.sp
  · simp only [List.length_map, List.length_range] at hi
    rw [hslot q hq i hi]; exact hb.frame q hq i (by simpa using hi)
  · obtain ⟨hs, he⟩ := hr r (List.mem_filter.mpr ⟨mem_calleeRegs hr', by
      rw [inSlots_false hn]; rfl⟩)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · rw [hst p fun h ↦ hp (Or.inr (frame_in_stack hS hF h))]; exact hb.same p hp

/-- **A call** keeping the callee-saved registers, SP and the mapped bytes, changing memory only
where `Rc` holds: in the outputs or the stack, but not the slots. -/
theorem Frame.call {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {R Rc : BitVec 64 → Prop} (hb : Frame m0 F S slots R st)
    (hsame : SameOutside st.dmem st'.dmem Rc) (hsaved : Saved st st')
    (hRc : ∀ p, Rc p → R p ∨ InRange (stackBelow m0 S) S p)
    (hslot : ∀ q ∈ slots, ∀ i < 8, ¬Rc (fbase m0 F + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i)) :
    Frame m0 F S slots R st' := by
  refine ⟨hsaved.2.1 ▸ hb.sp, fun q hq i hi ↦ ?_, fun r hr hn ↦ (hsaved.1 r hr).trans
    (hb.regs r hr hn), fun p hp ↦ ?_, fun p hp ↦ hsaved.2.2 p (hb.kept p hp)⟩
  · simp only [List.length_map, List.length_range] at hi
    rw [hsame _ (hslot q hq i hi)]; exact hb.frame q hq i (by simpa using hi)
  · rw [hsame p fun h ↦ hp (hRc p h)]; exact hb.same p hp

/-- **The epilogue** with the frame as region 0 and other regions: it restores the entry's
callee-saved registers, X30 and SP. -/
theorem Frame.saved [Labels] {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {R : BitVec 64 → Prop} {rs : List (BitVec 64 × Nat)} {S₁ : SState}
    (hb : Frame m0 F S slots R st)
    (hm : Match (Env.ofMachine st ((fbase m0 F, F) :: rs)) S₁ st')
    (hwf : (Env.ofMachine st ((fbase m0 F, F) :: rs)).WF)
    (hx30 : XReg.X30 ∈ slots.map (·.2)) (hr : restores slots F S₁ = true) :
    Saved m0 st' ∧ st'.regs.X30 = m0.regs.X30 := by
  simp only [restores, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hr
  obtain ⟨hr, hsp⟩ := hr
  have hbase : (Env.ofMachine st ((fbase m0 F, F) :: rs)).base 0 = fbase m0 F := rfl
  have hreg : ∀ r ∈ savedRegs, st'.regs.getXReg r = m0.regs.getXReg r := by
    intro r hrs
    have h := hm.regs r _ (hr r hrs)
    cases hf : slots.find? (·.2 == r) with
    | some p =>
      obtain ⟨hp, rfl⟩ := find?_mem hf
      rw [hf] at h
      apply UInt64.toBitVec_inj.mp
      rw [h]
      exact slot_load (r := 0) (by rw [hbase]; exact hb.frame) hp
    | none =>
      rw [hf] at h
      apply UInt64.toBitVec_inj.mp
      rw [h]
      show (st.regs.getXReg r).toBitVec = _
      by_cases hc : calleeSaved r = true
      · rw [hb.regs r hc (find?_none hf)]
      · have : r = .X30 := by
          cases r <;> simp_all [calleeSaved, savedRegs]
        subst this
        exact absurd hx30 (find?_none hf)
  refine ⟨⟨fun r hc ↦ hreg r (mem_savedRegs hc), ?_, fun p hp ↦ hm.kept hwf p (hb.kept p hp)⟩,
    hreg .X30 (by simp [savedRegs])⟩
  apply UInt64.toBitVec_inj.mp
  rw [hm.sp, hsp]
  simp only [Sym.eval, hbase]
  rw [show BitVec.ofInt 64 (F : Int) = BitVec.ofNat 64 F from rfl, BitVec.sub_add_cancel]

/-- The callee's stack (`n'` bytes below the frame) is inside the stack. -/
theorem callee_stack {m0 st : MachineData} {F S n' : Nat} (hS : StackOk m0 S)
    (hsp : st.regs.SP.toBitVec = fbase m0 F) (hle : F + n' ≤ S) {p : BitVec 64}
    (h : InRange (stackBelow st n') n' p) : InRange (stackBelow m0 S) S p := by
  unfold stackBelow at h
  rw [hsp] at h
  exact inRange_stack hle hS.2.1 h

/-- The callee's stack is below the frame. -/
theorem callee_below {m0 st : MachineData} {F S n' : Nat} (hS : StackOk m0 S)
    (hsp : st.regs.SP.toBitVec = fbase m0 F) (hle : F + n' ≤ S) {o : Nat} (ho : o < F)
    : ¬InRange (stackBelow st n') n' (fbase m0 F + BitVec.ofNat 64 o) := by
  unfold stackBelow
  rw [hsp]
  have := m0.regs.SP.toNat_lt
  have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  exact Arrays.not_inRange_below (by simp at hSle ⊢; omega)

/-- The callee's stack at SP = the frame's base. -/
theorem stackOk_callee {m0 st : MachineData} {F S n' : Nat} {slots : List (Nat × XReg)}
    {R : BitVec 64 → Prop} (hS : StackOk m0 S)
    (hb : Frame m0 F S slots R st) (hF16 : F % 16 = 0) (hle : F + n' ≤ S) : StackOk st n' := by
  obtain ⟨hal, hSle, hmap⟩ := hS
  have hsp : st.regs.SP.toNat = m0.regs.SP.toNat - F := by
    rw [← UInt64.toNat_toBitVec, hb.sp, fbase_toNat ⟨hal, hSle, hmap⟩ (by omega)]
  refine ⟨by rw [hsp]; omega, by rw [hsp]; omega, fun i hi ↦ ?_⟩
  have := hb.kept _ (hmap (S - F - n' + i) (by omega))
  have hS' : S ≤ m0.regs.SP.toBitVec.toNat := hSle
  have e : st.regs.SP.toBitVec - BitVec.ofNat 64 n' + BitVec.ofNat 64 i =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - F - n' + i) := by
    rw [hb.sp]
    bv_omega
  rw [e]
  exact this

/-- Bytes of the frame are apart from what is apart from the stack. -/
theorem apart_frame_sub {m0 : MachineData} {F S : Nat} (hS : StackOk m0 S) (hF : F ≤ S)
    {x : BitVec 64} {n o k : Nat} (h : Apart x n (stackBelow m0 S) S) (hk : o + k ≤ F) :
    Apart (fbase m0 F + BitVec.ofNat 64 o) k x n := by
  have hSle : S ≤ m0.regs.SP.toNat := hS.2.1
  have hfb := fbase_toNat hS hF
  have hlt := m0.regs.SP.toNat_lt
  have h2 : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have e2 : (stackBelow m0 S).toNat = m0.regs.SP.toNat - S := by
    unfold stackBelow; rw [toNat_sub_ofNat h2]; rfl
  have e1 : (fbase m0 F + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - F + o := by
    rw [Arrays.toNat_add_ofNat' (by rw [hfb]; omega), hfb]
  unfold Apart at *
  rw [e1]
  rw [e2] at h
  omega

/-- The callee's stack is apart from what is apart from the stack. -/
theorem apart_callee {m0 st : MachineData} {F S n' : Nat} (hS : StackOk m0 S)
    (hsp : st.regs.SP.toBitVec = fbase m0 F) (hle : F + n' ≤ S) {x : BitVec 64} {n : Nat}
    (h : Apart x n (stackBelow m0 S) S) : Apart x n (stackBelow st n') n' := by
  have hSle : S ≤ m0.regs.SP.toNat := hS.2.1
  have hfb := fbase_toNat hS (by omega : F ≤ S)
  have h1 : n' ≤ (fbase m0 F).toNat := by rw [hfb]; omega
  have h2 : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have e1 : (stackBelow st n').toNat = m0.regs.SP.toNat - F - n' := by
    unfold stackBelow; rw [hsp, toNat_sub_ofNat h1, hfb]
  have e2 : (stackBelow m0 S).toNat = m0.regs.SP.toNat - S := by
    unfold stackBelow; rw [toNat_sub_ofNat h2]; rfl
  unfold Apart at *
  rw [e1]
  rw [e2] at h
  omega

/-- The frame is apart from the callee's stack. -/
theorem frame_apart_callee {m0 st : MachineData} {F S n' : Nat} (hS : StackOk m0 S)
    (hsp : st.regs.SP.toBitVec = fbase m0 F) (hle : F + n' ≤ S) {o k : Nat} (hk : o + k ≤ F) :
    Apart (fbase m0 F + BitVec.ofNat 64 o) k (stackBelow st n') n' := by
  have hSle : S ≤ m0.regs.SP.toNat := hS.2.1
  have hfb := fbase_toNat hS (by omega : F ≤ S)
  have h1 : n' ≤ (fbase m0 F).toNat := by rw [hfb]; omega
  have hlt := m0.regs.SP.toNat_lt
  have e1 : (stackBelow st n').toNat = m0.regs.SP.toNat - F - n' := by
    unfold stackBelow; rw [hsp, toNat_sub_ofNat h1, hfb]
  have e2 : (fbase m0 F + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - F + o := by
    rw [Arrays.toNat_add_ofNat' (by rw [hfb]; omega), hfb]
  unfold Apart
  rw [e1, e2]
  omega

/-- The frame's bytes, readable in a body. -/
theorem frame_readable {m0 st : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {R : BitVec 64 → Prop} (hS : StackOk m0 S) (hF : F ≤ S) (hb : Frame m0 F S slots R st)
    {o k : Nat} (hk : o + k ≤ F) : Readable st (fbase m0 F + BitVec.ofNat 64 o) k := by
  obtain ⟨hmap, hnw, he⟩ := frame_ok hS hF
  exact readable_sub ⟨hmap, hnw⟩ hb.kept hk

/-- **The read-only data for a callee** using `n'` bytes below the frame, memory changed only
apart from it. -/
theorem rodataAt_callee [Labels] {m0 st : MachineData} {F S n' : Nat} {R : BitVec 64 → Prop}
    (hS : StackOk m0 S) (h : RodataAt m0 S) (hs : SameOutside m0.dmem st.dmem R)
    (hR : ∀ q, R q → ∀ t : NativeRustcVm.Data.Item, ¬InRange (rodataAddr t) t.bytes.length q)
    (hsp : st.regs.SP.toBitVec = fbase m0 F) (hle : F + n' ≤ S) : RodataAt st n' := fun t ↦ by
  obtain ⟨hb, hnw, hap⟩ := h t
  have hnw' : (rodataAddr t).toNat + t.bytes.length ≤ 2 ^ 64 := hnw
  refine ⟨Arrays.bytesAt_congr hb fun i hi ↦ hs _ fun hr ↦ hR _ hr t
    (Arrays.inRange_add hnw' hi), hnw, apart_callee hS hsp hle hap⟩

/-- **A block writing in the frame below `lo`** (region 0) changes nothing outside the frame nor
the slots above `lo`. -/
theorem frame_write [Labels] {m0 st st' : MachineData} {F S lo : Nat} {S1 : SState}
    (hS : StackOk m0 S) (hF : F ≤ S) (hm : Match (Env.ofMachine st [(fbase m0 F, F)]) S1 st')
    (hwf : (Env.ofMachine st [(fbase m0 F, F)]).WF) (hw : ∀ w ∈ S1.mem, w.r = 0 ∧ w.off + w.n ≤ lo)
    (hlo : lo ≤ F) {slots : List (Nat × XReg)} (hsl : ∀ q ∈ slots, lo ≤ q.1 ∧ q.1 + 8 ≤ F) :
    (∀ p, ¬InRange (fbase m0 F) F p → st'.dmem.get? p = st.dmem.get? p) ∧
    (∀ q ∈ slots, ∀ i < 8, st'.dmem.get? (fbase m0 F + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i) =
      st.dmem.get? (fbase m0 F + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i)) := by
  have hnw : (fbase m0 F).toNat + F ≤ 2 ^ 64 := (frame_ok hS hF).2.1
  refine ⟨same_of_region hm hwf (r := 0) rfl fun w hw' ↦ ⟨(hw w hw').1, by
    have := (hw w hw').2; omega⟩, fun q hq i hi ↦ hm.get?_mem0 hwf ?_⟩
  rintro ⟨w, hw', b, sz, hb, h1, h2⟩
  obtain ⟨hr, hoff⟩ := hw w hw'
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨hq1, hq2⟩ := hsl q hq
  rw [NativeRustcVm.addr_add, Arrays.toNat_add_ofNat' (by omega)] at h1 h2
  omega

end

end NativeRustcVmArm.Layout
