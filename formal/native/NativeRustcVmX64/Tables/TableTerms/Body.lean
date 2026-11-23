module

public import NativeRustcVmX64.Sumcheck.Ctx
public import NativeRustcVmX64.Sumcheck.Common

/-!
# Function bodies with a frame and outputs, calls at any offset (x86-64)

`Bd m0 F S slots R o d`: the frame (`Transcript.Frame`: RSP at its offset `o`, the pushed
registers in their slots, the return address, every byte kept) and memory changed only where `R`
holds (the outputs) or in the `S` bytes of stack below the entry's RSP. A block keeps it where its
writes are in the frame below the return address or in regions of outputs (`Bd.step`, `WrOk`); a
call at offset `o` keeps it where the callee changes neither a slot nor the return address
(`Bd.call_at`): the callee's stack is the function's below offset `o` (`Bd.stackOk_at`,
`Bd.callee_in`, `Bd.apart_at`), the frame from `o + 8` apart from it (`frame_apart_callee`). The
epilogue returns (`Bd.done`). A function passing stack arguments calls at offsets other than `0`.
-/

namespace NativeRustcVmX64.Tables.Body

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript

@[expose] public section

/-- **A body**: the frame, memory changed only where `R` holds or in the `S` bytes of stack. -/
structure Bd (m0 : MachineData) (F S : Nat) (slots : Slots) (R : BitVec 64 → Prop) (o : Nat)
    (d : MachineData) : Prop where
  fr : Frame m0 F slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem
    (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q)

/-- Each write of a block is in region `0` or in one of the regions `outs`. -/
def WrOk (Sy : SState) (outs : List Nat) : Bool :=
  Sy.mem.all fun w ↦ w.r == 0 || outs.contains w.r

/-- The registers `rs` are their atoms. -/
def Keeps (Sy : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ Sy.reg r == some (.reg r)

end

public section

theorem keeps_reg [Labels] {env : Env} {Sy : SState} {m : MachineData} (hm : Match env Sy m)
    {rs : List Reg64} (h : Keeps Sy rs = true) {r : Reg64} (hr : r ∈ rs) :
    reg m r = env.regs r := by
  have := List.all_eq_true.mp h r hr
  simp only [beq_iff_eq] at this
  exact hm.regs r _ this

/-- The frame's offset `o` is `F - o` below the entry's RSP. -/
theorem off_frame_eq {m0 : MachineData} {F o : Nat} (ho : o ≤ F) :
    off (stackBelow m0 F) o = stackBelow m0 (F - o) := by
  unfold stackBelow
  rw [off]
  have e : BitVec.ofNat 64 F = BitVec.ofNat 64 (F - o) + BitVec.ofNat 64 o := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel ho]
  rw [e]
  bv_omega

variable {m0 d d' : MachineData} {F S : Nat} {slots : Slots} {R : BitVec 64 → Prop}

theorem frame_wf' {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hst : StackOk m0 S) (hFS : F ≤ S) (hk : Kept m0.dmem d.dmem)
    (hrest : ∀ x ∈ rest, NativeRustcVm.Mapped m0.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2)
    (hap : ((stackBelow m0 F, F + 8) :: rest).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2) :
    (frameEnv m0 d F rest vars ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped hst hFS) hk, frame_noWrap hst hFS⟩
    (fun x hx ↦ ⟨Mapped.keeps (hrest x hx).1 hk, (hrest x hx).2⟩) hap

variable [Labels]

/-- A byte a block wrote: in a region, below its write's end. -/
theorem written_in {env : Env} {Sy : SState} (hwf : env.WF) (hm : Match env Sy d')
    (hin : writesIn Sy = true) {q : BitVec 64} (h : Written env Sy q) :
    ∃ w ∈ Sy.mem, ∃ b sz, env.regions[w.r]? = some (b, sz) ∧ w.off + w.n ≤ sz ∧
      ∃ j, j < w.off + w.n ∧ q = off b j := by
  obtain ⟨w, hw, b, sz, hb, j, hj1, hj2, rfl⟩ := written_off hwf h
  refine ⟨w, hw, b, sz, hb, ?_, j, hj2, rfl⟩
  unfold writesIn at hin
  have hw' := List.all_eq_true.mp hin w hw
  revert hw'
  cases hS : Sy.regions[w.r]? with
  | none => simp
  | some sz' =>
    intro hw'
    simp only [decide_eq_true_eq] at hw'
    obtain ⟨b', hb'⟩ := hm.regions _ _ hS
    rw [hb] at hb'
    cases hb'
    exact hw'

/-- **A byte a block wrote** is in `R` or the stack: its writes in region `0` below `F`, or in
regions `outs` of outputs. -/
theorem written_cover {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} (hst : StackOk m0 S) (hFS : F ≤ S) (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) Sy d') (hin : writesIn Sy = true)
    (hbr : belowRet F Sy = true) {outs : List Nat} (hW : WrOk Sy outs = true)
    (hR : ∀ r ∈ outs, ∀ x, rest[r - 1]? = some x → ∀ q, NativeRustcVm.InRange x.1 x.2 q → R q)
    {q : BitVec 64} (h : Written (frameEnv m0 d F rest vars ret) Sy q) :
    R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q := by
  obtain ⟨w, hw, b, sz, hb, hle, j, hj, rfl⟩ := written_in hwf hm hin h
  have hnw := hwf.noWrap _ b sz hb
  have hw' := List.all_eq_true.mp hW w hw
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hw'
  cases hr : w.r with
  | zero =>
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have := belowRet_spec hbr w hw hr
    exact Or.inr (inRange_frame_stack hst.2.1 hst.1 hFS (inRange_off_self (by omega) (by omega)))
  | succ i =>
    rw [hr] at hb hw'
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ] at hb
    rcases hw' with h0 | hmem
    · cases h0
    · exact Or.inl (hR _ hmem (b, sz) hb _ (inRange_off_self (by omega) (by omega)))

/-- **A block** keeps a body, its writes in the frame or output regions. -/
theorem Bd.step {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} {o o' : Nat} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) Sy d')
    (hS : MidOk F o' slots Sy = true) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) {outs : List Nat}
    (hW : WrOk Sy outs = true)
    (hR : ∀ r ∈ outs, ∀ x, rest[r - 1]? = some x → ∀ q, NativeRustcVm.InRange x.1 x.2 q → R q) :
    Bd m0 F S slots R o' d' := by
  have hS' := hS
  simp only [MidOk, Bool.and_eq_true] at hS'
  exact ⟨Frame.of_block hb.fr hwf hm hS hle, fun q hq ↦
    (hm.get?_mem0 hwf fun h ↦ hq (written_cover hst hFS hwf hm hS'.1.1.2 hS'.1.1.1.2 hW hR h)).trans
      (hb.same q hq)⟩

/-- A block's memory outside its writes, which are in the frame below `F` or in `outs`. -/
theorem same_block {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) Sy d') (hin : writesIn Sy = true)
    (hbr : belowRet F Sy = true) {outs : List Nat} (hW : WrOk Sy outs = true) {X : BitVec 64 → Prop}
    (hR : ∀ r ∈ outs, ∀ x, rest[r - 1]? = some x → ∀ q, NativeRustcVm.InRange x.1 x.2 q → X q) :
    NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 F) F q ∨ X q) := by
  intro q hq
  refine hm.get?_mem0 hwf fun h ↦ hq ?_
  obtain ⟨w, hw, b, sz, hb, hle, j, hj, rfl⟩ := written_in hwf hm hin h
  have hnw := hwf.noWrap _ b sz hb
  have hw' := List.all_eq_true.mp hW w hw
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hw'
  cases hr : w.r with
  | zero =>
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have := belowRet_spec hbr w hw hr
    exact Or.inl (inRange_off_self (by omega) (by omega))
  | succ i =>
    rw [hr] at hb hw'
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ] at hb
    rcases hw' with h0 | hmem
    · cases h0
    · exact Or.inr (hR _ hmem (b, sz) hb _ (inRange_off_self (by omega) (by omega)))

omit [Labels] in
/-- **A call at offset `o`** keeps a body where the callee changes bytes in `R` or the stack, but
not the slots or the return address. -/
theorem Bd.call_at {o : Nat} (hb : Bd m0 F S slots R o d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {Rc : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem Rc)
    (hRc : ∀ q, Rc q → R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ Rc (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ Rc (off (stackBelow m0 F) (F + j))) : Bd m0 F S slots R (o + 8) d' := by
  refine ⟨⟨by rw [hrsp, hb.fr.sp, off_add], fun p hp ↦ ?_, fun j hj ↦ ?_,
    kept_trans hb.fr.kept hs.2, fun r hr hsl ↦ (hs.1 r hr).trans (hb.fr.regs r hr hsl)⟩,
    fun q hq ↦ (hso q fun h ↦ hq (hRc q h)).trans (hb.same q hq)⟩
  · refine bytesAt_congr (hb.fr.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    exact hso _ (hR p hp i hi')
  · rw [hso _ (hRr j hj)]
    exact hb.fr.ret j hj

omit [Labels] in
/-- At a call at offset `o`: RSP `F - o` below the entry's. -/
theorem Bd.rsp_at {o : Nat} (hb : Bd m0 F S slots R o d) (ho : o ≤ F) :
    rspOf d = stackBelow m0 (F - o) := by
  rw [hb.fr.sp, off_frame_eq ho]

omit [Labels] in
/-- The callee's stack is fine. -/
theorem Bd.stackOk_at {o : Nat} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (ho : o ≤ F)
    {n' : Nat} (hn : F - o + n' ≤ S) : StackOk d n' :=
  stackOk_callee hst hb.fr.kept (hb.rsp_at ho) hn

omit [Labels] in
/-- **The callee's stack**: inside the function's, apart from the frame from offset `o`. -/
theorem Bd.callee_in {o : Nat} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (ho : o ≤ F)
    {n' : Nat} (hn : F - o + n' ≤ S) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow d n') n' q) :
    NativeRustcVm.InRange (stackBelow m0 S) S q ∧
      ¬ NativeRustcVm.InRange (off (stackBelow m0 F) o) (F - o + 8) q := by
  rw [off_frame_eq ho]
  exact inRange_callee (hb.rsp_at ho) hst.2.1 hst.1 hn h

omit [Labels] in
/-- What is apart from the stack is apart from a callee's at offset `o`. -/
theorem Bd.apart_at {o : Nat} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (ho : o ≤ F)
    {n' : Nat} (hn : F - o + n' ≤ S) {x : BitVec 64} {l : Nat}
    (h : NativeRustcVm.Apart x l (stackBelow m0 S) (S + 8)) :
    NativeRustcVm.Apart x l (stackBelow d n') (n' + 8) :=
  apart_callee h (hb.rsp_at ho) hst.1 hn

omit [Labels] in
/-- **The frame from offset `o + 8`** is apart from a callee's stack entered at offset `o`. -/
theorem frame_apart_callee {o : Nat} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S)
    (hFS : F ≤ S) (ho : o ≤ F) {n' : Nat} (hn : F - o + n' ≤ S) {j l : Nat} (hj : o + 8 ≤ j)
    (hjl : j + l ≤ F + 8) (hl : 0 < l) :
    NativeRustcVm.Apart (off (stackBelow m0 F) j) l (stackBelow d n') (n' + 8) := by
  have h1 := hst.1; have h2 := hst.2.1
  have hc : (stackBelow d n').toNat = (rspOf m0).toNat - (F - o + n') := by
    rw [stackBelow_callee (hb.rsp_at ho) (by omega), stackBelow_toNat (by omega)]
  have hf := stackBelow_toNat (m := m0) (n := F) (by omega)
  have ht : (off (stackBelow m0 F) j).toNat = (rspOf m0).toNat - F + j := by
    rw [toNat_off (by rw [hf]; omega), hf]
  unfold NativeRustcVm.Apart
  rw [ht, hc]
  omega

omit [Labels] in
/-- A byte of the frame from offset `o` is in the function's stack or is its return address. -/
theorem frame_in {j : Nat} (hst : StackOk m0 S) (hFS : F ≤ S) (hj : j < F + 8) :
    NativeRustcVm.InRange (stackBelow m0 F) (F + 8) (off (stackBelow m0 F) j) :=
  inRange_off_self hj (by have := frame_noWrap (F := F) hst hFS; unfold NativeRustcVm.NoWrap at this; omega)

omit [Labels] in
/-- **A call at offset `o`** whose callee changes only its stack and `Ro` apart from the frame. -/
theorem Bd.call_apart_at {o : Nat} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (ho : o ≤ F) (hs : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64) {n' : Nat}
    (hn : F - o + n' ≤ S) {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d n') n' q))
    (hRo : ∀ q, Ro q → R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q)
    (hRof : ∀ q, Ro q → ¬ NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q)
    (hle : ∀ p ∈ slots, o ≤ p.1 ∧ p.1 + 8 ≤ F) : Bd m0 F S slots R (o + 8) d' := by
  have hnw := frame_noWrap (F := F) hst hFS
  unfold NativeRustcVm.NoWrap at hnw
  have hout : ∀ j, o ≤ j → j < F + 8 → ¬ (Ro (off (stackBelow m0 F) j) ∨
      NativeRustcVm.InRange (stackBelow d n') n' (off (stackBelow m0 F) j)) := by
    rintro j hoj hj (h | h)
    · exact hRof _ h (frame_in hst hFS hj)
    · exact (hb.callee_in hst ho hn h).2 ((inRange_off_iff (by omega) (by omega)).mpr
        ⟨hoj, by omega⟩)
  refine hb.call_at hs hrsp hso (fun q h ↦ ?_)
    (fun p hp i hi ↦ hout (p.1 + i) (by have := hle p hp; omega) (by have := hle p hp; omega))
    (fun j hj ↦ hout (F + j) (by omega) (by omega))
  rcases h with h | h
  · exact hRo q h
  · exact Or.inr (hb.callee_in hst ho hn h).1

omit [Labels] in
/-- **A frame word kept by a call** at offset `o`, at an offset from `o + 8`, apart from `Ro`. -/
theorem keepW_call {o : Nat} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (ho : o ≤ F)
    {n' : Nat} (hn : F - o + n' ≤ S) {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d n') n' q))
    {j : Nat} (hj : o + 8 ≤ j) (hjF : j + 8 ≤ F + 8)
    (hRo : ∀ i < 8, ¬ Ro (off (stackBelow m0 F) (j + i))) {w : UInt64}
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 F) j) w) :
    NativeRustcVm.WordAt d'.dmem (off (stackBelow m0 F) j) w := by
  have hA := frame_apart_callee hb hst hFS ho hn hj hjF (by omega)
  have hst' := hb.stackOk_at hst ho hn
  have hnwc := noWrap_stackBelow hst'
  have hnw := frame_noWrap (F := F) hst hFS
  unfold NativeRustcVm.NoWrap at hnw
  refine NativeRustcVm.BytesAt.of_sameOutside h hso fun i hi hq ↦ ?_
  have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
  rw [off_add] at hq
  rcases hq with hq | hq
  · exact hRo i hi' hq
  · have hin : NativeRustcVm.InRange (off (stackBelow m0 F) j) 8 (off (stackBelow m0 F) (j + i)) := by
      rw [← off_add]; exact inRange_off_self hi' (by omega)
    exact not_inRange_of_apart hA (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega)
      hnwc hin (inRange_mono hq (by omega))

end

public section

variable {m0 : MachineData} {F S : Nat} {slots : Slots} {R : BitVec 64 → Prop}

/-- **The epilogue**: from a body, a block restoring the slots and returning reaches the entry's
return address with RSP 8 above the entry's, the callee-saved registers restored, memory kept. -/
theorem Bd.done [Host] {k : Nat} {ds : List Directive} {Sy Sy' : SState} {st : MachineState}
    {o : Nat} (hb : Bd m0 F S slots R o st.data) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hk : ds.IsInfixAt Host.prog k) (hx : exec ds Sy = some (Sy', .ret (.load 0 F 8)))
    (hpc : st.pc = Host.addrOf k)
    (hm : Match (frameEnv m0 st.data F [] (fun _ ↦ 0) 0) Sy st.data)
    (hE : EpiOk F slots Sy' = true) (hmem : Sy'.mem = []) {Q : MachineState → Prop}
    (cont : ∀ st', st'.pc = retOf m0 → rspOf st'.data = rspOf m0 + 8#64 → Saved m0 st'.data →
      st'.data.dmem = st.data.dmem → Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hwf : (frameEnv m0 st.data F [] (fun _ ↦ 0) 0).WF :=
    frame_wf' hst hFS hb.fr.kept (by simp) (List.pairwise_singleton _ _)
  refine exec_at hk hx hwf nofun hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hb.fr hwf hm' hE
  simp only [PcOk] at hpc'
  exact .done _ (cont st' (by rw [hpc']; exact hb.fr.load_ret hst hFS) hrsp hsv
    (hm'.dmem_eq hwf hmem))

/-- **The epilogue**, the final state's `Match` too. -/
theorem Bd.done' [Host] {k : Nat} {ds : List Directive} {Sy Sy' : SState} {st : MachineState}
    {o : Nat} (hb : Bd m0 F S slots R o st.data) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hk : ds.IsInfixAt Host.prog k) (hx : exec ds Sy = some (Sy', .ret (.load 0 F 8)))
    (hpc : st.pc = Host.addrOf k)
    (hm : Match (frameEnv m0 st.data F [] (fun _ ↦ 0) 0) Sy st.data)
    (hE : EpiOk F slots Sy' = true) (hmem : Sy'.mem = []) {Q : MachineState → Prop}
    (cont : ∀ st', Match (frameEnv m0 st.data F [] (fun _ ↦ 0) 0) Sy' st'.data →
      st'.pc = retOf m0 → rspOf st'.data = rspOf m0 + 8#64 → Saved m0 st'.data →
      st'.data.dmem = st.data.dmem → Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hwf : (frameEnv m0 st.data F [] (fun _ ↦ 0) 0).WF :=
    frame_wf' hst hFS hb.fr.kept (by simp) (List.pairwise_singleton _ _)
  refine exec_at hk hx hwf nofun hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hb.fr hwf hm' hE
  simp only [PcOk] at hpc'
  exact .done _ (cont st' hm' (by rw [hpc']; exact hb.fr.load_ret hst hFS) hrsp hsv
    (hm'.dmem_eq hwf hmem))

end

end NativeRustcVmX64.Tables.Body
