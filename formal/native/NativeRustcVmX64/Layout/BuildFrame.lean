module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Spec.Arrays

/-!
# Function bodies with a frame and outputs (x86-64)

`Bd m0 F S slots R o d`: the frame (`Transcript.Frame`: RSP at its offset `o`, the pushed
registers in their slots, the return address, every byte kept) and memory changed only where `R`
holds (the outputs) or in the `S` bytes of stack. Made by the prologue (`Bd.entry`), kept by a
block (`Bd.of_block`: its writes in the frame below the return address or in regions inside `R`
or the stack), by a call (`Bd.call`); the epilogue returns (`Bd.done`). Registers a block keeps
(`Keeps`, `keeps_reg`), the callee's stack (`Bd.callee`).
-/

namespace NativeRustcVmX64.Layout.BuildFrame

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript

@[expose] public section

/-- **A body**: the frame, memory changed only where `R` holds or in the `S` bytes of stack. -/
structure Bd (m0 : MachineData) (F S : Nat) (slots : Slots) (R : BitVec 64 → Prop) (o : Nat)
    (d : MachineData) : Prop where
  fr : Frame m0 F slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem
    (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q)

/-- The registers `rs` are their atoms. -/
def Keeps (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- A block of one region (part of the frame): RSP and the callee-saved registers not in a slot
kept, every write within the region. -/
def SubOk (slots : Slots) (S : SState) : Bool :=
  keepsOthers slots S && S.reg .rsp == some (.reg .rsp) && writesIn S && S.mem.all (·.r == 0)

/-- A block of regions named by aliases: RSP and the callee-saved registers not in a slot kept,
every write within its region. -/
def AOk (slots : Slots) (S : SState) : Bool :=
  keepsOthers slots S && S.reg .rsp == some (.reg .rsp) && writesIn S

end

public section

theorem inRange_mono' {a q : BitVec 64} {k k' : Nat} (h : NativeRustcVm.InRange a k q)
    (hk : k ≤ k') : NativeRustcVm.InRange a k' q := by
  unfold NativeRustcVm.InRange at h ⊢; omega

theorem keeps_reg_some {Sy : SState} {rs : List Reg64} (h : Keeps Sy rs = true) {r : Reg64}
    (hr : r ∈ rs) : Sy.reg r = some (.reg r) := by
  have := List.all_eq_true.mp h r hr
  simpa using this

theorem keeps_reg [Labels] {env : Env} {Sy : SState} {m : MachineData} (hm : Match env Sy m)
    {rs : List Reg64} (h : Keeps Sy rs = true) {r : Reg64} (hr : r ∈ rs) :
    reg m r = env.regs r := by
  have := List.all_eq_true.mp h r hr
  simp only [beq_iff_eq] at this
  exact hm.regs r _ this

variable {m0 d d' : MachineData} {F S : Nat} {slots : Slots} {R : BitVec 64 → Prop}

/-- The frame's offset `j` as a number. -/
theorem off_fb_toNat (hst : StackOk m0 S) (hFS : F ≤ S) {j : Nat} (hj : j < F + 8) :
    (off (stackBelow m0 F) j).toNat = (rspOf m0).toNat - F + j := by
  have := hst.1; have := hst.2.1
  rw [toNat_off (by rw [stackBelow_toNat (by omega)]; omega), stackBelow_toNat (by omega)]

/-- The frame's region in a block's environment, well formed with `rest`. -/
theorem fr_wf {o : Nat} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hrest : ∀ x ∈ rest, NativeRustcVm.Mapped m0.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2)
    (hap : ((stackBelow m0 F, F + 8) :: rest).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2) :
    (frameEnv m0 d F rest vars ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped hst hFS) hb.fr.kept, frame_noWrap hst hFS⟩
    (fun x hx ↦ ⟨Mapped.keeps (hrest x hx).1 hb.fr.kept, (hrest x hx).2⟩) hap

theorem fr_wf0 {o : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (hFS : F ≤ S) :
    (frameEnv m0 d F [] vars ret).WF :=
  fr_wf hb hst hFS (by simp) (List.pairwise_singleton _ _)

theorem fr_wf1 {o : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64} {a : BitVec 64} {n : Nat}
    (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hma : NativeRustcVm.Mapped m0.dmem a n) (hna : NativeRustcVm.NoWrap a n)
    (hap : NativeRustcVm.Apart (stackBelow m0 F) (F + 8) a n) :
    (frameEnv m0 d F [(a, n)] vars ret).WF :=
  fr_wf hb hst hFS (by
    intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ⟨hma, hna⟩)
    (List.pairwise_pair.mpr hap)

variable [Labels]

/-- **A byte a block wrote** is in `R` or the stack: its writes in region 0 below `F`, those in
the other regions inside `R` or the stack. -/
theorem written_cover {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} (hst : StackOk m0 S) (hFS : F ≤ S) (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) Sy d') (hin : writesIn Sy = true)
    (hbr : belowRet F Sy = true)
    (hrest : ∀ x ∈ rest, ∀ q, NativeRustcVm.InRange x.1 x.2 q →
      R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q)
    {q : BitVec 64} (h : Written (frameEnv m0 d F rest vars ret) Sy q) :
    R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q := by
  obtain ⟨w, hw, b, sz, hb, j, hj1, hj2, rfl⟩ := written_off hwf h
  have hjs : j < sz := by
    unfold writesIn at hin
    rw [List.all_eq_true] at hin
    have hw' := hin w hw
    revert hw'
    cases hS : Sy.regions[w.r]? with
    | none => simp
    | some sz' =>
      intro hw'
      simp only [decide_eq_true_eq] at hw'
      obtain ⟨b', hb'⟩ := hm.regions _ _ hS
      rw [hb] at hb'
      cases hb'
      omega
  have hnw := hwf.noWrap _ b sz hb
  cases hr : w.r with
  | zero =>
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have := belowRet_spec hbr w hw hr
    exact Or.inr (inRange_frame_stack hst.2.1 hst.1 hFS (inRange_off_self (by omega) (by omega)))
  | succ i =>
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ] at hb
    exact hrest _ (List.mem_of_getElem? hb) _ (inRange_off_self hjs (by omega))

/-- A block keeps `SameOutside` of a body. -/
theorem same_step {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} (hst : StackOk m0 S) (hFS : F ≤ S) (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) Sy d') (hin : writesIn Sy = true)
    (hbr : belowRet F Sy = true)
    (hrest : ∀ x ∈ rest, ∀ q, NativeRustcVm.InRange x.1 x.2 q →
      R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q)
    (hsame : NativeRustcVm.SameOutside m0.dmem d.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q)) :
    NativeRustcVm.SameOutside m0.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q) :=
  fun q hq ↦ (hm.get?_mem0 hwf fun h ↦ hq (written_cover hst hFS hwf hm hin hbr hrest h)).trans
    (hsame q hq)

/-- **The prologue** makes a body. -/
theorem Bd.entry {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} {o : Nat} (hst : StackOk m0 S) (hFS : F ≤ S)
    (hwf : (frameEnv m0 m0 F rest vars ret).WF) (hm : Match (frameEnv m0 m0 F rest vars ret) Sy d')
    (hS : ProOk F o slots Sy = true) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hcs : ∀ p ∈ slots, calleeSaved p.2 = true)
    (hrest : ∀ x ∈ rest, ∀ q, NativeRustcVm.InRange x.1 x.2 q →
      R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q) :
    Bd m0 F S slots R o d' := by
  have hS' := hS
  simp only [ProOk, Bool.and_eq_true] at hS'
  exact ⟨Frame.of_prologue Frame.entry hwf hm hS hle hcs,
    same_step hst hFS hwf hm hS'.1.2 hS'.1.1.2 hrest fun _ _ ↦ rfl⟩

/-- A prologue may read additional regions while writing only its frame. -/
theorem Bd.entry_frame {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} {o : Nat} (hst : StackOk m0 S) (hFS : F ≤ S)
    (hwf : (frameEnv m0 m0 F rest vars ret).WF) (hm : Match (frameEnv m0 m0 F rest vars ret) Sy d')
    (hS : ProOk F o slots Sy = true) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hcs : ∀ p ∈ slots, calleeSaved p.2 = true)
    (hw : ∀ w ∈ Sy.mem, w.r = 0 ∧ w.off + w.n ≤ F) :
    Bd m0 F S slots R o d' :=
  ⟨Frame.of_prologue Frame.entry hwf hm hS hle hcs,
    (sameOutside_low hwf hm rfl (show F ≤ F + 8 by omega) hw).mono
      (fun _ h => Or.inr (inRange_frame_stack hst.2.1 hst.1 hFS h))⟩

/-- A block may read additional regions while writing only its frame. -/
theorem Bd.of_block_frame {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {Sy : SState} {o o' : Nat} (hb : Bd m0 F S slots R o d)
    (hst : StackOk m0 S) (hFS : F ≤ S)
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) Sy d')
    (hS : MidOk F o' slots Sy = true) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hw : ∀ w ∈ Sy.mem, w.r = 0 ∧ w.off + w.n ≤ F) :
    Bd m0 F S slots R o' d' := by
  refine ⟨Frame.of_block hb.fr hwf hm hS hle, ?_⟩
  have hs := sameOutside_low hwf hm rfl (show F ≤ F + 8 by omega) hw
  intro q hq
  exact (hs q (fun h => hq (Or.inr (inRange_frame_stack hst.2.1 hst.1 hFS h)))).trans
    (hb.same q hq)

/-- **A block** keeps a body. -/
theorem Bd.of_block {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} {o o' : Nat} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) Sy d')
    (hS : MidOk F o' slots Sy = true) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hrest : ∀ x ∈ rest, ∀ q, NativeRustcVm.InRange x.1 x.2 q →
      R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q) :
    Bd m0 F S slots R o' d' := by
  have hS' := hS
  simp only [MidOk, Bool.and_eq_true] at hS'
  exact ⟨Frame.of_block hb.fr hwf hm hS hle,
    same_step hst hFS hwf hm hS'.1.1.2 hS'.1.1.1.2 hrest hb.same⟩

/-- A block of the frame alone keeps a body. -/
theorem Bd.of_block0 {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} {o o' : Nat} (hb : Bd m0 F S slots R o d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hm : Match (frameEnv m0 d F [] vars ret) Sy d')
    (hS : MidOk F o' slots Sy = true) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) :
    Bd m0 F S slots R o' d' :=
  hb.of_block hst hFS (fr_wf0 hb hst hFS) hm hS hle (by simp)

/-- **A block writing nothing** keeps a body. -/
theorem Bd.of_read {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} {o o' : Nat} (hb : Bd m0 F S slots R o d)
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) Sy d')
    (hS : MidOk F o' slots Sy = true) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) (hmem : Sy.mem = []) :
    Bd m0 F S slots R o' d' :=
  ⟨Frame.of_block hb.fr hwf hm hS hle, by rw [hm.dmem_eq hwf hmem]; exact hb.same⟩

omit [Labels] in
/-- **A call** keeps a body where the callee changes bytes in `R` or the stack, but not the slots
or the return address. -/
theorem Bd.call (hb : Bd m0 F S slots R 0 d) (hs : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64)
    {Rc : BitVec 64 → Prop} (hso : NativeRustcVm.SameOutside d.dmem d'.dmem Rc)
    (hRc : ∀ q, Rc q → R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ Rc (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ Rc (off (stackBelow m0 F) (F + j))) : Bd m0 F S slots R 8 d' :=
  ⟨Frame.call_slots hb.fr hs hrsp hso hR hRr,
    fun q hq ↦ (hso q fun h ↦ hq (hRc q h)).trans (hb.same q hq)⟩

omit [Labels] in
/-- At a call: RSP the frame's base. -/
theorem Bd.rsp0 (hb : Bd m0 F S slots R 0 d) : rspOf d = stackBelow m0 F := by
  rw [hb.fr.sp, off_zero]

omit [Labels] in
/-- **The callee's stack**: inside the stack, apart from the frame. -/
theorem Bd.callee (hb : Bd m0 F S slots R 0 d) (hst : StackOk m0 S) {n' : Nat}
    (hn' : F + n' ≤ S) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow d n') n' q) :
    NativeRustcVm.InRange (stackBelow m0 S) S q ∧
      ¬ NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q :=
  inRange_callee hb.rsp0 hst.2.1 hst.1 hn' h

omit [Labels] in
theorem Bd.stackOk (hb : Bd m0 F S slots R 0 d) (hst : StackOk m0 S) {n' : Nat}
    (hn' : F + n' ≤ S) : StackOk d n' :=
  stackOk_callee hst hb.fr.kept hb.rsp0 hn'

omit [Labels] in
/-- A byte at offset `j` of the frame is in it. -/
theorem fb_in (hst : StackOk m0 S) (hFS : F ≤ S) {j : Nat} (hj : j < F + 8) :
    NativeRustcVm.InRange (stackBelow m0 F) (F + 8) (off (stackBelow m0 F) j) :=
  inRange_off_self hj (by have := frame_noWrap (F := F) hst hFS; unfold NativeRustcVm.NoWrap at this; omega)

omit [Labels] in
/-- **A call** whose callee changes only its stack and `Ro`, apart from the frame, keeps a body. -/
theorem Bd.call_apart (hb : Bd m0 F S slots R 0 d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hs : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64) {n' : Nat} (hn' : F + n' ≤ S)
    {Ro : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ Ro q ∨ NativeRustcVm.InRange (stackBelow d n') n' q))
    (hRo : ∀ q, Ro q → R q ∨ NativeRustcVm.InRange (stackBelow m0 S) S q)
    (hRof : ∀ q, Ro q → ¬ NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Bd m0 F S slots R 8 d' := by
  have hout : ∀ j < F + 8, ¬ (Ro (off (stackBelow m0 F) j) ∨
      NativeRustcVm.InRange (stackBelow d n') n' (off (stackBelow m0 F) j)) := by
    rintro j hj (h | h)
    · exact hRof _ h (fb_in hst hFS hj)
    · exact (hb.callee hst hn' h).2 (fb_in hst hFS hj)
  refine hb.call hs hrsp hso (fun q h ↦ ?_)
    (fun p hp i hi ↦ hout (p.1 + i) (by have := hle p hp; omega))
    (fun j hj ↦ hout (F + j) (by omega))
  rcases h with h | h
  · exact hRo q h
  · exact Or.inr (hb.callee hst hn' h).1

/-- **The bytes a block of one region wrote**: offsets of the region. -/
theorem sub_written {a : BitVec 64} {l : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} (hwf : (Env.ofMachine d [(a, l)] vars ret).WF)
    (hm : Match (Env.ofMachine d [(a, l)] vars ret) Sy d') (hS : SubOk slots Sy = true) {q : BitVec 64}
    (h : Written (Env.ofMachine d [(a, l)] vars ret) Sy q) : ∃ j, j < l ∧ q = off a j := by
  simp only [SubOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨-, hin⟩, hr0⟩ := hS
  obtain ⟨w, hw', b, sz, hb', j, hj1, hj2, rfl⟩ := written_off hwf h
  have hw0 : w.r = 0 := by simpa using List.all_eq_true.mp hr0 w hw'
  rw [hw0] at hb'
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  have hwl : w.off + w.n ≤ l := by
    have := List.all_eq_true.mp hin w hw'
    rw [hw0] at this
    revert this
    cases hS : Sy.regions[0]? with
    | none => simp
    | some sz' =>
      intro this
      simp only [decide_eq_true_eq] at this
      obtain ⟨b', hb'⟩ := hm.regions _ _ hS
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb'
      omega
  exact ⟨j, by omega, rfl⟩

/-- **A block of one region** changes memory only there. -/
theorem sub_same {a : BitVec 64} {l : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} (hwf : (Env.ofMachine d [(a, l)] vars ret).WF)
    (hm : Match (Env.ofMachine d [(a, l)] vars ret) Sy d') (hS : SubOk slots Sy = true) :
    NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange a l) := fun q hq ↦
  hm.get?_mem0 hwf fun h ↦ hq (by
    obtain ⟨j, hj, rfl⟩ := sub_written hwf hm hS h
    exact inRange_off_self hj (by have := hwf.noWrap 0 a l rfl; omega))

/-- **A byte a block wrote** is a byte of one of its written regions. -/
theorem written_in {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} (hwf : (Env.ofMachine d rs vars ret).WF)
    (hm : Match (Env.ofMachine d rs vars ret) Sy d') (hin : writesIn Sy = true) {q : BitVec 64}
    (h : Written (Env.ofMachine d rs vars ret) Sy q) :
    ∃ w ∈ Sy.mem, ∃ b sz, rs[w.r]? = some (b, sz) ∧ NativeRustcVm.InRange b sz q := by
  obtain ⟨w, hw', b, sz, hb', j, hj1, hj2, rfl⟩ := written_off hwf h
  refine ⟨w, hw', b, sz, hb', inRange_off_self (N := sz) ?_ (by
    have := hwf.noWrap _ b sz hb'; omega)⟩
  have := List.all_eq_true.mp hin w hw'
  revert this
  cases hS : Sy.regions[w.r]? with
  | none => simp
  | some sz' =>
    intro this
    simp only [decide_eq_true_eq] at this
    obtain ⟨b', hb''⟩ := hm.regions _ _ hS
    rw [hb'] at hb''
    cases hb''
    omega

/-- **A block of regions named by aliases** keeps a body: its writes in `R` (off the frame) or in
the frame's first `L` bytes, below the slots. -/
theorem Bd.of_written {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} {oo L : Nat} (hb : Bd m0 F S slots R oo d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hwf : (Env.ofMachine d rs vars ret).WF) (hm : Match (Env.ofMachine d rs vars ret) Sy d')
    (hS : AOk slots Sy = true) (hL : L ≤ F) (hsl : ∀ p ∈ slots, L ≤ p.1)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hW : ∀ q, Written (Env.ofMachine d rs vars ret) Sy q →
      (R q ∧ ¬ NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q) ∨
        NativeRustcVm.InRange (stackBelow m0 F) L q) :
    Bd m0 F S slots R oo d' := by
  simp only [AOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨hk, hsp⟩, -⟩ := hS
  have hnw := frame_noWrap (F := F) hst hFS
  unfold NativeRustcVm.NoWrap at hnw
  have hnot : ∀ j, L ≤ j → j < F + 8 →
      ¬ Written (Env.ofMachine d rs vars ret) Sy (off (stackBelow m0 F) j) := by
    intro j hj1 hj2 h
    rcases hW _ h with ⟨-, h'⟩ | h'
    · exact h' (inRange_off_self hj2 (by omega))
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), toNat_off (by omega)] at h'
      omega
  refine ⟨⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hb.fr.kept (hm.kept hwf),
    fun r hr hs ↦ ?_⟩, fun q hq ↦ ?_⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact hb.fr.sp
  · refine bytesAt_congr (hb.fr.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    have := hsl p hp
    have := hle p hp
    rw [off_add]
    exact hm.get?_mem0 hwf (hnot _ (by omega) (by omega))
  · rw [hm.get?_mem0 hwf (hnot _ (by omega) (by omega))]
    exact hb.fr.ret j hj
  · have := hm.regs r _ (keepsOthers_spec hk hr hs)
    rw [Sym.eval, Env.ofMachine_regs] at this
    exact this.trans (hb.fr.regs r hr hs)
  · refine (hm.get?_mem0 hwf fun h ↦ hq ?_).trans (hb.same q hq)
    rcases hW q h with ⟨h', -⟩ | h'
    · exact Or.inl h'
    · exact Or.inr (inRange_frame_stack hst.2.1 hst.1 hFS (inRange_mono' h' hL))

/-- **A block writing nothing** of regions named by aliases keeps a body. -/
theorem Bd.of_read' {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {Sy : SState} {oo : Nat} (hb : Bd m0 F S slots R oo d)
    (hwf : (Env.ofMachine d rs vars ret).WF) (hm : Match (Env.ofMachine d rs vars ret) Sy d')
    (hS : AOk slots Sy = true) (hmem : Sy.mem = []) : Bd m0 F S slots R oo d' := by
  simp only [AOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨hk, hsp⟩, -⟩ := hS
  have hd := hm.dmem_eq hwf hmem
  refine ⟨⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, ?_, fun r hr hs ↦ ?_⟩, ?_⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact hb.fr.sp
  · rw [hd]; exact hb.fr.slot p hp
  · rw [hd]; exact hb.fr.ret j hj
  · rw [hd]; exact hb.fr.kept
  · have := hm.regs r _ (keepsOthers_spec hk hr hs)
    rw [Sym.eval, Env.ofMachine_regs] at this
    exact this.trans (hb.fr.regs r hr hs)
  · rw [hd]; exact hb.same

/-- **A block of part of the frame**: from a state whose only region is the `l` bytes at offset `o`
of the frame, below the slots, keeping RSP and the callee-saved registers not in a slot. -/
theorem Bd.of_sub {o l L : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64} {Sy : SState}
    {oo : Nat} (hb : Bd m0 F S slots R oo d) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hwf : (Env.ofMachine d [(off (stackBelow m0 F) o, l)] vars ret).WF)
    (hm : Match (Env.ofMachine d [(off (stackBelow m0 F) o, l)] vars ret) Sy d')
    (hS : SubOk slots Sy = true) (hl : o + l ≤ L) (hL : L ≤ F) (hsl : ∀ p ∈ slots, L ≤ p.1)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Bd m0 F S slots R oo d' := by
  have hw : ∀ q, Written (Env.ofMachine d [(off (stackBelow m0 F) o, l)] vars ret) Sy q →
      ∃ j, o ≤ j ∧ j < o + l ∧ q = off (stackBelow m0 F) j := fun q h ↦ by
    obtain ⟨j, hj, rfl⟩ := sub_written hwf hm hS h
    exact ⟨o + j, by omega, by omega, off_off _ _ _⟩
  simp only [SubOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨hk, hsp⟩, -⟩, -⟩ := hS
  have hnw := frame_noWrap (F := F) hst hFS
  unfold NativeRustcVm.NoWrap at hnw
  have hnot : ∀ j, o + l ≤ j → j < F + 8 →
      ¬ Written (Env.ofMachine d [(off (stackBelow m0 F) o, l)] vars ret) Sy
        (off (stackBelow m0 F) j) := by
    intro j hj1 hj2 h
    obtain ⟨j', hj'1, hj'2, he⟩ := hw _ h
    have := off_inj (b := stackBelow m0 F) (N := F + 8) hnw (by omega) hj2 he
    omega
  refine ⟨⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hb.fr.kept (hm.kept hwf),
    fun r hr hs ↦ ?_⟩, fun q hq ↦ ?_⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact hb.fr.sp
  · refine bytesAt_congr (hb.fr.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    have := hsl p hp
    have := hle p hp
    rw [off_add]
    exact hm.get?_mem0 hwf (hnot _ (by omega) (by omega))
  · rw [hm.get?_mem0 hwf (hnot _ (by omega) (by omega))]
    exact hb.fr.ret j hj
  · have := hm.regs r _ (keepsOthers_spec hk hr hs)
    rw [Sym.eval, Env.ofMachine_regs] at this
    exact this.trans (hb.fr.regs r hr hs)
  · refine (hm.get?_mem0 hwf fun h ↦ hq (Or.inr ?_)).trans (hb.same q hq)
    obtain ⟨j, hj1, hj2, rfl⟩ := hw q h
    exact inRange_frame_stack hst.2.1 hst.1 hFS (inRange_off_self (by omega) (by omega))

end

public section

variable {m0 d d' : MachineData} {F S : Nat} {slots : Slots} {R : BitVec 64 → Prop}

/-- **The epilogue**: from a body, a block restoring the slots and returning reaches the entry's
return address with RSP 8 above the entry's, the callee-saved registers restored, memory kept. -/
theorem Bd.done [Host] {k : Nat} {ds : List Directive} {Sy Sy' : SState} {st : MachineState}
    {o : Nat} (hb : Bd m0 F S slots R o st.data) (hst : StackOk m0 S) (hFS : F ≤ S)
    (hk : ds.IsInfixAt Host.prog k) (hx : exec ds Sy = some (Sy', .ret (.load 0 F 8)))
    (hpc : st.pc = Host.addrOf k)
    (hm : Match (frameEnv m0 st.data F [] (fun _ ↦ 0) 0) Sy st.data)
    (hE : EpiOk F slots Sy' = true) (hmem : Sy'.mem = []) {Q : MachineState → Prop}
    (cont : ∀ st', Match (frameEnv m0 st.data F [] (fun _ ↦ 0) 0) Sy' st'.data →
      st'.pc = retOf m0 → rspOf st'.data = rspOf m0 + 8#64 → Saved m0 st'.data →
      st'.data.dmem = st.data.dmem → Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hwf := fr_wf0 (vars := fun _ ↦ 0) (ret := 0) hb hst hFS
  refine exec_at hk hx hwf nofun hpc hm fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hb.fr hwf hm' hE
  simp only [PcOk] at hpc'
  exact .done _ (cont st' hm' (by rw [hpc']; exact hb.fr.load_ret hst hFS) hrsp hsv
    (hm'.dmem_eq hwf hmem))

end

end NativeRustcVmX64.Layout.BuildFrame
