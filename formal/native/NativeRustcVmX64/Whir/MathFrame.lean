module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Got

/-!
# Frames, calls and outputs of `whir.rs`'s leaf functions (x86-64)

What the proofs of `fold_row`, `lanes_of`, `subspace_table`, `subspace_at_table`, `novel_eval`,
`induced_weight` and `glued_eval` share: the AArch64 `NativeRustcVmArm.Whir.MathFrame` on x86-64's
frames. Region 0 of a block's environment is the `F` bytes below the entry's RSP and the return
address at RSP (`stackBelow m0 F`, `F + 8` bytes; `F` the pushes, the frame and the 8-byte slot a
call pushes its return address in).

- `Frame m0 F S slots outs st`: the state `st` of a function's body entered in `m0`: RSP at the
  region's offset `8`, the pushed registers in their slots (`Arrays.SlotsAt`), the other
  callee-saved registers the entry's, memory as at the entry but in the outputs `outs` and the `S`
  bytes of stack (`ChangesIn`), every mapped byte still mapped. The prologue makes one
  (`Frame.of_entry`), a block keeps one (`Frame.of_block`, `Frame.of_write`, `Frame.change`), a
  block ending in a call and the call keep one (`Frame.call`; the callee's stack
  `stackOk_callee`, an argument apart from it `offStack_callee`), the epilogue returns with the
  entry's registers (`Frame.done`).
- Arguments a body reads: unchanged where apart from the outputs and the stack
  (`Frame.get?_arg`).
-/

namespace NativeRustcVmX64.Whir

open NativeRustcX64 NativeRustcX64.Sym
open NativeRustcVm (Region InAny wordOf)
open NativeRustcVmX64.Field (frameEnv frame_wf frame_noWrap frame_add frame_rsp load_ret frameS
  midS)
open NativeRustcVmX64.Arrays (SlotsAt slot_load calleeRegs mem_calleeRegs freeRegs free_mem
  keepsRegs keepsAll regs_eq_of restoredRegs restores find?_mem find?_none stackOk_mono
  inRange_stack stackBelow_toNat not_inRange_below not_inRange_above written_region0
  not_inRange_of_apart inSlots_false)

public section

/-! ## Addresses -/

/-- The `F` bytes below RSP and the return address, within the `S` the function may use. -/
theorem frame_ok {m : MachineData} {F S : Nat} (hS : StackOk m S) (hF : F ≤ S) :
    Mapped m.dmem (stackBelow m F) (F + 8) ∧ NoWrap (stackBelow m F) (F + 8) ∧
      (stackBelow m F).toNat = (rspOf m).toNat - F :=
  ⟨(stackOk_mono hS hF).2.2, frame_noWrap (stackOk_mono hS hF), stackBelow_toNat (by
    have := hS.1; omega)⟩

/-- The stack and the return address do not wrap. -/
theorem stack_noWrap {m : MachineData} {S : Nat} (hS : StackOk m S) :
    NoWrap (stackBelow m S) (S + 8) := frame_noWrap hS

/-- A byte of the frame is a byte of the stack's range, `S - F` further up. -/
theorem frame_addr {m : MachineData} {F S j : Nat} (hS : StackOk m S) (hF : F ≤ S) :
    stackBelow m F + BitVec.ofNat 64 j = stackBelow m S + BitVec.ofNat 64 (S - F + j) := by
  unfold stackBelow
  have h1 := hS.1
  apply BitVec.eq_of_toNat_eq
  have := (rspOf m).isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- A range apart from the stack (and the return address) holds no byte of the frame. -/
theorem not_inRange_frame {m : MachineData} {F S j : Nat} {a : BitVec 64} {n : Nat}
    (hS : StackOk m S) (hF : F ≤ S) (ho : OffStack m a n S) (hna : NoWrap a n) (hj : j < F + 8) :
    ¬InRange a n (stackBelow m F + BitVec.ofNat 64 j) := by
  rw [frame_addr hS hF]
  exact not_inRange_of_apart (Arrays.apart_symm ho) (stack_noWrap hS) hna (by omega)

/-- Outputs apart from the stack hold no byte of the frame. -/
theorem not_inAny_frame {m : MachineData} {F S j : Nat} {outs : List Region}
    (hS : StackOk m S) (hF : F ≤ S)
    (hout : ∀ r ∈ outs, OffStack m r.addr r.size S ∧ NoWrap r.addr r.size) (hj : j < F + 8) :
    ¬InAny outs (stackBelow m F + BitVec.ofNat 64 j) := fun ⟨r, hr, hp⟩ ↦
  not_inRange_frame hS hF (hout r hr).1 (hout r hr).2 hj hp

/-- The frame's first `L` bytes are among the `S` of stack. -/
theorem inRange_frame {m : MachineData} {F S L : Nat} {p : BitVec 64} (hS : StackOk m S)
    (hF : F ≤ S) (hL : L ≤ F) (h : InRange (stackBelow m F) L p) :
    InRange (stackBelow m S) S p :=
  inRange_stack (n := 0) (k := L) hS.1 (by omega) hL (by simpa using h)

/-! ## Sub-ranges of arguments -/

theorem Readable.sub {m : MachineData} {a : BitVec 64} {N o n : Nat} (h : Readable m a N)
    (hle : o + n ≤ N) : Readable m (a + BitVec.ofNat 64 o) n :=
  ⟨fun i hi ↦ by rw [addr_add]; exact h.1 _ (by omega), NativeRustcVm.NoWrap.sub h.2 hle⟩

theorem Readable.mono {m : MachineData} {a : BitVec 64} {N n : Nat} (h : Readable m a N)
    (hle : n ≤ N) : Readable m a n :=
  ⟨fun i hi ↦ h.1 i (by omega), NativeRustcVm.NoWrap.mono h.2 hle⟩

theorem OffStack.sub {m : MachineData} {a : BitVec 64} {N o n S : Nat} (h : OffStack m a N S)
    (hw : NoWrap a N) (hle : o + n ≤ N) : OffStack m (a + BitVec.ofNat 64 o) n S := by
  unfold OffStack Apart at *
  unfold NoWrap at hw
  rcases NativeRustcVm.toNat_add_ofNat_le (a := a) (i := o) (by omega) with h1 | ⟨h1, h2⟩ <;>
    rw [h1] <;> omega

theorem WhirIn.sub {m : MachineData} {a : BitVec 64} {N o n S : Nat} (h : WhirIn m a N S)
    (hle : o + n ≤ N) : WhirIn m (a + BitVec.ofNat 64 o) n S :=
  ⟨Readable.sub h.1 hle, OffStack.sub h.2 h.1.2 hle⟩

/-- A slice inside an argument: readable and apart from the stack. -/
theorem WhirIn.sliceOk {m : MachineData} {a : BitVec 64} {N o S : Nat} {n : BitVec 64}
    (h : WhirIn m a N S) (hle : o + 16 * n.toNat ≤ N) :
    SliceOk m (a + BitVec.ofNat 64 o) n S :=
  WhirIn.sub h hle

/-- An argument readable at the entry is readable where its bytes stayed mapped. -/
theorem Readable.keep {m m' : MachineData} {a : BitVec 64} {n : Nat} (h : Readable m a n)
    (hk : Kept m.dmem m'.dmem) : Readable m' a n :=
  ⟨fun i hi ↦ hk _ (h.1 i hi), h.2⟩

/-! ## A callee's stack -/

section
variable {m0 d : MachineData} {F S N : Nat}

/-- **A callee's `StackOk`**: its RSP the frame's base, every mapped byte kept. -/
theorem stackOk_callee (hS : StackOk m0 S) (hk : Kept m0.dmem d.dmem)
    (hsp : rspOf d = stackBelow m0 F) (hle : F + N ≤ S) : StackOk d N :=
  Transcript.stackOk_callee hS hk hsp hle

/-- An argument apart from the caller's stack is apart from a callee's. -/
theorem offStack_callee {a : BitVec 64} {n : Nat} (h : OffStack m0 a n S) (hS : StackOk m0 S)
    (hsp : rspOf d = stackBelow m0 F) (hle : F + N ≤ S) : OffStack d a n N :=
  Transcript.apart_callee h hsp hS.1 hle

theorem whirIn_callee {a : BitVec 64} {n : Nat} (h : WhirIn m0 a n S) (hS : StackOk m0 S)
    (hk : Kept m0.dmem d.dmem) (hsp : rspOf d = stackBelow m0 F) (hle : F + N ≤ S) :
    WhirIn d a n N :=
  ⟨Readable.keep h.1 hk, offStack_callee h.2 hS hsp hle⟩

theorem sliceOk_callee {a n : BitVec 64} (h : SliceOk m0 a n S) (hS : StackOk m0 S)
    (hk : Kept m0.dmem d.dmem) (hsp : rspOf d = stackBelow m0 F) (hle : F + N ≤ S) :
    SliceOk d a n N :=
  whirIn_callee h hS hk hsp hle

/-- **A callee's stack is inside its caller's**, below the frame. -/
theorem inRange_callee {p : BitVec 64} (hS : StackOk m0 S) (hsp : rspOf d = stackBelow m0 F)
    (hle : F + N ≤ S) (h : InRange (stackBelow d N) N p) : InRange (stackBelow m0 S) S p :=
  (Transcript.inRange_callee hsp hS.2.1 hS.1 hle h).1

/-- A frame byte is not one of a callee's stack. -/
theorem not_inRange_callee (hS : StackOk m0 S) (hsp : rspOf d = stackBelow m0 F)
    (hle : F + N ≤ S) {j : Nat} (hj : j < F + 8) :
    ¬InRange (stackBelow d N) N (stackBelow m0 F + BitVec.ofNat 64 j) := by
  unfold stackBelow
  rw [hsp]
  have := hS.1
  have := hS.2.1
  have := (rspOf m0).isLt
  exact not_inRange_below (by rw [stackBelow_toNat (by omega)]; omega)
    (by rw [stackBelow_toNat (by omega)]; omega)

end

/-! ## Changes -/

/-- `ChangesIn` is transitive, the second state's stack a callee's (its RSP the first's
`stackBelow m F`). -/
theorem ChangesIn.trans {m m' m'' : MachineData} {N N' f : Nat} {rs : List Region}
    (h : ChangesIn m m' N rs) (h' : ChangesIn m' m'' N' rs) (hS : StackOk m N)
    (hsp : rspOf m' = stackBelow m f) (hfN : f + N' ≤ N) : ChangesIn m m'' N rs := fun p hp ↦ by
  rw [h' p fun hp' ↦ hp (hp'.elim .inl fun hs ↦ .inr (inRange_callee hS hsp hfN hs))]
  exact h p hp

/-- A callee's stack changes, inside a caller's stack: a `ChangesIn` of the caller. -/
theorem ChangesIn.of_stack {m m' m'' : MachineData} {N N' f : Nat} {rs : List Region}
    (h : ChangesIn m m' N rs)
    (h' : SameOutside m'.dmem m''.dmem (InRange (stackBelow m' N') N')) (hS : StackOk m N)
    (hsp : rspOf m' = stackBelow m f) (hfN : f + N' ≤ N) : ChangesIn m m'' N rs := fun p hp ↦ by
  rw [h' p fun hs ↦ hp (.inr (inRange_callee hS hsp hfN hs))]
  exact h p hp

/-- `ChangesIn` with more regions. -/
theorem ChangesIn.mono {m m' : MachineData} {N : Nat} {rs rs' : List Region}
    (h : ChangesIn m m' N rs) (hr : ∀ r ∈ rs, r ∈ rs') : ChangesIn m m' N rs' :=
  fun p hp ↦ h p fun h' ↦ hp (h'.elim (fun hi ↦ .inl (hi.mono hr)) .inr)

theorem ChangesIn.refl (m : MachineData) (N : Nat) (rs : List Region) : ChangesIn m m N rs :=
  fun _ _ ↦ rfl

/-- Where every write of a block is in the first `len` bytes of region `r`, memory changes only
there. -/
theorem same_region_le [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz len : Nat} (hb : env.regions[r]? = some (b, sz))
    (hlen : len ≤ sz) (hall : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ len) :
    SameOutside env.mem0 m.dmem (InRange b len) := by
  refine fun p hp ↦ hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ hp ?_
  obtain ⟨hr, hle⟩ := hall w hw
  rw [hr, hb] at hb'
  cases hb'
  have := hwf.noWrap r b sz hb
  rw [Sym.inRange_iff (by omega)]
  omega

/-! ## The frame -/

/-- **A function's body**: RSP at offset `8` of the frame (region 0), the pushed registers in
their slots, the other callee-saved registers the entry's, memory as at the entry but in the
outputs `outs` and the `S` bytes of stack, every mapped byte still there. -/
structure Frame (m0 : MachineData) (F S : Nat) (slots : List (Nat × Reg64)) (outs : List Region)
    (st : MachineData) : Prop where
  rsp : rspOf st = stackBelow m0 F + BitVec.ofInt 64 8
  frame : SlotsAt st.dmem (stackBelow m0 F) m0 slots
  regs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → reg st r = reg m0 r
  same : ChangesIn m0 st S outs
  kept : Kept m0.dmem st.dmem

section
variable {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × Reg64)} {outs : List Region}

/-- The frame's environment of a body is well formed. -/
theorem Frame.wf {vars : Nat → BitVec 64} {ret : BitVec 64} (hb : Frame m0 F S slots outs st)
    (hS : StackOk m0 S) (hF : F ≤ S) : (frameEnv m0 st F vars ret).WF :=
  frame_wf (stackOk_mono hS hF) hb.kept

/-- A body in its frame environment, RSP at offset `8` (`Field.midS`). -/
theorem Frame.mid_match [Labels] {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hb : Frame m0 F S slots outs st) : Match (frameEnv m0 st F vars ret) (midS F) st :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial trivial

/-- A GOT call uses the existing frame plus one read-only loader slot. -/
@[expose] def gotMidS (F : Nat) (l : Label) : SState :=
  (init [F + 8, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot l, 1, 0)]).withKnownBytes
    1 0 8 (.label l)

@[expose] def gotEnv [Labels] (m0 st : MachineData) (F : Nat) (l : Label)
    (vars : Nat → BitVec 64 := fun _ => 0) (ret : BitVec 64 := 0) : Env :=
  Env.ofMachine st [(stackBelow m0 F, F + 8), (gotAddr l, 8)] vars ret

/-- GOT environments expose the same frame address, registers and backing memory. -/
theorem gotEnv_ptr [Labels] {m0 st : MachineData} {F : Nat} {l : Label}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (gotEnv m0 st F l vars ret) =
      stackBelow m0 F + BitVec.ofNat 64 o := by
  change stackBelow m0 F + BitVec.ofInt 64 (o : Int) = _
  rw [BitVec.ofInt_natCast]

theorem gotEnv_regs [Labels] {m0 st : MachineData} {F : Nat} {l : Label}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (r : Reg64) :
    (gotEnv m0 st F l vars ret).regs r = reg st r := by
  rfl

theorem gotEnv_mem0 [Labels] {m0 st : MachineData} {F : Nat} {l : Label}
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (gotEnv m0 st F l vars ret).mem0 = st.dmem := by
  rfl

/-- The original stack separation also separates a slot from the smaller symbolic frame. -/
theorem Frame.got_wf [Labels] {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    {l : Label} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) (hF : F ≤ S)
    (hg : GotAt m0 S areas symbols) (hl : l ∈ symbols) :
    (gotEnv m0 st F l vars ret).WF := by
  obtain ⟨hmap, hnw, hbase⟩ := frame_ok hS hF
  have hsbase := stackBelow_toNat hS.1
  have hgap : Apart (gotAddr l) 8 (stackBelow m0 F) (F + 8) :=
    NativeRustcVm.Apart.mono_right
      (show Apart (gotAddr l) 8 (stackBelow m0 S) (S + 8) from (hg.1 l hl).2.2.1)
      (by rw [hsbase, hbase]; omega) (by rw [hsbase, hbase]; have := hS.1; omega)
  exact Env.wf_of
    ⟨⟨fun i hi => hb.kept _ (hmap i hi), hnw⟩,
      ⟨fun i hi => hb.kept _ (hg.mapped hl i hi), (hg.1 l hl).2.1⟩, trivial⟩
    (List.pairwise_pair.mpr hgap.symm)

/-- The frame preserves loader bytes whenever its outputs are among the protected areas. -/
theorem Frame.got_byte [Labels] {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S)
    (hg : GotAt m0 S areas symbols) (hnw : ∀ a ∈ areas, NoWrap a.1 a.2)
    (hout : ∀ r ∈ outs, (r.addr, r.size) ∈ areas) {l : Label} (hl : l ∈ symbols)
    {i : Nat} (hi : i < 8) :
    st.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      some (byteOf (Labels.label l).toBitVec i) := by
  have heq := hg.unchanged hS hnw (fun p hp => hb.same p (fun h => hp (h.elim
    (fun ⟨r, hr, hin⟩ => Or.inr ⟨(r.addr, r.size), hout r hr, hin⟩) Or.inl)))
  exact (heq l hl i hi).trans (hg.byte hl hi)

/-- A slot's actual bytes seed the symbolic memory used by an indirect call. -/
theorem Frame.got_match [Labels] {l : Label} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hb : Frame m0 F S slots outs st)
    (hbytes : ∀ i < 8, st.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      some (byteOf (Labels.label l).toBitVec i)) :
    Match (gotEnv m0 st F l vars ret) (gotMidS F l) st := by
  have hm : Match (gotEnv m0 st F l vars ret)
      (init [F + 8, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot l, 1, 0)]) st :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial
      ⟨(BitVec.add_zero _).symm, trivial⟩
  apply hm.withKnownBytes
  intro i hi
  simpa [gotEnv, Env.base, Sym.eval] using hbytes i hi

/-- A stack-only body passes its loader slots to a callee whose data lies in that frame. -/
theorem Frame.got_after [Labels] {areas areas' : List (BitVec 64 × Nat)}
    {symbols : List Label} {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {T : SState} {d : MachineData} {N : Nat}
    (hb : Frame m0 F S slots [] st) (hS : StackOk m0 S) (hle : F + N ≤ S)
    (hg : GotAt m0 S areas symbols)
    (hwf : (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret).WF)
    (hm : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) T d)
    (hw : ∀ w ∈ T.mem, w.r = 0 ∧ w.off + w.n ≤ F)
    (hsp : rspOf d = stackBelow m0 F)
    (hcover : ∀ a ∈ areas', (stackBelow m0 F).toNat ≤ a.1.toNat ∧
      a.1.toNat + a.2 ≤ (stackBelow m0 F).toNat + F) :
    GotAt d N areas' symbols := by
  have hF : F ≤ S := by omega
  have hbase := (frame_ok hS hF).2.2
  have hsbase := stackBelow_toNat hS.1
  have hd : (stackBelow d N).toNat = (rspOf m0).toNat - F - N := by
    rw [stackBelow_toNat (by rw [hsp, hbase]; have := hS.1; omega), hsp, hbase]
  have hbytes := (hg.areas (areas' := []) (by simp)).unchanged hS (by simp)
    (fun p hp => by
      rw [hm.get?_mem0 hwf (fun h => hp (Or.inl
        (inRange_frame hS hF le_rfl (written_region0 rfl hwf (by omega) hw h))))]
      exact hb.same p (fun h => h.elim (fun ⟨_, hr, _⟩ => by cases hr)
        (fun h => hp (Or.inl h))))
  apply NativeRustcVmX64.GotAt.callee hg hbytes
  · rw [hsbase, hd]
    have := hS.1
    omega
  · rw [hsbase, hd]
    have := hS.1
    omega
  · intro a ha
    obtain ⟨hlo, hhi⟩ := hcover a ha
    refine ⟨(stackBelow m0 S, S + 8), List.mem_cons_self, ?_, ?_⟩ <;>
      rw [hsbase] <;> rw [hbase] at hlo hhi <;> have := hS.1 <;> omega

/-- **Bytes a body did not change**: outside the outputs and the stack. -/
theorem Frame.get?_eq (hb : Frame m0 F S slots outs st) {p : BitVec 64}
    (h : ¬(InAny outs p ∨ InRange (stackBelow m0 S) S p)) : st.dmem.get? p = m0.dmem.get? p :=
  hb.same p h

/-- **An argument's bytes in a body**: those of a region apart from the outputs and the
stack. -/
theorem Frame.get?_arg (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) {a : BitVec 64}
    {n : Nat} (hin : WhirIn m0 a n S)
    (hap : ∀ r ∈ outs, Apart a n r.addr r.size ∧ NoWrap r.addr r.size) :
    ∀ j < n, st.dmem.get? (a + BitVec.ofNat 64 j) = m0.dmem.get? (a + BitVec.ofNat 64 j) :=
  fun _ hj ↦ hb.get?_eq fun h ↦ h.elim
    (fun ⟨r, hr, hp⟩ ↦ not_inRange_of_apart (hap r hr).1 hin.1.2 (hap r hr).2 hj hp)
    (not_inRange_of_apart (Arrays.apart_mono hin.2 (Nat.le_add_right S 8)) hin.1.2
      (NativeRustcVm.NoWrap.mono (stack_noWrap hS) (by omega)) hj)

/-- An argument readable at the entry is readable in a body. -/
theorem Frame.readable (hb : Frame m0 F S slots outs st) {x : BitVec 64} {n : Nat}
    (h : Readable m0 x n) : Readable st x n :=
  Readable.keep h hb.kept

/-- **The entry block**: from the entry (`Field.frameS F`), the prologue's pushes in their slots,
the other callee-saved registers untouched, RSP at offset `8` make a body. -/
theorem Frame.of_entry [Labels] {vars : Nat → BitVec 64} {ret : BitVec 64} {S' : SState}
    (hS : StackOk m0 S) (hF : F ≤ S) (hm : Match (frameEnv m0 m0 F vars ret) S' st)
    (hsp : S'.reg .rsp = some (.ptr 0 8))
    (hw : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.1 + i) S'.mem = some (.reg p.2, i))
    (hregs : ∀ r ∈ freeRegs slots, S'.reg r = some (.reg r))
    (hmem : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F) : Frame m0 F S slots outs st := by
  have hSF := stackOk_mono hS hF
  have hwf := frame_wf (m := m0) (vars := vars) (ret := ret) hSF fun _ h ↦ h
  refine ⟨?_, fun p hp ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_, hm.kept hwf⟩
  · exact hm.regs .rsp _ hsp
  · exact hm.bytesAt_write (r := 0) rfl (by have := (hw p hp).1; omega) (hw p hp).2
  · exact hm.regs r _ (hregs r (free_mem hr hn))
  · refine hm.get?_mem0 hwf fun h ↦ hp (Or.inr ?_)
    have := written_region0 rfl hwf (Nat.le_add_right F 8) hmem h
    exact inRange_frame hS hF le_rfl this

/-- **A step of a body**: the next state keeps the free callee-saved registers, RSP and the mapped
bytes, and changes memory only in `R`, among the outputs and the stack and apart from the
slots. -/
theorem Frame.change (hb : Frame m0 F S slots outs st) {R : BitVec 64 → Prop}
    (hsame : SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → InAny outs p ∨ InRange (stackBelow m0 S) S p)
    (hfr : ∀ q ∈ slots, ∀ i < 8, ¬R (stackBelow m0 F + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i))
    (hregs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → reg st' r = reg st r)
    (hrsp : rspOf st' = rspOf st) (hkept : Kept st.dmem st'.dmem) :
    Frame m0 F S slots outs st' := by
  refine ⟨hrsp ▸ hb.rsp, fun q hq i hi ↦ ?_, fun r hr hn ↦ (hregs r hr hn).trans (hb.regs r hr hn),
    fun p hp ↦ ?_, fun p hp ↦ hkept p (hb.kept p hp)⟩
  · simp only [List.length_map, List.length_range] at hi
    rw [hsame _ (hfr q hq i hi)]
    exact hb.frame q hq i hi
  · rw [hsame p fun h ↦ hp (hR p h)]
    exact hb.same p hp

/-- **A block that writes nothing and keeps RSP and the free callee-saved registers** keeps a
body. -/
theorem Frame.of_block [Labels] {env : Env} {S₀ S₁ : SState} (hb : Frame m0 F S slots outs st)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsAll S₀ S₁ (freeRegs slots) = true) : Frame m0 F S slots outs st' := by
  unfold keepsAll at hk
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk
  obtain ⟨hr, hmem⟩ := hk
  have he := regs_eq_of hm₀ hm hr
  have hdm : st'.dmem = st.dmem := (hm.dmem_eq hwf hmem).trans hd.symm
  refine hb.change (R := fun _ ↦ False) (fun p _ ↦ by rw [hdm]) (fun _ h ↦ h.elim)
    (fun _ _ _ _ h ↦ h) (fun r hr' hn ↦ he r (List.mem_cons_of_mem _ (free_mem hr' hn)))
    (he .rsp (by simp)) (fun p h ↦ by rw [hdm]; exact h)

/-- **A block writing region `r`** keeps a body: it keeps RSP and the free callee-saved registers,
and writes into the first `len` bytes of region `r` only, a range among the outputs and the stack,
apart from the slots. -/
theorem Frame.of_write [Labels] {env : Env} {S₀ S₁ : SState} (hb : Frame m0 F S slots outs st)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsRegs S₀ S₁ (.rsp :: freeRegs slots) = true) {r : Nat} {a : BitVec 64} {n len : Nat}
    (hr : env.regions[r]? = some (a, n)) (hlen : len ≤ n)
    (hall : ∀ w ∈ S₁.mem, w.r = r ∧ w.off + w.n ≤ len)
    (hR : ∀ p, InRange a len p → InAny outs p ∨ InRange (stackBelow m0 S) S p)
    (hfr : ∀ q ∈ slots, ∀ i < 8,
      ¬InRange a len (stackBelow m0 F + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i)) :
    Frame m0 F S slots outs st' := by
  have he := regs_eq_of hm₀ hm hk
  refine hb.change (hd ▸ same_region_le hm hwf hr hlen hall) hR hfr
    (fun r' hr' hn ↦ he r' (List.mem_cons_of_mem _ (free_mem hr' hn))) (he .rsp (by simp))
    (hd ▸ hm.kept hwf)

/-- RSP after a block ending in a call: the frame's base. -/
theorem rsp_call [Labels] {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S₁ : SState} {d : MachineData}
    (hm : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ d)
    (hsp : S₁.reg .rsp = some (.ptr 0 0)) : rspOf d = stackBelow m0 F := by
  show d.regs.get64 .rsp = _
  rw [hm.regs .rsp _ hsp]
  simp [Sym.eval]

/-- **A block ending in a call, and the call**: from a body, a block that writes only the frame
(region 0) below offset `L` (the return address, locals below the pushed registers), keeps the
free callee-saved registers and leaves RSP at offset `0` calls a function of `N` bytes of stack,
which returns (`hQ`) with the callee-saved registers kept, changing only the outputs, the frame
below `L` and its stack: a body again. -/
theorem Frame.call [Host] {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (hspec : Spec (Labels.label l) P Q)
    {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S₀ S₁ : SState} {st1 : MachineState} {next : Int64} {R : MachineState → Prop} {L N : Nat}
    (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) (hle : F + N ≤ S) (hL : L ≤ F)
    (hslots : ∀ p ∈ slots, L ≤ p.1 ∧ p.1 + 8 ≤ F)
    (hout : ∀ r ∈ outs, OffStack m0 r.addr r.size S ∧ NoWrap r.addr r.size)
    (hwf : (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret).WF)
    (hm₀ : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₀ st)
    (hm : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ st1.data)
    (hpc : PcOk (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) (.call l) next st1)
    (hk : keepsRegs S₀ S₁ (freeRegs slots) = true)
    (hsp : S₁.reg .rsp = some (.ptr 0 0)) (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ L)
    (hP : P st1.data)
    (hQ : ∀ m', Q st1.data m' → Saved st1.data m' ∧ SameOutside st1.data.dmem m'.dmem
      (fun p ↦ InAny outs p ∨ InRange (stackBelow m0 F) L p ∨ InRange (stackBelow st1.data N) N p))
    (cont : ∀ st2 : MachineState, st2.pc = next → Frame m0 F S slots outs st2.data →
      Q st1.data st2.data → Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hr0 := (rspOf m0).isLt
  have hfb : (stackBelow m0 F).toNat = (rspOf m0).toNat - F := stackBelow_toNat (by omega)
  have hrsp1 := rsp_call hm hsp
  have hk1 : Kept m0.dmem st1.data.dmem := fun p h ↦ hm.kept hwf p (hb.kept p h)
  have hwr : ∀ p, Written (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ p →
      InRange (stackBelow m0 F) L p := fun p h ↦ written_region0 rfl hwf (by omega) hw h
  refine call_then hpc hspec hP fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hsaved, hsame⟩ := hQ _ hpost
  refine cont st2 hpc2 ⟨?_, fun p hp i hi ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_,
    fun p h ↦ hsaved.2 p (hk1 p h)⟩ hpost
  · rw [hrsp2, hrsp1]; rfl
  · simp only [List.length_map, List.length_range] at hi
    obtain ⟨hL', hF'⟩ := hslots p hp
    show st2.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) = _
    rw [addr_add, hsame _ ?_, hm.get?_mem0 hwf ?_]
    · rw [← addr_add]; exact hb.frame p hp i hi
    · exact fun h ↦ not_inRange_above (k := L) (by omega) (by omega) (hwr _ h)
    · rintro (h | h | h)
      · exact not_inAny_frame hS (by omega) hout (by omega) h
      · exact not_inRange_above (k := L) (by omega) (by omega) h
      · exact not_inRange_callee hS hrsp1 hle (by omega) h
  · exact (hsaved.1 r hr).trans ((regs_eq_of hm₀ hm hk r (free_mem hr hn)).trans
      (hb.regs r hr hn))
  · rw [hsame p fun h ↦ hp (h.elim .inl fun h ↦ .inr (h.elim (inRange_frame hS (by omega) hL)
      (inRange_callee hS hrsp1 hle))),
      hm.get?_mem0 hwf fun h ↦ hp (.inr (inRange_frame hS (by omega) hL (hwr p h)))]
    exact hb.same p hp

/-- **The epilogue**: run from a body in its frame environment, it returns to the entry's return
address with RSP 8 above the entry's and the entry's callee-saved registers, its memory the
body's. -/
theorem Frame.done [Labels] {vars : Nat → BitVec 64} {ret : BitVec 64} {S₁ : SState}
    {st' : MachineState} {next : Int64} (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S)
    (hF : F ≤ S) (hout : ∀ r ∈ outs, OffStack m0 r.addr r.size S ∧ NoWrap r.addr r.size)
    (hm : Match (frameEnv m0 st F vars ret) S₁ st'.data)
    (hpc : PcOk (frameEnv m0 st F vars ret) (.ret (.load 0 F 8)) next st')
    (hr : restores slots F S₁ = true) (hmem : S₁.mem = []) :
    st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧ st'.data.dmem = st.dmem ∧
      Saved m0 st'.data := by
  have hwf := hb.wf (vars := vars) (ret := ret) hS hF
  simp only [restores, Bool.and_eq_true, beq_iff_eq] at hr
  obtain ⟨hr, hsp⟩ := hr
  have hdm : st'.data.dmem = st.dmem := hm.dmem_eq hwf hmem
  refine ⟨?_, ?_, hdm, fun r hc ↦ ?_, fun p h ↦ ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    refine load_ret (stackOk_mono hS hF) fun j hj ↦ hb.same _ fun h ↦ ?_
    rw [show rspOf m0 + BitVec.ofNat 64 j = stackBelow m0 F + BitVec.ofNat 64 (F + j) from
      (frame_add F j).symm] at h
    rcases h with h | h
    · exact not_inAny_frame hS hF hout (by omega) h
    · revert h
      rw [frame_addr hS hF]
      have := stack_noWrap hS
      unfold NoWrap at this
      rw [Sym.inRange_iff (by omega), toNat_add_ofNat _ _ (by omega)]
      omega
  · show st'.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact frame_rsp F 8
  · simp only [restoredRegs, List.all_eq_true, beq_iff_eq] at hr
    have h := hm.regs r _ (hr r (mem_calleeRegs hc))
    cases hf : slots.find? (·.2 == r) with
    | some p =>
      obtain ⟨hp, rfl⟩ := find?_mem hf
      rw [hf] at h
      show st'.data.regs.get64 p.2 = _
      rw [h]
      exact slot_load (r := 0) hb.frame hp
    | none =>
      rw [hf] at h
      show st'.data.regs.get64 r = _
      rw [h]
      exact hb.regs r hc (find?_none hf)
  · rw [hdm]; exact hb.kept p h

end

/-! ## Values the executor computes -/

/-- An unsigned comparison with a literal. -/
theorem ult_ofNat {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64) :
    x.ult (BitVec.ofNat 64 n) = decide (x.toNat < n) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv_beq_toNat (a b : BitVec 64) : (a == b) = decide (a.toNat = b.toNat) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [beq_eq_false_iff_ne.mpr h]
    exact (decide_eq_false fun h' ↦ h (BitVec.eq_of_toNat_eq h')).symm

theorem bv_ult_toNat (a b : BitVec 64) : a.ult b = decide (a.toNat < b.toNat) := rfl

/-- **Bytes a block kept**: in region `r`, a range no write of the block touches. -/
theorem Match.keep [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    {o len : Nat} (hle : o + len ≤ sz)
    (hall : ∀ w ∈ S.mem, w.r = r ∧ (w.off + w.n ≤ o ∨ o + len ≤ w.off)) :
    ∀ i < len, m.dmem.get? (b + BitVec.ofNat 64 (o + i)) =
      env.mem0.get? (b + BitVec.ofNat 64 (o + i)) := by
  intro i hi
  refine hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ ?_
  obtain ⟨hr, hoff⟩ := hall w hw
  rw [hr, hb] at hb'
  cases hb'
  have hnw := hwf.noWrap r b sz hb
  rw [toNat_add_ofNat _ _ (by omega)] at h1 h2
  omega

end

end NativeRustcVmX64.Whir
