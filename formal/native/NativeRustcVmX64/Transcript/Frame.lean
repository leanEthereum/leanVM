module

public import NativeRustcVmX64.Transcript.Glue
public import NativeRustcVmX64.Spec.Transcript
public import NativeRustcVmX64.Basic
public import NativeRustcX64.Got

/-!
# A function's frame, through its blocks and calls (x86-64)

Region 0 of a block's environment (`frameEnv`) is the `F` bytes below the entry's RSP and the
return address at RSP (`stackBelow m0 F`, `F + 8` bytes). A function pushes callee-saved registers
into it at the offsets `slots`, keeps RSP at an offset `o` of it between its prologue and
epilogue (`8` in its body, `0` at a call: the call pushes its return address at offset `0`), and
pops them on return. `Frame m0 F slots o d` says the machine state `d` has RSP at offset `o`, the
slots holding the entry's registers, the return address the entry's, the other callee-saved
registers the entry's, every byte of the entry's memory kept.

- the entry is one (`Frame.entry`, no slots, RSP at `F`);
- the prologue establishes it (`Frame.of_prologue`, its block checked by `ProOk`);
- a block keeps it (`Frame.of_block`, by `MidOk`: the other callee-saved registers kept, no write
  over a slot or the return address, every write within its region);
- a call keeps it where the callee changes no byte of the frame (`Frame.call`, `Frame.call_slots`);
- the epilogue restores the registers and returns (`Frame.epilogue`, by `EpiOk`; `Frame.load_ret`).

Then the callee's stack below the frame (`stackOk_callee`, `apart_callee`, `inRange_callee`,
`RcAt.callee`).
-/

namespace NativeRustcVmX64.Transcript

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Transcript

@[expose] public section

/-- The slots: each saved register's offset in the frame. -/
abbrev Slots := List (Nat × Reg64)

/-- The callee-saved registers not in a slot are their atoms. -/
def keepsOthers (slots : Slots) (S : SState) : Bool :=
  allRegs.all fun r => !calleeSaved r || slots.any (·.2 == r) || S.reg r == some (.reg r)

/-- Each slot holds its register's atom. -/
def slotsWritten (slots : Slots) (S : SState) : Bool :=
  slots.all fun p => (List.range 8).all fun t => findWrite 0 (p.1 + t) S.mem == some (.reg p.2, t)

/-- No write into region 0 overlaps a slot. -/
def slotsUntouched (slots : Slots) (S : SState) : Bool :=
  S.mem.all fun w => w.r != 0 || slots.all fun p => w.off + w.n ≤ p.1 || p.1 + 8 ≤ w.off

/-- Every write into region 0 is below its offset `F` (the return address). -/
def belowRet (F : Nat) (S : SState) : Bool :=
  S.mem.all fun w => w.r != 0 || decide (w.off + w.n ≤ F)

/-- Each slot's register is loaded from it. -/
def slotsLoaded (slots : Slots) (S : SState) : Bool :=
  slots.all fun p => S.reg p.2 == some (.load 0 p.1 8)

/-- Every write is within its region. -/
def writesIn (S : SState) : Bool :=
  S.mem.all fun w => match S.regions[w.r]? with
    | some sz => decide (w.off + w.n ≤ sz)
    | none => false

/-- A prologue's end, RSP at offset `o`. -/
def ProOk (F o : Nat) (slots : Slots) (S : SState) : Bool :=
  slotsWritten slots S && keepsOthers slots S && belowRet F S && writesIn S &&
    S.reg .rsp == some (.ptr 0 (o : Int))

/-- A block in the frame's body, RSP at offset `o` at its end. -/
def MidOk (F o : Nat) (slots : Slots) (S : SState) : Bool :=
  slotsUntouched slots S && belowRet F S && writesIn S && keepsOthers slots S &&
    S.reg .rsp == some (.ptr 0 (o : Int))

/-- An epilogue's end: the slots popped, RSP above the return address. -/
def EpiOk (F : Nat) (slots : Slots) (S : SState) : Bool :=
  slotsLoaded slots S && keepsOthers slots S && S.reg .rsp == some (.ptr 0 ((F + 8 : Nat) : Int))

/-- A block's environment: region 0 the frame and the return address, then `rest`. -/
abbrev frameEnv (m0 d : MachineData) (F : Nat) (rest : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64 := fun _ ↦ 0) (ret : BitVec 64 := 0) : Env :=
  Env.ofMachine d ((stackBelow m0 F, F + 8) :: rest) vars ret

/-- **The frame**: RSP at its offset `o`, the slots holding the entry's registers, the return
address the entry's, the other callee-saved registers the entry's, the entry's bytes kept. -/
structure Frame (m0 : MachineData) (F : Nat) (slots : Slots) (o : Nat) (d : MachineData) :
    Prop where
  sp : rspOf d = off (stackBelow m0 F) o
  slot : ∀ p ∈ slots,
    NativeRustcVm.WordAt d.dmem (off (stackBelow m0 F) p.1) (UInt64.ofBitVec (reg m0 p.2))
  ret : ∀ j < 8, d.dmem.get? (off (stackBelow m0 F) (F + j)) =
    m0.dmem.get? (off (stackBelow m0 F) (F + j))
  kept : Kept m0.dmem d.dmem
  regs : ∀ r, calleeSaved r = true → slots.any (·.2 == r) = false → reg d r = reg m0 r

end

public section

theorem kept_trans {a b c : DataMem} (h₁ : Kept a b) (h₂ : Kept b c) : Kept a c :=
  fun p hp ↦ h₂ p (h₁ p hp)

theorem keepsOthers_spec {slots : Slots} {S : SState} (h : keepsOthers slots S = true) {r : Reg64}
    (hr : calleeSaved r = true) (hs : slots.any (·.2 == r) = false) : S.reg r = some (.reg r) := by
  unfold keepsOthers at h
  rw [List.all_eq_true] at h
  have := h r (mem_allRegs r)
  simp only [hr, hs, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

variable {m0 d d' : MachineData} {F n : Nat} {slots : Slots}

/-- `F + j` above the frame's base is `j` above RSP. -/
theorem frame_add (F j : Nat) : off (stackBelow m0 F) (F + j) = rspOf m0 + BitVec.ofNat 64 j := by
  rw [off, stackBelow, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem off_frame_F : off (stackBelow m0 F) F = rspOf m0 := by
  have := frame_add (m0 := m0) F 0
  rw [Nat.add_zero] at this
  simpa using this

theorem eval_ptr0 [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (o : Nat) : (Sym.ptr 0 (o : Int)).eval (frameEnv m0 d F rest vars ret) =
      off (stackBelow m0 F) o := by
  show (frameEnv m0 d F rest vars ret).base 0 + BitVec.ofInt 64 (o : Int) = _
  rw [BitVec.ofInt_natCast]
  rfl

theorem frame_noWrap (h : StackOk m0 n) (hF : F ≤ n) :
    NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8) := by
  unfold NativeRustcVm.NoWrap
  rw [stackBelow_toNat (by have := h.1; omega)]
  have := h.1
  have := h.2.1
  omega

theorem stack_noWrap (h : StackOk m0 n) : NativeRustcVm.NoWrap (stackBelow m0 n) n :=
  (noWrap_stackBelow h).mono (by omega)

/-- The frame is mapped. -/
theorem frame_mapped (h : StackOk m0 n) (hF : F ≤ n) :
    NativeRustcVm.Mapped m0.dmem (stackBelow m0 F) (F + 8) := by
  intro i hi
  have e : stackBelow m0 F + BitVec.ofNat 64 i =
      stackBelow m0 n + BitVec.ofNat 64 (n - F + i) := by
    apply BitVec.eq_of_toNat_eq
    have := h.1
    have := h.2.1
    have h1 := stackBelow_toNat (m := m0) (n := F) (by omega)
    have h2 := stackBelow_toNat (m := m0) (n := n) (by omega)
    rw [NativeRustcVm.toNat_add_ofNat (a := stackBelow m0 F) (i := i) (by omega),
      NativeRustcVm.toNat_add_ofNat (a := stackBelow m0 n) (i := n - F + i) (by omega), h1, h2]
    omega
  rw [e]
  exact h.2.2 _ (by omega)

/-- The frame's environment is well formed, with `rest` mapped, not wrapping, and pairwise apart
from each other and the frame. -/
theorem frame_wf {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hok : NativeRustcVm.Mapped d.dmem (stackBelow m0 F) (F + 8) ∧
      NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8))
    (hrest : ∀ x ∈ rest, NativeRustcVm.Mapped d.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2)
    (hap : ((stackBelow m0 F, F + 8) :: rest).Pairwise
      fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2) :
    (frameEnv m0 d F rest vars ret).WF where
  noWrap r b k hb := by
    cases r with
    | zero => cases hb; exact hok.2
    | succ r => exact (hrest _ (List.mem_of_getElem? hb)).2
  mapped r b k hb := by
    cases r with
    | zero => cases hb; exact hok.1
    | succ r => exact (hrest _ (List.mem_of_getElem? hb)).1
  disjoint r r' b b' k k' hne hb hb' := by
    have := List.pairwise_iff_getElem.mp hap
    simp only [Env.ofMachine_regions] at hb hb'
    obtain ⟨hr, hbr⟩ := List.getElem?_eq_some_iff.mp hb
    obtain ⟨hr', hbr'⟩ := List.getElem?_eq_some_iff.mp hb'
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := this r r' hr hr' h
      rw [hbr, hbr'] at this
      unfold NativeRustcVm.Apart at this
      exact this
    · have := this r' r hr' hr h
      rw [hbr, hbr'] at this
      unfold NativeRustcVm.Apart at this
      dsimp only at this
      omega

variable [Labels]

/-- A byte of region 0 no write of a block covers, where every write into region 0 misses it and
every write is within its region. -/
theorem not_written0 {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : SState} (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hin : writesIn S = true) {j : Nat}
    (hj : j < F + 8) (hmiss : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ j ∨ j < w.off) :
    ¬ Written (frameEnv m0 d F rest vars ret) S (off (stackBelow m0 F) j) := by
  rintro ⟨w, hw, b, sz, hb, h1, h2⟩
  have hnw0 := hwf.noWrap 0 (stackBelow m0 F) (F + 8) rfl
  have hq : (off (stackBelow m0 F) j).toNat = (stackBelow m0 F).toNat + j := toNat_off (by omega)
  rw [hq] at h1 h2
  by_cases hr : w.r = 0
  · rw [hr] at hb
    cases hb
    rcases hmiss w hw hr with h | h <;> omega
  · unfold writesIn at hin
    rw [List.all_eq_true] at hin
    have hw' := hin w hw
    obtain ⟨sz', hS'⟩ : ∃ sz', S.regions[w.r]? = some sz' := by
      revert hw'
      cases S.regions[w.r]? with
      | none => simp
      | some x => exact fun _ ↦ ⟨x, rfl⟩
    rw [hS'] at hw'
    simp only [decide_eq_true_eq] at hw'
    obtain ⟨b', hb'⟩ := hm.regions _ _ hS'
    rw [hb] at hb'
    cases hb'
    have := hwf.disjoint 0 w.r _ _ _ _ (Ne.symm hr) rfl hb
    omega

omit [Labels] in
theorem belowRet_spec {S : SState} (h : belowRet F S = true) :
    ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ F := by
  intro w hw hr
  unfold belowRet at h
  rw [List.all_eq_true] at h
  have := h w hw
  simp only [hr, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at this
  exact this

omit [Labels] in
theorem slotsUntouched_spec {S : SState} (h : slotsUntouched slots S = true) :
    ∀ w ∈ S.mem, w.r = 0 → ∀ p ∈ slots, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off := by
  intro w hw hr p hp
  unfold slotsUntouched at h
  rw [List.all_eq_true] at h
  have := h w hw
  simp only [hr, bne_self_eq_false, Bool.false_or, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at this
  exact this p hp

/-- RSP at the entry, as region 0's offset `F`. -/
theorem match_rsp {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} :
    m0.regs.get64 .rsp = (Sym.ptr 0 (F : Int)).eval (frameEnv m0 d F rest vars ret) := by
  rw [eval_ptr0, off_frame_F]
  rfl

/-- RSP in a frame, as region 0's offset `o`. -/
theorem Frame.rsp_eval {o : Nat} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hf : Frame m0 F slots o d) :
    d.regs.get64 .rsp = (Sym.ptr 0 (o : Int)).eval (frameEnv m0 d F rest vars ret) := by
  rw [eval_ptr0]
  exact hf.sp

omit [Labels] in
/-- A state with the entry's RSP, return address and callee-saved registers, and its bytes kept:
a frame without slots (a leaf function's, before its `ret`). -/
theorem Frame.of_saved (hs : Saved m0 d) (hsp : rspOf d = rspOf m0)
    (hret : ∀ j < 8, d.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)) : Frame m0 F [] F d :=
  ⟨hsp.trans off_frame_F.symm, nofun, fun j hj ↦ by rw [frame_add]; exact hret j hj, hs.2,
    fun r hr _ ↦ hs.1 r hr⟩

omit [Labels] in
/-- The entry is a frame without slots, RSP at offset `F`. -/
theorem Frame.entry : Frame m0 F [] F m0 :=
  ⟨off_frame_F.symm, nofun, fun _ _ ↦ rfl, fun _ h ↦ h, fun _ _ _ ↦ rfl⟩

/-- **The prologue** establishes the frame, from one without slots (the entry's, `Frame.entry`),
pushing callee-saved registers. -/
theorem Frame.of_prologue {d' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} {o o' : Nat}
    (hf : Frame m0 F [] o d) (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hS : ProOk F o' slots S = true)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) (hcs : ∀ p ∈ slots, calleeSaved p.2 = true) :
    Frame m0 F slots o' d' := by
  simp only [ProOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨hw, hk⟩, hbr⟩, hin⟩, hsp⟩ := hS
  refine ⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept (hm.kept hwf), fun r hr hs ↦ ?_⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0]
  · unfold slotsWritten at hw
    rw [List.all_eq_true] at hw
    have hp' := hw p hp
    rw [List.all_eq_true] at hp'
    have := wordAt_write hm (r := 0) (o := p.1) rfl (by have := hle p hp; omega) (v := .reg p.2)
      fun t ht ↦ by
        have := hp' t (List.mem_range.mpr ht)
        simpa using this
    rwa [show (Sym.reg p.2).eval (frameEnv m0 d F rest vars ret) = reg m0 p.2 from
      hf.regs p.2 (hcs p hp) rfl] at this
  · rw [hm.get?_mem0 hwf (not_written0 hwf hm hin (by omega) fun w hw hr ↦ ?_)]
    · exact hf.ret j hj
    · have := belowRet_spec hbr w hw hr
      omega
  · exact (hm.regs r _ (keepsOthers_spec hk hr hs)).trans (hf.regs r hr rfl)

/-- **A block** keeps the frame. -/
theorem Frame.of_block {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {o o' : Nat} (hf : Frame m0 F slots o d)
    (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hS : MidOk F o' slots S = true)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Frame m0 F slots o' d' := by
  simp only [MidOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨hu, hbr⟩, hin⟩, hk⟩, hsp⟩ := hS
  refine ⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept (hm.kept hwf), fun r hr hs ↦ ?_⟩
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0]
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    refine (hm.get?_mem0 hwf (not_written0 hwf hm hin (by have := hle p hp; omega)
      fun w hw hr ↦ ?_))
    have := slotsUntouched_spec hu w hw hr p hp
    omega
  · rw [hm.get?_mem0 hwf (not_written0 hwf hm hin (by omega) fun w hw hr ↦ ?_)]
    · exact hf.ret j hj
    · have := belowRet_spec hbr w hw hr
      omega
  · have := hm.regs r _ (keepsOthers_spec hk hr hs)
    rw [Sym.eval, Env.ofMachine_regs] at this
    exact this.trans (hf.regs r hr hs)

omit [Labels] in
/-- **A call** keeps the frame where the callee changes none of its slots' or the return
address's bytes (it may write an output elsewhere in the frame). -/
theorem Frame.call_slots (hf : Frame m0 F slots 0 d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ R (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ R (off (stackBelow m0 F) (F + j))) : Frame m0 F slots 8 d' := by
  refine ⟨?_, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hs.2, fun r hr hsl ↦ ?_⟩
  · rw [hrsp, hf.sp, off_zero]
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    exact hso _ (hR p hp i hi')
  · rw [hso _ (hRr j hj)]
    exact hf.ret j hj
  · exact (hs.1 r hr).trans (hf.regs r hr hsl)

omit [Labels] in
/-- **A call** keeps the frame where the callee changes none of its bytes. -/
theorem Frame.call (hf : Frame m0 F slots 0 d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q)
    (hnw : NativeRustcVm.NoWrap (stackBelow m0 F) (F + 8)) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) :
    Frame m0 F slots 8 d' :=
  Frame.call_slots hf hs hrsp hso
    (fun p hp i hi h ↦ hR _ h (inRange_off_self (by have := hle p hp; omega) (by unfold NativeRustcVm.NoWrap at hnw; omega)))
    (fun j hj h ↦ hR _ h (inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hnw; omega)))

omit [Labels] in
/-- The return address, loaded from the frame. -/
theorem Frame.load_ret {o : Nat} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} (hf : Frame m0 F slots o d) (h : StackOk m0 n) (hF : F ≤ n) :
    Int64.ofBitVec ((frameEnv m0 d F rest vars ret).load 0 F 8) = retOf m0 := by
  have hget : ∀ j < 8, m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      some ((m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)).getD 0) := fun j hj ↦ by
    have := frame_mapped h hF (F + j) (by omega)
    rw [show stackBelow m0 F + BitVec.ofNat 64 (F + j) = off (stackBelow m0 F) (F + j) from rfl,
      frame_add] at this
    revert this
    cases m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) <;> simp
  rw [retOf, loadInt_of_get? _ _ 8 _ hget, Option.getD_some]
  unfold Env.load
  congr 3
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [show (frameEnv m0 d F rest vars ret).base 0 = stackBelow m0 F from rfl, Env.ofMachine_mem0,
    show stackBelow m0 F + BitVec.ofNat 64 (F + j) = off (stackBelow m0 F) (F + j) from rfl,
    hf.ret j hj, frame_add]

/-- **The epilogue** restores the registers: `Saved`, RSP 8 above the entry's. -/
theorem Frame.epilogue {o : Nat} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hf : Frame m0 F slots o d)
    (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hS : EpiOk F slots S = true) :
    Saved m0 d' ∧ rspOf d' = rspOf m0 + 8#64 := by
  simp only [EpiOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨hl, hk⟩, hsp⟩ := hS
  have hslot : ∀ p ∈ slots, reg d' p.2 = reg m0 p.2 := by
    intro p hp
    unfold slotsLoaded at hl
    rw [List.all_eq_true] at hl
    have := hm.regs p.2 _ (by simpa using hl p hp)
    rw [Sym.eval, load_ofMachine (o := p.1) rfl (hf.slot p hp)] at this
    exact this
  refine ⟨⟨fun r hr ↦ ?_, kept_trans hf.kept (hm.kept hwf)⟩, ?_⟩
  · cases hs : slots.any (·.2 == r)
    · have := hm.regs r _ (keepsOthers_spec hk hr hs)
      rw [Sym.eval, Env.ofMachine_regs] at this
      exact this.trans (hf.regs r hr hs)
    · obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp hs
      rw [← Reg64.eq_of_beq hpr]
      exact hslot p hp
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp, eval_ptr0, frame_add]

end

/-! ## The callee's stack below the frame -/

public section

variable {m0 d : MachineData} {n F : Nat}

theorem inRange_mono {a q : BitVec 64} {k k' : Nat} (h : NativeRustcVm.InRange a k q)
    (hk : k ≤ k') : NativeRustcVm.InRange a k' q := by
  unfold NativeRustcVm.InRange at h ⊢
  omega

theorem Apart.symm' {a b : BitVec 64} {n N : Nat} (h : NativeRustcVm.Apart a n b N) :
    NativeRustcVm.Apart b N a n := by
  unfold NativeRustcVm.Apart at h ⊢
  omega

theorem Apart.sub {a b b' : BitVec 64} {n N N' : Nat} (h : NativeRustcVm.Apart a n b N)
    (h1 : b.toNat ≤ b'.toNat) (h2 : b'.toNat + N' ≤ b.toNat + N) :
    NativeRustcVm.Apart a n b' N' := by
  unfold NativeRustcVm.Apart at h ⊢
  omega

/-- The callee's stack is the caller's, below the frame. -/
theorem stackBelow_callee (hsp : rspOf d = stackBelow m0 F) {n' : Nat}
    (hn : F + n' ≤ (rspOf m0).toNat) : stackBelow d n' = stackBelow m0 (F + n') := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (rspOf d).toNat = (rspOf m0).toNat - F := by rw [hsp, stackBelow_toNat (by omega)]
  rw [stackBelow_toNat (by omega), stackBelow_toNat hn, h1]
  omega

/-- The callee's stack is fine. -/
theorem stackOk_callee (h : StackOk m0 n) (hk : Kept m0.dmem d.dmem)
    (hsp : rspOf d = stackBelow m0 F) {n' : Nat} (hn' : F + n' ≤ n) : StackOk d n' := by
  have h1 : (rspOf d).toNat = (rspOf m0).toNat - F := by
    rw [hsp, stackBelow_toNat (by have := h.1; omega)]
  refine ⟨by have := h.1; omega, by have := h.2.1; omega, fun i hi ↦ ?_⟩
  have e : rspOf d - BitVec.ofNat 64 n' + BitVec.ofNat 64 i =
      stackBelow m0 n + BitVec.ofNat 64 (n - F - n' + i) := by
    rw [show rspOf d - BitVec.ofNat 64 n' = stackBelow d n' from rfl,
      stackBelow_callee hsp (by have := h.1; omega)]
    apply BitVec.eq_of_toNat_eq
    have := h.1
    have := h.2.1
    have h1 := stackBelow_toNat (m := m0) (n := F + n') (by omega)
    have h2 := stackBelow_toNat (m := m0) (n := n) (by omega)
    rw [NativeRustcVm.toNat_add_ofNat (a := stackBelow m0 (F + n')) (i := i) (by omega),
      NativeRustcVm.toNat_add_ofNat (a := stackBelow m0 n) (i := n - F - n' + i) (by omega), h1, h2]
    omega
  rw [e]
  exact hk _ (h.2.2 _ (by omega))

/-- What is apart from the stack is apart from the callee's. -/
theorem apart_callee {a : BitVec 64} {l : Nat}
    (h : NativeRustcVm.Apart a l (stackBelow m0 n) (n + 8)) (hsp : rspOf d = stackBelow m0 F)
    (hn : n ≤ (rspOf m0).toNat) {n' : Nat} (hn' : F + n' ≤ n) :
    NativeRustcVm.Apart a l (stackBelow d n') (n' + 8) := by
  rw [stackBelow_callee hsp (by omega)]
  have h1 := stackBelow_toNat (m := m0) (n := F + n') (by omega)
  have h2 := stackBelow_toNat (m := m0) (n := n) hn
  refine Apart.sub h ?_ ?_ <;> rw [h1, h2] <;> omega

/-- What is apart from the stack is apart from the frame. -/
theorem apart_frame {a : BitVec 64} {l : Nat}
    (h : NativeRustcVm.Apart a l (stackBelow m0 n) (n + 8)) (hn : n ≤ (rspOf m0).toNat)
    (hF : F ≤ n) : NativeRustcVm.Apart a l (stackBelow m0 F) (F + 8) := by
  have h1 := stackBelow_toNat (m := m0) (n := F) (by omega)
  have h2 := stackBelow_toNat (m := m0) (n := n) hn
  refine Apart.sub h ?_ ?_ <;> rw [h1, h2] <;> omega

/-- The callee's stack within the caller's, below the frame. -/
theorem inRange_callee (hsp : rspOf d = stackBelow m0 F) (h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64)
    (hn : n ≤ (rspOf m0).toNat) {n' : Nat} (hn' : F + n' ≤ n) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow d n') n' q) :
    NativeRustcVm.InRange (stackBelow m0 n) n q ∧
      ¬ NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q := by
  rw [stackBelow_callee hsp (by omega)] at h
  have hs := stackBelow_toNat (m := m0) hn
  have hs' := stackBelow_toNat (m := m0) (n := F + n') (by omega)
  have hf := stackBelow_toNat (m := m0) (n := F) (by omega)
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at h
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega),
    inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
  omega

/-- The frame below its return address is the top of the stack. -/
theorem inRange_frame_stack (h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64) (hn : n ≤ (rspOf m0).toNat)
    (hF : F ≤ n) {q : BitVec 64} (h : NativeRustcVm.InRange (stackBelow m0 F) F q) :
    NativeRustcVm.InRange (stackBelow m0 n) n q := by
  have hs := stackBelow_toNat (m := m0) hn
  have hf := stackBelow_toNat (m := m0) (n := F) (by omega)
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at h
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
  omega

/-- Three regions pairwise apart. -/
theorem pairwise3 {α : Type} {R : α → α → Prop} {x y z : α} (h1 : R x y) (h2 : R x z)
    (h3 : R y z) : [x, y, z].Pairwise R :=
  .cons (fun b hb ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> assumption) (List.pairwise_pair.mpr h3)

/-- Two regions, mapped and not wrapping, after their bytes were kept. -/
theorem rest2_ok {d d' : DataMem} {x y : BitVec 64 × Nat}
    (hx : NativeRustcVm.Mapped d x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2)
    (hy : NativeRustcVm.Mapped d y.1 y.2 ∧ NativeRustcVm.NoWrap y.1 y.2) (hk : Kept d d') :
    ∀ z ∈ [x, y], NativeRustcVm.Mapped d' z.1 z.2 ∧ NativeRustcVm.NoWrap z.1 z.2 := by
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact ⟨Mapped.keeps hx.1 hk, hx.2⟩
  · exact ⟨Mapped.keeps hy.1 hk, hy.2⟩

/-- An interval of an area is in it. -/
theorem inRange_of_off {b q : BitVec 64} {N o l : Nat} (hN : NativeRustcVm.NoWrap b N)
    (hle : o + l ≤ N) (h : NativeRustcVm.InRange (off b o) l q) : NativeRustcVm.InRange b N q :=
  inRange_of_touch hN (touch_of_inRange hN hle h)

/-- Part of a mapped area is mapped. -/
theorem mapped_off {d : DataMem} {b : BitVec 64} {N o k : Nat} (h : NativeRustcVm.Mapped d b N)
    (hle : o + k ≤ N) : NativeRustcVm.Mapped d (off b o) k :=
  fun i hi ↦ by rw [off_add]; exact h _ (by omega)

variable [Labels]

/-- The round constants for a callee using `n'` bytes of stack below an `F`-byte frame, kept
where its caller's memory changed. -/
theorem RcAt.callee (h : RcAt m0 n) (hd : ∀ i < 192, d.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i))
    (hsp : rspOf d = stackBelow m0 F) (hn : n ≤ (rspOf m0).toNat) {n' : Nat}
    (hn' : F + n' ≤ n) : RcAt d n' := by
  obtain ⟨hw, hnw, hap⟩ := h
  refine ⟨bytesAt_congr hw fun i hi ↦ hd i ?_, hnw, apart_callee hap hsp hn hn'⟩
  have : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 := by
    rw [length_flatMap_wordBytes]; rfl
  exact hi.trans_eq this

/-- Preserve loader bytes through writes to a subset of the protected areas and stack. -/
theorem got_keep {areas writes : List (BitVec 64 × Nat)} {symbols : List Label}
    (hg : GotAt m0 n areas symbols) (hst : StackOk m0 n)
    (hmem : ∀ a ∈ writes, a ∈ areas)
    (hnw : ∀ a ∈ writes, NativeRustcVm.NoWrap a.1 a.2)
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (fun q =>
      (∃ a ∈ writes, NativeRustcVm.InRange a.1 a.2 q) ∨
        NativeRustcVm.InRange (stackBelow m0 n) n q)) :
    ∀ l ∈ symbols, ∀ i < 8, d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) :=
  (hg.areas hmem).unchanged hst hnw (SameOutside.mono hs fun _ h => h.elim Or.inr Or.inl)

/-- Pass preserved loader bytes and the protected geometry to a callee. -/
theorem got_callee {areas areas' : List (BitVec 64 × Nat)} {symbols : List Label}
    (hg : GotAt m0 n areas symbols)
    (hd : ∀ l ∈ symbols, ∀ i < 8, d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i))
    (hsp : rspOf d = stackBelow m0 F) (hn : n ≤ (rspOf m0).toNat) {n' : Nat}
    (hn' : F + n' ≤ n)
    (ha : ∀ l ∈ symbols, ∀ a ∈ areas', Apart (gotAddr l) 8 a.1 a.2) :
    GotAt d n' areas' symbols :=
  hg.transport hd (fun l hl => apart_callee (hg.1 l hl).2.2.1 hsp hn hn') ha

/-- A callee's temporary output in the caller's frame is apart from every GOT slot. -/
theorem got_apart_frame {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (hg : GotAt m0 n areas symbols) (hst : StackOk m0 n) {l : Label} (hl : l ∈ symbols)
    {ob len : Nat} (hF : F ≤ n) (hob : ob + len ≤ F) :
    Apart (gotAddr l) 8 (off (stackBelow m0 F) ob) len := by
  have hf := apart_frame (hg.1 l hl).2.2.1 hst.1 hF
  have hn := hst.1
  have hb := stackBelow_toNat (m := m0) (n := F) (by have := hst.1; omega)
  have ho : (off (stackBelow m0 F) ob).toNat = (stackBelow m0 F).toNat + ob :=
    toNat_off (by have := hst.2.1; omega)
  exact Apart.sub hf (by rw [ho]; omega) (by rw [ho]; omega)

/-- The round constants, kept where the memory changed only apart from them. -/
theorem rc_keep {d d' : DataMem} {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange rcAddr 192 q) :
    ∀ i < 192, d'.get? (rcAddr + BitVec.ofNat 64 i) = d.get? (rcAddr + BitVec.ofNat 64 i) :=
  fun i hi ↦ hs _ fun h ↦ hR _ h (inRange_off_self hi (by omega))

end

end NativeRustcVmX64.Transcript
