module

public import NativeRustcVmArm.Transcript.Glue
public import NativeRustcVmArm.Transcript.Stack

/-!
# A function's frame, through its blocks and calls

A function that saves registers in a frame of `F` bytes below SP (`frameBase m0 F`) at the offsets
`slots` and restores them on return: `Frame m0 F slots d` says the machine state `d` has SP at the
frame, the slots holding the entry's registers, the other callee-saved registers the entry's, and
every byte of the entry's memory. Blocks run with region 0 the frame (`frameEnv`).

- the prologue establishes it (`Frame.of_prologue`, its block checked by `ProOk`);
- a block keeps it (`Frame.of_block`, by `MidOk`: SP and the other callee-saved registers kept, no
  write over a slot, every write within its region);
- a call keeps it where the callee changes no byte of the frame (`Frame.call`);
- the epilogue restores the registers (`Frame.epilogue`, by `EpiOk`): `Saved` holds.
-/

namespace NativeRustcVmArm.Transcript

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Transcript

@[expose] public section

/-- The frame's address: `F` bytes below the entry's SP. -/
def frameBase (m : MachineData) (F : Nat) : BitVec 64 := m.regs.SP.toBitVec - BitVec.ofNat 64 F

/-- The slots: each saved register's offset in the frame. -/
abbrev Slots := List (Nat × XReg)

/-- The callee-saved registers not in a slot are their atoms. -/
def keepsOthers (slots : Slots) (S : SState) : Bool :=
  allXRegs.all fun r => !calleeSaved r || slots.any (·.2 == r) || S.reg r == some (.reg r)

/-- Each slot holds its register's atom. -/
def slotsWritten (slots : Slots) (S : SState) : Bool :=
  slots.all fun p => (List.range 8).all fun t => findWrite 0 (p.1 + t) S.mem == some (.reg p.2, t)

/-- No write into region 0 overlaps a slot. -/
def slotsUntouched (slots : Slots) (S : SState) : Bool :=
  S.mem.all fun w => w.r != 0 || slots.all fun p => w.off + w.n ≤ p.1 || p.1 + 8 ≤ w.off

/-- Each slot's register is loaded from it. -/
def slotsLoaded (slots : Slots) (S : SState) : Bool :=
  slots.all fun p => S.reg p.2 == some (.load 0 p.1 8)

/-- Every write is within its region. -/
def writesIn (S : SState) : Bool :=
  S.mem.all fun w => match S.regions[w.r]? with
    | some (sz, _) => decide (w.off + w.n ≤ sz)
    | none => false

/-- A prologue's end. -/
def ProOk (slots : Slots) (S : SState) : Bool :=
  slotsWritten slots S && keepsOthers slots S && S.sp == .ptr 0 0

/-- A block in the frame's body. -/
def MidOk (slots : Slots) (S : SState) : Bool :=
  slotsUntouched slots S && writesIn S && keepsOthers slots S && S.sp == .ptr 0 0

/-- An epilogue's end. -/
def EpiOk (F : Nat) (slots : Slots) (S : SState) : Bool :=
  slotsLoaded slots S && keepsOthers slots S && S.sp == .ptr 0 F

/-- A block's environment: region 0 the frame, then `rest`. -/
abbrev frameEnv (m0 d : MachineData) (F : Nat) (rest : List (BitVec 64 × Nat)) : Env :=
  Env.ofMachine d ((frameBase m0 F, F) :: rest)

/-- **The frame**: SP at it, the slots holding the entry's registers, the other callee-saved
registers the entry's, the entry's bytes kept. -/
structure Frame (m0 : MachineData) (F : Nat) (slots : Slots) (d : MachineData) : Prop where
  sp : d.regs.SP.toBitVec = frameBase m0 F
  slot : ∀ p ∈ slots, NativeRustcVm.WordAt d.dmem (off (frameBase m0 F) p.1) (m0.regs.getXReg p.2)
  kept : Kept m0.dmem d.dmem
  regs : ∀ r, calleeSaved r = true → slots.any (·.2 == r) = false →
    d.regs.getXReg r = m0.regs.getXReg r

end

public section

theorem kept_trans {a b c : DataMem} (h₁ : Kept a b) (h₂ : Kept b c) : Kept a c :=
  fun p hp ↦ h₂ p (h₁ p hp)

theorem keepsOthers_spec {slots : Slots} {S : SState} (h : keepsOthers slots S = true) {r : XReg}
    (hr : calleeSaved r = true) (hs : slots.any (·.2 == r) = false) : S.reg r = some (.reg r) := by
  unfold keepsOthers at h
  rw [List.all_eq_true] at h
  have := h r (mem_allXRegs r)
  simp only [hr, hs, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

theorem frameBase_add {m : MachineData} {F : Nat} :
    frameBase m F + BitVec.ofInt 64 (F : Int) = m.regs.SP.toBitVec := by
  rw [BitVec.ofInt_natCast, frameBase, BitVec.sub_add_cancel]

theorem frame_noWrap {m : MachineData} {F : Nat} (hF : F ≤ m.regs.SP.toNat) :
    (frameBase m F).toNat + F ≤ 2 ^ 64 := by
  rw [frameBase, frame_toNat (n := F) hF le_rfl]
  have := m.regs.SP.toNat_lt
  omega

variable [Labels] {m0 d d' : MachineData} {F : Nat} {slots : Slots}
  {rest : List (BitVec 64 × Nat)} {S : SState}

theorem eval_ptr00 (env : Env) (h : env.base 0 = frameBase m0 F) :
    (Sym.ptr 0 0).eval env = frameBase m0 F := by
  rw [Sym.eval, h, ofInt_zero64, BitVec.add_zero]

/-- **The prologue** establishes the frame. -/
theorem Frame.of_prologue (hwf : (frameEnv m0 m0 F rest).WF)
    (hm : Match (frameEnv m0 m0 F rest) S d) (hS : ProOk slots S = true)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Frame m0 F slots d := by
  simp only [ProOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨hw, hk⟩, hsp⟩ := hS
  refine ⟨?_, fun p hp ↦ ?_, hm.kept hwf, fun r hr hs ↦ ?_⟩
  · rw [hm.sp, hsp]; exact eval_ptr00 _ rfl
  · unfold slotsWritten at hw
    rw [List.all_eq_true] at hw
    have hp' := hw p hp
    rw [List.all_eq_true] at hp'
    have := wordAt_write hm (r := 0) (o := p.1) rfl (hle p hp) (v := .reg p.2) fun t ht ↦ by
      have := hp' t (List.mem_range.mpr ht)
      simpa using this
    exact this
  · exact UInt64.toBitVec_inj.mp (hm.regs r _ (keepsOthers_spec hk hr hs))

/-- **The prologue** run from a state `d` with the entry's slot registers, callee-saved registers,
SP and bytes (a function that tests its arguments before saving registers). -/
theorem Frame.of_prologue_from (hsv : Saved m0 d)
    (hsl : ∀ p ∈ slots, d.regs.getXReg p.2 = m0.regs.getXReg p.2)
    (hwf : (frameEnv m0 d F rest).WF) (hm : Match (frameEnv m0 d F rest) S d')
    (hS : ProOk slots S = true) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Frame m0 F slots d' := by
  simp only [ProOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨hw, hk⟩, hsp⟩ := hS
  refine ⟨?_, fun p hp ↦ ?_, kept_trans hsv.2.2 (hm.kept hwf), fun r hr hs ↦ ?_⟩
  · rw [hm.sp, hsp]; exact eval_ptr00 _ rfl
  · unfold slotsWritten at hw
    rw [List.all_eq_true] at hw
    have hp' := hw p hp
    rw [List.all_eq_true] at hp'
    have := wordAt_write hm (r := 0) (o := p.1) rfl (hle p hp) (v := .reg p.2) fun t ht ↦ by
      have := hp' t (List.mem_range.mpr ht)
      simpa using this
    rw [← hsl p hp]
    exact this
  · exact (UInt64.toBitVec_inj.mp (hm.regs r _ (keepsOthers_spec hk hr hs))).trans (hsv.1 r hr)

theorem not_written_slot (hwf : (frameEnv m0 d F rest).WF) (hm : Match (frameEnv m0 d F rest) S d')
    (hu : slotsUntouched slots S = true) (hin : writesIn S = true)
    {p : Nat × XReg} (hp : p ∈ slots) (hle : p.1 + 8 ≤ F) {i : Nat} (hi : i < 8) :
    ¬ Written (frameEnv m0 d F rest) S (off (frameBase m0 F) (p.1 + i)) := by
  rintro ⟨w, hw, b, sz, hb, h1, h2⟩
  have hnw0 := hwf.noWrap 0 (frameBase m0 F) F rfl
  have hq : (off (frameBase m0 F) (p.1 + i)).toNat = (frameBase m0 F).toNat + (p.1 + i) :=
    toNat_off (by omega)
  rw [hq] at h1 h2
  by_cases hr : w.r = 0
  · rw [hr] at hb
    cases hb
    unfold slotsUntouched at hu
    rw [List.all_eq_true] at hu
    have := hu w hw
    simp only [hr, bne_self_eq_false, Bool.false_or, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at this
    have := this p hp
    omega
  · unfold writesIn at hin
    rw [List.all_eq_true] at hin
    have hw' := hin w hw
    obtain ⟨sz', al, hS'⟩ : ∃ sz' al, S.regions[w.r]? = some (sz', al) := by
      revert hw'
      cases S.regions[w.r]? with
      | none => simp
      | some x => exact fun _ ↦ ⟨x.1, x.2, rfl⟩
    rw [hS'] at hw'
    simp only [decide_eq_true_eq] at hw'
    obtain ⟨b', hb', -⟩ := hm.regions _ _ _ hS'
    rw [hb] at hb'
    cases hb'
    have := hwf.disjoint 0 w.r _ _ _ _ (Ne.symm hr) rfl hb
    omega

/-- **A block** keeps the frame. -/
theorem Frame.of_block (hf : Frame m0 F slots d) (hwf : (frameEnv m0 d F rest).WF)
    (hm : Match (frameEnv m0 d F rest) S d') (hS : MidOk slots S = true)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Frame m0 F slots d' := by
  simp only [MidOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨hu, hin⟩, hk⟩, hsp⟩ := hS
  refine ⟨?_, fun p hp ↦ ?_, kept_trans hf.kept (hm.kept hwf), fun r hr hs ↦ ?_⟩
  · rw [hm.sp, hsp]; exact eval_ptr00 _ rfl
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    rw [off_add]
    exact hm.get?_mem0 hwf (not_written_slot hwf hm hu hin hp (hle p hp) hi)
  · have := hm.regs r _ (keepsOthers_spec hk hr hs)
    rw [Sym.eval, Env.ofMachine_regs] at this
    exact (UInt64.toBitVec_inj.mp this).trans (hf.regs r hr hs)

omit [Labels] in
/-- **A call** keeps the frame where the callee changes none of its bytes. -/
theorem Frame.call (hf : Frame m0 F slots d) (hs : Saved d d') {R : BitVec 64 → Prop}
    (hso : SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange (frameBase m0 F) F q)
    (hnw : (frameBase m0 F).toNat + F ≤ 2 ^ 64) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) :
    Frame m0 F slots d' := by
  refine ⟨?_, fun p hp ↦ ?_, kept_trans hf.kept hs.2.2, fun r hr hsl ↦ ?_⟩
  · rw [hs.2.1]; exact hf.sp
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := hi
    refine hso _ fun h ↦ hR _ h ?_
    rw [off_add]
    exact inRange_off_self (by have := hle p hp; omega) (by omega)
  · exact (hs.1 r hr).trans (hf.regs r hr hsl)

omit [Labels] in
/-- **A call** keeps the frame where the callee changes none of its slots' bytes (it may write an
output elsewhere in the frame). -/
theorem Frame.call_slots (hf : Frame m0 F slots d) (hs : Saved d d') {R : BitVec 64 → Prop}
    (hso : SameOutside d.dmem d'.dmem R)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ R (off (frameBase m0 F) (p.1 + i))) : Frame m0 F slots d' := by
  refine ⟨?_, fun p hp ↦ ?_, kept_trans hf.kept hs.2.2, fun r hr hsl ↦ ?_⟩
  · rw [hs.2.1]; exact hf.sp
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := hi
    rw [off_add]
    exact hso _ (hR p hp i hi')
  · exact (hs.1 r hr).trans (hf.regs r hr hsl)

omit [Labels] in
/-- An output at offset `o` of the frame, `n` bytes, misses every slot. -/
theorem not_slot_out (hnw : (frameBase m0 F).toNat + F ≤ 2 ^ 64) {o n : Nat} (hon : o + n ≤ F)
    (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) (hS : ∀ p ∈ slots, o + n ≤ p.1 ∨ p.1 + 8 ≤ o) :
    ∀ p ∈ slots, ∀ i < 8,
      ¬ NativeRustcVm.InRange (off (frameBase m0 F) o) n (off (frameBase m0 F) (p.1 + i)) := by
  intro p hp i hi h
  have := hle p hp
  rw [inRange_off_iff (by omega) (by omega)] at h
  have := hS p hp
  omega

/-- **The epilogue** restores the registers: `Saved`, and each slot's register the entry's. -/
theorem Frame.epilogue (hf : Frame m0 F slots d) (hwf : (frameEnv m0 d F rest).WF)
    (hm : Match (frameEnv m0 d F rest) S d') (hS : EpiOk F slots S = true) :
    Saved m0 d' ∧ ∀ p ∈ slots, d'.regs.getXReg p.2 = m0.regs.getXReg p.2 := by
  simp only [EpiOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨hl, hk⟩, hsp⟩ := hS
  have hslot : ∀ p ∈ slots, d'.regs.getXReg p.2 = m0.regs.getXReg p.2 := by
    intro p hp
    unfold slotsLoaded at hl
    rw [List.all_eq_true] at hl
    have := hm.regs p.2 _ (by simpa using hl p hp)
    rw [Sym.eval, load_ofMachine (o := p.1) rfl (hf.slot p hp)] at this
    exact UInt64.toBitVec_inj.mp this
  refine ⟨⟨fun r hr ↦ ?_, ?_, kept_trans hf.kept (hm.kept hwf)⟩, hslot⟩
  · cases hs : slots.any (·.2 == r)
    · have := hm.regs r _ (keepsOthers_spec hk hr hs)
      rw [Sym.eval, Env.ofMachine_regs] at this
      exact (UInt64.toBitVec_inj.mp this).trans (hf.regs r hr hs)
    · obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp hs
      rw [← XReg.eq_of_beq hpr]
      exact hslot p hp
  · apply UInt64.toBitVec_inj.mp
    rw [hm.sp, hsp, Sym.eval, show (frameEnv m0 d F rest).base 0 = frameBase m0 F from rfl,
      frameBase_add]

end

end NativeRustcVmArm.Transcript

/-! ## The frame in the stack -/

namespace NativeRustcVmArm.Transcript

open NativeRustcArm NativeRustcVm.Transcript

public section

variable {m0 d : MachineData} {n F : Nat}

theorem frameBase_toNat (hn : n ≤ m0.regs.SP.toNat) (hF : F ≤ n) :
    (frameBase m0 F).toNat = m0.regs.SP.toNat - F :=
  frame_toNat hn hF

/-- The callee's stack starts where the caller's does. -/
theorem stackBelow_frame (hsp : d.regs.SP.toBitVec = frameBase m0 F) (hn : n ≤ m0.regs.SP.toNat)
    (hF : F ≤ n) : stackBelow d (n - F) = stackBelow m0 n := by
  apply BitVec.eq_of_toNat_eq
  have h1 : d.regs.SP.toNat = m0.regs.SP.toNat - F := by
    rw [← UInt64.toNat_toBitVec, hsp, frameBase_toNat hn hF]
  rw [toNat_stackBelow (by omega), toNat_stackBelow hn, h1]
  omega

theorem inRange_mono {a q : BitVec 64} {k k' : Nat} (h : NativeRustcVm.InRange a k q) (hk : k ≤ k') :
    NativeRustcVm.InRange a k' q := by
  unfold NativeRustcVm.InRange at h ⊢
  omega

/-- The frame is the top of the stack. -/
theorem inRange_frame_stack (hn : n ≤ m0.regs.SP.toNat) (hF : F ≤ n) {q : BitVec 64}
    (h : NativeRustcVm.InRange (frameBase m0 F) F q) :
    NativeRustcVm.InRange (stackBelow m0 n) n q := by
  have hf := frameBase_toNat hn hF
  have hs := toNat_stackBelow (m := m0) hn
  have := m0.regs.SP.toNat_lt
  unfold NativeRustcVm.InRange at h ⊢
  rw [BitVec.toNat_sub] at h ⊢
  rw [hf] at h
  rw [hs]
  have := q.isLt
  omega

/-- The callee's stack is below the frame. -/
theorem not_frame_of_callee (hn : n ≤ m0.regs.SP.toNat) (hF : F ≤ n) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow m0 n) (n - F) q) :
    ¬ NativeRustcVm.InRange (frameBase m0 F) F q := by
  have hf := frameBase_toNat hn hF
  have hs := toNat_stackBelow (m := m0) hn
  have := m0.regs.SP.toNat_lt
  unfold NativeRustcVm.InRange at h ⊢
  rw [BitVec.toNat_sub] at h ⊢
  rw [hf]
  rw [hs] at h
  have := q.isLt
  omega

/-- What is apart from the stack is apart from the frame. -/
theorem apart_frame {a : BitVec 64} {l : Nat}
    (h : NativeRustcVm.Apart a l (stackBelow m0 n) n) (hn : n ≤ m0.regs.SP.toNat) (hF : F ≤ n) :
    NativeRustcVm.Apart a l (frameBase m0 F) F := by
  have hf := frameBase_toNat hn hF
  have hs := toNat_stackBelow (m := m0) hn
  unfold NativeRustcVm.Apart at h ⊢
  omega

/-- What is apart from the stack is apart from the callee's. -/
theorem apart_callee {a : BitVec 64} {l : Nat}
    (h : NativeRustcVm.Apart a l (stackBelow m0 n) n) (hsp : d.regs.SP.toBitVec = frameBase m0 F)
    (hn : n ≤ m0.regs.SP.toNat) (hF : F ≤ n) {n' : Nat} (hn' : n' ≤ n - F) :
    NativeRustcVm.Apart a l (stackBelow d n') n' := by
  have e := stackBelow_frame (n := n' + F) hsp (by omega) (by omega)
  rw [Nat.add_sub_cancel] at e
  rw [e]
  have hs := toNat_stackBelow (m := m0) hn
  have hs' := toNat_stackBelow (m := m0) (n := n' + F) (by omega)
  unfold NativeRustcVm.Apart at h ⊢
  omega

/-- The callee's stack within the caller's. -/
theorem inRange_callee (hsp : d.regs.SP.toBitVec = frameBase m0 F) (hn : n ≤ m0.regs.SP.toNat)
    (hF : F ≤ n) {n' : Nat} (hn' : n' ≤ n - F) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow d n') n' q) :
    NativeRustcVm.InRange (stackBelow m0 n) n q ∧ ¬ NativeRustcVm.InRange (frameBase m0 F) F q := by
  have e := stackBelow_frame (n := n' + F) hsp (by omega) (by omega)
  rw [Nat.add_sub_cancel] at e
  rw [e] at h
  have hs := toNat_stackBelow (m := m0) hn
  have hs' := toNat_stackBelow (m := m0) (n := n' + F) (by omega)
  have hf := frameBase_toNat hn hF
  have := m0.regs.SP.toNat_lt
  have := q.isLt
  unfold NativeRustcVm.InRange at h ⊢
  rw [BitVec.toNat_sub] at h ⊢
  rw [BitVec.toNat_sub, hf]
  rw [hs'] at h
  rw [hs]
  omega

/-- The frame is mapped. -/
theorem frame_mapped (h : StackOk m0 n) (hF : F ≤ n) : Mapped m0.dmem (frameBase m0 F) F := by
  intro i hi
  have e : frameBase m0 F + BitVec.ofNat 64 i =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - F + i) := by
    apply BitVec.eq_of_toNat_eq
    have := m0.regs.SP.toNat_lt
    have := h.2.1
    simp only [frameBase, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
      UInt64.toNat_toBitVec]
    omega
  rw [e]
  exact h.2.2 _ (by omega)

theorem frame_aligned (h : StackOk m0 n) (hF : F ≤ n) (h16 : F % 16 = 0) :
    (frameBase m0 F).toNat % 16 = 0 := by
  rw [frameBase_toNat h.2.1 hF]
  have := h.1
  omega

/-- The callee's stack is fine. -/
theorem stackOk_callee (h : StackOk m0 n) (hk : Kept m0.dmem d.dmem)
    (hsp : d.regs.SP.toBitVec = frameBase m0 F) (hF : F ≤ n) (h16 : F % 16 = 0) {n' : Nat}
    (hn' : n' ≤ n - F) : StackOk d n' := by
  have hn := h.2.1
  have h1 : d.regs.SP.toNat = m0.regs.SP.toNat - F := by
    rw [← UInt64.toNat_toBitVec, hsp, frameBase_toNat hn hF]
  have := StackOk.call h hk hF h16 h1
  obtain ⟨hal, hle, hmap⟩ := this
  refine ⟨hal, by omega, fun i hi ↦ ?_⟩
  have e : d.regs.SP.toBitVec - BitVec.ofNat 64 n' + BitVec.ofNat 64 i =
      d.regs.SP.toBitVec - BitVec.ofNat 64 (n - F) + BitVec.ofNat 64 (n - F - n' + i) := by
    apply BitVec.eq_of_toNat_eq
    have := d.regs.SP.toNat_lt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
    omega
  rw [e]
  exact hmap _ (by omega)

/-- Part of a mapped area is mapped. -/
theorem mapped_off {d : DataMem} {b : BitVec 64} {N o n : Nat} (h : Mapped d b N)
    (hle : o + n ≤ N) : Mapped d (off b o) n :=
  fun i hi ↦ by rw [off_add]; exact h _ (by omega)

/-- Three regions pairwise apart. -/
theorem pairwise3 {α : Type} {R : α → α → Prop} {x y z : α} (h1 : R x y) (h2 : R x z)
    (h3 : R y z) : [x, y, z].Pairwise R :=
  .cons (fun b hb ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> assumption) (List.pairwise_pair.mpr h3)

/-- An interval of an area is in it. -/
theorem inRange_of_off {b q : BitVec 64} {N o n : Nat} (hN : NativeRustcVm.NoWrap b N)
    (hle : o + n ≤ N) (h : NativeRustcVm.InRange (off b o) n q) : NativeRustcVm.InRange b N q :=
  inRange_of_touch hN (touch_of_inRange hN hle h)

end

end NativeRustcVmArm.Transcript
