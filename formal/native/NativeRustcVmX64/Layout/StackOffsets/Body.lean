module

public import NativeRustcVmX64.Layout.StackOffsets.Exec
public import NativeRustcVmX64.Layout.StackOffsets.Model

/-!
# `stack_offsets` on x86-64: the body, its registers, the blocks' steps

The body (`B m0 o`): `BuildFrame.Bd` with the 1328-byte frame, `stack_offsets`' 1344 bytes of
stack and `offsets` as output. The callee-saved registers the body reads (`Regs`: `offsets`'
length RBX, `sizes` R12, `offsets` R14, `n` R15). A block run from a fresh state of the frame
(`run0`) or of the frame and one word (`run1`) keeps the body. The conditions the executor states
(`ult_eval`, `eq_eval`, `addC_eval`), a branch on them (`pc_of`).
-/

namespace NativeRustcVmX64.Layout.StackOffsets

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Layout.BuildFrame

@[expose] public section

/-- The output: `offsets`. -/
abbrev R (m0 : MachineData) : BitVec 64 → Prop := NativeRustcVm.InRange (out m0) (8 * cap m0)

/-- **The body**, RSP at the frame's offset `o`. -/
abbrev B (m0 : MachineData) (o : Nat) (d : MachineData) : Prop := Bd m0 1328 1344 slots (R m0) o d

/-- **The callee-saved registers the body reads**. -/
structure Regs (m0 d : MachineData) : Prop where
  rbx : reg d .rbx = reg m0 .rcx
  r12 : reg d .r12 = reg m0 .rdi
  r14 : reg d .r14 = reg m0 .rdx
  r15 : reg d .r15 = reg m0 .rsi

end

public section

theorem SS_eq : stackOffsetsStack = 1344 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1328 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_ge : ∀ p ∈ slots, 1280 ≤ p.1 := by decide

theorem Regs.saved {m0 d d' : MachineData} (h : Regs m0 d) (hs : Saved d d') : Regs m0 d' :=
  ⟨(hs.1 .rbx rfl).trans h.rbx, (hs.1 .r12 rfl).trans h.r12, (hs.1 .r14 rfl).trans h.r14,
    (hs.1 .r15 rfl).trans h.r15⟩

theorem Regs.of {m0 d d' : MachineData} (h : Regs m0 d)
    (he : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg d' r = reg d r) : Regs m0 d' :=
  ⟨(he .rbx (by simp)).trans h.rbx, (he .r12 (by simp)).trans h.r12,
    (he .r14 (by simp)).trans h.r14, (he .r15 (by simp)).trans h.r15⟩

/-! ## Conditions -/

section
variable [Labels]

theorem ult_eval (env : Env) (a b : Sym) :
    (SBool.cmp .ult .W64 a b).eval env = decide ((a.eval env).toNat < (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, BitVec.ult]

theorem eq_eval (env : Env) (a b : Sym) :
    (SBool.cmp .eq .W64 a b).eval env = decide ((a.eval env).toNat = (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64]
  by_cases h : a.eval env = b.eval env
  · simp [h]
  · simp only [beq_eq_false_iff_ne.mpr h]
    exact (decide_eq_false fun h' ↦ h (BitVec.eq_of_toNat_eq h')).symm

theorem test_eval (env : Env) (a : Sym) :
    (SBool.cmp .eq .W64 (.bin .and .W64 a a) (.lit 0)).eval env = decide ((a.eval env).toNat = 0) := by
  rw [eq_eval]
  simp [Sym.eval, BinOp.apply]

theorem addC_eval (env : Env) (a b : Sym) :
    (SBool.cmp .addC .W64 a b).eval env =
      decide (2 ^ 64 ≤ (a.eval env).toNat + (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, BitVec.unsigned]
  have ha := (a.eval env).isLt
  have hb := (b.eval env).isLt
  have h2 : (a.eval env + b.eval env).toNat = ((a.eval env).toNat + (b.eval env).toNat) % 2 ^ 64 :=
    BitVec.toNat_add _ _
  rw [h2, Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq]
  constructor
  · intro h; omega
  · intro h; omega

omit [Labels] in
/-- A branch on a condition the executor evaluates to `decide P`. -/
theorem pc_of {pc a b : Int64} {c : Bool} {P : Prop} [Decidable P]
    (h : pc = if c = true then a else b) (hc : c = decide P) : (P → pc = a) ∧ (¬P → pc = b) := by
  subst hc
  exact ⟨fun hp ↦ by simpa [hp] using h, fun hp ↦ by simpa [hp] using h⟩

end

theorem add_eval {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (BinOp.apply .add .W64 x y).toNat = x.toNat + y.toNat := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem lit_toNat {c : Nat} (h : c < 2 ^ 64) : (BitVec.ofNat 64 c).toNat = c :=
  NativeRustcVm.toNat_ofNat_of_lt h

/-- `p + 8 i`. -/
theorem idx_eval [Labels] (env : Env) (p i : Reg64) :
    (idx p i).eval env = env.regs p + BitVec.ofNat 64 (8 * (env.regs i).toNat) := by
  simp only [idx, Sym.eval, BinOp.apply, low_W64, ext_W64]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Width.bits]
  omega

/-! ## The frame's geometry -/

variable {m0 : MachineData}

theorem fb_toNat (hst : StackOk m0 1344) : (stackBelow m0 1328).toNat = (rspOf m0).toNat - 1328 :=
  stackBelow_toNat (by have := hst.1; omega)

theorem fb_noWrap (hst : StackOk m0 1344) : NativeRustcVm.NoWrap (stackBelow m0 1328) (1328 + 8) :=
  frame_noWrap hst (by decide)

theorem ob_eq (m0 : MachineData) : ob m0 = off (stackBelow m0 1328) 16 := rfl

theorem ob_toNat (hst : StackOk m0 1344) : (ob m0).toNat = (rspOf m0).toNat - 1312 := by
  have := hst.1; have := hst.2.1
  rw [ob_eq, toNat_off (by rw [fb_toNat hst]; omega), fb_toNat hst]
  omega

/-- The frame's bytes are the stack's. -/
theorem frame_in (hst : StackOk m0 1344) {q : BitVec 64}
    (h : NativeRustcVm.InRange (stackBelow m0 1328) 1328 q) :
    NativeRustcVm.InRange (stackBelow m0 1344) 1344 q :=
  inRange_frame_stack hst.2.1 hst.1 (by decide) h

/-- What is off the stack is apart from the frame. -/
theorem apart_fr (hst : StackOk m0 1344) {a : BitVec 64} {l : Nat} (h : OffStack m0 a l 1344) :
    NativeRustcVm.Apart a l (stackBelow m0 1328) (1328 + 8) :=
  apart_frame h hst.1 (by decide)

/-- The output's bytes are not the frame's. -/
theorem R_not_frame (hst : StackOk m0 1344) (hoff : OffStack m0 (out m0) (8 * cap m0) 1344)
    (hno : NativeRustcVm.NoWrap (out m0) (8 * cap m0)) {q : BitVec 64} (h : R m0 q) :
    ¬ NativeRustcVm.InRange (stackBelow m0 1328) (1328 + 8) q :=
  not_inRange_of_apart (apart_fr hst hoff) hno (fb_noWrap hst) h

/-- An offset of the frame, below its return address, is in the stack. -/
theorem off_in_stack (hst : StackOk m0 1344) {o l : Nat} (hl : o + l ≤ 1328) {q : BitVec 64}
    (h : NativeRustcVm.InRange (off (stackBelow m0 1328) o) l q) :
    NativeRustcVm.InRange (stackBelow m0 1344) 1344 q :=
  frame_in hst (inRange_of_off (by have := fb_noWrap hst; unfold NativeRustcVm.NoWrap at this ⊢; omega) hl h)

/-- A sub-range of the output is in the output. -/
theorem R_sub (hno : NativeRustcVm.NoWrap (out m0) (8 * cap m0)) {o l : Nat}
    (hl : o + l ≤ 8 * cap m0) {q : BitVec 64}
    (h : NativeRustcVm.InRange (out m0 + BitVec.ofNat 64 o) l q) : R m0 q :=
  NativeRustcVm.InRange.of_sub h hno hl

/-! ## Blocks in the body -/

variable [Host]

/-- A body in the frame's environment, RSP at offset `8`. -/
theorem match0 {d : MachineData} {ret : BitVec 64} (hb : B m0 8 d) :
    Match (frameEnv m0 d 1328 [] (fun _ ↦ 0) ret) bodyS d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hb.fr.rsp_eval, trivial⟩ trivial trivial trivial

/-- **A block of the frame alone** keeps the body. -/
theorem run0 {ds : List Directive} {kk : Nat} {Sy0 Sy1 : SState} {x : Exit} {st : MachineState}
    {o o' : Nat} {ret : BitVec 64} {Q : MachineState → Prop} (hst : StackOk m0 1344)
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds Sy0 = some (Sy1, x))
    (hret : ∀ l, x = .call l → ret = (Host.addrOf (kk + ds.length)).toBitVec)
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 o st.data)
    (hm : Match (frameEnv m0 st.data 1328 [] (fun _ ↦ 0) ret) Sy0 st.data)
    (hok : MidOk 1328 o' slots Sy1 = true)
    (cont : ∀ st', Match (frameEnv m0 st.data 1328 [] (fun _ ↦ 0) ret) Sy1 st'.data →
      PcOk (frameEnv m0 st.data 1328 [] (fun _ ↦ 0) ret) x (Host.addrOf (kk + ds.length)) st' →
      B m0 o' st'.data → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hwf := fr_wf0 (vars := fun _ ↦ 0) (ret := ret) hb hst (by decide)
  exact exec_at hk hx hwf hret hpc hm fun st' hm' hpc' ↦
    cont st' hm' hpc' (hb.of_block0 hst (by decide) hm' hok slots_le)

/-- **A block of the frame and one more region** inside the output or the stack keeps the body. -/
theorem run1 {ds : List Directive} {kk : Nat} {Sy0 Sy1 : SState} {x : Exit} {st : MachineState}
    {o o' : Nat} {a : BitVec 64} {l : Nat} {Q : MachineState → Prop} (hst : StackOk m0 1344)
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds Sy0 = some (Sy1, x))
    (hret : ∀ l, x = .call l → (0 : BitVec 64) = (Host.addrOf (kk + ds.length)).toBitVec)
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 o st.data)
    (hma : NativeRustcVm.Mapped m0.dmem a l) (hna : NativeRustcVm.NoWrap a l)
    (hap : NativeRustcVm.Apart (stackBelow m0 1328) (1328 + 8) a l)
    (hin : ∀ q, NativeRustcVm.InRange a l q →
      R m0 q ∨ NativeRustcVm.InRange (stackBelow m0 1344) 1344 q)
    (hm : Match (frameEnv m0 st.data 1328 [(a, l)] (fun _ ↦ 0) 0) Sy0 st.data)
    (hok : MidOk 1328 o' slots Sy1 = true)
    (cont : ∀ st', Match (frameEnv m0 st.data 1328 [(a, l)] (fun _ ↦ 0) 0) Sy1 st'.data →
      PcOk (frameEnv m0 st.data 1328 [(a, l)] (fun _ ↦ 0) 0) x (Host.addrOf (kk + ds.length)) st' →
      (frameEnv m0 st.data 1328 [(a, l)] (fun _ ↦ 0) 0).WF →
      B m0 o' st'.data → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  have hwf := fr_wf1 (vars := fun _ ↦ 0) (ret := 0) hb hst (by decide) hma hna hap
  exact exec_at hk hx hwf hret hpc hm fun st' hm' hpc' ↦
    cont st' hm' hpc' hwf (hb.of_block hst (by decide) hwf hm' hok slots_le (by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact hin))

end

end NativeRustcVmX64.Layout.StackOffsets
