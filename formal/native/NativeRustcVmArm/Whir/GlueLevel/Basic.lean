module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Whir.GlueLevel.Exec
public import NativeRustcVmArm.Whir.GlueLevel.Mem
public import NativeRustcVmArm.Whir.Frame
public import NativeRustcVmArm.Whir.MathFrame
public import NativeRustcVmArm.Sumcheck.Common

/-!
# `glue_level`'s frame and its calls

`glue_level(s, λ, μ, oodPoint, oodValue, queries, weights, batched)` keeps a 112-byte frame below
the entry's SP: `μ` at 8, X29, X30 and the callee-saved registers from 16 (`slots`). Between its
prologue and epilogue (`FR`, `NativeRustcVmArm.Ring.Fr` with the state's bytes as output) memory
changes in its stack and the state only. A call of `EW::mul` keeps the frame and changes the stack
only (`mul_call`, `SO`); a block without writes keeps both (`reg_block`).
-/

namespace NativeRustcVmArm.Whir.GlueLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- The prologue's slots: `μ` (X3) at 8, X29 and X30 at 16, the callee-saved registers above. -/
def slots : List (Nat × XReg) :=
  [(8, .X3), (16, .X29), (24, .X30), (32, .X28), (40, .X27), (48, .X26), (56, .X25),
    (64, .X24), (72, .X23), (80, .X22), (88, .X21), (96, .X20), (104, .X19)]

/-- The state's address. -/
abbrev pOf (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- `λ`. -/
abbrev lamOf (m0 : MachineData) : EW := ⟨m0.regs.X1, m0.regs.X2⟩
/-- The out-of-domain value. -/
abbrev oodOf (m0 : MachineData) : EW := ⟨m0.regs.X6, m0.regs.X7⟩
/-- The batched value. -/
abbrev batOf (m0 : MachineData) : EW := (glueArgs m0).2.2

/-- **Between the prologue and the epilogue**: the frame, memory changed in the stack and the
state only. -/
abbrev FR (m0 m : MachineData) : Prop :=
  Fr m0 112 glueLevelStack slots [] (InRange (pOf m0) stateBytes) m

/-- Memory changed in the stack only. -/
abbrev SO (m0 m : MachineData) : Prop :=
  SameOutside m0.dmem m.dmem (InRange (stackBelow m0 glueLevelStack) glueLevelStack)

end

public section

theorem glueLevelStack_eq : glueLevelStack = 704 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 112 := by decide

theorem pairwise3 {α : Type} {R : α → α → Prop} {a b c : α} (hab : R a b) (hac : R a c)
    (hbc : R b c) : [a, b, c].Pairwise R :=
  List.pairwise_cons.mpr ⟨fun x hx ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      exacts [hab, hac], List.pairwise_pair.mpr hbc⟩

theorem pairwise4 {α : Type} {R : α → α → Prop} {a b c d : α} (hab : R a b) (hac : R a c)
    (had : R a d) (hbc : R b c) (hbd : R b d) (hcd : R c d) : [a, b, c, d].Pairwise R :=
  List.pairwise_cons.mpr ⟨fun x hx ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      exacts [hab, hac, had], pairwise3 hbc hbd hcd⟩

/-- The `n`-th word's comparison `cbz w0` makes, on `1`. -/
theorem cbz_one [Labels] {env : Env} (h : env.regs .X0 = 1#64) :
    (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval env = false := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, h]
  decide

variable {s : WhirStateW} {m0 : MachineData}

/-- **Where the state is**: below the stack or above the six argument words. -/
theorem state_geo (hpre : GlueLevelPre s m0) :
    (pOf m0).toNat + 61152 ≤ m0.regs.SP.toNat - 704 ∨ m0.regs.SP.toNat + 48 ≤ (pOf m0).toNat := by
  have h1 : (pOf m0).toNat + 61152 ≤ (stackBelow m0 glueLevelStack).toNat ∨
      (stackBelow m0 glueLevelStack).toNat + 704 ≤ (pOf m0).toNat :=
    hpre.2.2.2.2.2.2.2.2.1.2
  have h2 : (pOf m0).toNat + 61152 ≤ m0.regs.SP.toBitVec.toNat ∨
      m0.regs.SP.toBitVec.toNat + 48 ≤ (pOf m0).toNat :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hs : (stackBelow m0 glueLevelStack).toNat = m0.regs.SP.toNat - 704 :=
    Ring.base_toNat hpre.1.2.1
  have hS : 704 ≤ m0.regs.SP.toNat := hpre.1.2.1
  have e : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
  rw [hs] at h1
  rw [e] at h2
  generalize (pOf m0).toNat = a at *
  generalize m0.regs.SP.toNat = b at *
  omega

/-- The state is apart from the frame. -/
theorem state_not_frame (hpre : GlueLevelPre s m0) :
    ∀ q, InRange (pOf m0) stateBytes q → ¬InRange (base m0 112) 112 q := by
  have hap := Ring.apart_frame (F := 112) hpre.1.2.1 (by decide) hpre.2.2.2.2.2.2.2.2.1.2
  exact fun q hq ↦ NativeRustcVm.Transcript.not_inRange_of_apart hap
    hpre.2.2.2.2.2.2.2.2.1.1.2
    (Ring.base_noWrap (by have := hpre.1.2.1; rw [glueLevelStack_eq] at this; omega)) hq

/-- The frame is in the stack. -/
theorem frame_in_stack (hpre : GlueLevelPre s m0) {q : BitVec 64}
    (h : InRange (base m0 112) 112 q) : InRange (stackBelow m0 glueLevelStack) glueLevelStack q :=
  inRange_frame h (by decide) hpre.1.2.1

/-- **An input** apart from the stack and the state: its bytes as at the entry. -/
theorem input_same (hpre : GlueLevelPre s m0) {m : MachineData} (hfr : FR m0 m) {a : BitVec 64}
    {n : Nat} (hna : NoWrap a n) (hst : OffStack m0 a n glueLevelStack)
    (hap : Apart (pOf m0) stateBytes a n) :
    ∀ i < n, m.dmem.get? (a + BitVec.ofNat 64 i) = m0.dmem.get? (a + BitVec.ofNat 64 i) :=
  fun i hi ↦ by
    have hin : InRange a n (a + BitVec.ofNat 64 i) :=
      NativeRustcVm.inRange_add hi (by unfold NoWrap at hna; omega)
    exact hfr.same _ fun h ↦ h.elim
      (NativeRustcVm.Transcript.not_inRange_of_apart hst hna (Ring.base_noWrap hpre.1.2.1) hin)
      (NativeRustcVm.Transcript.not_inRange_of_apart (NativeRustcVm.Apart.symm hap) hna
        hpre.2.2.2.2.2.2.2.2.1.1.2 hin)

/-- **The six argument words** at the entry's SP, unchanged. -/
theorem arg_word (hpre : GlueLevelPre s m0) {m : MachineData} (hfr : FR m0 m) {i : Nat}
    (hi : i < 6) :
    NativeRustcVm.wordOf m.dmem (m0.regs.SP.toBitVec + BitVec.ofNat 64 (8 * i)) = whirStackArg m0 i := by
  have hS : 704 ≤ m0.regs.SP.toNat := hpre.1.2.1
  have e : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
  have hst : OffStack m0 m0.regs.SP.toBitVec 48 glueLevelStack := by
    show _ ∨ _
    right
    rw [show (stackBelow m0 glueLevelStack).toNat = m0.regs.SP.toNat - 704 from
      Ring.base_toNat hpre.1.2.1, e, glueLevelStack_eq]
    omega
  have := input_same hpre hfr hpre.2.2.2.2.2.2.2.1.2 hst hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact NativeRustcVm.wordOf_congr fun j hj ↦ by
    rw [NativeRustcVm.addr_add_add]
    exact this _ (by omega)

/-- **A block writing in the state**: the frame kept, the state's bytes but the written ones. -/
theorem fr_block [Labels] (hpre : GlueLevelPre s m0) {m m' : MachineData} {env : Env}
    {S S' : SState} {W : Nat → Prop} (h : FR m0 m) (hm : Match env S m) (hm' : Match env S' m')
    (hwf : env.WF) (hd : m.dmem = env.mem0) (hsp : S'.sp = S.sp)
    (hf : Foot env S' (pOf m0) stateBytes W) :
    FR m0 m' ∧ NativeRustcVm.Transcript.Agree m.dmem m'.dmem (pOf m0) stateBytes W := by
  have hpnw := hpre.2.2.2.2.2.2.2.2.1.1.2
  refine ⟨h.step (W := Written env S') (Match.sp_eq hm hm' hsp) (by simp)
    (fun q hq ↦ hm'.kept hwf q (hd ▸ hq)) (fun q hq ↦ by rw [hm'.get?_mem0 hwf hq, hd])
    (fun q hq ↦ .inr (written_of_foot hpnw hf hq)) fun pr hpr i hi hq ↦
      state_not_frame hpre _ (written_of_foot hpnw hf hq) ?_, hd ▸ agree_of_foot hm' hwf hpnw hf⟩
  have := slots_le pr hpr
  rw [NativeRustcVm.addr_add_add]
  exact NativeRustcVm.inRange_add (by omega) (by omega)

/-- **A callee writing `n` bytes at `a`** in the state keeps the frame. -/
theorem fr_out (hpre : GlueLevelPre s m0) {m m' : MachineData} {a : BitVec 64} {n : Nat}
    (h : FR m0 m) (ha : ∀ q, InRange a n q → InRange (pOf m0) stateBytes q) (hS : Saved m m')
    (hs : SameOutside m.dmem m'.dmem (fun q ↦ InRange a n q ∨ InRange (stackBelow m 0) 0 q)) :
    FR m0 m' :=
  h.call (N' := 0) hpre.1.2.1 (by decide) (by simp) slots_le ha (state_not_frame hpre) hS
    fun q hq ↦ hs q fun h' ↦ hq (h'.elim .inr .inl)

/-- A callee's change of the `n` bytes at offset `o` of the state. -/
theorem agree_changes {p : BitVec 64} {d d' : Mem 64} {o n : Nat} {b : BitVec 64}
    (hpnw : NoWrap p stateBytes) (hle : o + n ≤ stateBytes)
    (hs : SameOutside d d' (fun q ↦ InRange (off p o) n q ∨ InRange b 0 q)) :
    NativeRustcVm.Transcript.Agree d d' p stateBytes (fun j ↦ o ≤ j ∧ j < o + n) :=
  agree_of_sameOutside hs fun j hj hW h ↦ h.elim
    (not_inRange_off hpnw hj hle (by omega)) (fun h0 ↦ by unfold InRange at h0; omega)

variable [Host]

/-- **A call of `EW::mul`** keeps the frame and changes the stack only. -/
theorem mul_call (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (hpre : GlueLevelPre s m0)
    {st : MachineState} {next : Int64} (hfr : FR m0 st.data) (hso : SO m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel ∧ retOf st.data = next) {R : MachineState → Prop}
    (cont : ∀ m, FR m0 m → SO m0 m → EWMulPost st.data m →
      Eventually (step1 Host.exe) R ⟨m, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hmul hpc.1 (hfr.stackOk hpre.1 (by decide) (by decide)))
    fun ⟨m, pc⟩ ⟨hpc', hq⟩ ↦ by
      simp only at hpc' hq
      rw [hpc', hpc.2]
      refine cont m (hfr.call (N' := ewMulStack) hpre.1.2.1 (by decide) (by simp) slots_le
        (fun _ h ↦ h) (state_not_frame hpre) hq.2.2.2 fun q hq' ↦ hq.2.2.1 q fun h ↦ hq' (.inl h))
        ?_ hq
      intro q hq'
      rw [hq.2.2.1 q fun h ↦ hq' (inRange_stack_sub h hfr.sp (by decide) hpre.1.2.1)]
      exact hso q hq'

/-- **A block without writes** keeps the frame, and memory. -/
theorem reg_block {m m' : MachineData} {S' : SState} (hfr : FR m0 m) (hso : SO m0 m)
    (hm : Match (Env.ofMachine m []) S' m') (hmem : S'.mem = []) (hsp : S'.sp = .sp) :
    FR m0 m' ∧ SO m0 m' ∧ m'.dmem = m.dmem := by
  have hd := hm.dmem_eq (Env.wf_nil m) hmem
  refine ⟨Ring.Fr.ofBlock hfr (match_nil m) hm (Env.wf_nil m) rfl hmem hsp (by simp), ?_, hd⟩
  intro q hq
  rw [hd]
  exact hso q hq

end

end NativeRustcVmArm.Whir.GlueLevel
