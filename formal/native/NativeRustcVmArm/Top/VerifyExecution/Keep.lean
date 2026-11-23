module

public import NativeRustcVmArm.Top.VerifyExecution.Flow
public import NativeRustcVm.Top.Same
public import NativeRustcVm.Top.Walk
public import NativeRustcVm.Transcript.Update

/-!
# `verify_execution`: what a call keeps

The addresses a callee writes, as numbers (`Geo.inT`, `Geo.inW`, `At.inStk`); the working area's
bytes a callee does not write stay the same (`Geo.sameW`), and so do the bytecode and the public
input (`At.bc`, `At.pub`). The arguments the blocks compute (`eval_addW`, `eval_ptrW`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)

public section

variable [Labels] {a : DecArea} {m0 st : MachineData}

theorem Geo.inT (g : Geo a m0) {p : BitVec 64} (hp : InRange m0.regs.X0.toBitVec tstateBytes p) :
    m0.regs.X0.toBitVec.toNat ≤ p.toNat ∧ p.toNat < m0.regs.X0.toBitVec.toNat + 760 :=
  (inRange_nat g.tN).mp hp

theorem Geo.inW (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) {p : BitVec 64}
    (hp : InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n p) :
    m0.regs.X4.toBitVec.toNat + o ≤ p.toNat ∧ p.toNat < m0.regs.X4.toBitVec.toNat + o + n := by
  have hw := g.wAddr ho
  have := g.wN
  rw [inRange_nat (by rw [hw]; omega), hw] at hp
  exact hp

theorem At.inStk (h : At m0 st) (g : Geo a m0) {N : Nat} (hN : N ≤ 18288) {p : BitVec 64}
    (hp : InRange (stackBelow st N) N p) :
    m0.regs.SP.toBitVec.toNat - 96 - N ≤ p.toNat ∧ p.toNat < m0.regs.SP.toBitVec.toNat - 96 := by
  have hsb := h.sb g hN
  have := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  rw [inRange_nat (by rw [hsb]; omega), hsb] at hp
  omega

/-- **The working area's bytes from `o`** stay the same across a change outside them. -/
theorem Geo.sameW (g : Geo a m0) {d d' : DataMem} {W : BitVec 64 → Prop}
    (hs : SameOutside d d' W) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552)
    (hW : ∀ p, W p → p.toNat < m0.regs.X4.toBitVec.toNat + o ∨
      m0.regs.X4.toBitVec.toNat + o + n ≤ p.toNat) :
    NativeRustcVm.Layout.Same d d' (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n :=
  NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hp ↦ by
    have hp' := hW _ hp
    have hw := g.wAddr ho
    have := g.wN
    rw [toNat_addr (by rw [hw]; omega), hw] at hp'
    omega

/-- Words apart from every changed address stay. -/
theorem At.wordsAt' (h : At m0 st) (g : Geo a m0) {x : BitVec 64} {ws : List UInt64}
    (hw : NativeRustcVm.WordsAt m0.dmem x ws) (hN : x.toNat + 8 * ws.length ≤ 2 ^ 64)
    (ht : x.toNat + 8 * ws.length ≤ m0.regs.X0.toBitVec.toNat ∨
      m0.regs.X0.toBitVec.toNat + 760 ≤ x.toNat)
    (hww : x.toNat + 8 * ws.length ≤ m0.regs.X4.toBitVec.toNat ∨
      m0.regs.X4.toBitVec.toNat + 495552 ≤ x.toNat)
    (hs : x.toNat + 8 * ws.length ≤ m0.regs.SP.toBitVec.toNat - 18384 ∨
      m0.regs.SP.toBitVec.toNat ≤ x.toNat) : NativeRustcVm.WordsAt st.dmem x ws :=
  wordsAt_keep hw h.body.same hN fun p hp ↦ by
    rcases g.writable hp with hp | hp | hp <;> omega

/-- **The bytecode** stays. -/
theorem At.bc (h : At m0 st) (g : Geo a m0) {bcw : List UInt64}
    (hl : bcw.length = m0.regs.X2.toNat)
    (hw : NativeRustcVm.WordsAt m0.dmem m0.regs.X1.toBitVec bcw) :
    NativeRustcVm.WordsAt st.dmem m0.regs.X1.toBitVec bcw := by
  rcases Nat.eq_zero_or_pos m0.regs.X2.toNat with hn | hn
  · rw [List.eq_nil_of_length_eq_zero (hl.trans hn)]
    exact NativeRustcVm.wordsAt_nil _ _
  · have := g.bN
    have := g.bt hn
    have := g.bw hn
    have := g.bS hn
    exact h.wordsAt' g hw (by rw [hl]; omega) (by rw [hl]; omega) (by rw [hl]; omega)
      (by rw [hl]; omega)

/-- **The public input** stays. -/
theorem At.pub (h : At m0 st) (g : Geo a m0) {P : Vector UInt64 4}
    (hw : NativeRustcVm.WordsAt m0.dmem m0.regs.X3.toBitVec P.toList) :
    NativeRustcVm.WordsAt st.dmem m0.regs.X3.toBitVec P.toList := by
  have := g.pN
  have := g.tp
  have := g.pw
  have := g.pS
  have hl : P.toList.length = 4 := by simp
  exact h.wordsAt' g hw (by rw [hl]; omega) (by rw [hl]; omega) (by rw [hl]; omega)
    (by rw [hl]; omega)

theorem eval_addW (r : XReg) :
    (Sym.bin .add .W64 (.ptr 1 0) (.reg r)).eval (envOf m0 st) =
      m0.regs.X4.toBitVec + (st.regs.getXReg r).toBitVec := by
  simp [Sym.eval, BinOp.apply, ext, envOf, Env.ofMachine, Env.base]

theorem eval_ptrW (o : Int) :
    (Sym.ptr 1 o).eval (envOf m0 st) = m0.regs.X4.toBitVec + BitVec.ofInt 64 o := rfl


/-- The frame's first word is readable. -/
theorem At.readableSP (h : At m0 st) (g : Geo a m0) : Readable st st.regs.SP.toBitVec 8 := by
  have hF := frame_toNat g
  have := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  rw [h.body.sp]
  exact ⟨Mapped.within (h.frameMapped g) (by rw [hF]; omega) le_rfl (by omega),
    show _ ≤ _ by rw [hF]; omega⟩

/-- The frame's first word apart from a working-area range. -/
theorem At.spApartW (h : At m0 st) (g : Geo a m0) {o n : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) :
    NativeRustcVm.Apart st.regs.SP.toBitVec 8 (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := by
  have hF := frame_toNat g
  have := g.s
  have := g.wS
  show _ ∨ _
  rw [h.body.sp, hF, g.wAddr ho]
  omega

/-- The frame's first word apart from the `TState`. -/
theorem At.spApartT (h : At m0 st) (g : Geo a m0) :
    NativeRustcVm.Apart st.regs.SP.toBitVec 8 m0.regs.X0.toBitVec tstateBytes := by
  have hF := frame_toNat g
  have := g.s
  have := g.tS
  show _ ∨ _
  rw [h.body.sp, hF]
  unfold tstateBytes
  omega

/-- A working-area range a callee writes, as `WhirOut`. -/
theorem At.whirOut (h : At m0 st) (g : Geo a m0) {o n N : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) (hN : N ≤ 18288) :
    WhirOut st m0.regs.X0.toBitVec a (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n N :=
  ⟨h.outOk g ho hn hN, g.rodataApart ho hn⟩


/-- A working-area range only read, apart from the regions `ws` written. -/
theorem At.readIn (h : At m0 st) (g : Geo a m0) {o n N : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) (hN : N ≤ 18288) {ws : List NativeRustcVm.Region}
    (hws : ∀ w ∈ ws,
      NativeRustcVm.Apart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n w.addr w.size) :
    NativeRustcVmArm.ReadIn st (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n N ws :=
  ⟨h.readable g ho hn, h.offStack g ho hn hN, hws⟩

/-- The public input, only read, apart from the `TState` and a working-area range. -/
theorem At.pubIn (h : At m0 st) (g : Geo a m0) {o n N : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) (hN : N ≤ 18288) :
    NativeRustcVmArm.ReadIn st m0.regs.X3.toBitVec 32 N
      [⟨m0.regs.X0.toBitVec, tstateBytes⟩, ⟨m0.regs.X4.toBitVec + BitVec.ofNat 64 o, n⟩] := by
  have hsb := h.sb g hN
  have := g.pN
  have := g.pS
  have := g.tp
  have := g.pw
  have := g.s
  refine ⟨⟨h.mapped g.mP, by show _ ≤ _; omega⟩, by show _ ∨ _; rw [hsb]; omega, ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨by show _ ∨ _; unfold tstateBytes; omega, by show _ ∨ _; rw [g.wAddr ho]; omega⟩


/-- A working-area address is in neither the `TState` nor the decoded area. -/
theorem Geo.notTA_w (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552)
    {q : BitVec 64} (hq : InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n q) :
    ¬InRange m0.regs.X0.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have := g.inW ho hn hq
  have := g.tw
  have := g.aw
  refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · have := (inRange_nat g.tN).mp hi; omega
  · have := (inRange_nat g.aN).mp hi; omega

/-- A stack address is in neither the `TState` nor the decoded area. -/
theorem At.notTA_stk (h : At m0 st) (g : Geo a m0) {N : Nat} (hN : N ≤ 18288) {q : BitVec 64}
    (hq : InRange (stackBelow st N) N q) :
    ¬InRange m0.regs.X0.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have := h.inStk g hN hq
  have := g.tS
  have := g.aS
  refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · have := (inRange_nat g.tN).mp hi; omega
  · have := (inRange_nat g.aN).mp hi; omega


/-! ## The read-only data Keccak's GKR reads -/

omit [Labels] in
theorem rmfeProject_length : (NativeRustcVm.Data.Item.bytes .rmfeProject).length = 128 := by
  rw [NativeRustcVm.Data.Item.bytes, NativeRustcVm.length_wordsBytes,
    NativeRustcVm.Data.rmfeProject,
    List.length_map]
  rfl

omit [Labels] in
theorem keccakRho_length : (NativeRustcVm.Data.Item.bytes .keccakRho).length = 100 := by
  have h4 : ∀ x, (NativeRustcVm.Data.u32Bytes x).length = 4 := fun x ↦ by
    simp [NativeRustcVm.Data.u32Bytes, NativeRustcVm.length_wordBytes]
  rw [NativeRustcVm.Data.Item.bytes, NativeRustcVm.length_flatMap_const h4]
  rfl

/-- **`RMFE_PROJECT`** at its label, from the read-only data. -/
theorem projectAt_of {m : MachineData} {n : Nat} (h : RodataAt m n) : ProjectAt m := by
  have := h.bytesAt .rmfeProject
  have e : rmfeProjectW.toList = NativeRustcVm.Data.rmfeProject := by
    simp [rmfeProjectW, NativeRustcVm.Data.rmfeProject]
  unfold ProjectAt
  rw [e]
  exact this

/-- **`KECCAK_RHO`** at its label, from the read-only data. -/
theorem rhoAt_of {m : MachineData} {n : Nat} (h : RodataAt m n) : RhoAt m :=
  h.bytesAt .keccakRho

end

end NativeRustcVmArm.Top.VerifyExecution
