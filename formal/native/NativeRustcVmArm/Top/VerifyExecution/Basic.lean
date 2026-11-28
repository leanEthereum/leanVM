module

public import NativeRustcVmArm.Spec.Top
public import NativeRustcVmArm.Spec.Layout
public import NativeRustcVmArm.Spec.Bus
public import NativeRustcVmArm.Spec.Tables
public import NativeRustcVmArm.Spec.KeccakGkr
public import NativeRustcVmArm.Spec.Ring
public import NativeRustcVmArm.Spec.Whir
public import NativeRustcVmArm.Rodata.Keccak
public import NativeRustcVmArm.Top.VerifyExecution.Exec
public import NativeRustcVm.RodataLemmas

/-!
# `verify_execution`: where things are

The facts `VerifyExecutionPre` gives as numbers (`Geo`, `geo_of`): the stack below the entry's SP
(`S`), the `TState` (X0), the decoded area, the public input (X3), the working area (X4), the
bytecode (X1, X2 words), pairwise apart, mapped and apart from the read-only data. Between the
calls the frame's body (`At`: SP `S − 96`, the slots, X19 the working area, X20 the `TState`,
memory as at the entry but in the `TState`, the working area and the stack, `Writable`), from
which the callees' footprints follow (`At.stackOk`, `At.rodataAt`, `At.outOk`, …) and which a
call writing only those keeps (`At.call`, `wr_t`, `wr_w`, `wr_stk`).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution
open NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)

public section

theorem verifyExecutionStack_eq : verifyExecutionStack = 18384 := rfl
theorem workAreaBytes_eq : workAreaBytes = 495552 := rfl
theorem tstateBytes_eq : tstateBytes = 760 := rfl

section
variable [Labels]

/-- The addresses `verify_execution` may change: the `TState`, the working area, the stack. -/
@[expose] def Writable (m0 : MachineData) : BitVec 64 → Prop :=
  NativeRustcVm.InAny [⟨m0.regs.X0.toBitVec, tstateBytes⟩, ⟨m0.regs.X4.toBitVec, workAreaBytes⟩,
    stackR m0 verifyExecutionStack]

/-- `VerifyExecutionPre`'s addresses as numbers, its areas mapped and apart from the read-only
data. -/
structure Geo (a : DecArea) (m0 : MachineData) : Prop where
  s : 18384 ≤ m0.regs.SP.toBitVec.toNat
  al : m0.regs.SP.toBitVec.toNat % 16 = 0
  tN : m0.regs.X0.toBitVec.toNat + 760 ≤ 2 ^ 64
  aN : a.words.toNat + 8 * a.len ≤ 2 ^ 64
  pN : m0.regs.X3.toBitVec.toNat + 32 ≤ 2 ^ 64
  wN : m0.regs.X4.toBitVec.toNat + 495552 ≤ 2 ^ 64
  bN : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤ 2 ^ 64
  tS : m0.regs.X0.toBitVec.toNat + 760 ≤ m0.regs.SP.toBitVec.toNat - 18384 ∨
    m0.regs.SP.toBitVec.toNat ≤ m0.regs.X0.toBitVec.toNat
  aS : a.words.toNat + 8 * a.len ≤ m0.regs.SP.toBitVec.toNat - 18384 ∨
    m0.regs.SP.toBitVec.toNat ≤ a.words.toNat
  pS : m0.regs.X3.toBitVec.toNat + 32 ≤ m0.regs.SP.toBitVec.toNat - 18384 ∨
    m0.regs.SP.toBitVec.toNat ≤ m0.regs.X3.toBitVec.toNat
  wS : m0.regs.X4.toBitVec.toNat + 495552 ≤ m0.regs.SP.toBitVec.toNat - 18384 ∨
    m0.regs.SP.toBitVec.toNat ≤ m0.regs.X4.toBitVec.toNat
  ta : m0.regs.X0.toBitVec.toNat + 760 ≤ a.words.toNat ∨
    a.words.toNat + 8 * a.len ≤ m0.regs.X0.toBitVec.toNat
  tp : m0.regs.X0.toBitVec.toNat + 760 ≤ m0.regs.X3.toBitVec.toNat ∨
    m0.regs.X3.toBitVec.toNat + 32 ≤ m0.regs.X0.toBitVec.toNat
  tw : m0.regs.X0.toBitVec.toNat + 760 ≤ m0.regs.X4.toBitVec.toNat ∨
    m0.regs.X4.toBitVec.toNat + 495552 ≤ m0.regs.X0.toBitVec.toNat
  ap : a.words.toNat + 8 * a.len ≤ m0.regs.X3.toBitVec.toNat ∨
    m0.regs.X3.toBitVec.toNat + 32 ≤ a.words.toNat
  aw : a.words.toNat + 8 * a.len ≤ m0.regs.X4.toBitVec.toNat ∨
    m0.regs.X4.toBitVec.toNat + 495552 ≤ a.words.toNat
  pw : m0.regs.X3.toBitVec.toNat + 32 ≤ m0.regs.X4.toBitVec.toNat ∨
    m0.regs.X4.toBitVec.toNat + 495552 ≤ m0.regs.X3.toBitVec.toNat
  bS : 0 < m0.regs.X2.toNat →
    m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤ m0.regs.SP.toBitVec.toNat - 18384 ∨
      m0.regs.SP.toBitVec.toNat ≤ m0.regs.X1.toBitVec.toNat
  bt : 0 < m0.regs.X2.toNat → m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤
    m0.regs.X0.toBitVec.toNat ∨ m0.regs.X0.toBitVec.toNat + 760 ≤ m0.regs.X1.toBitVec.toNat
  ba : 0 < m0.regs.X2.toNat → m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤
    a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ m0.regs.X1.toBitVec.toNat
  bw : 0 < m0.regs.X2.toNat → m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤
    m0.regs.X4.toBitVec.toNat ∨ m0.regs.X4.toBitVec.toNat + 495552 ≤ m0.regs.X1.toBitVec.toNat
  n32 : 9 + 8 * m0.regs.X2.toNat < 2 ^ 32
  mS : Mapped m0.dmem (stackBelow m0 verifyExecutionStack) verifyExecutionStack
  mP : Mapped m0.dmem m0.regs.X3.toBitVec 32
  mW : Mapped m0.dmem m0.regs.X4.toBitVec 495552
  mB : Mapped m0.dmem m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat)
  rod : RodataAt m0 verifyExecutionStack
  rt : RodataApart m0.regs.X0.toBitVec 760
  ra : RodataApart a.words (8 * a.len)
  rp : RodataApart m0.regs.X3.toBitVec 32
  rw : RodataApart m0.regs.X4.toBitVec 495552
  rb : 0 < m0.regs.X2.toNat → RodataApart m0.regs.X1.toBitVec (8 * m0.regs.X2.toNat)

theorem geo_of {a : DecArea} {s : TState} {m0 : MachineData} (hpre : VerifyExecutionPre a s m0) :
    Geo a m0 := by
  obtain ⟨⟨hal, hsN, hmS⟩, hrod, hn32, hts, -, ⟨hbM, hbN⟩, ⟨hpM, hpN⟩, ⟨hwM, hwN⟩, hdis, hapR,
    hbcD⟩ := hpre
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs : 18384 ≤ m0.regs.SP.toBitVec.toNat := hsN
  have hsb : (stackBelow m0 18384).toNat = m0.regs.SP.toBitVec.toNat - 18384 :=
    toNat_subAddr hs
  have hTN : m0.regs.X0.toBitVec.toNat + 760 ≤ 2 ^ 64 := hts.footprint.1.2
  have hAN : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hts.footprint.2.1.2
  simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart, stackR,
    DecArea.region, verifyExecutionStack_eq, tstateBytes_eq, workAreaBytes_eq] at hdis
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hdis
  rw [hsb] at h01 h02 h03 h04
  simp only [ApartRodata, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, DecArea.region] at hapR
  obtain ⟨hrt, hra, hrp, hrw⟩ := hapR
  refine ⟨hs, hal, hTN, hAN, hpN, hwN, hbN, by omega, by omega, by omega, by omega, h12, h13, h14,
    h23, h24, h34, fun hn ↦ ?_, fun hn ↦ ?_, fun hn ↦ ?_, fun hn ↦ ?_, hn32, hmS, hpM, hwM, hbM,
    hrod, hrt, hra, hrp, hrw, fun hn ↦ (hbcD hn).2⟩
  all_goals
    obtain ⟨h, -⟩ := hbcD hn
    simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart,
      stackR, DecArea.region, verifyExecutionStack_eq, tstateBytes_eq, workAreaBytes_eq] at h
    obtain ⟨⟨b0, -⟩, ⟨b1, b2, b3⟩, -⟩ := h
    rw [hsb] at b0
    omega


/-! ## The frame between the calls -/

omit [Labels] in
theorem slotsIn : SlotsIn slots 16 96 := by
  intro p hp
  simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- Between the calls: the frame's body, X19 the working area, X20 the `TState`. -/
structure At (m0 st : MachineData) : Prop where
  body : Body m0 96 slots (Writable m0) st
  x19 : st.regs.X19 = m0.regs.X4
  x20 : st.regs.X20 = m0.regs.X0

variable {a : DecArea} {m0 st : MachineData}

/-- A working-area address as a number. -/
theorem Geo.wAddr (g : Geo a m0) {o : Nat} (ho : o < 495552) :
    (m0.regs.X4.toBitVec + BitVec.ofNat 64 o).toNat = m0.regs.X4.toBitVec.toNat + o :=
  toNat_addr (by have := g.wN; omega)

/-- A changed address as numbers. -/
theorem Geo.writable (g : Geo a m0) {p : BitVec 64} (hp : Writable m0 p) :
    (m0.regs.X0.toBitVec.toNat ≤ p.toNat ∧ p.toNat < m0.regs.X0.toBitVec.toNat + 760) ∨
    (m0.regs.X4.toBitVec.toNat ≤ p.toNat ∧ p.toNat < m0.regs.X4.toBitVec.toNat + 495552) ∨
    (m0.regs.SP.toBitVec.toNat - 18384 ≤ p.toNat ∧ p.toNat < m0.regs.SP.toBitVec.toNat) := by
  have hs := g.s
  simp only [Writable, NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds, stackR] at hp
  rcases hp with hp | hp | hp
  · exact .inl ((inRange_nat g.tN).mp hp)
  · exact .inr (.inl ((inRange_nat g.wN).mp hp))
  · exact .inr (.inr ((inRange_below hs).mp hp))

theorem At.sp (h : At m0 st) (g : Geo a m0) :
    st.regs.SP.toBitVec.toNat = m0.regs.SP.toBitVec.toNat - 96 := by
  rw [h.body.sp]; exact toNat_subAddr (by have := g.s; omega)

theorem At.sb (h : At m0 st) (g : Geo a m0) {N : Nat} (hN : N ≤ 18288) :
    (stackBelow st N).toNat = m0.regs.SP.toBitVec.toNat - 96 - N := by
  show (st.regs.SP.toBitVec - BitVec.ofNat 64 N).toNat = _
  rw [toNat_subAddr (by rw [h.sp g]; have := g.s; omega), h.sp g]

omit [Labels] in
theorem At.mapped (h : At m0 st) {x : BitVec 64} {n : Nat} (hm : Mapped m0.dmem x n) :
    Mapped st.dmem x n :=
  Mapped.kept hm h.body.kept

/-- The stack below SP is the entry's. -/
theorem At.stackMapped (h : At m0 st) (g : Geo a m0) {N : Nat} (hN : N ≤ 18288) :
    Mapped st.dmem (stackBelow st N) N := by
  have hs := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  have hsb : (stackBelow m0 verifyExecutionStack).toNat = m0.regs.SP.toBitVec.toNat - 18384 :=
    toNat_subAddr hs
  have := h.sb g hN
  exact h.mapped (Mapped.within g.mS (by rw [hsb]; unfold verifyExecutionStack; omega)
    (by rw [hsb]; omega) (by rw [hsb]; unfold verifyExecutionStack; omega))

theorem At.stackOk (h : At m0 st) (g : Geo a m0) {N : Nat} (hN : N ≤ 18288) : StackOk st N := by
  have hsp := h.sp g
  have hal := g.al
  have hs := g.s
  refine ⟨?_, ?_, h.stackMapped g hN⟩
  · show st.regs.SP.toBitVec.toNat % 16 = 0
    omega
  · show N ≤ st.regs.SP.toBitVec.toNat
    omega

/-- **The read-only data** stays at its labels, apart from the stack below SP. -/
theorem At.rodataAt (h : At m0 st) (g : Geo a m0) {N : Nat} (hN : N ≤ 18288) : RodataAt st N := by
  intro it
  have hs := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  have hsb : (stackBelow m0 verifyExecutionStack).toNat = m0.regs.SP.toBitVec.toNat - 18384 :=
    toNat_subAddr hs
  obtain ⟨hb, hnw, hap⟩ := g.rod it
  have ht := g.rt it
  have hw := g.rw it
  unfold NativeRustcVm.Apart at hap ht hw
  unfold NativeRustcVm.NoWrap at hnw
  rw [hsb] at hap
  have hsb' := h.sb g hN
  refine ⟨bytesAt_keep hb h.body.same hnw fun p hp ↦ ?_, hnw, ?_⟩
  · rcases g.writable hp with hp | hp | hp <;> unfold verifyExecutionStack at * <;> omega
  · unfold NativeRustcVm.Apart; rw [hsb']; unfold verifyExecutionStack at hap; omega

omit [Labels] in
theorem keccakRC_length : (NativeRustcVm.Data.Item.bytes .keccakRC).length = 192 := by
  rw [NativeRustcVm.Data.Item.bytes, NativeRustcVm.length_wordsBytes, keccakRC_eq]; rfl

/-- The working area's bytes from `o`: apart from the round constants. -/
theorem Geo.rcApart (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) :
    NativeRustcVm.Apart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n rcAddr 192 := by
  have h := g.rw .keccakRC
  rw [keccakRC_length, ← rcAddr_eq] at h
  unfold NativeRustcVm.Apart at h ⊢
  rw [g.wAddr ho]
  omega

/-- The working area's bytes from `o`: apart from the read-only data. -/
theorem Geo.rodataApart (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) :
    RodataApart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := fun it ↦ by
  have h := g.rw it
  unfold NativeRustcVm.Apart at h ⊢
  rw [g.wAddr ho]
  omega

/-- The `TState` apart from the round constants. -/
theorem Geo.tRc (g : Geo a m0) :
    NativeRustcVm.Apart m0.regs.X0.toBitVec tstateBytes rcAddr 192 := by
  have h := g.rt .keccakRC
  rw [keccakRC_length, ← rcAddr_eq] at h
  exact h

/-- **The `TState`** apart from the stack below SP and the round constants. -/
theorem At.tstateOk (h : At m0 st) (g : Geo a m0) {N : Nat} (hN : N ≤ 18288) :
    TStateOk st m0.regs.X0.toBitVec a N := by
  have hsb := h.sb g hN
  have := g.tS
  have := g.aS
  have := g.s
  refine ⟨?_, ?_, g.tRc⟩ <;> show _ ∨ _ <;> rw [hsb] <;> (try unfold tstateBytes) <;> omega

/-- The working area's bytes from `o` as an output beside the `TState`. -/
theorem At.outOk (h : At m0 st) (g : Geo a m0) {o n N : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) (hN : N ≤ 18288) :
    OutOk st m0.regs.X0.toBitVec a (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n N := by
  have hsb := h.sb g hN
  have hw := g.wAddr ho
  have := g.wS
  have := g.tw
  have := g.aw
  have := g.wN
  have := g.s
  refine ⟨h.mapped (Mapped.within g.mW (by omega) (by omega) (by omega)), ?_, ?_, ?_, ?_,
    g.rcApart ho hn⟩
  · show _ ≤ _; omega
  all_goals show _ ∨ _; (try rw [hsb]); (try unfold tstateBytes); omega

/-- The working area's bytes from `o` are readable. -/
theorem At.readable (h : At m0 st) (g : Geo a m0) {o n : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) : Readable st (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n := by
  have hw := g.wAddr ho
  have := g.wN
  exact ⟨h.mapped (Mapped.within g.mW (by omega) (by omega) (by omega)),
    by show _ ≤ _; omega⟩

/-- The working area's bytes from `o` are apart from the stack below SP. -/
theorem At.offStack (h : At m0 st) (g : Geo a m0) {o n N : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) (hN : N ≤ 18288) :
    OffStack st (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n N := by
  have hsb := h.sb g hN
  have hw := g.wAddr ho
  have := g.wS
  have := g.s
  show _ ∨ _; rw [hsb, hw]; omega

/-- Two working-area ranges that do not overlap are apart. -/
theorem Geo.apartW (g : Geo a m0) {o n o' n' : Nat} (ho : o < 495552) (ho' : o' < 495552)
    (hle : o + n ≤ o' ∨ o' + n' ≤ o) :
    NativeRustcVm.Apart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n
      (m0.regs.X4.toBitVec + BitVec.ofNat 64 o') n' := by
  unfold NativeRustcVm.Apart; rw [g.wAddr ho, g.wAddr ho']; omega

/-- A working-area range is apart from the `TState`. -/
theorem Geo.apartWT (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) :
    NativeRustcVm.Apart (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n m0.regs.X0.toBitVec
      tstateBytes := by
  have := g.tw
  unfold NativeRustcVm.Apart tstateBytes; rw [g.wAddr ho]; omega

/-! ## A call -/

/-- A call writing only the `TState`, the working area and the stack below SP keeps the body. -/
theorem At.call (h : At m0 st) (g : Geo a m0) {st' : MachineData} {W : BitVec 64 → Prop}
    (hs : SameOutside st.dmem st'.dmem W) (hsv : Saved st st')
    (hW : ∀ p, W p → Writable m0 p ∧
      (p.toNat < m0.regs.SP.toBitVec.toNat - 96 + 16 ∨ m0.regs.SP.toBitVec.toNat ≤ p.toNat)) :
    At m0 st' :=
  ⟨h.body.call slotsIn (by have := g.s; omega) hs hsv hW, (hsv.1 .X19 rfl).trans h.x19,
    (hsv.1 .X20 rfl).trans h.x20⟩

/-- A write into the `TState`. -/
theorem wr_t (g : Geo a m0) {p : BitVec 64} (hp : InRange m0.regs.X0.toBitVec tstateBytes p) :
    Writable m0 p ∧
      (p.toNat < m0.regs.SP.toBitVec.toNat - 96 + 16 ∨ m0.regs.SP.toBitVec.toNat ≤ p.toNat) := by
  refine ⟨⟨_, List.mem_cons_self, hp⟩, ?_⟩
  have := (inRange_nat g.tN).mp hp
  have := g.tS
  have := g.s
  omega

/-- A write into the working area. -/
theorem wr_w (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) {p : BitVec 64}
    (hp : InRange (m0.regs.X4.toBitVec + BitVec.ofNat 64 o) n p) :
    Writable m0 p ∧
      (p.toNat < m0.regs.SP.toBitVec.toNat - 96 + 16 ∨ m0.regs.SP.toBitVec.toNat ≤ p.toNat) := by
  have hw := g.wAddr ho
  have := g.wS
  have := g.s
  have hp' := (inRange_nat (by rw [hw]; have := g.wN; omega)).mp hp
  rw [hw] at hp'
  refine ⟨⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩, by omega⟩
  show InRange m0.regs.X4.toBitVec workAreaBytes p
  rw [workAreaBytes_eq, inRange_nat g.wN]
  omega

/-- A write into the stack below SP. -/
theorem wr_stk (h : At m0 st) (g : Geo a m0) {N : Nat} (hN : N ≤ 18288) {p : BitVec 64}
    (hp : InRange (stackBelow st N) N p) :
    Writable m0 p ∧
      (p.toNat < m0.regs.SP.toBitVec.toNat - 96 + 16 ∨ m0.regs.SP.toBitVec.toNat ≤ p.toNat) := by
  have hsb := h.sb g hN
  have := g.s
  have hsl := m0.regs.SP.toBitVec.isLt
  have hp' := (inRange_nat (by rw [hsb]; omega)).mp hp
  rw [hsb] at hp'
  refine ⟨⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩, by omega⟩
  show InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 verifyExecutionStack) verifyExecutionStack p
  rw [inRange_below (show verifyExecutionStack ≤ _ from this)]
  unfold verifyExecutionStack
  omega

end

end

end NativeRustcVmArm.Top.VerifyExecution
