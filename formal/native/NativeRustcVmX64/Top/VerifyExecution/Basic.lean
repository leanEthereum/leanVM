module

public import NativeRustcVmX64.Top.VerifyExecution.Exec
public import NativeRustcVmX64.Top.Basic
public import NativeRustcVmX64.Got
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcVmX64.Spec.Bus
public import NativeRustcVmX64.Spec.Tables
public import NativeRustcVmX64.Spec.KeccakGkr
public import NativeRustcVmX64.Spec.Ring
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVm.Top.Walk
public import NativeRustcVm.Top.Same
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `verify_execution`: where things are (x86-64)

The addresses it may change (`Writable`: the `TState`, the working area, its stack); what
`VerifyExecutionPre` gives as numbers, relative to the stack's bottom `vsb m0` (`Geo`, `geo_of`);
between the calls (`At`: the frame, RSP at offset `40`, the changes `Writable`, RBX the working
area, R14 the `TState`); at a call (`AtCall`: RSP at offset `32`, a callee's stack below it), the
facts a callee's precondition asks of the stack, the read-only data, the `TState` and the working
area's parts (`AtCall.stackOk`, `rodataAt`, `tstateOk`, `outOk`, …), the preserved loader slots
(`AtCall.got`), and the frame after it (`AtCall.ret`).
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Top (workAreaBytes)

/-- The stack's bottom: the `17888` bytes below the entry's RSP start here. -/
@[expose] public def vsb (m0 : MachineData) : Nat := (stackBelow m0 17888).toNat

public section

theorem vsb_eq (m0 : MachineData) : (stackBelow m0 17888).toNat = vsb m0 := rfl

theorem verifyExecutionStack_eq : verifyExecutionStack = 17888 := rfl
theorem workAreaBytes_eq : workAreaBytes = 495552 := rfl
theorem tstateBytes_eq : tstateBytes = 760 := rfl

section
variable [Labels]

/-- The addresses `verify_execution` may change: the `TState`, the working area, its stack. -/
@[expose] def Writable (m0 : MachineData) : BitVec 64 → Prop :=
  NativeRustcVm.InAny [⟨reg m0 .rdi, tstateBytes⟩, ⟨reg m0 .r8, workAreaBytes⟩,
    frameR m0 verifyExecutionStack]

/-- What `verify_execution` ends in, its walk's result `r`: returned, AL `r`'s success, the
`TState` its last state, the changes `Writable`, the callee-saved registers kept. -/
@[expose] def Done (a : DecArea) (m0 : MachineData) (r : Option (Unit × TState))
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ OkAl st.data r.isSome ∧
    NextAt st.data.dmem (reg m0 .rdi) a r ∧
    NativeRustcVm.SameOutside m0.dmem st.data.dmem (Writable m0) ∧ Saved m0 st.data

end

end

/-- `VerifyExecutionPre`'s addresses as numbers, relative to the stack's bottom; its areas mapped
and apart from the read-only data. -/
public structure Geo [Labels] (a : DecArea) (m0 : MachineData) : Prop where
  R : (rspOf m0).toNat = vsb m0 + 17888
  e8 : vsb m0 + 17896 ≤ 2 ^ 64
  tN : (reg m0 .rdi).toNat + 760 ≤ 2 ^ 64
  aN : a.words.toNat + 8 * a.len ≤ 2 ^ 64
  pN : (reg m0 .rcx).toNat + 32 ≤ 2 ^ 64
  wN : (reg m0 .r8).toNat + 495552 ≤ 2 ^ 64
  bN : (reg m0 .rsi).toNat + 8 * (reg m0 .rdx).toNat ≤ 2 ^ 64
  tS : (reg m0 .rdi).toNat + 760 ≤ vsb m0 ∨ vsb m0 + 17896 ≤ (reg m0 .rdi).toNat
  aS : a.words.toNat + 8 * a.len ≤ vsb m0 ∨ vsb m0 + 17896 ≤ a.words.toNat
  pS : (reg m0 .rcx).toNat + 32 ≤ vsb m0 ∨ vsb m0 + 17896 ≤ (reg m0 .rcx).toNat
  wS : (reg m0 .r8).toNat + 495552 ≤ vsb m0 ∨ vsb m0 + 17896 ≤ (reg m0 .r8).toNat
  ta : (reg m0 .rdi).toNat + 760 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (reg m0 .rdi).toNat
  tp : (reg m0 .rdi).toNat + 760 ≤ (reg m0 .rcx).toNat ∨
    (reg m0 .rcx).toNat + 32 ≤ (reg m0 .rdi).toNat
  tw : (reg m0 .rdi).toNat + 760 ≤ (reg m0 .r8).toNat ∨
    (reg m0 .r8).toNat + 495552 ≤ (reg m0 .rdi).toNat
  ap : a.words.toNat + 8 * a.len ≤ (reg m0 .rcx).toNat ∨ (reg m0 .rcx).toNat + 32 ≤ a.words.toNat
  aw : a.words.toNat + 8 * a.len ≤ (reg m0 .r8).toNat ∨
    (reg m0 .r8).toNat + 495552 ≤ a.words.toNat
  pw : (reg m0 .rcx).toNat + 32 ≤ (reg m0 .r8).toNat ∨
    (reg m0 .r8).toNat + 495552 ≤ (reg m0 .rcx).toNat
  bS : 0 < (reg m0 .rdx).toNat → (reg m0 .rsi).toNat + 8 * (reg m0 .rdx).toNat ≤ vsb m0 ∨
    vsb m0 + 17896 ≤ (reg m0 .rsi).toNat
  bt : 0 < (reg m0 .rdx).toNat → (reg m0 .rsi).toNat + 8 * (reg m0 .rdx).toNat ≤
    (reg m0 .rdi).toNat ∨ (reg m0 .rdi).toNat + 760 ≤ (reg m0 .rsi).toNat
  ba : 0 < (reg m0 .rdx).toNat → (reg m0 .rsi).toNat + 8 * (reg m0 .rdx).toNat ≤
    a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (reg m0 .rsi).toNat
  bw : 0 < (reg m0 .rdx).toNat → (reg m0 .rsi).toNat + 8 * (reg m0 .rdx).toNat ≤
    (reg m0 .r8).toNat ∨ (reg m0 .r8).toNat + 495552 ≤ (reg m0 .rsi).toNat
  n32 : 9 + 8 * (reg m0 .rdx).toNat < 2 ^ 32
  mS : NativeRustcVm.Mapped m0.dmem (stackBelow m0 17888) (17888 + 8)
  mP : NativeRustcVm.Mapped m0.dmem (reg m0 .rcx) 32
  mW : NativeRustcVm.Mapped m0.dmem (reg m0 .r8) 495552
  mB : NativeRustcVm.Mapped m0.dmem (reg m0 .rsi) (8 * (reg m0 .rdx).toNat)
  rod : RodataAt m0 17888
  rt : RodataApart (reg m0 .rdi) 760
  ra : RodataApart a.words (8 * a.len)
  rp : RodataApart (reg m0 .rcx) 32
  rw : RodataApart (reg m0 .r8) 495552
  rb : 0 < (reg m0 .rdx).toNat → RodataApart (reg m0 .rsi) (8 * (reg m0 .rdx).toNat)
  got : GotAt m0 verifyExecutionStack
    ([(reg m0 .rdi, tstateBytes), (a.words, 8 * a.len),
      (reg m0 .rcx, 32), (reg m0 .r8, workAreaBytes)] ++ rodataAreas ++
      if (reg m0 .rdx).toNat = 0 then [] else
        [(reg m0 .rsi, 8 * (reg m0 .rdx).toNat)]) ["memcpy", "memset"]

public section

theorem geo_of [Labels] {a : DecArea} {s : TState} {m0 : MachineData}
    (hpre : VerifyExecutionPre a s m0) : Geo a m0 := by
  obtain ⟨hst, hrod, hn32, hts, -, ⟨hbM, hbN⟩, ⟨hpM, hpN⟩, ⟨hwM, hwN⟩, hdis, hapR, hbcD, hgot⟩ := hpre
  have hs : 17888 ≤ (rspOf m0).toNat := hst.1
  have h8 := hst.2.1
  have hR : (rspOf m0).toNat = vsb m0 + 17888 := by rw [vsb, stackBelow_toNat hs]; omega
  have hTN : (reg m0 .rdi).toNat + 760 ≤ 2 ^ 64 := hts.footprint.1.2
  have hAN : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hts.footprint.2.1.2
  simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
    false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart, stackR,
    DecArea.region, verifyExecutionStack_eq, tstateBytes_eq, workAreaBytes_eq, vsb_eq] at hdis
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hdis
  simp only [ApartRodata, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, DecArea.region] at hapR
  obtain ⟨hrt, hra, hrp, hrw⟩ := hapR
  refine ⟨hR, by omega, hTN, hAN, hpN, hwN, hbN, by omega, by omega, by omega, by omega, h12, h13,
    h14, h23, h24, h34, fun hn ↦ ?_, fun hn ↦ ?_, fun hn ↦ ?_, fun hn ↦ ?_, hn32, hst.2.2, hpM,
    hwM, hbM, hrod, hrt, hra, hrp, hrw, fun hn ↦ (hbcD hn).2, hgot⟩
  all_goals
    obtain ⟨h, -⟩ := hbcD hn
    simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart,
      stackR, DecArea.region, verifyExecutionStack_eq, tstateBytes_eq, workAreaBytes_eq,
      vsb_eq] at h
    obtain ⟨⟨b0, -, -, -⟩, ⟨b1, b2, b3⟩, -⟩ := h
    omega

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 96 := by decide
theorem slots_ge : ∀ p ∈ slots, 48 ≤ p.1 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

end

/-- Between the calls: the frame, RSP at offset `40`; the changes `Writable`; RBX the working
area, R14 the `TState`. -/
public structure At [Labels] (m0 d : MachineData) : Prop where
  frame : Frame m0 96 slots 40 d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (Writable m0)
  rbx : reg d .rbx = reg m0 .r8
  r14 : reg d .r14 = reg m0 .rdi

/-- At a call (RSP at offset `o`, `32` but for `verify_stacked_opening`'s `0`, the return address
below it): the frame, the changes. -/
public structure AtCall [Labels] (m0 d : MachineData) (o : Nat := 32) : Prop where
  frame : Frame m0 96 slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (Writable m0)

public section

variable [Labels] {a : DecArea} {m0 d : MachineData} {c : Nat}

/-- The frame's base as a number. -/
theorem Geo.F (g : Geo a m0) : (stackBelow m0 96).toNat = vsb m0 + 17792 := by
  rw [stackBelow_toNat (by have := g.R; omega)]; have := g.R; omega

/-- A working-area address as a number. -/
theorem Geo.wo (g : Geo a m0) {o : Nat} (ho : o < 495552) :
    (off (reg m0 .r8) o).toNat = (reg m0 .r8).toNat + o :=
  toNat_off (by have := g.wN; have := (reg m0 .r8).isLt; omega)

theorem Geo.fnw (g : Geo a m0) : NativeRustcVm.NoWrap (stackBelow m0 96) (96 + 8) := by
  unfold NativeRustcVm.NoWrap; rw [g.F]; have := g.e8; omega

theorem Geo.fmapped (g : Geo a m0) :
    NativeRustcVm.Mapped m0.dmem (stackBelow m0 96) (96 + 8) := by
  intro i hi
  have e : stackBelow m0 96 + BitVec.ofNat 64 i = stackBelow m0 17888 + BitVec.ofNat 64 (17792 + i) := by
    apply BitVec.eq_of_toNat_eq
    rw [NativeRustcVm.toNat_add_ofNat (by rw [g.F]; have := g.e8; omega),
      NativeRustcVm.toNat_add_ofNat (by rw [vsb_eq]; have := g.e8; omega), g.F, vsb_eq]
    omega
  rw [e]
  exact g.mS _ (by omega)

/-- A changed address as numbers. -/
theorem Geo.writable (g : Geo a m0) {p : BitVec 64} (hp : Writable m0 p) :
    ((reg m0 .rdi).toNat ≤ p.toNat ∧ p.toNat < (reg m0 .rdi).toNat + 760) ∨
    ((reg m0 .r8).toNat ≤ p.toNat ∧ p.toNat < (reg m0 .r8).toNat + 495552) ∨
    (vsb m0 ≤ p.toNat ∧ p.toNat < vsb m0 + 17888) := by
  rcases inAny3 hp with hp | hp | hp
  · exact .inl ((inR g.tN).mp hp)
  · exact .inr (.inl ((inR g.wN).mp hp))
  · refine .inr (.inr ?_)
    have := (inR (a := stackBelow m0 17888) (n := 17888)
      (by unfold NativeRustcVm.NoWrap; rw [vsb_eq]; have := g.e8; omega)).mp hp
    rwa [vsb_eq] at this

omit [Labels] in
/-- An address of the `TState` is writable. -/
theorem wr_t {p : BitVec 64} (hp : NativeRustcVm.InRange (reg m0 .rdi) tstateBytes p) :
    Writable m0 p := ⟨_, List.mem_cons_self, hp⟩

/-- An address of the working area is writable. -/
theorem wr_w (g : Geo a m0) {p : BitVec 64} (hp : (reg m0 .r8).toNat ≤ p.toNat ∧
    p.toNat < (reg m0 .r8).toNat + 495552) : Writable m0 p :=
  ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, (inR g.wN).mpr hp⟩

/-- An address of the stack is writable. -/
theorem wr_s (g : Geo a m0) {p : BitVec 64} (hp : vsb m0 ≤ p.toNat ∧ p.toNat < vsb m0 + 17888) :
    Writable m0 p :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    (inR (a := stackBelow m0 17888) (n := 17888)
      (by unfold NativeRustcVm.NoWrap; rw [vsb_eq]; have := g.e8; omega)).mpr
      (by rw [vsb_eq]; exact hp)⟩

/-- **A block between the calls ending in a call**: from `At`, a block keeping the frame, writing
only below offset `48` of it, ends in `AtCall`. -/
theorem At.toCall (h : At m0 d) (g : Geo a m0) {d' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 d 96 rest vars ret).WF) (hm : Match (frameEnv m0 d 96 rest vars ret) S d')
    (hmid : MidOk 96 32 slots S = true) {hi : Nat} (hhi : hi ≤ 48)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ hi) : AtCall m0 d' := by
  refine ⟨Frame.of_block h.frame hwf hm hmid slots_le, fun q hq ↦ ?_⟩
  have hs := sameOutside_low hwf hm (r := 0) rfl (by omega) hw
  rw [hs q fun hq' ↦ hq (wr_s g (by
    rw [inR (by unfold NativeRustcVm.NoWrap; rw [g.F]; have := g.e8; omega), g.F] at hq'
    omega))]
  exact h.same q hq

theorem Geo.stackOk (g : Geo a m0) : StackOk m0 verifyExecutionStack := by
  refine ⟨by rw [verifyExecutionStack_eq]; have := g.R; omega, by have := g.R; have := g.e8; omega, ?_⟩
  exact g.mS

/-- The callee's stack below the frame, `N` bytes, as a number. -/
theorem Geo.cs (g : Geo a m0) {N : Nat} (hN : N ≤ 17824) :
    (stackBelow m0 (64 + N)).toNat = vsb m0 + 17824 - N := by
  rw [stackBelow_toNat (by have := g.R; omega)]; have := g.R; omega

/-- The callee's RSP. -/
theorem AtCall.sp (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) :
    rspOf d = stackBelow m0 (96 - c) := by
  rw [h.frame.sp]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_off (by rw [g.F]; have := g.e8; omega), g.F,
    stackBelow_toNat (by have := g.R; omega), g.R]
  omega

theorem AtCall.sb (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) {N : Nat}
    (hN : N ≤ 17792 + c) : (stackBelow d N).toNat = vsb m0 + 17792 + c - N := by
  rw [stackBelow_callee (h.sp g hc) (by have := g.R; omega), stackBelow_toNat (by have := g.R; omega),
    g.R]
  omega

theorem AtCall.stackOk (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) {N : Nat}
    (hN : N ≤ 17792 + c) : StackOk d N :=
  stackOk_callee g.stackOk h.frame.kept (h.sp g hc) (by rw [verifyExecutionStack_eq]; omega)

/-- **The read-only data** for a callee. -/
theorem AtCall.rodataAt (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) {N : Nat} (hN : N ≤ 17792 + c) :
    RodataAt d N := by
  refine rodataAt_keep g.rod h.same (fun p hp t hi ↦ ?_) ?_ ?_
  · have hn := g.rod.noWrap t
    have hap := g.rod.apart t
    have ht := g.rt t
    have hw := g.rw t
    unfold NativeRustcVm.Apart at hap ht hw
    rw [vsb_eq] at hap
    rw [inR hn] at hi
    rcases g.writable hp with hp | hp | hp <;> omega
  · rw [vsb_eq, h.sb g hc hN]; omega
  · rw [vsb_eq, h.sb g hc hN]; omega

/-- The loader slots remain outside every write of the execution walk. -/
theorem AtCall.got (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) {N : Nat}
    (hN : N ≤ 17792 + c) {areas : List (BitVec 64 × Nat)}
    (hap : ∀ l ∈ ["memcpy", "memset"], ∀ r ∈ areas,
      NativeRustcVm.Apart (gotAddr l) 8 r.1 r.2) :
    GotAt d N areas ["memcpy", "memset"] := by
  apply g.got.transport _ _ hap
  · intro l hl i hi
    apply h.same
    intro hw
    obtain ⟨_, hn, hs, ha⟩ := g.got.1 l hl
    have ht : NativeRustcVm.Apart (gotAddr l) 8 (reg m0 .rdi) tstateBytes :=
      ha (reg m0 .rdi, tstateBytes) (by simp)
    have hwork : NativeRustcVm.Apart (gotAddr l) 8 (reg m0 .r8) workAreaBytes :=
      ha (reg m0 .r8, workAreaBytes) (by simp)
    have hq := NativeRustcVm.toNat_add_ofNat
      (a := gotAddr l) (i := i) (by change (gotAddr l).toNat + 8 ≤ 2 ^ 64 at hn; omega)
    change NativeRustcVm.Apart (gotAddr l) 8 (stackBelow m0 17888) 17896 at hs
    unfold NativeRustcVm.Apart at hs ht hwork
    rw [vsb_eq] at hs
    change _ + 8 ≤ _ ∨ _ + 760 ≤ _ at ht
    change _ + 8 ≤ _ ∨ _ + 495552 ≤ _ at hwork
    rcases g.writable hw with hw | hw | hw <;> omega
  · intro l hl
    apply NativeRustcVm.Apart.mono_right (g.got.1 l hl).2.2.1
    · change vsb m0 ≤ (stackBelow d N).toNat
      rw [h.sb g hc hN]; omega
    · change (stackBelow d N).toNat + (N + 8) ≤ vsb m0 + 17896
      rw [h.sb g hc hN]; omega

theorem Geo.gotT (g : Geo a m0) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    NativeRustcVm.Apart (gotAddr l) 8 (reg m0 .rdi) tstateBytes :=
  (g.got.1 l hl).2.2.2 (reg m0 .rdi, tstateBytes) (by simp)

theorem Geo.gotA (g : Geo a m0) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    NativeRustcVm.Apart (gotAddr l) 8 a.words (8 * a.len) :=
  (g.got.1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)

theorem Geo.gotB (g : Geo a m0) {l : Label} (hl : l ∈ ["memcpy", "memset"])
    (hn : (reg m0 .rdx).toNat ≠ 0) :
    NativeRustcVm.Apart (gotAddr l) 8 (reg m0 .rsi) (8 * (reg m0 .rdx).toNat) :=
  (g.got.1 l hl).2.2.2 (reg m0 .rsi, 8 * (reg m0 .rdx).toNat) (by simp [hn])

theorem Geo.gotP (g : Geo a m0) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    NativeRustcVm.Apart (gotAddr l) 8 (reg m0 .rcx) 32 :=
  (g.got.1 l hl).2.2.2 (reg m0 .rcx, 32) (by simp)

theorem Geo.gotW (g : Geo a m0) {l : Label} (hl : l ∈ ["memcpy", "memset"])
    {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) :
    NativeRustcVm.Apart (gotAddr l) 8 (off (reg m0 .r8) o) n := by
  have hw : NativeRustcVm.Apart (gotAddr l) 8 (reg m0 .r8) workAreaBytes :=
    (g.got.1 l hl).2.2.2 (reg m0 .r8, workAreaBytes) (by simp)
  apply NativeRustcVm.Apart.mono_right hw
  · rw [g.wo ho]; omega
  · rw [g.wo ho]; change _ ≤ _ + 495552; omega

theorem Geo.gotRod (g : Geo a m0) {l : Label} (hl : l ∈ ["memcpy", "memset"])
    (t : NativeRustcVm.Data.Item) :
    NativeRustcVm.Apart (gotAddr l) 8 (rodataAddr t) t.bytes.length := by
  have hr : (rodataAddr t, t.bytes.length) ∈ rodataAreas :=
    List.mem_map.mpr ⟨t, by cases t <;> decide, rfl⟩
  exact (g.got.1 l hl).2.2.2 (rodataAddr t, t.bytes.length)
    (by simp only [List.mem_append, hr, or_true, true_or])

theorem Geo.gotRodata (g : Geo a m0) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    ∀ r ∈ rodataAreas, NativeRustcVm.Apart (gotAddr l) 8 r.1 r.2 :=
  fun r hr ↦ (g.got.1 l hl).2.2.2 r
    (by simp only [List.mem_append, hr, or_true, true_or])

theorem AtCall.rcAt (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) {N : Nat} (hN : N ≤ 17792 + c) : RcAt d N :=
  (h.rodataAt g hc hN).rcAt

omit [Labels] in
theorem rc_len : (NativeRustcVm.Data.Item.bytes .keccakRC).length = 192 := by
  rw [NativeRustcVm.Data.Item.bytes, NativeRustcVm.length_wordsBytes, keccakRC_eq]; rfl

theorem Geo.gotRc (g : Geo a m0) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    NativeRustcVm.Apart (gotAddr l) 8 rcAddr 192 := by
  have h := g.gotRod hl .keccakRC
  rwa [rc_len, ← rcAddr_eq] at h

/-- The `TState` apart from the round constants. -/
theorem Geo.tRc (g : Geo a m0) : NativeRustcVm.Apart (reg m0 .rdi) tstateBytes rcAddr 192 := by
  have h := g.rt .keccakRC
  rw [rc_len, ← rcAddr_eq] at h
  exact h

/-- A working-area range apart from the round constants. -/
theorem Geo.wRc (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) :
    NativeRustcVm.Apart (off (reg m0 .r8) o) n rcAddr 192 := by
  have h := g.rw .keccakRC
  rw [rc_len, ← rcAddr_eq] at h
  unfold NativeRustcVm.Apart at h ⊢
  rw [g.wo ho]
  omega

/-- A working-area range apart from the read-only data. -/
theorem Geo.wRod (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) :
    RodataApart (off (reg m0 .r8) o) n := fun t ↦ by
  have h := g.rw t
  unfold NativeRustcVm.Apart at h ⊢
  rw [g.wo ho]
  omega

/-- **The `TState`** apart from a callee's stack and the round constants. -/
theorem AtCall.tstateOk (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) {N : Nat} (hN : N ≤ 17792 + c) :
    TStateOk d (reg m0 .rdi) a N := by
  have hsb := h.sb g hc hN
  have := g.tS
  have := g.aS
  refine ⟨?_, ?_, g.tRc⟩ <;> show _ ∨ _ <;> rw [hsb] <;> (try unfold tstateBytes) <;> omega

/-- A working-area range as a callee's output beside the `TState`. -/
theorem AtCall.outOk (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) {o n N : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) (hN : N ≤ 17792 + c) : OutOk d (reg m0 .rdi) a (off (reg m0 .r8) o) n N := by
  have hsb := h.sb g hc hN
  have hw := g.wo ho
  have := g.wS
  have := g.tw
  have := g.aw
  have := g.wN
  refine ⟨Mapped.keeps (mapped_off g.mW hn) h.frame.kept, ?_, ?_, ?_, ?_, g.wRc ho hn⟩
  · show _ ≤ _; omega
  all_goals show _ ∨ _; (try rw [hsb]); (try unfold tstateBytes); omega

theorem AtCall.readable (h : AtCall m0 d c) (g : Geo a m0) {o n : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) : Readable d (off (reg m0 .r8) o) n :=
  ⟨Mapped.keeps (mapped_off g.mW hn) h.frame.kept, by
    show _ ≤ _; rw [g.wo ho]; have := g.wN; omega⟩

theorem AtCall.offStack (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) {o n N : Nat} (ho : o < 495552)
    (hn : o + n ≤ 495552) (hN : N ≤ 17792 + c) : OffStack d (off (reg m0 .r8) o) n N := by
  show _ ∨ _
  rw [h.sb g hc hN, g.wo ho]
  have := g.wS
  omega

/-- Two working-area ranges that do not overlap are apart. -/
theorem Geo.apartW (g : Geo a m0) {o n o' n' : Nat} (ho : o < 495552) (ho' : o' < 495552)
    (hle : o + n ≤ o' ∨ o' + n' ≤ o) :
    NativeRustcVm.Apart (off (reg m0 .r8) o) n (off (reg m0 .r8) o') n' := by
  unfold NativeRustcVm.Apart; rw [g.wo ho, g.wo ho']; omega

/-- A working-area range apart from the `TState`. -/
theorem Geo.apartWT (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) :
    NativeRustcVm.Apart (off (reg m0 .r8) o) n (reg m0 .rdi) tstateBytes := by
  have := g.tw
  unfold NativeRustcVm.Apart tstateBytes; rw [g.wo ho]; omega

/-- A working-area range apart from the decoded area. -/
theorem Geo.apartWA (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) :
    NativeRustcVm.Apart (off (reg m0 .r8) o) n a.words (8 * a.len) := by
  have := g.aw
  unfold NativeRustcVm.Apart; rw [g.wo ho]; omega

/-- A working-area range: its addresses as numbers. -/
theorem Geo.inW (g : Geo a m0) {o n : Nat} (ho : o < 495552) (hn : o + n ≤ 495552) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (reg m0 .r8) o) n q) :
    (reg m0 .r8).toNat + o ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + o + n := by
  rw [inR (by unfold NativeRustcVm.NoWrap; rw [g.wo ho]; have := g.wN; omega), g.wo ho] at hq
  exact hq

/-- The `TState`: its addresses as numbers. -/
theorem Geo.inT (g : Geo a m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q) :
    (reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760 :=
  (inR g.tN).mp hq

/-- A callee's stack: its addresses as numbers. -/
theorem AtCall.inS (h : AtCall m0 d c) (g : Geo a m0) (hc : c ≤ 96) {N : Nat} (hN : N ≤ 17792 + c) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d N) N q) :
    vsb m0 + 17792 + c - N ≤ q.toNat ∧ q.toNat < vsb m0 + 17792 + c := by
  rw [inR (by unfold NativeRustcVm.NoWrap; rw [h.sb g hc hN]; have := g.e8; omega), h.sb g hc hN] at hq
  omega

/-- **After a call** changing only the `TState`, the working area and the callee's stack: between
the calls again. -/
theorem AtCall.ret (h : AtCall m0 d) (g : Geo a m0) {d' : MachineData} (hrbx : reg d .rbx = reg m0 .r8)
    (hr14 : reg d .r14 = reg m0 .rdi) (hs : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64)
    {R : BitVec 64 → Prop} (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → (vsb m0 ≤ q.toNat ∧ q.toNat < vsb m0 + 17824) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .r8).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 495552)) :
    At m0 d' := by
  have hf := Frame.call_low_at (L := 32) h.frame hs hrsp hso (fun q hq ↦ by
    rw [g.F]
    have := g.tS
    have := g.wS
    rcases hR q hq with hq | hq | hq <;> omega) (fun p hp ↦ by have := slots_ge p hp; omega)
    (by decide) g.fnw slots_le
  refine ⟨hf, fun q hq ↦ ?_, (hs.1 .rbx rfl).trans hrbx, (hs.1 .r14 rfl).trans hr14⟩
  rw [hso q fun hr ↦ hq (by
    rcases hR q hr with hr | hr | hr
    · exact wr_s g ⟨hr.1, by omega⟩
    · exact wr_t ((inR g.tN).mpr hr)
    · exact wr_w g hr)]
  exact h.same q hq

end

end NativeRustcVmX64.Top.VerifyExecution
