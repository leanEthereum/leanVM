module

public import NativeRustcVmX64.Wire.PhaseM.Exec
public import NativeRustcVmX64.Wire.PhaseM.Num
public import NativeRustcVmX64.Wire.PhaseM.Model
public import NativeRustcVmX64.Wire.Decode.Steps
public import NativeRustcX64.Got

/-!
# `phase_m`'s places and states (x86-64)

The reader at `r` (RDI), the phase's words at `out` (RSI, `phaseBytes`), the working area at `w`
(RDX, `workBytes`); the frame (`Frame`, 160 bytes below the entry's RSP: the pushed registers
from `112`, `out` kept at `48`, the locals) in the 1216 bytes of stack the function uses. Numbers
are written with the entry's registers themselves (`SP0`, `RD`, …, notations, one `omega` atom
each). `Geo`: the places as numbers, from the precondition (`geo_of`). `Bod`: what every state of
the body keeps (the frame, memory changed only where the function may, R12 the reader, R14 the
working area, `out` at the frame's `48`). `FW`: a word of the frame. A block from `frS` (`fblk`),
one writing the frame's locals (`wblk`), a call kept (`Bod.call`), `Reader::le` for four bytes
(`le4`); the epilogue (`fin`, `b18`) and the way out with `None` (`none_run`, `b17`).
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap Frame.of_block
  Frame.epilogue Frame.load_ret Frame.call_slots after after_eq sameOutside_low MidOk)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off PhaseAt Mapped.keeps)
open NativeRustcVmX64.Sumcheck (keepW)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- The entry's RSP, as a number. -/
scoped notation:max "SP0 " m:max => BitVec.toNat (NativeRustcX64.rspOf m)
/-- The reader's address. -/
scoped notation:max "RD " m:max => NativeRustcX64.reg m Reg64.rdi
/-- The phase's address. -/
scoped notation:max "OUT " m:max => NativeRustcX64.reg m Reg64.rsi
/-- The working area's address. -/
scoped notation:max "WK " m:max => NativeRustcX64.reg m Reg64.rdx

@[expose] public section

/-- Byte `o` of the working area. -/
abbrev wa (m0 : MachineData) (o : Nat) : BitVec 64 := off (WK m0) o

/-- Word `o` of the frame. -/
abbrev FW (m0 : MachineData) (d : Mem 64) (o : Nat) (v : UInt64) : Prop :=
  NativeRustcVm.WordAt d (off (stackBelow m0 160) o) v

/-- What the body may change: the stack, the reader's cursor, the phase, the working area. -/
def Chg (m0 : MachineData) (q : BitVec 64) : Prop :=
  (SP0 m0 - 1216 ≤ q.toNat ∧ q.toNat < SP0 m0) ∨
    ((RD m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (RD m0).toNat + 24) ∨
    ((OUT m0).toNat ≤ q.toNat ∧ q.toNat < (OUT m0).toNat + 395288) ∨
    ((WK m0).toNat ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 483584)

/-- **The places**, as numbers: the stack (with the return address), the round constants, the
reader, its `L` bytes at `bp`, the phase, the working area. -/
structure Geo [Labels] (m0 : MachineData) (bp : BitVec 64) (L : Nat) : Prop where
  st : StackOk m0 1216
  rc : RcAt m0 1216
  rNw : (RD m0).toNat + 24 ≤ 2 ^ 64
  bNw : bp.toNat + L ≤ 2 ^ 64
  oOk : NativeRustcVm.Region.Ok m0.dmem ⟨OUT m0, 395288⟩
  wOk : NativeRustcVm.Region.Ok m0.dmem ⟨WK m0, 483584⟩
  sC : (SP0 m0 - 1216) + 1224 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (SP0 m0 - 1216)
  sR : (SP0 m0 - 1216) + 1224 ≤ (RD m0).toNat ∨ (RD m0).toNat + 24 ≤ (SP0 m0 - 1216)
  sB : (SP0 m0 - 1216) + 1224 ≤ bp.toNat ∨ bp.toNat + L ≤ (SP0 m0 - 1216)
  sO : (SP0 m0 - 1216) + 1224 ≤ (OUT m0).toNat ∨ (OUT m0).toNat + 395288 ≤ (SP0 m0 - 1216)
  sW : (SP0 m0 - 1216) + 1224 ≤ (WK m0).toNat ∨ (WK m0).toNat + 483584 ≤ (SP0 m0 - 1216)
  cR : rcAddr.toNat + 192 ≤ (RD m0).toNat ∨ (RD m0).toNat + 24 ≤ rcAddr.toNat
  cB : rcAddr.toNat + 192 ≤ bp.toNat ∨ bp.toNat + L ≤ rcAddr.toNat
  cO : rcAddr.toNat + 192 ≤ (OUT m0).toNat ∨ (OUT m0).toNat + 395288 ≤ rcAddr.toNat
  cW : rcAddr.toNat + 192 ≤ (WK m0).toNat ∨ (WK m0).toNat + 483584 ≤ rcAddr.toNat
  rB : (RD m0).toNat + 24 ≤ bp.toNat ∨ bp.toNat + L ≤ (RD m0).toNat
  rO : (RD m0).toNat + 24 ≤ (OUT m0).toNat ∨ (OUT m0).toNat + 395288 ≤ (RD m0).toNat
  rW : (RD m0).toNat + 24 ≤ (WK m0).toNat ∨ (WK m0).toNat + 483584 ≤ (RD m0).toNat
  bO : bp.toNat + L ≤ (OUT m0).toNat ∨ (OUT m0).toNat + 395288 ≤ bp.toNat
  bW : bp.toNat + L ≤ (WK m0).toNat ∨ (WK m0).toNat + 483584 ≤ bp.toNat
  oW : (OUT m0).toNat + 395288 ≤ (WK m0).toNat ∨ (WK m0).toNat + 483584 ≤ (OUT m0).toNat
  got : GotAt m0 1216
    [(rcAddr, 192), (RD m0, 24), (OUT m0, 395288), (WK m0, 483584)] ["memcpy", "memset"]

/-- **What the body keeps**, RSP at the frame's offset `o`. -/
structure Bod [Labels] (m0 : MachineData) (o : Nat) (m : MachineData) : Prop where
  fr : Frame m0 160 slots o m
  chg : NativeRustcVm.SameOutside m0.dmem m.dmem (Chg m0)
  r12 : reg m .r12 = RD m0
  r14 : reg m .r14 = WK m0
  out : FW m0 m.dmem 48 (UInt64.ofBitVec (OUT m0))

/-- **The result** for the reader's bytes `B` from `c`. -/
def Res (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat) (m : MachineData) : Prop :=
  match phaseM B c with
  | some (po, c') => boolRet m = 1 ∧ PhaseAt m.dmem (OUT m0) (phaseW po) ∧
      ReaderAt m.dmem (RD m0) bp B c'
  | none => boolRet m = 0

/-- What `phase_m` reaches. -/
abbrev Post [Labels] (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ PhaseMPost m0 st.data

end

public section

theorem phaseMStack_eq : phaseMStack = 1216 := rfl
theorem workBytes_eq : workBytes = 483584 := rfl
theorem phaseBytes_eq : phaseBytes = 395288 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 160 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_lo : ∀ p ∈ slots, 112 ≤ p.1 ∧ p.1 + 8 ≤ 160 := by decide

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c L : Nat}

section
variable [Labels]

theorem geo_of (h : PhaseMPre m0) (hR : ReaderAt m0.dmem (RD m0) bp B c) : Geo m0 bp B.length := by
  obtain ⟨hst, hrc, hoOk, hwOk, bp', B', c', hR', hd, hgot⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := hR'.unique hR
  have hst' : StackOk m0 1216 := hst
  have hS := stackBelow_toNat (m := m0) (n := 1216) hst'.1
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, stackR, rcR,
    phaseMStack_eq, workBytes_eq, phaseBytes_eq, NativeRustcVm.Apart] at hd
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := hd
  rw [hS] at h1 h2 h3 h4 h5
  exact ⟨hst', hrc, hR.ok.2, hR.noWrap, hoOk, hwOk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15.1, hgot⟩

theorem Geo.sp (G : Geo m0 bp L) : 1216 ≤ SP0 m0 := G.st.1
theorem Geo.top (G : Geo m0 bp L) : SP0 m0 + 8 ≤ 2 ^ 64 := G.st.2.1
theorem Geo.oNw (G : Geo m0 bp L) : (OUT m0).toNat + 395288 ≤ 2 ^ 64 := G.oOk.2
theorem Geo.wNw (G : Geo m0 bp L) : (WK m0).toNat + 483584 ≤ 2 ^ 64 := G.wOk.2
theorem Geo.cNw (G : Geo m0 bp L) : rcAddr.toNat + 192 ≤ 2 ^ 64 := G.rc.2.1

/-- Byte `j` of the frame. -/
theorem Geo.fr (G : Geo m0 bp L) {j : Nat} (hj : j < 168) :
    (off (stackBelow m0 160) j).toNat = SP0 m0 - 160 + j :=
  frame_toNat (by have := G.sp; omega) G.top hj

/-- Byte `o` of the working area. -/
theorem Geo.wa (G : Geo m0 bp L) {o : Nat} (ho : o < 483584) :
    (wa m0 o).toNat = (WK m0).toNat + o := by
  have := G.wNw
  exact toNat_off (by omega)

/-- A frame word kept by a change missing it. -/
theorem FW.keep (G : Geo m0 bp L) {d d' : Mem 64} {o : Nat} {v : UInt64} (ho : o + 8 ≤ 168)
    (h : FW m0 d o v) {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → q.toNat < SP0 m0 - 160 + o ∨ SP0 m0 - 160 + o + 8 ≤ q.toNat) :
    FW m0 d' o v := by
  have := G.top
  have := G.sp
  refine wordAt_keep h hs (by rw [G.fr (by omega)]; omega) fun q hq ↦ ?_
  rw [G.fr (by omega)]; exact hR q hq

/-- The round constants, kept by the body. -/
theorem Geo.rc_keep (G : Geo m0 bp L) {d : Mem 64}
    (h : NativeRustcVm.SameOutside m0.dmem d (Chg m0)) :
    ∀ j < 192, d.get? (rcAddr + BitVec.ofNat 64 j) = m0.dmem.get? (rcAddr + BitVec.ofNat 64 j) :=
  fun j hj ↦ h _ fun hq ↦ by
    have hcn := G.cNw
    have h1 := G.sC; have h2 := G.cR; have h3 := G.cO; have h4 := G.cW
    unfold Chg at hq
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hq
    omega

/-- The loader slots survive the body's stack, reader, phase and work writes. -/
theorem Geo.got_keep (G : Geo m0 bp L) {d : Mem 64}
    (h : NativeRustcVm.SameOutside m0.dmem d (Chg m0)) :
    ∀ l ∈ ["memcpy", "memset"], ∀ i < 8,
      d.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  intro l hl i hi
  obtain ⟨_, hn, hs, ha⟩ := G.got.1 l hl
  have hr := ha (RD m0, 24) (by simp)
  have ho := ha (OUT m0, 395288) (by simp)
  have hw := ha (WK m0, 483584) (by simp)
  change Apart (gotAddr l) 8 (stackBelow m0 1216) 1224 at hs
  unfold NativeRustcX64.Apart at hs hr ho hw
  dsimp only at hr ho hw
  change (gotAddr l).toNat + 8 ≤ 2 ^ 64 at hn
  rw [stackBelow_toNat G.sp] at hs
  refine h _ fun hq => ?_
  unfold Chg at hq
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hq
  omega

/-- **A call** keeps the body's state where the callee changes only what the body may and none of
the slots, the return address and `out`'s word. -/
theorem Bod.call (G : Geo m0 bp L) {d d' : MachineData} (hb : Bod m0 0 d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → Chg m0 q ∧ (q.toNat < SP0 m0 - 112 ∨
      (SP0 m0 - 104 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) ∨ SP0 m0 + 8 ≤ q.toNat)) :
    Bod m0 8 d' := by
  have hsp := G.sp
  have h8 := G.top
  have hnot : ∀ j, 112 ≤ j → j < 168 → ¬ R (off (stackBelow m0 160) j) := fun j hj hj' hq ↦ by
    have := (hR _ hq).2
    rw [G.fr hj'] at this
    omega
  refine ⟨Frame.call_slots hb.fr hs hrsp hso
      (fun p hp i hi ↦ hnot _ (by have := slots_lo p hp; omega) (by have := slots_lo p hp; omega))
      (fun j hj ↦ hnot _ (by omega) (by omega)),
    (hb.chg.trans hso).mono fun q hq ↦ hq.elim id fun h ↦ (hR q h).1,
    (hs.1 .r12 rfl).trans hb.r12, (hs.1 .r14 rfl).trans hb.r14,
    hb.out.keep G (by omega) hso fun q hq ↦ by have := (hR q hq).2; omega⟩

end

/-! ## Steps -/

variable [Host] {k : Nat}

/-- **A block from `frS`** keeping memory, R12 and R14. -/
theorem fblk (hp : Placed code k) (G : Geo m0 bp L) {bj : List Directive} {j : Nat}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {x : Exit}
    (hrun : exec bj frS = some (after bj frS, x)) (hx : ∀ l, x = .call l → False)
    (hok : FrOk (after bj frS) = true) (h12 : (after bj frS).reg .r12 = some (.reg .r12))
    (h14 : (after bj frS).reg .r14 = some (.reg .r14))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hbod : Bod m0 8 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Bod m0 8 st'.data → st'.data.dmem = st.data.dmem →
      Match (frameEnv m0 st.data 160 []) (after bj frS) st'.data →
      PcOk (frameEnv m0 st.data 160 []) x (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  simp only [FrOk, Bool.and_eq_true, List.isEmpty_iff] at hok
  have hst : StackOk m0 1216 := G.st
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 160) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hbod.fr.kept,
      frame_noWrap hst (by decide)⟩ (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 160 []) frS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of hb hne hp) hrun hwf (fun l h ↦ (hx l h).elim) hpc hm
    fun st' hm' hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hok.2
  refine cont st' ⟨Frame.of_block hbod.fr hwf hm' hok.1 slots_le, ?_,
    (hm'.regs .r12 _ h12).trans hbod.r12, (hm'.regs .r14 _ h14).trans hbod.r14,
    by rw [hd]; exact hbod.out⟩ hd hm' hpc'
  rw [hd]; exact hbod.chg

/-- **A block from `frS` writing the frame's locals** (below `112`, not `out`'s word), RSP at its
offset `o` at the end. -/
theorem wblk (hp : Placed code k) (G : Geo m0 bp L) {bj : List Directive} {j : Nat} {o : Nat}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {x : Exit}
    (hrun : exec bj frS = some (after bj frS, x))
    (hok : MidOk 160 o slots (after bj frS) = true)
    (hw : ∀ w ∈ (after bj frS).mem, w.r = 0 ∧ w.off + w.n ≤ 112 ∧ (w.off + w.n ≤ 48 ∨ 56 ≤ w.off))
    (h12 : (after bj frS).reg .r12 = some (.reg .r12))
    (h14 : (after bj frS).reg .r14 = some (.reg .r14))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hbod : Bod m0 8 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Bod m0 o st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (fun q ↦ SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) →
      (∀ o' v, o' + 8 ≤ 168 → (∀ w ∈ (after bj frS).mem, w.r = 0 → w.off + w.n ≤ o' ∨
        o' + 8 ≤ w.off) → FW m0 st.data.dmem o' v → FW m0 st'.data.dmem o' v) →
      Match (frameEnv m0 st.data 160 [] (fun _ ↦ 0) (Host.addrOf (k + j + bj.length)).toBitVec)
        (after bj frS) st'.data →
      PcOk (frameEnv m0 st.data 160 [] (fun _ ↦ 0) (Host.addrOf (k + j + bj.length)).toBitVec) x
        (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hst : StackOk m0 1216 := G.st
  have hsp := G.sp
  have htop := G.top
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 160) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + j + bj.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hbod.fr.kept, frame_noWrap hst (by decide)⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 160 [] (fun _ ↦ 0) (Host.addrOf (k + j + bj.length)).toBitVec)
      frS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of hb hne hp) hrun hwf (fun _ _ ↦ rfl) hpc hm fun st' hm' hpc' ↦ ?_
  have hs := sameOutside_low hwf hm' (r := 0) rfl (hi := 112) (by omega) fun w hw' ↦
    ⟨(hw w hw').1, (hw w hw').2.1⟩
  have hS := stackBelow_toNat (m := m0) (n := 160) (by omega)
  have hs' : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (fun q ↦ SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) := hs.mono fun q h ↦ by
    have := iv_of_inRange (by rw [hS]; omega) h
    rw [hS] at this
    omega
  have hout : FW m0 st'.data.dmem 48 (UInt64.ofBitVec (OUT m0)) :=
    NativeRustcVmX64.Sumcheck.keepW hwf hm' (NativeRustcVmX64.Sumcheck.writesIn_of_mid hok)
      (by omega) (fun w hw' _ ↦ (hw w hw').2.2) hbod.out
  refine cont st' ⟨Frame.of_block hbod.fr hwf hm' hok slots_le,
    (hbod.chg.trans hs').mono fun q hq ↦ hq.elim id fun h ↦ .inl (by omega),
    (hm'.regs .r12 _ h12).trans hbod.r12, (hm'.regs .r14 _ h14).trans hbod.r14, hout⟩ hs'
    (fun o' v ho hmiss h ↦ NativeRustcVmX64.Sumcheck.keepW hwf hm'
      (NativeRustcVmX64.Sumcheck.writesIn_of_mid hok) ho hmiss h) hm' hpc'

/-- The environment of a block reaching `n` bytes of the working area from its byte `o`. -/
abbrev aEnv (m0 d : MachineData) (o n : Nat) (ret : BitVec 64 := 0) : Sym.Env :=
  frameEnv m0 d 160 [(wa m0 o, n)] (fun _ ↦ 0) ret

theorem aEnv_wf (G : Geo m0 bp L) {d : MachineData} (hk : Kept m0.dmem d.dmem) {o n : Nat}
    (hon : o + n ≤ 483584) (hn : 0 < n) (ret : BitVec 64) : (aEnv m0 d o n ret).WF := by
  have hst : StackOk m0 1216 := G.st
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsW := G.sW
  have hS := stackBelow_toNat (m := m0) (n := 160) (by omega)
  have hwa : (wa m0 o).toNat = (WK m0).toNat + o := toNat_off (by omega)
  have hwm : NativeRustcVm.Mapped m0.dmem (WK m0) 483584 := G.wOk.1
  refine frame_wf ⟨Mapped.keeps (frame_mapped hst (by decide)) hk, frame_noWrap hst (by decide)⟩
    (fun x hx ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hx; subst hx
    exact ⟨NativeRustcVmX64.Transcript.mapped_off (Mapped.keeps hwm hk) hon,
      show (wa m0 o).toNat + n ≤ 2 ^ 64 by omega⟩
  · show NativeRustcVm.Apart (stackBelow m0 160) (160 + 8) (wa m0 o) n
    unfold NativeRustcVm.Apart; rw [hS, hwa]; omega

/-- **A block reaching the working area** (region 1, `n` bytes from its byte `o`): it writes the
frame's locals (not `out`) and that part. -/
theorem ablk (hp : Placed code k) (G : Geo m0 bp L) {bj : List Directive} {j o n o' : Nat}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {S0 : SState} {x : Exit}
    (hrun : exec bj S0 = some (after bj S0, x)) (hon : o + n ≤ 483584) (hn : 0 < n)
    (hok : MidOk 160 o' slots (after bj S0) = true)
    (hw : ∀ w ∈ (after bj S0).mem, (w.r = 0 ∧ w.off + w.n ≤ 112 ∧ (w.off + w.n ≤ 48 ∨ 56 ≤ w.off)) ∨
      (w.r = 1 ∧ w.off + w.n ≤ n))
    (h12 : (after bj S0).reg .r12 = some (.reg .r12))
    (h14 : (after bj S0).reg .r14 = some (.reg .r14))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hbod : Bod m0 8 st.data)
    (hm : Match (aEnv m0 st.data o n (Host.addrOf (k + j + bj.length)).toBitVec) S0 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Bod m0 o' st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (fun q ↦ (SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) ∨
          ((WK m0).toNat + o ≤ q.toNat ∧ q.toNat < (WK m0).toNat + o + n)) →
      (∀ o' v, o' + 8 ≤ 168 → (∀ w ∈ (after bj S0).mem, w.r = 0 → w.off + w.n ≤ o' ∨
        o' + 8 ≤ w.off) → FW m0 st.data.dmem o' v → FW m0 st'.data.dmem o' v) →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (fun q ↦ ∃ w ∈ (after bj S0).mem,
        (w.r = 0 ∧ SP0 m0 - 160 + w.off ≤ q.toNat ∧ q.toNat < SP0 m0 - 160 + w.off + w.n) ∨
        (w.r = 1 ∧ (WK m0).toNat + o + w.off ≤ q.toNat ∧
          q.toNat < (WK m0).toNat + o + w.off + w.n)) →
      Match (aEnv m0 st.data o n (Host.addrOf (k + j + bj.length)).toBitVec) (after bj S0)
        st'.data →
      PcOk (aEnv m0 st.data o n (Host.addrOf (k + j + bj.length)).toBitVec) x
        (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hwf := aEnv_wf G hbod.fr.kept hon hn (Host.addrOf (k + j + bj.length)).toBitVec
  refine exec_at (infix_of hb hne hp) hrun hwf (fun _ _ ↦ rfl) hpc hm fun st' hm' hpc' ↦ ?_
  have hS := stackBelow_toNat (m := m0) (n := 160) (by omega)
  have hwa : (wa m0 o).toNat = (WK m0).toNat + o := toNat_off (by omega)
  have hs : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (fun q ↦ (SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) ∨
        ((WK m0).toNat + o ≤ q.toNat ∧ q.toNat < (WK m0).toNat + o + n)) := fun q hq ↦
    hm'.get?_mem0 hwf fun ⟨w, hw', b, sz, hb', h1, h2⟩ ↦ hq (by
      rcases hw w hw' with ⟨hr, hle, -⟩ | ⟨hr, hle⟩
      · rw [hr] at hb'
        simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hb'
        obtain ⟨rfl, rfl⟩ := hb'
        rw [hS] at h1 h2
        exact .inl (by omega)
      · rw [hr] at hb'
        simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq, Prod.mk.injEq] at hb'
        obtain ⟨rfl, rfl⟩ := hb'
        rw [hwa] at h1 h2
        exact .inr (by omega))
  have hkeep : ∀ o' v, o' + 8 ≤ 168 → (∀ w ∈ (after bj S0).mem, w.r = 0 → w.off + w.n ≤ o' ∨
      o' + 8 ≤ w.off) → FW m0 st.data.dmem o' v → FW m0 st'.data.dmem o' v :=
    fun o' v ho hmiss h ↦ NativeRustcVmX64.Sumcheck.keepW hwf hm'
      (NativeRustcVmX64.Sumcheck.writesIn_of_mid hok) ho hmiss h
  refine cont st' ⟨Frame.of_block hbod.fr hwf hm' hok slots_le,
    (hbod.chg.trans hs).mono fun q hq ↦ ?_,
    (hm'.regs .r12 _ h12).trans hbod.r12, (hm'.regs .r14 _ h14).trans hbod.r14,
    hkeep 48 _ (by omega) (fun w hw' hr ↦ by
      rcases hw w hw' with ⟨-, -, h⟩ | ⟨h, -⟩
      · omega
      · omega) hbod.out⟩ hs hkeep (fun q hq ↦
    hm'.get?_mem0 hwf fun ⟨w, hw', b, sz, hb', h1, h2⟩ ↦ hq ⟨w, hw', by
      rcases hw w hw' with ⟨hr, -, -⟩ | ⟨hr, -⟩
      · rw [hr] at hb'
        simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hb'
        obtain ⟨rfl, rfl⟩ := hb'
        rw [hS] at h1 h2
        exact .inl ⟨hr, by omega, by omega⟩
      · rw [hr] at hb'
        simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq, Prod.mk.injEq] at hb'
        obtain ⟨rfl, rfl⟩ := hb'
        rw [hwa] at h1 h2
        exact .inr ⟨hr, by omega, by omega⟩⟩) hm' hpc'
  rcases hq with hq | hq | hq
  · exact hq
  · exact .inl (by omega)
  · exact .inr (.inr (.inr (by omega)))

/-- **The epilogue** (`b18`, at `NativeRustcVmX64.Vm.PhaseM.label_24`): the result as it is. -/
theorem fin (hp : Placed code k) (G : Geo m0 bp L) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b18Offset)) (hfr : Frame m0 160 slots 112 st.data)
    (hchg : NativeRustcVm.SameOutside m0.dmem st.data.dmem (Chg m0))
    (hres : ∀ bp' B' c', ReaderAt m0.dmem (RD m0) bp' B' c' → Res m0 bp' B' c' st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hepi, hmem, hrax⟩ := ok_b18
  have hst : StackOk m0 1216 := G.st
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 160) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hfr.kept,
      frame_noWrap hst (by decide)⟩ (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 160 []) epiS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hfr.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b18_in_code (by simp [b18]) hp) exit_b18 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hfr hwf hm' hepi
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  have ha : reg st'.data .rax = reg st.data .rax := hm'.regs .rax _ hrax
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; exact hfr.load_ret hst (by decide), hrsp, fun bp' B' c' hR ↦ ?_,
    fun q hq ↦ ?_, hsv⟩
  · have := hres bp' B' c' hR
    unfold Res at this
    unfold boolRet
    rw [ha, hd]
    exact this
  · rw [hd]
    refine hchg q fun h ↦ hq ?_
    have hS := stackBelow_toNat (m := m0) (n := 1216) G.sp
    have := G.oNw; have := G.wNw; have := G.top; have := G.rNw
    rcases h with h | h | h | h
    · refine ⟨frameR m0 phaseMStack, by simp, ?_⟩
      show NativeRustcVm.InRange (stackBelow m0 1216) 1216 q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hS]; omega), hS]
      omega
    · refine ⟨curRegion (RD m0), by simp, ?_⟩
      show NativeRustcVm.InRange (off (RD m0) 16) 8 q
      have h16 : (off (RD m0) 16).toNat = (RD m0).toNat + 16 := toNat_off (by omega)
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [h16]; omega), h16]
      omega
    · refine ⟨⟨OUT m0, phaseBytes⟩, by simp, ?_⟩
      show NativeRustcVm.InRange (OUT m0) phaseBytes q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [phaseBytes_eq]; omega),
        phaseBytes_eq]
      omega
    · refine ⟨⟨WK m0, workBytes⟩, by simp, ?_⟩
      show NativeRustcVm.InRange (WK m0) workBytes q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [workBytes_eq]; omega),
        workBytes_eq]
      omega

/-- **The way out with `None`** (`b17`, at `NativeRustcVmX64.Vm.PhaseM.label_23`), the reader as at the entry. -/
theorem none_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hR : ReaderAt m0.dmem (RD m0) bp B c) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b17Offset)) (hbod : Bod m0 8 st.data) (hn : phaseM B c = none) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hmid, hmem, hrax⟩ := ok_b17
  have hst : StackOk m0 1216 := G.st
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 160) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hbod.fr.kept,
      frame_noWrap hst (by decide)⟩ (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 160 []) frS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) exit_b17 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  refine fin hp G (hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b17_next)) (Frame.of_block hbod.fr hwf hm'
    hmid slots_le) (by rw [hd]; exact hbod.chg) fun bp' B' c' hR' ↦ ?_
  obtain ⟨rfl, rfl, rfl⟩ := hR.unique hR'
  unfold Res
  rw [hn]
  unfold boolRet
  rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
  rfl

end

end NativeRustcVmX64.Wire.PhaseM
