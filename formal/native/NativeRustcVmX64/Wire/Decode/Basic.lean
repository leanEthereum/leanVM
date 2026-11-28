module

public import NativeRustcVmX64.Wire.Decode.Exec
public import NativeRustcVmX64.Wire.PhaseM.Num
public import NativeVm.Entry.Data
public import NativeRustcX64.Got

/-!
# `decode`'s places, states and model (x86-64)

The wire's `L` bytes at `bp` (RDI, RSI), the decoded area of `len` words at `dec` (RDX, RCX), the
working area at `w` (R8); the frame (`Frame`, 80 bytes, the reader at its byte `8`) in the 1296
bytes of stack the function uses. Numbers are written with the entry's registers themselves
(`SP0`, `LN`, …, notations, so that `omega` sees one atom each). `Geo`: the places as numbers,
from the precondition (`geo_of`). `Bod`: what every state of the body keeps (the frame, memory
changed only in the stack, the decoded area and the working area, RBX the working area, R15 the
length). `Dec`: what the decoded area holds after the stream, the phase count and `done`'s phases.
`Res`: the result. A block from `frS` (`fblk`); the epilogue (`fin`).
-/

namespace NativeRustcVmX64.Wire.Decode

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.Decode
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap Frame.of_block
  Frame.epilogue Frame.load_ret after after_eq)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off DecArea DecodedAt PhaseAt
  Mapped.keeps)
open NativeRustcVmX64.Wire.PhaseM (bytesAt_keep wordAt_keep iv_of_inRange)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- The entry's RSP, as a number. -/
scoped notation:max "SP0 " m:max => BitVec.toNat (NativeRustcX64.rspOf m)
/-- The wire's length. -/
scoped notation:max "LN " m:max => BitVec.toNat (NativeRustcX64.reg m Reg64.rsi)
/-- The decoded area's word count. -/
scoped notation:max "LEN " m:max => BitVec.toNat (NativeRustcX64.reg m Reg64.rcx)
/-- The wire's bytes' address. -/
scoped notation:max "BP " m:max => NativeRustcX64.reg m Reg64.rdi
/-- The decoded area's address. -/
scoped notation:max "DEC " m:max => NativeRustcX64.reg m Reg64.rdx
/-- The working area's address. -/
scoped notation:max "WK " m:max => NativeRustcX64.reg m Reg64.r8

@[expose] public section

/-- The reader, at the frame's byte `8`. -/
abbrev rdA (m0 : MachineData) : BitVec 64 := off (stackBelow m0 80) 8
/-- The wire's bytes. -/
abbrev Bs (m0 : MachineData) : List UInt8 := bytesOf m0.dmem (BP m0) (LN m0)
/-- Word `i` of the decoded area. -/
abbrev wd (m0 : MachineData) (i : Nat) : BitVec 64 := off (DEC m0) (8 * i)

/-- What the body may change: the stack, the decoded area, the working area. -/
def Chg (m0 : MachineData) (q : BitVec 64) : Prop :=
  (SP0 m0 - 1296 ≤ q.toNat ∧ q.toNat < SP0 m0) ∨
    ((DEC m0).toNat ≤ q.toNat ∧ q.toNat < (DEC m0).toNat + 8 * LEN m0) ∨
    ((WK m0).toNat ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 483584)

/-- **The places**, as numbers. -/
structure Geo [Labels] (m0 : MachineData) : Prop where
  st : StackOk m0 1296
  rc : RcAt m0 1296
  Llt : LN m0 < 2 ^ 32
  len : decodedWords (LN m0) ≤ LEN m0
  bOk : NativeRustcVm.Region.Ok m0.dmem ⟨BP m0, LN m0⟩
  dOk : NativeRustcVm.Region.Ok m0.dmem ⟨DEC m0, 8 * LEN m0⟩
  wOk : NativeRustcVm.Region.Ok m0.dmem ⟨WK m0, 483584⟩
  sD : (DEC m0).toNat + 8 * LEN m0 ≤ SP0 m0 - 1296 ∨ SP0 m0 + 8 ≤ (DEC m0).toNat
  sW : (WK m0).toNat + 483584 ≤ SP0 m0 - 1296 ∨ SP0 m0 + 8 ≤ (WK m0).toNat
  cD : rcAddr.toNat + 192 ≤ (DEC m0).toNat ∨ (DEC m0).toNat + 8 * LEN m0 ≤ rcAddr.toNat
  cW : rcAddr.toNat + 192 ≤ (WK m0).toNat ∨ (WK m0).toNat + 483584 ≤ rcAddr.toNat
  dW : (DEC m0).toNat + 8 * LEN m0 ≤ (WK m0).toNat ∨ (WK m0).toNat + 483584 ≤ (DEC m0).toNat
  sB : 0 < LN m0 → (BP m0).toNat + LN m0 ≤ SP0 m0 - 1296 ∨ SP0 m0 + 8 ≤ (BP m0).toNat
  bD : 0 < LN m0 → (BP m0).toNat + LN m0 ≤ (DEC m0).toNat ∨
    (DEC m0).toNat + 8 * LEN m0 ≤ (BP m0).toNat
  bW : 0 < LN m0 → (BP m0).toNat + LN m0 ≤ (WK m0).toNat ∨
    (WK m0).toNat + 483584 ≤ (BP m0).toNat
  cB : 0 < LN m0 → rcAddr.toNat + 192 ≤ (BP m0).toNat ∨ (BP m0).toNat + LN m0 ≤ rcAddr.toNat
  got : GotAt m0 1296
    [(rcAddr, 192), (DEC m0, 8 * LEN m0), (WK m0, 483584)] ["memcpy", "memset"]

/-- **What the body keeps**, RSP at the frame's offset `o`. -/
structure Bod [Labels] (m0 : MachineData) (o : Nat) (m : MachineData) : Prop where
  fr : Frame m0 80 slots o m
  chg : NativeRustcVm.SameOutside m0.dmem m.dmem (Chg m0)
  rbx : reg m .rbx = WK m0
  r15 : reg m .r15 = reg m0 .rsi

/-- **The decoded area** after the stream's count `n` and words `ws`, the phase count `p` and the
phases `done`. -/
structure Dec (m0 : MachineData) (d : Mem 64) (n : Nat) (ws : List K) (p : Nat)
    (done : List PhaseOut) : Prop where
  nle : n ≤ maxStream (LN m0)
  wsl : ws.length = 2 * n
  count : NativeRustcVm.WordAt d (wd m0 0) n.toUInt64
  words : NativeRustcVm.WordsAt d (wd m0 1) (ws.map K.lane)
  pcnt : NativeRustcVm.WordAt d (wd m0 (streamEnd (LN m0))) p.toUInt64
  phases : ∀ j (h : j < done.length), PhaseAt d (wd m0 (phaseBase (LN m0) j)) (phaseW done[j])

/-- **The result**: `decodeM`'s, AL `1` and the decoded proof, or AL `0`. -/
def Res (m0 m : MachineData) : Prop :=
  match decodeM (Bs m0) with
  | some r => boolRet m = 1 ∧
      DecodedAt m.dmem ⟨DEC m0, LEN m0, LN m0⟩ (streamW r.1) (openingsW r.2)
  | none => boolRet m = 0

/-- What `decode` reaches. -/
abbrev Post [Labels] (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ DecodePost m0 st.data

end

public section

theorem decodeStack_eq : decodeStack = 1296 := rfl
theorem workBytes_eq : workBytes = 483584 := rfl
theorem phaseBytes_eq : phaseBytes = 395288 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_lo : ∀ p ∈ slots, 32 ≤ p.1 ∧ p.1 + 8 ≤ 80 := by decide

/-- `decodedWords L` as a number. -/
theorem decodedWords_eq (L : Nat) : decodedWords L = 2 * (L / 16) + 2 + 8 * 49411 := by
  simp only [decodedWords, phaseBase, streamEnd, maxStream, show phaseWords = 49411 from rfl,
    wireMaxPhases]
  omega

theorem phaseBase_eq (L k : Nat) : phaseBase L k = 2 * (L / 16) + 2 + k * 49411 := by
  simp only [phaseBase, streamEnd, maxStream, show phaseWords = 49411 from rfl]
  omega

theorem streamEnd_eq (L : Nat) : streamEnd L = 2 * (L / 16) + 1 := by
  simp only [streamEnd, maxStream]
  omega

variable {m0 : MachineData}

theorem length_Bs : (Bs m0).length = LN m0 := length_bytesOf _ _ _

theorem Bs_eq {B : List UInt8} (hl : B.length = LN m0)
    (h : NativeRustcVm.BytesAt m0.dmem (BP m0) B) : B = Bs m0 := by
  have := bytesOf_eq h
  rw [hl] at this
  exact this.symm

/-- `decodeM`'s result: what it is when it is not. -/
theorem res_none {m : MachineData} (h : decodeM (Bs m0) = none) (hb : boolRet m = 0) :
    Res m0 m := by
  unfold Res; rw [h]; exact hb

section
variable [Labels]

theorem geo_of (h : DecodePre m0) : Geo m0 := by
  obtain ⟨hst, hrc, hL, hlen, hbOk, hdOk, hwOk, hd, hd', hgot⟩ := h
  have hst' : StackOk m0 1296 := hst
  have hS := stackBelow_toNat (m := m0) (n := 1296) hst'.1
  have h8 := hst'.2.1
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, stackR, rcR,
    decodeStack_eq, workBytes_eq] at hd hd'
  obtain ⟨⟨-, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := hd
  unfold NativeRustcVm.Apart at h2 h3 h4 h5 h6
  rw [hS] at h2 h3
  refine ⟨hst', hrc, hL, hlen, hbOk, hdOk, hwOk, by omega, by omega,
    by omega, by omega, by omega, fun hp ↦ ?_, fun hp ↦ ?_, fun hp ↦ ?_, fun hp ↦ ?_, hgot⟩
  all_goals
    obtain ⟨⟨-, g2, -, -⟩, ⟨g4, -, -⟩, ⟨g5, g6⟩, -⟩ := hd' hp
    unfold NativeRustcVm.Apart at g2 g4 g5 g6
    rw [hS] at g2
    omega

theorem Geo.sp (G : Geo m0) : 1296 ≤ SP0 m0 := G.st.1
theorem Geo.top (G : Geo m0) : SP0 m0 + 8 ≤ 2 ^ 64 := G.st.2.1
theorem Geo.dNw (G : Geo m0) : (DEC m0).toNat + 8 * LEN m0 ≤ 2 ^ 64 := G.dOk.2
theorem Geo.wNw (G : Geo m0) : (WK m0).toNat + 483584 ≤ 2 ^ 64 := G.wOk.2
theorem Geo.bNw (G : Geo m0) : (BP m0).toNat + LN m0 ≤ 2 ^ 64 := G.bOk.2
theorem Geo.cNw (G : Geo m0) : rcAddr.toNat + 192 ≤ 2 ^ 64 := G.rc.2.1
theorem Geo.cS (G : Geo m0) : rcAddr.toNat + 192 ≤ SP0 m0 - 1296 ∨ SP0 m0 + 8 ≤ rcAddr.toNat := by
  have := G.rc.2.2
  unfold NativeRustcVm.Apart at this
  rw [stackBelow_toNat G.sp] at this
  omega

/-- Byte `j` of the frame. -/
theorem Geo.fr (G : Geo m0) {j : Nat} (hj : j < 88) :
    (off (stackBelow m0 80) j).toNat = SP0 m0 - 80 + j :=
  PhaseM.frame_toNat (by have := G.sp; omega) G.top hj

/-- Word `i` of the decoded area. -/
theorem Geo.wd (G : Geo m0) {i : Nat} (hi : i < LEN m0) :
    (wd m0 i).toNat = (DEC m0).toNat + 8 * i := by
  have := G.dNw
  exact toNat_off (by omega)

/-- The loader slots survive the decoder's stack, decoded-area and work writes. -/
theorem Geo.got_keep (G : Geo m0) {d : Mem 64}
    (h : NativeRustcVm.SameOutside m0.dmem d (Chg m0)) :
    ∀ l ∈ ["memcpy", "memset"], ∀ i < 8,
      d.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  intro l hl i hi
  obtain ⟨_, hn, hs, ha⟩ := G.got.1 l hl
  have hd := ha (DEC m0, 8 * LEN m0) (by simp)
  have hw := ha (WK m0, 483584) (by simp)
  change Apart (gotAddr l) 8 (stackBelow m0 1296) 1304 at hs
  unfold Apart at hs hd hw
  dsimp only at hd hw
  change (gotAddr l).toNat + 8 ≤ 2 ^ 64 at hn
  rw [stackBelow_toNat G.sp] at hs
  refine h _ fun hq => ?_
  unfold Chg at hq
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hq
  omega

/-- The bytes, as at the entry. -/
theorem bytes_entry (G : Geo m0) : NativeRustcVm.BytesAt m0.dmem (BP m0) (Bs m0) :=
  bytesAt_bytesOf G.bOk.1

end

/-! ## Steps -/

variable [Host] {k : Nat}

/-- **A block from `frS`** keeping memory, RBX and R15. -/
theorem fblk (hp : Placed code k) (G : Geo m0) {bj : List Directive} {j : Nat}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ []) {x : Exit}
    (hrun : exec bj frS = some (after bj frS, x)) (hx : ∀ l, x = .call l → False)
    (hok : FrOk (after bj frS) = true) (hbx : (after bj frS).reg .rbx = some (.reg .rbx))
    (h15 : (after bj frS).reg .r15 = some (.reg .r15))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hbod : Bod m0 8 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Bod m0 8 st'.data → st'.data.dmem = st.data.dmem →
      Match (frameEnv m0 st.data 80 []) (after bj frS) st'.data →
      PcOk (frameEnv m0 st.data 80 []) x (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  simp only [FrOk, Bool.and_eq_true, List.isEmpty_iff] at hok
  have hst : StackOk m0 1296 := G.st
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 80) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hbod.fr.kept,
      frame_noWrap hst (by decide)⟩ (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 80 []) frS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of hb hne hp) hrun hwf (fun l h ↦ (hx l h).elim) hpc hm
    fun st' hm' hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hok.2
  refine cont st' ⟨Frame.of_block hbod.fr hwf hm' hok.1 slots_le, ?_,
    (hm'.regs .rbx _ hbx).trans hbod.rbx, (hm'.regs .r15 _ h15).trans hbod.r15⟩ hd hm' hpc'
  rw [hd]; exact hbod.chg

/-- **The epilogue** (`b15`, at `NativeRustcVmX64.Vm.Decode.label_10`): the result as it is. -/
theorem fin (hp : Placed code k) (G : Geo m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b15Offset)) (hbod : Bod m0 8 st.data) (hres : Res m0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hepi, hmem, hrax⟩ := ok_b15
  have hst : StackOk m0 1296 := G.st
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 80) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hbod.fr.kept,
      frame_noWrap hst (by decide)⟩ (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 80 []) frS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hbod.fr hwf hm' hepi
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf hmem
  have ha : reg st'.data .rax = reg st.data .rax := hm'.regs .rax _ hrax
  simp only [PcOk] at hpc'
  refine .done _ ⟨by rw [hpc']; exact hbod.fr.load_ret hst (by decide), hrsp, ?_, ?_, hsv⟩
  · intro B hl hB
    rw [Bs_eq hl hB]
    have hres' := hres
    unfold Res at hres'
    unfold boolRet at hres' ⊢
    rw [ha, hd]
    exact hres'
  · intro q hq
    rw [hd]
    refine hbod.chg q fun h ↦ hq ?_
    have hS := stackBelow_toNat (m := m0) (n := 1296) G.sp
    have := G.dNw; have := G.wNw; have := G.top
    rcases h with h | h | h
    · refine ⟨frameR m0 decodeStack, by simp, ?_⟩
      show NativeRustcVm.InRange (stackBelow m0 1296) 1296 q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hS]; omega), hS]
      omega
    · refine ⟨⟨DEC m0, 8 * LEN m0⟩, by simp, ?_⟩
      show NativeRustcVm.InRange (DEC m0) (8 * LEN m0) q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega)]
      omega
    · refine ⟨⟨WK m0, workBytes⟩, by simp, ?_⟩
      show NativeRustcVm.InRange (WK m0) workBytes q
      rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [workBytes_eq]; omega),
        workBytes_eq]
      omega

end

end NativeRustcVmX64.Wire.Decode
