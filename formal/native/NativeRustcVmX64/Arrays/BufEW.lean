module

public import NativeRustcVmX64.Arrays.Common

/-!
# `Buf<EW, N>::extend` on x86-64, for every `N`

rustc compiles `Buf<EW, N>::extend(self, xs)` to the same code for every `N` but the constant `N`
and the local labels: `b0` sets AL = 1 and returns at once for an empty `xs` (`b7`); `b1` pushes
RBX, loads the count `c` and sets R8 = `c + 1`, RCX = `-N` (`-max(c, N)`), R9 = the slot of entry
`c` plus `8`, R10 = `0`, RDX = `16·|xs|`; the loop head `b2` leaves (`b5`: AL = 0, `b6`, `b7`)
when the buffer is full, else `b3` copies element `j` (at RSI + R10) into entry `c + j` (at
R9 + R10 - 8), stores the count `c + j + 1` and loops while elements remain, then returns (`b4`,
`b6`, `b7`).

**`spec_of`**: given an instance's blocks, placed, and the executor's runs of them (`Runs`, its
facts decided per instance), the instance meets `BufEWExtendPre N`/`BufEWExtendPost N`. The loop
head's invariant (`Inv`): `j` elements copied, the count word `c + j`, the entries the buffer's
then `xs`'s first `j`, RBX's entry value in the pushed slot (`Frame`).
-/

namespace NativeRustcVmX64.Arrays.BufEW

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Field
open NativeRustcVm (ewsOf ewOf wordOf bufEWOf BufEWAt EWsAt EWAt WordAt)

@[expose] public section

/-- At the entry (`b0`, `b7`): region 0 the pushed slot and the return address, RSP at `8`. -/
abbrev entryS : SState := frameS 8
/-- At `b1`: also region 1 the count word, RDI its address. -/
def countS : SState := init [16, 8] [(.rsp, .ptr 0 8), (.rdi, .ptr 1 0)]
/-- Registers only (`b2`, `b4`). -/
def regsS : SState := init []
/-- A turn of the loop (`b3`): region 0 the entry written, 1 the count word, 2 the element read;
R9 + R10 the entry plus `8`, RSI + R10 the element, RDI the count word. -/
def bodyS : SState := init [16, 8, 16] [(.rdi, .ptr 1 0)] [] []
  [(.bin .add .W64 (.reg .r9) (.reg .r10), 0, 8), (.bin .add .W64 (.reg .rsi) (.reg .r10), 2, 0)]
/-- The epilogue (`b5`-`b7`, `b6`-`b7`): region 0 the pushed slot and the return address, RSP at
`0`. -/
def endS : SState := init [16] [(.rsp, .ptr 0 0)]

/-- `b0`'s branch: `xs` empty. -/
def c0 : SBool := .cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0)
/-- `b2`'s branch: the buffer full. -/
def c2 : SBool := .cmp .eq .W64 (.bin .add .W64 (.reg .rcx) (.reg .r8)) (.lit 1)
/-- `b3`'s branch: elements remain. -/
def c3 : SBool := .not (.cmp .eq .W64 (.reg .rdx) (.bin .add .W64 (.lit 16) (.reg .r10)))

/-- `movb $1, %al`. -/
def al1 : Sym := .bin .merge .W8 (.reg .rax) (.lit 1)
/-- `b1`'s RCX: minus the larger of the count and `N`. -/
def rcxSym (N : Nat) : Sym :=
  .un .neg .W64 (.ite (.not (.cmp .ult .W64 (.load 1 0 8) (.lit (N + 1)))) (.load 1 0 8) (.lit N))
/-- `b1`'s R9: the slot of entry `c` plus `8`. -/
def r9Sym : Sym :=
  .bin .add .W64 (.lit 16) (.bin .add .W64 (.ptr 1 0) (.bin .shl .W64 (.load 1 0 8) (.lit 4)))

/-- The callee-saved registers but RBX. -/
def others : List Reg64 := [.rbp, .r12, .r13, .r14, .r15]
/-- The registers the loop head keeps. -/
def loopRegs : List Reg64 := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] ++ others
/-- The registers a turn keeps. -/
def bodyRegs : List Reg64 := [.rax, .rcx, .rdx, .rsi, .rdi, .r9, .rsp] ++ others

/-- What the executor's runs of an instance's blocks give. -/
structure Runs [Host] (N : Nat) (b0 b1 b2 b3 b4 b5 b6 b7 : List Directive)
    (k k1 k2 k3 k4 k5 k6 k7 : Nat) (l2 l3 l5 l6 : Label)
    (S0 S7a S1 S2 S3 S4 S7 S7' : SState) : Prop where
  hb0 : b0.IsInfixAt Host.prog k
  hb1 : b1.IsInfixAt Host.prog k1
  hb2 : b2.IsInfixAt Host.prog k2
  hb3 : b3.IsInfixAt Host.prog k3
  hb4 : b4.IsInfixAt Host.prog k4
  hb567 : (b5 ++ b6 ++ b7).IsInfixAt Host.prog k5
  hb67 : (b6 ++ b7).IsInfixAt Host.prog k6
  hb7 : b7.IsInfixAt Host.prog k7
  e1 : k + b0.length = k1
  e2 : k1 + b1.length = k2
  e3 : k2 + b2.length = k3
  e4 : k3 + b3.length = k4
  hl2 : Labels.label l2 = Host.addrOf k2
  hl3 : Labels.label l3 = Host.addrOf k5
  hl5 : Labels.label l5 = Host.addrOf k6
  hl6 : Labels.label l6 = Host.addrOf k7
  x0 : exec b0 entryS = some (S0, .cond c0 l6)
  x7a : exec b7 S0 = some (S7a, .ret (.load 0 8 8))
  x1 : exec b1 countS = some (S1, .fall)
  x2 : exec b2 regsS = some (S2, .cond c2 l3)
  x3 : exec b3 bodyS = some (S3, .cond c3 l2)
  x4 : exec b4 regsS = some (S4, .jump l5)
  x7 : exec (b5 ++ b6 ++ b7) endS = some (S7, .ret (.load 0 8 8))
  x7' : exec (b6 ++ b7) endS = some (S7', .ret (.load 0 8 8))
  f0 : keepsAll entryS S0 (.rdx :: .rsi :: .rdi :: Arrays.calleeRegs) = true ∧
    S0.reg .rax = some al1
  f7a : keeps entryS S7a = true ∧ S7a.reg .rsp = some (.ptr 0 ((8 + 8 : Nat) : Int)) ∧
    S7a.mem = [] ∧ S7a.reg .rax = some al1
  f1 : S1.reg .rax = some (.reg .rax) ∧
    S1.reg .rdx = some (.bin .shl .W64 (.reg .rdx) (.lit 4)) ∧ S1.reg .r9 = some r9Sym ∧
    S1.reg .rcx = some (rcxSym N) ∧ S1.reg .r8 = some (.bin .add .W64 (.load 1 0 8) (.lit 1)) ∧
    S1.reg .r10 = some (.lit 0) ∧ S1.reg .rsp = some (.ptr 0 0) ∧
    S1.reg .rsi = some (.reg .rsi) ∧ S1.reg .rdi = some (.ptr 1 0) ∧
    keepsRegs countS S1 others = true ∧ (∀ w ∈ S1.mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (∀ i < 8, findWrite 0 (0 + i) S1.mem = some (.reg .rbx, i))
  f2 : keepsAll regsS S2 loopRegs = true
  f3 : S3.reg .r8 = some (.bin .add .W64 (.reg .r8) (.lit 1)) ∧
    S3.reg .r10 = some (.bin .add .W64 (.lit 16) (.reg .r10)) ∧
    keepsRegs bodyS S3 bodyRegs = true ∧
    (∀ w ∈ S3.mem, (w.r = 0 ∧ w.off + w.n ≤ 16) ∨ (w.r = 1 ∧ w.off + w.n ≤ 8)) ∧
    (∀ i < 8, findWrite 0 (0 + i) S3.mem = some (.load 2 0 8, i)) ∧
    (∀ i < 8, findWrite 0 (0 + 8 + i) S3.mem = some (.load 2 8 8, i)) ∧
    (∀ i < 8, findWrite 1 (0 + i) S3.mem = some (.reg .r8, i))
  f4 : keepsAll regsS S4 (.rax :: others) = true
  f7 : S7.reg .rax = some (.lit 0) ∧ S7.reg .rbx = some (.load 0 0 8) ∧
    S7.reg .rsp = some (.ptr 0 ((8 + 8 : Nat) : Int)) ∧ S7.mem = [] ∧
    keepsRegs endS S7 others = true
  f7' : S7'.reg .rax = some (.reg .rax) ∧ S7'.reg .rbx = some (.load 0 0 8) ∧
    S7'.reg .rsp = some (.ptr 0 ((8 + 8 : Nat) : Int)) ∧ S7'.mem = [] ∧
    keepsRegs endS S7' others = true

end

public section

/-- The buffer. -/
abbrev buf (m : MachineData) : BitVec 64 := reg m .rdi
/-- `xs`. -/
abbrev src (m : MachineData) : BitVec 64 := reg m .rsi
/-- `|xs|`. -/
abbrev len (m : MachineData) : Nat := (reg m .rdx).toNat
/-- The buffer's count. -/
abbrev cnt (m : MachineData) : Nat := (wordOf m.dmem (buf m)).toNat
/-- `xs`'s elements. -/
abbrev xs (m : MachineData) : List EW := ewsOf m.dmem (src m) (len m)

theorem slice_toList (m : MachineData) : (slice m (reg m .rsi) (reg m .rdx)).toList = xs m := rfl

theorem calleeRegs_eq : Arrays.calleeRegs = .rbx :: others := rfl

/-- The frame of the loop and the epilogue: RSP at the pushed slot, RBX's entry value there, the
other callee-saved registers the entry's, memory as at the entry but in the buffer and the slot. -/
structure Frame (N : Nat) (m0 s : MachineData) : Prop where
  rsp : rspOf s = stackBelow m0 8
  slot : SlotsAt s.dmem (stackBelow m0 8) m0 [(0, .rbx)]
  regs : ∀ r ∈ others, reg s r = reg m0 r
  kept : Kept m0.dmem s.dmem
  same : Changes m0 s bufEWExtendStack (buf m0) (8 + 16 * N)

/-- **The loop head**, `j` elements copied. -/
structure Inv (N : Nat) (m0 : MachineData) (j : Nat) (s : MachineData) : Prop where
  frame : Frame N m0 s
  lt : j < len m0
  le : cnt m0 + j ≤ N
  al : boolRet s = 1
  rdi : reg s .rdi = buf m0
  rsi : reg s .rsi = src m0
  rdx : reg s .rdx = BitVec.ofNat 64 (16 * len m0)
  r10 : reg s .r10 = BitVec.ofNat 64 (16 * j)
  r8 : reg s .r8 = BitVec.ofNat 64 (cnt m0 + j + 1)
  rcx : reg s .rcx = -BitVec.ofNat 64 N
  r9 : reg s .r9 = buf m0 + BitVec.ofNat 64 (16 * cnt m0 + 16)
  count : WordAt s.dmem (buf m0) (cnt m0 + j).toUInt64
  ents : EWsAt s.dmem (buf m0 + 8#64) (bufEWOf m0.dmem (buf m0) ++ (xs m0).take j)

/-- The postcondition, reached. -/
abbrev Post (N : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ BufEWExtendPost N m0 s.data

/-- The buffer at the entry. -/
theorem bufEWAt_entry {N : Nat} {m0 : MachineData} (hc : cnt m0 ≤ N)
    (hm : Mapped m0.dmem (buf m0) (8 + 16 * N)) :
    BufEWAt m0.dmem (buf m0) N (bufEWOf m0.dmem (buf m0)) := by
  refine ⟨by simp [bufEWOf]; exact hc, ?_, ?_⟩
  · simp only [bufEWOf, NativeRustcVm.length_ewsOf, Nat.toUInt64_eq, UInt64.ofNat_toNat]
    exact NativeRustcVm.wordAt_of_mapped fun i hi ↦ hm i (by omega)
  · refine NativeRustcVm.ewsAt_of_mapped fun i hi ↦ ?_
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add]
    have hc' : (wordOf m0.dmem (buf m0)).toNat ≤ N := hc
    exact hm _ (by omega)

/-- The return address is neither in the buffer nor in the pushed slot. -/
theorem ret_same {N : Nat} {m0 s : MachineData} (hpre : BufEWExtendPre N m0)
    (hc : Changes m0 s bufEWExtendStack (buf m0) (8 + 16 * N)) :
    ∀ j < 8, s.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) := by
  intro j hj
  have hS := hpre.1
  have hS1 := hS.1
  have hS2 := hS.2.1
  refine hc _ fun h ↦ h.elim (ret_not_in hS hpre.2.2.1.2 hpre.2.2.2.2.2.1 j hj) fun h ↦ ?_
  have := (rspOf m0).isLt
  rw [Sym.inRange_iff (by rw [stackBelow_toNat hS1]; omega), stackBelow_toNat hS1,
    toNat_add_ofNat _ _ (by omega)] at h
  omega

variable [Host] {N : Nat}

/-- **The epilogue** (`b5`-`b7` or `b6`-`b7`) from the frame: back at the return address with RAX
the block's `v`, memory as in the frame, the callee-saved registers the entry's. -/
theorem finish {bb : List Directive} {kb : Nat} {S : SState} {v : Sym}
    (hk : bb.IsInfixAt Host.prog kb) (hx : exec bb endS = some (S, .ret (.load 0 8 8)))
    (hf : S.reg .rax = some v ∧ S.reg .rbx = some (.load 0 0 8) ∧
      S.reg .rsp = some (.ptr 0 ((8 + 8 : Nat) : Int)) ∧ S.mem = [] ∧
      keepsRegs endS S others = true)
    {m0 : MachineData} (hpre : BufEWExtendPre N m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf kb) (hF : Frame N m0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = retOf m0 ∧ rspOf s'.data = rspOf m0 + 8#64 ∧
      reg s'.data .rax = v.eval (frameEnv m0 s.data 8) ∧ s'.data.dmem = s.data.dmem ∧
      Saved m0 s'.data) s := by
  obtain ⟨hax, hbx, hsp, hmem, hkeep⟩ := hf
  have hS : StackOk m0 8 := hpre.1
  have hwf := frame_wf (m := s.data) (vars := fun _ ↦ 0) (ret := 0) hS hF.kept
  have hm : Match (frameEnv m0 s.data 8) endS s.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show rspOf s.data = stackBelow m0 8 + BitVec.ofInt 64 0 by rw [hF.rsp]; simp, trivial⟩
      trivial trivial trivial
  refine exec_at hk hx hwf (by intro l h; cases h) hpc hm fun s' hm' hpc' ↦ .done _ ?_
  have hdm : s'.data.dmem = s.data.dmem := hm'.dmem_eq hwf hmem
  refine ⟨?_, ?_, hm'.regs .rax _ hax, hdm, fun r hr ↦ ?_, fun p h ↦ hm'.kept hwf p (hF.kept p h)⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    exact load_ret hS (ret_same hpre hF.same)
  · show s'.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ hsp]
    exact frame_rsp 8 8
  · rcases List.mem_cons.mp (calleeRegs_eq ▸ mem_calleeRegs hr) with rfl | h
    · show s'.data.regs.get64 .rbx = _
      rw [hm'.regs .rbx _ hbx]
      exact slot_load (r := 0) hF.slot (by simp)
    · exact (regs_eq_of hm hm' hkeep r h).trans (hF.regs r h)

omit [Host] in
/-- A block of registers only keeps the frame. -/
theorem Frame.regs_block [Labels] {m0 s s' : MachineData} {S' : SState} {rs : List Reg64}
    (hF : Frame N m0 s) (hm : Match (Env.ofMachine s []) S' s')
    (hk : keepsAll regsS S' rs = true) (hrs : ∀ r ∈ others, r ∈ rs) :
    Frame N m0 s' ∧ (∀ r ∈ rs, reg s' r = reg s r) ∧ s'.dmem = s.dmem := by
  unfold keepsAll at hk
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk
  obtain ⟨hr, hmem⟩ := hk
  have he := regs_eq_of (match_nil _) hm hr
  have hdm : s'.dmem = s.dmem := hm.dmem_eq (Env.wf_nil _) hmem
  refine ⟨⟨?_, ?_, fun r h ↦ (he r (List.mem_cons_of_mem _ (hrs r h))).trans (hF.regs r h),
    by rw [hdm]; exact hF.kept, fun p hp ↦ by rw [hdm]; exact hF.same p hp⟩,
    fun r h ↦ he r (List.mem_cons_of_mem _ h), hdm⟩
  · show reg s' .rsp = _
    rw [he .rsp (by simp)]; exact hF.rsp
  · rw [hdm]; exact hF.slot

omit [Host] in
theorem sixteen_add (i : Nat) :
    BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

variable {b0 b1 b2 b3 b4 b5 b6 b7 : List Directive} {k k1 k2 k3 k4 k5 k6 k7 : Nat}
  {l2 l3 l5 l6 : Label} {S0 S7a S1 S2 S3 S4 S7 S7' : SState}

/-- **A turn of the loop**: the buffer full and `None` returned, or element `j` copied, then back
at the head or `Some` returned. -/
theorem step (R : Runs N b0 b1 b2 b3 b4 b5 b6 b7 k k1 k2 k3 k4 k5 k6 k7 l2 l3 l5 l6
      S0 S7a S1 S2 S3 S4 S7 S7')
    {m0 : MachineData} (hpre : BufEWExtendPre N m0) {j : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf k2) (hI : Inv N m0 j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post N m0 s' ∨
      (s'.pc = Host.addrOf k2 ∧ Inv N m0 (j + 1) s'.data)) s := by
  have hS : StackOk m0 8 := hpre.1
  obtain ⟨-, hc, ⟨hmB, hnB⟩, ⟨hmS, hnS⟩, hap, hoB, hoS⟩ := hpre
  have hnB' : (buf m0).toNat + (8 + 16 * N) ≤ 2 ^ 64 := hnB
  have hnS' : (src m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnS
  have hlS := lt_of_offStack hnS hoS
  have hlt := hI.lt
  have hle := hI.le
  have hL : len m0 = (reg m0 .rdx).toNat := rfl
  have hC : cnt m0 = (wordOf m0.dmem (buf m0)).toNat := rfl
  have hC2 : cnt m0 = (wordOf m0.dmem (reg m0 .rdi)).toNat := rfl
  have eB : (buf m0).toNat = (reg m0 .rdi).toNat := rfl
  have eS : (src m0).toNat = (reg m0 .rsi).toNat := rfl
  have hN : 16 * N ≤ 2 ^ 64 := by omega
  -- `b2`: full?
  refine exec_at R.hb2 R.x2 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun s2 hm2 hpc2 ↦ ?_
  obtain ⟨hF2, e2, hdm2⟩ := hI.frame.regs_block hm2 R.f2 (fun r h ↦ by
    exact List.mem_append_right _ h)
  simp only [PcOk, c2, R.e3] at hpc2
  rw [eval_cmp_eq, eval_add, eval_reg, eval_reg, eval_lit] at hpc2
  rw [show (Env.ofMachine s.data []).regs .rcx = reg s.data .rcx from rfl,
    show (Env.ofMachine s.data []).regs .r8 = reg s.data .r8 from rfl, hI.rcx, hI.r8,
    neg_add_beq_one (by omega) (by omega)] at hpc2
  obtain ⟨hT, hFl⟩ := pc_cond hpc2
  by_cases hfull : cnt m0 + j = N
  · -- the buffer full: `None`.
    have hpc5 := (hT (decide_eq_true (by omega))).trans R.hl3
    obtain ⟨g0, g1, g2, g3, g4⟩ := R.f7
    refine Eventually.mono (finish R.hb567 R.x7 ⟨g0, g1, g2, g3, g4⟩ ⟨hS, hc, ⟨hmB, hnB⟩,
      ⟨hmS, hnS⟩, hap, hoB, hoS⟩ hpc5 hF2) fun s' ⟨h1, h2, h3, h4, h5⟩ ↦ Or.inl ⟨h1, h2, ?_,
      fun p hp ↦ by rw [h4]; exact hF2.same p hp, h5⟩
    split
    · rename_i hn; exfalso; omega
    show (reg s'.data .rax).toNat % 256 = 0
    rw [h3]; rfl
  have hpc3 := hFl fun h ↦ hfull (by have := of_decide_eq_true h; omega)
  -- the turn: three regions
  have hcj : cnt m0 + j < N := by omega
  obtain ⟨dst, hdst⟩ : ∃ d : BitVec 64, d = buf m0 + BitVec.ofNat 64 (8 + 16 * (cnt m0 + j)) :=
    ⟨_, rfl⟩
  obtain ⟨sj, hsj⟩ : ∃ d : BitVec 64, d = src m0 + BitVec.ofNat 64 (16 * j) := ⟨_, rfl⟩
  have hkept : Kept m0.dmem s2.data.dmem := hF2.kept
  have hnD : NoWrap dst 16 := by
    unfold NoWrap; rw [hdst, toNat_add_ofNat _ _ (by omega)]; omega
  have hnC : NoWrap (buf m0) 8 := by unfold NoWrap; omega
  have hnJ : NoWrap sj 16 := by
    unfold NoWrap; rw [hsj, toNat_add_ofNat _ _ (by omega)]; omega
  have hmD : Mapped s2.data.dmem dst 16 := fun i hi ↦ by
    rw [hdst, addr_add]; exact hkept _ (hmB _ (by omega))
  have hmC : Mapped s2.data.dmem (buf m0) 8 := fun i hi ↦ hkept _ (hmB _ (by omega))
  have hmJ : Mapped s2.data.dmem sj 16 := fun i hi ↦ by
    rw [hsj, addr_add]; exact hkept _ (hmS _ (by omega))
  have hdD : dst.toNat = (buf m0).toNat + (8 + 16 * (cnt m0 + j)) := by
    rw [hdst]; exact toNat_add_ofNat _ _ (by omega)
  have hdJ : sj.toNat = (src m0).toNat + 16 * j := by
    rw [hsj]; exact toNat_add_ofNat _ _ (by omega)
  have hap' : (buf m0).toNat + (8 + 16 * N) ≤ (src m0).toNat ∨
      (src m0).toNat + 16 * len m0 ≤ (buf m0).toNat := hap
  have hwf : (Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]).WF := by
    refine Env.wf_of ⟨⟨hmD, hnD⟩, ⟨hmC, hnC⟩, ⟨hmJ, hnJ⟩, trivial⟩ ?_
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons nofun .nil))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · show Apart dst 16 (buf m0) 8
        unfold Apart; omega
      · show Apart dst 16 sj 16
        unfold Apart; omega
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      show Apart (buf m0) 8 sj 16
      unfold Apart; omega
  have r2 : ∀ r ∈ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10],
      reg s2.data r = reg s.data r := fun r h ↦ e2 r (List.mem_append_left _ h)
  have hm3 : Match (Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]) bodyS s2.data := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨?_, trivial⟩ trivial trivial ⟨?_, ?_, trivial⟩
    · show reg s2.data .rdi = buf m0 + BitVec.ofInt 64 0
      rw [r2 .rdi (by simp), hI.rdi]; simp
    · show reg s2.data .r9 + reg s2.data .r10 = dst + BitVec.ofInt 64 8
      rw [r2 .r9 (by simp), r2 .r10 (by simp), hI.r9, hI.r10,
        show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, hdst, addr_add, addr_add]
      exact addr_eq (by omega)
    · show reg s2.data .rsi + reg s2.data .r10 = sj + BitVec.ofInt 64 0
      rw [r2 .rsi (by simp), r2 .r10 (by simp), hI.rsi, hI.r10, hsj]; simp
  refine exec_at R.hb3 R.x3 hwf (by intro l h; cases h) hpc3 hm3 fun s3 hm3' hpc3' ↦ ?_
  obtain ⟨g8, g10, gk, gw, gw0, gw1, gw2⟩ := R.f3
  have e3 := regs_eq_of hm3 hm3' gk
  have hsame3 := same01 hm3' hwf le_rfl le_rfl gw
  -- the element read, unchanged since the entry
  have hJ : ewOf s2.data.dmem sj = (xs m0)[j]'(by simp; exact hlt) := by
    rw [hsj]
    exact elem_of_apart hF2.same hS hnS hoS (apart_symm hap) hnB hlt
  -- the entry written
  have hv : ewArg ((Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]).load 2 0 8)
      ((Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]).load 2 8 8) =
      (xs m0)[j]'(by simp; exact hlt) := by
    rw [← hJ]
    have h := ewOf_loads (Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]) 2 0
    rw [add_ofNat_zero] at h
    exact h.symm
  have hD : EWAt s3.data.dmem dst ((xs m0)[j]'(by simp; exact hlt)) := by
    have a := ewAt_of_writes hm3' (r := 0) (o := 0) rfl (by decide) gw0 gw1
    rw [eval_load, eval_load, hv, add_ofNat_zero] at a
    exact a
  -- the count written
  have hCw : WordAt s3.data.dmem (buf m0) (cnt m0 + j + 1).toUInt64 := by
    have a := wordAt_of_write hm3' (r := 1) (o := 0) rfl (by decide) gw2
    rw [add_ofNat_zero, eval_reg] at a
    rw [show (Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]).regs .r8 =
      reg s2.data .r8 from rfl, r2 .r8 (by simp), hI.r8] at a
    exact a
  have hlen0 : (bufEWOf m0.dmem (buf m0) ++ (xs m0).take j).length = cnt m0 + j := by
    simp [bufEWOf]; omega
  have hE : EWsAt s3.data.dmem (buf m0 + 8#64)
      (bufEWOf m0.dmem (buf m0) ++ (xs m0).take (j + 1)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp; exact hlt), Option.toList_some,
      ← List.append_assoc, NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton, hlen0]
    constructor
    · refine ewsAt_congr (hdm2 ▸ hI.ents) fun i hi ↦ ?_
      rw [hlen0] at hi
      rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add]
      refine hsame3 _ ?_ ?_
      · rw [Sym.inRange_iff hnD, hdD, toNat_add_ofNat _ _ (by omega)]; omega
      · rw [Sym.inRange_iff hnC, toNat_add_ofNat _ _ (by omega)]; omega
    · rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add, ← hdst]
      exact hD
  have hsameT : Changes m0 s3.data bufEWExtendStack (buf m0) (8 + 16 * N) := fun p hp ↦ by
    have hp' : ¬InRange (buf m0) (8 + 16 * N) p := fun h ↦ hp (Or.inl h)
    rw [hsame3 p (fun h ↦ hp' ?_) (fun h ↦ hp' ?_)]
    · exact hF2.same p hp
    · rw [Sym.inRange_iff hnD, hdD] at h; rw [Sym.inRange_iff hnB]; omega
    · rw [Sym.inRange_iff hnC] at h; rw [Sym.inRange_iff hnB]; omega
  have hF3 : Frame N m0 s3.data := by
    refine ⟨?_, fun p hp i hi ↦ ?_, fun r h ↦ (e3 r (List.mem_append_right _ h)).trans
      (hF2.regs r h), fun p h ↦ hm3'.kept hwf p (hkept p h), hsameT⟩
    · show reg s3.data .rsp = _
      rw [e3 .rsp (by simp [bodyRegs])]; exact hF2.rsp
    · have hp1 : p.1 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rw [hp]
      simp only [List.length_map, List.length_range] at hi
      have hS1 := hS.1
      have hr0 := (rspOf m0).isLt
      have hfb : (stackBelow m0 8).toNat = (rspOf m0).toNat - 8 := stackBelow_toNat hS1
      have hoB' := hoB
      simp only [OffStack, Apart, bufEWExtendStack] at hoB'
      rw [hfb] at hoB'
      show s3.data.dmem.get? (stackBelow m0 8 + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) = _
      rw [addr_add, hsame3 _ ?_ ?_, ← addr_add]
      · exact hF2.slot p hp i (by simpa using hi)
      · rw [Sym.inRange_iff hnD, hdD, hp1, toNat_add_ofNat _ _ (by omega), hfb]; omega
      · rw [Sym.inRange_iff hnC, hp1, toNat_add_ofNat _ _ (by omega), hfb]; omega
  have r3 : ∀ r ∈ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r9], reg s3.data r = reg s.data r := by
    intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (e3 _ (by simp [bodyRegs])).trans (r2 _ (by simp))
  have h8 : reg s3.data .r8 = BitVec.ofNat 64 (cnt m0 + (j + 1) + 1) := by
    rw [show reg s3.data .r8 = (Sym.bin .add .W64 (.reg .r8) (.lit 1)).eval
      (Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]) from hm3'.regs .r8 _ g8,
      eval_add, eval_reg, eval_lit]
    show reg s2.data .r8 + _ = _
    rw [r2 .r8 (by simp), hI.r8, ← BitVec.ofNat_add]
    exact congrArg _ (by omega)
  have h10 : reg s3.data .r10 = BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show reg s3.data .r10 = (Sym.bin .add .W64 (.lit 16) (.reg .r10)).eval
      (Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]) from hm3'.regs .r10 _ g10,
      eval_add, eval_reg, eval_lit]
    show _ + reg s2.data .r10 = _
    rw [r2 .r10 (by simp), hI.r10, sixteen_add]
  -- the loop test
  simp only [PcOk, c3, R.e4] at hpc3'
  rw [eval_not, eval_cmp_eq, eval_add, eval_reg, eval_reg, eval_lit] at hpc3'
  rw [show (Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]).regs .rdx =
      reg s2.data .rdx from rfl,
    show (Env.ofMachine s2.data [(dst, 16), (buf m0, 8), (sj, 16)]).regs .r10 =
      reg s2.data .r10 from rfl, r2 .rdx (by simp), r2 .r10 (by simp), hI.rdx, hI.r10,
    sixteen_add, ofNat_beq (by omega) (by omega)] at hpc3'
  obtain ⟨hT3, hF3'⟩ := pc_cond hpc3'
  have hal3 : boolRet s3.data = 1 := by
    unfold boolRet; rw [r3 .rax (by simp)]; exact hI.al
  by_cases hM : j + 1 < len m0
  · have hpc4 := (hT3 (by simp; omega)).trans R.hl2
    refine .done _ (Or.inr ⟨hpc4, hF3, hM, by omega, hal3, (r3 .rdi (by simp)).trans hI.rdi,
      (r3 .rsi (by simp)).trans hI.rsi, (r3 .rdx (by simp)).trans hI.rdx, h10, h8,
      (r3 .rcx (by simp)).trans hI.rcx, (r3 .r9 (by simp)).trans hI.r9, ?_, hE⟩)
    rw [show cnt m0 + (j + 1) = cnt m0 + j + 1 by omega]; exact hCw
  · have hpc4 := hF3' (by simp; omega)
    refine exec_at R.hb4 R.x4 (Env.wf_nil _) (by intro l h; cases h) hpc4 (match_nil _)
      fun s4 hm4 hpc4' ↦ ?_
    obtain ⟨hF4, e4, hdm4⟩ := hF3.regs_block hm4 R.f4 (fun r h ↦ List.mem_cons_of_mem _ h)
    simp only [PcOk] at hpc4'
    obtain ⟨g0, g1, g2, g3, g4⟩ := R.f7'
    refine Eventually.mono (finish R.hb67 R.x7' ⟨g0, g1, g2, g3, g4⟩ ⟨hS, hc, ⟨hmB, hnB⟩,
      ⟨hmS, hnS⟩, hap, hoB, hoS⟩ (hpc4'.trans R.hl5) hF4) fun s' ⟨h1, h2, h3, h4, h5⟩ ↦
      Or.inl ⟨h1, h2, ?_, fun p hp ↦ by rw [h4, hdm4]; exact hsameT p hp, h5⟩
    have hj : j + 1 = len m0 := by omega
    rw [slice_toList]
    split
    rotate_left
    · rename_i hn; exfalso; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (reg s'.data .rax).toNat % 256 = 1
      rw [h3, eval_reg]
      show (reg s4.data .rax).toNat % 256 = 1
      rw [e4 .rax (by simp)]; exact hal3
    · simp [bufEWOf]; omega
    · rw [h4, hdm4]
      have : (bufEWOf m0.dmem (buf m0) ++ xs m0).length = cnt m0 + j + 1 := by
        simp [bufEWOf]; omega
      rw [this]; exact hCw
    · rw [h4, hdm4, ← List.take_of_length_le (l := xs m0) (i := j + 1) (by simp; omega)]
      exact hE

/-- **`Buf<EW, N>::extend` meets its contract**, from an instance's runs. -/
theorem spec_of (R : Runs N b0 b1 b2 b3 b4 b5 b6 b7 k k1 k2 k3 k4 k5 k6 k7 l2 l3 l5 l6
      S0 S7a S1 S2 S3 S4 S7 S7')
    {l0 : Label} (hl0 : Labels.label l0 = Host.addrOf k) :
    Spec (Labels.label l0) (BufEWExtendPre N) (BufEWExtendPost N) := by
  intro m0 hpre
  rw [hl0]
  have hpre' := hpre
  obtain ⟨hS, hc, ⟨hmB, hnB⟩, ⟨hmS, hnS⟩, hap, hoB, hoS⟩ := hpre
  have hS8 : StackOk m0 8 := hS
  have hnB' : (buf m0).toNat + (8 + 16 * N) ≤ 2 ^ 64 := hnB
  have hlS := lt_of_offStack hnS hoS
  have hL : len m0 = (reg m0 .rdx).toNat := rfl
  have hC : cnt m0 = (wordOf m0.dmem (buf m0)).toNat := rfl
  have hC2 : cnt m0 = (wordOf m0.dmem (reg m0 .rdi)).toNat := rfl
  have eB : (buf m0).toNat = (reg m0 .rdi).toNat := rfl
  have hc' : cnt m0 ≤ N := hc
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) hS8 fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 8) entryS m0 := match_frame
  refine exec_then R.hb0 R.x0 hwf (by intro l h; cases h) hm fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hk0, hax0⟩ := R.f0
  simp only [PcOk, c0, R.e1] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs, beq_ofNat _ (by decide)] at hpc1
  obtain ⟨hT, hFl⟩ := pc_cond hpc1
  have hal : boolRet s1.data = 1 := by
    show (s1.data.regs.get64 .rax).toNat % 256 = 1
    rw [hm1.regs .rax _ hax0]
    exact merge_one_mod _
  by_cases hz : len m0 = 0
  · -- `xs` empty: `Some`.
    have hpc7 := (hT (decide_eq_true hz)).trans R.hl6
    refine exec_at R.hb7 R.x7a hwf (by intro l h; cases h) hpc7 hm1 fun s' hm' hpc' ↦ .done _ ?_
    obtain ⟨hkeep, hsp, hmem, hax⟩ := R.f7a
    obtain ⟨hpc'', hrsp, hso, hsaved⟩ := leaf_done hS8 hm' hpc' hsp hkeep
      (fun w hw ↦ by rw [hmem] at hw; cases hw)
    have hdm : s'.data.dmem = m0.dmem := hm'.dmem_eq hwf hmem
    refine ⟨hpc'', hrsp, ?_, fun p hp ↦ hso p fun h ↦ hp (Or.inr h), hsaved⟩
    rw [slice_toList]
    split
    rotate_left
    · rename_i hn; exfalso; omega
    refine ⟨?_, ?_⟩
    · show (s'.data.regs.get64 .rax).toNat % 256 = 1
      rw [hm'.regs .rax _ hax]
      exact merge_one_mod _
    · rw [hdm, show xs m0 = [] from List.eq_nil_of_length_eq_zero (by simp; exact hz),
        List.append_nil]
      exact bufEWAt_entry hc hmB
  have hpc1 := hFl fun h ↦ hz (of_decide_eq_true h)
  -- `b1`: the push, the count, the loop's registers
  have hk0' := hk0
  unfold keepsAll at hk0'
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk0'
  obtain ⟨hr0, hmem0⟩ := hk0'
  have e1 := regs_eq_of hm hm1 hr0
  have hdm1 : s1.data.dmem = m0.dmem := hm1.dmem_eq hwf hmem0
  have hS1 := hS8.1
  have hr0' := (rspOf m0).isLt
  have hfb : (stackBelow m0 8).toNat = (rspOf m0).toNat - 8 := stackBelow_toNat hS1
  have hoB' := hoB
  simp only [OffStack, Apart, bufEWExtendStack] at hoB'
  rw [hfb] at hoB'
  have hwf1 : (Env.ofMachine s1.data [(stackBelow m0 8, 16), (buf m0, 8)]).WF := by
    refine Env.wf_of ⟨⟨fun i hi ↦ ?_, ?_⟩, ⟨fun i hi ↦ ?_, ?_⟩, trivial⟩ ?_
    · show (s1.data.dmem.get? (stackBelow m0 8 + BitVec.ofNat 64 i)).isSome
      rw [hdm1]; exact hS8.2.2 i hi
    · show (stackBelow m0 8).toNat + 16 ≤ 2 ^ 64
      rw [hfb]; have := hS8.2.1; omega
    · show (s1.data.dmem.get? (buf m0 + BitVec.ofNat 64 i)).isSome
      rw [hdm1]; exact hmB i (by have : i < 8 := hi; omega)
    · show (buf m0).toNat + 8 ≤ 2 ^ 64
      omega
    refine List.pairwise_pair.mpr ?_
    show Apart (stackBelow m0 8) 16 (buf m0) 8
    unfold Apart; rw [hfb]; omega
  have hm1' : Match (Env.ofMachine s1.data [(stackBelow m0 8, 16), (buf m0, 8)]) countS s1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨?_, ?_, trivial⟩ trivial trivial trivial
  case refine_1 =>
    show reg s1.data .rsp = stackBelow m0 8 + BitVec.ofInt 64 8
    rw [e1 .rsp (by simp)]
    show rspOf m0 = _
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
    unfold stackBelow; simp
  case refine_2 =>
    show reg s1.data .rdi = buf m0 + BitVec.ofInt 64 0
    rw [e1 .rdi (by simp)]; simp
  refine exec_at R.hb1 R.x1 hwf1 (by intro l h; cases h) hpc1 hm1' fun s2 hm2 hpc2 ↦ ?_
  simp only [PcOk, R.e2] at hpc2
  obtain ⟨g0, gdx, g9, gcx, g8, g10, gsp, gsi, gdi, gk, gw, gw0⟩ := R.f1
  have e2 := regs_eq_of hm1' hm2 gk
  have hunw : ∀ p, ¬InRange (stackBelow m0 8) 8 p → s2.data.dmem.get? p = m0.dmem.get? p :=
    fun p hp ↦ by
      rw [hm2.get?_mem0 hwf1 fun h ↦ hp (written_region0 rfl hwf1 (by decide) gw h)]
      show s1.data.dmem.get? p = _
      rw [hdm1]
  have hinB : ∀ i < 8 + 16 * N, ¬InRange (stackBelow m0 8) 8 (buf m0 + BitVec.ofNat 64 i) :=
    fun i hi ↦ not_inRange_of_apart (apart_mono hoB (by decide)) hnB
      (by unfold NoWrap; rw [hfb]; omega) hi
  have hload : (Env.ofMachine s1.data [(stackBelow m0 8, 16), (buf m0, 8)]).load 1 0 8 =
      (wordOf m0.dmem (buf m0)).toBitVec := by
    rw [load8_eq]
    show (wordOf s1.data.dmem (buf m0 + BitVec.ofNat 64 0)).toBitVec = _
    rw [hdm1, add_ofNat_zero]
  have hcN : (wordOf m0.dmem (buf m0)).toNat < 2 ^ 60 := by omega
  have hI : Inv N m0 0 s2.data := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, Nat.pos_of_ne_zero hz, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · show s2.data.regs.get64 .rsp = _
      rw [hm2.regs .rsp _ gsp]; show stackBelow m0 8 + BitVec.ofInt 64 0 = _; simp
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      have a := hm2.bytesAt_write (r := 0) rfl (by decide) gw0
      rw [eval_reg] at a
      rw [show (Env.ofMachine s1.data [(stackBelow m0 8, 16), (buf m0, 8)]).regs .rbx =
        reg m0 .rbx from e1 .rbx (by simp [Arrays.calleeRegs])] at a
      exact a
    · intro r hr
      refine (e2 r hr).trans (e1 r ?_)
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [Arrays.calleeRegs]
    · intro p h
      exact hm2.kept hwf1 p (by show (s1.data.dmem.get? p).isSome; rw [hdm1]; exact h)
    · intro p hp
      exact hunw p fun h ↦ hp (Or.inr h)
    · show (s2.data.regs.get64 .rax).toNat % 256 = 1
      rw [hm2.regs .rax _ g0, eval_reg]
      exact hal
    · show s2.data.regs.get64 .rdi = _
      rw [hm2.regs .rdi _ gdi]; show buf m0 + BitVec.ofInt 64 0 = _; simp
    · show s2.data.regs.get64 .rsi = _
      rw [hm2.regs .rsi _ gsi, eval_reg]; exact e1 .rsi (by simp)
    · show s2.data.regs.get64 .rdx = _
      rw [hm2.regs .rdx _ gdx, eval_shl_lit _ (by decide), eval_reg]
      show reg s1.data .rdx <<< 4 = _
      rw [e1 .rdx (by simp)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    · show s2.data.regs.get64 .r10 = _
      rw [hm2.regs .r10 _ g10]; rfl
    · show s2.data.regs.get64 .r8 = _
      rw [hm2.regs .r8 _ g8, eval_add, eval_load, eval_lit, hload]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
    · show s2.data.regs.get64 .rcx = _
      rw [hm2.regs .rcx _ gcx]
      simp only [rcxSym, Sym.eval, SBool.eval, CmpOp.apply, UnOp.apply, low_W64, ext_W64, hload]
      have hult : (wordOf m0.dmem (buf m0)).toBitVec.ult (BitVec.ofNat 64 (N + 1)) = true := by
        rw [BitVec.ult_iff_lt, BitVec.lt_def, UInt64.toNat_toBitVec, toNat_ofNat_lt (by omega)]
        omega
      simp [hult]
    · show s2.data.regs.get64 .r9 = _
      rw [hm2.regs .r9 _ g9]
      simp only [r9Sym, eval_add, eval_lit, eval_shl_lit _ (show 4 < 64 by decide), eval_load,
        hload]
      show BitVec.ofNat 64 16 + (buf m0 + BitVec.ofInt 64 0 + (wordOf m0.dmem (buf m0)).toBitVec <<< 4)
        = _
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        UInt64.toNat_toBitVec, show BitVec.ofInt 64 0 = 0#64 from rfl]
      omega
    · rw [Nat.add_zero, Nat.toUInt64_eq, UInt64.ofNat_toNat]
      refine wordAt_congr (NativeRustcVm.wordAt_of_mapped fun i hi ↦ hmB i (by omega))
        fun i hi ↦ hunw _ (hinB i (by omega))
    · rw [List.take_zero, List.append_nil]
      refine ewsAt_congr (bufEWAt_entry hc hmB).2.2 fun i hi ↦ ?_
      simp [bufEWOf] at hi
      rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add]
      exact hunw _ (hinB _ (by omega))
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf k2 ∧ ∃ j, len m0 - j = n ∧ Inv N m0 j s.data)
    (fun n s ⟨hpc, j, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
  refine Eventually.mono (step R hpre' hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨len m0 - (j + 1), by have := hI'.lt; omega, hpc', j + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.BufEW
