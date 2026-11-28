module

public import NativeRustcVmX64.Arrays.Common

/-!
# `Buf<u64, N>::extend` on x86-64, for every `N`

rustc compiles `Buf<u64, N>::extend(self, xs)` (instantiated at `N = 230`) without a frame: `b0`
sets AL = 1 and returns at once for an empty `xs` (`b4`); `b1` loads the count `c` and sets
RCX = `c + 1`, R8 = `-N` (`-max(c, N)`), RDX = `8·|xs|`; the loop head `b2` returns `None` (`b5`:
AL = 0) when the buffer is full, else `b3` copies element `j` (at RSI, advanced by 8) into entry
`c + j` (at RDI + 8 RCX), stores the count `c + j + 1` and loops while elements remain, then
returns `Some` (`b4`).

**`spec_of`**: given an instance's blocks, placed, and the executor's runs of them (`Runs`, its
facts decided per instance), the instance meets `BufU64ExtendPre N`/`BufU64ExtendPost N`. The loop
head's invariant (`Inv`): `j` elements copied, the count word `c + j`, the entries the buffer's
then `xs`'s first `j`.
-/

namespace NativeRustcVmX64.Arrays.BufU64

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Field
open NativeRustcVm (wordsOf wordOf bufWordsOf BufWordsAt WordsAt WordAt)

@[expose] public section

/-- At the entry and the returns (`b0`, `b4`, `b5`): region 0 the return address. -/
abbrev retS : SState := frameS 0
/-- At `b1`: region 0 the count word, RDI its address. -/
def countS : SState := init [8] [(.rdi, .ptr 0 0)]
/-- Registers only (`b2`). -/
def regsS : SState := init []
/-- A turn of the loop (`b3`): region 0 the entry written (at RDI + 8 RCX), 1 the count word (at
RDI), 2 the element read (at RSI). -/
def bodyS : SState := init [8, 8, 8] [(.rsi, .ptr 2 0)] [] []
  [(.bin .add .W64 (.reg .rdi) (.bin .mul .W64 (.reg .rcx) (.lit 8)), 0, 0), (.reg .rdi, 1, 0)]

/-- `b0`'s branch: `xs` empty. -/
def c0 : SBool := .cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0)
/-- `b2`'s branch: the buffer full. -/
def c2 : SBool := .cmp .eq .W64 (.bin .add .W64 (.reg .r8) (.reg .rcx)) (.lit 1)
/-- `b3`'s branch: elements remain. -/
def c3 : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.lit (2 ^ 64 - 8)) (.reg .rdx)) (.lit 0))

/-- `movb $1, %al`. -/
def al1 : Sym := .bin .merge .W8 (.reg .rax) (.lit 1)
/-- `b1`'s R8: minus the larger of the count and `N`. -/
def r8Sym (N : Nat) : Sym :=
  .un .neg .W64 (.ite (.not (.cmp .ult .W64 (.load 0 0 8) (.lit (N + 1)))) (.load 0 0 8) (.lit N))

/-- The registers the loop head keeps. -/
def loopRegs : List Reg64 := [.rax, .rcx, .rdx, .rsi, .rdi, .r8] ++ Arrays.calleeRegs
/-- The registers a turn keeps. -/
def bodyRegs : List Reg64 := [.rax, .rdi, .r8, .rsp] ++ Arrays.calleeRegs

/-- What the executor's runs of an instance's blocks give. -/
structure Runs [Host] (N : Nat) (b0 b1 b2 b3 b4 b5 : List Directive)
    (k k1 k2 k3 k4 k5 : Nat) (l2 l3 l5 : Label) (S0 S1 S2 S3 S4 S5 : SState) : Prop where
  hb0 : b0.IsInfixAt Host.prog k
  hb1 : b1.IsInfixAt Host.prog k1
  hb2 : b2.IsInfixAt Host.prog k2
  hb3 : b3.IsInfixAt Host.prog k3
  hb4 : b4.IsInfixAt Host.prog k4
  hb5 : b5.IsInfixAt Host.prog k5
  e1 : k + b0.length = k1
  e2 : k1 + b1.length = k2
  e3 : k2 + b2.length = k3
  e4 : k3 + b3.length = k4
  hl2 : Labels.label l2 = Host.addrOf k2
  hl3 : Labels.label l3 = Host.addrOf k5
  hl5 : Labels.label l5 = Host.addrOf k4
  x0 : exec b0 retS = some (S0, .cond c0 l5)
  x1 : exec b1 countS = some (S1, .fall)
  x2 : exec b2 regsS = some (S2, .cond c2 l3)
  x3 : exec b3 bodyS = some (S3, .cond c3 l2)
  x4 : exec b4 retS = some (S4, .ret (.load 0 0 8))
  x5 : exec b5 retS = some (S5, .ret (.load 0 0 8))
  f0 : keepsAll retS S0 (.rdx :: .rsi :: .rdi :: Arrays.calleeRegs) = true ∧
    S0.reg .rax = some al1
  f1 : S1.reg .rax = some (.reg .rax) ∧
    S1.reg .rdx = some (.bin .shl .W64 (.reg .rdx) (.lit 3)) ∧
    S1.reg .r8 = some (r8Sym N) ∧ S1.reg .rcx = some (.bin .add .W64 (.load 0 0 8) (.lit 1)) ∧
    S1.reg .rsi = some (.reg .rsi) ∧ S1.reg .rdi = some (.ptr 0 0) ∧
    keepsAll countS S1 (.rsp :: Arrays.calleeRegs) = true
  f2 : keepsAll regsS S2 loopRegs = true
  f3 : S3.reg .rcx = some (.bin .add .W64 (.reg .rcx) (.lit 1)) ∧
    S3.reg .rdx = some (.bin .add .W64 (.lit (2 ^ 64 - 8)) (.reg .rdx)) ∧
    S3.reg .rsi = some (.ptr 2 8) ∧
    keepsRegs bodyS S3 bodyRegs = true ∧
    (∀ w ∈ S3.mem, (w.r = 0 ∧ w.off + w.n ≤ 8) ∨ (w.r = 1 ∧ w.off + w.n ≤ 8)) ∧
    (∀ i < 8, findWrite 0 (0 + i) S3.mem = some (.load 2 0 8, i)) ∧
    (∀ i < 8, findWrite 1 (0 + i) S3.mem = some (.reg .rcx, i))
  f4 : S4.reg .rax = some (.reg .rax) ∧ S4.reg .rsp = some (.ptr 0 ((0 + 8 : Nat) : Int)) ∧
    S4.mem = [] ∧ keepsRegs retS S4 Arrays.calleeRegs = true
  f5 : S5.reg .rax = some (.lit 0) ∧ S5.reg .rsp = some (.ptr 0 ((0 + 8 : Nat) : Int)) ∧
    S5.mem = [] ∧ keepsRegs retS S5 Arrays.calleeRegs = true

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
abbrev ws (m : MachineData) : List UInt64 := wordsOf m.dmem (src m) (len m)

/-- What every state of the function keeps: RSP, the callee-saved registers, memory but the
buffer, every mapped byte. -/
structure Frame (N : Nat) (m0 s : MachineData) : Prop where
  rsp : rspOf s = rspOf m0
  regs : ∀ r, calleeSaved r = true → reg s r = reg m0 r
  kept : Kept m0.dmem s.dmem
  same : Changes m0 s bufU64ExtendStack (buf m0) (8 + 8 * N)

/-- **The loop head**, `j` elements copied. -/
structure Inv (N : Nat) (m0 : MachineData) (j : Nat) (s : MachineData) : Prop where
  frame : Frame N m0 s
  lt : j < len m0
  le : cnt m0 + j ≤ N
  al : boolRet s = 1
  rdi : reg s .rdi = buf m0
  rsi : reg s .rsi = src m0 + BitVec.ofNat 64 (8 * j)
  rdx : reg s .rdx = BitVec.ofNat 64 (8 * (len m0 - j))
  rcx : reg s .rcx = BitVec.ofNat 64 (cnt m0 + j + 1)
  r8 : reg s .r8 = -BitVec.ofNat 64 N
  count : WordAt s.dmem (buf m0) (cnt m0 + j).toUInt64
  ents : WordsAt s.dmem (buf m0 + 8#64) (bufWordsOf m0.dmem (buf m0) ++ (ws m0).take j)

/-- The postcondition, reached. -/
abbrev Post (N : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ BufU64ExtendPost N m0 s.data

/-- The buffer at the entry. -/
theorem bufWordsAt_entry {N : Nat} {m0 : MachineData} (hc : cnt m0 ≤ N)
    (hm : Mapped m0.dmem (buf m0) (8 + 8 * N)) :
    BufWordsAt m0.dmem (buf m0) N (bufWordsOf m0.dmem (buf m0)) := by
  refine ⟨by simp [bufWordsOf]; exact hc, ?_, ?_⟩
  · simp only [bufWordsOf, NativeRustcVm.length_wordsOf, Nat.toUInt64_eq, UInt64.ofNat_toNat]
    exact NativeRustcVm.wordAt_of_mapped fun i hi ↦ hm i (by omega)
  · refine NativeRustcVm.wordsAt_of_mapped fun i hi ↦ ?_
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add]
    have hc' : (wordOf m0.dmem (buf m0)).toNat ≤ N := hc
    exact hm _ (by omega)

/-- The word view of `wordsAt` kept where memory is unchanged. -/
theorem wordsAt_congr {d d' : DataMem} {a : BitVec 64} {xs : List UInt64} (h : WordsAt d a xs)
    (he : ∀ j < 8 * xs.length, d'.get? (a + BitVec.ofNat 64 j) = d.get? (a + BitVec.ofNat 64 j)) :
    WordsAt d' a xs := fun j hj ↦ by
  have : (xs.flatMap NativeRustcVm.wordBytes).length = 8 * xs.length := by
    rw [List.length_flatMap]; simp [NativeRustcVm.length_wordBytes, Nat.mul_comm]
  rw [he j (by omega)]; exact h j hj

/-- The return address is not in the buffer. -/
theorem ret_same {N : Nat} {m0 s : MachineData} (hpre : BufU64ExtendPre N m0)
    (hc : Changes m0 s bufU64ExtendStack (buf m0) (8 + 8 * N)) :
    ∀ j < 8, s.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) := by
  intro j hj
  refine hc _ fun h ↦ h.elim (ret_not_in hpre.1 hpre.2.2.1.2 hpre.2.2.2.2.2 j hj) fun h ↦ ?_
  unfold InRange at h
  exact absurd h (by simp [bufU64ExtendStack])

variable [Host] {N : Nat}

/-- **A return** (`b4`, `b5`) from the frame: back at the return address with RAX the block's
`v`, memory as in the frame, the callee-saved registers the entry's. -/
theorem finish {bb : List Directive} {kb : Nat} {S : SState} {v : Sym}
    (hk : bb.IsInfixAt Host.prog kb) (hx : exec bb retS = some (S, .ret (.load 0 0 8)))
    (hf : S.reg .rax = some v ∧ S.reg .rsp = some (.ptr 0 ((0 + 8 : Nat) : Int)) ∧ S.mem = [] ∧
      keepsRegs retS S Arrays.calleeRegs = true)
    {m0 : MachineData} (hpre : BufU64ExtendPre N m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf kb) (hF : Frame N m0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = retOf m0 ∧ rspOf s'.data = rspOf m0 + 8#64 ∧
      reg s'.data .rax = v.eval (frameEnv m0 s.data 0) ∧ s'.data.dmem = s.data.dmem ∧
      Saved m0 s'.data) s := by
  obtain ⟨hax, hsp, hmem, hkeep⟩ := hf
  have hS : StackOk m0 0 := hpre.1
  have hwf := frame_wf (m := s.data) (vars := fun _ ↦ 0) (ret := 0) hS hF.kept
  have hm : Match (frameEnv m0 s.data 0) retS s.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show rspOf s.data = stackBelow m0 0 + BitVec.ofInt 64 ((0 : Nat) : Int) by
        rw [hF.rsp]; unfold stackBelow; simp, trivial⟩ trivial trivial trivial
  refine exec_at hk hx hwf (by intro l h; cases h) hpc hm fun s' hm' hpc' ↦ .done _ ?_
  have hdm : s'.data.dmem = s.data.dmem := hm'.dmem_eq hwf hmem
  refine ⟨?_, ?_, hm'.regs .rax _ hax, hdm, fun r hr ↦ ?_, fun p h ↦ hm'.kept hwf p (hF.kept p h)⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    exact load_ret hS (ret_same hpre hF.same)
  · show s'.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ hsp]
    exact frame_rsp 0 8
  · exact (regs_eq_of hm hm' hkeep r (mem_calleeRegs hr)).trans (hF.regs r hr)

variable {b0 b1 b2 b3 b4 b5 : List Directive} {k k1 k2 k3 k4 k5 : Nat} {l2 l3 l5 : Label}
  {S0 S1 S2 S3 S4 S5 : SState}

/-- **A turn of the loop**: the buffer full and `None` returned, or element `j` copied, then back
at the head or `Some` returned. -/
theorem step (R : Runs N b0 b1 b2 b3 b4 b5 k k1 k2 k3 k4 k5 l2 l3 l5 S0 S1 S2 S3 S4 S5)
    {m0 : MachineData} (hpre : BufU64ExtendPre N m0) {j : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf k2) (hI : Inv N m0 j s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post N m0 s' ∨
      (s'.pc = Host.addrOf k2 ∧ Inv N m0 (j + 1) s'.data)) s := by
  have hpre' := hpre
  obtain ⟨hS, hc, ⟨hmB, hnB⟩, ⟨hmS, hnS⟩, hap, hoB⟩ := hpre
  have hnB' : (buf m0).toNat + (8 + 8 * N) ≤ 2 ^ 64 := hnB
  have hnS' : (src m0).toNat + 8 * len m0 ≤ 2 ^ 64 := hnS
  have hlt := hI.lt
  have hle := hI.le
  have hL : len m0 = (reg m0 .rdx).toNat := rfl
  have hC : cnt m0 = (wordOf m0.dmem (buf m0)).toNat := rfl
  have hC2 : cnt m0 = (wordOf m0.dmem (reg m0 .rdi)).toNat := rfl
  have eB : (buf m0).toNat = (reg m0 .rdi).toNat := rfl
  have eS : (src m0).toNat = (reg m0 .rsi).toNat := rfl
  have hN : 8 * N ≤ 2 ^ 64 := by omega
  -- `b2`: full?
  refine exec_at R.hb2 R.x2 (Env.wf_nil _) (by intro l h; cases h) hpc (match_nil _)
    fun s2 hm2 hpc2 ↦ ?_
  have hk2 := R.f2
  unfold keepsAll at hk2
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk2
  obtain ⟨hr2, hmem2⟩ := hk2
  have e2 := regs_eq_of (match_nil _) hm2 hr2
  have hdm2 : s2.data.dmem = s.data.dmem := hm2.dmem_eq (Env.wf_nil _) hmem2
  have hF2 : Frame N m0 s2.data :=
    ⟨by show reg s2.data .rsp = _; rw [e2 .rsp (by simp)]; exact hI.frame.rsp,
      fun r hr ↦ (e2 r (List.mem_cons_of_mem _ (List.mem_append_right _ (mem_calleeRegs hr)))).trans
        (hI.frame.regs r hr),
      by rw [hdm2]; exact hI.frame.kept, fun p hp ↦ by rw [hdm2]; exact hI.frame.same p hp⟩
  have r2 : ∀ r ∈ [Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8], reg s2.data r = reg s.data r :=
    fun r h ↦ e2 r (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  simp only [PcOk, c2, R.e3] at hpc2
  rw [eval_cmp_eq, eval_add, eval_reg, eval_reg, eval_lit] at hpc2
  rw [show (Env.ofMachine s.data []).regs .r8 = reg s.data .r8 from rfl,
    show (Env.ofMachine s.data []).regs .rcx = reg s.data .rcx from rfl, hI.r8, hI.rcx,
    neg_add_beq_one (by omega) (by omega)] at hpc2
  obtain ⟨hT, hFl⟩ := pc_cond hpc2
  by_cases hfull : cnt m0 + j = N
  · -- the buffer full: `None`.
    have hpc5 := (hT (decide_eq_true (by omega))).trans R.hl3
    refine Eventually.mono (finish R.hb5 R.x5 R.f5 hpre' hpc5 hF2)
      fun s' ⟨h1, h2, h3, h4, h5⟩ ↦ Or.inl ⟨h1, h2, ?_,
        fun p hp ↦ by rw [h4]; exact hF2.same p hp, h5⟩
    split
    · rename_i hn; exfalso; omega
    show (reg s'.data .rax).toNat % 256 = 0
    rw [h3]; rfl
  have hpc3 := hFl fun h ↦ hfull (by have := of_decide_eq_true h; omega)
  -- the turn: three regions
  have hcj : cnt m0 + j < N := by omega
  obtain ⟨dst, hdst⟩ : ∃ d : BitVec 64, d = buf m0 + BitVec.ofNat 64 (8 + 8 * (cnt m0 + j)) :=
    ⟨_, rfl⟩
  obtain ⟨sj, hsj⟩ : ∃ d : BitVec 64, d = src m0 + BitVec.ofNat 64 (8 * j) := ⟨_, rfl⟩
  have hkept : Kept m0.dmem s2.data.dmem := hF2.kept
  have hnD : NoWrap dst 8 := by
    unfold NoWrap; rw [hdst, toNat_add_ofNat _ _ (by omega)]; omega
  have hnC : NoWrap (buf m0) 8 := by unfold NoWrap; omega
  have hnJ : NoWrap sj 8 := by
    unfold NoWrap; rw [hsj, toNat_add_ofNat _ _ (by omega)]; omega
  have hmD : Mapped s2.data.dmem dst 8 := fun i hi ↦ by
    rw [hdst, addr_add]; exact hkept _ (hmB _ (by omega))
  have hmC : Mapped s2.data.dmem (buf m0) 8 := fun i hi ↦ hkept _ (hmB _ (by omega))
  have hmJ : Mapped s2.data.dmem sj 8 := fun i hi ↦ by
    rw [hsj, addr_add]; exact hkept _ (hmS _ (by omega))
  have hdD : dst.toNat = (buf m0).toNat + (8 + 8 * (cnt m0 + j)) := by
    rw [hdst]; exact toNat_add_ofNat _ _ (by omega)
  have hdJ : sj.toNat = (src m0).toNat + 8 * j := by
    rw [hsj]; exact toNat_add_ofNat _ _ (by omega)
  have hap' : (buf m0).toNat + (8 + 8 * N) ≤ (src m0).toNat ∨
      (src m0).toNat + 8 * len m0 ≤ (buf m0).toNat := hap
  have hwf : (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]).WF := by
    refine Env.wf_of ⟨⟨hmD, hnD⟩, ⟨hmC, hnC⟩, ⟨hmJ, hnJ⟩, trivial⟩ ?_
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons nofun .nil))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · show Apart dst 8 (buf m0) 8
        unfold Apart; omega
      · show Apart dst 8 sj 8
        unfold Apart; omega
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      show Apart (buf m0) 8 sj 8
      unfold Apart; omega
  have hm3 : Match (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]) bodyS s2.data := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨?_, trivial⟩ trivial trivial ⟨?_, ?_, trivial⟩
    · show reg s2.data .rsi = sj + BitVec.ofInt 64 0
      rw [r2 .rsi (by simp), hI.rsi, hsj]; simp
    · show reg s2.data .rdi + BinOp.apply .mul .W64 (reg s2.data .rcx) (BitVec.ofNat 64 8) =
        dst + BitVec.ofInt 64 0
      rw [r2 .rdi (by simp), r2 .rcx (by simp), hI.rdi, hI.rcx, hdst]
      simp only [BinOp.apply, low_W64, ext_W64, show BitVec.ofInt 64 0 = 0#64 from rfl,
        BitVec.add_zero]
      rw [← BitVec.ofNat_mul]
      exact congrArg _ (congrArg _ (by omega))
    · show reg s2.data .rdi = buf m0 + BitVec.ofInt 64 0
      rw [r2 .rdi (by simp), hI.rdi]; simp
  refine exec_at R.hb3 R.x3 hwf (by intro l h; cases h) hpc3 hm3 fun s3 hm3' hpc3' ↦ ?_
  obtain ⟨gcx, gdx, gsi, gk, gw, gw0, gw1⟩ := R.f3
  have e3 := regs_eq_of hm3 hm3' gk
  have hsame3 := same01 hm3' hwf le_rfl le_rfl gw
  -- the element read, unchanged since the entry
  have hJ : (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]).load 2 0 8 =
      ((ws m0)[j]'(by simp; exact hlt)).toBitVec := by
    rw [load8_eq, NativeRustcVm.getElem_wordsOf]
    show (wordOf s2.data.dmem (sj + BitVec.ofNat 64 0)).toBitVec = _
    rw [add_ofNat_zero, hsj]
    refine congrArg _ (NativeRustcVm.wordOf_congr fun i hi ↦ ?_)
    rw [addr_add]
    refine hF2.same _ fun h ↦ h.elim (fun h ↦ ?_) (fun h ↦ ?_)
    · rw [Sym.inRange_iff hnB, toNat_add_ofNat _ _ (by omega)] at h; omega
    · unfold InRange at h; simp [bufU64ExtendStack] at h
  -- the entry written
  have hD : WordAt s3.data.dmem dst ((ws m0)[j]'(by simp; exact hlt)) := by
    have a := wordAt_of_write hm3' (r := 0) (o := 0) rfl (by decide) gw0
    rw [eval_load, hJ, add_ofNat_zero, UInt64.ofBitVec_toBitVec] at a
    exact a
  -- the count written
  have hCw : WordAt s3.data.dmem (buf m0) (cnt m0 + j + 1).toUInt64 := by
    have a := wordAt_of_write hm3' (r := 1) (o := 0) rfl (by decide) gw1
    rw [add_ofNat_zero, eval_reg] at a
    rw [show (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]).regs .rcx =
      reg s2.data .rcx from rfl, r2 .rcx (by simp), hI.rcx] at a
    exact a
  have hlen0 : (bufWordsOf m0.dmem (buf m0) ++ (ws m0).take j).length = cnt m0 + j := by
    simp [bufWordsOf]; omega
  have hE : WordsAt s3.data.dmem (buf m0 + 8#64)
      (bufWordsOf m0.dmem (buf m0) ++ (ws m0).take (j + 1)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp; exact hlt), Option.toList_some,
      ← List.append_assoc, NativeRustcVm.wordsAt_append, NativeRustcVm.wordsAt_singleton, hlen0]
    constructor
    · refine wordsAt_congr (hdm2 ▸ hI.ents) fun i hi ↦ ?_
      rw [hlen0] at hi
      rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add]
      refine hsame3 _ ?_ ?_
      · rw [Sym.inRange_iff hnD, hdD, toNat_add_ofNat _ _ (by omega)]; omega
      · rw [Sym.inRange_iff hnC, toNat_add_ofNat _ _ (by omega)]; omega
    · rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add, ← hdst]
      exact hD
  have hsameT : Changes m0 s3.data bufU64ExtendStack (buf m0) (8 + 8 * N) := fun p hp ↦ by
    have hp' : ¬InRange (buf m0) (8 + 8 * N) p := fun h ↦ hp (Or.inl h)
    rw [hsame3 p (fun h ↦ hp' ?_) (fun h ↦ hp' ?_)]
    · exact hF2.same p hp
    · rw [Sym.inRange_iff hnD, hdD] at h; rw [Sym.inRange_iff hnB]; omega
    · rw [Sym.inRange_iff hnC] at h; rw [Sym.inRange_iff hnB]; omega
  have hF3 : Frame N m0 s3.data :=
    ⟨by show reg s3.data .rsp = _; rw [e3 .rsp (by simp [bodyRegs])]; exact hF2.rsp,
      fun r hr ↦ (e3 r (List.mem_append_right _ (mem_calleeRegs hr))).trans (hF2.regs r hr),
      fun p h ↦ hm3'.kept hwf p (hkept p h), hsameT⟩
  have r3 : ∀ r ∈ [Reg64.rax, .rdi, .r8], reg s3.data r = reg s.data r := by
    intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact (e3 _ (by simp [bodyRegs])).trans (r2 _ (by simp))
  have hcx : reg s3.data .rcx = BitVec.ofNat 64 (cnt m0 + (j + 1) + 1) := by
    rw [show reg s3.data .rcx = (Sym.bin .add .W64 (.reg .rcx) (.lit 1)).eval
      (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]) from hm3'.regs .rcx _ gcx,
      eval_add, eval_reg, eval_lit]
    show reg s2.data .rcx + _ = _
    rw [r2 .rcx (by simp), hI.rcx, ← BitVec.ofNat_add]
    exact congrArg _ (by omega)
  have hdx : reg s3.data .rdx = BitVec.ofNat 64 (8 * (len m0 - (j + 1))) := by
    rw [show reg s3.data .rdx = (Sym.bin .add .W64 (.lit (2 ^ 64 - 8)) (.reg .rdx)).eval
      (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]) from hm3'.regs .rdx _ gdx,
      eval_add, eval_reg, eval_lit]
    show _ + reg s2.data .rdx = _
    rw [r2 .rdx (by simp), hI.rdx]
    have hlj : 8 * (len m0 - j) < 2 ^ 64 := by omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, toNat_ofNat_lt hlj, toNat_ofNat_lt (by decide),
      toNat_ofNat_lt (by omega)]
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    rw [h64] at hnS' ⊢
    omega
  have hsi : reg s3.data .rsi = src m0 + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [show reg s3.data .rsi = (Sym.ptr 2 8).eval
      (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]) from hm3'.regs .rsi _ gsi]
    show sj + BitVec.ofInt 64 8 = _
    rw [hsj, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add]
    exact congrArg _ (congrArg _ (by omega))
  -- the loop test
  simp only [PcOk, c3, R.e4] at hpc3'
  rw [eval_not, eval_cmp_eq, eval_add, eval_reg, eval_lit, eval_lit] at hpc3'
  rw [show (Env.ofMachine s2.data [(dst, 8), (buf m0, 8), (sj, 8)]).regs .rdx =
      reg s2.data .rdx from rfl, r2 .rdx (by simp), hI.rdx,
    sub8_beq_zero (by omega)] at hpc3'
  obtain ⟨hT3, hF3'⟩ := pc_cond hpc3'
  have hal3 : boolRet s3.data = 1 := by
    unfold boolRet; rw [r3 .rax (by simp)]; exact hI.al
  by_cases hM : j + 1 < len m0
  · have hpc4 := (hT3 (by simp; omega)).trans R.hl2
    refine .done _ (Or.inr ⟨hpc4, hF3, hM, by omega, hal3, (r3 .rdi (by simp)).trans hI.rdi,
      hsi, hdx, hcx, (r3 .r8 (by simp)).trans hI.r8, ?_, hE⟩)
    rw [show cnt m0 + (j + 1) = cnt m0 + j + 1 by omega]; exact hCw
  · have hpc4 := hF3' (by simp; omega)
    refine Eventually.mono (finish R.hb4 R.x4 R.f4 hpre' hpc4 hF3)
      fun s' ⟨h1, h2, h3, h4, h5⟩ ↦ Or.inl ⟨h1, h2, ?_, fun p hp ↦ by rw [h4]; exact hsameT p hp,
        h5⟩
    have hj : j + 1 = len m0 := by omega
    split
    rotate_left
    · rename_i hn; exfalso; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (reg s'.data .rax).toNat % 256 = 1
      rw [h3, eval_reg]
      exact hal3
    · simp [bufWordsOf]; omega
    · rw [h4]
      have : (bufWordsOf m0.dmem (buf m0) ++ ws m0).length = cnt m0 + j + 1 := by
        simp [bufWordsOf]; omega
      rw [this]; exact hCw
    · rw [h4]
      have hE' := hE
      rw [List.take_of_length_le (l := ws m0) (i := j + 1) (by simp; omega)] at hE'
      exact hE'

/-- **`Buf<u64, N>::extend` meets its contract**, from an instance's runs. -/
theorem spec_of (R : Runs N b0 b1 b2 b3 b4 b5 k k1 k2 k3 k4 k5 l2 l3 l5 S0 S1 S2 S3 S4 S5)
    {l0 : Label} (hl0 : Labels.label l0 = Host.addrOf k) :
    Spec (Labels.label l0) (BufU64ExtendPre N) (BufU64ExtendPost N) := by
  intro m0 hpre
  rw [hl0]
  have hpre' := hpre
  obtain ⟨hS, hc, ⟨hmB, hnB⟩, ⟨hmS, hnS⟩, hap, hoB⟩ := hpre
  have hS0 : StackOk m0 0 := hS
  have hnB' : (buf m0).toNat + (8 + 8 * N) ≤ 2 ^ 64 := hnB
  have hL : len m0 = (reg m0 .rdx).toNat := rfl
  have hC : cnt m0 = (wordOf m0.dmem (buf m0)).toNat := rfl
  have hC2 : cnt m0 = (wordOf m0.dmem (reg m0 .rdi)).toNat := rfl
  have eB : (buf m0).toNat = (reg m0 .rdi).toNat := rfl
  have hc' : cnt m0 ≤ N := hc
  have hnS' : (reg m0 .rsi).toNat + 8 * len m0 ≤ 2 ^ 64 := hnS
  have hap' : (buf m0).toNat + (8 + 8 * N) ≤ (reg m0 .rsi).toNat ∨
      (reg m0 .rsi).toNat + 8 * len m0 ≤ (buf m0).toNat := hap
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) hS0 fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 0) retS m0 := match_frame
  refine exec_then R.hb0 R.x0 hwf (by intro l h; cases h) hm fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hk0, hax0⟩ := R.f0
  simp only [PcOk, c0, R.e1] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs, beq_ofNat _ (by decide)] at hpc1
  obtain ⟨hT, hFl⟩ := pc_cond hpc1
  have hal : boolRet s1.data = 1 := by
    show (s1.data.regs.get64 .rax).toNat % 256 = 1
    rw [hm1.regs .rax _ hax0]
    exact merge_one_mod _
  have hk0' := hk0
  unfold keepsAll at hk0'
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk0'
  obtain ⟨hr0, hmem0⟩ := hk0'
  have e1 := regs_eq_of hm hm1 hr0
  have hdm1 : s1.data.dmem = m0.dmem := hm1.dmem_eq hwf hmem0
  have hF1 : Frame N m0 s1.data :=
    ⟨by show reg s1.data .rsp = _; exact e1 .rsp (by simp),
      fun r hr ↦ e1 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (mem_calleeRegs hr))))),
      by rw [hdm1]; exact fun _ h ↦ h, fun p _ ↦ by rw [hdm1]⟩
  by_cases hz : len m0 = 0
  · -- `xs` empty: `Some`.
    have hpc4 := (hT (decide_eq_true hz)).trans R.hl5
    refine Eventually.mono (finish R.hb4 R.x4 R.f4 hpre' hpc4 hF1)
      fun s' ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_, fun p _ ↦ by rw [h4, hdm1], h5⟩
    split
    rotate_left
    · rename_i hn; exfalso; omega
    refine ⟨?_, ?_⟩
    · show (reg s'.data .rax).toNat % 256 = 1
      rw [h3, eval_reg]
      exact hal
    · rw [h4, hdm1, show wordsOf m0.dmem (reg m0 .rsi) (reg m0 .rdx).toNat = [] from
        List.eq_nil_of_length_eq_zero (by simp; exact hz), List.append_nil]
      exact bufWordsAt_entry hc hmB
  have hpc1 := hFl fun h ↦ hz (of_decide_eq_true h)
  -- `b1`: the count, the loop's registers
  have hwf1 : (Env.ofMachine s1.data [(buf m0, 8)]).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ by
      show (s1.data.dmem.get? (buf m0 + BitVec.ofNat 64 i)).isSome
      rw [hdm1]; exact hmB i (by have : i < 8 := hi; omega), by
      show (buf m0).toNat + 8 ≤ 2 ^ 64; omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm1' : Match (Env.ofMachine s1.data [(buf m0, 8)]) countS s1.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show reg s1.data .rdi = buf m0 + BitVec.ofInt 64 0 by rw [e1 .rdi (by simp)]; simp,
        trivial⟩ trivial trivial trivial
  refine exec_at R.hb1 R.x1 hwf1 (by intro l h; cases h) hpc1 hm1' fun s2 hm2 hpc2 ↦ ?_
  simp only [PcOk, R.e2] at hpc2
  obtain ⟨g0, gdx, g8, gcx, gsi, gdi, gk⟩ := R.f1
  have gk' := gk
  unfold keepsAll at gk'
  simp only [Bool.and_eq_true, List.isEmpty_iff] at gk'
  obtain ⟨gr, gmem⟩ := gk'
  have e2 := regs_eq_of hm1' hm2 gr
  have hdm2 : s2.data.dmem = m0.dmem := (hm2.dmem_eq hwf1 gmem).trans hdm1
  have hload : (Env.ofMachine s1.data [(buf m0, 8)]).load 0 0 8 =
      (wordOf m0.dmem (buf m0)).toBitVec := by
    rw [load8_eq]
    show (wordOf s1.data.dmem (buf m0 + BitVec.ofNat 64 0)).toBitVec = _
    rw [hdm1, add_ofNat_zero]
  have hcN : (wordOf m0.dmem (buf m0)).toNat < 2 ^ 61 := by omega
  have hI : Inv N m0 0 s2.data := by
    refine ⟨⟨?_, fun r hr ↦ ?_, by rw [hdm2]; exact fun _ h ↦ h, fun p _ ↦ by rw [hdm2]⟩,
      Nat.pos_of_ne_zero hz, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show reg s2.data .rsp = _
      rw [e2 .rsp (by simp)]; exact hF1.rsp
    · exact (e2 r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_calleeRegs hr)))).trans
        (hF1.regs r hr)
    · show (s2.data.regs.get64 .rax).toNat % 256 = 1
      rw [hm2.regs .rax _ g0, eval_reg]
      exact hal
    · show s2.data.regs.get64 .rdi = _
      rw [hm2.regs .rdi _ gdi]; show buf m0 + BitVec.ofInt 64 0 = _; simp
    · show s2.data.regs.get64 .rsi = _
      rw [hm2.regs .rsi _ gsi, eval_reg]
      show reg s1.data .rsi = _
      rw [e1 .rsi (by simp)]; simp
    · show s2.data.regs.get64 .rdx = _
      rw [hm2.regs .rdx _ gdx, eval_shl_lit _ (by decide), eval_reg]
      show reg s1.data .rdx <<< 3 = _
      rw [e1 .rdx (by simp)]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    · show s2.data.regs.get64 .rcx = _
      rw [hm2.regs .rcx _ gcx, eval_add, eval_load, eval_lit, hload]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
    · show s2.data.regs.get64 .r8 = _
      rw [hm2.regs .r8 _ g8]
      simp only [r8Sym, Sym.eval, SBool.eval, CmpOp.apply, UnOp.apply, low_W64, ext_W64, hload]
      have hult : (wordOf m0.dmem (buf m0)).toBitVec.ult (BitVec.ofNat 64 (N + 1)) = true := by
        rw [BitVec.ult_iff_lt, BitVec.lt_def, UInt64.toNat_toBitVec, toNat_ofNat_lt (by omega)]
        omega
      simp [hult]
    · rw [Nat.add_zero, Nat.toUInt64_eq, UInt64.ofNat_toNat, hdm2]
      exact NativeRustcVm.wordAt_of_mapped fun i hi ↦ hmB i (by omega)
    · rw [List.take_zero, List.append_nil, hdm2]
      exact (bufWordsAt_entry hc hmB).2.2
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf k2 ∧ ∃ j, len m0 - j = n ∧ Inv N m0 j s.data)
    (fun n s ⟨hpc, j, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
  refine Eventually.mono (step R hpre' hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨len m0 - (j + 1), by have := hI'.lt; omega, hpc', j + 1, rfl, hI'⟩

end

end NativeRustcVmX64.Arrays.BufU64
