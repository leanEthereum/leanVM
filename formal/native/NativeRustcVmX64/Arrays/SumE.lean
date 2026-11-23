module

public import NativeRustcVmX64.Arrays.SumE.Exec
public import NativeRustcVm.Arrays.Folds
public import NativeRustcVmX64.Code.Vm.SumE.Names

/-!
# `sum_e` on x86-64

**`sumE_spec`**: rustc's `sum_e(values)`, placed anywhere in the program, meets
`SumEPre`/`SumEPost`. No stack, no memory written, no callee-saved register touched (`Base`).
`E` addition is the lanes' `xor`. At `len = 0` it returns `0` (`b3`); below `4` the tail loop
(`b7`, `b8`: `TInv`) adds every value; from `4` on (`len ≤ 16`) the unrolled loop (`b4`, `b5`:
`UInv`) adds four values a turn for the `len & 28 = 4·⌊len/4⌋` first values, and the tail loop
(`b6`, `b7`, `b8`) the `len & 3` others; `b9` returns.
-/

namespace NativeRustcVmX64.Arrays.SumE

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumE NativeVm.Model
  NativeRustcVmX64.Field
open NativeRustcVm (ewsOf ewOf)

public section

/-- The values' address. -/
abbrev addr (m : MachineData) : BitVec 64 := reg m .rdi
/-- Their number. -/
abbrev len (m : MachineData) : Nat := (reg m .rsi).toNat
/-- The values at the entry. -/
abbrev xs (m : MachineData) : List EW := ewsOf m.dmem (addr m) (len m)

/-- The sum of the first `i` values. -/
def acc (m : MachineData) (i : Nat) : EW := ((xs m).take i).foldl (· + ·) 0

theorem sumE_eq_acc (m : MachineData) :
    sumE (slice m (reg m .rdi) (reg m .rsi)) = acc m (len m) := by
  unfold slice acc
  rw [NativeRustcVm.sumE_eq, List.take_of_length_le (by simp)]

theorem lt_len {m : MachineData} {i : Nat} (h : i < len m) : i < (xs m).length := by
  simp only [xs, len, NativeRustcVm.length_ewsOf] at h ⊢; exact h

theorem acc_succ (m : MachineData) {i : Nat} (h : i < len m) :
    acc m (i + 1) = acc m i + (xs m)[i]'(lt_len h) :=
  NativeRustcVm.foldl_take_succ _ _ _ _

theorem acc4 (m0 : MachineData) (t : Nat) (h : 4 * t + 4 ≤ len m0) :
    acc m0 (4 * t + 4) = acc m0 (4 * t) + (xs m0)[4 * t]'(lt_len (by omega)) +
      (xs m0)[4 * t + 1]'(lt_len (by omega)) + (xs m0)[4 * t + 1 + 1]'(lt_len (by omega)) +
      (xs m0)[4 * t + 1 + 1 + 1]'(lt_len (by omega)) := by
  rw [show 4 * t + 4 = 4 * t + 1 + 1 + 1 + 1 by omega, acc_succ m0 (by omega),
    acc_succ m0 (by omega), acc_succ m0 (by omega), acc_succ m0 (by omega)]

/-! ## Values -/

theorem ult_eval (x : BitVec 64) {c : Nat} (hc : c < 2 ^ 64) :
    CmpOp.apply .ult .W64 x (BitVec.ofNat 64 c) = decide (x.toNat < c) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [CmpOp.apply, low_W64]
  rw [BitVec.ult_iff_lt, BitVec.lt_def, toNat_ofNat_lt hc]

theorem trunc_eval32 (x : BitVec 64) (hx : x.toNat < 2 ^ 32) : UnOp.apply .trunc .W32 x = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [UnOp.apply, toNat_ext, toNat_low]
  rw [show Width.W32.bits = 32 from rfl, Nat.mod_eq_of_lt hx]

theorem and_eval32 (x : BitVec 64) {c : Nat} (hx : x.toNat < 2 ^ 32) (hc : c < 2 ^ 32) :
    BinOp.apply .and .W32 x (BitVec.ofNat 64 c) = BitVec.ofNat 64 (x.toNat &&& c) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : x.toNat &&& c ≤ x.toNat := Nat.and_le_left
  simp only [BinOp.apply, toNat_ext, BitVec.toNat_and, toNat_low, BitVec.toNat_ofNat]
  rw [show Width.W32.bits = 32 from rfl, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (show x.toNat &&& c < 2 ^ 64 by omega)]

theorem shl4_eval32 (x : BitVec 64) (hx : x.toNat < 2 ^ 28) :
    BinOp.apply .shl .W32 x (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * x.toNat) := by
  have hc : shiftCount .W32 (BitVec.ofNat 64 4) = 4 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, hc, toNat_ext, BitVec.toNat_shiftLeft, toNat_low, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  rw [show Width.W32.bits = 32 from rfl]
  omega

theorem shl4_ofNat (i : Nat) : BitVec.ofNat 64 i <<< 4 = BitVec.ofNat 64 (16 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem and3 : ∀ n, n ≤ 16 → n &&& 3 = n % 4 := by decide
theorem and28 : ∀ n, n ≤ 16 → n &&& 28 = 4 * (n / 4) := by decide

/-! ## The frame: nothing written, nothing saved changed -/

/-- What every block keeps: RSP, the callee-saved registers, memory. -/
structure Base (m0 s : MachineData) : Prop where
  rsp : rspOf s = rspOf m0
  regs : ∀ r, calleeSaved r = true → reg s r = reg m0 r
  dmem : s.dmem = m0.dmem

theorem Base.step [Labels] {m0 s s' : MachineData} {env : Env} {S₀ S₁ : SState}
    (hb : Base m0 s) (hm₀ : Match env S₀ s) (hm : Match env S₁ s') (hwf : env.WF)
    (hd : s.dmem = env.mem0) (hk : keepsAll S₀ S₁ calleeRegs = true) : Base m0 s' := by
  unfold keepsAll at hk
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk
  obtain ⟨hr, hmem⟩ := hk
  have he := regs_eq_of hm₀ hm hr
  refine ⟨?_, fun r hc ↦ (he r (List.mem_cons_of_mem _ (mem_calleeRegs hc))).trans (hb.regs r hc),
    (hm.dmem_eq hwf hmem).trans (hd.symm.trans hb.dmem)⟩
  show reg s' .rsp = _
  rw [he .rsp (by simp)]; exact hb.rsp

/-- A block of registers only from a base. -/
theorem Base.regs' [Labels] {m0 s s' : MachineData} {S₁ : SState} (hb : Base m0 s)
    (hm : Match (Env.ofMachine s []) S₁ s') (hk : keepsAll regsS S₁ calleeRegs = true) :
    Base m0 s' :=
  hb.step (match_nil _) hm (Env.wf_nil _) rfl hk

/-- Part of a readable region, in a state that kept its bytes. -/
theorem sub_readable {m0 s : MachineData} {a : BitVec 64} {n o c : Nat} (h : Readable m0 a n)
    (hk : Kept m0.dmem s.dmem) (hc : 0 < c) (hle : o + c ≤ n) :
    Readable s (a + BitVec.ofNat 64 o) c := by
  obtain ⟨hm, hn⟩ := h
  unfold NoWrap at hn
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [addr_add]; exact hk _ (hm _ (by omega))
  · show (a + BitVec.ofNat 64 o).toNat + c ≤ 2 ^ 64
    rw [toNat_add_ofNat _ _ (by omega)]; omega

/-- A value read from a one-region environment at `b`, `b + o` its address. -/
theorem elem_load {m0 s : MachineData} (hd : s.dmem = m0.dmem) {b : BitVec 64} {sz o i : Nat}
    (hb : b + BitVec.ofNat 64 o = addr m0 + BitVec.ofNat 64 (16 * i)) (hi : i < len m0) :
    ewArg ((Env.ofMachine s [(b, sz)]).load 0 o 8) ((Env.ofMachine s [(b, sz)]).load 0 (o + 8) 8) =
      (xs m0)[i]'(lt_len hi) := by
  rw [← ewOf_loads, NativeRustcVm.getElem_ewsOf]
  show ewOf s.dmem (b + BitVec.ofNat 64 o) = _
  rw [hd, hb]

variable [Host] {k : Nat}

theorem hb (hp : Placed code k) {b : List Directive} {j : Nat} (hj : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hj.trans hp.1 hne

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.SumE.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.SumE.b0Offset) :=
  hp.label NativeRustcVmX64.Vm.SumE.entry_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ SumEPost m0 s.data

/-- **A return** (`b3`, `b9`): RAX, RDX the sum. -/
theorem ret_of {b : List Directive} {kb : Nat} {S : SState} (hk : b.IsInfixAt Host.prog kb)
    (hx : exec b retS = some (S, .ret (.load 0 0 8))) {v0 v1 : Sym} (h0 : S.reg .rax = some v0)
    (h1 : S.reg .rdx = some v1)
    (hfacts : keepsRegs retS S calleeRegs = true ∧ S.reg .rsp = some (.ptr 0 8) ∧ S.mem = [])
    {m0 : MachineData} (hpre : SumEPre m0) {s : MachineState} (hpc : s.pc = Host.addrOf kb)
    (hB : Base m0 s.data)
    (hv : ewArg (v0.eval (frameEnv m0 s.data 0)) (v1.eval (frameEnv m0 s.data 0)) =
      acc m0 (len m0)) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hkeep, hsp, hmem⟩ := hfacts
  have hS : StackOk m0 0 := hpre.1
  have hwf := frame_wf (m := s.data) (vars := fun _ ↦ 0) (ret := 0) hS
    (fun p h ↦ by rw [hB.dmem]; exact h)
  have hrsp : rspOf s.data = stackBelow m0 0 + BitVec.ofInt 64 ((0 : Nat) : Int) := by
    rw [hB.rsp]; unfold stackBelow; simp
  have hm : Match (frameEnv m0 s.data 0) retS s.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hrsp, trivial⟩ trivial trivial trivial
  refine exec_at hk hx hwf (by intro l h; cases h) hpc hm fun s' hm' hpc' ↦ .done _ ?_
  have hdm : s'.data.dmem = s.data.dmem := hm'.dmem_eq hwf hmem
  refine ⟨?_, ?_, ?_, fun p _ ↦ by rw [hdm, hB.dmem], fun r hr ↦ ?_, fun p h ↦ ?_⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    exact load_ret hS fun j _ ↦ by rw [hB.dmem]
  · show s'.data.regs.get64 .rsp = _
    rw [hm'.regs .rsp _ hsp]
    exact frame_rsp 0 8
  · rw [sumE_eq_acc, ← hv]
    show ewArg (s'.data.regs.get64 .rax) (s'.data.regs.get64 .rdx) = _
    rw [hm'.regs .rax _ h0, hm'.regs .rdx _ h1]
  · exact (regs_eq_of hm hm' hkeep r (mem_calleeRegs hr)).trans (hB.regs r hr)
  · rw [hdm, hB.dmem]; exact h

/-! ## The tail loop -/

/-- **The tail loop's head** `NativeRustcVmX64.Vm.SumE.label_8`, from value `i0`, `j` more added. -/
structure TInv (m0 : MachineData) (i0 j : Nat) (s : MachineData) : Prop where
  base : Base m0 s
  lt : i0 + j < len m0
  rsi : reg s .rsi = addr m0 + BitVec.ofNat 64 (16 * i0) + BitVec.ofNat 64 8
  rdi : reg s .rdi = BitVec.ofNat 64 (16 * j)
  rcx : reg s .rcx = BitVec.ofNat 64 (16 * (len m0 - i0))
  acc : ewArg (reg s .rax) (reg s .rdx) = acc m0 (i0 + j)

omit [Host] in
theorem sixteen_add (i : Nat) :
    BitVec.ofNat 64 16 + BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

/-- **The tail loop** (`b8`), then the return (`b9`). -/
theorem tail (hp : Placed code k) {m0 : MachineData} (hpre : SumEPre m0) {i0 j : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumE.b8Offset)) (hI : TInv m0 i0 j s.data) :
    Eventually (step1 Host.exe) (Post m0) s := by
  have h16 : len m0 ≤ 16 := hpre.2.1
  have hrV : Readable m0 (addr m0) (16 * len m0) := hpre.2.2
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumE.b8Offset) ∧ ∃ j, len m0 - i0 - j = n ∧
    TInv m0 i0 j s.data) (fun n s ⟨hpc, j, hn, hI⟩ ↦ ?_) ⟨hpc, j, rfl, hI⟩
  have hlt := hI.lt
  have hd := hI.base.dmem
  have hr := sub_readable (o := 16 * (i0 + j)) (c := 16) hrV (by rw [hd]; exact fun _ h ↦ h)
    (by omega) (by omega)
  have hwf : (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * (i0 + j)), 16)]).WF :=
    Env.wf_of ⟨⟨hr.1, hr.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hal : (Sym.bin .add .W64 (.reg .rsi) (.reg .rdi)).eval
      (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * (i0 + j)), 16)]) =
      addr m0 + BitVec.ofNat 64 (16 * (i0 + j)) + BitVec.ofInt 64 8 := by
    rw [eval_add, eval_reg, eval_reg]
    show reg s.data .rsi + reg s.data .rdi = _
    rw [hI.rsi, hI.rdi, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact addr_eq (by omega)
  have hm : Match (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * (i0 + j)), 16)]) tailS
      s.data := match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨hal, trivial⟩
  refine exec_at (hb hp b8_in_code (by simp [b8])) run_b8 hwf (by intro l h; cases h) hpc hm
    fun s' hm' hpc' ↦ ?_
  have hB := hI.base.step hm hm' hwf rfl (after_eq run_b8 ▸ b8_keeps)
  have hE : ewArg ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * (i0 + j)), 16)]).load
      0 0 8) ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * (i0 + j)), 16)]).load 0 8 8) =
      (xs m0)[i0 + j]'(lt_len hlt) := elem_load hd (add_ofNat_zero _) hlt
  have hacc : ewArg (reg s'.data .rax) (reg s'.data .rdx) = acc m0 (i0 + (j + 1)) := by
    rw [show i0 + (j + 1) = i0 + j + 1 by omega, acc_succ m0 hlt, ← hI.acc, ← hE]
    show ewArg (s'.data.regs.get64 .rax) (s'.data.regs.get64 .rdx) = _
    rw [hm'.regs .rax (.bin .xor .W64 (.reg .rax) (.load 0 0 8)) rfl,
      hm'.regs .rdx (.bin .xor .W64 (.reg .rdx) (.load 0 8 8)) rfl, eval_xor, eval_xor,
      eval_reg, eval_reg, eval_load, eval_load]
    rfl
  have hdi : reg s'.data .rdi = BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show reg s'.data .rdi = (Sym.bin .add .W64 (.lit 16) (.reg .rdi)).eval
      (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * (i0 + j)), 16)]) from
      hm'.regs .rdi _ rfl, eval_add, eval_lit, eval_reg]
    show _ + reg s.data .rdi = _
    rw [hI.rdi, sixteen_add]
  have hcx : reg s'.data .rcx = reg s.data .rcx := hm'.regs .rcx (.reg .rcx) rfl
  have hsi : reg s'.data .rsi = reg s.data .rsi := hm'.regs .rsi (.reg .rsi) rfl
  simp only [PcOk, NativeRustcVmX64.Vm.SumE.b8_length] at hpc'
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg] at hpc'
  rw [show (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * (i0 + j)), 16)]).regs .rcx =
      reg s.data .rcx from rfl,
    show (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * (i0 + j)), 16)]).regs .rdi =
      reg s.data .rdi from rfl, hI.rcx, hI.rdi, sixteen_add,
    ofNat_beq (by omega) (by omega)] at hpc'
  obtain ⟨hT, hF⟩ := pc_cond hpc'
  by_cases hlast : 16 * (len m0 - i0) = 16 * (j + 1)
  · refine Eventually.mono (ret_of (hb hp b9_in_code (by simp [b9])) run_b9 rfl rfl
      (after_eq run_b9 ▸ b9_ret) hpre (hF (by simp [hlast])) hB ?_) fun _ h ↦ Or.inl h
    rw [show len m0 = i0 + (j + 1) by omega, ← hacc]
    rfl
  · refine .done _ (Or.inr ⟨len m0 - i0 - (j + 1), by omega,
      (hT (by simp [hlast])).trans (hp.label NativeRustcVmX64.Vm.SumE.label_8_at), j + 1, rfl, hB, by omega, ?_, hdi,
      hcx.trans hI.rcx, hacc⟩)
    exact hsi.trans hI.rsi

/-- **`NativeRustcVmX64.Vm.SumE.label_7`** (`b7`): the tail from value `i0`. -/
theorem fromL7 (hp : Placed code k) {m0 : MachineData} (hpre : SumEPre m0) {i0 : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumE.b7Offset)) (hB : Base m0 s.data)
    (hlt : i0 < len m0) (hr8 : reg s.data .r8 = BitVec.ofNat 64 i0)
    (hrcx : reg s.data .rcx = BitVec.ofNat 64 (len m0 - i0))
    (hrdi : reg s.data .rdi = addr m0)
    (hacc : ewArg (reg s.data .rax) (reg s.data .rdx) = acc m0 i0) :
    Eventually (step1 Host.exe) (Post m0) s := by
  have h16 : len m0 ≤ 16 := hpre.2.1
  refine exec_at (hb hp b7_in_code (by simp [b7])) run_b7 (Env.wf_nil _) (by intro l h; cases h)
    hpc (match_nil _) fun s' hm' hpc' ↦ ?_
  have hB' := hB.regs' hm' (after_eq run_b7 ▸ b7_keeps)
  simp only [PcOk, NativeRustcVmX64.Vm.SumE.b7_length] at hpc'
  refine tail hp hpre (i0 := i0) (j := 0) hpc' ⟨hB', by omega, ?_, ?_, ?_, ?_⟩
  · rw [show reg s'.data .rsi = (Sym.bin .add .W64 (.lit 8) (.bin .add .W64
      (.bin .shl .W64 (.reg .r8) (.lit 4)) (.reg .rdi))).eval (Env.ofMachine s.data []) from
      hm'.regs .rsi _ rfl, eval_add, eval_add, eval_shl_lit _ (by decide), eval_lit, eval_reg,
      eval_reg]
    show _ + ((reg s.data .r8) <<< 4 + reg s.data .rdi) = _
    rw [hr8, hrdi, shl4_ofNat, BitVec.add_comm (BitVec.ofNat 64 (16 * i0)),
      BitVec.add_comm (BitVec.ofNat 64 8)]
  · rw [show reg s'.data .rdi = (Sym.lit 0).eval (Env.ofMachine s.data []) from
      hm'.regs .rdi _ rfl]
    rfl
  · rw [show reg s'.data .rcx = (Sym.bin .shl .W32 (.reg .rcx) (.lit 4)).eval
      (Env.ofMachine s.data []) from hm'.regs .rcx _ rfl]
    show BinOp.apply .shl .W32 (reg s.data .rcx) (BitVec.ofNat 64 4) = _
    rw [hrcx, shl4_eval32 _ (by rw [toNat_ofNat_lt (by omega)]; omega), toNat_ofNat_lt (by omega)]
  · rw [Nat.add_zero, ← hacc]
    show ewArg (s'.data.regs.get64 .rax) (s'.data.regs.get64 .rdx) = _
    rw [Match.reg_eq (r := .rax) (match_nil _) hm' rfl rfl,
      Match.reg_eq (r := .rdx) (match_nil _) hm' rfl rfl]

/-! ## The unrolled loop -/

/-- **The unrolled loop's head** `NativeRustcVmX64.Vm.SumE.label_5`, `4 t` values added. -/
structure UInv (m0 : MachineData) (t : Nat) (s : MachineData) : Prop where
  base : Base m0 s
  le : 4 * t + 4 ≤ 4 * (len m0 / 4)
  r8 : reg s .r8 = BitVec.ofNat 64 (4 * t)
  rsi : reg s .rsi = BitVec.ofNat 64 (4 * (len m0 / 4))
  r9 : reg s .r9 = addr m0 + BitVec.ofNat 64 (64 * t) + BitVec.ofNat 64 56
  rcx : reg s .rcx = BitVec.ofNat 64 (len m0 % 4)
  rdi : reg s .rdi = addr m0
  acc : ewArg (reg s .rax) (reg s .rdx) = acc m0 (4 * t)

/-- The unrolled loop's exit, `.LSumE_6` (`b6`): the return, or the tail. -/
theorem fromL6 (hp : Placed code k) {m0 : MachineData} (hpre : SumEPre m0) {t : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumE.b6Offset)) (hB : Base m0 s.data)
    (ht : 4 * t = 4 * (len m0 / 4)) (hr8 : reg s.data .r8 = BitVec.ofNat 64 (4 * t))
    (hrcx : reg s.data .rcx = BitVec.ofNat 64 (len m0 % 4))
    (hrdi : reg s.data .rdi = addr m0)
    (hacc : ewArg (reg s.data .rax) (reg s.data .rdx) = acc m0 (4 * t)) :
    Eventually (step1 Host.exe) (Post m0) s := by
  refine exec_at (hb hp b6_in_code (by simp [b6])) run_b6 (Env.wf_nil _) (by intro l h; cases h)
    hpc (match_nil _) fun s' hm' hpc' ↦ ?_
  have hB' := hB.regs' hm' (after_eq run_b6 ▸ b6_keeps)
  have e : ∀ r ∈ [Reg64.rax, .rdx, .rcx, .rdi, .r8], reg s'.data r = reg s.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq (match_nil _) hm' rfl rfl
  have hacc' : ewArg (reg s'.data .rax) (reg s'.data .rdx) = acc m0 (4 * t) := by
    rw [e .rax (by simp), e .rdx (by simp), hacc]
  simp only [PcOk, NativeRustcVmX64.Vm.SumE.b6_length] at hpc'
  rw [eval_test, eval_reg] at hpc'
  rw [show (Env.ofMachine s.data []).regs .rcx = reg s.data .rcx from rfl, hrcx,
    ofNat_beq (by omega) (by decide)] at hpc'
  obtain ⟨hT, hF⟩ := pc_cond hpc'
  by_cases hz : len m0 % 4 = 0
  · refine ret_of (hb hp b9_in_code (by simp [b9])) run_b9 rfl rfl (after_eq run_b9 ▸ b9_ret)
      hpre ((hT (by simp [hz])).trans (hp.label NativeRustcVmX64.Vm.SumE.label_9_at)) hB' ?_
    rw [show len m0 = 4 * t by omega, ← hacc']
    rfl
  · refine fromL7 hp hpre (i0 := 4 * t) (hF (by simp [hz])) hB' (by omega)
      ((e .r8 (by simp)).trans hr8) ?_ ((e .rdi (by simp)).trans hrdi) hacc'
    rw [e .rcx (by simp), hrcx, show len m0 % 4 = len m0 - 4 * t by omega]

/-- **The unrolled loop** (`b5`), then its exit. -/
theorem unrolled (hp : Placed code k) {m0 : MachineData} (hpre : SumEPre m0) {t : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumE.b5Offset)) (hI : UInv m0 t s.data) :
    Eventually (step1 Host.exe) (Post m0) s := by
  have h16 : len m0 ≤ 16 := hpre.2.1
  have hrV : Readable m0 (addr m0) (16 * len m0) := hpre.2.2
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumE.b5Offset) ∧ ∃ t, len m0 / 4 - t = n ∧
    UInv m0 t s.data) (fun n s ⟨hpc, t, hn, hI⟩ ↦ ?_) ⟨hpc, t, rfl, hI⟩
  have hle := hI.le
  have hd := hI.base.dmem
  have hr := sub_readable (o := 64 * t) (c := 64) hrV (by rw [hd]; exact fun _ h ↦ h)
    (by omega) (by omega)
  have hwf : (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).WF :=
    Env.wf_of ⟨⟨hr.1, hr.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]) blkS s.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show reg s.data .r9 = addr m0 + BitVec.ofNat 64 (64 * t) + BitVec.ofInt 64 56 by
        rw [hI.r9]; rfl, trivial⟩ trivial trivial trivial
  refine exec_at (hb hp b5_in_code (by simp [b5])) run_b5 hwf (by intro l h; cases h) hpc hm
    fun s' hm' hpc' ↦ ?_
  have hB := hI.base.step hm hm' hwf rfl (after_eq run_b5 ▸ b5_keeps)
  have hlen : 4 * t + 4 ≤ len m0 := by omega
  have e0 : ewArg ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).load 0 0 8)
      ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).load 0 8 8) =
      (xs m0)[4 * t]'(lt_len (by omega)) :=
    elem_load hd (by rw [addr_add]; exact addr_eq (by omega)) (by omega)
  have e1 : ewArg ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).load 0 16 8)
      ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).load 0 24 8) =
      (xs m0)[4 * t + 1]'(lt_len (by omega)) :=
    elem_load hd (by rw [addr_add]; exact addr_eq (by omega)) (by omega)
  have e2 : ewArg ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).load 0 32 8)
      ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).load 0 40 8) =
      (xs m0)[4 * t + 1 + 1]'(lt_len (by omega)) :=
    elem_load hd (by rw [addr_add]; exact addr_eq (by omega)) (by omega)
  have e3 : ewArg ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).load 0 48 8)
      ((Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).load 0 56 8) =
      (xs m0)[4 * t + 1 + 1 + 1]'(lt_len (by omega)) :=
    elem_load hd (by rw [addr_add]; exact addr_eq (by omega)) (by omega)
  have hacc : ewArg (reg s'.data .rax) (reg s'.data .rdx) = acc m0 (4 * (t + 1)) := by
    rw [show 4 * (t + 1) = 4 * t + 4 by omega, acc4 m0 t hlen, ← hI.acc, ← e0, ← e1, ← e2, ← e3]
    show ewArg (s'.data.regs.get64 .rax) (s'.data.regs.get64 .rdx) = _
    rw [hm'.regs .rax (.bin .xor .W64 (.bin .xor .W64 (.bin .xor .W64 (.bin .xor .W64 (.reg .rax)
        (.load 0 0 8)) (.load 0 16 8)) (.load 0 32 8)) (.load 0 48 8)) rfl,
      hm'.regs .rdx (.bin .xor .W64 (.bin .xor .W64 (.bin .xor .W64 (.bin .xor .W64 (.reg .rdx)
        (.load 0 8 8)) (.load 0 24 8)) (.load 0 40 8)) (.load 0 56 8)) rfl]
    simp only [eval_xor, eval_reg, eval_load]
    rfl
  have h8 : reg s'.data .r8 = BitVec.ofNat 64 (4 * (t + 1)) := by
    rw [show reg s'.data .r8 = (Sym.bin .add .W64 (.lit 4) (.reg .r8)).eval
      (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]) from
      hm'.regs .r8 _ rfl, eval_add, eval_lit, eval_reg]
    show _ + reg s.data .r8 = _
    rw [hI.r8, ← BitVec.ofNat_add]
    exact congrArg _ (by omega)
  have e : ∀ r ∈ [Reg64.rcx, .rdi, .rsi], reg s'.data r = reg s.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm hm' rfl rfl
  simp only [PcOk, NativeRustcVmX64.Vm.SumE.b5_length] at hpc'
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg] at hpc'
  rw [show (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).regs .rsi =
      reg s.data .rsi from rfl,
    show (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]).regs .r8 =
      reg s.data .r8 from rfl, hI.rsi, hI.r8, ← BitVec.ofNat_add,
    ofNat_beq (by omega) (by omega)] at hpc'
  obtain ⟨hT, hF⟩ := pc_cond hpc'
  by_cases hlast : 4 * (len m0 / 4) = 4 + 4 * t
  · refine Eventually.mono (fromL6 hp hpre (t := t + 1) (hF (by simp [hlast])) hB (by omega) h8
      ((e .rcx (by simp)).trans hI.rcx) ((e .rdi (by simp)).trans hI.rdi) hacc)
      fun _ h ↦ Or.inl h
  · refine .done _ (Or.inr ⟨len m0 / 4 - (t + 1), by omega,
      (hT (by simp [hlast])).trans (hp.label NativeRustcVmX64.Vm.SumE.label_5_at), t + 1, rfl,
      ⟨hB, by omega, h8, (e .rsi (by simp)).trans hI.rsi, ?_, (e .rcx (by simp)).trans hI.rcx,
        (e .rdi (by simp)).trans hI.rdi, hacc⟩⟩)
    rw [show reg s'.data .r9 = (Sym.ptr 0 120).eval
      (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (64 * t), 64)]) from hm'.regs .r9 _ rfl]
    show addr m0 + BitVec.ofNat 64 (64 * t) + BitVec.ofInt 64 120 = _
    rw [show BitVec.ofInt 64 120 = BitVec.ofNat 64 120 from rfl]
    simp only [addr_add]
    exact addr_eq (by omega)

/-! ## The entry -/

/-- **`sum_e` meets its contract.** -/
theorem sumE_spec (hp : Placed code k) : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have h16 : len m0 ≤ 16 := hpre.2.1
  have hL : len m0 = (reg m0 .rsi).toNat := rfl
  have hB0 : Base m0 m0 := ⟨rfl, fun _ _ ↦ rfl, rfl⟩
  refine exec_then (hb hp b0_in_code (by simp [b0])) run_b0 (Env.wf_nil _)
    (by intro l h; cases h) (match_nil _) fun s1 hm1 hpc1 ↦ ?_
  have hB1 := hB0.regs' hm1 (after_eq run_b0 ▸ b0_keeps)
  have e1 : ∀ r ∈ [Reg64.rsi, .rdi], reg s1.data r = reg m0 r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq (match_nil _) hm1 rfl rfl
  simp only [PcOk, NativeRustcVmX64.Vm.SumE.b0_length] at hpc1
  rw [eval_test, eval_reg, Env.ofMachine_regs, beq_ofNat _ (by decide)] at hpc1
  obtain ⟨hT, hF⟩ := pc_cond hpc1
  by_cases hz : len m0 = 0
  · -- `len = 0`: return `0`.
    refine ret_of (hb hp b3_in_code (by simp [b3])) run_b3 rfl rfl (after_eq run_b3 ▸ b3_ret) hpre
      ((hT (decide_eq_true hz)).trans (hp.label NativeRustcVmX64.Vm.SumE.label_1_at)) hB1 ?_
    rw [hz]
    rfl
  have hpc1 := hF (fun h ↦ hz (of_decide_eq_true h))
  refine exec_at (hb hp b1_in_code (by simp [b1])) run_b1 (Env.wf_nil _) (by intro l h; cases h)
    hpc1 (match_nil _) fun s2 hm2 hpc2 ↦ ?_
  have hB2 := hB1.regs' hm2 (after_eq run_b1 ▸ b1_keeps)
  have e2 : ∀ r ∈ [Reg64.rsi, .rdi], reg s2.data r = reg m0 r := by
    intro r hr
    rw [← e1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq (match_nil _) hm2 rfl rfl
  have hsi1 : (reg s1.data .rsi).toNat < 2 ^ 32 := by rw [e1 .rsi (by simp)]; omega
  have hcx2 : reg s2.data .rcx = BitVec.ofNat 64 (len m0 % 4) := by
    rw [show reg s2.data .rcx = (Sym.bin .and .W32 (.un .trunc .W32 (.reg .rsi)) (.lit 3)).eval
      (Env.ofMachine s1.data []) from hm2.regs .rcx _ rfl]
    show BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (reg s1.data .rsi)) (BitVec.ofNat 64 3) = _
    rw [trunc_eval32 _ hsi1, and_eval32 _ hsi1 (by decide), e1 .rsi (by simp), and3 _ h16]
  simp only [PcOk, NativeRustcVmX64.Vm.SumE.b1_length] at hpc2
  have hsi : s1.data.regs.get64 .rsi = reg m0 .rsi := e1 .rsi (by simp)
  have hu := ult_eval (reg m0 .rsi) (c := 4) (by decide)
  simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, hsi, hu] at hpc2
  obtain ⟨hT2, hF2⟩ := pc_cond hpc2
  by_cases h4 : len m0 < 4
  · -- below `4`: the tail from `0`.
    have hpc2 := hF2 (by simp [h4])
    refine exec_at (hb hp b2_in_code (by simp [b2])) run_b2 (Env.wf_nil _)
      (by intro l h; cases h) hpc2 (match_nil _) fun s3 hm3 hpc3 ↦ ?_
    have hB3 := hB2.regs' hm3 (after_eq run_b2 ▸ b2_keeps)
    simp only [PcOk] at hpc3
    refine fromL7 hp hpre (i0 := 0) (hpc3.trans (hp.label NativeRustcVmX64.Vm.SumE.label_7_at)) hB3 (by omega)
      (hm3.regs .r8 (.lit 0) rfl) ?_ ?_ ?_
    · rw [show reg s3.data .rcx = reg s2.data .rcx from Match.reg_eq (match_nil _) hm3 rfl rfl,
        hcx2, Nat.mod_eq_of_lt h4, Nat.sub_zero]
    · exact (Match.reg_eq (r := .rdi) (match_nil _) hm3 rfl rfl).trans (e2 .rdi (by simp))
    · show ewArg (s3.data.regs.get64 .rax) (s3.data.regs.get64 .rdx) = _
      rw [hm3.regs .rax (.lit 0) rfl, hm3.regs .rdx (.lit 0) rfl]
      rfl
  · -- from `4`: the unrolled loop.
    have hpc2 := (hT2 (by simp [h4])).trans (hp.label NativeRustcVmX64.Vm.SumE.label_4_at)
    refine exec_at (hb hp b4_in_code (by simp [b4])) run_b4 (Env.wf_nil _)
      (by intro l h; cases h) hpc2 (match_nil _) fun s3 hm3 hpc3 ↦ ?_
    have hB3 := hB2.regs' hm3 (after_eq run_b4 ▸ b4_keeps)
    simp only [PcOk, NativeRustcVmX64.Vm.SumE.b4_length] at hpc3
    have hsi2 : (reg s2.data .rsi).toNat < 2 ^ 32 := by rw [e2 .rsi (by simp)]; omega
    have hdi : reg s3.data .rdi = addr m0 :=
      (Match.reg_eq (r := .rdi) (match_nil _) hm3 rfl rfl).trans (e2 .rdi (by simp))
    refine unrolled hp hpre (t := 0) hpc3 ⟨hB3, by omega, hm3.regs .r8 (.lit 0) rfl, ?_, ?_, ?_,
      hdi, ?_⟩
    · rw [show reg s3.data .rsi = (Sym.bin .and .W32 (.reg .rsi) (.lit 28)).eval
        (Env.ofMachine s2.data []) from hm3.regs .rsi _ rfl]
      show BinOp.apply .and .W32 (reg s2.data .rsi) (BitVec.ofNat 64 28) = _
      rw [and_eval32 _ hsi2 (by decide), e2 .rsi (by simp), and28 _ h16]
    · rw [show reg s3.data .r9 = (Sym.bin .add .W64 (.reg .rdi) (.lit 56)).eval
        (Env.ofMachine s2.data []) from hm3.regs .r9 _ rfl, eval_add, eval_reg, eval_lit]
      show reg s2.data .rdi + _ = _
      rw [e2 .rdi (by simp)]
      simp
    · rw [show reg s3.data .rcx = reg s2.data .rcx from Match.reg_eq (match_nil _) hm3 rfl rfl,
        hcx2]
    · show ewArg (s3.data.regs.get64 .rax) (s3.data.regs.get64 .rdx) = _
      rw [hm3.regs .rax (.lit 0) rfl, hm3.regs .rdx (.lit 0) rfl]
      rfl

end

end NativeRustcVmX64.Arrays.SumE
