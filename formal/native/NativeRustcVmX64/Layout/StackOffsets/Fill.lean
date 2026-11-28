module

public import NativeRustcVmX64.Layout.StackOffsets.Init

/-!
# `stack_offsets` on x86-64: the order array `0, 1, …, n - 1` (`b3` to `b12`)

From the entry's body at `b3` (`Start`) to `b13` with the order array written and the sort's
arguments set (`fill`): `b3` keeps `8 n` in RBP, `n = 0` goes to `b6`; `b4` splits at eight
blocks: `b5` to the one-word loop, `b7` to the eight-word loop `b8` (`step8`, `Inv8`), which ends
in `b9` (the rest or not); `b10` starts the one-word loop `b11` (`step11`, `Inv11`); `b12` sets
the sort's arguments.
-/

namespace NativeRustcVmX64.Layout.StackOffsets

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.StackOffsets NativeRustcVmX64.Layout.BuildFrame
open NativeRustcVm (WordAt)

@[expose] public section

/-- After the entry, at `b3`. -/
abbrev Start [Host] (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b3Offset) ∧ n m0 ≤ cap m0 ∧ B m0 8 s.data ∧ Regs m0 s.data ∧
    reg s.data .r13 = ob m0

/-- At `b13`. -/
abbrev At13 [Host] (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b13Offset) ∧ Ready m0 s.data

/-- Before the one-word loop (`b10`): `c` words written. -/
structure Pre10 (m0 : MachineData) (c : Nat) (d : MachineData) : Prop where
  init : Init m0 c d
  lt : c < n m0
  rcx : (reg d .rcx).toNat = c
  r13 : reg d .r13 = ob m0 + BitVec.ofNat 64 (8 * c)
  rax : (reg d .rax).toNat = n m0 - c

end

public section

theorem ofInt64 : BitVec.ofInt 64 64 = BitVec.ofNat 64 64 := rfl

/-- Registers a block keeps (`Keeps`), read after it. -/
theorem kp [Labels] {env : Env} {Sy : SState} {m : MachineData} (hm : Match env Sy m)
    {rs : List Reg64} (h : Keeps Sy rs = true) {rs' : List Reg64} (hs : ∀ r ∈ rs', r ∈ rs) :
    ∀ r ∈ rs', reg m r = env.regs r := fun r hr ↦ keeps_reg hm h (hs r hr)

variable {m0 : MachineData}

/-- `Init` after a step: the body, the registers it reads, `j'` words. -/
theorem Init.step {j j' : Nat} {d d' : MachineData} (h : Init m0 j d) (hb : B m0 8 d')
    (he : ∀ r ∈ [Reg64.rbp, .rbx, .r12, .r14, .r15], reg d' r = reg d r)
    (ho : Ords m0 j' d'.dmem) (hle : j' ≤ n m0) : Init m0 j' d' where
  b := hb
  regs := h.regs.of fun r hr ↦ he r (List.mem_cons_of_mem _ hr)
  rbp := (he .rbp (by simp)).trans h.rbp
  ords := ho
  le := hle

theorem ords_zero (m0 : MachineData) (d : Mem 64) : Ords m0 0 d := fun _ h ↦ absurd h (by omega)

variable [Host] {k : Nat}

/-- **A block of registers only** from `bodyS`: the body, memory kept. -/
theorem step0 {ds : List Directive} {kk : Nat} {Sy1 : SState} {x : Exit} {st : MachineState}
    {Q : MachineState → Prop} (hst : StackOk m0 1344) (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds bodyS = some (Sy1, x))
    (hret : ∀ l, x = .call l → (0 : BitVec 64) = (Host.addrOf (kk + ds.length)).toBitVec)
    (hpc : st.pc = Host.addrOf kk) (hb : B m0 8 st.data)
    (hok : MidOk 1328 8 slots Sy1 = true) (hmem : Sy1.mem = [])
    (cont : ∀ st', Match (frameEnv m0 st.data 1328 [] (fun _ ↦ 0) 0) Sy1 st'.data →
      PcOk (frameEnv m0 st.data 1328 [] (fun _ ↦ 0) 0) x (Host.addrOf (kk + ds.length)) st' →
      B m0 8 st'.data → st'.data.dmem = st.data.dmem → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st :=
  run0 hst hk hx hret hpc hb (match0 hb) hok fun st' hm' hpc' hb' ↦
    cont st' hm' hpc' hb' (hm'.dmem_eq (fr_wf0 hb hst (by decide)) hmem)

/-- `b12`: the sort's arguments. -/
theorem l12 (hp : Placed code k) (hst : StackOk m0 1344) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b12Offset)) (hI : Init m0 (n m0) st.data) :
    Eventually (step1 Host.exe) (At13 k m0) st := by
  obtain ⟨hok, hmem, hx7, hx6, hx2, hx1, hK⟩ := ok_b12
  refine step0 hst (b12_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b12 nofun hpc hI.b hok
    hmem fun st' hm' hpc' hb' hd ↦ .done _ ⟨hpc', ?_⟩
  refine ⟨hI.step hb' (kp hm' hK (by simp [cs])) (hd ▸ hI.ords) hI.le, ?_, ?_, ?_, ?_⟩
  · exact (hm'.regs .rdi _ hx7).trans (eval_ptr0 16)
  · show (st'.data.regs.get64 .rsi).toNat = _
    rw [hm'.regs .rsi _ hx6]
    exact congrArg BitVec.toNat hI.regs.r15
  · exact (hm'.regs .rdx _ hx2).trans hI.regs.r12
  · show (st'.data.regs.get64 .rcx).toNat = _
    rw [hm'.regs .rcx _ hx1]
    exact congrArg BitVec.toNat hI.regs.r15

/-- **A turn of the one-word loop** `b11`: word `c + j` written. -/
theorem step11 (hp : Placed code k) (hst : StackOk m0 1344) (hn : n m0 ≤ 158) {c j : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b11Offset)) (hI : Inv11 m0 c j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b12Offset) ∧ Init m0 (n m0) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b11Offset) ∧ Inv11 m0 c (j + 1) s.data)) st := by
  have hlt := hI.lt
  have hok := ord_ok (o := 8 * (c + j)) (l := 8) hst hI.init.b (by omega)
  have hwf := wf_one (d := st.data) (vars := fun _ ↦ 0) (ret := 0) hok.1 hok.2
  have e13 : st.data.regs.get64 .r13 = ob m0 + BitVec.ofNat 64 (8 * c) := hI.r13
  have edx : (st.data.regs.get64 .rdx).toNat = j := hI.rdx
  have hm : Match (Env.ofMachine st.data [(off (stackBelow m0 1328) (16 + 8 * (c + j)), 8)]
      (fun _ ↦ 0) 0) ordOneS st.data := by
    refine match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨?_, trivial⟩
    beta_reduce
    rw [idx_eval]
    show st.data.regs.get64 .r13 + BitVec.ofNat 64 (8 * (st.data.regs.get64 .rdx).toNat) =
      off (stackBelow m0 1328) (16 + 8 * (c + j)) + BitVec.ofInt 64 0
    rw [e13, edx, ofInt_zero64, BitVec.add_zero, NativeRustcVm.addr_add, ob_add,
      show 16 + (8 * c + 8 * j) = 16 + 8 * (c + j) by omega]
  refine exec_at (b11_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b11 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hS, hw0, hrdx', hK⟩ := ok_b11
  have hb' : B m0 8 st'.data :=
    hI.init.b.of_sub hst (by decide) hwf hm' hS (L := 1280) (by omega) (by decide) slots_ge slots_le
  have hsame := sub_same hwf hm' hS
  have hw := wordAt_write hm' (r := 0) (o := 0) rfl (by decide) (fun t ht ↦ by simpa using hw0 t ht)
  rw [u64_of (addReg_eval hI.rcx hI.rdx (by omega)), off_zero] at hw
  have hords : Ords m0 (c + j + 1) st'.data.dmem := by
    refine hI.init.ords.write hst (c := 1) (by omega) ?_ fun i hi ↦ ?_
    · rw [ob_add]; exact hsame
    · obtain rfl : i = 0 := by omega
      rw [ob_add, show 8 * 0 = 0 from rfl, NativeRustcVm.addr_add_zero, Nat.add_zero]
      exact hw
  have hK' := kp hm' hK (rs' := [Reg64.rbp, .rbx, .r12, .r14, .r15]) (by simp [cs])
  have hrax : ((Sym.reg .rax).eval (Env.ofMachine st.data
      [(off (stackBelow m0 1328) (16 + 8 * (c + j)), 8)] (fun _ ↦ 0) 0)).toNat = n m0 - c := hI.rax
  have hdx1 := addLit_eval (r := .rdx) (k := 1)
    (env := Env.ofMachine st.data [(off (stackBelow m0 1328) (16 + 8 * (c + j)), 8)] (fun _ ↦ 0) 0)
    hI.rdx (by omega) (by decide)
  simp only [PcOk] at hpc'
  obtain ⟨hy, hno⟩ := pc_of (P := n m0 - c ≠ j + 1) hpc' (by
    rw [SBool.eval, eq_eval, hrax, hdx1, decide_not])
  by_cases hl : n m0 - c = j + 1
  · exact .done _ (Or.inl ⟨hno (not_not.mpr hl),
      hI.init.step hb' hK' (by rw [show n m0 = c + j + 1 by omega]; exact hords) le_rfl⟩)
  · refine .done _ (Or.inr ⟨(hy hl).trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_11_at),
      ⟨hI.init.step hb' hK' hords (by omega), by omega, ?_, ?_, ?_, ?_⟩⟩)
    · rw [kp hm' hK (rs' := [Reg64.rcx]) (by simp [cs]) .rcx (by simp)]; exact hI.rcx
    · rw [kp hm' hK (rs' := [Reg64.r13]) (by simp [cs]) .r13 (by simp)]; exact hI.r13
    · rw [kp hm' hK (rs' := [Reg64.rax]) (by simp [cs]) .rax (by simp)]; exact hI.rax
    · show (st'.data.regs.get64 .rdx).toNat = _
      rw [hm'.regs .rdx _ hrdx']
      exact hdx1

/-- **The one-word loop**, to `b12` and then `b13`. -/
theorem loop11 (hp : Placed code k) (hst : StackOk m0 1344) (hn : n m0 ≤ 158) {c j : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b11Offset)) (hI : Inv11 m0 c j st.data) :
    Eventually (step1 Host.exe) (At13 k m0) st := by
  refine Eventually.bind (Sym.loop (Q := fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b12Offset) ∧
      Init m0 (n m0) s.data)
    (fun r s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b11Offset) ∧ ∃ j, n m0 - c - j = r ∧ Inv11 m0 c j s.data)
    (fun r s ⟨hpc, j, hr, hI⟩ ↦ ?_) ⟨hpc, j, rfl, hI⟩) fun s h ↦ l12 hp hst h.1 h.2
  refine Eventually.mono (step11 hp hst hn hpc hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨n m0 - c - (j + 1), by have := hI'.lt; have := hI.lt; omega, hpc', j + 1, rfl,
      hI'⟩

/-- `b10`: the one-word loop's start. -/
theorem l10 (hp : Placed code k) (hst : StackOk m0 1344) (hn : n m0 ≤ 158) {c : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b10Offset)) (hP : Pre10 m0 c st.data) :
    Eventually (step1 Host.exe) (At13 k m0) st := by
  obtain ⟨hok, hmem, hrdx, hK⟩ := ok_b10
  refine step0 hst (b10_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b10 nofun hpc hP.init.b
    hok hmem fun st' hm' hpc' hb' hd ↦ loop11 (c := c) (j := 0) hp hst hn hpc' ⟨hP.init.step hb'
      (kp hm' hK (by simp [cs])) (hd ▸ hP.init.ords) hP.init.le, by have := hP.lt; omega, ?_, ?_, ?_,
      ?_⟩
  · rw [kp hm' hK (rs' := [Reg64.rcx]) (by simp [cs]) .rcx (by simp)]; exact hP.rcx
  · rw [kp hm' hK (rs' := [Reg64.r13]) (by simp [cs]) .r13 (by simp)]; exact hP.r13
  · rw [kp hm' hK (rs' := [Reg64.rax]) (by simp [cs]) .rax (by simp)]; exact hP.rax
  · show (st'.data.regs.get64 .rdx).toNat = _
    rw [hm'.regs .rdx _ hrdx]
    rfl

/-- The eight-word loop's end, at `b9`. -/
abbrev At9 (k : Nat) (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b9Offset) ∧ Init m0 (n m0 / 8 * 8) s.data ∧
    (reg s.data .rcx).toNat = n m0 / 8 * 8 ∧
    reg s.data .r13 = ob m0 + BitVec.ofNat 64 (8 * (n m0 / 8 * 8)) ∧
    (reg s.data .rax).toNat = n m0 % 8

/-- **A turn of the eight-word loop** `b8`: words `8 q` to `8 q + 7` written. -/
theorem step8 (hp : Placed code k) (hst : StackOk m0 1344) (hn : n m0 ≤ 158) {q : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b8Offset)) (hI : Inv8 m0 q st.data) :
    Eventually (step1 Host.exe) (fun s ↦ At9 k m0 s ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackOffsets.b8Offset) ∧ Inv8 m0 (q + 1) s.data)) st := by
  have hlt := hI.lt
  have hN : n m0 / 8 * 8 ≤ n m0 := Nat.div_mul_le_self _ _
  have hok := ord_ok (o := 64 * q) (l := 64) hst hI.init.b (by omega)
  have hwf := wf_one (d := st.data) (vars := fun _ ↦ 0) (ret := 0) hok.1 hok.2
  have e13 : st.data.regs.get64 .r13 = ob m0 + BitVec.ofNat 64 (64 * q) := hI.r13
  have hm : Match (Env.ofMachine st.data [(off (stackBelow m0 1328) (16 + 64 * q), 64)]
      (fun _ ↦ 0) 0) quadS st.data := by
    refine match_ofMachine ⟨rfl, trivial⟩ ⟨?_, trivial⟩ trivial trivial trivial
    show _ = off (stackBelow m0 1328) (16 + 64 * q) + BitVec.ofInt 64 0
    rw [e13, ofInt_zero64, BitVec.add_zero, ob_add]
  refine exec_at (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b8 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hS, h0, hmid, h7, hrcx, hr13, hK⟩ := ok_b8
  have hb' : B m0 8 st'.data :=
    hI.init.b.of_sub hst (by decide) hwf hm' hS (L := 1280) (by omega) (by decide) slots_ge slots_le
  have hsame := sub_same hwf hm' hS
  have e : (st.data.regs.get64 .rcx).toNat = 8 * q := hI.rcx
  have hval : ∀ i < 8, WordAt st'.data.dmem (off (off (stackBelow m0 1328) (16 + 64 * q)) (8 * i))
      (8 * q + i).toUInt64 := by
    intro i hi
    rcases (show i = 0 ∨ i ∈ [1, 2, 3, 4, 5, 6] ∨ i = 7 by simp; omega) with rfl | hmem | rfl
    · have := wordAt_write hm' (r := 0) (o := 8 * 0) rfl (by decide)
        (fun t ht ↦ by simpa using h0 t ht)
      rwa [u64_of (show ((Sym.reg .rcx).eval (Env.ofMachine st.data
        [(off (stackBelow m0 1328) (16 + 64 * q), 64)] (fun _ ↦ 0) 0)).toNat = 8 * q + 0 from e)]
        at this
    · have hi' : 1 ≤ i ∧ i ≤ 6 := by simp at hmem; omega
      have := wordAt_write hm' (r := 0) (o := 8 * i) rfl (by omega) (hmid i hmem)
      rwa [u64_of (addLit_eval e (by omega) (by omega))] at this
    · have := wordAt_write hm' (r := 0) (o := 8 * 7) rfl (by decide)
        (fun t ht ↦ by simpa using h7 t ht)
      rwa [u64_of (litAdd_eval e (by omega) (by decide))] at this
  have hords : Ords m0 (8 * q + 8) st'.data.dmem := by
    refine hI.init.ords.write hst (c := 8) (by omega) ?_ fun i hi ↦ ?_
    · rw [ob_add, show 16 + 8 * (8 * q) = 16 + 64 * q by omega]; exact hsame
    · rw [ob_add, show 16 + 8 * (8 * q) = 16 + 64 * q by omega]; exact hval i hi
  have hK' := kp hm' hK (rs' := [Reg64.rbp, .rbx, .r12, .r14, .r15]) (by simp)
  have hinit : Init m0 (8 * (q + 1)) st'.data := hI.init.step hb' hK' hords (by omega)
  have e8 : ((Sym.bin .add .W64 (.reg .rcx) (.lit 8)).eval (Env.ofMachine st.data
      [(off (stackBelow m0 1328) (16 + 64 * q), 64)] (fun _ ↦ 0) 0)).toNat = 8 * q + 8 :=
    addLit_eval e (by omega) (by decide)
  have edx : ((Sym.reg .rdx).eval (Env.ofMachine st.data
      [(off (stackBelow m0 1328) (16 + 64 * q), 64)] (fun _ ↦ 0) 0)).toNat = n m0 / 8 * 8 := hI.rdx
  have hrcx' : (reg st'.data .rcx).toNat = 8 * (q + 1) := by
    show (st'.data.regs.get64 .rcx).toNat = _
    rw [hm'.regs .rcx _ hrcx, e8]; omega
  have hr13' : reg st'.data .r13 = ob m0 + BitVec.ofNat 64 (64 * (q + 1)) := by
    show st'.data.regs.get64 .r13 = _
    rw [hm'.regs .r13 _ hr13]
    show off (stackBelow m0 1328) (16 + 64 * q) + BitVec.ofInt 64 64 = _
    rw [ofInt64, off_add, ob_add, show 16 + 64 * q + 64 = 16 + 64 * (q + 1) by omega]
  have hrax' : (reg st'.data .rax).toNat = n m0 % 8 := by
    rw [kp hm' hK (rs' := [Reg64.rax]) (by simp) .rax (by simp)]; exact hI.rax
  have hrdx' : (reg st'.data .rdx).toNat = n m0 / 8 * 8 := by
    rw [kp hm' hK (rs' := [Reg64.rdx]) (by simp) .rdx (by simp)]; exact hI.rdx
  simp only [PcOk] at hpc'
  obtain ⟨hy, hno⟩ := pc_of (P := 8 * q + 8 ≠ n m0 / 8 * 8) hpc' (by
    rw [SBool.eval, eq_eval, e8, edx, decide_not])
  by_cases hl : 8 * q + 8 = n m0 / 8 * 8
  · refine .done _ (Or.inl ⟨hno (not_not.mpr hl), ?_, ?_, ?_, hrax'⟩)
    · rw [← hl, show 8 * q + 8 = 8 * (q + 1) by omega]; exact hinit
    · rw [← hl]; omega
    · rw [hr13', ← hl, show 8 * (8 * q + 8) = 64 * (q + 1) by omega]
  · exact .done _ (Or.inr ⟨(hy hl).trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_8_at),
      ⟨hinit, by omega, hrcx', hr13', hrdx', hrax'⟩⟩)

/-- `b10` from `b9`'s fall-through, or `b12`. -/
theorem l9 (hp : Placed code k) (hst : StackOk m0 1344) (hn : n m0 ≤ 158) {st : MachineState}
    (h : At9 k m0 st) : Eventually (step1 Host.exe) (At13 k m0) st := by
  obtain ⟨hpc, hI, hrcx, hr13, hrax⟩ := h
  obtain ⟨hok, hmem, hK⟩ := ok_b9
  refine step0 hst (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b9 nofun hpc hI.b hok hmem
    fun st' hm' hpc' hb' hd ↦ ?_
  have hI' := hI.step hb' (kp hm' hK (by simp [cs])) (hd ▸ hI.ords) hI.le
  simp only [PcOk] at hpc'
  obtain ⟨hy, hno⟩ := pc_of (P := n m0 % 8 = 0) hpc' (by
    rw [test_eval]; exact congrArg (fun x ↦ decide (x = 0)) hrax)
  have hN := Nat.div_add_mod (n m0) 8
  by_cases h0 : n m0 % 8 = 0
  · have e : n m0 / 8 * 8 = n m0 := by omega
    rw [e] at hI'
    exact l12 hp hst ((hy h0).trans (hp.label NativeRustcVmX64.Vm.StackOffsets.label_12_at)) hI'
  · refine l10 hp hst hn (hno h0) ⟨hI', by omega, ?_, ?_, ?_⟩
    · rw [kp hm' hK (rs' := [Reg64.rcx]) (by simp [cs]) .rcx (by simp)]; exact hrcx
    · rw [kp hm' hK (rs' := [Reg64.r13]) (by simp [cs]) .r13 (by simp)]; exact hr13
    · rw [kp hm' hK (rs' := [Reg64.rax]) (by simp [cs]) .rax (by simp)]
      show (reg st.data .rax).toNat = _
      rw [hrax]; omega

end

end NativeRustcVmX64.Layout.StackOffsets
