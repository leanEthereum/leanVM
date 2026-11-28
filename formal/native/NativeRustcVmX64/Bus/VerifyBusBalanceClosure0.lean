module

public import NativeRustcVmX64.Bus.VerifyBusBalanceClosure0.Exec
public import NativeRustcVmX64.Bus.VerifyBusBalanceFrame
public import NativeRustcVmX64.Spec.Bus
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.Fingerprints.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names

/-!
# `verify_bus_balance::{closure#0}` on x86-64

`b0` pushes R15, R14, RBX into its 96-byte frame (`b0a`), reads its environment (RSI), pushes
`fingerprints`' eight stack arguments (its own stack argument and the counts `b0b`, the share's
limbs `b0c`, `bytecode_low`'s length `b0d`) and calls `fingerprints`; `b1` pops the frame and
returns (`fpClosure_spec`).
-/

namespace NativeRustcVmX64.Bus.FpClosure

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalanceClosure0
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVm.Transcript
open NativeRustcVm (wordOf ewOf ewsOf)

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 96 := by decide
theorem slots_ge : ∀ p ∈ slots, 72 ≤ p.1 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

/-- A register a block's literal state keeps, by a check over all registers. -/
theorem keep_of_all {S : SState} {P : Reg64 → Bool}
    (h : allRegs.all (fun r ↦ P r || S.reg r == some (.reg r)) = true) {r : Reg64}
    (hr : P r = false) : S.reg r = some (.reg r) := by
  have := List.all_eq_true.mp h r (mem_allRegs r)
  simp only [hr, Bool.false_or, beq_iff_eq] at this
  exact this

/-- Region `r` plus `o`. -/
theorem ptr_eval [Labels] {m : MachineData} {rs : List (BitVec 64 × Nat)}
    {vs : Nat → BitVec 64} {ret : BitVec 64} {r n : Nat} {b : BitVec 64}
    (hb : rs[r]? = some (b, n)) (o : Nat) :
    (Sym.ptr r (o : Int)).eval (Env.ofMachine m rs vs ret) = off b o := by
  rw [Sym.eval, Env.base_ofMachine m rs vs ret hb, BitVec.ofInt_natCast]

/-- A word loaded from a region's mapped bytes. -/
theorem load_word {m : MachineData} {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64}
    {ret : BitVec 64} {r n o : Nat} {b : BitVec 64} (hb : rs[r]? = some (b, n))
    (h : NativeRustcVm.Mapped m.dmem (off b o) 8) :
    (Env.ofMachine m rs vs ret).load r o 8 = (wordOf m.dmem (off b o)).toBitVec :=
  load_ofMachine hb (NativeRustcVm.wordAt_of_mapped h)

/-- Bytes apart from the frame's first `96`, kept. -/
theorem get_keep {d d' : DataMem} {fb a : BitVec 64} {n : Nat}
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange fb 96))
    (hA : NativeRustcVm.Apart a n fb (96 + 8)) (ha : NativeRustcVm.NoWrap a n)
    (hfb : NativeRustcVm.NoWrap fb (96 + 8)) :
    ∀ i < n, d'.get? (a + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i) := fun i hi ↦
  hs _ fun h ↦ not_inRange_of_apart hA ha hfb
    (inRange_off_self hi (by unfold NativeRustcVm.NoWrap at ha; omega)) (inRange_mono h (by omega))

/-- A word of kept bytes. -/
theorem wordOf_keep {d d' : DataMem} {a : BitVec 64} {n o : Nat}
    (h : ∀ i < n, d'.get? (a + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i))
    (ho : o + 8 ≤ n) : wordOf d' (off a o) = wordOf d (off a o) :=
  NativeRustcVm.wordOf_congr fun i hi ↦ by rw [off_add]; exact h _ (by omega)

/-- A stack argument the frame holds. -/
theorem stackArg_eq {d : MachineData} {fb : BitVec 64} (hsp : rspOf d = fb) {i : Nat}
    {w : UInt64} (h : NativeRustcVm.WordAt d.dmem (off fb (8 + 8 * i)) w) :
    stackArg d i = w.toBitVec := by
  unfold stackArg
  rw [hsp]
  exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt h)

/-- A byte of the frame at offset `j ≥ 96` is not one of its first `96`. -/
theorem not_low {fb : BitVec 64} {j : Nat} (h1 : 96 ≤ j) (h2 : j < 2 ^ 64) :
    ¬ NativeRustcVm.InRange fb 96 (off fb j) := by
  have := inRange_off_iff (b := fb) (o := 0) (n := 96) (j := j) h2 (by omega)
  rw [off_zero] at this
  rw [this]
  omega

theorem callee_ne {r : Reg64} (hr : calleeSaved r = true) : (r == .rsp) = false := by
  cases r <;> first | rfl | exact absurd hr (by decide)

variable [Host] {k : Nat}

/-- **The closure's contract.** -/
theorem fpClosure_spec (hp : Placed code k)
    (hfp : Spec (Labels.label NativeRustcVmX64.Vm.Fingerprints.entryLabel) FingerprintsPre FingerprintsPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost := by
  intro m0 hpre
  obtain ⟨hS, hA, hER, hES, hW, hM, hML, hBL, hSh, hOR, hOS⟩ := id hpre
  have h96 : 96 ≤ fpClosureStack := by unfold fpClosureStack; omega
  have hle' : 96 + fingerprintsStack ≤ fpClosureStack := by unfold fpClosureStack; omega
  have hN : fpClosureStack ≤ (rspOf m0).toNat := hS.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hS.2.1
  have hfbn : (stackBelow m0 96).toNat = (rspOf m0).toNat - 96 := stackBelow_toNat (by omega)
  have hfnw : NativeRustcVm.NoWrap (stackBelow m0 96) (96 + 8) := frame_noWrap hS h96
  have hfm : NativeRustcVm.Mapped m0.dmem (stackBelow m0 96) (96 + 8) := frame_mapped hS h96
  have hA2 : (rspOf m0).toNat + 8 + 8 * 1 ≤ 2 ^ 64 := hA.2
  have hnw112 : NativeRustcVm.NoWrap (stackBelow m0 96) 112 := by
    unfold NativeRustcVm.NoWrap; omega
  have hm112 : NativeRustcVm.Mapped m0.dmem (stackBelow m0 96) 112 := by
    intro i hi
    by_cases h : i < 104
    · exact hfm i h
    · have e1 : stackBelow m0 96 + BitVec.ofNat 64 i =
          rspOf m0 + 8#64 + BitVec.ofNat 64 (i - 104) := by
        apply BitVec.eq_of_toNat_eq
        rw [NativeRustcVm.toNat_add_ofNat (by omega), hfbn,
          NativeRustcVm.toNat_add_ofNat (a := rspOf m0 + 8#64) (by
            rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
              NativeRustcVm.toNat_add_ofNat (by omega)]; omega),
          show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
          NativeRustcVm.toNat_add_ofNat (by omega)]
        omega
      rw [e1]
      exact hA.1 (i - 104) (by omega)
  have hoF : NativeRustcVm.Apart (reg m0 .rdi) 48 (stackBelow m0 96) (96 + 8) :=
    apart_frame hOS hN h96
  have heF : NativeRustcVm.Apart (reg m0 .rsi) 56 (stackBelow m0 96) (96 + 8) :=
    apart_frame hES hN h96
  have hshF : NativeRustcVm.Apart (envWord m0 6) 16 (stackBelow m0 96) (96 + 8) :=
    apart_frame hSh.2 hN h96
  -- The blocks' places.
  have hb0 := infix_of b0_in_code (by simp [b0]) hp
  rw [b0_split] at hb0
  obtain ⟨hba, hb0'⟩ := hb0.append
  obtain ⟨hbb, hb0''⟩ := hb0'.append
  obtain ⟨hbc, hbd⟩ := hb0''.append
  rw [len_b0a] at hbb hbc hbd
  rw [len_b0b] at hbc hbd
  rw [len_b0c] at hbd
  unfold NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entry_at]
  -- `b0a`: the prologue, the environment's words.
  have hwfA := frame_wf (m0 := m0) (d := m0) (F := 96) (rest := [(reg m0 .rsi, 56)])
    (vars := fun _ ↦ 0) (ret := 0) ⟨hfm, hfnw⟩
    (fun x hx ↦ by rw [List.mem_singleton] at hx; subst hx; exact hER)
    (List.pairwise_pair.mpr (Apart.symm' heF))
  have hmA : Match (frameEnv m0 m0 96 [(reg m0 .rsi, 56)] (fun _ ↦ 0) 0) sA m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  refine exec_then hba exit_b0a hwfA nofun hmA fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hwsA, hrax, hr10, hr11, hrbx, hr14, hrsi, hrdx, hrcx, hr8, hr9, hr15, hrdi⟩ :=
    ok_b0a
  have hf1 : Frame m0 96 slots 72 st1.data :=
    Frame.of_prologue Frame.entry hwfA hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 96) :=
    sameOutside_low hwfA hm1 (r := 0) rfl (by decide) fun w hw ↦
      ⟨(hwsA w hw).1, (hwsA w hw).2.2⟩
  have eA : ∀ {i : Nat}, i < 7 →
      (frameEnv m0 m0 96 [(reg m0 .rsi, 56)] (fun _ ↦ 0) 0).load 1 (8 * i) 8 = envWord m0 i :=
    fun hi ↦ load_word rfl (mapped_off hER.1 (by omega))
  have x1rsi : reg st1.data .rsi = envWord m0 0 := (hm1.regs .rsi _ hrsi).trans (eA (i := 0) (by decide))
  have x1rdx : reg st1.data .rdx = envWord m0 1 := (hm1.regs .rdx _ hrdx).trans (eA (i := 1) (by decide))
  have x1rcx : reg st1.data .rcx = envWord m0 2 := (hm1.regs .rcx _ hrcx).trans (eA (i := 2) (by decide))
  have x1r8 : reg st1.data .r8 = envWord m0 3 := (hm1.regs .r8 _ hr8).trans (eA (i := 3) (by decide))
  have x1r9 : reg st1.data .r9 = envWord m0 4 := (hm1.regs .r9 _ hr9).trans (eA (i := 4) (by decide))
  have x1r15 : reg st1.data .r15 = envWord m0 6 := (hm1.regs .r15 _ hr15).trans (eA (i := 6) (by decide))
  have x1r14 : reg st1.data .r14 = reg m0 .rsi := (hm1.regs .r14 _ hr14).trans (eval_ptr rfl)
  have x1rax : reg st1.data .rax = reg m0 .r9 := hm1.regs .rax _ hrax
  have x1r10 : reg st1.data .r10 = reg m0 .r8 := hm1.regs .r10 _ hr10
  have x1r11 : reg st1.data .r11 = reg m0 .rcx := hm1.regs .r11 _ hr11
  have x1rbx : reg st1.data .rbx = reg m0 .rdx := hm1.regs .rbx _ hrbx
  have x1rdi : reg st1.data .rdi = reg m0 .rdi := hm1.regs .rdi _ hrdi
  simp only [PcOk] at hpc1
  rw [len_b0a] at hpc1
  -- `b0b`: the stack argument and the counts pushed.
  have hwfB : (Env.ofMachine st1.data [(stackBelow m0 96, 112)] (fun _ ↦ 0) 0).WF :=
    Env.wf_of ⟨⟨Mapped.keeps hm112 hf1.kept, hnw112⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hmB : Match (Env.ofMachine st1.data [(stackBelow m0 96, 112)] (fun _ ↦ 0) 0) sB st1.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf1.sp.trans (ptr_eval rfl 72).symm, trivial⟩ trivial trivial
      trivial
  refine exec_at hbb exit_b0b hwfB nofun hpc1 hmB fun st2 hm2 hpc2 => ?_
  obtain ⟨hspB, hwsB, w64, w56, w48, w40, w32, hallB⟩ := ok_b0b
  have kB : ∀ {r : Reg64}, (r == .rsp) = false → reg st2.data r = reg st1.data r :=
    fun h ↦ hm2.regs _ _ (keep_of_all hallB h)
  have hTouch : ∀ {j : Nat}, 72 ≤ j → j < 112 →
      ¬ Touch (stackBelow m0 96) 112 (fun j ↦ 32 ≤ j ∧ j < 72) (off (stackBelow m0 96) j) := by
    rintro j h1 h2 ⟨j', hj', ⟨-, hj2⟩, heq⟩
    have := off_inj hnw112 hj' h2 heq
    omega
  have hsB := sameOutside_touch hwfB hm2 (r := 0) rfl (by decide) hwsB
  have hf2 : Frame m0 96 slots 32 st2.data :=
    BusFrame.Frame.of_same hf1 ((hm2.regs .rsp _ hspB).trans (ptr_eval rfl 32))
      (fun r hr _ ↦ kB (callee_ne hr)) (hm2.kept hwfB) hsB
      (fun p hp i hi ↦ hTouch (by have := slots_ge p hp; omega)
        (by have := slots_le p hp; omega))
      (fun j hj ↦ hTouch (by omega) (by omega))
  have hs2 : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 96) :=
    hsB.mono fun q ⟨j, hj, ⟨_, hj2⟩, heq⟩ ↦ heq ▸ inRange_off_self (by omega) (by omega)
  have hs02 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 96) :=
    (hs1.trans hs2).mono fun _ h ↦ h.elim id id
  have wB : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 112 → WordW 0 o v (after b0b sB) →
      NativeRustcVm.WordAt st2.data.dmem (off (stackBelow m0 96) o)
        (UInt64.ofBitVec (v.eval (Env.ofMachine st1.data [(stackBelow m0 96, 112)]
          (fun _ ↦ 0) 0))) :=
    fun h hw ↦ wordAt_write hm2 rfl h hw
  have v64 : (Sym.load 0 104 8).eval
      (Env.ofMachine st1.data [(stackBelow m0 96, 112)] (fun _ ↦ 0) 0) = stackArg m0 0 := by
    have := load_word (m := st1.data) (rs := [(stackBelow m0 96, 112)]) (vs := fun _ ↦ 0)
      (ret := 0) (r := 0) (o := 104) rfl (mapped_off (Mapped.keeps hm112 hf1.kept) (by decide))
    rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ by
      rw [off_add]; exact hs1 _ (not_low (by omega) (by omega))] at this
    have e8 : off (stackBelow m0 96) 104 = rspOf m0 + BitVec.ofNat 64 (8 + 8 * 0) :=
      frame_add 96 8
    rw [e8] at this
    exact this
  simp only [PcOk] at hpc2
  rw [len_b0b] at hpc2
  -- `b0c`: the share's limbs pushed.
  have x2r15 : reg st2.data .r15 = envWord m0 6 := (kB rfl).trans x1r15
  have hwfC := frame_wf (m0 := m0) (d := st2.data) (F := 96) (rest := [(envWord m0 6, 16)])
    (vars := fun _ ↦ 0) (ret := 0) ⟨Mapped.keeps hfm hf2.kept, hfnw⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨Mapped.keeps hSh.1.1 hf2.kept, hSh.1.2⟩)
    (List.pairwise_pair.mpr (Apart.symm' hshF))
  have hmC : Match (frameEnv m0 st2.data 96 [(envWord m0 6, 16)] (fun _ ↦ 0) 0) sC st2.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.rsp_eval, known_ptr rfl x2r15, trivial⟩ trivial
      trivial trivial
  refine exec_at hbc exit_b0c hwfC nofun hpc2 hmC fun st3 hm3 hpc3 => ?_
  obtain ⟨hmidC, hwsC, w24, w16, hallC⟩ := ok_b0c
  have kC : ∀ {r : Reg64}, (r == .rsp || r == .r15) = false → reg st3.data r = reg st2.data r :=
    fun h ↦ hm3.regs _ _ (keep_of_all hallC h)
  have hf3 : Frame m0 96 slots 16 st3.data := Frame.of_block hf2 hwfC hm3 hmidC slots_le
  have hs3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 96) :=
    sameOutside_low hwfC hm3 (r := 0) rfl (by decide) fun w hw ↦
      ⟨(hwsC w hw).1, by have := hwsC w hw; omega⟩
  have hs03 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 96) :=
    (hs02.trans hs3).mono fun _ h ↦ h.elim id id
  have hshK := get_keep hs02 hshF hSh.1.2 hfnw
  have vC0 : (Sym.load 1 0 8).eval (frameEnv m0 st2.data 96 [(envWord m0 6, 16)] (fun _ ↦ 0) 0) =
      (wordOf m0.dmem (envWord m0 6)).toBitVec := by
    have := load_word (m := st2.data) (rs := [(stackBelow m0 96, 96 + 8), (envWord m0 6, 16)])
      (vs := fun _ ↦ 0) (ret := 0) (r := 1) (o := 0) rfl
      (mapped_off (Mapped.keeps hSh.1.1 hf2.kept) (by decide))
    rw [wordOf_keep hshK (by decide), off_zero] at this
    exact this
  have vC8 : (Sym.load 1 8 8).eval (frameEnv m0 st2.data 96 [(envWord m0 6, 16)] (fun _ ↦ 0) 0) =
      (wordOf m0.dmem (off (envWord m0 6) 8)).toBitVec := by
    have := load_word (m := st2.data) (rs := [(stackBelow m0 96, 96 + 8), (envWord m0 6, 16)])
      (vs := fun _ ↦ 0) (ret := 0) (r := 1) (o := 8) rfl
      (mapped_off (Mapped.keeps hSh.1.1 hf2.kept) (by decide))
    rw [wordOf_keep hshK (by decide)] at this
    exact this
  simp only [PcOk] at hpc3
  rw [len_b0c] at hpc3
  -- `b0d`: `bytecode_low`'s length pushed, `fingerprints` called.
  have x3r14 : reg st3.data .r14 = reg m0 .rsi := (kC rfl).trans ((kB rfl).trans x1r14)
  have hwfD := frame_wf (m0 := m0) (d := st3.data) (F := 96) (rest := [(reg m0 .rsi, 56)])
    (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.b0Offset + b0a.length + b0b.length + b0c.length + b0d.length)).toBitVec)
    ⟨Mapped.keeps hfm hf3.kept, hfnw⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨Mapped.keeps hER.1 hf3.kept, hER.2⟩)
    (List.pairwise_pair.mpr (Apart.symm' heF))
  have hmD : Match (frameEnv m0 st3.data 96 [(reg m0 .rsi, 56)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.b0Offset + b0a.length + b0b.length + b0c.length + b0d.length)).toBitVec) sD st3.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf3.rsp_eval, known_ptr rfl x3r14, trivial⟩ trivial
      trivial trivial
  refine exec_at hbd exit_b0d hwfD (fun _ _ ↦ rfl) hpc3 hmD fun st4 hm4 hpc4 => ?_
  obtain ⟨hmidD, hwsD, w8, hallD⟩ := ok_b0d
  have kD : ∀ {r : Reg64}, (r == .rsp || r == .r14) = false → reg st4.data r = reg st3.data r :=
    fun h ↦ hm4.regs _ _ (keep_of_all hallD h)
  have hf4 : Frame m0 96 slots 0 st4.data := Frame.of_block hf3 hwfD hm4 hmidD slots_le
  have hs4 : NativeRustcVm.SameOutside st3.data.dmem st4.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 96) :=
    sameOutside_low hwfD hm4 (r := 0) rfl (by decide) fun w hw ↦
      ⟨(hwsD w hw).1, by have := hwsD w hw; omega⟩
  have hs04 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 96) 96) :=
    (hs03.trans hs4).mono fun _ h ↦ h.elim id id
  have hsp4 : rspOf st4.data = stackBelow m0 96 := by rw [hf4.sp, off_zero]
  have k4 : ∀ {r : Reg64}, (r == .rsp || r == .r14) = false → (r == .rsp || r == .r15) = false →
      (r == .rsp) = false → reg st4.data r = reg st1.data r :=
    fun h1 h2 h3 ↦ (kD h1).trans ((kC h2).trans (kB h3))
  have x4rdi : reg st4.data .rdi = reg m0 .rdi := (k4 rfl rfl rfl).trans x1rdi
  have x4rsi : reg st4.data .rsi = envWord m0 0 := (k4 rfl rfl rfl).trans x1rsi
  have x4rdx : reg st4.data .rdx = envWord m0 1 := (k4 rfl rfl rfl).trans x1rdx
  have x4rcx : reg st4.data .rcx = envWord m0 2 := (k4 rfl rfl rfl).trans x1rcx
  have x4r8 : reg st4.data .r8 = envWord m0 3 := (k4 rfl rfl rfl).trans x1r8
  have x4r9 : reg st4.data .r9 = envWord m0 4 := (k4 rfl rfl rfl).trans x1r9
  -- The stack arguments.
  have hinC := writesIn_of_mid hmidC
  have hinD := writesIn_of_mid hmidD
  have keepCD : ∀ {o : Nat} {w : UInt64}, 32 ≤ o → o + 8 ≤ 104 →
      NativeRustcVm.WordAt st2.data.dmem (off (stackBelow m0 96) o) w →
      NativeRustcVm.WordAt st4.data.dmem (off (stackBelow m0 96) o) w :=
    fun h1 h2 h ↦ keepW hwfD hm4 hinD h2 (fun w hw _ ↦ .inl (by have := hwsD w hw; omega))
      (keepW hwfC hm3 hinC h2 (fun w hw _ ↦ .inl (by have := hwsC w hw; omega)) h)
  have keepD : ∀ {o : Nat} {w : UInt64}, 16 ≤ o → o + 8 ≤ 104 →
      NativeRustcVm.WordAt st3.data.dmem (off (stackBelow m0 96) o) w →
      NativeRustcVm.WordAt st4.data.dmem (off (stackBelow m0 96) o) w :=
    fun h1 h2 h ↦ keepW hwfD hm4 hinD h2 (fun w hw _ ↦ .inl (by have := hwsD w hw; omega)) h
  have sa0 : stackArg st4.data 0 = envWord m0 5 := by
    refine (stackArg_eq hsp4 (i := 0) (wordAt_write hm4 (r := 0) (o := 8) rfl (by decide) w8)).trans ?_
    have := load_word (m := st3.data) (rs := [(stackBelow m0 96, 96 + 8), (reg m0 .rsi, 56)])
      (vs := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.b0Offset + b0a.length + b0b.length + b0c.length + b0d.length)).toBitVec)
      (r := 1) (o := 40) rfl (mapped_off (Mapped.keeps hER.1 hf3.kept) (by decide))
    rw [wordOf_keep (get_keep hs03 heF hER.2 hfnw) (by decide)] at this
    exact this
  have sa1 : stackArg st4.data 1 = (wordOf m0.dmem (envWord m0 6)).toBitVec :=
    (stackArg_eq hsp4 (i := 1) (keepD (o := 16) (by decide) (by decide)
      (wordAt_write hm3 (r := 0) (o := 16) rfl (by decide) w16))).trans vC0
  have sa2 : stackArg st4.data 2 = (wordOf m0.dmem (off (envWord m0 6) 8)).toBitVec :=
    (stackArg_eq hsp4 (i := 2) (keepD (o := 24) (by decide) (by decide)
      (wordAt_write hm3 (r := 0) (o := 24) rfl (by decide) w24))).trans vC8
  have sa3 : stackArg st4.data 3 = reg m0 .rdx :=
    (stackArg_eq hsp4 (i := 3) (keepCD (o := 32) (by decide) (by decide) (wB (by decide) w32))).trans x1rbx
  have sa4 : stackArg st4.data 4 = reg m0 .rcx :=
    (stackArg_eq hsp4 (i := 4) (keepCD (o := 40) (by decide) (by decide) (wB (by decide) w40))).trans x1r11
  have sa5 : stackArg st4.data 5 = reg m0 .r8 :=
    (stackArg_eq hsp4 (i := 5) (keepCD (o := 48) (by decide) (by decide) (wB (by decide) w48))).trans x1r10
  have sa6 : stackArg st4.data 6 = reg m0 .r9 :=
    (stackArg_eq hsp4 (i := 6) (keepCD (o := 56) (by decide) (by decide) (wB (by decide) w56))).trans x1rax
  have sa7 : stackArg st4.data 7 = stackArg m0 0 :=
    (stackArg_eq hsp4 (i := 7) (keepCD (o := 64) (by decide) (by decide) (wB (by decide) w64))).trans v64
  -- `fingerprints`.
  have ew : ∀ {a : BitVec 64} {n : Nat}, EWsOk m0 a n fpClosureStack →
      ewsOf st4.data.dmem a n = ewsOf m0.dmem a n := fun h ↦
    NativeRustcVm.ewsOf_congr (get_keep hs04 (apart_frame h.2 hN h96) h.1.2 hfnw)
  have sl : ∀ {a n : BitVec 64}, SliceOk m0 a n fpClosureStack → slice st4.data a n = slice m0 a n :=
    fun h ↦ by unfold slice; rw [ew (n := _) h]
  have hpre4 : FingerprintsPre st4.data := by
    simp only [FingerprintsPre]
    rw [x4rdi, x4rsi, x4rdx, x4rcx, x4r8, x4r9, sa0]
    refine ⟨stackOk_callee hS hf4.kept hsp4 hle', ⟨?_, ?_⟩,
      ⟨⟨Mapped.keeps hW.1.1 hf4.kept, hW.1.2⟩, apart_callee hW.2 hsp4 hN hle'⟩,
      ⟨⟨Mapped.keeps hM.1.1 hf4.kept, hM.1.2⟩, apart_callee hM.2 hsp4 hN hle'⟩,
      ⟨⟨Mapped.keeps hML.1.1 hf4.kept, hML.1.2⟩, apart_callee hML.2 hsp4 hN hle'⟩,
      ⟨⟨Mapped.keeps hBL.1.1 hf4.kept, hBL.1.2⟩, apart_callee hBL.2 hsp4 hN hle'⟩,
      ⟨Mapped.keeps hOR.1 hf4.kept, hOR.2⟩, apart_callee hOS hsp4 hN hle'⟩
    · rw [hsp4]
      exact mapped_off (Mapped.keeps hfm hf4.kept) (by decide)
    · rw [hsp4, hfbn]; omega
  refine call_then hpc4 hfp hpre4 fun st5 hpc5 hrsp5 hpost5 => ?_
  simp only [FingerprintsPost, fpArgs] at hpost5
  obtain ⟨hews5, hch5, hsv5⟩ := hpost5
  rw [x4rdi, x4rsi, x4rdx, x4rcx, x4r8, x4r9, sa0, sa1, sa2, sa3, sa4, sa5, sa6, sa7, ew hW, ew hM,
    sl hML, sl hBL] at hews5
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st4.data fingerprintsStack) fingerprintsStack q →
      NativeRustcVm.InRange (stackBelow m0 fpClosureStack) fpClosureStack q ∧
        ¬ NativeRustcVm.InRange (stackBelow m0 96) (96 + 8) q :=
    fun q hq ↦ inRange_callee hsp4 h8 hN hle' hq
  have hnotR : ∀ j < 104, ¬ (NativeRustcVm.InRange (reg st4.data .rdi) 48
      (off (stackBelow m0 96) j) ∨ NativeRustcVm.InRange (stackBelow st4.data fingerprintsStack)
        fingerprintsStack (off (stackBelow m0 96) j)) := by
    intro j hj h
    have hin : NativeRustcVm.InRange (stackBelow m0 96) (96 + 8) (off (stackBelow m0 96) j) :=
      inRange_off_self hj (by omega)
    rcases h with h | h
    · rw [x4rdi] at h; exact not_inRange_of_apart hoF hOR.2 hfnw h hin
    · exact (hcal _ h).2 hin
  have hf5 : Frame m0 96 slots 8 st5.data :=
    BusFrame.Frame.call_at hf4 hsv5 hrsp5 hch5
      (fun p hp i hi ↦ hnotR _ (by have := slots_le p hp; omega)) (fun j hj ↦ hnotR _ (by omega))
  -- `b1`: the epilogue.
  change st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.b0Offset + b0.length) at hpc5
  rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.b0_next] at hpc5
  have hwfE := frame_wf (m0 := m0) (d := st5.data) (F := 96) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps hfm hf5.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _)
  have hmE : Match (frameEnv m0 st5.data 96 [] (fun _ ↦ 0) 0) sE st5.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf5.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwfE nofun hpc5 hmE
    fun st6 hm6 hpc6 => ?_
  obtain ⟨hsv6, hrsp6⟩ := Frame.epilogue hf5 hwfE hm6 ok_b1.1
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq hwfE ok_b1.2
  simp only [PcOk] at hpc6
  refine .done _ ⟨by rw [hpc6]; exact hf5.load_ret hS h96, hrsp6, ?_⟩
  simp only [FpClosurePost, fpClosureArgs]
  refine ⟨?_, ?_, hsv6⟩
  · rw [hd6]
    exact hews5
  · intro q hq
    rw [hd6]
    simp only [not_or] at hq
    rw [hch5 q ?_]
    · exact hs04 q fun h ↦ hq.2 (inRange_frame_stack h8 hN h96 h)
    · rintro (h | h)
      · rw [x4rdi] at h; exact hq.1 h
      · exact hq.2 (hcal q h).1

end

end NativeRustcVmX64.Bus.FpClosure
