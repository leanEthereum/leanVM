module

public import NativeRustcVmX64.Whir.NextLevel.Queries

/-!
# `next_level`: the zeroing loop (x86-64)

`NativeRustcVmX64.Vm.NextLevel.label_9` (`b17`) zeroes the frame's 80 bytes at `RSP + RCX + 616` (the frame's offset
`760 + 80 i`, RCX `72 + 80 i`) for `i < 46` (`zero_step`, `zero_loop`): to `b18` with `H17`.
Nothing it writes is read again.
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

public section

theorem ofInt_neg616 : (BitVec.ofInt 64 (-616)).toNat = 2 ^ 64 - 616 := by
  rw [BitVec.toNat_ofInt]; rfl

theorem mem_filter_rcx {r : Reg64} (h : r ≠ .rcx) : r ∈ allRegs.filter (· != .rcx) := by
  rw [List.mem_filter]
  cases r <;> first | exact absurd rfl h | exact ⟨by simp [allRegs], rfl⟩

theorem cZero_eval [Labels] (env : Env) {i : Nat} (h : env.regs .rcx = BitVec.ofNat 64 (72 + 80 * i))
    (hi : i < 46) : cZero.eval env = !decide (i = 45) := by
  simp only [cZero, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h]
  rw [← BitVec.ofNat_add, ofNat_beq (X := 80 + (72 + 80 * i)) (k := 3752) (by omega) (by omega)]
  have e : (80 + (72 + 80 * i) = 3752) ↔ i = 45 := by omega
  simp only [e]

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat} {xs ood : Array EW} {v lam : EW}
  {qs : Array UInt64} {s8 : TState}

/-- **A turn of the zeroing loop.** -/
theorem zero_step (hp : Placed code k) (c : Ctx a s level w rounds m0) {i : Nat} (hi : i < 46)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b17Offset))
    (hrcx : reg st.data .rcx = BitVec.ofNat 64 (72 + 80 * i))
    (hH : H17 a level w rounds m0 xs ood v lam qs s8 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ H17 a level w rounds m0 xs ood v lam qs s8 st'.data ∧
      ((st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b17Offset) ∧ i + 1 < 46 ∧
        reg st'.data .rcx = BitVec.ofNat 64 (72 + 80 * (i + 1))) ∨
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b18Offset))) st := by
  have g := c.geo
  have hK := hH.K
  have hxs : xs.size ≤ 6 := by rw [hH.size]; exact c.fold
  have hos : ood.size ≤ 30 := by rw [hH.osize]; exact c.mu
  set o := 760 + 80 * i with ho
  have hl := c.loc_toNat (j := o) (by omega)
  have hmap : NativeRustcVm.Mapped st.data.dmem (loc m0 o) 80 := fun j hj ↦ by
    have := (c.region_ok hK.fr.frame.kept).1 (o + j) (by omega)
    rw [off_add]; exact this
  have hwf : (Env.ofMachine st.data [(loc m0 o, 80)]).WF :=
    Env.wf_of ⟨⟨hmap, by show (loc m0 o).toNat + 80 ≤ 2 ^ 64; rw [hl]; have := g.hA; omega⟩,
      trivial⟩
      (List.pairwise_singleton _ _)
  have hsp : rspOf st.data = loc m0 72 := hK.fr.frame.sp
  have hal : (Sym.bin .add .W64 (.reg .rsp) (.reg .rcx)).eval
      (Env.ofMachine st.data [(loc m0 o, 80)]) =
      (Env.ofMachine st.data [(loc m0 o, 80)]).base 0 + BitVec.ofInt 64 (-616) := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs,
      Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rw [show st.data.regs.get64 .rsp = rspOf st.data from rfl, hsp,
      show st.data.regs.get64 .rcx = reg st.data .rcx from rfl, hrcx]
    apply BitVec.eq_of_toNat_eq
    have := g.hN; have := g.hA
    have h72 := c.loc_toNat (j := 72) (by omega)
    have e1 : (loc m0 72 + BitVec.ofNat 64 (72 + 80 * i)).toNat =
        (rspOf m0).toNat - 8176 + 144 + 80 * i := by
      rw [NativeRustcVm.toNat_add_ofNat (by rw [h72]; omega), h72]; omega
    have e2 : (loc m0 o + BitVec.ofInt 64 (-616)).toNat = (rspOf m0).toNat - 8176 + 144 + 80 * i := by
      rw [BitVec.toNat_add, hl, ofInt_neg616]; omega
    rw [e1, e2]
  have hm : Match (Env.ofMachine st.data [(loc m0 o, 80)]) zeroS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨hal, trivial⟩
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) exit_b17 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hw, hrcx', hkr⟩ := ok_b17
  have hso : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (loc m0 o) 80) :=
    sameOutside_low hwf hm' (r := 0) rfl (le_refl 80) hw
  have hr : ∀ r, r ≠ .rcx → reg st'.data r = reg st.data r := fun r hr ↦
    hm'.regs r _ (hkr r (mem_filter_rcx hr))
  obtain ⟨hK', hz⟩ := c.K_low hK hr (hm'.kept hwf) (lo := o) (n := 80) (by omega) (by omega) hso
  have hfa : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (NativeRustcVm.InRange (fa m0) (o + 80)) :=
    NativeRustcVm.SameOutside.mono hso fun q hq ↦ c.loc_fa (by omega) hq
  have hH' : H17 a level w rounds m0 xs ood v lam qs s8 st'.data :=
    ⟨hK', (hr .rbx (by decide)).trans hH.rbx, (hr .r12 (by decide)).trans hH.r12,
      (hr .r14 (by decide)).trans hH.r14, by rw [hr .r15 (by decide)]; exact hH.r15,
      (hr .rax (by decide)).trans hH.rax, hH.ff.keep hz hxs hos, hH.size, hH.osize,
      c.qbuf_frame (hi := o + 80) (by omega) hfa hH.qbuf,
      c.ts_frame (hi := o + 80) (by omega) (hm'.kept hwf) hfa hH.ts⟩
  have e' : reg st'.data .rcx = (Sym.bin .add .W64 (.lit 80) (.reg .rcx)).eval
      (Env.ofMachine st.data [(loc m0 o, 80)]) := hm'.regs .rcx _ hrcx'
  have hrcx2 : reg st'.data .rcx = BitVec.ofNat 64 (72 + 80 * (i + 1)) := by
    rw [e']
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .rcx = reg st.data .rcx from rfl, hrcx, ← BitVec.ofNat_add]
    congr 1
    omega
  simp only [PcOk, cZero_eval (Env.ofMachine st.data [(loc m0 o, 80)]) hrcx hi] at hpc'
  by_cases h45 : i = 45
  · have e : (!decide (i = 45)) = false := by simp [h45]
    simp only [e, Bool.false_eq_true, ite_false] at hpc'
    have hpc'' : st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b18Offset) := hpc'
    exact .done _ ⟨hH', Or.inr hpc''⟩
  · have e : (!decide (i = 45)) = true := by simp [h45]
    simp only [e, ite_true] at hpc'
    exact .done _ ⟨hH', Or.inl ⟨hpc'.trans (hp.label NativeRustcVmX64.Vm.NextLevel.label_9_at), by omega, hrcx2⟩⟩

/-- **The zeroing loop**, from its head with RCX `72`, to `b18`. -/
theorem zero_loop (hp : Placed code k) (c : Ctx a s level w rounds m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b17Offset)) (hrcx : reg st.data .rcx = BitVec.ofNat 64 72)
    (hH : H17 a level w rounds m0 xs ood v lam qs s8 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b18Offset) ∧
      H17 a level w rounds m0 xs ood v lam qs s8 st'.data) st := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b17Offset) ∧ ∃ i, 46 - i = n ∧ i < 46 ∧
      reg st.data .rcx = BitVec.ofNat 64 (72 + 80 * i) ∧
      H17 a level w rounds m0 xs ood v lam qs s8 st.data)
    (fun n st ⟨hpc, i, hn, hi, hr, hH⟩ ↦ ?_) ⟨hpc, 0, rfl, by decide, hrcx, hH⟩
  refine Eventually.mono (zero_step hp c hi hpc hr hH) fun st' ⟨hH', h⟩ ↦ ?_
  rcases h with ⟨hpc', hi', hr'⟩ | hpc'
  · exact Or.inr ⟨46 - (i + 1), by omega, hpc', i + 1, rfl, hi', hr', hH'⟩
  · exact Or.inl ⟨hpc', hH'⟩

end

end NativeRustcVmX64.Whir.Levels.NL
