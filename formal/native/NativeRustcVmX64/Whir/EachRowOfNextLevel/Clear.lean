module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.Start
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names

/-!
# `each_row` with `next_level`'s closure: clearing the lanes (x86-64)

`b11` stores eight zero words at `RSP + RAX + 88` for RAX from 56 in steps of 64 below 1080: the
lanes `[152, 1176)` of the frame. An iteration (`clear_step`) runs `b11` in a region of its own
(the 64 bytes from `RSP + RAX + 88`), keeps the frame, the registers of `keepL` and memory outside
the lanes; sixteen of them (`clear_loop`) reach `b12`.
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

abbrev HitL (m0 : MachineData) : BitVec 64 → Prop := EachRow.Hit m0 1984 eachRowNextStack 152 1176

/-- The registers the lanes' clearing keeps. -/
@[expose] def keepL : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15, .rdi, .rsp]

theorem clear_writes : ∀ w ∈ (after b11 zS).mem, w.r = 0 ∧ w.off + w.n ≤ 64 := by
  rw [after_eq run_b11]; decide

theorem clear_keeps : ∀ r ∈ keepL, (after b11 zS).reg r = some (.reg r) := by
  rw [after_eq run_b11]; decide

variable [Host] {k : Nat}

/-- **An iteration of the lanes' clearing.** -/
theorem clear_step (hp : Placed code k) (c : Ctx rows op m0) {ms m : MachineData}
    {i : Nat} (hi : i ≤ 15) (hfr : FR m0 8 m) (hrax : reg m .rax = BitVec.ofNat 64 (56 + 64 * i))
    (hs : SameOutside ms.dmem m.dmem (HitL m0)) (hk : ∀ r ∈ keepL, reg m r = reg ms r)
    {R : MachineState → Prop}
    (next : ∀ m', i < 15 → FR m0 8 m' → reg m' .rax = BitVec.ofNat 64 (56 + 64 * (i + 1)) →
      SameOutside ms.dmem m'.dmem (HitL m0) → (∀ r ∈ keepL, reg m' r = reg ms r) →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b11Offset)⟩)
    (done : ∀ m', FR m0 8 m' → SameOutside ms.dmem m'.dmem (HitL m0) →
      (∀ r ∈ keepL, reg m' r = reg ms r) →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b12Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b11Offset)⟩ := by
  have hl := lay c
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hb : (fb m0 + BitVec.ofNat 64 (152 + 64 * i)).toNat =
      (rspOf m0).toNat - 1984 + (152 + 64 * i) := hl.addr (by omega)
  let env := Env.ofMachine m [(fb m0 + BitVec.ofNat 64 (152 + 64 * i), 64)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun j hj ↦ by
        rw [addr_add]
        exact hfr.kept _ (hl.mapped0 _ (by omega)), by
        show _ + 64 ≤ _
        rw [hb]
        have : eachRowNextStack = 3136 := rfl
        omega⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match env zS m :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      show (Sym.bin .add .W64 (.reg .rsp) (.reg .rax)).eval env =
        fb m0 + BitVec.ofNat 64 (152 + 64 * i) + BitVec.ofInt 64 (-88)
      rw [NativeRustcVmX64.Arrays.eval_add]
      show m.regs.get64 .rsp + m.regs.get64 .rax = _
      rw [show m.regs.get64 .rsp = _ from hfr.rsp, show m.regs.get64 .rax = _ from hrax, addr_add]
      apply BitVec.eq_of_toNat_eq
      have hfb := hl.base
      rw [toNat_add_ofNat _ _ (by rw [hfb]; omega), hfb, BitVec.toNat_add,
        toNat_add_ofNat _ _ (by rw [hfb]; omega), hfb]
      simp only [BitVec.toNat_ofInt]
      omega, trivial⟩
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b11Offset) := b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk11 run_b11 hwf (fun _ h ↦ by cases h) hm fun st hm' hpc ↦ ?_
  rw [← after_eq run_b11] at hm'
  have hs' : SameOutside m.dmem st.data.dmem (HitL m0) := by
    intro q hq
    refine hm'.get?_mem0 hwf fun ⟨w, hw, b', sz, hb', h1, h2⟩ ↦ hq ?_
    obtain ⟨hr, ho2⟩ := clear_writes w hw
    rw [hr] at hb'
    have hb'' : ([(fb m0 + BitVec.ofNat 64 (152 + 64 * i), 64)] : List (BitVec 64 × Nat))[0]? =
      some (b', sz) := hb'
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hb''
    obtain ⟨rfl, rfl⟩ := hb''
    rw [hb] at h1 h2
    show EachRow.Hit m0 1984 eachRowNextStack 152 1176 q
    rw [hl.hit_iff (by decide) (by decide)]
    left
    omega
  have hfr' : FR m0 8 st.data :=
    hfr.step hl (by decide) (by decide) ((rv hm' (v := .reg .rsp) (clear_keeps _ (by simp [keepL]))).trans
      hfr.rsp) (hm'.kept hwf) hs' (by decide)
  have hso : SameOutside ms.dmem st.data.dmem (HitL m0) := fun q hq ↦ (hs' q hq).trans (hs q hq)
  have hkeep : ∀ r ∈ keepL, reg st.data r = reg ms r := fun r hr ↦
    (rv hm' (clear_keeps r hr)).trans (hk r hr)
  have hra : env.regs .rax = BitVec.ofNat 64 (56 + 64 * i) := hrax
  simp only [PcOk] at hpc
  rw [after_eq run_b11] at hm'
  split at hpc
  · rename_i hc
    have hi15 : i < 15 := by
      rcases Nat.lt_or_ge i 15 with h | h
      · exact h
      · obtain rfl : i = 15 := by omega
        simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hra] at hc
        exact absurd hc (by decide)
    rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_7 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b11Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_7_at]
      at hpc
    obtain ⟨d, pc⟩ := st
    simp only at hpc hfr' hso hkeep hm'
    subst hpc
    refine next d hi15 hfr' ?_ hso hkeep
    rw [rv hm' (v := .bin .add .W64 (.lit 64) (.reg .rax)) rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hra]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show Width.W64.bits = 64 from rfl]
    omega
  · obtain ⟨d, pc⟩ := st
    simp only at hpc hfr' hso hkeep
    subst hpc
    exact done d hfr' hso hkeep

/-- **The lanes' clearing**, from iteration `i`. -/
theorem clear_loop (hp : Placed code k) (c : Ctx rows op m0) {ms : MachineData}
    {R : MachineState → Prop}
    (done : ∀ m', FR m0 8 m' → SameOutside ms.dmem m'.dmem (HitL m0) →
      (∀ r ∈ keepL, reg m' r = reg ms r) →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b12Offset)⟩) :
    ∀ n i m, 15 - i = n → i ≤ 15 → FR m0 8 m → reg m .rax = BitVec.ofNat 64 (56 + 64 * i) →
      SameOutside ms.dmem m.dmem (HitL m0) → (∀ r ∈ keepL, reg m r = reg ms r) →
      Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b11Offset)⟩ := by
  intro n
  induction n with
  | zero =>
    intro i m hn hi hfr hrax hs hk
    exact clear_step hp c hi hfr hrax hs hk (fun _ hlt ↦ absurd hlt (by omega)) done
  | succ n ih =>
    intro i m hn hi hfr hrax hs hk
    exact clear_step hp c hi hfr hrax hs hk
      (fun m' _ hfr' hrax' hs' hk' ↦ ih (i + 1) m' (by omega) (by omega) hfr' hrax' hs' hk') done

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
