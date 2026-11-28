module

public import NativeRustcVmArm.Whir.LanesOf.Inv

/-!
# `lanes_of`'s returns

`b15`: `None` (X0 `0`), more than 64 lanes. `b19`: `Some(len)` (X0 `1`, X1 X2), the lanes written.
`b14`: X1 X2, X0 already `1` (`Done`).
-/

namespace NativeRustcVmArm.Whir.LanesOf

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.LanesOf

public section

variable [Host] {k : Nat}

/-- The contract's end. -/
abbrev Q (m0 : MachineData) : MachineState → Prop :=
  fun s ↦ s.pc = retOf m0 ∧ LanesOfPost m0 s.data

theorem inf (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

omit [Host] in
theorem retOf_eq {st m0 : MachineData} (h : st.regs.X30 = m0.regs.X30) : retOf st = retOf m0 := by
  simp only [retOf, h]

/-- Continue from a state at `pc`. -/
theorem goto {R : MachineState → Prop} {pc : Int64} {s : MachineState} (h : s.pc = pc)
    (H : Eventually (step1 Host.exe) R ⟨s.data, pc⟩) : Eventually (step1 Host.exe) R s := by
  obtain ⟨d, pc'⟩ := s
  simp only at h
  subst h
  exact H

omit [Host] in
theorem pc_taken [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {s : MachineState}
    (h : PcOk env (.cond c l) next s) (hc : c.eval env = true) : s.pc = Labels.label l := by
  simp only [PcOk, hc, ↓reduceIte] at h
  exact h

omit [Host] in
theorem pc_fall [Labels] {env : Env} {c : SBool} {l : Label} {next : Int64} {s : MachineState}
    (h : PcOk env (.cond c l) next s) (hc : c.eval env = false) : s.pc = next := by
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at h
  exact h

omit [Host] in
theorem toNat_of_eq {x : UInt64} {v : BitVec 64} {n : Nat} (h : x.toBitVec = v)
    (hv : v.toNat = n) : x.toNat = n := by
  rw [← hv, ← h]; rfl

omit [Host] in
theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **`b19`**: `Some(X2)`. -/
theorem ret19 (hp : Placed code k) {m0 st : MachineData} {f : Nat → EW} {n : Nat}
    (hb : Body m0 f n st) (hx2 : st.regs.X2.toNat = n) (hsz : (lanesM m0).size = n)
    (hf : ∀ j (h : j < (lanesM m0).size), (lanesM m0)[j] = f j) (hn : n ≤ 64) :
    Eventually (step1 Host.exe) (Q m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b19Offset)⟩ := by
  refine exec_then (inf hp b19_in_code (by simp [b19])) run_b19 (Env.wf_nil _) (match_nil _)
    fun s hm hpc ↦ .done _ ?_
  have hk := after_eq run_b19 ▸ b19_keeps
  have hfr := hb.fr.of_regsS hm hk.1 hk.2
  have hd := hm.dmem_eq (Env.wf_nil _) hk.2
  have h30 : s.data.regs.X30 = m0.regs.X30 := (reg_kept hm (r := .X30) rfl).trans hb.x30
  simp only [PcOk] at hpc
  refine ⟨hpc.trans (retOf_eq h30), post_some hfr (hb.lanes.of_dmem hd) hsz hf hn ?_ ?_⟩
  · exact UInt64.toBitVec_inj.mp (hm.regs .X0 _ rfl)
  · have h1 := hm.regs .X1 _ rfl
    show (s.data.regs.getXReg .X1).toBitVec.toNat = n
    rw [h1]
    exact hx2

/-- **`b14`**: X1 X2. -/
theorem ret14 (hp : Placed code k) {m0 st : MachineData} {f : Nat → EW} {n : Nat}
    (hD : Done m0 f n st) (hsz : (lanesM m0).size = n)
    (hf : ∀ j (h : j < (lanesM m0).size), (lanesM m0)[j] = f j) (hn : n ≤ 64) :
    Eventually (step1 Host.exe) (Q m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b14Offset)⟩ := by
  refine exec_then (inf hp b14_in_code (by simp [b14])) run_b14 (Env.wf_nil _) (match_nil _)
    fun s hm hpc ↦ .done _ ?_
  have hk := after_eq run_b14 ▸ b14_keeps
  have hb := hD.body
  have hfr := hb.fr.of_regsS hm hk.1 hk.2
  have hd := hm.dmem_eq (Env.wf_nil _) hk.2
  have h30 : s.data.regs.X30 = m0.regs.X30 := (reg_kept hm (r := .X30) rfl).trans hb.x30
  simp only [PcOk] at hpc
  refine ⟨hpc.trans (retOf_eq h30), post_some hfr (hb.lanes.of_dmem hd) hsz hf hn ?_ ?_⟩
  · exact (reg_kept hm (r := .X0) rfl).trans hD.x0
  · have h1 := hm.regs .X1 _ rfl
    show (s.data.regs.getXReg .X1).toBitVec.toNat = n
    rw [h1]
    exact hD.x2

/-- **`b15`**: `None`. -/
theorem ret15 (hp : Placed code k) {m0 st : MachineData} (hfr : Fr m0 st)
    (h30 : st.regs.X30 = m0.regs.X30) (hsz : 64 < (lanesM m0).size) :
    Eventually (step1 Host.exe) (Q m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b15Offset)⟩ := by
  refine exec_then (inf hp b15_in_code (by simp [b15])) run_b15 (Env.wf_nil _) (match_nil _)
    fun s hm hpc ↦ .done _ ?_
  have hk := after_eq run_b15 ▸ b15_keeps
  have hfr' := hfr.of_regsS hm hk.1 hk.2
  have h30' : s.data.regs.X30 = m0.regs.X30 := (reg_kept hm (r := .X30) rfl).trans h30
  simp only [PcOk] at hpc
  exact ⟨hpc.trans (retOf_eq h30'), post_none hfr' hsz (UInt64.toBitVec_inj.mp (hm.regs .X0 _ rfl))⟩

end

end NativeRustcVmArm.Whir.LanesOf
