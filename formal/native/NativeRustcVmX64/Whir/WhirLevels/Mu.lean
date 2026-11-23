module

public import NativeRustcVmX64.Whir.WhirLevels.Fold

/-!
# `whir_levels`: `μ` and the last level's test (x86-64)

`mu_step`: from `Mid k` at `b4`, R9 becomes `μ = logN - |α|` (the state's count of `α`s) and the
code goes to `NativeRustcVmX64.Vm.WhirLevels.label_6` (`b8`, the last level) or falls to `b5` (`next_level`'s call), `Mid k`
kept (`b4` writes no memory and no callee-saved register).
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.WhirLevels

public section

/-- `Mid k` and `μ` in R9. -/
structure MidMu [Labels] (a : DecArea) (s0 : TState) (levels : List Whir.Level) (b : BasisW)
    (claim : EW) (m0 : MachineData) (rate k : Nat) (s : TState) (w : WhirStateW)
    (rs : Array FoldRoundW) (d : MachineData) : Prop where
  mid : Mid a s0 levels b claim m0 rate k s w rs d
  r9 : (reg d .r9).toNat = logN m0 - w.alphas.size

variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **`μ` and the last level's test.** -/
theorem mu_step (hp : Placed code k0) (c : Ctx a s0 levels ba b claim m0 rate) {k : Nat}
    {s : TState} {w : WhirStateW} {rs : Array FoldRoundW} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b4Offset)) (hm : Mid a s0 levels b claim m0 rate k s w rs st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      MidMu a s0 levels b claim m0 rate k s w rs st'.data ∧
        ((k + 1 = levels.length ∧ st'.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b8Offset)) ∨
          (k + 1 < levels.length ∧ st'.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b5Offset)))) st := by
  have hl := hm.loop
  have hk := hm.lt
  have hl6 := c.len_le
  obtain ⟨hsm, hsnw, hsap⟩ := c.state_region hl.fr.frame.kept
  let env := frameEnv m0 st.data 112 [(pA m0, 24)] (fun _ ↦ 0) 0
  have hwf : env.WF := c.wf hl.fr.frame.kept (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx; exact ⟨hsm, hsnw⟩)
    (List.pairwise_pair.mpr hsap)
  have hmS : Match env wS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hl.fr.frame.rsp_eval, known_ptr rfl hl.rbp, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf nofun hpc hmS
    fun st1 hm1 hpc1 ↦ .done _ ?_
  obtain ⟨hmid, hmem, ⟨k12, k13, k15⟩, krbp, krbx, kr9⟩ := ok_b4
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  have hf1 : Fr m0 8 st1.data :=
    ⟨Frame.of_block hl.fr.frame hwf hm1 hmid slots_le, by rw [Sm, hd]; exact hl.fr.same⟩
  have e : ∀ {r : Reg64} {v : Sym}, (after b4 wS).reg r = some v →
      reg st1.data r = v.eval env := fun h ↦ hm1.regs _ _ h
  have hloop : Loop levels m0 k 8 st1.data :=
    ⟨hf1, (e krbx).trans hl.rbx, (e k12).trans hl.r12, (e k13).trans hl.r13, (e k15).trans hl.r15,
      (e krbp).trans (by rw [eval_ptr rfl]), by rw [hd]; exact hl.w24,
      by rw [hd]; exact hl.w32, by rw [hd]; exact hl.w40, by rw [hd]; exact hl.w48,
      by rw [hd]; exact hl.w56⟩
  -- `μ`
  have h56 : env.load 0 56 8 = reg m0 .rsi :=
    load_ofMachine (o := 56) rfl hl.w56
  have hcnt : NativeRustcVm.WordAt st.data.dmem (off (pA m0) 16) w.alphas.size.toUInt64 := by
    have := hm.wa.1.alphas.2.1
    simpa [alphasOff] using this
  have h16 : env.load 1 16 8 = (w.alphas.size.toUInt64).toBitVec :=
    load_ofMachine (o := 16) (r := 1) rfl hcnt
  have hal : w.alphas.size ≤ 30 := by
    have := hm.wa.1.alphas.1
    simpa [stackCap] using this
  have hmu : (reg st1.data .r9).toNat = logN m0 - w.alphas.size := by
    rw [e kr9, v9_eval env h56 h16]
    show _ - (BitVec.ofNat 64 w.alphas.size).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨⟨hloop, by rw [hd]; exact hm.ts, by rw [hd]; exact hm.wa, hk, hm.alphas, hm.glued,
    hm.roots, hm.fin, hm.nxt⟩, hmu⟩, ?_⟩
  -- the test
  have h13 : env.regs .r13 = BitVec.ofNat 64 k - 1#64 := hl.r13
  have h48 : env.load 0 48 8 = 1#64 - BitVec.ofNat 64 levels.length := by
    rw [load_ofMachine (o := 48) rfl hl.w48]
    show 1#64 - reg m0 .r9 = _
    rw [c.len]
    simp
  simp only [PcOk, c4_eval env hk (by omega) h13 h48] at hpc1
  by_cases hlast : k + 1 = levels.length
  · simp only [hlast, decide_true, ↓reduceIte] at hpc1
    exact .inl ⟨hlast, hpc1.trans (hp.label NativeRustcVmX64.Vm.WhirLevels.label_6_at)⟩
  · simp only [hlast, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact .inr ⟨by omega, hpc1⟩

end

end NativeRustcVmX64.Whir.Levels.WL
