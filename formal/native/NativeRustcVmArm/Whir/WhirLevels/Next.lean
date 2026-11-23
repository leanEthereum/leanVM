module

public import NativeRustcVmArm.Code.Vm.NextLevel.Names
public import NativeRustcVmArm.Whir.WhirLevels.Calls

/-!
# `whir_levels`: `next_level`'s call

`next_call`: from `Mid k` with a level after `k`, `next_level` (index `k`, the level at
`levels + 24 k`, the next level's fold and rate exponent, `μ`) rejects (the run rejected, `0`), or
gives `Head (k + 1)` (`1`).
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Layout.Ladder

public section

section
variable [Labels] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat}

/-- Level `k` in a state of the frame. -/
theorem Ctx.levelAt (c : Ctx a s0 levels ba b claim m0 rate) {st : MachineData} (hf : WFr m0 st)
    {k : Nat} (hk : k < levels.length) :
    LevelAt st.dmem (lvA m0 + BitVec.ofNat 64 (levelBytes * k)) (lvl (logN m0) rate k) := by
  have := c.levels_at hf k hk
  rwa [c.getElem hk] at this

omit [Labels] in
theorem level_le {len k : Nat} (hk : k < len) :
    levelBytes * k + levelBytes ≤ levelBytes * len := by
  have := Nat.mul_le_mul_left levelBytes (show k + 1 ≤ len by omega)
  rw [Nat.mul_succ] at this
  exact this

end

section
variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat}

/-- **`next_level`** at level `k`: the run rejected (`0`), or `Head (k + 1)` (`1`). -/
theorem next_call
    (hnl : ∀ a s level w rounds, Spec (Labels.label NativeRustcVmArm.Vm.NextLevel.entryLabel)
      (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds))
    (c : Ctx a s0 levels ba b claim m0 rate) {k : Nat} {s : TState} {w : WhirStateW}
    {rs : Array FoldRoundW} {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hm : Mid a s0 levels b claim m0 rate k s w rs st.data) (hk1 : k + 1 < levels.length)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.NextLevel.entryLabel ∧ retOf st.data = next)
    (hx0 : st.data.regs.X0 = m0.regs.X0) (hx1 : st.data.regs.X1.toNat = k)
    (hx2 : st.data.regs.X2.toBitVec = lvA m0 + BitVec.ofNat 64 (levelBytes * k))
    (hx3 : st.data.regs.X3.toNat = foldAt (k + 1))
    (hx4 : st.data.regs.X4.toNat = rate + 3 * (k + 1))
    (hx5 : st.data.regs.X5.toNat = logN m0 - w.alphas.size) (hx6 : st.data.regs.X6 = m0.regs.X6)
    (cont : ∀ m2, WFr m0 m2 → Regs m0 levels.length m2 →
      m2.regs.getXReg .X26 = st.data.regs.getXReg .X26 →
      (m2.regs.X0 = 0 ∧ runAll s0 levels b claim m0 = none) ∨
        (m2.regs.X0 = 1 ∧ ∃ s' w', Head a s0 levels b claim m0 (k + 1) s' w' m2) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨hv, -, hv2, -⟩ := stack_val
  have hle : 96 + nextLevelStack ≤ whirLevelsStack := by omega
  have hf := hm.fr
  have hl6 := c.len_le.2
  have hadm := admissible_iff.mp c.adm
  have hlog := c.logN_le
  have ht : st.data.regs.X0.toBitVec = tA m0 := by rw [hx0]
  have hp : st.data.regs.X6.toBitVec = pA m0 := by rw [hx6]
  have hlv := level_le (show k < levels.length by omega)
  have hpre : NextLevelPre a s (lvl (logN m0) rate k) w rs st.data := by
    refine ⟨?_, ?_, by have := hm.roots; omega, ?_, ?_, ?_, ?_, qAt_le _ _ _, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [ht]; exact c.whirT hf (by omega) rfl hle
    · rw [ht]; exact hm.ts
    · rw [hp]; exact hm.wa
    · rw [hx2]; exact c.levelAt hf (by omega)
    · show foldAt k ≤ roundCap
      unfold foldAt roundCap; split_ifs <;> omega
    · show rate + 3 * k < 64
      omega
    · rw [hx3]; unfold foldAt; split_ifs <;> omega
    · rw [hx4]; omega
    · rw [hx5]; unfold stackCap; omega
    · rw [hm.glued]; unfold gluedCap; omega
    · rw [ht, hp]; exact c.whirOut hf (by omega) rfl hle c.pout
    · rw [hx2]; exact c.whirIn hf hle (whirIn_sub c.lin hlv)
    · rw [hx2, hp]; exact apart_sub c.lp c.lin.1.2 hlv
    · rw [hx2, ht]; exact apart_sub c.lt c.lin.1.2 hlv
  refine Fr.leafAt hf c.hN hle keep_saved slots_le (fun q hq ↦ c.outs_not_frame (by omega) hq)
    (hnl a s _ w rs) hpc hpre (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq ↦ ?_,
      hq.2.2.2.2⟩) fun m2 hf2 hq hcs ↦ cont m2 hf2 (hm.regs.saved hcs) (hcs .X26 rfl) ?_
  · rcases hq with ⟨r, hr, hq⟩ | hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · right; left; rw [← hp]; exact hq
      · right; right; rw [← ht]; exact hq
    · left; exact hq
  · obtain ⟨h0, hnext, hwa, -, -⟩ := hq
    rw [hx1, hx3, hx4, hx5] at h0 hnext hwa
    have hrun := hm.nxt hk1
    have e : nextLevelM k (lvl (logN m0) rate k) ⟨foldAt (k + 1), rate + 3 * (k + 1), 0⟩
        (logN m0 - w.alphas.size) w rs =
        nextLevelM k (lvl (logN m0) rate k) (lvl (logN m0) rate (k + 1))
          (logN m0 - w.alphas.size) w rs := rfl
    rw [e] at h0 hnext hwa
    rcases hres : (nextLevelM k (lvl (logN m0) rate k) (lvl (logN m0) rate (k + 1))
        (logN m0 - w.alphas.size) w rs).run s with _ | ⟨w', s'⟩
    · rw [hres] at h0 hrun
      exact .inl ⟨h0, hrun⟩
    · rw [hres] at h0 hrun
      obtain ⟨ha', hg', hr'⟩ := nextLevelM_facts hres
      refine .inr ⟨h0, s', w', hf2, hm.regs.saved hcs, ?_, ?_, hk1, ?_, ?_, ?_, hrun⟩
      · rw [← ht]; exact hnext w' s' hres
      · rw [← hp]; exact (hwa w' s' hres).1
      · rw [ha', hm.alphas]
      · rw [hg', hm.glued]; omega
      · have := hm.roots; omega

end

end

end NativeRustcVmArm.Whir.WhirLevels
