module

public import NativeRustcVmX64.Whir.GlueLevel.Facts
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names

/-!
# `glue_level`: the claim and the first glued claim (x86-64)

`b3` stores the new claim and checks the glued claims' count; `b4` writes the first new glued
claim's header and calls `Buf<EW, 30>::extend` for its point; `b5` checks its `Some`. At `b6`
(`AtB6`): the template `t5`, the count as at the entry, the point in the first new glued claim.
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Whir.Rows
open NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Vm.GlueLevel
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero toNat_off)

@[expose] public section

/-- **At `b6`**: the template `t5`, the count as at the entry, the first glued claim's point. -/
structure AtB6 [Host] (s : WhirStateW) (m0 : MachineData) (k : Nat) (st : MachineState) :
    Prop where
  at6 : At s m0 k NativeRustcVmX64.Vm.GlueLevel.b6Offset wrAll t5 (vA s m0) st
  cnt : Same m0.dmem st.data.dmem (off (pOf m0) 504) 8
  pt : BufEWAt st.data.dmem (off (pOf m0) (o1 s.glued.size + 40)) stackCap
    (slice m0 (reg m0 .r8) (reg m0 .r9)).toList

end

public section

variable {s : WhirStateW} {m0 : MachineData}

theorem toBitVec_toUInt64 (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

theorem pre_r8 (hpre : GlueLevelPre s m0) :
    SliceOk m0 (reg m0 .r8) (reg m0 .r9) glueLevelStack ∧
      Apart (pOf m0) stateBytes (reg m0 .r8) (16 * (reg m0 .r9).toNat) ∧
      (reg m0 .r9).toNat ≤ stackCap := by
  obtain ⟨-, -, -, -, -, h9, -, -, -, hs, -, -, -, ha, -, -⟩ := hpre
  exact ⟨hs, ha, h9⟩

variable [Host] {k : Nat}

/-- **From `b3` to `b6`.** -/
theorem first_step (hp : Placed code k)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hpre : GlueLevelPre s m0) {st : MachineState} (h : At s m0 k NativeRustcVmX64.Vm.GlueLevel.b3Offset noWr t3 (v3 s m0) st) :
    Eventually (step1 Host.exe) (AtB6 s m0 k) st := by
  obtain ⟨m3, pc3⟩ := st
  obtain ⟨hpc, hB⟩ := h
  simp only at hpc hB
  subst hpc
  have hl := lay hpre
  have hpnw := pre_pnw hpre
  have hn := pre_size hpre
  obtain ⟨⟨⟨h8m, h8w⟩, h8s⟩, h8a, h9⟩ := pre_r8 hpre
  have hc3 : Same m0.dmem m3.dmem (off (pOf m0) 504) 8 := keep_reg hpre hB.same rs_2 rfl
  have hw3 : WordAt m3.dmem (off (pOf m0) 504) s.glued.size.toUInt64 :=
    wordAt_keep0 hc3 le_rfl (pre_st hpre).glued_len
  have hcnt : ∀ ret, (envG s m0 m3 (v3 s m0) ret).load 3 0 8 = BitVec.ofNat 64 s.glued.size :=
    fun ret ↦ ldW (wordAt_add0 hw3)
  -- `b3`: the claim
  refine jumpStepA hl (hB.mono (wr := wrAll) fun _ h ↦ by cases h)
    (b3_in_code.trans hp.1 (by simp [b3])) run_b3 (fun _ h ↦ by cases h) ([1].contains ·)
    (sub_of _ (by simp)) (by rw [rs_sizes]; rfl) (T' := t4)
    (vals' := vA s m0) rfl rfl (fun ret ↦ by vtac0; exact hcnt ret) (by rw [rs_sizes]; rfl) rfl
    rfl t4_al (fun _ _ _ _ hx ↦ by rw [show t4.bounds = [] from rfl] at hx; cases hx)
    fun st4 hpc4 hB4 _ hloc4 ↦ ?_
  simp only [PcOk] at hpc4
  rw [above_false (by
    show ((envG s m0 m3 (v3 s m0) 0).load 3 0 8).toNat ≤ 9
    rw [hcnt, BitVec.toNat_ofNat]
    omega)] at hpc4
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4 hB4 hloc4
  subst hpc4
  rw [show k + NativeRustcVmX64.Vm.GlueLevel.b3Offset + b3.length = k + NativeRustcVmX64.Vm.GlueLevel.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.GlueLevel.b3_next]]
  have hc4 : Same m0.dmem d4.dmem (off (pOf m0) 504) 8 :=
    same_trans hc3 (keep_reg hpre hloc4 rs_2 rfl)
  have hal4 : WordAt d4.dmem (off (pOf m0) 16) s.alphas.size.toUInt64 := by
    have := (pre_st hpre).alphas.2.1
    rw [Array.length_toList] at this
    exact wordAt_keep0 (keep_reg hpre hB4.same rs_1 rfl) (by decide) this
  have hld2 : ∀ ret, (envG s m0 d4 (vA s m0) ret).load 2 0 8 = vA s m0 22 :=
    fun ret ↦ ldW (wordAt_add0 hal4)
  have hr5 := reg_info hpre rs_4
  -- `b4`: the first glued claim, `extend` of its point
  refine callStepA hl hB4 (b4_in_code.trans hp.1 (by simp [b4])) run_b4
    ([1, 4, 5].contains ·) (sub_of _ (by simp))
    (by rw [rs_sizes]; rfl) rfl hext (S := bufEWExtendStack) (by decide)
    (W := InRange (off (pOf m0) (o1 s.glued.size + 40)) 488) ?_ ?_
    (fun q hq ↦ ⟨4, _, by decide, rs_4, hq⟩) (T' := t5) (vals' := vA s m0) rfl rfl
    (fun ret ↦ by vtac0 <;> exact hld2 ret) (fun i hi ↦ by cases hi) (fun i hi ↦ by cases hi)
    (fun mc ret ↦ hl.notW rs_4 (by rfl) mc _ ret) (by rw [rs_sizes]; rfl) rfl rfl
    (fun m ret ↦ headA_al rfl m _ ret)
    (fun _ _ _ _ hx ↦ by rw [show t5.bounds = [] from rfl] at hx; cases hx)
    fun st5 hpc5 hB5 hex hloc5 ↦ ?_
  · -- the precondition of `extend`
    intro mc hm hk hst
    have hrdi : reg mc .rdi = off (pOf m0) (o1 s.glued.size + 40) :=
      (hm.regs .rdi _ rfl).trans (by addr_tac)
    have hrsi : reg mc .rsi = reg m0 .r8 := hm.regs .rsi _ rfl
    have hrdx : reg mc .rdx = reg m0 .r9 := hm.regs .rdx _ rfl
    have hrsp : rspOf mc = stackBelow m0 96 := (hm.regs .rsp _ rfl).trans (by
      show stackBelow m0 96 + BitVec.ofInt 64 0 = _
      simp)
    have hw0 : WordAt mc.dmem (reg mc .rdi) 0 := by
      have := NativeRustcVmX64.Transcript.wordAt_write hm (r := 5) (o := 0)
        (b := off (pOf m0) (o1 s.glued.size + 40)) (sz := 488) rfl (by decide)
        (v := .lit 0) (by decide)
      rw [hrdi, ← off_zero (off (pOf m0) (o1 s.glued.size + 40))]
      exact this
    refine ⟨hst, by rw [NativeRustcVm.wordOf_of_wordAt hw0]; decide, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrdi]
      exact ⟨fun j hj ↦ hk _ (hr5.1 j hj), hr5.2.1⟩
    · rw [hrsi, hrdx]
      exact ⟨fun j hj ↦ hk _ (h8m j hj), h8w⟩
    · rw [hrdi, hrsi, hrdx]
      exact apart_off_of hpnw (by decide) (by unfold stateBytes o1; omega) h8a
    · rw [hrdi]
      exact offStack_call hpre hrsp (by have := hr5.2.2; unfold Apart at this ⊢; omega)
        (by decide)
    · rw [hrsi, hrdx]
      exact offStack_call hpre hrsp h8s (by decide)
  · -- its frame
    intro mc m' hm hq
    have hrdi : reg mc .rdi = off (pOf m0) (o1 s.glued.size + 40) :=
      (hm.regs .rdi _ rfl).trans (by addr_tac)
    refine ⟨fun q hq' ↦ hq.2.1 q fun h ↦ hq' (h.elim (fun h1 ↦ .inr ?_) .inl), hq.2.2⟩
    rw [hrdi] at h1
    exact h1
  -- `b5`: `extend`'s `Some`
  obtain ⟨mc, hm, hlocm, hq⟩ := hex
  have hrdi : reg mc .rdi = off (pOf m0) (o1 s.glued.size + 40) :=
    (hm.regs .rdi _ rfl).trans (by addr_tac)
  have hrsi : reg mc .rsi = reg m0 .r8 := hm.regs .rsi _ rfl
  have hrdx : reg mc .rdx = reg m0 .r9 := hm.regs .rdx _ rfl
  have hw0 : WordAt mc.dmem (reg mc .rdi) 0 := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm (r := 5) (o := 0)
        (b := off (pOf m0) (o1 s.glued.size + 40)) (sz := 488) rfl (by decide)
      (v := .lit 0) (by decide)
    rw [hrdi, ← off_zero (off (pOf m0) (o1 s.glued.size + 40))]
    exact this
  have hpost := hq.1
  have hfit : (0 : UInt64).toNat + (reg mc .rdx).toNat ≤ 30 := by
    rw [hrdx]; unfold stackCap at h9; simp only [UInt64.toNat_zero]; omega
  rw [NativeRustcVm.wordOf_of_wordAt hw0, ite_eq_left hfit] at hpost
  obtain ⟨hal5, hbuf⟩ := hpost
  have hnil : NativeRustcVm.bufEWOf mc.dmem (reg mc .rdi) = [] := by
    unfold NativeRustcVm.bufEWOf
    rw [NativeRustcVm.wordOf_of_wordAt hw0]
    rfl
  have hsl : slice mc (reg mc .rsi) (reg mc .rdx) = slice m0 (reg m0 .r8) (reg m0 .r9) := by
    rw [hrsi, hrdx]
    unfold slice
    rw [NativeRustcVm.ewsOf_congr (d := m0.dmem) (same_trans
      (keep_out hpre hB4.same h8w h8s h8a) (keep_out hpre hlocm h8w h8s h8a))]
  rw [hnil, hsl, List.nil_append, hrdi] at hbuf
  obtain ⟨d5, pc5⟩ := st5
  simp only at hpc5 hB5 hloc5 hal5 hbuf
  subst hpc5
  rw [show k + NativeRustcVmX64.Vm.GlueLevel.b4Offset + b4.length = k + NativeRustcVmX64.Vm.GlueLevel.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.GlueLevel.b4_next]]
  refine jumpStepA hl hB5 (b5_in_code.trans hp.1 (by simp [b5])) run_b5 (fun _ h ↦ by cases h)
    ([1, 4].contains ·) (sub_of _ (by simp)) (by rw [rs_sizes]; rfl) (T' := t5) (vals' := vA s m0) rfl rfl
    (fun ret ↦ by vtac0) (by rw [rs_sizes]; rfl) rfl rfl (fun m ret ↦ headA_al rfl m _ ret)
    (fun _ _ _ _ hx ↦ by rw [show t5.bounds = [] from rfl] at hx; cases hx)
    fun st6 hpc6 hB6 _ hloc6 ↦ .done _ ⟨⟨?_, hB6⟩, ?_, ?_⟩
  · simp only [PcOk] at hpc6
    rw [al_false (by unfold boolRet at hal5; exact hal5)] at hpc6
    exact hpc6
  · exact same_trans hc4 (same_trans (keep_reg hpre hloc5 rs_2 rfl)
      (keep_reg hpre hloc6 rs_2 rfl))
  · exact bufEWAt_keep0 (keep_reg hpre hloc6 rs_4 rfl) (by decide) hbuf

end

end NativeRustcVmX64.Whir.GlueLevel
