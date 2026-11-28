module

public import NativeRustcVmX64.Whir.GlueLevel.Second
public import NativeRustcVmX64.Code.Vm.BufEW230Extend.Names

/-!
# `glue_level`: the second glued claim's weights and the count (x86-64)

`b9` calls `Buf<EW, 230>::extend` for the second glued claim's weights; `b10` checks its `Some`;
`b11` counts the second glued claim, sets AL to `1` and jumps to the epilogue. At `b13`
(`AtB13`): the template `t13`, the buffers the callees filled, AL `1`.
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Whir.Rows
open NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Vm.GlueLevel
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero toNat_off)

@[expose] public section

/-- The weights. -/
abbrev wsOf (m0 : MachineData) : List EW := (slice m0 (stackArg m0 4) (stackArg m0 5)).toList

/-- **At `b13`**: the template `t13`, the buffers, AL `1`. -/
structure AtB13 [Host] (s : WhirStateW) (m0 : MachineData) (k : Nat) (st : MachineState) :
    Prop where
  at13 : At s m0 k NativeRustcVmX64.Vm.GlueLevel.b13Offset wrAll t13 (vA s m0) st
  pt : BufEWAt st.data.dmem (off (pOf m0) (o1 s.glued.size + 40)) stackCap
    (slice m0 (reg m0 .r8) (reg m0 .r9)).toList
  qs : BufWordsAt st.data.dmem (off (pOf m0) (o2 s.glued.size + 528)) queryCap (qsOf m0)
  ws : BufEWAt st.data.dmem (off (pOf m0) (o2 s.glued.size + 2376)) queryCap (wsOf m0)
  al : (reg st.data .rax).toNat % 256 = 1

end

public section

variable {s : WhirStateW} {m0 : MachineData}

theorem pre_ws (hpre : GlueLevelPre s m0) :
    WhirIn m0 (stackArg m0 4) (16 * (stackArg m0 5).toNat) glueLevelStack ∧
      Apart (pOf m0) stateBytes (stackArg m0 4) (16 * (stackArg m0 5).toNat) ∧
      (stackArg m0 5).toNat ≤ queryCap := by
  obtain ⟨-, -, -, -, -, -, -, hn, -, -, -, hw, -, -, -, ha⟩ := hpre
  exact ⟨hw, ha, hn⟩

variable [Host] {k : Nat}

/-- **From `b9` to `b13`.** -/
theorem third_step (hp : Placed code k)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW230Extend.entryLabel) (BufEWExtendPre 230) (BufEWExtendPost 230))
    (hpre : GlueLevelPre s m0) {st : MachineState} (h : AtB9 s m0 k st) :
    Eventually (step1 Host.exe) (AtB13 s m0 k) st := by
  obtain ⟨⟨hpc, hB⟩, hpt9, hqs9⟩ := h
  obtain ⟨m9, pc9⟩ := st
  simp only at hpc hB hpt9 hqs9
  subst hpc
  have hl := lay hpre
  have hpnw := pre_pnw hpre
  have hn := pre_size hpre
  obtain ⟨⟨⟨hwm, hww⟩, hws⟩, hwa, hwn⟩ := pre_ws hpre
  have hr8 := reg_info hpre rs_7
  -- `b9`: `extend` of the weights
  refine callStepA hl hB (b9_in_code.trans hp.1 (by simp [b9])) run_b9
    ([1, 3, 4, 6, 8].contains ·) (sub_of _ (by simp)) (by rw [rs_sizes]; rfl) rfl hext
    (S := bufEWExtendStack) (by decide)
    (W := InRange (off (pOf m0) (o2 s.glued.size + 2376)) 3688) ?_ ?_
    (fun q hq ↦ ⟨7, _, by decide, rs_7, hq⟩) (T' := t10) (vals' := vA s m0) rfl rfl
    (fun ret ↦ by vtac0) (fun i hi ↦ by cases hi) (fun i hi ↦ by cases hi)
    (fun mc ret ↦ hl.notW rs_7 (by rfl) mc _ ret) (by rw [rs_sizes]; rfl) rfl rfl
    (fun m ret ↦ headA_al rfl m _ ret)
    (fun _ _ _ _ hx ↦ by rw [show t10.bounds = [] from rfl] at hx; cases hx)
    fun st10 hpc10 hB10 hex hloc10 ↦ ?_
  · -- the precondition of `extend`
    intro mc hm hk hst
    have hrdi : reg mc .rdi = off (pOf m0) (o2 s.glued.size + 2376) :=
      (hm.regs .rdi _ rfl).trans (by addr_tac)
    have hrsi : reg mc .rsi = stackArg m0 4 :=
      (hm.regs .rsi _ rfl).trans (hl.loadArg hB.same (i := 4) (by decide))
    have hrdx : reg mc .rdx = stackArg m0 5 :=
      (hm.regs .rdx _ rfl).trans (hl.loadArg hB.same (i := 5) (by decide))
    have hrsp : rspOf mc = stackBelow m0 96 := (hm.regs .rsp _ rfl).trans (by
      show stackBelow m0 96 + BitVec.ofInt 64 0 = _
      simp)
    have hw0 : WordAt mc.dmem (reg mc .rdi) 0 := by
      have := NativeRustcVmX64.Transcript.wordAt_write hm (r := 8) (o := 0)
        (b := off (pOf m0) (o2 s.glued.size + 2376)) (sz := 3688) rfl (by decide)
        (v := .lit 0) (by decide)
      rw [hrdi, ← off_zero (off (pOf m0) (o2 s.glued.size + 2376))]
      exact this
    refine ⟨hst, by rw [NativeRustcVm.wordOf_of_wordAt hw0]; decide, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrdi]
      exact ⟨fun j hj ↦ hk _ (hr8.1 j hj), hr8.2.1⟩
    · rw [hrsi, hrdx]
      exact ⟨fun j hj ↦ hk _ (hwm j hj), hww⟩
    · rw [hrdi, hrsi, hrdx]
      exact apart_off_of hpnw (by decide) (by unfold stateBytes o2; omega) hwa
    · rw [hrdi]
      exact offStack_call hpre hrsp (by have := hr8.2.2; unfold Apart at this ⊢; omega)
        (by decide)
    · rw [hrsi, hrdx]
      exact offStack_call hpre hrsp hws (by decide)
  · -- its frame
    intro mc m' hm hq
    have hrdi : reg mc .rdi = off (pOf m0) (o2 s.glued.size + 2376) :=
      (hm.regs .rdi _ rfl).trans (by addr_tac)
    refine ⟨fun q hq' ↦ hq.2.1 q fun h ↦ hq' (h.elim (fun h1 ↦ .inr ?_) .inl), hq.2.2⟩
    rw [hrdi] at h1
    exact h1
  -- `b10`: `extend`'s `Some`
  obtain ⟨mc, hm, hlocm, hq⟩ := hex
  have hrdi : reg mc .rdi = off (pOf m0) (o2 s.glued.size + 2376) :=
    (hm.regs .rdi _ rfl).trans (by addr_tac)
  have hrsi : reg mc .rsi = stackArg m0 4 :=
    (hm.regs .rsi _ rfl).trans (hl.loadArg hB.same (i := 4) (by decide))
  have hrdx : reg mc .rdx = stackArg m0 5 :=
    (hm.regs .rdx _ rfl).trans (hl.loadArg hB.same (i := 5) (by decide))
  have hw0 : WordAt mc.dmem (reg mc .rdi) 0 := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm (r := 8) (o := 0)
      (b := off (pOf m0) (o2 s.glued.size + 2376)) (sz := 3688) rfl (by decide)
      (v := .lit 0) (by decide)
    rw [hrdi, ← off_zero (off (pOf m0) (o2 s.glued.size + 2376))]
    exact this
  have hpost := hq.1
  have hfit : (0 : UInt64).toNat + (reg mc .rdx).toNat ≤ 230 := by
    rw [hrdx]; unfold queryCap at hwn; simp only [UInt64.toNat_zero]; omega
  rw [NativeRustcVm.wordOf_of_wordAt hw0, ite_eq_left hfit] at hpost
  obtain ⟨hal10, hbuf⟩ := hpost
  have hnil : NativeRustcVm.bufEWOf mc.dmem (reg mc .rdi) = [] := by
    unfold NativeRustcVm.bufEWOf
    rw [NativeRustcVm.wordOf_of_wordAt hw0]
    rfl
  have hsl : slice mc (reg mc .rsi) (reg mc .rdx) = slice m0 (stackArg m0 4) (stackArg m0 5) := by
    rw [hrsi, hrdx]
    unfold slice
    rw [NativeRustcVm.ewsOf_congr (d := m0.dmem) (same_trans
      (keep_out hpre hB.same hww hws hwa) (keep_out hpre hlocm hww hws hwa))]
  rw [hnil, hsl, List.nil_append, hrdi] at hbuf
  obtain ⟨d10, pc10⟩ := st10
  simp only at hpc10 hB10 hloc10 hal10 hbuf
  subst hpc10
  rw [show k + NativeRustcVmX64.Vm.GlueLevel.b9Offset + b9.length = k + NativeRustcVmX64.Vm.GlueLevel.b10Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.GlueLevel.b9_next]]
  have hpt10 := bufEWAt_keep0 (keep_reg hpre hloc10 rs_4 rfl) (by decide) hpt9
  have hqs10 := bufWordsAt_keep0 (keep_reg hpre hloc10 rs_6 rfl) (by decide) hqs9
  refine jumpStepA hl hB10 (b10_in_code.trans hp.1 (by simp [b10])) run_b10
    (fun _ h ↦ by cases h) ([1, 3, 4, 6].contains ·) (sub_of _ (by simp)) (by rw [rs_sizes]; rfl)
    (T' := t10) (vals' := vA s m0) rfl rfl (fun ret ↦ by vtac0) (by rw [rs_sizes]; rfl) rfl rfl
    (fun m ret ↦ headA_al rfl m _ ret)
    (fun _ _ _ _ hx ↦ by rw [show t10.bounds = [] from rfl] at hx; cases hx)
    fun st11 hpc11 hB11 _ hloc11 ↦ ?_
  simp only [PcOk] at hpc11
  rw [al_false (by unfold boolRet at hal10; exact hal10)] at hpc11
  obtain ⟨d11, pc11⟩ := st11
  simp only at hpc11 hB11 hloc11
  subst hpc11
  rw [show k + NativeRustcVmX64.Vm.GlueLevel.b10Offset + b10.length = k + NativeRustcVmX64.Vm.GlueLevel.b11Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.GlueLevel.b10_next]]
  -- `b11`: the count, AL
  refine jumpStepA hl hB11 (b11_in_code.trans hp.1 (by simp [b11])) run_b11
    (fun _ h ↦ by cases h) ([1, 3, 4, 6].contains ·) (sub_of _ (by simp)) (by rw [rs_sizes]; rfl)
    (T' := t13) (vals' := vA s m0) rfl rfl (fun ret ↦ by vtac0) (by rw [rs_sizes]; rfl) rfl rfl
    (fun m ret ↦ headA_al rfl m _ ret)
    (fun _ _ _ _ hx ↦ by rw [show t13.bounds = [] from rfl] at hx; cases hx)
    fun st13 hpc13 hB13 hm13 hloc13 ↦ .done _ ⟨⟨?_, hB13⟩, ?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc13
    rw [hpc13]
    exact hp.label NativeRustcVmX64.Vm.GlueLevel.label_11_at
  · exact bufEWAt_keep0 (same_trans (keep_reg hpre hloc11 rs_4 rfl)
      (keep_reg hpre hloc13 rs_4 rfl)) (by decide) hpt10
  · exact bufWordsAt_keep0 (same_trans (keep_reg hpre hloc11 rs_6 rfl)
      (keep_reg hpre hloc13 rs_6 rfl)) (by decide) hqs10
  · exact bufEWAt_keep0 (same_trans (keep_reg hpre hloc11 rs_7 rfl)
      (keep_reg hpre hloc13 rs_7 rfl)) (by decide) hbuf
  · rw [show reg st13.data .rax = _ from hm13.regs .rax _ rfl]
    exact NativeRustcVmX64.Transcript.merge_one_mod _

end

end NativeRustcVmX64.Whir.GlueLevel
