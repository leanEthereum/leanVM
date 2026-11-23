module

public import NativeRustcVmX64.Whir.GlueLevel.First
public import NativeRustcVmX64.Code.Vm.BufU64x230Extend.Names

/-!
# `glue_level`: the second glued claim's header and queries (x86-64)

`b6` counts the first glued claim and checks the count; `b7` writes the second glued claim's
header and calls `Buf<u64, 230>::extend` for its queries; `b8` checks its `Some`. At `b9`
(`AtB9`): the template `t8`, the first glued claim's point and the second's queries.
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Whir.Rows
open NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Vm.GlueLevel
open NativeRustcVm (WordAt EWAt BufEWAt BufWordsAt)
open NativeRustcVm.Transcript (off off_off off_zero toNat_off)

@[expose] public section

/-- The queries. -/
abbrev qsOf (m0 : MachineData) : List UInt64 :=
  NativeRustcVm.wordsOf m0.dmem (stackArg m0 2) (stackArg m0 3).toNat

/-- **At `b9`**: the template `t8`, the first glued claim's point, the second's queries. -/
structure AtB9 [Host] (s : WhirStateW) (m0 : MachineData) (k : Nat) (st : MachineState) :
    Prop where
  at9 : At s m0 k NativeRustcVmX64.Vm.GlueLevel.b9Offset wrAll t8 (vA s m0) st
  pt : BufEWAt st.data.dmem (off (pOf m0) (o1 s.glued.size + 40)) stackCap
    (slice m0 (reg m0 .r8) (reg m0 .r9)).toList
  qs : BufWordsAt st.data.dmem (off (pOf m0) (o2 s.glued.size + 528)) queryCap (qsOf m0)

end

public section

variable {s : WhirStateW} {m0 : MachineData}

theorem pre_qs (hpre : GlueLevelPre s m0) :
    WhirIn m0 (stackArg m0 2) (8 * (stackArg m0 3).toNat) glueLevelStack ∧
      Apart (pOf m0) stateBytes (stackArg m0 2) (8 * (stackArg m0 3).toNat) ∧
      (stackArg m0 3).toNat ≤ queryCap := by
  obtain ⟨-, -, -, -, -, -, hq, -, -, -, hw, -, -, -, ha, -⟩ := hpre
  exact ⟨hw, ha, hq⟩

variable [Host] {k : Nat}

/-- **From `b6` to `b9`.** -/
theorem second_step (hp : Placed code k)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufU64x230Extend.entryLabel) (BufU64ExtendPre 230) (BufU64ExtendPost 230))
    (hpre : GlueLevelPre s m0) {st : MachineState} (h : AtB6 s m0 k st) :
    Eventually (step1 Host.exe) (AtB9 s m0 k) st := by
  obtain ⟨⟨hpc, hB⟩, hc6, hpt6⟩ := h
  obtain ⟨m6, pc6⟩ := st
  simp only at hpc hB hc6 hpt6
  subst hpc
  have hl := lay hpre
  have hpnw := pre_pnw hpre
  have hn := pre_size hpre
  obtain ⟨⟨⟨hqm, hqw⟩, hqs⟩, hqa, hqn⟩ := pre_qs hpre
  have hw6 : WordAt m6.dmem (off (pOf m0) 504) s.glued.size.toUInt64 :=
    wordAt_keep0 hc6 le_rfl (pre_st hpre).glued_len
  have hcnt : ∀ ret, (envG s m0 m6 (vA s m0) ret).load 3 0 8 = BitVec.ofNat 64 s.glued.size :=
    fun ret ↦ ldW (wordAt_add0 hw6)
  -- `b6`: the count
  refine jumpStepA hl hB (b6_in_code.trans hp.1 (by simp [b6])) run_b6 (fun _ h ↦ by cases h)
    ([1, 3, 4].contains ·) (sub_of _ (by simp)) (by rw [rs_sizes]; rfl) (T' := t7)
    (vals' := vA s m0) rfl rfl (fun ret ↦ by vtac0 <;> (rw [hcnt ret]; rfl)) (by rw [rs_sizes]; rfl) rfl rfl t7_al
    (fun _ _ _ _ hx ↦ by rw [show t7.bounds = [] from rfl] at hx; cases hx)
    fun st7 hpc7 hB7 _ hloc7 ↦ ?_
  simp only [PcOk] at hpc7
  rw [above_false (by
    show ((envG s m0 m6 (vA s m0) 0).load 3 0 8 + BitVec.ofNat 64 1).toNat ≤ 9
    rw [hcnt, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega)] at hpc7
  obtain ⟨d7, pc7⟩ := st7
  simp only at hpc7 hB7 hloc7
  subst hpc7
  rw [show k + NativeRustcVmX64.Vm.GlueLevel.b6Offset + b6.length = k + NativeRustcVmX64.Vm.GlueLevel.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.GlueLevel.b6_next]]
  have hpt7 := bufEWAt_keep0 (keep_reg hpre hloc7 rs_4 rfl) (by decide) hpt6
  have hr7 := reg_info hpre rs_6
  -- `b7`: the second glued claim's header, `extend` of its queries
  refine callStepA hl hB7 (b7_in_code.trans hp.1 (by simp [b7])) run_b7
    ([1, 3, 4, 6, 7].contains ·) (sub_of _ (by simp)) (by rw [rs_sizes]; rfl) rfl hext
    (S := bufU64ExtendStack) (by decide)
    (W := InRange (off (pOf m0) (o2 s.glued.size + 528)) 1848) ?_ ?_
    (fun q hq ↦ ⟨6, _, by decide, rs_6, hq⟩) (T' := t8) (vals' := vA s m0) rfl rfl
    (fun ret ↦ by vtac0) (fun i hi ↦ by cases hi) (fun i hi ↦ by cases hi)
    (fun mc ret ↦ hl.notW rs_6 (by rfl) mc _ ret) (by rw [rs_sizes]; rfl) rfl rfl t8_al
    (fun _ _ _ _ hx ↦ by rw [show t8.bounds = [] from rfl] at hx; cases hx)
    fun st8 hpc8 hB8 hex hloc8 ↦ ?_
  · -- the precondition of `extend`
    intro mc hm hk hst
    have hrdi : reg mc .rdi = off (pOf m0) (o2 s.glued.size + 528) :=
      (hm.regs .rdi _ rfl).trans (by addr_tac)
    have hrsi : reg mc .rsi = stackArg m0 2 :=
      (hm.regs .rsi _ rfl).trans (hl.loadArg hB7.same (i := 2) (by decide))
    have hrdx : reg mc .rdx = stackArg m0 3 :=
      (hm.regs .rdx _ rfl).trans (hl.loadArg hB7.same (i := 3) (by decide))
    have hrsp : rspOf mc = stackBelow m0 96 := (hm.regs .rsp _ rfl).trans (by
      show stackBelow m0 96 + BitVec.ofInt 64 0 = _
      simp)
    have hw0 : WordAt mc.dmem (reg mc .rdi) 0 := by
      have := NativeRustcVmX64.Transcript.wordAt_write hm (r := 7) (o := 0)
        (b := off (pOf m0) (o2 s.glued.size + 528)) (sz := 1848) rfl (by decide)
        (v := .lit 0) (by decide)
      rw [hrdi, ← off_zero (off (pOf m0) (o2 s.glued.size + 528))]
      exact this
    refine ⟨hst, by rw [NativeRustcVm.wordOf_of_wordAt hw0]; decide, ?_, ?_, ?_, ?_⟩
    · rw [hrdi]
      exact ⟨fun j hj ↦ hk _ (hr7.1 j hj), hr7.2.1⟩
    · rw [hrsi, hrdx]
      exact ⟨fun j hj ↦ hk _ (hqm j hj), hqw⟩
    · rw [hrdi, hrsi, hrdx]
      exact apart_off_of hpnw (by decide) (by unfold stateBytes o2; omega) hqa
    · rw [hrdi]
      exact offStack_call hpre hrsp (by have := hr7.2.2; unfold Apart at this ⊢; omega)
        (by decide)
  · -- its frame
    intro mc m' hm hq
    have hrdi : reg mc .rdi = off (pOf m0) (o2 s.glued.size + 528) :=
      (hm.regs .rdi _ rfl).trans (by addr_tac)
    refine ⟨fun q hq' ↦ hq.2.1 q fun h ↦ hq' (h.elim (fun h1 ↦ .inr ?_) .inl), hq.2.2⟩
    rw [hrdi] at h1
    exact h1
  -- `b8`: `extend`'s `Some`
  obtain ⟨mc, hm, hlocm, hq⟩ := hex
  have hrdi : reg mc .rdi = off (pOf m0) (o2 s.glued.size + 528) :=
    (hm.regs .rdi _ rfl).trans (by addr_tac)
  have hrsi : reg mc .rsi = stackArg m0 2 :=
    (hm.regs .rsi _ rfl).trans (hl.loadArg hB7.same (i := 2) (by decide))
  have hrdx : reg mc .rdx = stackArg m0 3 :=
    (hm.regs .rdx _ rfl).trans (hl.loadArg hB7.same (i := 3) (by decide))
  have hw0 : WordAt mc.dmem (reg mc .rdi) 0 := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm (r := 7) (o := 0)
      (b := off (pOf m0) (o2 s.glued.size + 528)) (sz := 1848) rfl (by decide)
      (v := .lit 0) (by decide)
    rw [hrdi, ← off_zero (off (pOf m0) (o2 s.glued.size + 528))]
    exact this
  have hpost := hq.1
  have hfit : (0 : UInt64).toNat + (reg mc .rdx).toNat ≤ 230 := by
    rw [hrdx]; unfold queryCap at hqn; simp only [UInt64.toNat_zero]; omega
  rw [NativeRustcVm.wordOf_of_wordAt hw0, ite_eq_left hfit] at hpost
  obtain ⟨hal8, hbuf⟩ := hpost
  have hnil : NativeRustcVm.bufWordsOf mc.dmem (reg mc .rdi) = [] := by
    unfold NativeRustcVm.bufWordsOf
    rw [NativeRustcVm.wordOf_of_wordAt hw0]
    rfl
  have hws : NativeRustcVm.wordsOf mc.dmem (reg mc .rsi) (reg mc .rdx).toNat = qsOf m0 := by
    rw [hrsi, hrdx]
    exact NativeRustcVm.wordsOf_congr (same_trans
      (keep_out hpre hB7.same hqw hqs hqa) (keep_out hpre hlocm hqw hqs hqa))
  rw [hnil, hws, List.nil_append, hrdi] at hbuf
  obtain ⟨d8, pc8⟩ := st8
  simp only at hpc8 hB8 hloc8 hal8 hbuf
  subst hpc8
  rw [show k + NativeRustcVmX64.Vm.GlueLevel.b7Offset + b7.length = k + NativeRustcVmX64.Vm.GlueLevel.b8Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.GlueLevel.b7_next]]
  refine jumpStepA hl hB8 (b8_in_code.trans hp.1 (by simp [b8])) run_b8 (fun _ h ↦ by cases h)
    ([1, 3, 4, 6].contains ·) (sub_of _ (by simp)) (by rw [rs_sizes]; rfl) (T' := t8) (vals' := vA s m0)
    rfl rfl (fun ret ↦ by vtac0) (by rw [rs_sizes]; rfl) rfl rfl t8_al
    (fun _ _ _ _ hx ↦ by rw [show t8.bounds = [] from rfl] at hx; cases hx)
    fun st9 hpc9 hB9 _ hloc9 ↦ .done _ ⟨⟨?_, hB9⟩, ?_, ?_⟩
  · simp only [PcOk] at hpc9
    rw [al_false (by unfold boolRet at hal8; exact hal8)] at hpc9
    exact hpc9
  · exact bufEWAt_keep0 (same_trans (keep_reg hpre hloc8 rs_4 rfl)
      (keep_reg hpre hloc9 rs_4 rfl)) (by decide) hpt7
  · exact bufWordsAt_keep0 (keep_reg hpre hloc9 rs_6 rfl) (by decide) hbuf

end

end NativeRustcVmX64.Whir.GlueLevel
