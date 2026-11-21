module

public import NativeVm.Code.Phase1.Tail
public import NativeVm.Code.Phase2.Kit

/-!
# Phase 1: the announced sizes and the layout

The code of `Model.readAnnouncedSizes`, proved against it (`phase1_ok : Phase1Ok phase1`).

`r14` holds the layout's address (`layoutR`) throughout. `readLoop` reads the eight announced
scalars (`readScalars 8`, one `readScalar` a pass), each low limb to layout word `9 + i`, the high
limbs `or`ed into `r13`; `tail` (`NativeVm.Code.Phase1.Code`) makes phase 1's checks and writes
the layout. The model's step is `readScalars 8` and then `tailP` of the scalars
(`readAnnouncedSizes_run`), which is the layout exactly when the checks hold (`tailP_eq`,
`tail_spec`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters LeanVM.Protocol.Verifier
open Phase1 (readLoop tail orC tailP TailOk layoutA rateA LFr LDom InL)

/-- **Phase 1**: the announced sizes and the layout. -/
def phase1 : Stmt := blk [
  I (.load .r14 (cw ctxWork)), I (.addi .r14 552),
  I (.movi .r12 0), I (.movi .r13 0),
  readLoop, tail]

/-- Phase 1's regions. -/
abbrev rs1 : List Region := [layoutR, scratchR]

theorem rs1_regions : ∀ r ∈ rs1, r ∈ regions := by decide

theorem layoutR_mem : layoutR ∈ regions := by decide

variable {env : Env} {inp : Input} {s0 s s' : QState} {t : TState}

/-- The layout's word `j`. -/
theorem layout_wd (env : Env) (j : Nat) :
    wd (layoutR.at env.work) j = wd env.work (layoutR.off + j) := by
  rw [Region.at, wd_wd]

/-! ## The model's state and the frame through the layout's writes -/

theorem codeRel_of_lfr (hc : CodeRel env t s) (hin : Inputs env inp s0.mem)
    (F : LFr (layoutR.at env.work) s s') : CodeRel env t s' := by
  obtain ⟨st, h1, h2, h3, h4⟩ := hc
  have hww := workWords_lt hin
  have hlt : ∀ k < 490, layoutR.off + k < workWords inp.bytecode.size := fun k hk ↦
    region_lt layoutR_mem (by rw [layoutR_size]; exact hk)
  refine ⟨st, h1, h2.congrW (by rw [F.rdi]; exact h2.rdi) F.dom (fun k hk ↦ ?_) (fun k hk ↦ ?_)
    (fun k hk ↦ ?_), h3, h4⟩
  · refine F.mem _ fun ⟨j, hj, e⟩ ↦ ?_
    rw [layout_wd] at e
    exact hin.ctx_ne_work (by rcases hk with hk | hk <;> lay_omega) (hlt j hj) e
  · refine F.mem _ fun ⟨j, hj, e⟩ ↦ ?_
    rw [layout_wd] at e
    exact wd_ne_of_disj h2.layout.fitDec hin.fitWork hin.disjDec hk (hlt j hj) e
  · refine F.mem _ fun ⟨j, hj, e⟩ ↦ ?_
    rw [layout_wd, layoutR_off] at e
    have := hlt j hj
    rw [layoutR_off] at this
    have hk' : k < 69 := by rw [Transcript.workWords_val] at hk; exact hk
    exact wd_ne_work (by omega) (by omega) (by omega) e

theorem base_of_lfr (hb : Base env rs1 s0 s) (F : LFr (layoutR.at env.work) s s') :
    Base env rs1 s0 s' :=
  ⟨⟨F.rdi.trans hb.1.1, fun a hf hr ↦ (F.mem a fun ⟨k, hk, e⟩ ↦ hr layoutR (by simp)
    ⟨k, by rw [layoutR_size]; exact hk, by rw [e, layout_wd]⟩).trans (hb.1.2 a hf hr)⟩,
    fun a ↦ (F.dom a).trans (hb.2 a)⟩

theorem ldom_of (hin : Inputs env inp s0.mem) (hb : Base env rs1 s0 s) :
    LDom (layoutR.at env.work) s.mem := fun k hk ↦ by
  rw [layout_wd]
  exact hin.region_some hb layoutR_mem (by rw [layoutR_size]; exact hk)

/-! ## Reading -/

/-- What the reading loop holds after `k` scalars `acc`. -/
def ReadX (env : Env) (k : Nat) (acc : Array EW) (s : QState) : Prop :=
  k ≤ 8 ∧ acc.size = k ∧ s.reg .r12 = k.toUInt64 ∧ s.reg .r13 = orC acc ∧
    s.reg .r14 = layoutR.at env.work ∧
    ∀ i < k, s.mem (wd (layoutR.at env.work) (9 + i)) = some (acc.getD i 0).c0

theorem readX_stable (hin : Inputs env inp s0.mem) (k : Nat) (acc : Array EW) :
    Stable env (ReadX env k acc) := fun s s' ⟨h1, h2, h3, h4, h5, h6⟩ hk ↦
  ⟨h1, h2, by rw [hk.reg (by decide)]; exact h3, by rw [hk.reg (by decide)]; exact h4,
    by rw [hk.reg (by decide)]; exact h5, fun i hi ↦ by
      rw [layout_wd, hin.keeps_region hk layoutR_mem (by rw [layoutR_size]; omega), ← layout_wd]
      exact h6 i hi⟩

/-- The reading loop's state after `k` scalars. -/
def ReadInv (env : Env) (s0 : QState) (k : Nat) (acc : Array EW) (t : TState) (s : QState) : Prop :=
  CodeRel env t s ∧ Fr env rs1 s0 (ReadX env k acc) s

theorem readBody (hin : Inputs env inp s0.mem) {k : Nat} (hk : k < 8) (acc : Array EW) :
    Refines (ReadInv env s0 k acc) (blk [Transcript.readScalar,
        I (.store ⟨.r14, some (.r12, .W64), wdisp 9⟩ .r9), I (.or .r13 .r10), I (.addi .r12 1)])
      (do pure (acc.push (← Model.readScalar)))
      (fun acc' t' s' ↦ ReadInv env s0 (k + 1) acc' t' s') (Kept env rs1 s0) := by
  refine Refines.blk_cons (readScalar_fr (readX_stable hin k acc)) fun x ↦ Refines.pure ?_
  rintro t s ⟨hc, ⟨hb, h1, h2, h3, h4, h5, h6⟩, h9, h10⟩
  have hj : 9 + k < layoutR.size := by rw [layoutR_size]; omega
  refine wp_store_rel (q := layoutR) (by simp) layoutR_mem hin hj (by
    rw [eval_idx64 (j := layoutR.off) (by rw [h5]; rfl) h3 9]
    exact congrArg (wd env.work) (by omega)) hc hb fun hc2 hb2 ↦ ?_
  refine wp_reg_rel rfl (by decide) hc2 hb2 fun hc3 hb3 ↦ ?_
  refine wp_reg_rel rfl (by decide) hc3 hb3 fun hc4 hb4 ↦ ?_
  refine WP.blk_nil ⟨hc4, hb4, by omega, by rw [Array.size_push, h2], by reg_simp; rw [h3, toUInt64_succ],
    by reg_simp; rw [h4, h10, Phase1.orC_push], by reg_simp; exact h5, fun i hi ↦ ?_⟩
  reg_simp
  rw [← layout_wd]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [setMem_wd_ne _ _ (by omega) (by omega) (by omega), h6 i hi]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, h2, Nat.ne_of_lt hi]
  · rw [setMem_wd_eq _ _ rfl, h9]
    subst h2
    simp [Array.getD_eq_getD_getElem?]

theorem readLoop_refines (hin : Inputs env inp s0.mem) :
    Refines (ReadInv env s0 0 #[]) readLoop (readScalars 8)
      (fun acc t s ↦ ReadInv env s0 8 acc t s) (Kept env rs1 s0) := by
  have := Refines.foldlM (l := List.range 8) (init := (#[] : Array EW))
    (f := fun acc _ ↦ do pure (acc.push (← Model.readScalar)))
    (cond := .cmp .ltu .r12 (.imm 8))
    (body := blk [Transcript.readScalar,
        I (.store ⟨.r14, some (.r12, .W64), wdisp 9⟩ .r9), I (.or .r13 .r10), I (.addi .r12 1)])
    (Inv := ReadInv env s0) (E := Kept env rs1 s0)
    (fun k acc t s ⟨_, _, h1, _, h3, _⟩ ↦ by
      rw [List.length_range, Phase1.cmp_ltu_w (k := 8) (ki := 8) rfl h3, toNat_toUInt64 (by omega),
        decide_eq_true_iff])
    (fun k hk acc ↦ readBody hin (by simpa using hk) acc)
  rwa [List.length_range] at this

/-! ## The contract -/

theorem phase1_run (bc : Array UInt64) (t : TState) :
    (readScalars 8 >>= fun a ↦ Model.liftOpt (tailP bc a)).run t =
      (Model.readAnnouncedSizes bc).run t := by
  rw [Phase1.readAnnouncedSizes_run, StateT.run_bind]
  show _ = ((readScalars 8).run t).bind _
  cases (readScalars 8).run t with
  | none => rfl
  | some r => exact Refines.liftOpt_run _ _

/-- **Phase 1 computes `readAnnouncedSizes`.** -/
theorem phase1_ok : Phase1Ok phase1 := by
  intro env inp t0 s0 hc hin
  apply runs_of_refines
  refine Refines.of_run (phase1_run inp.bytecode) ?_
  rintro t s ⟨rfl, rfl⟩
  unfold phase1
  refine wp_load (eval_cw hc.rdi _) hc.layout.workPtr ?_
  fstep; fstep; fstep
  have hb0 : Base env rs1 s (((((s.setReg .r14 env.work).setReg .r14 (env.work + 552)).setReg
      .r12 0).setReg .r13 0)) :=
    (((Base.start hc.rdi).setReg (d := .r14) (by decide) _).setReg (d := .r14) (by decide) _
      |>.setReg (d := .r12) (by decide) _ |>.setReg (d := .r13) (by decide) _)
  refine (Refines.blk_cons (readLoop_refines hin) fun a ↦ Refines.liftOpt ?_) t _
    ⟨(((hc.setReg (r := .r14) (by decide) _).setReg (r := .r14) (by decide) _).setReg (r := .r12)
      (by decide) _).setReg (r := .r13) (by decide) _,
      hb0, by omega, rfl, by reg_simp; rfl, by reg_simp; rfl, by reg_simp; rfl,
      fun i hi ↦ absurd hi (by omega)⟩
  rintro t s ⟨hc1, hb1, -, h2, -, h4, h5, h6⟩
  have hn := hin.bcLen
  have hlen : s.mem (wd env.ctx ctxBytecodeLen) = some inp.bytecode.size.toUInt64 :=
    (hb1.1.ctx hin (fun r hr ↦ stop_le_of_mem (rs1_regions r hr) _)
      (by unfold ctxBytecodeLen; rw [scratchW_val]; omega)).trans hn.2
  refine WP.mono (Phase1.tail_spec h5 hc1.rdi hlen hn.1 (ldom_of hin hb1) h2 h6 h4)
    (fun s' ⟨ok, lay, F⟩ ↦ ⟨(layoutA inp.bytecode a, rateA a), ?_, codeRel_of_lfr hc1 hin F, lay,
      (base_of_lfr hb1 F).1⟩)
    (fun s' ⟨nok, F⟩ ↦ ⟨?_, (base_of_lfr hb1 F).1⟩)
  · rw [Phase1.tailP_eq _ _ h2]; simp [ok]
  · rw [Phase1.tailP_eq _ _ h2]; simp [nok]

/-- info: 'NativeVm.Code.phase1_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phase1_ok

end NativeVm.Code
