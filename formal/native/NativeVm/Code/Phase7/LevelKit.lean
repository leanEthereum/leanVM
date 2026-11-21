module

public import NativeVm.Code.Phase7.Adapt
public import NativeVm.Code.Phase7.Init
public import NativeVm.Code.Phase7.FoldRounds
public import NativeVm.Code.Phase7.Params
public import NativeVm.Code.Phase7.Scalars
public import NativeVm.Code.Phase7.Sample
public import NativeVm.Code.Phase7.Query
public import NativeVm.Code.Phase7.Batch

/-!
# A level's pieces besides the delegated ones

`tableC`: the subspace table of `μ` (`cMu`) at `tabO`. `incC`: the next level's index and the
non-final levels left, in `r15` too. The words a level writes (`levelW`) and the facts it keeps
(`dep_*`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wdisp wd_inj wd_zero eval_cw wp_load wp_store wp_storei wp_reg ctxWork
  toUInt64_succ)

/-- The words a non-final level writes. -/
def levelW (j : Nat) : Prop :=
  (whirR.off ≤ j ∧ j < sc 0) ∨ j = sc 0 ∨ j = sc 1 ∨ (sc 3 ≤ j ∧ j < sc 8) ∨ (sc 27 ≤ j ∧ j < dataEnd)

/-- The subspace table of `μ` at `tabO`, its layers at `layO`. -/
def tableC : Stmt := blk [ldW, ldw .r15 cMu, leaw .r14 tabO, leaw .rbx layO, subTableC]

/-- The table's words. -/
def tableW (j : Nat) : Prop := (tabO ≤ j ∧ j < tabO + 62) ∨ (layO ≤ j ∧ j < layO + 30)

variable {p : Par} {s : QState} {F : QState → Prop}

theorem subTableC_writes_rdi : subTableC.writes .rdi = false := by decide +kernel

theorem tableC_core {mu : Nat} (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hmu : NatAt s.mem (wd p.env.work cMu) mu) (hmu30 : mu ≤ 30) :
    WP tableC s (fun s' ↦ TableAt s'.mem (wd p.env.work tabO) (subspaceTable mu) ∧
      ∀ a, (∀ k, tableW k → a ≠ wd p.env.work k) → s'.mem a = s.mem a) F := by
  have hsome : ∀ k, mineLo ≤ k → k < dataEnd → (s.mem (wd p.env.work k)).isSome := fun k h1 h2 ↦
    hin.workSome k (by have := workWords_ge p.inp.bytecode.size; rw [dataEnd_val] at h2; omega)
  unfold tableC ldW
  refine wp_load (eval_cw hrdi _) hwp ?_
  refine ldw_wp (env := p.env) (by simp) (by simpa using hmu.2) ?_
  refine wp_reg rfl (wp_reg rfl ?_)
  refine WP.blk_cons (WP.mono (subTableC_spec (T := wd p.env.work tabO) (L := wd p.env.work layO)
    hmu30 (by simp) (by simp only [QState.setReg_reg]; simp; exact eval_w (env := p.env) (by simp) _)
    (by simp only [QState.setReg_reg]; simp; exact eval_w (env := p.env) (by simp) _)
    (fun k hk ↦ by rw [wd_wd]; exact hsome _ (by oomega) (by oomega))
    (fun k hk ↦ by rw [wd_wd]; exact hsome _ (by oomega) (by oomega))
    (area_fits hin (by oomega) (by oomega)) (area_fits hin (by oomega) (by oomega))
    (area_disj hin (by oomega) (by oomega) (by oomega))) (fun s1 h1 ↦ ?_) (fun _ h ↦ h))
  refine WP.blk_nil ⟨h1.1, fun a ha ↦ ?_⟩
  refine h1.2 a (fun k hk e ↦ ha (tabO + k) (.inl ⟨by omega, by oomega⟩) (by rw [e, wd_wd]))
    (fun k hk e ↦ ha (layO + k) (.inr ⟨by omega, by oomega⟩) (by rw [e, wd_wd]))

/-- **The subspace table**, with its frame. -/
theorem tableC_spec {mu : Nat} (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hmu : NatAt s.mem (wd p.env.work cMu) mu) (hmu30 : mu ≤ 30) :
    WP tableC s (fun s' ↦ TableAt s'.mem (wd p.env.work tabO) (subspaceTable mu) ∧
      FrM p.env s s' ∧ Only p.env tableW s.mem s'.mem) F :=
  WP.mono (NativeVm.Transcript.WP.frame (tableC_core hrdi hin hwp hmu hmu30))
    (fun _ ⟨⟨h1, h2⟩, hd, hr⟩ ↦ ⟨h1,
      frM_of (hr .rdi (by unfold tableC; simp only [blk, Stmt.writes, subTableC_writes_rdi]; decide))
        hd h2 (fun k hk ↦ by unfold tableW at hk; oomega),
      fun k _ _ hk ↦ h2 _ fun j hj e ↦ hk (by
        have : j < 2 ^ 61 := by unfold tableW at hj; oomega
        have h' : k < 2 ^ 61 := by oomega
        rw [(wd_inj h' this).mp e]; exact hj)⟩) fun _ h ↦ h.1

/-! ## The ladder's queries -/

theorem ladder_queries_table : ∀ μ < 31, ∀ r < 5, Whir.Admissible μ r →
    ∀ lv ∈ toLevels ((ladderTable.getD (r - 1) []).getD (μ - 16) []), 1 ≤ lv.queries := by
  decide +kernel

/-- Every level queries at least one position. -/
theorem ladder_queries_pos {μ r : Nat} (hadm : Whir.Admissible μ r) {L : List Whir.Level}
    (h : Whir.ladder μ r = some L) : ∀ lv ∈ L, 1 ≤ lv.queries := by
  have hb := Admissible.bounds hadm
  rw [ladder_table μ (by omega) r (by omega) hadm, Option.some.injEq] at h
  exact h ▸ ladder_queries_table μ (by omega) r (by omega) hadm

end NativeVm.Code.P7
