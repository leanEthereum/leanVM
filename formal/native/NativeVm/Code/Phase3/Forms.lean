module

public import NativeVm.Code.Phase3.FormsRun

/-!
# Phase 3: the bus forms of a side

`formsCode side`: `accumulateSide`'s forms and padding rows' sum for one side (`sideFold`), the
side's table blocks being the literal data `sideD side` (`FormsData*`, checked against the
statement's tables). `forms_spec`: from the side's selectors (`tselR side`), padding weights
(`padWR side`), slot weights (`wR`) and `β` (`betaR`), the side's forms in `busR` (empty before) and
the sum in `sumR side`; it writes only `busR` (the side's forms), `sumR side` and `formTmpR`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters LeanVM.Protocol.Verifier

/-- **The forms of a side.** -/
def formsCode (side : Nat) : Stmt := formsWith side (sideD side)

theorem formTmpR_off : formTmpR.off = 60862 := ftOff_val

/-- **The forms of a side** (`sideFold`). -/
theorem forms_spec {env : Env} {inp : Input} {s : QState} {layout : LayoutW} {rate side : Nat}
    {forms : Array (Array FormW)} {sels pws weights : Array EW} {beta : EW} (hside : side < 3)
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx ctxWork) = some env.work)
    (hi : Inputs env inp s.mem) (hl : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hf : FormsAt s.mem (busR.at env.work) forms)
    (he : ∀ t < nTables, (forms.getD t #[]).getD side #[] = #[])
    (hts : EWArr s.mem ((tselR side).at env.work) sels) (hsz : sels.size = (sideBlocks layout side).size)
    (hpw : EWArr s.mem ((padWR side).at env.work) pws) (hpsz : pws.size = (sideBlocks layout side).size)
    (hw : side < 2 → EWArr s.mem (wR.at env.work) weights ∧ weights.size = 2 ^ busBits)
    (hb : side < 2 → EWAt s.mem (betaR.at env.work) beta) :
    WP (formsCode side) s (fun s' ↦
        FormsAt s'.mem (busR.at env.work) (sideFold forms side (sideBlocks layout side) sels pws
          (sideWeights weights side) (sideBeta beta side)).1 ∧
        EWAt s'.mem ((sumR side).at env.work) (sideFold forms side (sideBlocks layout side) sels pws
          (sideWeights weights side) (sideBeta beta side)).2 ∧
        Wrote env [busR, sumR side, tmpR, formTmpR] s s') (fun _ ↦ False) := by
  obtain ⟨rows, -, -, hbb⟩ := hl.rows
  have hbl := sideBlocks_ents hbb hside
  have hD := dOk_sideD hside
  have hlen : (sideBlocks layout side).size = (sideD side).length := by
    simpa using congrArg List.length hbl
  have hwk := dataEnd_le inp.bytecode.size
  have hfit := workWords_lt hi
  have hcw : ∀ k < dataEnd, wd env.ctx ctxWork ≠ wd env.work k := fun k hk ↦
    hi.ctx_ne_work (by rw [ctxEnd_val]; decide) (by omega)
  have hdom : ∀ k < dataEnd, (s.mem (wd env.work k)).isSome := fun k hk ↦ hi.workSome k (by omega)
  have v1 := fs_tselR_off side
  have v2 := fs_padWR_off side
  have v3 := sumR_off side
  have v4 := busR_off
  have v5 := busR_size
  have v6 := formTmpR_off
  have v7 := ftOff_val
  have v8 := dataEnd_eq
  have hbits : (2 : Nat) ^ busBits = 16 := rfl
  have ea : ∀ {mem : UInt64 → Option UInt64} {r : Region} {xs : Array EW}, EWArr mem (r.at env.work) xs →
      ∀ j (h : j < xs.size), EAtI mem env.work (r.off + 2 * j) xs[j] := fun h j hj ↦
    ⟨by have := (h j hj).1; rwa [Region.at, wd_wd] at this,
     by have := (h j hj).2; rwa [Region.at, wd_wd, wd_wd] at this⟩
  unfold formsCode
  refine WP.mono (WP.frame (formsWith_spec (E := fun _ ↦ False) (w := env.work) (ctx := env.ctx)
    (side := side) (D := sideD side) (blocks := sideBlocks layout side) (sels := sels) (pws := pws)
    (ws := sideWeights weights side) (β := sideBeta beta side) (forms := forms)
    hside hD hcw hbl hsz hpsz hrdi hwp hdom (ea hts)
    (fun j hj ↦ by have := ea hpw j hj; rwa [v2] at this)
    (fun h2 j hj ↦ by
      obtain ⟨hw1, hw2⟩ := hw (by omega)
      unfold sideWeights; rw [iteF h2]
      have := ea hw1 j (by omega)
      rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)])
    (fun h2 ↦ by subst h2; rfl)
    (fun h2 ↦ by
      unfold sideBeta; rw [iteF h2]
      have := hb (by omega)
      exact ⟨by have := this.1; rwa [Region.at] at this,
        by have := this.2; rwa [Region.at, wd_wd] at this⟩)
    (fun h2 ↦ by subst h2; rfl)
    (fun t ht ↦ ⟨by
      have := (hf.2.2 t ht side hside).2.1
      rw [he t ht] at this
      rw [Region.at, wd_wd] at this
      exact this.2, he t ht⟩)
    ⟨hf.1, hf.2.1⟩))
    (fun s' ⟨hI, hdm, _⟩ ↦ ?_) (fun _ h ↦ h.1)
  have hacc := accI_all (forms := forms) (side := side) (ws := sideWeights weights side)
    (β := sideBeta beta side) hsz hpsz
  rw [hlen] at hacc
  rw [← hacc]
  refine ⟨⟨hI.ok.1, hI.ok.2, fun t ht s₁ hs₁ ↦ ?_⟩, ?_, ⟨?_, fun a ha ↦ ?_, hdm⟩⟩
  · by_cases h1 : s₁ = side
    · subst h1
      rw [Region.at, wd_wd]
      exact (hI.fz t ht).formAt le_rfl
    · rw [hI.other t s₁ h1]
      refine (hf.2.2 t ht s₁ hs₁).congr fun k hk ↦ ?_
      have := formOff_eq t s₁
      have hk' : k < 741 := hk
      rw [Region.at, wd_wd, wd_wd]
      refine hI.keep.word (by unfold nTables at ht; omega) fun j hj ↦ ⟨?_, ?_⟩
      · unfold W at hj; obtain ⟨t', ht', h1', h2'⟩ | h | h | h := hj <;>
          (try have := formOff_eq t' side) <;> (try unfold nTables at ht') <;> unfold formCap at * <;>
          omega
      · unfold W at hj
        obtain ⟨t', ht', h1', h2'⟩ | h | h | h := hj
        · have := formOff_eq t' side
          unfold nTables at ht ht'; unfold formCap at h2'
          omega
        all_goals (unfold nTables at ht; omega)
  · have := hI.sum
    exact ⟨by rw [Region.at]; exact this.1, by rw [Region.at, wd_wd]; exact this.2⟩
  · rw [hI.rdi, hrdi]
  · refine hI.keep a fun k hk e ↦ ?_
    subst e
    unfold W at hk
    obtain ⟨t', ht', h1', h2'⟩ | h | h | h := hk
    · have := formOff_eq t' side
      unfold nTables at ht'; unfold formCap at h2'
      exact ha busR (by simp) ⟨k - busR.off, by omega, by rw [show busR.off + (k - busR.off) = k by omega]⟩
    · exact ha (sumR side) (by simp) ⟨0, by show 0 < 8; omega, by rw [Nat.add_zero, h]⟩
    · exact ha (sumR side) (by simp) ⟨1, by show 1 < 8; omega, by rw [h]⟩
    · exact ha formTmpR (by simp) ⟨k - formTmpR.off, by show _ < 24576; omega,
        by rw [show formTmpR.off + (k - formTmpR.off) = k by omega]⟩

end NativeVm.Code.P3
