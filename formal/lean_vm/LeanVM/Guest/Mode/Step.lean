module

public import LeanVM.Guest.Mode.SoundJoin
public import LeanVM.Guest.Mode.Abs
public import LeanVM.Guest.Mode.SoundEntry
public import LeanVM.Guest.Value.Tower
public import LeanVM.Prover.ExecuteComplete

/-!
# A function's certificate, and a `JUMP`'s values

A function's certificate (`Cert`: its program, its view and its code). `jump_vals`: a `JUMP` reads
three written cells, and falls through on `0` or goes where its target and frame cells name. The
residuals' cells written (`IdxIn`, `ResIn`), and the step's small lemmas.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-! ## What a `JUMP` does -/

theorem ofK_limbs {x : E} (h1 : x.limb 1 = 0) : x = ofK (x.limb 0) :=
  E.ext fun l ↦ by fin_cases l <;> simp [h1]

/-- A `JUMP` reads three written cells, and falls through on `0` or goes where its target and frame
cells name. -/
theorem jump_vals {C : Ctx} {s s' : St} {c d f : ℕ} (hs : s.Good)
    (e : runOp C s (.jump c d f) = .ok s') :
    ∃ vc vd vf, s.mem.get (s.fp + c) = some vc ∧ s.mem.get (s.fp + d) = some vd ∧
      s.mem.get (s.fp + f) = some vf ∧ s.mem ≤ s'.mem ∧
      ((vc = 0 ∧ s'.pc = s.pc + 1 ∧ s'.fp = s.fp) ∨
        (vc ≠ 0 ∧ vd = ofK (g ^ s'.pc) ∧ vf = ofK (g ^ s'.fp) ∧ s'.pc < C.ops.size ∧
          s'.fp < maxCells)) := by
  simp only [runOp, bind_ok] at e
  obtain ⟨ca, hca, cb, hcb, cc, hcc, wc, hwc, vc, hvc, wd, hwd, vd, hvd, wf, hwf, vf, hvf, s1, hs1,
    e⟩ := e
  obtain ⟨m, hm, rfl⟩ := St.withMem_ok hs1
  simp only [pure_ok] at hm; subst hm
  obtain ⟨rfl, -⟩ := cellAt_ok hca
  obtain ⟨rfl, -⟩ := cellAt_ok hcb
  obtain ⟨rfl, -⟩ := cellAt_ok hcc
  obtain ⟨hc1, rfl⟩ := inK_ok hvc
  obtain ⟨hd1, rfl⟩ := inK_ok hvd
  obtain ⟨hf1, rfl⟩ := inK_ok hvf
  have hle1 : s.mem ≤ ((s.mem.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f) :=
    Mem.le_trans (Mem.le_trans (Mem.le_ensure _ _) (Mem.le_ensure _ _)) (Mem.le_ensure _ _)
  have hwf1 := ((hs.wf.ensure (s.fp + c)).ensure (s.fp + d)).ensure (s.fp + f)
  refine ⟨wc, wd, wf, Mem.read_ok hwc, Mem.read_ok hwd, Mem.read_ok hwf, ?_⟩
  split_ifs at e with h0
  · simp only [pure_ok] at e; subst e
    exact ⟨hle1, Or.inl ⟨eq_zero_of_limbs h0 hc1, rfl, rfl⟩⟩
  · simp only [bind_ok, pure_ok] at e
    obtain ⟨⟨pc', s2⟩, h2, ⟨fp', s3⟩, h3, rfl⟩ := e
    obtain ⟨f2, hg2, hlt2⟩ := St.logOr_ok (by exact ⟨hwf1, hs.dl⟩) h2
    obtain ⟨f3, hg3, hlt3⟩ := St.logOr_ok f2.good h3
    refine ⟨Mem.le_trans hle1 (Mem.le_trans f2.le f3.le),
      Or.inr ⟨fun h ↦ h0 (by rw [h, limb_zero]), ?_, ?_, hlt2, hlt3⟩⟩
    · rw [ofK_limbs hd1, ← hg2]
    · rw [ofK_limbs hf1, ← hg3]

/-! ## Conditions -/

theorem imm_zero : OffsetInstruction.immediateWord 0 0 = 0 :=
  eq_zero_of_limbs (by simp [OffsetInstruction.immediateWord, show K.ofBits 0 = 0 from rfl])
    (by simp [OffsetInstruction.immediateWord, show K.ofBits 0 = 0 from rfl])

theorem imm_ne_zero {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : ¬(a = 0 ∧ b = 0)) :
    OffsetInstruction.immediateWord a b ≠ 0 := by
  intro h0
  have h1 := congrArg (·.limb 0) h0
  have h2 := congrArg (·.limb 1) h0
  simp only [OffsetInstruction.immediateWord, limb_ofLimbs, limb_zero] at h1 h2
  exact h ⟨Value.ofBits_inj ha (by norm_num) (h1.trans rfl), Value.ofBits_inj hb (by norm_num) (h2.trans rfl)⟩

/-! ## Residuals -/

/-- An exponent's base has a word. -/
def IdxIn (s : St) : Idx → Prop
  | .num _ => True
  | .ex b _ => ∃ v, BaseVal s b v

/-- A residual's cells are written. -/
def ResIn (s : St) : Res → Prop
  | .lt a b => IdxIn s a ∧ IdxIn s b
  | .nz o => s.mem.written (s.fp + o) = true
  | .sub a _ => IdxIn s a.lo ∧ IdxIn s a.hi
  | .name _ => True

/-! ## A function's certificate -/

/-- What one function's walk is: its program, its view, and its code. -/
structure Cert where
  E : Env
  F : Fun
  code : List OffsetInstruction

/-! ## The step -/

theorem Moves.refl' {M : ℕ → E} {s : St} (hs : Fine M s) : Moves M s s :=
  ⟨hs, Mem.le_refl _, rfl, rfl, rfl⟩

theorem fine_steps {M : ℕ → E} {s : St} (h : Fine M s) (n : ℕ) : Fine M { s with steps := n } :=
  ⟨h.agree, h.dl, h.small, h.fp⟩

end

end LeanVM.Guest.Mode
