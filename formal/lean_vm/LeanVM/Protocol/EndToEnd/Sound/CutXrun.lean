/-
  LeanVM.Protocol.EndToEnd.Sound.CutXrun

  The cut verifier's extracted run: wherever the ghost verifier's run returns, the cut's run from
  the same state returns the same value.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.CutRun
public import LeanVM.Protocol.EndToEnd.Sound.Extractor

/-!
# The cut verifier's run

`XCut H F p q`: wherever the extracted run of `p` (`xrun`, with the hash and permutation answers
`H`, `F`) returns a value, the extracted run of `q` from the same state and history returns it too.
Like `CutRel` it passes through a common prefix program (`XCut.bind`) and a final return
(`XCut.mapRet`), so the cut levels (`xcut_whirLevelsGF`) give the cut verifier
(`xcut_leanVmProgramG`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.KeccakHash

@[expose] public section

variable (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)

/-- **`q` cuts `p` on runs**: wherever `p`'s extracted run returns a value, `q`'s does. -/
def XCut {α : Type} (p q : VerifierProgram α) : Prop :=
  ∀ s h a s' hist, xrun H F p s h = some (a, s', hist) → ∃ s₁ h₁, xrun H F q s h = some (a, s₁, h₁)

variable {H F}

theorem XCut.bind {α β : Type} (p : VerifierProgram α) {f g : α → VerifierProgram β}
    (hfg : ∀ a, XCut H F (f a) (g a)) : XCut H F (p.bind f) (p.bind g) := by
  intro s h b s' hist hx
  rw [xrun_bind] at hx ⊢
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨s₁, h₁, hg⟩ := hfg r.1 _ _ _ _ _ hf
  exact ⟨s₁, h₁, by rw [hr, Option.bind_some, hg]⟩

theorem XCut.mapRet {α β : Type} {p q : VerifierProgram α} (hpq : XCut H F p q) (w : α → β) :
    XCut H F (p.bind fun a ↦ VerifierProgram.ret (w a)) (q.bind fun a ↦ VerifierProgram.ret (w a)) := by
  intro s h b s' hist hx
  rw [xrun_bind] at hx ⊢
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, -, -⟩ := hf
  obtain ⟨s₁, h₁, hq⟩ := hpq _ _ _ _ _ hr
  exact ⟨s₁, h₁, by rw [hq, Option.bind_some]; rfl⟩

/-- The full final step's run returns where the cut's does, with the same trace. -/
theorem xcut_fin (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) :
    XCut H F (finFull logN laneFolds eb index level s rounds) (finCut logN index level s rounds) := by
  intro st h a s' hist hx
  rw [finFull_eq, xrun_bind] at hx
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  rw [xrun_bind] at hf
  obtain ⟨r', -, hret⟩ := Option.bind_eq_some_iff.mp hf
  simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hret
  obtain ⟨rfl, -, -⟩ := hret
  exact ⟨r.2.1, r.2.2, hr⟩

/-- **The cut levels' run** returns where the full levels' does. -/
theorem xcut_whirLevelsGF (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      XCut H F (whirLevelsGF logN (finFull logN laneFolds eb) index levels s)
        (whirLevelsGF logN (finCut logN) index levels s)
  | _, [], _ => fun _ _ _ _ _ hx ↦ by simp [whirLevelsGF, xrun] at hx
  | index, [level], s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    exact XCut.bind _ fun r ↦ xcut_fin logN laneFolds eb index level r.1 r.2
  | index, level :: next :: rest, s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    refine XCut.bind _ fun r ↦ ?_
    rw [midTailC_eq_pre, midTailC_eq_pre]
    exact XCut.bind _ fun p ↦
      (xcut_whirLevelsGF logN laneFolds eb (index + 1) (next :: rest) p.2).mapRet
        fun tr ↦ WhirTrace.mid r.2 p.1 tr

theorem xcut_verifyStackedOpeningG (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    XCut H F (verifyStackedOpeningG stackLog logInvRate claims)
      (verifyStackedOpeningCut stackLog logInvRate claims) := by
  refine XCut.bind _ fun _ ↦ XCut.bind _ fun c ↦ ?_
  unfold verifyWhirG verifyWhirCut
  simp only [VerifierProgram.bind_eq]
  refine XCut.bind _ fun config ↦ ?_
  rw [whirLevelsG_eq]
  exact xcut_whirLevelsGF _ _ _ _ _ _

theorem xcut_veBodyG (ev : List K → List E → E → VerifierProgram Unit) (publicInput : Digest)
    (layout : Verifier.Layout) (ρ : ℕ) :
    XCut H F (veBodyG ev publicInput layout ρ) (veBodyCut ev publicInput layout ρ) := by
  unfold veBodyG veBodyCut
  simp only [VerifierProgram.bind_eq]
  refine XCut.bind _ fun _ ↦ XCut.bind _ fun ood ↦ XCut.bind _ fun r ↦ ?_
  obtain ⟨cl, kp, ks⟩ := r
  refine XCut.bind _ fun y ↦ ?_
  obtain ⟨t, w⟩ := y
  exact xcut_verifyStackedOpeningG _ _ _

/-- **The cut verifier's run** returns where the ghost verifier's does. -/
theorem xcut_leanVmProgramG (bytecode : List K) (pd : Digest) :
    XCut H F (leanVmProgramG bytecode pd) (leanVmProgramCut bytecode pd) :=
  (XCut.bind _ fun (a : Verifier.Layout × ℕ) ↦ (xcut_veBodyG _ pd a.1 a.2).mapRet
    fun tr ↦ (a, tr)).mapRet fun d ↦ (true, d)

end
end LeanVM.Protocol.EndToEnd.Sound
