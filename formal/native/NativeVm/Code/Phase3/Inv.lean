module

public import NativeVm.Code.Phase3.Frame
public import NativeVm.Code.Refine

/-!
# Phase 3's run, step by step

Every state of the run holds `Base`: the code holds the model's state (`CodeRel`), the inputs and
the layout survive, and every word outside phase 3's regions is the start's (`Kept`). A step of the
run writes regions of phase 3 (`Ok3`) and keeps `Base` (`Base.step`); a step of the model is a
refinement from `Base` and the facts the step needs to `Base` and the facts after it (`ref3`), code
with no model step a run from one to the other (`pre3`). Failures keep `Kept`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

variable {env : Env} {inp : Input} {s0 : QState} {layout : LayoutW} {rate : Nat}

/-- **What every state of phase 3's run holds.** -/
structure Base (env : Env) (inp : Input) (s0 : QState) (layout : LayoutW) (rate : Nat) (t : TState)
    (s : QState) : Prop where
  rel : CodeRel env t s
  hin : Inputs env inp s.mem
  kept : Kept env rs3 s0 s
  lay : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate

theorem layoutR_stop_le {r : Region} (h : Ok3 r) : layoutR.stop ≤ r.off := by
  have e : layoutR.stop = 559 := by decide
  rw [e]
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [busR_off] at h1; omega
  · rw [claimsR_off] at h1; omega
  · rw [scratchR_off] at h1; omega

theorem Base.rdi {t : TState} {s : QState} (h : Base env inp s0 layout rate t s) :
    s.reg .rdi = env.ctx := h.kept.1

theorem Base.wp {t : TState} {s : QState} (h : Base env inp s0 layout rate t s) :
    s.mem (wd env.ctx ctxWork) = some env.work := h.rel.workPtr3

/-- What a failing step keeps. -/
theorem Base.fail {t : TState} {s s' : QState} {regs : List Reg64} {ws : List Region}
    (h : Base env inp s0 layout rate t s) (hws : ∀ r ∈ ws, Ok3 r) (hs : Step3 env regs ws s s') :
    Kept env rs3 s0 s' :=
  h.kept.trans ((hs.kept h.rdi).ok3 hws)

/-- **A step keeps `Base`.** -/
theorem Base.step {t t' : TState} {s s' : QState} {regs : List Reg64} {ws : List Region}
    (h : Base env inp s0 layout rate t s) (hws : ∀ r ∈ ws, Ok3 r) (hs : Step3 env regs ws s s')
    (hc : CodeRel env t' s') : Base env inp s0 layout rate t' s' := by
  refine ⟨hc, h.hin.step3 hws hs h.rdi, h.fail hws hs, h.lay.congr ?_⟩
  have := hs.same h.hin hws (ok0_of_mem (q := layoutR) (by simp [regions]))
    fun r hr ↦ Or.inl (layoutR_stop_le (hws r hr))
  exact this

/-- A run of code with no transcript step is a step. -/
theorem Base.wrote {t : TState} {s s' : QState} {ws : List Region}
    (h : Base env inp s0 layout rate t s) (hws : ∀ r ∈ ws, Ok3 r) (hw : Wrote env ws s s') :
    Base env inp s0 layout rate t s' :=
  h.step hws hw.step (h.rel.wrote3 h.hin hws hw)

/-- **A step of the model**: from `Base` and `P`, code running `m` writing `ws`, then `Base` and
`P'` of the result. -/
theorem ref3 {α : Type} {c : Stmt} {m : VM α} {regs : List Reg64} {ws : List Region}
    {P : QState → Prop} {Q P' : α → QState → Prop} (hws : ∀ r ∈ ws, Ok3 r)
    (h : ∀ t s, Base env inp s0 layout rate t s → P s → WP c s
      (fun s' ↦ ∃ x t', m.run t = some (x, t') ∧ CodeRel env t' s' ∧ Q x s' ∧ Step3 env regs ws s s')
      (fun s' ↦ m.run t = none ∧ Step3 env regs ws s s'))
    (hc : ∀ x s s', Inputs env inp s.mem → P s → Step3 env regs ws s s' → Q x s' → P' x s') :
    Refines (fun t s ↦ Base env inp s0 layout rate t s ∧ P s) c m
      (fun x t s ↦ Base env inp s0 layout rate t s ∧ P' x s) (Kept env rs3 s0) := by
  rintro t s ⟨hb, hp⟩
  refine WP.mono (h t s hb hp) ?_ ?_
  · rintro s' ⟨x, t', hr, hc', hq, hs⟩
    exact ⟨x, t', hr, hb.step hws hs hc', hc x s s' hb.hin hp hs hq⟩
  · rintro s' ⟨hr, hs⟩
    exact ⟨hr, hb.fail hws hs⟩

/-- **Code with no model step**: from `Base` and `P` to `Base` and `P'`, writing `ws`. -/
theorem pre3 {c : Stmt} {ws : List Region} {P P' Q : QState → Prop} (hws : ∀ r ∈ ws, Ok3 r)
    (h : ∀ t s, Base env inp s0 layout rate t s → P s → WP c s (fun s' ↦ Q s' ∧ Wrote env ws s s')
      (fun _ ↦ False))
    (hc : ∀ s s', Inputs env inp s.mem → P s → Wrote env ws s s' → Q s' → P' s') :
    ∀ t s, Base env inp s0 layout rate t s ∧ P s →
      WP c s (fun s' ↦ Base env inp s0 layout rate t s' ∧ P' s') fun _ ↦ False := by
  rintro t s ⟨hb, hp⟩
  exact WP.mono (h t s hb hp) (fun s' ⟨hq, hw⟩ ↦ ⟨hb.wrote hws hw, hc s s' hb.hin hp hw hq⟩)
    fun _ h ↦ h

/-- Registers set, memory kept: a run writing no region. -/
theorem wrote_regs {s s' : QState} (hm : s'.mem = s.mem) (hr : s'.reg .rdi = s.reg .rdi) :
    Wrote env [] s s' :=
  ⟨hr, fun a _ ↦ by rw [hm], fun a ↦ by rw [hm]⟩

theorem ok3_nil : ∀ r ∈ ([] : List Region), Ok3 r := by simp

/-! ## Carrying values through a step -/

section carry

variable {regs : List Reg64} {ws : List Region} {s s' : QState}

theorem Step3.ewatR (hs : Step3 env regs ws s s') (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r)
    {q : Region} (hc : Clear ws q.off (q.off + 2)) {x : EW} (h : EWAt s.mem (q.at env.work) x) :
    EWAt s'.mem (q.at env.work) x :=
  hs.ewat hi hws hc h

theorem Step3.ewarrR (hs : Step3 env regs ws s s') (hi : Inputs env inp s.mem)
    (hws : ∀ r ∈ ws, Ok3 r) {q : Region} (hc : Clear ws q.off q.stop) {xs : Array EW}
    (hn : 2 * xs.size ≤ q.size) (h : EWArr s.mem (q.at env.work) xs) :
    EWArr s'.mem (q.at env.work) xs :=
  hs.ewarr hi hws (n := q.size) hc hn h

theorem Step3.natAtR (hs : Step3 env regs ws s s') (hi : Inputs env inp s.mem)
    (hws : ∀ r ∈ ws, Ok3 r) {q : Region} (hc : Clear ws q.off (q.off + 1)) {n : Nat}
    (h : NatAt s.mem (q.at env.work) n) : NatAt s'.mem (q.at env.work) n :=
  hs.natAt hi hws hc h

end carry

end NativeVm.Code.P3
