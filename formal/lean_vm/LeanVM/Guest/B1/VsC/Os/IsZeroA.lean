/-
  LeanVM.Guest.B1.VsC.Os.IsZeroA

  `is_zero` placed: a leaf touching no memory.
-/

module

public import LeanVM.Guest.B1.VsC.IsZeroC
public import LeanVM.Guest.B1.VsC.LeafEnd
public import LeanVM.Guest.B1.VsC.ChunkDC
import LeanVM.Guest.CoreRef

/-!
# `is_zero`, placed

`is_zero` branches, so it is not a straight leaf; on either path it calls nothing, loads nothing and
hints no heap word (`iz_evs`). Its completeness with no words of its own (`is_zero_complete0`, from
its relation and `is_zero_freePost`) is placed by `leafAtA_of_callCompletes0_leaf`:
`is_zero_leafA`, block its frame, ending at its cursor, in any region.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value

@[expose] public section

/-- **`is_zero`'s paths call nothing, load nothing, hint no heap word.** -/
theorem iz_evs {σ : Val} {es : List Ev} {vs : List V} (hw : walk σ izBody = .ret es vs) :
    calls es = [] ∧ loadAddrs σ es = [] ∧ heapHintAddrs σ es = [] := by
  rw [izBody, walk_straight_pre σ _ _ rfl] at hw
  unfold walk at hw
  by_cases h0 : σ (.n 11) = 0 <;> simp [walk1, walk, h0, Out.seq, Out.pre, slEvs, izHead] at hw <;>
    (rw [← hw.1]; exact ⟨rfl, rfl, rfl⟩)

theorem is_zero_pureIn : coreProgram.PureIn ["is_zero"] := by
  intro g hg fn hf
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_is_zero] at hf
  obtain rfl := Option.some.inj hf
  decide +kernel

theorem is_zero_not_loop : coreProgram.loop "is_zero" = false := by decide +kernel

/-- **`is_zero` completes with no words of its own.** -/
theorem is_zero_complete0 (k : ℕ) (Pre : Reader → Prop) (w : E) :
    CallCompletes0 k "is_zero" [w] [if w = 0 then 1 else 0] Pre PostQuiet := fun rd _ _ => by
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree coreProgram_wf ((is_zero_iff rd [w] [if w = 0 then 1 else 0]).mpr rfl)
  exact ⟨t, hn, hv, hb, is_zero_freePost rd w _ t hn hv⟩

/-- **`is_zero` completes placed**, at its cursor, in any region. -/
theorem is_zero_leafA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} (k : ℕ)
    (w : E) (R : ℕ → Prop) (Pre : Reader → Prop) :
    LeafAtA fs al cert k "is_zero" [w] [if w = 0 then 1 else 0] R (fun _ => True) Pre PostQuiet := by
  refine leafAtA_of_callCompletes0_leaf is_zero_pureIn List.mem_cons_self is_zero_not_loop
    (fun fn σ es vs hf hw => ?_) (is_zero_complete0 k Pre w) fun rd t _ _ hn hv _ _ => ?_
  · rw [find_is_zero] at hf
    cases hf
    rw [is_zero_body] at hw
    exact (iz_evs hw).1
  · cases t with
    | phantom => exact hv.elim
    | node f σ bufs kids =>
      obtain ⟨fn', hfn, -, es, vs, hw, -, -, hk⟩ := hv
      simp only [Tree.name] at hn
      subst hn
      rw [find_is_zero] at hfn
      cases hfn
      have hw' := hw
      rw [is_zero_body] at hw'
      obtain ⟨hc, hl, hh⟩ := iz_evs hw'
      have hev : (Memory.Tree.node "is_zero" σ bufs kids).events coreProgram = es := by
        simp only [Tree.events, Tree.name, Tree.val, find_is_zero, hw]
      rw [hc] at hk
      have hkids : kids = [] := by
        cases kids with
        | nil => rfl
        | cons _ _ => simp [Tree.KidsValid] at hk
      subst hkids
      refine ⟨⟨fun A hA => ?_, by rw [Tree.LoadsRKids]; trivial⟩,
        ⟨fun A hA => ?_, by rw [Tree.HintsRKids]; trivial⟩⟩
      · rw [hev, hl] at hA; exact absurd hA List.not_mem_nil
      · rw [hev, hh] at hA; exact absurd hA List.not_mem_nil

end
end LeanVM.Guest.B1.VsC
