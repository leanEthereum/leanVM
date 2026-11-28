/-
  LeanVM.Guest.B1.VsC.IsZeroC

  `is_zero` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.Log2C
public import LeanVM.Guest.B1.Whir.IsZero
public import LeanVM.Guest.Complete.Free
public import LeanVM.Guest.Memory.GuestWf
public import LeanVM.Guest.Memory.Straight
import LeanVM.Guest.CoreRef

/-!
# `is_zero`, complete

`is_zero(w)` hints `w`'s low limb, pins it as `split_limbs` does (`split_iff`: the limb and
`(w + lo)·y⁻¹` in `K`), and tests the norm. Its relation is its meaning (`is_zero_iff`), so a valid
tree exists on every memory (`callCompletes_of_rel`); on any valid tree the hinted limb is pinned
by the atoms before the branch, so the tree is exact, and it pops nothing (`is_zero_complete`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `is_zero`'s statements before its branch. -/
def izHead : List Stmt :=
  [.atom (.hint (.limbs (.n 0) [.n 1])), .atom (.add (.n 2) (.n 0) (.n 1)),
    .atom (.const (.n 3) (word 2 1)), .atom (.mul (.n 4) (.n 2) (.n 3)),
    .atom (.assertInK (.n 1) (.n 4)), .atom (.mul (.n 5) (.n 1) (.n 1)),
    .atom (.const (.n 6) (word 2 0)), .atom (.mul (.n 7) (.n 1) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 4)), .atom (.add (.n 9) (.n 5) (.n 8)),
    .atom (.mul (.n 10) (.n 4) (.n 4)), .atom (.add (.n 11) (.n 9) (.n 10))]

/-- The expansion of `is_zero`. -/
def izBody : List Stmt :=
  izHead ++ [.ite (.n 11) [.atom (.const (.n 12) (word 1 0))] [.atom (.const (.n 12) (word 0 0))],
    .atom (.copy (.n 13) (.n 12)), .ret [.n 13]]

theorem is_zero_body : Fn.body fn% «is_zero» = izBody := stmtsEqb_sound (by decide +kernel)

theorem find_is_zero : coreProgram.find? "is_zero" = some fn% «is_zero» :=
  coreProgram_find?_at (j := idx% «is_zero») rfl

/-- The hinted limb. -/
def izHint : Atom := .hint (.limbs (.n 0) [.n 1])

theorem iz_sites : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ [izHint])) pinsInverse
    izBody = true := by decide +kernel

theorem iz_noWit : NoWitG "is_zero" := noWitG_of (by decide +kernel : noWitness "is_zero" idx% «is_zero» = true)

/-- The head's atoms are on every path. -/
theorem iz_head_mem {σ : Val} {es : List Ev} {vs : List V} (hw : walk σ izBody = .ret es vs) {a : Atom}
    (ha : Stmt.atom a ∈ izHead) : Ev.atom a ∈ es := by
  rw [izBody, walk_straight_pre σ _ _ rfl] at hw
  cases h : walk σ [Stmt.ite (.n 11) [.atom (.const (.n 12) (word 1 0))] [.atom (.const (.n 12) (word 0 0))],
      .atom (.copy (.n 13) (.n 12)), .ret [.n 13]] with
  | ret es' vs' =>
    rw [h, Out.pre] at hw
    cases hw
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, ha, ?_⟩)
    simp [slEvs]
  | fall es' => rw [h, Out.pre] at hw; cases hw
  | stuck => rw [h, Out.pre] at hw; cases hw

/-- **Every valid tree of `is_zero` pops nothing and is exact.** -/
theorem is_zero_freePost (rd : Reader) (w : E) (rets : List E) (t : Tree) (hn : t.name = "is_zero")
    (hv : t.Valid coreProgram rd [w] rets) : FreePost rd t := by
  refine ⟨pops_nil_of_noWitness iz_noWit hv hn rd, ?_⟩
  cases t with
  | phantom => simp [Tree.Valid] at hv
  | node f σ bufs kids =>
    obtain ⟨fn, hf, hp, es, vs, hw, -, hes, hk⟩ := hv
    simp only [Tree.name] at hn
    subst hn
    rw [find_is_zero] at hf
    cases hf
    rw [is_zero_body] at hw
    have hp' : σ (.n 0) = w := by
      have : [σ (.n 0)] = [w] := hp
      simpa using this
    have hat : ∀ a, Stmt.atom a ∈ izHead → a.Holds rd σ := fun a ha => hes _ (iz_head_mem hw ha)
    have h2 := hat (.add (.n 2) (.n 0) (.n 1)) (by simp [izHead])
    have h3 := hat (.const (.n 3) (word 2 1)) (by simp [izHead])
    have h4 := hat (.mul (.n 4) (.n 2) (.n 3)) (by simp [izHead])
    have hk' := hat (.assertInK (.n 1) (.n 4)) (by simp [izHead])
    simp only [Atom.Holds] at h2 h3 h4 hk'
    have hlo : σ (.n 1) = ofK ((σ (.n 0)).limb 0) := by
      refine (split_iff (σ (.n 0)) (σ (.n 1))).mp ⟨hk'.1, ?_⟩
      rw [← word_y_inv, ← h3, ← h2, ← h4]
      exact hk'.2
    have hkids : kids = [] := by
      have hc : calls es = [] := by
        rw [izBody, walk_straight_pre σ _ _ rfl] at hw
        unfold walk at hw
        by_cases h0 : σ (.n 11) = 0 <;> simp [walk1, walk, h0, Out.seq, Out.pre, slEvs, izHead] at hw <;>
          (rw [← hw.1]; rfl)
      rw [hc] at hk
      cases kids with
      | nil => rfl
      | cons _ _ => simp [Tree.KidsValid] at hk
    subst hkids
    rw [Tree.every_node]
    refine ⟨exactAt_of_walk (find_is_zero) (by rw [is_zero_body]; exact hw)
      (exact_of_sites iz_sites hw hes fun a ha _ => ?_), by rw [Tree.EveryKids]; trivial⟩
    simp only [List.mem_singleton] at ha
    subst ha
    show [σ (.n 1)] = (List.range 1).map fun j => ofK (if j = 0 then (σ (.n 0)).limb 0 else (σ (.n 0)).limb 1)
    simp [hlo]

/-- **`is_zero` completes** on every memory, returning `1` at `w = 0` and `0` elsewhere. -/
theorem is_zero_complete (k : ℕ) (Pre : Reader → Prop) (w : E) :
    CallCompletes k "is_zero" [w] [if w = 0 then 1 else 0] Pre FreePost :=
  callCompletes_of_rel coreProgram_wf fun b => ⟨0, [], wordsIn_nil b, fun rd _ _ _ =>
    ⟨(is_zero_iff rd _ _).mpr rfl, fun t hn hv _ => is_zero_freePost rd w _ t hn hv⟩⟩

end
end LeanVM.Guest.B1.VsC
