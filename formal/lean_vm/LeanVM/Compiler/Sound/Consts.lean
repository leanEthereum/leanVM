/-
  LeanVM.Compiler.Sound.Consts

  A right table of constant parameters (`ConstsOk`): its facts follow from a function's
  obligations, so a compiled program's preconditions may carry them.
-/

module

public import LeanVM.Compiler.Consts
public import LeanVM.Compiler.Sound.Main

/-!
# The constant parameters' facts

`withConsts U T` is the precondition `U` with the table `T`'s facts: the arguments of a call of
`g` that `T.at g` names hold their words.

* `oblList_consts`: where `T` is right of a block (`blockOk`), the block's obligations under `U`
  give its obligations under `withConsts U T`, what the statements before each call teach
  (`learn`: a `const` atom's value holds its word, `KnownHolds`) supplying the facts. The call
  relation may shrink on the way (`CallRel.Le C' C`).
* `World.withConsts`: the program's world with `withConsts W.U T`. Its frames are entered on the
  same run with a stronger precondition (`World.entered_withConsts`), so its located call relation
  is within the world's (`World.c_withConsts`); its obligations follow from the world's
  (`World.obligations_withConsts`), the parameters being the frame's argument words
  (`World.params_vf`); and in every frame of a function its precondition holds at, the cells
  `2 + k` the table names hold their words (`World.pre_withConsts_cell`).
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The precondition `U` with the table `T`'s facts: the arguments of a call of `g` that `T`
names hold their words. -/
def withConsts (U : String → List E → Prop) (T : Consts) : String → List E → Prop :=
  fun g a => U g a ∧ ∀ x ∈ T.at g, a[x.1]? = some x.2

/-- Every value `kn` names holds its word. -/
def KnownHolds (σ : Val) (kn : Known) : Prop := ∀ x ∈ kn, σ x.1 = x.2

/-! ## The located call relation, by its frames -/

section Located

variable {rd : Reader} {vf : String → K → Val} {A A' : String → K → List E → List E → Prop}

theorem locN_monoA (P : Program) (hA : ∀ f fp a r, A f fp a r → A' f fp a r) :
    ∀ n, CallRel.Le (P.locN rd vf A n) (P.locN rd vf A' n)
  | 0 => fun _ _ _ h => h.elim
  | n + 1 => fun _ _ _ ⟨fn, fp, hf, hAx, hp, h⟩ =>
      ⟨fn, fp, hf, hA _ _ _ _ hAx, hp, holdsList_mono (locN_monoA P hA n) fn.body id (fun _ h => h) h⟩

/-- The located call relation grows with the frames it allows. -/
theorem relL_monoA (P : Program) (hA : ∀ f fp a r, A f fp a r → A' f fp a r) :
    CallRel.Le (P.RelL rd vf A) (P.RelL rd vf A') :=
  fun f a r ⟨n, h⟩ => ⟨n, locN_monoA P hA n f a r h⟩

end Located

/-! ## The obligations with the table's facts -/

section Obligations

variable {T : Consts} {C C' : CallRel} {U : String → List E → Prop} {rd : Reader} {σ : Val}

theorem argsOk_words {kn : Known} (hk : KnownHolds σ kn) {f : String} {args : List V}
    (h : argsOk T kn f args = true) : ∀ x ∈ T.at f, (args.map σ)[x.1]? = some x.2 := by
  intro x hx
  have hx' := List.all_eq_true.mp h x hx
  cases hv : args[x.1]? with
  | none => rw [hv] at hx'; exact absurd hx' (by simp)
  | some v =>
      rw [hv] at hx'
      have hm : (v, x.2) ∈ kn := by simpa using hx'
      simp [List.getElem?_map, hv, hk _ hm]

theorem learn_holds {kn : Known} (hk : KnownHolds σ kn) {a : Atom} (ha : a.Holds rd σ) :
    KnownHolds σ (learn kn (.atom a)) := by
  cases a with
  | const d c =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact hk x hx
  | _ => exact hk

mutual
/-- **A statement's obligations, with the table's facts**. -/
theorem obl_consts (hC : CallRel.Le C' C) : ∀ (s : Stmt) {kn : Known} {A B : Prop},
    KnownHolds σ kn → stmtOk T kn s = true → (A → B) → Obl C U rd σ s A →
      Obl C' (withConsts U T) rd σ s B
  | .atom _, _, _, _, _, _, hAB, h => fun ha => hAB (h ha)
  | .ite _ z n, _, _, _, hk, hs, hAB, h => by
      simp only [stmtOk, Bool.and_eq_true] at hs
      exact fun hK => ⟨fun h0 => oblList_consts hC z hk hs.1 hAB ((h hK).1 h0),
        fun h0 => oblList_consts hC n hk hs.2 hAB ((h hK).2 h0)⟩
  | .match_ x arms, _, _, _, hk, hs, hAB, h => ⟨h.1, oblArms_consts hC x arms 0 hk hs hAB h.2⟩
  | .call _ _ _, _, _, _, hk, hs, hAB, h =>
      ⟨⟨h.1, argsOk_words hk hs⟩, fun hc => hAB (h.2 (hC _ _ _ hc))⟩
  | .callIf _ _ _, _, _, _, hk, hs, hAB, h => fun hK =>
      ⟨fun h0 => ⟨(h hK).1 h0, argsOk_words hk hs⟩,
        fun hc => hAB ((h hK).2 fun h0 => hC _ _ _ (hc h0))⟩
  | .dispatch _ fs _ _, _, _, _, hk, hs, hAB, h =>
      ⟨h.1, fun j hj hx => ⟨h.2.1 j hj hx,
          argsOk_words hk (List.all_eq_true.mp hs _ (List.getElem_mem hj))⟩,
        fun ⟨j, hj, hx, hc⟩ => hAB (h.2.2 ⟨j, hj, hx, hC _ _ _ hc⟩)⟩
  | .ret _, _, _, _, _, _, _, _ => trivial

/-- **A block's obligations, with the table's facts**: each statement knowing what the ones
before it taught. -/
theorem oblList_consts (hC : CallRel.Le C' C) : ∀ (ss : List Stmt) {kn : Known} {A B : Prop},
    KnownHolds σ kn → blockOk T kn ss = true → (A → B) → OblList C U rd σ ss A →
      OblList C' (withConsts U T) rd σ ss B
  | [], _, _, _, _, _, hAB, h => hAB h
  | .atom _ :: ss, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact fun ha => oblList_consts hC ss (learn_holds hk ha) hs.2 hAB (h ha)
  | .ite c z n :: ss, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact obl_consts hC (.ite c z n) hk hs.1 (oblList_consts hC ss hk hs.2 hAB) h
  | .match_ x arms :: ss, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact obl_consts hC (.match_ x arms) hk hs.1 (oblList_consts hC ss hk hs.2 hAB) h
  | .call f args rets :: ss, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact obl_consts hC (.call f args rets) hk hs.1 (oblList_consts hC ss hk hs.2 hAB) h
  | .callIf c f args :: ss, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact obl_consts hC (.callIf c f args) hk hs.1 (oblList_consts hC ss hk hs.2 hAB) h
  | .dispatch x fs args rets :: ss, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact obl_consts hC (.dispatch x fs args rets) hk hs.1 (oblList_consts hC ss hk hs.2 hAB) h
  | .ret vs :: ss, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact obl_consts hC (.ret vs) hk hs.1 (oblList_consts hC ss hk hs.2 hAB) h

/-- **The arms' obligations, with the table's facts**. -/
theorem oblArms_consts (hC : CallRel.Le C' C) (x : V) : ∀ (arms : List (List Stmt)) (j : Nat)
    {kn : Known} {A B : Prop}, KnownHolds σ kn → armsOk T kn arms = true → (A → B) →
      OblArms C U rd σ x j arms A → OblArms C' (withConsts U T) rd σ x j arms B
  | [], _, _, _, _, _, _, _, _ => trivial
  | a :: as, j, _, _, _, hk, hs, hAB, h => by
      simp only [armsOk, Bool.and_eq_true] at hs
      exact ⟨fun hx => oblList_consts hC a hk hs.1 hAB (h.1 hx),
        oblArms_consts hC x as (j + 1) hk hs.2 hAB h.2⟩
end

/-- A function's entry knowledge holds where its parameters are words its table entries name. -/
theorem entryKnown_holds {f : Fn} {ws : List E} (hp : f.params.map σ = ws)
    (hw : ∀ x ∈ T.at f.name, ws[x.1]? = some x.2) : KnownHolds σ (entryKnown T f) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := List.mem_filterMap.mp hx
  cases hv : f.params[y.1]? with
  | none => rw [hv] at hxy; cases hxy
  | some v =>
      rw [hv] at hxy
      cases hxy
      have h1 := hw y hy
      rw [← hp, List.getElem?_map, hv] at h1
      exact Option.some.inj h1

end Obligations

/-! ## The table the back end uses is right -/

section Empty

mutual
theorem stmtOk_empty (kn : Known) : ∀ s : Stmt, stmtOk {} kn s = true
  | .atom _ => rfl
  | .ite _ z n => by simp only [stmtOk, blockOk_empty, Bool.and_self]
  | .match_ _ arms => armsOk_empty kn arms
  | .call .. => rfl
  | .callIf .. => rfl
  | .dispatch _ fs _ _ => List.all_eq_true.mpr fun _ _ => rfl
  | .ret _ => rfl

theorem blockOk_empty (kn : Known) : ∀ ss : List Stmt, blockOk {} kn ss = true
  | [] => rfl
  | s :: ss => by simp only [blockOk, stmtOk_empty, blockOk_empty, Bool.and_self]

theorem armsOk_empty (kn : Known) : ∀ arms : List (List Stmt), armsOk {} kn arms = true
  | [] => rfl
  | a :: as => by simp only [armsOk, blockOk_empty, armsOk_empty, Bool.and_self]
end

end Empty

/-- **The back end's table is right of the program.** -/
theorem constTable_ok (p : List TracedFn) : ConstsOk (constTable p) (p.map (·.core)) = true := by
  unfold constTable
  dsimp only
  split
  · assumption
  · exact Bool.and_eq_true_iff.mpr ⟨rfl, List.all_eq_true.mpr fun f _ => blockOk_empty _ f.body⟩

/-- A right table names nothing of `main`. -/
theorem ConstsOk.main {T : Consts} {p : Program} (h : ConstsOk T p = true) : T.at "main" = [] :=
  List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp h).1

/-! ## A compiled program's world with the table's facts -/

namespace World

variable {κ : ℕ} (W : World κ)

/-- The world whose precondition carries the table's facts. -/
def withConsts (T : Consts) : World κ := { W with U := LeanVM.Compiler.withConsts W.U T }

variable {W} {T : Consts}

/-- A frame entered with the table's facts was entered. -/
theorem entered_withConsts {g : String} {fp : K} {a r : List E}
    (h : (W.withConsts T).Entered g fp a r) : W.Entered g fp a r := by
  obtain ⟨hm, ⟨hg, hjt, tf, htf, hn, hs, hU⟩, hr, rest⟩ := h
  exact ⟨hm, ⟨hg, hjt, tf, htf, hn, hs, hU.1⟩, hr, rest⟩

/-- Its located call relation is within the world's. -/
theorem c_withConsts : CallRel.Le (W.withConsts T).C W.C :=
  relL_monoA W.core fun _ _ _ _ h => entered_withConsts h

/-- **The obligations with the table's facts follow from the world's**, for a table right of the
program. -/
theorem obligations_withConsts (hW : W.Compiled) (hT : ConstsOk T W.core = true) {tf : TracedFn}
    (htf : tf ∈ W.p) (h : W.Obligations tf) : (W.withConsts T).Obligations tf := by
  intro fp hmain hU
  exact oblList_consts c_withConsts tf.core.body
    (entryKnown_holds (World.params_vf hW htf fp) hU.2)
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hT).2 tf.core (List.mem_map_of_mem htf)) id
    (h fp hmain hU.1)

/-- **A frame of `g` its precondition holds at has the table's words in its cells**: cell
`2 + k` holds the word of each entry `(k, c)` of `g`. -/
theorem pre_withConsts_cell {g : String} {fp : K} (h : (W.withConsts T).Pre g fp)
    {x : Nat × E} (hx : x ∈ T.at g) : wd W.L fp (2 + x.1) = x.2 := by
  obtain ⟨-, -, tf, -, rfl, -, hU⟩ := h
  have h1 := hU.2 x hx
  simp only [frameWords, List.getElem?_map] at h1
  cases hr : (List.range (sigOf tf).1)[x.1]? with
  | none => rw [hr] at h1; cases h1
  | some i =>
      rw [hr] at h1
      obtain ⟨_, hi⟩ := List.getElem?_eq_some_iff.mp hr
      rw [List.getElem_range] at hi
      subst hi
      exact Option.some.inj h1

end World

end
end LeanVM.Compiler
