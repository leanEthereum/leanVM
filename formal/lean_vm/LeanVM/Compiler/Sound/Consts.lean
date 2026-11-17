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
`g` that `T g` names hold their words.

* `oblList_consts`: where `T` is right of a block (`blockOk`), the block's obligations under `U`
  give its obligations under `withConsts U T`, what the statements before each call teach
  (`learn`: a `const` atom's value holds its word, `KnownHolds`) supplying the facts. The call
  relation may shrink on the way (`CallRel.Le C' C`).
* `World.withConsts`: the program's world with `withConsts W.U T`. Its frames are entered on the
  same run with a stronger precondition (`World.entered_withConsts`), so its located call relation
  is within the world's (`World.c_withConsts`); its obligations follow from the world's
  (`World.obligations_withConsts`), the parameters being the frame's argument words
  (`World.params_vf`); with the back end's table (`constsOf (loopTable W.p)`, right of the program
  by `lowerProgram_consts`) its callers' preconditions carry the constant parameters
  (`World.ConstsIn`).
* `program_sound`: `program_sound_of` at the world with the back end's table, its `main` body
  back at the world: a compiled program is sound with no precondition about its constant
  parameters.
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The precondition `U` with the table `T`'s facts: the arguments of a call of `g` that `T`
names hold their words. -/
def withConsts (U : String → List E → Prop) (T : String → List (ℕ × E)) :
    String → List E → Prop :=
  fun g a => U g a ∧ ∀ x ∈ T g, a[x.1]? = some x.2

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

variable {T : String → List (ℕ × E)} {C C' : CallRel} {U : String → List E → Prop} {rd : Reader}
  {σ : Val}

theorem argsOk_words {kn : Known} (hk : KnownHolds σ kn) {f : String} {args : List V}
    (h : argsOk T kn f args = true) : ∀ x ∈ T f, (args.map σ)[x.1]? = some x.2 := by
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
    (hw : ∀ x ∈ T f.name, ws[x.1]? = some x.2) : KnownHolds σ (entryKnown T f) := by
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

/-- A right table names nothing of `main`. -/
theorem ConstsOk.main {T : String → List (ℕ × E)} {p : Program} (h : ConstsOk T p = true) :
    T "main" = [] :=
  List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp h).1

/-! ## A compiled program's world with the table's facts -/

namespace World

variable {κ : ℕ} (W : World κ)

/-- The world whose precondition carries the table's facts. -/
def withConsts (T : String → List (ℕ × E)) : World κ :=
  { W with U := LeanVM.Compiler.withConsts W.U T }

variable {W} {T : String → List (ℕ × E)}

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

/-- **With the back end's table, the callers' preconditions carry the constant parameters.** -/
theorem constsIn_withConsts : (W.withConsts (constsOf (loopTable W.p))).ConstsIn :=
  fun _ _ h => h.2

end World

/-- **(c) The program is compiled correctly**: on a memory where a run of the compiled program
from `(g^0, 1)` halts, every function's obligations holding, `main`'s core body holds at frame
`1` under the valuation by places, its calls located: `program_sound_of` at the world whose
preconditions carry the constant parameters, whose obligations and `main`'s precondition follow
from the world's. -/
theorem program_sound {κ : ℕ} {W : World κ} (hW : W.Compiled) (hκ : κ < 64)
    (hobl : ∀ tf ∈ W.p, W.Obligations tf)
    (hU : ∀ tf ∈ W.p, tf.core.name = "main" → W.U "main" (frameWords W.L 1 2 (sigOf tf).1))
    {k : ℕ} (hs : Safe W.prog W.L k ⟨addressOfIndex 0, 1⟩) : W.MainHolds := by
  have hT := lowerProgram_consts hW.1
  obtain ⟨tf, htf, hn, hp, hb⟩ := program_sound_of (W := W.withConsts (constsOf (loopTable W.p)))
    hW hκ World.constsIn_withConsts
    (fun tf htf => World.obligations_withConsts hW hT htf (hobl tf htf))
    (fun tf htf hn => ⟨hU tf htf hn, by rw [ConstsOk.main hT]; intro x hx; cases hx⟩) hs
  exact ⟨tf, htf, hn, hp, holdsList_mono World.c_withConsts _ id (fun _ h => h) hb⟩

/-- (c) for a valid execution of the compiled program. -/
theorem program_sound_valid {κ : ℕ} {W : World κ} (hW : W.Compiled) (hκ : κ < 64)
    (hobl : ∀ tf ∈ W.p, W.Obligations tf)
    (hU : ∀ tf ∈ W.p, tf.core.name = "main" → W.U "main" (frameWords W.L 1 2 (sigOf tf).1))
    {input : PublicInput} {steps : ℕ}
    (h : ValidExecution W.prog input ⟨κ, W.L, steps⟩) : W.MainHolds :=
  program_sound hW hκ hobl hU (safe_of_validExecution h)

/-! ## The statements -/

/-- **(b), for every program.** -/
theorem fnSound : FnSoundStmt :=
  fun _ hW hκ hUc _ htf hne hobl => fn_sound hW hκ hUc htf hne hobl

/-- **(c), for every program.** -/
theorem programSound : ProgramSoundStmt :=
  fun _ hW hκ hobl hU _ hs => program_sound hW hκ hobl hU hs

end
end LeanVM.Compiler
