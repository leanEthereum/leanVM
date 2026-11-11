/-
  LeanVM.Guest.B1.VerifySub.Always

  What every successful run of a program returns.
-/

module

public import LeanVM.Guest.B1.VerifySub.Split
public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Protocol.WithHash

/-!
# Every result of a program

`Always p P`: every value `p` can return satisfies `P`, whatever it reads and samples
(structurally, on `VerifierProgram`). `Always.run`: a run that returns `a` returns one such value;
`RunsTo.always`: so does a run from a carried sponge.

`tablesSeg_lanes` (in `Lanes`) uses it on `tablesSeg`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Every value `p` can return satisfies `P`. -/
def Always {α : Type} : VerifierProgram α → (α → Prop) → Prop
  | .ret a, P => P a
  | .fail, _ => True
  | .read k, P => ∀ x, Always (k x) P
  | .sample k, P => ∀ c, Always (k c) P
  | .grind _ k, P => Always k P
  | .commit _ _ k, P => Always k P
  | .query _ _ k, P => ∀ r, Always (k r) P

theorem Always.mono {α : Type} {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) (p : VerifierProgram α) :
    Always p P → Always p Q := by
  induction p with
  | ret a => exact hPQ a
  | fail => exact fun _ ↦ trivial
  | read k ih => exact fun h x ↦ ih x (h x)
  | sample k ih => exact fun h c ↦ ih c (h c)
  | grind _ k ih => exact ih
  | commit _ _ k ih => exact ih
  | query _ _ k ih => exact fun h r ↦ ih r (h r)

theorem always_true {α : Type} : ∀ p : VerifierProgram α, Always p fun _ ↦ True
  | .ret _ => trivial
  | .fail => trivial
  | .read k => fun x ↦ always_true (k x)
  | .sample k => fun c ↦ always_true (k c)
  | .grind _ k => always_true k
  | .commit _ _ k => always_true k
  | .query _ _ k => fun r ↦ always_true (k r)

theorem Always.bind {α β : Type} {Q : α → Prop} {P : β → Prop} {f : α → VerifierProgram β}
    (hf : ∀ a, Q a → Always (f a) P) (p : VerifierProgram α) : Always p Q → Always (p.bind f)
        P := by
  induction p with
  | ret a => exact hf a
  | fail => exact fun _ ↦ trivial
  | read k ih => exact fun h x ↦ ih x (h x)
  | sample k ih => exact fun h c ↦ ih c (h c)
  | grind _ k ih => exact ih
  | commit _ _ k ih => exact ih
  | query _ _ k ih => exact fun h r ↦ ih r (h r)

/-- **A run returns one of the values.** -/
theorem Always.run {α : Type} {P : α → Prop} (p : VerifierProgram α) :
    ∀ {st st' : VerifierProgramState} {a : α}, Always p P → runId p st = some (a, st') → P a := by
  induction p with
  | ret b =>
    intro st st' a h hr
    simp only [runId, Compile.runWithHash, pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact h
  | fail => intro st st' a _ hr; cases hr
  | read k ih =>
    intro st st' a h hr
    simp only [runId, Compile.runWithHash] at hr
    split at hr
    · cases hr
    · exact ih _ (h _) hr
  | sample k ih =>
    intro st st' a h hr
    exact ih _ (h _) hr
  | grind b k ih =>
    intro st st' a h hr
    simp only [runId, Compile.runWithHash] at hr
    split at hr
    · cases hr
    · rename_i x xs _
      change (if powOk b (Compile.squeeze (m := Id) keccakF1600
          (Compile.absorb (m := Id) keccakF1600 st.sponge x dsPowNonce)).1 = true then
        Compile.runWithHash (m := Id) keccak256 keccakF1600 k (VerifierProgramState.mk (Compile.squeeze (m := Id) keccakF1600
          (Compile.absorb (m := Id) keccakF1600 st.sponge x dsPowNonce)).2 xs st.openings st.roots)
        else none) = some (a, st') at hr
      split at hr
      · exact ih h hr
      · cases hr
  | commit hh ww k ih =>
    intro st st' a h hr
    simp only [runId, Compile.runWithHash] at hr
    split at hr
    · revert hr
      split
      · exact ih h
      · intro hr; cases hr
    · cases hr
  | query i ps k ih =>
    intro st st' a h hr
    obtain ⟨_, _, _, _, _, rows, _, _, _, hr'⟩ :=
      (Compile.runWithHash_query_eq_some_iff keccak256 keccakF1600 i ps k st (a, st')).mp hr
    exact ih _ (h _) hr'

/-- **A run from a carried sponge returns one of the values.** -/
theorem RunsTo.always {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α} {P : α
    → Prop}
    (h : RunsTo p s xs a s') {sp : Sponge} (hs : s.Carries sp) (hp : Always p P) : P a := by
  obtain ⟨_, -, e⟩ := h sp hs [] [] []
  exact Always.run p hp e

/-! ## The primitives -/

theorem always_readN : ∀ n : ℕ, Always (VerifierProgram.readScalars n) fun xs ↦ xs.length = n
  | 0 => rfl
  | n + 1 => by
    intro x
    show Always ((VerifierProgram.readScalars n).bind fun xs ↦ VerifierProgram.ret (x :: xs)) _
    exact Always.bind (fun xs hxs ↦ by show (x :: xs).length = n + 1; simp [hxs]) _ (always_readN n)

theorem always_require (c : Prop) [Decidable c] : Always (VerifierProgram.require c) fun _ ↦ c := by
  unfold VerifierProgram.require
  split
  · assumption
  · trivial

theorem always_roundPoly (count : ℕ) (claim : E) (e : Option E) :
    Always (sumcheckRoundPoly count claim e) fun _ ↦ True := always_true _

theorem always_sumcheck (count : ℕ) : ∀ (eqs : List (Option E)) (claim : E),
    Always (sumcheck claim count eqs) fun r ↦ r.1.length = eqs.length
  | [], _ => rfl
  | e :: eqs, claim => by
    unfold sumcheck
    simp only [VerifierProgram.bind_eq]
    refine Always.bind (fun msg _ ↦ ?_) _ (always_roundPoly count claim e)
    intro ch
    show Always ((sumcheck (polyEval msg ch) count eqs).bind fun r ↦ _) _
    refine Always.bind (Q := fun r ↦ r.1.length = eqs.length) (fun r hr ↦ ?_) _
      (always_sumcheck count eqs _)
    obtain ⟨pt, fin⟩ := r
    show (ch :: pt).length = (e :: eqs).length
    simp only [List.length_cons, hr]

end
end LeanVM.Guest.B1.VerifySub
