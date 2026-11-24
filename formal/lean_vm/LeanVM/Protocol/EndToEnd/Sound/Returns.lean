/-
  LeanVM.Protocol.EndToEnd.Sound.Returns

  What a verifier program returns: a return invariant on programs of the verifier language, its
  rules, and the bound on the number of column claims the front phases of leanVM's deployed
  verifier program return.
-/

module

public import LeanVM.Protocol.Verifier.Claims
import LeanVM.Protocol.Compile.SpecRules.Basic
import LeanVM.Protocol.EndToEnd.Sound.Frame

/-!
# The returns of the leanVM verifier

`RetOK Q p` says that every value `p` returns, along any history, satisfies `Q`. It is a
property of the program alone, with no probability, and it composes through `bind`
(`RetOK.bind`): a sequence returns only what its continuation returns on a value its first part
returns.

Every return invariant `Claims.AllRet` proves of a program is one (`RetOK.of_allRet`); the
instances read the column claims the front phases of `verifyExecutionClaims`
(`LeanVM.Protocol.Verifier.Claims`, the claim-list form of `Statement/Verifier/Lib.lean`'s
`verifyExecution`) return off them:

* `retOK_busTable`: the bus phase followed by the table sumcheck returns at most
  `4 + tableWidths.sum` claims: four framework claims (the two memory limbs' columns and the two
  final counters), then one per column of the six tables (`Claims.tableWidths_sum`: `153`);
* `retOK_publicInputPhase`: the public-input phase returns two claims, one per memory limb.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {α β : Type}

/-! ## The return invariant -/

/-- Every return of `p` satisfies `Q`. -/
def RetOK (Q : α → Prop) (p : VerifierProgram α) : Prop :=
  ∀ (l : List Ev) (a : α), p.after l = some (.ret a) → Q a

/-- A weaker predicate holds of every return. -/
theorem RetOK.mono {Q Q' : α → Prop} {p : VerifierProgram α} (h : RetOK Q p) (hQ : ∀ a, Q a →
    Q' a) :
    RetOK Q' p :=
  fun l a hl ↦ hQ a (h l a hl)

/-- A program that returns at once returns its value. -/
theorem RetOK.ret {Q : α → Prop} {a : α} (h : Q a) : RetOK Q (VerifierProgram.ret a) := by
  intro l b hl
  cases l with
  | nil =>
    simp only [VerifierProgram.after, Option.some.injEq, VerifierProgram.ret.injEq] at hl
    exact hl ▸ h
  | cons e l => cases e <;> simp [VerifierProgram.after] at hl

/-- A rejecting program returns nothing. -/
theorem RetOK.fail {Q : α → Prop} : RetOK Q (VerifierProgram.fail : VerifierProgram α) := by
  intro l b hl
  cases l with
  | nil => simp [VerifierProgram.after] at hl
  | cons e l => cases e <;> simp [VerifierProgram.after] at hl

/-- The trivial predicate holds of every return. -/
theorem RetOK.true (p : VerifierProgram α) : RetOK (fun _ ↦ True) p :=
  fun _ _ _ ↦ trivial

/-- A pure step that may fail returns the option's value. -/
theorem RetOK.liftOption (o : Option α) : RetOK (fun a ↦ o = some a) (Verifier.liftOption o) := by
  cases o with
  | none => exact RetOK.fail
  | some a => exact RetOK.ret rfl

/-- A sequence returns what its continuation returns on a return of its first part. -/
theorem RetOK.bind {Q' : α → Prop} {Q : β → Prop} {p : VerifierProgram α}
    {f : α → VerifierProgram β} (hp : RetOK Q' p) (hf : ∀ a, Q' a → RetOK Q (f a)) :
    RetOK Q (p.bind f) := by
  intro l b hl
  obtain ⟨a, l₁, l₂, -, h1, h2⟩ := after_bind_ret hl
  exact hf a (hp l₁ a h1) l₂ b h2

/-- What every value a program can return satisfies, every return along a history does. -/
theorem RetOK.of_allRet {Q : α → Prop} {p : VerifierProgram α} (h : Claims.AllRet p Q) :
    RetOK Q p := by
  induction h with
  | ret hq => exact RetOK.ret hq
  | fail => exact RetOK.fail
  | read _ ih | sample _ ih | query _ ih =>
    rintro (_ | ⟨e, l⟩) a hl
    · simp [VerifierProgram.after] at hl
    · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at hl
      exact ih _ l a hl
  | grind _ ih | commit _ ih =>
    rintro (_ | ⟨e, l⟩) a hl
    · simp [VerifierProgram.after] at hl
    · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at hl
      split at hl
      · exact ih l a hl
      · cases hl

/-- A sequence whose continuation's returns satisfy `Q` whatever the first part returns. -/
theorem RetOK.bind_true {Q : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hf : ∀ a, RetOK Q (f a)) : RetOK Q (p.bind f) :=
  (RetOK.true p).bind fun a _ ↦ hf a

/-- `readN n` returns `n` scalars. -/
theorem RetOK.readN : ∀ n : ℕ, RetOK (fun xs : List E ↦ xs.length = n)
    (VerifierProgram.readScalars n)
  | 0 => RetOK.ret rfl
  | n + 1 => RetOK.bind_true fun _ ↦ (RetOK.readN n).bind fun xs hxs ↦
      RetOK.ret (by simp [hxs])

/-! ## The front phases of the leanVM verifier -/

/-- The bus phase and the table sumcheck return at most four claims and one per column of the
tables. -/
theorem retOK_busTable (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ 4 + tableWidths.sum)
      ((verifyBusBalance ev layout).bind (tablePhaseClaims layout)) :=
  .of_allRet <| Claims.AllRet.bind (fun bus hb ↦ (Claims.allRet_tablePhaseClaims layout bus).mono
    fun _ h ↦ by have := hb.2.2; omega) _ (Claims.allRet_verifyBusBalance ev layout)

/-- The public-input phase returns two claims. -/
theorem retOK_publicInputPhase (layout : Layout) (publicInput : Digest) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ 2)
      (publicInputPhase layout publicInput) :=
  (RetOK.of_allRet (Claims.allRet_publicInputPhase layout publicInput)).mono fun _ h ↦ h.2

end
end LeanVM.Protocol.EndToEnd.Sound
