/-
  LeanVM.Protocol.EndToEnd.Sound.Returns

  What a verifier program returns: a return invariant on programs of the verifier language, its
  rules, and the bound on the number of column claims the front phases of leanVM's deployed
  verifier program return.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.Compile.SpecRules.Basic

/-!
# The returns of the leanVM verifier

`RetOK Q p` says that every value `p` returns, along any history, satisfies `Q`. It is a
property of the program alone, with no probability, and it composes through `bind`
(`RetOK.bind`): a sequence returns only what its continuation returns on a value its first part
returns.

The instances bound the column claims the front phases of `verifyExecutionClaims`
(`LeanVM.Protocol.Verifier.Claims`, the claim-list form of `Statement/LeanVmVerifier.lean`'s
`verifyExecution` at leanVM `f128`) return:

* `retOK_verifyBusBalance`: the bus phase returns four framework claims (the two memory limbs'
  columns and the two final counters);
* `retOK_busTable`: the bus phase followed by the table sumcheck returns at most `4 + 153 = 157`
  claims, every one of the six tables contributing one claim per column (`tables_width_sum`);
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

/-- A sequence that returns at once: both parts return. -/
private theorem bind_eq_ret' {p : VerifierProgram α} {f : α → VerifierProgram β} {b : β} (h : p.bind
    f = .ret b) :
    ∃ a, p = .ret a ∧ f a = .ret b := by
  cases p <;> simp_all [VerifierProgram.bind]

/-- A sequence returns what its continuation returns on a return of its first part. -/
theorem RetOK.bind {Q' : α → Prop} {Q : β → Prop} {p : VerifierProgram α} {f : α →
    VerifierProgram β}
    (hp : RetOK Q' p) (hf : ∀ a, Q' a → RetOK Q (f a)) : RetOK Q (p.bind f) := by
  intro l b hl
  rcases VerifierProgram.after_bind_cases f hl with ⟨q, hq, hr⟩ | ⟨a, l₁, l₂, -, h1, -, h2⟩
  · obtain ⟨a, rfl, hfa⟩ := bind_eq_ret' hr.symm
    exact hf a (hp l a hq) [] b (by simp [VerifierProgram.after, hfa])
  · exact hf a (hp l₁ a h1) l₂ b h2

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

/-- The bus phase returns four framework claims, whatever checks the fixed polynomial's value. -/
theorem retOK_verifyBusBalance (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout) :
    RetOK (fun bus : BusResult ↦ bus.claims.length ≤ 4) (verifyBusBalance ev layout) := by
  unfold verifyBusBalance
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ RetOK.bind_true fun r ↦ ?_
  obtain ⟨countRoot, point, treeValues⟩ := r
  refine RetOK.bind_true fun _ ↦ (RetOK.readN 2).bind fun memory hm ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ RetOK.bind_true fun r ↦ ?_
  obtain ⟨share, bytecodePoint, value⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.ret ?_
  simp only [List.length_append, List.length_zipWith, List.length_cons, List.length_nil, hm]
  omega

/-- The tables' row evaluations: one claim per column of each row's table, added to the claims
so far. -/
theorem retOK_tableTerms (constraintPowers formPowers point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim),
      RetOK (fun r : E × List ColumnClaim ↦
          r.2.length ≤ claims.length + (rows.map fun r ↦ r.1.width).sum)
        (tableTermsClaims constraintPowers formPowers point rows cursor final claims)
  | [], _, _, _ => RetOK.ret (by simp)
  | (table, h, forms, weight) :: rest, cursor, final, claims => by
    refine (RetOK.readN table.width).bind fun evaluations he ↦
      (retOK_tableTerms constraintPowers formPowers point rest _ _ _).mono fun r hr ↦ ?_
    simp only [List.length_append, List.length_map, List.length_zipIdx, he,
      List.map_cons, List.sum_cons] at hr ⊢
    omega

/-- A sum over the first components of a zip is at most the sum over the first list. -/
theorem sum_map_zip_fst_le {α β : Type} (f : α → ℕ) :
    ∀ (l₁ : List α) (l₂ : List β), ((l₁.zip l₂).map fun r ↦ f r.1).sum ≤ (l₁.map f).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l₁, _ :: l₂ => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    exact Nat.add_le_add_left (sum_map_zip_fst_le f l₁ l₂) _

/-- The six tables have `153` columns in all (`KECCAK`'s `92` the widest). -/
theorem tables_width_sum : (tables.map Table.width).sum = 153 := by decide +kernel

/-- The table sumcheck returns at most `153` claims, one per column of the six tables. -/
theorem retOK_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ 153)
      (tableSumcheckClaims heights busForms constraintPowers formPowers equalityPoint target) := by
  unfold tableSumcheckClaims
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨challenges, claim⟩ := r
  refine (retOK_tableTerms _ _ _ _ 0 0 []).bind fun r hr ↦ ?_
  obtain ⟨final, claims⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.ret ?_
  have hs := sum_map_zip_fst_le Table.width tables (List.zip heights (List.zip busForms
    (tableWeights heights equalityPoint challenges.reverse)))
  rw [tables_width_sum] at hs
  simp only [List.length_nil, Nat.zero_add] at hr
  omega

/-- The table phase returns the bus's claims and at most `153` more. -/
theorem retOK_tablePhase (layout : Layout) (bus : BusResult) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ bus.claims.length + 153)
      (tablePhaseClaims layout bus) := by
  unfold tablePhaseClaims
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (retOK_tableSumcheck _ _ _ _ _ _).bind fun claims hc ↦ RetOK.ret ?_
  simp only [List.length_append]
  omega

/-- The bus phase and the table sumcheck return at most `4 + 153 = 157` claims. -/
theorem retOK_busTable (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ 157)
      ((verifyBusBalance ev layout).bind (tablePhaseClaims layout)) :=
  (retOK_verifyBusBalance ev layout).bind fun bus hb ↦
    (retOK_tablePhase layout bus).mono fun _ h ↦ by omega

/-- The public-input phase returns two claims. -/
theorem retOK_publicInputPhase (layout : Layout) (publicInput : Digest) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ 2)
      (publicInputPhase layout publicInput) := by
  unfold publicInputPhase
  refine RetOK.bind_true fun _ ↦ RetOK.ret ?_
  simp only [List.length_zipWith, List.length_cons, List.length_nil]
  omega

end
end LeanVM.Protocol.EndToEnd.Sound
