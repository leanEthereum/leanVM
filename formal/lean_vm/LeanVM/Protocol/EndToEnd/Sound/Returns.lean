/-
  LeanVM.Protocol.EndToEnd.Sound.Returns

  What a verifier program returns: a return invariant on programs of the verifier language, its
  rules, and the bound on the number of column claims the front phases of leanVM's deployed
  verifier program return.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Basic
public import LeanVM.Protocol.Verifier.Cost

/-!
# The returns of the leanVM verifier

`RetOK Q p` says that every value `p` returns, along any history, satisfies `Q`. It is a
property of the program alone, with no probability, and it composes through `bind`
(`RetOK.bind`): a sequence returns only what its continuation returns on a value its first part
returns.

The instances bound the column claims the front phases of `leanVmProgram`
(`LeanVM.Protocol.Verifier`) return, with the unfoldings and inductions of
`LeanVM.Protocol.Verifier.Cost`:

* `retOK_verifyBusBalance`: the bus phase returns at most five framework claims (the three memory
  columns and the two final counters);
* `retOK_busTable`: the bus phase followed by the table sumcheck returns at most `5 + 6 · 37 = 227`
  claims, every one of the six tables contributing one claim per column and being at most `37`
  columns wide (`tables_width_le`);
* `retOK_publicInputPhase`: the public-input phase returns at most three claims.

## Deployed behaviour

The statements are on the program `leanVmProgram` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, as transcribed in `LeanVM.Protocol.Verifier`.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {α β : Type}

/-! ## The return invariant -/

/-- Every return of `p` satisfies `Q`. -/
def RetOK (Q : α → Prop) (p : Prog α) : Prop :=
  ∀ (l : List Ev) (a : α), p.after l = some (.ret a) → Q a

/-- A weaker predicate holds of every return. -/
theorem RetOK.mono {Q Q' : α → Prop} {p : Prog α} (h : RetOK Q p) (hQ : ∀ a, Q a → Q' a) :
    RetOK Q' p :=
  fun l a hl ↦ hQ a (h l a hl)

/-- A program that returns at once returns its value. -/
theorem RetOK.ret {Q : α → Prop} {a : α} (h : Q a) : RetOK Q (Prog.ret a) := by
  intro l b hl
  cases l with
  | nil =>
    simp only [Prog.after, Option.some.injEq, Prog.ret.injEq] at hl
    exact hl ▸ h
  | cons e l => cases e <;> simp [Prog.after] at hl

/-- A rejecting program returns nothing. -/
theorem RetOK.fail {Q : α → Prop} : RetOK Q (Prog.fail : Prog α) := by
  intro l b hl
  cases l with
  | nil => simp [Prog.after] at hl
  | cons e l => cases e <;> simp [Prog.after] at hl

/-- The trivial predicate holds of every return. -/
theorem RetOK.true (p : Prog α) : RetOK (fun _ ↦ True) p :=
  fun _ _ _ ↦ trivial

/-- A sequence that returns at once: both parts return. -/
private theorem bind_eq_ret' {p : Prog α} {f : α → Prog β} {b : β} (h : p.bind f = .ret b) :
    ∃ a, p = .ret a ∧ f a = .ret b := by
  cases p <;> simp_all [Prog.bind]

/-- A sequence returns what its continuation returns on a return of its first part. -/
theorem RetOK.bind {Q' : α → Prop} {Q : β → Prop} {p : Prog α} {f : α → Prog β}
    (hp : RetOK Q' p) (hf : ∀ a, Q' a → RetOK Q (f a)) : RetOK Q (p.bind f) := by
  intro l b hl
  rcases Prog.after_bind_cases f hl with ⟨q, hq, hr⟩ | ⟨a, l₁, l₂, -, h1, -, h2⟩
  · obtain ⟨a, rfl, hfa⟩ := bind_eq_ret' hr.symm
    exact hf a (hp l a hq) [] b (by simp [Prog.after, hfa])
  · exact hf a (hp l₁ a h1) l₂ b h2

/-- A sequence whose continuation's returns satisfy `Q` whatever the first part returns. -/
theorem RetOK.bind_true {Q : β → Prop} {p : Prog α} {f : α → Prog β}
    (hf : ∀ a, RetOK Q (f a)) : RetOK Q (p.bind f) :=
  (RetOK.true p).bind fun a _ ↦ hf a

/-- `readN n` returns `n` scalars. -/
theorem RetOK.readN : ∀ n : ℕ, RetOK (fun xs : List E ↦ xs.length = n) (Prog.readN n)
  | 0 => RetOK.ret rfl
  | n + 1 => RetOK.bind_true fun _ ↦ (RetOK.readN n).bind fun xs hxs ↦
      RetOK.ret (by simp [hxs])

/-! ## The front phases of the leanVM verifier -/

/-- The bus phase returns at most five framework claims. -/
theorem retOK_verifyBusBalance (layout : Layout) :
    RetOK (fun bus : BusResult ↦ bus.claims.length ≤ 5) (verifyBusBalance .computed layout) := by
  unfold verifyBusBalance
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun r ↦ ?_
  obtain ⟨countRoot, point, treeValues⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.bind_true fun memory ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ RetOK.ret ?_
  simp only [List.length_append, List.length_zipWith, List.length_cons, List.length_nil]
  omega

/-- The tables' row evaluations: at most `w` claims per row, added to the claims so far. -/
theorem retOK_tableTerms (constraintPowers formPowers point : List E) (w : ℕ) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), (∀ r ∈ rows, r.1.width ≤ w) →
      RetOK (fun r : E × List ColumnClaim ↦ r.2.length ≤ claims.length + rows.length * w)
        (tableTerms constraintPowers formPowers point rows cursor final claims)
  | [], _, _, _, _ => RetOK.ret (by simp)
  | (table, h, forms, weight) :: rest, cursor, final, claims, hw => by
    have h0 := hw _ List.mem_cons_self
    refine (RetOK.readN table.width).bind fun evaluations he ↦
      (retOK_tableTerms constraintPowers formPowers point w rest _ _ _
        fun r hr ↦ hw r (List.mem_cons_of_mem _ hr)).mono fun r hr ↦ ?_
    simp only [List.length_append, List.length_map, List.length_zipIdx, he,
      List.length_cons, Nat.succ_mul] at hr h0 ⊢
    omega

/-- The table sumcheck returns at most `6 · 37` claims. -/
theorem retOK_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ 6 * 37)
      (tableSumcheck heights busForms constraintPowers formPowers equalityPoint target) := by
  unfold tableSumcheck
  refine RetOK.bind_true fun r ↦ ?_
  obtain ⟨challenges, claim⟩ := r
  have hrows : ∀ r ∈ List.zip tables (List.zip heights (List.zip busForms
      (tableWeights heights equalityPoint challenges.reverse))), r.1.width ≤ 37 :=
    fun r hr ↦ tables_width_le _ (List.of_mem_zip hr).1
  have hlen : (List.zip tables (List.zip heights (List.zip busForms
      (tableWeights heights equalityPoint challenges.reverse)))).length ≤ 6 := by
    simp only [List.length_zip]
    exact (min_le_left _ _).trans (by simp [tables])
  refine (retOK_tableTerms _ _ _ 37 _ 0 0 [] hrows).bind fun r hr ↦ ?_
  obtain ⟨final, claims⟩ := r
  refine RetOK.bind_true fun _ ↦ RetOK.ret ?_
  simp only [List.length_nil, Nat.zero_add] at hr
  have := Nat.mul_le_mul_right 37 hlen
  omega

/-- The table phase returns the bus's claims and at most `6 · 37` more. -/
theorem retOK_tablePhase (layout : Layout) (bus : BusResult) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ bus.claims.length + 6 * 37)
      (tablePhase layout bus) := by
  unfold tablePhase
  refine RetOK.bind_true fun _ ↦ (retOK_tableSumcheck _ _ _ _ _ _).bind fun claims hc ↦
    RetOK.ret ?_
  simp only [List.length_append]
  omega

/-- The bus phase and the table sumcheck return at most `5 + 6·37` claims. -/
theorem retOK_busTable (layout : Layout) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ 227)
      ((verifyBusBalance .computed layout).bind (tablePhase layout)) :=
  (retOK_verifyBusBalance layout).bind fun bus hb ↦
    (retOK_tablePhase layout bus).mono fun _ h ↦ by omega

/-- The public-input phase returns three claims. -/
theorem retOK_publicInputPhase (layout : Layout) (publicInput : Digest) :
    RetOK (fun claims : List ColumnClaim ↦ claims.length ≤ 3)
      (publicInputPhase layout publicInput) := by
  unfold publicInputPhase
  refine RetOK.bind_true fun _ ↦ RetOK.ret ?_
  simp only [List.length_zipWith, List.length_cons, List.length_nil]
  omega

end
end LeanVM.Protocol.EndToEnd.Sound
