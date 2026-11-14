/-
  LeanVM.Guest.B1.Place.ArmExactAll

  Every arm of `open_stacked` passes the exactness check, so its node is exact at every node once its `level_positions`,
  `opening_round` and grind check callees' trees are.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactA
public import LeanVM.Guest.B1.Place.ArmExactB
public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.B1.Whir.Sound

/-!
# The arms, exact at every node

`armExact_all`: the arm of `μ` passes `armExactOk` (`ArmExactA`, `ArmExactB`). `flatNodeT_every`: so a valid tree of
it satisfying `FlatNodeT` is exact at every node, given that each entered `armExactS` callee's predicate (its
`level_positions`, `opening_round`, grind checks) gives `Every` exact on its valid trees; every other callee is exact
for free.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- **The arm of `μ` passes the exactness check.** -/
theorem armExact_all {μ : ℕ} (hm : μ - minOpenLog < 11) : ∃ j, armExactOk (openName μ) j = true := by
  rw [openName_eq hm]
  generalize μ - minOpenLog = m at hm
  interval_cases m
  · exact ⟨_, armExact0⟩
  · exact ⟨_, armExact1⟩
  · exact ⟨_, armExact2⟩
  · exact ⟨_, armExact3⟩
  · exact ⟨_, armExact4⟩
  · exact ⟨_, armExact5⟩
  · exact ⟨_, armExact6⟩
  · exact ⟨_, armExact7⟩
  · exact ⟨_, armExact8⟩
  · exact ⟨_, armExact9⟩
  · exact ⟨_, armExact10⟩

/-- **A valid arm node of `FlatNodeT` is exact at every node** when its predicates cover its calls and each entered
`armExactS` callee's predicate gives `Every` exact on its valid trees. -/
theorem flatNodeT_every {μ : ℕ} (hm : μ - minOpenLog < 11) {fn : Fn} {pre : List Stmt} {Q : Val → Prop}
    {Ts : Val → Reader → List (Memory.Tree → Prop)} {rd : Reader} {t : Memory.Tree} {args rets : List E}
    (hf : coreProgram.find? (openName μ) = some fn) (h : FlatNodeT (openName μ) fn pre Q Ts rd t)
    (hv : t.Valid coreProgram rd args rets)
    (hlen : ∀ σ, (pre.filterMap (Stmt.callSF σ)).length ≤ (Ts σ rd).length)
    (hE : ∀ σ c T, (c, T) ∈ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)).zip (Ts σ rd) → c.taken = true →
      armExactS c.f = true → ∀ t : Memory.Tree, t.name = c.f → t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ) →
      T t → t.Every (ExactAt coreProgram rd)) :
    t.Every (ExactAt coreProgram rd) := by
  obtain ⟨σ, bufs, ks, es, vs, rfl, hw, hc, -, hK⟩ := h
  obtain ⟨j, hj⟩ := armExact_all hm
  refine armExact_every (Ts := Ts σ rd) hj hv fun fn' es' vs' hf' hw' => ?_
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  rw [hw, Out.ret.injEq] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  rw [hc]
  exact ⟨by simpa using hlen σ, hc ▸ hK, hE σ⟩

end
end LeanVM.Guest.B1.Arm
