/-
  LeanVM.Guest.B1.Place.ArmExactAll

  Every arm of `open_stacked` passes the exactness check, so its node is exact at every node once its `is_zero` and
  `level_positions` callees' trees are.
-/

module

public import LeanVM.Guest.B1.Place.ArmExact0
public import LeanVM.Guest.B1.Place.ArmExact1
public import LeanVM.Guest.B1.Place.ArmExact2
public import LeanVM.Guest.B1.Place.ArmExact3
public import LeanVM.Guest.B1.Place.ArmExact4
public import LeanVM.Guest.B1.Place.ArmExact5
public import LeanVM.Guest.B1.Place.ArmExactB
public import LeanVM.Guest.B1.Place.ArmExactC
public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.B1.Whir.Sound
public import LeanVM.Guest.B1.Whir.WinEx
public import LeanVM.Guest.B2C.Table

/-!
# The arms, exact at every node

`armExact_all`: the arm of `μ` passes `armExactOk` (`ArmExact0` to `ArmExact5`, `ArmExactB`, `ArmExactC`). `flatNodeT_every`: so a valid tree of
it satisfying `FlatNodeT` is exact at every node, given that each entered `armExactS` callee's predicate (its
`is_zero`, `level_positions`) gives `Every` exact on its valid trees; every other callee is exact
for free. `winHint_exact_of_winEx`: a flat body's window hints exact (`WinEx`, the honest valuation's) give the window
hints on its path exact, as `flatNodeT_every` asks.
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

/-- **A valid arm node of `FlatNodeT` is exact at every node** when its window hints are exact at the valuations
`Q` admits, its predicates cover its calls and each entered `armExactS` callee's predicate gives `Every` exact on its
valid trees. -/
theorem flatNodeT_every {μ : ℕ} (hm : μ - minOpenLog < 11) {fn : Fn} {pre : List Stmt} {Q : Val → Prop}
    {Ts : Val → Reader → List (Memory.Tree → Prop)} {rd : Reader} {t : Memory.Tree} {args rets : List E}
    (hf : coreProgram.find? (openName μ) = some fn) (h : FlatNodeT (openName μ) fn pre Q Ts rd t)
    (hv : t.Valid coreProgram rd args rets)
    (hW : ∀ σ es vs, Q σ → walk σ fn.body = .ret es vs → ∀ a, Ev.atom a ∈ es → isWinHint a = true →
      a.Exact rd σ)
    (hlen : ∀ σ, (pre.filterMap (Stmt.callSF σ)).length ≤ (Ts σ rd).length)
    (hE : ∀ σ c T, (c, T) ∈ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)).zip (Ts σ rd) → c.taken = true →
      armExactS c.f = true → ∀ t : Memory.Tree, t.name = c.f → t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ) →
      T t → t.Every (ExactAt coreProgram rd)) :
    t.Every (ExactAt coreProgram rd) := by
  obtain ⟨σ, bufs, ks, es, vs, rfl, hw, hc, hQ, hK⟩ := h
  obtain ⟨j, hj⟩ := armExact_all hm
  refine armExact_every (Ts := Ts σ rd) hj hv (fun fn' es' vs' hf' hw' => ?_) fun fn' es' vs' hf' hw' => ?_
  · rw [hf, Option.some.injEq] at hf'
    subst hf'
    exact hW σ es' vs' hQ hw'
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  rw [hw, Out.ret.injEq] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  rw [hc]
  exact ⟨by simpa using hlen σ, hc ▸ hK, hE σ⟩

theorem mem_blockAtoms_of_atoms {a : Atom} : ∀ {arm : List Stmt}, arm.all Whir.Stmt.isAtom = true →
    a ∈ B2C.blockAtoms arm → Stmt.atom a ∈ arm
  | [], _, h => by simp [B2C.blockAtoms] at h
  | s :: ss, hat, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hat
    simp only [B2C.blockAtoms, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | atom b =>
        simp only [B2C.stmtAtoms, List.mem_singleton] at h
        subst h
        exact List.mem_cons_self
      | _ => simp [Whir.Stmt.isAtom] at hat
    · exact List.mem_cons_of_mem _ (mem_blockAtoms_of_atoms hat.2 h)

theorem mem_armsAtoms {a : Atom} : ∀ {arms : List (List Stmt)}, a ∈ B2C.armsAtoms arms →
    ∃ arm ∈ arms, a ∈ B2C.blockAtoms arm
  | [], h => by simp [B2C.armsAtoms] at h
  | arm :: arms, h => by
    simp only [B2C.armsAtoms, List.mem_append] at h
    rcases h with h | h
    · exact ⟨arm, List.mem_cons_self, h⟩
    · obtain ⟨arm', h1, h2⟩ := mem_armsAtoms h
      exact ⟨arm', List.mem_cons_of_mem _ h1, h2⟩

/-- A flat block's atoms, its `match` arms' included, are window-exact where the block's window hints are. -/
theorem winA_of_blockAtoms {σ : Val} : ∀ {ss : List Stmt}, ss.all Whir.Stmt.flat = true → WinEx ss σ →
    ∀ a ∈ B2C.blockAtoms ss, WinA σ a
  | [], _, _, a, h => by simp [B2C.blockAtoms] at h
  | s :: ss, hfl, hW, a, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hfl
    simp only [B2C.blockAtoms, List.mem_append] at h
    rcases h with h | h
    · have hs := hW s List.mem_cons_self
      cases s with
      | atom b =>
        simp only [B2C.stmtAtoms, List.mem_singleton] at h
        subst h
        exact hs
      | match_ x arms =>
        simp only [B2C.stmtAtoms] at h
        obtain ⟨arm, harm, ha⟩ := mem_armsAtoms h
        have hf : arms.all (fun arm ↦ arm.all Whir.Stmt.isAtom) = true := hfl.1
        exact hs arm harm a (mem_blockAtoms_of_atoms (List.all_eq_true.mp hf arm harm) ha)
      | ite c z n => simp [Whir.Stmt.flat] at hfl
      | _ => simp [B2C.stmtAtoms] at h
    · exact winA_of_blockAtoms hfl.2 (fun t ht ↦ hW t (List.mem_cons_of_mem _ ht)) a h

/-- **The window hints on a flat body's path are exact** where the body's are (`WinEx`). -/
theorem winHint_exact_of_winEx {σ : Val} {pre : List Stmt} {body : List Stmt} {vs : List V}
    (hb : body = pre ++ [.ret vs]) (hfl : pre.all Whir.Stmt.flat = true) (hW : WinEx pre σ) {es : List Ev}
    {vs' : List V} (hw : walk σ body = .ret es vs') (rd : Reader) :
    ∀ a, Ev.atom a ∈ es → isWinHint a = true → a.Exact rd σ := by
  intro a ha hwin
  have hm : a ∈ B2C.blockAtoms body := B2C.walk_blockAtoms body (by rw [hw]; exact ha)
  have hpre : a ∈ B2C.blockAtoms pre := by
    have e : ∀ ss : List Stmt, a ∈ B2C.blockAtoms (ss ++ [.ret vs]) → a ∈ B2C.blockAtoms ss := by
      intro ss
      induction ss with
      | nil => simp [B2C.blockAtoms, B2C.stmtAtoms]
      | cons s ss ih =>
        simp only [List.cons_append, B2C.blockAtoms, List.mem_append]
        exact fun h ↦ h.imp_right ih
    exact e pre (hb ▸ hm)
  refine winA_of_blockAtoms hfl hW a hpre ?_ rd
  unfold isWinHint at hwin
  split at hwin
  · rfl
  · exact absurd hwin Bool.false_ne_true

end
end LeanVM.Guest.B1.Arm
