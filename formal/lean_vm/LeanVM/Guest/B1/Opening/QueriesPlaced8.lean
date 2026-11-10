/-
  LeanVM.Guest.B1.Opening.QueriesPlaced8

  `opening_queries`' start by kind: its chain buffer its own data, no `frameAddr`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced7

/-!
# The function, placed

`oqMainA_ok`: the start of `opening_queries` by kind: its chain buffer (`HeapBuf(g^(N+1))`,
`allocDyn`), its loads (its odd first query's, its point and window pointer, the chain's first
word), no `frameAddr`; `oqMainA_allocSz`, `oqMainA_callS`: its one `HeapBuf` and its one call
(the odd first query's walk).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The loads of the function's own body: its odd first query's, its point `positions[0]`, its
window pointer `qptrs[0]`, the chain's first word. -/
def OqMainL (s : Oq) (odd : ℕ) (p : V) (off : ℕ) : Prop :=
  (odd = 1 ∧ OqQLoad s (.n 3) (.n 4) p off) ∨ (odd = 1 ∧ p = .n 5 ∧ off = 0) ∨
    (odd = 1 ∧ p = .n 6 ∧ off = 0) ∨ (p = .n 10 ∧ off = 0)

/-- The chain's `HeapBuf`. -/
def oqAlloc : Atom := .hint (.allocDyn (.n 10) (.n 9))

theorem oqMainA_ok (s : Oq) (odd : ℕ) (walk : String) :
    AtomsOk (fun a ↦ AtomKind (OqMainL s odd) (fun _ _ ↦ False) a ∨ a = oqAlloc)
      (oqMainA s odd walk) := by
  unfold oqMainA
  refine atomsOk_append (atomsOk_append ?_ ?_) ?_
  · exact atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inr rfl)
      atomsOk_nil))
  · split_ifs with h1
    · refine atomsOk_append (atomsOk_append (atomsOk_cons (Or.inl (Or.inr (Or.inl ⟨h1, rfl, rfl⟩)))
        (atomsOk_cons (Or.inl (Or.inr (Or.inr (Or.inl ⟨h1, rfl, rfl⟩)))) atomsOk_nil)) ?_)
        (atomsOk_cons (Or.inl trivial)
        (atomsOk_cons (Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) atomsOk_nil))
      exact (oqQuery_atoms_ok _ _ _ _ _ _ _ _ _ _).mono fun a ha ↦
        Or.inl (AtomKind.mono (fun p off h ↦ Or.inl ⟨h1, h⟩) (fun p run h ↦ h) ha)
    · exact atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
        atomsOk_nil)
  · exact atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial)
      atomsOk_nil))

theorem AtomsOk.load' {L : V → ℕ → Prop} {F : V → List V → Prop} {b : Atom}
    (hb : ∀ d p off, b ≠ .load d p off) {ss : List Stmt}
    (h : AtomsOk (fun a ↦ AtomKind L F a ∨ a = b) ss) {q : V × ℕ}
    (hq : q ∈ ss.filterMap stmtLoad?) : L q.1 q.2 := by
  obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp hq
  rcases h x hx with ⟨a, rfl, ha | rfl⟩ | ⟨y, arms, rfl, -⟩ | ⟨f, args, rets, rfl⟩
  · cases a with
    | load d p off =>
      simp only [stmtLoad?, Option.some.injEq] at he
      subst he; exact ha
    | _ => simp [stmtLoad?] at he
  · cases a with
    | load d p off => exact absurd rfl (hb d p off)
    | _ => simp [stmtLoad?] at he
  · simp [stmtLoad?] at he
  · simp [stmtLoad?] at he

theorem AtomsOk.addrS' {L : V → ℕ → Prop} {b : Atom} (hb : ∀ p run, b ≠ .frameAddr p run)
    {ss : List Stmt} (h : AtomsOk (fun a ↦ AtomKind L (fun _ _ ↦ False) a ∨ a = b) ss) :
    ss.filterMap Stmt.addrS = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  rcases h x hx with ⟨a, rfl, ha | rfl⟩ | ⟨y, arms, rfl, -⟩ | ⟨f, args, rets, rfl⟩
  · cases a with
    | frameAddr p run => exact ha.elim
    | _ => rfl
  · cases a with
    | frameAddr p run => exact absurd rfl (hb p run)
    | _ => rfl
  · rfl
  · rfl

theorem oqMainA_allocSz (s : Oq) (odd : ℕ) (walk : String) :
    (oqMainA s odd walk).filterMap Stmt.allocSz = [(.n 10, .inr (.n 9))] := by
  unfold oqMainA
  rw [List.filterMap_append, List.filterMap_append]
  have h2 : (if odd = 1 then [Stmt.atom (.load (.n 11) (.n 5) 0), .atom (.load (.n 12) (.n 6) 0)] ++
      oqQueryT s (.n 11) (.n 12) (.n 0) (.n 1) (.n 3) (.n 4) 13 true 0 walk ++
      [.atom (.mul (.n (oqMK s odd - 1)) (.n (oqRes s 13 true)) (.n 2)),
        .atom (.load (.n (oqMK s odd - 1)) (.n 10) 0)]
      else [.atom (.const (.n 11) (word 0 0)), .atom (.load (.n 11) (.n 10) 0)]).filterMap
        Stmt.allocSz = [] := by
    split_ifs
    · rw [List.filterMap_append, List.filterMap_append,
        AtomsOk.allocSz (oqQuery_atoms_ok _ _ _ _ _ _ _ _ _ _)]
      rfl
    · rfl
  rw [h2]
  rfl

/-- The function's start's call: its odd first query's walk. -/
theorem oqMainA_callS (s : Oq) (odd : ℕ) (walk : String) :
    (oqMainA s odd walk).filterMap Stmt.callS =
      if odd = 1 then [(none, walk, [.n (oqOut s (oqKL s 13 true) (s.B - 1) 0),
        .n (oqOut s (oqKL s 13 true) (s.B - 1) 1), .n 12, .n 0, .n 1], [])] else [] := by
  unfold oqMainA
  split_ifs
  · simp only [List.filterMap_append, oqQueryT_callS]
    rfl
  · rfl

end
end LeanVM.Guest.B1
