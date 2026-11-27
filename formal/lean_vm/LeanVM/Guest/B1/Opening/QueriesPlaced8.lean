/-
  LeanVM.Guest.B1.Opening.QueriesPlaced8

  `opening_queries`' start by kind: its chain buffer its own data, no `frameAddr`, no call.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced7
import LeanVM.Guest.StmtsAppend

/-!
# The function's start by kind

`oqStartFlat s even`: the start's statements with level 0's branch taken (`oqEvenT` when `even`,
`oqOddT` otherwise), a flat list. `oqStart_ok`: its atoms by kind: its chain buffer
(`HeapBuf(g^(N+1))`, `allocDyn`), its loads (its odd first query's, its point and window pointer,
the chain's first word), no `frameAddr`; `oqStart_allocSz`, `oqStart_callS`: its one `HeapBuf`, no
call.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The function's start, level 0's branch taken: the even start when `even`, the odd query
otherwise. -/
def oqStartFlat (s : Oq) (even : Bool) : List Stmt :=
  if s.base = 1 then oqMainPre ⧺ (if even then oqEvenT else oqOddT s) ⧺ oqMainPost s else oqMainA s

/-- The loads of the function's own body: its odd first query's, its point `positions[0]`, its
window pointer `qptrs[0]`, the chain's first word. -/
def OqMainL (s : Oq) (even : Bool) (p : V) (off : ℕ) : Prop :=
  (s.base = 1 ∧ even = false ∧ OqQLoad s (.n oqMCoefs) (.n oqMHs) (.n 16) (oqCh s 17 true) p off) ∨
    (s.base = 1 ∧ even = false ∧ p = .n oqMPos ∧ off = 0) ∨
    (s.base = 1 ∧ even = false ∧ p = .n oqMQp ∧ off = 0) ∨ (p = .n 11 ∧ off = 0)

/-- The chain's `HeapBuf`. -/
def oqAlloc : Atom := .hint (.allocDyn (.n 11) (.n 10))

theorem oqStart_ok (s : Oq) (even : Bool) :
    AtomsOk (fun a ↦ AtomKind (OqMainL s even) (fun _ _ ↦ False) a ∨ a = oqAlloc) (oqStartFlat s even) := by
  unfold oqStartFlat
  split
  · rename_i hb
    refine atomsOk_append (atomsOk_append ?_ ?_) ?_
    · exact atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inr rfl)
        (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial) atomsOk_nil))))
    · split
      · exact atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
          atomsOk_nil)
      · rename_i he
        have he' : even = false := by simpa using he
        refine atomsOk_append (atomsOk_append (atomsOk_cons (Or.inl (Or.inr (Or.inl ⟨hb, he', rfl, rfl⟩)))
          (atomsOk_cons (Or.inl (Or.inr (Or.inr (Or.inl ⟨hb, he', rfl, rfl⟩)))) atomsOk_nil)) ?_)
          (atomsOk_cons (Or.inl trivial)
          (atomsOk_cons (Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) atomsOk_nil))
        exact (oqQuery_atoms_ok _ _ _ _ _ _ _ _ _).mono fun a ha ↦
          Or.inl (AtomKind.mono (fun p off h ↦ Or.inl ⟨hb, he', h⟩) (fun p run h ↦ h) ha)
    · exact atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial)
        (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial) atomsOk_nil))))
  · rename_i hb
    simp only [oqMainA, hb, ↓reduceIte]
    exact atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inr rfl)
      (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
      (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial) (atomsOk_cons (Or.inl trivial)
      atomsOk_nil)))))))

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

theorem oqStart_allocSz (s : Oq) (even : Bool) :
    (oqStartFlat s even).filterMap Stmt.allocSz = [(.n 11, .inr (.n 10))] := by
  unfold oqStartFlat
  split
  · have h2 : (if even then oqEvenT else oqOddT s).filterMap Stmt.allocSz = [] := by
      split
      · rfl
      · unfold oqOddT
        rw [List.filterMap_append, List.filterMap_append,
          AtomsOk.allocSz (oqQuery_atoms_ok _ _ _ _ _ _ _ _ _)]
        rfl
    rw [List.filterMap_append, List.filterMap_append, h2]
    rfl
  · rename_i hb
    simp only [oqMainA, hb, ↓reduceIte]
    rfl

/-- The function's start calls nothing. -/
theorem oqStart_callS (s : Oq) (even : Bool) : (oqStartFlat s even).filterMap Stmt.callS = [] := by
  unfold oqStartFlat
  split
  · rename_i hb
    refine callS_flat (flat_append (flat_append (flat_of_atoms oqMainPre_atoms) ?_)
      (flat_of_atoms (oqMainPost_atoms s)))
    split
    · exact flat_of_atoms oqEvenT_atoms
    · exact oqOddT_flat s
  · rename_i hb
    exact callS_flat (oqMainA_flat hb)

end
end LeanVM.Guest.B1
