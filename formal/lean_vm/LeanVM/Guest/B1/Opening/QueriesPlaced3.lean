/-
  LeanVM.Guest.B1.Opening.QueriesPlaced3

  The statements of `opening_queries`' loop bodies, by kind; a flat body's walk.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced2

/-!
# One iteration, placed: its statements by kind

An iteration's body is flat: its atoms and its path's `match`es of quiet arms (`oqLoop1A`,
`oqLoop0A`), then the tail's `callIf` and `ret []`. `AtomsOk.matchOk`, `AtomsOk.evs_holds`: a body
holding statement by statement (`BlockOk`) walks (`walk_flatM`) with every event holding.
`oqLoop1A_ok`, `oqLoop0A_ok`: its atoms by kind, its loads through the challenges, the final
coefficients, the positions, the window pointers and windows, the flags, the cap leaves and the
chain; no `frameAddr`, no `HeapBuf`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Statements by kind -/

theorem AtomsOk.mono {P Q : Atom → Prop} {ss : List Stmt} (h : AtomsOk P ss)
    (hPQ : ∀ a, P a → Q a) : AtomsOk Q ss := fun x hx ↦ by
  rcases h x hx with ⟨a, rfl, ha⟩ | hm
  · exact Or.inl ⟨a, rfl, hPQ a ha⟩
  · exact Or.inr hm

theorem AtomsOk.allocSz {L : V → ℕ → Prop} {F : V → List V → Prop} {ss : List Stmt}
    (h : AtomsOk (AtomKind L F) ss) : ss.filterMap Stmt.allocSz = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  rcases h x hx with ⟨a, rfl, ha⟩ | ⟨y, arms, rfl, -⟩ | ⟨f, args, rets, rfl⟩
  · cases a with
    | hint hh => cases hh <;> first | exact ha.elim | rfl
    | _ => rfl
  · rfl
  · rfl

/-- No call in a list of atoms. -/
theorem callS_atoms {ss : List Stmt} (h : AllAtoms ss) : ss.filterMap Stmt.callS = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := h x hx
  rfl

/-- No call in a flat body. -/
theorem callS_flat {ss : List Stmt} (h : Flat ss) : ss.filterMap Stmt.callS = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  rcases h x hx with ⟨a, rfl⟩ | ⟨y, arms, rfl, -⟩ <;> rfl

theorem AtomsOk.load {L : V → ℕ → Prop} {F : V → List V → Prop} {ss : List Stmt}
    (h : AtomsOk (AtomKind L F) ss) {q : V × ℕ} (hq : q ∈ ss.filterMap stmtLoad?) : L q.1 q.2 := by
  obtain ⟨x, hx, he⟩ := List.mem_filterMap.mp hq
  rcases h x hx with ⟨a, rfl, ha⟩ | ⟨y, arms, rfl, -⟩ | ⟨f, args, rets, rfl⟩
  · cases a with
    | load d p off =>
      simp only [stmtLoad?, Option.some.injEq] at he
      subst he; exact ha
    | _ => simp [stmtLoad?] at he
  · simp [stmtLoad?] at he
  · simp [stmtLoad?] at he

/-- No `frameAddr` in a body whose `frameAddr`s are none (`F = False`). -/
theorem AtomsOk.addrS {L : V → ℕ → Prop} {ss : List Stmt}
    (h : AtomsOk (AtomKind L fun _ _ ↦ False) ss) : ss.filterMap Stmt.addrS = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  rcases h x hx with ⟨a, rfl, ha⟩ | ⟨y, arms, rfl, -⟩ | ⟨f, args, rets, rfl⟩
  · cases a with
    | frameAddr p run => exact ha.elim
    | _ => rfl
  · rfl
  · rfl

/-- **A body holding statement by statement names the arms its `match`es take.** -/
theorem AtomsOk.matchOk {P : Atom → Prop} {ss : List Stmt} (h : AtomsOk P ss) {C : CallRel}
    {rd : Reader} {σ : Val} (hb : BlockOkC C rd σ ss) : ∀ x ∈ ss, MatchOk σ x := fun x hx ↦ by
  rcases h x hx with ⟨a, rfl, -⟩ | ⟨y, arms, rfl, -, hl⟩ | ⟨f, args, rets, rfl⟩
  · trivial
  · obtain ⟨j, hj, hy, -⟩ := hb _ hx
    exact ⟨hl, j, hj, hy⟩
  · trivial

/-- **A body holding statement by statement: its walk's events hold.** -/
theorem AtomsOk.evs_holds {P : Atom → Prop} {ss : List Stmt} (h : AtomsOk P ss) {C : CallRel}
    {rd : Reader} {σ : Val} (hb : BlockOkC C rd σ ss) : ∀ e ∈ ss.flatMap (fmEvs σ), e.Holds rd σ := by
  intro e he
  obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp he
  rcases h x hx with ⟨a, rfl, -⟩ | ⟨y, arms, rfl, -, hl⟩ | ⟨f, args, rets, rfl⟩
  · simp only [fmEvs, slEvs, List.mem_singleton] at he
    subst he
    exact hb _ hx
  · obtain ⟨j, hj, hy, ha⟩ := hb _ hx
    exact fmEvs_match hj hl hy ha e he
  · simp only [fmEvs, slEvs, List.mem_singleton] at he
    subst he
    trivial

/-- An address of the region `R`. -/
def OqIn (R : ℕ → Prop) (A : K) : Prop := ∃ i, A = Parameters.addressOfIndex i ∧ R i

theorem addr_gpow (c k off : ℕ) :
    (ofK (Parameters.addressOfIndex c) * gen ^ k).limb 0 * Parameters.addressOfIndex off =
      Parameters.addressOfIndex (c + k + off) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, gpow_add', limb_ofK]
  simp [gpow_add']

/-- A loop's guard, by kind: no load. -/
theorem oqGuardA_ok {L : V → ℕ → Prop} {F : V → List V → Prop} (g : ℕ) :
    AtomsOk (AtomKind L F) (oqGuardA g) :=
  atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
    (atomsOk_cons trivial atomsOk_nil))))

/-! ## A level-0 iteration's atoms by kind -/

/-- The loads of a level-0 iteration: its queries', the points and the window pointers at
`positions·x²`, `qptrs·x²` offsets `odd`, `odd + 1`, the chain (non-final levels). -/
def OqIt1L (s : Oq) (odd : ℕ) (p : V) (off : ℕ) : Prop :=
  OqQLoad s (.n 6) (.n 7) p off ∨ (p = .n 11 ∧ (off = odd ∨ off = odd + 1)) ∨
    (p = .n 13 ∧ (off = odd ∨ off = odd + 1)) ∨ (s.final ≠ 1 ∧ p = .n (oqC1 s) ∧ off = 0) ∨
    (s.final ≠ 1 ∧ p = .n (oqC1 s + 6) ∧ off = 1)

theorem oqLoop1A_ok (s : Oq) (odd : ℕ) (walk : String) :
    AtomsOk (AtomKind (OqIt1L s odd) fun _ _ ↦ False) (oqLoop1A s odd walk) := by
  unfold oqLoop1A
  dsimp only
  refine atomsOk_append (atomsOk_append (atomsOk_append (atomsOk_append (atomsOk_append ?_ ?_) ?_)
    ?_) ?_) (oqGuardA_ok _)
  · exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))
      (atomsOk_cons (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))) atomsOk_nil)))))
  · exact (oqQuery_atoms_ok _ _ _ _ _ _ _ _ _ _).mono fun a ha ↦
      AtomKind.mono (fun p off h ↦ Or.inl h) (fun p run h ↦ h) ha
  · exact atomsOk_cons (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
      (atomsOk_cons (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))) atomsOk_nil)
  · exact (oqQuery_atoms_ok _ _ _ _ _ _ _ _ _ _).mono fun a ha ↦
      AtomKind.mono (fun p off h ↦ Or.inl h) (fun p run h ↦ h) ha
  · split
    · exact atomsOk_nil
    · rename_i h
      exact atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl, rfl⟩))))
        (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
        (atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, rfl, rfl⟩))))
        atomsOk_nil)))))))

/-! ## A deeper iteration's atoms by kind -/

/-- The loads of a deeper iteration: its query's, its point `positions[x]`, its window pointer
`qptrs[x]`, the chain (non-final levels). -/
def OqIt0L (s : Oq) (p : V) (off : ℕ) : Prop :=
  OqQLoad s (.n 6) (.n 7) p off ∨ (p = .n 10 ∧ off = 0) ∨ (p = .n 12 ∧ off = 0) ∨
    (s.final ≠ 1 ∧ p = .n (oqC0 s) ∧ off = 0) ∨ (s.final ≠ 1 ∧ p = .n (oqC0 s + 4) ∧ off = 1)

theorem oqLoop0A_ok (s : Oq) (walk : String) :
    AtomsOk (AtomKind (OqIt0L s) fun _ _ ↦ False) (oqLoop0A s walk) := by
  unfold oqLoop0A
  dsimp only
  refine atomsOk_append (atomsOk_append (atomsOk_append ?_ ?_) ?_) (oqGuardA_ok _)
  · exact atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inl ⟨rfl, rfl⟩)) (atomsOk_cons trivial
      (atomsOk_cons (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) atomsOk_nil)))
  · exact (oqQuery_atoms_ok _ _ _ _ _ _ _ _ _ _).mono fun a ha ↦
      AtomKind.mono (fun p off h ↦ Or.inl h) (fun p run h ↦ h) ha
  · split
    · exact atomsOk_nil
    · rename_i h
      exact atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl, rfl⟩))))
        (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
        (atomsOk_cons (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, rfl, rfl⟩)))) atomsOk_nil)))))

/-! ## The calls -/

/-- A query's one call: `walk_path`'s. -/
theorem oqQueryT_callS (s : Oq) (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool) (pr : ℕ)
    (walk : String) :
    (oqQueryT s x bp cap flags coefs hs b emit pr walk).filterMap Stmt.callS =
      [(none, walk, [.n (oqOut s (oqKL s b emit) (s.B - 1) 0), .n (oqOut s (oqKL s b emit) (s.B - 1) 1),
        bp, cap, flags], [])] := by
  have h1 : AllAtoms (oqPrepT s b ++ (if emit then oqPadT (oqK1 s b) else []) ++
      oqLeafT s b (oqPr s b emit pr) (oqKL s b emit)) := by
    refine allAtoms_append (allAtoms_append (oqPrepT_atoms _ _) ?_) (oqLeafT_atoms _ _ _ _)
    split
    · exact oqPadT_atoms _
    · exact allAtoms_nil
  have h2 : AllAtoms (oqFoldT s coefs x b (oqCh s b emit) ++
      (if s.final = 1 then oqFinT s x hs (oqVal s (oqCh s b emit)) else [])) := by
    refine allAtoms_append (oqFoldT_atoms _ _ _ _ _) ?_
    split
    · exact oqFinT_atoms _ _ _ _
    · exact allAtoms_nil
  rw [QD.oqQueryT_eq, List.filterMap_append, List.filterMap_append, callS_atoms h1, callS_atoms h2]
  rfl

end
end LeanVM.Guest.B1
