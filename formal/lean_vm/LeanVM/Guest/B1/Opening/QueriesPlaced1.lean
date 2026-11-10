/-
  LeanVM.Guest.B1.Opening.QueriesPlaced1

  The statements of `opening_queries`' templates, by kind: their loads and where they read, no
  `frameAddr` and no `HeapBuf` in a query.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesMain
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.B1.Opening.WalkMatch

/-!
# The statements of `opening_queries`, by kind

The placed form (`RelAtIn`) needs, of a body, its `HeapBuf`s, its `frameAddr`s (a query has
none), its calls and where its loads read. `OqAtomOk`: an atom of a query is a load reading the
fold's challenges (`coefs`, below `3·folds`) or, at the final level, the final coefficients (`hs`,
below `n_hs`), or neither a load, a `frameAddr` nor a `HeapBuf`; `OqWAtomOk`:
an atom of `walk_path` is a load reading its windows (`bp`, below `npw + 2`: the path's and the
cap's two), the flag (`.n (Cq + 2)` at `2^(cd-1)`) or the cap leaf (`.n (Cq + 8)` at `2^(cd+1)`,
`+ 1`), or neither. `AtomsOk`: every statement is such an atom, a `match` of quiet arms
(`walk_window`: keccaks, constants, copies) or a call. `oqQuery_atoms_ok`: every statement of a
query is (its call of `walk_path` among them); `wp_atoms_ok`: every statement of `walk_path`'s body
but its return.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- A load of a query: its pointer and offset: the fold's challenges, the final coefficients. -/
def OqQLoad (s : Oq) (coefs hs : V) (p : V) (off : ℕ) : Prop :=
  (p = coefs ∧ off < 3 * s.folds) ∨ (s.final = 1 ∧ p = hs ∧ off < s.nHs)

/-- A load of `walk_path`: its pointer and offset: the windows (the path's and the cap's two), the
flag, the cap leaf. -/
def OqWLoad (s : Oq) (bp : V) (ch : ℕ) (p : V) (off : ℕ) : Prop :=
  (p = bp ∧ off < oqNpw s + 2) ∨ (p = .n (oqCq s ch + 2) ∧ off = 2 ^ (s.cd - 1)) ∨
    (p = .n (oqCq s ch + 8) ∧ (off = 2 ^ (s.cd + 1) ∨ off = 2 ^ (s.cd + 1) + 1))

/-- **An atom by kind**: a load whose pointer and offset satisfy `L`, a `frameAddr` whose pointer
and run satisfy `F`, or neither a load, a `frameAddr` nor a `HeapBuf`. -/
def AtomKind (L : V → ℕ → Prop) (F : V → List V → Prop) : Atom → Prop
  | .load _ p off => L p off
  | .frameAddr p run => F p run
  | .hint (.alloc ..) => False
  | .hint (.allocDyn ..) => False
  | _ => True

theorem AtomKind.mono {L L' : V → ℕ → Prop} {F F' : V → List V → Prop}
    (hL : ∀ p off, L p off → L' p off) (hF : ∀ p run, F p run → F' p run) {a : Atom}
    (h : AtomKind L F a) : AtomKind L' F' a := by
  cases a with
  | load _ p off => exact hL p off h
  | frameAddr p run => exact hF p run h
  | hint hh => cases hh <;> exact h
  | _ => exact h

/-- **An atom of a query, by kind**: a load as `OqQLoad`, or neither a load, a `frameAddr` nor a
`HeapBuf`. -/
abbrev OqAtomOk (s : Oq) (coefs hs : V) : Atom → Prop :=
  AtomKind (OqQLoad s coefs hs) (fun _ _ ↦ False)

/-- **An atom of `walk_path`, by kind**: a load as `OqWLoad`, or neither a load, a `frameAddr` nor
a `HeapBuf`. -/
abbrev OqWAtomOk (s : Oq) (bp : V) (ch : ℕ) : Atom → Prop :=
  AtomKind (OqWLoad s bp ch) (fun _ _ ↦ False)

/-- Every statement is an atom of the kind `P`, a `match` of quiet atom arms (fewer than
`2^64`), or a call. -/
def AtomsOk (P : Atom → Prop) (ss : List Stmt) : Prop :=
  ∀ x ∈ ss, (∃ a, x = .atom a ∧ P a) ∨
    (∃ y arms, x = .match_ y arms ∧ Stmt.flatM (.match_ y arms) = true ∧ arms.length ≤ 2 ^ 64 - 1) ∨
    ∃ f args rets, x = .call f args rets

theorem atomsOk_append {P : Atom → Prop} {ss ts : List Stmt} (h1 : AtomsOk P ss) (h2 : AtomsOk P ts) :
    AtomsOk P (ss ++ ts) :=
  fun x h ↦ (List.mem_append.mp h).elim (h1 x) (h2 x)

theorem atomsOk_flatten {P : Atom → Prop} {bs : List (List Stmt)} (h : ∀ b ∈ bs, AtomsOk P b) :
    AtomsOk P bs.flatten := fun x hm ↦ by
  obtain ⟨b, hb, hm⟩ := List.mem_flatten.mp hm
  exact h b hb x hm

theorem atomsOk_nil {P : Atom → Prop} : AtomsOk P [] := fun _ h ↦ absurd h (by simp)

/-- A singleton list of statements. -/
theorem atomsOk_cons {P : Atom → Prop} {a : Atom} {ss : List Stmt} (ha : P a) (h : AtomsOk P ss) :
    AtomsOk P (.atom a :: ss) := fun x hx ↦ by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inl ⟨a, rfl, ha⟩
  · exact h x hx

theorem atomsOk_match {P : Atom → Prop} {y : V} {arms : List (List Stmt)} {ss : List Stmt}
    (ha : Stmt.flatM (.match_ y arms) = true) (hl : arms.length ≤ 2 ^ 64 - 1) (h : AtomsOk P ss) :
    AtomsOk P (.match_ y arms :: ss) := fun x hx ↦ by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inr (Or.inl ⟨y, arms, rfl, ha, hl⟩)
  · exact h x hx

theorem atomsOk_call {P : Atom → Prop} {f : String} {args rets : List V} {ss : List Stmt}
    (h : AtomsOk P ss) : AtomsOk P (.call f args rets :: ss) := fun x hx ↦ by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inr (Or.inr ⟨f, args, rets, rfl⟩)
  · exact h x hx

theorem AtomsOk.flatM {P : Atom → Prop} {ss : List Stmt} (h : AtomsOk P ss) :
    ss.all Stmt.flatM = true := by
  rw [List.all_eq_true]
  intro x hx
  rcases h x hx with ⟨a, rfl, -⟩ | ⟨y, arms, rfl, hm, -⟩ | ⟨f, args, rets, rfl⟩
  · rfl
  · exact hm
  · rfl

theorem oqStepT_quiet (pr ch l K n0 n1 : ℕ) (bit : Bool) :
    (oqStepT pr ch l K n0 n1 bit).all Stmt.quietS = true := by
  cases bit <;> rfl

theorem oqArmT_quiet (s : Oq) (pr kL ch i a : ℕ) : (oqArmT s pr kL ch i a).all Stmt.quietS = true := by
  rw [List.all_eq_true]
  intro x hx
  simp only [oqArmT, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ⟨_, ⟨r, -, rfl⟩, hx⟩ | rfl | rfl
  · exact List.all_eq_true.mp (oqStepT_quiet ..) x hx
  · rfl
  · rfl

theorem oqWin_match_flatM (s : Oq) (pr kL ch i : ℕ) :
    Stmt.flatM (.match_ (.n (oqWk s ch i)) ((List.range (2 ^ oqWw s i)).map (oqArmT s pr kL ch i))) =
      true := by
  simp only [Stmt.flatM, List.all_eq_true, List.mem_map, List.mem_range]
  rintro _ ⟨a, -, rfl⟩
  exact List.all_eq_true.mp (oqArmT_quiet s pr kL ch i a)

section
variable (s : Oq) (coefs hs : V)

theorem ok_rowT (b R : ℕ) : AtomsOk (OqAtomOk s coefs hs) (oqRowT b R) :=
  atomsOk_cons trivial atomsOk_nil

theorem ok_packsT (b R : ℕ) : AtomsOk (OqAtomOk s coefs hs) (oqPacksT b R) := by
  refine atomsOk_flatten fun x hx ↦ ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
    atomsOk_nil)))

theorem ok_prepT (b : ℕ) : AtomsOk (OqAtomOk s coefs hs) (oqPrepT s b) := by
  unfold oqPrepT
  refine atomsOk_append (ok_rowT _ _ _ _ _) ?_
  split
  · exact ok_packsT _ _ _ _ _
  · exact atomsOk_nil

theorem ok_padT (pr : ℕ) : AtomsOk (OqAtomOk s coefs hs) (oqPadT pr) :=
  atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
    (atomsOk_cons trivial atomsOk_nil))))

theorem ok_leafT (b pr kL : ℕ) : AtomsOk (OqAtomOk s coefs hs) (oqLeafT s b pr kL) := by
  refine atomsOk_flatten fun x hx ↦ ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
  unfold oqBlockT
  split_ifs
  · exact atomsOk_cons trivial atomsOk_nil
  · refine atomsOk_append (atomsOk_flatten fun y hy ↦ ?_) (atomsOk_cons trivial atomsOk_nil)
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hy
    unfold oqXorT
    dsimp only
    split_ifs
    · exact atomsOk_cons trivial atomsOk_nil
    · exact atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil)
    · exact atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil)
    · exact atomsOk_cons trivial atomsOk_nil

theorem ok_roundT (x : V) (b F : ℕ) {j : ℕ} (hj : j < s.folds) :
    AtomsOk (OqAtomOk s coefs hs) (oqRoundT s coefs x b F j) := by
  unfold oqRoundT
  refine atomsOk_append (atomsOk_append ?_ ?_) (atomsOk_flatten fun y hy ↦ ?_)
  · exact atomsOk_cons (Or.inl ⟨rfl, by omega⟩) (atomsOk_cons (Or.inl ⟨rfl, by omega⟩)
      (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons (Or.inl ⟨rfl, by omega⟩)
      (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil)))))))
  · split
    · exact atomsOk_nil
    · exact atomsOk_cons trivial atomsOk_nil
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hy
    exact atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil)

theorem ok_foldT (x : V) (b F : ℕ) : AtomsOk (OqAtomOk s coefs hs) (oqFoldT s coefs x b F) := by
  unfold oqFoldT
  refine atomsOk_append (atomsOk_flatten fun y hy ↦ ?_) (atomsOk_cons trivial atomsOk_nil)
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
  exact ok_roundT s coefs hs x b F (List.mem_range.mp hj)

theorem ok_nvLevelT (w : V) : ∀ (ins : List ℕ) (k : ℕ),
    AtomsOk (OqAtomOk s coefs hs) (nvLevelT w ins k).1
  | lo :: hi :: rest, k => by
    rw [nvLevelT]
    exact atomsOk_cons trivial (atomsOk_cons trivial (ok_nvLevelT w rest (k + 2)))
  | [_], _ => atomsOk_cons trivial atomsOk_nil
  | [], _ => atomsOk_nil

theorem ok_nvLevelsT (ws : ℕ → ℕ) : ∀ (c i : ℕ) (ins : List ℕ) (k : ℕ),
    AtomsOk (OqAtomOk s coefs hs) (nvLevelsT ws c i ins k).1
  | 0, _, _, _ => atomsOk_nil
  | c + 1, i, ins, k => by
    rw [nvLevelsT]
    exact atomsOk_append (ok_nvLevelT _ _ _ _ _ _) (ok_nvLevelsT ws c _ _ _)

theorem ok_novel (hfinal : s.final = 1) (v : ℕ) :
    AtomsOk (OqAtomOk s coefs hs) (oqNovel s hs v).1 := by
  unfold oqNovel nvLevel0T
  dsimp only
  refine atomsOk_append (atomsOk_flatten fun y hy ↦ ?_) (ok_nvLevelsT _ _ _ _ _ _ _ _)
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hy
  rw [List.mem_range] at hm
  exact atomsOk_cons (Or.inr ⟨hfinal, rfl, by omega⟩) (atomsOk_cons (Or.inr ⟨hfinal, rfl, by omega⟩)
    (atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil)))

theorem ok_finT (hfinal : s.final = 1) (x : V) (v : ℕ) :
    AtomsOk (OqAtomOk s coefs hs) (oqFinT s x hs v) := by
  unfold oqFinT oqWsT
  refine atomsOk_append (atomsOk_append (atomsOk_cons trivial (atomsOk_flatten fun y hy ↦ ?_))
    (ok_novel s coefs hs hfinal v)) (atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil))
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
  exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial atomsOk_nil))

end

section
variable (s : Oq) (bp : V) (ch : ℕ)

theorem ok_pathT (pr kL : ℕ) : AtomsOk (OqWAtomOk s bp ch) (oqPathT s bp pr kL ch) := by
  unfold oqPathT
  refine atomsOk_cons trivial (atomsOk_flatten fun y hy ↦ ?_)
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  rw [List.mem_range] at hi
  refine atomsOk_cons (Or.inl ⟨rfl, by omega⟩) (atomsOk_append ?_ (atomsOk_cons trivial
    (atomsOk_match (oqWin_match_flatM s pr kL ch i) (by
      rw [List.length_map, List.length_range]
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (oqWw_le s i)) (by norm_num))
      atomsOk_nil)))
  split
  · exact atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
      (atomsOk_cons trivial atomsOk_nil))))
  · exact atomsOk_nil

theorem ok_capT (cap flags : V) (kL : ℕ) :
    AtomsOk (OqWAtomOk s bp ch) (oqCapT s bp cap flags kL ch) := by
  unfold oqCapT
  exact atomsOk_cons (Or.inl ⟨rfl, by omega⟩) (atomsOk_cons (Or.inl ⟨rfl, by omega⟩)
    (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial (atomsOk_cons trivial
    (atomsOk_cons trivial (atomsOk_cons (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))
    (atomsOk_cons (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)) atomsOk_nil)))))))))))

end

/-- **Every statement of a query is an atom of its kind**, or its call of `walk_path`. -/
theorem oqQuery_atoms_ok {s : Oq} (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool)
    (pr : ℕ) (walk : String) :
    AtomsOk (OqAtomOk s coefs hs) (oqQueryT s x bp cap flags coefs hs b emit pr walk) := by
  unfold oqQueryT
  refine atomsOk_append (atomsOk_append (atomsOk_append (atomsOk_append
    (atomsOk_append (ok_prepT _ _ _ _) ?_) (ok_leafT _ _ _ _ _ _)) (atomsOk_call atomsOk_nil))
    (ok_foldT _ _ _ _ _ _)) ?_
  · split_ifs
    · exact ok_padT _ _ _ _
    · exact atomsOk_nil
  · split_ifs with h
    · exact ok_finT _ _ _ h _ _
    · exact atomsOk_nil

/-- **Every statement of `walk_path`'s body but its return is an atom of its kind** or a `match`. -/
theorem wp_atoms_ok (s : Oq) :
    AtomsOk (OqWAtomOk s (.n 2) wpCh) (oqPathT s (.n 2) (wpPr s) 0 wpCh ++
      oqCapT s (.n 2) (.n 3) (.n 4) 0 wpCh) :=
  atomsOk_append (ok_pathT _ _ _ _ _) (ok_capT _ _ _ _ _ _)

end
end LeanVM.Guest.B1
