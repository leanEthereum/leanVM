/-
  LeanVM.Guest.Memory.LiftPure

  Pure functions complete in the uniform placed form (`CompleteAtD`) from their relation on every
  memory defined below `2^κ` and holding the caller's words, by trees loading those words; and leaf
  bodies (no call), whose loads a predicate on atoms bounds.
-/

module

public import LeanVM.Guest.Memory.Uniform

/-!
# Pure functions, placed

**A pure function whose loads read the caller's words** is complete in the placed form
(`completeAtD_of_relIn`): if on every memory defined below `2^κ` and holding the caller's words
`Lin` its relation holds by a tree loading from `Lin` only (`Program.RelIn`), then on a memory
`rd1` kept on `Lin` and below `2^κ` (`lowLin`) one tree serves, placed at every frame pointer, every
memory defined below `2^κ` and holding `Lin` (`relAtIn_uniform_pure`): the range checks' reads only
need the memory defined there.

**Leaf bodies.** `Stmt.leafOk lok`: a body of atoms, branches and arms only (no call, no
`callIf`, no dispatch), every atom placing nothing (`atomUnplaced`) and passing `lok`. Its walks'
events are its atoms and branch conditions (`walk_leafOk`), so a valid tree of it has no callee
(`calls_nil_of_leafOk`), its function is pure on its own (`pureIn_of_leafOk`), and its relation
loads from `R` when the walks' loads do (`relIn_of_leaf`, on the walks that hold `relIn_of_leaf'`).
-/

namespace LeanVM.Guest.Lift

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 (LowDef Within CompleteAtD Returns disj_nil relAtIn_dmono)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Placed completeness from `RelIn` on every low memory -/

/-- The memory `rd1` kept on the caller's words and below `2^κ`. -/
noncomputable def lowLin (rd1 : Reader) (κ : ℕ) (Lin : Layout) : Reader :=
  B1.Main.restrict rd1 fun i => RegionL Lin i ∨ i < 2 ^ κ

theorem lowLin_low {rd1 : Reader} {κ : ℕ} {Lin : Layout} (hl : LowDef κ rd1) :
    LowDef κ (lowLin rd1 κ Lin) := fun i hi => by
  rw [lowLin, B1.Main.restrict_of ⟨i, rfl, Or.inr hi⟩]
  exact hl i hi

theorem lowLin_memL {rd1 : Reader} {κ : ℕ} {Lin : Layout} (hL : MemL rd1 Lin) :
    MemL (lowLin rd1 κ Lin) Lin :=
  B1.Main.memL_restrict hL fun _ hi => Or.inl hi

/-- **A pure function loading the caller's words, placed**: its relation on every memory defined
below `2^κ` and holding `Lin`, by trees loading from `Lin`, gives it at every frame pointer by one
tree. -/
theorem completeAtD_of_relIn {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) {κ : ℕ} {Lin : Layout} {args rets : List E}
    (h : ∀ rd, LowDef κ rd → MemL rd Lin → coreProgram.RelIn rd (RegionL Lin) g args rets) :
    CompleteAtD fs cert κ g Lin args (Returns rets) := by
  intro fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (h _ (lowLin_low (Lin := Lin) hl1) (lowLin_memL hL1))
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtIn_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [lowLin, B1.Main.restrict_of ⟨i, rfl, Or.inl hi⟩, B1.Main.memL_agree hL' hL1 i hi]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi | hi⟩ := B1.Main.restrict_supp' rd1 _ _ _ hv
    · rw [B1.Main.memL_agree hL' hL1 i hi, ← B1.Main.restrict_of (rd := rd1)
        (S := fun i => RegionL Lin i ∨ i < 2 ^ κ) ⟨i, rfl, Or.inl hi⟩]
      exact Option.isSome_iff_exists.mpr ⟨v, hv⟩
    · exact hl i hi
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-! ## Leaf bodies -/

mutual
/-- A statement of atoms, branches and arms only, its atoms placing nothing and passing `lok`. -/
def Stmt.leafOk (lok : Atom → Bool) : Stmt → Bool
  | .atom a => atomUnplaced a && lok a
  | .ite _ z n => Stmt.leafOkList lok z && Stmt.leafOkList lok n
  | .match_ _ arms => Stmt.leafOkArms lok arms
  | .ret _ => true
  | _ => false

/-- A block of `leafOk` statements. -/
def Stmt.leafOkList (lok : Atom → Bool) : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.leafOk lok s && Stmt.leafOkList lok ss

/-- Arms of `leafOk` blocks. -/
def Stmt.leafOkArms (lok : Atom → Bool) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.leafOkList lok a && Stmt.leafOkArms lok as
end

/-- No condition on an atom but placing nothing. -/
def anyAtom : Atom → Bool := fun _ ↦ true

theorem leafOkList_append (lok : Atom → Bool) : ∀ (l l' : List Stmt),
    Stmt.leafOkList lok (l ++ l') = (Stmt.leafOkList lok l && Stmt.leafOkList lok l')
  | [], _ => by simp [Stmt.leafOkList]
  | s :: l, l' => by
    rw [List.cons_append, Stmt.leafOkList, Stmt.leafOkList, leafOkList_append lok l l',
      Bool.and_assoc]

/-- A leaf body checked by ranges of statements: the range from `a` and the rest from `a + n`
make the rest from `a`. -/
theorem leafOk_drop {lok : Atom → Bool} {l : List Stmt} {a n : ℕ}
    (h : Stmt.leafOkList lok ((l.drop a).take n) = true)
    (h' : Stmt.leafOkList lok (l.drop (a + n)) = true) : Stmt.leafOkList lok (l.drop a) = true := by
  rw [← List.take_append_drop n (l.drop a), leafOkList_append, List.drop_drop]
  exact Bool.and_eq_true_iff.mpr ⟨h, h'⟩

theorem leafOk_end {lok : Atom → Bool} {l : List Stmt} {a : ℕ} (ha : l.length ≤ a) :
    Stmt.leafOkList lok (l.drop a) = true := by
  rw [List.drop_eq_nil_of_le ha]; rfl

/-- An event of a leaf body's walk: an atom passing `lok`, or a branch condition. -/
def EvLeafOk (lok : Atom → Bool) : Ev → Prop
  | .atom a => lok a = true
  | .inK _ => True
  | _ => False

section Walk

variable {lok : Atom → Bool} {σ : Val}

mutual
theorem walk1_leafOk : ∀ (s : Stmt), Stmt.leafOk lok s = true → (walk1 σ s).All (EvLeafOk lok)
  | .atom _, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      simp only [Stmt.leafOk, Bool.and_eq_true] at h
      exact h.2
  | .ite c z n, h => by
      simp only [Stmt.leafOk, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.all_pre (fun e he => by rw [List.mem_singleton] at he; subst he; trivial) ?_
      split_ifs
      · exact walk_leafOk z h.1
      · exact walk_leafOk n h.2
  | .match_ x arms, h => walkArms_leafOk x arms 0 h
  | .call .., h => by simp [Stmt.leafOk] at h
  | .callIf .., h => by simp [Stmt.leafOk] at h
  | .dispatch .., h => by simp [Stmt.leafOk] at h
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_leafOk : ∀ (ss : List Stmt), Stmt.leafOkList lok ss = true →
    (walk σ ss).All (EvLeafOk lok)
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, h => by
      simp only [Stmt.leafOkList, Bool.and_eq_true] at h
      rw [walk]
      exact Out.all_seq (walk_leafOk ss h.2) (walk1_leafOk s h.1)

theorem walkArms_leafOk (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    Stmt.leafOkArms lok arms = true → (walkArms σ x j arms).All (EvLeafOk lok)
  | [], _, _ => trivial
  | a :: as, j, h => by
      simp only [Stmt.leafOkArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_leafOk a h.1
      · exact walkArms_leafOk x as (j + 1) h.2
end

end Walk

mutual
theorem leafOk_pure {lok : Atom → Bool} (S : List String) :
    ∀ (s : Stmt), Stmt.leafOk lok s = true → Stmt.pure S s = true
  | .atom _, h => by
      simp only [Stmt.leafOk, Bool.and_eq_true] at h
      exact h.1
  | .ite _ z n, h => by
      simp only [Stmt.leafOk, Bool.and_eq_true] at h
      simp only [Stmt.pure, leafOkList_pure S z h.1, leafOkList_pure S n h.2, Bool.and_self]
  | .match_ _ arms, h => by
      simp only [Stmt.leafOk] at h
      simp only [Stmt.pure, leafOkArms_pure S arms h]
  | .call .., h => by simp [Stmt.leafOk] at h
  | .callIf .., h => by simp [Stmt.leafOk] at h
  | .dispatch .., h => by simp [Stmt.leafOk] at h
  | .ret _, _ => rfl

theorem leafOkList_pure {lok : Atom → Bool} (S : List String) :
    ∀ (ss : List Stmt), Stmt.leafOkList lok ss = true → Stmt.pureList S ss = true
  | [], _ => rfl
  | s :: ss, h => by
      simp only [Stmt.leafOkList, Bool.and_eq_true] at h
      simp only [Stmt.pureList, leafOk_pure S s h.1, leafOkList_pure S ss h.2, Bool.and_self]

theorem leafOkArms_pure {lok : Atom → Bool} (S : List String) :
    ∀ (arms : List (List Stmt)), Stmt.leafOkArms lok arms = true → Stmt.pureArms S arms = true
  | [], _ => rfl
  | a :: as, h => by
      simp only [Stmt.leafOkArms, Bool.and_eq_true] at h
      simp only [Stmt.pureArms, leafOkList_pure S a h.1, leafOkArms_pure S as h.2, Bool.and_self]
end

/-- A function with a leaf body is pure on its own. -/
theorem pureIn_of_leafOk {lok : Atom → Bool} {g : String} {fn : Fn}
    (hf : coreProgram.find? g = some fn) (h : Stmt.leafOkList lok fn.body = true) :
    coreProgram.PureIn [g] := by
  intro g' hg' fn' hf'
  rw [List.mem_singleton] at hg'
  subst hg'
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  exact leafOkList_pure _ _ h

theorem calls_nil_of_leafOk {lok : Atom → Bool} {es : List Ev} (h : ∀ e ∈ es, EvLeafOk lok e) :
    calls es = [] := by
  rw [calls, List.filterMap_eq_nil_iff]
  intro e he
  have := h e he
  cases e <;> simp_all [EvLeafOk, Ev.call?]

/-- **A leaf's relation, loading from `R`**: when the loads of every walk that holds lie in `R`. -/
theorem relIn_of_leaf' {lok : Atom → Bool} {g : String} {fn : Fn} {rd : Reader} {R : ℕ → Prop}
    {args rets : List E} (hf : coreProgram.find? g = some fn)
    (hleaf : Stmt.leafOkList lok fn.body = true)
    (hload : ∀ σ es vs, fn.params.map σ = args → walk σ fn.body = .ret es vs →
      (∀ e ∈ es, e.Holds rd σ) → ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧ R i)
    (h : coreProgram.Rel rd g args rets) : coreProgram.RelIn rd R g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree coreProgram_wf h
  refine ⟨t, hn, hv, hb, ?_⟩
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs kids =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hf', hp, es, vs, hw, -, hes, hkv⟩ := hv
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    have hall := walk_leafOk (σ := σ) _ hleaf
    rw [hw] at hall
    have hc := calls_nil_of_leafOk hall
    rw [hc] at hkv
    match kids, hkv with
    | [], _ =>
      rw [Tree.LoadsR, events_node hf hw]
      exact ⟨hload σ es vs hp hw hes, trivial⟩

/-- **A leaf's relation, loading from `R`**: when the loads of every walk lie in `R`. -/
theorem relIn_of_leaf {lok : Atom → Bool} {g : String} {fn : Fn} {rd : Reader} {R : ℕ → Prop}
    {args rets : List E} (hf : coreProgram.find? g = some fn)
    (hleaf : Stmt.leafOkList lok fn.body = true)
    (hload : ∀ σ es vs, fn.params.map σ = args → walk σ fn.body = .ret es vs →
      ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧ R i)
    (h : coreProgram.Rel rd g args rets) : coreProgram.RelIn rd R g args rets :=
  relIn_of_leaf' hf hleaf (fun σ es vs hp hw _ ↦ hload σ es vs hp hw) h

/-! ## Frame runs fitting their frames -/

mutual
/-- The atoms of a statement, its branches' and arms' included. -/
def stmtAtoms : Stmt → List Atom
  | .atom a => [a]
  | .ite _ z n => blockAtoms z ++ blockAtoms n
  | .match_ _ arms => armsAtoms arms
  | _ => []

/-- The atoms of a block. -/
def blockAtoms : List Stmt → List Atom
  | [] => []
  | s :: ss => stmtAtoms s ++ blockAtoms ss

/-- The atoms of arms. -/
def armsAtoms : List (List Stmt) → List Atom
  | [] => []
  | a :: as => blockAtoms a ++ armsAtoms as
end

/-- **Every frame run fits its frame**: a `frameAddr` run of a function's body has its cells, from
the certificate's cell of its first value on, within the function's frame. The certificates'
fact, discharged for the deployed instance from the checker's (`B2C.FnStatic`). -/
def RunsFit (fs : String → ℕ) (cert : String → V → ℕ) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∀ p r rs, Atom.frameAddr p (r :: rs) ∈ blockAtoms fn.body →
    cert f r + (rs.length + 1) ≤ fs f

end
end LeanVM.Guest.Lift
