/-
  LeanVM.Prover.Complete.Link.RowIdBase

  `rowProds`' base terms at a row: each block's form under its weight and gate.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdStepVal

/-!
# The base terms at a row

`rowBaseStep` pushes, for each monomial of a block's form, its coefficient times the block's weight
table (`ω` or `eq(τ, ·)`), its gate column and the monomial's columns. Where every monomial's
columns and every gate are columns of the table (`FormVars`, `tables_vars`), the tables a term reads
are the table's columns, so the block sums to `weight·gate·form` at the row (`baseTerms_val`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset

/-! ## Forms over a table's columns -/

/-- Every monomial of the form reads columns below `n`. -/
def FormVars (n : ℕ) (f : Form) : Prop := ∀ m ∈ f.terms, ∀ v ∈ m.1, v < n

theorem FormVars.addScaled {n : ℕ} {f g : Form} (hf : FormVars n f) (hg : FormVars n g) (w : E) :
    FormVars n (f.addScaled g w) := by
  unfold Form.addScaled FormVars
  suffices h : ∀ (L : List (List ℕ × E)) (acc : List (List ℕ × E)),
      (∀ m ∈ L, ∀ v ∈ m.1, v < n) → (∀ m ∈ acc, ∀ v ∈ m.1, v < n) →
      ∀ m ∈ L.foldl (fun acc t ↦ addTerm acc t.1 (w * t.2)) acc, ∀ v ∈ m.1, v < n from
    h g.terms f.terms hg hf
  intro L
  induction L with
  | nil => intro acc _ h; exact h
  | cons t L ih =>
    intro acc hL hacc
    refine ih _ (fun m hm ↦ hL m (List.mem_cons_of_mem _ hm)) fun m hm ↦ ?_
    rcases addTerm_vars _ _ _ m hm with h | ⟨y, hy, h⟩
    · rw [h]; exact hL t List.mem_cons_self
    · rw [h]; exact hacc y hy

theorem FormVars.empty (n : ℕ) : FormVars n ({} : Form) := fun m hm ↦ by simp at hm

theorem FormVars.const (n : ℕ) (c : E) : FormVars n (Form.const c) := fun m hm ↦ by
  simp [Form.const] at hm; subst hm; simp

/-- The tables' link forms and gates read the table's columns. -/
theorem tables_vars : ∀ t < nTables,
    (tables.getD t default).links.bytecodeLink.pc < (tables.getD t default).width ∧
    (∀ sf ∈ (tables.getD t default).links.bytecodeLink.operands, ∀ m ∈ sf.2.terms,
      ∀ v ∈ m.1, v < (tables.getD t default).width) ∧
    ∀ a ∈ (tables.getD t default).links.memory,
      (∀ m ∈ a.address.terms, ∀ v ∈ m.1, v < (tables.getD t default).width) ∧
      (∀ m ∈ a.value.terms, ∀ v ∈ m.1, v < (tables.getD t default).width) ∧
      ∀ g ∈ a.gate, g < (tables.getD t default).width := by
  decide +kernel

theorem jump_vars (coefs : List E) :
    FormVars (tables.getD opJump default).width (jumpConstraintForm coefs) := by
  intro m hm
  simp only [jumpConstraintForm, List.mem_cons, List.not_mem_nil, or_false] at hm
  have hw : (tables.getD opJump default).width = 14 := by decide
  rw [hw]
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

theorem formVars_payloadForms (ch : LinkChallenges) {t : ℕ} (ht : t < nTables) (mu : List E) :
    FormVars (tables.getD t default).width (payloadForms ch (tables.getD t default).links mu).1 ∧
      ∀ g ∈ (payloadForms ch (tables.getD t default).links mu).2,
        g.1 < (tables.getD t default).width ∧ FormVars (tables.getD t default).width g.2 := by
  obtain ⟨hpc, hop, hmem⟩ := tables_vars t ht
  set w := (tables.getD t default).width
  have hgates : ∀ g ∈ linkGates (tables.getD t default).links, g < w := by
    unfold linkGates
    refine foldl_inv (fun gs : List ℕ ↦ ∀ g ∈ gs, g < w)
      (fun a ↦ a ∈ (tables.getD t default).links.memory) _ ?_ _ _ (fun _ h ↦ h) (by simp)
    intro gs a ha hgs
    have hg := (hmem a ha).2.2
    cases hga : a.gate with
    | none => exact hgs
    | some g0 =>
      dsimp only
      split
      · exact hgs
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact hgs g' h
        · simp at h; subst h; exact hg _ (by simp [hga])
  unfold payloadForms
  dsimp only
  refine foldl_inv (fun acc : Form × List (ℕ × Form) ↦
      FormVars w acc.1 ∧ ∀ g ∈ acc.2, g.1 < w ∧ FormVars w g.2)
    (fun am : Access × E ↦ am.1 ∈ (tables.getD t default).links.memory) _ ?_ _ _
    (fun am ham ↦ (List.of_mem_zip ham).1) ⟨?_, ?_⟩
  · intro acc am ham hacc
    obtain ⟨access, m⟩ := am
    have ha := hmem access ham
    have hadd : ∀ f, FormVars w f → ∀ x, FormVars w (((f.addScaled access.address
        (x * ch.gammaMem.getD 0 0)).addScaled (Form.const 1)
        (x * ch.gammaMem.getD 3 0)).addScaled access.value (x * ch.gammaMem.getD 1 0)) :=
      fun f hf x ↦ ((hf.addScaled ha.1 _).addScaled (FormVars.const w 1) _).addScaled ha.2.1 _
    dsimp only
    split
    · exact ⟨hadd _ hacc.1 _, hacc.2⟩
    · refine ⟨hacc.1, fun g hg ↦ ?_⟩
      simp only [List.mem_map] at hg
      obtain ⟨⟨g', f⟩, hgf, rfl⟩ := hg
      have h0 := hacc.2 _ hgf
      dsimp only
      split
      · exact ⟨h0.1, hadd _ h0.2 _⟩
      · exact h0
  · refine foldl_inv (FormVars w) (fun sf ↦ sf ∈ (tables.getD t default).links.bytecodeLink.operands) _
      (fun f sf hsf hf ↦ hf.addScaled (fun m hm ↦ hop sf hsf m hm) _) _ _ (fun _ h ↦ h) ?_
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simpa using hpc
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    simp at hm
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    exact ⟨hgates g' hg', FormVars.empty w⟩

/-! ## The base terms -/

/-- A base term of block `b` for the monomial `(vars, c)`. -/
def baseTerm (b : Block) (vc : List ℕ × E) : E × Array ℕ :=
  (vc.2, #[if b.onEq then 2 else 0] ++ (b.gate.map fun g ↦ #[3 + g]).getD #[] ++
    (vc.1.map (3 + ·)).toArray)

theorem foldl_push {α : Type} (f : Array (E × Array ℕ) → α → Array (E × Array ℕ))
    (g : α → E × Array ℕ) (hf : ∀ ts x, f ts x = ts.push (g x)) :
    ∀ (l : List α) (ts : Array (E × Array ℕ)), (l.foldl f ts).toList = ts.toList ++ l.map g
  | [], ts => by simp
  | x :: l, ts => by rw [List.foldl_cons, foldl_push f g hf l, hf]; simp

theorem foldl_rowBaseStep : ∀ (bs : List Block) (terms : Array (E × Array ℕ)),
    (bs.foldl rowBaseStep terms).toList = terms.toList ++ bs.flatMap fun b ↦ b.form.terms.map (baseTerm b)
  | [], terms => by simp
  | b :: bs, terms => by
    rw [List.foldl_cons, foldl_rowBaseStep bs, rowBaseStep, foldl_push _ _ (fun _ _ ↦ rfl)]
    simp [baseTerm]

/-- The value of block `b` at row `u`, over tables `T` whose columns' tables are `col`. -/
theorem baseTerms_val (T : Array (Array E)) (u : ℕ) (n : ℕ) (col : ℕ → E)
    (hcol : ∀ v < n, tv T u (3 + v) = col v) (b : Block) (hb : FormVars n b.form)
    (hg : ∀ g ∈ b.gate, g < n) :
    ((b.form.terms.map (baseTerm b)).map (termAt ⟨T, #[]⟩ u)).sum =
      tv T u (if b.onEq then 2 else 0) * (b.gate.map col).getD 1 * b.form.evaluate col := by
  rw [Form.evaluate, LeanVM.Protocol.Tables.sumE_eq, List.map_map, ← List.sum_map_mul_left]
  refine congrArg _ (List.map_congr_left fun vc hvc ↦ ?_)
  have hv := hb vc hvc
  simp only [Function.comp_apply, baseTerm, termAt_eq, Array.toList_append, List.map_append,
    List.prod_append, foldl_mul_map]
  have hm : ((vc.1.map (3 + ·)).toArray.toList.map (tv T u)).prod = (vc.1.map col).prod := by
    rw [List.toList_toArray, List.map_map]
    exact congrArg _ (List.map_congr_left fun v hv' ↦ hcol v (hv v hv'))
  rw [hm]
  cases hgb : b.gate with
  | none => simp; ring
  | some g =>
    have := hcol g (hg g (by simp [hgb]))
    simp [this]; ring

end LeanVM.Prover.Complete.RowId

end
