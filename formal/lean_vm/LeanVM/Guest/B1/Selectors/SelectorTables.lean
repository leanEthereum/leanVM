/-
  LeanVM.Guest.B1.Selectors.SelectorTables

  B1 for `selector_tables`: it writes the opening point's strided eq tables over each nibble's
  top coordinates.
-/

module

public import LeanVM.Guest.B1.Selectors.ColumnSelector

/-!
# `selector_tables` (TRIAGE G #69)

`selector_tables(point, point1)` (G:3186-3206) allocates `sel_eq` (`7·64` words) and for each
nibble `j < 7` computes the eq levels over its top coordinates `4j + 3, 4j + 2, …` (level `w` from
level `w - 1`: entry `i` times `1 + r`, then times `r`, `r` coordinate `4j + 3 - w`) and stores
level `w`'s `2^(w+1)` entries at `sel_eq[64j + 16w ..]`, strided by `2^(3 - w)`: entry `u` there
is the eq weight of `u`'s bits `3 - w .. 3` (`selEqEntry`).

The body is `stPre ++ [ret]` (`stFound`, by kernel evaluation): nibble `j`'s values from
`3 + 36j` (`stNib`), level `w`'s entry `i` at value `stV j w i`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- Nibble `j`'s first value. -/
def stB (j : ℕ) : ℕ := 3 + 36 * j

/-- Level `w`'s first entry, past its two loads for `w ≥ 1`. -/
def stM (j w : ℕ) : ℕ := stB j + [0, 4, 10, 20].getD w 0

/-- The value of level `w`'s entry `i`. -/
def stV (j w i : ℕ) : ℕ := stM j w + i

/-- Level `w ≥ 1` of nibble `j`: the coordinate and its complement, then the products. -/
def stLevel (j w : ℕ) : List Stmt :=
  [.atom (.load (.n (stM j w - 2)) (.n 0) (4 * j + 3 - w)),
    .atom (.load (.n (stM j w - 1)) (.n 1) (4 * j + 3 - w))] ++
  ((List.range (2 ^ w)).map fun i ↦
    [.atom (.mul (.n (stM j w + 2 * i)) (.n (stV j (w - 1) i)) (.n (stM j w - 1))),
      .atom (.mul (.n (stM j w + 2 * i + 1)) (.n (stV j (w - 1) i)) (.n (stM j w - 2)))]).flatten

/-- The stores of level `w`: entry `i` at `64j + 16w + i·2^(3 - w)`. -/
def stStores (j w : ℕ) : List Stmt :=
  (List.range (2 ^ (w + 1))).map fun i ↦
    .atom (.load (.n (stV j w i)) (.n 2) (64 * j + 16 * w + i * 2 ^ (3 - w)))

/-- Nibble `j`. -/
def stNib (j : ℕ) : List Stmt :=
  [.atom (.load (.n (stB j)) (.n 1) (4 * j + 3)), .atom (.load (.n (stB j + 1)) (.n 0) (4 * j + 3))] ++
    stLevel j 1 ++ stLevel j 2 ++ stLevel j 3 ++ ((List.range 4).map (stStores j)).flatten

/-- `selector_tables`'s statements before its `ret`. -/
def stPre : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 448))] ++ ((List.range 7).map stNib).flatten ++
    [.atom (.copy (.n 255) (.n 2))]

/-- The function found by name is the template. -/
noncomputable def stCheck : Bool :=
  match coreProgram.find? "selector_tables" with
  | some fn => decide (fn.params = [.n 0, .n 1]) && tbStmtsEqb fn.body (stPre ++ [.ret [.n 255]])
  | none => false

theorem stCheck_eq : stCheck = true := by decide +kernel

theorem stFound : ∃ fn : Fn, coreProgram.find? "selector_tables" = some fn ∧
    fn.params = [.n 0, .n 1] ∧ fn.body = stPre ++ [.ret [.n 255]] := by
  have h := stCheck_eq
  unfold stCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem stLevel_noRet (j w : ℕ) : Stmt.noRetList (stLevel j w) = true := by
  rw [stLevel, tb_noRetList_append, tb_noRetList_flatten_range _ _ (fun _ => rfl)]; rfl

theorem stStores_noRet (j w : ℕ) : Stmt.noRetList (stStores j w) = true :=
  tb_noRetList_mapAtoms _ _

theorem stNib_noRet (j : ℕ) : Stmt.noRetList (stNib j) = true := by
  simp only [stNib, tb_noRetList_append, stLevel_noRet,
    tb_noRetList_flatten_range _ _ (stStores_noRet j)]; rfl

theorem stPre_noRet : Stmt.noRetList stPre = true := by
  rw [stPre, tb_noRetList_append, tb_noRetList_append, tb_noRetList_flatten_range _ _ stNib_noRet]
  rfl

/-! ## The entries -/

/-- **A level from the one below**: entry `2i + c` of level `w + 1` is entry `i` of level `w`
times coordinate `4j + 2 - w` (`c = 1`) or its complement. -/
theorem selEqEntry_succ (p p1 : List E) (j : ℕ) {w : ℕ} (hw : w < 3) (i c : ℕ) (hc : c < 2) :
    selEqEntry p p1 j (w + 1) ((2 * i + c) * 2 ^ (2 - w)) =
      (if c = 1 then p.getD (4 * j + (2 - w)) 0 else p1.getD (4 * j + (2 - w)) 0) *
        selEqEntry p p1 j w (i * 2 ^ (3 - w)) := by
  unfold selEqEntry
  rw [show 3 - (w + 1) = 2 - w by omega, Finset.prod_eq_prod_Ico_succ_bot (by omega),
    show 3 - w = 2 - w + 1 by omega]
  congr 1
  · rw [Nat.testBit_mul_two_pow]
    simp only [le_refl, decide_true, Bool.true_and, Nat.sub_self, Nat.testBit_zero]
    interval_cases c <;> simp [Nat.add_mod]
  · refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_Ico.mp ht
    rw [Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, decide_eq_true (by omega : 2 - w ≤ t),
      decide_eq_true (by omega : 2 - w + 1 ≤ t), Bool.true_and, Bool.true_and,
      show t - (2 - w) = (t - (2 - w + 1)) + 1 by omega, Nat.testBit_succ,
      show (2 * i + c) / 2 = i by omega]

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- What level `w ≥ 1` of nibble `j` gives: the coordinate, its complement, the products. -/
theorem holds_stLevel {j w : ℕ} (h : Stmt.HoldsList C rd σ (stLevel j w) True kret) :
    LoadHolds rd (σ (.n 0)) (4 * j + 3 - w) (σ (.n (stM j w - 2))) ∧
    LoadHolds rd (σ (.n 1)) (4 * j + 3 - w) (σ (.n (stM j w - 1))) ∧
    ∀ i < 2 ^ w, σ (.n (stV j w (2 * i))) = σ (.n (stV j (w - 1) i)) * σ (.n (stM j w - 1)) ∧
      σ (.n (stV j w (2 * i + 1))) = σ (.n (stV j (w - 1) i)) * σ (.n (stM j w - 2)) := by
  rw [stLevel, tb_holdsList_append_noRet rfl, tb_holdsList_flatten_range _ _ (fun _ => rfl)] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
  refine ⟨h1.1, h1.2, fun i hi => ?_⟩
  have := h2 i hi
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
  simp only [stV, ← Nat.add_assoc]
  exact this

/-- The parts of nibble `j`. -/
theorem holds_stNib {j : ℕ} (h : Stmt.HoldsList C rd σ (stNib j) True kret) :
    (LoadHolds rd (σ (.n 1)) (4 * j + 3) (σ (.n (stB j))) ∧
      LoadHolds rd (σ (.n 0)) (4 * j + 3) (σ (.n (stB j + 1)))) ∧
    Stmt.HoldsList C rd σ (stLevel j 1) True kret ∧ Stmt.HoldsList C rd σ (stLevel j 2) True kret ∧
    Stmt.HoldsList C rd σ (stLevel j 3) True kret ∧
    (∀ w < 4, ∀ i < 2 ^ (w + 1),
      LoadHolds rd (σ (.n 2)) (64 * j + 16 * w + i * 2 ^ (3 - w)) (σ (.n (stV j w i)))) := by
  have n0 : Stmt.noRetList [Stmt.atom (.load (.n (stB j)) (.n 1) (4 * j + 3)),
      Stmt.atom (.load (.n (stB j + 1)) (.n 0) (4 * j + 3))] = true := rfl
  rw [stNib, tb_holdsList_append_noRet (by simp only [tb_noRetList_append, stLevel_noRet, n0,
      Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, stLevel_noRet, n0,
      Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, stLevel_noRet, n0,
      Bool.and_self]),
    tb_holdsList_append_noRet n0, tb_holdsList_flatten_range _ _ (stStores_noRet j)] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
  refine ⟨h0, h1, h2, h3, fun w hw i hi => ?_⟩
  have := h4 w hw
  rw [stStores, tb_holdsList_mapAtoms] at this
  exact this i hi

/-- **The eq levels of nibble `j`**: level `w`'s entry `i` is the table's entry `i·2^(3 - w)`. -/
theorem stLevels {j : ℕ} (hj : j < 7) {p p1 : List E} (hp : p.length = 28) (hp1 : p1.length = 28)
    (hpt : TbReadsAt rd (σ (.n 0)) p) (hpt1 : TbReadsAt rd (σ (.n 1)) p1)
    (h : Stmt.HoldsList C rd σ (stNib j) True kret) :
    ∀ w < 4, ∀ i < 2 ^ (w + 1), σ (.n (stV j w i)) = selEqEntry p p1 j w (i * 2 ^ (3 - w)) := by
  obtain ⟨⟨l0, l1⟩, hL1, hL2, hL3, -⟩ := holds_stNib h
  have hrd : ∀ (q : List E) (pq : E), q.length = 28 → TbReadsAt rd pq q → ∀ s < 4, ∀ x,
      LoadHolds rd pq (4 * j + s) x → x = q.getD (4 * j + s) 0 := fun q pq hq hr s hs x hx => by
    have := hr (4 * j + s) (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact tb_loadHolds_unique hx this
  intro w hw
  induction w with
  | zero =>
    intro i hi
    have e0 := hrd p1 _ hp1 hpt1 3 (by omega) _ l0
    have e1 := hrd p _ hp hpt 3 (by omega) _ l1
    interval_cases i
    · simp only [stV, stM, stB, List.getD_cons_zero, Nat.add_zero, selEqEntry, Nat.zero_mul,
        Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]
      rw [show (3 : ℕ) - 0 = 3 from rfl, Finset.prod_Ico_succ_top (by omega), Finset.Ico_self,
        Finset.prod_empty, one_mul, ← e0]
      rfl
    · simp only [selEqEntry]
      rw [show (3 : ℕ) - 0 = 3 from rfl, Finset.prod_Ico_succ_top (by omega), Finset.Ico_self,
        Finset.prod_empty, one_mul, show 1 * 2 ^ 3 = 8 from rfl,
        show (8 : ℕ).testBit 3 = true by decide, ite_eq_left rfl, ← e1]
      rfl
  | succ w ih =>
    intro i hi
    have hL : Stmt.HoldsList C rd σ (stLevel j (w + 1)) True kret := by
      have hw3 : w < 3 := by omega
      interval_cases w
      · exact hL1
      · exact hL2
      · exact hL3
    obtain ⟨hz, hz1, hm⟩ := holds_stLevel hL
    have ez := hrd p _ hp hpt (2 - w) (by omega) _ (by
      rw [show 4 * j + (2 - w) = 4 * j + 3 - (w + 1) by omega]; exact hz)
    have ez1 := hrd p1 _ hp1 hpt1 (2 - w) (by omega) _ (by
      rw [show 4 * j + (2 - w) = 4 * j + 3 - (w + 1) by omega]; exact hz1)
    obtain ⟨i', c, hc, rfl⟩ : ∃ i' c, c < 2 ∧ i = 2 * i' + c := ⟨i / 2, i % 2, by omega, by omega⟩
    have hi' : i' < 2 ^ (w + 1) := by rw [pow_succ] at hi; omega
    rw [show 3 - (w + 1) = 2 - w by omega, selEqEntry_succ p p1 j (by omega) i' c hc,
      ← ih (by omega) i' hi']
    obtain ⟨m0, m1⟩ := hm i' hi'
    interval_cases c
    · simp only [Nat.add_zero]
      rw [m0, Nat.add_sub_cancel, mul_comm, ez1]; rfl
    · rw [m1, Nat.add_sub_cancel, mul_comm, ez]; rfl

end Sem

/-- **`selector_tables` is sound**: for the point and its complements read at its arguments, the
returned buffer holds their strided eq tables. -/
theorem selector_tables_sound {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd "selector_tables" args rets) : SelTablesOut rd args rets := by
  obtain ⟨fn, hf, hp, hb⟩ := stFound
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb stPre_noRet args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar hret
  subst hpar hret
  rw [stPre, tb_holdsList_append_noRet (by
      rw [tb_noRetList_append, tb_noRetList_flatten_range _ _ stNib_noRet]; rfl),
    tb_holdsList_append_noRet rfl, tb_holdsList_flatten_range _ _ stNib_noRet] at hpre
  obtain ⟨⟨-, hnibs⟩, hcopy⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hcopy
  simp only [SelTablesOut]
  intro p p1 hp hp1 hpt hpt1 j hj w hw u hu hdiv
  have hN := hnibs j hj
  have hlev := stLevels hj hp hp1 hpt hpt1 hN
  obtain ⟨-, -, -, -, hst⟩ := holds_stNib hN
  obtain ⟨i, rfl⟩ := hdiv
  have hi : i < 2 ^ (w + 1) := by
    have : 2 ^ (3 - w) * 2 ^ (w + 1) = 16 := by
      rw [← pow_add, show 3 - w + (w + 1) = 4 by omega]; rfl
    by_contra hc
    have := Nat.mul_le_mul_left (2 ^ (3 - w)) (Nat.le_of_not_lt hc)
    omega
  rw [hcopy, mul_comm (2 ^ (3 - w)) i, ← hlev w hw i hi]
  exact hst w hw i hi

theorem selector_tables_holds : selector_tables_Spec := fun _ _ _ h => selector_tables_sound h

end
end LeanVM.Guest.B1.Tables
