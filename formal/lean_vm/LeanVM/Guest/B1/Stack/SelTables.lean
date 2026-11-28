/-
  LeanVM.Guest.B1.Stack.SelTables

  B1 of `selector_tables`: per nibble of the opening point, the eq tables over its top coordinates.
-/

module

public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

/-!
# `selector_tables`

`selector_tables(point, point1, n_nib)` allocates `sel_eq` (`32 n_nib` words) and, per nibble `j`,
builds the eq tables of its top `w + 1` coordinates `4j + 3 - w .. 4j + 3`, `w < 4`, level by level
(`stLev`: level `w + 1`'s entry `k` is level `w`'s `k / 2` times `point1` or `point` at coordinate
`4j + 2 - w`, as `k` is even or odd), and stores level `w`'s entry `k` at
`32 j + SEL_EQ_OFF[w] + k·2^(3-w)` (`selLev`, `MeaningSelectorTables`, `selector_tables_holds`).
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The meaning -/

/-- `SEL_EQ_OFF`: level `w`'s offset in a nibble's stride. -/
def selOff (w : ℕ) : ℕ := [4, 2, 1, 16].getD w 0

/-- Level `w`'s entry `k` of nibble `j`, from the point's words `p` and one plus them `p1`. -/
def selLev (p p1 : ℕ → E) (j : ℕ) : ℕ → ℕ → E
  | 0, k => if k = 0 then p1 (4 * j + 3) else p (4 * j + 3)
  | w + 1, k => selLev p p1 j w (k / 2) * (if k % 2 = 0 then p1 (4 * j + 2 - w) else p (4 * j + 2 - w))

/-- **`selector_tables(point, point1, n_nib)`**: on the words `p` at `point` and `p1` at `point1`
below `4 n_nib`, it returns `sel_eq`, holding level `w`'s entry `k` of nibble `j` at
`32 j + selOff w + k·2^(3-w)`. -/
def MeaningSelectorTables (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [pt, pt1], rets => ∃ q : E, rets = [q] ∧ ∀ p p1 : ℕ → E,
      (∀ i < 4 * n, LoadHolds rd pt i (p i)) → (∀ i < 4 * n, LoadHolds rd pt1 i (p1 i)) →
      ∀ j < n, ∀ w < 4, ∀ k < 2 ^ (w + 1),
        LoadHolds rd q (32 * j + selOff w + k * 2 ^ (3 - w)) (selLev p p1 j w k)
  | _, _ => False

/-! ## The template -/

/-- Level `w`'s first value in the nibble from `s`: its two coordinate loads. -/
def stBase (s w : ℕ) : ℕ := s + 2 * w + 2 ^ (w + 1) - 4

/-- Level `w`'s entry `k`'s value. -/
def stV (s w k : ℕ) : ℕ := if w = 0 then s + k else stBase s w + 2 + k

/-- Level `w ≥ 1` of nibble `j` from `s`: the coordinate's two words, then each entry's two
products. -/
def stLev (j s w : ℕ) : List Stmt :=
  [.atom (.load (.n (stBase s w)) (.n 0) (4 * j + 3 - w)),
    .atom (.load (.n (stBase s w + 1)) (.n 1) (4 * j + 3 - w))] ++
  ((List.range (2 ^ w)).map fun i ↦
    [osMul (stV s w (2 * i)) (stV s (w - 1) i) (stBase s w + 1),
      osMul (stV s w (2 * i + 1)) (stV s (w - 1) i) (stBase s w)]).flatten

/-- The stores of nibble `j`'s levels. -/
def stStores (j s : ℕ) : List Stmt :=
  ((List.range 4).map fun w ↦ (List.range (2 ^ (w + 1))).map fun k ↦
    (.atom (.load (.n (stV s w k)) (.n 3) (32 * j + selOff w + k * 2 ^ (3 - w))) : Stmt)).flatten

/-- Nibble `j` from `s`. -/
def stNib (j s : ℕ) : List Stmt :=
  [.atom (.load (.n s) (.n 1) (4 * j + 3)), .atom (.load (.n (s + 1)) (.n 0) (4 * j + 3))] ++
    stLev j s 1 ++ stLev j s 2 ++ stLev j s 3 ++ stStores j s

/-- The statements of `selector_tables__L{n}` before its return. -/
def stBodyA (n : ℕ) : List Stmt :=
  [osCst 2 (gw (32 * n)), .atom (.hint (.allocDyn (.n 3) (.n 2)))] ++
    ((List.range n).map fun j ↦ stNib j (4 + 36 * j)).flatten ++ [.atom (.copy (.n (4 + 36 * n)) (.n 3))]

/-- **The expansion of `selector_tables__L{n}`.** -/
def stBody (n : ℕ) : List Stmt := stBodyA n ++ [.ret [.n (4 + 36 * n)]]

set_option maxRecDepth 100000 in
theorem selector_tables_L4_body : Fn.body fn% «selector_tables__L4» = stBody 4 :=
  stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem selector_tables_L5_body : Fn.body fn% «selector_tables__L5» = stBody 5 :=
  stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem selector_tables_L6_body : Fn.body fn% «selector_tables__L6» = stBody 6 :=
  stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem selector_tables_L7_body : Fn.body fn% «selector_tables__L7» = stBody 7 :=
  stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem selector_tables_L8_body : Fn.body fn% «selector_tables__L8» = stBody 8 :=
  stmtsEqb_sound (by decide +kernel)

/-! ## Soundness -/

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem stBodyA_flat (n : ℕ) : (stBodyA n).all Stmt.flat = true := by
  simp [stBodyA, stNib, stLev, stStores, List.all_flatten, List.all_map, Stmt.flat, osMul, osCst]

theorem stLev_ok {j s w : ℕ} (h : AllOk C rd σ (stLev j s w)) :
    LoadHolds rd (σ (.n 0)) (4 * j + 3 - w) (σ (.n (stBase s w))) ∧
      LoadHolds rd (σ (.n 1)) (4 * j + 3 - w) (σ (.n (stBase s w + 1))) ∧
      ∀ i < 2 ^ w, σ (.n (stV s w (2 * i))) = σ (.n (stV s (w - 1) i)) * σ (.n (stBase s w + 1)) ∧
        σ (.n (stV s w (2 * i + 1))) = σ (.n (stV s (w - 1) i)) * σ (.n (stBase s w)) := by
  simp only [stLev, allOk_append, allOk_cons, allOk_nil, and_true, allOk_flatten, List.mem_map,
    List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨l0, l1⟩, hp⟩ := h
  simp only [StmtOk, Atom.Holds] at l0 l1
  refine ⟨l0, l1, fun i hi ↦ ?_⟩
  have := hp i hi
  simp only [StmtOk, Atom.Holds] at this
  exact this

theorem stStores_ok {j s : ℕ} (h : AllOk C rd σ (stStores j s)) :
    ∀ w < 4, ∀ k < 2 ^ (w + 1),
      LoadHolds rd (σ (.n 3)) (32 * j + selOff w + k * 2 ^ (3 - w)) (σ (.n (stV s w k))) := by
  intro w hw k hk
  have := h _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨w, List.mem_range.2 hw, rfl⟩,
    List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩⟩)
  simpa [StmtOk, Atom.Holds] using this

theorem stNib_ok_stores {j s : ℕ} (h : AllOk C rd σ (stNib j s)) : AllOk C rd σ (stStores j s) := by
  simp only [stNib, allOk_append] at h
  exact h.2

/-- Nibble `j`'s levels hold `selLev`. -/
theorem stNib_vals {p p1 : ℕ → E} {j s : ℕ} (hp : ∀ i ≤ 4 * j + 3, LoadHolds rd (σ (.n 0)) i (p i))
    (hp1 : ∀ i ≤ 4 * j + 3, LoadHolds rd (σ (.n 1)) i (p1 i)) (h : AllOk C rd σ (stNib j s)) :
    ∀ w < 4, ∀ k < 2 ^ (w + 1), σ (.n (stV s w k)) = selLev p p1 j w k := by
  simp only [stNib, allOk_append, allOk_cons, allOk_nil, and_true] at h
  obtain ⟨⟨⟨⟨⟨l0, l1⟩, h1⟩, h2⟩, h3⟩, -⟩ := h
  simp only [StmtOk, Atom.Holds] at l0 l1
  have hlev : ∀ w, 1 ≤ w → w < 4 → AllOk C rd σ (stLev j s w) := fun w h1w hw ↦ by
    interval_cases w
    exacts [h1, h2, h3]
  intro w
  induction w with
  | zero =>
    intro _ k hk
    rcases k with _ | _ | k
    · simp only [stV, ↓reduceIte, Nat.add_zero, selLev]
      exact loadHolds_unique l0 (hp1 _ le_rfl)
    · simp only [stV, ↓reduceIte, selLev]
      exact loadHolds_unique l1 (hp _ le_rfl)
    · simp at hk
  | succ w ih =>
    intro hw k hk
    obtain ⟨lb0, lb1, hprod⟩ := stLev_ok (hlev (w + 1) (by omega) hw)
    have hr : σ (.n (stBase s (w + 1))) = p (4 * j + 2 - w) := by
      rw [show 4 * j + 2 - w = 4 * j + 3 - (w + 1) by omega]
      exact loadHolds_unique lb0 (hp _ (by omega))
    have hr1 : σ (.n (stBase s (w + 1) + 1)) = p1 (4 * j + 2 - w) := by
      rw [show 4 * j + 2 - w = 4 * j + 3 - (w + 1) by omega]
      exact loadHolds_unique lb1 (hp1 _ (by omega))
    obtain ⟨i, rfl | rfl⟩ : ∃ i, k = 2 * i ∨ k = 2 * i + 1 := ⟨k / 2, by omega⟩
    · have hi : i < 2 ^ (w + 1) := by rw [pow_succ] at hk; omega
      rw [(hprod i hi).1, Nat.add_sub_cancel, ih (by omega) i hi, hr1, selLev,
        show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega]
      simp
    · have hi : i < 2 ^ (w + 1) := by rw [pow_succ] at hk; omega
      rw [(hprod i hi).2, Nat.add_sub_cancel, ih (by omega) i hi, hr, selLev,
        show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega]
      simp

/-- **`selector_tables__L{n}` gives its meaning**, from its template. -/
theorem st_sound {name : String} {f : Fn} (n : ℕ) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = stBody n) (rd : Reader)
    (args rets : List E) (h : coreProgram.Rel rd name args rets) : MeaningSelectorTables n rd args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem hfind args rets).mp h
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [hbody, stBody, holdsList_flat_ret _ (stBodyA_flat n)] at hb
  obtain ⟨hA, hret⟩ := hb
  simp only [stBodyA, allOk_append, allOk_cons, allOk_nil, and_true, allOk_flatten, List.mem_map,
    List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hA
  obtain ⟨⟨-, hnib⟩, hcp⟩ := hA
  simp only [StmtOk, Atom.Holds] at hcp
  simp only [List.map_cons, List.map_nil] at hret
  refine ⟨σ (.n 3), by rw [← hret, hcp], fun p p1 hp hp1 j hj w hw k hk ↦ ?_⟩
  have hv := stNib_vals (p := p) (p1 := p1) (fun i hi ↦ hp i (by omega)) (fun i hi ↦ hp1 i (by omega))
    (hnib j hj) w hw k hk
  rw [← hv]
  exact stStores_ok (stNib_ok_stores (hnib j hj)) w hw k hk

/-- `selector_tables`' specializations: the nibbles and the name. -/
def selectorTablesNames : List (ℕ × String) :=
  [(4, "selector_tables__L4"), (5, "selector_tables__L5"), (6, "selector_tables__L6"),
    (7, "selector_tables__L7"), (8, "selector_tables__L8")]

set_option maxRecDepth 100000 in
/-- **`selector_tables` gives its meaning**, every specialization. -/
theorem selector_tables_holds : ∀ p ∈ selectorTablesNames, ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd p.2 args rets → MeaningSelectorTables p.1 rd args rets := by
  intro p hp
  simp only [selectorTablesNames, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact st_sound 4 (coreProgram_find?_at (j := idx% «selector_tables__L4») rfl) rfl selector_tables_L4_body
  · exact st_sound 5 (coreProgram_find?_at (j := idx% «selector_tables__L5») rfl) rfl selector_tables_L5_body
  · exact st_sound 6 (coreProgram_find?_at (j := idx% «selector_tables__L6») rfl) rfl selector_tables_L6_body
  · exact st_sound 7 (coreProgram_find?_at (j := idx% «selector_tables__L7») rfl) rfl selector_tables_L7_body
  · exact st_sound 8 (coreProgram_find?_at (j := idx% «selector_tables__L8») rfl) rfl selector_tables_L8_body

end
end LeanVM.Guest.B1.Stack
