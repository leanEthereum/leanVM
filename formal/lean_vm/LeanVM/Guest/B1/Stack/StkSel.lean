/-
  LeanVM.Guest.B1.Stack.StkSel

  B1 of `stack_selectors`: each stack block's selector is its placement's `eqAbove` at the opening
  point.
-/

module

public import LeanVM.Guest.B1.Stack.Placed
public import LeanVM.Guest.B1.Stack.ColSelAll

/-!
# `stack_selectors`

`stack_selectors(offs, kaps, point, point1, g_squares, n_nib)` builds the selector tables
(`selector_tables__L{n}`), then per block reads its offset and kappa and dispatches on the kappa to
`column_selector__L{n}_L{κ}`, storing the selector at `sel[b]` (`stsBody`). On a layout `buildLayout`
returns, the offset is the block's index, aligned to its size and inside the stack (`layout_block`);
the column selector's product over the index's bits from `κ` to `4 n` is the placement's
`eqAbove` at the opening point, the point zero and `point1` one past the stack's log
(`eqAbove_selProd`). `stack_selectors_holds`: every specialization gives `MeaningStackSelectors`.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- Block `b`: its offset, `g_squares·g^34`, its kappa, the dispatch, the store. -/
def stsBlock (n b : ℕ) : List Stmt :=
  [.atom (.load (.n (7 + 5 * b)) (.n 0) b), osCst (8 + 5 * b) (csW 34), osMul (9 + 5 * b) 4 (8 + 5 * b),
    .atom (.load (.n (10 + 5 * b)) (.n 1) b),
    .dispatch (.n (10 + 5 * b)) ((List.range 31).map (cselName n)) [.n (7 + 5 * b), .n 5, .n (9 + 5 * b)]
      [.n (11 + 5 * b)],
    .atom (.load (.n (11 + 5 * b)) (.n 6) b)]

/-- `stack_selectors__L{n}` before its return. -/
def stsBodyA (n : ℕ) : List Stmt :=
  [.call ("selector_tables__L" ++ natStr n) [.n 2, .n 3] [.n 5], .atom (.hint (.alloc (.n 6) 52))] ++
    ((List.range 52).map (stsBlock n)).flatten ++ [.atom (.copy (.n 267) (.n 6))]

/-- **The expansion of `stack_selectors__L{n}`.** -/
def stsBody (n : ℕ) : List Stmt := stsBodyA n ++ [.ret [.n 267]]

set_option maxRecDepth 100000 in
theorem stack_selectors_L4_body : Fn.body fn% «stack_selectors__L4» = stsBody 4 :=
  stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem stack_selectors_L5_body : Fn.body fn% «stack_selectors__L5» = stsBody 5 :=
  stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem stack_selectors_L6_body : Fn.body fn% «stack_selectors__L6» = stsBody 6 :=
  stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem stack_selectors_L7_body : Fn.body fn% «stack_selectors__L7» = stsBody 7 :=
  stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem stack_selectors_L8_body : Fn.body fn% «stack_selectors__L8» = stsBody 8 :=
  stmtsEqb_sound (by decide +kernel)

/-! ## `eqAbove` as the selector's product -/

/-- The opening point padded with zeros, and one plus it padded with ones. -/
def padPt (x : List E) (t : ℕ) : E := (x ++ List.replicate (40 - x.length) 0).getD t 0
def padPt1 (x : List E) (t : ℕ) : E := (x.map (1 + ·) ++ List.replicate (40 - x.length) 1).getD t 0

theorem foldl_mul_eq (a : E) : ∀ l : List E, l.foldl (· * ·) a = a * l.prod
  | [] => by simp
  | y :: l => by rw [List.foldl_cons, foldl_mul_eq _ l, List.prod_cons, mul_assoc]

theorem prod_map_range (h : ℕ → E) : ∀ k, ((List.range k).map h).prod = ∏ i ∈ Finset.range k, h i
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, prod_map_range h k, Finset.prod_range_succ]
    simp

theorem padPt_lt {x : List E} {t : ℕ} (ht : t < x.length) : padPt x t = x[t] := by
  simp [padPt, List.getD_eq_getElem?_getD, List.getElem?_append_left ht, List.getElem?_eq_getElem ht]

theorem padPt1_lt {x : List E} {t : ℕ} (ht : t < x.length) : padPt1 x t = 1 + x[t] := by
  rw [padPt1, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using ht), List.getElem?_map,
    List.getElem?_eq_getElem ht]
  rfl

theorem padPt1_ge {x : List E} {t : ℕ} (ht : x.length ≤ t) (h40 : t < 40) : padPt1 x t = 1 := by
  simp only [padPt1, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simpa using ht)]
  simp [show t - x.length < 40 - x.length by omega]

/-- **`eqAbove` is the column selector's product**: at an index below `2^m`, `m` the point's length,
the product over the index's bits from `vc` to `N`, `m ≤ N ≤ 40`, of `point` or `point1`. -/
theorem eqAbove_selProd (x : List E) {vc idx N : ℕ} (hvc : vc ≤ x.length) (hidx : idx < 2 ^ x.length)
    (hN : x.length ≤ N) (hN40 : N ≤ 40) :
    ({ variableCount := vc, index := idx } : Placement).eqAbove x =
      ∏ t ∈ Finset.Ico vc N, selBit (padPt x) (padPt1 x) idx t := by
  rw [← Finset.prod_Ico_consecutive _ hvc hN]
  have hhigh : ∏ t ∈ Finset.Ico x.length N, selBit (padPt x) (padPt1 x) idx t = 1 := by
    refine Finset.prod_eq_one fun t ht ↦ ?_
    have ht' := Finset.mem_Ico.1 ht
    have hb : idx.testBit t = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) ht'.1))
    simp only [selBit, hb, Bool.false_eq_true, ↓reduceIte]
    exact padPt1_ge ht'.1 (by omega)
  rw [hhigh, mul_one, Finset.prod_Ico_eq_prod_range]
  unfold Placement.eqAbove eqEval
  simp only
  rw [foldl_mul_eq, one_mul]
  have hz : List.zipWith (fun a b ↦ 1 + a + b) (selectorPoint (idx >>> vc) (x.length - vc)) (x.drop vc) =
      (List.range (x.length - vc)).map fun i ↦ selBit (padPt x) (padPt1 x) idx (vc + i) := by
    apply List.ext_getElem (by simp [selectorPoint])
    intro i h1 h2
    simp only [List.getElem_zipWith, selectorPoint, List.getElem_map, List.getElem_range,
      List.getElem_drop]
    have hi : vc + i < x.length := by simp [selectorPoint] at h1; omega
    rw [← Nat.shiftRight_add, Nat.shiftRight_eq_div_pow, selBit, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (idx / 2 ^ (vc + i)) with h | h
    · rw [h, eOfNat_zero, padPt1_lt hi]; simp
    · rw [h, eOfNat_one, padPt_lt hi, e_add_self, zero_add]; simp
  rw [hz, prod_map_range]

/-! ## Soundness -/

theorem stsBodyA_flat (n : ℕ) : (stsBodyA n).all Stmt.flat = true := by
  simp [stsBodyA, stsBlock, List.all_flatten, List.all_map, Stmt.flat, osMul, osCst]

theorem cselNames_getD (n vc : ℕ) (h : vc < 31) :
    ((List.range 31).map (cselName n)).getD vc "" = cselName n vc := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp

/-- **`stack_selectors__L{n}` gives its meaning**, from its template and `selector_tables__L{n}`'s. -/
theorem sts_sound {m : ℕ} (hm : m ≤ 32) (hm6 : 6 ≤ m) (L : MemoryImage m) {name : String} {f : Fn}
    (n : ℕ) (hn4 : 4 ≤ n) (hn : n ≤ 8) (hfind : coreProgram.find? name = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hbody : f.body = stsBody n)
    (hst : ∀ args rets, coreProgram.Rel L.read ("selector_tables__L" ++ natStr n) args rets →
      MeaningSelectorTables n L.read args rets)
    (args rets : List E) (h : coreProgram.Rel L.read name args rets) :
    MeaningStackSelectors n L.read args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem hfind args rets).mp h
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [hbody, stsBody, holdsList_flat_ret _ (stsBodyA_flat n)] at hb
  obtain ⟨hA, hret⟩ := hb
  simp only [stsBodyA, allOk_append, allOk_cons, allOk_nil, and_true, allOk_flatten, List.mem_map,
    List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hA
  obtain ⟨⟨⟨hcall, -⟩, hblk⟩, hcp⟩ := hA
  simp only [StmtOk, Atom.Holds, List.map_cons, List.map_nil] at hcall hcp
  simp only [List.map_cons, List.map_nil] at hret
  intro layout gmv x ⟨bytecode, rows, hbl⟩ hplaced hxl hnn hexp hpt hpt1
  have hx4 : x.length ≤ 4 * n := by omega
  have hx40 : x.length ≤ 40 := by omega
  -- the tables
  obtain ⟨q, hq, htab⟩ := hst _ _ hcall
  simp only [List.cons.injEq, and_true] at hq
  have hreadP : ∀ i < 4 * n, LoadHolds L.read (σ (.n 2)) i (padPt x i) := fun i hi ↦ by
    have := hpt i (by simp; omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  have hreadP1 : ∀ i < 4 * n, LoadHolds L.read (σ (.n 3)) i (padPt1 x i) := fun i hi ↦ by
    have := hpt1 i (by simp; omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  have htabs := htab (padPt x) (padPt1 x) hreadP hreadP1
  rw [← hq] at htabs
  refine ⟨σ (.n 6), by rw [← hret, hcp], fun b hb ↦ ?_⟩
  obtain ⟨p, hp, ho, hk⟩ := hplaced.2 b hb
  have hb52 : b < 52 := by simpa [nStkBlocks, stackBlocks_length] using hb
  obtain ⟨p', hp', -, -, hal, hin⟩ := layout_block hbl hb52
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  refine ⟨p, hp, ?_⟩
  have hvc : p.variableCount ≤ layout.stackLog := by
    have : 2 ^ p.variableCount ≤ 2 ^ layout.stackLog := le_trans (Nat.le_add_left _ _) hin
    exact (Nat.pow_le_pow_iff_right (by decide)).1 this
  have hidx : p.index < 2 ^ layout.stackLog := lt_of_lt_of_le (by
    have := Nat.one_le_two_pow (n := p.variableCount); omega) hin
  -- the block
  have hB := hblk b hb52
  simp only [stsBlock, allOk_cons, allOk_nil, and_true] at hB
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hB
  simp only [StmtOk, Atom.Holds] at b0 b1 b2 b3 b5
  have e0 := loadHolds_unique b0 ho
  have e3 := loadHolds_unique b3 hk
  obtain ⟨hvc31, hrel⟩ := stmtOk_dispatch (by rw [e3, gen_pow_eq_ofK])
    (by omega) (by simp) b4
  simp only [List.length_map, List.length_range] at hvc31
  rw [cselNames_getD n _ hvc31] at hrel
  simp only [List.map_cons, List.map_nil] at hrel
  have hcs := column_selector_holds hm hm6 L n p.variableCount hn4 hn (by omega) _ _ hrel
    (padPt x) (padPt1 x) p.index htabs (fun j hj u hu ↦ by
      rw [b2, b1, csW_eq (by decide), loadHolds_mul_gen_pow,
        show 34 + (16 * j + u) = sizeBits + 16 * j + u by simp only [sizeBits]; omega]
      exact hexp.2 j hj u hu) e0
    (lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) (by omega))) hal
  simp only [List.cons.injEq, and_true] at hcs
  rw [hcs] at b5
  rw [show p = ({ variableCount := p.variableCount, index := p.index } : Placement) from rfl,
    eqAbove_selProd x (by omega) (by rw [hxl]; exact hidx) hx4 (by omega)]
  exact b5

set_option maxRecDepth 100000 in
/-- **`stack_selectors` gives its meaning**, every specialization. -/
theorem stack_selectors_holds {m : ℕ} (hm : m ≤ 32) (hm6 : 6 ≤ m) (L : MemoryImage m) :
    ∀ p ∈ stackSelectorsNames, ∀ args rets, coreProgram.Rel L.read p.2 args rets →
      MeaningStackSelectors p.1 L.read args rets := by
  have hst := fun q (hq : q ∈ selectorTablesNames) ↦ selector_tables_holds q hq L.read
  intro p hp
  simp only [stackSelectorsNames, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact sts_sound hm hm6 L 4 (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «stack_selectors__L4») rfl) rfl stack_selectors_L4_body
      (hst (4, "selector_tables__L4") (by simp [selectorTablesNames]))
  · exact sts_sound hm hm6 L 5 (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «stack_selectors__L5») rfl) rfl stack_selectors_L5_body
      (hst (5, "selector_tables__L5") (by simp [selectorTablesNames]))
  · exact sts_sound hm hm6 L 6 (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «stack_selectors__L6») rfl) rfl stack_selectors_L6_body
      (hst (6, "selector_tables__L6") (by simp [selectorTablesNames]))
  · exact sts_sound hm hm6 L 7 (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «stack_selectors__L7») rfl) rfl stack_selectors_L7_body
      (hst (7, "selector_tables__L7") (by simp [selectorTablesNames]))
  · exact sts_sound hm hm6 L 8 (by decide) (by decide)
      (coreProgram_find?_at (j := idx% «stack_selectors__L8») rfl) rfl stack_selectors_L8_body
      (hst (8, "selector_tables__L8") (by simp [selectorTablesNames]))

end
end LeanVM.Guest.B1.Stack
