/-
  LeanVM.Guest.Complete.CycVs

  The cycle hand facts of `verify_sub` and the callees whose values it certifies (`verify_keccak`,
  `check_stack_terminal`), from those values' bounds (`VsNodeVals`).
-/

module

public import LeanVM.Guest.Complete.CycOwn

/-!
# `verify_sub`'s cycle hand facts from its values

What `verify_sub`'s path certifies of the child's shape, read at each node (`VsNodeVals`):

* at `verify_sub`: its commitment count `v42 = g^c`, `c ≤ 32`, and its four shape values' exponents within
  `19, 24, 24, 24` (`p`, `w`, `n`, `τ`);
* at `verify_keccak`: `v18 = g^e` with `e` within its table log's exponent (`v6`'s, `τ - 4` when `τ ≥ 4`);
* at `check_stack_terminal`: `v58`'s exponent within `30` (`v51 · g^6`, `v51` a pointer width within `24`).

Each cycle hand fact is then linear arithmetic at each opcode (`verify_sub_cyc`, `verify_keccak_cyc`,
`check_stack_terminal_cyc`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-- **The values `verify_sub` certifies, at a node**: its own shape values, `verify_keccak`'s reduced height and
`check_stack_terminal`'s window. -/
def VsNodeVals (f : String) (σ : Val) : Prop :=
  (f = "verify_sub" → (∃ e, GPow (σ (.n 42)) e ∧ e ≤ 32) ∧ logG (σ (.n 645)) ≤ 19 ∧ logG (σ (.n 409)) ≤ 24 ∧
    logG (σ (.n 408)) ≤ 24 ∧ logG (σ (.n 120)) ≤ 24) ∧
  (f = "verify_keccak" → ∃ e, GPow (σ (.n 18)) e ∧ e ≤ logG (σ (.n 6))) ∧
  (f = "check_stack_terminal" → logG (σ (.n 58)) ≤ 30)

/-! ## `verify_sub` -/

theorem chhand_vs : Data.chhandJ (idx% «verify_sub») = some ⟨[.n 42, .n 645, .n 409, .n 408, .n 120],
    [(6, 18446744073709551616)], ⟨[93630, 120390, 28382, 55975, 12647, 8979], [(6, [1, 11, 4, 4, 2, 0]),
      (7, [1, 3, 2, 12, 1, 1]), (8, [4, 6, 5, 8, 1, 1]), (9, [16, 12, 10, 14, 1, 2]), (9, [24, 40, 14, 34, 2, 3]),
      (9, [26, 42, 16, 35, 2, 3]), (9, [28, 44, 15, 36, 2, 3]), (10, [3, 12, 12, 21, 6, 0]),
      (9, [65, 129, 1, 76, 1, 0])]⟩, []⟩ := rfl

theorem chcert_vs : Data.chcertJ (idx% «verify_sub») =
    .stat [] ⟨[97665, 127639, 30300, 61707, 13090, 9286], []⟩ [] := rfl

set_option maxRecDepth 100000 in
/-- **`verify_sub`'s cycle hand fact**, from its values. -/
theorem verify_sub_cyc (op : Opcode) (C₁ C₂ : ℕ) {σ : Val} (h : VsNodeVals "verify_sub" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "verify_sub" σ := by
  obtain ⟨⟨c, gc, hc⟩, hp', hw, hn, hτ⟩ := h.1 rfl
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «verify_sub») rfl) (by decide) (by decide)
    (by decide) chhand_vs chcert_vs fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «verify_sub») rfl))
  subst e
  have hp : (fn% «verify_sub»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5].map σ with hps
  set vs : List E := ps ++ [V.n 42, .n 645, .n 409, .n 408, .n 120].map σ with hvs
  have a6 : argExp vs 6 = c := argExp_gpow rfl gc
  have a7 : argExp vs 7 = logG (σ (.n 645)) := rfl
  have a8 : argExp vs 8 = logG (σ (.n 409)) := rfl
  have a9 : argExp vs 9 = logG (σ (.n 408)) := rfl
  have a10 : argExp vs 10 = logG (σ (.n 120)) := rfl
  refine ⟨argsPre_gT (vs := vs) (k := 6) (e := c) gc.1 gc.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, a6, a7, a8, a9, a10] <;> omega

/-! ## `verify_keccak` -/

theorem chhand_vk : Data.chhandJ (idx% «verify_keccak») = some ⟨[.n 18], [(12, 18446744073709551616)],
    ⟨[8833, 11371, 2714, 5533, 94, 699], [(12, [1, 4, 4, 7, 2, 0]), (12, [1, 4, 4, 7, 2, 0]),
      (12, [1, 4, 4, 7, 2, 0])]⟩, [(.n 63, 0), (.n 65, 0), (.n 1188, 0), (.n 1190, 0), (.n 3354, 0), (.n 3356, 0),
      (.n 64, 1048577), (.n 1189, 1048577), (.n 3355, 1048577)]⟩ := rfl

theorem chcert_vk : Data.chcertJ (idx% «verify_keccak») =
    .stat [] ⟨[8833, 11371, 2714, 5533, 94, 699], [(6, [3, 12, 12, 21, 6, 0])]⟩ [] := rfl

set_option maxRecDepth 100000 in
/-- **`verify_keccak`'s cycle hand fact**, from its values. -/
theorem verify_keccak_cyc (op : Opcode) (C₁ C₂ : ℕ) {σ : Val} (h : VsNodeVals "verify_keccak" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "verify_keccak" σ := by
  obtain ⟨e, ge, he⟩ := h.2.1 rfl
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «verify_keccak») rfl) (by decide) (by decide)
    (by decide) chhand_vk chcert_vk fun fn hfn => ?_
  have e' := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «verify_keccak») rfl))
  subst e'
  have hp : (fn% «verify_keccak»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
    .n 11] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11].map σ with hps
  set vs : List E := ps ++ [V.n 18].map σ with hvs
  have a12 : argExp vs 12 = e := argExp_gpow rfl ge
  have a6 : argExp ps 6 = logG (σ (.n 6)) := rfl
  refine ⟨argsPre_gT (vs := vs) (k := 12) (e := e) ge.1 ge.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, a12, a6] <;> omega

/-! ## `check_stack_terminal` -/

theorem chhand_cst : Data.chhandJ (idx% «check_stack_terminal») = some ⟨[.n 58], [],
    ⟨[3353, 8905, 231, 5081, 151, 0], [(23, [65, 129, 1, 20, 1, 0]), (6, [65, 129, 1, 76, 1, 0])]⟩,
    [(.n 572, 0), (.n 609, 0), (.n 612, 0), (.n 615, 0), (.n 616, 0)]⟩ := rfl

theorem chcert_cst : Data.chcertJ (idx% «check_stack_terminal») =
    .stat [] ⟨[5303, 12775, 261, 5681, 181, 0], [(6, [65, 129, 1, 76, 1, 0])]⟩ [] := rfl

set_option maxRecDepth 100000 in
/-- **`check_stack_terminal`'s cycle hand fact**, from its values. -/
theorem check_stack_terminal_cyc (op : Opcode) (C₁ C₂ : ℕ) {σ : Val} (h : VsNodeVals "check_stack_terminal" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "check_stack_terminal" σ := by
  have h58 := h.2.2 rfl
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «check_stack_terminal») rfl) (by decide) (by decide)
    (by decide) chhand_cst chcert_cst fun fn hfn => ?_
  have e' := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «check_stack_terminal») rfl))
  subst e'
  set ps : List E := (fn% «check_stack_terminal»).params.map σ with hps
  set vs : List E := ps ++ [V.n 58].map σ with hvs
  have hlen : ps.length = 23 := by rw [hps, List.length_map]; rfl
  have a23 : argExp vs 23 = logG (σ (.n 58)) := by
    unfold argExp
    rw [hvs, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
    rfl
  have a6 : argExp vs 6 = argExp ps 6 := by
    unfold argExp
    rw [hvs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  refine ⟨fun q hq => by simp at hq, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, a23, a6] <;> omega

end
end LeanVM.Guest.Complete
