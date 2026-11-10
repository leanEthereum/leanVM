/-
  LeanVM.Guest.B1.Selectors.Nibble

  The inline nibble gadgets `sel_eq_nibble` and `sel_g_nibble` as templates over their first
  values and pointers, and what they store.
-/

module

public import LeanVM.Guest.B1.Selectors.SelectorTables

/-!
# `sel_eq_nibble`, `sel_g_nibble` (TRIAGE G #45, #46)

Both are `@inline` (G:1951-1987): their atoms sit in their callers (`sel_partial_nibble`,
`shared_selector_tables`'s loop), numbered from a first value.

* `nbEq B pz pz1 peq w` (`sel_eq_nibble(out, z, z1, w)`): level `0` (`z1[0]`, `z[0]`) at values
  `B`, `B + 1`; level `t ≥ 1` its coordinate and complement at `nbM B t - 2`, `nbM B t - 1`, then
  entry `i` times the complement at `nbM B t + 2i` and times the coordinate at `nbM B t + 2i + 1`;
  then the levels stored at `out[0 ..]`. `holds_nbEq`: it stores `eqLevels` of the coordinates it
  reads.
* `nbG c pgs pgo w` (`sel_g_nibble(out, gs, w)`): `1` at `c`, `gs[0]` at `c + 1`, then for
  `t ≥ 1` `gs[t]` and the products `vals[2^t + i] = vals[i]·gs[t]`; then the table stored at
  `out[0 ..]`. `holds_nbG`: it stores `gTable` of the shares it reads.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The eq levels -/

/-- Level `t ≥ 1`'s first product, past its two loads. -/
def nbM (B t : ℕ) : ℕ := B + [0, 4, 10, 20].getD t 0

/-- The value of level `t`'s entry `i`. -/
def nbLv (B t i : ℕ) : ℕ :=
  if t = 0 then B + i
  else if i < 2 ^ t then nbM B t + 2 * i else nbM B t + 2 * (i - 2 ^ t) + 1

/-- Level `t ≥ 1`: the coordinate and its complement, then the products. -/
def nbLevel (B : ℕ) (pz pz1 : V) (t : ℕ) : List Stmt :=
  [.atom (.load (.n (nbM B t - 2)) pz t), .atom (.load (.n (nbM B t - 1)) pz1 t)] ++
  ((List.range (2 ^ t)).map fun i ↦
    [.atom (.mul (.n (nbM B t + 2 * i)) (.n (nbLv B (t - 1) i)) (.n (nbM B t - 1))),
      .atom (.mul (.n (nbM B t + 2 * i + 1)) (.n (nbLv B (t - 1) i)) (.n (nbM B t - 2)))]).flatten

/-- The value of the eq levels' entry `e`, level by level. -/
def nbEqV (B e : ℕ) : ℕ :=
  if e < 2 then nbLv B 0 e else if e < 6 then nbLv B 1 (e - 2) else if e < 14 then nbLv B 2 (e - 6)
  else nbLv B 3 (e - 14)

/-- `sel_eq_nibble(out, z, z1, w)` from value `B`, `1 ≤ w ≤ 4`. -/
def nbEq (B : ℕ) (pz pz1 peq : V) (w : ℕ) : List Stmt :=
  [.atom (.load (.n B) pz1 0), .atom (.load (.n (B + 1)) pz 0)] ++
    ((List.range (w - 1)).map fun t ↦ nbLevel B pz pz1 (t + 1)).flatten ++
    (List.range (2 ^ (w + 1) - 2)).map (fun e ↦ .atom (.load (.n (nbEqV B e)) peq e))

/-! ## The `g` table -/

/-- The `g` value of entry `u`. -/
def nbGV (c u : ℕ) : ℕ := if u = 0 then c else if u = 1 then c + 1 else c + u + Nat.log2 u

/-- The `g` table's step `t ≥ 1`: the share, then the products. -/
def nbGStep (c : ℕ) (pgs : V) (t : ℕ) : List Stmt :=
  .atom (.load (.n (c + 2 ^ t + t - 1)) pgs t) ::
    (List.range (2 ^ t)).map fun i ↦
      .atom (.mul (.n (c + 2 ^ t + t + i)) (.n (nbGV c i)) (.n (c + 2 ^ t + t - 1)))

/-- `sel_g_nibble(out, gs, w)` from value `c`, `1 ≤ w`. -/
def nbG (c : ℕ) (pgs pgo : V) (w : ℕ) : List Stmt :=
  [.atom (.const (.n c) (word 1 0)), .atom (.load (.n (c + 1)) pgs 0)] ++
    ((List.range (w - 1)).map fun t ↦ nbGStep c pgs (t + 1)).flatten ++
    (List.range (2 ^ w)).map (fun u ↦ .atom (.load (.n (nbGV c u)) pgo u))

theorem nbLevel_noRet (B : ℕ) (pz pz1 : V) (t : ℕ) : Stmt.noRetList (nbLevel B pz pz1 t) = true := by
  rw [nbLevel, tb_noRetList_append, tb_noRetList_flatten_range _ _ (fun _ => rfl)]; rfl

theorem nbGStep_noRet (c : ℕ) (pgs : V) (t : ℕ) : Stmt.noRetList (nbGStep c pgs t) = true := by
  rw [nbGStep, Stmt.noRetList, tb_noRetList_mapAtoms]; rfl

theorem nbEq_noRet (B : ℕ) (pz pz1 peq : V) (w : ℕ) : Stmt.noRetList (nbEq B pz pz1 peq w) = true := by
  simp only [nbEq, tb_noRetList_append, tb_noRetList_flatten_range _ _ (fun _ => nbLevel_noRet _ _ _ _),
    tb_noRetList_mapAtoms]
  rfl

theorem nbG_noRet (c : ℕ) (pgs pgo : V) (w : ℕ) : Stmt.noRetList (nbG c pgs pgo w) = true := by
  simp only [nbG, tb_noRetList_append, tb_noRetList_flatten_range _ _ (fun _ => nbGStep_noRet _ _ _),
    tb_noRetList_mapAtoms]
  rfl

/-! ## The semantics -/

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem holds_nbLevel {B : ℕ} {pz pz1 : V} {t : ℕ}
    (h : Stmt.HoldsList C rd σ (nbLevel B pz pz1 t) True kret) :
    LoadHolds rd (σ pz) t (σ (.n (nbM B t - 2))) ∧ LoadHolds rd (σ pz1) t (σ (.n (nbM B t - 1))) ∧
    ∀ i < 2 ^ t, σ (.n (nbM B t + 2 * i)) = σ (.n (nbLv B (t - 1) i)) * σ (.n (nbM B t - 1)) ∧
      σ (.n (nbM B t + 2 * i + 1)) = σ (.n (nbLv B (t - 1) i)) * σ (.n (nbM B t - 2)) := by
  rw [nbLevel, tb_holdsList_append_noRet rfl, tb_holdsList_flatten_range _ _ (fun _ => rfl)] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
  refine ⟨h1.1, h1.2, fun i hi => ?_⟩
  have := h2 i hi
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
  exact this

theorem holds_nbGStep {c : ℕ} {pgs : V} {t : ℕ}
    (h : Stmt.HoldsList C rd σ (nbGStep c pgs t) True kret) :
    LoadHolds rd (σ pgs) t (σ (.n (c + 2 ^ t + t - 1))) ∧
    ∀ i < 2 ^ t, σ (.n (c + 2 ^ t + t + i)) = σ (.n (nbGV c i)) * σ (.n (c + 2 ^ t + t - 1)) := by
  rw [nbGStep, show ∀ (a : Stmt) (l : List Stmt), a :: l = [a] ++ l from fun _ _ => rfl,
    tb_holdsList_append_noRet rfl, tb_holdsList_mapAtoms] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
  exact ⟨h1, h2⟩

/-- The value loaded as coordinate `t`, and its complement. -/
def nbZ (B t : ℕ) : ℕ := if t = 0 then B + 1 else nbM B t - 2
def nbZ1 (B t : ℕ) : ℕ := if t = 0 then B else nbM B t - 1

theorem nbLevels {B : ℕ} {pz pz1 : V} {w : ℕ}
    (hL : ∀ t < w - 1, Stmt.HoldsList C rd σ (nbLevel B pz pz1 (t + 1)) True kret) :
    ∀ t < w, ∀ i < 2 ^ (t + 1), σ (.n (nbLv B t i)) = ∏ s ∈ Finset.range (t + 1),
      bitPick i s (σ (.n (nbZ B s))) (σ (.n (nbZ1 B s))) := by
  intro t ht
  induction t with
  | zero =>
    intro i hi
    rw [Finset.prod_range_one]
    interval_cases i
    · simp [nbLv, bitPick, nbZ1]
    · simp [nbLv, bitPick, nbZ]
  | succ t ih =>
    intro i hi
    obtain ⟨-, -, hm⟩ := holds_nbLevel (hL t (by omega))
    rw [Finset.prod_range_succ]
    by_cases hlo : i < 2 ^ (t + 1)
    · obtain ⟨h1, -⟩ := hm i hlo
      have hv : nbLv B (t + 1) i = nbM B (t + 1) + 2 * i := by
        simp only [nbLv, Nat.succ_ne_zero, ↓reduceIte, hlo]
      rw [hv, h1, Nat.add_sub_cancel, ih (by omega) i hlo, bitPick, testBit_lt_two_pow hlo]
      simp [nbZ1]
    · obtain ⟨v, rfl⟩ : ∃ v, i = 2 ^ (t + 1) + v := ⟨i - 2 ^ (t + 1), by omega⟩
      have hv' : v < 2 ^ (t + 1) := by rw [pow_succ 2 (t + 1)] at hi; omega
      obtain ⟨-, h2⟩ := hm v hv'
      have hv : nbLv B (t + 1) (2 ^ (t + 1) + v) = nbM B (t + 1) + 2 * v + 1 := by
        simp only [nbLv, Nat.succ_ne_zero, ↓reduceIte, hlo, Nat.add_sub_cancel_left]
      rw [hv, h2, Nat.add_sub_cancel, ih (by omega) v hv', bitPick,
        testBit_two_pow_add_self hv']
      simp only [↓reduceIte, nbZ, Nat.succ_ne_zero]
      exact congrArg (· * _) (Finset.prod_congr rfl fun s hs => by
        simp only [bitPick, testBit_two_pow_add hv' (Finset.mem_range.mp hs)])

theorem nb_log2_two_pow_add {t v : ℕ} (hv : v < 2 ^ t) : Nat.log2 (2 ^ t + v) = t :=
  (Nat.log2_eq_iff (by positivity)).mpr ⟨by omega, by rw [pow_succ]; omega⟩

/-- The value loaded as share `t`. -/
def nbGL (c t : ℕ) : ℕ := if t = 0 then c + 1 else c + 2 ^ t + t - 1

theorem nbGs {c : ℕ} {pgs : V} {w : ℕ} (h1 : σ (.n c) = word 1 0)
    (hG : ∀ t < w - 1, Stmt.HoldsList C rd σ (nbGStep c pgs (t + 1)) True kret) :
    ∀ t < w, ∀ u < 2 ^ (t + 1), σ (.n (nbGV c u)) = ∏ s ∈ Finset.range (t + 1),
      bitPick u s (σ (.n (nbGL c s))) 1 := by
  intro t ht
  induction t with
  | zero =>
    intro u hu
    rw [Finset.prod_range_one]
    interval_cases u
    · simp [nbGV, bitPick, h1, tb_word_one]
    · simp [nbGV, bitPick, nbGL]
  | succ t ih =>
    intro u hu
    obtain ⟨-, hm⟩ := holds_nbGStep (hG t (by omega))
    rw [Finset.prod_range_succ]
    by_cases hlo : u < 2 ^ (t + 1)
    · rw [ih (by omega) u hlo, bitPick, testBit_lt_two_pow hlo]
      simp
    · obtain ⟨v, rfl⟩ : ∃ v, u = 2 ^ (t + 1) + v := ⟨u - 2 ^ (t + 1), by omega⟩
      have hv' : v < 2 ^ (t + 1) := by rw [pow_succ 2 (t + 1)] at hu; omega
      have hp1 : 2 ≤ 2 ^ (t + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hv : nbGV c (2 ^ (t + 1) + v) = c + 2 ^ (t + 1) + (t + 1) + v := by
        simp only [nbGV, show 2 ^ (t + 1) + v ≠ 0 by omega, show 2 ^ (t + 1) + v ≠ 1 by omega,
          ↓reduceIte, nb_log2_two_pow_add hv']
        omega
      rw [hv, hm v hv', ih (by omega) v hv', bitPick, testBit_two_pow_add_self hv']
      simp only [↓reduceIte, nbGL, Nat.succ_ne_zero]
      exact congrArg (· * _) (Finset.prod_congr rfl fun s hs => by
        simp only [bitPick, testBit_two_pow_add hv' (Finset.mem_range.mp hs)])

/-- **`sel_eq_nibble`**: for `1 ≤ w ≤ 4`, it reads `w` coordinates and their complements and stores
their eq levels. -/
theorem holds_nbEq {B : ℕ} {pz pz1 peq : V} {w : ℕ} (hw1 : 1 ≤ w) (hw4 : w ≤ 4)
    (h : Stmt.HoldsList C rd σ (nbEq B pz pz1 peq w) True kret) :
    ∃ zs zs1 : List E, zs.length = w ∧ zs1.length = w ∧ TbReadsAt rd (σ pz) zs ∧
      TbReadsAt rd (σ pz1) zs1 ∧ TbReadsAt rd (σ peq) (eqLevels zs zs1) := by
  have nL := tb_noRetList_flatten_range (w - 1) _ (fun t => nbLevel_noRet B pz pz1 (t + 1))
  have n0 : Stmt.noRetList [Stmt.atom (.load (.n B) pz1 0), Stmt.atom (.load (.n (B + 1)) pz 0)] =
    true := rfl
  rw [nbEq, tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nL, n0, Bool.and_self]),
    tb_holdsList_append_noRet n0, tb_holdsList_mapAtoms,
    tb_holdsList_flatten_range _ _ (fun t => nbLevel_noRet B pz pz1 (t + 1))] at h
  obtain ⟨⟨h0, hL⟩, hEq⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
  have hlev := nbLevels hL
  let zs := (List.range w).map fun t ↦ σ (.n (nbZ B t))
  let zs1 := (List.range w).map fun t ↦ σ (.n (nbZ1 B t))
  have ezs : ∀ t < w, zs.getD t 0 = σ (.n (nbZ B t)) := fun t ht => by
    simp [zs, List.getD_eq_getElem?_getD, ht]
  have ezs1 : ∀ t < w, zs1.getD t 0 = σ (.n (nbZ1 B t)) := fun t ht => by
    simp [zs1, List.getD_eq_getElem?_getD, ht]
  have hlz : zs.length = w := by simp [zs]
  have hlz1 : zs1.length = w := by simp [zs1]
  refine ⟨zs, zs1, hlz, hlz1, fun t ht => ?_, fun t ht => ?_, fun e he => ?_⟩
  · rw [hlz] at ht
    rw [← List.getD_eq_getElem _ 0 (by rw [hlz]; exact ht), ezs t ht]
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · exact h0.2
    · have := (holds_nbLevel (hL (t - 1) (by omega))).1
      rw [show t - 1 + 1 = t by omega] at this
      simpa [nbZ, show t ≠ 0 by omega] using this
  · rw [hlz1] at ht
    rw [← List.getD_eq_getElem _ 0 (by rw [hlz1]; exact ht), ezs1 t ht]
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · exact h0.1
    · have := (holds_nbLevel (hL (t - 1) (by omega))).2.1
      rw [show t - 1 + 1 = t by omega] at this
      simpa [nbZ1, show t ≠ 0 by omega] using this
  · have hlen := eqLevels_length hlz hlz1
    rw [hlen] at he
    have hval : σ (.n (nbEqV B e)) = (eqLevels zs zs1).getD e 0 := by
      obtain ⟨t, i, ht, hi, hei, hst⟩ : ∃ t i, t < w ∧ i < 2 ^ (t + 1) ∧
          e = 2 ^ (t + 1) - 2 + i ∧ nbEqV B e = nbLv B t i := by
        by_cases e2 : e < 2
        · exact ⟨0, e, by omega, by simpa using e2, by simp, by simp [nbEqV, e2]⟩
        have hw2 : 2 ≤ w := by
          by_contra hc
          have : w = 1 := by omega
          subst this; simp at he; omega
        by_cases e6 : e < 6
        · exact ⟨1, e - 2, by omega, by simp; omega, by simp; omega, by simp [nbEqV, e2, e6]⟩
        have hw3 : 3 ≤ w := by
          by_contra hc
          have : w = 2 := by omega
          subst this; simp at he; omega
        by_cases e14 : e < 14
        · exact ⟨2, e - 6, by omega, by simp; omega, by simp; omega,
            by simp [nbEqV, e2, e6, e14]⟩
        have hw4' : w = 4 := by
          by_contra hc
          have : w = 3 := by omega
          subst this; simp at he; omega
        subst hw4'
        exact ⟨3, e - 14, by omega, by simp; omega, by simp; omega,
          by simp [nbEqV, e2, e6, e14]⟩
      rw [hst, hlev t ht i hi, hei, eqLevels_getD (hlz.trans hlz1.symm) (by omega)
        (by omega) hi]
      refine Finset.prod_congr rfl fun s hs => ?_
      have hs' := Finset.mem_range.mp hs
      rw [ezs s (by omega), ezs1 s (by omega)]
    rw [← List.getD_eq_getElem _ 0 (by rw [hlen]; exact he), ← hval]
    exact hEq e he

/-- **`sel_g_nibble`**: for `1 ≤ w`, it reads `w` shares and stores their `g`-power table. -/
theorem holds_nbG {c : ℕ} {pgs pgo : V} {w : ℕ} (hw1 : 1 ≤ w)
    (h : Stmt.HoldsList C rd σ (nbG c pgs pgo w) True kret) :
    ∃ gl : List E, gl.length = w ∧ TbReadsAt rd (σ pgs) gl ∧ TbReadsAt rd (σ pgo) (gTable gl) := by
  have nG := tb_noRetList_flatten_range (w - 1) _ (fun t => nbGStep_noRet c pgs (t + 1))
  have n0 : Stmt.noRetList [Stmt.atom (.const (.n c) (word 1 0)),
    Stmt.atom (.load (.n (c + 1)) pgs 0)] = true := rfl
  rw [nbG, tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nG, n0, Bool.and_self]),
    tb_holdsList_append_noRet n0, tb_holdsList_mapAtoms,
    tb_holdsList_flatten_range _ _ (fun t => nbGStep_noRet c pgs (t + 1))] at h
  obtain ⟨⟨h0, hG⟩, hGs⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
  have hgs := nbGs h0.1 hG
  let gl := (List.range w).map fun t ↦ σ (.n (nbGL c t))
  have egl : ∀ t < w, gl.getD t 0 = σ (.n (nbGL c t)) := fun t ht => by
    simp [gl, List.getD_eq_getElem?_getD, ht]
  have hlg : gl.length = w := by simp [gl]
  refine ⟨gl, hlg, fun t ht => ?_, fun u hu => ?_⟩
  · rw [hlg] at ht
    rw [← List.getD_eq_getElem _ 0 (by rw [hlg]; exact ht), egl t ht]
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simpa [nbGL] using h0.2
    · have := (holds_nbGStep (hG (t - 1) (by omega))).1
      rw [show t - 1 + 1 = t by omega] at this
      simpa [nbGL, show t ≠ 0 by omega] using this
  · rw [gTable_length hlg] at hu
    rw [← List.getD_eq_getElem _ 0 (by rw [gTable_length hlg]; exact hu), gTable_getD hlg hu]
    have := hgs (w - 1) (by omega) u (by rw [show w - 1 + 1 = w by omega]; exact hu)
    rw [show w - 1 + 1 = w by omega] at this
    rw [Finset.prod_congr rfl fun s hs => by rw [egl s (Finset.mem_range.mp hs)], ← this]
    exact hGs u hu

end Sem

end
end LeanVM.Guest.B1.Tables
