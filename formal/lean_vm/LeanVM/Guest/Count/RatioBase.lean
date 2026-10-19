/-
  LeanVM.Guest.Count.RatioBase

  A set of guest functions given by core indices, closed under calls, within ratios of
  instructions per word: the counts of its valid trees within those ratios of their words.
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Memory.WeightRatio
public import LeanVM.Guest.Memory.GuestCntPm

/-!
# Counts within a ratio of the words, by index

`krIn J` is the set of the core functions of indices `J`. `krClosedAt J C i` checks that the calls
of function `i` are the functions of indices `C i`, all in `J`; `krRatioAt A i` that function `i`
has at most `A op / 1000` of `op`'s instructions (`B2C.pathMax`) per frame word (`B2C.fs`), read
from the compiled data by index. Both are decided over `J`, by index, comparing no names but the
calls'. `kr_weight`: then every valid tree of a function of `J` counts at most `A op / 1000` of
`op`'s instructions per word it allocates.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

@[expose] public section

/-- The core functions of indices `J`. -/
def krIn (J : List ℕ) (g : String) : Prop := ∃ i ∈ J, (coreProgram[i]?).map Fn.name = some g

/-- The name of core function `k`. -/
noncomputable def krName (k : ℕ) : String := ((coreProgram[k]?).map Fn.name).getD ""

/-- Function `i` calls the functions of indices `C i`, all in `J`. -/
noncomputable def krClosedAt (J : List ℕ) (C : ℕ → List ℕ) (i : ℕ) : Bool :=
  (Stmt.blockCallees ((coreProgram[i]?).getD default).body == (C i).map krName) &&
    (C i).all fun k => decide (k ∈ J) && Nat.blt k 1043

/-- Function `i` within the ratios `A op / 1000`. -/
noncomputable def krRatioAt (A : Opcode → ℕ) (i : ℕ) : Bool :=
  [Opcode.xor, .mulNative, .setConstant, .deref, .jump, .blake2s].all fun op =>
    Nat.ble (1000 * (plumbOf (i + 1)).pmax.getD (opIdx op) 0) (A op * fsN (i + 1))

theorem kr_all_append {p : ℕ → Bool} {l1 l2 : List ℕ} (h1 : l1.all p = true) (h2 : l2.all p = true) :
    (l1 ++ l2).all p = true := by
  rw [List.all_append, h1, h2]; rfl

theorem kr_idxOf {i : ℕ} (hi : i < coreProgram.length) : idxOf coreProgram[i].name = some (i + 1) := by
  unfold idxOf
  rw [coreProgram_indexOf?_getElem hi]
  rfl

theorem kr_of_in {J : List ℕ} {g : String} (h : krIn J g) :
    ∃ i ∈ J, ∃ hi : i < coreProgram.length, coreProgram[i].name = g := by
  obtain ⟨i, hJ, h⟩ := h
  rcases hc : coreProgram[i]? with _ | fn
  · rw [hc] at h; exact absurd h (by simp)
  · rw [hc] at h
    obtain ⟨hlt, hfn⟩ := List.getElem?_eq_some_iff.mp hc
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨i, hJ, hlt, by rw [hfn, h]⟩

/-- **The functions of `J` call only functions of `J`.** -/
theorem kr_callsIn {J : List ℕ} {C : ℕ → List ℕ} (h : J.all (krClosedAt J C) = true) :
    CallsIn coreProgram (krIn J) := by
  refine callsIn_of_callees fun f hs fn hf g hg => ?_
  obtain ⟨i, hJ, hi, rfl⟩ := kr_of_in hs
  rw [coreProgram_find_getElem hi, Option.some.injEq] at hf
  subst hf
  have hc := List.all_eq_true.mp h i hJ
  simp only [krClosedAt, Bool.and_eq_true, beq_iff_eq, List.getElem?_eq_getElem hi, Option.getD_some] at hc
  rw [hc.1] at hg
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hg
  have hk' := List.all_eq_true.mp hc.2 k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at hk'
  have hkl : k < coreProgram.length := by rw [coreProgram_length]; exact hk'.2
  refine ⟨k, hk'.1, ?_⟩
  simp [krName, List.getElem?_eq_getElem hkl]

/-- **Every function of `J` within the ratios.** -/
theorem kr_ratio {J : List ℕ} {A : Opcode → ℕ} (h : J.all (krRatioAt A) = true) (op : Opcode) :
    ∀ g, krIn J g → 1000 * pathMax g op ≤ A op * fs g := by
  intro g hg
  obtain ⟨i, hJ, hi, rfl⟩ := kr_of_in hg
  have hx := kr_idxOf hi
  obtain ⟨_, _, _, _, _, _, hfs, _⟩ := fn_of_idx hx
  have hr := List.all_eq_true.mp (List.all_eq_true.mp h i hJ) op (by cases op <;> simp)
  rw [hfs]
  unfold pathMax
  simp only [hx]
  exact Nat.le_of_ble_eq_true hr

/-- **Off `verify_lean_xmss`, the frame weights are the path maxima.** -/
theorem kr_ratio_om {J : List ℕ} {A : Opcode → ℕ} (h : J.all (krRatioAt A) = true) (h16 : 16 ∉ J)
    (op : Opcode) : ∀ g, krIn J g → 1000 * kcOm op g ≤ A op * fs g := by
  intro g hg
  obtain ⟨i, hJ, hi, rfl⟩ := kr_of_in hg
  have hne : ¬ coreProgram[i].name = "verify_lean_xmss" := fun e => h16 ((kc_name_xmss hi).mp e ▸ hJ)
  have := kr_ratio h op coreProgram[i].name ⟨i, hJ, by simp [List.getElem?_eq_getElem hi]⟩
  unfold kcOm
  simp only [hne, ↓reduceIte, Nat.add_zero]
  exact this

/-- **A valid tree of a function of `J` within the ratios of its words.** -/
theorem kr_weight {J : List ℕ} {C : ℕ → List ℕ} {A : Opcode → ℕ} (hc : J.all (krClosedAt J C) = true)
    (hr : J.all (krRatioAt A) = true) (h16 : 16 ∉ J) {f : String} (hf : krIn J f) (op : Opcode)
    {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) :
    1000 * t.weight (kcOm op) ≤ A op * t.total fs :=
  weight_le_ratio (S := krIn J) (kr_callsIn hc) (kr_ratio_om hr h16 op) t (hn ▸ hf) hv

end
end LeanVM.Guest.Count
