/-
  LeanVM.Guest.B1.VerifySub.PhOodRingCt

  `verify_sub`'s `c_table`: the ring map's Frobenius coefficients, `ringCoefficients f g`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Flat

/-!
# The map's Frobenius coefficients

`vsCtT` (statements `3016 .. 3591`, checked by the kernel): for each `b < 8`, from `power = g_b`,
for each `p < 8` the store `c_table[8p + b] = f_p · power`, then (but after the last) eight
squarings of `power`. The challenges are at `ctCh` (`ch[0] .. ch[15]`, `f` then `g`); block `b`'s
values run from `3041 + 64 b`, nine a step (`ctB`, `ctPw`). `ct_reads`: the table holds
`ringCoefficients f g` (`ringCoefficients_getElem?`: entry `8p + b` is `f_p · g_b^(2^(8p))`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `ringCoefficients` -/

/-- `ringCoefficients`' step. -/
def ringCoeffStep (acc : List E × List E) (fP : E) : List E × List E :=
  (acc.1 ++ acc.2.map (fP * ·), acc.2.map (frobenius8 · 1))

theorem ringCoefficients_eq (f g : List E) : ringCoefficients f g = (f.foldl ringCoeffStep ([], g)).1 := rfl

theorem rc_foldl : ∀ (f a gs : List E), (f.foldl ringCoeffStep (a, gs)).1 = a ++ (f.foldl ringCoeffStep ([], gs)).1
  | [], a, _ => by simp
  | x :: f, a, gs => by
    simp only [List.foldl_cons, ringCoeffStep, List.nil_append]
    rw [rc_foldl f, rc_foldl f (gs.map (x * ·)), List.append_assoc]

theorem frobenius8_one (v : E) (p : ℕ) : (frobenius8 v 1) ^ 2 ^ (8 * p) = v ^ 2 ^ (8 * (p + 1)) := by
  rw [frobenius8, ringMapWidth, ← pow_mul, ← pow_add]
  congr 2
  ring

/-- **Entry `8p + b`** of the coefficients is `f_p · g_b^(2^(8p))`. -/
theorem ringCoefficients_getElem? : ∀ (f gs : List E), gs.length = 8 → ∀ p < f.length, ∀ b < 8,
    (ringCoefficients f gs)[8 * p + b]? = some (f.getD p 0 * gs.getD b 0 ^ 2 ^ (8 * p))
  | [], _, _, p, hp, _, _ => absurd hp (by simp)
  | x :: f, gs, hl, p, hp, b, hb => by
    rw [ringCoefficients_eq, List.foldl_cons, rc_foldl]
    simp only [ringCoeffStep, List.nil_append]
    rcases p with _ | p
    · rw [List.getElem?_append_left (by simp [hl]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show b < gs.length by omega)]
    · rw [List.getElem?_append_right (by simp [hl]; omega)]
      have ih := ringCoefficients_getElem? f (gs.map (frobenius8 · 1)) (by simp [hl]) p
        (by simpa using hp) b hb
      rw [ringCoefficients_eq] at ih
      simp only [List.length_map, hl, show 8 * (p + 1) + b - 8 = 8 * p + b by omega] at ih ⊢
      rw [ih]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (show b < gs.length by omega), Option.map_some, Option.getD_some]
      rw [frobenius8_one]
      simp

theorem ringCoefficients_length : ∀ (f gs : List E), gs.length = 8 →
    (ringCoefficients f gs).length = 8 * f.length
  | [], _, _ => rfl
  | x :: f, gs, hl => by
    rw [ringCoefficients_eq, List.foldl_cons, rc_foldl]
    simp only [ringCoeffStep, List.nil_append, List.length_append, List.length_map, hl, List.length_cons]
    rw [← ringCoefficients_eq, ringCoefficients_length f _ (by simp [hl])]
    ring

/-! ## The table -/

/-- `ch[0] .. ch[15]`: the map's challenges, `f` then `g`. -/
def ctCh : List ℕ :=
  [2997, 2998, 2999, 3000, 3001, 3002, 3003, 3017, 3018, 3019, 3020, 3021, 3022, 3023, 3024, 3038]

/-- Block `b`'s first value. -/
def ctB (b : ℕ) : ℕ := 3041 + 64 * b

/-- `power` before step `p` of block `b`. -/
def ctPw (b p : ℕ) : ℕ := if p = 0 then ctCh.getD (8 + b) 0 else ctB b + 9 * (p - 1) + 8

/-- Step `p` of block `b`: the store, then (but after the last) the eight squarings. -/
def ctStep (b p : ℕ) : List Stmt :=
  [.atom (.mul (.n (ctB b + 9 * p)) (.n (ctCh.getD p 0)) (.n (ctPw b p))),
    .atom (.load (.n (ctB b + 9 * p)) (.n 3040) (8 * p + b))] ++
  (if p < 7 then (List.range 8).map fun t ↦
    .atom (.mul (.n (ctB b + 9 * p + t + 1)) (.n (if t = 0 then ctPw b p else ctB b + 9 * p + t))
      (.n (if t = 0 then ctPw b p else ctB b + 9 * p + t))) else [])

/-- `verify_sub`'s statements 3016 to 3591. -/
def vsCtT : List Stmt := ((List.range 8).map fun b ↦ ((List.range 8).map (ctStep b)).flatten).flatten

theorem vsCtT_eq : (vsPre.drop 3016).take 576 = vsCtT := stmtsEqb_sound (by decide +kernel)

theorem mem_vsCtT {b p : ℕ} (hb : b < 8) (hp : p < 8) {s : Stmt} (hs : s ∈ ctStep b p) : s ∈ vsCtT :=
  List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩,
    List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩, hs⟩⟩

section Table

variable {rd : Reader} {σ : Val} (hA : ∀ x, Stmt.atom x ∈ vsCtT → x.Holds rd σ)
include hA

theorem ct_square {b p t : ℕ} (hb : b < 8) (hp : p < 7) (ht : t < 8) :
    σ (.n (ctB b + 9 * p + t + 1)) = σ (.n (if t = 0 then ctPw b p else ctB b + 9 * p + t)) ^ 2 := by
  have h := hA _ (mem_vsCtT (p := p) hb (by omega) (List.mem_append_right _ (by
    rw [ite_eq_left hp]; exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)))
  simp only [Atom.Holds] at h
  rw [h, sq]

/-- **`power` before step `p`** is `g_b^(2^(8p))`. -/
theorem ct_power {b : ℕ} (hb : b < 8) : ∀ p < 8,
    σ (.n (ctPw b p)) = σ (.n (ctCh.getD (8 + b) 0)) ^ 2 ^ (8 * p)
  | 0, _ => by simp [ctPw]
  | p + 1, hp => by
    have ih := ct_power hb p (by omega)
    have chain : ∀ t < 8, σ (.n (ctB b + 9 * p + t + 1)) =
        σ (.n (ctCh.getD (8 + b) 0)) ^ 2 ^ (8 * p + t + 1) := by
      intro t ht
      induction t with
      | zero =>
        rw [ct_square hA hb (by omega) ht]
        simp only [↓reduceIte]
        rw [ih, ← pow_mul, ← pow_succ]
      | succ t iht =>
        rw [ct_square hA hb (by omega) ht]
        simp only [Nat.add_one_ne_zero, ↓reduceIte]
        rw [show ctB b + 9 * p + (t + 1) = ctB b + 9 * p + t + 1 by omega, iht (by omega), ← pow_mul,
          ← pow_succ, show 8 * p + t + 1 + 1 = 8 * p + (t + 1) + 1 by ring]
    rw [show ctPw b (p + 1) = ctB b + 9 * p + 7 + 1 by unfold ctPw; split <;> omega, chain 7 (by omega),
      show 8 * p + 7 + 1 = 8 * (p + 1) by ring]

/-- **Store `8p + b`** is `f_p · g_b^(2^(8p))`. -/
theorem ct_store {b p : ℕ} (hb : b < 8) (hp : p < 8) :
    LoadHolds rd (σ (.n 3040)) (8 * p + b)
      (σ (.n (ctCh.getD p 0)) * σ (.n (ctCh.getD (8 + b) 0)) ^ 2 ^ (8 * p)) := by
  have hm := hA _ (mem_vsCtT hb hp (List.mem_append_left _ (List.mem_cons_self ..)))
  have hl := hA _ (mem_vsCtT hb hp (List.mem_append_left _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  simp only [Atom.Holds] at hm hl
  rw [hm, ct_power hA hb p hp] at hl
  exact hl

/-- **The table holds the coefficients** of `f = ch[0 .. 7]`, `g = ch[8 .. 15]`. -/
theorem ct_reads : ReadsAt rd (σ (.n 3040))
    (ringCoefficients ((List.range 8).map fun i ↦ σ (.n (ctCh.getD i 0)))
      ((List.range 8).map fun i ↦ σ (.n (ctCh.getD (8 + i) 0)))) := by
  intro k hk
  rw [ringCoefficients_length _ _ (by simp)] at hk
  simp only [List.length_map, List.length_range] at hk
  have e := ringCoefficients_getElem? ((List.range 8).map fun i ↦ σ (.n (ctCh.getD i 0)))
    ((List.range 8).map fun i ↦ σ (.n (ctCh.getD (8 + i) 0))) (by simp) (k / 8) (by simp; omega)
    (k % 8) (by omega)
  rw [show 8 * (k / 8) + k % 8 = k by omega, List.getElem?_eq_getElem (by
    rw [ringCoefficients_length _ _ (by simp)]; simp; omega)] at e
  rw [Option.some_inj.mp e]
  have hs := ct_store hA (b := k % 8) (p := k / 8) (by omega) (by omega)
  rw [show 8 * (k / 8) + k % 8 = k by omega] at hs
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show k / 8 < 8 by omega),
    List.getElem?_range (show k % 8 < 8 by omega), Option.map_some, Option.getD_some]
  exact hs

end Table

end
end LeanVM.Guest.B1.VerifySub
