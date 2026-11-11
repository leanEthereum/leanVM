/-
  LeanVM.Guest.B1.Eq.RsLoop

  B1 for `__loop5`, the chunked loop of `rs_eq_run`, and `mul_range` loops whose body calls.
-/

module

public import LeanVM.Guest.B1.Eq.RsRows

/-!
# `__loop5` (`rs_eq_run`'s `mul_range` loop, lean_ethereum.py:1071-1073 at leanVM `40f877dc`)

At `xq = g^t` the body calls `rs_eq_rows__L8` on the row `chain·g^(64 t)` and the coordinates
from `z·g^(8 t)`, `p·g^(8 t)` (`L5Body`), then continues at `xq·g` (`loop5_sound`,
`loop5_complete`).

A loop whose body calls a function is not `loop_iff`'s (its body's meaning would depend on the
depth); `loop_rel_iff` takes the body's meaning at the program's relation, a step of the loop
at depth `d + 1` giving it through the callee's relation at depth `d`, and the converse from the
relation itself (`rel_iff`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Loops whose body calls -/

/-- **A `mul_range` loop whose body calls**: as `loop_iff`, the step given at depth `d + 1` one
way (`hsound`) and at the program's relation the other (`hcomp`). -/
theorem loop_rel_iff {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hsound : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] →
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (hcomp : ∀ x, B x → IsInK (x * gen + N) → (x * gen + N ≠ 0 → P.Rel rd f (x * gen :: ps) []) →
      P.Rel rd f (x :: ps) [])
    (k : ℕ) :
    P.Rel rd f (gen ^ k :: ps) [] ↔
      ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
        ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  constructor
  · rintro ⟨d, hd⟩
    induction d generalizing k with
    | zero => exact hd.elim
    | succ d ih =>
      obtain ⟨hB, -, hnext⟩ := hsound d _ hd
      by_cases h0 : gen ^ k * gen + N = 0
      · refine ⟨k + 1, by omega, (gen_pow_add_eq_zero_iff k).mp h0, fun j h1 h2 => by omega,
          fun j h1 h2 => ?_⟩
        rwa [show j = k by omega]
      · have := hnext h0
        rw [gen_pow_mul_gen] at this
        obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
        refine ⟨m, by omega, hN, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
        · rcases Nat.lt_or_ge (k + 1) j with h | h
          · exact hfirst j h h2
          · rw [show j = k + 1 by omega]
            intro he
            exact h0 ((gen_pow_add_eq_zero_iff k).mpr he.symm)
        · rcases Nat.lt_or_ge k j with h | h
          · exact hall j (by omega) h2
          · rwa [show j = k by omega]
  · rintro ⟨m, hkm, hN, hfirst, hall⟩
    obtain ⟨t, rfl⟩ : ∃ t, m = k + 1 + t := ⟨m - k - 1, by omega⟩
    have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
      rw [hN]
      exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
    induction t generalizing k with
    | zero =>
      exact hcomp _ (hall k le_rfl (by omega)) (hK k)
        (fun h => absurd ((gen_pow_add_eq_zero_iff k).mpr hN) h)
    | succ t ih =>
      refine hcomp _ (hall k le_rfl (by omega)) (hK k) (fun _ => ?_)
      rw [gen_pow_mul_gen]
      exact ih (k + 1) (by omega) (by rw [hN]; congr 1; omega)
        (fun j h1 h2 => hfirst j (by omega) (by omega)) (fun j h1 h2 => hall j (by omega) (by omega))

/-- **A guarded `mul_range` loop whose body calls** (`guarded_loop_iff`'s form). -/
theorem guarded_loop_rel_iff {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hsound : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] →
      B x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (hcomp : ∀ x, B x → IsInK (x * gen + N) → (x * gen + N ≠ 0 → P.Rel rd f (x * gen :: ps) []) →
      P.Rel rd f (x :: ps) []) :
    (IsInK (1 + N) ∧ (1 + N ≠ 0 → P.Rel rd f (1 :: ps) [])) ↔
      ∃ m < ordG, N = gen ^ m ∧ ∀ j < m, B (gen ^ j) := by
  have hl := loop_rel_iff hsound hcomp 0
  rw [pow_zero] at hl
  constructor
  · rintro ⟨hK, hrun⟩
    by_cases h1 : 1 + N = 0
    · refine ⟨0, by decide, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      rw [pow_zero]; exact (e_add_eq_zero_iff.mp h1).symm
    · obtain ⟨m, hm, hN, hfirst, hall⟩ := hl.mp (hrun h1)
      refine ⟨m, ?_, hN, fun j hj => hall j (Nat.zero_le j) hj⟩
      by_contra hge
      rcases Nat.lt_or_ge ordG m with hgt | hle
      · have : gen ^ (m - ordG) = N := by
          obtain ⟨t, rfl⟩ : ∃ t, m = ordG + t := ⟨m - ordG, by omega⟩
          rw [hN, pow_add, gen_pow_ordG, one_mul, Nat.add_sub_cancel_left]
        exact hfirst (m - ordG) (Nat.sub_pos_of_lt hgt) (Nat.sub_lt (by omega) ordG_pos) this
      · have hm' : m = ordG := by omega
        rw [hm', gen_pow_ordG] at hN
        exact h1 (by rw [hN]; exact e_add_self 1)
  · rintro ⟨m, hm, hN, hall⟩
    refine ⟨?_, fun h1 => ?_⟩
    · rw [hN]
      exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK m)
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (show 1 + N = 0 by rw [hN, h, pow_zero]; exact e_add_self 1) h1
      · exact h
    exact hl.mpr ⟨m, hm0, hN, first_hit_of_lt hm hN, fun j _ hj => hall j hj⟩

/-! ## `__loop5` -/

/-- The expansion of `__loop5`. -/
def l5Body : List Stmt :=
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 5) (.n 5)),
    .atom (.mul (.n 7) (.n 6) (.n 6)), .atom (.mul (.n 8) (.n 0) (.n 0)),
    .atom (.mul (.n 9) (.n 8) (.n 8)), .atom (.mul (.n 10) (.n 9) (.n 9)),
    .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.mul (.n 12) (.n 11) (.n 11)),
    .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 2) (.n 13)),
    .atom (.mul (.n 15) (.n 3) (.n 7)), .atom (.mul (.n 16) (.n 4) (.n 7)),
    .call "rs_eq_rows__L8" [.n 14, .n 15, .n 16] [.n 17],
    .atom (.const (.n 18) (word 2 0)), .atom (.mul (.n 19) (.n 0) (.n 18)),
    .atom (.add (.n 20) (.n 19) (.n 1)), .atom (.const (.n 21) (word 2 0)),
    .atom (.mul (.n 22) (.n 0) (.n 21)), .callIf (.n 20) "__loop5" [.n 22, .n 1, .n 2, .n 3, .n 4],
    .ret []]

theorem core80_body : Fn.body Data.core80 = l5Body := stmtsEqb_sound (by decide +kernel)

theorem find_loop5 : coreProgram.find? "__loop5" = some Data.core80 :=
  Program.find?_of_indexOf? (j := 80) (by decide +kernel) rfl

/-- The loop's body at `x`: one row from `chain·x^64`, the coordinates from `z·x^8`, `p·x^8`. -/
def L5Body (rd : Reader) (chain z p x : E) : Prop :=
  ∃ r, coreProgram.Rel rd "rs_eq_rows__L8" [chain * x ^ 64, z * x ^ 8, p * x ^ 8] [r]

theorem pow8_eq (x : E) : (x * x) * (x * x) * ((x * x) * (x * x)) = x ^ 8 := by ring

theorem pow64_eq (x : E) :
    let a := x * x; let b := a * a; let c := b * b; let d := c * c; let e := d * d; e * e = x ^ 64 := by
  simp only; ring

/-- **`__loop5`, one step**, at depth `d + 1`. -/
theorem loop5_sound (rd : Reader) (N chain z p : E) (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) "__loop5" (x :: [N, chain, z, p]) []) :
    L5Body rd chain z p x ∧ IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop5" (x * gen :: [N, chain, z, p]) []) := by
  rw [relN_succ_iff find_loop5, show Fn.params Data.core80 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
    core80_body, l5Body] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨σ, hp, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hc, h18, h19, h20, h21,
    h22, hK, hcall, -⟩ := h
  simp only [List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hp
  have e7 : σ (.n 7) = σ (.n 0) ^ 8 := by rw [h7, h6, h5, pow8_eq]
  have e13 : σ (.n 13) = σ (.n 0) ^ 64 := by
    rw [h13, h12, h11, h10, h9, h8]; exact pow64_eq _
  refine ⟨⟨σ (.n 17), ?_⟩, by rwa [h20, h19, h18] at hK, fun hne => ?_⟩
  · rw [← e7, ← e13, ← h14, ← h15, ← h16]
    exact relN_le_rel _ d _ _ _ hc
  · have := hcall (by rwa [h20, h19, h18])
    rwa [h22, h21] at this

/-- **`__loop5`, one step back**: the body and the next step give the loop at `x`. -/
theorem loop5_complete (rd : Reader) (N chain z p : E) (x : E) (hB : L5Body rd chain z p x)
    (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → coreProgram.Rel rd "__loop5" (x * gen :: [N, chain, z, p]) []) :
    coreProgram.Rel rd "__loop5" (x :: [N, chain, z, p]) [] := by
  obtain ⟨r, hr⟩ := hB
  rw [rel_iff_sem find_loop5, show Fn.params Data.core80 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
    core80_body, l5Body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
  let w : List E := [x, N, chain, z, p, x * x, (x * x) * (x * x), (x * x) * (x * x) * ((x * x) * (x * x)),
    x * x, (x * x) * (x * x), ((x * x) * (x * x)) * ((x * x) * (x * x)),
    (((x * x) * (x * x)) * ((x * x) * (x * x))) * (((x * x) * (x * x)) * ((x * x) * (x * x))),
    x ^ 32, x ^ 64, chain * x ^ 64, z * x ^ 8, p * x ^ 8, r, gen, x * gen, x * gen + N, gen,
    x * gen]
  refine ⟨Val.ofArgs w, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, ?_, ?_, ?_, rfl, rfl,
    rfl, rfl, rfl, ?_, ?_, trivial⟩
  all_goals simp only [ofArgs_n, w, List.getD_cons_succ, List.getD_cons_zero]
  · ring
  · ring
  · rw [pow8_eq]
  · rw [pow8_eq]
  · exact hr
  · exact hK
  · exact hnext

end
end LeanVM.Guest.B1
