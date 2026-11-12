/-
  LeanVM.Guest.B1.Ring.Weight

  B1 of `ring_switch_weight`: its core IR computes `ringWeight`.
-/

module

public import LeanVM.Guest.B1.Ring.Interface
public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Eq.RsEqRun

/-!
# `ring_switch_weight` (TRIAGE G #66)

`ring_switch_weight(z_vals, point1, c_table, qkeccakv_g)` (G:3298-3307, `Data.core14`) writes a
row of `64` ones (`rswInit`), calls `rs_eq_run` on it, whose last row holds `ringRow 1 r p k`
(`Π (r_n^(2^k) + p_n)`, B1-a's `MeaningRsEqRun`), and sums `c_table[k] · row[k]` (`rswTerm`).
With `p = 1 + r'` the factor is `1 + r_n^(2^k) + r'_n`, so the sum is
`ringWeight r r' c_table` (V:2109; `ringWeight_eq`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## `ringWeight` as a sum -/

/-- A left-to-right sum of `t 0, …, t (n - 1)`. -/
def gsum (t : ℕ → E) (n : ℕ) : E := (List.range n).foldl (fun s k ↦ s + t k) 0

theorem gsum_zero (t : ℕ → E) : gsum t 0 = 0 := rfl

theorem gsum_succ (t : ℕ → E) (n : ℕ) : gsum t (n + 1) = gsum t n + t n := by
  simp [gsum, List.range_succ, List.foldl_append]

theorem gsum_one (t : ℕ → E) : gsum t 1 = t 0 := by rw [gsum_succ, gsum_zero, zero_add]

theorem gsum_congr {t t' : ℕ → E} : ∀ {n : ℕ}, (∀ k < n, t k = t' k) → gsum t n = gsum t' n
  | 0, _ => rfl
  | n + 1, h => by
    rw [gsum_succ, gsum_succ, gsum_congr (fun k hk => h k (by omega)), h n (by omega)]

theorem gsum_cons (t : ℕ → E) : ∀ n, gsum t (n + 1) = t 0 + gsum (fun k ↦ t (k + 1)) n
  | 0 => by rw [gsum_succ, gsum_zero, gsum_zero, zero_add, add_zero]
  | n + 1 => by rw [gsum_succ, gsum_cons t n, gsum_succ, add_assoc]

/-- One product of `ringWeight` (V:2109): `c · Π (1 + v_n + r'_n)`. -/
def rwProd (vs rP : List E) (c : E) : E :=
  (List.zip vs rP).foldl (fun product (value, challenge) ↦ product * (1 + value + challenge)) c

theorem ringWeight_fold (r rP : List E) :
    ∀ (cs : List E) (s : E) (j : ℕ),
      (cs.foldl (fun (acc : E × List E) c ↦
          (acc.1 + rwProd acc.2 rP c, acc.2.map fun value ↦ value * value))
        (s, r.map (· ^ 2 ^ j))) =
        (s + gsum (fun k ↦ rwProd (r.map (· ^ 2 ^ (j + k))) rP (cs.getD k 0)) cs.length,
          r.map (· ^ 2 ^ (j + cs.length)))
  | [], s, j => by simp [gsum_zero]
  | c :: cs, s, j => by
    have hr : (r.map (· ^ 2 ^ j)).map (fun value ↦ value * value) = r.map (· ^ 2 ^ (j + 1)) := by
      rw [List.map_map]; congr 1; funext x
      simp only [Function.comp_apply]
      rw [← pow_two, ← pow_mul, ← pow_succ]
    rw [List.foldl_cons, hr, ringWeight_fold r rP cs _ (j + 1), List.length_cons, gsum_cons]
    have hf : (fun k ↦ rwProd (r.map (· ^ 2 ^ (j + 1 + k))) rP (cs.getD k 0)) =
        (fun k ↦ rwProd (r.map (· ^ 2 ^ (j + (k + 1)))) rP ((c :: cs).getD (k + 1) 0)) := by
      funext k; rw [show j + 1 + k = j + (k + 1) by omega, List.getD_cons_succ]
    rw [hf, show j + 1 + cs.length = j + (cs.length + 1) by omega, List.getD_cons_zero,
      add_assoc]
    simp only [Nat.add_zero]

/-- **`ringWeight` as a sum** of its products. -/
theorem ringWeight_eq (r rP cs : List E) :
    ringWeight r rP cs = gsum (fun k ↦ rwProd (r.map (· ^ 2 ^ k)) rP (cs.getD k 0)) cs.length := by
  have h := ringWeight_fold r rP cs 0 0
  have hr0 : r.map (· ^ 2 ^ 0) = r := by simp
  rw [hr0] at h
  simp only [zero_add] at h
  show (cs.foldl (fun (acc : E × List E) c ↦
      (acc.1 + rwProd acc.2 rP c, acc.2.map fun value ↦ value * value)) (0, r)).1 = _
  rw [h]

theorem foldl_mul_start : ∀ (l : List E) (c : E), l.foldl (· * ·) c = c * l.foldl (· * ·) 1
  | [], c => by simp
  | x :: l, c => by
    rw [List.foldl_cons, List.foldl_cons, foldl_mul_start l (c * x), foldl_mul_start l (1 * x),
      one_mul, mul_assoc]

/-- With `r' = 1 + p`, a product of `ringWeight` is `ringRow` (B1-a's, `rs_eq_run`'s rows):
`1 + v + (1 + p) = v + p` in characteristic two. -/
theorem rwProd_eq_ringRow (k : ℕ) :
    ∀ (rs ps : List E) (c : E), rs.length = ps.length →
      rwProd (rs.map (· ^ 2 ^ k)) (ps.map (1 + ·)) c = c * ringRow 1 rs ps k
  | [], [], c, _ => by simp [rwProd, ringRow]
  | r :: rs, p :: ps, c, h => by
    have h' : rs.length = ps.length := by simpa using h
    have e : 1 + r ^ 2 ^ k + (1 + p) = r ^ 2 ^ k + p := by
      rw [add_comm (1 : E) (r ^ 2 ^ k), add_assoc, ← add_assoc (1 : E), e_add_self, zero_add]
    have := rwProd_eq_ringRow k rs ps (c * (r ^ 2 ^ k + p)) h'
    simp only [rwProd, List.map_cons, List.zip_cons_cons, List.foldl_cons] at this ⊢
    rw [e, this]
    simp only [ringRow, List.zipWith_cons_cons, List.foldl_cons, one_mul]
    rw [foldl_mul_start _ (r ^ 2 ^ k + p), mul_assoc]
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp at h

/-! ## The body -/

/-- Row `0`'s entry `k`: `1` (`prod_chains[k] = 1`). -/
def rswInit (k : ℕ) : List Stmt :=
  [.atom (.const (.n (13 + k)) (word 1 0)), .atom (.load (.n (13 + k)) (.n 12) k)]

/-- The value of `c_table[k]`, of the last row's entry `k`, of their product. -/
def rswC (k : ℕ) : ℕ := if k = 0 then 78 else 4 * k + 77
def rswP (k : ℕ) : ℕ := if k = 0 then 79 else 4 * k + 78
def rswM (k : ℕ) : ℕ := if k = 0 then 80 else 4 * k + 79

/-- Term `k` of the sum: `c_table[k]·row[k]`, added to the running sum (`4k + 80`). -/
def rswTerm (k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.load (.n 78) (.n 2) 0), .atom (.load (.n 79) (.n 77) 0),
      .atom (.mul (.n 80) (.n 78) (.n 79))]
  else
    [.atom (.load (.n (4 * k + 77)) (.n 2) k), .atom (.load (.n (4 * k + 78)) (.n 77) k),
      .atom (.mul (.n (4 * k + 79)) (.n (4 * k + 77)) (.n (4 * k + 78))),
      .atom (.add (.n (4 * k + 80)) (.n (4 * k + 76)) (.n (4 * k + 79)))]

/-- `ring_switch_weight`'s body. -/
def rswT : List Stmt :=
  [.atom (.const (.n 4) (word 2 0)), .atom (.mul (.n 5) (.n 3) (.n 4)),
    .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 7)), .atom (.mul (.n 9) (.n 8) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.hint (.allocDyn (.n 12) (.n 11)))] ++
  ((List.range 64).map rswInit).flatten ++ [.call "rs_eq_run" [.n 12, .n 0, .n 1, .n 3] [.n 77]] ++
  ((List.range 64).map rswTerm).flatten ++ [.atom (.copy (.n 333) (.n 332)), .ret [.n 333]]

theorem rsw_body : Data.core14.body = rswT := stmtsEqb_sound (by decide +kernel)

theorem find_rsw : coreProgram.find? "ring_switch_weight" = some Data.core14 :=
  coreProgram_find?_at (j := 14) rfl

theorem rswInit_noRet (k : ℕ) : Stmt.noRetList (rswInit k) = true := rfl

theorem rswTerm_noRet (k : ℕ) : Stmt.noRetList (rswTerm k) = true := by
  unfold rswTerm; split <;> rfl

/-- What term `k` asks of a valuation. -/
theorem holds_rswTerm {k : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (rswTerm k) True kret) :
    LoadHolds rd (σ (.n 2)) k (σ (.n (rswC k))) ∧ LoadHolds rd (σ (.n 77)) k (σ (.n (rswP k))) ∧
      σ (.n (rswM k)) = σ (.n (rswC k)) * σ (.n (rswP k)) ∧
      (k ≠ 0 → σ (.n (4 * k + 80)) = σ (.n (4 * (k - 1) + 80)) + σ (.n (rswM k))) := by
  unfold rswTerm at h
  split at h
  · subst_vars
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
    exact ⟨h.1, h.2.1, h.2.2, fun h0 => absurd rfl h0⟩
  · rename_i hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
    simp only [rswC, rswP, rswM, hk, ↓reduceIte]
    refine ⟨h.1, h.2.1, h.2.2.1, fun _ => ?_⟩
    rw [h.2.2.2, show 4 * (k - 1) + 80 = 4 * k + 76 by omega]

/-- The running sum: `4k + 80` holds `Σ_{j ≤ k} c_table[j]·row[j]`. -/
theorem rsw_acc (hm : ∀ k < 64, (k ≠ 0 → σ (.n (4 * k + 80)) = σ (.n (4 * (k - 1) + 80)) +
      σ (.n (rswM k)))) :
    ∀ k < 64, σ (.n (4 * k + 80)) = gsum (fun j ↦ σ (.n (rswM j))) (k + 1)
  | 0, _ => by rw [gsum_one]; rfl
  | k + 1, hk => by
    rw [hm (k + 1) hk (by omega), Nat.add_sub_cancel, rsw_acc hm k (by omega), gsum_succ (n := k + 1)]

/-- **`ring_switch_weight` computes `ringWeight`**, from `rs_eq_run`'s (`rs_eq_run_sound`). -/
theorem ring_switch_weight_holds : ring_switch_weight_Spec := by
  intro rd args rets h
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_rsw args rets).mp h
  simp only [Data.core14, List.map_cons, List.map_nil] at hpar hb
  subst hpar
  rw [rsw_body] at hb
  simp only [rswT, holdsList_append] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨-, -, -, -, -, -, -, -, -, hb⟩ := hb
  obtain ⟨hinit, hb⟩ := (holdsList_range_flatten 64 rswInit rswInit_noRet _ _).mp hb
  obtain ⟨hcall, hb⟩ := hb
  obtain ⟨hterm, e333, hret⟩ := (holdsList_range_flatten 64 rswTerm rswTerm_noRet _ _).mp hb
  have hrow0 : ∀ k < 64, LoadHolds rd (σ (.n 12)) k 1 := by
    intro k hk
    have := hinit k hk
    simp only [rswInit, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    rw [← word_one, ← this.1]; exact this.2
  have ht := fun k hk => holds_rswTerm (hterm k hk)
  have hrsm := rs_eq_run_sound rd _ _ hcall
  simp only [List.map_cons, List.map_nil, MeaningRsEqRun] at hrsm
  obtain ⟨count, hcount, hcg, zs, ps, c, hzl, hpl, hcl, hz, hp, hc, hrows, hret77⟩ := hrsm
  simp only [List.cons.injEq, and_true] at hret77
  have hpk : ∀ k < 64, σ (.n (rswP k)) = ringRow 1 zs ps k := by
    intro k hk
    have l := (ht k hk).2.1
    rw [hret77, loadHolds_mul_gen_pow] at l
    rcases Nat.eq_zero_or_pos count with h0 | hpos
    · subst h0
      have hz0 : zs = [] := List.length_eq_zero_iff.mp hzl
      have hp0 : ps = [] := List.length_eq_zero_iff.mp hpl
      subst hz0 hp0
      simp only [Nat.zero_add, Nat.reduceDiv, mul_zero] at l
      rw [loadHolds_unique l (hrow0 k hk)]
      rfl
    · have hH : 1 ≤ (count + 7) / 8 := by omega
      have r := hrows _ hH le_rfl k hk
      have hmin : min (8 * ((count + 7) / 8)) count = count := by omega
      rw [hmin, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at r
      have hck : c.getD k 0 = 1 := by
        have := hc hpos k (by rw [hcl]; exact hk)
        rw [List.getD_eq_getElem _ _ (by rw [hcl]; exact hk)]
        exact loadHolds_unique this (hrow0 k hk)
      rw [hck] at r
      exact loadHolds_unique l r
  refine ⟨count, hcount, hcg, zs, ps, (List.range 64).map (fun k ↦ σ (.n (rswC k))), hzl, hpl,
    by simp [kBits], hz, hp, ?_, ?_⟩
  · intro k hk
    simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    exact (ht k hk).1
  · rw [← hret]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [e333, show (332 : ℕ) = 4 * 63 + 80 from rfl,
      rsw_acc (fun k hk => (ht k hk).2.2.2) 63 (by decide), ringWeight_eq]
    simp only [List.length_map, List.length_range]
    refine gsum_congr fun k hk => ?_
    rw [(ht k hk).2.2.1, hpk k hk, rwProd_eq_ringRow k zs ps _ (by rw [hzl, hpl]),
      List.getD_eq_getElem _ _ (by simpa using hk)]
    simp only [List.getElem_map, List.getElem_range]

end
end LeanVM.Guest.B1.VerifySub
