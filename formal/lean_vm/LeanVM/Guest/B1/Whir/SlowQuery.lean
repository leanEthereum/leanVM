/-
  LeanVM.Guest.B1.Whir.SlowQuery

  B1 for `residual_query_slow`: a query's unfactored weight on a level with a zero challenge.
-/

module

public import LeanVM.Guest.B1.Whir.SlowT
public import LeanVM.Guest.B1.Whir.ResQuery
public import LeanVM.Guest.B1.Whir.Flat

/-!
# `residual_query_slow`

`residual_query_slow__L{pre}_L{yr}_L{vo}(x, fold_cs, tail_cs)` walks the chain
`chain_0 = x`, `chain_(t+1) = chain_t·(chain_t + VALS[vo + t])` over `t < n = pre + yr`, and multiplies
the factors `1 + c_t + c_t·INVS[vo + t]·chain_t`, the challenge `c_t` read at `fold_cs·g^t` below
`pre`, else at `tail_cs·g^(t - pre)`. Its body is `rqsBody pre yr vo`: coordinate `0` first, its
inverse `1` folded away (`rqsHead`), then a block of eleven values a coordinate (`rqsStep`, values
from `11 t`), the product copied and returned. `rqs_sound`: a function of that body returns
the product of the factors (`rqsFac`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

theorem rqsSteps_flat (pre vo : ℕ) : ∀ t f, (rqsSteps pre vo t f).all Stmt.flat = true
  | _, 0 => rfl
  | t, f + 1 => by
    rw [rqsSteps, List.all_append, rqsSteps_flat pre vo (t + 1) f, Bool.and_true]
    rfl

theorem rqsPre_flat (pre yr vo : ℕ) : (rqsPre pre yr vo).all Stmt.flat = true := by
  rw [rqsPre, List.all_append, List.all_append, rqsSteps_flat]
  rfl

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Coordinate `t`'s factor. -/
abbrev rqsFac (vo n : ℕ) (cs : ℕ → E) (x : E) (t : ℕ) : E :=
  1 + cs t + cs t * word (vanishInv (vo + t)) 0 * residualChain (osVals vo n) x t

/-- The challenge of coordinate `t`, read where the body reads it. -/
theorem rqs_load {pre yr t : ℕ} {fc tc : E} {cs : ℕ → E} (ht : t < pre + yr)
    (hf : ∀ t < pre, LoadHolds rd fc t (cs t)) (hy : ∀ j < yr, LoadHolds rd tc j (cs (pre + j)))
    {w : E} (h : LoadHolds rd (if t < pre then fc else tc) (if t < pre then t else t - pre) w) :
    w = cs t := by
  by_cases hp : t < pre
  · simp only [hp, ↓reduceIte] at h
    exact loadHolds_unique h (hf t hp)
  · simp only [hp, ↓reduceIte] at h
    have := hy (t - pre) (by omega)
    rw [show pre + (t - pre) = t by omega] at this
    exact loadHolds_unique h this

/-- **The coordinates' blocks**: from coordinate `t ≥ 1` with `f` left, the product so far at
`11 t - 4` and the chain at `11 t - 1`, the product over every coordinate is at `11 n - 4`. -/
theorem rqsSteps_sound {pre yr vo : ℕ} {x fc tc : E} {cs : ℕ → E}
    (h1 : σ (.n 1) = fc) (h2 : σ (.n 2) = tc)
    (hf : ∀ t < pre, LoadHolds rd fc t (cs t)) (hy : ∀ j < yr, LoadHolds rd tc j (cs (pre + j))) :
    ∀ (f t : ℕ), 1 ≤ t → t + f = pre + yr →
      σ (.n (11 * t - 4)) = ∏ s ∈ Finset.range t, rqsFac vo (pre + yr) cs x s →
      σ (.n (11 * t - 1)) = residualChain (osVals vo (pre + yr)) x t →
      AllOk C rd σ (rqsSteps pre vo t f) →
      σ (.n (11 * (pre + yr) - 4)) = ∏ s ∈ Finset.range (pre + yr), rqsFac vo (pre + yr) cs x s
  | 0, t, _, htf, hp, _, _ => by
    obtain rfl : t = pre + yr := by omega
    exact hp
  | f + 1, t, ht, htf, hp, hc, hok => by
    rw [rqsSteps, allOk_append] at hok
    obtain ⟨hs, hr⟩ := hok
    simp only [rqsStep, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hs
    obtain ⟨l0, c1, a2, c3, m4, m5, a6, m7, c8, a9, m10⟩ := hs
    have hld : LoadHolds rd (if t < pre then fc else tc) (if t < pre then t else t - pre)
        (σ (.n (11 * t))) := by
      by_cases hpt : t < pre
      · simp only [hpt, ↓reduceIte] at l0 ⊢; rwa [h1] at l0
      · simp only [hpt, ↓reduceIte] at l0 ⊢; rwa [h2] at l0
    have hcs := rqs_load (by omega) hf hy hld
    refine rqsSteps_sound h1 h2 hf hy f (t + 1) (by omega) (by omega) ?_ ?_ hr
    · rw [show 11 * (t + 1) - 4 = 11 * t + 7 by omega, m7, a6, m5, m4, a2, c1, c3, hcs, hp, hc,
        Finset.prod_range_succ, word_one]
    · rw [show 11 * (t + 1) - 1 = 11 * t + 10 by omega, m10, a9, c8, hc, residualChain,
        osVals_getD (by omega)]

/-- **`residual_query_slow`'s body returns `slowQuery`** at the challenges it reads, its first
coordinate's inverse `1` (`slowQuery` of `SlowSpec.lean` is this product, by `rfl`). -/
theorem rqs_sound {pre yr vo : ℕ} {f : Fn} (hpre : 1 ≤ pre) (hinv : vanishInv vo = 1)
    (hpar : f.params = [.n 0, .n 1, .n 2]) (hb : f.body = rqsBody pre yr vo)
    {x fc tc : E} {rets : List E} (h : f.Sem C rd [x, fc, tc] rets) {cs : ℕ → E}
    (hf : ∀ t < pre, LoadHolds rd fc t (cs t)) (hy : ∀ j < yr, LoadHolds rd tc j (cs (pre + j))) :
    rets = [∏ t ∈ Finset.range (pre + yr), rqsFac vo (pre + yr) cs x t] := by
  obtain ⟨σ, hp, hh⟩ := h
  rw [hpar] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2⟩ := hp
  rw [hb, rqsBody, holdsList_flat_ret _ (rqsPre_flat pre yr vo)] at hh
  obtain ⟨hok, hret⟩ := hh
  rw [rqsPre, allOk_append, allOk_append] at hok
  obtain ⟨⟨hh0, hst⟩, hcp⟩ := hok
  simp only [rqsHead, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hh0
  obtain ⟨l3, c4, a5, m6, a7, c8, a9, m10⟩ := hh0
  rw [h1] at l3
  have hc0 : σ (.n 3) = cs 0 := loadHolds_unique l3 (hf 0 hpre)
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at hcp
  have hprod := rqsSteps_sound (vo := vo) (x := x) h1 h2 hf hy (pre + yr - 1) 1 le_rfl (by omega)
    (by
      rw [show 11 * 1 - 4 = 7 by rfl, a7, a5, m6, c4, hc0, h0, Finset.prod_range_one]
      simp only [rqsFac, residualChain, Nat.add_zero, hinv, word_one, mul_one])
    (by
      rw [show 11 * 1 - 1 = 10 by rfl, m10, a9, c8, h0, residualChain, residualChain,
        osVals_getD (by omega), Nat.add_zero]) hst
  simp only [List.map_cons, List.map_nil] at hret
  rw [← hret, hcp, hprod]

end
end LeanVM.Guest.B1.Whir
