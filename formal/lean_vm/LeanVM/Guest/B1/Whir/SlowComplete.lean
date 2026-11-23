/-
  LeanVM.Guest.B1.Whir.SlowComplete

  `residual_query_slow` and `level_residual_sum`'s loop, completely.
-/

module

public import LeanVM.Guest.B1.Whir.SlowLevel
import LeanVM.Guest.B1.Common.Vc

/-!
# The slow residual, completely

Each template holds of a valuation that returns its value (the soundness lemmas then say there is
no other):

* `rqs_complete`: `residual_query_slow`'s body at the challenges it reads returns the product of its
  factors, on the valuation `rqsSig` (the head's values, then eleven a coordinate, `rqsBlk`);
* `lrsLoop_complete`: the loop runs from `g^j`, `j < Q`, to `g^Q`, on a memory whose buffers hold
  the sum's partial values (`lrsAcc`) and `λ`'s powers, its `residual_query_slow` at depth `1`.

The sum and `level_residual_slow` themselves are placed in `Place/LsKey.lean`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `residual_query_slow` -/

section Rqs

variable (x fc tc : E) (cs : ℕ → E) (vo n : ℕ)

/-- The chain at coordinate `t`. -/
abbrev rqsCh (t : ℕ) : E := residualChain (osVals vo n) x t

/-- The product of the first `t` factors. -/
abbrev rqsPr (t : ℕ) : E := ∏ s ∈ Finset.range t, rqsFac vo n cs x s

/-- Coordinate `t ≥ 1`'s eleven values. -/
def rqsBlk (t i : ℕ) : E :=
  [cs t, word 1 0, word 1 0 + cs t, word (vanishInv (vo + t)) 0, cs t * word (vanishInv (vo + t)) 0,
    cs t * word (vanishInv (vo + t)) 0 * rqsCh x vo n t,
    word 1 0 + cs t + cs t * word (vanishInv (vo + t)) 0 * rqsCh x vo n t, rqsPr x cs vo n (t + 1),
    word (vanishVal (vo + t)) 0, rqsCh x vo n t + word (vanishVal (vo + t)) 0,
    rqsCh x vo n (t + 1)].getD i 0

/-- The body's valuation: the parameters, the head's eight values, the coordinates' blocks, and the
product copied at `11 n`. -/
def rqsSig (k : ℕ) : E :=
  if k = 11 * n then rqsPr x cs vo n n
  else if k < 3 then [x, fc, tc].getD k 0
  else if k < 11 then
    [cs 0, word 1 0, word 1 0 + cs 0, cs 0 * x, rqsPr x cs vo n 1, word (vanishVal vo) 0,
      x + word (vanishVal vo) 0, rqsCh x vo n 1].getD (k - 3) 0
  else rqsBlk x cs vo n (k / 11) (k % 11)

theorem rqsSig_blk {t i : ℕ} (ht : 1 ≤ t) (htn : t < n) (hi : i < 11) :
    rqsSig x fc tc cs vo n (11 * t + i) = rqsBlk x cs vo n t i := by
  have h1 : ¬ (11 * t + i = 11 * n) := by omega
  have h2 : ¬ (11 * t + i < 3) := by omega
  have h3 : ¬ (11 * t + i < 11) := by omega
  simp only [rqsSig, h1, h2, h3, ↓reduceIte, show (11 * t + i) / 11 = t by omega,
    show (11 * t + i) % 11 = i by omega]

theorem rqsSig_lt3 {k : ℕ} (hk : k < 3) (hn : 1 ≤ n) :
    rqsSig x fc tc cs vo n k = [x, fc, tc].getD k 0 := by
  have h1 : ¬ (k = 11 * n) := by omega
  simp only [rqsSig, h1, hk, ↓reduceIte]

theorem rqsSig_head {k : ℕ} (h3 : 3 ≤ k) (h11 : k < 11) (_hn : 1 ≤ n) :
    rqsSig x fc tc cs vo n k = [cs 0, word 1 0, word 1 0 + cs 0, cs 0 * x, rqsPr x cs vo n 1,
      word (vanishVal vo) 0, x + word (vanishVal vo) 0, rqsCh x vo n 1].getD (k - 3) 0 := by
  have h1 : ¬ (k = 11 * n) := by omega
  have h2 : ¬ (k < 3) := by omega
  simp only [rqsSig, h1, h2, h11, ↓reduceIte]

theorem rqsSig_ch {t : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) (hn : 1 ≤ n) :
    rqsSig x fc tc cs vo n (11 * t - 1) = rqsCh x vo n t := by
  rcases Nat.lt_or_ge 1 t with h | h
  · rw [show 11 * t - 1 = 11 * (t - 1) + 10 by omega,
      rqsSig_blk x fc tc cs vo n (by omega) (by omega) (by omega)]
    simp only [rqsBlk, List.getD_cons_succ, List.getD_cons_zero, Nat.sub_add_cancel ht]
  · obtain rfl : t = 1 := by omega
    rw [show 11 * 1 - 1 = 10 by rfl, rqsSig_head x fc tc cs vo n (by omega) (by omega) hn]
    simp only [Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]

theorem rqsSig_pr {t : ℕ} (ht : 1 ≤ t) (htn : t ≤ n) (hn : 1 ≤ n) :
    rqsSig x fc tc cs vo n (11 * t - 4) = rqsPr x cs vo n t := by
  rcases Nat.lt_or_ge 1 t with h | h
  · rw [show 11 * t - 4 = 11 * (t - 1) + 7 by omega,
      rqsSig_blk x fc tc cs vo n (by omega) (by omega) (by omega)]
    simp only [rqsBlk, List.getD_cons_succ, List.getD_cons_zero, Nat.sub_add_cancel ht]
  · obtain rfl : t = 1 := by omega
    rw [show 11 * 1 - 4 = 7 by rfl, rqsSig_head x fc tc cs vo n (by omega) (by omega) hn]
    simp only [Nat.reduceSub, List.getD_cons_succ, List.getD_cons_zero]

end Rqs

variable {C : CallRel} {rd : Reader}

/-- The valuation of a numbered value. -/
abbrev rqsV (x fc tc : E) (cs : ℕ → E) (vo n : ℕ) : Val := fun v ↦ rqsSig x fc tc cs vo n v.idx

/-- **The coordinates' blocks hold** on `rqsSig`. -/
theorem rqsSteps_complete {pre yr vo : ℕ} {x fc tc : E} {cs : ℕ → E}
    (hf : ∀ t < pre, LoadHolds rd fc t (cs t)) (hy : ∀ j < yr, LoadHolds rd tc j (cs (pre + j))) :
    ∀ (f t : ℕ), 1 ≤ t → t + f = pre + yr →
      AllOk C rd (rqsV x fc tc cs vo (pre + yr)) (rqsSteps pre vo t f)
  | 0, _, _, _ => allOk_nil
  | f + 1, t, ht, htf => by
    rw [rqsSteps, allOk_append]
    refine ⟨?_, rqsSteps_complete hf hy f (t + 1) (by omega) (by omega)⟩
    have hb : ∀ i < 11, rqsSig x fc tc cs vo (pre + yr) (11 * t + i) = rqsBlk x cs vo (pre + yr) t i :=
      fun i hi ↦ rqsSig_blk x fc tc cs vo _ ht (by omega) hi
    have h0 := hb 0 (by omega)
    rw [Nat.add_zero] at h0
    have hch := rqsSig_ch x fc tc cs vo (pre + yr) ht (by omega) (by omega)
    have hpr := rqsSig_pr x fc tc cs vo (pre + yr) ht (by omega) (by omega)
    have hpt : rqsSig x fc tc cs vo (pre + yr) (if t < pre then 1 else 2) = if t < pre then fc else tc := by
      by_cases hp : t < pre
      · simp only [hp, ↓reduceIte, rqsSig_lt3 x fc tc cs vo (pre + yr) (show 1 < 3 by omega) (by omega),
          List.getD_cons_succ, List.getD_cons_zero]
      · simp only [hp, ↓reduceIte, rqsSig_lt3 x fc tc cs vo (pre + yr) (show 2 < 3 by omega) (by omega),
          List.getD_cons_succ, List.getD_cons_zero]
    simp only [rqsStep, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, rqsV, V.n]
    rw [h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega), hb 5 (by omega),
      hb 6 (by omega), hb 7 (by omega), hb 8 (by omega), hb 9 (by omega), hb 10 (by omega), hch, hpr, hpt]
    simp only [rqsBlk, List.getD_cons_zero, List.getD_cons_succ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · by_cases hp : t < pre
      · simp only [hp, ↓reduceIte]
        exact hf t hp
      · simp only [hp, ↓reduceIte]
        have := hy (t - pre) (by omega)
        rwa [show pre + (t - pre) = t by omega] at this
    · rw [rqsPr, rqsPr, Finset.prod_range_succ, word_one]
    · rw [rqsCh, rqsCh, residualChain, osVals_getD (by omega)]

/-- **`residual_query_slow`'s body holds** at the challenges it reads, returning the product of
its factors. -/
theorem rqs_complete {pre yr vo : ℕ} {f : Fn} (hpre : 1 ≤ pre) (hinv : vanishInv vo = 1)
    (hpar : f.params = [.n 0, .n 1, .n 2]) (hb : f.body = rqsBody pre yr vo) {x fc tc : E}
    {cs : ℕ → E} (hf : ∀ t < pre, LoadHolds rd fc t (cs t))
    (hy : ∀ j < yr, LoadHolds rd tc j (cs (pre + j))) :
    f.Sem C rd [x, fc, tc] [∏ t ∈ Finset.range (pre + yr), rqsFac vo (pre + yr) cs x t] := by
  have hn : 1 ≤ pre + yr := by omega
  refine ⟨rqsV x fc tc cs vo (pre + yr), ?_, ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil, rqsV, V.n,
      rqsSig_lt3 x fc tc cs vo _ (show 0 < 3 by omega) hn, rqsSig_lt3 x fc tc cs vo _ (show 1 < 3 by omega) hn,
      rqsSig_lt3 x fc tc cs vo _ (show 2 < 3 by omega) hn, List.getD_cons_succ, List.getD_cons_zero]
  rw [hb, rqsBody, holdsList_flat_ret _ (rqsPre_flat pre yr vo)]
  refine ⟨?_, ?_⟩
  · rw [rqsPre, allOk_append, allOk_append]
    refine ⟨⟨?_, rqsSteps_complete hf hy _ 1 le_rfl (by omega)⟩, ?_⟩
    · simp only [rqsHead, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, rqsV, V.n]
      rw [rqsSig_head x fc tc cs vo _ (show 3 ≤ 3 by omega) (by omega) hn,
        rqsSig_head x fc tc cs vo _ (show 3 ≤ 4 by omega) (by omega) hn,
        rqsSig_head x fc tc cs vo _ (show 3 ≤ 5 by omega) (by omega) hn,
        rqsSig_head x fc tc cs vo _ (show 3 ≤ 6 by omega) (by omega) hn,
        rqsSig_head x fc tc cs vo _ (show 3 ≤ 7 by omega) (by omega) hn,
        rqsSig_head x fc tc cs vo _ (show 3 ≤ 8 by omega) (by omega) hn,
        rqsSig_head x fc tc cs vo _ (show 3 ≤ 9 by omega) (by omega) hn,
        rqsSig_head x fc tc cs vo _ (show 3 ≤ 10 by omega) (by omega) hn,
        rqsSig_lt3 x fc tc cs vo _ (show 0 < 3 by omega) hn,
        rqsSig_lt3 x fc tc cs vo _ (show 1 < 3 by omega) hn]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.reduceSub, true_and]
      refine ⟨hf 0 hpre, ?_, ?_⟩
      · simp only [rqsPr, Finset.prod_range_one, rqsFac, residualChain, Nat.add_zero, hinv, word_one,
          mul_one]
      · rw [rqsCh, residualChain, residualChain, osVals_getD hn, Nat.add_zero]
    · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, rqsV, V.n]
      rw [rqsSig_pr x fc tc cs vo (pre + yr) hn le_rfl hn]
      simp only [rqsSig, ↓reduceIte]
  · simp only [List.map_cons, List.map_nil, rqsV, V.n, rqsSig, ↓reduceIte, rqsPr]

/-! ## The loop and the sum -/

/-- The loop's valuation at `x = g^j`. -/
def lrsLoopSig (x N acc pw posp fc tc lam a p q w : E) : List E :=
  [x, N, acc, pw, posp, fc, tc, lam, acc * x, a, pw * x, p, posp * x, q, w, p * w, a + p * w,
    acc * x, pw * x, p, p * lam, pw * x, word 2 0, x * word 2 0, x * word 2 0 + N, word 2 0,
    x * word 2 0]

/-- **An iteration, completely**: at `x = g^j`, `j < Q`, on a memory whose buffers hold `lrsAcc`
and `λ^(2 + k)` at `j` and `j + 1`, the position read, its `residual_query_slow` returning the
query's weight at depth `1`, and the loop from `g^(j + 1)` at depth `i + 1` when `j + 1 < Q`. -/
theorem lrsLoop_step_complete {P : Program} {rq self : String} {fn : Fn} (hf : P.find? self = some fn)
    (hpar : fn.params = lrsLoopParams) (hb : fn.body = lrsLoopBody rq self) {n vo Q : ℕ}
    {acc pw posp fc tc lam : E} {pos cs : ℕ → E} {i j : ℕ} (hj : j < Q)
    (hacc : ∀ k ≤ Q, LoadHolds rd acc k (lrsAcc n vo pos cs lam k))
    (hpw : ∀ k ≤ Q, LoadHolds rd pw k (lam ^ 2 * lam ^ k))
    (hpos : ∀ k < Q, LoadHolds rd posp k (pos k))
    (hrq : ∀ k < Q, P.relN rd 1 rq [pos k, fc, tc] [∏ t ∈ Finset.range n, rqsFac vo n cs (pos k) t])
    (hnext : j + 1 < Q → P.relN rd (i + 1) self (gen ^ (j + 1) :: [gen ^ Q, acc, pw, posp, fc, tc, lam]) []) :
    P.relN rd (i + 2) self (gen ^ j :: [gen ^ Q, acc, pw, posp, fc, tc, lam]) [] := by
  rw [B1.relN_succ_iff_fnSem hf]
  refine ⟨fun v ↦ (lrsLoopSig (gen ^ j) (gen ^ Q) acc pw posp fc tc lam (lrsAcc n vo pos cs lam j)
    (lam ^ 2 * lam ^ j) (pos j) (∏ t ∈ Finset.range n, rqsFac vo n cs (pos j) t)).getD v.idx 0,
    by rw [hpar]; rfl, ?_⟩
  rw [hb]
  simp only [lrsLoopBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  have la : LoadHolds rd (acc * gen ^ j) 0 (lrsAcc n vo pos cs lam j) :=
    (loadHolds_mul_gen_pow rd acc j 0 _).mpr (hacc j hj.le)
  have lp : LoadHolds rd (pw * gen ^ j) 0 (lam ^ 2 * lam ^ j) :=
    (loadHolds_mul_gen_pow rd pw j 0 _).mpr (hpw j hj.le)
  have lq : LoadHolds rd (posp * gen ^ j) 0 (pos j) :=
    (loadHolds_mul_gen_pow rd posp j 0 _).mpr (hpos j hj)
  have la1 : LoadHolds rd (acc * gen ^ j) 1 (lrsAcc n vo pos cs lam j +
      lam ^ 2 * lam ^ j * ∏ t ∈ Finset.range n, rqsFac vo n cs (pos j) t) := by
    refine (loadHolds_mul_gen_pow rd acc j 1 _).mpr ?_
    convert hacc (j + 1) hj using 1
    simp only [lrsAcc, Finset.sum_range_succ, mul_add]
    ring
  have lp1 : LoadHolds rd (pw * gen ^ j) 1 (lam ^ 2 * lam ^ j * lam) := by
    refine (loadHolds_mul_gen_pow rd pw j 1 _).mpr ?_
    convert hpw (j + 1) hj using 1
    ring
  have hg : gen ^ j * word 2 0 = gen ^ (j + 1) := by rw [word_gen, pow_succ]
  refine ⟨rfl, la, rfl, lp, rfl, lq, relN_mono P (by omega) _ _ _ (hrq j hj), rfl, rfl, rfl, la1, rfl,
    lp, rfl, rfl, lp1, rfl, rfl, rfl, rfl, rfl, ⟨?_, fun hne ↦ ?_, trivial⟩⟩
  · show IsInK (gen ^ j * word 2 0 + gen ^ Q)
    rw [hg]
    exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  · have hne' : gen ^ (j + 1) + gen ^ Q ≠ 0 := by rw [← hg]; exact hne
    have hjQ : j + 1 < Q := by
      by_contra hc
      obtain rfl : Q = j + 1 := by omega
      exact hne' (CharTwo.add_self_eq_zero _)
    have := hnext hjQ
    rw [← hg] at this
    exact this

/-- **The loop, completely**: from `g^j`, `j + i + 1 = Q`, it runs to `g^Q` at depth `i + 2`. -/
theorem lrsLoop_complete {P : Program} {rq self : String} {fn : Fn} (hf : P.find? self = some fn)
    (hpar : fn.params = lrsLoopParams) (hb : fn.body = lrsLoopBody rq self) {n vo Q : ℕ}
    {acc pw posp fc tc lam : E} {pos cs : ℕ → E}
    (hacc : ∀ k ≤ Q, LoadHolds rd acc k (lrsAcc n vo pos cs lam k))
    (hpw : ∀ k ≤ Q, LoadHolds rd pw k (lam ^ 2 * lam ^ k))
    (hpos : ∀ k < Q, LoadHolds rd posp k (pos k))
    (hrq : ∀ k < Q, P.relN rd 1 rq [pos k, fc, tc] [∏ t ∈ Finset.range n, rqsFac vo n cs (pos k) t]) :
    ∀ i j, j + i + 1 = Q → P.relN rd (i + 2) self (gen ^ j :: [gen ^ Q, acc, pw, posp, fc, tc, lam]) [] := by
  intro i
  induction i with
  | zero =>
    intro j hji
    exact lrsLoop_step_complete hf hpar hb (by omega) hacc hpw hpos hrq (fun h ↦ absurd h (by omega))
  | succ i ih =>
    intro j hji
    exact lrsLoop_step_complete hf hpar hb (by omega) hacc hpw hpos hrq
      (fun _ ↦ ih (j + 1) (by omega))

end
end LeanVM.Guest.B1.Whir
