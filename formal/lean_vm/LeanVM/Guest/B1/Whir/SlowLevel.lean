/-
  LeanVM.Guest.B1.Whir.SlowLevel

  B1 for `level_residual_slow`, `level_residual_sum` and its loop: a level's unfactored residual sum,
  `0` at a zero flag.
-/

module

public import LeanVM.Guest.B1.Whir.SlowQuery
public import LeanVM.Guest.B1.Whir.SlowSpec
public import LeanVM.Guest.B1.Tables.Basic
import LeanVM.Guest.B1.Common.Vc

/-!
# `level_residual_slow`

`level_residual_slow__L{Q}_L{pre}_L{yr}_L{vo}(positions, fold_cs, tail_cs, λ, z)` returns `z` at
`z = 0`, else `level_residual_sum__L{Q}_L{pre}_L{yr}_L{vo}(positions, fold_cs, tail_cs, λ)`, which
allocates two buffers `acc`, `pw` of `Q + 1` cells, stores `acc[0] = 0`, `pw[0] = λ²`, runs its loop
over `x = g^k`, `k < Q`, which stores `acc[k + 1] = acc[k] + pw[k]·w_k` and `pw[k + 1] = pw[k]·λ`,
`w_k` the query weight `residual_query_slow` returns at `positions[k]`, and returns `acc[Q]`. Their
bodies are `lrsBody sum`, `lsumBody Q loop` and `lrsLoopBody rq loop` (`Whir/SlowT.lean`).

* `lrsLoop_step`: an iteration's stores;
* `lsum_sound`: the sum returns `λ²·Σ_{k<Q} λ^k·w_k` (`lrsAcc`), each `w_k` the product of
  `residual_query_slow`'s factors at `positions[k]` (`rqs_sound`);
* `lrs_sound`: `level_residual_slow` returns `slowVal`: `0` at `z = 0`, else the sum.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- What `residual_query_slow` at `rq` returns, as its callers read it. -/
def RqOk (C : CallRel) (rq : String) (n vo : ℕ) (fc tc : E) (cs : ℕ → E) : Prop :=
  ∀ x r, C rq [x, fc, tc] [r] → r = ∏ t ∈ Finset.range n, rqsFac vo n cs x t

variable {rd : Reader}

/-- **An iteration of the loop** at `x`: `acc[x·g] = acc[x] + pw[x]·w(positions[x])` and
`pw[x·g] = pw[x]·λ`, and the loop runs on at `x·g` below the bound. -/
theorem lrsLoop_step {P : Program} {rq self : String} {fn : Fn} (hf : P.find? self = some fn)
    (hpar : fn.params = lrsLoopParams) (hb : fn.body = lrsLoopBody rq self) {n vo : ℕ}
    {N acc pw pos fc tc lam : E} {cs : ℕ → E}
    (hrq : ∀ d, RqOk (P.relN rd d) rq n vo fc tc cs) (d : ℕ) (x : E)
    (h : P.relN rd (d + 1) self (x :: [N, acc, pw, pos, fc, tc, lam]) []) :
    (∃ a p q, LoadHolds rd (acc * x) 0 a ∧ LoadHolds rd (pw * x) 0 p ∧ LoadHolds rd (pos * x) 0 q ∧
      LoadHolds rd (acc * x) 1 (a + p * ∏ t ∈ Finset.range n, rqsFac vo n cs q t) ∧
      LoadHolds rd (pw * x) 1 (p * lam)) ∧
      (x * gen + N ≠ 0 → P.relN rd d self (x * gen :: [N, acc, pw, pos, fc, tc, lam]) []) := by
  rw [B1.relN_succ_iff_fnSem hf] at h
  obtain ⟨σ, hp, hh⟩ := h
  rw [hpar] at hp
  simp only [lrsLoopParams, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hp
  rw [hb] at hh
  simp only [lrsLoopBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hh
  obtain ⟨m8, l9, m10, l11, m12, l13, hc, m15, a16, m17, l16, m18, l19, m20, m21, l20, c22, m23, a24,
    c25, m26, ⟨-, hcont, -⟩⟩ := hh
  rw [h2, h0] at m8 m17
  rw [h3, h0] at m10 m18 m21
  rw [h4, h0] at m12
  rw [m8] at l9
  rw [m10] at l11
  rw [m12] at l13
  rw [m17] at l16
  rw [m18] at l19
  rw [m21] at l20
  have hw := hrq d _ _ (by rw [← h5, ← h6]; exact hc)
  refine ⟨⟨σ (.n 9), σ (.n 11), σ (.n 13), l9, l11, l13, ?_, ?_⟩, fun hne ↦ ?_⟩
  · rwa [a16, m15, hw] at l16
  · rw [m20, loadHolds_unique l19 l11, h7] at l20; exact l20
  · have hx := hcont (by rw [a24, m23, c22, h1, h0, B1.word_gen]; exact hne)
    rw [m26, c25, h0, B1.word_gen, h1, h2, h3, h4, h5, h6, h7] at hx
    exact hx

/-- The sum's partial values: `acc[j]` and `pw[j]`. -/
def lrsAcc (n vo : ℕ) (pos cs : ℕ → E) (lam : E) (j : ℕ) : E :=
  lam ^ 2 * ∑ k ∈ Finset.range j, lam ^ k * ∏ t ∈ Finset.range n, rqsFac vo n cs (pos k) t

/-- **The loop's stores**: from `g^0` to `g^Q`, `acc[j]` and `pw[j] = λ^(2 + j)` for `j ≤ Q`. -/
theorem lrs_stores {n vo Q : ℕ} {acc pw posp lam : E} {pos cs : ℕ → E}
    (hpos : ∀ k < Q, LoadHolds rd posp k (pos k))
    (h0 : LoadHolds rd acc 0 0) (hp0 : LoadHolds rd pw 0 (lam * lam))
    (hB : ∀ j < Q, ∃ a p q, LoadHolds rd (acc * gen ^ j) 0 a ∧ LoadHolds rd (pw * gen ^ j) 0 p ∧
      LoadHolds rd (posp * gen ^ j) 0 q ∧
      LoadHolds rd (acc * gen ^ j) 1 (a + p * ∏ t ∈ Finset.range n, rqsFac vo n cs q t) ∧
      LoadHolds rd (pw * gen ^ j) 1 (p * lam)) :
    ∀ j ≤ Q, LoadHolds rd acc j (lrsAcc n vo pos cs lam j) ∧ LoadHolds rd pw j (lam ^ 2 * lam ^ j)
  | 0, _ => by
    refine ⟨by simpa [lrsAcc] using h0, by simpa [pow_two] using hp0⟩
  | j + 1, hj => by
    obtain ⟨ha, hp⟩ := lrs_stores hpos h0 hp0 hB j (by omega)
    obtain ⟨a, p, q, la, lp, lq, la1, lp1⟩ := hB j (by omega)
    rw [loadHolds_mul_gen_pow, Nat.add_zero] at la lp lq
    rw [loadHolds_mul_gen_pow] at la1 lp1
    rw [← loadHolds_unique ha la, ← loadHolds_unique hp lp, ← loadHolds_unique (hpos j (by omega)) lq]
      at la1
    rw [← loadHolds_unique hp lp] at lp1
    refine ⟨?_, ?_⟩
    · convert la1 using 1
      simp only [lrsAcc, Finset.sum_range_succ, mul_add, pow_succ]
      ring
    · convert lp1 using 1
      ring

/-- The loop's first test: `1 + g^Q ≠ 0` for `1 ≤ Q < 2^30`. -/
theorem one_add_gen_pow_ne {Q : ℕ} (h1 : 1 ≤ Q) (h2 : Q < 2 ^ 30) : (1 : E) + gen ^ Q ≠ 0 := by
  intro h0
  have : gen ^ Q = gen ^ 0 := by rw [pow_zero]; exact (CharTwo.add_eq_zero.mp h0).symm
  exact absurd (gen_pow_inj (by omega) (by omega) this) (by omega)

/-- **`level_residual_sum`'s body returns `λ²·Σ_{k<Q} λ^k·w_k`** (`lrsAcc … Q`), at `Q ≥ 1`
queries, the positions it reads, its loop's body `lrsLoopBody` and `residual_query_slow` at `rq`
returning the query weight; its calls through any `C` below `P.Rel`. -/
theorem lsum_sound {P : Program} {C : CallRel} (hC : ∀ f a r, C f a r → P.Rel rd f a r) {Q n vo : ℕ}
    {rq loop : String} {fo fl : Fn} (hQ : 1 ≤ Q) (hQb : Q < 2 ^ 30) (hpar : fo.params = lsumParams)
    (hb : fo.body = lsumBody Q loop) (hfl : P.find? loop = some fl) (hflp : fl.params = lrsLoopParams)
    (hflb : fl.body = lrsLoopBody rq loop) {a rets : List E} (h : fo.Sem C rd a rets) {pos cs : ℕ → E}
    (hrq : ∀ d, RqOk (P.relN rd d) rq n vo (a.getD 1 0) (a.getD 2 0) cs)
    (hpos : ∀ k < Q, LoadHolds rd (a.getD 0 0) k (pos k)) :
    rets = [lrsAcc n vo pos cs (a.getD 3 0) Q] := by
  obtain ⟨σ, hp, hh⟩ := h
  rw [hpar] at hp
  subst hp
  simp only [lsumParams, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] at hrq hpos ⊢
  rw [hb] at hh
  simp only [lsumBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hh
  obtain ⟨-, -, -, -, c8, l8, m9, l9, c10, c11, a12, c13, c14, -, hloop, l15, hr⟩ := hh
  rw [← hr]
  have hgQ : gw Q = gen ^ Q := gw_eq (by unfold u128Bound; omega)
  have h12 : σ (.n 12) ≠ 0 := by
    rw [a12, c10, c11, hgQ, word_one]
    exact one_add_gen_pow_ne hQ hQb
  have hl := hC _ _ _ (hloop h12)
  rw [c13, c14, hgQ, word_one, ← pow_zero gen] at hl
  obtain ⟨m, hm, hN, hall⟩ := Tables.tb_loop_sound (B := fun x ↦ ∃ a p q,
    LoadHolds rd (σ (.n 5) * x) 0 a ∧ LoadHolds rd (σ (.n 7) * x) 0 p ∧
    LoadHolds rd (σ (.n 0) * x) 0 q ∧
    LoadHolds rd (σ (.n 5) * x) 1 (a + p * ∏ t ∈ Finset.range n, rqsFac vo n cs q t) ∧
    LoadHolds rd (σ (.n 7) * x) 1 (p * σ (.n 3)))
    (fun d x hx ↦ lrsLoop_step hfl hflp hflb hrq d x hx) 0 hl
  have hQm : Q ≤ m := by
    by_contra hc
    have := gen_pow_inj (show Q < 2 ^ 64 - 1 by omega) (show m < 2 ^ 64 - 1 by omega) hN
    omega
  have hst := lrs_stores hpos (by rw [c8, word_zero] at l8; exact l8) (by rw [m9] at l9; exact l9)
    (fun j hj ↦ hall j (Nat.zero_le _) (by omega)) Q le_rfl
  rw [loadHolds_unique l15 hst.1]

/-- **`level_residual_slow`'s body returns `slowVal`**: at a zero flag the flag, else its sum's
value, `sum` returning `lrsAcc` (`lsum_sound`). -/
theorem lrs_sound {C : CallRel} {Q n vo : ℕ} {sum : String} {fo : Fn} (hpar : fo.params = lrsParams)
    (hb : fo.body = lrsBody sum) {a rets : List E} (h : fo.Sem C rd a rets) {pos cs : ℕ → E}
    (hsum : ∀ r, C sum (a.take 4) [r] → r = lrsAcc n vo pos cs (a.getD 3 0) Q) :
    rets = [slowVal Q n vo pos cs (a.getD 3 0) (a.getD 4 0)] := by
  obtain ⟨σ, hp, hh⟩ := h
  rw [hpar] at hp
  subst hp
  simp only [lrsParams, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    List.take_succ_cons, List.take_zero] at hsum ⊢
  rw [hb] at hh
  simp only [lrsBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hh
  obtain ⟨-, hz, hnz⟩ := hh
  by_cases h4 : σ (.n 4) = 0
  · obtain ⟨c5, c6, hr⟩ := hz h4
    rw [← hr, c6, c5, h4, slowVal, ite_eq_left rfl]
  · obtain ⟨hs, c6, hr⟩ := hnz h4
    rw [← hr, c6, hsum _ hs, slowVal, ite_eq_right h4, lrsAcc]
    rfl

end
end LeanVM.Guest.B1.Whir
