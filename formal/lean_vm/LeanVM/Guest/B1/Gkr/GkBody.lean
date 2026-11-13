/-
  LeanVM.Guest.B1.Gkr.GkBody

  B1-a's `gk_complete` (`Sumcheck/Gkr.lean`), at every number of rounds and over any call
  relation: the honest valuation of `gkBody n` satisfies it.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Gkr

/-!
# The rounds' body, completely, at any number of rounds

`gk_body_holds`: from `MeaningGkrRounds n` at `[rec, pt, tabs]`, the valuation of B1-a's
`gk_complete` (`gkVals`, a function of the value's index) satisfies `gkBody n` with its returns,
for every `1 ≤ n < 16` and every call relation (the body has no call). The proof is `gk_complete`'s,
copied: B1-a states it for the specializations `gkr_rounds__L{1,2,4,6}` only; `verify_bus_gkr_loop0_loop0`'s
iteration is `gkBody 8` renamed.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem gk_body_holds (n : ℕ) (hn : 1 ≤ n) (hn2 : n < 16) (C : CallRel) (rd : Reader)
    (rec pt tabs : E) {rets : List E} (h : MeaningGkrRounds n rd [rec, pt, tabs] rets) :
    ∃ σ : Val, (∀ v, σ v = σ (.n v.idx)) ∧ σ (.n 0) = rec ∧ σ (.n 1) = pt ∧ σ (.n 2) = tabs ∧
      Stmt.HoldsList C rd σ (gkBody n) False (fun rs => rs = rets) := by
  obtain ⟨hr0, cap, cur, claim, cs, es, ⟨hcl, hcap⟩, hcur, hclaim, hlen, h4, hflat, hles,
    hpt, hres⟩ := h
  let Cf : ℕ → List E := fun q ↦ [(cs.getD q []).getD 0 0, (cs.getD q []).getD 1 0,
    (cs.getD q []).getD 2 0, (cs.getD q []).getD 3 0]
  let ef : ℕ → E := fun q ↦ es.getD q 0
  have hcs : cs = (List.range n).map Cf := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Cf, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, Option.getD_some]
    exact list4_eq (h4 _ (List.getElem_mem h1))
  have hes : es = (List.range n).map ef := by
    apply List.ext_getElem (by simp [hles])
    intro i h1 h2
    simp [ef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  have hC4 : ∀ q, (Cf q).length = 4 := fun _ ↦ rfl
  have hm : ∀ q, q < n → ∀ t, t < 4 → LoadHolds rd cur (4 * q + t) ((Cf q).getD t 0) := by
    intro q hq t ht
    rw [hcs] at hflat
    have hk : 4 * q + t < ((List.range n).map Cf).flatten.length := by
      rw [flatten4_length Cf hC4]; omega
    have := hflat _ hk
    rwa [show ((List.range n).map Cf).flatten[4 * q + t] =
        ((List.range n).map Cf).flatten.getD (4 * q + t) 0 by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk],
      flatten4_get Cf hC4 n q t hq ht] at this
  rcases cap with _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, cap⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hcl <;> try omega
  let cap := [a3, a4, a5, a6, a7]
  let St := gkSt Cf ef claim ⟨cap, []⟩
  let P := gkP Cf ef claim ⟨cap, []⟩
  let cl : ℕ → E := fun q ↦ (St q).1
  simp only [hcs, hes, gkrRun_range1, gkrRun_range2] at hres
  obtain ⟨hres1, ⟨-, hres2⟩, hres3, hres4⟩ := hres
  let σ : Val := fun v ↦ gkVals [rec, pt, tabs] cap cur Cf ef cl P n v.idx
  have ev : ∀ k, σ (.n k) = gkVals [rec, pt, tabs] cap cur Cf ef cl P n k := fun _ ↦ rfl
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have e0 : σ (.n 0) = rec := by simp [ev, gkVals]
  have e1 : σ (.n 1) = pt := by simp [ev, gkVals]
  have e8 : σ (.n 8) = cur := by simp [ev, gkVals]
  have vw : ∀ q t r, q < n → t < 4 → r < 3 → σ (.n (10 + 40 * q + 3 * t + r)) =
      if r = 2 then word 0 dsObserve else (Cf q).getD t 0 :=
    fun q t r hq ht hr ↦ gkVals_word _ _ _ _ _ _ _ hq ht hr
  have vc : ∀ q, q < n → ∀ c : Fin 13, σ (.n (22 + 40 * q + c.val)) = cellsOfState (P q) false c :=
    fun q hq c ↦ gkVals_cells _ _ _ _ _ _ _ hq c
  have va : ∀ q u, q < n → u < 13 → σ (.n (37 + 40 * q + u)) =
      (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD u 0 :=
    fun q u hq hu ↦ gkVals_arith _ _ _ _ _ _ _ hq hu
  have hcl : ∀ q, q ≤ n → σ (.n (9 + 40 * q)) = cl q := by
    intro q hq
    cases q with
    | zero => simp [ev, gkVals, cl, St, gkSt]
    | succ q =>
      rw [idx _ (37 + 40 * q + 12) (by ring), va q 12 (by omega) (by omega)]
      show _ = polyEval ((cl q + ef q * sumE (Cf q)) :: Cf q) (challengeOf (P q))
      rw [show Cf q = [(Cf q).getD 0 0, (Cf q).getD 1 0, (Cf q).getD 2 0, (Cf q).getD 3 0] from rfl,
        ← gk_eval]
      rfl
  have capq : ∀ q, q < n → [σ (.n (gkCapPrev q)), σ (.n (gkCapPrev q + 1)),
      σ (.n (gkCapPrev q + 2)), σ (.n (gkCapPrev q + 3)), σ (.n (gkCapPrev q + 4))] =
        (St q).2.cap := by
    intro q hq
    cases q with
    | zero => simp [ev, gkVals, gkCapPrev, St, gkSt, cap]
    | succ q =>
      have c : ∀ i (hi : i < 5), σ (.n (gkCapPrev (q + 1) + i)) =
          cellsOfState (P q) false ⟨8 + i, by omega⟩ :=
        fun i hi ↦ (idx _ (22 + 40 * q + (⟨8 + i, by omega⟩ : Fin 13).val)
          (show 30 + 40 * q + i = 22 + 40 * q + (8 + i) by ring)).trans (vc q (by omega) _)
      rw [show σ (.n (gkCapPrev (q + 1))) = _ from c 0 (by omega), c 1 (by omega), c 2 (by omega),
        c 3 (by omega), c 4 (by omega)]
      rfl
  have e2 : σ (.n 2) = tabs := by simp [ev, gkVals]
  refine ⟨σ, fun v => rfl, e0, e1, e2, ?_⟩
  rw [gkBody]
  simp only [holdsList_append, holdsList_range_flatten n gkRound (fun _ => rfl), holds_gkRound,
    Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq ↦ ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show LoadHolds rd (σ (.n 0)) 0 (σ (.n 3))
    rw [e0, show σ (.n 3) = a3 by simp [ev, gkVals, cap]]
    exact hcap 0 (by simp)
  · show LoadHolds rd (σ (.n 0)) 862 (σ (.n 4))
    rw [e0, show σ (.n 4) = a4 by simp [ev, gkVals, cap]]
    exact hcap 1 (by simp)
  · show LoadHolds rd (σ (.n 0)) 1724 (σ (.n 5))
    rw [e0, show σ (.n 5) = a5 by simp [ev, gkVals, cap]]
    exact hcap 2 (by simp)
  · show LoadHolds rd (σ (.n 0)) 2586 (σ (.n 6))
    rw [e0, show σ (.n 6) = a6 by simp [ev, gkVals, cap]]
    exact hcap 3 (by simp)
  · show LoadHolds rd (σ (.n 0)) 3448 (σ (.n 7))
    rw [e0, show σ (.n 7) = a7 by simp [ev, gkVals, cap]]
    exact hcap 4 (by simp)
  · show LoadHolds rd (σ (.n 0)) 4310 (σ (.n 8)); rw [e0, e8]; exact hcur
  · show LoadHolds rd (σ (.n 0)) 5172 (σ (.n 9))
    rw [e0, idx 9 (9 + 40 * 0) (by ring), hcl 0 (by omega)]; exact hclaim
  · have w : ∀ t, t < 4 → σ (.n (10 + 40 * q + 3 * t)) = (Cf q).getD t 0 := fun t ht ↦ by
      rw [idx _ (10 + 40 * q + 3 * t + 0) (by ring), vw q t 0 hq ht (by omega)]; rfl
    have w0 : σ (.n (10 + 40 * q)) = (Cf q).getD 0 0 := (idx _ _ (by ring)).trans (w 0 (by omega))
    have w1 : σ (.n (13 + 40 * q)) = (Cf q).getD 1 0 := (idx _ _ (by ring)).trans (w 1 (by omega))
    have w2 : σ (.n (16 + 40 * q)) = (Cf q).getD 2 0 := (idx _ _ (by ring)).trans (w 2 (by omega))
    have w3 : σ (.n (19 + 40 * q)) = (Cf q).getD 3 0 := (idx _ _ (by ring)).trans (w 3 (by omega))
    have wc : ∀ t, t < 4 → σ (.n (10 + 40 * q + 3 * t + 1)) = (Cf q).getD t 0 := fun t ht ↦ by
      rw [vw q t 1 hq ht (by omega)]; rfl
    have wt : ∀ t, t < 4 → σ (.n (10 + 40 * q + 3 * t + 1 + 1)) = word 0 dsObserve := fun t ht ↦ by
      rw [idx _ (10 + 40 * q + 3 * t + 2) (by ring), vw q t 2 hq ht (by omega)]; rfl
    have b0 : σ (.n (22 + 40 * q)) = cellsOfState (P q) false 0 := vc q hq 0
    have hr : σ (.n (35 + 40 * q)) = challengeOf (P q) := gkVals_chal _ _ _ _ _ _ _ hq
    have he : σ (.n (36 + 40 * q)) = ef q := gkVals_e _ _ _ _ _ _ _ hq
    have a : ∀ u, u < 13 → σ (.n (37 + 40 * q + u)) =
        (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD u 0 := fun u hu ↦ va q u hq hu
    have a0 := (idx (37 + 40 * q) (37 + 40 * q + 0) (by ring)).trans (a 0 (by omega))
    have a1 := (idx (38 + 40 * q) (37 + 40 * q + 1) (by ring)).trans (a 1 (by omega))
    have a2 := (idx (39 + 40 * q) (37 + 40 * q + 2) (by ring)).trans (a 2 (by omega))
    have a3 := (idx (40 + 40 * q) (37 + 40 * q + 3) (by ring)).trans (a 3 (by omega))
    have a4 := (idx (41 + 40 * q) (37 + 40 * q + 4) (by ring)).trans (a 4 (by omega))
    have a5 := (idx (42 + 40 * q) (37 + 40 * q + 5) (by ring)).trans (a 5 (by omega))
    have a6 := (idx (43 + 40 * q) (37 + 40 * q + 6) (by ring)).trans (a 6 (by omega))
    have a7 := (idx (44 + 40 * q) (37 + 40 * q + 7) (by ring)).trans (a 7 (by omega))
    have a8 := (idx (45 + 40 * q) (37 + 40 * q + 8) (by ring)).trans (a 8 (by omega))
    have a9 := (idx (46 + 40 * q) (37 + 40 * q + 9) (by ring)).trans (a 9 (by omega))
    have a10 := (idx (47 + 40 * q) (37 + 40 * q + 10) (by ring)).trans (a 10 (by omega))
    have a11 := (idx (48 + 40 * q) (37 + 40 * q + 11) (by ring)).trans (a 11 (by omega))
    have a12 := (idx (49 + 40 * q) (37 + 40 * q + 12) (by ring)).trans (a 12 (by omega))
    simp only [gkArith, List.getD_cons_succ,
      List.getD_cons_zero] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    have hin : ([.n (11 + 40 * q), .n (12 + 40 * q), .n (14 + 40 * q), .n (15 + 40 * q),
        .n (17 + 40 * q), .n (18 + 40 * q), .n (20 + 40 * q), .n (21 + 40 * q),
        .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
        .n (gkCapPrev q + 4)] : List V).map σ =
        [(Cf q).getD 0 0, word 0 dsObserve, (Cf q).getD 1 0, word 0 dsObserve,
          (Cf q).getD 2 0, word 0 dsObserve, (Cf q).getD 3 0, word 0 dsObserve] ++
          (St q).2.cap := by
      rw [← capq q hq]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [idx (11 + 40 * q) _ (show _ = 10 + 40 * q + 3 * 0 + 1 by ring), wc 0 (by omega),
        idx (12 + 40 * q) _ (show _ = 10 + 40 * q + 3 * 0 + 1 + 1 by ring), wt 0 (by omega),
        idx (14 + 40 * q) _ (show _ = 10 + 40 * q + 3 * 1 + 1 by ring), wc 1 (by omega),
        idx (15 + 40 * q) _ (show _ = 10 + 40 * q + 3 * 1 + 1 + 1 by ring), wt 1 (by omega),
        idx (17 + 40 * q) _ (show _ = 10 + 40 * q + 3 * 2 + 1 by ring), wc 2 (by omega),
        idx (18 + 40 * q) _ (show _ = 10 + 40 * q + 3 * 2 + 1 + 1 by ring), wt 2 (by omega),
        idx (20 + 40 * q) _ (show _ = 10 + 40 * q + 3 * 3 + 1 by ring), wc 3 (by omega),
        idx (21 + 40 * q) _ (show _ = 10 + 40 * q + 3 * 3 + 1 + 1 by ring), wt 3 (by omega)]
    refine ⟨fun t ht ↦ ⟨?_, ⟨by rw [wc t ht, w t ht], wt t ht⟩⟩, keccakA_of (rd := rd) rfl rfl ?_,
      by rw [ChallengeOk, hr, b0, Keccak.challengeOf_cells], ?_⟩
    · rw [e8, w t ht]; exact hm q hq t ht
    · funext c
      rw [cells13_gkRun13, vc q hq c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      show _ = permOf _
      rw [hin]
      show gkP Cf ef claim ⟨cap, []⟩ q = _
      rw [gkP_eq Cf ef claim cap q rfl, gk_pend]
      rfl
    · have hpe : LoadHolds rd pt q (ef q) := by
        have := hpt q (by rw [hles]; omega)
        rwa [show es[q] = ef q by simp [ef, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show q < es.length by rw [hles]; omega)]] at this
      refine ⟨by rw [e1, he]; exact hpe, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [a0, w0, w1]
      · rw [a1, a0, w2]
      · rw [a2, a1, w3]
      · rw [a3, he, a2]
      · rw [a4, hcl q hq.le, a3]
      · rw [e1, hr]
        have := hres1 q (by simp; omega)
        simp only [List.getElem_map, List.getElem_range] at this
        rwa [loadHolds_mul_gen_pow] at this
      · rw [a5, hr, w3]
      · rw [a6, w2, a5]
      · rw [a7, hr, a6]
      · rw [a8, w1, a7]
      · rw [a9, hr, a8]
      · rw [a10, w0, a9]
      · rw [a11, hr, a10]
      · rw [a12, a4, a11]
  · show LoadHolds rd (σ (.n 0)) (m' + 1) (σ (.n (30 + 40 * (m' + 1 - 1))))
    rw [e0, idx _ (22 + 40 * m' + (8 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 0 (by simp [gkSt, Fs.squeeze, capOf])
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 862) (σ (.n (31 + 40 * (m' + 1 - 1))))
    rw [e0, idx _ (22 + 40 * m' + (9 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 1 (by simp [gkSt, Fs.squeeze, capOf])
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 1724) (σ (.n (32 + 40 * (m' + 1 - 1))))
    rw [e0, idx _ (22 + 40 * m' + (10 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 2 (by simp [gkSt, Fs.squeeze, capOf])
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 2586) (σ (.n (33 + 40 * (m' + 1 - 1))))
    rw [e0, idx _ (22 + 40 * m' + (11 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 3 (by simp [gkSt, Fs.squeeze, capOf])
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 3448) (σ (.n (34 + 40 * (m' + 1 - 1))))
    rw [e0, idx _ (22 + 40 * m' + (12 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 4 (by simp [gkSt, Fs.squeeze, capOf])
  · show σ (.n (10 + 40 * (m' + 1))) = word (2 ^ (4 * (m' + 1))) 0
    exact gkVals_tail0 _ _ _ _ _ _ _
  · show σ (.n (11 + 40 * (m' + 1))) = σ (.n 8) * σ (.n (10 + 40 * (m' + 1)))
    rw [ev, gkVals_tail1, e8, ev, gkVals_tail0]
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 4310) (σ (.n (11 + 40 * (m' + 1))))
    rw [e0, ev, gkVals_tail1, word_two_pow (by omega)]
    exact hres3
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 5172) (σ (.n (49 + 40 * (m' + 1 - 1))))
    rw [e0, show m' + 1 - 1 = m' by omega, idx _ (9 + 40 * (m' + 1)) (by ring),
      hcl (m' + 1) (by omega)]
    exact hres4
  · show σ (.n (12 + 40 * (m' + 1))) = word 0 0
    rw [ev, gkVals_tail2, word_zero]
  · show [σ (.n (12 + 40 * (m' + 1)))] = rets
    rw [hr0, ev, gkVals_tail2]

end
end LeanVM.Guest.B1
