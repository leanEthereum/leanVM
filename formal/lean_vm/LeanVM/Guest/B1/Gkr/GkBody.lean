/-
  LeanVM.Guest.B1.Gkr.GkBody

  B1-a's `gk_complete` (`Sumcheck/Gkr.lean`), at every number of rounds and over any call
  relation: the honest valuation of `gkBody n` satisfies it.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Gkr

/-!
# The rounds' body, completely, at any number of rounds

`gk_body_holds`: from `MeaningGkrRounds n` at `[rec, pt]`, the valuation of B1-a's `gk_complete`
(`gkVals`, a function of the value's index) satisfies `gkBody n` with its returns `[]`, for every
`1 ≤ n < 16` and every call relation (the body has no call). The proof is `gk_complete`'s, copied: B1-a
states it for the two specializations `gkr_rounds__L1`, `__L2` only; `__loop27`'s iteration is
`gkBody 4` renamed.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem gk_body_holds (n : ℕ) (hn : 1 ≤ n) (hn2 : n < 16) (C : CallRel) (rd : Reader) (rec pt : E)
    (h : MeaningGkrRounds n rd [rec, pt] [0]) :
    ∃ σ : Val, (∀ v, σ v = σ (.n v.idx)) ∧ σ (.n 0) = rec ∧ σ (.n 1) = pt ∧
      Stmt.HoldsList C rd σ (gkBody n) False (fun rs => rs = [0]) := by
  obtain ⟨hr0, cap, cur, claim, cs, es, ⟨hcl, hcap⟩, hcan, hcur, hclaim, hlen, h4, hflat, hles,
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
  rcases cap with _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, cap⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hcl <;> try omega
  let cap := [a2, a3, a4, a5, a6]
  let St := gkSt Cf ef claim ⟨cap, []⟩
  let P := gkP Cf ef claim ⟨cap, []⟩
  let cl : ℕ → E := fun q ↦ (St q).1
  simp only [hcs, hes, gkrRun_range1, gkrRun_range2] at hres
  obtain ⟨hres1, ⟨-, hres2⟩, hres3, hres4⟩ := hres
  let σ : Val := fun v ↦ gkVals [rec, pt] cap cur Cf ef cl P n v.idx
  have ev : ∀ k, σ (.n k) = gkVals [rec, pt] cap cur Cf ef cl P n k := fun _ ↦ rfl
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have pcan : ∀ x t, IsCanonical128 (fsPackVals x t 6) ∧ IsCanonical128 (fsPackVals x t 8) :=
    fsPackVals_canonical
  have pc : ∀ x t, (fsPackVals x t 6, fsPackVals x t 8) = Keccak.scalarCells x t := fsPackVals_cells
  have zc : IsCanonical128 (0 : E) := by
    rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have kcan : ∀ (L : List E), (∀ x ∈ L, IsCanonical128 x) → ∀ c : Fin 13,
      IsCanonical128 (cells13 L c) := by
    intro L hL c
    simp only [cells13, List.getD_eq_getElem?_getD]
    cases h : L[c.val]? with
    | none => exact zc
    | some x => exact hL x (List.mem_of_getElem? h)
  have e0 : σ (.n 0) = rec := by simp [ev, gkVals]
  have e1 : σ (.n 1) = pt := by simp [ev, gkVals]
  have e7 : σ (.n 7) = cur := by simp [ev, gkVals]
  have vw : ∀ q t, q < n → t < 4 → σ (.n (9 + 74 * q + 10 * t)) = (Cf q).getD t 0 :=
    fun q t hq ht ↦ gkVals_word _ _ _ _ _ _ _ hq ht
  have vp : ∀ q t u, q < n → t < 4 → u < 9 →
      σ (.n (9 + 74 * q + 10 * t + 1 + u)) = fsPackVals ((Cf q).getD t 0) dsObserve u :=
    fun q t u hq ht hu ↦ gkVals_pack _ _ _ _ _ _ _ hq ht hu
  have vc : ∀ q, q < n → ∀ c : Fin 13, σ (.n (49 + 74 * q + c.val)) = cellsOfState (P q) false c :=
    fun q hq c ↦ gkVals_cells _ _ _ _ _ _ _ hq c
  have va : ∀ q u, q < n → u < 13 → σ (.n (70 + 74 * q + u)) =
      (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD u 0 :=
    fun q u hq hu ↦ gkVals_arith _ _ _ _ _ _ _ hq hu
  have hcl : ∀ q, q ≤ n → σ (.n (8 + 74 * q)) = cl q := by
    intro q hq
    cases q with
    | zero => simp [ev, gkVals, cl, St, gkSt]
    | succ q =>
      rw [idx _ (70 + 74 * q + 12) (by ring), va q 12 (by omega) (by omega)]
      show _ = polyEval ((cl q + ef q * sumE (Cf q)) :: Cf q) (challengeOf (P q))
      rw [show Cf q = [(Cf q).getD 0 0, (Cf q).getD 1 0, (Cf q).getD 2 0, (Cf q).getD 3 0] from rfl,
        ← gk_eval]
      rfl
  have capq : ∀ q, q < n → [σ (.n (gkCapPrev q)), σ (.n (gkCapPrev q + 1)), σ (.n (gkCapPrev q + 2)),
      σ (.n (gkCapPrev q + 3)), σ (.n (gkCapPrev q + 4))] = (St q).2.cap := by
    intro q hq
    cases q with
    | zero => simp [ev, gkVals, gkCapPrev, St, gkSt, cap]
    | succ q =>
      have c : ∀ i (hi : i < 5), σ (.n (gkCapPrev (q + 1) + i)) = cellsOfState (P q) false ⟨8 + i, by omega⟩ :=
        fun i hi ↦ (idx _ (49 + 74 * q + (⟨8 + i, by omega⟩ : Fin 13).val)
          (show 57 + 74 * q + i = 49 + 74 * q + (8 + i) by ring)).trans (vc q (by omega) _)
      rw [show σ (.n (gkCapPrev (q + 1))) = _ from c 0 (by omega), c 1 (by omega), c 2 (by omega),
        c 3 (by omega), c 4 (by omega)]
      rfl
  refine ⟨σ, fun v => rfl, e0, e1, ?_⟩
  rw [gkBody]
  simp only [holdsList_append, holdsList_range_flatten n gkRound (fun _ => rfl), holds_gkRound,
    Stmt.HoldsList, Stmt.Holds]
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · show LoadHolds rd (σ (.n 0)) 0 (σ (.n 2))
    rw [e0, show σ (.n 2) = a2 by simp [ev, gkVals, cap]]
    exact hcap 0 (by simp)
  · show LoadHolds rd (σ (.n 0)) 862 (σ (.n 3))
    rw [e0, show σ (.n 3) = a3 by simp [ev, gkVals, cap]]
    exact hcap 1 (by simp)
  · show LoadHolds rd (σ (.n 0)) 1724 (σ (.n 4))
    rw [e0, show σ (.n 4) = a4 by simp [ev, gkVals, cap]]
    exact hcap 2 (by simp)
  · show LoadHolds rd (σ (.n 0)) 2586 (σ (.n 5))
    rw [e0, show σ (.n 5) = a5 by simp [ev, gkVals, cap]]
    exact hcap 3 (by simp)
  · show LoadHolds rd (σ (.n 0)) 3448 (σ (.n 6))
    rw [e0, show σ (.n 6) = a6 by simp [ev, gkVals, cap]]
    exact hcap 4 (by simp)
  · show LoadHolds rd (σ (.n 0)) 4310 (σ (.n 7)); rw [e0, e7]; exact hcur
  · show LoadHolds rd (σ (.n 0)) 5172 (σ (.n 8))
    rw [e0, hcl 0 (by omega)]; exact hclaim
  · have w0 : σ (.n (9 + 74 * q)) = (Cf q).getD 0 0 := (idx _ _ (by ring)).trans (vw q 0 hq (by omega))
    have w1 : σ (.n (19 + 74 * q)) = (Cf q).getD 1 0 := (idx _ _ (by ring)).trans (vw q 1 hq (by omega))
    have w2 : σ (.n (29 + 74 * q)) = (Cf q).getD 2 0 := (idx _ _ (by ring)).trans (vw q 2 hq (by omega))
    have w3 : σ (.n (39 + 74 * q)) = (Cf q).getD 3 0 := (idx _ _ (by ring)).trans (vw q 3 hq (by omega))
    have b0 : σ (.n (49 + 74 * q)) = cellsOfState (P q) false 0 := vc q hq 0
    have b1 : σ (.n (50 + 74 * q)) = cellsOfState (P q) false 1 :=
      (idx _ (49 + 74 * q + (1 : Fin 13).val) (by simp; ring)).trans (vc q hq 1)
    have hr : σ (.n (68 + 74 * q)) = challengeOf (P q) := by
      rw [idx _ (62 + 74 * q + 6) (by ring), ev, gkVals_chal _ _ _ _ _ _ _ hq (u := 6) (by omega),
        challengeVals_six]
    have he : σ (.n (69 + 74 * q)) = ef q := gkVals_e _ _ _ _ _ _ _ hq
    have a0 : σ (.n (70 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 0 0 :=
      (idx _ (70 + 74 * q + 0) (by ring)).trans (va q 0 hq (by omega))
    have a1 : σ (.n (71 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 1 0 :=
      (idx _ (70 + 74 * q + 1) (by ring)).trans (va q 1 hq (by omega))
    have a2 : σ (.n (72 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 2 0 :=
      (idx _ (70 + 74 * q + 2) (by ring)).trans (va q 2 hq (by omega))
    have a3 : σ (.n (73 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 3 0 :=
      (idx _ (70 + 74 * q + 3) (by ring)).trans (va q 3 hq (by omega))
    have a4 : σ (.n (74 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 4 0 :=
      (idx _ (70 + 74 * q + 4) (by ring)).trans (va q 4 hq (by omega))
    have a5 : σ (.n (75 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 5 0 :=
      (idx _ (70 + 74 * q + 5) (by ring)).trans (va q 5 hq (by omega))
    have a6 : σ (.n (76 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 6 0 :=
      (idx _ (70 + 74 * q + 6) (by ring)).trans (va q 6 hq (by omega))
    have a7 : σ (.n (77 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 7 0 :=
      (idx _ (70 + 74 * q + 7) (by ring)).trans (va q 7 hq (by omega))
    have a8 : σ (.n (78 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 8 0 :=
      (idx _ (70 + 74 * q + 8) (by ring)).trans (va q 8 hq (by omega))
    have a9 : σ (.n (79 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 9 0 :=
      (idx _ (70 + 74 * q + 9) (by ring)).trans (va q 9 hq (by omega))
    have a10 : σ (.n (80 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 10 0 :=
      (idx _ (70 + 74 * q + 10) (by ring)).trans (va q 10 hq (by omega))
    have a11 : σ (.n (81 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 11 0 :=
      (idx _ (70 + 74 * q + 11) (by ring)).trans (va q 11 hq (by omega))
    have a12 : σ (.n (82 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 12 0 :=
      (idx _ (70 + 74 * q + 12) (by ring)).trans (va q 12 hq (by omega))
    simp only [gkArith, List.getD_cons_succ,
      List.getD_cons_zero] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    have hin : ([.n (16 + 74 * q), .n (18 + 74 * q), .n (26 + 74 * q), .n (28 + 74 * q),
        .n (36 + 74 * q), .n (38 + 74 * q), .n (46 + 74 * q), .n (48 + 74 * q),
        .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
        .n (gkCapPrev q + 4)] : List V).map σ =
        [fsPackVals ((Cf q).getD 0 0) dsObserve 6, fsPackVals ((Cf q).getD 0 0) dsObserve 8,
          fsPackVals ((Cf q).getD 1 0) dsObserve 6, fsPackVals ((Cf q).getD 1 0) dsObserve 8,
          fsPackVals ((Cf q).getD 2 0) dsObserve 6, fsPackVals ((Cf q).getD 2 0) dsObserve 8,
          fsPackVals ((Cf q).getD 3 0) dsObserve 6, fsPackVals ((Cf q).getD 3 0) dsObserve 8] ++
          (St q).2.cap := by
      rw [← capq q hq]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [idx (16 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 0 + 1 + 6 by ring), vp q 0 6 hq (by omega) (by omega),
        idx (18 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 0 + 1 + 8 by ring), vp q 0 8 hq (by omega) (by omega),
        idx (26 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 1 + 1 + 6 by ring), vp q 1 6 hq (by omega) (by omega),
        idx (28 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 1 + 1 + 8 by ring), vp q 1 8 hq (by omega) (by omega),
        idx (36 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 2 + 1 + 6 by ring), vp q 2 6 hq (by omega) (by omega),
        idx (38 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 2 + 1 + 8 by ring), vp q 2 8 hq (by omega) (by omega),
        idx (46 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 3 + 1 + 6 by ring), vp q 3 6 hq (by omega) (by omega),
        idx (48 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 3 + 1 + 8 by ring), vp q 3 8 hq (by omega) (by omega)]
    have hcanq : AllCanonical (St q).2.cap := by
      cases q with
      | zero => simpa [St, gkSt, cap] using hcan
      | succ q =>
        intro x hx
        simp only [St, gkSt, Fs.squeeze, capOf, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact cellsOfState_canonical _ _ _
    refine ⟨fun t ht ↦ ⟨?_, fsPackOk_of_vals fun u hu ↦ ?_⟩, keccak13_mk (rd := rd) rfl rfl (kcan _ ?_) fun c ↦ ?_,
      challengeOk_of_vals (by rw [b1]; exact cellsOfState_canonical _ _ _) fun u hu ↦ ?_, ?_⟩
    · rw [e7, vw q t hq ht]; exact hm q hq t ht
    · rw [vp q t u hq ht hu, vw q t hq ht]
    · rw [hin]
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | h
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      · exact hcanq x h
    · rw [cells13_gkRun13, vc q hq c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      show _ = permOf _
      rw [hin]
      show gkP Cf ef claim ⟨cap, []⟩ q = _
      rw [gkP_eq Cf ef claim cap q rfl]
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
        ← pc]
      rfl
    · rw [b0, b1]; exact gkVals_chal _ _ _ _ _ _ _ hq hu
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
  · show LoadHolds rd (σ (.n 0)) (m' + 1) (σ (.n (57 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (8 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 0 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 862) (σ (.n (58 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (9 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 1 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 1724) (σ (.n (59 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (10 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 2 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 2586) (σ (.n (60 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (11 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 3 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 3448) (σ (.n (61 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (12 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 4 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show σ (.n (9 + 74 * (m' + 1))) = word (2 ^ (4 * (m' + 1))) 0 0
    exact gkVals_tail0 _ _ _ _ _ _ _
  · show σ (.n (10 + 74 * (m' + 1))) = σ (.n 7) * σ (.n (9 + 74 * (m' + 1)))
    rw [ev, gkVals_tail1, e7, ev, gkVals_tail0]
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 4310) (σ (.n (10 + 74 * (m' + 1))))
    rw [e0, ev, gkVals_tail1, word_two_pow (by omega)]
    exact hres3
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 5172) (σ (.n (82 + 74 * (m' + 1 - 1))))
    rw [e0, show m' + 1 - 1 = m' by omega, idx _ (8 + 74 * (m' + 1)) (by ring), hcl (m' + 1) (by omega)]
    exact hres4
  · show σ (.n (11 + 74 * (m' + 1))) = word 0 0 0
    rw [ev, gkVals_tail2, word_zero]
  · simp only [List.map_cons, List.map_nil, ev, gkVals_tail2]

end
end LeanVM.Guest.B1
