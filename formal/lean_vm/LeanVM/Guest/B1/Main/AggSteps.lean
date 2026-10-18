/-
  LeanVM.Guest.B1.Main.AggSteps

  One iteration of each batching loop of `aggregate_claims`, read forward.
-/

module

public import LeanVM.Guest.B1.Main.AggChain
public import LeanVM.Guest.B1.Main.AggEqtree
public import LeanVM.Guest.B1.Loops

/-!
# The batching loops, forward

At `x = g^c`, each loop's iteration (`loop95_step` to `loop99_step`) gives what it reads, what
it stores, and the next iteration while `x·g ≠ N`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem noRetList_obsChainT (s0 s1 cur : V) (B n : ℕ) :
    Stmt.noRetList (obsChainT s0 s1 cur B n) = true :=
  noRetList_flatten _ (by simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]; intro _ _; rfl)

set_option maxRecDepth 100000 in
theorem find_loop95 : coreProgram.find? "__loop95" = some Data.core566 :=
  Program.find?_of_indexOf? (j := 566) (by decide +kernel) rfl

/-- **`__loop95` at `x = g^c`**: from the transcript row `c`, the state of `cv`, the child's
public input's cells, its fresh and carried cells are absorbed into row `c + 1`, the pointers
stored. -/
theorem loop95_step {N absorb cpi cfresh frow ccar crow : E} (x : E)
    (h : coreProgram.Rel rd "__loop95" [x, N, absorb, cpi, cfresh, frow, ccar, crow] []) :
    (∀ c, x = gen ^ c → ∃ s0 s1, LoadHolds rd absorb (2 * c) s0 ∧
      LoadHolds rd absorb (2 * c + 1) s1 ∧ ∀ cv, (s0, s1) = digestScalars cv →
      ∃ (p0 p1 : E) (fs cs : List E), LoadHolds rd cpi (2 * c) p0 ∧ LoadHolds rd cpi (2 * c + 1) p1 ∧
        fs.length = 106 ∧ ReadsAt rd (cfresh * gen ^ (106 * c)) fs ∧ cs.length = 53 ∧
        ReadsAt rd (ccar * gen ^ (53 * c)) cs ∧ LoadHolds rd frow c (cfresh * gen ^ (106 * c)) ∧
        LoadHolds rd crow c (ccar * gen ^ (53 * c)) ∧
        LoadHolds rd absorb (2 * c + 2) (digestScalars (obsAll cv (p0 :: p1 :: (fs ++ cs)))).1 ∧
        LoadHolds rd absorb (2 * c + 3) (digestScalars (obsAll cv (p0 :: p1 :: (fs ++ cs)))).2) ∧
      (x * gen + N ≠ 0 →
        coreProgram.Rel rd "__loop95" [x * gen, N, absorb, cpi, cfresh, frow, ccar, crow] []) := by
  rw [rel_iff_sem find_loop95] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core566 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := hp
  rw [core566_body, l95Body] at h
  simp only [holdsList_append, holds_fsNextT] at h
  rw [holdsList_noRet (obsChainT (.n 43) (.n 44) (.n 54) 56 106) (noRetList_obsChainT ..),
    holdsList_noRet (obsChainT (.n 1644) (.n 1645) (.n 1654) 1656 53) (noRetList_obsChainT ..)] at h
  generalize hC1 : Stmt.HoldsList (coreProgram.Rel rd) rd σ (obsChainT (.n 43) (.n 44) (.n 54) 56 106)
    True (fun rs => rs = []) = C1 at h
  generalize hC2 : Stmt.HoldsList (coreProgram.Rel rd) rd σ
    (obsChainT (.n 1644) (.n 1645) (.n 1654) 1656 53) True (fun rs => rs = []) = C2 at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h8, h9, l10, l11, h12, h13, hf1, h29, hf2, h45, h46, h47, h48, h49, h50, h51, h52, h53,
    h54, h55, l54, hc1, h1646, h1647, h1648, h1649, h1650, h1651, h1652, h1653, h1654, h1655, l1654,
    hc2, l2449, l2450, c2451, h2452, h2453, c2454, h2455, -, hcall, -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h2453, h2452, c2451, p0, p1]; exact hne)
    rwa [h2455, c2454, p0, p1, p2, p3, p4, p5, p6, p7] at this
  have e9 : σ (.n 9) = absorb * gen ^ (2 * c) := by rw [h9, h8, p2, p0, hx, ← pow_add]; ring_nf
  have e13 : σ (.n 13) = cpi * gen ^ (2 * c) := by rw [h13, h12, p3, p0, hx, ← pow_add]; ring_nf
  have e29 : σ (.n 29) = cpi * gen ^ (2 * c) := by rw [h29, h12, p3, p0, hx, ← pow_add]; ring_nf
  have e53 : σ (.n 53) = gen ^ (106 * c) := by
    rw [h53, h52, h51, h50, h49, h48, h47, h46, h45, p0, hx]; ring
  have e1653 : σ (.n 1653) = gen ^ (53 * c) := by
    rw [h1653, h1652, h1651, h1650, h1649, h1648, h1647, h1646, p0, hx]; ring
  rw [e9, loadHolds_mul_gen_pow, Nat.add_zero] at l10
  rw [e9, loadHolds_mul_gen_pow] at l11
  refine ⟨σ (.n 10), σ (.n 11), l10, l11, fun cv hcv => ?_⟩
  obtain ⟨q14, s27⟩ := fsNext_out hf1 hcv
  obtain ⟨q30, s43⟩ := fsNext_out hf2 s27
  obtain ⟨fs, hfl, hfr, s1644⟩ := obsChain_sound _ _ _ _ _ _ (hC1 ▸ hc1) s43
  obtain ⟨cs, hcl, hcr, s2449⟩ := obsChain_sound _ _ _ _ _ _ (hC2 ▸ hc2) s1644
  rw [e13, loadHolds_mul_gen_pow, Nat.add_zero] at q14
  rw [e29, loadHolds_mul_gen_pow] at q30
  rw [h54, p4, e53] at hfr l54
  rw [h1654, p6, e1653] at hcr l1654
  rw [h55, p5, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l54
  rw [h1655, p7, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l1654
  have hall : obsAll cv (σ (.n 14) :: σ (.n 30) :: (fs ++ cs)) =
      obsAll (obsAll (obsCv (obsCv cv (σ (.n 14))) (σ (.n 30))) fs) cs := by
    simp [obsAll, List.foldl_append]
  rw [e9, loadHolds_mul_gen_pow] at l2449 l2450
  refine ⟨σ (.n 14), σ (.n 30), fs, cs, q14, q30, hfl, hfr, hcl, hcr, l54, l1654, ?_, ?_⟩
  · rw [hall, ← s2449]
    simpa [chainS0, show 2 * c + 2 = 2 * c + 2 by rfl] using l2449
  · rw [hall, ← s2449]
    simpa [chainS1] using l2450

set_option maxRecDepth 100000 in
theorem find_loop96 : coreProgram.find? "__loop96" = some Data.core567 :=
  Program.find?_of_indexOf? (j := 567) (by decide +kernel) rfl

/-- **`__loop96` at `x = g^c`**: from row `c` of the chain, the state of `cv`, two squeezes give
the bytecode lambdas, stored at `lam[2c]`, `lam[2c + 1]`; row `c + 1` holds the new state and the
running claim plus `λ_f` times the fresh bytecode value and `λ_c` times the carried one. -/
theorem loop96_step {N bcc lam frow crow : E} (x : E)
    (h : coreProgram.Rel rd "__loop96" [x, N, bcc, lam, frow, crow] []) :
    (∀ c, x = gen ^ c → ∃ s0 s1, LoadHolds rd bcc (3 * c) s0 ∧ LoadHolds rd bcc (3 * c + 1) s1 ∧
      ∀ cv, (s0, s1) = digestScalars cv →
      LoadHolds rd lam (2 * c) (challengeOf (sqCv cv)) ∧
      LoadHolds rd lam (2 * c + 1) (challengeOf (sqCv (sqCv cv))) ∧
      LoadHolds rd bcc (3 * c + 3) (digestScalars (sqCv (sqCv cv))).1 ∧
      LoadHolds rd bcc (3 * c + 4) (digestScalars (sqCv (sqCv cv))).2 ∧
      ∃ fp cp acc fv cv' : E, LoadHolds rd frow c fp ∧ LoadHolds rd crow c cp ∧
        LoadHolds rd bcc (3 * c + 2) acc ∧ LoadHolds rd fp 22 fv ∧ LoadHolds rd cp 22 cv' ∧
        LoadHolds rd bcc (3 * c + 5)
          (acc + challengeOf (sqCv cv) * fv + challengeOf (sqCv (sqCv cv)) * cv')) ∧
      (x * gen + N ≠ 0 → coreProgram.Rel rd "__loop96" [x * gen, N, bcc, lam, frow, crow] []) := by
  rw [rel_iff_sem find_loop96] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core567 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hp
  rw [core567_body, l96Body] at h
  simp only [holdsList_append, holds_squeezeT] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h6, h7, h8, l9, l10, hs1, hs2, h39, h40, l24, h41, l38, h42, l43, h44, l45, l30, l31,
    l46, l47, h48, h49, l50, h51, h52, l52, c53, h54, h55, c56, h57, -, hcall, -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h55, h54, c53, p0, p1]; exact hne)
    rwa [h57, c56, p0, p1, p2, p3, p4, p5] at this
  have e8 : σ (.n 8) = bcc * gen ^ (3 * c) := by rw [h8, h7, h6, p2, p0, hx]; ring
  have e40 : σ (.n 40) = lam * gen ^ (2 * c) := by rw [h40, h39, p3, p0, hx]; ring
  have e41 : σ (.n 41) = lam * gen ^ (2 * c) := by rw [h41, h39, p3, p0, hx]; ring
  rw [e8, loadHolds_mul_gen_pow, Nat.add_zero] at l9
  rw [e8, loadHolds_mul_gen_pow] at l10
  refine ⟨σ (.n 9), σ (.n 10), l9, l10, fun cv hcv => ?_⟩
  obtain ⟨q16, q24⟩ := squeeze_out hs1 hcv
  obtain ⟨q30, q38⟩ := squeeze_out hs2 q16
  simp only [Nat.reduceAdd] at q16 q24 q30 q38
  rw [e40, loadHolds_mul_gen_pow, Nat.add_zero, q24] at l24
  rw [e41, loadHolds_mul_gen_pow, q38] at l38
  rw [e8, loadHolds_mul_gen_pow] at l30 l31 l46 l52
  rw [h42, p4, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l43
  rw [h44, p5, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l45
  refine ⟨l24, l38, ?_, ?_, σ (.n 43), σ (.n 45), σ (.n 46), σ (.n 47), σ (.n 50), l43, l45,
    l46, l47, l50, ?_⟩
  · rw [show 3 * c + 3 = 3 * c + 3 by rfl, ← congrArg Prod.fst q30]; exact l30
  · rw [← congrArg Prod.snd q30]; exact l31
  · rw [h52, h51, h49, h48, q24, q38] at l52; exact l52

set_option maxRecDepth 100000 in
theorem find_loop98 : coreProgram.find? "__loop98" = some Data.core570 :=
  Program.find?_of_indexOf? (j := 570) (by decide +kernel) rfl

/-- **`__loop98` at `x = g^c`**: from row `c` of the chain, the state of `cv`, three squeezes give
the matrix lambdas, stored at `lam[3c ..]`; row `c + 1` holds the new state and the running claim
plus `λ_f` times the fresh matrix value and `λ_a`, `λ_b` times the carried values. -/
theorem loop98_step {N mcc lam frow crow : E} (x : E)
    (h : coreProgram.Rel rd "__loop98" [x, N, mcc, lam, frow, crow] []) :
    (∀ c, x = gen ^ c → ∃ s0 s1, LoadHolds rd mcc (3 * c) s0 ∧ LoadHolds rd mcc (3 * c + 1) s1 ∧
      ∀ cv, (s0, s1) = digestScalars cv →
      LoadHolds rd lam (3 * c) (challengeOf (sqCv cv)) ∧
      LoadHolds rd lam (3 * c + 1) (challengeOf (sqCv (sqCv cv))) ∧
      LoadHolds rd lam (3 * c + 2) (challengeOf (sqCv (sqCv (sqCv cv)))) ∧
      LoadHolds rd mcc (3 * c + 3) (digestScalars (sqCv (sqCv (sqCv cv)))).1 ∧
      LoadHolds rd mcc (3 * c + 4) (digestScalars (sqCv (sqCv (sqCv cv)))).2 ∧
      ∃ fp cp acc fv ca cb : E, LoadHolds rd frow c fp ∧ LoadHolds rd crow c cp ∧
        LoadHolds rd mcc (3 * c + 2) acc ∧ LoadHolds rd fp 105 fv ∧ LoadHolds rd cp 51 ca ∧
        LoadHolds rd cp 52 cb ∧
        LoadHolds rd mcc (3 * c + 5) (acc + challengeOf (sqCv cv) * fv +
          challengeOf (sqCv (sqCv cv)) * ca + challengeOf (sqCv (sqCv (sqCv cv))) * cb)) ∧
      (x * gen + N ≠ 0 → coreProgram.Rel rd "__loop98" [x * gen, N, mcc, lam, frow, crow] []) := by
  rw [rel_iff_sem find_loop98] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core570 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hp
  rw [core570_body, l98Body] at h
  simp only [holdsList_append, holds_squeezeT] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h6, h7, h8, l9, l10, hs1, hs2, hs3, h53, h54, h55, l24, h56, l38, h57, l52, h58, l59,
    h60, l61, l44, l45, l62, l63, h64, h65, l66, h67, h68, l69, h70, h71, l71, c72, h73, h74, c75,
    h76, -, hcall, -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h74, h73, c72, p0, p1]; exact hne)
    rwa [h76, c75, p0, p1, p2, p3, p4, p5] at this
  have e8 : σ (.n 8) = mcc * gen ^ (3 * c) := by rw [h8, h7, h6, p2, p0, hx]; ring
  have e55 : σ (.n 55) = lam * gen ^ (3 * c) := by rw [h55, h54, h53, p3, p0, hx]; ring
  have e56 : σ (.n 56) = lam * gen ^ (3 * c) := by rw [h56, h54, h53, p3, p0, hx]; ring
  have e57 : σ (.n 57) = lam * gen ^ (3 * c) := by rw [h57, h54, h53, p3, p0, hx]; ring
  rw [e8, loadHolds_mul_gen_pow, Nat.add_zero] at l9
  rw [e8, loadHolds_mul_gen_pow] at l10
  refine ⟨σ (.n 9), σ (.n 10), l9, l10, fun cv hcv => ?_⟩
  obtain ⟨q16, q24⟩ := squeeze_out hs1 hcv
  obtain ⟨q30, q38⟩ := squeeze_out hs2 q16
  obtain ⟨q44, q52⟩ := squeeze_out hs3 q30
  simp only [Nat.reduceAdd] at q16 q24 q30 q38 q44 q52
  rw [e55, loadHolds_mul_gen_pow, Nat.add_zero, q24] at l24
  rw [e56, loadHolds_mul_gen_pow, q38] at l38
  rw [e57, loadHolds_mul_gen_pow, q52] at l52
  rw [e8, loadHolds_mul_gen_pow] at l44 l45 l62 l71
  rw [h58, p4, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l59
  rw [h60, p5, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l61
  refine ⟨l24, l38, l52, ?_, ?_, σ (.n 59), σ (.n 61), σ (.n 62), σ (.n 63), σ (.n 66),
    σ (.n 69), l59, l61, l62, l63, l66, l69, ?_⟩
  · rw [← congrArg Prod.fst q44]; exact l44
  · rw [← congrArg Prod.snd q44]; exact l45
  · rw [h71, h70, h68, h67, h65, h64, q24, q38, q52] at l71; exact l71

/-- **A product of eq factors**, as the guest chains it from the first factor. -/
theorem eqEval_chain {f r : List E} {n : ℕ} (hf : f.length = n) (hr : r.length = n) {P : ℕ → E}
    (h0 : P 0 = 1 + f.getD 0 0 + r.getD 0 0)
    (hs : ∀ k, k + 1 < n → P (k + 1) = P k * (1 + f.getD (k + 1) 0 + r.getD (k + 1) 0)) :
    ∀ k < n, P k = eqEval (f.take (k + 1)) (r.take (k + 1)) := by
  intro k hk
  induction k with
  | zero =>
    rw [h0]
    cases f with
    | nil => simp at hf; omega
    | cons a f =>
      cases r with
      | nil => simp at hr; omega
      | cons b r =>
        simp only [List.take_succ_cons, List.take_zero, List.getD_cons_zero, eqEval,
          List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil, one_mul]
  | succ k ih =>
    rw [hs k hk, ih (by omega), eqEval_take_succ f r (k + 1) (by omega) (by omega),
      List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

set_option maxRecDepth 100000 in
theorem find_loop97 : coreProgram.find? "__loop97" = some Data.core569 :=
  Program.find?_of_indexOf? (j := 569) (by decide +kernel) rfl

/-- **`__loop97` at `x = g^c`**: the bytecode weight's row `c + 1`: the row before, plus the lambdas
times the eq products of the fresh and carried points (read through the rows' pointers) with the
batched point. -/
theorem loop97_step {N frow crow bcp wsum lam : E} (x : E)
    (h : coreProgram.Rel rd "__loop97" [x, N, frow, crow, bcp, wsum, lam] []) :
    (∀ c, x = gen ^ c → ∃ fp cp : E, LoadHolds rd frow c fp ∧ LoadHolds rd crow c cp ∧
      ∃ r f g : List E, r.length = 22 ∧ f.length = 22 ∧ g.length = 22 ∧ ReadsAt rd bcp r ∧
        ReadsAt rd fp f ∧ ReadsAt rd cp g ∧ ∃ w lf lc : E, LoadHolds rd wsum c w ∧
        LoadHolds rd lam (2 * c) lf ∧ LoadHolds rd lam (2 * c + 1) lc ∧
        LoadHolds rd wsum (c + 1) (w + lf * eqEval f r + lc * eqEval g r)) ∧
      (x * gen + N ≠ 0 →
        coreProgram.Rel rd "__loop97" [x * gen, N, frow, crow, bcp, wsum, lam] []) := by
  rw [rel_iff_sem find_loop97] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core569 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := hp
  rw [core569_body, l97Body, holdsList_append, holdsList_append,
    holdsList_range_flatten 21 (fun k => l97Coord (k + 1)) (fun _ => rfl)] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen,
    word_one] at h
  obtain ⟨h7, l8, h9, l10, l11, c12, l13, h14, h15, c16, l17, h18, h19, hM, h251, h252, l253, h254,
    l255, h256, h257, h258, l259, h260, h261, h262, l261, c263, h264, h265, c266, h267, -, hcall,
    -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h265, h264, c263, p0, p1]; exact hne)
    rwa [h267, c266, p0, p1, p2, p3, p4, p5, p6] at this
  have hC : ∀ k < 21, LoadHolds rd (σ (.n 4)) (k + 1) (σ (.n (20 + 11 * k))) ∧
      LoadHolds rd (σ (.n 8)) (k + 1) (σ (.n (20 + 11 * k + 2))) ∧
      σ (.n (25 + 11 * k)) = σ (.n (if k = 0 then 15 else 14 + 11 * k)) *
        (1 + σ (.n (20 + 11 * k + 2)) + σ (.n (20 + 11 * k))) ∧
      LoadHolds rd (σ (.n 10)) (k + 1) (σ (.n (20 + 11 * k + 7))) ∧
      σ (.n (30 + 11 * k)) = σ (.n (if k = 0 then 19 else 19 + 11 * k)) *
        (1 + σ (.n (20 + 11 * k + 7)) + σ (.n (20 + 11 * k))) := by
    intro k hk
    have := hM k hk
    simp only [l97Coord, Nat.add_sub_cancel, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one,
      Nat.add_eq_right] at this
    obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, -⟩ := this
    refine ⟨q0, q2, ?_, q7, ?_⟩
    · rw [show 25 + 11 * k = 20 + 11 * k + 5 by ring, q5, q4, q3, q1]
      rcases k with _ | k
      · rfl
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]
        congr 1; exact congrArg (fun i => σ (.n i)) (by omega)
    · rw [show 30 + 11 * k = 20 + 11 * k + 10 by ring, q10, q9, q8, q6]
      rcases k with _ | k
      · rfl
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]
        congr 1; exact congrArg (fun i => σ (.n i)) (by omega)
  let rIdx : ℕ → ℕ := fun k => if k = 0 then 11 else 20 + 11 * (k - 1)
  let fIdx : ℕ → ℕ := fun k => if k = 0 then 13 else 20 + 11 * (k - 1) + 2
  let gIdx : ℕ → ℕ := fun k => if k = 0 then 17 else 20 + 11 * (k - 1) + 7
  let r := (List.range 22).map fun k => σ (.n (rIdx k))
  let f := (List.range 22).map fun k => σ (.n (fIdx k))
  let g := (List.range 22).map fun k => σ (.n (gIdx k))
  have gd : ∀ (I : ℕ → ℕ) k, k < 22 → ((List.range 22).map fun k => σ (.n (I k))).getD k 0 =
      σ (.n (I k)) := fun I k hk => by simp [List.getD_eq_getElem?_getD, hk]
  have rdOf : ∀ (p : E) (I : ℕ → ℕ), (∀ k < 22, LoadHolds rd p k (σ (.n (I k)))) →
      ReadsAt rd p ((List.range 22).map fun k => σ (.n (I k))) := fun p I hI k hk => by
    simp only [List.length_map, List.length_range] at hk
    simpa using hI k hk
  have hF : ∀ k < 22, σ (.n (if k = 0 then 15 else 25 + 11 * (k - 1))) =
      eqEval (f.take (k + 1)) (r.take (k + 1)) := by
    refine eqEval_chain (by simp [f]) (by simp [r]) ?_ ?_
    · simp only [↓reduceIte]; rw [gd _ 0 (by omega), gd _ 0 (by omega), h15, h14, c12]; rfl
    · intro k hk
      obtain ⟨-, -, e, -⟩ := hC k (by omega)
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [gd _ _ hk, gd _ _ hk, e]
      simp only [fIdx, rIdx, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rcases k with _ | k
      · rfl
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]
        congr 1; exact congrArg (fun i => σ (.n i)) (by omega)
  have hG : ∀ k < 22, σ (.n (if k = 0 then 19 else 30 + 11 * (k - 1))) =
      eqEval (g.take (k + 1)) (r.take (k + 1)) := by
    refine eqEval_chain (by simp [g]) (by simp [r]) ?_ ?_
    · simp only [↓reduceIte]; rw [gd _ 0 (by omega), gd _ 0 (by omega), h19, h18, c16]; rfl
    · intro k hk
      obtain ⟨-, -, -, -, e⟩ := hC k (by omega)
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [gd _ _ hk, gd _ _ hk, e]
      simp only [gIdx, rIdx, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rcases k with _ | k
      · rfl
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]
        congr 1; exact congrArg (fun i => σ (.n i)) (by omega)
  have hF21 := hF 21 (by omega)
  have hG21 := hG 21 (by omega)
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at hF21 hG21
  rw [List.take_of_length_le (by simp [f]), List.take_of_length_le (by simp [r])] at hF21
  rw [List.take_of_length_le (by simp [g]), List.take_of_length_le (by simp [r])] at hG21
  rw [h7, p2, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l8
  rw [h9, p3, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l10
  refine ⟨σ (.n 8), σ (.n 10), l8, l10, r, f, g, by simp [r], by simp [f], by simp [g], ?_, ?_, ?_,
    σ (.n 253), σ (.n 255), σ (.n 259), ?_, ?_, ?_, ?_⟩
  · refine rdOf _ _ fun k hk => ?_
    rcases k with _ | k
    · simpa [rIdx, p4] using l11
    · simpa [rIdx, p4] using (hC k (by omega)).1
  · refine rdOf _ _ fun k hk => ?_
    rcases k with _ | k
    · simpa [fIdx] using l13
    · simpa [fIdx] using (hC k (by omega)).2.1
  · refine rdOf _ _ fun k hk => ?_
    rcases k with _ | k
    · simpa [gIdx] using l17
    · simpa [gIdx] using (hC k (by omega)).2.2.2.1
  · rw [h252, p5, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l253; exact l253
  · rw [h254, h251, p6, p0, hx, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero,
      show c + c = 2 * c by ring] at l255; exact l255
  · rw [h258, h251, p6, p0, hx, ← pow_add, loadHolds_mul_gen_pow,
      show c + c = 2 * c by ring] at l259; exact l259
  · rw [h262, p5, p0, hx, loadHolds_mul_gen_pow, h261, h260, h257, h256, hF21, hG21] at l261
    exact l261

end
end LeanVM.Guest.B1.Main
