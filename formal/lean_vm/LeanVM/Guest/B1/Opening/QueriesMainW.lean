/-
  LeanVM.Guest.B1.Opening.QueriesMainW

  `opening_queries` is sound with its queries named: the witness `oqsOf`, read off its frame and
  its loop's frames.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesW

/-!
# `opening_queries`, its queries named

`oqMain1_sound_w` (level 0) and `oqMain0_sound_w` (deeper, the final level among them): under a
call relation `C ≤ Rel` unfolding at `V`, a valuation holding the function's body (its loop called
at `1`, the bound `g^N`), the positions and window pointers naming positions, gives
`MeaningOpeningQueriesW` at `oqsOf … σ V`: the odd first query from the function's own frame, then
iteration `j`'s from the loop's frame `V loop (g^j :: oqLoopArgs σ) []` (`loopV_frames`). The
queries read the same rounds (`roundsAt_unique`) and final coefficients (`wordsAt_unique`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Lists of iterations -/

theorem oqLength_flatMap_range {α : Type} (f : ℕ → List α) (n : ℕ) (hf : ∀ j, (f j).length = n) :
    ∀ N, ((List.range N).flatMap f).length = n * N
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, oqLength_flatMap_range f n hf N]
    simp [hf, Nat.mul_succ]

theorem oqGetD_flatMap_range {α : Type} (f : ℕ → List α) (n : ℕ) (hf : ∀ j, (f j).length = n)
    (d : α) : ∀ (N j e : ℕ), j < N → e < n →
      ((List.range N).flatMap f).getD (n * j + e) d = (f j).getD e d
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | N + 1, j, e, hj, he => by
    rw [List.range_succ, List.flatMap_append]
    have hl := oqLength_flatMap_range f n hf N
    rcases Nat.lt_or_ge j N with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hl]; nlinarith)]
      exact oqGetD_flatMap_range f n hf d N j e h he
    · obtain rfl : j = N := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega)]
      simp [hl]

/-! ## The queries read the same words -/

theorem roundsAt_unique {c : E} {r1 r2 : List FoldRound} (h1 : RoundsAt rd c r1)
    (h2 : RoundsAt rd c r2) (hl : r1.length = r2.length) : r1 = r2 := by
  apply List.ext_getElem hl
  intro j hj1 hj2
  obtain ⟨a1, b1, t1⟩ := h1 j hj1
  obtain ⟨a2, b2, t2⟩ := h2 j hj2
  rw [List.getD_eq_getElem _ _ hj1] at a1 b1 t1
  rw [List.getD_eq_getElem _ _ hj2] at a2 b2 t2
  have e1 := loadHolds_unique a1 a2
  have e2 := loadHolds_unique b1 b2
  have e3 := loadHolds_unique t1 t2
  generalize r1[j] = x at *
  generalize r2[j] = y at *
  cases x; cases y
  simp_all

theorem wordsAt_unique {p : E} {x1 x2 : List E} (h1 : WordsAt rd p x1) (h2 : WordsAt rd p x2)
    (hl : x1.length = x2.length) : x1 = x2 := by
  apply List.ext_getElem hl
  intro j hj1 hj2
  have := loadHolds_unique (h1 j hj1) (h2 j hj2)
  rwa [List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ hj2] at this

/-! ## The function's tail -/

/-- The function's call of its loop and its tail: the call, and the returned words: the chain's
`N`-th word at a non-final level, `0` at the final level. -/
theorem oqMain_tail {C : CallRel} {s : Oq} {odd : ℕ} {walk loop : String} {rets : List E}
    (h : Stmt.HoldsList C rd σ (oqMainT s odd walk loop) False (fun rs ↦ rs = rets)) :
    BlockOkC C rd σ (oqMainA s odd walk) ∧
      (σ (.n (oqMK s odd + 1)) ≠ 0 → C loop [σ (.n (oqMK s odd + 2)), σ (.n 7), σ (.n 5), σ (.n 6),
        σ (.n 0), σ (.n 1), σ (.n 3), σ (.n 4), σ (.n 10), σ (.n 2)] []) ∧
      (s.final = 1 → rets = [0]) ∧
      (s.final ≠ 1 → ∃ v, LoadHolds rd (σ (.n 10) * σ (.n 7)) 0 v ∧ rets = [v]) := by
  rw [oqMainT, holdsList_append, holdsList_append, holdsList_flatC (oqMainA_flatC s odd walk)] at h
  obtain ⟨hA, h⟩ := h
  rw [Stmt.HoldsList, Stmt.Holds, Stmt.HoldsList] at h
  obtain ⟨-, hcall, h⟩ := h
  refine ⟨hA, fun hne ↦ by simpa using hcall hne, fun hf ↦ ?_, fun hf ↦ ?_⟩
  · simp only [hf, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
    rw [← h.2, h.1, word_zero]
  · simp only [hf, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
    obtain ⟨e3, e4, e5, hret⟩ := h
    refine ⟨σ (.n (oqMK s odd + 4)), ?_, by rw [← hret, e5]⟩
    rw [← e3]; exact e4

/-! ## Deeper levels -/

theorem oqChain_succ_zero {base : ℕ} (hb : base = 0) (mu : E) (ds : ℕ → E) (i : ℕ) :
    oqChain 0 base mu ds (i + 1) = (oqChain 0 base mu ds i + ds i) * mu := by
  simp [oqChain, hb]

theorem oqsOf_length_zero {s : Oq} (hb0 : s.base = 0) (loop : String) (N : ℕ) (rd : Reader)
    (σ : Val) (V : FrameMap) : (oqsOf s 0 loop N rd σ V).length = N := by
  unfold oqsOf
  rw [List.length_append, oqLength_flatMap_range _ 1 (fun j => by simp [oqIterOf, hb0])]
  simp

/-- **`opening_queries` deeper is sound with its queries named** (`base = 0`, `odd = 0`; the final
level among them). -/
theorem oqMain0_sound_w {sh : OqShape} (hs : sh.oq.RowShape) (hfin : sh.oq.FinOk)
    (hb0 : sh.base = 0) (hodd : sh.odd = 0) (hpd : 1 ≤ sh.oq.pd) (hcd : 1 ≤ sh.cd)
    (hcd8 : sh.cd ≤ 8) (hdep : sh.cd ≤ sh.depth) {name loop : String}
    (hW : WalkFn (oqWalkOf sh.oq) sh.oq.pd sh.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT sh.oq 0 (oqWalkOf sh.oq) loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T sh.oq (oqWalkOf sh.oq) loop) :
    opening_queries_sound_w_Spec name loop sh := by
  intro rd C V hU _ fm' σ args rets N hfm' hp hh hN hNo hpos
  rw [hfm] at hfm'
  cases hfm'
  rw [hpm] at hp
  simp only [List.map_cons, List.map_nil] at hp
  subst hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hN hpos
  rw [hodd]
  set s := sh.oq with hsdef
  have hsb : s.base = 0 := hb0
  have hsc : s.cd = sh.cd := rfl
  have es : s.pd + s.cd = sh.depth := by simp only [hsdef, OqShape.oq]; omega
  have hQ : oqCount sh.odd sh.base N = N := by simp [oqCount, hb0]
  rw [hQ] at hpos
  rw [hbm] at hh
  obtain ⟨hA, hcall, hfin1, hfin0⟩ := oqMain_tail hh
  obtain ⟨hg, hst, h0even⟩ := oqMainA_basic hA
  -- the iterations' frames
  have hfr := loopV_frames (rd := rd) hU hfl (by rw [hbl]; rfl) (oqLoop0A_flatC s (oqWalkOf s))
    (Nv := σ (.n 7)) (rest := [σ (.n 5), σ (.n 6), σ (.n 0), σ (.n 1), σ (.n 3), σ (.n 4), σ (.n 10),
      σ (.n 2)])
    (fun τ x hp hA => oqLoop0_hc hpl τ x hp hA) hN hNo (fun hN0 => by
      have hne : σ (.n (oqMK s 0 + 1)) ≠ 0 := by
        rw [hg, hN]
        intro h0
        have := (gen_pow_eq_one_iff hNo).mp (e_add_eq_zero_iff.mp h0).symm
        omega
      have := hcall hne
      rwa [hst] at this)
  set τ : ℕ → Val := fun j => V loop [gen ^ j, σ (.n 7), σ (.n 5), σ (.n 6), σ (.n 0), σ (.n 1),
    σ (.n 3), σ (.n 4), σ (.n 10), σ (.n 2)] [] with hτ
  have hit : ∀ j < N,
      LoadHolds rd (σ (.n 5)) j (τ j (.n 11)) ∧ LoadHolds rd (σ (.n 6)) j (τ j (.n 13)) ∧
      (∃ w, w = oqQueryW s rd (τ j (.n 13)) (τ j (.n 4)) (τ j (.n 5)) 14 true (τ j) V ∧
        QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 3)) (σ (.n 4)) (τ j (.n 11)) (τ j (.n 13)) w
          (τ j (.n (oqRes s 14 true)))) ∧
      (s.final ≠ 1 → ∃ v : E, LoadHolds rd (σ (.n 10)) j v ∧
        LoadHolds rd (σ (.n 10)) (j + 1) ((v + τ j (.n (oqRes s 14 true))) * σ (.n 2))) := by
    intro j hj
    obtain ⟨hp, hA⟩ := hfr j hj
    obtain ⟨t0, hps⟩ := loop_params hpl hp
    simp only [List.cons.injEq] at hps
    obtain ⟨-, t2, t3, t4, t5, t6, t7, t8, t9, -⟩ := hps
    have := oqIter0_sound_w hU hs hfin hpd hcd hcd8 hW (i := j) hA t0 (fun x bp hx hbp => by
      rw [← t2] at hx
      rw [← t3] at hbp
      obtain ⟨q, hq, hxq, hfrq⟩ := hpos j hj x bp hx hbp
      exact ⟨q, by rw [es]; exact hq, hxq, by rw [es]; exact hfrq⟩)
    obtain ⟨a1, a2, a3, a4⟩ := this
    generalize hw : oqQueryW s rd (τ j (.n 13)) (τ j (.n 4)) (τ j (.n 5)) 14 true (τ j) V = w at a3
    rw [← t2] at a1
    rw [← t3] at a2
    rw [← t4, ← t5, ← t6, ← t7] at a3
    rw [← t8, ← t9] at a4
    exact ⟨a1, a2, ⟨w, rfl, a3⟩, a4⟩
  -- the witness
  set ws := oqsOf s 0 loop N rd σ V with hws
  have hwsI : ∀ j < N, ws.getD j default =
      oqQueryW s rd (τ j (.n 13)) (τ j (.n 4)) (τ j (.n 5)) 14 true (τ j) V := by
    intro j hj
    simp only [hws, oqsOf, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.nil_append]
    have := oqGetD_flatMap_range (fun j => oqIterOf s rd (V loop (gen ^ j :: oqLoopArgs σ) []) V) 1
      (fun j => by simp [oqIterOf, hsb]) default N j 0 hj (by omega)
    rw [Nat.one_mul, Nat.add_zero] at this
    rw [this]
    simp [oqIterOf, hsb, hτ, oqLoopArgs]
  have hQW : ∀ j < N, QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 3)) (σ (.n 4)) (τ j (.n 11))
      (τ j (.n 13)) (ws.getD j default) (τ j (.n (oqRes s 14 true))) := fun j hj ↦ by
    obtain ⟨w, hw, h⟩ := (hit j hj).2.2.1
    rw [hwsI j hj, ← hw]; exact h
  -- the rounds and the final coefficients, shared
  have hR : ∀ j < N, ∃ rounds : List FoldRound, rounds.length = s.folds ∧
      RoundsAt rd (σ (.n 3)) rounds ∧ FoldsNonzero rounds (K.ofBits (ws.getD j default).1) ∧
      (s.final ≠ 1 → τ j (.n (oqRes s 14 true)) = qwFold s.base rounds (ws.getD j default)) ∧
      (s.final = 1 → ∃ hsv : List E, hsv.length = s.nHs ∧ WordsAt rd (σ (.n 4)) hsv ∧
        qwFold s.base rounds (ws.getD j default) =
          novelSum hsv (wsChain (s.vs.map K.ofBits) (τ j (.n 11))) s.nHs s.hsBits) :=
    fun j hj ↦ (hQW j hj).2.2.2.2
  choose! rr hrr using hR
  let rounds : List FoldRound := if N = 0 then List.replicate s.folds ⟨0, 0, 0⟩ else rr 0
  have hrl : rounds.length = s.folds := by
    by_cases h0 : N = 0
    · simp [rounds, h0]
    · simp only [rounds, h0, ↓reduceIte]; exact (hrr 0 (by omega)).1
  have hrj : ∀ j < N, rr j = rounds := fun j hj ↦ by
    have h0 : N ≠ 0 := by omega
    simp only [rounds, h0, ↓reduceIte]
    exact roundsAt_unique (hrr j hj).2.1 (hrr 0 (by omega)).2.1 (by rw [(hrr j hj).1, (hrr 0 (by omega)).1])
  have hH : ∀ j < N, ∃ hsv : List E, s.final = 1 → hsv.length = s.nHs ∧ WordsAt rd (σ (.n 4)) hsv ∧
      qwFold s.base rounds (ws.getD j default) =
        novelSum hsv (wsChain (s.vs.map K.ofBits) (τ j (.n 11))) s.nHs s.hsBits := fun j hj ↦ by
    by_cases hf : s.final = 1
    · obtain ⟨hsv, h1, h2, h3⟩ := (hrr j hj).2.2.2.2 hf
      exact ⟨hsv, fun _ ↦ ⟨h1, h2, by rw [← hrj j hj]; exact h3⟩⟩
    · exact ⟨[], fun h ↦ absurd h hf⟩
  choose! hh hhh using hH
  let hsv : List E := if N = 0 ∨ s.final ≠ 1 then List.replicate s.nHs 0 else hh 0
  have hhl : hsv.length = s.nHs := by
    by_cases h0 : N = 0 ∨ s.final ≠ 1
    · simp [hsv, h0]
    · simp only [hsv, h0, ↓reduceIte]; exact (hhh 0 (by omega) (by omega)).1
  have hhj : ∀ j < N, s.final = 1 → hh j = hsv := fun j hj hf ↦ by
    have h0 : ¬ (N = 0 ∨ s.final ≠ 1) := by omega
    simp only [hsv, h0, ↓reduceIte]
    exact wordsAt_unique (hhh j hj hf).2.1 (hhh 0 (by omega) hf).2.1
      (by rw [(hhh j hj hf).1, (hhh 0 (by omega) hf).1])
  -- the chain
  have hds : ∀ j < N, s.final ≠ 1 → τ j (.n (oqRes s 14 true)) = qwFold s.base rounds (ws.getD j default) :=
    fun j hj hf ↦ by rw [(hrr j hj).2.2.2.1 hf, hrj j hj]
  refine ⟨N, hNo, hN, by rw [hQ, oqsOf_length_zero hsb], rounds, hsv, hrl, hhl, fun k hk ↦ ?_, ?_⟩
  · rw [hQ] at hk
    obtain ⟨l5, l6, hq⟩ := hit k hk
    obtain ⟨q1, q2, q3, q4, -⟩ := hQW k hk
    obtain ⟨-, hRA, hNZ, -, -⟩ := hrr k hk
    rw [hrj k hk] at hRA hNZ
    refine ⟨hRA, fun hf ↦ ?_, by rw [← q2]; exact l5, by rw [← es]; exact q1,
      ⟨τ k (.n 13), l6, by rw [← es]; exact q3⟩, by rw [← es]; exact q4, hNZ, fun hf ↦ ?_⟩
    · rw [← hhj k hk hf]; exact (hhh k hk hf).2.1
    · have := (hhh k hk hf).2.2
      rw [hhj k hk hf, q2] at this
      exact this
  · by_cases hf : sh.final = 1
    · simp only [hf, ↓reduceIte]; exact hfin1 hf
    · simp only [hf, ↓reduceIte]
      rw [hodd]
      have hchain : ∀ i ≤ N, LoadHolds rd (σ (.n 10)) i
          (oqChain 0 sh.base (σ (.n 2)) (fun k ↦ qwFold sh.base rounds (ws.getD k default)) i) := by
        intro i hi
        induction i with
        | zero =>
          simp only [oqChain, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
          exact h0even (by decide)
        | succ i ih =>
          obtain ⟨v, hv, hv1⟩ := (hit i (by omega)).2.2.2 hf
          have e := loadHolds_unique hv (ih (by omega))
          rw [e, hds i (by omega) hf] at hv1
          rw [oqChain_succ_zero hb0]
          exact hv1
      obtain ⟨v, hv, hret⟩ := hfin0 hf
      rw [hN, loadHolds_mul_gen_pow, Nat.add_zero] at hv
      exact ⟨σ (.n 10), hchain, by rw [hret, loadHolds_unique hv (hchain N le_rfl)]⟩

end
end LeanVM.Guest.B1
