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

variable {P : Program} {rd : Reader} {σ : Val}

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
  obtain ⟨a1, b1⟩ := h1 j hj1
  obtain ⟨a2, b2⟩ := h2 j hj2
  rw [List.getD_eq_getElem _ _ hj1] at a1 b1
  rw [List.getD_eq_getElem _ _ hj2] at a2 b2
  have e1 := loadHolds_unique a1 a2
  have e2 := loadHolds_unique b1 b2
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
    (hW : WalkFn P (oqWalkOf sh.oq) sh.oq.pd sh.cd) {fm fl : Fn}
    (hfm : P.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT sh.oq 0 (oqWalkOf sh.oq) loop)
    (hfl : P.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T sh.oq (oqWalkOf sh.oq) loop) :
    opening_queries_sound_w_SpecP P name loop sh := by
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
      RoundsAt rd (σ (.n 3)) rounds ∧
      (s.final ≠ 1 → τ j (.n (oqRes s 14 true)) = qwFold s.base rounds (ws.getD j default)) ∧
      (s.final = 1 → ∃ hsv : List E, hsv.length = s.nHs ∧ WordsAt rd (σ (.n 4)) hsv ∧
        qwFold s.base rounds (ws.getD j default) =
          novelSum hsv (wsChain (s.vs.map K.ofBits) (τ j (.n 11))) s.nHs s.hsBits) :=
    fun j hj ↦ (hQW j hj).2.2.2.2
  choose! rr hrr using hR
  let rounds : List FoldRound := if N = 0 then List.replicate s.folds ⟨0, 0⟩ else rr 0
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
    · obtain ⟨hsv, h1, h2, h3⟩ := (hrr j hj).2.2.2 hf
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
    fun j hj hf ↦ by rw [(hrr j hj).2.2.1 hf, hrj j hj]
  refine ⟨N, hNo, hN, by rw [hQ, oqsOf_length_zero hsb], rounds, hsv, hrl, hhl, fun k hk ↦ ?_, ?_⟩
  · rw [hQ] at hk
    obtain ⟨l5, l6, hq⟩ := hit k hk
    obtain ⟨q1, q2, q3, q4, -⟩ := hQW k hk
    obtain ⟨-, hRA, -, -⟩ := hrr k hk
    rw [hrj k hk] at hRA
    refine ⟨hRA, fun hf ↦ ?_, by rw [← q2]; exact l5, by rw [← es]; exact q1,
      ⟨τ k (.n 13), l6, by rw [← es]; exact q3⟩, by rw [← es]; exact q4, fun hf ↦ ?_⟩
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

/-! ## Level 0 -/

theorem oqChain_succ_one {odd base : ℕ} (hb : base = 1) (mu : E) (ds : ℕ → E) (i : ℕ) :
    oqChain odd base mu ds (i + 1) =
      ((oqChain odd base mu ds i + ds (odd + 2 * i)) * mu + ds (odd + 2 * i + 1)) * mu := by
  simp [oqChain, hb]

theorem oqsOf_length_one {s : Oq} (hb1 : s.base = 1) {odd : ℕ} (hodd : odd ≤ 1) (loop : String)
    (N : ℕ) (rd : Reader) (σ : Val) (V : FrameMap) :
    (oqsOf s odd loop N rd σ V).length = odd + 2 * N := by
  unfold oqsOf
  rw [List.length_append, oqLength_flatMap_range _ 2 (fun j => by simp [oqIterOf, hb1])]
  split_ifs with h <;> simp <;> omega

/-- The odd first query of the function's start, and the chain's first word, its result times
`λ⁻¹`. -/
theorem oqMainA_odd_w {C : CallRel} {V : FrameMap} (hU : UnfoldsVP P rd C V) {s : Oq}
    (hs : s.RowShape) (hfin : s.FinOk) (hpd : 1 ≤ s.pd) (hcd : 1 ≤ s.cd) (hcd8 : s.cd ≤ 8)
    (hW : WalkFn P (oqWalkOf s) s.pd s.cd) (hA : BlockOkC C rd σ (oqMainA s 1 (oqWalkOf s)))
    (hpos : ∀ x bp, LoadHolds rd (σ (.n 5)) 0 x → LoadHolds rd (σ (.n 6)) 0 bp → PosRun rd s x bp) :
    LoadHolds rd (σ (.n 5)) 0 (σ (.n 11)) ∧ LoadHolds rd (σ (.n 6)) 0 (σ (.n 12)) ∧
      QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 3)) (σ (.n 4)) (σ (.n 11)) (σ (.n 12))
        (oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V) (σ (.n (oqRes s 13 true))) ∧
      LoadHolds rd (σ (.n 10)) 0 (σ (.n (oqRes s 13 true)) * σ (.n 2)) := by
  have mem : BlockOkC C rd σ (oqQueryT s (.n 11) (.n 12) (.n 0) (.n 1) (.n 3) (.n 4) 13 true 0 (oqWalkOf s)) :=
    hA.mono fun a ha => by simp only [oqMainA, ↓reduceIte, List.mem_append]; simp_all
  have l11 := hA.atom (by simp [oqMainA] : Stmt.atom (.load (.n 11) (.n 5) 0) ∈ _)
  have l12 := hA.atom (by simp [oqMainA] : Stmt.atom (.load (.n 12) (.n 6) 0) ∈ _)
  have c1 := hA.atom (by simp [oqMainA] :
    Stmt.atom (.mul (.n (oqMK s 1 - 1)) (.n (oqRes s 13 true)) (.n 2)) ∈ _)
  have c2 := hA.atom (by simp [oqMainA] : Stmt.atom (.load (.n (oqMK s 1 - 1)) (.n 10) 0) ∈ _)
  simp only [Atom.Holds] at c1 l11 l12
  obtain ⟨-, hpd', -, -, -, -⟩ := oqQuery_pieces mem
  obtain ⟨e1, z⟩ := oqPad_values (hpd' rfl)
  refine ⟨l11, l12, oqQuery_sound_w hU hs hfin hpd hcd hcd8 hW mem e1 z (hpos _ _ l11 l12), ?_⟩
  have := c2
  simp only [Atom.Holds, c1] at this
  exact this

/-- **`opening_queries` at level 0 is sound with its queries named** (`base = 1`, a non-final
level). -/
theorem oqMain1_sound_w {sh : OqShape} (hs : sh.oq.RowShape) (hfin : sh.oq.FinOk)
    (hb1 : sh.base = 1) (hnf : sh.final = 0) (hodd : sh.odd ≤ 1) (hpd : 1 ≤ sh.oq.pd)
    (hcd : 1 ≤ sh.cd) (hcd8 : sh.cd ≤ 8) (hdep : sh.cd ≤ sh.depth) {name loop : String}
    (hW : WalkFn P (oqWalkOf sh.oq) sh.oq.pd sh.cd) {fm fl : Fn}
    (hfm : P.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT sh.oq sh.odd (oqWalkOf sh.oq) loop)
    (hfl : P.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T sh.oq sh.odd (oqWalkOf sh.oq) loop) :
    opening_queries_sound_w_SpecP P name loop sh := by
  intro rd C V hU _ fm' σ args rets N hfm' hp hh hN hNo hpos
  rw [hfm] at hfm'
  cases hfm'
  rw [hpm] at hp
  simp only [List.map_cons, List.map_nil] at hp
  subst hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hN hpos
  set odd := sh.odd with hoddv
  set s := sh.oq with hsdef
  have hsb : s.base = 1 := hb1
  have es : s.pd + s.cd = sh.depth := by simp only [hsdef, OqShape.oq]; omega
  have hQ : oqCount odd sh.base N = odd + 2 * N := by simp [oqCount, hb1]
  rw [hQ] at hpos
  have hpos' : ∀ k < odd + 2 * N, ∀ x bp, LoadHolds rd (σ (.n 5)) k x → LoadHolds rd (σ (.n 6)) k bp →
      PosRun rd s x bp := fun k hk x bp hx hbp ↦ by
    obtain ⟨q, hq, hxq, hfrq⟩ := hpos k hk x bp hx hbp
    exact ⟨q, by rw [es]; exact hq, hxq, by rw [es]; exact hfrq⟩
  rw [hbm] at hh
  obtain ⟨hA, hcall, -, hfin0⟩ := oqMain_tail hh
  obtain ⟨hg, hst, h0even⟩ := oqMainA_basic hA
  have hfr := loopV_frames (rd := rd) hU hfl (by rw [hbl]; rfl) (oqLoop1A_flatC s odd (oqWalkOf s))
    (Nv := σ (.n 7)) (rest := [σ (.n 5), σ (.n 6), σ (.n 0), σ (.n 1), σ (.n 3), σ (.n 4), σ (.n 10),
      σ (.n 2)])
    (fun τ x hp hA => oqLoop1_hc hpl τ x hp hA) hN hNo (fun hN0 => by
      have hne : σ (.n (oqMK s odd + 1)) ≠ 0 := by
        rw [hg, hN]
        intro h0
        have := (gen_pow_eq_one_iff hNo).mp (e_add_eq_zero_iff.mp h0).symm
        omega
      have := hcall hne
      rwa [hst] at this)
  set τ : ℕ → Val := fun j => V loop [gen ^ j, σ (.n 7), σ (.n 5), σ (.n 6), σ (.n 0), σ (.n 1),
    σ (.n 3), σ (.n 4), σ (.n 10), σ (.n 2)] [] with hτ
  -- the queries of an iteration
  have hit : ∀ j < N,
      LoadHolds rd (σ (.n 5)) (2 * j + odd) (τ j (.n 14)) ∧
      LoadHolds rd (σ (.n 6)) (2 * j + odd) (τ j (.n 15)) ∧
      (∃ w, w = oqQueryW s rd (τ j (.n 15)) (τ j (.n 4)) (τ j (.n 5)) 16 true (τ j) V ∧
        QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 3)) (σ (.n 4)) (τ j (.n 14)) (τ j (.n 15)) w
          (τ j (.n (oqRes s 16 true)))) ∧
      LoadHolds rd (σ (.n 5)) (2 * j + odd + 1) (τ j (.n (oqE1 s))) ∧
      LoadHolds rd (σ (.n 6)) (2 * j + odd + 1) (τ j (.n (oqE1 s + 1))) ∧
      (∃ w, w = oqQueryW s rd (τ j (.n (oqE1 s + 1))) (τ j (.n 4)) (τ j (.n 5)) (oqE1 s + 2) false
          (τ j) V ∧
        QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 3)) (σ (.n 4)) (τ j (.n (oqE1 s)))
          (τ j (.n (oqE1 s + 1))) w (τ j (.n (oqRes s (oqE1 s + 2) false)))) ∧
      ∃ v : E, LoadHolds rd (σ (.n 10)) j v ∧
        LoadHolds rd (σ (.n 10)) (j + 1) (((v + τ j (.n (oqRes s 16 true))) * σ (.n 2) +
          τ j (.n (oqRes s (oqE1 s + 2) false))) * σ (.n 2)) := by
    intro j hj
    obtain ⟨hp, hA⟩ := hfr j hj
    obtain ⟨t0, hps⟩ := loop_params hpl hp
    simp only [List.cons.injEq] at hps
    obtain ⟨-, t2, t3, t4, t5, t6, t7, t8, t9, -⟩ := hps
    have := oqIter1_sound_w hU hs hfin hpd hcd hcd8 hW (odd := odd) (i := j) hA t0
      (fun k hk x bp hx hbp => by
        rw [← t2] at hx
        rw [← t3] at hbp
        exact hpos' k (by omega) x bp hx hbp)
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := this
    generalize hw1 : oqQueryW s rd (τ j (.n 15)) (τ j (.n 4)) (τ j (.n 5)) 16 true (τ j) V = w1 at a3
    generalize hw2 : oqQueryW s rd (τ j (.n (oqE1 s + 1))) (τ j (.n 4)) (τ j (.n 5)) (oqE1 s + 2) false
      (τ j) V = w2 at a6
    rw [← t2] at a1 a4
    rw [← t3] at a2 a5
    rw [← t4, ← t5, ← t6, ← t7] at a3 a6
    obtain ⟨v, b1, b2⟩ := a7 (by show sh.final ≠ 1; omega)
    rw [← t8] at b1 b2
    rw [← t9] at b2
    exact ⟨a1, a2, ⟨w1, rfl, a3⟩, a4, a5, ⟨w2, rfl, a6⟩, v, b1, b2⟩
  -- the odd first query
  have hM : odd = 1 → LoadHolds rd (σ (.n 5)) 0 (σ (.n 11)) ∧ LoadHolds rd (σ (.n 6)) 0 (σ (.n 12)) ∧
      QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 3)) (σ (.n 4)) (σ (.n 11)) (σ (.n 12))
        (oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V) (σ (.n (oqRes s 13 true))) ∧
      LoadHolds rd (σ (.n 10)) 0 (σ (.n (oqRes s 13 true)) * σ (.n 2)) := by
    intro h1
    have hA' : BlockOkC C rd σ (oqMainA s 1 (oqWalkOf s)) := by rw [← h1]; exact hA
    exact oqMainA_odd_w hU hs hfin hpd hcd hcd8 hW hA' (fun x bp hx hbp ↦ hpos' 0 (by omega) x bp hx hbp)
  -- the witness, by index
  set ws := oqsOf s odd loop N rd σ V with hws
  have hwsM : odd = 1 → ws.getD 0 default = oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V := by
    intro h1; simp [hws, oqsOf, h1]
  have hwsI : ∀ j < N, ∀ e < 2, ws.getD (odd + (2 * j + e)) default =
      (oqIterOf s rd (τ j) V).getD e default := by
    intro j hj e he
    have hl : (if odd = 1 then [oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V] else []).length =
        odd := by
      split_ifs with h <;> simp <;> omega
    simp only [hws, oqsOf]
    rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]
    rw [oqGetD_flatMap_range _ 2 (fun j => by simp [oqIterOf, hsb]) default N j e hj he]
    simp [hτ, oqLoopArgs]
  have hiter : ∀ j < N, oqIterOf s rd (τ j) V =
      [oqQueryW s rd (τ j (.n 15)) (τ j (.n 4)) (τ j (.n 5)) 16 true (τ j) V,
        oqQueryW s rd (τ j (.n (oqE1 s + 1))) (τ j (.n 4)) (τ j (.n 5)) (oqE1 s + 2) false (τ j) V] :=
    fun j _ ↦ by simp [oqIterOf, hsb]
  -- every query, by index
  let dOf : ℕ → E := fun k ↦ if k < odd then σ (.n (oqRes s 13 true))
    else if (k - odd) % 2 = 0 then τ ((k - odd) / 2) (.n (oqRes s 16 true))
    else τ ((k - odd) / 2) (.n (oqRes s (oqE1 s + 2) false))
  have hQW : ∀ k < odd + 2 * N, ∃ x bp : E, LoadHolds rd (σ (.n 5)) k x ∧ LoadHolds rd (σ (.n 6)) k bp ∧
      QueryW rd s (σ (.n 0)) (σ (.n 1)) (σ (.n 3)) (σ (.n 4)) x bp (ws.getD k default) (dOf k) := by
    intro k hk
    by_cases hk0 : k < odd
    · have h1 : odd = 1 := by omega
      obtain rfl : k = 0 := by omega
      obtain ⟨a1, a2, a3, -⟩ := hM h1
      refine ⟨_, _, a1, a2, ?_⟩
      rw [hwsM h1]
      simpa [dOf, hk0] using a3
    · obtain ⟨j, hj, e, he, rfl⟩ : ∃ j < N, ∃ e < 2, k = odd + (2 * j + e) :=
        ⟨(k - odd) / 2, by omega, (k - odd) % 2, by omega, by omega⟩
      obtain ⟨a1, a2, ⟨w1, hw1, a3⟩, a4, a5, ⟨w2, hw2, a6⟩, -⟩ := hit j hj
      rw [hwsI j hj e he, hiter j hj]
      interval_cases e
      · refine ⟨_, _, by rw [show odd + (2 * j + 0) = 2 * j + odd by omega]; exact a1,
          by rw [show odd + (2 * j + 0) = 2 * j + odd by omega]; exact a2, ?_⟩
        have hd : dOf (odd + (2 * j + 0)) = τ j (.n (oqRes s 16 true)) := by
          simp only [dOf, show ¬ odd + (2 * j + 0) < odd by omega, ↓reduceIte,
            show (odd + (2 * j + 0) - odd) % 2 = 0 by omega, show (odd + (2 * j + 0) - odd) / 2 = j by omega]
        rw [hd, List.getD_cons_zero, ← hw1]; exact a3
      · refine ⟨_, _, by rw [show odd + (2 * j + 1) = 2 * j + odd + 1 by omega]; exact a4,
          by rw [show odd + (2 * j + 1) = 2 * j + odd + 1 by omega]; exact a5, ?_⟩
        have hd : dOf (odd + (2 * j + 1)) = τ j (.n (oqRes s (oqE1 s + 2) false)) := by
          simp only [dOf, show ¬ odd + (2 * j + 1) < odd by omega, ↓reduceIte,
            show (odd + (2 * j + 1) - odd) % 2 = 1 by omega, show (odd + (2 * j + 1) - odd) / 2 = j by omega,
            show (1 : ℕ) ≠ 0 by decide]
        rw [hd, List.getD_cons_succ, List.getD_cons_zero, ← hw2]; exact a6
  -- the rounds, shared
  have hR : ∀ k < odd + 2 * N, ∃ rounds : List FoldRound, rounds.length = s.folds ∧
      RoundsAt rd (σ (.n 3)) rounds ∧
      dOf k = qwFold s.base rounds (ws.getD k default) := fun k hk ↦ by
    obtain ⟨x, bp, -, -, -, -, -, -, rounds, h1, h2, h4, -⟩ := hQW k hk
    exact ⟨rounds, h1, h2, h4 (by simp [hsdef, OqShape.oq, hnf])⟩
  choose! rr hrr using hR
  let rounds : List FoldRound := if odd + 2 * N = 0 then List.replicate s.folds ⟨0, 0⟩ else rr 0
  have hrl : rounds.length = s.folds := by
    by_cases h0 : odd + 2 * N = 0
    · simp [rounds, h0]
    · simp only [rounds, h0, ↓reduceIte]; exact (hrr 0 (by omega)).1
  have hrj : ∀ k < odd + 2 * N, rr k = rounds := fun k hk ↦ by
    have h0 : odd + 2 * N ≠ 0 := by omega
    simp only [rounds, h0, ↓reduceIte]
    exact roundsAt_unique (hrr k hk).2.1 (hrr 0 (by omega)).2.1 (by rw [(hrr k hk).1, (hrr 0 (by omega)).1])
  have hds : ∀ k < odd + 2 * N, dOf k = qwFold sh.base rounds (ws.getD k default) := fun k hk ↦ by
    rw [(hrr k hk).2.2, hrj k hk]; rfl
  refine ⟨N, hNo, hN, by rw [hQ, oqsOf_length_one hsb hodd], rounds, List.replicate sh.nHs 0, hrl,
    by simp, fun k hk ↦ ?_, ?_⟩
  · rw [hQ] at hk
    obtain ⟨x, bp, l5, l6, q1, q2, q3, q4, -⟩ := hQW k hk
    obtain ⟨-, hRA, -⟩ := hrr k hk
    rw [hrj k hk] at hRA
    refine ⟨hRA, fun hf ↦ absurd hf (by omega), by rw [← q2]; exact l5, by rw [← es]; exact q1,
      ⟨bp, l6, by rw [← es]; exact q3⟩, by rw [← es]; exact q4, fun hf ↦ absurd hf (by omega)⟩
  · simp only [hnf, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
    have hchain : ∀ i ≤ N, LoadHolds rd (σ (.n 10)) i
        (oqChain odd sh.base (σ (.n 2)) (fun k ↦ qwFold sh.base rounds (ws.getD k default)) i) := by
      intro i hi
      induction i with
      | zero =>
        by_cases h1 : odd = 1
        · have := (hM h1).2.2.2
          simp only [oqChain, h1, ↓reduceIte]
          rw [← hds 0 (by omega)]
          simpa [dOf, h1] using this
        · simp only [oqChain, h1, ↓reduceIte]
          exact h0even h1
      | succ i ih =>
        obtain ⟨-, -, -, -, -, -, v, hv, hv1⟩ := hit i (by omega)
        have e := loadHolds_unique hv (ih (by omega))
        have d0 : dOf (odd + 2 * i) = τ i (.n (oqRes s 16 true)) := by
          simp only [dOf, show ¬ odd + 2 * i < odd by omega, ↓reduceIte,
            show (odd + 2 * i - odd) % 2 = 0 by omega, show (odd + 2 * i - odd) / 2 = i by omega]
        have d1 : dOf (odd + 2 * i + 1) = τ i (.n (oqRes s (oqE1 s + 2) false)) := by
          simp only [dOf, show ¬ odd + 2 * i + 1 < odd by omega, ↓reduceIte,
            show (odd + 2 * i + 1 - odd) % 2 = 1 by omega, show (odd + 2 * i + 1 - odd) / 2 = i by omega,
            show (1 : ℕ) ≠ 0 by decide]
        rw [e, ← d0, ← d1, hds _ (by omega), hds _ (by omega)] at hv1
        rw [oqChain_succ_one hb1]
        exact hv1
    obtain ⟨v, hv, hret⟩ := hfin0 (by simp [hsdef, OqShape.oq, hnf])
    rw [hN, loadHolds_mul_gen_pow, Nat.add_zero] at hv
    exact ⟨σ (.n 10), hchain, by rw [hret, loadHolds_unique hv (hchain N le_rfl)]⟩

end
end LeanVM.Guest.B1
