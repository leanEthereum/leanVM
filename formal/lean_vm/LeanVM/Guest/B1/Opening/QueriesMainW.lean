/-
  LeanVM.Guest.B1.Opening.QueriesMainW

  `opening_queries` is sound with its queries named: the witness `oqsOf`, read off its frame and
  its loop's frames.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesW
import LeanVM.Guest.Value.FieldBits

/-!
# `opening_queries`, its queries named

`oqMain1_sound_w` (level 0) and `oqMain0_sound_w` (deeper, the final level among them): at a cap
depth `1 ≤ cd ≤ 8`, under a call relation `C ≤ Rel` unfolding at `V`, a valuation holding the
function's body (its loop called at `1`, the bound `g^N`, at level 0 `odd_g = g^odd`), the
positions and window pointers naming positions, gives `MeaningOpeningQueriesW` at `oqsOf … σ V`:
the odd first query from the function's own frame (the start's branch on `odd_g + 1`), then
iteration `j`'s from the loop's frame `V loop (g^j :: oqLoopArgs s σ) []` (`loopV_frames`), at
level 0 on the positions and windows moved past the odd query. The
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

theorem oqLoopArgs_zero {s : Oq} (hb : s.base ≠ 1) (σ : Val) :
    oqLoopArgs s σ = [σ (.n oqMN), σ (.n oqMPos), σ (.n oqMQp), σ (.n oqMCap), σ (.n oqMFlags),
      σ (.n oqMCoefs), σ (.n oqMHs), σ (.n 11), σ (.n oqMLamInv)] := by
  simp [oqLoopArgs, hb]

theorem oqLoopArgs_one {s : Oq} (hb : s.base = 1) (σ : Val) :
    oqLoopArgs s σ = [σ (.n oqMN), σ (.n (oqMK s - 2)), σ (.n (oqMK s - 1)), σ (.n oqMCap),
      σ (.n oqMFlags), σ (.n oqMCoefs), σ (.n oqMHs), σ (.n 11), σ (.n oqMLamInv)] := by
  simp [oqLoopArgs, hb]

/-- The function's start, its call of its loop and its tail: the call, and the returned words: the
chain's `N`-th word at a non-final level, `0` at the final level. -/
theorem oqMain_tail {C : CallRel} {s : Oq} {loop : String} {rets : List E}
    (h : Stmt.HoldsList C rd σ (oqMainT s loop) False (fun rs ↦ rs = rets)) :
    OqStartOk C rd σ s ∧
      (σ (.n (oqMK s + 1)) ≠ 0 → C loop (σ (.n (oqMK s + 2)) :: oqLoopArgs s σ) []) ∧
      (s.final = 1 → rets = [0]) ∧
      (s.final ≠ 1 → ∃ v, LoadHolds rd (σ (.n 11) * σ (.n oqMN)) 0 v ∧ rets = [v]) := by
  rw [oqMainT, holdsList_append, holdsList_append, holdsList_oqMainA] at h
  obtain ⟨hA, h⟩ := h
  rw [Stmt.HoldsList, Stmt.Holds, Stmt.HoldsList] at h
  obtain ⟨-, hcall, h⟩ := h
  refine ⟨hA, fun hne ↦ by simpa [oqLoopArgs] using hcall hne, fun hf ↦ ?_, fun hf ↦ ?_⟩
  · simp only [hf, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
    rw [← h.2, h.1, word_zero]
  · simp only [hf, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
    obtain ⟨e3, e4, e5, hret⟩ := h
    refine ⟨σ (.n (oqMK s + 4)), ?_, by rw [← hret, e5]⟩
    rw [← e3]; exact e4

/-- The function's parameters' values, from its arguments. -/
theorem oqMain_args {fm : Fn} (hpm : fm.params = oqMainParams) {σ : Val} {args : List E}
    (hp : fm.params.map σ = args) :
    args = [σ (.n oqMCap), σ (.n oqMFlags), σ (.n oqMLamInv), σ (.n oqMCoefs), σ (.n oqMHs),
      σ (.n oqMPos), σ (.n oqMQp), σ (.n oqMN), σ (.n oqMOdd)] := by
  rw [← hp, hpm]; rfl

/-! ## Deeper levels -/

theorem oqChain_succ_zero {base : ℕ} (hb : base = 0) (mu : E) (ds : ℕ → E) (i : ℕ) :
    oqChain 0 base mu ds (i + 1) = (oqChain 0 base mu ds i + ds i) * mu := by
  simp [oqChain, hb]

theorem oqsOf_length_zero {s : Oq} (hb0 : s.base = 0) (cd : ℕ) (loop : String) (N : ℕ) (rd : Reader)
    (σ : Val) (V : FrameMap) : (oqsOf s cd 0 loop N rd σ V).length = N := by
  unfold oqsOf
  rw [List.length_append, oqLength_flatMap_range _ 1 (fun j => by simp [oqIterOf, hb0])]
  simp

/-- **`opening_queries` deeper is sound with its queries named** (`base = 0`, `odd = 0`; the final
level among them). -/
theorem oqMain0_sound_w {sh : OqShape} (hs : sh.oq.RowShape) (hfin : sh.oq.FinOk)
    (hb0 : sh.base = 0) {name loop : String} {fm fl : Fn}
    (hfm : P.find? name = some fm) (hpm : fm.params = oqMainParams)
    (hbm : fm.body = oqMainT sh.oq loop)
    (hfl : P.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T sh.oq loop) :
    opening_queries_sound_w_SpecP P name loop sh := by
  intro cd hcd hcd8 rd C V hU _ fm' σ args rets N odd hfm' hp hh hN hNo hO hodd hpos
  rw [hfm] at hfm'
  cases hfm'
  have hargs := oqMain_args hpm hp
  subst hargs
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hN hO hpos
  obtain rfl : odd = 0 := by rw [hb0] at hodd; omega
  set s := sh.oq with hsdef
  have hsb : s.base = 0 := hb0
  have hsb1 : s.base ≠ 1 := by omega
  have hQ : oqCount 0 sh.base N = N := by simp [oqCount, hb0]
  rw [hQ] at hpos
  rw [hbm] at hh
  obtain ⟨hA, hcall, hfin1, hfin0⟩ := oqMain_tail hh
  obtain ⟨hg, hst, h0even⟩ := oqMainA_basic hA
  -- the iterations' frames
  have hfr := loopV_frames (rd := rd) hU hfl (by rw [hbl]; rfl) (oqLoop0A_flatC s)
    (Nv := σ (.n oqMN)) (rest := [σ (.n oqMPos), σ (.n oqMQp), σ (.n oqMCap), σ (.n oqMFlags),
      σ (.n oqMCoefs), σ (.n oqMHs), σ (.n 11), σ (.n oqMLamInv)])
    (fun τ x hp hA => oqLoop0_hc hpl τ x hp hA) hN hNo (fun hN0 => by
      have hne : σ (.n (oqMK s + 1)) ≠ 0 := by
        rw [hg, hN]
        intro h0
        have := (gen_pow_eq_one_iff hNo).mp (e_add_eq_zero_iff.mp h0).symm
        omega
      have := hcall hne
      rwa [hst, oqLoopArgs_zero hsb1] at this)
  set τ : ℕ → Val := fun j => V loop [gen ^ j, σ (.n oqMN), σ (.n oqMPos), σ (.n oqMQp),
    σ (.n oqMCap), σ (.n oqMFlags), σ (.n oqMCoefs), σ (.n oqMHs), σ (.n 11), σ (.n oqMLamInv)] []
    with hτ
  have hit : ∀ j < N,
      LoadHolds rd (σ (.n oqMPos)) j (τ j (.n 11)) ∧ LoadHolds rd (σ (.n oqMQp)) j (τ j (.n 13)) ∧
      (∃ w, w = oqQueryW s cd rd (τ j (.n 13)) 14 true (τ j) ∧
        QueryW rd s cd (σ (.n oqMCap)) (σ (.n oqMFlags)) (σ (.n oqMCoefs)) (σ (.n oqMHs))
          (τ j (.n 11)) (τ j (.n 13)) w (τ j (.n (oqRes s 14 true)))) ∧
      (s.final ≠ 1 → ∃ v : E, LoadHolds rd (σ (.n 11)) j v ∧
        LoadHolds rd (σ (.n 11)) (j + 1) ((v + τ j (.n (oqRes s 14 true))) * σ (.n oqMLamInv))) := by
    intro j hj
    obtain ⟨hp, hA⟩ := hfr j hj
    obtain ⟨t0, hps⟩ := loop_params hpl hp
    simp only [List.cons.injEq] at hps
    obtain ⟨-, t2, t3, t4, t5, t6, t7, t8, t9, -⟩ := hps
    have := oqIter0_sound_w hs hfin hcd hcd8 (i := j) hA t0 (fun x bp hx hbp => by
      rw [← t2] at hx
      rw [← t3] at hbp
      exact hpos j hj x bp hx hbp)
    obtain ⟨a1, a2, a3, a4⟩ := this
    generalize hw : oqQueryW s cd rd (τ j (.n 13)) 14 true (τ j) = w at a3
    rw [← t2] at a1
    rw [← t3] at a2
    rw [← t4, ← t5, ← t6, ← t7] at a3
    rw [← t8, ← t9] at a4
    exact ⟨a1, a2, ⟨w, rfl, a3⟩, a4⟩
  -- the witness
  set ws := oqsOf s cd 0 loop N rd σ V with hws
  have hwsI : ∀ j < N, ws.getD j default = oqQueryW s cd rd (τ j (.n 13)) 14 true (τ j) := by
    intro j hj
    simp only [hws, oqsOf, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.nil_append]
    have := oqGetD_flatMap_range (fun j => oqIterOf s cd rd (V loop (gen ^ j :: oqLoopArgs s σ) [])) 1
      (fun j => by simp [oqIterOf, hsb]) default N j 0 hj (by omega)
    rw [Nat.one_mul, Nat.add_zero] at this
    rw [this]
    simp [oqIterOf, hsb, hτ, oqLoopArgs_zero hsb1]
  have hQW : ∀ j < N, QueryW rd s cd (σ (.n oqMCap)) (σ (.n oqMFlags)) (σ (.n oqMCoefs))
      (σ (.n oqMHs)) (τ j (.n 11)) (τ j (.n 13)) (ws.getD j default) (τ j (.n (oqRes s 14 true))) :=
    fun j hj ↦ by
      obtain ⟨w, hw, h⟩ := (hit j hj).2.2.1
      rw [hwsI j hj, ← hw]; exact h
  -- the rounds and the final coefficients, shared
  have hR : ∀ j < N, ∃ rounds : List FoldRound, rounds.length = s.folds ∧
      RoundsAt rd (σ (.n oqMCoefs)) rounds ∧
      (s.final ≠ 1 → τ j (.n (oqRes s 14 true)) = qwFold s.base rounds (ws.getD j default)) ∧
      (s.final = 1 → ∃ hsv : List E, hsv.length = s.nHs ∧ WordsAt rd (σ (.n oqMHs)) hsv ∧
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
  have hH : ∀ j < N, ∃ hsv : List E, s.final = 1 → hsv.length = s.nHs ∧
      WordsAt rd (σ (.n oqMHs)) hsv ∧ qwFold s.base rounds (ws.getD j default) =
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
  refine ⟨N, hNo, hN, 0, by omega, hO, by rw [hQ, oqsOf_length_zero hsb], rounds, hsv, hrl, hhl,
    fun k hk ↦ ?_, ?_⟩
  · rw [hQ] at hk
    obtain ⟨l5, l6, hq⟩ := hit k hk
    obtain ⟨q1, q2, q3, q4, -⟩ := hQW k hk
    obtain ⟨-, hRA, -, -⟩ := hrr k hk
    rw [hrj k hk] at hRA
    refine ⟨hRA, fun hf ↦ ?_, by rw [← q2]; exact l5, q1, ⟨τ k (.n 13), l6, q3⟩, q4, fun hf ↦ ?_⟩
    · rw [← hhj k hk hf]; exact (hhh k hk hf).2.1
    · have := (hhh k hk hf).2.2
      rw [hhj k hk hf, q2] at this
      exact this
  · by_cases hf : sh.final = 1
    · simp only [hf, ↓reduceIte]; exact hfin1 hf
    · simp only [hf, ↓reduceIte]
      have hchain : ∀ i ≤ N, LoadHolds rd (σ (.n 11)) i
          (oqChain 0 sh.base (σ (.n oqMLamInv)) (fun k ↦ qwFold sh.base rounds (ws.getD k default)) i) := by
        intro i hi
        induction i with
        | zero =>
          simp only [oqChain, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
          exact h0even hsb1
        | succ i ih =>
          obtain ⟨v, hv, hv1⟩ := (hit i (by omega)).2.2.2 hf
          have e := loadHolds_unique hv (ih (by omega))
          rw [e, hds i (by omega) hf] at hv1
          rw [oqChain_succ_zero hb0]
          exact hv1
      obtain ⟨v, hv, hret⟩ := hfin0 hf
      rw [hN, loadHolds_mul_gen_pow, Nat.add_zero] at hv
      exact ⟨σ (.n 11), hchain, by rw [hret, loadHolds_unique hv (hchain N le_rfl)]⟩

/-! ## Level 0 -/

theorem oqChain_succ_one {odd base : ℕ} (hb : base = 1) (mu : E) (ds : ℕ → E) (i : ℕ) :
    oqChain odd base mu ds (i + 1) =
      ((oqChain odd base mu ds i + ds (odd + 2 * i)) * mu + ds (odd + 2 * i + 1)) * mu := by
  simp [oqChain, hb]

theorem oqsOf_length_one {s : Oq} (hb1 : s.base = 1) {odd : ℕ} (hodd : odd ≤ 1) (cd : ℕ)
    (loop : String) (N : ℕ) (rd : Reader) (σ : Val) (V : FrameMap) :
    (oqsOf s cd odd loop N rd σ V).length = odd + 2 * N := by
  unfold oqsOf
  rw [List.length_append, oqLength_flatMap_range _ 2 (fun j => by simp [oqIterOf, hb1])]
  split_ifs with h <;> simp <;> omega

/-- The odd first query (level 0's start, `odd_g ≠ 1`), and the chain's first word, its result
times `λ⁻¹`. -/
theorem oqOdd_w {C : CallRel} {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {cd : ℕ} (hcd : 1 ≤ cd)
    (hcd8 : cd ≤ 8) (hA : BlockOkC C rd σ (oqOddT s))
    (hpos : ∀ x bp, LoadHolds rd (σ (.n oqMPos)) 0 x → LoadHolds rd (σ (.n oqMQp)) 0 bp →
      PosRun rd s cd x bp) :
    LoadHolds rd (σ (.n oqMPos)) 0 (σ (.n 15)) ∧ LoadHolds rd (σ (.n oqMQp)) 0 (σ (.n 16)) ∧
      QueryW rd s cd (σ (.n oqMCap)) (σ (.n oqMFlags)) (σ (.n oqMCoefs)) (σ (.n oqMHs)) (σ (.n 15))
        (σ (.n 16)) (oqQueryW s cd rd (σ (.n 16)) 17 true σ) (σ (.n (oqRes s 17 true))) ∧
      LoadHolds rd (σ (.n 11)) 0 (σ (.n (oqRes s 17 true)) * σ (.n oqMLamInv)) := by
  have mem := hA.mono fun a h => oqOddT_mem_q h
  have l15 := hA.atom (by simp [oqOddT] : Stmt.atom (.load (.n 15) (.n oqMPos) 0) ∈ _)
  have l16 := hA.atom (by simp [oqOddT] : Stmt.atom (.load (.n 16) (.n oqMQp) 0) ∈ _)
  have c1 := hA.atom (by simp [oqOddT] :
    Stmt.atom (.mul (.n (oqEnd s 17 true)) (.n (oqRes s 17 true)) (.n oqMLamInv)) ∈ _)
  have c2 := hA.atom (by simp [oqOddT] : Stmt.atom (.load (.n (oqEnd s 17 true)) (.n 11) 0) ∈ _)
  simp only [Atom.Holds] at c1 l15 l16
  obtain ⟨-, hpd', -, -, -, -⟩ := oqQuery_pieces mem
  obtain ⟨e1, z⟩ := oqPad_values (hpd' rfl)
  refine ⟨l15, l16, oqQuery_sound_w hs hfin hcd hcd8 mem e1 z (hpos _ _ l15 l16), ?_⟩
  have := c2
  simp only [Atom.Holds, c1] at this
  exact this

/-- **`opening_queries` at level 0 is sound with its queries named** (`base = 1`, a non-final
level). -/
theorem oqMain1_sound_w {sh : OqShape} (hs : sh.oq.RowShape) (hfin : sh.oq.FinOk)
    (hb1 : sh.base = 1) (hnf : sh.final = 0) {name loop : String} {fm fl : Fn}
    (hfm : P.find? name = some fm) (hpm : fm.params = oqMainParams)
    (hbm : fm.body = oqMainT sh.oq loop)
    (hfl : P.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T sh.oq loop) :
    opening_queries_sound_w_SpecP P name loop sh := by
  intro cd hcd hcd8 rd C V hU _ fm' σ args rets N odd hfm' hp hh hN hNo hO hodd hpos
  rw [hfm] at hfm'
  cases hfm'
  have hargs := oqMain_args hpm hp
  subst hargs
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hN hO hpos
  rw [hb1] at hodd
  set s := sh.oq with hsdef
  have hsb : s.base = 1 := hb1
  have hQ : oqCount odd sh.base N = odd + 2 * N := by simp [oqCount, hb1]
  rw [hQ] at hpos
  have hpos' : ∀ k < odd + 2 * N, ∀ x bp, LoadHolds rd (σ (.n oqMPos)) k x →
      LoadHolds rd (σ (.n oqMQp)) k bp → PosRun rd s cd x bp := hpos
  rw [hbm] at hh
  obtain ⟨hA, hcall, -, hfin0⟩ := oqMain_tail hh
  obtain ⟨hg, hst, -⟩ := oqMainA_basic hA
  obtain ⟨h13, hmp, hmq, heven, hoddB⟩ := oqStart1_facts hsb hA
  -- the branch: `odd_g + 1 = 0` exactly at `odd = 0`
  have h13z : σ (.n 13) = 0 ↔ odd ≠ 1 := by
    rw [h13, hO, e_add_eq_zero_iff, gen_pow_eq_one_iff (by norm_num; omega)]
    omega
  have hmp' : σ (.n (oqMK s - 2)) = σ (.n oqMPos) * gen ^ odd := by rw [hmp, hO]
  have hmq' : σ (.n (oqMK s - 1)) = σ (.n oqMQp) * gen ^ odd := by rw [hmq, hO]
  have hfr := loopV_frames (rd := rd) hU hfl (by rw [hbl]; rfl) (oqLoop1A_flatC s)
    (Nv := σ (.n oqMN)) (rest := [σ (.n (oqMK s - 2)), σ (.n (oqMK s - 1)), σ (.n oqMCap),
      σ (.n oqMFlags), σ (.n oqMCoefs), σ (.n oqMHs), σ (.n 11), σ (.n oqMLamInv)])
    (fun τ x hp hA => oqLoop1_hc hpl τ x hp hA) hN hNo (fun hN0 => by
      have hne : σ (.n (oqMK s + 1)) ≠ 0 := by
        rw [hg, hN]
        intro h0
        have := (gen_pow_eq_one_iff hNo).mp (e_add_eq_zero_iff.mp h0).symm
        omega
      have := hcall hne
      rwa [hst, oqLoopArgs_one hsb] at this)
  set τ : ℕ → Val := fun j => V loop [gen ^ j, σ (.n oqMN), σ (.n (oqMK s - 2)),
    σ (.n (oqMK s - 1)), σ (.n oqMCap), σ (.n oqMFlags), σ (.n oqMCoefs), σ (.n oqMHs), σ (.n 11),
    σ (.n oqMLamInv)] [] with hτ
  -- the queries of an iteration
  have hit : ∀ j < N,
      LoadHolds rd (σ (.n oqMPos)) (odd + 2 * j) (τ j (.n 13)) ∧
      LoadHolds rd (σ (.n oqMQp)) (odd + 2 * j) (τ j (.n 14)) ∧
      (∃ w, w = oqQueryW s cd rd (τ j (.n 14)) 15 true (τ j) ∧
        QueryW rd s cd (σ (.n oqMCap)) (σ (.n oqMFlags)) (σ (.n oqMCoefs)) (σ (.n oqMHs))
          (τ j (.n 13)) (τ j (.n 14)) w (τ j (.n (oqRes s 15 true)))) ∧
      LoadHolds rd (σ (.n oqMPos)) (odd + 2 * j + 1) (τ j (.n (oqE1 s))) ∧
      LoadHolds rd (σ (.n oqMQp)) (odd + 2 * j + 1) (τ j (.n (oqE1 s + 1))) ∧
      (∃ w, w = oqQueryW s cd rd (τ j (.n (oqE1 s + 1))) (oqE1 s + 2) false (τ j) ∧
        QueryW rd s cd (σ (.n oqMCap)) (σ (.n oqMFlags)) (σ (.n oqMCoefs)) (σ (.n oqMHs))
          (τ j (.n (oqE1 s))) (τ j (.n (oqE1 s + 1))) w (τ j (.n (oqRes s (oqE1 s + 2) false)))) ∧
      ∃ v : E, LoadHolds rd (σ (.n 11)) j v ∧
        LoadHolds rd (σ (.n 11)) (j + 1) (((v + τ j (.n (oqRes s 15 true))) * σ (.n oqMLamInv) +
          τ j (.n (oqRes s (oqE1 s + 2) false))) * σ (.n oqMLamInv)) := by
    intro j hj
    obtain ⟨hp, hA⟩ := hfr j hj
    obtain ⟨t0, hps⟩ := loop_params hpl hp
    simp only [List.cons.injEq] at hps
    obtain ⟨-, t2, t3, t4, t5, t6, t7, t8, t9, -⟩ := hps
    have := oqIter1_sound_w hs hfin hcd hcd8 (i := j) hA t0
      (fun k hk x bp hx hbp => by
        rw [t2.symm.trans hmp', loadHolds_mul_gen_pow] at hx
        rw [t3.symm.trans hmq', loadHolds_mul_gen_pow] at hbp
        exact hpos' _ (by omega) x bp hx hbp)
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := this
    generalize hw1 : oqQueryW s cd rd (τ j (.n 14)) 15 true (τ j) = w1 at a3
    generalize hw2 : oqQueryW s cd rd (τ j (.n (oqE1 s + 1))) (oqE1 s + 2) false (τ j) = w2 at a6
    rw [t2.symm.trans hmp', loadHolds_mul_gen_pow] at a1 a4
    rw [t3.symm.trans hmq', loadHolds_mul_gen_pow] at a2 a5
    rw [← Nat.add_assoc] at a4 a5
    rw [← t4, ← t5, ← t6, ← t7] at a3 a6
    obtain ⟨v, b1, b2⟩ := a7 (by show sh.final ≠ 1; omega)
    rw [← t8] at b1 b2
    rw [← t9] at b2
    exact ⟨a1, a2, ⟨w1, rfl, a3⟩, a4, a5, ⟨w2, rfl, a6⟩, v, b1, b2⟩
  -- the odd first query
  have hM : odd = 1 → LoadHolds rd (σ (.n oqMPos)) 0 (σ (.n 15)) ∧
      LoadHolds rd (σ (.n oqMQp)) 0 (σ (.n 16)) ∧
      QueryW rd s cd (σ (.n oqMCap)) (σ (.n oqMFlags)) (σ (.n oqMCoefs)) (σ (.n oqMHs)) (σ (.n 15))
        (σ (.n 16)) (oqQueryW s cd rd (σ (.n 16)) 17 true σ) (σ (.n (oqRes s 17 true))) ∧
      LoadHolds rd (σ (.n 11)) 0 (σ (.n (oqRes s 17 true)) * σ (.n oqMLamInv)) := by
    intro h1
    exact oqOdd_w hs hfin hcd hcd8 (hoddB fun h => (h13z.mp h) h1)
      (fun x bp hx hbp ↦ hpos' 0 (by omega) x bp hx hbp)
  -- the witness, by index
  set ws := oqsOf s cd odd loop N rd σ V with hws
  have hwsM : odd = 1 → ws.getD 0 default = oqQueryW s cd rd (σ (.n 16)) 17 true σ := by
    intro h1; simp [hws, oqsOf, h1]
  have hwsI : ∀ j < N, ∀ e < 2, ws.getD (odd + (2 * j + e)) default =
      (oqIterOf s cd rd (τ j)).getD e default := by
    intro j hj e he
    have hl : (if odd = 1 then [oqQueryW s cd rd (σ (.n 16)) 17 true σ] else []).length = odd := by
      split_ifs with h <;> simp <;> omega
    simp only [hws, oqsOf]
    rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]
    rw [oqGetD_flatMap_range _ 2 (fun j => by simp [oqIterOf, hsb]) default N j e hj he]
    simp [hτ, oqLoopArgs_one hsb]
  have hiter : ∀ j < N, oqIterOf s cd rd (τ j) =
      [oqQueryW s cd rd (τ j (.n 14)) 15 true (τ j),
        oqQueryW s cd rd (τ j (.n (oqE1 s + 1))) (oqE1 s + 2) false (τ j)] :=
    fun j _ ↦ by simp [oqIterOf, hsb]
  -- every query, by index
  let dOf : ℕ → E := fun k ↦ if k < odd then σ (.n (oqRes s 17 true))
    else if (k - odd) % 2 = 0 then τ ((k - odd) / 2) (.n (oqRes s 15 true))
    else τ ((k - odd) / 2) (.n (oqRes s (oqE1 s + 2) false))
  have hQW : ∀ k < odd + 2 * N, ∃ x bp : E, LoadHolds rd (σ (.n oqMPos)) k x ∧
      LoadHolds rd (σ (.n oqMQp)) k bp ∧
      QueryW rd s cd (σ (.n oqMCap)) (σ (.n oqMFlags)) (σ (.n oqMCoefs)) (σ (.n oqMHs)) x bp
        (ws.getD k default) (dOf k) := by
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
      · refine ⟨_, _, by rw [show odd + (2 * j + 0) = odd + 2 * j by omega]; exact a1,
          by rw [show odd + (2 * j + 0) = odd + 2 * j by omega]; exact a2, ?_⟩
        have hd : dOf (odd + (2 * j + 0)) = τ j (.n (oqRes s 15 true)) := by
          simp only [dOf, show ¬ odd + (2 * j + 0) < odd by omega, ↓reduceIte,
            show (odd + (2 * j + 0) - odd) % 2 = 0 by omega, show (odd + (2 * j + 0) - odd) / 2 = j by omega]
        rw [hd, List.getD_cons_zero, ← hw1]; exact a3
      · refine ⟨_, _, by rw [show odd + (2 * j + 1) = odd + 2 * j + 1 by omega]; exact a4,
          by rw [show odd + (2 * j + 1) = odd + 2 * j + 1 by omega]; exact a5, ?_⟩
        have hd : dOf (odd + (2 * j + 1)) = τ j (.n (oqRes s (oqE1 s + 2) false)) := by
          simp only [dOf, show ¬ odd + (2 * j + 1) < odd by omega, ↓reduceIte,
            show (odd + (2 * j + 1) - odd) % 2 = 1 by omega, show (odd + (2 * j + 1) - odd) / 2 = j by omega,
            show (1 : ℕ) ≠ 0 by decide]
        rw [hd, List.getD_cons_succ, List.getD_cons_zero, ← hw2]; exact a6
  -- the rounds, shared
  have hR : ∀ k < odd + 2 * N, ∃ rounds : List FoldRound, rounds.length = s.folds ∧
      RoundsAt rd (σ (.n oqMCoefs)) rounds ∧
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
  refine ⟨N, hNo, hN, odd, by rw [hb1]; exact hodd, hO, by rw [hQ, oqsOf_length_one hsb hodd],
    rounds, List.replicate sh.nHs 0, hrl, by simp, fun k hk ↦ ?_, ?_⟩
  · rw [hQ] at hk
    obtain ⟨x, bp, l5, l6, q1, q2, q3, q4, -⟩ := hQW k hk
    obtain ⟨-, hRA, -⟩ := hrr k hk
    rw [hrj k hk] at hRA
    refine ⟨hRA, fun hf ↦ absurd hf (by omega), by rw [← q2]; exact l5, q1, ⟨bp, l6, q3⟩, q4,
      fun hf ↦ absurd hf (by omega)⟩
  · simp only [hnf, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
    have hchain : ∀ i ≤ N, LoadHolds rd (σ (.n 11)) i
        (oqChain odd sh.base (σ (.n oqMLamInv)) (fun k ↦ qwFold sh.base rounds (ws.getD k default)) i) := by
      intro i hi
      induction i with
      | zero =>
        by_cases h1 : odd = 1
        · have := (hM h1).2.2.2
          simp only [oqChain, h1, ↓reduceIte]
          rw [← hds 0 (by omega)]
          simpa [dOf, h1] using this
        · simp only [oqChain, h1, ↓reduceIte]
          exact heven (h13z.mpr h1)
      | succ i ih =>
        obtain ⟨-, -, -, -, -, -, v, hv, hv1⟩ := hit i (by omega)
        have e := loadHolds_unique hv (ih (by omega))
        have d0 : dOf (odd + 2 * i) = τ i (.n (oqRes s 15 true)) := by
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
    exact ⟨σ (.n 11), hchain, by rw [hret, loadHolds_unique hv (hchain N le_rfl)]⟩

end
end LeanVM.Guest.B1
