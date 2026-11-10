/-
  LeanVM.Guest.B1.Opening.QueriesW

  One query and one loop iteration of `opening_queries`, sound with their witnesses named.
-/

module

public import LeanVM.Guest.B1.Opening.Witness
public import LeanVM.Guest.B1.Opening.QueriesMain
public import LeanVM.Guest.AcceptableChild

/-!
# A query and an iteration, their witnesses named

`winPosOf_eq`: the windows a run holds spell the position. `oqSibsOf_eq`: children cells holding
siblings off the walk's side give them. `oqQuery_sound_s`, `oqQuery_sound_w`: one query is
`QueryOpensS` at its witness `oqQueryW`. `oqIter1_sound_w`, `oqIter0_sound_w`: a loop iteration's
queries are those of `oqIterOf`. `loopV_frames`: a guarded loop's iterations, under a call relation
unfolding at `V`, hold at the frames `V f (g^j :: ps) []`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Reading words -/

theorem memRead_of_load {p : E} {off : ℕ} {v : E} (h : LoadHolds rd p off v) :
    memRead rd p off = v := by
  unfold memRead; rw [h.2]; rfl

theorem readN_of_readsAt {p : E} {xs : List E} (h : ReadsAt rd p xs) :
    readN rd p xs.length = xs := by
  apply List.ext_getElem (by simp [readN])
  intro i h1 h2
  simp only [readN, List.getElem_map, List.getElem_range]
  exact memRead_of_load (h i h2)

/-- **The exponent of a small power of `g`.** -/
theorem gLog7_gen_pow {v : ℕ} (hv : v < 128) : gLog7 (gen ^ v) = v := by
  unfold gLog7
  have : (List.range 128).find? (fun n ↦ decide (gen ^ n = gen ^ v)) = some v := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp, v, by simpa using hv, by simp, fun j hj ↦ ?_⟩
    simp only [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not]
    intro h
    have := gen_pow_inj (by omega) (by omega) h
    omega
  rw [this]; rfl

/-- The window holding bit `l` of a position: it is one of the position's, and `l` is in it. -/
theorem qwAt_spec {d cd l : ℕ} (hcd : cd ≤ 8) (hl : l < d) :
    qwAt d cd l < qwN d cd ∧ (qwWin d cd (qwAt d cd l)).1 ≤ l ∧
      l < (qwWin d cd (qwAt d cd l)).1 + (qwWin d cd (qwAt d cd l)).2 ∧
      (qwWin d cd (qwAt d cd l)).2 ≤ 7 := by
  unfold qwAt qwWin qwN qwNp
  split_ifs <;> simp only <;> omega

/-- **The windows a run holds spell the position.** -/
theorem winPosOf_eq {bp : E} {d cd q : ℕ} (hcd : cd ≤ 8) (hq : q < 2 ^ d)
    (h : ∀ i < qwN d cd, LoadHolds rd bp i (gen ^ qwVal d cd q i)) : winPosOf rd bp d cd = q := by
  apply Nat.eq_of_testBit_eq
  intro l
  unfold winPosOf
  rw [testBit_bitsVal]
  by_cases hl : l < d
  · obtain ⟨hi, h1, h2, h7⟩ := qwAt_spec (cd := cd) hcd hl
    have hv : qwVal d cd q (qwAt d cd l) < 128 := by
      unfold qwVal
      calc _ < 2 ^ (qwWin d cd (qwAt d cd l)).2 := Nat.mod_lt _ (by positivity)
        _ ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) h7
        _ = 128 := by norm_num
    rw [memRead_of_load (h _ hi), gLog7_gen_pow hv, qwVal, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, decide_eq_true hl, Bool.true_and, decide_eq_true (by omega),
      Bool.true_and, Nat.add_sub_cancel' h1]
  · simp only [hl, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hq
      (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem digestOfCells_scalars (d : Digest) :
    digestOfCells (digestHalves d).1 (digestHalves d).2 = d := by
  unfold digestOfCells
  rw [Prod.mk.eta, digestOfScalars_digestScalars]
  rfl

/-- **Children cells holding siblings off the walk's side give them.** -/
theorem oqSibsOf_eq {pd ch q : ℕ} {sibs : List Digest} (hl : sibs.length = pd)
    (h : ∀ l < pd, SibAt σ ch q l (sibs.getD l default)) :
    oqSibsOf pd ch q σ = sibs := by
  apply List.ext_getElem (by simp [oqSibsOf, hl])
  intro l h1 h2
  have hl' : l < pd := by simpa [oqSibsOf] using h1
  simp only [oqSibsOf, List.getElem_map, List.getElem_range]
  have e := h l hl'
  simp only [SibAt, sibOff] at e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  simp only at e1 e2
  rw [e1, e2, digestOfCells_scalars, List.getD_eq_getElem _ _ h2]

/-! ## One query -/

/-- **One query is `QueryOpensS`** at its row and the siblings its walk's frame's children cells
hold: under a call relation unfolding at `V`, the query's `walk_path` call holds at the frame
`V (oqWalkOf s) (oqWalkArgs …) []`. -/
theorem oqQuery_sound_s {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V) {s : Oq}
    (hs : s.RowShape) (hpd : 1 ≤ s.pd) (hcd : 1 ≤ s.cd) (hW : WalkFn (oqWalkOf s) s.pd s.cd)
    {bp cap flags wp : Core.V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : BlockOkC C rd σ (oqQueryT s bp cap flags wp b emit pr (oqWalkOf s)))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    {q : ℕ} (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i) :
    (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd (σ bp) i (gen ^ qwVal (s.pd + s.cd) s.cd q i)) ∧
    QueryOpensS rd s.base s.I (s.pd + s.cd) s.cd (σ cap) (σ flags) (σ wp) q (oqRow b s.R σ)
      (oqSibsOf s.pd wpCh q (V (oqWalkOf s) (oqWalkArgs s b emit (σ bp) (σ cap) (σ flags) σ) []))
      (σ (.n (oqDot s b))) := by
  obtain ⟨hP, hD, -, -, hcall⟩ := oqQuery_pieces hA
  obtain ⟨fn, hf, hp, hb⟩ := hW
  obtain ⟨fn', hf', hpar, hh⟩ := hU _ _ _ hcall
  rw [hf] at hf'
  cases hf'
  rw [hp] at hpar
  rw [hb] at hh
  obtain ⟨-, hwl, sibs, hsl, hsib, hflag, hc0, hc1⟩ :=
    wp_frame_sound (s := ⟨0, 0, s.pd, s.cd, 0, [], 0, 0⟩) hpd hcd hpar hh (oqQuery_leaf hs hA hpad hz) hq hwin
  have hrl : (oqRow b s.R σ).length = s.R := by simp [oqRow]
  have hWd := oqWord_sound hs hP hD
  obtain ⟨hw, hdot⟩ := oqDot_sound hs hD hWd
  refine ⟨hwl, ?_⟩
  rw [show oqWalkArgs s b emit (σ bp) (σ cap) (σ flags) σ = [σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 0)),
    σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 1)), σ bp, σ cap, σ flags] from rfl, oqSibsOf_eq hsl hsib]
  unfold QueryOpensS
  rw [show s.pd + s.cd - s.cd = s.pd by omega]
  refine ⟨by rw [hrl]; rfl, hsl, oqW s b σ, fun l hl => hw l (by simpa [Oq.lo] using hl),
    hc0, hc1, hflag, ?_⟩
  rw [hdot, rowDot_eq]
  congr 1

/-- What a query establishes of its witness `w`: its position below `2^(pd + cd)`, the window
run at `bp` holding its windows, and `QueryOpensS` at its row and siblings. -/
def QueryW (rd : Reader) (s : Oq) (cap flags wp bp : E) (w : QW) (d : E) : Prop :=
  w.1 < 2 ^ (s.pd + s.cd) ∧
    (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd bp i (gen ^ qwVal (s.pd + s.cd) s.cd w.1 i)) ∧
    QueryOpensS rd s.base s.I (s.pd + s.cd) s.cd cap flags wp w.1 w.2.1 w.2.2 d

/-- **A query whose window pointer names a position's windows** is sound at its witness
`oqQueryW`. -/
theorem oqQuery_sound_w {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V) {s : Oq}
    (hs : s.RowShape) (hpd : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8)
    (hW : WalkFn (oqWalkOf s) s.pd s.cd)
    {bp cap flags wp : Core.V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : BlockOkC C rd σ (oqQueryT s bp cap flags wp b emit pr (oqWalkOf s)))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    (hrun : WinRun rd (σ bp) (s.pd + s.cd) s.cd) :
    QueryW rd s (σ cap) (σ flags) (σ wp) (σ bp) (oqQueryW s rd (σ bp) (σ cap) (σ flags) b emit σ V)
      (σ (.n (oqDot s b))) := by
  obtain ⟨q, hq, -, hfr⟩ := hrun
  have hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i := fun i v hv hi ↦ hfr i hi v hv.2
  obtain ⟨hl, ho⟩ := oqQuery_sound_s hU hs hpd (by omega) hW hA hpad hz hq hwin
  have e : winPosOf rd (σ bp) (s.pd + s.cd) s.cd = q := winPosOf_eq hcd8 hq hl
  unfold oqQueryW
  rw [e]
  exact ⟨hq, hl, ho⟩

/-! ## The iterations -/

/-- **A level-0 iteration** at `x = g^i`, its two queries at their witnesses. -/
theorem oqIter1_sound_w {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V) {s : Oq}
    (hs : s.RowShape) (hpd : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8)
    (hW : WalkFn (oqWalkOf s) s.pd s.cd) {odd i : ℕ}
    (hA : BlockOkC C rd σ (oqLoop1A s odd (oqWalkOf s))) (hx : σ (.n 0) = gen ^ i)
    (hbool : ∀ k, k = 2 * i + odd ∨ k = 2 * i + odd + 1 → ∀ bp, LoadHolds rd (σ (.n 2)) k bp →
      WinRun rd bp (s.pd + s.cd) s.cd) :
    ∃ v : E,
      LoadHolds rd (σ (.n 2)) (2 * i + odd) (σ (.n 10)) ∧
      QueryW rd s (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 10))
        (oqQueryW s rd (σ (.n 10)) (σ (.n 3)) (σ (.n 4)) 11 true σ V) (σ (.n (oqDot s 11))) ∧
      LoadHolds rd (σ (.n 2)) (2 * i + odd + 1) (σ (.n (oqE1 s))) ∧
      QueryW rd s (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n (oqE1 s)))
        (oqQueryW s rd (σ (.n (oqE1 s))) (σ (.n 3)) (σ (.n 4)) (oqE1 s + 1) false σ V)
        (σ (.n (oqDot s (oqE1 s + 1)))) ∧
      LoadHolds rd (σ (.n 6)) i v ∧
      LoadHolds rd (σ (.n 6)) (i + 1) (((v + σ (.n (oqDot s 11))) * σ (.n 7) +
        σ (.n (oqDot s (oqE1 s + 1)))) * σ (.n 7)) := by
  have p8 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.mul (.n 9) (.n 8) (.n 0)) ∈ _)
  have p10 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.load (.n 10) (.n 9) odd) ∈ _)
  have pe1 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.load (.n (oqE1 s)) (.n 9) (odd + 1)) ∈ _)
  simp only [Atom.Holds] at p8 p9 p10 pe1
  have h9 : σ (.n 9) = σ (.n 2) * gen ^ (2 * i) := by rw [p9, p8, hx, mul_assoc, ← pow_add]; ring_nf
  rw [h9, loadHolds_mul_gen_pow] at p10 pe1
  have hq1 := hA.mono fun a h => oqLoop1A_mem_q1 (odd := odd) h
  have hq2 := hA.mono fun a h => oqLoop1A_mem_q2 (odd := odd) h
  obtain ⟨-, -, hpd', -, -⟩ := oqQuery_pieces hq1
  obtain ⟨e1, z⟩ := oqPad_values (hpd' rfl)
  have pe1' : LoadHolds rd (σ (.n 2)) (2 * i + odd + 1) (σ (.n (oqE1 s))) := by
    rw [show 2 * i + odd + 1 = 2 * i + (odd + 1) by omega]; exact pe1
  have w1 := oqQuery_sound_w hU hs hpd hcd hcd8 hW hq1 e1 z (hbool _ (Or.inl rfl) _ p10)
  have w2 := oqQuery_sound_w hU hs hpd hcd hcd8 hW hq2 e1 z (hbool _ (Or.inr rfl) _ pe1')
  set c := oqC1 s with hc
  have c0 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n c) (.n 6) (.n 0)) ∈ _)
  have c1 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.load (.n (c + 1)) (.n c) 0) ∈ _)
  have c2 := hA.atom (by simp [oqLoop1A, ← hc] :
    Stmt.atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 11))) ∈ _)
  have c3 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)) ∈ _)
  have c4 := hA.atom (by simp [oqLoop1A, ← hc] :
    Stmt.atom (.add (.n (c + 4)) (.n (c + 3)) (.n (oqDot s (oqE1 s + 1)))) ∈ _)
  have c5 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 5)) (.n (c + 4)) (.n 7)) ∈ _)
  have c6 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 6)) (.n 6) (.n 0)) ∈ _)
  have c7 := hA.atom (by simp [oqLoop1A, ← hc] : Stmt.atom (.load (.n (c + 5)) (.n (c + 6)) 1) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5 c6 c7
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c6, hx, loadHolds_mul_gen_pow, c5, c4, c3, c2] at c7
  exact ⟨_, p10, w1, pe1', w2, c1, c7⟩

/-- **A deeper iteration** at `x = g^i`, its query at its witness. -/
theorem oqIter0_sound_w {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V) {s : Oq}
    (hs : s.RowShape) (hpd : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8)
    (hW : WalkFn (oqWalkOf s) s.pd s.cd) {i : ℕ}
    (hA : BlockOkC C rd σ (oqLoop0A s (oqWalkOf s))) (hx : σ (.n 0) = gen ^ i)
    (hbool : ∀ bp, LoadHolds rd (σ (.n 2)) i bp → WinRun rd bp (s.pd + s.cd) s.cd) :
    ∃ v : E, LoadHolds rd (σ (.n 2)) i (σ (.n 9)) ∧
      QueryW rd s (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) (σ (.n 9))
        (oqQueryW s rd (σ (.n 9)) (σ (.n 3)) (σ (.n 4)) 10 true σ V) (σ (.n (oqDot s 10))) ∧
      LoadHolds rd (σ (.n 6)) i v ∧
      LoadHolds rd (σ (.n 6)) (i + 1) ((v + σ (.n (oqDot s 10))) * σ (.n 7)) := by
  have p8 := hA.atom (by simp [oqLoop0A] : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hA.atom (by simp [oqLoop0A] : Stmt.atom (.load (.n 9) (.n 8) 0) ∈ _)
  simp only [Atom.Holds] at p8 p9
  rw [p8, hx, loadHolds_mul_gen_pow, Nat.add_zero] at p9
  have hq := hA.mono fun a h => oqLoop0A_mem_q h
  obtain ⟨-, -, hpd', -, -⟩ := oqQuery_pieces hq
  obtain ⟨e1, z⟩ := oqPad_values (hpd' rfl)
  have w1 := oqQuery_sound_w hU hs hpd hcd hcd8 hW hq e1 z (hbool _ p9)
  set c := oqC0 s with hc
  have c0 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n c) (.n 6) (.n 0)) ∈ _)
  have c1 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.load (.n (c + 1)) (.n c) 0) ∈ _)
  have c2 := hA.atom (by simp [oqLoop0A, ← hc] :
    Stmt.atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 10))) ∈ _)
  have c3 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)) ∈ _)
  have c4 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n (c + 4)) (.n 6) (.n 0)) ∈ _)
  have c5 := hA.atom (by simp [oqLoop0A, ← hc] : Stmt.atom (.load (.n (c + 3)) (.n (c + 4)) 1) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c4, hx, loadHolds_mul_gen_pow, c3, c2] at c5
  exact ⟨_, p9, w1, c1, c5⟩

/-! ## A guarded loop's frames -/

/-- **A guarded loop's iterations hold at their frames**: under a call relation unfolding at `V`,
when the loop is called at `1` with the bound `N_v = g^N`, its iterations `j < N` hold at the
frames `V f (g^j :: N_v :: rest) []`. -/
theorem loopV_frames {C : CallRel} {V : FrameMap} (hU : UnfoldsV rd C V) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {A : List Stmt} {c : ℕ} {args : List Core.V}
    (hb : fn.body = A ++ [.callIf (.n c) f args, .ret []]) (hA : FlatC A) {Nv : E}
    {rest : List E}
    (hc : ∀ (τ : Val) (x : E), fn.params.map τ = x :: Nv :: rest → BlockOkC C rd τ A →
      τ (.n c) = x * gen + Nv ∧ args.map τ = x * gen :: Nv :: rest)
    {N : ℕ} (hN : Nv = gen ^ N) (hNo : N < ordG) (h0 : 0 < N → C f (1 :: Nv :: rest) []) :
    ∀ j < N, fn.params.map (V f (gen ^ j :: Nv :: rest) []) = gen ^ j :: Nv :: rest ∧
      BlockOkC C rd (V f (gen ^ j :: Nv :: rest) []) A := by
  have unf : ∀ j, C f (gen ^ j :: Nv :: rest) [] →
      fn.params.map (V f (gen ^ j :: Nv :: rest) []) = gen ^ j :: Nv :: rest ∧
      BlockOkC C rd (V f (gen ^ j :: Nv :: rest) []) A ∧
      (V f (gen ^ j :: Nv :: rest) [] (.n c) ≠ 0 →
        C f (args.map (V f (gen ^ j :: Nv :: rest) [])) []) := by
    intro j hC
    obtain ⟨fn', hf', hp, hh⟩ := hU _ _ _ hC
    rw [hf] at hf'
    cases hf'
    rw [hb, holdsList_append, holdsList_flatC hA] at hh
    obtain ⟨hall, h⟩ := hh
    simp only [Stmt.HoldsList, Stmt.Holds] at h
    exact ⟨hp, hall, h.2.1⟩
  have calls : ∀ j < N, C f (gen ^ j :: Nv :: rest) [] := by
    intro j hj
    induction j with
    | zero => rw [pow_zero]; exact h0 hj
    | succ j ih =>
      obtain ⟨hp, hall, hcall⟩ := unf j (ih (by omega))
      obtain ⟨e1, e2⟩ := hc _ _ hp hall
      have := hcall (by
        rw [e1, hN, ← pow_succ]
        intro h
        have := gen_pow_inj (lt_trans (show j + 1 < N by omega) hNo) hNo (e_add_eq_zero_iff.mp h)
        omega)
      rwa [e2, ← pow_succ] at this
  intro j hj
  obtain ⟨hp, hall, -⟩ := unf j (calls j hj)
  exact ⟨hp, hall⟩

end
end LeanVM.Guest.B1
