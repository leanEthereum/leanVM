/-
  LeanVM.Guest.B1.Opening.QueriesW

  One query and one loop iteration of `opening_queries`, sound with their witnesses named.
-/

module

public import LeanVM.Guest.B1.Opening.Witness
public import LeanVM.Guest.B1.Opening.QueriesMain
public import LeanVM.Guest.AcceptableChild
import LeanVM.Guest.Value.FieldBits

/-!
# A query and an iteration, their witnesses named

`winPosOf_eq`: the windows a run holds spell the position. `oqSibsOf_eq`: hinted cells holding
siblings give them. `oqQuery_sound_w`: one query is `QueryW` at its witness `oqQueryW`. `oqIter1_sound_w`, `oqIter0_sound_w`: a loop iteration's queries are those of
`oqIterOf`. `loopV_frames`: a guarded loop's iterations, under a call relation unfolding at `V`,
hold at the frames `V f (g^j :: ps) []`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {P : Program} {rd : Reader} {σ : Val}

/-! ## Reading words -/

theorem memRead_of_load {p : E} {off : ℕ} {v : E} (h : LoadHolds rd p off v) :
    memRead rd p off = v := by
  unfold memRead; rw [h.2]; rfl

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

/-- **Hinted cells holding siblings give them.** -/
theorem oqSibsOf_eq {pd ch : ℕ} {sibs : List Digest} (hl : sibs.length = pd)
    (h : ∀ l < pd, SibAt σ ch l (sibs.getD l default)) : oqSibsOf pd ch σ = sibs := by
  apply List.ext_getElem (by simp [oqSibsOf, hl])
  intro l h1 h2
  have hl' : l < pd := by simpa [oqSibsOf] using h1
  simp only [oqSibsOf, List.getElem_map, List.getElem_range]
  have e := h l hl'
  simp only [SibAt] at e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  simp only at e1 e2
  rw [e1, e2, digestOfCells_scalars, List.getD_eq_getElem _ _ h2]

/-! ## One query -/

/-- What a query at a level of cap depth `cd` establishes of its witness `w` at the point `x`
(window run `bp`): its position below `2^(pd + cd)`, the point `eOfNat` of it, the run holding its
windows, `QueryOpensS` at its row and siblings, and some rounds read at `coefs`; at a non-final
level its result `d` is the fold, at the final level the fold is the final polynomial, the
coefficients read at `hs`. -/
def QueryW (rd : Reader) (s : Oq) (cd : ℕ) (cap flags coefs hs x bp : E) (w : QW) (d : E) : Prop :=
  w.1 < 2 ^ (s.pd + cd) ∧ x = eOfNat w.1 ∧
    (∀ i < qwN (s.pd + cd) cd, LoadHolds rd bp i (gen ^ qwVal (s.pd + cd) cd w.1 i)) ∧
    QueryOpensS rd s.base s.folds s.pd cap flags w.1 w.2.1 w.2.2 ∧
    ∃ rounds : List FoldRound, rounds.length = s.folds ∧ RoundsAt rd coefs rounds ∧
      (s.final ≠ 1 → d = foldRow (lanesOf s.base w.2.1) (K.ofBits w.1) rounds) ∧
      (s.final = 1 → ∃ hsv : List E, hsv.length = s.nHs ∧ WordsAt rd hs hsv ∧
        foldRow (lanesOf s.base w.2.1) (K.ofBits w.1) rounds =
          novelSum hsv (wsChain (s.vs.map K.ofBits) x) s.nHs s.hsBits)

/-- The final level's shape facts the check needs. -/
def Oq.FinOk (s : Oq) : Prop :=
  s.final = 1 → s.nHs % 2 = 0 ∧ 2 ≤ s.nHs ∧ 1 ≤ s.hsBits ∧ s.hsBits - 1 ≤ s.mu

instance (s : Oq) : Decidable s.FinOk := by unfold Oq.FinOk; infer_instance

/-- The query's point and windows name a position of depth `pd + cd` (`QueryPosOk`, one query). -/
def PosRun (rd : Reader) (s : Oq) (cd : ℕ) (x bp : E) : Prop :=
  ∃ q < 2 ^ (s.pd + cd), x = eOfNat q ∧
    FrameRun rd bp (qwN (s.pd + cd) cd) fun i ↦ gen ^ qwVal (s.pd + cd) cd q i

/-- **A query** at a level of cap depth `cd`, at the point `x` whose window pointer names a run of
the windows of the position `x` encodes, is sound at its witness `oqQueryW`. -/
theorem oqQuery_sound_w {C : CallRel} {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {cd : ℕ}
    (hcd : 1 ≤ cd) (hcd8 : cd ≤ 8) {x bp cap flags coefs hsV : Core.V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : BlockOkC C rd σ (oqQueryT s x bp cap flags coefs hsV b emit pr))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    (hpos : PosRun rd s cd (σ x) (σ bp)) :
    QueryW rd s cd (σ cap) (σ flags) (σ coefs) (σ hsV) (σ x) (σ bp)
      (oqQueryW s cd rd (σ bp) b emit σ) (σ (.n (oqRes s b emit))) := by
  obtain ⟨q, hq, hx, -, hfr⟩ := hpos
  have hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + cd) cd →
      v = gen ^ qwVal (s.pd + cd) cd q i := fun i v hv hi ↦ hfr i hi v hv.2
  obtain ⟨-, -, -, -, -, hFin⟩ := oqQuery_pieces hA
  obtain ⟨hwl, ⟨sibs, hsib, hopen⟩, hRA, hval⟩ := oqQuery_sound hs hcd hA hpad hz hq hx hwin
  have e : winPosOf rd (σ bp) (s.pd + cd) cd = q := winPosOf_eq hcd8 hq hwl
  have hsibs : oqSibsOf s.pd (oqCh s b emit) σ = sibs := oqSibsOf_eq hopen.2.1 hsib
  unfold oqQueryW
  rw [e, hsibs]
  refine ⟨hq, hx, hwl, hopen, oqRounds s (oqFo s b emit) σ, by simp [oqRounds], hRA, fun hnf ↦ ?_,
    fun h1 ↦ ?_⟩
  · simp only [oqRes, hnf, ↓reduceIte]; exact hval
  · obtain ⟨hn, hn2, hb1, hmu⟩ := hfin h1
    obtain ⟨hW', hl, hv⟩ := oqFin_sound hn hn2 hb1 hmu (hFin h1)
    exact ⟨_, hl, hW', by rw [← hval, hv]⟩

/-! ## The iterations -/

theorem oqLoop1A_mem_q1 {s : Oq} {a : Stmt}
    (h : a ∈ oqQueryT s (.n 13) (.n 14) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs) 15 true 0) :
    a ∈ oqLoop1A s := by
  simp only [oqLoop1A, List.mem_append]; simp_all

theorem oqLoop1A_mem_q2 {s : Oq} {a : Stmt}
    (h : a ∈ oqQueryT s (.n (oqE1 s)) (.n (oqE1 s + 1)) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs)
      (oqE1 s + 2) false (oqK1 s 15)) :
    a ∈ oqLoop1A s := by
  simp only [oqLoop1A, List.mem_append]; simp_all

theorem oqLoop0A_mem_q {s : Oq} {a : Stmt}
    (h : a ∈ oqQueryT s (.n 11) (.n 13) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs) 14 true 0) :
    a ∈ oqLoop0A s := by
  simp only [oqLoop0A, List.mem_append]; simp_all

theorem oqOddT_mem_q {s : Oq} {a : Stmt}
    (h : a ∈ oqQueryT s (.n 15) (.n 16) (.n oqMCap) (.n oqMFlags) (.n oqMCoefs) (.n oqMHs) 17 true 0) :
    a ∈ oqOddT s := by
  simp only [oqOddT, List.mem_append]; simp_all

/-- **A level-0 iteration** at `x = g^i` at a level of cap depth `cd`, its two queries (the
positions and windows `2i`, `2i + 1` of its moved runs) at their witnesses, and (non-final levels)
the chain step. -/
theorem oqIter1_sound_w {C : CallRel} {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {cd : ℕ}
    (hcd : 1 ≤ cd) (hcd8 : cd ≤ 8) {i : ℕ}
    (hA : BlockOkC C rd σ (oqLoop1A s)) (hx : σ (.n oqX) = gen ^ i)
    (hpos : ∀ k, k = 2 * i ∨ k = 2 * i + 1 → ∀ x bp, LoadHolds rd (σ (.n oqPos)) k x →
      LoadHolds rd (σ (.n oqQp)) k bp → PosRun rd s cd x bp) :
    LoadHolds rd (σ (.n oqPos)) (2 * i) (σ (.n 13)) ∧ LoadHolds rd (σ (.n oqQp)) (2 * i) (σ (.n 14)) ∧
      QueryW rd s cd (σ (.n oqCap)) (σ (.n oqFlags)) (σ (.n oqCoefs)) (σ (.n oqHs)) (σ (.n 13))
        (σ (.n 14)) (oqQueryW s cd rd (σ (.n 14)) 15 true σ) (σ (.n (oqRes s 15 true))) ∧
      LoadHolds rd (σ (.n oqPos)) (2 * i + 1) (σ (.n (oqE1 s))) ∧
      LoadHolds rd (σ (.n oqQp)) (2 * i + 1) (σ (.n (oqE1 s + 1))) ∧
      QueryW rd s cd (σ (.n oqCap)) (σ (.n oqFlags)) (σ (.n oqCoefs)) (σ (.n oqHs)) (σ (.n (oqE1 s)))
        (σ (.n (oqE1 s + 1))) (oqQueryW s cd rd (σ (.n (oqE1 s + 1))) (oqE1 s + 2) false σ)
        (σ (.n (oqRes s (oqE1 s + 2) false))) ∧
      (s.final ≠ 1 → ∃ v : E, LoadHolds rd (σ (.n oqChainP)) i v ∧
        LoadHolds rd (σ (.n oqChainP)) (i + 1) (((v + σ (.n (oqRes s 15 true))) * σ (.n oqLamInv) +
          σ (.n (oqRes s (oqE1 s + 2) false))) * σ (.n oqLamInv))) := by
  have p10 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.mul (.n 10) (.n oqX) (.n oqX)) ∈ _)
  have p11 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.mul (.n 11) (.n oqPos) (.n 10)) ∈ _)
  have p12 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.mul (.n 12) (.n oqQp) (.n 10)) ∈ _)
  have p13 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.load (.n 13) (.n 11) 0) ∈ _)
  have p14 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.load (.n 14) (.n 12) 0) ∈ _)
  have pe1 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.load (.n (oqE1 s)) (.n 11) 1) ∈ _)
  have pe2 := hA.atom (by simp [oqLoop1A] : Stmt.atom (.load (.n (oqE1 s + 1)) (.n 12) 1) ∈ _)
  simp only [Atom.Holds] at p10 p11 p12 p13 p14 pe1 pe2
  have h11 : σ (.n 11) = σ (.n oqPos) * gen ^ (2 * i) := by rw [p11, p10, hx, ← pow_add, two_mul]
  have h12 : σ (.n 12) = σ (.n oqQp) * gen ^ (2 * i) := by rw [p12, p10, hx, ← pow_add, two_mul]
  rw [h11, loadHolds_mul_gen_pow] at p13 pe1
  rw [h12, loadHolds_mul_gen_pow] at p14 pe2
  rw [Nat.add_zero] at p13 p14
  have hq1 := hA.mono fun a h => oqLoop1A_mem_q1 h
  have hq2 := hA.mono fun a h => oqLoop1A_mem_q2 h
  obtain ⟨-, hpd', -, -, -, -⟩ := oqQuery_pieces hq1
  obtain ⟨e1, z⟩ := oqPad_values (hpd' rfl)
  have w1 := oqQuery_sound_w hs hfin hcd hcd8 hq1 e1 z (hpos _ (Or.inl rfl) _ _ p13 p14)
  have w2 := oqQuery_sound_w hs hfin hcd hcd8 hq2 e1 z (hpos _ (Or.inr rfl) _ _ pe1 pe2)
  refine ⟨p13, p14, w1, pe1, pe2, w2, fun hnf ↦ ?_⟩
  set c := oqC1 s with hc
  have mem : ∀ a, Stmt.atom a ∈ [Stmt.atom (.mul (.n c) (.n oqChainP) (.n oqX)), .atom (.load (.n (c + 1)) (.n c) 0),
      .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqRes s 15 true))),
      .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n oqLamInv)),
      .atom (.add (.n (c + 4)) (.n (c + 3)) (.n (oqRes s (oqE1 s + 2) false))),
      .atom (.mul (.n (c + 5)) (.n (c + 4)) (.n oqLamInv)), .atom (.mul (.n (c + 6)) (.n oqChainP) (.n oqX)),
      .atom (.load (.n (c + 5)) (.n (c + 6)) 1)] → a.Holds rd σ := fun a h ↦
    hA.atom (by simp only [oqLoop1A, hnf, ↓reduceIte, List.mem_append]; exact Or.inl (Or.inr h))
  have c0 := mem (.mul (.n c) (.n oqChainP) (.n oqX)) (by simp)
  have c1 := mem (.load (.n (c + 1)) (.n c) 0) (by simp)
  have c2 := mem (.add (.n (c + 2)) (.n (c + 1)) (.n (oqRes s 15 true))) (by simp)
  have c3 := mem (.mul (.n (c + 3)) (.n (c + 2)) (.n oqLamInv)) (by simp)
  have c4 := mem (.add (.n (c + 4)) (.n (c + 3)) (.n (oqRes s (oqE1 s + 2) false))) (by simp)
  have c5 := mem (.mul (.n (c + 5)) (.n (c + 4)) (.n oqLamInv)) (by simp)
  have c6 := mem (.mul (.n (c + 6)) (.n oqChainP) (.n oqX)) (by simp)
  have c7 := mem (.load (.n (c + 5)) (.n (c + 6)) 1) (by simp)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5 c6 c7
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c6, hx, loadHolds_mul_gen_pow, c5, c4, c3, c2] at c7
  exact ⟨_, c1, c7⟩

/-- **A deeper iteration** at `x = g^i` at a level of cap depth `cd`, its query at its witness, and
(non-final levels) the chain step. -/
theorem oqIter0_sound_w {C : CallRel} {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {cd : ℕ}
    (hcd : 1 ≤ cd) (hcd8 : cd ≤ 8) {i : ℕ}
    (hA : BlockOkC C rd σ (oqLoop0A s)) (hx : σ (.n oqX) = gen ^ i)
    (hpos : ∀ x bp, LoadHolds rd (σ (.n oqPos)) i x → LoadHolds rd (σ (.n oqQp)) i bp →
      PosRun rd s cd x bp) :
    LoadHolds rd (σ (.n oqPos)) i (σ (.n 11)) ∧ LoadHolds rd (σ (.n oqQp)) i (σ (.n 13)) ∧
      QueryW rd s cd (σ (.n oqCap)) (σ (.n oqFlags)) (σ (.n oqCoefs)) (σ (.n oqHs)) (σ (.n 11))
        (σ (.n 13)) (oqQueryW s cd rd (σ (.n 13)) 14 true σ) (σ (.n (oqRes s 14 true))) ∧
      (s.final ≠ 1 → ∃ v : E, LoadHolds rd (σ (.n oqChainP)) i v ∧
        LoadHolds rd (σ (.n oqChainP)) (i + 1) ((v + σ (.n (oqRes s 14 true))) * σ (.n oqLamInv))) := by
  have p10 := hA.atom (by simp [oqLoop0A] : Stmt.atom (.mul (.n 10) (.n oqPos) (.n oqX)) ∈ _)
  have p11 := hA.atom (by simp [oqLoop0A] : Stmt.atom (.load (.n 11) (.n 10) 0) ∈ _)
  have p12 := hA.atom (by simp [oqLoop0A] : Stmt.atom (.mul (.n 12) (.n oqQp) (.n oqX)) ∈ _)
  have p13 := hA.atom (by simp [oqLoop0A] : Stmt.atom (.load (.n 13) (.n 12) 0) ∈ _)
  simp only [Atom.Holds] at p10 p11 p12 p13
  rw [p10, hx, loadHolds_mul_gen_pow, Nat.add_zero] at p11
  rw [p12, hx, loadHolds_mul_gen_pow, Nat.add_zero] at p13
  have hq := hA.mono fun a h => oqLoop0A_mem_q h
  obtain ⟨-, hpd', -, -, -, -⟩ := oqQuery_pieces hq
  obtain ⟨e1, z⟩ := oqPad_values (hpd' rfl)
  have w1 := oqQuery_sound_w hs hfin hcd hcd8 hq e1 z (hpos _ _ p11 p13)
  refine ⟨p11, p13, w1, fun hnf ↦ ?_⟩
  set c := oqC0 s with hc
  have mem : ∀ a, Stmt.atom a ∈ [Stmt.atom (.mul (.n c) (.n oqChainP) (.n oqX)), .atom (.load (.n (c + 1)) (.n c) 0),
      .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqRes s 14 true))),
      .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n oqLamInv)), .atom (.mul (.n (c + 4)) (.n oqChainP) (.n oqX)),
      .atom (.load (.n (c + 3)) (.n (c + 4)) 1)] → a.Holds rd σ := fun a h ↦
    hA.atom (by simp only [oqLoop0A, hnf, ↓reduceIte, List.mem_append]; exact Or.inl (Or.inr h))
  have c0 := mem (.mul (.n c) (.n oqChainP) (.n oqX)) (by simp)
  have c1 := mem (.load (.n (c + 1)) (.n c) 0) (by simp)
  have c2 := mem (.add (.n (c + 2)) (.n (c + 1)) (.n (oqRes s 14 true))) (by simp)
  have c3 := mem (.mul (.n (c + 3)) (.n (c + 2)) (.n oqLamInv)) (by simp)
  have c4 := mem (.mul (.n (c + 4)) (.n oqChainP) (.n oqX)) (by simp)
  have c5 := mem (.load (.n (c + 3)) (.n (c + 4)) 1) (by simp)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 c5
  rw [c0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at c1
  rw [c4, hx, loadHolds_mul_gen_pow, c3, c2] at c5
  exact ⟨_, c1, c5⟩

/-! ## A guarded loop's frames -/

/-- **A guarded loop's iterations hold at their frames**: under a call relation unfolding at `V`,
when the loop is called at `1` with the bound `N_v = g^N`, its iterations `j < N` hold at the
frames `V f (g^j :: N_v :: rest) []`. -/
theorem loopV_frames {C : CallRel} {V : FrameMap} (hU : UnfoldsVP P rd C V) {f : String} {fn : Fn}
    (hf : P.find? f = some fn) {A : List Stmt} {c : ℕ} {args : List Core.V}
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
