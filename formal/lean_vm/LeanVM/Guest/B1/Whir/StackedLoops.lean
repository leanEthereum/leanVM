/-
  LeanVM.Guest.B1.Whir.StackedLoops

  `open_stacked`'s two loop helpers: the squeezes that decode a level's query positions, and a
  level's residual chain over its queries.
-/

module

public import LeanVM.Guest.B1.Whir.StackedBlocks

/-!
# The loops of `open_stacked` (TRIAGE #36)

* The squeeze loop (`sqLoopBody`, G:1147-1157), at `x = g^j`: the state at `sqz[2j], sqz[2j+1]`
  squeezed once into `sqz[2j+2], sqz[2j+3]`, and `decode_query_bits` of the challenge into the
  positions and bit runs at `posOff + j·(192/depth)` (`SqBody`).
* The residual loop (`resLoopBody`, G:1283-1294), at `x = g^i`: query `i`'s position, its basis
  product over the level's coordinates, `chain[i+1] = chain[i] + qw[qo+i]·product` (`ResBody`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Powers by square-and-multiply -/

/-- The exponent the digits `ds` give from `a`. -/
def osDigitsVal (a : ℕ) (ds : List Bool) : ℕ := ds.foldl (fun a d => 2 * a + d.toNat) a

theorem osPowSteps_noRet (x : ℕ) : ∀ ds acc k, Stmt.noRetList (osPowSteps x ds acc k).1 = true
  | [], _, _ => rfl
  | d :: ds, acc, k => by
    unfold osPowSteps
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact osPowSteps_noRet x ds k (k + 1)
    · simp only [↓reduceIte]
      exact osPowSteps_noRet x ds (k + 1) (k + 2)

theorem osPowSteps_sound (x : ℕ) {kret : List E → Prop} :
    ∀ (ds : List Bool) (acc k a : ℕ), σ (.n acc) = σ (.n x) ^ a →
      Stmt.HoldsList C rd σ (osPowSteps x ds acc k).1 True kret →
      σ (.n (osPowSteps x ds acc k).2) = σ (.n x) ^ osDigitsVal a ds
  | [], acc, _, a, ha, _ => ha
  | d :: ds, acc, k, a, ha, h => by
    unfold osPowSteps at h ⊢
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h ⊢
      refine osPowSteps_sound x ds k (k + 1) (2 * a) ?_ h.2
      rw [h.1, ha, ← pow_add, two_mul]
    · simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h ⊢
      refine osPowSteps_sound x ds (k + 1) (k + 2) (2 * a + 1) ?_ h.2.2
      rw [h.2.1, h.1, ha, ← pow_add, ← pow_succ, two_mul]

/-! ## The squeeze loop -/

/-- One squeeze of the loop at `x`: the state at `sqz·x²` squeezed into its next two words, and
the challenge decoded at `g^posOff·x^(192/depth)`. -/
def SqBody (rd : Reader) (depth posOff : ℕ) (sqz qpos qbp x : E) : Prop :=
  ∃ cv, LoadHolds rd (sqz * (x * x)) 0 (digestScalars cv).1 ∧
    LoadHolds rd (sqz * (x * x)) 1 (digestScalars cv).2 ∧
    LoadHolds rd (sqz * (x * x)) 2 (digestScalars (sqCv cv)).1 ∧
    LoadHolds rd (sqz * (x * x)) 3 (digestScalars (sqCv cv)).2 ∧
    MeaningDecodeQueryBits depth rd [challengeOf (sqCv cv),
      qpos * gen ^ posOff * x ^ (192 / depth), qbp * gen ^ posOff * x ^ (192 / depth)] []

theorem sqPtr_noRet (posOff q base k : ℕ) : Stmt.noRetList (sqPtr posOff q base k).1 = true := by
  unfold sqPtr; split <;> rfl

theorem sqPtr_sound {posOff q base k : ℕ} (hpo : posOff < 2 ^ 128) {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (sqPtr posOff q base k).1 True kret) :
    σ (.n (sqPtr posOff q base k).2.1) = σ (.n base) * gen ^ posOff * σ (.n q) := by
  unfold sqPtr at h ⊢
  by_cases h0 : posOff = 0
  · simp only [h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, pow_zero, mul_one] at h ⊢
    exact h.1
  · simp only [h0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h ⊢
    rw [h.2.2.1, h.2.1, h.1, os_gw_eq hpo]

theorem sqLoop_step {lv : OsLvl} {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hb : fn.body = sqLoopOf lv)
    (hdec : ∀ a r, coreProgram.Rel rd lv.decode a r → MeaningDecodeQueryBits lv.depth rd a r)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth)
    (hpo : lv.posOff < 2 ^ 128) {d : ℕ} {x N sqz qpos qbp : E}
    (h : coreProgram.relN rd (d + 1) lv.sqLoop [x, N, sqz, qpos, qbp] []) :
    SqBody rd lv.depth lv.posOff sqz qpos qbp x ∧ IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d lv.sqLoop [x * gen, N, sqz, qpos, qbp] []) := by
  rw [relN_succ_iff hfind, hp, hb, sqLoopOf, sqLoopBody] at h
  obtain ⟨σ, hpar, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hpar
  simp only [holdsList_append] at h
  obtain ⟨hA, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hS, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hB, h⟩ := holdsList_true_of (by rfl) h
  obtain ⟨hP, h⟩ := holdsList_true_of (osPowSteps_noRet _ _ _ _) h
  obtain ⟨h1, h⟩ := holdsList_true_of (sqPtr_noRet _ _ _ _) h
  obtain ⟨h2, h⟩ := holdsList_true_of (sqPtr_noRet _ _ _ _) h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hA hB h
  obtain ⟨a5, a6, l7, l8, a9, a10⟩ := hA
  obtain ⟨b25, b26, l25, l26⟩ := hB
  obtain ⟨hcall, e0, e1, e2, e3, e4, hK, hrec, -⟩ := h
  obtain ⟨⟨cv, hcv, hv⟩, -⟩ := (holds_squeezeT _ _ _ True _).mp (by simpa using hS)
  have hq := osPowSteps_sound 0 _ 0 27 1 (by rw [pow_one]) hP
  rw [hdig] at hq
  have hp1 := sqPtr_sound hpo h1
  have hp2 := sqPtr_sound hpo h2
  rw [hq] at hp1 hp2
  have hrow : σ (.n 6) = σ (.n 2) * (σ (.n 0) * σ (.n 0)) := by rw [a6, a5]
  have f16 : σ (.n (11 + 5)) = sqVals cv 5 := hv 5 (by omega)
  have f17 : σ (.n (11 + 6)) = sqVals cv 6 := hv 6 (by omega)
  have f24 : σ (.n (11 + 13)) = sqVals cv 13 := hv 13 (by omega)
  simp only [Nat.reduceAdd] at f16 f17 f24
  rw [a9, a10] at hcv
  have c1 : σ (.n 7) = (digestScalars cv).1 := congrArg Prod.fst hcv
  have c2 : σ (.n 8) = (digestScalars cv).2 := congrArg Prod.snd hcv
  rw [e2, e1, e0, word_gen] at hK hrec
  refine ⟨⟨cv, ?_, ?_, ?_, ?_, ?_⟩, hK, fun hne => ?_⟩
  · rw [← hrow, ← c1]; exact l7
  · rw [← hrow, ← c2]; exact l8
  · rw [← hrow]; convert l25 using 1; rw [b25, f16]; rfl
  · rw [← hrow]; convert l26 using 1; rw [b26, f17]; rfl
  · have := hdec _ _ (relN_le_rel coreProgram d _ _ _ hcall)
    simp only [List.map_cons, List.map_nil] at this
    rwa [f24, hp1, hp2] at this
  · have := hrec hne
    simp only [List.map_cons, List.map_nil, e4, e3, word_gen] at this
    exact this

theorem os_gen_pow_sq (j : ℕ) : gen ^ j * gen ^ j = gen ^ (2 * j) := by rw [← pow_add, two_mul]

theorem sqBody_at {depth posOff : ℕ} {sqz qpos qbp : E} {j : ℕ}
    (h : SqBody rd depth posOff sqz qpos qbp (gen ^ j)) :
    ∃ cv, LoadHolds rd sqz (2 * j) (digestScalars cv).1 ∧
      LoadHolds rd sqz (2 * j + 1) (digestScalars cv).2 ∧
      LoadHolds rd sqz (2 * j + 2) (digestScalars (sqCv cv)).1 ∧
      LoadHolds rd sqz (2 * j + 3) (digestScalars (sqCv cv)).2 ∧
      MeaningDecodeQueryBits depth rd [challengeOf (sqCv cv),
        qpos * gen ^ (posOff + j * (192 / depth)), qbp * gen ^ (posOff + j * (192 / depth))] [] := by
  obtain ⟨cv, l0, l1, l2, l3, hd⟩ := h
  rw [os_gen_pow_sq, loadHolds_mul_gen_pow] at l0 l1 l2 l3
  rw [← pow_mul, mul_assoc, mul_assoc, ← pow_add] at hd
  rw [Nat.add_zero] at l0
  exact ⟨cv, l0, l1, l2, l3, hd⟩

/-- **The query positions' squeezes** (G:1144-1157): `nsq` squeezes from the chain state `cv`,
the `j`-th challenge decoded at `posOff + j·(192/depth)`, then the batching challenge `lam` at
the returned `OsSt.k - 1`. -/
theorem osSqueezes_sound {lv : OsLvl} {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) (hb : fn.body = sqLoopOf lv)
    (hdec : ∀ a r, coreProgram.Rel rd lv.decode a r → MeaningDecodeQueryBits lv.depth rd a r)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth)
    (hpo : lv.posOff < 2 ^ 128) {maxSq nsq qpos qbp : ℕ} (hnsq : nsq < 2 ^ 62) {cur : E} {s : OsSt}
    {cv : Digest} {xs : List E} (hat : OsCur rd σ cur s cv xs) {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ (osSqueezes maxSq nsq qpos qbp lv.sqLoop s).1 True kret) :
    OsCur rd σ cur (osSqueezes maxSq nsq qpos qbp lv.sqLoop s).2 (sqCv (sqAll nsq cv).2) xs ∧
      σ (.n ((osSqueezes maxSq nsq qpos qbp lv.sqLoop s).2.k - 1)) =
        challengeOf (sqCv (sqAll nsq cv).2) ∧
      (∀ j < nsq, MeaningDecodeQueryBits lv.depth rd [challengeOf (sqCv (sqAll j cv).2),
        σ (.n qpos) * gen ^ (lv.posOff + j * (192 / lv.depth)),
        σ (.n qbp) * gen ^ (lv.posOff + j * (192 / lv.depth))] []) ∧
      (osSqueezes maxSq nsq qpos qbp lv.sqLoop s).2.co = s.co := by
  unfold osSqueezes at h ⊢
  simp only at h ⊢
  rw [holdsList_append] at h
  obtain ⟨hpre, hsq⟩ := holdsList_true_of (by simp [osHeap, Stmt.noRetList, Stmt.noRet]) h
  clear h
  simp only [osHeap, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, and_true, word_one] at hpre
  obtain ⟨-, -, l0, l1, e2, e3, e4, e5, e6, -, hrun, e7, e8, l9, l10⟩ := hpre
  rw [e4, e3, e2, os_gw_eq (by omega)] at hrun
  rw [e5, e6, os_gw_eq (by omega)] at hrun
  obtain ⟨m, hm, hN, hB⟩ := guarded_loop_sound (P := coreProgram) (f := lv.sqLoop)
    (ps := [gen ^ nsq, σ (.n (s.k + 1)), σ (.n qpos), σ (.n qbp)])
    (B := SqBody rd lv.depth lv.posOff (σ (.n (s.k + 1))) (σ (.n qpos)) (σ (.n qbp)))
    (fun d x hx => sqLoop_step hfind hp hb hdec hdig hpo hx) hrun
  have hmn : m = nsq := gen_pow_inj hm (by omega) hN.symm
  subst hmn
  set sqz := σ (.n (s.k + 1))
  have hchain : ∀ j ≤ m, LoadHolds rd sqz (2 * j) (digestScalars (sqAll j cv).2).1 ∧
      LoadHolds rd sqz (2 * j + 1) (digestScalars (sqAll j cv).2).2 := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [show (digestScalars (sqAll 0 cv).2).1 = σ (.n s.f0) from (congrArg Prod.fst hat.fs).symm]
        exact l0
      · rw [show (digestScalars (sqAll 0 cv).2).2 = σ (.n s.f1) from (congrArg Prod.snd hat.fs).symm]
        exact l1
    | succ j ih =>
      obtain ⟨i0, i1⟩ := ih (by omega)
      obtain ⟨cvj, b0, b1, b2, b3, -⟩ := sqBody_at (hB j (by omega))
      have hc : cvj = (sqAll j cv).2 := digestScalars_injective (Prod.ext (loadHolds_unique b0 i0)
        (loadHolds_unique b1 i1))
      subst hc
      rw [sqAll_succ_snd, show 2 * (j + 1) = 2 * j + 2 by ring]
      exact ⟨b2, by rw [show 2 * j + 2 + 1 = 2 * j + 3 by ring]; exact b3⟩
  obtain ⟨c0, c1⟩ := hchain m le_rfl
  rw [e8, e7, os_gw_eq (by omega), loadHolds_mul_gen_pow] at l9 l10
  have h9 := loadHolds_unique l9 (by simpa using c0)
  have h10 := loadHolds_unique l10 c1
  obtain ⟨⟨cv', hcv', hv⟩, -⟩ := (holds_squeezeT _ _ _ True _).mp hsq
  have hc' : cv' = (sqAll m cv).2 := digestScalars_injective (by rw [← hcv', h9, h10])
  subst hc'
  refine ⟨⟨?_, hat.reads, hat.cursor⟩, ?_, fun j hj => ?_, trivial⟩
  · show (σ (.n (s.k + 16)), σ (.n (s.k + 17))) = _
    rw [show s.k + 16 = s.k + 11 + 5 by ring, show s.k + 17 = s.k + 11 + 6 by ring,
      hv 5 (by omega), hv 6 (by omega)]
    rfl
  · show σ (.n (s.k + 25 - 1)) = _
    rw [show s.k + 25 - 1 = s.k + 11 + 13 by omega, hv 13 (by omega)]
    rfl
  · obtain ⟨cvj, b0, b1, -, -, hd⟩ := sqBody_at (hB j hj)
    obtain ⟨i0, i1⟩ := hchain j (by omega)
    have hc : cvj = (sqAll j cv).2 := digestScalars_injective (Prod.ext (loadHolds_unique b0 i0)
      (loadHolds_unique b1 i1))
    rwa [hc] at hd

/-! ## The residual loop -/

/-- The subspace-vanishing chain from `ch0` (G:1290): `ch ← ch·(ch + vals[t])`. -/
def resChain (vals : List ℕ) (ch0 : E) : ℕ → E
  | 0 => ch0
  | t + 1 => resChain vals ch0 t * (resChain vals ch0 t + eOfNat (vals.getD t 0))

/-- A query's basis product over `cols` coordinates (G:1287-1292). -/
def resProd (a b : ℕ → E) (vals : List ℕ) (ch0 : E) (cols : ℕ) : E :=
  ∏ t ∈ Finset.range cols, (a t + b t * resChain vals ch0 t)

/-- One query of the residual loop at `x`: its position at `qpos·x`, its product over the basis
rows at `basis_a`, `basis_b`, the chain's next entry. -/
def ResBody (rd : Reader) (posOff row cols qo : ℕ) (vals : List ℕ) (qpos ba bb rc qw x : E) :
    Prop :=
  ∃ ch0, LoadHolds rd (qpos * x) posOff ch0 ∧
    (∀ t < cols, LoadHolds rd ba (row + t) (memAt rd ba (row + t)) ∧
      LoadHolds rd bb (row + t) (memAt rd bb (row + t))) ∧
    ∃ r0 wq, LoadHolds rd (rc * x) 0 r0 ∧ LoadHolds rd (qw * x) qo wq ∧
      LoadHolds rd (rc * x) 1 (r0 + wq * resProd (fun t => memAt rd ba (row + t))
        (fun t => memAt rd bb (row + t)) vals ch0 cols)

/-- The value of the chain after coordinate `t`. -/
def resChIdx (t : ℕ) : ℕ := if t = 0 then 8 else 8 * t + 7

theorem resStep_noRet (row val t : ℕ) : Stmt.noRetList (resStep row val t) = true := rfl

theorem resLoop_step {posOff row cols qo : ℕ} {vals : List ℕ} {loop : String} {fn : Fn}
    (hfind : coreProgram.find? loop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hb : fn.body = resLoopBody posOff row cols qo vals loop) (hc : 1 ≤ cols) {d : ℕ}
    {x N qpos ba bb rc qw : E}
    (h : coreProgram.relN rd (d + 1) loop [x, N, qpos, ba, bb, rc, qw] []) :
    ResBody rd posOff row cols qo vals qpos ba bb rc qw x ∧ IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d loop [x * gen, N, qpos, ba, bb, rc, qw] []) := by
  rw [relN_succ_iff hfind, hp, hb, resLoopBody] at h
  obtain ⟨σ, hpar, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hpar
  simp only [holdsList_append] at h
  obtain ⟨hA, h⟩ := holdsList_true_of (by rfl) h
  rw [holdsList_range_flatten _ _ (fun t => resStep_noRet _ _ _)] at h
  obtain ⟨hS, h⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hA h
  obtain ⟨a7, l8, l9, l10, a11, a12⟩ := hA
  obtain ⟨e0, l1, e2, l3, e4, e5, e6, l5, e7, e8, e9, e10, e11, hK, hrec, -⟩ := h
  set A : ℕ → E := fun t => memAt rd (σ (.n 3)) (row + t)
  set B : ℕ → E := fun t => memAt rd (σ (.n 4)) (row + t)
  have hstep : ∀ t < cols - 1,
      σ (.n (resChIdx (t + 1))) = σ (.n (resChIdx t)) * (σ (.n (resChIdx t)) + eOfNat (vals.getD t 0)) ∧
      σ (.n (8 * (t + 1) + 12)) = σ (.n (8 * t + 12)) * (A (t + 1) + B (t + 1) * σ (.n (resChIdx (t + 1)))) ∧
      LoadHolds rd (σ (.n 3)) (row + (t + 1)) (A (t + 1)) ∧
      LoadHolds rd (σ (.n 4)) (row + (t + 1)) (B (t + 1)) := by
    intro t ht
    have h := hS t ht
    simp only [resStep, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
      show t + 1 - 1 = t by omega] at h
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := h
    have hch : (if t + 1 = 1 then 8 else 13 + 8 * t - 6) = resChIdx t := by
      unfold resChIdx; split <;> split <;> omega
    have hpe : (if t + 1 = 1 then 12 else 13 + 8 * t - 1) = 8 * t + 12 := by split <;> omega
    rw [hch] at b1 b2
    rw [hpe] at b7
    have hA : A (t + 1) = σ (.n (13 + 8 * t + 3)) := memAt_of_load b3
    have hB : B (t + 1) = σ (.n (13 + 8 * t + 4)) := memAt_of_load b4
    have hc1 : resChIdx (t + 1) = 13 + 8 * t + 2 := by unfold resChIdx; split <;> omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hc1, b2, b1, b0, word_eOfNat]
    · rw [show 8 * (t + 1) + 12 = 13 + 8 * t + 7 by ring, b7, b6, b5, hA, hB, hc1, mul_comm (σ (.n (13 + 8 * t + 4)))]
    · rw [hA]; exact b3
    · rw [hB]; exact b4
  have hind : ∀ t ≤ cols - 1, σ (.n (resChIdx t)) = resChain vals (σ (.n 8)) t ∧
      σ (.n (8 * t + 12)) = ∏ s ∈ Finset.range (t + 1), (A s + B s * resChain vals (σ (.n 8)) s) := by
    intro t ht
    induction t with
    | zero =>
      refine ⟨rfl, ?_⟩
      simp only [Nat.mul_zero, Nat.zero_add, Finset.prod_range_one, resChain]
      rw [a12, a11, show A 0 = σ (.n 9) from by simpa [A] using memAt_of_load l9,
        show B 0 = σ (.n 10) from by simpa [B] using memAt_of_load l10]
    | succ t ih =>
      obtain ⟨i1, i2⟩ := ih (by omega)
      obtain ⟨s1, s2, -, -⟩ := hstep t (by omega)
      refine ⟨by rw [s1, i1]; rfl, ?_⟩
      rw [s2, i2, s1, i1, Finset.prod_range_succ _ (t + 1)]
      rfl
  have hpe : σ (.n (if cols = 1 then 12 else 13 + 8 * (cols - 1) - 1)) =
      resProd A B vals (σ (.n 8)) cols := by
    rw [show (if cols = 1 then 12 else 13 + 8 * (cols - 1) - 1) = 8 * (cols - 1) + 12 by split <;> omega,
      (hind (cols - 1) le_rfl).2, show cols - 1 + 1 = cols by omega]
    rfl
  rw [e9, e8, e7, word_gen] at hK hrec
  refine ⟨⟨σ (.n 8), by rw [← a7]; exact l8, fun t ht => ?_, σ (.n (13 + 8 * (cols - 1) + 1)),
    σ (.n (13 + 8 * (cols - 1) + 3)), by rw [← e0]; exact l1, by rw [← e2]; exact l3, ?_⟩,
    hK, fun hne => ?_⟩
  · rcases t with _ | t
    · exact ⟨by simpa using loadHolds_memAt l9, by simpa using loadHolds_memAt l10⟩
    · obtain ⟨-, -, h3, h4⟩ := hstep t (by omega)
      exact ⟨h3, h4⟩
  · rw [← e6]
    convert l5 using 2
    rw [e5, e4, hpe]
  · have := hrec hne
    simp only [List.map_cons, List.map_nil, e11, e10, word_gen] at this
    exact this

end
end LeanVM.Guest.B1
