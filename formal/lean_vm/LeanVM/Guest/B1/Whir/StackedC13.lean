/-
  LeanVM.Guest.B1.Whir.StackedC13

  `open_stacked`'s residual chains and out-of-domain weights at their honest values.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC12
public import LeanVM.Guest.B1.Whir.StackedEnd

/-!
# The residual chains and the out-of-domain weights, honestly (TRIAGE #36)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The residual chains -/

/-- A level's residual values from its first: the chain's size and pointer `chv`, its first entry,
the loop's bound and arguments, `inner[lvl] = i0`, `beta = b`, `chain[n] = r`, the product and the
next inner sum. -/
def osResVals (maxQ nq : ℕ) (chv i0 b r : E) : List E :=
  [osGw (maxQ + 1), chv, 0, 1, osGw nq, 1 + osGw nq, 1, osGw nq, i0, b, r, b * r, i0 + b * r]

theorem os_one_add_gw_inK {nq : ℕ} (h : nq < 2 ^ 128) : IsInK (1 + osGw nq) := by
  rw [os_gw_eq h]; exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK nq)

/-- **A level's residual chain** at its honest values (the loop's call not checked here). -/
theorem osResidual_complete {maxQ ich ba bb lvl k : ℕ} {lv : OsLvl} (hnq : lv.queries < 2 ^ 128)
    {chv ichv betav i0 b r : E} (hich : σ (.n ich) = ichv) (hbe : σ (.n osBetas) = betav)
    (l0 : LoadHolds rd chv 0 0) (l1 : LoadHolds rd ichv lvl i0) (l2 : LoadHolds rd betav lvl b)
    (l3 : LoadHolds rd chv lv.queries r) (l4 : LoadHolds rd ichv (lvl + 1) (i0 + b * r)) {kret : List E → Prop}
    (hcall : 1 + osGw lv.queries ≠ 0 → C lv.resLoop [1, osGw lv.queries, σ (.n osQpos), σ (.n ba), σ (.n bb), chv,
      σ (.n osQw)] [])
    (hv : ∀ j < 13, σ (.n (k + j)) = (osResVals maxQ lv.queries chv i0 b r).getD j 0) :
    Stmt.HoldsList C rd σ (osResidual maxQ ich ba bb lvl lv k) True kret := by
  have e := fun j (hj : j < 13) => hv j hj
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
  have e6 := e 6 (by omega); have e7 := e 7 (by omega); have e8 := e 8 (by omega)
  have e9 := e 9 (by omega); have e10 := e 10 (by omega); have e11 := e 11 (by omega)
  have e12 := e 12 (by omega)
  simp only [osResVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  unfold osResidual osHeap
  simp only [List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_zero,
    word_one]
  refine ⟨e0, trivial, e2, by rw [e1, e2]; exact l0, e3, e4, by rw [e5, e3, e4], e6, e7,
    by rw [e5]; exact os_one_add_gw_inK hnq, fun h => by simp only [List.map_cons, List.map_nil]; rw [e6, e7, e1]; exact hcall (by rwa [e5] at h),
    by rw [e8, hich]; exact l1,
    by rw [e9, hbe]; exact l2, by rw [e10, e1]; exact l3, by rw [e11, e9, e10], by rw [e12, e8, e11],
    by rw [e12, hich]; exact l4⟩

theorem os_zipIdx_map_rangeD {α β : Type} [Inhabited α] (f : α × ℕ → β) (l : List α) :
    l.zipIdx.map f = (List.range l.length).map fun i => f (l.getD i default, i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

/-- The residual chains' values, level `lvl`'s from `13·lvl`. -/
def osResidualsVals (maxQ : ℕ) (lvs : List OsLvl) (chv i0 b r : ℕ → E) : List E :=
  ((List.range lvs.length).map fun lvl =>
    osResVals maxQ (lvs.getD lvl default).queries (chv lvl) (i0 lvl) (b lvl) (r lvl)).flatten

theorem os_length_residualsVals (maxQ : ℕ) (lvs : List OsLvl) (chv i0 b r : ℕ → E) :
    (osResidualsVals maxQ lvs chv i0 b r).length = 13 * lvs.length := by
  unfold osResidualsVals
  rw [oq_length_flatten_uniform _ 13 (fun _ => rfl)]

/-- **Every level's residual chain** at its honest values. -/
theorem osResiduals_complete {maxQ ich ba bb k : ℕ} {lvs : List OsLvl}
    (hnq : ∀ lv ∈ lvs, lv.queries < 2 ^ 128) {chv i0 b r : ℕ → E} {ichv betav : E}
    (hich : σ (.n ich) = ichv) (hbe : σ (.n osBetas) = betav)
    (hm : ∀ lvl < lvs.length, LoadHolds rd (chv lvl) 0 0 ∧ LoadHolds rd ichv lvl (i0 lvl) ∧
      LoadHolds rd betav lvl (b lvl) ∧ LoadHolds rd (chv lvl) (lvs.getD lvl default).queries (r lvl) ∧
      LoadHolds rd ichv (lvl + 1) (i0 lvl + b lvl * r lvl)) {kret : List E → Prop}
    (hcall : ∀ lvl < lvs.length, 1 + osGw (lvs.getD lvl default).queries ≠ 0 →
      C (lvs.getD lvl default).resLoop [1, osGw (lvs.getD lvl default).queries, σ (.n osQpos), σ (.n ba), σ (.n bb),
        chv lvl, σ (.n osQw)] [])
    (hv : ∀ j < 13 * lvs.length, σ (.n (k + j)) = (osResidualsVals maxQ lvs chv i0 b r).getD j 0) :
    Stmt.HoldsList C rd σ (osResiduals maxQ ich ba bb k lvs) True kret := by
  unfold osResiduals
  rw [os_zipIdx_map_rangeD, holdsList_range_flatten _ _ (fun _ => rfl)]
  refine ⟨fun lvl hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, m4⟩ := hm lvl hl
  have hlv : lvs.getD lvl default ∈ lvs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; exact List.getElem_mem _
  refine osResidual_complete (hnq _ hlv) hich hbe m0 m1 m2 m3 m4 (hcall lvl hl) fun j hj => ?_
  rw [Nat.add_assoc, hv _ (by nlinarith), osResidualsVals,
    oq_getD_flatten_uniform _ 13 (fun _ => rfl) _ lvl j hl hj]

/-! ## The out-of-domain weights -/

/-- An out-of-domain weight's values from its first: the scalar `sc`, then each factor's six, its
running product last. -/
def osOodWVals (sc : E) (z c : ℕ → E) (n : ℕ) : List E :=
  sc :: ((List.range n).map fun t => [1, z t, 1 + z t, c t, 1 + z t + c t,
    sc * ∏ u ∈ Finset.range (t + 1), (1 + z u + c u)]).flatten

theorem os_length_oodWVals (sc : E) (z c : ℕ → E) (n : ℕ) : (osOodWVals sc z c n).length = 1 + 6 * n := by
  simp only [osOodWVals, List.length_cons]
  rw [oq_length_flatten_uniform _ 6 (fun _ => rfl)]; ring

/-- **An out-of-domain weight** at its honest values: the scalar read, each factor `1 + z_t + c_t`
from its point's coordinate and the terminal point's, the running product. -/
theorem osOodWeight_complete {yrLog tch zf ris ol k : ℕ} {oodv oodzv : E} (hood : σ (.n osOod) = oodv)
    (hoz : σ (.n osOodz) = oodzv) {sc : E} {z c : ℕ → E} (hsc : LoadHolds rd oodv (ol * 4) sc)
    (hz : ∀ t < zf + yrLog, LoadHolds rd oodzv (ol * 22 + t) (z t))
    (hc : ∀ t < zf + yrLog, LoadHolds rd (σ (.n (osOodSrc tch zf ris t).1)) (osOodSrc tch zf ris t).2 (c t))
    {kret : List E → Prop}
    (hv : ∀ j < 1 + 6 * (zf + yrLog), σ (.n (k + j)) = (osOodWVals sc z c (zf + yrLog)).getD j 0) :
    Stmt.HoldsList C rd σ (osOodWeight yrLog tch zf ris ol 0 k) True kret := by
  set n := zf + yrLog
  have h0 : σ (.n k) = sc := by simpa [osOodWVals] using hv 0 (by omega)
  have hf : ∀ t < n, ∀ i < 6, σ (.n (k + 1 + 6 * t + i)) =
      [1, z t, 1 + z t, c t, 1 + z t + c t, sc * ∏ u ∈ Finset.range (t + 1), (1 + z u + c u)].getD i 0 := by
    intro t ht i hi
    rw [show k + 1 + 6 * t + i = k + (6 * t + i + 1) by ring, hv _ (by omega), osOodWVals,
      List.getD_cons_succ, oq_getD_flatten_uniform _ 6 (fun _ => rfl) _ t i ht hi]
  unfold osOodWeight osOodFacs
  rw [os_zipIdx_map_range, List.map_map]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, Nat.zero_mul, Nat.add_zero]
  refine ⟨by rw [h0, hood]; exact hsc, ?_⟩
  rw [holdsList_range_flatten _ _ (fun _ => rfl)]
  refine ⟨fun t ht => ?_, trivial⟩
  have f0 := hf t ht 0 (by omega); have f1 := hf t ht 1 (by omega); have f2 := hf t ht 2 (by omega)
  have f3 := hf t ht 3 (by omega); have f4 := hf t ht 4 (by omega); have f5 := hf t ht 5 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at f0 f1 f2 f3 f4 f5
  have hsrc : (if t < zf then (osFch, ris + t) else (tch, t - zf)) = osOodSrc tch zf ris t := rfl
  simp only [Function.comp, osOodFac, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one, hsrc]
  refine ⟨f0, by rw [f1, hoz]; exact hz t ht, by rw [f2, f0, f1], by rw [f3]; exact hc t ht, by rw [f4, f2, f3],
    ?_⟩
  rw [f5, f4]
  split
  · rename_i h; subst h
    rw [h0]; simp
  · rename_i h
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have := hf t' (by omega) 5 (by omega)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at this
    rw [show k + 1 + 6 * (t' + 1) - 1 = k + 1 + 6 * t' + 5 by omega, this, Finset.prod_range_succ _ (t' + 1)]
    ring

/-- The running sum plus a weight `w`. -/
def osAccAdd (acc : Option E) (w : E) : E := match acc with | none => w | some a => a + w

/-- The running sum's added value, none before the first weight. -/
def osAccTail (acc : Option E) (w : E) : List E := match acc with | none => [] | some a => [a + w]

/-- The out-of-domain weights' values of the levels `ol ..` (one sample each), `acc` the running
sum before them. -/
def osOodWsVals (yrLog : ℕ) (sc : ℕ → E) (z c : ℕ → ℕ → E) : ℕ → ℕ → List OsLvl → Option E → List E
  | _, _, [], _ => []
  | prev, ol, lv :: rest, acc =>
    osOodWVals (sc ol) (z ol) (c ol) (prev - yrLog + yrLog) ++
      osAccTail acc (sc ol * ∏ u ∈ Finset.range (prev - yrLog + yrLog), (1 + z ol u + c ol u)) ++
      osOodWsVals yrLog sc z c lv.logCols (ol + 1) rest
        (some (osAccAdd acc (sc ol * ∏ u ∈ Finset.range (prev - yrLog + yrLog), (1 + z ol u + c ol u))))

/-- The running sum after the levels `ol ..`. -/
def osOodWsAcc (yrLog : ℕ) (sc : ℕ → E) (z c : ℕ → ℕ → E) : ℕ → ℕ → List OsLvl → Option E → Option E
  | _, _, [], acc => acc
  | prev, ol, lv :: rest, acc =>
    osOodWsAcc yrLog sc z c lv.logCols (ol + 1) rest
      (some (osAccAdd acc (sc ol * ∏ u ∈ Finset.range (prev - yrLog + yrLog), (1 + z ol u + c ol u))))

theorem os_oodW_last (sc : E) (z c : ℕ → E) {n : ℕ} (hn : 0 < n) :
    (osOodWVals sc z c n).getD (6 * n) 0 = sc * ∏ u ∈ Finset.range n, (1 + z u + c u) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show 6 * (m + 1) = 6 * m + 5 + 1 by ring, osOodWVals, List.getD_cons_succ,
    oq_getD_flatten_uniform _ 6 (fun _ => rfl) _ m 5 (by omega) (by omega)]
  rfl

/-- **The out-of-domain weights** at their honest values, summed into the running sum. -/
theorem osOodWeights_complete {yrLog tch : ℕ} {oodv oodzv : E} (hood : σ (.n osOod) = oodv)
    (hoz : σ (.n osOodz) = oodzv) {sc : ℕ → E} {z c : ℕ → ℕ → E} {kret : List E → Prop} :
    ∀ (lvs : List OsLvl) (ol prev : ℕ) (acc : Option ℕ) (accv : Option E) (k : ℕ),
      (∀ lv ∈ lvs, lv.oodHere = 1) → (acc = none ↔ accv = none) →
      (∀ a v, acc = some a → accv = some v → σ (.n a) = v) →
      (∀ i < lvs.length, 0 < osPrevColsAt lvs prev i - yrLog + yrLog ∧
        LoadHolds rd oodv ((ol + i) * 4) (sc (ol + i)) ∧
        (∀ t < osPrevColsAt lvs prev i - yrLog + yrLog, LoadHolds rd oodzv ((ol + i) * 22 + t) (z (ol + i) t)) ∧
        ∀ t < osPrevColsAt lvs prev i - yrLog + yrLog,
          LoadHolds rd (σ (.n (osOodSrc tch (osPrevColsAt lvs prev i - yrLog) (lvs.getD i default).foldsOff t).1))
            (osOodSrc tch (osPrevColsAt lvs prev i - yrLog) (lvs.getD i default).foldsOff t).2 (c (ol + i) t)) →
      (∀ j < (osOodWsVals yrLog sc z c prev ol lvs accv).length,
        σ (.n (k + j)) = (osOodWsVals yrLog sc z c prev ol lvs accv).getD j 0) →
      Stmt.HoldsList C rd σ (osOodWeights yrLog tch prev ol lvs acc k).1 True kret ∧
        (osOodWeights yrLog tch prev ol lvs acc k).2.2 = k + (osOodWsVals yrLog sc z c prev ol lvs accv).length ∧
        ((osOodWeights yrLog tch prev ol lvs acc k).2.1 = none ↔ osOodWsAcc yrLog sc z c prev ol lvs accv = none) ∧
        ∀ a v, (osOodWeights yrLog tch prev ol lvs acc k).2.1 = some a →
          osOodWsAcc yrLog sc z c prev ol lvs accv = some v → σ (.n a) = v
  | [], _, _, acc, accv, k, _, hn, hs, _, _ => ⟨trivial, by simp [osOodWeights, osOodWsVals], hn, hs⟩
  | lv :: rest, ol, prev, acc, accv, k, hood1, hn, hs, hm, hv => by
    have h1 : lv.oodHere = 1 := hood1 lv (by simp)
    obtain ⟨hpos, m0, mz, mc⟩ := hm 0 (by simp)
    simp only [osPrevColsAt, ↓reduceIte, List.getD_cons_zero, Nat.add_zero] at hpos m0 mz mc
    set n := prev - yrLog + yrLog
    set w := sc ol * ∏ u ∈ Finset.range n, (1 + z ol u + c ol u)
    have hvs : osOodWsVals yrLog sc z c prev ol (lv :: rest) accv =
        osOodWVals (sc ol) (z ol) (c ol) n ++ osAccTail accv w ++
          osOodWsVals yrLog sc z c lv.logCols (ol + 1) rest (some (osAccAdd accv w)) := rfl
    have hacc : osOodWsAcc yrLog sc z c prev ol (lv :: rest) accv =
        osOodWsAcc yrLog sc z c lv.logCols (ol + 1) rest (some (osAccAdd accv w)) := rfl
    rw [hvs] at hv ⊢
    rw [hacc]
    obtain ⟨hv12, g3⟩ := os_look_app hv
    obtain ⟨g1, g2⟩ := os_look_app hv12
    have hw1 := osOodWeight_complete (C := C) (rd := rd) (kret := kret) (tch := tch) (ris := lv.foldsOff) hood hoz m0 mz mc
      (k := k) (fun j hj => g1 j (by rw [os_length_oodWVals]; exact hj))
    have hlast : σ (.n (k + 6 * n)) = w := by
      rw [g1 _ (by rw [os_length_oodWVals]; omega), os_oodW_last _ _ _ hpos]
    have hrest := fun acc' k' => osOodWeights_complete (yrLog := yrLog) (tch := tch) (sc := sc) (z := z)
      (c := c) (kret := kret) hood hoz rest (ol + 1) lv.logCols acc'
      (some (osAccAdd accv w)) k' (fun lv' h' => hood1 lv' (by simp [h']))
    have hmr : ∀ i < rest.length, 0 < osPrevColsAt rest lv.logCols i - yrLog + yrLog ∧
        LoadHolds rd oodv ((ol + 1 + i) * 4) (sc (ol + 1 + i)) ∧
        (∀ t < osPrevColsAt rest lv.logCols i - yrLog + yrLog,
          LoadHolds rd oodzv ((ol + 1 + i) * 22 + t) (z (ol + 1 + i) t)) ∧
        ∀ t < osPrevColsAt rest lv.logCols i - yrLog + yrLog,
          LoadHolds rd (σ (.n (osOodSrc tch (osPrevColsAt rest lv.logCols i - yrLog) (rest.getD i default).foldsOff t).1))
            (osOodSrc tch (osPrevColsAt rest lv.logCols i - yrLog) (rest.getD i default).foldsOff t).2
            (c (ol + 1 + i) t) := fun i hi => by
      have := hm (i + 1) (by simp; omega)
      have e : osPrevColsAt (lv :: rest) prev (i + 1) = osPrevColsAt rest lv.logCols i := by
        cases i <;> simp [osPrevColsAt]
      rw [e, List.getD_cons_succ, show ol + (i + 1) = ol + 1 + i by ring] at this
      exact this
    have hnr : Stmt.noRetList (osOodWeight yrLog tch (prev - yrLog) lv.foldsOff ol 0 k) = true := by
      unfold osOodWeight osOodFacs
      rw [os_zipIdx_map_range, List.map_map]
      show Stmt.noRetList (List.flatten _) = true
      rw [noRetList_flatten_range _ _ (fun _ => rfl)]
    have hl1 : (osOodWVals (sc ol) (z ol) (c ol) n).length = 1 + 6 * n := os_length_oodWVals _ _ _ _
    simp only [osOodWeights, h1, List.range_one, List.foldl_cons, List.foldl_nil]
    cases acc with
    | none =>
      have hav : accv = none := hn.mp rfl
      subst hav
      simp only [osAccTail, osAccAdd, List.append_nil] at g2 g3 ⊢
      obtain ⟨r1, r2, r3, r4⟩ := hrest (some (k + 6 * n)) (k + 6 * n + 1) (by simp) (fun a v ha hv' => by
          simp only [Option.some.injEq] at ha hv'
          subst ha hv'
          exact hlast) hmr (fun j hj => by
        rw [show k + 6 * n + 1 + j = k + (osOodWVals (sc ol) (z ol) (c ol) n).length + j by rw [hl1]; ring]
        simpa [osAccAdd] using g3 j (by simpa [osAccAdd] using hj))
      simp only [osAccAdd] at r2 r3 r4
      refine ⟨?_, by rw [r2]; simp only [List.length_append, hl1]; ring, r3, r4⟩
      simp only [List.nil_append, holdsList_append]
      exact (holdsList_noRet _ hnr _ _).mpr ⟨hw1, r1⟩
    | some a =>
      obtain ⟨av, rfl⟩ : ∃ av, accv = some av := by
        cases h' : accv with
        | none => exact absurd (hn.mpr h') (by simp)
        | some v => exact ⟨v, rfl⟩
      simp only [osAccTail, osAccAdd] at g2 g3 ⊢
      have hav := hs a av rfl rfl
      have ha : σ (.n (k + 6 * n + 1)) = av + w := by
        have := g2 0 (by simp)
        simp only [List.getD_cons_zero, Nat.add_zero] at this
        rw [← this, hl1]; ring_nf
      obtain ⟨r1, r2, r3, r4⟩ := hrest (some (k + 6 * n + 1)) (k + 6 * n + 2) (by simp) (fun a' v ha' hv' => by
          simp only [Option.some.injEq] at ha' hv'
          subst ha' hv'
          exact ha) hmr (fun j hj => by
        have := g3 j (by simpa [osAccAdd] using hj)
        simp only [List.length_append, List.length_cons, List.length_nil, hl1] at this
        rw [show k + 6 * n + 2 + j = k + (1 + 6 * n + (0 + 1)) + j by ring, this]
        rfl)
      simp only [osAccAdd] at r2 r3 r4
      refine ⟨?_, by rw [r2]; simp only [List.length_append, hl1, List.length_cons, List.length_nil]; ring, r3, r4⟩
      simp only [List.nil_append, holdsList_append]
      refine (holdsList_noRet _ hnr _ _).mpr ⟨hw1, (holdsList_noRet _ rfl _ _).mpr ⟨?_, r1⟩⟩
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      rw [ha, hav, hlast]

end
end LeanVM.Guest.B1
