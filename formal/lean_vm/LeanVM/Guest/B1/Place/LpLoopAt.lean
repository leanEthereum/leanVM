/-
  LeanVM.Guest.B1.Place.LpLoopAt

  `level_positions`' loop placed (`RelAtIn`): one iteration, its decoder call before its tail,
  and the loop from its first iteration, its decoders' frame runs its data. After the old squeeze
  loop's `Place/SqAt.lean`.
-/

module

public import LeanVM.Guest.B1.Place.Lp

/-!
# `level_positions`' loop, placed

The loop's body (`lpLoopBody d cd name`) is straight-line: before its `ret []` (`lpLoopPre`) it
allocates nothing, has no `frameAddr`, calls `decode_query_windows__L{d}_L{cd}` and its tail
(`lpLoopPre_calls`), and loads only through the row `sqz·x^5`, at offsets below `10`
(`lpLoopPre_loads`). A loop helper places its tail at `fp + fs L`, then its other callees:
iteration `j` of `n` takes `(n - j + 1)·fs L + (n - j)·fs D` words (`lpTot`), its decoder at
`lpDecAt`.

`lpLoop_iter`: one iteration from its decoder's and its tail's placed relations.
`lpLoop_relAtIn`: the loop from iteration `0` at `fp`, from `decode_query_windows`' placed
completeness (`QwDecodeAtD`), on every memory holding the capacity chain at `sqz` and the caller's
words (`LpMem`, its decoders at `lpDecAt`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Protocol.Compile (challengeOf)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## The body's statements -/

/-- The loop's body before its final `ret []`. -/
def lpLoopPre (d cd : ℕ) (name : String) : List Stmt :=
  lpIterA d cd ++ osLoopTailA (lpIterTail d) ++
    [.callIf (.n (lpIterTail d + 2)) name
      (.n (lpIterTail d + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1))]

theorem lpLoopBody_pre (d cd : ℕ) (name : String) :
    lpLoopBody d cd name = lpLoopPre d cd name ++ [.ret []] := by
  rw [lpIterBody_eq, osLoopTail_split, lpLoopPre]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem lpLoopPre_flat (d cd : ℕ) (name : String) : (lpLoopPre d cd name).all Stmt.flat = true := by
  have h := lpIterA_flat d cd
  rw [lpLoopPre, List.all_append, h]
  rfl

theorem lp_osPowSteps_mem_mul (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ),
    ∀ s ∈ (osPowSteps x ds acc k).1, ∃ d a b, s = .atom (.mul d a b)
  | [], _, _, s, hs => by simp [osPowSteps] at hs
  | true :: ds, acc, k, s, hs => by
    simp only [osPowSteps, ↓reduceIte, List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
    · exact lp_osPowSteps_mem_mul x ds _ _ s hs
  | false :: ds, acc, k, s, hs => by
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨_, _, _, rfl⟩
    · exact lp_osPowSteps_mem_mul x ds _ _ s hs

theorem lp_fm_pow_nil {α : Type} (F : Stmt → Option α) (hm : ∀ d a b, F (.atom (.mul d a b)) = none)
    (x : ℕ) (ds : List Bool) (acc k : ℕ) : (osPowSteps x ds acc k).1.filterMap F = [] :=
  List.filterMap_eq_nil_iff.mpr fun s hs => by
    obtain ⟨d, a, b, rfl⟩ := lp_osPowSteps_mem_mul x ds acc k s hs; exact hm d a b

theorem lp_pow_straight (x : ℕ) (ds : List Bool) (acc k : ℕ) :
    (osPowSteps x ds acc k).1.all Main.Stmt.straight = true :=
  List.all_eq_true.mpr fun s hs => by
    obtain ⟨d, a, b, rfl⟩ := lp_osPowSteps_mem_mul x ds acc k s hs; rfl

theorem lpLoopPre_straight (d cd : ℕ) (name : String) :
    (lpLoopPre d cd name).all Main.Stmt.straight = true := by
  simp only [lpLoopPre, lpIterA, List.all_append, lp_pow_straight, Bool.and_true]
  rfl

theorem lpLoopPre_allocs (d cd : ℕ) (name : String) :
    (lpLoopPre d cd name).filterMap Main.Stmt.allocSz = [] := by
  simp only [lpLoopPre, lpIterA, List.filterMap_append,
    lp_fm_pow_nil Main.Stmt.allocSz (fun _ _ _ => rfl), List.append_nil]
  rfl

theorem lpLoopPre_addrs (d cd : ℕ) (name : String) :
    (lpLoopPre d cd name).filterMap Main.Stmt.addrS = [] := by
  simp only [lpLoopPre, lpIterA, List.filterMap_append,
    lp_fm_pow_nil Main.Stmt.addrS (fun _ _ _ => rfl), List.append_nil]
  rfl

/-- The decoder call's arguments. -/
def lpDecArgs (d : ℕ) : List V :=
  [.n 39, .n (40 + osPowLen (192 / d)), .n (40 + osPowLen (192 / d) + 1), .n 5]

/-- The calls of the loop's body: the decoder, then the tail. -/
def lpCallsS (d cd : ℕ) (name : String) : List (Option V × String × List V × List V) :=
  [(none, qwDecName d cd, lpDecArgs d, []),
    (some (.n (lpIterTail d + 2)), name,
      .n (lpIterTail d + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1), [])]

theorem lpLoopPre_calls (d cd : ℕ) (name : String) :
    (lpLoopPre d cd name).filterMap Main.Stmt.callS = lpCallsS d cd name := by
  simp only [lpLoopPre, lpIterA, List.filterMap_append,
    lp_fm_pow_nil Main.Stmt.callS (fun _ _ _ => rfl), List.append_nil]
  rfl

theorem lpLoopPre_loadsEq (d cd : ℕ) (name : String) :
    (lpLoopPre d cd name).filterMap Stmt.loadS =
      (List.range 10).map fun i => ((.n 9 : V), i) := by
  simp only [lpLoopPre, lpIterA, List.filterMap_append,
    lp_fm_pow_nil Stmt.loadS (fun _ _ _ => rfl), List.append_nil]
  rfl

theorem lpLoopPre_loads (d cd : ℕ) (name : String) :
    ∀ q ∈ (lpLoopPre d cd name).filterMap Stmt.loadS, q.1 = .n 9 ∧ q.2 < 10 := by
  intro q hq
  rw [lpLoopPre_loadsEq] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  exact ⟨rfl, List.mem_range.mp hi⟩

/-! ## One iteration -/

/-- The calls the decoder's arguments pin: only the decoder's, to `dargs`. -/
def lpDecRel (d cd : ℕ) (dargs : List E) : CallRel := fun f a _ ↦ f = qwDecName d cd → a = dargs

/-- **One iteration of `level_positions`' loop, placed at `fp`**: its tail at `fp + fs L` (or
skipped at the last), its decoder after the tail's `m` words, its loads through the row in `R`. -/
theorem lpLoop_iter (fs : String → ℕ) (cert : String → V → ℕ) {d cd : ℕ} {name : String}
    {fn : Fn} (hfind : coreProgram.find? name = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = lpLoopBody d cd name) (hlp : coreProgram.loop name = true)
    (hne : name ≠ qwDecName d cd) (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d)
    {rd : Reader} {R Rd Dd Dt : ℕ → Prop} {X N sqz pos wp tabs : E}
    {cap : List E} (hcl : cap.length = 5) (hcan : AllCanonical cap) (fp : ℕ) {m : ℕ}
    (hrow : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) i (cap.getD i 0))
    (hnext : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) (5 + i) ((capOf (⟨cap, []⟩ : Fs).perm).getD i 0))
    (hdec : RelAtIn coreProgram fs cert rd Rd Dd (fp + fs name + m) (fs (qwDecName d cd))
      (qwDecName d cd) [challengeOf (⟨cap, []⟩ : Fs).perm, pos * X ^ (192 / d), wp * X ^ (192 / d),
        tabs] [])
    (hRd : ∀ i, Rd i → R i) (hK : IsInK (X * gen + N))
    (htail : if X * gen + N ≠ 0 then
      RelAtIn coreProgram fs cert rd R Dt (fp + fs name) m name [X * gen, N, sqz, pos, wp, tabs] []
      else m = fs name)
    (hreg : ∀ t < 10, ∃ i, (sqz * X ^ 5).limb 0 * Parameters.addressOfIndex t =
        Parameters.addressOfIndex i ∧ R i) :
    RelAtIn coreProgram fs cert rd R (fun i => Dd i ∨ (X * gen + N ≠ 0 ∧ Dt i)) fp
      (fs name + m + fs (qwDecName d cd)) name [X, N, sqz, pos, wp, tabs] [] := by
  obtain ⟨σ, hpar, hA, hg, hta⟩ := lpIter_completeC
    (C := lpDecRel d cd [challengeOf (⟨cap, []⟩ : Fs).perm, pos * X ^ (192 / d), wp * X ^ (192 / d),
      tabs]) (rd := rd) d cd hpw X N sqz pos wp tabs cap hcl hcan hrow hnext (fun _ => rfl)
  have hpv : σ (.n 0) = X ∧ σ (.n 1) = N ∧ σ (.n 2) = sqz ∧ σ (.n 3) = pos ∧ σ (.n 4) = wp ∧
      σ (.n 5) = tabs := by
    simpa [osParams, List.range_succ] using hpar
  have hm : ∀ s ∈ lpIterA d cd, StmtOk (lpDecRel d cd [challengeOf (⟨cap, []⟩ : Fs).perm,
      pos * X ^ (192 / d), wp * X ^ (192 / d), tabs]) rd σ s :=
    fun s hs => hA s (List.mem_append_left _ hs)
  have h6 : σ (.n 6) = σ (.n 0) * σ (.n 0) :=
    hm (.atom (.mul (.n 6) (.n 0) (.n 0))) (by simp [lpIterA])
  have h7 : σ (.n 7) = σ (.n 6) * σ (.n 6) :=
    hm (.atom (.mul (.n 7) (.n 6) (.n 6))) (by simp [lpIterA])
  have h8 : σ (.n 8) = σ (.n 7) * σ (.n 0) :=
    hm (.atom (.mul (.n 8) (.n 7) (.n 0))) (by simp [lpIterA])
  have h9 : σ (.n 9) = σ (.n 2) * σ (.n 8) :=
    hm (.atom (.mul (.n 9) (.n 2) (.n 8))) (by simp [lpIterA])
  have hσ9 : σ (.n 9) = sqz * X ^ 5 := by
    rw [h9, h8, h7, h6, hpv.1, hpv.2.2.1]; ring
  have hdargs : (lpDecArgs d).map σ = [challengeOf (⟨cap, []⟩ : Fs).perm, pos * X ^ (192 / d),
      wp * X ^ (192 / d), tabs] :=
    hm (.call (qwDecName d cd) (lpDecArgs d) []) (by simp [lpIterA, lpDecArgs]) rfl
  have hpre : fn.body = lpLoopPre d cd name ++ [.ret []] := hb.trans (lpLoopBody_pre d cd name)
  have hst := lpLoopPre_straight d cd name
  set es := (lpLoopPre d cd name).flatMap (Main.slEvs σ) with hes_def
  have hw : walk σ fn.body = .ret es [] := by rw [hpre]; exact Main.walk_straight σ [] _ hst
  have hholds : Stmt.HoldsList (lpDecRel d cd [challengeOf (⟨cap, []⟩ : Fs).perm,
      pos * X ^ (192 / d), wp * X ^ (192 / d), tabs]) rd σ fn.body False (fun rs => rs = []) := by
    rw [hpre, holdsList_flat_ret _ (lpLoopPre_flat d cd name)]
    refine ⟨?_, rfl⟩
    rw [lpLoopPre, allOk_append]
    exact ⟨hA, allOk_cons.mpr ⟨⟨by rw [hg]; exact hK, fun _ h => absurd h hne⟩, allOk_nil⟩⟩
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    have := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hfind))
      hholds
    rw [hw] at this
    exact fun e he => (this.1 e he).1
  obtain ⟨had, hal, hadr, hcl'⟩ := Main.straight_parts σ _ hst
  have hal0 : allocs σ es = [] := by rw [hal, lpLoopPre_allocs]; rfl
  have hcalls : calls es = [⟨qwDecName d cd, lpDecArgs d, [], true⟩] ++
      [⟨name, .n (lpIterTail d + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1), [],
        decide (σ (.n (lpIterTail d + 2)) ≠ 0)⟩] := by
    rw [hcl', lpLoopPre_calls]; rfl
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun i => Dd i ∨ (X * gen + N ≠ 0 ∧ Dt i))
    (Dk := fun i => False ∨ (true = true ∧ Dd i)) (Rt := R) (Dt := Dt) (fp := fp) (m := m)
    (N := fs (qwDecName d cd)) (args := [X, N, sqz, pos, wp, tabs]) (rets := []) hfind hlp
    (by rw [hp]; exact hpar) hw rfl hev hcalls ?_
    (by rw [had, lpLoopPre_allocs, hal0]; rfl)
    (fun q hq' => by rw [hadr, lpLoopPre_addrs] at hq'; simp at hq')
    ?_ (fun i hi => Or.inl hi) (fun A hA => ?_) ?_
  · rwa [hal0, List.sum_nil, Nat.add_zero] at h
  · simp only [hg]
    split
    · next hc =>
      have hne' : X * gen + N ≠ 0 := by simpa using hc
      rw [List.map_nil, hta]
      simpa [hne'] using htail
    · next hc =>
      have h0 : X * gen + N = 0 := by simpa using hc
      simpa [h0] using htail
  · rw [hal0, List.sum_nil, Nat.add_zero]
    refine ⟨fs (qwDecName d cd), 0, Rd, Dd, rfl, fun i hi => Or.inl (Or.inl (hRd i hi)), ?_, rfl,
      fun i hi => hi⟩
    simp only [↓reduceIte, List.map_nil]
    rw [hdargs]; exact hdec
  · rw [loadAddrs_straight σ _ hst] at hA
    obtain ⟨⟨p, off⟩, hq', rfl⟩ := List.mem_map.mp hA
    have hql := lpLoopPre_loads d cd name _ hq'
    obtain ⟨i, hi, hR⟩ := hreg off hql.2
    refine ⟨i, ?_, Or.inr (Or.inl hR)⟩
    have hp9 : p = .n 9 := hql.1
    rw [hp9, hσ9]; exact hi
  · intro i hi
    rcases hi with hi | ⟨ht, hi⟩
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, hi⟩))
    · refine Or.inr (Or.inr ⟨?_, hi⟩)
      simp only [hg]
      exact decide_eq_true ht

/-! ## The loop -/

/-- The words of the loop from iteration `j` of `n`: each iteration's frame and decoder, then the
skipped tail's frame. -/
def lpTot (fs : String → ℕ) (name dec : String) (n j : ℕ) : ℕ :=
  (n - j + 1) * fs name + (n - j) * fs dec

/-- The tail's words after iteration `j`. -/
def lpTailTot (fs : String → ℕ) (name dec : String) (n j : ℕ) : ℕ :=
  if j + 1 < n then lpTot fs name dec n (j + 1) else fs name

/-- Iteration `j`'s decoder, the loop entered at `fp`. -/
def lpDecAt (fs : String → ℕ) (name dec : String) (n fp j : ℕ) : ℕ :=
  fp + j * fs name + fs name + lpTailTot fs name dec n j

theorem lpTot_step (fs : String → ℕ) (name dec : String) {n j : ℕ} (hj : j < n) :
    lpTot fs name dec n j = fs name + lpTailTot fs name dec n j + fs dec := by
  unfold lpTailTot lpTot
  split
  · rw [show n - j = (n - (j + 1)) + 1 by omega, Nat.add_mul, Nat.add_mul (n - (j + 1)) 1]; ring
  · rw [show n - j = 1 by omega]; ring

theorem lpTot_le (fs : String → ℕ) (name dec : String) {n j : ℕ} (hj : j ≤ n) :
    j * fs name + lpTot fs name dec n j ≤ lpTot fs name dec n 0 := by
  unfold lpTot
  have h1 : (n - 0 + 1) * fs name = j * fs name + (n - j + 1) * fs name := by
    rw [← Nat.add_mul]; congr 1; omega
  have h2 : (n - j) * fs dec ≤ (n - 0) * fs dec := Nat.mul_le_mul_right _ (by omega)
  omega

theorem lpDecAt_eq (fs : String → ℕ) (name dec : String) {n j : ℕ} (fp : ℕ) (hj : j < n) :
    lpDecAt fs name dec n fp j = fp + (n + 1) * fs name + (n - 1 - j) * fs dec := by
  obtain ⟨t, rfl⟩ : ∃ t, n = j + 1 + t := ⟨n - j - 1, by omega⟩
  unfold lpDecAt lpTailTot lpTot
  split
  · rw [show j + 1 + t - (j + 1) = t by omega, show j + 1 + t - 1 - j = t by omega]; ring
  · obtain rfl : t = 0 := by omega
    rw [show j + 1 + 0 - 1 - j = 0 by omega]; ring

/-- The decoders' frame runs from iteration `j`, decoder `i` at `dfp i`. -/
def lpRunsFrom (cert : String → V → ℕ) (d cd n : ℕ) (dfp : ℕ → ℕ) (cap : List E) (j : ℕ) :
    Layout :=
  ((List.range (n - j)).map fun i =>
    qwRunL cert (qwDecName d cd) (dfp (j + i)) d cd (sqChal cap (j + i))).flatten

theorem regionL_lpRunsFrom {cert : String → V → ℕ} {d cd n : ℕ} {dfp : ℕ → ℕ} {cap : List E}
    {j i : ℕ} : RegionL (lpRunsFrom cert d cd n dfp cap j) i ↔
      ∃ j', j ≤ j' ∧ j' < n ∧
        RegionL (qwRunL cert (qwDecName d cd) (dfp j') d cd (sqChal cap j')) i := by
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    simp only [lpRunsFrom, List.mem_flatten, List.mem_map, List.mem_range] at hq
    obtain ⟨_, ⟨t, ht, rfl⟩, hq⟩ := hq
    exact ⟨j + t, by omega, by omega, q, hq, h1, h2⟩
  · rintro ⟨j', h1, h2, q, hq, h3, h4⟩
    refine ⟨q, ?_, h3, h4⟩
    simp only [lpRunsFrom, List.mem_flatten, List.mem_map, List.mem_range]
    exact ⟨_, ⟨j' - j, by omega, by rw [show j + (j' - j) = j' by omega]⟩, hq⟩

/-- Blocks in pairwise disjoint windows, each disjoint, are disjoint: the first parts, then the
second parts. -/
theorem lp_disj_windows {m : ℕ} (A B : ℕ → Layout) (lo len : ℕ → ℕ)
    (hD : ∀ j < m, DisjL (A j ++ B j)) (hW : ∀ j < m, Within (A j ++ B j) (lo j) (len j))
    (hsep : ∀ i < m, ∀ j < m, i ≠ j → lo i + len i ≤ lo j ∨ lo j + len j ≤ lo i) :
    DisjL (((List.range m).map A).flatten ++ ((List.range m).map B).flatten) := by
  have hwin : ∀ i < m, ∀ j < m, i ≠ j → ∀ x ∈ A i ++ B i, ∀ y ∈ A j ++ B j,
      x.1 + x.2.length ≤ y.1 ∨ y.1 + y.2.length ≤ x.1 := fun i hi j hj hij x hx y hy => by
    have h1 := hW i hi x hx; have h2 := hW j hj y hy; have := hsep i hi j hj hij; omega
  have hpr : ∀ (C : ℕ → Layout), (∀ j < m, ∀ x ∈ C j, x ∈ A j ++ B j) → (∀ j < m, DisjL (C j)) →
      DisjL ((List.range m).map C).flatten := fun C hC hCD => by
    unfold DisjL
    rw [List.pairwise_flatten, List.pairwise_map]
    refine ⟨fun l hl => ?_, (List.pairwise_lt_range (n := m)).imp_of_mem fun hi hj hij x hx y hy => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
      exact hCD j (List.mem_range.mp hj)
    · exact hwin _ (List.mem_range.mp hi) _ (List.mem_range.mp hj) (by omega) x
        (hC _ (List.mem_range.mp hi) x hx) y (hC _ (List.mem_range.mp hj) y hy)
  unfold DisjL
  rw [List.pairwise_append]
  refine ⟨hpr A (fun j _ x hx => List.mem_append_left _ hx)
      (fun j hj => (List.pairwise_append.mp (hD j hj)).1),
    hpr B (fun j _ x hx => List.mem_append_right _ hx)
      (fun j hj => (List.pairwise_append.mp (hD j hj)).2.1), fun x hx y hy => ?_⟩
  obtain ⟨_, hl1, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl1
  obtain ⟨_, hl2, hy⟩ := List.mem_flatten.mp hy
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl2
  rw [List.mem_range] at hi hj
  by_cases hij : i = j
  · subst hij
    exact (List.pairwise_append.mp (hD i hi)).2.2 x hx y hy
  · exact hwin i hi j hj hij x (List.mem_append_left _ hx) y (List.mem_append_right _ hy)

/-- **`level_positions`' loop, placed** from its first iteration at `fp`: on every memory holding
the capacity chain from `cap` in the rows of `sqz` and the caller's words (`LpMem`, decoder `j` at
`lpDecAt`), the loop holds, its decoders' runs its data. -/
theorem lpLoop_relAtIn (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {d cd : ℕ}
    {name : String} {fn : Fn} (hfind : coreProgram.find? name = some fn)
    (hp : fn.params = osParams 6) (hb : fn.body = lpLoopBody d cd name)
    (hlp : coreProgram.loop name = true) (hne : name ≠ qwDecName d cd)
    (hpw : digitsVal (osPowDigits (192 / d)) 1 = 192 / d)
    (hdec : QwDecodeAtD fs cert k d cd (qwDecName d cd))
    {n : ℕ} (hn : 0 < n) (hn' : n < 2 ^ 64 - 1) {sqz pos wp tabs : E} {cap : List E}
    (hcl : cap.length = 5) (hcan : AllCanonical cap) {Lin : Layout} (fp : ℕ)
    (hmem : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j ≤ n, ∀ i < 5,
      LoadHolds rd sqz (5 * j + i) ((sqCaps cap j).getD i 0))
    (hdmem : ∀ rd, LowDef k rd → MemL rd Lin →
      LpMem cert d cd n (lpDecAt fs name (qwDecName d cd) n fp) cap pos wp tabs rd)
    (hreg : ∀ j < n, ∀ t < 10, ∃ i, (sqz * (gen ^ j) ^ 5).limb 0 * Parameters.addressOfIndex t =
      Parameters.addressOfIndex i ∧ RegionL Lin i)
    (hregd : ∀ j < n, QwRegs d [sqChal cap j, pos * (gen ^ j) ^ (192 / d),
        wp * (gen ^ j) ^ (192 / d), tabs] (RegionL Lin)) :
    ∃ Lown : Layout,
      Within (lpRunsFrom cert d cd n (lpDecAt fs name (qwDecName d cd) n fp) cap 0 ++ Lown) fp
        (lpTot fs name (qwDecName d cd) n 0) ∧
      DisjL (lpRunsFrom cert d cd n (lpDecAt fs name (qwDecName d cd) n fp) cap 0 ++ Lown) ∧
      ∀ rd, LowDef k rd →
        MemL rd (lpRunsFrom cert d cd n (lpDecAt fs name (qwDecName d cd) n fp) cap 0 ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin)
          (RegionL (lpRunsFrom cert d cd n (lpDecAt fs name (qwDecName d cd) n fp) cap 0)) fp
          (lpTot fs name (qwDecName d cd) n 0) name [1, gen ^ n, sqz, pos, wp, tabs] [] := by
  set D := qwDecName d cd with hD
  set dA := lpDecAt fs name D n fp with hdA
  have hdecj : ∀ j < n, ∃ Lj : Layout,
      Within (qwRunL cert D (dA j) d cd (sqChal cap j) ++ Lj) (dA j) (fs D) ∧
      DisjL (qwRunL cert D (dA j) d cd (sqChal cap j) ++ Lj) ∧
      ∀ rd, LowDef k rd → MemL rd (qwRunL cert D (dA j) d cd (sqChal cap j) ++ Lj ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL (qwRunL cert D (dA j) d cd (sqChal cap j)))
          (dA j) (fs D) D
          [sqChal cap j, pos * (gen ^ j) ^ (192 / d), wp * (gen ^ j) ^ (192 / d), tabs] [] :=
    fun j hj => hdec _ _ _ _ Lin _ (hregd j hj) fun rd hl hm => by
      obtain ⟨hT, hP⟩ := hdmem rd hl hm
      refine ⟨hT, fun i hi => ?_⟩
      obtain ⟨h1, h2⟩ := hP j hj i hi
      rw [← pow_mul, loadHolds_mul_gen_pow, loadHolds_mul_gen_pow]
      exact ⟨h1, h2⟩
  classical
  let Lj : ℕ → Layout := fun j => if h : j < n then Classical.choose (hdecj j h) else []
  have hLj : ∀ j (h : j < n), Lj j = Classical.choose (hdecj j h) := fun j h => by simp [Lj, h]
  let Lown : Layout := ((List.range n).map Lj).flatten
  have e1 : lpRunsFrom cert d cd n dA cap 0 =
      ((List.range n).map fun j => qwRunL cert D (dA j) d cd (sqChal cap j)).flatten := by
    simp [lpRunsFrom, hD]
  refine ⟨Lown, ?_, ?_, fun rd hlow hL => ?_⟩
  · rw [within_append]
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · rw [e1] at hq
      simp only [List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨j, hj, rfl⟩, hq⟩ := hq
      have hw := (Classical.choose_spec (hdecj j hj)).1 q (List.mem_append_left _ hq)
      have := lpTot_le fs name D (n := n) (j := j) (by omega)
      have := lpTot_step fs name D (n := n) (j := j) hj
      simp only [hdA, lpDecAt] at hw ⊢
      omega
    · simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨j, hj, rfl⟩, hq⟩ := hq
      rw [hLj j hj] at hq
      have hw := (Classical.choose_spec (hdecj j hj)).1 q (List.mem_append_right _ hq)
      have := lpTot_le fs name D (n := n) (j := j) (by omega)
      have := lpTot_step fs name D (n := n) (j := j) hj
      simp only [hdA, lpDecAt] at hw ⊢
      omega
  · rw [e1]
    refine lp_disj_windows _ Lj (fun j => dA j) (fun _ => fs D)
      (fun j hj => ?_) (fun j hj => ?_) (fun i hi j hj hij => ?_)
    · rw [hLj j hj]; exact (Classical.choose_spec (hdecj j hj)).2.1
    · rw [hLj j hj]; exact (Classical.choose_spec (hdecj j hj)).1
    · simp only [hdA]
      rw [lpDecAt_eq fs name D fp hi, lpDecAt_eq fs name D fp hj]
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · right
        have : (n - 1 - j + 1) * fs D ≤ (n - 1 - i) * fs D := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      · left
        have : (n - 1 - i + 1) * fs D ≤ (n - 1 - j) * fs D := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
  obtain ⟨h12, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hR, hO⟩ := Main.memL_append.mp h12
  have hd := hmem rd hlow hLin
  have hrel : ∀ j (hj : j < n), RelAtIn coreProgram fs cert rd (RegionL Lin)
      (RegionL (qwRunL cert D (dA j) d cd (sqChal cap j))) (dA j) (fs D) D
      [sqChal cap j, pos * (gen ^ j) ^ (192 / d), wp * (gen ^ j) ^ (192 / d), tabs] [] :=
    fun j hj => by
      refine (Classical.choose_spec (hdecj j hj)).2.2 rd hlow
        (Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨?_, ?_⟩, hLin⟩)
      · intro q hq
        exact hR q (by
          rw [e1]
          simp only [List.mem_flatten, List.mem_map, List.mem_range]
          exact ⟨_, ⟨j, hj, rfl⟩, hq⟩)
      · intro q hq
        rw [← hLj j hj] at hq
        exact hO q (by
          simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range]
          exact ⟨_, ⟨j, hj, rfl⟩, hq⟩)
  have hKj : ∀ j, IsInK (gen ^ j * gen + gen ^ n) := fun j =>
    isInK_add (by rw [gen_pow_mul_gen]; exact gen_pow_isInK _) (gen_pow_isInK _)
  have hrowj : ∀ j < n, ∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) i ((sqCaps cap j).getD i 0) :=
    fun j hj i hi => by
      rw [← pow_mul, loadHolds_mul_gen_pow, show j * 5 + i = 5 * j + i by ring]
      exact hd j (by omega) i hi
  have hnextj : ∀ j < n, ∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) (5 + i)
      ((capOf (⟨sqCaps cap j, []⟩ : Fs).perm).getD i 0) := fun j hj i hi => by
    rw [← pow_mul, loadHolds_mul_gen_pow, show j * 5 + (5 + i) = 5 * (j + 1) + i by ring]
    exact hd (j + 1) (by omega) i hi
  have hstep : ∀ t j, j + t + 1 = n →
      RelAtIn coreProgram fs cert rd (RegionL Lin)
        (fun i => RegionL (lpRunsFrom cert d cd n dA cap j) i)
        (fp + j * fs name) (lpTot fs name D n j) name [gen ^ j, gen ^ n, sqz, pos, wp, tabs] [] := by
    intro t
    induction t with
    | zero =>
      intro j hj
      have h0 : gen ^ j * gen + gen ^ n = 0 := by
        rw [gen_pow_add_eq_zero_iff]; congr 1; omega
      have := lpLoop_iter fs cert hfind hp hb hlp hne hpw (rd := rd) (R := RegionL Lin)
        (Dt := fun _ => False) (N := gen ^ n) (sqz := sqz) (pos := pos) (wp := wp) (tabs := tabs)
        (sqCaps_length cap hcl j) (sqCaps_canonical cap hcan j) (fp + j * fs name) (m := fs name)
        (hrowj j (by omega)) (hnextj j (by omega))
        (by
          have := hrel j (by omega)
          simp only [hdA, lpDecAt, lpTailTot, show ¬ (j + 1 < n) by omega, ↓reduceIte] at this
          exact this)
        (fun i h => h) (hKj j) (by simp [h0])
        (fun t ht => hreg j (by omega) t ht)
      rw [show lpTot fs name D n j = fs name + fs name + fs D by
        rw [lpTot_step fs name D (by omega)]
        simp only [lpTailTot, show ¬ (j + 1 < n) by omega, ↓reduceIte]]
      refine relAtIn_dmono this fun i hi => ?_
      obtain ⟨j', h1, h2, hi'⟩ := regionL_lpRunsFrom.mp hi
      obtain rfl : j' = j := by omega
      simp only [hdA, lpDecAt, lpTailTot, show ¬ (j' + 1 < n) by omega, ↓reduceIte] at hi'
      exact Or.inl hi'
    | succ t ih =>
      intro j hj
      have hne' : gen ^ j * gen + gen ^ n ≠ 0 := by
        rw [ne_eq, gen_pow_add_eq_zero_iff]
        intro he
        have := gen_pow_inj (by omega) (by omega) he
        omega
      have ht := ih (j + 1) (by omega)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc] at ht
      have := lpLoop_iter fs cert hfind hp hb hlp hne hpw (rd := rd) (R := RegionL Lin)
        (Dt := fun i => RegionL (lpRunsFrom cert d cd n dA cap (j + 1)) i)
        (N := gen ^ n) (sqz := sqz) (pos := pos) (wp := wp) (tabs := tabs)
        (sqCaps_length cap hcl j) (sqCaps_canonical cap hcan j) (fp + j * fs name)
        (m := lpTot fs name D n (j + 1)) (hrowj j (by omega)) (hnextj j (by omega))
        (by
          have := hrel j (by omega)
          simp only [hdA, lpDecAt, lpTailTot, show j + 1 < n by omega, ↓reduceIte] at this
          exact this)
        (fun i h => h) (hKj j)
        (by
          split
          · rw [gen_pow_mul_gen]; exact ht
          · next h => exact absurd hne' h)
        (fun t ht => hreg j (by omega) t ht)
      rw [show lpTot fs name D n j = fs name + lpTot fs name D n (j + 1) + fs D by
        rw [lpTot_step fs name D (by omega)]
        simp only [lpTailTot, show j + 1 < n by omega, ↓reduceIte]]
      refine relAtIn_dmono this fun i hi => ?_
      obtain ⟨j', h1, h2, hi'⟩ := regionL_lpRunsFrom.mp hi
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · simp only [hdA, lpDecAt, lpTailTot, show j + 1 < n by omega, ↓reduceIte] at hi'
        exact Or.inl hi'
      · exact Or.inr ⟨hne', regionL_lpRunsFrom.mpr ⟨j', by omega, h2, hi'⟩⟩
  have := hstep (n - 1) 0 (by omega)
  simpa using this

end
end LeanVM.Guest.B1
