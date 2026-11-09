/-
  LeanVM.Guest.B1.Place.SqAt

  `open_stacked`'s squeeze loop placed (`RelAtIn`): one iteration, its decode call before its
  tail, and the loop from its first iteration, its decoders' frame runs its data. After mumbai's
  `B1/Whir/SqAt.lean`.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Whir.CSqLoop

/-!
# The squeeze loop, placed

A squeeze loop helper's body (`sqLoopBody lv name`) is straight-line: before its `ret []`
(`sqLoopPre`) it allocates nothing, has no `frameAddr`, calls
`decode_query_windows__L{depth}_L{capDepth}` and its tail (`sqLoopPre_calls`), and loads only through the row `sqz·x^5`, at offsets below `10`
(`sqLoopPre_loads`). A loop helper places its tail at `fp + fs L`, then its other callees:
iteration `j` of `n` takes `(n - j + 1)·fs L + (n - j)·fs D` words (`sqTot`), its decoder at
`sqDecAt`.

`sqLoop_iter`: one iteration from its decoder's and its tail's placed relations.
`sqLoop_relAtIn`: the loop from iteration `0` at `fp`, from `decode_query_windows`' placed
completeness (`QwDecodeAtD`), on every memory holding the capacity chain at `sqz`, the window table
at `tabs` and, at `qpos` and `qbp`, what each decoder stores: the positions and the pointers into
its `wins` run (`qwPtrAt`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Protocol.Compile (challengeOf)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## The body's statements -/

/-- The decoder a level's squeeze loop calls. -/
def sqDecName (lv : OsLv) : String :=
  "decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth

/-- The squeeze loop's body before its final `ret []`. -/
def sqLoopPre (lv : OsLv) (name : String) : List Stmt :=
  sqLoopA lv ++ osLoopTailA (sqTail lv) ++
    [.callIf (.n (sqTail lv + 2)) name (.n (sqTail lv + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1))]

theorem sqLoopBody_pre (lv : OsLv) (name : String) :
    sqLoopBody lv name = sqLoopPre lv name ++ [.ret []] := by
  rw [sqLoopBody_split, sqLoopPre, sqTail]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem straight_of_flat : ∀ l : List Stmt, l.all Stmt.flat = true → l.all Main.Stmt.straight = true
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h ⊢
    refine ⟨?_, straight_of_flat l h.2⟩
    have h1 := h.1
    cases s <;> simp_all [Stmt.flat, Main.Stmt.straight]

theorem sqLoopPre_flat (lv : OsLv) (name : String) : (sqLoopPre lv name).all Stmt.flat = true := by
  have h := sqLoopA_flat lv
  rw [← sqTail] at h
  rw [sqLoopPre, List.all_append, h]
  rfl

theorem sqLoopPre_straight (lv : OsLv) (name : String) :
    (sqLoopPre lv name).all Main.Stmt.straight = true :=
  straight_of_flat _ (sqLoopPre_flat lv name)

theorem osPowSteps_mem_mul (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), ∀ s ∈ (osPowSteps x ds acc k).1,
    ∃ d a b, s = .atom (.mul d a b)
  | [], _, _, s, hs => by simp [osPowSteps] at hs
  | true :: ds, acc, k, s, hs => by
    simp only [osPowSteps, ↓reduceIte, List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
    · exact osPowSteps_mem_mul x ds _ _ s hs
  | false :: ds, acc, k, s, hs => by
    simp only [osPowSteps, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨_, _, _, rfl⟩
    · exact osPowSteps_mem_mul x ds _ _ s hs

theorem osMat_mem (b o k : ℕ) : ∀ s ∈ (osMat b o k).1,
    (∃ d c, s = .atom (.const d c)) ∨ ∃ d a b, s = .atom (.mul d a b) := by
  intro s hs
  unfold osMat at hs
  split_ifs at hs
  · simp at hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr ⟨_, _, _, rfl⟩

theorem fm_pow_nil {α : Type} (F : Stmt → Option α) (hm : ∀ d a b, F (.atom (.mul d a b)) = none)
    (x : ℕ) (ds : List Bool) (acc k : ℕ) : (osPowSteps x ds acc k).1.filterMap F = [] :=
  List.filterMap_eq_nil_iff.mpr fun s hs => by
    obtain ⟨d, a, b, rfl⟩ := osPowSteps_mem_mul x ds acc k s hs; exact hm d a b

theorem fm_mat_nil {α : Type} (F : Stmt → Option α) (hm : ∀ d a b, F (.atom (.mul d a b)) = none)
    (hc : ∀ d c, F (.atom (.const d c)) = none) (b o k : ℕ) : (osMat b o k).1.filterMap F = [] :=
  List.filterMap_eq_nil_iff.mpr fun s hs => by
    rcases osMat_mem b o k s hs with ⟨d, c, rfl⟩ | ⟨d, a, b, rfl⟩
    · exact hc d c
    · exact hm d a b

theorem sqLoopPre_allocs (lv : OsLv) (name : String) :
    (sqLoopPre lv name).filterMap Main.Stmt.allocSz = [] := by
  simp only [sqLoopPre, sqLoopA, List.filterMap_append,
    fm_pow_nil Main.Stmt.allocSz (fun _ _ _ => rfl),
    fm_mat_nil Main.Stmt.allocSz (fun _ _ _ => rfl) (fun _ _ => rfl),
    List.append_nil]
  rfl

theorem sqLoopPre_addrs (lv : OsLv) (name : String) :
    (sqLoopPre lv name).filterMap Main.Stmt.addrS = [] := by
  simp only [sqLoopPre, sqLoopA, List.filterMap_append,
    fm_pow_nil Main.Stmt.addrS (fun _ _ _ => rfl),
    fm_mat_nil Main.Stmt.addrS (fun _ _ _ => rfl) (fun _ _ => rfl),
    List.append_nil]
  rfl

/-- The calls of the squeeze loop's body: the decoder, then the tail. -/
def sqCallsS (lv : OsLv) (name : String) : List (Option V × String × List V × List V) :=
  [(none, sqDecName lv, [.n 39, .n (osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2,
      .n (osMat 4 lv.posOff ((osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2, .n 5], []),
    (some (.n (sqTail lv + 2)), name,
      .n (sqTail lv + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1), [])]

theorem sqLoopPre_calls (lv : OsLv) (name : String) :
    (sqLoopPre lv name).filterMap Main.Stmt.callS = sqCallsS lv name := by
  simp only [sqLoopPre, sqLoopA, List.filterMap_append,
    fm_pow_nil Main.Stmt.callS (fun _ _ _ => rfl),
    fm_mat_nil Main.Stmt.callS (fun _ _ _ => rfl) (fun _ _ => rfl),
    List.append_nil]
  rfl

theorem sqLoopPre_loadsEq (lv : OsLv) (name : String) :
    (sqLoopPre lv name).filterMap Stmt.loadS =
      (List.range 10).map fun i => ((.n 9 : V), i) := by
  simp only [sqLoopPre, sqLoopA, List.filterMap_append,
    fm_pow_nil Stmt.loadS (fun _ _ _ => rfl),
    fm_mat_nil Stmt.loadS (fun _ _ _ => rfl) (fun _ _ => rfl),
    List.append_nil]
  rfl

theorem sqLoopPre_loads (lv : OsLv) (name : String) :
    ∀ q ∈ (sqLoopPre lv name).filterMap Stmt.loadS, q.1 = .n 9 ∧ q.2 < 10 := by
  intro q hq
  rw [sqLoopPre_loadsEq] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  exact ⟨rfl, List.mem_range.mp hi⟩

/-! ## One iteration -/

/-- **One iteration of a squeeze loop, placed at `fp`**: its tail at `fp + fs L` (or skipped at
the last), its decoder after the tail's `m` words, its loads through the row in `R`. -/
theorem sqLoop_iter (fs : String → ℕ) (cert : String → V → ℕ) {lv : OsLv} {name : String}
    {fn : Fn} (hfind : coreProgram.find? name = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = sqLoopBody lv name) (hlp : coreProgram.loop name = true)
    (hpw : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth)
    (hpo : lv.posOff < u128Bound) {rd : Reader} {R Rd Dd Dt : ℕ → Prop} {X N sqz qpos qbp tabs : E}
    {cap : List E} (hcl : cap.length = 5) (hcan : AllCanonical cap) (fp : ℕ) {m : ℕ}
    (hrow : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) i (cap.getD i 0))
    (hnext : ∀ i < 5, LoadHolds rd (sqz * X ^ 5) (5 + i) ((capOf (⟨cap, []⟩ : Fs).perm).getD i 0))
    (hdec : RelAtIn coreProgram fs cert rd Rd Dd (fp + fs name + m) (fs (sqDecName lv))
      (sqDecName lv) [challengeOf (⟨cap, []⟩ : Fs).perm, qpos * gen ^ lv.posOff * X ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * X ^ (192 / lv.depth), tabs] [])
    (hRd : ∀ i, Rd i → R i) (hK : IsInK (X * gen + N))
    (htail : if X * gen + N ≠ 0 then
      RelAtIn coreProgram fs cert rd R Dt (fp + fs name) m name [X * gen, N, sqz, qpos, qbp, tabs] []
      else m = fs name)
    (hreg : ∀ t < 10, ∃ i, (sqz * X ^ 5).limb 0 * Parameters.addressOfIndex t =
        Parameters.addressOfIndex i ∧ R i) :
    RelAtIn coreProgram fs cert rd R (fun i => Dd i ∨ (X * gen + N ≠ 0 ∧ Dt i)) fp
      (fs name + m + fs (sqDecName lv)) name [X, N, sqz, qpos, qbp, tabs] [] := by
  set σ := sqIterVal lv X N sqz qpos qbp tabs cap with hσ
  obtain ⟨hpar, ⟨hA, h8, hdargs⟩, hg, hta⟩ := sqIter_completeC (C := fun _ _ _ => True) (rd := rd)
    lv hpw hpo X N sqz qpos qbp tabs cap hcl hcan hrow hnext trivial
  rw [← hσ] at hpar hA h8 hdargs hg hta
  have hpre : fn.body = sqLoopPre lv name ++ [.ret []] := hb.trans (sqLoopBody_pre lv name)
  have hst := sqLoopPre_straight lv name
  set es := (sqLoopPre lv name).flatMap (Main.slEvs σ) with hes_def
  have hw : walk σ fn.body = .ret es [] := by rw [hpre]; exact Main.walk_straight σ [] _ hst
  have hholds : Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) := by
    rw [hpre, holdsList_flat_ret _ (sqLoopPre_flat lv name)]
    refine ⟨?_, rfl⟩
    rw [sqLoopPre, allOk_append]
    refine ⟨hA, allOk_cons.mpr ⟨⟨by rw [hg]; exact hK, fun _ => trivial⟩, allOk_nil⟩⟩
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    have := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hfind))
      hholds
    rw [hw] at this
    exact fun e he => (this.1 e he).1
  obtain ⟨had, hal, hadr, hcl'⟩ := Main.straight_parts σ _ hst
  have hal0 : allocs σ es = [] := by rw [hal, sqLoopPre_allocs]; rfl
  have hcalls : calls es = [⟨sqDecName lv, [.n 39, .n (osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2,
      .n (osMat 4 lv.posOff ((osMat 3 lv.posOff (40 + osPowLen (192 / lv.depth))).2.2 + 1)).2.2, .n 5], [],
      true⟩] ++
      [⟨name, .n (sqTail lv + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1), [],
        decide (σ (.n (sqTail lv + 2)) ≠ 0)⟩] := by
    rw [hcl', sqLoopPre_calls]; rfl
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    coreProgram_wf (R := R) (D := fun i => Dd i ∨ (X * gen + N ≠ 0 ∧ Dt i))
    (Dk := fun i => False ∨ (true = true ∧ Dd i)) (Rt := R) (Dt := Dt) (fp := fp) (m := m)
    (N := fs (sqDecName lv)) hfind hlp (by rw [hp]) hw rfl hev hcalls ?_
    (by rw [had, sqLoopPre_allocs, hal0]; rfl)
    (fun q hq' => by rw [hadr, sqLoopPre_addrs] at hq'; simp at hq')
    ?_ (fun i hi => Or.inl hi) (fun A hA => ?_) ?_
  · rwa [hal0, List.sum_nil, Nat.add_zero] at h
  · simp only [hg]
    split
    · next hc =>
      have hne : X * gen + N ≠ 0 := by simpa using hc
      rw [List.map_nil, hta]
      simpa [hne] using htail
    · next hc =>
      have h0 : X * gen + N = 0 := by simpa using hc
      simpa [h0] using htail
  · rw [hal0, List.sum_nil, Nat.add_zero]
    refine ⟨fs (sqDecName lv), 0, Rd, Dd, rfl, fun i hi => Or.inl (Or.inl (hRd i hi)), ?_, rfl,
      fun i hi => hi⟩
    simp only [↓reduceIte, List.map_nil]
    rw [hdargs]; exact hdec
  · rw [loadAddrs_straight σ _ hst] at hA
    obtain ⟨⟨p, off⟩, hq', rfl⟩ := List.mem_map.mp hA
    have hql := sqLoopPre_loads lv name _ hq'
    obtain ⟨i, hi, hR⟩ := hreg off hql.2
    refine ⟨i, ?_, Or.inr (Or.inl hR)⟩
    have hp8 : p = .n 9 := hql.1
    rw [hp8, h8]; exact hi
  · intro i hi
    rcases hi with hi | ⟨ht, hi⟩
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, hi⟩))
    · refine Or.inr (Or.inr ⟨?_, hi⟩)
      simp only [hg]
      exact decide_eq_true ht

/-! ## The loop -/

/-- The words of the squeeze loop from iteration `j` of `n`: each iteration's frame and decoder,
then the skipped tail's frame. -/
def sqTot (fs : String → ℕ) (lv : OsLv) (name : String) (n j : ℕ) : ℕ :=
  (n - j + 1) * fs name + (n - j) * fs (sqDecName lv)

/-- The tail's words after iteration `j`. -/
def sqTailTot (fs : String → ℕ) (lv : OsLv) (name : String) (n j : ℕ) : ℕ :=
  if j + 1 < n then sqTot fs lv name n (j + 1) else fs name

/-- Iteration `j`'s decoder, the loop entered at `fp`. -/
def sqDecAt (fs : String → ℕ) (lv : OsLv) (name : String) (n fp j : ℕ) : ℕ :=
  fp + j * fs name + fs name + sqTailTot fs lv name n j

theorem sqTot_step (fs : String → ℕ) (lv : OsLv) (name : String) {n j : ℕ} (hj : j < n) :
    sqTot fs lv name n j = fs name + sqTailTot fs lv name n j + fs (sqDecName lv) := by
  unfold sqTailTot sqTot
  split
  · rw [show n - j = (n - (j + 1)) + 1 by omega, Nat.add_mul, Nat.add_mul (n - (j + 1)) 1]; ring
  · rw [show n - j = 1 by omega]; ring

theorem sqTot_le (fs : String → ℕ) (lv : OsLv) (name : String) {n j : ℕ} (hj : j ≤ n) :
    j * fs name + sqTot fs lv name n j ≤ sqTot fs lv name n 0 := by
  unfold sqTot
  have h1 : (n - 0 + 1) * fs name = j * fs name + (n - j + 1) * fs name := by
    rw [← Nat.add_mul]; congr 1; omega
  have h2 : (n - j) * fs (sqDecName lv) ≤ (n - 0) * fs (sqDecName lv) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- The capacity of iteration `j` from `cap0`. -/
def sqCapJ (cap0 : List E) (j : ℕ) : List E := ((⟨cap0, []⟩ : Fs).squeezeN j).2.cap

/-- The challenge iteration `j` decodes. -/
def sqWJ (cap0 : List E) (j : ℕ) : E := challengeOf (⟨sqCapJ cap0 j, []⟩ : Fs).perm

/-- The decoders' frame runs from iteration `j`. -/
def sqRuns (fs : String → ℕ) (cert : String → V → ℕ) (lv : OsLv) (name : String) (n fp : ℕ)
    (w : ℕ → E) (j : ℕ) : Layout :=
  ((List.range (n - j)).map fun i =>
    qwRunL cert (sqDecName lv) (sqDecAt fs lv name n fp (j + i)) lv.depth lv.capDepth (w (j + i))).flatten

theorem regionL_sqRuns {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {name : String}
    {n fp : ℕ} {w : ℕ → E} {j i : ℕ} : RegionL (sqRuns fs cert lv name n fp w j) i ↔
      ∃ j', j ≤ j' ∧ j' < n ∧
        RegionL (qwRunL cert (sqDecName lv) (sqDecAt fs lv name n fp j') lv.depth lv.capDepth (w j')) i := by
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range] at hq
    obtain ⟨_, ⟨t, ht, rfl⟩, hq⟩ := hq
    exact ⟨j + t, by omega, by omega, q, hq, h1, h2⟩
  · rintro ⟨j', h1, h2, q, hq, h3, h4⟩
    refine ⟨q, ?_, h3, h4⟩
    simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range]
    exact ⟨_, ⟨j' - j, by omega, by rw [show j + (j' - j) = j' by omega]⟩, hq⟩

theorem sqDecAt_eq (fs : String → ℕ) (lv : OsLv) (name : String) {n j : ℕ} (fp : ℕ) (hj : j < n) :
    sqDecAt fs lv name n fp j = fp + (n + 1) * fs name + (n - 1 - j) * fs (sqDecName lv) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = j + 1 + t := ⟨n - j - 1, by omega⟩
  unfold sqDecAt sqTailTot sqTot
  split
  · rw [show j + 1 + t - (j + 1) = t by omega, show j + 1 + t - 1 - j = t by omega]; ring
  · obtain rfl : t = 0 := by omega
    rw [show j + 1 + 0 - 1 - j = 0 by omega]; ring

/-- Blocks in pairwise disjoint windows, each disjoint, are disjoint: the first parts, then the
second parts. -/
theorem os_disj_windows {m : ℕ} (A B : ℕ → Layout) (lo len : ℕ → ℕ)
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

/-- **A level's squeeze loop, placed** from its first iteration at `fp`: on every memory holding
the capacity chain from `cap0` in the rows `sqz·(g^j)^5`, the window table at `tabs` and, at `qpos`
and `qbp`, what each decoder stores (the positions and the pointers into its `wins` run at
`sqDecAt`), the loop holds, its decoders' runs its data (`sqRuns`). -/
theorem sqLoop_relAtIn (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {lv : OsLv}
    {name : String} {fn : Fn} (hfind : coreProgram.find? name = some fn)
    (hp : fn.params = osParams 6) (hb : fn.body = sqLoopBody lv name)
    (hlp : coreProgram.loop name = true)
    (hpw : digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth)
    (hpo : lv.posOff < u128Bound) (hdec : QwDecodeAtD fs cert k lv.depth lv.capDepth (sqDecName lv))
    {n : ℕ} (hn : 0 < n) (hn' : n < ordG) {sqz qpos qbp tabs : E} {cap0 : List E}
    (hcl : cap0.length = 5) (hcan : AllCanonical cap0) {Lin : Layout} (fp : ℕ)
    (hmem : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < n,
      (∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) i ((sqCapJ cap0 j).getD i 0)) ∧
        ∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) (5 + i)
          ((capOf (⟨sqCapJ cap0 j, []⟩ : Fs).perm).getD i 0))
    (hdmem : ∀ rd, LowDef k rd → MemL rd Lin → WinTabs rd tabs ∧ ∀ j < n, ∀ i < 192 / lv.depth,
      LoadHolds rd (qpos * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth)) i
          (eOfNat (qwPosOf lv.depth (sqWJ cap0 j) i)) ∧
        LoadHolds rd (qbp * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth)) i
          (qwPtrAt cert (sqDecName lv) (sqDecAt fs lv name n fp j) lv.depth lv.capDepth i))
    (hreg : ∀ j < n, ∀ t < 10, ∃ i, (sqz * (gen ^ j) ^ 5).limb 0 * Parameters.addressOfIndex t =
      Parameters.addressOfIndex i ∧ RegionL Lin i)
    (hregd : ∀ j < n, QwRegs lv.depth [sqWJ cap0 j, qpos * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth), tabs] (RegionL Lin)) :
    ∃ Lown : Layout, Within (sqRuns fs cert lv name n fp (sqWJ cap0) 0 ++ Lown) fp
        (sqTot fs lv name n 0) ∧
      DisjL (sqRuns fs cert lv name n fp (sqWJ cap0) 0 ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd (sqRuns fs cert lv name n fp (sqWJ cap0) 0 ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin)
          (RegionL (sqRuns fs cert lv name n fp (sqWJ cap0) 0)) fp (sqTot fs lv name n 0) name
          [1, gen ^ n, sqz, qpos, qbp, tabs] [] := by
  have hn2 : n < 2 ^ 64 - 1 := hn'
  have hdecj : ∀ j < n, ∃ Lj : Layout,
      Within (qwRunL cert (sqDecName lv) (sqDecAt fs lv name n fp j) lv.depth lv.capDepth (sqWJ cap0 j) ++ Lj)
        (sqDecAt fs lv name n fp j) (fs (sqDecName lv)) ∧
      DisjL (qwRunL cert (sqDecName lv) (sqDecAt fs lv name n fp j) lv.depth lv.capDepth (sqWJ cap0 j) ++ Lj) ∧
      ∀ rd, LowDef k rd →
        MemL rd (qwRunL cert (sqDecName lv) (sqDecAt fs lv name n fp j) lv.depth lv.capDepth (sqWJ cap0 j) ++ Lj ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin)
          (RegionL (qwRunL cert (sqDecName lv) (sqDecAt fs lv name n fp j) lv.depth lv.capDepth (sqWJ cap0 j)))
          (sqDecAt fs lv name n fp j) (fs (sqDecName lv)) (sqDecName lv)
          [sqWJ cap0 j, qpos * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth),
            qbp * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth), tabs] [] := fun j hj =>
    hdec _ _ _ _ Lin _ (hregd j hj) fun rd hl hm =>
      ⟨(hdmem rd hl hm).1, fun i hi => (hdmem rd hl hm).2 j hj i hi⟩
  classical
  let Lj : ℕ → Layout := fun j => if h : j < n then Classical.choose (hdecj j h) else []
  have hLj : ∀ j (h : j < n), Lj j = Classical.choose (hdecj j h) := fun j h => by simp [Lj, h]
  let Lown : Layout := ((List.range n).map Lj).flatten
  refine ⟨Lown, ?_, ?_, fun rd hlow hL => ?_⟩
  · rw [within_append]
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨j, hj, rfl⟩, hq⟩ := hq
      simp only [Nat.zero_add] at hq
      have hw := (Classical.choose_spec (hdecj j (by omega))).1 q (List.mem_append_left _ hq)
      have := sqTot_le fs lv name (n := n) (j := j) (by omega)
      have := sqTot_step fs lv name (n := n) (j := j) (by omega)
      simp only [sqDecAt] at hw ⊢
      omega
    · simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨j, hj, rfl⟩, hq⟩ := hq
      rw [hLj j hj] at hq
      have hw := (Classical.choose_spec (hdecj j hj)).1 q (List.mem_append_right _ hq)
      have := sqTot_le fs lv name (n := n) (j := j) (by omega)
      have := sqTot_step fs lv name (n := n) (j := j) hj
      simp only [sqDecAt] at hw ⊢
      omega
  · have e1 : sqRuns fs cert lv name n fp (sqWJ cap0) 0 =
        ((List.range n).map fun j =>
          qwRunL cert (sqDecName lv) (sqDecAt fs lv name n fp j) lv.depth lv.capDepth (sqWJ cap0 j)).flatten := by
      simp [sqRuns]
    rw [e1]
    refine os_disj_windows _ Lj (fun j => sqDecAt fs lv name n fp j) (fun _ => fs (sqDecName lv))
      (fun j hj => ?_) (fun j hj => ?_) (fun i hi j hj hij => ?_)
    · rw [hLj j hj]; exact (Classical.choose_spec (hdecj j hj)).2.1
    · rw [hLj j hj]; exact (Classical.choose_spec (hdecj j hj)).1
    · rw [sqDecAt_eq fs lv name fp hi, sqDecAt_eq fs lv name fp hj]
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · right
        have : (n - 1 - j + 1) * fs (sqDecName lv) ≤ (n - 1 - i) * fs (sqDecName lv) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      · left
        have : (n - 1 - i + 1) * fs (sqDecName lv) ≤ (n - 1 - j) * fs (sqDecName lv) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
  obtain ⟨h12, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hR, hO⟩ := Main.memL_append.mp h12
  have hd := hmem rd hlow hLin
  have hrel : ∀ j (hj : j < n), RelAtIn coreProgram fs cert rd (RegionL Lin)
      (RegionL (qwRunL cert (sqDecName lv) (sqDecAt fs lv name n fp j) lv.depth lv.capDepth (sqWJ cap0 j)))
      (sqDecAt fs lv name n fp j) (fs (sqDecName lv)) (sqDecName lv)
      [sqWJ cap0 j, qpos * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth), tabs] [] := fun j hj => by
    refine (Classical.choose_spec (hdecj j hj)).2.2 rd hlow
      (Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨?_, ?_⟩, hLin⟩)
    · intro q hq
      exact hR q (by
        simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range]
        exact ⟨_, ⟨j, hj, by simp⟩, hq⟩)
    · intro q hq
      rw [← hLj j hj] at hq
      exact hO q (by
        simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range]
        exact ⟨_, ⟨j, hj, rfl⟩, hq⟩)
  have hKj : ∀ j, IsInK (gen ^ j * gen + gen ^ n) := fun j =>
    isInK_add (by rw [gen_pow_mul_gen]; exact gen_pow_isInK _) (gen_pow_isInK _)
  have hclj : ∀ j, (sqCapJ cap0 j).length = 5 := fun j => squeezeN_cap_length _ _ hcl
  have hcanj : ∀ j, AllCanonical (sqCapJ cap0 j) := fun j => squeezeN_cap_canonical _ _ hcan
  have hstep : ∀ t j, j + t + 1 = n →
      RelAtIn coreProgram fs cert rd (RegionL Lin)
        (fun i => RegionL (sqRuns fs cert lv name n fp (sqWJ cap0) j) i)
        (fp + j * fs name) (sqTot fs lv name n j) name [gen ^ j, gen ^ n, sqz, qpos, qbp, tabs] [] := by
    intro t
    induction t with
    | zero =>
      intro j hj
      obtain ⟨hr0, hn0⟩ := hd j (by omega)
      have h0 : gen ^ j * gen + gen ^ n = 0 := by
        rw [gen_pow_add_eq_zero_iff]; congr 1; omega
      have := sqLoop_iter fs cert hfind hp hb hlp hpw hpo (rd := rd) (R := RegionL Lin)
        (Dt := fun _ => False) (N := gen ^ n) (sqz := sqz) (qpos := qpos) (qbp := qbp) (tabs := tabs)
        (hclj j) (hcanj j) (fp + j * fs name) (m := fs name) hr0 hn0
        (by
          have := hrel j (by omega)
          simp only [sqDecAt, sqTailTot, show ¬ (j + 1 < n) by omega, ↓reduceIte] at this
          exact this)
        (fun i h => h) (hKj j) (by simp [h0])
        (fun t ht => hreg j (by omega) t ht)
      rw [show sqTot fs lv name n j = fs name + fs name + fs (sqDecName lv) by
        rw [sqTot_step fs lv name (by omega)]
        simp only [sqTailTot, show ¬ (j + 1 < n) by omega, ↓reduceIte]]
      refine relAtIn_dmono this fun i hi => ?_
      obtain ⟨j', h1, h2, hi'⟩ := regionL_sqRuns.mp hi
      obtain rfl : j' = j := by omega
      simp only [sqDecAt, sqTailTot, show ¬ (j' + 1 < n) by omega, ↓reduceIte] at hi'
      exact Or.inl hi'
    | succ t ih =>
      intro j hj
      obtain ⟨hr0, hn0⟩ := hd j (by omega)
      have hne : gen ^ j * gen + gen ^ n ≠ 0 := by
        rw [ne_eq, gen_pow_add_eq_zero_iff]
        intro he
        have := gen_pow_inj (by omega) (by omega) he
        omega
      have ht := ih (j + 1) (by omega)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc] at ht
      have := sqLoop_iter fs cert hfind hp hb hlp hpw hpo (rd := rd) (R := RegionL Lin)
        (Dt := fun i => RegionL (sqRuns fs cert lv name n fp (sqWJ cap0) (j + 1)) i)
        (N := gen ^ n) (sqz := sqz) (qpos := qpos) (qbp := qbp) (tabs := tabs)
        (hclj j) (hcanj j) (fp + j * fs name) (m := sqTot fs lv name n (j + 1)) hr0 hn0
        (by
          have := hrel j (by omega)
          simp only [sqDecAt, sqTailTot, show j + 1 < n by omega, ↓reduceIte] at this
          exact this)
        (fun i h => h) (hKj j)
        (by
          split
          · rw [gen_pow_mul_gen]; exact ht
          · next h => exact absurd hne h)
        (fun t ht => hreg j (by omega) t ht)
      rw [show sqTot fs lv name n j = fs name + sqTot fs lv name n (j + 1) + fs (sqDecName lv) by
        rw [sqTot_step fs lv name (by omega)]
        simp only [sqTailTot, show j + 1 < n by omega, ↓reduceIte]]
      refine relAtIn_dmono this fun i hi => ?_
      obtain ⟨j', h1, h2, hi'⟩ := regionL_sqRuns.mp hi
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · simp only [sqDecAt, sqTailTot, show j + 1 < n by omega, ↓reduceIte] at hi'
        exact Or.inl hi'
      · exact Or.inr ⟨hne, regionL_sqRuns.mpr ⟨j', by omega, h2, hi'⟩⟩
  have := hstep (n - 1) 0 (by omega)
  simpa using this

end
end LeanVM.Guest.B1
