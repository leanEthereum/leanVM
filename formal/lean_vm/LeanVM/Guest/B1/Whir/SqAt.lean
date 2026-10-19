/-
  LeanVM.Guest.B1.Whir.SqAt

  `open_stacked`'s squeeze loop placed (`RelAtIn`): one iteration, its decode call after its tail,
  and the loop from its first iteration, its decoders' frame runs its data.
-/

module

public import LeanVM.Guest.B1.Whir.SqIter
public import LeanVM.Guest.B1.Whir.OsCallees
public import LeanVM.Guest.B1.Whir.QueriesAt

/-!
# The squeeze loop, placed (TRIAGE #36)

A squeeze loop helper's body is straight-line: before its `ret []` (`sqLoopPre`) it allocates
nothing, has no `frameAddr`, calls `decode_query_bits` and its tail, and loads only through the
row `sqz·x²` (`SqPlace`, checked per level by kernel evaluation). A loop helper places its tail at
`fp + fs L`, then its other callees: iteration `j` of `n` takes `(n - j + 1)·fs L + (n - j)·fs D`
words (`sqTot`), its decoder at `sqDecAt`.

`sqLoop_iter`: one iteration from its decoder's and its tail's placed relations.
`sqLoop_relAtIn`: the loop from iteration `0` at `fp`, from `decode_query_bits`' placed
completeness (`OsDecodeAt`), on every memory holding the state chain at `sqz` and, at `qpos` and
`qbp`, what each decoder stores: the positions and the pointers into its frame run.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The body's statements -/

/-- The squeeze loop's body before its final `ret []`. -/
def sqLoopPre (lv : OsLvl) : List Stmt := (sqLoopOf lv).dropLast

theorem sqLoopOf_split (lv : OsLvl) : sqLoopOf lv = sqLoopPre lv ++ [.ret []] := by
  unfold sqLoopPre
  have hne : sqLoopOf lv ≠ [] := by rw [sqLoopOf_eq]; simp
  have hl : (sqLoopOf lv).getLast hne = .ret [] := by simp [sqLoopOf_eq]
  conv_lhs => rw [← List.dropLast_append_getLast hne, hl]

/-- The calls of the squeeze loop's body: the decoder, then the tail. -/
def sqCallsS (lv : OsLvl) : List (Option V × String × List V × List V) :=
  [(none, lv.decode, [.n 24, .n (sqP1 lv).2.1, .n (sqP2 lv).2.1], []),
    (some (.n (sqE lv + 2)), lv.sqLoop, [.n (sqE lv + 4), .n 1, .n 2, .n 3, .n 4], [])]

/-- **The body of a level's squeeze loop helper**, checked. -/
def sqPlaceB (lv : OsLvl) : Bool :=
  (sqLoopPre lv).all Main.Stmt.straight && decide ((sqLoopPre lv).filterMap Main.Stmt.allocSz = []) &&
    decide ((sqLoopPre lv).filterMap Main.Stmt.addrS = []) &&
    decide ((sqLoopPre lv).filterMap Main.Stmt.callS = sqCallsS lv) &&
    ((sqLoopPre lv).filterMap Stmt.loadS).all fun q => q.1 == .n 6 && decide (q.2 < 4)

structure SqPlace (lv : OsLvl) : Prop where
  straight : (sqLoopPre lv).all Main.Stmt.straight = true
  allocs : (sqLoopPre lv).filterMap Main.Stmt.allocSz = []
  addrs : (sqLoopPre lv).filterMap Main.Stmt.addrS = []
  calls : (sqLoopPre lv).filterMap Main.Stmt.callS = sqCallsS lv
  loads : ((sqLoopPre lv).filterMap Stmt.loadS).all (fun q => q.1 == .n 6 && decide (q.2 < 4)) = true

theorem sqPlace_of {lv : OsLvl} (h : sqPlaceB lv = true) : SqPlace lv := by
  simp only [sqPlaceB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem sq_holds_events {C : CallRel} {rd : Reader} {σ : Val} {f : String} {fn : Fn} {es : List Memory.Ev}
    {vs : List V} {kret : List E → Prop} (hf : coreProgram.find? f = some fn)
    (hh : Stmt.HoldsList C rd σ fn.body False kret) (hw : walk σ fn.body = .ret es vs) :
    ∀ e ∈ es, e.Holds rd σ := by
  have := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at this
  exact fun e he => (this.1 e he).1

/-! ## One iteration -/

/-- **One iteration of a squeeze loop, placed at `fp`**: its tail at `fp + fs L` (or skipped at
the last), its decoder after the tail's `m` words, its loads through the row in `R`. -/
theorem sqLoop_iter (fs : String → ℕ) (cert : String → V → ℕ) {lv : OsLvl} (hpl : SqPlace lv)
    {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn) (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hb : fn.body = sqLoopOf lv) (hlp : coreProgram.loop lv.sqLoop = true) (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth) {rd : Reader}
    {R Rd Dd Dt : ℕ → Prop} {x N sqz qpos qbp : E} {cv : Digest} (fp : ℕ) {m : ℕ}
    (l0 : LoadHolds rd (sqz * (x * x)) 0 (digestScalars cv).1)
    (l1 : LoadHolds rd (sqz * (x * x)) 1 (digestScalars cv).2)
    (l2 : LoadHolds rd (sqz * (x * x)) 2 (digestScalars (sqCv cv)).1)
    (l3 : LoadHolds rd (sqz * (x * x)) 3 (digestScalars (sqCv cv)).2)
    (hdec : RelAtIn coreProgram fs cert rd Rd Dd (fp + fs lv.sqLoop + m) (fs lv.decode) lv.decode
      [challengeOf (sqCv cv), qpos * gen ^ lv.posOff * x ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * x ^ (192 / lv.depth)] [])
    (hRd : ∀ i, Rd i → R i) (hK : IsInK (x * gen + N))
    (htail : if x * gen + N ≠ 0 then RelAtIn coreProgram fs cert rd R Dt (fp + fs lv.sqLoop) m lv.sqLoop
      [x * gen, N, sqz, qpos, qbp] [] else m = fs lv.sqLoop)
    (hreg : ∀ t < 4, OqIn R ((sqz * (x * x)).limb 0 * Parameters.gpow t)) :
    RelAtIn coreProgram fs cert rd R (fun i => Dd i ∨ (x * gen + N ≠ 0 ∧ Dt i)) fp
      (fs lv.sqLoop + m + fs lv.decode) lv.sqLoop [x, N, sqz, qpos, qbp] [] := by
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = sqIterVal lv x N sqz qpos qbp cv := ⟨_, rfl⟩
  obtain ⟨parg, p6, p24, pp1, pp2, pe2, pe4⟩ := sqIterVal_ptrs hpo hdig x N sqz qpos qbp cv
  rw [← hσ] at parg p6 p24 pp1 pp2 pe2 pe4
  have hargs : ([.n 0, .n 1, .n 2, .n 3, .n 4] : List V).map σ = [x, N, sqz, qpos, qbp] := by
    simp only [List.map_cons, List.map_nil, parg 0 (by omega), parg 1 (by omega), parg 2 (by omega),
      parg 3 (by omega), parg 4 (by omega)]
    rfl
  have hholds : Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs => rs = []) := by
    rw [hb, hσ]
    refine sqIter_holds hpo hdig l0 l1 l2 l3 hdec.relAt.rel hK fun hne => ?_
    rw [ite_pos' hne] at htail
    exact htail.relAt.rel
  have hbody : fn.body = sqLoopPre lv ++ [.ret []] := hb.trans (sqLoopOf_split lv)
  set es := (sqLoopPre lv).flatMap (Main.slEvs σ)
  have hw' : walk σ fn.body = .ret es [] := by rw [hbody]; exact Main.walk_straight σ [] _ hpl.straight
  have hev := sq_holds_events hfind hholds hw'
  obtain ⟨had, hal, hadr, hcl⟩ := Main.straight_parts σ _ hpl.straight
  have hal0 : allocs σ es = [] := by rw [hal, hpl.allocs]; rfl
  have hcalls : calls es = [⟨lv.decode, [.n 24, .n (sqP1 lv).2.1, .n (sqP2 lv).2.1], [], true⟩] ++
      [⟨lv.sqLoop, [.n (sqE lv + 4), .n 1, .n 2, .n 3, .n 4], [], decide (σ (.n (sqE lv + 2)) ≠ 0)⟩] := by
    rw [hcl, hpl.calls]; rfl
  have hdargs : ([.n 24, .n (sqP1 lv).2.1, .n (sqP2 lv).2.1] : List V).map σ =
      [challengeOf (sqCv cv), qpos * gen ^ lv.posOff * x ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * x ^ (192 / lv.depth)] := by
    simp only [List.map_cons, List.map_nil, p24, pp1, pp2]
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) coreProgram_wf
    (R := R) (D := fun i => Dd i ∨ (x * gen + N ≠ 0 ∧ Dt i)) (Dk := fun i => False ∨ (true = true ∧ Dd i))
    (Rt := R) (Dt := Dt) (fp := fp) (m := m) (N := fs lv.decode) hfind hlp (hp ▸ hargs) hw' rfl hev hcalls ?_
    (by rw [had, hpl.allocs, hal0]; rfl)
    (fun q hq' => by rw [hadr, hpl.addrs] at hq'; simp at hq')
    ?_ (fun i hi => Or.inl hi) (fun A hA => ?_) ?_
  · rwa [hal0, List.sum_nil, Nat.add_zero] at h
  · by_cases ht : x * gen + N ≠ 0
    · rw [ite_pos' ht] at htail
      simp only [pe2]
      rw [ite_pos' (decide_eq_true ht), List.map_nil]
      have : ([.n (sqE lv + 4), .n 1, .n 2, .n 3, .n 4] : List V).map σ = [x * gen, N, sqz, qpos, qbp] := by
        simp only [List.map_cons, List.map_nil, pe4, parg 1 (by omega), parg 2 (by omega), parg 3 (by omega),
          parg 4 (by omega)]
        rfl
      rw [this]; exact htail
    · rw [ite_neg' ht] at htail
      simp only [pe2]
      rw [ite_neg' (by simpa using ht)]
      exact htail
  · rw [hal0, List.sum_nil, Nat.add_zero]
    refine ⟨fs lv.decode, 0, Rd, Dd, rfl, fun i hi => Or.inl (Or.inl (hRd i hi)), ?_, rfl, fun i hi => hi⟩
    simp only [↓reduceIte, List.map_nil]
    rw [hdargs]; exact hdec
  · rw [loadAddrs_straight σ _ hpl.straight] at hA
    obtain ⟨⟨p, off⟩, hq', rfl⟩ := List.mem_map.mp hA
    have hb' := List.all_eq_true.mp hpl.loads _ hq'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb'
    obtain ⟨rfl, ho⟩ := hb'
    obtain ⟨i, hi, hR⟩ := hreg off ho
    exact ⟨i, by rw [p6]; exact hi, Or.inr (Or.inl hR)⟩
  · intro i hi
    rcases hi with hi | ⟨ht, hi⟩
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, hi⟩))
    · refine Or.inr (Or.inr ⟨?_, hi⟩)
      simp only [pe2]
      exact decide_eq_true ht

/-! ## The loop -/

/-- The words of the squeeze loop from iteration `j` of `n`: each iteration's frame and decoder,
then the skipped tail's frame. -/
def sqTot (fs : String → ℕ) (lv : OsLvl) (n j : ℕ) : ℕ :=
  (n - j + 1) * fs lv.sqLoop + (n - j) * fs lv.decode

/-- The tail's words after iteration `j`. -/
def sqTailTot (fs : String → ℕ) (lv : OsLvl) (n j : ℕ) : ℕ :=
  if j + 1 < n then sqTot fs lv n (j + 1) else fs lv.sqLoop

/-- Iteration `j`'s decoder, the loop entered at `fp`. -/
def sqDecAt (fs : String → ℕ) (lv : OsLvl) (n fp j : ℕ) : ℕ :=
  fp + j * fs lv.sqLoop + fs lv.sqLoop + sqTailTot fs lv n j

theorem sqTot_step (fs : String → ℕ) (lv : OsLvl) {n j : ℕ} (hj : j < n) :
    sqTot fs lv n j = fs lv.sqLoop + sqTailTot fs lv n j + fs lv.decode := by
  unfold sqTailTot sqTot
  split
  · rw [show n - j = (n - (j + 1)) + 1 by omega, Nat.add_mul, Nat.add_mul (n - (j + 1)) 1]; ring
  · rw [show n - j = 1 by omega]; ring

theorem sqTot_le (fs : String → ℕ) (lv : OsLvl) {n j : ℕ} (hj : j ≤ n) :
    j * fs lv.sqLoop + sqTot fs lv n j ≤ sqTot fs lv n 0 := by
  unfold sqTot
  have h1 : (n - 0 + 1) * fs lv.sqLoop = j * fs lv.sqLoop + (n - j + 1) * fs lv.sqLoop := by
    rw [← Nat.add_mul]; congr 1; omega
  have h2 : (n - j) * fs lv.decode ≤ (n - 0) * fs lv.decode := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The decoders' frame runs from iteration `j`. -/
def sqRuns (fs : String → ℕ) (cert : String → V → ℕ) (lv : OsLvl) (n fp : ℕ) (w : ℕ → E) (j : ℕ) :
    Main.Layout :=
  ((List.range (n - j)).map fun i => dqRunL cert lv.decode (sqDecAt fs lv n fp (j + i)) (w (j + i))).flatten

theorem regionL_sqRuns {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLvl} {n fp : ℕ} {w : ℕ → E}
    {j i : ℕ} : RegionL (sqRuns fs cert lv n fp w j) i ↔
      ∃ j', j ≤ j' ∧ j' < n ∧ RegionL (dqRunL cert lv.decode (sqDecAt fs lv n fp j') (w j')) i := by
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range] at hq
    obtain ⟨_, ⟨t, ht, rfl⟩, hq⟩ := hq
    exact ⟨j + t, by omega, by omega, q, hq, h1, h2⟩
  · rintro ⟨j', h1, h2, q, hq, h3, h4⟩
    refine ⟨q, ?_, h3, h4⟩
    simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range]
    exact ⟨_, ⟨j' - j, by omega, by rw [show j + (j' - j) = j' by omega]⟩, hq⟩

/-- The challenge of iteration `j` from the chain state `cv`. -/
def sqW (cv : Digest) (j : ℕ) : E := challengeOf (sqCv (sqAll j cv).2)

theorem sqDecAt_eq (fs : String → ℕ) (lv : OsLvl) {n j : ℕ} (fp : ℕ) (hj : j < n) :
    sqDecAt fs lv n fp j = fp + (n + 1) * fs lv.sqLoop + (n - 1 - j) * fs lv.decode := by
  obtain ⟨t, rfl⟩ : ∃ t, n = j + 1 + t := ⟨n - j - 1, by omega⟩
  unfold sqDecAt sqTailTot sqTot
  split
  · rw [show j + 1 + t - (j + 1) = t by omega, show j + 1 + t - 1 - j = t by omega]; ring
  · obtain rfl : t = 0 := by omega
    rw [show j + 1 + 0 - 1 - j = 0 by omega]; ring

/-- Blocks in pairwise disjoint windows, each disjoint, are disjoint: the first parts, then the
second parts. -/
theorem os_disj_windows {m : ℕ} (A B : ℕ → Main.Layout) (lo len : ℕ → ℕ)
    (hD : ∀ j < m, DisjL (A j ++ B j)) (hW : ∀ j < m, Within (A j ++ B j) (lo j) (len j))
    (hsep : ∀ i < m, ∀ j < m, i ≠ j → lo i + len i ≤ lo j ∨ lo j + len j ≤ lo i) :
    DisjL (((List.range m).map A).flatten ++ ((List.range m).map B).flatten) := by
  have hwin : ∀ i < m, ∀ j < m, i ≠ j → ∀ x ∈ A i ++ B i, ∀ y ∈ A j ++ B j,
      x.1 + x.2.length ≤ y.1 ∨ y.1 + y.2.length ≤ x.1 := fun i hi j hj hij x hx y hy => by
    have h1 := hW i hi x hx; have h2 := hW j hj y hy; have := hsep i hi j hj hij; omega
  have hpr : ∀ (C : ℕ → Main.Layout), (∀ j < m, ∀ x ∈ C j, x ∈ A j ++ B j) → (∀ j < m, DisjL (C j)) →
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
  refine ⟨hpr A (fun j _ x hx => List.mem_append_left _ hx) (fun j hj => (List.pairwise_append.mp (hD j hj)).1),
    hpr B (fun j _ x hx => List.mem_append_right _ hx) (fun j hj => (List.pairwise_append.mp (hD j hj)).2.1),
    fun x hx y hy => ?_⟩
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
the state chain at `sqz` and, at `qpos` and `qbp`, what each decoder stores (the positions and
the pointers into its frame run at `sqDecAt`), the loop holds, its decoders' frame runs its data
(`sqRuns`). -/
theorem sqLoop_relAtIn (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {lv : OsLvl} (hpl : SqPlace lv)
    {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn) (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hb : fn.body = sqLoopOf lv) (hlp : coreProgram.loop lv.sqLoop = true) (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth)
    (hdec : OsDecodeAtD fs cert k lv.depth lv.decode) {n : ℕ} (hn : 0 < n) (hn' : n + 1 < ordG)
    {sqz qpos qbp : E} {cv : Digest} {Lin : Main.Layout} (fp : ℕ)
    (hmem : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < n,
      LoadHolds rd sqz (2 * j) (digestScalars (sqAll j cv).2).1 ∧
        LoadHolds rd sqz (2 * j + 1) (digestScalars (sqAll j cv).2).2 ∧
        LoadHolds rd sqz (2 * j + 2) (digestScalars (sqCv (sqAll j cv).2)).1 ∧
        LoadHolds rd sqz (2 * j + 3) (digestScalars (sqCv (sqAll j cv).2)).2)
    (hdmem : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < n, ∀ i < 192 / lv.depth,
      LoadHolds rd (qpos * gen ^ (lv.posOff + j * (192 / lv.depth))) i
          (eOfNat ((eToNat (sqW cv j) >>> (i * lv.depth)) % 2 ^ lv.depth)) ∧
        LoadHolds rd (qbp * gen ^ (lv.posOff + j * (192 / lv.depth))) i
          (ofK (Parameters.gpow (sqDecAt fs lv n fp j + cert lv.decode (.n 3))) * gen ^ (i * lv.depth)))
    (hreg : ∀ j < n, ∀ t < 4, OqIn (RegionL Lin) (sqz.limb 0 * Parameters.gpow (2 * j + t))) :
    ∃ Lown : Main.Layout, Within (sqRuns fs cert lv n fp (sqW cv) 0 ++ Lown) fp (sqTot fs lv n 0) ∧
      DisjL (sqRuns fs cert lv n fp (sqW cv) 0 ++ Lown) ∧ ∀ rd, LowDef k rd → MemL rd (sqRuns fs cert lv n fp (sqW cv) 0 ++ Lown ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL (sqRuns fs cert lv n fp (sqW cv) 0)) fp
          (sqTot fs lv n 0) lv.sqLoop [1, gen ^ n, sqz, qpos, qbp] [] := by
  have hn'' : n + 1 < 2 ^ 64 - 1 := hn'
  have hptr : ∀ j, ∀ (b : E), b * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth) =
      b * gen ^ (lv.posOff + j * (192 / lv.depth)) := fun j b => by
    rw [← pow_mul, mul_assoc, ← pow_add]
  have hdecj : ∀ j < n, ∃ Lj : Main.Layout,
      Within (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqW cv j) ++ Lj) (sqDecAt fs lv n fp j) (fs lv.decode) ∧
      DisjL (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqW cv j) ++ Lj) ∧ ∀ rd, LowDef k rd → MemL rd (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqW cv j) ++ Lj ++ Lin) →
        RelAtIn coreProgram fs cert rd (RegionL Lin)
          (RegionL (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqW cv j))) (sqDecAt fs lv n fp j) (fs lv.decode)
          lv.decode [sqW cv j, qpos * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth),
            qbp * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth)] [] := fun j hj => by
    rw [hptr, hptr]
    exact hdec _ _ _ Lin _ fun rd hl hm i hi => hdmem rd hl hm j hj i hi
  classical
  let Lj : ℕ → Main.Layout := fun j => if h : j < n then Classical.choose (hdecj j h) else []
  have hLj : ∀ j (h : j < n), Lj j = Classical.choose (hdecj j h) := fun j h => by simp [Lj, h]
  let Lown : Main.Layout := ((List.range n).map Lj).flatten
  refine ⟨Lown, ?_, ?_, fun rd hlow hL => ?_⟩
  · rw [within_append]
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨j, hj, rfl⟩, hq⟩ := hq
      simp only [Nat.zero_add] at hq
      have hw := (Classical.choose_spec (hdecj j (by omega))).1 q (List.mem_append_left _ hq)
      have := sqTot_le fs lv (n := n) (j := j) (by omega)
      have := sqTot_step fs lv (n := n) (j := j) (by omega)
      simp only [sqDecAt] at hw ⊢
      omega
    · simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨j, hj, rfl⟩, hq⟩ := hq
      rw [hLj j hj] at hq
      have hw := (Classical.choose_spec (hdecj j hj)).1 q (List.mem_append_right _ hq)
      have := sqTot_le fs lv (n := n) (j := j) (by omega)
      have := sqTot_step fs lv (n := n) (j := j) hj
      simp only [sqDecAt] at hw ⊢
      omega
  · have e1 : sqRuns fs cert lv n fp (sqW cv) 0 =
        ((List.range n).map fun j => dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqW cv j)).flatten := by
      simp [sqRuns]
    rw [e1]
    refine os_disj_windows _ Lj (fun j => sqDecAt fs lv n fp j) (fun _ => fs lv.decode) (fun j hj => ?_)
      (fun j hj => ?_) (fun i hi j hj hij => ?_)
    · rw [hLj j hj]; exact (Classical.choose_spec (hdecj j hj)).2.1
    · rw [hLj j hj]; exact (Classical.choose_spec (hdecj j hj)).1
    · rw [sqDecAt_eq fs lv fp hi, sqDecAt_eq fs lv fp hj]
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · right
        have : (n - 1 - j + 1) * fs lv.decode ≤ (n - 1 - i) * fs lv.decode := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      · left
        have : (n - 1 - i + 1) * fs lv.decode ≤ (n - 1 - j) * fs lv.decode := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
  obtain ⟨h12, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hR, hO⟩ := Main.memL_append.mp h12
  have hd := hmem rd hlow hLin
  have hrel : ∀ j (hj : j < n), RelAtIn coreProgram fs cert rd (RegionL Lin)
      (RegionL (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqW cv j))) (sqDecAt fs lv n fp j) (fs lv.decode)
      lv.decode [sqW cv j, qpos * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth)] [] := fun j hj => by
    refine (Classical.choose_spec (hdecj j hj)).2.2 rd hlow (Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨?_, ?_⟩, hLin⟩)
    · intro q hq
      exact hR q (by
        simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range]
        exact ⟨_, ⟨j, hj, by simp⟩, hq⟩)
    · intro q hq
      rw [← hLj j hj] at hq
      exact hO q (by
        simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range]
        exact ⟨_, ⟨j, hj, rfl⟩, hq⟩)
  have hstep : ∀ t j, j + t + 1 = n →
      RelAtIn coreProgram fs cert rd (RegionL Lin) (fun i => RegionL (sqRuns fs cert lv n fp (sqW cv) j) i)
        (fp + j * fs lv.sqLoop) (sqTot fs lv n j) lv.sqLoop [gen ^ j, gen ^ n, sqz, qpos, qbp] [] := by
    intro t
    induction t with
    | zero =>
      intro j hj
      obtain ⟨m0, m1, m2, m3⟩ := hd j (by omega)
      have h0 : gen ^ j * gen + gen ^ n = 0 := by rw [gen_pow_add_eq_zero_iff]; congr 1; omega
      have := sqLoop_iter fs cert hpl hfind hp hb hlp hpo hdig (rd := rd) (R := RegionL Lin) (Dt := fun _ => False)
        (N := gen ^ n) (sqz := sqz) (qpos := qpos) (qbp := qbp) (cv := (sqAll j cv).2) (fp + j * fs lv.sqLoop)
        (m := fs lv.sqLoop)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow, Nat.add_zero]; exact m0)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m1)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m2)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m3)
        (by
          have := hrel j (by omega)
          rwa [sqDecAt, sqTailTot, ite_neg' (by omega)] at this)
        (fun i h => h) (by rw [h0]; exact (isInK_iff _).mpr ⟨0, ofK_zero.symm⟩)
        (by rw [ite_neg' (by simp [h0])])
        (fun t ht => by
          obtain ⟨i, hi, hR'⟩ := hreg j (by omega) t ht
          refine ⟨i, ?_, hR'⟩
          rw [os_gen_pow_sq, oq_limb_mul_gen_pow m0.1]; exact hi)
      rw [show sqTot fs lv n j = fs lv.sqLoop + fs lv.sqLoop + fs lv.decode by
        rw [sqTot_step fs lv (by omega), sqTailTot, ite_neg' (by omega)]]
      refine relAtIn_dmono this fun i hi => ?_
      obtain ⟨j', h1, h2, hi'⟩ := regionL_sqRuns.mp hi
      obtain rfl : j' = j := by omega
      exact Or.inl (by rwa [sqDecAt, sqTailTot, ite_neg' (by omega)] at hi')
    | succ t ih =>
      intro j hj
      obtain ⟨m0, m1, m2, m3⟩ := hd j (by omega)
      have hne : gen ^ j * gen + gen ^ n ≠ 0 := by
        rw [ne_eq, gen_pow_add_eq_zero_iff]
        intro he
        have := gen_pow_inj (by omega) (by omega) he
        omega
      have ht := ih (j + 1) (by omega)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc] at ht
      have := sqLoop_iter fs cert hpl hfind hp hb hlp hpo hdig (rd := rd) (R := RegionL Lin)
        (Dt := fun i => RegionL (sqRuns fs cert lv n fp (sqW cv) (j + 1)) i)
        (N := gen ^ n) (sqz := sqz) (qpos := qpos) (qbp := qbp) (cv := (sqAll j cv).2) (fp + j * fs lv.sqLoop)
        (m := sqTot fs lv n (j + 1))
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow, Nat.add_zero]; exact m0)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m1)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m2)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m3)
        (by
          have := hrel j (by omega)
          rwa [sqDecAt, sqTailTot, ite_pos' (by omega)] at this)
        (fun i h => h) (isInK_add (by rw [gen_pow_mul_gen]; exact gen_pow_isInK _) (gen_pow_isInK _))
        (by rw [ite_pos' hne, gen_pow_mul_gen]; exact ht)
        (fun t ht => by
          obtain ⟨i, hi, hR'⟩ := hreg j (by omega) t ht
          refine ⟨i, ?_, hR'⟩
          rw [os_gen_pow_sq, oq_limb_mul_gen_pow m0.1]; exact hi)
      rw [show sqTot fs lv n j = fs lv.sqLoop + sqTot fs lv n (j + 1) + fs lv.decode by
        rw [sqTot_step fs lv (by omega), sqTailTot, ite_pos' (by omega)]]
      refine relAtIn_dmono this fun i hi => ?_
      obtain ⟨j', h1, h2, hi'⟩ := regionL_sqRuns.mp hi
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact Or.inl (by rwa [sqDecAt, sqTailTot, ite_pos' (by omega)] at hi')
      · exact Or.inr ⟨hne, regionL_sqRuns.mpr ⟨j', by omega, h2, hi'⟩⟩
  have := hstep (n - 1) 0 (by omega)
  simpa using this

end
end LeanVM.Guest.B1
