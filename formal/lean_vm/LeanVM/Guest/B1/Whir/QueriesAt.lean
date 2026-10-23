/-
  LeanVM.Guest.B1.Whir.QueriesAt

  `opening_queries`' loop helper placed (`RelAtIn`): one iteration's path, its frame run, where
  its loads read.
-/

module

public import LeanVM.Guest.B1.Whir.QueriesIter
public import LeanVM.Guest.B1.Uniform

/-!
# One query, placed (TRIAGE #28, #35)

The loop body is straight-line: its statements before the final `ret []` (`oqLoopPre`) are atoms
and the tail's `callIf`. `OqPlace` lists what each specialization's body is, checked by kernel
evaluation: straight-line, no `HeapBuf`, one `frameAddr` (`verify_merkle_path`'s run of hinted
children, 80 cells from `.n P`), one call (the tail), and loads only through the weights, the
query sum's steps, the query's weight and bit run, the bits, the run (`.n (P + 86)` and the
levels' children), the flag and the cap (`oqLoadB`).

`oqLoop_iter`: one iteration at `fp`, its tail at `fp + fs L` (`relAtIn_of_walk_loop`), its run's
first `4·pd` cells its own data, every other load in the caller's region.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The body's statements -/

/-- The loop body before its final `ret []`. -/
def oqLoopPre (base I blocks pd cd : ℕ) (loop : String) : List Stmt :=
  (oqLoopBody base I blocks pd cd loop).dropLast

/-- A `frameAddr`'s run: its first value and its length. -/
def oqRunS : Stmt → Option (V × ℕ)
  | .atom (.frameAddr _ (r :: rs)) => some (r, rs.length + 1)
  | _ => none

/-- The first value of the cap leaf's tail. -/
def oqK7 (base I blocks pd cd : ℕ) : ℕ := oqP base I blocks + 79 + 13 * pd + 6 * cd - 5

/-- Where a load of the loop body reads (its pointer value and offset), as a check. -/
def oqLoadB (base I blocks pd cd : ℕ) (q : V × ℕ) : Bool :=
  let K2 := oqK2 base I blocks
  let P := oqP base I blocks
  let K7 := oqK7 base I blocks pd cd
  (q.1 == .n 2 && decide (q.2 < I)) || q == (.n K2, 0) || q == (.n (K2 + 2), 0) || q == (.n (K2 + 6), 1) ||
    q == (.n (K2 + 7), 0) || (q.1 == .n (P - 1) && decide (q.2 < pd + cd)) ||
    (q.1 == .n (P + 86) && decide (q.2 < 2)) ||
    ((List.range pd).any fun l => decide (1 ≤ l) && q.1 == .n (P + 79 + 13 * l + 7) && decide (q.2 < 2)) ||
    q == (.n (K7 + 1), 0) || q == (.n (K7 + 10), 0) || q == (.n (K7 + 14), 0)

/-- **The body of a specialization's loop helper**, checked by kernel evaluation. -/
structure OqPlace (base I blocks pd cd : ℕ) (loop : String) : Prop where
  straight : (oqLoopPre base I blocks pd cd loop).all Main.Stmt.straight = true
  allocs : (oqLoopPre base I blocks pd cd loop).filterMap Main.Stmt.allocSz = []
  addrs : (oqLoopPre base I blocks pd cd loop).filterMap Main.Stmt.addrS =
    [(.n (oqP base I blocks + 4 * pd), .n (oqP base I blocks))]
  runs : (oqLoopPre base I blocks pd cd loop).filterMap oqRunS = [(.n (oqP base I blocks), 80)]
  calls : (oqLoopPre base I blocks pd cd loop).filterMap Main.Stmt.callS =
    [(some (.n (oqK7 base I blocks pd cd + 17)), loop,
      [.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [])]
  loads : ((oqLoopPre base I blocks pd cd loop).filterMap Stmt.loadS).all (oqLoadB base I blocks pd cd) = true

theorem oqLoopBody_split (base I blocks pd cd : ℕ) (loop : String) :
    oqLoopBody base I blocks pd cd loop = oqLoopPre base I blocks pd cd loop ++ [.ret []] := by
  unfold oqLoopPre
  have hne : oqLoopBody base I blocks pd cd loop ≠ [] := by simp [oqLoopBody, oqCapT]
  have hl : (oqLoopBody base I blocks pd cd loop).getLast hne = .ret [] := by simp [oqLoopBody, oqCapT]
  conv_lhs => rw [← List.dropLast_append_getLast hne, hl]

theorem oq_runs_straight (σ : Val) : ∀ pre : List Stmt, pre.all Main.Stmt.straight = true →
    runs (pre.flatMap (Main.slEvs σ)) = pre.filterMap oqRunS
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := oq_runs_straight σ pre h.2
    simp only [runs, List.flatMap_cons, List.filterMap_append] at ih ⊢
    rw [ih]
    match s, h.1 with
    | .atom a, _ =>
      cases a with
      | frameAddr p run => cases run <;> simp [Main.slEvs, Ev.run?, oqRunS, List.filterMap_cons]
      | _ => simp [Main.slEvs, Ev.run?, oqRunS, List.filterMap_cons]
    | .call .., _ => simp [Main.slEvs, Ev.run?, oqRunS, List.filterMap_cons]
    | .callIf c _ _, _ =>
      by_cases hc : σ c = 0 <;> simp [Main.slEvs, hc, Ev.run?, oqRunS, List.filterMap_cons]

private theorem oq_holds_events {C : CallRel} {rd : Reader} {σ : Val} {f : String} {fn : Fn} {es : List Ev}
    {vs : List V} {kret : List E → Prop} (hf : coreProgram.find? f = some fn)
    (hh : Stmt.HoldsList C rd σ fn.body False kret) (hw : walk σ fn.body = .ret es vs) :
    ∀ e ∈ es, e.Holds rd σ := by
  have := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at this
  exact fun e he => (this.1 e he).1

/-- A pointer `g^a` times `g^j`, read at `off`: the word `a + j + off`. -/
theorem oq_addr (a j off : ℕ) : (ofK (Parameters.gpow a) * gen ^ j).limb 0 * Parameters.gpow off = Parameters.gpow (a + j + off) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, limb_ofK]
  simp [Parameters.gpow, pow_add]

/-! ## One iteration -/

/-- `A` is a word of the region `R`. -/
def OqIn (R : ℕ → Prop) (A : K) : Prop := ∃ i, A = Parameters.gpow i ∧ R i

/-- **One iteration of `opening_queries`' loop, placed at `fp`**: its tail at `fp + fs L` (or
skipped at the last), its frame run's first `4·pd` cells its own, every other load in `R`. -/
theorem oqLoop_iter (fs : String → ℕ) (cert : String → V → ℕ) {base I blocks pd cd : ℕ}
    (hs : OqShape base I blocks pd cd) {loop : String} {lf : Fn} (hfind : coreProgram.find? loop = some lf)
    (hp : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hb : lf.body = oqLoopBody base I blocks pd cd loop) (hpl : OqPlace base I blocks pd cd loop)
    (hlp : coreProgram.loop loop = true) {rd : Reader} {R : ℕ → Prop}
    {x N rew qsc qw qbp flags cap : E} {leaf : List K} (hleaf : leaf.length = oqR base I) {q : ℕ}
    (hq : q < 2 ^ (pd + cd)) {sibs : List Digest} (hsl : sibs.length = pd) (fp : ℕ) {m : ℕ}
    (hw : ∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw))
    (hs0 : LoadHolds rd (qsc * x) 0 (memAt rd (qsc * x) 0))
    (hw0 : LoadHolds rd (qw * x) 0 (memAt rd (qw * x) 0))
    (hs1 : LoadHolds rd (qsc * x) 1 (memAt rd (qsc * x) 0 + memAt rd (qw * x) 0 *
      ∑ jw ∈ Finset.range I, leafRowWord base leaf jw * memAt rd rew jw))
    (hdbp : LoadHolds rd (qbp * x) 0 (memAt rd (qbp * x) 0))
    (hbits : ∀ l < pd + cd, LoadHolds rd (memAt rd (qbp * x) 0) l (bitE (q.testBit l)))
    (hcell : ∀ j < 4 * pd, LoadHolds rd (ofK (Parameters.gpow (fp + cert loop (.n (oqP base I blocks))))) j
      ((climbCells (hashWords leaf) q sibs).getD j 0))
    (hflag : LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) 1)
    (hcap : CapCell rd cap (2 ^ cd + q / 2 ^ pd) (climb (m := Id) blake2sBytes (hashWords leaf) q sibs))
    (hK : IsInK (x * gen + N))
    (htail : if x * gen + N ≠ 0 then RelAtIn coreProgram fs cert rd R (fun _ => False) (fp + fs loop) m loop
      [x * gen, N, rew, qsc, qw, qbp, flags, cap] [] else m = fs loop)
    (hRw : ∀ jw < I, OqIn R (rew.limb 0 * Parameters.gpow jw))
    (hRs : OqIn R ((qsc * x).limb 0 * Parameters.gpow 0) ∧ OqIn R ((qsc * x).limb 0 * Parameters.gpow 1))
    (hRq : OqIn R ((qw * x).limb 0 * Parameters.gpow 0)) (hRb : OqIn R ((qbp * x).limb 0 * Parameters.gpow 0))
    (hRd : ∀ l < pd + cd, OqIn R ((memAt rd (qbp * x) 0).limb 0 * Parameters.gpow l))
    (hRf : OqIn R ((flags * gen ^ (2 ^ (cd - 1) + q / 2 ^ (pd + 1))).limb 0 * Parameters.gpow 0))
    (hRc : OqIn R ((cap * gen ^ (2 * (2 ^ cd + q / 2 ^ pd))).limb 0 * Parameters.gpow 0) ∧
      OqIn R ((cap * gen ^ (2 * (2 ^ cd + q / 2 ^ pd) + 1)).limb 0 * Parameters.gpow 0)) :
    RelAtIn coreProgram fs cert rd R (fun _ => False) fp (fs loop + m) loop [x, N, rew, qsc, qw, qbp, flags, cap] [] := by
  set P := oqP base I blocks
  set c0 := fp + cert loop (.n P)
  set ptr : E := ofK (Parameters.gpow c0)
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = oqIterVal rd [x, N, rew, qsc, qw, qbp, flags, cap] base I blocks pd cd leaf q sibs ptr :=
    ⟨_, rfl⟩
  have hptrK : IsInK ptr := (isInK_iff _).mpr ⟨_, rfl⟩
  have hbits' : ∀ l < pd + cd, memAt rd (memAt rd (qbp * x) 0) l = bitE (q.testBit l) :=
    fun l hl => memAt_of_load (hbits l hl)
  obtain ⟨p2, pk2, pk22, pk26, pk27, pdb, p86, plv, pf, pc0, pc1, p17, p19, pptr, parg⟩ :=
    oqIterVal_ptrs (rd := rd) (N := N) (rew := rew) (flags := flags) (cap := cap) (ptr := ptr) (leaf := leaf) hs hq
      hsl hbits'
  rw [← hσ] at p2 pk2 pk22 pk26 pk27 pdb p86 plv pf pc0 pc1 p17 p19 pptr parg
  change σ (.n (oqK7 base I blocks pd cd + 17)) = x * gen + N at p17
  change σ (.n (oqK7 base I blocks pd cd + 19)) = x * gen at p19
  have hargs : ([.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map σ = [x, N, rew, qsc, qw, qbp, flags, cap] := by
    simp only [List.map_cons, List.map_nil, parg 0 (by omega), parg 1 (by omega), parg 2 (by omega),
      parg 3 (by omega), parg 4 (by omega), parg 5 (by omega), parg 6 (by omega), parg 7 (by omega)]
    rfl
  have hholds : Stmt.HoldsList (coreProgram.Rel rd) rd σ lf.body False (fun rs => rs = []) := by
    rw [hb, hσ]
    refine oqIter_holds hs hleaf hq hsl hw hs0 hw0 hs1 hdbp hbits hptrK hcell hflag hcap hK fun hne => ?_
    rw [ite_pos' hne] at htail
    exact htail.relAt.rel
  have hbody : lf.body = oqLoopPre base I blocks pd cd loop ++ [.ret []] := hb.trans (oqLoopBody_split _ _ _ _ _ _)
  set es := (oqLoopPre base I blocks pd cd loop).flatMap (Main.slEvs σ)
  have hw' : walk σ lf.body = .ret es [] := by rw [hbody]; exact Main.walk_straight σ [] _ hpl.straight
  have hev := oq_holds_events hfind hholds hw'
  obtain ⟨had, hal, hadr, hcl⟩ := Main.straight_parts σ _ hpl.straight
  have hal0 : allocs σ es = [] := by rw [hal, hpl.allocs]; rfl
  have hcalls : calls es = [] ++ [⟨loop, [.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      [], decide (σ (.n (oqK7 base I blocks pd cd + 17)) ≠ 0)⟩] := by
    rw [hcl, hpl.calls]; rfl
  have hrun : (.n P, 80) ∈ runs es := by rw [oq_runs_straight σ _ hpl.straight, hpl.runs]; simp [P]
  have hown : ∀ t < 80, ownData cert fp (fp + fs loop + m) loop (allocs σ es) es (c0 + t) := fun t ht =>
    Or.inr ⟨_, hrun, Nat.le_add_right c0 t, Nat.add_lt_add_left ht c0⟩
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) coreProgram_wf
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False) (fp := fp) (m := m)
    (N := 0) hfind hlp (hp ▸ hargs) hw' rfl hev hcalls ?_
    (by rw [had, hpl.allocs, hal0]; rfl)
    (fun q hq' => by
      rw [hadr, hpl.addrs] at hq'
      simp only [List.mem_singleton] at hq'
      subst hq'
      exact pptr)
    (by rw [hal0]; exact ⟨rfl, fun i h => h.elim⟩)
    (fun i hi => Or.inl hi)
    (fun A hA => ?_)
    (fun _ h => h.elim)
  · rw [hal0, List.sum_nil, Nat.add_zero, Nat.add_zero, List.map_nil] at h; exact h
  · by_cases ht : x * gen + N ≠ 0
    · rw [ite_pos' ht] at htail
      simp only [p17]
      rw [ite_pos' (decide_eq_true ht), List.map_nil]
      have : ([.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] : List V).map σ =
          [x * gen, N, rew, qsc, qw, qbp, flags, cap] := by
        simp only [List.map_cons, List.map_nil, p19, parg 1 (by omega), parg 2 (by omega), parg 3 (by omega),
          parg 4 (by omega), parg 5 (by omega), parg 6 (by omega), parg 7 (by omega)]
        rfl
      rw [this]; exact htail
    · rw [ite_neg' ht] at htail
      simp only [p17]
      rw [ite_neg' (by simpa using ht)]
      exact htail
  · rw [loadAddrs_straight σ _ hpl.straight] at hA
    obtain ⟨⟨p, off⟩, hq', rfl⟩ := List.mem_map.mp hA
    have hb' := List.all_eq_true.mp hpl.loads _ hq'
    simp only [oqLoadB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Prod.mk.injEq,
      List.any_eq_true, List.mem_range, or_assoc, oqK7] at hb'
    have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.gpow i ∧
        (ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i ∨ R i ∨ False ∨
          ((⟨loop, [.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [],
            decide (σ (.n (oqK7 base I blocks pd cd + 17)) ≠ 0)⟩ : Call).taken = true ∧ False)) :=
      fun A ⟨i, hi, hR⟩ => ⟨i, hi, Or.inr (Or.inl hR)⟩
    have inOwn : ∀ t < 80, ∃ i, Parameters.gpow (c0 + t) = Parameters.gpow i ∧
        (ownData cert fp (fp + fs loop + m) loop (allocs σ es) es i ∨ R i ∨ False ∨
          ((⟨loop, [.n (oqK7 base I blocks pd cd + 19), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [],
            decide (σ (.n (oqK7 base I blocks pd cd + 17)) ≠ 0)⟩ : Call).taken = true ∧ False)) :=
      fun t ht => ⟨_, rfl, Or.inl (hown t ht)⟩
    rcases hb' with ⟨rfl, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, ho⟩ |
      ⟨rfl, ho⟩ | ⟨l, hl, ⟨hl1, rfl⟩, ho⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [p2]; exact inR _ (hRw off ho)
    · rw [pk2]; exact inR _ hRs.1
    · rw [pk22]; exact inR _ hRq
    · rw [pk26]; exact inR _ hRs.2
    · rw [pk27]; exact inR _ hRb
    · rw [pdb]; exact inR _ (hRd off ho)
    · rw [p86, oq_addr, Nat.add_assoc]
      exact inOwn _ (by cases q.testBit 0 <;> simp <;> omega)
    · rw [plv l hl1 hl, oq_addr, Nat.add_assoc]
      exact inOwn _ (by have := hs.pd20; cases q.testBit l <;> simp <;> omega)
    · rw [pf]; exact inR _ hRf
    · rw [pc0]; exact inR _ hRc.1
    · rw [pc1]; exact inR _ hRc.2

/-! ## The loop -/

/-- What one iteration at `x` reads from the caller's words: the weights, the query sum's step,
the query's weight, the bit run's pointer and the bits, the parent's flag, the cap leaf. -/
def OqIterMem (rd : Reader) (base I pd cd : ℕ) (rew qsc qw qbp flags cap x : E) (leaf : List K) (q : ℕ)
    (sibs : List Digest) : Prop :=
  (∀ jw < I, LoadHolds rd rew jw (memAt rd rew jw)) ∧
    LoadHolds rd (qsc * x) 0 (memAt rd (qsc * x) 0) ∧ LoadHolds rd (qw * x) 0 (memAt rd (qw * x) 0) ∧
    LoadHolds rd (qsc * x) 1 (memAt rd (qsc * x) 0 + memAt rd (qw * x) 0 *
      ∑ jw ∈ Finset.range I, leafRowWord base leaf jw * memAt rd rew jw) ∧
    LoadHolds rd (qbp * x) 0 (memAt rd (qbp * x) 0) ∧
    (∀ l < pd + cd, LoadHolds rd (memAt rd (qbp * x) 0) l (bitE (q.testBit l))) ∧
    LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (pd + 1)) 1 ∧
    CapCell rd cap (2 ^ cd + q / 2 ^ pd) (climb (m := Id) blake2sBytes (hashWords leaf) q sibs)

/-- Where one iteration at `x` reads the caller's words: in `R`. -/
def OqIterReg (R : ℕ → Prop) (rd : Reader) (I pd cd : ℕ) (rew qsc qw qbp flags cap x : E) (q : ℕ) : Prop :=
  (∀ jw < I, OqIn R (rew.limb 0 * Parameters.gpow jw)) ∧
    (OqIn R ((qsc * x).limb 0 * Parameters.gpow 0) ∧ OqIn R ((qsc * x).limb 0 * Parameters.gpow 1)) ∧
    OqIn R ((qw * x).limb 0 * Parameters.gpow 0) ∧ OqIn R ((qbp * x).limb 0 * Parameters.gpow 0) ∧
    (∀ l < pd + cd, OqIn R ((memAt rd (qbp * x) 0).limb 0 * Parameters.gpow l)) ∧
    OqIn R ((flags * gen ^ (2 ^ (cd - 1) + q / 2 ^ (pd + 1))).limb 0 * Parameters.gpow 0) ∧
    (OqIn R ((cap * gen ^ (2 * (2 ^ cd + q / 2 ^ pd))).limb 0 * Parameters.gpow 0) ∧
      OqIn R ((cap * gen ^ (2 * (2 ^ cd + q / 2 ^ pd) + 1)).limb 0 * Parameters.gpow 0))

theorem oq_length_climbCells (D : Digest) (q : ℕ) (sibs : List Digest) :
    (climbCells D q sibs).length = 4 * sibs.length := by
  rw [climbCells, List.flatMap]
  exact (oq_length_flatten_uniform _ 4 (fun _ => length_lvlCells _ _ _) _)

/-- The loop's frame runs from iteration `j0`: iteration `j0 + i` at `fp + i·fs L`. -/
def oqLoopRuns (fs : String → ℕ) (cert : String → V → ℕ) (loop : String) (P : ℕ) (fp j0 n : ℕ)
    (leaf : ℕ → List K) (pos : ℕ → ℕ) (sibs : ℕ → List Digest) : Main.Layout :=
  (List.range (n - j0)).map fun i => (fp + i * fs loop + cert loop (.n P),
    climbCells (hashWords (leaf (j0 + i))) (pos (j0 + i)) (sibs (j0 + i)))

theorem oq_disj_frames {b S c m : ℕ} {L : ℕ → List E} (h : ∀ i < m, c + (L i).length ≤ S) :
    DisjL ((List.range m).map fun i => (b + i * S + c, L i)) := by
  unfold DisjL
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := m)).imp_of_mem ?_
  intro i j hi hj hij
  left
  show b + i * S + c + (L i).length ≤ b + j * S + c
  have h1 := h i (List.mem_range.mp hi)
  have h2 : (i + 1) * S ≤ j * S := Nat.mul_le_mul_right _ hij
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

/-- **`opening_queries`' loop, placed**: from iteration `j0 < n`, on every memory holding the
iterations' frame runs and the caller's words `Lin` that the iterations read (`OqIterMem`, within
`RegionL Lin`), the loop helper is complete, its runs its own layout, its tree its `n - j0 + 1` frames. -/
theorem oqLoop_completeAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {base I blocks pd cd : ℕ}
    (hs : OqShape base I blocks pd cd) {loop : String} {lf : Fn} (hfind : coreProgram.find? loop = some lf)
    (hp : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hb : lf.body = oqLoopBody base I blocks pd cd loop) (hpl : OqPlace base I blocks pd cd loop)
    (hlp : coreProgram.loop loop = true) (hfit : cert loop (.n (oqP base I blocks)) + 4 * pd ≤ fs loop)
    {n : ℕ} (hn : n < ordG) {Lin : Main.Layout} {rew qsc qw qbp flags cap : E} {leaf : ℕ → List K}
    (hleaf : ∀ j < n, (leaf j).length = oqR base I) {pos : ℕ → ℕ} (hq : ∀ j < n, pos j < 2 ^ (pd + cd))
    {sibs : ℕ → List Digest} (hsl : ∀ j < n, (sibs j).length = pd)
    (hmem : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < n,
      OqIterMem rd base I pd cd rew qsc qw qbp flags cap (gen ^ j) (leaf j) (pos j) (sibs j) ∧
        OqIterReg (RegionL Lin) rd I pd cd rew qsc qw qbp flags cap (gen ^ j) (pos j)) :
    ∀ j0 < n, CompleteAtB fs cert k loop Lin [gen ^ j0, gen ^ n, rew, qsc, qw, qbp, flags, cap] (Returns [])
      ((n - j0 + 1) * fs loop) := by
  intro j0 hj0 fp
  have hn' : n < 2 ^ 64 - 1 := hn
  set P := oqP base I blocks
  refine ⟨(n - j0 + 1) * (fs loop), oqLoopRuns fs cert loop P fp j0 n leaf pos sibs, [], [], ⟨rfl, rfl⟩, ?_,
    ?_, le_rfl, fun rd hlow hmemL => ?_⟩
  · intro e he
    simp only [List.nil_append, oqLoopRuns, List.mem_map, List.mem_range] at he
    obtain ⟨i, hi, rfl⟩ := he
    rw [oq_length_climbCells, hsl _ (by omega)]
    refine ⟨by omega, ?_⟩
    have : (i + 1) * (fs loop) ≤ (n - j0 + 1) * (fs loop) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · rw [List.nil_append]
    exact oq_disj_frames fun i hi => by rw [oq_length_climbCells, hsl _ (by omega)]; exact hfit
  simp only [List.nil_append] at hmemL
  obtain ⟨hruns, hlin⟩ := Main.memL_append.mp hmemL
  have hd := hmem rd hlow hlin
  have hcell : ∀ j, j0 ≤ j → j < n → ∀ t < 4 * pd,
      LoadHolds rd (ofK (Parameters.gpow (fp + (j - j0) * (fs loop) + cert loop (.n P)))) t
        ((climbCells (hashWords (leaf j)) (pos j) (sibs j)).getD t 0) := by
    intro j hj1 hj2 t ht
    have := hruns _ (List.mem_map.mpr ⟨j - j0, List.mem_range.mpr (by omega), rfl⟩)
    simp only [show j0 + (j - j0) = j by omega] at this
    have hlen : t < (climbCells (hashWords (leaf j)) (pos j) (sibs j)).length := by
      rw [oq_length_climbCells, hsl j hj2]; exact ht
    have h := this t hlen
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  have hstep : ∀ t j, j + t + 1 = n → j0 ≤ j →
      RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + (j - j0) * (fs loop)) ((n - j + 1) * (fs loop)) loop
        [gen ^ j, gen ^ n, rew, qsc, qw, qbp, flags, cap] [] := by
    intro t
    induction t with
    | zero =>
      intro j hj hlo
      obtain ⟨⟨m1, m2, m3, m4, m5, m6, m7, m8⟩, r1, r2, r3, r4, r5, r6, r7⟩ := hd j (by omega)
      have h0 : gen ^ j * gen + gen ^ n = 0 := by rw [gen_pow_add_eq_zero_iff]; congr 1; omega
      have := oqLoop_iter fs cert hs hfind hp hb hpl hlp (rd := rd) (R := RegionL Lin) (N := gen ^ n)
        (hleaf j (by omega)) (hq j (by omega)) (hsl j (by omega)) (fp + (j - j0) * (fs loop)) (m := (fs loop)) m1 m2 m3 m4 m5 m6
        (hcell j hlo (by omega)) m7 m8 (by rw [h0]; exact ((isInK_iff _).mpr ⟨0, ofK_zero.symm⟩)) (by rw [ite_neg' (by simp [h0])]) r1 r2 r3 r4
        r5 r6 r7
      rwa [show n - j + 1 = 2 by omega, two_mul]
    | succ t ih =>
      intro j hj hlo
      obtain ⟨⟨m1, m2, m3, m4, m5, m6, m7, m8⟩, r1, r2, r3, r4, r5, r6, r7⟩ := hd j (by omega)
      have hne : gen ^ j * gen + gen ^ n ≠ 0 := by
        rw [ne_eq, gen_pow_add_eq_zero_iff]
        intro he
        have := gen_pow_inj (by omega) (by omega) he
        omega
      have ht := ih (j + 1) (by omega) (by omega)
      rw [show j + 1 - j0 = (j - j0) + 1 by omega, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc] at ht
      have := oqLoop_iter fs cert hs hfind hp hb hpl hlp (rd := rd) (R := RegionL Lin) (N := gen ^ n)
        (hleaf j (by omega)) (hq j (by omega)) (hsl j (by omega)) (fp + (j - j0) * (fs loop)) (m := (n - (j + 1) + 1) * (fs loop))
        m1 m2 m3 m4 m5 m6 (hcell j hlo (by omega)) m7 m8
        (isInK_add (by rw [gen_pow_mul_gen]; exact gen_pow_isInK _) (gen_pow_isInK _))
        (by rw [ite_pos' hne, gen_pow_mul_gen]; exact ht) r1 r2 r3 r4 r5 r6 r7
      rwa [show (n - j + 1) * (fs loop) = (fs loop) + (n - (j + 1) + 1) * (fs loop) by
        rw [show n - j + 1 = (n - (j + 1) + 1) + 1 by omega, Nat.add_mul, Nat.one_mul, Nat.add_comm]]
  have := hstep (n - j0 - 1) j0 (by omega) le_rfl
  rw [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at this
  exact relAtIn_dmono this fun i hi => by obtain ⟨q, hq', _⟩ := hi; simp at hq'

/-! ## `opening_queries` -/

/-- What `opening_queries` reads from its caller's words: the weights `wts`, the queries' weights
`qwV`, their bit runs' pointers `dbpV` and bits, the parents' flags, the cap leaves. -/
def OqTopMem (rd : Reader) (I pd cd : ℕ) (rew qw qbp flags cap : E) (wts qwV dbpV : ℕ → E)
    (leaf : ℕ → List K) (pos : ℕ → ℕ) (sibs : ℕ → List Digest) (n : ℕ) : Prop :=
  (∀ jw < I, LoadHolds rd rew jw (wts jw)) ∧ (∀ j < n, LoadHolds rd qw j (qwV j)) ∧
    (∀ j < n, LoadHolds rd qbp j (dbpV j)) ∧
    (∀ j < n, ∀ l < pd + cd, LoadHolds rd (dbpV j) l (bitE ((pos j).testBit l))) ∧
    (∀ j < n, LoadHolds rd flags (2 ^ (cd - 1) + pos j / 2 ^ (pd + 1)) 1) ∧
    ∀ j < n, CapCell rd cap (2 ^ cd + pos j / 2 ^ pd)
      (climb (m := Id) blake2sBytes (hashWords (leaf j)) (pos j) (sibs j))

/-- Where `opening_queries` reads its caller's words: in `R`. -/
def OqTopReg (R : ℕ → Prop) (I pd cd : ℕ) (rew qw qbp flags cap : E) (dbpV : ℕ → E) (pos : ℕ → ℕ) (n : ℕ) :
    Prop :=
  (∀ jw < I, OqIn R (rew.limb 0 * Parameters.gpow jw)) ∧ (∀ j < n, OqIn R (qw.limb 0 * Parameters.gpow j)) ∧
    (∀ j < n, OqIn R (qbp.limb 0 * Parameters.gpow j)) ∧ (∀ j < n, ∀ l < pd + cd, OqIn R ((dbpV j).limb 0 * Parameters.gpow l)) ∧
    (∀ j < n, OqIn R (flags.limb 0 * Parameters.gpow (2 ^ (cd - 1) + pos j / 2 ^ (pd + 1)))) ∧
    ∀ j < n, OqIn R (cap.limb 0 * Parameters.gpow (2 * (2 ^ cd + pos j / 2 ^ pd))) ∧
      OqIn R (cap.limb 0 * Parameters.gpow (2 * (2 ^ cd + pos j / 2 ^ pd) + 1))

/-- The query sum chain: `qsc[j]`, the weighted rows' dot products of the queries below `j`. -/
def oqSum (base I : ℕ) (wts qwV : ℕ → E) (leaf : ℕ → List K) (j : ℕ) : E :=
  ∑ i ∈ Finset.range j, qwV i * ∑ jw ∈ Finset.range I, leafRowWord base (leaf i) jw * wts jw

theorem oq_limb_mul_gen_pow {p : E} (hp : IsInK p) (j off : ℕ) :
    (p * gen ^ j).limb 0 * Parameters.gpow off = p.limb 0 * Parameters.gpow (j + off) := by
  conv_lhs => rw [eq_ofK_limb hp, gen_pow_eq_ofK, ← ofK_mul, limb_ofK]
  simp [Parameters.gpow, pow_add, mul_assoc]

theorem oq_in_mono {R R' : ℕ → Prop} (h : ∀ i, R i → R' i) {A : K} (hA : OqIn R A) : OqIn R' A :=
  let ⟨i, hi, hR⟩ := hA; ⟨i, hi, h i hR⟩

/-- The body of `opening_queries` before its `ret`. -/
def oqPre (loop : String) : List Stmt := (oqBody loop).dropLast

/-- **`opening_queries`, placed**: at a shape whose loop helper is checked (`OqPlace`) and whose
frame run fits the frame (`hfit`), on every memory holding the caller's words (`OqTopMem`, within
`Lin`), it returns the query sum `oqSum … n`, its chain the one `HeapBuf` it allocates, by a tree of
its frame, the chain and the loop's `n + 1` frames. -/
theorem opening_queries_completeAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {base I blocks pd cd : ℕ}
    (hs : OqShape base I blocks pd cd) {name loop : String} {f lf : Fn} (hfind : coreProgram.find? name = some f)
    (hp : f.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]) (hb : f.body = oqBody loop)
    (hnl : coreProgram.loop name = false) (hlfind : coreProgram.find? loop = some lf)
    (hlp' : lf.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hlb : lf.body = oqLoopBody base I blocks pd cd loop) (hpl : OqPlace base I blocks pd cd loop)
    (hlp : coreProgram.loop loop = true) (hfit : cert loop (.n (oqP base I blocks)) + 4 * pd ≤ fs loop)
    {n : ℕ} (hn : n + 1 < ordG) {Lin : Main.Layout} {cap flags qw qbp rew : E} {leaf : ℕ → List K}
    (hleaf : ∀ j < n, (leaf j).length = oqR base I) {pos : ℕ → ℕ} (hq : ∀ j < n, pos j < 2 ^ (pd + cd))
    {sibs : ℕ → List Digest} (hsl : ∀ j < n, (sibs j).length = pd) {wts qwV dbpV : ℕ → E}
    (hlin : ∀ rd, LowDef k rd → MemL rd Lin → OqTopMem rd I pd cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n)
    (hreg : OqTopReg (RegionL Lin) I pd cd rew qw qbp flags cap dbpV pos n) :
    CompleteAtB fs cert k name Lin [cap, flags, qw, qbp, rew, gen ^ n]
      (Returns [oqSum base I wts qwV leaf n]) (fs name + (n + 1) + (n + 1) * fs loop) := by
  intro fp
  set b := fp + fs name
  set qscV : List E := (List.range (n + 1)).map (oqSum base I wts qwV leaf)
  set qsc : E := ofK (Parameters.gpow b)
  set Lq : Main.Layout := Lin ++ [(b, qscV)]
  set kid : Kid := ⟨loop, decide (1 + gen ^ n ≠ 0), [1, gen ^ n, rew, qsc, qw, qbp, flags, cap], Lq, Returns []⟩
  have hqscV : ∀ j ≤ n, qscV.getD j 0 = oqSum base I wts qwV leaf j := fun j hj => by
    simp [qscV, List.getD_eq_getElem?_getD, List.getElem?_range (show j < n + 1 by omega)]
  have hqlen : qscV.length = n + 1 := by simp [qscV]
  have hkid : ∀ κ ∈ [kid], κ.taken = true → CompleteAtB fs cert k κ.f κ.Lin κ.args κ.Out ((n + 1) * fs loop) := by
    intro κ hκ ht
    simp only [List.mem_singleton] at hκ
    subst hκ
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · simp [kid, h0] at ht
        exact absurd (e_add_self _) ht
      · exact h0
    have := oqLoop_completeAt fs cert k hs hlfind hlp' hlb hpl hlp hfit (by omega) (Lin := Lq) (rew := rew) (qsc := qsc)
      (qw := qw) (qbp := qbp) (flags := flags) (cap := cap) hleaf hq hsl ?_ 0 hn0
    · simpa [kid] using this
    intro rd hlow hmem j hj
    obtain ⟨hL, hQ⟩ := Main.memL_append.mp hmem
    obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hlin rd hlow hL
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hreg
    have hqs : ReadsAt rd qsc qscV := hQ _ (List.mem_singleton.mpr rfl)
    have hq0 : ∀ i ≤ n, LoadHolds rd qsc i (oqSum base I wts qwV leaf i) := fun i hi => by
      have := hqs i (by omega)
      rwa [← hqscV i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hqscK : IsInK qsc := (isInK_iff _).mpr ⟨_, rfl⟩
    have e1 : memAt rd (qsc * gen ^ j) 0 = oqSum base I wts qwV leaf j :=
      memAt_of_load ((loadHolds_gen_pow rd qsc j _).mpr (hq0 j (by omega)))
    have e2 : memAt rd (qw * gen ^ j) 0 = qwV j := memAt_of_load ((loadHolds_gen_pow rd qw j _).mpr (m2 j hj))
    have e3 : memAt rd (qbp * gen ^ j) 0 = dbpV j := memAt_of_load ((loadHolds_gen_pow rd qbp j _).mpr (m3 j hj))
    have ew : ∀ jw < I, memAt rd rew jw = wts jw := fun jw hjw => memAt_of_load (m1 jw hjw)
    have inL : ∀ i, RegionL Lin i → RegionL Lq i := fun i ⟨q, hq', h⟩ => ⟨q, List.mem_append_left _ hq', h⟩
    have inQ : ∀ t ≤ n, RegionL Lq (b + t) := fun t ht =>
      ⟨(b, qscV), List.mem_append_right _ (List.mem_singleton.mpr rfl), Nat.le_add_right b t,
        by show b + t < b + qscV.length; rw [hqlen]; omega⟩
    refine ⟨⟨fun jw hjw => by rw [ew jw hjw]; exact m1 jw hjw, by rw [e1, loadHolds_gen_pow]; exact hq0 j (by omega),
      by rw [e2, loadHolds_gen_pow]; exact m2 j hj, ?_, by rw [e3, loadHolds_gen_pow]; exact m3 j hj,
      by rw [e3]; exact m4 j hj, m5 j hj, m6 j hj⟩, fun jw hjw => oq_in_mono inL (r1 jw hjw), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e1, e2, Finset.sum_congr rfl fun jw hjw => by rw [ew jw (Finset.mem_range.mp hjw)],
        loadHolds_mul_gen_pow]
      have := hq0 (j + 1) (by omega)
      rw [oqSum, Finset.sum_range_succ] at this
      exact this
    · refine ⟨⟨b + j + 0, by rw [oq_limb_mul_gen_pow hqscK]; simp [qsc, limb_ofK, Parameters.gpow, pow_add],
          inQ j (by omega)⟩,
        ⟨b + j + 1, by rw [oq_limb_mul_gen_pow hqscK]; simp [qsc, limb_ofK, Parameters.gpow, pow_add, mul_assoc],
          inQ (j + 1) (by omega)⟩⟩
    · rw [oq_limb_mul_gen_pow (m2 j hj).1, Nat.add_zero]; exact oq_in_mono inL (r2 j hj)
    · rw [oq_limb_mul_gen_pow (m3 j hj).1, Nat.add_zero]; exact oq_in_mono inL (r3 j hj)
    · intro l hl; rw [e3]; exact oq_in_mono inL (r4 j hj l hl)
    · rw [oq_limb_mul_gen_pow (m5 j hj).1, Nat.add_zero]; exact oq_in_mono inL (r5 j hj)
    · refine ⟨?_, ?_⟩
      · rw [oq_limb_mul_gen_pow (m6 j hj).1.1, Nat.add_zero]; exact oq_in_mono inL (r6 j hj).1
      · rw [oq_limb_mul_gen_pow (m6 j hj).1.1, Nat.add_zero]; exact oq_in_mono inL (r6 j hj).2
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromIn_of_kidsB (fs := fs) (cert := cert) k (fun _ => (n + 1) * fs loop)
    [kid] hkid (b + (n + 1))
  have hNb' : N ≤ (n + 1) * fs loop := by
    refine le_trans hNb ?_
    simp only [kidsBound, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    split
    · exact le_rfl
    · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
  obtain ⟨o, rfl⟩ : ∃ o, outs = [o] := by
    match outs, ho with
    | [o], _ => exact ⟨o, rfl⟩
  have ho1 : kid.taken = true → o.1 = [] := fun ht => (ho.1 ht).1
  have hW1 : Within [(b, qscV)] b (n + 1) := fun e he => by
    simp only [List.mem_singleton] at he
    subst he
    simp only [hqlen]; omega
  refine ⟨fs name + (n + 1) + N, [(b, qscV)] ++ L, [oqSum base I wts qwV leaf n], [], ⟨rfl, rfl⟩, ?_,
    ?_, by omega, fun rd hlow hmem => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hW1.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append (List.pairwise_singleton _ _) hD hW1 hW le_rfl
  obtain ⟨h1, hLin⟩ := Main.memL_append.mp hmem
  obtain ⟨-, h2⟩ := Main.memL_append.mp h1
  obtain ⟨hQ1, hL⟩ := Main.memL_append.mp h2
  have hQ : ReadsAt rd qsc qscV := hQ1 _ (List.mem_singleton_self _)
  have hq0 : ∀ i ≤ n, LoadHolds rd qsc i (oqSum base I wts qwV leaf i) := fun i hi => by
    have := hQ i (by omega)
    rwa [← hqscV i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  set σ := Val.ofArgs [cap, flags, qw, qbp, rew, gen ^ n, gen, gen ^ (n + 1), qsc, 0, 1, 1 + gen ^ n, 1,
    qsc * gen ^ n, oqSum base I wts qwV leaf n] with hσ
  have hbody : f.body = oqPre loop ++ [.ret [.n 14]] := by rw [hb]; rfl
  have hstr : (oqPre loop).all Main.Stmt.straight = true := rfl
  have hholds : Stmt.HoldsList (fun _ _ _ => True) rd σ f.body False
      (fun rs => rs = [oqSum base I wts qwV leaf n]) := by
    rw [hb]
    simp only [oqBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, hσ, ofArgs_n,
      List.getD_cons_zero, List.getD_cons_succ, word_gen, true_and, and_true]
    refine ⟨by rw [pow_succ], ?_, hq0 0 (by omega), ?_, ?_, ?_, fun _ => trivial, ?_⟩
    · show (0 : E) = word 0 0 0
      rw [word_zero]
    · show (1 : E) = word 1 0 0
      rw [word_one]
    · show (1 : E) = word 1 0 0
      rw [word_one]
    · exact isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n)
    · have := hq0 n le_rfl
      rw [← loadHolds_gen_pow] at this
      exact this
  have hw : walk σ f.body = .ret ((oqPre loop).flatMap (Main.slEvs σ)) [.n 14] := by
    rw [hbody]; exact Main.walk_straight σ _ _ hstr
  have hev := oq_holds_events hfind hholds hw
  obtain ⟨had, hal, hadr, hcl⟩ := Main.straight_parts σ _ hstr
  have hlog : logG (σ (.n 7)) = n + 1 := by
    show logG (gen ^ (n + 1)) = n + 1
    rw [gen_pow_eq_ofK]; exact logG_spec (by omega)
  have hal' : allocs σ ((oqPre loop).flatMap (Main.slEvs σ)) = [n + 1] := by
    rw [hal]; show [logG (σ (.n 7))] = [n + 1]; rw [hlog]
  have hcalls : calls ((oqPre loop).flatMap (Main.slEvs σ)) =
      [⟨loop, [.n 12, .n 5, .n 4, .n 8, .n 2, .n 3, .n 1, .n 0], [], decide (σ (.n 11) ≠ 0)⟩] := by
    rw [hcl]; rfl
  have hown : ∀ t ≤ n, ownData cert fp (fp + fs name) name (allocs σ ((oqPre loop).flatMap (Main.slEvs σ)))
      ((oqPre loop).flatMap (Main.slEvs σ)) (b + t) := fun t ht => by
    rw [hal']
    exact Or.inl ⟨(n + 1, fp + fs name), by simp [bases], by simp [b], by simp [b]; omega⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion [kid] [o] i) (fp := fp) (N := N)
    hfind (Or.inl hnl) (by rw [hp]) hw rfl hev
    (by rw [had, hal']; rfl)
    (fun q hq' => by
      rw [hadr, show (oqPre loop).filterMap Main.Stmt.addrS = [] from rfl] at hq'
      simp at hq')
    ?_ ?_ (fun i hi => by obtain ⟨q, hq', _⟩ := hi; simp at hq')
  · rwa [hal', List.sum_singleton] at h
  · rw [hcalls, hal', List.sum_singleton]
    refine hK rd σ _ _ (fun _ => False) ?_ hlow hL ?_ ?_
    · refine ⟨rfl, rfl, fun ht => ⟨rfl, by rw [List.map_nil, ho1 ht]⟩, trivial⟩
    · simp only [Kid.lins, kid, Lq, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact Main.memL_append.mpr ⟨hLin, Main.memL_cons.mpr ⟨hQ, Main.memL_nil.mpr trivial⟩⟩
    · refine ⟨fun _ i hi => ?_, trivial⟩
      obtain ⟨q, hq', h1, h2⟩ := hi
      rcases List.mem_append.mp hq' with hq' | hq'
      · exact Or.inl (Or.inl ⟨q, hq', h1, h2⟩)
      · simp only [List.mem_singleton] at hq'
        subst hq'
        simp only [hqlen] at h1 h2
        have := hown (i - b) (by omega)
        rw [show b + (i - b) = i by omega, hal'] at this
        exact Or.inl (Or.inr this)
  · intro A hA
    rw [loadAddrs_straight σ _ hstr] at hA
    simp only [oqPre, oqBody, List.dropLast, List.filterMap_cons, Stmt.loadS, List.filterMap_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hA
    rcases hA with rfl | rfl
    · refine ⟨b + 0, ?_, Or.inl (hown 0 (by omega))⟩
      simp [hσ, ofArgs_n, qsc, limb_ofK, Parameters.gpow]
    · refine ⟨b + n, ?_, Or.inl (hown n le_rfl)⟩
      simp only [hσ, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero, qsc]
      rw [oq_limb_mul_gen_pow ((isInK_iff _).mpr ⟨_, rfl⟩)]
      simp [limb_ofK, Parameters.gpow, pow_add]

/-- **`opening_queries` at the shape `(base, I, depth, cd)`, placed**: the form its 50
specializations are proved in (`QueriesAtSpec`). -/
def OqCompleteAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (base I depth cd : ℕ) (name : String) : Prop :=
  ∀ (n : ℕ), n + 1 < ordG → ∀ (Lin : Main.Layout) (cap flags qw qbp rew : E) (leaf : ℕ → List K) (pos : ℕ → ℕ)
    (sibs : ℕ → List Digest) (wts qwV dbpV : ℕ → E),
    (∀ j < n, (leaf j).length = oqR base I) → (∀ j < n, pos j < 2 ^ depth) →
    (∀ j < n, (sibs j).length = depth - cd) →
    (∀ rd, LowDef k rd → MemL rd Lin →
      OqTopMem rd I (depth - cd) cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n) →
    OqTopReg (RegionL Lin) I (depth - cd) cd rew qw qbp flags cap dbpV pos n →
    CompleteAtD fs cert k name Lin [cap, flags, qw, qbp, rew, gen ^ n] (Returns [oqSum base I wts qwV leaf n])

/-- `OqCompleteAt` by trees of at most `B n` words. -/
def OqCompleteAtB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (base I depth cd : ℕ) (name : String)
    (B : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ), n + 1 < ordG → ∀ (Lin : Main.Layout) (cap flags qw qbp rew : E) (leaf : ℕ → List K) (pos : ℕ → ℕ)
    (sibs : ℕ → List Digest) (wts qwV dbpV : ℕ → E),
    (∀ j < n, (leaf j).length = oqR base I) → (∀ j < n, pos j < 2 ^ depth) →
    (∀ j < n, (sibs j).length = depth - cd) →
    (∀ rd, LowDef k rd → MemL rd Lin →
      OqTopMem rd I (depth - cd) cd rew qw qbp flags cap wts qwV dbpV leaf pos sibs n) →
    OqTopReg (RegionL Lin) I (depth - cd) cd rew qw qbp flags cap dbpV pos n →
    CompleteAtB fs cert k name Lin [cap, flags, qw, qbp, rew, gen ^ n] (Returns [oqSum base I wts qwV leaf n]) (B n)

theorem OqCompleteAtB.toD {fs : String → ℕ} {cert : String → V → ℕ} {k base I depth cd : ℕ} {name : String}
    {B : ℕ → ℕ} (h : OqCompleteAtB fs cert k base I depth cd name B) : OqCompleteAt fs cert k base I depth cd name :=
  fun n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV h1 h2 h3 h4 h5 =>
    (h n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV h1 h2 h3 h4 h5).toCompleteAtD

end
end LeanVM.Guest.B1
