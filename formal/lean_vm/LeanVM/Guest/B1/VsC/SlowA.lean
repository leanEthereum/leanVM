/-
  LeanVM.Guest.B1.VsC.SlowA

  The slow residual completes placed: `level_residual_sum` (its two `HeapBuf`s at its cursor),
  its loop and `residual_query_slow` (by their shapes), `level_residual_slow`.
-/

module

public import LeanVM.Guest.B1.VsC.SlowC
public import LeanVM.Guest.Complete.PureA
public import LeanVM.Guest.Complete.ComposeA

/-!
# The slow residual, placed

`SlowC.lean` proves the slow residual layout-free; here it is placed on the aligned allocator
(`CallAtA`), its pointer arguments `ptrAt` of their first cells.

* `ShapeR`: a subtree's block, its end from every cursor, its loads and heap hints in a region.
  Every valid tree of a straight leaf reading its arguments' arrays has its shape (`shapeR_leaf`,
  from `loadsR_hintsR_of_loadOk`); so has every valid tree of `level_residual_sum`'s loop from an
  iteration `j` (`lp_shape`: block `lpB`, end `lpE`, loading the sum's buffers, the positions and
  the challenges, `LpRegion`).
* `lsumA_complete'`: `level_residual_sum` at frame `fp` and cursor `c`, its buffers `acc`, `pw` at
  `c` and `c + Q + 1` (its own words), its loop by the transfer `callAtA_of_callCompletes0`.
* `lrsA_complete'`: `level_residual_slow`, its sum's frame from its cursor.
* `lrsA_complete`: every specialization.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## Shapes -/

/-- A subtree placed by its shape alone: block `B`, end `Ec c` from every cursor `c`, its loads and
heap hints in `R`. -/
def ShapeR (fs : String → ℕ) (al : String → Bool) (B : ℕ) (Ec : ℕ → ℕ) (R : ℕ → Prop) (t : Tree) : Prop :=
  t.block fs coreProgram.loop = B ∧ (∀ c, t.endA fs coreProgram.loop al c = Ec c) ∧
    t.LoadsR coreProgram R ∧ t.HintsR coreProgram R

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem ptrAt_mul_gen (a j : ℕ) : ptrAt a * gen ^ j = ptrAt (a + j) := by
  rw [gen_pow_eq_ofK, ptrAt, ptrAt, ← ofK_mul, gpow_add']

theorem ptrAt_inj {a b : ℕ} (h : ptrAt a = ptrAt b) : addressOfIndex a = addressOfIndex b :=
  ofK_injective h

/-- A cell of a run `[a, a + n)` of `R`. -/
theorem rng {R : ℕ → Prop} {a n x : ℕ} (h : ∀ i < n, R (a + i)) (hx : a ≤ x) (hy : x < a + n) : R x := by
  have := h (x - a) (by omega)
  rwa [Nat.add_sub_cancel' hx] at this

mutual
/-- Loads in `R` are loads in `R'` when each cell of `R` has the address of one of `R'`. -/
theorem loadsR_mono' {R R' : ℕ → Prop} (hR : ∀ i, R i → ∃ i', addressOfIndex i = addressOfIndex i' ∧ R' i') :
    ∀ t : Tree, t.LoadsR coreProgram R → t.LoadsR coreProgram R'
  | .node f σ bufs kids, h => by
    rw [Tree.LoadsR] at h ⊢
    refine ⟨fun A hA => ?_, loadsRKids_mono' hR kids h.2⟩
    obtain ⟨i, hi, hr⟩ := h.1 A hA
    obtain ⟨i', he, hr'⟩ := hR i hr
    exact ⟨i', hi.trans he, hr'⟩
  | .phantom .., _ => by simp only [Tree.LoadsR]

/-- `loadsR_mono'` for the callees. -/
theorem loadsRKids_mono' {R R' : ℕ → Prop} (hR : ∀ i, R i → ∃ i', addressOfIndex i = addressOfIndex i' ∧ R' i') :
    ∀ ks : List Tree, Tree.LoadsRKids coreProgram R ks → Tree.LoadsRKids coreProgram R' ks
  | [], _ => by simp only [Tree.LoadsRKids]
  | k :: ks, h => by
    rw [Tree.LoadsRKids] at h ⊢
    exact ⟨loadsR_mono' hR k h.1, loadsRKids_mono' hR ks h.2⟩
end

/-- **Every valid tree of a straight leaf reading its arguments' arrays has its shape**: block
`fs f`, ending at its cursor, loading from those arrays. -/
theorem shapeR_leaf {f : String} {fn : Fn} {ps : List (ℕ × ℕ)} {args rets : List E} {rd : Reader}
    {t : Tree} {R : ℕ → Prop} (hfind : coreProgram.find? f = some fn)
    (hparams : fn.params = (List.range args.length).map V.n)
    (hL : (atomsOf fn.body).all (loadOkB ps) = true) (hr : (retOf fn.body).isSome = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length) (hptr : ∀ q ∈ ps, ∃ b, args.getD q.1 0 = ptrAt b)
    (hR : ∀ i, argRegion args ps i → ∃ i', addressOfIndex i = addressOfIndex i' ∧ R i')
    (hlp : coreProgram.loop f = false) (hpure : Stmt.pureList [f] fn.body = true)
    (hn : t.name = f) (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) :
    ShapeR fs al (fs f) id R t := by
  have hS : coreProgram.PureIn [f] := by
    intro g hg fn' hf'
    rw [List.mem_singleton] at hg
    subst hg
    rw [hfind, Option.some.injEq] at hf'
    subst hf'
    exact hpure
  obtain ⟨vs0, hr'⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr'
  have hnc : ∀ fn' σ es vs, coreProgram.find? f = some fn' → walk σ fn'.body = .ret es vs → calls es = [] := by
    intro fn' σ es vs hfn hw
    rw [hfind] at hfn
    cases hfn
    have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs0] := by rw [hbody, ← eq_map_atomsOf hss]
    have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs0 := by rw [hb']; exact walk_atoms _ _ _
    rw [hw'] at hw
    cases hw
    exact calls_atoms _
  obtain ⟨hlo, hhi⟩ := loadsR_hintsR_of_loadOk R hfind hparams hL hr hargs hptr hn hv
  refine ⟨(block_endA_leaf (fs := fs) (al := al) hS (List.mem_singleton_self f) hlp hnc hn hv hb 0).1,
    fun c => ?_, loadsR_mono' hR t hlo, hhi⟩
  have := block_endA_leaf (fs := fs) (al := al) hS (List.mem_singleton_self f) hlp hnc hn hv hb c
  exact this.2

/-! ## The loop of `level_residual_sum`, by its shape -/

/-- `residual_query_slow`'s facts the loop's shape reads: its template reads its challenges'
arrays, places nothing, and is not a loop helper. -/
def RqFacts (rq : String) (pre yr : ℕ) : Prop :=
  ∃ fr : Fn, coreProgram.find? rq = some fr ∧ fr.params = osParams 3 ∧
    pureChecks 3 [(1, pre), (2, yr)] fr.body = true ∧ Stmt.pureList [rq] fr.body = true ∧
    coreProgram.loop rq = false

/-- The loop's block from iteration `j` of `Q`: its frames, then its last phantom. -/
def lpB (fs : String → ℕ) (self : String) (Q j : ℕ) : ℕ := (Q - j) * fs self + fs (tailKey self)

/-- An iteration's step of the cursor: its `residual_query_slow`'s frame. -/
def lpStep (fs : String → ℕ) (al : String → Bool) (rq : String) (x : ℕ) : ℕ := allocBase (al rq) x + fs rq

/-- The loop's end from iteration `j` of `Q`, from the cursor `c`. -/
def lpE (fs : String → ℕ) (al : String → Bool) (rq : String) (Q j c : ℕ) : ℕ := (lpStep fs al rq)^[Q - j] c

/-- An iterated step adding at most `d` adds at most `n·d`. -/
theorem iter_le_add {g : ℕ → ℕ} {d : ℕ} (hg : ∀ x, g x ≤ x + d) (n c : ℕ) : g^[n] c ≤ c + n * d := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have := ih (g c)
    have := hg c
    rw [Nat.succ_mul]
    omega

/-- The loop's end past its cursor, every frame at most `F`. -/
theorem lpE_le_frames {fs : String → ℕ} {al : String → Bool} {F : ℕ} (hF : ∀ f, fs f ≤ F) (rq : String) (Q j c : ℕ) :
    lpE fs al rq Q j c ≤ c + (Q - j) * (15 + F) :=
  iter_le_add (fun x => by have := allocBase_le (al rq) x; have := hF rq; unfold lpStep; omega) _ c

/-- What the loop reads: the sum's buffers at `ia` and `ipw`, the positions at `ip`, the challenges
at `ifc` and `itc`. -/
def LpRegion (Q pre yr ia ipw ip ifc itc : ℕ) (R : ℕ → Prop) : Prop :=
  (∀ i < Q + 1, R (ia + i)) ∧ (∀ i < Q + 1, R (ipw + i)) ∧ (∀ i < Q, R (ip + i)) ∧
    (∀ i < pre, R (ifc + i)) ∧ ∀ i < yr, R (itc + i)

/-- **One iteration's shape**, the next one's when `j + 1 < Q`. -/
theorem lp_shape_step {rq self : String} {f : Fn} (hfind : coreProgram.find? self = some f)
    (hparams : f.params = osParams 8) (hbody : f.body = lrsLoopBody rq self)
    (hls : coreProgram.loop self = true) {pre yr : ℕ} (hrq : RqFacts rq pre yr)
    {Q ia ipw ip ifc itc : ℕ} {lam : E} {R : ℕ → Prop} (hR : LpRegion Q pre yr ia ipw ip ifc itc R)
    (hQ : Q < 2 ^ 30) {j : ℕ} (hj : j < Q)
    (hnext : j + 1 < Q → ∀ rd t, t.name = self →
      t.Valid coreProgram rd (lpArgs (j + 1) Q (ptrAt ia) (ptrAt ipw) (ptrAt ip) (ptrAt ifc) (ptrAt itc) lam) [] →
      t.BufsOk coreProgram → ShapeR fs al (lpB fs self Q (j + 1)) (lpE fs al rq Q (j + 1)) R t) :
    ∀ rd t, t.name = self →
      t.Valid coreProgram rd (lpArgs j Q (ptrAt ia) (ptrAt ipw) (ptrAt ip) (ptrAt ifc) (ptrAt itc) lam) [] →
      t.BufsOk coreProgram → ShapeR fs al (lpB fs self Q j) (lpE fs al rq Q j) R t := by
  intro rd t hn hv hb
  obtain ⟨fr, hfr, hpr, hckr, hpurer, hlr⟩ := hrq
  cases t with
  | phantom _ _ => exact hv.elim
  | node g σ bufs kids =>
  simp only [Tree.name] at hn
  rw [hn] at hv hb ⊢
  obtain ⟨fn, hf, hp, es, vs, hw, -, hev, hk⟩ := hv
  have hff : fn = f := Option.some.inj (hf.symm.trans hfind)
  rw [hff] at hp hw
  have hw0 : walk σ f.body = .ret ((lpPre rq self).flatMap (slEvs σ)) [] := by
    rw [hbody, lpBody_eq]; exact walk_straight σ [] _ (lpPre_straight rq self)
  rw [hw0] at hw
  cases hw
  have hp' : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7)] =
      [gen ^ j, gen ^ Q, ptrAt ia, ptrAt ipw, ptrAt ip, ptrAt ifc, ptrAt itc, lam] := by
    rw [hparams] at hp; exact hp
  simp only [List.cons.injEq, and_true] at hp'
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hp'
  have hat : ∀ a, a ∈ lpA1 ∨ a ∈ lpA2 → a.Holds rd σ := fun a ha =>
    hev (.atom a) (by rw [lp_evs]; rcases ha with ha | ha <;> simp [ha])
  have e8 : σ (.n 8) = σ (.n 2) * σ (.n 0) := hat (.mul (.n 8) (.n 2) (.n 0)) (Or.inl (by simp [lpA1]))
  have e10 : σ (.n 10) = σ (.n 3) * σ (.n 0) := hat (.mul (.n 10) (.n 3) (.n 0)) (Or.inl (by simp [lpA1]))
  have e12 : σ (.n 12) = σ (.n 4) * σ (.n 0) := hat (.mul (.n 12) (.n 4) (.n 0)) (Or.inl (by simp [lpA1]))
  have e17 : σ (.n 17) = σ (.n 2) * σ (.n 0) := hat (.mul (.n 17) (.n 2) (.n 0)) (Or.inr (by simp [lpA2]))
  have e18 : σ (.n 18) = σ (.n 3) * σ (.n 0) := hat (.mul (.n 18) (.n 3) (.n 0)) (Or.inr (by simp [lpA2]))
  have e21 : σ (.n 21) = σ (.n 3) * σ (.n 0) := hat (.mul (.n 21) (.n 3) (.n 0)) (Or.inr (by simp [lpA2]))
  have e22 : σ (.n 22) = word 2 0 := hat (.const (.n 22) (word 2 0)) (Or.inr (by simp [lpA2]))
  have e23 : σ (.n 23) = σ (.n 0) * σ (.n 22) := hat (.mul (.n 23) (.n 0) (.n 22)) (Or.inr (by simp [lpA2]))
  have e24 : σ (.n 24) = σ (.n 23) + σ (.n 1) := hat (.add (.n 24) (.n 23) (.n 1)) (Or.inr (by simp [lpA2]))
  have e25 : σ (.n 25) = word 2 0 := hat (.const (.n 25) (word 2 0)) (Or.inr (by simp [lpA2]))
  have e26 : σ (.n 26) = σ (.n 0) * σ (.n 25) := hat (.mul (.n 26) (.n 0) (.n 25)) (Or.inr (by simp [lpA2]))
  have hsucc : σ (.n 0) * word 2 0 = gen ^ (j + 1) := by rw [h0, word_gen, pow_succ]
  have h24 : σ (.n 24) = 0 ↔ j + 1 = Q := by
    rw [e24, e23, e22, hsucc, h1]; exact gen_add_ne' (by omega) (by omega)
  have hbufs : allocs σ ((lpPre rq self).flatMap (slEvs σ)) = [] := by
    rw [(straight_parts σ _ (lpPre_straight rq self)).2.1]; rfl
  have hev0 : (Memory.Tree.node self σ bufs kids).events coreProgram = (lpPre rq self).flatMap (slEvs σ) :=
    Complete.events_node hfind hw0
  rw [Tree.BufsOk, hev0, hbufs] at hb
  obtain ⟨rfl, hbk⟩ := hb
  rw [lp_calls] at hk
  rcases kids with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, ks⟩⟩⟩ <;> try (simp [Tree.KidsValid] at hk; done)
  rw [Tree.KidsValid, Tree.KidsValid, Tree.KidsValid] at hk
  obtain ⟨hn1, hv1, hn2, hv2, -⟩ := hk
  simp only [↓reduceIte] at hv1
  rw [Tree.BufsOkKids, Tree.BufsOkKids] at hbk
  obtain ⟨hb1, hb2, -⟩ := hbk
  -- The query's tree.
  have hs1 : ShapeR fs al (fs rq) id R t1 := by
    refine shapeR_leaf (ps := [(1, pre), (2, yr)]) hfr (by rw [hpr]; rfl) ?_ ?_ ?_ ?_ ?_ hlr hpurer hn1 hv1 hb1
    · simp only [pureChecks, Bool.and_eq_true] at hckr; exact hckr.1.2
    · simp only [pureChecks, Bool.and_eq_true] at hckr; exact hckr.2
    · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp
    · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨ifc, by simp [h5]⟩
      · exact ⟨itc, by simp [h6]⟩
    · rintro i ⟨q, hq, b, hqb, hbi, hib⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · have hqb' : ptrAt ifc = ptrAt b := by rw [← hqb]; simp [h5]
        have hab := ptrAt_inj hqb'
        have hib' : i < b + pre := hib
        refine ⟨ifc + (i - b), ?_, hR.2.2.2.1 (i - b) (by omega)⟩
        calc addressOfIndex i = addressOfIndex (b + (i - b)) := by rw [Nat.add_sub_cancel' hbi]
          _ = addressOfIndex b * addressOfIndex (i - b) := (gpow_add' _ _).symm
          _ = addressOfIndex ifc * addressOfIndex (i - b) := by rw [← hab]
          _ = addressOfIndex (ifc + (i - b)) := gpow_add' _ _
      · have hqb' : ptrAt itc = ptrAt b := by rw [← hqb]; simp [h6]
        have hab := ptrAt_inj hqb'
        have hib' : i < b + yr := hib
        refine ⟨itc + (i - b), ?_, hR.2.2.2.2 (i - b) (by omega)⟩
        calc addressOfIndex i = addressOfIndex (b + (i - b)) := by rw [Nat.add_sub_cancel' hbi]
          _ = addressOfIndex b * addressOfIndex (i - b) := (gpow_add' _ _).symm
          _ = addressOfIndex itc * addressOfIndex (i - b) := by rw [← hab]
          _ = addressOfIndex (itc + (i - b)) := gpow_add' _ _
  obtain ⟨hB1, hE1, hL1, hH1⟩ := hs1
  -- The tail's tree.
  have hs2 : ShapeR fs al (lpB fs self Q (j + 1)) (lpE fs al rq Q (j + 1)) R t2 := by
    by_cases hl : j + 1 = Q
    · have hd : decide (σ (.n 24) ≠ 0) = false := by simp [h24.mpr hl]
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hv2
      obtain ⟨⟨f', σ', rfl⟩, -⟩ := hv2
      simp only [Tree.name] at hn2
      have h0' : Q - (j + 1) = 0 := by omega
      refine ⟨?_, fun c => ?_, by simp only [Tree.LoadsR], by simp only [Tree.HintsR]⟩
      · rw [Tree.block, hn2, lpB, h0', zero_mul, zero_add]
      · rw [endA_phantom, lpE, h0']; rfl
    · have hd : decide (σ (.n 24) ≠ 0) = true := by simp [h24, hl]
      simp only [hd, ↓reduceIte] at hv2
      have ha : lpSelfArgs.map σ = lpArgs (j + 1) Q (ptrAt ia) (ptrAt ipw) (ptrAt ip) (ptrAt ifc) (ptrAt itc) lam := by
        simp only [lpSelfArgs, List.map_cons, List.map_nil, lpArgs, e26, e25, hsucc, h1, h2, h3, h4, h5, h6, h7]
      rw [ha] at hv2
      exact hnext (by omega) rd t2 hn2 hv2 hb2
  obtain ⟨hB2, hE2, hL2, hH2⟩ := hs2
  refine ⟨?_, fun c => ?_, ?_, ?_⟩
  · -- the block
    rw [Tree.block, hls]
    simp only [↓reduceIte, Tree.blockLast]
    rw [hB2]
    unfold lpB
    have : Q - j = (Q - (j + 1)) + 1 := by omega
    rw [this]
    generalize Q - (j + 1) = n
    ring
  · -- the end
    rw [endA_node, hls]
    simp only [↓reduceIte, List.sum_nil, add_zero]
    rw [endL_cons, endL_one, hn1, hB1, hE1, hE2]
    unfold lpE
    have : Q - j = (Q - (j + 1)) + 1 := by omega
    rw [this, Function.iterate_succ_apply]
    rfl
  · -- the loads
    rw [Tree.LoadsR, hev0]
    refine ⟨fun A hA => ?_, by rw [Tree.LoadsRKids, Tree.LoadsRKids, Tree.LoadsRKids]; exact ⟨hL1, hL2, trivial⟩⟩
    simp only [loadAddrs, List.mem_filterMap] at hA
    obtain ⟨e, he, hA⟩ := hA
    rw [lp_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ((⟨b, hb, rfl⟩ | rfl) | ⟨b, hb, rfl⟩) | rfl | rfl
    · simp only [lpA1, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Ev.loadAddr?, Option.some.injEq, reduceCtorEq] at hA <;>
        (subst hA
         simp only [e8, e10, e12, h0, h2, h3, h4, ptrAt_mul_gen, Main.addr_ofK]
         refine ⟨_, rfl, ?_⟩
         first
           | exact rng hR.1 (by omega) (by omega)
           | exact rng hR.2.1 (by omega) (by omega)
           | exact rng hR.2.2.1 (by omega) (by omega))
    · simp [Ev.loadAddr?] at hA
    · simp only [lpA2, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Ev.loadAddr?, Option.some.injEq, reduceCtorEq] at hA <;>
        (subst hA
         simp only [e17, e18, e21, h0, h2, h3, ptrAt_mul_gen, Main.addr_ofK]
         refine ⟨_, rfl, ?_⟩
         first
           | exact rng hR.1 (by omega) (by omega)
           | exact rng hR.2.1 (by omega) (by omega))
    · simp [Ev.loadAddr?] at hA
    · split at hA <;> simp [Ev.loadAddr?] at hA
  · -- the heap hints
    rw [Tree.HintsR, hev0]
    refine ⟨fun A hA => ?_, by rw [Tree.HintsRKids, Tree.HintsRKids, Tree.HintsRKids]; exact ⟨hH1, hH2, trivial⟩⟩
    rw [heapHintAddrs] at hA
    obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
    rw [lp_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ((⟨b, hb, rfl⟩ | rfl) | ⟨b, hb, rfl⟩) | rfl | rfl
    · simp only [lpA1, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Ev.hintAddrs] at hA
    · simp [Ev.hintAddrs] at hA
    · simp only [lpA2, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Ev.hintAddrs] at hA
    · simp [Ev.hintAddrs] at hA
    · split at hA <;> simp [Ev.hintAddrs] at hA

/-- **Every valid tree of the loop from iteration `j < Q` has its shape.** -/
theorem lp_shape {rq self : String} {f : Fn} (hfind : coreProgram.find? self = some f)
    (hparams : f.params = osParams 8) (hbody : f.body = lrsLoopBody rq self)
    (hls : coreProgram.loop self = true) {pre yr : ℕ} (hrq : RqFacts rq pre yr)
    {Q ia ipw ip ifc itc : ℕ} {lam : E} {R : ℕ → Prop} (hR : LpRegion Q pre yr ia ipw ip ifc itc R)
    (hQ : Q < 2 ^ 30) :
    ∀ m j, Q = j + m + 1 → ∀ rd t, t.name = self →
      t.Valid coreProgram rd (lpArgs j Q (ptrAt ia) (ptrAt ipw) (ptrAt ip) (ptrAt ifc) (ptrAt itc) lam) [] →
      t.BufsOk coreProgram → ShapeR fs al (lpB fs self Q j) (lpE fs al rq Q j) R t := by
  intro m
  induction m with
  | zero =>
    intro j hj
    exact lp_shape_step hfind hparams hbody hls hrq hR hQ (by omega) (fun h => absurd h (by omega))
  | succ m ih =>
    intro j hj
    exact lp_shape_step hfind hparams hbody hls hrq hR hQ (by omega) (fun _ => ih (j + 1) (by omega))

/-! ## `level_residual_sum`, placed -/

theorem le_lpE (rq : String) (Q j c : ℕ) : c ≤ lpE fs al rq Q j c := by
  unfold lpE
  generalize Q - j = n
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact le_trans (le_trans (le_allocBase _ c) (Nat.le_add_right _ _)) (ih _)

/-- A cell of an instance's `HeapBuf` of size `s` at `b`. -/
theorem ownData_buf {fp c : ℕ} {f : String} {bufs : List ℕ} {es : List Ev} {i s b : ℕ}
    (hm : (s, b) ∈ bufs.zip (bases c bufs)) (h1 : b ≤ i) (h2 : i < b + s) : ownData cert fp c f bufs es i :=
  Or.inl ⟨(s, b), hm, h1, h2⟩

variable (fs al cert) in
/-- What `level_residual_sum__L{Q}_L{pre}_L{yr}_L{vo}`'s placed completeness gives: at frame `fp`
and cursor `c`, on the positions at `ptrAt ip` and the challenges at `ptrAt ifc`, `ptrAt itc`
(cells of the region `R` its caller hands it), it returns `λ²·Σ_{k<Q} λ^k·w_k`, its buffers `acc`,
`pw` its own words at `c`. -/
def LsumA (kd : ℕ) (name : String) (Q pre yr vo : ℕ) : Prop :=
  ∀ (ip ifc itc : ℕ) (lam : E) (pos cs : ℕ → E) (R : ℕ → Prop),
    (∀ i < Q, R (ip + i)) → (∀ i < pre, R (ifc + i)) → (∀ i < yr, R (itc + i)) →
    ∀ fp c, fp + fs name ≤ c → ∃ e, CallAtA fs al cert kd name [ptrAt ip, ptrAt ifc, ptrAt itc, lam]
      [lrsAcc (pre + yr) vo pos cs lam Q] R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd (ptrAt ip) (posL Q pos) ∧ CsAt pre yr (ptrAt ifc) (ptrAt itc) cs rd) PostQuiet
      (fs name) fp c e

variable (fs al cert) in
/-- **`LsumA` with its end bounded**: every frame at most `F`, within `(Q + 2)·(2F + 32)`. -/
def LsumAE (kd : ℕ) (name : String) (Q pre yr vo : ℕ) : Prop :=
  ∀ (ip ifc itc : ℕ) (lam : E) (pos cs : ℕ → E) (R : ℕ → Prop),
    (∀ i < Q, R (ip + i)) → (∀ i < pre, R (ifc + i)) → (∀ i < yr, R (itc + i)) →
    ∀ fp c, fp + fs name ≤ c → ∃ e, (∀ F, (∀ f, fs f ≤ F) → e ≤ c + (Q + 2) * (2 * F + 32)) ∧
      CallAtA fs al cert kd name [ptrAt ip, ptrAt ifc, ptrAt itc, lam]
      [lrsAcc (pre + yr) vo pos cs lam Q] R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd (ptrAt ip) (posL Q pos) ∧ CsAt pre yr (ptrAt ifc) (ptrAt itc) cs rd) PostQuiet
      (fs name) fp c e

/-- `level_residual_sum`'s end, from its pieces. -/
theorem lsum_end_le {c Q F L T x : ℕ} (hL : L ≤ F) (hT : T ≤ F)
    (hx : x ≤ c + (Q + 1 + (Q + 1)) + 15 + Q * L + T + Q * (15 + F)) : x ≤ c + (Q + 2) * (2 * F + 32) := by
  have h1 : Q * L ≤ Q * F := Nat.mul_le_mul_left Q hL
  have h2 : Q * (15 + F) = 15 * Q + Q * F := by ring
  have h3 : (Q + 2) * (2 * F + 32) = 2 * (Q * F) + 32 * Q + 4 * F + 64 := by ring
  omega

/-- **`level_residual_sum` completes placed, its end bounded.** -/
theorem lsumAE_complete' {kd Q : ℕ} {name rq loop : String} {fo fl : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 4)
    (hbo : fo.body = lsumBody Q loop) (hlo : coreProgram.loop name = false)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = osParams 8)
    (hbl : fl.body = lrsLoopBody rq loop) (hll : coreProgram.loop loop = true)
    (hS : coreProgram.PureIn [loop, rq]) {pre yr vo : ℕ} (hrqF : RqFacts rq pre yr)
    (hrq : RqsComplete kd rq pre yr vo) (hQ1 : 1 ≤ Q) (hQ : Q < 2 ^ 30) :
    LsumAE fs al cert kd name Q pre yr vo := by
  intro ip ifc itc lam pos cs R hRp hRf hRt fp c hfc
  have hgQ : gw Q = gen ^ Q := gw_eq (by unfold u128Bound; omega)
  have hgQ1 : gw (Q + 1) = gen ^ (Q + 1) := gw_eq (by unfold u128Bound; omega)
  obtain ⟨r, hr⟩ : ∃ r : E, r = lrsAcc (pre + yr) vo pos cs lam Q := ⟨_, rfl⟩
  let σ : Val := lsσ Q (ptrAt ip) (ptrAt ifc) (ptrAt itc) lam (ptrAt c) (ptrAt (c + (Q + 1))) r
  have s5 : σ (.n 5) = ptrAt c := rfl
  have s7 : σ (.n 7) = ptrAt (c + (Q + 1)) := rfl
  set es := (lsPre Q loop).flatMap (slEvs σ) with hes
  have hw : walk σ fo.body = .ret es [.n 15] := by
    rw [hbo, lsBody_eq]; exact walk_straight σ _ _ (lsPre_straight Q loop)
  have hal : allocs σ es = [Q + 1, Q + 1] := by
    rw [hes, (straight_parts σ _ (lsPre_straight Q loop)).2.1]
    show [logG (gw (Q + 1)), logG (gw (Q + 1))] = _
    rw [hgQ1, gen_pow_eq_ofK, logG_spec (by omega)]
  have hsum : (allocs σ es).sum = Q + 1 + (Q + 1) := by rw [hal]; simp
  have h12 : σ (.n 12) ≠ 0 := by
    show word 1 0 + gw Q ≠ 0
    rw [word_one, hgQ]; exact Whir.one_add_gen_pow_ne hQ1 hQ
  have h12d : decide (σ (.n 12) ≠ 0) = true := by simp [h12]
  let Wo : Words := [(c, accL Q (pre + yr) vo pos cs lam), (c + (Q + 1), pwL Q lam)]
  have hRd : ∀ rd, HoldsWords rd Wo → ReadsAt rd (ptrAt c) (accL Q (pre + yr) vo pos cs lam) ∧
      ReadsAt rd (ptrAt (c + (Q + 1))) (pwL Q lam) := fun rd h =>
    ⟨h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hown : ∀ i, (c ≤ i ∧ i < c + (Q + 1)) ∨ (c + (Q + 1) ≤ i ∧ i < c + (Q + 1) + (Q + 1)) →
      ownData cert fp c name (allocs σ es) es i := by
    intro i hi
    rw [hal]
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ownData_buf (s := Q + 1) (b := c) (by simp [bases]) h1 h2
    · exact ownData_buf (s := Q + 1) (b := c + (Q + 1)) (by simp [bases]) h1 h2
  let Rc : ℕ → Prop := fun i =>
    ((c ≤ i ∧ i < c + (Q + 1)) ∨ (c + (Q + 1) ≤ i ∧ i < c + (Q + 1) + (Q + 1))) ∨ R i
  have hLp : LpRegion Q pre yr c (c + (Q + 1)) ip ifc itc Rc :=
    ⟨fun i hi => Or.inl (Or.inl ⟨by omega, by omega⟩), fun i hi => Or.inl (Or.inr ⟨by omega, by omega⟩),
      fun i hi => Or.inr (hRp i hi), fun i hi => Or.inr (hRf i hi), fun i hi => Or.inr (hRt i hi)⟩
  set cur := allocBase (al loop) (c + (allocs σ es).sum) with hcur
  have hargs : lsLoopArgs.map σ =
      lpArgs 0 Q (ptrAt c) (ptrAt (c + (Q + 1))) (ptrAt ip) (ptrAt ifc) (ptrAt itc) lam := by
    show [word 1 0, gw Q, ptrAt c, ptrAt (c + (Q + 1)), ptrAt ip, ptrAt ifc, ptrAt itc, lam] = _
    rw [word_one, hgQ, lpArgs, pow_zero]
  have hloop : CallAtA fs al cert kd loop (lsLoopArgs.map σ) [] Rc (fun _ => False) (fun _ => True)
      (fun rd => (ReadsAt rd (ptrAt ip) (posL Q pos) ∧ CsAt pre yr (ptrAt ifc) (ptrAt itc) cs rd) ∧
        HoldsWords rd Wo) PostQuiet (lpB fs loop Q 0) cur (cur + lpB fs loop Q 0)
      (lpE fs al rq Q 0 (cur + lpB fs loop Q 0)) := by
    rw [hargs]
    refine callAtA_of_callCompletes0 hS (by simp) (le_lpE rq Q 0 _)
      ((lp_loop hfl hpl hbl hrq hQ (ptrAt c) (ptrAt (c + (Q + 1))) (ptrAt ip) (ptrAt ifc) (ptrAt itc) lam pos cs
        (Q - 1) 0 (by omega)).mono (fun rd h => ?_) fun _ _ _ h => h) fun rd t _ _ hn hv hb _ => ?_
    · obtain ⟨ha, hp⟩ := hRd rd h.2
      exact ⟨ha, hp, h.1.1, h.1.2⟩
    · have := lp_shape (fs := fs) (al := al) hfl hpl hbl hll hrqF hLp hQ (Q - 1) 0 (by omega) rd t hn hv hb
      exact ⟨this.1, this.2.1 _, this.2.2.1, this.2.2.2⟩
  refine ⟨lpE fs al rq Q 0 (cur + lpB fs loop Q 0), fun F hF => lsum_end_le (hF loop) (hF (tailKey loop)) (by
    have := lpE_le_frames (al := al) hF rq Q 0 (cur + lpB fs loop Q 0)
    have hc : cur ≤ c + (allocs σ es).sum + 15 := by rw [hcur]; exact allocBase_le _ _
    rw [hsum] at hc
    unfold lpB at this ⊢
    rw [Nat.sub_zero] at this ⊢
    omega), callAtA_node hlo hfc ⟨σ, fo, es, [.n 15], Wo, (calls es).map fun _ => PostQuiet,
    fun rd => HoldsWords rd Wo, fun _ => False, hfo, by rw [hpo]; rfl, hw, by show [r] = _; rw [hr],
    ?_, ?_, ?_, ?_, fun _ h => h.elim, ?_, fun _ _ => trivial, ?_, ?_⟩⟩
  · -- placed
    rw [hal]
    refine ⟨?_, fun q hq => ?_⟩
    · rw [hes, (straight_parts σ _ (lsPre_straight Q loop)).1]; rfl
    · rw [hes, (straight_parts σ _ (lsPre_straight Q loop)).2.2.1] at hq
      exact absurd hq (by simp [lsPre, lsA1, Stmt.addrS])
  · -- own words
    rw [hsum]
    refine ⟨fun q hq => Or.inr ?_, ?_⟩
    · simp only [Wo, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simp [accL]
      · simp only [pwL, List.length_map, List.length_range]; omega
    · simp [Wo, accL, pwL]
  · -- loads
    intro A hA
    rw [hes] at hA
    simp only [loadAddrs, List.mem_filterMap] at hA
    obtain ⟨e, he, hA⟩ := hA
    rw [ls_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨b, hb, rfl⟩ | rfl | rfl | rfl
    · simp only [lsA1, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Ev.loadAddr?, Option.some.injEq, reduceCtorEq] at hA <;>
        (subst hA
         simp only [s5, s7, Main.addr_ofK]
         exact ⟨_, rfl, Or.inl (hown _ (by omega))⟩)
    · simp [Ev.loadAddr?] at hA
    · split at hA <;> simp [Ev.loadAddr?] at hA
    · simp only [Ev.loadAddr?, Option.some.injEq] at hA
      subst hA
      simp only [s5, Main.addr_ofK]
      exact ⟨_, rfl, Or.inl (hown _ (by omega))⟩
  · -- heap hints
    intro A hA
    rw [hes, heapHintAddrs] at hA
    obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
    rw [ls_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨b, hb, rfl⟩ | rfl | rfl | rfl
    · simp only [lsA1, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Ev.hintAddrs, hintDest?] at hA
    · simp [Ev.hintAddrs] at hA
    · split at hA <;> simp [Ev.hintAddrs] at hA
    · simp [Ev.hintAddrs] at hA
  · -- the loop
    rw [hes, ls_calls, KidsAtF]
    simp only [h12d, ↓reduceIte]
    refine ⟨lpB fs loop Q 0, lpE fs al rq Q 0 (cur + lpB fs loop Q 0), Rc, fun _ => False, fun _ => True,
      fun i hi => ?_, ?_, ?_⟩
    · rcases hi with hi | hi
      · exact Or.inl (Or.inr (hown i hi))
      · exact Or.inl (Or.inl hi)
    · rw [← hes]; exact hloop
    · rw [KidsAtF]; exact ⟨rfl, fun rd h => h.1, fun i h => h.elim⟩
  · -- the events
    intro rd _ hP hW e he
    obtain ⟨ha, hp⟩ := hRd rd hW
    rw [hes, ls_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨b, hb, rfl⟩ | rfl | rfl | rfl
    · simp only [lsA1, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        try first | exact rfl | trivial
      · show LoadHolds rd (ptrAt c) 0 (word 0 0)
        have := ha 0 (by simp [accL])
        simpa [accL, lrsAcc, word_zero] using this
      · show LoadHolds rd (ptrAt (c + (Q + 1))) 0 (lam * lam)
        have := hp 0 (by simp [pwL])
        simpa [pwL, pow_two] using this
    · show IsInK (word 1 0 + gw Q)
      rw [word_one, hgQ]; exact isInK_add one_isInK (gen_pow_isInK _)
    · split <;> trivial
    · show LoadHolds rd (ptrAt c) Q r
      have := ha Q (by simp [accL])
      simpa [accL, hr] using this
  · -- the post
    intro rd ts _ _ _ hv hq
    refine postQuiet_node hfo hw (fun c hc => ?_) (fun e he => ?_) hv hq _
    · rw [hes, ls_evs] at hc
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ⟨c', hc', hcc⟩ | hc | hc | hc
      · cases hcc; simp only [lsA1, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · cases hc
      · split at hc <;> cases hc
      · cases hc; rfl
    · rw [hes, ls_evs] at he
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with ⟨c', hc', rfl⟩ | rfl | rfl | rfl
      · simp only [lsA1, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
      · trivial
      · split <;> trivial
      · trivial

/-! ## `level_residual_slow`, placed -/

variable (fs al cert) in
/-- What `level_residual_slow__L{Q}_L{pre}_L{yr}_L{vo}`'s placed completeness gives: at a flag `z`
in `K`, it returns `slowVal`, its sum's frame from its cursor. -/
def LrsA (kd : ℕ) (name : String) (Q pre yr vo : ℕ) : Prop :=
  ∀ (ip ifc itc : ℕ) (lam z : E) (pos cs : ℕ → E) (R : ℕ → Prop), IsInK z →
    (∀ i < Q, R (ip + i)) → (∀ i < pre, R (ifc + i)) → (∀ i < yr, R (itc + i)) →
    ∀ fp c, fp + fs name ≤ c → ∃ e, CallAtA fs al cert kd name [ptrAt ip, ptrAt ifc, ptrAt itc, lam, z]
      [slowVal Q (pre + yr) vo pos cs lam z] R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd (ptrAt ip) (posL Q pos) ∧ CsAt pre yr (ptrAt ifc) (ptrAt itc) cs rd) PostQuiet
      (fs name) fp c e

variable (fs al cert) in
/-- **`LrsA` with its end bounded**: every frame at most `F`, within `(Q + 3)·(2F + 32)`. -/
def LrsAE (kd : ℕ) (name : String) (Q pre yr vo : ℕ) : Prop :=
  ∀ (ip ifc itc : ℕ) (lam z : E) (pos cs : ℕ → E) (R : ℕ → Prop), IsInK z →
    (∀ i < Q, R (ip + i)) → (∀ i < pre, R (ifc + i)) → (∀ i < yr, R (itc + i)) →
    ∀ fp c, fp + fs name ≤ c → ∃ e, (∀ F, (∀ f, fs f ≤ F) → e ≤ c + (Q + 3) * (2 * F + 32)) ∧
      CallAtA fs al cert kd name [ptrAt ip, ptrAt ifc, ptrAt itc, lam, z]
      [slowVal Q (pre + yr) vo pos cs lam z] R (fun _ => False) (fun _ => True)
      (fun rd => ReadsAt rd (ptrAt ip) (posL Q pos) ∧ CsAt pre yr (ptrAt ifc) (ptrAt itc) cs rd) PostQuiet
      (fs name) fp c e

/-- **`level_residual_slow` completes placed, its end bounded.** -/
theorem lrsAE_complete' {kd : ℕ} {name sum : String} {fo : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 5)
    (hbo : fo.body = lrsBody sum) (hlo : coreProgram.loop name = false) {Q pre yr vo : ℕ}
    (hsum : LsumAE fs al cert kd sum Q pre yr vo) : LrsAE fs al cert kd name Q pre yr vo := by
  intro ip ifc itc lam z pos cs R hz hRp hRf hRt fp c hfc
  obtain ⟨r, hr⟩ : ∃ r : E, r = slowVal Q (pre + yr) vo pos cs lam z := ⟨_, rfl⟩
  let σ : Val := fun v => [ptrAt ip, ptrAt ifc, ptrAt itc, lam, z, r, r].getD v.idx 0
  by_cases h0 : z = 0
  · have hr0 : r = 0 := by simp [hr, slowVal, h0]
    have hw : walk σ fo.body = .ret [.inK (.n 4), .atom (.copy (.n 5) (.n 4)), .atom (.copy (.n 6) (.n 5))]
        [.n 6] := by
      have : σ (.n 4) = 0 := h0
      simp [hbo, lrsBody, walk, walk1, Out.seq, Out.pre, this]
    refine ⟨c, fun _ _ => Nat.le_add_right _ _, callAtA_node hlo hfc ⟨σ, fo, _, _, [], [], fun _ => True, fun _ => False, hfo,
      by rw [hpo]; rfl, hw, by show [r] = _; rw [hr], ⟨rfl, fun q hq => by simp [addrs, Ev.addr?] at hq⟩,
      ⟨by simp, List.Pairwise.nil⟩, fun A hA => by simp [loadAddrs, Ev.loadAddr?] at hA,
      fun A hA => by simp [heapHintAddrs, Ev.hintAddrs] at hA, fun _ h => h.elim, ?_, fun _ _ => trivial,
      fun rd _ _ _ e he => ?_, fun rd ts _ _ _ hv hq => ?_⟩⟩
    · have hc0 : calls [Ev.inK (.n 4), .atom (.copy (.n 5) (.n 4)), .atom (.copy (.n 6) (.n 5))] = [] := rfl
      rw [hc0, KidsAtF]; exact ⟨rfl, fun _ _ => trivial, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hz
      · show r = z; rw [hr0, h0]
      · show r = r; rfl
    · have hc0 : calls [Ev.inK (.n 4), .atom (.copy (.n 5) (.n 4)), .atom (.copy (.n 6) (.n 5))] = [] := rfl
      refine postQuiet_node hfo hw (fun c hc => ?_) (fun e he => ?_) hv
        (by rw [hc0]; cases ts <;> simp [KidsPost]) _
      · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or] at hc
        rcases hc with h | h <;> cases h <;> rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> trivial
  · have hr' : r = lrsAcc (pre + yr) vo pos cs lam Q := by
      simp only [hr, slowVal, h0, ↓reduceIte, lrsAcc]
      rfl
    have hw : walk σ fo.body = .ret [.inK (.n 4), .call sum [.n 0, .n 1, .n 2, .n 3] [.n 5],
        .atom (.copy (.n 6) (.n 5))] [.n 6] := by
      have : σ (.n 4) ≠ 0 := h0
      simp [hbo, lrsBody, walk, walk1, Out.seq, Out.pre, this]
    have hc1 : calls [Ev.inK (.n 4), .call sum [.n 0, .n 1, .n 2, .n 3] [.n 5], .atom (.copy (.n 6) (.n 5))] =
        [⟨sum, [.n 0, .n 1, .n 2, .n 3], [.n 5], true⟩] := rfl
    have hal : allocs σ [Ev.inK (.n 4), .call sum [.n 0, .n 1, .n 2, .n 3] [.n 5],
        .atom (.copy (.n 6) (.n 5))] = [] := rfl
    set cur := allocBase (al sum) (c + 0) with hcur
    obtain ⟨ec, hecB, hca⟩ := hsum ip ifc itc lam pos cs R hRp hRf hRt cur (cur + fs sum) le_rfl
    rw [← hr'] at hca
    refine ⟨ec, fun F hF => by
      have h1 := hecB F hF
      have h2 : cur ≤ c + 0 + 15 := by rw [hcur]; exact allocBase_le _ _
      have h3 := hF sum
      have h4 : (Q + 3) * (2 * F + 32) = (Q + 2) * (2 * F + 32) + 2 * F + 32 := by ring
      omega, callAtA_node hlo hfc ⟨σ, fo, _, _, [], [PostQuiet], fun _ => True, fun _ => False, hfo,
      by rw [hpo]; rfl, hw, by show [r] = _; rw [hr], ⟨rfl, fun q hq => by simp [addrs, Ev.addr?] at hq⟩,
      ⟨by simp, List.Pairwise.nil⟩, fun A hA => by simp [loadAddrs, Ev.loadAddr?] at hA,
      fun A hA => by simp [heapHintAddrs, Ev.hintAddrs] at hA, fun _ h => h.elim, ?_, fun _ _ => trivial,
      fun rd _ _ _ e he => ?_, fun rd ts _ _ _ hv hq => ?_⟩⟩
    · rw [hc1, KidsAtF]
      simp only [↓reduceIte]
      refine ⟨fs sum, ec, R, fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi), ?_, ?_⟩
      · rw [hal]
        exact hca.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h.1) fun _ _ _ h => h
      · rw [KidsAtF]; exact ⟨rfl, fun _ _ => trivial, fun _ h => h.elim⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hz
      · trivial
      · show r = r; rfl
    · refine postQuiet_node hfo hw (fun c hc => ?_) (fun e he => ?_) hv ?_ _
      · simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or] at hc
        cases hc; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> trivial
      · rw [hc1] at hq ⊢
        exact hq

/-! ## Every specialization -/

/-- `residual_query_slow`'s template places nothing and calls nothing, within any set naming its
caller's loop. -/
theorem lrsTable_rqPure : ∀ e ∈ lrsTable,
    Stmt.pureList [e.2.2.2.2.2.2.2] (rqsBody e.2.2.1 e.2.2.2.1 e.2.2.2.2.1) = true ∧
      Stmt.pureList [e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2] (rqsBody e.2.2.1 e.2.2.2.1 e.2.2.2.2.1) = true := by
  decide +kernel

theorem loop_lrsLoopBody {rq self : String} {fl : Fn} (h : coreProgram.find? self = some fl)
    (hb : fl.body = lrsLoopBody rq self) : coreProgram.loop self = true := by
  have hn : fl.name = self := by simpa using List.find?_some h
  rw [Program.loop_of_find? h, Fn.loop, hb]
  show (self == fl.name) = true
  rw [hn]; exact beq_self_eq_true _

/-- **Every `level_residual_slow` and its sum complete placed, their ends bounded.** -/
theorem lrsAE_complete (kd : ℕ) : ∀ e ∈ lrsTable,
    LrsAE fs al cert kd e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 ∧
      LsumAE fs al cert kd e.2.2.2.2.2.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 := by
  intro e he
  obtain ⟨⟨fo, hfo, hpo, hbo⟩, ⟨fs', hfs, hps, hbs⟩, ⟨fl, hfl, hpl, hbl⟩⟩ := lrsTable_ok e he
  obtain ⟨hQ1, hQ, hrq⟩ := lrsTable_shapes e he
  obtain ⟨fr, hfr, hpr, hbr⟩ := rqsTable_ok _ hrq
  have hckr := rqsTable_pure _ hrq
  obtain ⟨hp1, hp2⟩ := lrsTable_rqPure e he
  have hlr : coreProgram.loop e.2.2.2.2.2.2.2 = false := by
    rw [Program.loop_of_find? hfr, Fn.loop, hbr, rqsBody, List.reverse_append]; rfl
  have hrqF : RqFacts e.2.2.2.2.2.2.2 e.2.2.1 e.2.2.2.1 :=
    ⟨fr, hfr, hpr.trans osParams_three.symm ▸ hpr, by rw [hbr]; exact hckr, by rw [hbr]; exact hp1, hlr⟩
  have hS : coreProgram.PureIn [e.2.2.2.2.2.2.1, e.2.2.2.2.2.2.2] := by
    intro g hg fn hfn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [hfl, Option.some.injEq] at hfn
      subst hfn
      rw [hbl]
      simp [lrsLoopBody, Stmt.pureList, Stmt.pure, atomUnplaced]
    · rw [hfr, Option.some.injEq] at hfn
      subst hfn
      rw [hbr]; exact hp2
  have hsum := lsumAE_complete' (fs := fs) (al := al) (cert := cert) hfs hps hbs
    (by rw [Program.loop_of_find? hfs, Fn.loop, hbs]; rfl) hfl hpl hbl (loop_lrsLoopBody hfl hbl) hS hrqF
    (rqs_complete kd _ hrq) hQ1 hQ
  exact ⟨lrsAE_complete' hfo hpo hbo (by rw [Program.loop_of_find? hfo, Fn.loop, hbo]; rfl) hsum, hsum⟩

theorem LsumAE.toA {kd : ℕ} {name : String} {Q pre yr vo : ℕ} (h : LsumAE fs al cert kd name Q pre yr vo) :
    LsumA fs al cert kd name Q pre yr vo := by
  intro ip ifc itc lam pos cs R h1 h2 h3 fp c hfc
  obtain ⟨e, -, he⟩ := h ip ifc itc lam pos cs R h1 h2 h3 fp c hfc
  exact ⟨e, he⟩

theorem LrsAE.toA {kd : ℕ} {name : String} {Q pre yr vo : ℕ} (h : LrsAE fs al cert kd name Q pre yr vo) :
    LrsA fs al cert kd name Q pre yr vo := by
  intro ip ifc itc lam z pos cs R hz h1 h2 h3 fp c hfc
  obtain ⟨e, -, he⟩ := h ip ifc itc lam z pos cs R hz h1 h2 h3 fp c hfc
  exact ⟨e, he⟩

/-- **`level_residual_sum` completes placed.** -/
theorem lsumA_complete' {kd Q : ℕ} {name rq loop : String} {fo fl : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 4)
    (hbo : fo.body = lsumBody Q loop) (hlo : coreProgram.loop name = false)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = osParams 8)
    (hbl : fl.body = lrsLoopBody rq loop) (hll : coreProgram.loop loop = true)
    (hS : coreProgram.PureIn [loop, rq]) {pre yr vo : ℕ} (hrqF : RqFacts rq pre yr)
    (hrq : RqsComplete kd rq pre yr vo) (hQ1 : 1 ≤ Q) (hQ : Q < 2 ^ 30) :
    LsumA fs al cert kd name Q pre yr vo :=
  (lsumAE_complete' hfo hpo hbo hlo hfl hpl hbl hll hS hrqF hrq hQ1 hQ).toA

/-- **`level_residual_slow` completes placed.** -/
theorem lrsA_complete' {kd : ℕ} {name sum : String} {fo : Fn}
    (hfo : coreProgram.find? name = some fo) (hpo : fo.params = osParams 5)
    (hbo : fo.body = lrsBody sum) (hlo : coreProgram.loop name = false) {Q pre yr vo : ℕ}
    (hsum : LsumAE fs al cert kd sum Q pre yr vo) : LrsA fs al cert kd name Q pre yr vo :=
  (lrsAE_complete' hfo hpo hbo hlo hsum).toA

/-- **Every `level_residual_slow` and its sum complete placed.** -/
theorem lrsA_complete (kd : ℕ) : ∀ e ∈ lrsTable,
    LrsA fs al cert kd e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 ∧
      LsumA fs al cert kd e.2.2.2.2.2.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 :=
  fun e he => ⟨(lrsAE_complete kd e he).1.toA, (lrsAE_complete kd e he).2.toA⟩

end
end LeanVM.Guest.B1.VsC
