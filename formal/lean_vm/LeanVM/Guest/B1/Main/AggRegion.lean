/-
  LeanVM.Guest.B1.Main.AggRegion

  `aggregate_claims`' completeness in the uniform region-indexed form (`RelAtIn`): its size chosen
  before the memory, its loads in its own buffers or in the children's claims and `defer_stmt`.
-/

module

public import LeanVM.Guest.B1.Main.AggPlaced
public import LeanVM.Guest.B1.Main.AggSize
public import LeanVM.Guest.B1.Main.Restrict

/-!
# `aggregate_claims`, by regions

`aggBufs` is the honest contents of the fifteen `HeapBuf`s, `aggOwnL` their layout at `fp`, and
`aggExtL` the caller's buffers it reads: the children's public inputs, fresh claims and carried
claims, and `defer_stmt`. A memory holding both layouts satisfies `AggMem`, `ChildClaimsAt` and the
deferred claim's cells (`aggMem_of_memL`, `childClaimsAt_of_memL`).

`aggregate_claims_relAtIn`: for every `fp` one size `n` serves every memory holding the layouts.
On the restriction of one such memory to them, its callees' relations load from the layouts only
and are placed anywhere at one size (`relAtIn_uniform_of_supp`); the body's own loads read the
layouts by the same restriction (`loads_of_supp`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-! ## The layouts -/

/-- **The honest contents of `aggregate_claims`' `HeapBuf`s**, in allocation order. -/
def aggBufs (cs : List ChildClaims) (h : BatchHints) (fresh carried : E) : List (List E) :=
  let n := cs.length
  let rs := (agRb cs h).1.1
  let rM := (agRm cs h).1.1
  [h.bytecodeRounds.flatMap (fun r => [r.1, r.2]), h.matrixRounds.flatMap (fun r => [r.1, r.2]),
    (List.range n).map (fun c => fresh * gen ^ (106 * c)),
    (List.range n).map (fun c => carried * gen ^ (53 * c)),
    (List.range (n + 1)).flatMap (fun c =>
      [(digestScalars (obsAll (agCv1 cs) ((cs.take c).flatMap childCells))).1,
        (digestScalars (obsAll (agCv1 cs) ((cs.take c).flatMap childCells))).2]),
    (List.range n).flatMap (fun c => [((agLB cs).getD c (0, 0)).1, ((agLB cs).getD c (0, 0)).2]),
    (List.range (n + 1)).flatMap (fun c => [(digestScalars (sqIt2 (agCvA cs) c)).1,
      (digestScalars (sqIt2 (agCvA cs) c)).2,
      sumE (List.zipWith bcTerm (cs.take c) ((agLB cs).take c))]),
    rs,
    (List.range (n + 1)).map (fun c =>
      sumE (List.zipWith (bcWeight rs) (cs.take c) ((agLB cs).take c))),
    (List.range n).flatMap (fun c => [((agLM cs h).getD c (0, 0, 0)).1,
      ((agLM cs h).getD c (0, 0, 0)).2.1, ((agLM cs h).getD c (0, 0, 0)).2.2]),
    (List.range (n + 1)).flatMap (fun c => [(digestScalars (sqIt3 (agRb cs h).2 c)).1,
      (digestScalars (sqIt3 (agRb cs h).2 c)).2,
      sumE (List.zipWith mtTerm (cs.take c) ((agLM cs h).take c))]),
    rM,
    (List.range 6).flatMap (fun t => (List.range (2 ^ (t + 1))).map (etK (rM.take 6) (t + 1))),
    (List.range 6).flatMap (fun t =>
      (List.range (2 ^ (t + 1))).map (etK ((rM.drop 14).take 6) (t + 1))),
    (List.range (n + 1)).flatMap (fun c =>
      [sumE (List.zipWith (mtWeightA rM) (cs.take c) ((agLM cs h).take c)),
        sumE (List.zipWith (mtWeightB rM) (cs.take c) ((agLM cs h).take c))])]

/-- `aggregate_claims`' `HeapBuf`s at `fp`. -/
def aggOwnL (fs : String → ℕ) (fp : ℕ) (cs : List ChildClaims) (h : BatchHints) (fresh carried : E) :
    Layout :=
  (bases (fp + fs "aggregate_claims") (aggSizes cs.length)).zip (aggBufs cs h fresh carried)

/-- The caller's buffers `aggregate_claims` reads: the children's public inputs, fresh claims and
carried claims, and the deferred claim at `defer_stmt`. -/
def aggExtL (ap af ac ad : ℕ) (cs : List ChildClaims) (d : DeferredClaim) : Layout :=
  [(ap, cs.flatMap fun c => [(digestScalars c.publicInput).1, (digestScalars c.publicInput).2]),
    (af, cs.flatMap fun c => fixedCells c.fresh), (ac, cs.flatMap fun c => c.carried.cells),
    (ad, d.cells)]

/-! ## Reading the layouts -/

theorem readsAt_pairs {p : E} {l : List (E × E)} (h : ReadsAt rd p (l.flatMap fun r => [r.1, r.2])) :
    ∀ r < l.length, LoadHolds rd p (2 * r) (l.getD r (0, 0)).1 ∧
      LoadHolds rd p (2 * r + 1) (l.getD r (0, 0)).2 := by
  intro r hr
  have := readsAt_flatMap_of l (w := 2) (fun _ _ => rfl) h r hr
  rw [List.getD_eq_getElem _ _ hr]
  exact ⟨by rw [← Nat.add_zero (2 * r), ← loadHolds_mul_gen_pow]; exact this 0 (by simp),
    by rw [← loadHolds_mul_gen_pow]; exact this 1 (by simp)⟩

theorem readsAt_range_map {p : E} {n : ℕ} {f : ℕ → E} (h : ReadsAt rd p ((List.range n).map f)) :
    ∀ c < n, LoadHolds rd p c (f c) := fun c hc => by
  have := h c (by simpa using hc)
  simpa using this

theorem sum_two_pow (t : ℕ) : ∑ j ∈ Finset.range t, 2 ^ (j + 1) = 2 ^ (t + 1) - 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    have : 2 ≤ 2 ^ (t + 1) := by
      have := Nat.one_le_two_pow (n := t); rw [pow_succ]; omega
    rw [pow_succ 2 (t + 1)]; omega

theorem length_flatMap_range (g : ℕ → List E) : ∀ t,
    ((List.range t).flatMap g).length = ∑ j ∈ Finset.range t, (g j).length
  | 0 => rfl
  | t + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range g t,
      Finset.sum_range_succ]
    simp

theorem readsAt_flatMap_range_off {p : E} {g : ℕ → List E} :
    ∀ m, ReadsAt rd p ((List.range m).flatMap g) →
      ∀ t < m, ReadsAt rd (p * gen ^ (∑ j ∈ Finset.range t, (g j).length)) (g t)
  | 0, _, t, ht => absurd ht (by omega)
  | m + 1, h, t, ht => by
    rw [List.range_succ, List.flatMap_append, readsAt_append'] at h
    rcases Nat.lt_or_ge t m with ht' | ht'
    · exact readsAt_flatMap_range_off m h.1 t ht'
    · have e : t = m := by omega
      subst e
      have h2 := h.2
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h2
      rwa [length_flatMap_range] at h2

theorem readsAt_eqLayers {p : E} {F : ℕ → ℕ → E}
    (h : ReadsAt rd p ((List.range 6).flatMap fun t => (List.range (2 ^ (t + 1))).map (F (t + 1)))) :
    ∀ t < 6, ∀ i < 2 ^ (t + 1), LoadHolds rd p (2 ^ (t + 1) - 2 + i) (F (t + 1) i) := by
  intro t ht i hi
  have := readsAt_flatMap_range_off 6 h t ht
  simp only [List.length_map, List.length_range, sum_two_pow] at this
  have := this i (by simpa using hi)
  rw [loadHolds_mul_gen_pow] at this
  simpa using this

/-! ## The layouts give the memory facts -/

/-- **The fifteen `HeapBuf`s held**, one `ReadsAt` each at `aggPtrs`. -/
theorem memL_own {fs : String → ℕ} {fp : ℕ} {cs : List ChildClaims} {h : BatchHints}
    {fresh carried : E} (hL : MemL rd (aggOwnL fs fp cs h fresh carried)) :
    let P := aggPtrs fs fp cs.length
    let B := aggBufs cs h fresh carried
    ReadsAt rd P.msgB (B.getD 0 []) ∧ ReadsAt rd P.msgM (B.getD 1 []) ∧
      ReadsAt rd P.frow (B.getD 2 []) ∧ ReadsAt rd P.crow (B.getD 3 []) ∧
      ReadsAt rd P.absb (B.getD 4 []) ∧ ReadsAt rd P.lamB (B.getD 5 []) ∧
      ReadsAt rd P.bcc (B.getD 6 []) ∧ ReadsAt rd P.rs (B.getD 7 []) ∧
      ReadsAt rd P.wB (B.getD 8 []) ∧ ReadsAt rd P.lamM (B.getD 9 []) ∧
      ReadsAt rd P.mcc (B.getD 10 []) ∧ ReadsAt rd P.rM (B.getD 11 []) ∧
      ReadsAt rd P.eqR (B.getD 12 []) ∧ ReadsAt rd P.eqC (B.getD 13 []) ∧
      ReadsAt rd P.wsum (B.getD 14 []) := by
  simp only [aggOwnL, aggSizes, bases, aggBufs, List.zip_cons_cons, List.zip_nil_right, memL_cons,
    memL_nil, and_true] at hL
  simp only [aggPtrs, aggSizes, bases, aggBufs, List.getD_cons_zero, List.getD_cons_succ]
  exact hL

theorem aggMem_of_memL {fs : String → ℕ} {fp : ℕ} {cs : List ChildClaims} {h : BatchHints}
    {fresh carried : E} (hbr : h.bytecodeRounds.length = 22) (hmr : h.matrixRounds.length = 28)
    (hL : MemL rd (aggOwnL fs fp cs h fresh carried)) :
    AggMem rd (aggPtrs fs fp cs.length) fresh carried cs h := by
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14⟩ := memL_own hL
  simp only [aggBufs, List.getD_cons_zero, List.getD_cons_succ] at m0 m1 m2 m3 m4 m5 m6 m7
  simp only [aggBufs, List.getD_cons_zero, List.getD_cons_succ] at m8 m9 m10 m11 m12 m13 m14
  have r4 := readsAt_range_flatMap (w := 2) (fun _ _ => rfl) m4
  have r5 := readsAt_range_flatMap (w := 2) (fun _ _ => rfl) m5
  have r6 := readsAt_range_flatMap (w := 3) (fun _ _ => rfl) m6
  have r9 := readsAt_range_flatMap (w := 3) (fun _ _ => rfl) m9
  have r10 := readsAt_range_flatMap (w := 3) (fun _ _ => rfl) m10
  have r14 := readsAt_range_flatMap (w := 2) (fun _ _ => rfl) m14
  refine ⟨fun r hr => readsAt_pairs m0 r (by omega), fun r hr => readsAt_pairs m1 r (by omega),
    fun c hc => ⟨readsAt_range_map m2 c hc, readsAt_range_map m3 c hc⟩,
    fun c hc => ⟨by simpa using r4 c (by omega) 0 (by omega),
      by simpa using r4 c (by omega) 1 (by omega)⟩,
    fun c hc => ⟨by simpa using r5 c hc 0 (by omega), by simpa using r5 c hc 1 (by omega)⟩,
    fun c hc => ⟨by simpa using r6 c (by omega) 0 (by omega),
      by simpa using r6 c (by omega) 1 (by omega), by simpa using r6 c (by omega) 2 (by omega)⟩,
    m7, fun c hc => readsAt_range_map m8 c (by omega),
    fun c hc => ⟨by simpa using r9 c hc 0 (by omega), by simpa using r9 c hc 1 (by omega),
      by simpa using r9 c hc 2 (by omega)⟩,
    fun c hc => ⟨by simpa using r10 c (by omega) 0 (by omega),
      by simpa using r10 c (by omega) 1 (by omega), by simpa using r10 c (by omega) 2 (by omega)⟩,
    m11, readsAt_eqLayers m12, readsAt_eqLayers m13,
    fun c hc => ⟨by simpa using r14 c (by omega) 0 (by omega),
      by simpa using r14 c (by omega) 1 (by omega)⟩⟩

theorem childClaimsAt_of_memL {ap af ac ad : ℕ} {cs : List ChildClaims} {d : DeferredClaim}
    (hsh : ∀ c ∈ cs, FreshShaped c.fresh ∧ c.carried.bytecodePoint.length = 22 ∧
      c.carried.matrixPoint.length = 28)
    (hL : MemL rd (aggExtL ap af ac ad cs d)) :
    ChildClaimsAt rd (ofK (gpow ap)) (ofK (gpow af)) (ofK (gpow ac)) cs ∧
      ReadsAt rd (ofK (gpow ad)) d.cells := by
  simp only [aggExtL, memL_cons, memL_nil, and_true] at hL
  obtain ⟨hp, hf, hc, hd⟩ := hL
  refine ⟨fun c hc' => ?_, hd⟩
  obtain ⟨g1, g2, g3⟩ := hsh cs[c] (List.getElem_mem hc')
  have p := readsAt_flatMap_of cs (w := 2) (fun _ _ => rfl) hp c hc'
  refine ⟨by simpa [loadHolds_mul_gen_pow] using p 0 (by simp),
    by simpa [loadHolds_mul_gen_pow] using p 1 (by simp), g1,
    readsAt_flatMap_of cs (w := 106) (fun a ha => (fixedCells_getD (hsh a ha).1).1) hf c hc', g2, g3,
    readsAt_flatMap_of cs (w := 53) (fun a ha => (deferCells_getD (hsh a ha).2.1 (hsh a ha).2.2).1) hc
      c hc'⟩

/-! ## The path, once -/

theorem length_aggBufs {cs : List ChildClaims} {h : BatchHints} {fresh carried : E}
    (hbr : h.bytecodeRounds.length = 22) (hmr : h.matrixRounds.length = 28) :
    (aggBufs cs h fresh carried).map List.length = aggSizes cs.length := by
  have hrb : (agRb cs h).1.1.length = 22 := by rw [agRb, batchRounds_length, hbr]
  have hrm : (agRm cs h).1.1.length = 28 := by rw [agRm, batchRounds_length, hmr]
  have l2 : ∀ (m : ℕ) (f : ℕ → E) (g : ℕ → E),
      ((List.range m).flatMap fun c => [f c, g c]).length = 2 * m := fun m f g => by
    rw [length_flatMap_range]; simp [mul_comm]
  have l3 : ∀ (m : ℕ) (f g k : ℕ → E),
      ((List.range m).flatMap fun c => [f c, g c, k c]).length = 3 * m := fun m f g k => by
    rw [length_flatMap_range]; simp [mul_comm]
  have lp : ∀ l : List (E × E), (l.flatMap fun r => [r.1, r.2]).length = 2 * l.length := fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons, ih]; ring
  have le : ∀ rs : List E,
      ((List.range 6).flatMap fun t => (List.range (2 ^ (t + 1))).map (etK rs (t + 1))).length =
        126 := fun rs => by
    rw [length_flatMap_range]; simp [Finset.sum_range_succ]
  simp only [aggBufs, aggSizes, List.map_cons, List.map_nil, lp, hbr, hmr, List.length_map,
    List.length_range, l2, l3, hrb, hrm, le, List.cons.injEq, and_true]
  and_intros
  all_goals trivial

theorem region_zip : ∀ (b : ℕ) (sizes : List ℕ) (bufs : List (List E)),
    bufs.map List.length = sizes → ∀ i, RegionL ((bases b sizes).zip bufs) i →
      ∃ q ∈ sizes.zip (bases b sizes), q.2 ≤ i ∧ i < q.2 + q.1
  | _, [], _, _, _, ⟨_, hq, _⟩ => by simp [bases] at hq
  | b, s :: sizes, [], hl, _, _ => by simp at hl
  | b, s :: sizes, x :: bufs, hl, i, ⟨q, hq, h1, h2⟩ => by
    simp only [List.map_cons, List.cons.injEq] at hl
    simp only [bases, List.zip_cons_cons, List.mem_cons] at hq ⊢
    rcases hq with rfl | hq
    · exact ⟨(s, b), Or.inl rfl, h1, by simp only at h2 ⊢; omega⟩
    · obtain ⟨q', hq', h1', h2'⟩ := region_zip (b + s) sizes bufs hl.2 i ⟨q, hq, h1, h2⟩
      exact ⟨q', Or.inr hq', h1', h2'⟩

theorem regionL_append {L L' : Layout} {i : ℕ} : RegionL (L ++ L') i ↔ RegionL L i ∨ RegionL L' i := by
  simp only [RegionL, List.mem_append]
  constructor
  · rintro ⟨q, hq | hq, h⟩
    · exact Or.inl ⟨q, hq, h⟩
    · exact Or.inr ⟨q, hq, h⟩
  · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩)
    · exact ⟨q, Or.inl hq, h⟩
    · exact ⟨q, Or.inr hq, h⟩

/-! ## The relation, by regions -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **`aggregate_claims`, by regions** (G:3319-3486; TRIAGE #77): for nonempty claims `cs` of the
guest's shape, at most `16`, hints of `22` and `28` rounds whose batching closes on `d`, the
children's public inputs, fresh and carried claims at `g^ap`, `g^af`, `g^ac` and `defer_stmt` at
`g^ad`, at every `fp` one size `n`, covering the frame and the `HeapBuf`s, serves every memory
holding `aggregate_claims`' `HeapBuf`s at `fp` and the caller's buffers: `aggregate_claims` holds
by a tree placed at `fp`, of `n` words, loading from its own data or the caller's buffers. -/
theorem aggregate_claims_relAtIn (fs : String → ℕ) (cert : String → V → ℕ) {cs : List ChildClaims}
    {h : BatchHints} {d : DeferredClaim} (hne : cs ≠ []) (hlen : cs.length ≤ 16)
    (hb : batch cs h = some d) (hbr : h.bytecodeRounds.length = 22)
    (hmr : h.matrixRounds.length = 28)
    (hsh : ∀ c ∈ cs, FreshShaped c.fresh ∧ c.carried.bytecodePoint.length = 22 ∧
      c.carried.matrixPoint.length = 28) (ap af ac ad fp : ℕ) :
    ∃ n, fs "aggregate_claims" + (aggSizes cs.length).sum ≤ n ∧ n ≤ aggBound fs cs.length ∧
      ∀ rd : Reader, MemL rd (aggOwnL fs fp cs h (ofK (gpow af)) (ofK (gpow ac)) ++
        aggExtL ap af ac ad cs d) →
      RelAtIn coreProgram fs cert rd (RegionL (aggExtL ap af ac ad cs d)) (fun _ => False) fp n
        "aggregate_claims" [gen ^ cs.length, ofK (gpow ap), ofK (gpow af), ofK (gpow ac),
          ofK (gpow ad)] [] := by
  classical
  have hn0 : 0 < cs.length := List.length_pos_iff.mpr hne
  set L := aggOwnL fs fp cs h (ofK (gpow af)) (ofK (gpow ac)) ++ aggExtL ap af ac ad cs d with hLdef
  set S := RegionL L with hS
  set P := aggPtrs fs fp cs.length with hP
  set σ := agVal cs h P (ofK (gpow ap)) (ofK (gpow af)) (ofK (gpow ac)) (ofK (gpow ad)) with hσ
  set es := agPre.flatMap (slEvs σ) with hes
  have hwf : Stmt.wfList coreProgram agBody = true := by
    have := coreProgram_wf Data.core29 (List.mem_of_find?_eq_some find_aggregate_claims)
    rwa [core29_body] at this
  have hw := walk_straight σ [] agPre agPre_straight
  rw [← agBody_eq] at hw
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ agPre agPre_straight
  rw [agPre_allocs] at e1 e2
  rw [agPre_addrs] at e3
  rw [agPre_calls] at e4
  have hK : 1 + gen ^ cs.length ≠ 0 := one_add_gen_pow_ne_zero hn0 (by unfold ordG; omega)
  have hlt : ∀ e ≤ 3 * cs.length + 3, e < 2 ^ 64 - 1 := fun e he => by
    have : 3 * cs.length + 3 < 2 ^ 64 - 1 := by norm_num; omega
    omega
  have t33 : σ (.n 33) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have t48 : σ (.n 48) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have t67 : σ (.n 67) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have t82 : σ (.n 82) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have t513 : σ (.n 513) ≠ 0 := by simp only [hσ, agVal]; ag_look; exact hK
  have g0 : logG (σ (.n 0)) = cs.length := by
    rw [show σ (.n 0) = gen ^ cs.length by simp only [hσ, agVal]; ag_look]
    exact logG_gen_pow (hlt _ (by omega))
  have g30 : logG (σ (.n 30)) = 2 * cs.length + 2 := by
    rw [show σ (.n 30) = gen ^ (2 * cs.length + 2) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g37 : logG (σ (.n 37)) = 2 * cs.length := by
    rw [show σ (.n 37) = gen ^ (2 * cs.length) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g42 : logG (σ (.n 42)) = 3 * cs.length + 3 := by
    rw [show σ (.n 42) = gen ^ (3 * cs.length + 3) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g63 : logG (σ (.n 63)) = cs.length + 1 := by
    rw [show σ (.n 63) = gen ^ (cs.length + 1) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g73 : logG (σ (.n 73)) = 3 * cs.length := by
    rw [show σ (.n 73) = gen ^ (3 * cs.length) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g78 : logG (σ (.n 78)) = 3 * cs.length + 3 := by
    rw [show σ (.n 78) = gen ^ (3 * cs.length + 3) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have g508 : logG (σ (.n 508)) = 2 * cs.length + 2 := by
    rw [show σ (.n 508) = gen ^ (2 * cs.length + 2) by simp only [hσ, agVal]; ag_look; ring]
    exact logG_gen_pow (hlt _ (by omega))
  have hall : allocs σ es = aggSizes cs.length := by
    rw [e2]
    simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, g0, g30, g37, g42, g63,
      g73, g78, g508, aggSizes]
  have hbuf : (allocDsts es).map σ = (bases (fp + fs "aggregate_claims") (allocs σ es)).map
      fun b => ofK (gpow b) := by
    rw [e1, hall]
    simp only [List.map_cons, List.map_nil, hσ, agVal]
    ag_look
    simp only [hP, aggPtrs, aggSizes, bases, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ]
  have hown : ∀ i, RegionL (aggOwnL fs fp cs h (ofK (gpow af)) (ofK (gpow ac))) i →
      ownData cert fp (fp + fs "aggregate_claims") "aggregate_claims" (allocs σ es) es i :=
    fun i hi => Or.inl (by rw [hall]; exact region_zip _ _ _ (length_aggBufs hbr hmr) i hi)
  have hSR : ∀ i, S i → RegionL (aggExtL ap af ac ad cs d) i ∨
      ownData cert fp (fp + fs "aggregate_claims") "aggregate_claims" (allocs σ es) es i :=
    fun i hi => (regionL_append.mp hi).elim (fun h => Or.inr (hown i h)) Or.inl
  by_cases hex : ∃ rd1, MemL rd1 L
  swap
  · exact ⟨_, le_rfl, by unfold aggBound; omega, fun rd hL => absurd ⟨rd, hL⟩ hex⟩
  obtain ⟨rd1, h1⟩ := hex
  -- the restriction of one memory to the layouts
  have h0 : MemL (restrict rd1 S) L := memL_restrict h1 fun i hi => hi
  obtain ⟨ho0, he0⟩ := memL_append.mp h0
  have hM0 := aggMem_of_memL hbr hmr ho0
  obtain ⟨hC0, hd0⟩ := childClaimsAt_of_memL hsh he0
  have hsupp := restrict_supp' rd1 S
  obtain ⟨m95, k95⟩ := relAtIn_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop95")
    (by simp) hsupp (ag_loop95 hn0 hC0 hM0)
  obtain ⟨m96, k96⟩ := relAtIn_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop96")
    (by simp) hsupp (ag_loop96 hn0 hC0 hM0)
  obtain ⟨m22, k22⟩ := relAtIn_uniform_of_supp fs cert coreProgram_wf aggPure
    (g := "batch_sumcheck__L22") (by simp) hsupp (ag_bs22 hbr hM0)
  obtain ⟨m97, k97⟩ := relAtIn_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop97")
    (by simp) hsupp (ag_loop97 hn0 hbr hC0 hM0)
  obtain ⟨m98, k98⟩ := relAtIn_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop98")
    (by simp) hsupp (ag_loop98 hn0 hC0 hM0)
  obtain ⟨m28, k28⟩ := relAtIn_uniform_of_supp fs cert coreProgram_wf aggPure
    (g := "batch_sumcheck__L28") (by simp) hsupp (ag_bs28 hmr hM0)
  obtain ⟨m99, k99⟩ := relAtIn_uniform_of_supp fs cert coreProgram_wf aggPure (g := "__loop99")
    (by simp) hsupp (ag_loop99 hn0 hmr hC0 hM0)
  have hs0 := walk_sat agBody hwf (agBody_holds hne hb hbr hmr hC0 hd0 P hM0)
  rw [hw] at hs0
  have hloadS := loads_of_supp hsupp fun e he => (hs0.1 e he).1
  have hx : ∀ A v, restrict rd1 S A = some v → restrict rd1 S A = some v := fun _ _ h => h
  have b95 : m95 ≤ cs.length * fs "__loop95" + fs "__loop95" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k95 0 _ hx; rw [← ht]; exact loop95_total hn0 hn hv hbo
  have b96 : m96 ≤ cs.length * fs "__loop96" + fs "__loop96" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k96 0 _ hx; rw [← ht]; exact loop96_total hn0 hn hv hbo
  have b97 : m97 ≤ cs.length * fs "__loop97" + fs "__loop97" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k97 0 _ hx; rw [← ht]; exact loop97_total hn0 hn hv hbo
  have b98 : m98 ≤ cs.length * fs "__loop98" + fs "__loop98" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k98 0 _ hx; rw [← ht]; exact loop98_total hn0 hn hv hbo
  have b99 : m99 ≤ cs.length * fs "__loop99" + fs "__loop99" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k99 0 _ hx; rw [← ht]; exact loop99_total hn0 hn hv hbo
  have b22 : m22 = fs "batch_sumcheck__L22" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k22 0 _ hx; rw [← ht]; exact bs22_total hn hv hbo
  have b28 : m28 = fs "batch_sumcheck__L28" := by
    obtain ⟨t, hn, hv, hbo, -, ht, -⟩ := k28 0 _ hx; rw [← ht]; exact bs28_total hn hv hbo
  refine ⟨fs "aggregate_claims" + (allocs σ es).sum +
    (m95 + (m96 + (m22 + (m97 + (m98 + (m28 + (m99 + 0))))))), by rw [hall]; omega,
    by rw [hall]; unfold aggBound; omega, fun rd hL => ?_⟩
  obtain ⟨ho, he⟩ := memL_append.mp hL
  obtain ⟨hC, hd⟩ := childClaimsAt_of_memL hsh he
  have hs := walk_sat agBody hwf (agBody_holds hne hb hbr hmr hC hd P (aggMem_of_memL hbr hmr ho))
  rw [hw] at hs
  have hext : ∀ A v, restrict rd1 S A = some v → rd A = some v := fun A v hA => by
    obtain ⟨i, rfl, hi⟩ := restrict_supp hA
    rw [restrict_of ⟨i, rfl, hi⟩] at hA
    rw [memL_agree hL h1 i hi]; exact hA
  refine relAtIn_of_walk (Dk := fun _ => False)
    (N := m95 + (m96 + (m22 + (m97 + (m98 + (m28 + (m99 + 0)))))))
    coreProgram_wf find_aggregate_claims (Or.inl aggregate_claims_not_loop)
    (by simp only [show Fn.params Data.core29 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
      List.map_cons, List.map_nil, hσ, agVal]; ag_look) (by rw [core29_body]; exact hw) rfl
    (fun e he => (hs.1 e he).1) hbuf (by rw [e3]; simp) ?_ ?_ (fun _ h => h.elim)
  · rw [e4]
    simp only [List.map_cons, List.map_nil, mkCall, KidsFromIn, ne_eq, t33, t48, t67, t82, t513,
      not_false_eq_true, decide_true, ↓reduceIte]
    refine ⟨m95, _, S, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m96, _, S, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m22, _, S, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m97, _, S, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m98, _, S, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m28, _, S, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_,
      m99, _, S, fun _ => False, rfl, fun i hi => Or.inl (hSR i hi), ?_, rfl, fun i hi => ?_⟩
    all_goals try (simp only [hσ, agVal]; ag_look)
    exacts [k95 _ rd hext, k96 _ rd hext, k22 _ rd hext, k97 _ rd hext, k98 _ rd hext, k28 _ rd hext,
      k99 _ rd hext, by simp at hi]
  · intro A hA
    obtain ⟨i, hi, hSi⟩ := hloadS A hA
    exact ⟨i, hi, (hSR i hSi).elim (fun h => Or.inr (Or.inl h)) Or.inl⟩

end
end LeanVM.Guest.B1.Main
