/-
  LeanVM.Guest.B1.Place.OsPlace

  A straight-line function returning some of its buffers, complete in the placed form from its
  callees' composition. Ported from mumbai's `B1/Whir/OsPlace.lean` (one returned buffer there).
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Main.KidsT

/-!
# Straight-line bodies returning buffers, placed

`os_completeAt_placeJ`: a function whose body is straight-line statements then a `ret`, with no
`frameAddr`, is `CompleteAtD` returning its buffers `js` (indices into its `HeapBuf`s, distinct),
when at every frame pointer a valuation satisfies its body with the allocator's pointers on every
memory holding its buffers and the caller's words, and its callees, from after its buffers, are
`KidsFromIn` on every memory holding also their layout. Its loads are in its buffers or the
caller's words because they hold on every such memory (`os_addr_in_regionL`).
`os_completeAt_placeJF`: the same for a flat body, its dispatches entering the selected callee.
`os_completeAt_placeJFOT`: at an optional words bound (`CompleteAtOT`), its callees `KidsFromInT`, the tree its
node with the callees' trees satisfying their predicates (`FlatNodeT`); `os_completeAt_placeJFO` drops them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A word every memory holding `M` holds at `A` lies in `M`'s region.** -/
theorem os_addr_in_regionL {κ : ℕ} {M : Layout} {A : K} {v : E}
    (hall : ∀ rd, LowDef κ rd → MemL rd M → rd A = some v) {rd : Reader} (hlow : LowDef κ rd)
    (hL : MemL rd M) : ∃ i, A = addressOfIndex i ∧ RegionL M i := by
  classical
  by_contra hn
  simp only [not_exists, not_and] at hn
  let rd2 : Reader := fun B => if B = A then some (v + 1) else rd B
  have hlow2 : LowDef κ rd2 := fun i hi => by
    simp only [rd2]; split
    · rfl
    · exact hlow i hi
  have hL2 : MemL rd2 M := by
    intro q hq k hk
    refine ⟨(hL q hq k hk).1, ?_⟩
    rw [Main.addr_ofK]
    have hne : addressOfIndex (q.1 + k) ≠ A := fun he
        => hn (q.1 + k) he.symm ⟨q, hq, by omega, by omega⟩
    simp only [rd2, hne, ↓reduceIte]
    rw [← Main.addr_ofK]; exact (hL q hq k hk).2
  have := hall rd2 hlow2 hL2
  simp only [rd2, ↓reduceIte, Option.some.injEq] at this
  exact one_ne_zero (by linear_combination this : (1 : E) = 0)

theorem os_kidsFromIn_rmono {rd : Reader} {σ : Val} {R R' : ℕ → Prop} (hR : ∀ i, R i → R' i) :
    ∀ (cs : List Call) (Dacc : ℕ → Prop) (b n : ℕ) (D : ℕ → Prop),
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n D → KidsFromIn coreProgram fs cert rd σ R' Dacc cs b n D
  | [], _, _, _, _, h => h
  | _ :: cs, _, _, _, _, ⟨m, n', Rk, Dk, hn, hRk, hc, hk⟩ =>
    ⟨m, n', Rk, Dk, hn, fun i hi => (hRk i hi).imp_left (hR i), hc, os_kidsFromIn_rmono hR cs _ _ _ _ hk⟩

theorem os_bases_getD : ∀ (b : ℕ) (sizes : List ℕ) (j : ℕ), j < sizes.length →
    (bases b sizes).getD j 0 = b + (sizes.take j).sum
  | _, [], _, h => absurd h (by simp)
  | b, s :: sizes, 0, _ => by simp [bases]
  | b, s :: sizes, j + 1, h => by
    simp only [bases, List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [os_bases_getD (b + s) sizes j (by simpa using h)]; ring

theorem os_length_bases : ∀ (b : ℕ) (sizes : List ℕ), (bases b sizes).length = sizes.length
  | _, [] => rfl
  | b, _ :: sizes => by simp [bases, os_length_bases _ sizes]

theorem os_bufL_getD {b : ℕ} {sizes : List ℕ} {own : List (List E)} {j : ℕ}
    (hown : List.Forall₂ (fun c s => c.length ≤ s) own sizes) (hj : j < sizes.length) :
    (bufL b sizes own).getD j default = ((bases b sizes).getD j 0, own.getD j []) := by
  have hl1 : (bases b sizes).length = sizes.length := os_length_bases b sizes
  have hl2 : own.length = sizes.length := hown.length_eq
  simp only [bufL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl1 ▸ hj),
    List.getElem?_eq_getElem (hl2 ▸ hj), Option.getD_some]
  rw [List.getElem?_eq_getElem (by simp [hl1, hl2, hj]), Option.getD_some, List.getElem_zip]

theorem os_map_getD_range {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun j => l.getD j d) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

/-- The entries `js` of `l`, then the others, are `l` permuted. -/
theorem os_perm_pick {α : Type} (l : List α) (d : α) (js : List ℕ) (hjs : js.Nodup)
    (hjl : ∀ j ∈ js, j < l.length) :
    (js.map (fun j => l.getD j d) ++
      ((List.range l.length).filter (fun j => decide (j ∉ js))).map (fun j => l.getD j d)).Perm l := by
  conv_rhs => rw [← os_map_getD_range l d]
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  have h1 : ((List.range l.length).filter (fun j => decide (j ∈ js)) ++
      (List.range l.length).filter (fun j => !decide (j ∈ js))).Perm (List.range l.length) :=
    List.filter_append_perm _ _
  have h2 : ((List.range l.length).filter (fun j => decide (j ∈ js))).Perm js := by
    refine (List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) hjs).mpr fun x => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hjl x h, h⟩⟩
  have h3 : (List.range l.length).filter (fun j => decide (j ∉ js)) =
      (List.range l.length).filter (fun j => !decide (j ∈ js)) := by
    congr 1
  rw [h3]
  exact (h2.symm.append_right _).trans h1

/-- The layout of the returned buffers `js`. -/
def osLoutJ (b : ℕ) (sizes : List ℕ) (own : List (List E)) (js : List ℕ) : Layout :=
  js.map fun j => (b + (sizes.take j).sum, own.getD j [])

/-- **A straight-line function returning its buffers `js` is complete, placed.** -/
theorem os_completeAt_placeJ {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E)
    (Out : List E → Layout → Prop) {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (js : List ℕ) (hjs : js.Nodup) (hjl : ∀ j ∈ js, j < sizes.length)
    {C : CallRel}
    (h : ∀ fp, ∃ (σ : Val) (own : List (List E)) (rets : List E) (N : ℕ) (L : Layout)
      (Dk : ℕ → Prop) (cs : List Call),
      (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ) = cs ∧
      List.Forall₂ (fun c s => c.length ≤ s) own sizes ∧
      Out rets (osLoutJ (fp + fs f) sizes own js) ∧
      Within L (fp + fs f + sizes.sum) N ∧ DisjL L ∧ fn.params.map σ = args ∧
      (∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd Lin →
        Stmt.HoldsList C rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b))) ∧
      ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd L → MemL rd Lin →
        KidsFromIn coreProgram fs cert rd σ
          (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes own) i)
          (fun _ => False) cs (fp + fs f + sizes.sum) N Dk) :
    CompleteAtD fs cert κ f Lin args Out := by
  intro fp
  obtain ⟨σ, own, rets, N, L, Dk, cs, hcs, hown, hout, hW, hD, hp, hh, hK⟩ := h fp
  set B := bufL (fp + fs f) sizes own with hB
  have hBlen : B.length = sizes.length := by
    simp only [hB, bufL, List.length_zip, os_length_bases, hown.length_eq, Nat.min_self]
  have hLo : osLoutJ (fp + fs f) sizes own js = js.map (fun j => B.getD j default) := by
    unfold osLoutJ
    refine List.map_congr_left fun j hj => ?_
    rw [hB, os_bufL_getD hown (hjl j hj), os_bases_getD _ _ _ (hjl j hj)]
  set Lo := osLoutJ (fp + fs f) sizes own js with hLod
  set Lr : Layout := ((List.range B.length).filter (fun j => decide (j ∉ js))).map
    (fun j => B.getD j default)
  have hperm0 : (Lo ++ Lr).Perm B := by
    rw [hLo]; exact os_perm_pick B default js hjs fun j hj => hBlen ▸ hjl j hj
  have hperm : (Lo ++ (Lr ++ L)).Perm (B ++ L) := by
    rw [← List.append_assoc]; exact hperm0.append_right L
  have hmem : ∀ q, q ∈ Lo ++ (Lr ++ L) ↔ q ∈ B ++ L := fun q => hperm.mem_iff
  have hBW : Within B (fp + fs f) sizes.sum := bufL_within _ _ _ hown
  have hBD : DisjL B := bufL_disj _ _ _ hown
  have hBL : DisjL (B ++ L) := disj_append hBD hD hBW hW le_rfl
  refine ⟨fs f + sizes.sum + N, Lr ++ L, rets, Lo, hout, fun q hq => ?_, ?_, fun rd hlow hL => ?_⟩
  · rcases List.mem_append.mp ((hmem q).mp hq) with hq | hq
    · have := hBW q hq; omega
    · have := hW q hq; omega
  · exact hBL.perm hperm.symm fun h => Or.symm h
  have hLm : MemL rd (B ++ L) := fun q hq => hL q (List.mem_append_left _ ((hmem q).mpr hq))
  have hLin : MemL rd Lin := fun q hq => hL q (List.mem_append_right _ hq)
  obtain ⟨hB1, hL1⟩ := Main.memL_append.mp hLm
  have hw := Main.walk_straight σ vs pre hst
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hst
  have hsat : ∀ rd', LowDef κ rd' → MemL rd' B → MemL rd' Lin →
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd' σ) ∧ vs.map σ = rets := fun rd' h1 h2 h3 => by
    have hs := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf))
      (hh rd' h1 h2 h3).1
    rw [hw] at hs
    exact ⟨fun e he => (hs.1 e he).1, hs.2⟩
  obtain ⟨hes, hr⟩ := hsat rd hlow hB1 hLin
  obtain ⟨-, hsz, hbuf⟩ := hh rd hlow hB1 hLin
  have hal : allocs σ (pre.flatMap (Main.slEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL B i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (Main.slEvs σ)))
        (pre.flatMap (Main.slEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ hown i hi)
  have hk := os_kidsFromIn_rmono (fs := fs) (cert := cert)
    (R' := fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (Main.slEvs σ)))
        (pre.flatMap (Main.slEvs σ)) i)
    (fun i hi => hi.imp_right (hown' i)) _ _ _ _ _ (hK rd hlow hB1 hL1 hLin)
  rw [← hcs, ← i4, show fp + fs f + sizes.sum =
    fp + fs f + (allocs σ (pre.flatMap (Main.slEvs σ))).sum by rw [hal]] at hk
  have hrel := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL Lo) (Dk := Dk) (N := N) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr hes
    (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp) hk (fun A hA => ?_) (fun i hi => ?_)
  · rw [hal] at hrel
    exact hrel
  · obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
    match e, hea with
    | .atom (.load d p off), hea =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      subst hea
      have hall : ∀ rd', LowDef κ rd' → MemL rd' (B ++ Lin) →
          rd' ((σ p).limb 0 * addressOfIndex off) = some (σ d) := fun rd' h1 h2 => by
        obtain ⟨h21, h22⟩ := Main.memL_append.mp h2
        exact ((hsat rd' h1 h21 h22).1 _ he).2
      obtain ⟨i, hi, hreg⟩ := os_addr_in_regionL hall hlow (Main.memL_append.mpr ⟨hB1, hLin⟩)
      refine ⟨i, hi, ?_⟩
      obtain ⟨q, hq, h1, h2⟩ := hreg
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (hown' i ⟨q, hq, h1, h2⟩)
      · exact Or.inr (Or.inl ⟨q, hq, h1, h2⟩)
  · obtain ⟨q, hq, h1, h2⟩ := hi
    have hqB : q ∈ B := hperm0.subset (List.mem_append_left _ hq)
    exact Or.inl (hown' i ⟨q, hqB, h1, h2⟩)


/-- **A flat function returning its buffers `js` is complete, placed**: `os_completeAt_placeJ`
with dispatches, each entering the callee its selector names. -/
theorem os_completeAt_placeJF {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E)
    (Out : List E → Layout → Prop) {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (js : List ℕ) (hjs : js.Nodup) (hjl : ∀ j ∈ js, j < sizes.length)
    {C : CallRel}
    (h : ∀ fp, ∃ (σ : Val) (own : List (List E)) (rets : List E) (N : ℕ) (L : Layout)
      (Dk : ℕ → Prop) (cs : List Call),
      (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) = cs ∧ (∀ s ∈ pre, DispOk σ s) ∧
      List.Forall₂ (fun c s => c.length ≤ s) own sizes ∧
      Out rets (osLoutJ (fp + fs f) sizes own js) ∧
      Within L (fp + fs f + sizes.sum) N ∧ DisjL L ∧ fn.params.map σ = args ∧
      (∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd Lin →
        Stmt.HoldsList C rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b))) ∧
      ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd L → MemL rd Lin →
        KidsFromIn coreProgram fs cert rd σ
          (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes own) i)
          (fun _ => False) cs (fp + fs f + sizes.sum) N Dk) :
    CompleteAtD fs cert κ f Lin args Out := by
  intro fp
  obtain ⟨σ, own, rets, N, L, Dk, cs, hcs, hdo, hown, hout, hW, hD, hp, hh, hK⟩ := h fp
  set B := bufL (fp + fs f) sizes own with hB
  have hBlen : B.length = sizes.length := by
    simp only [hB, bufL, List.length_zip, os_length_bases, hown.length_eq, Nat.min_self]
  have hLo : osLoutJ (fp + fs f) sizes own js = js.map (fun j => B.getD j default) := by
    unfold osLoutJ
    refine List.map_congr_left fun j hj => ?_
    rw [hB, os_bufL_getD hown (hjl j hj), os_bases_getD _ _ _ (hjl j hj)]
  set Lo := osLoutJ (fp + fs f) sizes own js with hLod
  set Lr : Layout := ((List.range B.length).filter (fun j => decide (j ∉ js))).map
    (fun j => B.getD j default)
  have hperm0 : (Lo ++ Lr).Perm B := by
    rw [hLo]; exact os_perm_pick B default js hjs fun j hj => hBlen ▸ hjl j hj
  have hperm : (Lo ++ (Lr ++ L)).Perm (B ++ L) := by
    rw [← List.append_assoc]; exact hperm0.append_right L
  have hmem : ∀ q, q ∈ Lo ++ (Lr ++ L) ↔ q ∈ B ++ L := fun q => hperm.mem_iff
  have hBW : Within B (fp + fs f) sizes.sum := bufL_within _ _ _ hown
  have hBD : DisjL B := bufL_disj _ _ _ hown
  have hBL : DisjL (B ++ L) := disj_append hBD hD hBW hW le_rfl
  refine ⟨fs f + sizes.sum + N, Lr ++ L, rets, Lo, hout, fun q hq => ?_, ?_, fun rd hlow hL => ?_⟩
  · rcases List.mem_append.mp ((hmem q).mp hq) with hq | hq
    · have := hBW q hq; omega
    · have := hW q hq; omega
  · exact hBL.perm hperm.symm fun h => Or.symm h
  have hLm : MemL rd (B ++ L) := fun q hq => hL q (List.mem_append_left _ ((hmem q).mpr hq))
  have hLin : MemL rd Lin := fun q hq => hL q (List.mem_append_right _ hq)
  obtain ⟨hB1, hL1⟩ := Main.memL_append.mp hLm
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, -⟩ := flat_parts σ pre hst
  have hsat : ∀ rd', LowDef κ rd' → MemL rd' B → MemL rd' Lin →
      (∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd' σ) ∧ vs.map σ = rets := fun rd' h1 h2 h3 => by
    have hs := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf))
      (hh rd' h1 h2 h3).1
    rw [hw] at hs
    exact ⟨fun e he => (hs.1 e he).1, hs.2⟩
  obtain ⟨hes, hr⟩ := hsat rd hlow hB1 hLin
  obtain ⟨-, hsz, hbuf⟩ := hh rd hlow hB1 hLin
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL B i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ)))
        (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ hown i hi)
  have hk := os_kidsFromIn_rmono (fs := fs) (cert := cert)
    (R' := fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ)))
        (pre.flatMap (flEvs σ)) i)
    (fun i hi => hi.imp_right (hown' i)) _ _ _ _ _ (hK rd hlow hB1 hL1 hLin)
  rw [← hcs, ← i4, show fp + fs f + sizes.sum =
    fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum by rw [hal]] at hk
  have hrel := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL Lo) (Dk := Dk) (N := N) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr hes
    (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp) hk (fun A hA => ?_) (fun i hi => ?_)
  · rw [hal] at hrel
    exact hrel
  · obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
    match e, hea with
    | .atom (.load d p off), hea =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      subst hea
      have hall : ∀ rd', LowDef κ rd' → MemL rd' (B ++ Lin) →
          rd' ((σ p).limb 0 * addressOfIndex off) = some (σ d) := fun rd' h1 h2 => by
        obtain ⟨h21, h22⟩ := Main.memL_append.mp h2
        exact ((hsat rd' h1 h21 h22).1 _ he).2
      obtain ⟨i, hi, hreg⟩ := os_addr_in_regionL hall hlow (Main.memL_append.mpr ⟨hB1, hLin⟩)
      refine ⟨i, hi, ?_⟩
      obtain ⟨q, hq, h1, h2⟩ := hreg
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (hown' i ⟨q, hq, h1, h2⟩)
      · exact Or.inr (Or.inl ⟨q, hq, h1, h2⟩)
  · obtain ⟨q, hq, h1, h2⟩ := hi
    have hqB : q ∈ B := hperm0.subset (List.mem_append_left _ hq)
    exact Or.inl (hown' i ⟨q, hqB, h1, h2⟩)


/-- **`CompleteAtO` by a tree satisfying a predicate of the memory.** -/
def CompleteAtOT (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (Bd : Option ℕ) (T : Reader → Tree → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ (∀ B ∈ Bd, n ≤ B) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (T rd)

theorem CompleteAtOT.toO {k : ℕ} {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    {Bd : Option ℕ} {T : Reader → Tree → Prop} (h : CompleteAtOT fs cert k f Lin args Out Bd T) :
    CompleteAtO fs cert k f Lin args Out Bd := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm => (hr rd hl hm).relAtIn⟩

/-- **A flat function's node**: at a valuation `σ` with `Q σ`, its body's walk returning, its callees' trees
satisfying `Ts σ rd`. -/
def FlatNodeT (f : String) (fn : Fn) (pre : List Stmt) (Q : Val → Prop) (Ts : Val → Reader → List (Tree → Prop))
    (rd : Reader) (t : Tree) : Prop :=
  ∃ (σ : Val) (bufs : List ℕ) (ks : List Tree) (es : List Ev) (vs : List V), t = .node f σ bufs ks ∧
    walk σ fn.body = .ret es vs ∧ calls es = (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) ∧ Q σ ∧
    KidsT (calls es) (Ts σ rd) ks

theorem os_kidsFromInT_rmono {rd : Reader} {σ : Val} {R R' : ℕ → Prop} (hR : ∀ i, R i → R' i) :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (Dacc : ℕ → Prop) (b n : ℕ) (D : ℕ → Prop),
      KidsFromInT coreProgram fs cert rd σ R Dacc cs Ts b n D →
        KidsFromInT coreProgram fs cert rd σ R' Dacc cs Ts b n D
  | [], _, _, _, _, _, h => h
  | _ :: cs, Ts, _, _, _, _, ⟨m, n', Rk, Dk, hn, hRk, hc, hk⟩ =>
    ⟨m, n', Rk, Dk, hn, fun i hi => (hRk i hi).imp_left (hR i), hc, os_kidsFromInT_rmono hR cs Ts.tail _ _ _ _ hk⟩

theorem os_kidsFromIn_toT_nil {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (Dacc : ℕ → Prop) (b n : ℕ) (D : ℕ → Prop),
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n D → KidsFromInT coreProgram fs cert rd σ R Dacc cs [] b n D
  | [], _, _, _, _, h => h
  | c :: cs, _, _, _, _, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ => by
    refine ⟨m, n', Rk, Dk, hn, hR, ?_, os_kidsFromIn_toT_nil cs _ _ _ _ hk⟩
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hc ⊢
      exact hc.relAtInT
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc ⊢
      exact hc

/-- **`os_completeAt_placeJF` at an optional words bound, by its node**: within `B` when the frame, the
buffers and the callees' total are; the tree the node at the valuation, its callees' trees satisfying
`Ts σ rd`. -/
theorem os_completeAt_placeJFOT {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E)
    (Out : List E → Layout → Prop) (Bd : Option ℕ) {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (js : List ℕ) (hjs : js.Nodup) (hjl : ∀ j ∈ js, j < sizes.length)
    {C : CallRel} (Q : Val → Prop) (Ts : Val → Reader → List (Tree → Prop))
    (h : ∀ fp, ∃ (σ : Val) (own : List (List E)) (rets : List E) (N : ℕ) (L : Layout)
      (Dk : ℕ → Prop) (cs : List Call),
      (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) = cs ∧ (∀ s ∈ pre, DispOk σ s) ∧ Q σ ∧
      List.Forall₂ (fun c s => c.length ≤ s) own sizes ∧
      Out rets (osLoutJ (fp + fs f) sizes own js) ∧
      Within L (fp + fs f + sizes.sum) N ∧ DisjL L ∧ (∀ B ∈ Bd, fs f + sizes.sum + N ≤ B) ∧
      fn.params.map σ = args ∧
      (∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd Lin →
        Stmt.HoldsList C rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b))) ∧
      ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd L → MemL rd Lin →
        KidsFromInT coreProgram fs cert rd σ
          (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes own) i)
          (fun _ => False) cs (Ts σ rd) (fp + fs f + sizes.sum) N Dk) :
    CompleteAtOT fs cert κ f Lin args Out Bd (FlatNodeT f fn pre Q Ts) := by
  intro fp
  obtain ⟨σ, own, rets, N, L, Dk, cs, hcs, hdo, hQ, hown, hout, hW, hD, hBd, hp, hh, hK⟩ := h fp
  set B := bufL (fp + fs f) sizes own with hB
  have hBlen : B.length = sizes.length := by
    simp only [hB, bufL, List.length_zip, os_length_bases, hown.length_eq, Nat.min_self]
  have hLo : osLoutJ (fp + fs f) sizes own js = js.map (fun j => B.getD j default) := by
    unfold osLoutJ
    refine List.map_congr_left fun j hj => ?_
    rw [hB, os_bufL_getD hown (hjl j hj), os_bases_getD _ _ _ (hjl j hj)]
  set Lo := osLoutJ (fp + fs f) sizes own js with hLod
  set Lr : Layout := ((List.range B.length).filter (fun j => decide (j ∉ js))).map
    (fun j => B.getD j default)
  have hperm0 : (Lo ++ Lr).Perm B := by
    rw [hLo]; exact os_perm_pick B default js hjs fun j hj => hBlen ▸ hjl j hj
  have hperm : (Lo ++ (Lr ++ L)).Perm (B ++ L) := by
    rw [← List.append_assoc]; exact hperm0.append_right L
  have hmem : ∀ q, q ∈ Lo ++ (Lr ++ L) ↔ q ∈ B ++ L := fun q => hperm.mem_iff
  have hBW : Within B (fp + fs f) sizes.sum := bufL_within _ _ _ hown
  have hBD : DisjL B := bufL_disj _ _ _ hown
  have hBL : DisjL (B ++ L) := disj_append hBD hD hBW hW le_rfl
  refine ⟨fs f + sizes.sum + N, Lr ++ L, rets, Lo, hout, fun q hq => ?_, ?_, hBd, fun rd hlow hL => ?_⟩
  · rcases List.mem_append.mp ((hmem q).mp hq) with hq | hq
    · have := hBW q hq; omega
    · have := hW q hq; omega
  · exact hBL.perm hperm.symm fun h => Or.symm h
  have hLm : MemL rd (B ++ L) := fun q hq => hL q (List.mem_append_left _ ((hmem q).mpr hq))
  have hLin : MemL rd Lin := fun q hq => hL q (List.mem_append_right _ hq)
  obtain ⟨hB1, hL1⟩ := Main.memL_append.mp hLm
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, -⟩ := flat_parts σ pre hst
  have hsat : ∀ rd', LowDef κ rd' → MemL rd' B → MemL rd' Lin →
      (∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd' σ) ∧ vs.map σ = rets := fun rd' h1 h2 h3 => by
    have hs := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf))
      (hh rd' h1 h2 h3).1
    rw [hw] at hs
    exact ⟨fun e he => (hs.1 e he).1, hs.2⟩
  obtain ⟨hes, hr⟩ := hsat rd hlow hB1 hLin
  obtain ⟨-, hsz, hbuf⟩ := hh rd hlow hB1 hLin
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL B i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ)))
        (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ hown i hi)
  have hk := os_kidsFromInT_rmono (fs := fs) (cert := cert)
    (R' := fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ)))
        (pre.flatMap (flEvs σ)) i)
    (fun i hi => hi.imp_right (hown' i)) _ _ _ _ _ _ (hK rd hlow hB1 hL1 hLin)
  rw [← hcs, ← i4, show fp + fs f + sizes.sum =
    fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum by rw [hal]] at hk
  have hrel := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert)
    (R := RegionL Lin) (D := RegionL Lo) (Dk := Dk) (N := N) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr
    hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp) _ hk (fun A hA => ?_) (fun i hi => ?_)
  · obtain ⟨t, ht, ks, rfl, hkT⟩ := hrel
    rw [hal] at ht
    exact ⟨_, ht, σ, _, ks, _, vs, rfl, hw, by rw [i4], hQ, hkT⟩
  · obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
    match e, hea with
    | .atom (.load d p off), hea =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      subst hea
      have hall : ∀ rd', LowDef κ rd' → MemL rd' (B ++ Lin) →
          rd' ((σ p).limb 0 * addressOfIndex off) = some (σ d) := fun rd' h1 h2 => by
        obtain ⟨h21, h22⟩ := Main.memL_append.mp h2
        exact ((hsat rd' h1 h21 h22).1 _ he).2
      obtain ⟨i, hi, hreg⟩ := os_addr_in_regionL hall hlow (Main.memL_append.mpr ⟨hB1, hLin⟩)
      refine ⟨i, hi, ?_⟩
      obtain ⟨q, hq, h1, h2⟩ := hreg
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (hown' i ⟨q, hq, h1, h2⟩)
      · exact Or.inr (Or.inl ⟨q, hq, h1, h2⟩)
  · obtain ⟨q, hq, h1, h2⟩ := hi
    have hqB : q ∈ B := hperm0.subset (List.mem_append_left _ hq)
    exact Or.inl (hown' i ⟨q, hqB, h1, h2⟩)

/-- **`os_completeAt_placeJF` at an optional words bound**: within `B` when the frame, the buffers
and the callees' total are. -/
theorem os_completeAt_placeJFO {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E)
    (Out : List E → Layout → Prop) (Bd : Option ℕ) {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (js : List ℕ) (hjs : js.Nodup) (hjl : ∀ j ∈ js, j < sizes.length)
    {C : CallRel}
    (h : ∀ fp, ∃ (σ : Val) (own : List (List E)) (rets : List E) (N : ℕ) (L : Layout)
      (Dk : ℕ → Prop) (cs : List Call),
      (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) = cs ∧ (∀ s ∈ pre, DispOk σ s) ∧
      List.Forall₂ (fun c s => c.length ≤ s) own sizes ∧
      Out rets (osLoutJ (fp + fs f) sizes own js) ∧
      Within L (fp + fs f + sizes.sum) N ∧ DisjL L ∧ (∀ B ∈ Bd, fs f + sizes.sum + N ≤ B) ∧
      fn.params.map σ = args ∧
      (∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd Lin →
        Stmt.HoldsList C rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b))) ∧
      ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd L → MemL rd Lin →
        KidsFromIn coreProgram fs cert rd σ
          (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes own) i)
          (fun _ => False) cs (fp + fs f + sizes.sum) N Dk) :
    CompleteAtO fs cert κ f Lin args Out Bd :=
  (os_completeAt_placeJFOT hf hl κ Lin args Out Bd hb hst haddrs sizes js hjs hjl (C := C) (fun _ => True)
    (fun _ _ => []) fun fp =>
      let ⟨σ, own, rets, N, L, Dk, cs, hcs, hdo, hown, hout, hW, hD, hBd, hp, hh, hK⟩ := h fp
      ⟨σ, own, rets, N, L, Dk, cs, hcs, hdo, trivial, hown, hout, hW, hD, hBd, hp, hh,
        fun rd hl hB hL hLin => os_kidsFromIn_toT_nil _ _ _ _ _ (hK rd hl hB hL hLin)⟩).toO

end
end LeanVM.Guest.B1
