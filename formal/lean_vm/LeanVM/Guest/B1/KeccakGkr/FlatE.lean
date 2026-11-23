/-
  LeanVM.Guest.B1.KeccakGkr.FlatE

  `completeAt_flatOutFB` and `completeAt_flatGB` by trees exact at every node, a function's paths exact and its
  callees' trees exact.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.FlatGB
public import LeanVM.Guest.B1.KeccakGkr.FlatGI
public import LeanVM.Guest.Budget.BoundedR
public import LeanVM.Guest.Exact.Ok
public import LeanVM.Guest.Exact.Kids
public import LeanVM.Guest.B1.Tables.FlatAtT

/-!
# Flat bodies, exact

`exT rd t`: `t` exact at every node on `rd`. `CompleteAtFBT`: `CompleteAtFB` by a tree satisfying a predicate of the
memory; `CompleteAtFB.toFBE`, `CompleteAtB.toDTBE`: a callee of `ExactOk` gains `exT`.

`completeAt_flatOutFBE`, `completeAt_flatGBE`: `completeAt_flatOutFB`, `completeAt_flatGB` by trees of `exT`, given the
honest valuation's path exact (the former) or the function's paths exact (`PathExactFn`, the latter) and its callees
complete by trees of `exT` (`KidsGBT` for the latter,
`kidsFromInT_of_kidsGBT` placing them). The node is `relAtInWT_of_walk`'s, exact by `exactAt_of_walk` and
`everyKids_of_kidsT`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- A tree exact at every node on `rd`. -/
abbrev exT (rd : Reader) (t : Tree) : Prop := t.Every (ExactAt coreProgram rd)

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`CompleteAtFB` by a tree satisfying a predicate of the memory.** -/
def CompleteAtFBT (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : ℕ → Layout)
    (args : List E) (Out : ℕ → List E → Layout → Prop) (T : Reader → Tree → Prop) (B : ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), n ≤ B ∧ Out fp rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin fp) →
      RelAtInT coreProgram fs cert rd (RegionL (Lin fp)) (RegionL Lout) fp n f args rets (T rd)

theorem CompleteAtFBT.mono_bound {k : ℕ} {f : String} {Lin : ℕ → Layout} {args : List E}
    {Out : ℕ → List E → Layout → Prop} {T : Reader → Tree → Prop} {B B' : ℕ}
    (h : CompleteAtFBT fs cert k f Lin args Out T B) (hB : B ≤ B') : CompleteAtFBT fs cert k f Lin args Out T B' :=
  fun fp => let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp; ⟨n, Lown, rets, Lout, hn.trans hB, ho, hw, hd, hr⟩

/-- **`CompleteAtFBT` without its trees' predicate.** -/
theorem CompleteAtFBT.toFB {k : ℕ} {f : String} {Lin : ℕ → Layout} {args : List E}
    {Out : ℕ → List E → Layout → Prop} {T : Reader → Tree → Prop} {B : ℕ}
    (h : CompleteAtFBT fs cert k f Lin args Out T B) : CompleteAtFB fs cert k f Lin args Out B :=
  fun fp => let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
    ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm => (hr rd hl hm).relAtIn⟩

/-- **A callee of `ExactOk` complete within a bound is so by trees of `exT`.** -/
theorem CompleteAtFB.toFBE {k : ℕ} {f : String} {Lin : ℕ → Layout} {args : List E}
    {Out : ℕ → List E → Layout → Prop} {B : ℕ} (h : CompleteAtFB fs cert k f Lin args Out B) (hg : ExactOk f) :
    CompleteAtFBT fs cert k f Lin args Out exT B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht⟩ := hr rd hl hm
    ⟨t, ht, every_exact_of_ok hg ht.2.1 ht.1⟩⟩

/-- **A callee of `ExactOk` complete within a bound is so by trees of `exT`.** -/
theorem CompleteAtB.toDTBE {k : ℕ} {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    {B : ℕ} (h : CompleteAtB fs cert k f Lin args Out B) (hg : ExactOk f) :
    CompleteAtDTBR fs cert k f Lin args Out exT B := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht⟩ := hr rd hl hm
    ⟨t, ht, every_exact_of_ok hg ht.2.1 ht.1⟩⟩

/-- Calls complete within `bd` by trees of `T` are `KidsDTBR`. -/
theorem kidsDTBR_of (κ : ℕ) (T : Reader → Tree → Prop) (bd : Kid → ℕ) : ∀ ks : List Kid,
    (∀ k ∈ ks, k.taken = true → CompleteAtDTBR fs cert κ k.f k.Lin k.args k.Out T (bd k)) →
    KidsDTBR fs cert κ ks (fun rd => ks.map fun _ => T rd) (ks.map bd)
  | [], _ => trivial
  | k :: ks, h => ⟨fun ht => h k List.mem_cons_self ht,
      kidsDTBR_of κ T bd ks fun k' hk' ht => h k' (List.mem_cons_of_mem _ hk') ht⟩

theorem kidsBoundL_map (bd : Kid → ℕ) : ∀ ks : List Kid, kidsBoundL fs ks (ks.map bd) = kidsBound fs bd ks
  | [] => rfl
  | k :: ks => by
    simp only [kidsBoundL, List.map_cons, List.headD_cons, List.tail_cons, kidsBoundL_map bd ks, kidsBound,
      List.sum_cons]

/-- A node whose path is exact, its callees' trees of `exT`, is of `exT`. -/
theorem every_node_of_exact {rd : Reader} {f : String} {fn : Fn} {σ : Val} {es : List Ev} {vs : List V}
    {bufs : List ℕ} {ks : List Tree} {Ts : List (Tree → Prop)} {args rets : List E}
    (hf : coreProgram.find? f = some fn) (hw : walk σ fn.body = .ret es vs) (hex : ∀ e ∈ es, e.Exact rd σ)
    (hv : (Memory.Tree.node f σ bufs ks).Valid coreProgram rd args rets) (hl : (calls es).length ≤ Ts.length)
    (hT : ∀ T ∈ Ts, ∀ t, T t → exT rd t) (hK : KidsT (calls es) Ts ks) :
    exT rd (Memory.Tree.node f σ bufs ks) := by
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := hv
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  rw [hw, Out.ret.injEq] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  exact Tree.every_node.mpr ⟨exactAt_of_walk hf hw hex,
    everyKids_of_kidsT hkv hl hK fun _ T hc _ t _ _ hTt => hT T (List.of_mem_zip hc).2 t hTt⟩

/-- **`completeAt_flatOutFB` by trees of `exT`**: the honest valuation's path exact, its callees complete within their
bounds by trees of `exT`. -/
theorem completeAt_flatOutFBE {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : ℕ → Layout) (args : List E)
    (rets : ℕ → List E) (Out : ℕ → List E → Layout → Prop)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hnl : pre.all noLoadIte = true)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hout : ∀ fp, Out fp (rets fp) (bufL (fp + fs f) sizes (own fp))) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (NB : ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtDTBR fs cert κ k.f k.Lin k.args k.Out exT (bd k))
    (hkB : ∀ fp, kidsBound fs bd (kids fp) ≤ NB)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL (Lin fp) i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd (Lin fp) → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd (Lin fp) →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets fp) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (kids fp) outs ∧
        (∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL (Lin fp) i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) ∧
        ∀ e ∈ pre.flatMap (flEvs σ), e.Exact rd σ) :
    CompleteAtFBT fs cert κ f Lin args Out exT (fs f + sizes.sum + NB) := by
  intro fp
  obtain ⟨N, L, outs, hNB, ho, hW, hD, -, hK⟩ := kidsFromInT_of_kidsDTBR (fs := fs) (cert := cert) κ
    (kids fp) _ _ (kidsDTBR_of κ exT bd (kids fp) (hkc fp)) (fp + fs f + sizes.sum)
  rw [kidsBoundL_map] at hNB
  refine ⟨fs f + sizes.sum + N, L, rets fp, bufL (fp + fs f) sizes (own fp),
    by have := hkB fp; omega, hout fp, ?_,
    disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    fun rd hlow hL => ?_⟩
  · simp only [within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld, hex⟩ := hσ fp outs ho rd hlow hB hLin
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets fp := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL (Lin fp) i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have hlen : (calls (pre.flatMap (flEvs σ))).length ≤ ((kids fp).map fun _ => exT rd).length := by
    rw [i4, callsMatch_length hcm, List.length_map]
  obtain ⟨t, ⟨hn, hv, hbo, hpl, htot, hlo, hda⟩, ks, rfl, hkT⟩ := relAtInWT_of_walk (P := coreProgram) (fs := fs)
    (cert := cert) (R := RegionL (Lin fp)) (D := RegionL (bufL (fp + fs f) sizes (own fp)))
    (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    _ hk (fun A hA => by
      rw [i5, flatMap_loadsEv σ pre hnl] at hA
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      obtain ⟨i, hi, h | h⟩ := hld q hq
      · exact ⟨i, hi, Or.inr (Or.inl h)⟩
      · exact ⟨i, hi, Or.inl (hown' i h)⟩) (fun i hi => Or.inl (hown' i hi))
  refine ⟨_, ⟨hn, hv, hbo, hpl, by rw [htot, hal], hlo, hda⟩, every_node_of_exact hf hw hex hv hlen ?_ hkT⟩
  intro T hT t hTt
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hT
  exact hTt

/-- The entered calls are complete within their bounds `Bs` (in order), at every prefix of frame pointers, by trees
of `T`. -/
def KidsGBT (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (T : Reader → Tree → Prop) :
    List KidG → List ℕ → Prop
  | k :: ks, Bs => (k.taken = true → ∀ ps, CompleteAtFBT fs cert κ k.f (fun p => k.Lin (ps ++ [p]))
      (k.args ps) (fun p => k.Out (ps ++ [p])) T (Bs.headD 0)) ∧ KidsGBT fs cert κ T ks Bs.tail
  | [], _ => True

theorem kidsGBT_of_zip {κ : ℕ} {T : Reader → Tree → Prop} : ∀ {ks : List KidG} {Bs : List ℕ},
    ks.length = Bs.length →
    (∀ kb ∈ ks.zip Bs, kb.1.taken = true → ∀ ps, CompleteAtFBT fs cert κ kb.1.f
      (fun p ↦ kb.1.Lin (ps ++ [p])) (kb.1.args ps) (fun p ↦ kb.1.Out (ps ++ [p])) T kb.2) →
    KidsGBT fs cert κ T ks Bs
  | [], _, _, _ => trivial
  | _ :: _, [], hl, _ => by simp at hl
  | k :: ks, B :: Bs, hl, h =>
    ⟨fun ht ps ↦ h (k, B) (by simp) ht ps,
      kidsGBT_of_zip (by simpa using hl) fun kb hkb ↦ h kb (List.mem_cons_of_mem _ hkb)⟩

theorem kidsGB_zip {κ : ℕ} : ∀ {ks : List KidG} {Bs : List ℕ}, KidsGB fs cert κ ks Bs →
    ∀ kb ∈ ks.zip Bs, kb.1.taken = true → ∀ ps, CompleteAtFB fs cert κ kb.1.f
      (fun p ↦ kb.1.Lin (ps ++ [p])) (kb.1.args ps) (fun p ↦ kb.1.Out (ps ++ [p])) kb.2
  | [], _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | k :: ks, B :: Bs, ⟨h1, h2⟩, kb, hkb, ht => by
    rcases List.mem_cons.mp hkb with rfl | hkb
    · exact h1 ht
    · exact kidsGB_zip h2 kb hkb ht

/-- **`kidsFromIn_of_kidsGB` by trees of `T`.** -/
theorem kidsFromInT_of_kidsGBT (κ : ℕ) (T : Reader → Tree → Prop) : ∀ (pre : List ℕ) (ks : List KidG)
    (Bs : List ℕ), KidsGBT fs cert κ T ks Bs →
    ∀ b : ℕ, ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)) (fps : List ℕ),
      N ≤ kidsGBound fs ks Bs ∧ fps.length = ks.length ∧ (∀ p ∈ fps, b ≤ p) ∧
      OutsOk (atAllG pre ks fps) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (atAllG pre ks fps) outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (atAllG pre ks fps) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (atAllG pre ks fps)) → RegionsOk R Dacc (atAllG pre ks fps) outs →
        KidsFromInT coreProgram fs cert rd σ R Dacc cs (ks.map fun _ => T rd) b N
          (fun i => Dacc i ∨ outRegion (atAllG pre ks fps) outs i)
  | _, [], _, _, b => ⟨0, [], [], [], le_rfl, rfl, fun _ h => by simp at h, trivial, fun _ h => by simp at h,
      disj_nil, trivial, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | pre, k :: ks, Bs, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hnB, hout, hw, hd, hrel⟩ := hok.1 ht pre b
      obtain ⟨N, L, outs, fps, hNB, hlen, hge, ho, hW, hD, hI, hK⟩ :=
        kidsFromInT_of_kidsGBT κ T (pre ++ [b]) ks Bs.tail hok.2 (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, b :: fps,
        by simp only [kidsGBound, ht, ↓reduceIte]; omega, by simp [hlen],
        fun p hp => ?_, ⟨fun _ => hout, ho⟩, ?_, disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact le_rfl
        · have := hge p hp; omega
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [atAllG, Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL (k.Lin (pre ++ [b])), RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte, List.map_cons, List.headD_cons]
            rw [hf, ha, hr]
            exact hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromInT_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct, atAllG] using hR2
    · obtain ⟨N, L, outs, fps, hNB, hlen, hge, ho, hW, hD, hI, hK⟩ :=
        kidsFromInT_of_kidsGBT κ T (pre ++ [b]) ks Bs.tail hok.2 (b + fs (tailKey k.f))
      refine ⟨fs (tailKey k.f) + N, L, ([], []) :: outs, b :: fps,
        by simp only [kidsGBound, ht, Bool.false_eq_true, ↓reduceIte]; omega, by simp [hlen],
        fun p hp => ?_,
        ⟨fun h => absurd h ht, ho⟩, hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩,
        ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact le_rfl
        · have := hge p hp; omega
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [atAllG, Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs (tailKey k.f), N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · have ht' : k.taken = false := by simpa using ht
          rw [hct]
          simp only [ht', Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInT_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

/-- **`completeAt_flatGB` by trees of `exT`**: the function's paths exact, its callees within `Bs` by trees of
`exT`. -/
theorem completeAt_flatGBE {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (hpx : PathExactFn fn) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hnl : pre.all noLoadIte = true)
    (sizes : List ℕ) (own : ℕ → List ℕ → List (List E))
    (hown : ∀ fp fps, List.Forall₂ (fun c s => c.length ≤ s) (own fp fps) sizes)
    (kids : ℕ → List KidG) (Bs : List ℕ) (NB : ℕ) (hkc : ∀ fp, KidsGBT fs cert κ exT (kids fp) Bs)
    (hkB : ∀ fp, kidsGBound fs (kids fp) Bs ≤ NB)
    (hσ : ∀ fp (fps : List ℕ) (outs : List (List E × Layout)), fps.length = (kids fp).length →
      (∀ p ∈ fps, fp + fs f + sizes.sum ≤ p) → OutsOk (atAllG [] (kids fp) fps) outs →
      ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes (own fp fps)) → MemL rd Lin →
      MemL rd (takenOuts (atAllG [] (kids fp) fps) outs) →
      MemL rd (Kid.lins (atAllG [] (kids fp) fps)) ∧
      RegionsOk (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp fps)) i)
        (fun _ => False) (atAllG [] (kids fp) fps) outs ∧
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
          (atAllG [] (kids fp) fps) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp fps)) i ∨
            outRegion (atAllG [] (kids fp) fps) outs i)) :
    CompleteAtDTBR fs cert κ f Lin args (Returns rets) exT (fs f + sizes.sum + NB) := by
  intro fp
  obtain ⟨N, L, outs, fps, hNB, hlen, hge, ho, hW, hD, hI, hK⟩ := kidsFromInT_of_kidsGBT (fs := fs)
    (cert := cert) κ exT [] (kids fp) Bs (hkc fp) (fp + fs f + sizes.sum)
  have hdj := disj_append (bufL_disj _ _ _ (hown fp fps)) hD (bufL_within _ _ _ (hown fp fps)) hW
    le_rfl
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp fps) ++ L, rets, [],
    by have := hkB fp; omega, ⟨rfl, rfl⟩, ?_, by simpa using hdj, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp fps)).mono (by omega) (by omega),
      hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  have hto : MemL rd (takenOuts (atAllG [] (kids fp) fps) outs) :=
    fun q hq => hLk q (takenOuts_sub hI q hq)
  obtain ⟨hlins, hreg, σ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ :=
    hσ fp fps outs hlen hge ho rd hlow hB hLin hto
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp fps)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp fps) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk hlins
    (regionsOk_mono (fun i h => h.imp_right (hown' i)) hreg)
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have hlen' : (calls (pre.flatMap (flEvs σ))).length ≤ ((kids fp).map fun _ => exT rd).length := by
    rw [i4, callsMatch_length hcm, List.length_map, atAllG_length, hlen, Nat.min_self]
  obtain ⟨t, ⟨hn, hv, hbo, hpl, htot, hlo, hda⟩, ks, rfl, hkT⟩ := relAtInWT_of_walk (P := coreProgram) (fs := fs)
    (cert := cert) (R := RegionL Lin) (D := RegionL [])
    (Dk := fun i => False ∨ outRegion (atAllG [] (kids fp) fps) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf)
    (by rw [i3, haddrs]; simp) _ hk (fun A hA => by
      rw [i5, flatMap_loadsEv σ pre hnl] at hA
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      obtain ⟨i, hi, h | h | h⟩ := hld q hq
      · exact ⟨i, hi, Or.inr (Or.inl h)⟩
      · exact ⟨i, hi, Or.inl (hown' i h)⟩
      · exact ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  refine ⟨_, ⟨hn, hv, hbo, hpl, by rw [htot, hal], hlo, hda⟩,
    every_node_of_exact hf hw (hpx rd σ _ vs hw hes) hv hlen' ?_ hkT⟩
  intro T hT t hTt
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hT
  exact hTt

end
end LeanVM.Guest.B1
