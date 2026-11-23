/-
  LeanVM.Guest.B1.Terminal.KidsDepBP

  `KidsDepBT`'s lift with the callees' own tree predicates: a flat function with dependent
  callees, each complete within its bound by a tree satisfying its predicate, is complete within
  its bound by a node whose `j`-th entered callee is a call of its `j`-th name within its `j`-th
  bound satisfying its `j`-th predicate.
-/

module

public import LeanVM.Guest.B1.Terminal.KidsDepBT

/-!
# Dependent callees within their bounds, by name, with predicates

`KidsDepBP fs cert κ ks Bs Ps`: `KidsDepB` with callee `j`, entered, `CompleteAtDTB` by trees of
`Ps[j]`. `namedP fs names Bs Ps`: callee `j`'s tree a call of `names[j]` within `Bs[j]` words
satisfying `Ps[j]`. `kidsFromInT_of_depBP`, `completeAt_flatDepRBP`: `kidsFromInT_of_depB`,
`completeAt_flatDepRBT` with them. `KidsDepB.toBP`: callees within their bounds, by trees of
`True` (`CompleteAtB.toDTB`).

The same with predicates of the memory (`CompleteAtDTBR`, `Budget/Bounded`; `KidsDepBPR`, `kidsFromInT_of_depBPR`), a tree's pops being read through it: `completeAt_flatDepRBPR` also gives the node's valuation a property `Qn` the obligations prove of it on each memory (the honest valuation, its own buffers held).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The dependent callees within their bounds by trees of their predicates**: callee `j`, on
every result before it, entered within `Bs[j]` words by a tree of `Ps[j]` (`CompleteAtDTB`),
skipped with its frame at most `Bs[j]`. -/
def KidsDepBP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    List KidD → List ℕ → List (Tree → Prop) → Prop
  | k :: ks, b :: Bs, P :: Ps => (∀ pv, ((k pv).taken = true →
        CompleteAtDTB fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out P b) ∧
      ((k pv).taken = false → fs (k pv).f ≤ b)) ∧ KidsDepBP fs cert κ ks Bs Ps
  | [], [], [] => True
  | _, _, _ => False

/-- **The dependent callees within their bounds by trees of their predicates of the memory.** -/
def KidsDepBPR (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    List KidD → List ℕ → List (Reader → Tree → Prop) → Prop
  | k :: ks, b :: Bs, P :: Ps => (∀ pv, ((k pv).taken = true →
        CompleteAtDTBR fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out P b) ∧
      ((k pv).taken = false → fs (k pv).f ≤ b)) ∧ KidsDepBPR fs cert κ ks Bs Ps
  | [], [], [] => True
  | _, _, _ => False

theorem KidsDepBPR.length {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ} {Ps : List (Reader → Tree → Prop)},
    KidsDepBPR fs cert κ ks Bs Ps → ks.length = Bs.length ∧ ks.length = Ps.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, ⟨_, hs⟩ => ⟨by simp [hs.length.1], by simp [hs.length.2]⟩
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [KidsDepBPR] at h

theorem KidsDepBP.toR {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ} {Ps : List (Tree → Prop)},
    KidsDepBP fs cert κ ks Bs Ps → KidsDepBPR fs cert κ ks Bs (Ps.map fun P _ => P)
  | [], [], [], _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h, hs⟩ => ⟨h, hs.toR⟩
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [KidsDepBP] at h

theorem map_const_eval (Ps : List (Tree → Prop)) (rd : Reader) :
    (Ps.map fun P (_ : Reader) => P).map (· rd) = Ps := by
  simp [Function.comp_def]

/-- **Callee `j` a call of `names[j]` within `Bs[j]` words satisfying `Ps[j]`.** -/
def namedP (fs : String → ℕ) : List String → List ℕ → List (Tree → Prop) → List (Tree → Prop)
  | n :: ns, b :: Bs, P :: Ps => (fun t => Budget.NamedWithin fs n b t ∧ P t) :: namedP fs ns Bs Ps
  | _, _, _ => []

theorem namedP_length : ∀ {ns : List String} {Bs : List ℕ} {Ps : List (Tree → Prop)} {m : ℕ},
    m = ns.length → m = Bs.length → m = Ps.length → (namedP fs ns Bs Ps).length = m
  | [], Bs, Ps, m, h, _, _ => by cases Bs <;> cases Ps <;> simp_all [namedP]
  | _ :: _, [], _, _, h1, h2, _ => by simp at h1 h2; omega
  | _ :: _, _ :: _, [], _, h1, _, h3 => by simp at h1 h3; omega
  | _ :: ns, _ :: Bs, _ :: Ps, m, h1, h2, h3 => by
    simp only [namedP, List.length_cons] at h1 h2 h3 ⊢
    rw [namedP_length (m := m - 1) (by omega) (by omega) (by omega)]
    omega

theorem KidsDepBP.length {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ} {Ps : List (Tree → Prop)},
    KidsDepBP fs cert κ ks Bs Ps → ks.length = Bs.length ∧ ks.length = Ps.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, ⟨_, hs⟩ => ⟨by simp [hs.length.1], by simp [hs.length.2]⟩
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [KidsDepBP] at h

/-- **Callees within their bounds, by trees of `True`.** -/
theorem KidsDepB.toBP {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ}, KidsDepB fs cert κ ks Bs →
    KidsDepBP fs cert κ ks Bs (List.replicate ks.length fun _ => True)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨fun pv => ⟨fun ht => ((h pv).1 ht).toDTB, (h pv).2⟩, hs.toBP⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [KidsDepB] at h

/-- A run within `B` words by a tree of `P`, by a call of `f`. -/
theorem relAtInT_named {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {B : ℕ} {P : Tree → Prop} (h : RelAtInT coreProgram fs cert rd R D fp n f args rets P)
    (hB : n ≤ B) :
    RelAtInT coreProgram fs cert rd R D fp n f args rets
      (fun t => Budget.NamedWithin fs f B t ∧ P t) :=
  let ⟨t, ht, hP⟩ := h
  ⟨t, ht, ⟨ht.1, by rw [ht.2.2.2.2.1]; exact hB⟩, hP⟩

theorem kidsFromInT_of_depBPR (κ : ℕ) : ∀ (ks : List KidD) (names : List String) (Bs : List ℕ)
    (Ps : List (Reader → Tree → Prop))
    (prev : List (List E × Layout)), List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) ks names →
    KidsDepBPR fs cert κ ks Bs Ps → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), N ≤ Bs.sum ∧
      outs.length = ks.length ∧
      OutsOk (kidsAt ks prev outs) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (kidsAt ks prev outs) outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (kidsAt ks prev outs) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (kidsAt ks prev outs)) → RegionsOk R Dacc (kidsAt ks prev outs) outs →
        KidsFromInT coreProgram fs cert rd σ R Dacc cs (namedP fs names Bs (Ps.map (· rd)))
          b N (fun i => Dacc i ∨ outRegion (kidsAt ks prev outs) outs i)
  | [], [], [], [], _, _, _, b => ⟨0, [], [], le_rfl, rfl, trivial, fun _ h => by simp at h, disj_nil,
      trivial, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | [], [], _ :: _, _, _, _, h, _ => by simp [KidsDepBPR] at h
  | [], [], [], _ :: _, _, _, h, _ => by simp [KidsDepBPR] at h
  | _ :: _, _ :: _, [], _, _, _, h, _ => by simp [KidsDepBPR] at h
  | _ :: _, _ :: _, _ :: _, [], _, _, h, _ => by simp [KidsDepBPR] at h
  | [], _ :: _, _, _, _, hn, _, _ => by simp at hn
  | _ :: _, [], _, _, _, hn, _, _ => by simp at hn
  | kf :: ks, nm :: names, bk :: Bs, P :: Ps, prev, hn, ⟨hok, hoks⟩, b => by
    obtain ⟨hnm, hns⟩ := List.forall₂_cons.mp hn
    by_cases ht : (kf prev).taken = true
    · obtain ⟨n, Lown, rets, Lout, hnb, hout, hw, hd, hrel⟩ := (hok prev).1 ht b
      obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, hK⟩ :=
        kidsFromInT_of_depBPR κ ks names Bs Ps (prev ++ [(rets, Lout)]) hns hoks (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, by simp only [List.sum_cons]; omega,
        by simp [hlen], ⟨fun _ => hout, ho⟩, ?_, disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [kidsAt, Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL (kf prev).Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            have h := relAtInT_named (B := bk) (hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)) hnb
            rw [hnm prev] at h ⊢
            exact h
          · refine kidsFromInT_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · have ht' : (kf prev).taken = false := by simpa using ht
      have hfb := (hok prev).2 ht'
      obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, hK⟩ :=
        kidsFromInT_of_depBPR κ ks names Bs Ps (prev ++ [([], [])]) hns hoks (b + fs (kf prev).f)
      refine ⟨fs (kf prev).f + N, L, ([], []) :: outs, by simp only [List.sum_cons]; omega,
        by simp [hlen], ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [kidsAt, Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs (kf prev).f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInT_dend cs _ _ _ _ ?_
            (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

theorem kidsFromInT_of_depBP (κ : ℕ) (ks : List KidD) (names : List String) (Bs : List ℕ)
    (Ps : List (Tree → Prop))
    (prev : List (List E × Layout)) (hn : List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) ks names)
    (hk : KidsDepBP fs cert κ ks Bs Ps) (b : ℕ) :
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), N ≤ Bs.sum ∧
      outs.length = ks.length ∧
      OutsOk (kidsAt ks prev outs) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (kidsAt ks prev outs) outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (kidsAt ks prev outs) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (kidsAt ks prev outs)) → RegionsOk R Dacc (kidsAt ks prev outs) outs →
        KidsFromInT coreProgram fs cert rd σ R Dacc cs (namedP fs names Bs Ps)
          b N (fun i => Dacc i ∨ outRegion (kidsAt ks prev outs) outs i) := by
  obtain ⟨N, L, outs, h1, h2, h3, h4, h5, h6, hK⟩ := kidsFromInT_of_depBPR κ ks names Bs _ prev hn hk.toR b
  refine ⟨N, L, outs, h1, h2, h3, h4, h5, h6, fun rd σ cs R Dacc hc hl hL hLin hR => ?_⟩
  have := hK rd σ cs R Dacc hc hl hL hLin hR
  rwa [map_const_eval] at this

/-- **`completeAt_flatDepRBT` with the callees' own predicates of the memory**: within
`fs f + sizes.sum + Bs.sum`, by a node of `f` whose `j`-th entered callee is a call of `names[j]` within `Bs[j]`
words satisfying `Ps[j]` on the memory, its valuation satisfying `Qn` there. -/
theorem completeAt_flatDepRBPR {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hni : pre.all notIteB = true)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List KidD)
    (names : List String) (Bs : List ℕ) (Ps : List (Reader → Tree → Prop)) (Qn : Reader → Val → Prop)
    (hn : ∀ fp, List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (kids fp) names)
    (hkc : ∀ fp, KidsDepBPR fs cert κ (kids fp) Bs Ps)
    (hkr : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs →
      RegionsOk (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i) (fun _ => False)
        (kidsAt (kids fp) [] outs) outs)
    (hkm : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) → MemL rd (Kid.lins (kidsAt (kids fp) [] outs)))
    (hσ : ∀ fp (outs : List (List E × Layout)), outs.length = (kids fp).length →
      OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd,
      LowDef κ rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) →
      ∃ σ : Val, Qn rd σ ∧ fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
          (kidsAt (kids fp) [] outs) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i ∨
            outRegion (kidsAt (kids fp) [] outs) outs i)) :
    CompleteAtDTBR fs cert κ f Lin args (Returns rets)
      (fun rd t => Budget.FlatShape coreProgram f (namedP fs names Bs (Ps.map (· rd))) t ∧
        ∃ σ bufs ks, t = .node f σ bufs ks ∧ Qn rd σ)
      (fs f + sizes.sum + Bs.sum) := by
  intro fp
  obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, hK⟩ := kidsFromInT_of_depBPR (fs := fs) (cert := cert) κ
    (kids fp) names Bs Ps [] (hn fp) (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], by omega, ⟨rfl, rfl⟩,
    ?_, by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  have hLo := memL_outsL hI hLk
  obtain ⟨σ, hQ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ := hσ fp outs hlen ho rd hlow hB hLin hLo
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (hkm fp outs ho rd hlow hB hLin hLo)
    ((hkr fp outs ho).mono_R fun i hi => hi.imp_right (hown' i))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  -- the number of calls
  have hcl : (calls (pre.flatMap (flEvs σ))).length ≤
      (namedP fs names Bs (Ps.map (· rd))).length := by
    rw [i4, kdbt_callsMatch_length hcm, kidsAt_length _ _ _ hlen,
      namedP_length (hn fp).length_eq (hkc fp).length.1 (by rw [List.length_map]; exact (hkc fp).length.2)]
  obtain ⟨t, ⟨htn, htv, htb, htp, htt, htl, htd⟩, ks, rfl, hkT⟩ :=
    relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kidsAt (kids fp) [] outs) outs i) (N := N)
    (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf)
    (by rw [i3, haddrs]; simp) _ hk (fun A hA => by
      rw [i5] at hA
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      obtain ⟨i, hi, h | h | h⟩ := hld q (filterMap_of_loadsEv hni hq)
      · exact ⟨i, hi, Or.inr (Or.inl h)⟩
      · exact ⟨i, hi, Or.inl (hown' i h)⟩
      · exact ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  refine ⟨_, ⟨htn, htv, htb, htp, by rw [htt, hal], htl, htd⟩, ⟨σ, _, ks, rfl,
    fun fn' es' vs' hf' hw' ↦ ?_⟩, σ, _, ks, rfl, hQ⟩
  rw [hf] at hf'
  cases hf'
  rw [hw] at hw'
  cases hw'
  exact ⟨hcl, hkT⟩


/-- **`completeAt_flatDepRBT` with the callees' own predicates**: within `fs f + sizes.sum + Bs.sum`, by
a node of `f` whose `j`-th entered callee is a call of `names[j]` within `Bs[j]` words satisfying
`Ps[j]`. -/
theorem completeAt_flatDepRBP {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hni : pre.all notIteB = true)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List KidD)
    (names : List String) (Bs : List ℕ) (Ps : List (Tree → Prop))
    (hn : ∀ fp, List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (kids fp) names)
    (hkc : ∀ fp, KidsDepBP fs cert κ (kids fp) Bs Ps)
    (hkr : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs →
      RegionsOk (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i) (fun _ => False)
        (kidsAt (kids fp) [] outs) outs)
    (hkm : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) → MemL rd (Kid.lins (kidsAt (kids fp) [] outs)))
    (hσ : ∀ fp (outs : List (List E × Layout)), outs.length = (kids fp).length →
      OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd,
      LowDef κ rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
          (kidsAt (kids fp) [] outs) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i ∨
            outRegion (kidsAt (kids fp) [] outs) outs i)) :
    CompleteAtDTB fs cert κ f Lin args (Returns rets)
      (Budget.FlatShape coreProgram f (namedP fs names Bs Ps))
      (fs f + sizes.sum + Bs.sum) :=
  (completeAt_flatDepRBPR hf hl κ Lin args rets hb hst haddrs hni sizes own hown kids names Bs
    (Ps.map fun P _ => P) (fun _ _ => True) hn (fun fp => (hkc fp).toR) hkr hkm
    fun fp outs hlen ho rd hlow hB hLin hLo =>
      let ⟨σ, h⟩ := hσ fp outs hlen ho rd hlow hB hLin hLo
      ⟨σ, trivial, h⟩).toDTB fun rd t ht => by
    rw [map_const_eval] at ht
    exact ht.1

end
end LeanVM.Guest.B1
