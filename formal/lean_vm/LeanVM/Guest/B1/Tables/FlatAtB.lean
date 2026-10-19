/-
  LeanVM.Guest.B1.Tables.FlatAtB

  `completeAt_straightD`, `completeAt_flatD` and `completeAt_flatOutD` by bounded trees.
-/

module

public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Main.WeightB

/-!
# Bounded trees: straight and flat bodies

The tree is the frame, the `HeapBuf`s and the callees' trees, so it is at most
`fs f + Σ sizes + Bk` once the callees' bounds `bd` sum to at most `Bk` (`kidsFromIn_of_kidsB`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL CompleteAtW kidsBoundW kidsWs kidsWs_sum
  kidsFromInW_of_kidsBW relAtInW_of_walk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}

/-- **A straight-line function is complete, placed, by a bounded tree within weights.** -/
theorem completeAt_straightW {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (Bk : ℕ) (Bkw : Θ → ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true →
      CompleteAtW fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k))
    (hBk : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk) (hBkw : ∀ fp θ, kidsBoundW bdw (kids fp) θ ≤ Bkw θ)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ ((pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) :
    CompleteAtW fs cert w κ f Lin args (Returns rets) (fs f + sizes.sum + Bk)
      fun θ => w θ f + Bkw θ := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInW_of_kidsBW (fs := fs) (cert := cert) (w := w) κ bd bdw (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    by have := hBk fp; omega, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hp, hh, hsz, hbuf, hcm, hld⟩ := hσ fp outs ho rd hlow hB hLin
  have hw := Main.walk_straight σ vs pre hst
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  have hal : allocs σ (pre.flatMap (Main.slEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (Main.slEvs σ))) (pre.flatMap (Main.slEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (Main.slEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (Main.slEvs σ))) (pre.flatMap (Main.slEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (Main.slEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtInW_of_walk (fs := fs) (cert := cert) (w := w) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    rw [kidsWs_sum]
    exact Nat.add_le_add_left (hBkw fp θ) _
  · rw [loadAddrs_straight σ pre hst] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

/-- **A straight-line function is complete, placed, by a bounded tree.** -/
theorem completeAt_straightB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (Bk : ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k))
    (hBk : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ ((pre.filterMap Main.Stmt.callS).map (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) :
    CompleteAtB fs cert κ f Lin args (Returns rets) (fs f + sizes.sum + Bk) :=
  (completeAt_straightW (Θ := Empty) (w := fun e => e.elim) hf hl κ Lin args rets hb hst haddrs sizes own hown kids bd
    (fun _ e => e.elim) Bk (fun e => e.elim) (fun fp k hk ht => Main.CompleteAtB.toWE (hkc fp k hk ht)) hBk (fun _ e => e.elim)
    hkr hkm hσ).toB

/-- **A flat body is complete, placed, by a bounded tree within weights.** -/
theorem completeAt_flatW {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (Bk : ℕ) (Bkw : Θ → ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true →
      CompleteAtW fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k))
    (hBk : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk) (hBkw : ∀ fp θ, kidsBoundW bdw (kids fp) θ ≤ Bkw θ)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) :
    CompleteAtW fs cert w κ f Lin args (Returns rets) (fs f + sizes.sum + Bk)
      fun θ => w θ f + Bkw θ := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInW_of_kidsBW (fs := fs) (cert := cert) (w := w) κ bd bdw (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    by have := hBk fp; omega, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ := hσ fp outs ho rd hlow hB hLin
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
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtInW_of_walk (fs := fs) (cert := cert) (w := w) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    rw [kidsWs_sum]
    exact Nat.add_le_add_left (hBkw fp θ) _
  · rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

/-- **A flat body is complete, placed, by a bounded tree.** -/
theorem completeAt_flatB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (Bk : ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k))
    (hBk : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) :
    CompleteAtB fs cert κ f Lin args (Returns rets) (fs f + sizes.sum + Bk) :=
  (completeAt_flatW (Θ := Empty) (w := fun e => e.elim) hf hl κ Lin args rets hb hst haddrs sizes own hown kids bd
    (fun _ e => e.elim) Bk (fun e => e.elim) (fun fp k hk ht => Main.CompleteAtB.toWE (hkc fp k hk ht)) hBk (fun _ e => e.elim)
    hkr hkm hσ).toB

/-- **A flat body returning its `HeapBuf`s, by a bounded tree within weights.** -/
theorem completeAt_flatOutW {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E) (rets : ℕ → List E)
    (Out : List E → Layout → Prop)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hout : ∀ fp, Out (rets fp) (bufL (fp + fs f) sizes (own fp))) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (Bk : ℕ) (Bkw : Θ → ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true →
      CompleteAtW fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k))
    (hBk : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk) (hBkw : ∀ fp θ, kidsBoundW bdw (kids fp) θ ≤ Bkw θ)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets fp) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) :
    CompleteAtW fs cert w κ f Lin args Out (fs f + sizes.sum + Bk)
      fun θ => w θ f + Bkw θ := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInW_of_kidsBW (fs := fs) (cert := cert) (w := w) κ bd bdw (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, L, rets fp, bufL (fp + fs f) sizes (own fp), hout fp, ?_,
    disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    by have := hBk fp; omega, fun rd hlow hL => ?_⟩
  · simp only [within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ := hσ fp outs ho rd hlow hB hLin
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
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtInW_of_walk (fs := fs) (cert := cert) (w := w) (R := RegionL Lin)
    (D := RegionL (bufL (fp + fs f) sizes (own fp)))
    (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => Or.inl (hown' i hi))
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    rw [kidsWs_sum]
    exact Nat.add_le_add_left (hBkw fp θ) _
  · rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

/-- **A flat body returning its `HeapBuf`s, by a bounded tree.** -/
theorem completeAt_flatOutB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E) (rets : ℕ → List E)
    (Out : List E → Layout → Prop)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hout : ∀ fp, Out (rets fp) (bufL (fp + fs f) sizes (own fp))) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (Bk : ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k))
    (hBk : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk)
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets fp) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) :
    CompleteAtB fs cert κ f Lin args Out (fs f + sizes.sum + Bk) :=
  (completeAt_flatOutW (Θ := Empty) (w := fun e => e.elim) hf hl κ Lin args rets Out hb hst haddrs sizes own hown hout kids bd
    (fun _ e => e.elim) Bk (fun e => e.elim) (fun fp k hk ht => Main.CompleteAtB.toWE (hkc fp k hk ht)) hBk (fun _ e => e.elim)
    hkr hkm hσ).toB

end
end LeanVM.Guest.B1
