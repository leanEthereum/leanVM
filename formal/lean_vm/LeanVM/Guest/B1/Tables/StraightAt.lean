/-
  LeanVM.Guest.B1.Tables.StraightAt

  A straight-line function with `HeapBuf`s and callees, complete in the uniform placed form.
-/

module

public import LeanVM.Guest.B1.Uniform

/-!
# Straight-line bodies, placed

`completeAt_straightD`: a function whose body is straight-line statements then a `ret`, with no
`frameAddr`, is `CompleteAtD` when its callees are, each reading the caller's words or its
`HeapBuf`s, and at every frame pointer, on every memory holding its buffers' honest words and the
caller's, a valuation satisfies its body with the allocator's pointers, frames matching the
callees, and loads from its buffers or the caller's words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A straight-line function is complete, placed.** -/
theorem completeAt_straightD {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out)
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
    CompleteAtD fs cert κ f Lin args (Returns rets) := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, -, hK⟩ := kidsFromIn_of_kidsD (fs := fs) (cert := cert) κ (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    fun rd hlow hL => ?_⟩
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
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h
    exact h
  · rw [loadAddrs_straight σ pre hst] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

/-! ## Words the caller's layout holds -/

/-- **A word every memory holding `Lin` holds lies in `Lin`'s region.** -/
theorem addr_in_region {κ : ℕ} {Lin : Layout} {p : E} {xs : List E}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd p xs) {rd : Reader} (hlow : LowDef κ rd)
    (hL : MemL rd Lin) {j : ℕ} (hj : j < xs.length) :
    ∃ i, p.limb 0 * gpow j = gpow i ∧ RegionL Lin i := by
  classical
  by_contra hn
  simp only [not_exists, not_and] at hn
  set A := p.limb 0 * gpow j
  let rd2 : Reader := fun B => if B = A then some (xs[j] + 1) else rd B
  have hlow2 : LowDef κ rd2 := fun i hi => by
    simp only [rd2]; split
    · rfl
    · exact hlow i hi
  have hL2 : MemL rd2 Lin := by
    intro q hq k hk
    refine ⟨(hL q hq k hk).1, ?_⟩
    rw [Main.addr_ofK]
    have hne : gpow (q.1 + k) ≠ A := fun he => hn (q.1 + k) he.symm ⟨q, hq, by omega, by omega⟩
    simp only [rd2, hne, ↓reduceIte]
    rw [← Main.addr_ofK]; exact (hL q hq k hk).2
  have := (hall rd2 hlow2 hL2 j hj).2
  rw [show rd2 A = some (xs[j] + 1) from by simp [rd2]] at this
  simp only [Option.some.injEq] at this
  exact one_ne_zero (by linear_combination this : (1 : E) = 0)

/-- A load whose address lies in a region reads the same on two memories agreeing there. -/
theorem loadHolds_agree {R : ℕ → Prop} {rd rd' : Reader} (hag : ∀ i, R i → rd' (gpow i) = rd (gpow i))
    {p v : E} {k : ℕ} (h : LoadHolds rd p k v) (hR : ∃ i, p.limb 0 * gpow k = gpow i ∧ R i) :
    LoadHolds rd' p k v := by
  obtain ⟨i, hi, hr⟩ := hR
  exact ⟨h.1, by rw [hi, hag i hr, ← hi]; exact h.2⟩

/-- **A pure function complete on every memory agreeing with an honest one on `Lin`'s region**
is `CompleteAt`, returning `rets` and no buffer. -/
theorem completeAt_of_rel_lowD {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) {Lin : Layout} {args rets : List E} (k : ℕ)
    (h : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → coreProgram.Rel rd' g args rets) :
    CompleteAtD fs cert k g Lin args (Returns rets) := by
  intro fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, h1⟩ := hex
  set rd0 := Main.restrict rd1 (RegionL Lin)
  have hsupp := Main.restrict_supp' rd1 (RegionL Lin)
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (Main.relIn_of_rel_supp coreProgram_wf hsupp
      (h rd1 hl1 h1 rd0 fun i hi => Main.restrict_of ⟨i, rfl, hi⟩))
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd _ hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtIn_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [Main.memL_agree hL' h1 i hi, Main.restrict_of ⟨i, rfl, hi⟩]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi⟩ := hsupp _ _ hv
    rw [Main.memL_agree hL' h1 i hi, ← Main.restrict_of (rd := rd1) (S := RegionL Lin) ⟨i, rfl, hi⟩, hv]
    rfl
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-- **Frames matching callees, index by index.** -/
theorem callsMatch_of (σ : Val) : ∀ (cs : List Call) (ks : List Kid) (outs : List (List E × Layout)),
    cs.length = ks.length → OutsOk ks outs →
    (∀ i (h1 : i < cs.length) (h2 : i < ks.length) (h3 : i < outs.length),
      cs[i].f = ks[i].f ∧ cs[i].taken = ks[i].taken ∧ (ks[i].taken = true →
        cs[i].args.map σ = ks[i].args ∧ (ks[i].Out outs[i].1 outs[i].2 → cs[i].rets.map σ = outs[i].1))) →
    CallsMatch σ cs ks outs
  | [], [], [], _, _, _ => trivial
  | c :: cs, k :: ks, o :: os, hl, ⟨ho, hos⟩, h => by
    obtain ⟨h1, h2, h3⟩ := h 0 (by simp) (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h1 h2 h3
    refine ⟨h1, h2, fun ht => ⟨(h3 ht).1, (h3 ht).2 (ho ht)⟩,
      callsMatch_of σ cs ks os (by simpa using hl) hos fun i a b d => ?_⟩
    have := h (i + 1) (by simp; omega) (by simp; omega) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    exact this
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | [], [], _ :: _, _, ho, _ => ho.elim
  | _ :: _, _ :: _, [], _, ho, _ => ho.elim

end
end LeanVM.Guest.B1
