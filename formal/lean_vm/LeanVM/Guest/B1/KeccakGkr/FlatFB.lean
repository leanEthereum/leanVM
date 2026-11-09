/-
  LeanVM.Guest.B1.KeccakGkr.FlatFB

  `completeAt_flatOutF` within a bound (`CompleteAtFB`): the function's frame, its buffers and its
  callees' bounds.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.FlatF
public import LeanVM.Guest.Budget.Bounded

/-!
# Flat bodies at the frame pointer, within a bound

`completeAt_flatOutFB` is `completeAt_flatOutF` with each entered callee complete within
`bd k` words (`CompleteAtB`) and the callees' words (`kidsBound fs bd`: an entered call's bound,
a skipped call's frame) at most `NB` at every frame pointer: the function is complete within
`fs f + sizes.sum + NB` words (its frame, its buffers, its callees). The proof is
`completeAt_flatOutF`'s, with `kidsFromIn_of_kidsB` for `kidsFromIn_of_kidsD`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem CompleteAtFB.mono_bound {k : ℕ} {f : String} {Lin : ℕ → Layout} {args : List E}
    {Out : ℕ → List E → Layout → Prop} {B B' : ℕ} (h : CompleteAtFB fs cert k f Lin args Out B)
    (hB : B ≤ B') : CompleteAtFB fs cert k f Lin args Out B' := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, le_trans hn hB, ho, hw, hd, hr⟩

/-- **`completeAt_flatOutF` within `fs f + sizes.sum + NB` words**: the callees within `bd`, their
words (`kidsBound`) within `NB` at every frame pointer. -/
theorem completeAt_flatOutFB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : ℕ → Layout) (args : List E) (rets : ℕ → List E)
    (Out : ℕ → List E → Layout → Prop)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hnl : pre.all noLoadIte = true)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hout : ∀ fp, Out fp (rets fp) (bufL (fp + fs f) sizes (own fp))) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (NB : ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k))
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
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL (Lin fp) i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) :
    CompleteAtFB fs cert κ f Lin args Out (fs f + sizes.sum + NB) := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, hNB, -, hK⟩ := kidsFromIn_of_kidsB (fs := fs) (cert := cert) κ bd
    (kids fp) (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, L, rets fp, bufL (fp + fs f) sizes (own fp),
    by have := hkB fp; omega, hout fp, ?_,
    disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    fun rd hlow hL => ?_⟩
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
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL (Lin fp) i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL (Lin fp))
    (D := RegionL (bufL (fp + fs f) sizes (own fp)))
    (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp)
    hk (fun A hA => ?_) (fun i hi => Or.inl (hown' i hi))
  · rw [hal] at h
    exact h
  · rw [i5, flatMap_loadsEv σ pre hnl] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

end
end LeanVM.Guest.B1
