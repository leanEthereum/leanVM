/-
  LeanVM.Guest.B1.Tables.FlatAtTE

  `completeAt_flatDTBR` with callees' predicates of the memory (`completeAt_flatDTBRR`), and a node of honest shape
  exact at every node (`CompleteAtDTBR.nodeEvery`).
-/

module

public import LeanVM.Guest.B1.Tables.FlatAtT
public import LeanVM.Guest.Budget.BoundedR
public import LeanVM.Guest.Exact.Kids

/-!
# Flat bodies, placed, callees' predicates of the memory

`completeAt_flatDTBRR`: `completeAt_flatDTBR`, the callees complete by trees of `Ts rd` on each memory `rd`
(`KidsDTBR`). `CompleteAtDTBR.nodeEvery`: a tree of honest shape whose function's computed hints are pinned by the
next atom, its callees' predicates giving `Every (ExactAt …)`, is exact at every node.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`completeAt_flatDTBR` with callees' predicates of the memory**: each entered callee's tree satisfies its
predicate of `Ts rd` on each memory `rd` (`KidsDTBR`). -/
theorem completeAt_flatDTBRR {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (Q : Reader → Val → Prop) (Ts : Reader → List (Tree → Prop)) (Bs : List ℕ) (KB : ℕ)
    (hkc : ∀ fp, KidsDTBR fs cert κ (kids fp) Ts Bs) (hKB : ∀ fp, kidsBoundL fs (kids fp) Bs ≤ KB)
    (hkl : ∀ fp rd, (kids fp).length ≤ (Ts rd).length)
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
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ (flatCalls pre σ) (kids fp) outs ∧
        (∀ q ∈ pre.flatMap (loadsEv σ), ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)) ∧ Q rd σ) :
    CompleteAtDTBR fs cert κ f Lin args (Returns rets)
      (fun rd ↦ Budget.NodeHonest coreProgram f (Q rd) (flatCalls pre) (fun _ ↦ sizes) (Ts rd)) (fs f + sizes.sum + KB) := by
  intro fp
  obtain ⟨N, L, outs, hNB, ho, hW, hD, -, hK⟩ := kidsFromInT_of_kidsDTBR (fs := fs) (cert := cert) κ
    (kids fp) Ts Bs (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [],
    by have := hKB fp; omega, ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld, hQ⟩ := hσ fp outs ho rd hlow hB hLin
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
  have hload : ∀ A ∈ loadAddrs σ (pre.flatMap (flEvs σ)), ∃ i, A = addressOfIndex i ∧
      (ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i ∨
        RegionL Lin i ∨ (False ∨ outRegion (kids fp) outs i)) := by
    intro A hA
    rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩
  obtain ⟨t, ht, ks, rfl, hkT⟩ := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert)
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i)
    (N := N) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf)
    (by rw [i3, haddrs]; simp) (Ts rd) hk hload (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rw [hal] at ht
  refine ⟨_, ht, σ, ks, rfl, hQ, fun fn' es' vs' hf' hw' => ?_, ?_, ?_⟩
  · rw [hf, Option.some.injEq] at hf'
    subst hf'
    rw [hw, Out.ret.injEq] at hw'
    rw [← hw'.1, i4]
    rfl
  · exact (callsMatch_length hcm).trans_le (hkl fp rd)
  · rw [i4] at hkT; exact hkT


/-- **A tree of honest shape, exact at every node**: its function's computed hints pinned by the next atom, each
callee's predicate giving `Every (ExactAt …)` on its valid trees. -/
theorem CompleteAtDTBR.nodeEvery {κ : ℕ} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hpin : Stmt.blockNextOk isComputed pinsInverse fn.body = true) {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {Q : Reader → Val → Prop} {cs : Val → List Call} {bs : Val → List ℕ}
    {Ts : Reader → List (Tree → Prop)} {B : ℕ}
    (h : CompleteAtDTBR fs cert κ f Lin args Out (fun rd ↦ Budget.NodeHonest coreProgram f (Q rd) cs bs (Ts rd)) B)
    (hT : ∀ rd σ, Q rd σ → ∀ c T, (c, T) ∈ (cs σ).zip (Ts rd) → c.taken = true → ∀ t : Tree, t.name = c.f →
      t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ) → T t → t.Every (ExactAt coreProgram rd)) :
    CompleteAtDTBR fs cert κ f Lin args Out
      (fun rd t ↦ Budget.NodeHonest coreProgram f (Q rd) cs bs (Ts rd) t ∧ t.Every (ExactAt coreProgram rd)) B :=
  fun fp =>
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
    ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
      let ⟨t, ht, hH⟩ := hr rd hl hm
      ⟨t, ht, hH, hH.every ht.2.1 (fun _ _ _ hv => exactAt_of_body hf hpin hv rd) (hT rd)⟩⟩

end
end LeanVM.Guest.B1
