/-
  LeanVM.Guest.B1.Tables.VtCStraightB

  A pure function and a function with one branch, complete by bounded trees (`CompleteAtB`).
-/

module

public import LeanVM.Guest.B1.Tables.GkrIteAt
public import LeanVM.Guest.B1.Main.WeightB

/-!
# Bounded trees: pure callees and one branch

`completeAt_of_rel_lowD` and `completeAt_iteD` with the tree's size bounded
(`vtc_completeAt_of_rel_lowB`, `vtc_completeAt_iteB`): a pure callee by a bound on its valid trees
on every memory holding the caller's words, a function with one branch by its frame, its
`HeapBuf`s and its callees' bounds.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL CompleteAtW kidsBoundW kidsWs kidsWs_sum
  kidsFromInW_of_kidsBW relAtInW_of_walk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}

/-- **`completeAt_of_rel_lowD` by a bounded tree**: the bound on every valid tree of `g` with its
paths' `HeapBuf`s, on every memory holding `Lin`. -/
theorem vtc_completeAt_of_rel_lowB {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) {Lin : Layout} {args rets : List E} (k : ℕ)
    (h : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → coreProgram.Rel rd' g args rets) {B : ℕ}
    (hB : ∀ rd, MemL rd Lin → ∀ (t : Tree) (rets' : List E), t.name = g →
      t.Valid coreProgram rd args rets' → t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtB fs cert k g Lin args (Returns rets) B := by
  intro fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, h1⟩ := hex
  set rd0 := Main.restrict rd1 (RegionL Lin)
  have h0 : MemL rd0 Lin := Main.memL_restrict h1 fun i hi => hi
  have hsupp := Main.restrict_supp' rd1 (RegionL Lin)
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (Main.relIn_of_rel_supp coreProgram_wf hsupp
      (h rd1 hl1 h1 rd0 fun i hi => Main.restrict_of ⟨i, rfl, hi⟩))
  have hnB : n ≤ B := by
    obtain ⟨t, hname, hv, hbo, -, ht, -⟩ := hn fp rd0 (fun _ _ => rfl) (fun _ h => h)
    rw [← ht]; exact hB rd0 h0 t rets hname hv hbo
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, hnB, fun rd _ hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtIn_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [Main.memL_agree hL' h1 i hi, Main.restrict_of ⟨i, rfl, hi⟩]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi⟩ := hsupp _ _ hv
    rw [Main.memL_agree hL' h1 i hi, ← Main.restrict_of (rd := rd1) (S := RegionL Lin) ⟨i, rfl, hi⟩, hv]
    rfl
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

/-- **`vtc_completeAt_of_rel_lowB` within weights**: the bound on the valid trees' words at every
frame size, at `w θ`. -/
theorem vtc_completeAt_of_rel_lowW {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) {Lin : Layout} {args rets : List E} (k : ℕ)
    (h : ∀ rd, LowDef k rd → MemL rd Lin → ∀ rd' : Reader,
      (∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) → coreProgram.Rel rd' g args rets)
    {B : (String → ℕ) → ℕ}
    (hB : ∀ (fs' : String → ℕ) rd, MemL rd Lin → ∀ (t : Tree) (rets' : List E), t.name = g →
      t.Valid coreProgram rd args rets' → t.BufsOk coreProgram → t.total fs' ≤ B fs') :
    CompleteAtW fs cert w k g Lin args (Returns rets) (B fs) fun θ => B (w θ) :=
  Main.CompleteAtB.toW_memTot (vtc_completeAt_of_rel_lowB hS hg k h (hB fs)) fun θ => hB (w θ)

/-- **A function with one branch is complete, placed, by a bounded tree within weights**: `completeAt_iteD` with
its callees bounded by `bd`, at most `Bk` together. -/
theorem vtc_completeAt_iteW {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre t e post : List Stmt} {c : V} {vs : List V}
    (hb : fn.body = pre ++ .ite c t e :: (post ++ [.ret vs]))
    (h1 : pre.all Main.Stmt.straight = true) (h2 : t.all Main.Stmt.straight = true)
    (h3 : e.all Main.Stmt.straight = true) (h4 : post.all Main.Stmt.straight = true) (br : Bool)
    (haddrs : (pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (Bk : ℕ) (Bkw : Θ → ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true →
      CompleteAtW fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k))
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, (σ c = 0 ↔ br = true) ∧ fn.params.map σ = args ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets) ∧
        ((pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.allocSz).map
          (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        (((pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ (((pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.callS).map
          (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ (pre ++ (if br then t else e) ++ post).filterMap Stmt.loadS, ∃ i,
          (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i))
    (hbd : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk) (hbdw : ∀ fp θ, kidsBoundW bdw (kids fp) θ ≤ Bkw θ) :
    CompleteAtW fs cert w κ f Lin args (Returns rets) (fs f + sizes.sum + Bk) fun θ => w θ f + Bkw θ := by
  intro fp
  obtain ⟨N, L, outs, ho, hW, hD, hNb, -, hK⟩ := kidsFromInW_of_kidsBW (fs := fs) (cert := cert) (w := w) κ bd bdw (kids fp)
    (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    by have := hbd fp; omega, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hc, hp, hh, hsz, hbuf, hcm, hld⟩ := hσ fp outs ho rd hlow hB hLin
  set lin := pre ++ (if br then t else e) ++ post with hlin
  have hbr : (if σ c = 0 then t else e) = (if br then t else e) := by
    by_cases h : σ c = 0
    · rw [ite_pos' h, ite_pos' (hc.mp h)]
    · rw [ite_neg' h, ite_neg' (fun h' => h (hc.mpr h'))]
  have hst : lin.all Main.Stmt.straight = true := by
    simp only [hlin, List.all_append, h1, h4, Bool.and_true, Bool.true_and]
    split <;> assumption
  set es := iteEvs σ pre (if br then t else e) post c with hes_def
  have hw : walk σ fn.body = .ret es vs := by rw [hb, walk_ite σ vs c pre t e post h1 h2 h3 h4, hbr]
  obtain ⟨j1, j2, j3, j4, j5⟩ := iteEvs_parts σ pre (if br then t else e) post c
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ lin hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ es, e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  have hal : allocs σ es = sizes := by rw [j2, i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ es) es i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls es) (fun i => RegionL Lin i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
    (fun _ => False) (by rw [j4, i4]; exact hcm) hlow hLk (memL_lins (hkm fp rd hB hLin))
    (regionsOk_of fun k hk ht i hi => Or.inl ((hkr fp k hk ht i hi).imp_right (hown' i)))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ es).sum := by rw [hal]
  rw [hb'] at hk
  have h := relAtInW_of_walk (fs := fs) (cert := cert) (w := w) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    hf (Or.inl hl) hp hw hr hes (by rw [hal, j1, i1]; exact hbuf)
    (by rw [j3, i3, haddrs]; simp) hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    rw [kidsWs_sum]
    exact Nat.add_le_add_left (hbdw fp θ) _
  · rw [j5, loadAddrs_straight σ lin hst] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

/-- **A function with one branch is complete, placed, by a bounded tree**: `completeAt_iteD` with
its callees bounded by `bd`, at most `Bk` together. -/
theorem vtc_completeAt_iteB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre t e post : List Stmt} {c : V} {vs : List V}
    (hb : fn.body = pre ++ .ite c t e :: (post ++ [.ret vs]))
    (h1 : pre.all Main.Stmt.straight = true) (h2 : t.all Main.Stmt.straight = true)
    (h3 : e.all Main.Stmt.straight = true) (h4 : post.all Main.Stmt.straight = true) (br : Bool)
    (haddrs : (pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (bd : Kid → ℕ) (Bk : ℕ)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k))
    (hkr : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ i, RegionL k.Lin i →
      RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i)
    (hkm : ∀ fp rd, MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin → ∀ k ∈ kids fp,
      MemL rd k.Lin)
    (hσ : ∀ fp (outs : List (List E × Layout)), OutsOk (kids fp) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ σ : Val, (σ c = 0 ↔ br = true) ∧ fn.params.map σ = args ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun r => r = rets) ∧
        ((pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.allocSz).map
          (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        (((pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        CallsMatch σ (((pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.callS).map
          (Main.mkCall σ)) (kids fp) outs ∧
        ∀ q ∈ (pre ++ (if br then t else e) ++ post).filterMap Stmt.loadS, ∃ i,
          (σ q.1).limb 0 * gpow q.2 = gpow i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i))
    (hbd : ∀ fp, kidsBound fs bd (kids fp) ≤ Bk) :
    CompleteAtB fs cert κ f Lin args (Returns rets) (fs f + sizes.sum + Bk) :=
  (vtc_completeAt_iteW (Θ := Empty) (w := fun e => e.elim) hf hl κ Lin args rets hb h1 h2 h3 h4 br haddrs sizes own
    hown kids bd (fun _ e => e.elim) Bk (fun e => e.elim) (fun fp k hk ht => Main.CompleteAtB.toWE (hkc fp k hk ht))
    hkr hkm hσ hbd (fun _ e => e.elim)).toB

end
end LeanVM.Guest.B1
