/-
  LeanVM.Guest.B1.Tables.GkrIteAt

  A function whose body is straight-line but for one branch, complete in the uniform placed form.
-/

module

public import LeanVM.Guest.B1.Tables.StraightAt
public import LeanVM.Guest.B1.Main.MainWalk

/-!
# One branch, placed

`completeAt_iteD`: `completeAt_straightD` for a body `pre ++ ite c t e :: post ++ [ret]`, every part
straight-line, on a branch fixed beforehand (`b`: `t` when `σ c = 0`). The path is the straight
block `pre ++ br ++ post` with the condition's `inK` between, which no frame, `HeapBuf`,
`frameAddr` or load reads.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The events of a body with one branch, the branch `br` taken. -/
noncomputable def iteEvs (σ : Val) (pre br post : List Stmt) (c : V) : List Ev :=
  pre.flatMap (Main.slEvs σ) ++ .inK c :: (br.flatMap (Main.slEvs σ) ++ post.flatMap (Main.slEvs σ))

theorem walk_ite (σ : Val) (vs : List V) (c : V) (pre t e post : List Stmt)
    (h1 : pre.all Main.Stmt.straight = true) (h2 : t.all Main.Stmt.straight = true)
    (h3 : e.all Main.Stmt.straight = true) (h4 : post.all Main.Stmt.straight = true) :
    walk σ (pre ++ .ite c t e :: (post ++ [.ret vs])) =
      .ret (iteEvs σ pre (if σ c = 0 then t else e) post c) vs := by
  rw [walk_pre_straight σ _ pre h1, walk, walk1, Main.walk_straight σ vs post h4]
  by_cases h : σ c = 0
  · rw [ite_pos' h, ite_pos' h, Main.walk_straight_fall σ t h2]
    simp [Out.pre, Out.seq, iteEvs]
  · rw [ite_neg' h, ite_neg' h, Main.walk_straight_fall σ e h3]
    simp [Out.pre, Out.seq, iteEvs]

theorem iteEvs_parts (σ : Val) (pre br post : List Stmt) (c : V) :
    allocDsts (iteEvs σ pre br post c) = allocDsts ((pre ++ br ++ post).flatMap (Main.slEvs σ)) ∧
    allocs σ (iteEvs σ pre br post c) = allocs σ ((pre ++ br ++ post).flatMap (Main.slEvs σ)) ∧
    addrs (iteEvs σ pre br post c) = addrs ((pre ++ br ++ post).flatMap (Main.slEvs σ)) ∧
    calls (iteEvs σ pre br post c) = calls ((pre ++ br ++ post).flatMap (Main.slEvs σ)) ∧
    loadAddrs σ (iteEvs σ pre br post c) = loadAddrs σ ((pre ++ br ++ post).flatMap (Main.slEvs σ)) := by
  simp only [iteEvs, allocDsts, allocs, addrs, calls, loadAddrs, List.flatMap_append,
    List.filterMap_append, List.filterMap_cons]
  simp [Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Ev.loadAddr?]

/-- **A function with one branch is complete, placed**, its branch `b` fixed by its arguments. -/
theorem completeAt_iteD {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre t e post : List Stmt} {c : V} {vs : List V}
    (hb : fn.body = pre ++ .ite c t e :: (post ++ [.ret vs]))
    (h1 : pre.all Main.Stmt.straight = true) (h2 : t.all Main.Stmt.straight = true)
    (h3 : e.all Main.Stmt.straight = true) (h4 : post.all Main.Stmt.straight = true) (br : Bool)
    (haddrs : (pre ++ (if br then t else e) ++ post).filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List Kid)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out)
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
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kids fp) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, j1, i1]; exact hbuf)
    (by rw [j3, i3, haddrs]; simp) hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h
    exact h
  · rw [j5, loadAddrs_straight σ lin hst] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩

end
end LeanVM.Guest.B1
