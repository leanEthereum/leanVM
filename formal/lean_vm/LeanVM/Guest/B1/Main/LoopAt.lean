/-
  LeanVM.Guest.B1.Main.LoopAt

  The uniform placed completeness (`CompleteAtD`) of a loop helper from its iterations, and of a
  straight-line iteration from its valuation and its callees' `CompleteAtD`.
-/

module

public import LeanVM.Guest.B1.Uniform
public import LeanVM.Guest.B1.Main.Straight

/-!
# Loops, placed

A loop helper's iteration `j` is placed at `fp`, its tail call (iteration `j + 1`, or the frame
of the call not taken) right after its frame, its own buffers and callees after the tail's
subtree. `completeAt_loop` composes the iterations from the last one down: each iteration,
given its tail's size `mt`, one size and one layout of its own words serving every memory that
holds them and the caller's words `Lin`, is complete at every `fp`.

`loopStep_straight`: an iteration of a straight-line body with no `HeapBuf` and no `frameAddr`,
whose callees before the tail are `CompleteAtD` (`Kid`s reading within `Lin`) and whose loads read `Lin`, given its valuation on every memory.

`CellL`, `regionL_of_mem`: the words of a layout and where they lie.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtD Returns Kid CallsMatch OutsOk RegionsOk outRegion
  kidsFromIn_of_kidsD relAtIn_dmono within_append)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## Layout words -/

theorem regionL_of_mem {L : Layout} {b k : ℕ} {xs : List E} (hq : (b, xs) ∈ L)
    (hk : k < xs.length) : RegionL L (b + k) :=
  ⟨(b, xs), hq, by simp, by simp only; omega⟩

theorem regionL_mono {L L' : Layout} (h : ∀ q ∈ L, q ∈ L') {i : ℕ} (hi : RegionL L i) :
    RegionL L' i :=
  let ⟨q, hq, h1, h2⟩ := hi; ⟨q, h q hq, h1, h2⟩

theorem memL_mono {rd : Reader} {L L' : Layout} (h : ∀ q ∈ L, q ∈ L') (hL : MemL rd L') :
    MemL rd L := fun q hq => hL q (h q hq)

theorem regionL_append_or {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

/-- **`L` lies within `L'`**: every memory holding `L'` holds `L`, and `L`'s words are `L'`'s. -/
def SubL (L L' : Layout) : Prop := (∀ rd, MemL rd L' → MemL rd L) ∧ ∀ i, RegionL L i → RegionL L' i

theorem SubL.of_mem {L L' : Layout} (h : ∀ q ∈ L, q ∈ L') : SubL L L' :=
  ⟨fun _ hL => memL_mono h hL, fun _ hi => regionL_mono h hi⟩

theorem SubL.append {L1 L2 L' : Layout} (h1 : SubL L1 L') (h2 : SubL L2 L') : SubL (L1 ++ L2) L' :=
  ⟨fun rd hL => memL_append.mpr ⟨h1.1 rd hL, h2.1 rd hL⟩, fun i hi =>
    (regionL_append_or hi).elim (h1.2 i) (h2.2 i)⟩

theorem SubL.trans {L1 L2 L3 : Layout} (h1 : SubL L1 L2) (h2 : SubL L2 L3) : SubL L1 L3 :=
  ⟨fun rd hL => h1.1 rd (h2.1 rd hL), fun i hi => h2.2 i (h1.2 i hi)⟩

/-- A run of an entry's words is within it. -/
theorem SubL.run {L : Layout} {b o : ℕ} {xs ys : List E} (hq : (b, ys) ∈ L)
    (hlen : o + xs.length ≤ ys.length) (h : ∀ k (hk : k < xs.length), xs[k] = ys[o + k]'(by omega)) :
    SubL [(b + o, xs)] L := by
  refine ⟨fun rd hL q hq' => ?_, fun i hi => ?_⟩
  · rw [List.mem_singleton] at hq'; subst hq'
    intro k hk
    have hk' : k < xs.length := hk
    have := hL _ hq (o + k) (by simp only; omega)
    rw [← h k hk'] at this
    refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
    rw [addr_ofK, Nat.add_assoc]
    have h2 := this.2
    rwa [addr_ofK] at h2
  · obtain ⟨q, hq', h1, h2⟩ := hi
    rw [List.mem_singleton] at hq'; subst hq'
    exact ⟨(b, ys), hq, by simp only at h1 ⊢; omega, by simp only at h2 ⊢; omega⟩

/-! ## The iterations -/

/-- **A loop helper is complete from its iterations**: iteration `j < m`, its tail of size `mt`
right after its frame (a `RelAtIn` when `j + 1 < m`, the frame of the call not taken otherwise),
is complete at every `fp` with one size and one layout of its own words from
`fp + fs f + mt`. -/
theorem completeAt_loop {f : String} (κ : ℕ) (Lin : Layout) (A : ℕ → List E) (m : ℕ)
    (step : ∀ j < m, ∀ fp mt : ℕ, ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧
      ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) →
        (j + 1 < m → RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          (A (j + 1)) []) →
        (j + 1 = m → mt = fs f) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f
          (A j) []) :
    ∀ j < m, CompleteAtD fs cert κ f Lin (A j) (Returns []) := by
  have key : ∀ t j, j + t + 1 = m → CompleteAtD fs cert κ f Lin (A j) (Returns []) := by
    intro t
    induction t with
    | zero =>
      intro j hj fp
      obtain ⟨n, L, hW, hD, hS⟩ := step j (by omega) fp (fs f)
      refine ⟨fs f + fs f + n, L, [], [], ⟨rfl, rfl⟩, ?_, by simpa using hD, fun rd hl hL => ?_⟩
      · simpa using hW.mono (by omega) (by omega)
      · refine relAtIn_dmono (hS rd hl (by simpa using hL) (fun h => by omega) (fun _ => rfl))
          fun i hi => ?_
        obtain ⟨q, hq, _⟩ := hi; simp at hq
    | succ t ih =>
      intro j hj fp
      obtain ⟨nt, Lt, rt, Lo, ⟨rfl, rfl⟩, hWt, hDt, hSt⟩ := ih (j + 1) (by omega) (fp + fs f)
      obtain ⟨n, L, hW, hD, hS⟩ := step j (by omega) fp nt
      simp only [List.nil_append] at hWt hDt
      refine ⟨fs f + nt + n, Lt ++ L, [], [], ⟨rfl, rfl⟩, ?_, by simpa using disj_append hDt hD hWt hW le_rfl,
        fun rd hl hL => ?_⟩
      · simp only [List.nil_append]
        rw [within_append]
        exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
      · simp only [List.nil_append, List.append_assoc] at hL
        obtain ⟨hL1, hL2⟩ := memL_append.mp hL
        refine relAtIn_dmono (hS rd hl hL2 (fun _ => ?_) (fun h => by omega)) fun i hi => ?_
        · refine relAtIn_dmono (hSt rd hl (by simpa using memL_append.mpr ⟨hL1, (memL_append.mp hL2).2⟩))
            fun i hi => ?_
          exact hi.elim
        · obtain ⟨q, hq, _⟩ := hi; simp at hq
  exact fun j hj => key (m - 1 - j) j (by omega)

/-! ## A straight-line iteration -/

theorem regionsOk_of_sub {R : ℕ → Prop} : ∀ (Dacc : ℕ → Prop) (ks : List Kid)
    (outs : List (List E × Layout)), (∀ k ∈ ks, ∀ i, RegionL k.Lin i → R i) →
    RegionsOk R Dacc ks outs
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | Dacc, k :: ks, o :: os, h => ⟨fun _ i hi => Or.inl (h k (by simp) i hi),
      regionsOk_of_sub _ ks os fun k' hk' => h k' (by simp [hk'])⟩

/-- **A straight-line loop iteration, placed**: the body `pre ++ [ret []]` places nothing, its
callees before the tail are the `Kid`s `ks` (each `CompleteAtD`, reading within `Lin`), and on every memory holding their words and `Lin`, for their results, a valuation
satisfies the body with the frames matching the kids and loads reading `Lin`. -/
theorem loopStep_straight {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Stmt.straight = true) (hal : pre.filterMap Stmt.allocSz = [])
    (had : pre.filterMap Stmt.addrS = []) (κ : ℕ) (Lin : Layout) (args : List E)
    (fronts : List (Option V × String × List V × List V)) (tc : V) (targs : List V)
    (hcs : pre.filterMap Stmt.callS = fronts ++ [(some tc, f, targs, [])])
    (ks : List Kid) (hks : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out)
    (hsub : ∀ k ∈ ks, ∀ q ∈ k.Lin, q ∈ Lin)
    (targs' : List E) (more : Bool) (fp mt : ℕ)
    (hσ : ∀ rd, LowDef κ rd → MemL rd Lin → ∀ outs, OutsOk ks outs → ∃ σ : Val,
      fn.params.map σ = args ∧
      Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) ∧
      CallsMatch σ (fronts.map (mkCall σ)) ks outs ∧ decide (σ tc ≠ 0) = more ∧
      targs.map σ = targs' ∧
      ∀ q ∈ pre.filterMap LeanVM.Guest.B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧ RegionL Lin i) :
    ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧
      ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) →
        (more = true → RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          targs' []) →
        (more = false → mt = fs f) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f args [] := by
  obtain ⟨N, L, outs, ho, hW, hD, -, hK⟩ := kidsFromIn_of_kidsD (fs := fs) (cert := cert) κ ks hks
    (fp + fs f + mt + 0)
  refine ⟨N, L, by simpa using hW, hD, fun rd hlow hL htail hnot => ?_⟩
  obtain ⟨hL1, hL2⟩ := memL_append.mp hL
  obtain ⟨σ, hp, hH, hcm, htk, hta, hld⟩ := hσ rd hlow hL2 outs ho
  have hwf : Stmt.wfList coreProgram fn.body = true :=
    coreProgram_wf fn (List.mem_of_find?_eq_some hf)
  have hw := walk_straight σ [] pre hs
  rw [← hb] at hw
  have hsat := walk_sat fn.body hwf hH
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ pre hs
  rw [hal] at e1 e2
  rw [had] at e3
  rw [hcs, List.map_append] at e4
  have hld' := LeanVM.Guest.B1.loadAddrs_straight σ pre hs
  have hc : (mkCall σ (some tc, f, targs, [])).taken = more := htk
  have hsumz : (allocs σ (pre.flatMap (Main.slEvs σ))).sum = 0 := by rw [e2]; rfl
  have := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := fun _ => False) (Dk := fun i => False ∨ outRegion ks outs i) (Rt := RegionL Lin)
    (Dt := fun _ => False) (fp := fp) (m := mt) (N := N) (σ := σ) (rd := rd) coreProgram_wf hf hl hp hw rfl
    (fun e he => (hsat.1 e he).1) e4 ?_ (by rw [e1, e2]; rfl) (by rw [e3]; simp) ?_
    (fun i hi => Or.inl hi) ?_ (fun i hi => hi.elim)
  · rwa [hsumz, Nat.add_zero] at this
  · cases more with
    | true =>
      simp only [hc, ↓reduceIte]
      simp only [mkCall, List.map_nil]
      rw [hta]
      exact htail rfl
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact hnot rfl
  · rw [hsumz]
    have hK' := hK rd σ _ (fun i => RegionL Lin i ∨ ownData cert fp (fp + fs f + mt) f
      (allocs σ (pre.flatMap (Main.slEvs σ))) (pre.flatMap (Main.slEvs σ)) i) (fun _ => False) hcm hlow
      hL1 (memL_mono (fun q hq => by
        obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
        exact hsub k hk q hq) hL2)
      (regionsOk_of_sub _ _ _ fun k hk i hi => Or.inl (regionL_mono (hsub k hk) hi))
    exact hK'
  · intro A hA
    rw [hld', List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    obtain ⟨i, hi, hr⟩ := hld q hq
    exact ⟨i, hi, Or.inr (Or.inl hr)⟩

/-- **A straight-line loop iteration with its own buffers, placed**: as `loopStep_straight`, the
body's `HeapBuf`s of sizes `sizes` from `fp + fs f + mt`, holding `bufs`, and its callees reading
within `Lin` and those buffers. -/
theorem loopStep_bufs {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Stmt.straight = true) (AL : List (V × (ℕ ⊕ V))) (hal : pre.filterMap Stmt.allocSz = AL)
    (had : pre.filterMap Stmt.addrS = []) (κ : ℕ) (Lin : Layout) (args : List E)
    (fronts : List (Option V × String × List V × List V)) (tc : V) (targs : List V)
    (hcs : pre.filterMap Stmt.callS = fronts ++ [(some tc, f, targs, [])])
    (sizes : List ℕ) (bufs : List (List E)) (hbl : List.Forall₂ (fun c s => c.length ≤ s) bufs sizes)
    (fp mt : ℕ) (ks : List Kid)
    (hks : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out)
    (hsub : ∀ k ∈ ks, SubL k.Lin (bufL (fp + fs f + mt) sizes bufs ++ Lin))
    (targs' : List E) (more : Bool)
    (hσ : ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f + mt) sizes bufs ++ Lin) → ∀ outs, OutsOk ks outs →
      ∃ σ : Val, fn.params.map σ = args ∧
      Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun rs => rs = []) ∧
      AL.map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
      (AL.map Prod.fst).map σ = (bases (fp + fs f + mt) sizes).map (fun b => ofK (gpow b)) ∧
      CallsMatch σ (fronts.map (mkCall σ)) ks outs ∧ decide (σ tc ≠ 0) = more ∧
      targs.map σ = targs' ∧
      ∀ q ∈ pre.filterMap LeanVM.Guest.B1.Stmt.loadS, ∃ i, (σ q.1).limb 0 * gpow q.2 = gpow i ∧
        (RegionL Lin i ∨ RegionL (bufL (fp + fs f + mt) sizes bufs) i)) :
    ∃ (n : ℕ) (L : Layout), Within L (fp + fs f + mt) n ∧ DisjL L ∧
      ∀ rd, LowDef κ rd → MemL rd (L ++ Lin) →
        (more = true → RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) (fp + fs f) mt f
          targs' []) →
        (more = false → mt = fs f) →
        RelAtIn coreProgram fs cert rd (RegionL Lin) (fun _ => False) fp (fs f + mt + n) f args [] := by
  set Lb := bufL (fp + fs f + mt) sizes bufs with hLb
  obtain ⟨N, L, outs, ho, hW, hD, -, hK⟩ := kidsFromIn_of_kidsD (fs := fs) (cert := cert) κ ks hks
    (fp + fs f + mt + sizes.sum)
  refine ⟨sizes.sum + N, Lb ++ L, ?_,
    disj_append (bufL_disj _ _ _ hbl) hD (LeanVM.Guest.B1.bufL_within _ _ _ hbl) hW le_rfl,
    fun rd hlow hL htail hnot => ?_⟩
  · rw [within_append]
    exact ⟨(LeanVM.Guest.B1.bufL_within _ _ _ hbl).mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
  rw [List.append_assoc] at hL
  obtain ⟨hLb, hL'⟩ := memL_append.mp hL
  obtain ⟨hL1, hL2⟩ := memL_append.mp hL'
  obtain ⟨σ, hp, hH, hsz, hdst, hcm, htk, hta, hld⟩ := hσ rd hlow (memL_append.mpr ⟨hLb, hL2⟩) outs ho
  have hwf : Stmt.wfList coreProgram fn.body = true :=
    coreProgram_wf fn (List.mem_of_find?_eq_some hf)
  have hw := walk_straight σ [] pre hs
  rw [← hb] at hw
  have hsat := walk_sat fn.body hwf hH
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ pre hs
  rw [hal] at e1 e2
  have hsz' := e2.trans hsz
  rw [had] at e3
  rw [hcs, List.map_append] at e4
  have hld' := LeanVM.Guest.B1.loadAddrs_straight σ pre hs
  have hc : (mkCall σ (some tc, f, targs, [])).taken = more := htk
  have hown : ∀ i, RegionL Lb i → ownData cert fp (fp + fs f + mt) f (allocs σ (pre.flatMap (slEvs σ)))
      (pre.flatMap (slEvs σ)) i := fun i hi => by
    rw [hsz']
    exact Or.inl (LeanVM.Guest.B1.bufL_region _ _ _ hbl i hi)
  have := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := fun _ => False) (Dk := fun i => False ∨ outRegion ks outs i) (Rt := RegionL Lin)
    (Dt := fun _ => False) (fp := fp) (m := mt) (N := N) (σ := σ) (rd := rd) coreProgram_wf hf hl hp hw rfl
    (fun e he => (hsat.1 e he).1) e4 ?_ (by rw [e1, hsz']; exact hdst) (by rw [e3]; simp) ?_
    (fun i hi => Or.inl hi) ?_ (fun i hi => hi.elim)
  · rwa [hsz', Nat.add_assoc] at this
  · cases more with
    | true =>
      simp only [hc, ↓reduceIte]
      simp only [mkCall, List.map_nil]
      rw [hta]
      exact htail rfl
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact hnot rfl
  · have hsum : (allocs σ (pre.flatMap (slEvs σ))).sum = sizes.sum := by rw [hsz']
    rw [hsum]
    exact hK rd σ _ _ (fun _ => False) hcm hlow hL1
      (LeanVM.Guest.B1.memL_lins fun k hk => (hsub k hk).1 rd (memL_append.mpr ⟨hLb, hL2⟩))
      (regionsOk_of_sub _ _ _ fun k hk i hi =>
        (regionL_append_or ((hsub k hk).2 i hi)).elim (fun h => Or.inr (hown i h)) Or.inl)
  · intro A hA
    rw [hld', List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    obtain ⟨i, hi, hr⟩ := hld q hq
    exact ⟨i, hi, hr.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inl (hown i h)⟩

end
end LeanVM.Guest.B1.Main
