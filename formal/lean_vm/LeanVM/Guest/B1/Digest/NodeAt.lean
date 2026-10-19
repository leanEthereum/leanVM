/-
  LeanVM.Guest.B1.Digest.NodeAt

  `CompleteAt` of a function from an explicit valuation of its body on every memory holding the
  caller's words, its callees each `CompleteAt` and returning fixed words.
-/

module

public import LeanVM.Guest.B1.Digest.Forced
public import LeanVM.Guest.B1.Da.RelIn

/-!
# A function complete from its valuations

`completeAt_node`: a function that is not a loop helper, its `HeapBuf`s of sizes `sizes` holding
`own fp`, is `CompleteAt` when every memory defined below `2^κ` holding its buffers and the
caller's words `Lin` has a valuation walking its body, loading from its buffers or `Lin`, whose
calls are those of `ks` (`CallsR`): callees `CompleteAt` on words within its buffers or `Lin`,
returning fixed words.

`completeAt_loop`: a loop helper without buffers, its last call its tail (`tail`, itself `CompleteAt`
when entered).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Guest.B1 (LowDef CompleteAt CompleteAtD CompleteAtB kidsFromIn_of_kidsB kidsBound DisjL disj_append Within Returns Kid OutsOk CallsMatch RegionsOk outRegion bufL)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- A callee returning fixed words. -/
structure KidR where
  f : String
  taken : Bool
  args : List E
  Lin : Layout
  rets : List E

def KidR.kid (k : KidR) : Kid := ⟨k.f, k.taken, k.args, k.Lin, Returns k.rets⟩

/-- The frames match the callees. -/
def CallsR (σ : Val) : List Call → List KidR → Prop
  | c :: cs, k :: ks => c.f = k.f ∧ c.taken = k.taken ∧
      (k.taken = true → c.args.map σ = k.args ∧ c.rets.map σ = k.rets) ∧ CallsR σ cs ks
  | [], [] => True
  | _, _ => False

theorem callsMatch_of {σ : Val} : ∀ {cs : List Call} {ks : List KidR} {outs : List (List E × Layout)},
    CallsR σ cs ks → OutsOk (ks.map KidR.kid) outs → CallsMatch σ cs (ks.map KidR.kid) outs
  | c :: cs, k :: ks, o :: os, ⟨h1, h2, h3, h4⟩, ⟨g1, g2⟩ =>
      ⟨h1, h2, fun ht => ⟨(h3 ht).1, by rw [(h3 ht).2, (g1 ht).1]⟩, callsMatch_of h4 g2⟩
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, _, h => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

theorem callsR_snoc {σ : Val} {t : KidR} : ∀ {cs : List Call} {ks : List KidR}, CallsR σ cs (ks ++ [t]) →
    ∃ cs' c, cs = cs' ++ [c] ∧ CallsR σ cs' ks ∧ CallsR σ [c] [t]
  | c :: cs, [], ⟨h1, h2, h3, h4⟩ => by
    match cs, h4 with
    | [], _ => exact ⟨[], c, rfl, trivial, ⟨h1, h2, h3, trivial⟩⟩
  | c :: cs, k :: ks, ⟨h1, h2, h3, h4⟩ => by
    obtain ⟨cs', c', rfl, h, h'⟩ := callsR_snoc (ks := ks) h4
    exact ⟨c :: cs', c', rfl, ⟨h1, h2, h3, h⟩, h'⟩
  | [], [], h => h.elim
  | [], _ :: _, h => h.elim

theorem regionsOk_all {R : ℕ → Prop} : ∀ {Dacc : ℕ → Prop} {ks : List Kid} {outs : List (List E × Layout)},
    (∀ k ∈ ks, k.taken = true → ∀ i, RegionL k.Lin i → R i) → RegionsOk R Dacc ks outs
  | _, k :: _, _ :: _, h => ⟨fun ht i hi => Or.inl (h k List.mem_cons_self ht i hi),
      regionsOk_all fun k' hk' => h k' (List.mem_cons_of_mem _ hk')⟩
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial

theorem memL_lins_of {rd : Reader} {ks : List Kid} (h : ∀ k ∈ ks, MemL rd k.Lin) :
    MemL rd (Kid.lins ks) := fun q hq => by
  obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
  exact h k hk q hq

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A function with callees, complete from its valuations**: its own words `Lb fp` lie in its
`HeapBuf`s of sizes `sizes`. -/
theorem completeAt_node {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (Lb : ℕ → Layout) (hLb : ∀ fp i, RegionL (Lb fp) i →
      ∃ q ∈ sizes.zip (bases (fp + fs f) sizes), q.2 ≤ i ∧ i < q.2 + q.1)
    (hWb : ∀ fp, Within (Lb fp) (fp + fs f) sizes.sum)
    (ks : ℕ → List KidR)
    (hok : ∀ fp, ∀ k ∈ ks fp, k.taken = true → CompleteAt fs cert κ k.f k.Lin k.args (Returns k.rets))
    (hkR : ∀ fp, ∀ k ∈ ks fp, k.taken = true → ∀ i, RegionL k.Lin i → RegionL (Lb fp) i ∨ RegionL Lin i)
    (hσ : ∀ fp rd, LowDef κ rd → MemL rd (Lb fp) → MemL rd Lin →
      (∀ k ∈ ks fp, MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        CallsR σ (calls es) (ks fp) ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ (RegionL (Lb fp) i ∨ RegionL Lin i)) :
    CompleteAt fs cert κ f Lin args (Returns rets) := by
  intro fp
  have hok' : ∀ k ∈ (ks fp).map KidR.kid, k.taken = true → CompleteAt fs cert κ k.f k.Lin k.args k.Out := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact hok fp k' hk' ht
  obtain ⟨N, LK, outs, ho, hW, hK⟩ := LeanVM.Guest.B1.kidsFromIn_of_kids κ _ hok' (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, Lb fp ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, fun rd hlow hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨(hWb fp).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLb', hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ fp rd hlow hLb' hLin
  have hbo : ∀ i, RegionL (Lb fp) i → ownData cert fp (fp + fs f) f (allocs σ es) es i := fun i hi => by
    rw [hal]; exact Or.inl (hLb fp i hi)
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion ((ks fp).map KidR.kid) outs i)
    (fp := fp) (N := N) hf (Or.inl hl) hp hw hr hes (by rw [hal]; exact hbuf) (by rw [ha]; simp) ?_ ?_
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [hal] at h
  · rw [hal]
    refine hK rd σ _ _ (fun _ => False) (callsMatch_of hc ho) hlow hLK (memL_lins_of fun k hk => ?_)
      (regionsOk_all fun k hk ht i hi => ?_)
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact hkL k' hk'
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      rcases hkR fp k' hk' ht i hi with h | h
      · exact Or.inr (by rw [← hal]; exact hbo i h)
      · exact Or.inl h
  · intro A hA
    obtain ⟨i, rfl, h | h⟩ := hload A hA
    · exact ⟨i, rfl, Or.inl (hbo i h)⟩
    · exact ⟨i, rfl, Or.inr (Or.inl h)⟩

/-- **A function with callees, complete from its valuations**: its own words `Lb fp` lie in its
`HeapBuf`s of sizes `sizes`. -/
theorem completeAt_nodeD {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (Lb : ℕ → Layout) (hLb : ∀ fp i, RegionL (Lb fp) i →
      ∃ q ∈ sizes.zip (bases (fp + fs f) sizes), q.2 ≤ i ∧ i < q.2 + q.1)
    (hWb : ∀ fp, Within (Lb fp) (fp + fs f) sizes.sum) (hDb : ∀ fp, DisjL (Lb fp))
    (ks : ℕ → List KidR)
    (hok : ∀ fp, ∀ k ∈ ks fp, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args (Returns k.rets))
    (hkR : ∀ fp, ∀ k ∈ ks fp, k.taken = true → ∀ i, RegionL k.Lin i → RegionL (Lb fp) i ∨ RegionL Lin i)
    (hσ : ∀ fp rd, LowDef κ rd → MemL rd (Lb fp) → MemL rd Lin →
      (∀ k ∈ ks fp, MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        CallsR σ (calls es) (ks fp) ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ (RegionL (Lb fp) i ∨ RegionL Lin i)) :
    CompleteAtD fs cert κ f Lin args (Returns rets) := by
  intro fp
  have hok' : ∀ k ∈ (ks fp).map KidR.kid, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact hok fp k' hk' ht
  obtain ⟨N, LK, outs, ho, hW, hD, -, hK⟩ := LeanVM.Guest.B1.kidsFromIn_of_kidsD κ _ hok' (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, Lb fp ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, ?_, fun rd hlow hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨(hWb fp).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append (hDb fp) hD (hWb fp) hW (by omega)
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLb', hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ fp rd hlow hLb' hLin
  have hbo : ∀ i, RegionL (Lb fp) i → ownData cert fp (fp + fs f) f (allocs σ es) es i := fun i hi => by
    rw [hal]; exact Or.inl (hLb fp i hi)
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion ((ks fp).map KidR.kid) outs i)
    (fp := fp) (N := N) hf (Or.inl hl) hp hw hr hes (by rw [hal]; exact hbuf) (by rw [ha]; simp) ?_ ?_
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [hal] at h
  · rw [hal]
    refine hK rd σ _ _ (fun _ => False) (callsMatch_of hc ho) hlow hLK (memL_lins_of fun k hk => ?_)
      (regionsOk_all fun k hk ht i hi => ?_)
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact hkL k' hk'
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      rcases hkR fp k' hk' ht i hi with h | h
      · exact Or.inr (by rw [← hal]; exact hbo i h)
      · exact Or.inl h
  · intro A hA
    obtain ⟨i, rfl, h | h⟩ := hload A hA
    · exact ⟨i, rfl, Or.inl (hbo i h)⟩
    · exact ⟨i, rfl, Or.inr (Or.inl h)⟩

/-- **A function with callees, complete from its valuations**: its own words `Lb fp` lie in its
`HeapBuf`s of sizes `sizes`. -/
theorem completeAt_nodeB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (Lb : ℕ → Layout) (hLb : ∀ fp i, RegionL (Lb fp) i →
      ∃ q ∈ sizes.zip (bases (fp + fs f) sizes), q.2 ≤ i ∧ i < q.2 + q.1)
    (hWb : ∀ fp, Within (Lb fp) (fp + fs f) sizes.sum) (hDb : ∀ fp, DisjL (Lb fp))
    (ks : ℕ → List KidR)
    (bd : Kid → ℕ)
    (hok : ∀ fp, ∀ k ∈ ks fp, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args (Returns k.rets) (bd k.kid))
    (hkR : ∀ fp, ∀ k ∈ ks fp, k.taken = true → ∀ i, RegionL k.Lin i → RegionL (Lb fp) i ∨ RegionL Lin i)
    (B : ℕ) (hB : ∀ fp, fs f + sizes.sum + kidsBound fs bd ((ks fp).map KidR.kid) ≤ B)
    (hσ : ∀ fp rd, LowDef κ rd → MemL rd (Lb fp) → MemL rd Lin →
      (∀ k ∈ ks fp, MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        CallsR σ (calls es) (ks fp) ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ (RegionL (Lb fp) i ∨ RegionL Lin i)) :
    CompleteAtB fs cert κ f Lin args (Returns rets) B := by
  intro fp
  have hok' : ∀ k ∈ (ks fp).map KidR.kid, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k) := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact hok fp k' hk' ht
  obtain ⟨N, LK, outs, ho, hW, hD, hNb, -, hK⟩ := LeanVM.Guest.B1.kidsFromIn_of_kidsB κ bd _ hok' (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, Lb fp ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, ?_, le_trans (by omega) (hB fp), fun rd hlow hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨(hWb fp).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append (hDb fp) hD (hWb fp) hW (by omega)
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLb', hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ fp rd hlow hLb' hLin
  have hbo : ∀ i, RegionL (Lb fp) i → ownData cert fp (fp + fs f) f (allocs σ es) es i := fun i hi => by
    rw [hal]; exact Or.inl (hLb fp i hi)
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion ((ks fp).map KidR.kid) outs i)
    (fp := fp) (N := N) hf (Or.inl hl) hp hw hr hes (by rw [hal]; exact hbuf) (by rw [ha]; simp) ?_ ?_
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [hal] at h
  · rw [hal]
    refine hK rd σ _ _ (fun _ => False) (callsMatch_of hc ho) hlow hLK (memL_lins_of fun k hk => ?_)
      (regionsOk_all fun k hk ht i hi => ?_)
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact hkL k' hk'
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      rcases hkR fp k' hk' ht i hi with h | h
      · exact Or.inr (by rw [← hal]; exact hbo i h)
      · exact Or.inl h
  · intro A hA
    obtain ⟨i, rfl, h | h⟩ := hload A hA
    · exact ⟨i, rfl, Or.inl (hbo i h)⟩
    · exact ⟨i, rfl, Or.inr (Or.inl h)⟩

/-- **A loop helper without buffers, complete from its valuations**, its tail call last. -/
theorem completeAt_loop {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) (κ : ℕ) (Lin : Layout) (args rets : List E) (ks : List KidR)
    (tail : KidR)
    (hok : ∀ k ∈ ks, k.taken = true → CompleteAt fs cert κ k.f k.Lin k.args (Returns k.rets))
    (htail : tail.taken = true → CompleteAt fs cert κ tail.f tail.Lin tail.args (Returns tail.rets))
    (hkR : ∀ k ∈ ks ++ [tail], k.taken = true → ∀ i, RegionL k.Lin i → RegionL Lin i)
    (hσ : ∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ k ∈ ks ++ [tail], MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        CallsR σ (calls es) (ks ++ [tail]) ∧ addrs es = [] ∧ allocs σ es = [] ∧ allocDsts es = [] ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ RegionL Lin i) :
    CompleteAt fs cert κ f Lin args (Returns rets) := by
  intro fp
  classical
  have hok' : ∀ k ∈ ks.map KidR.kid, k.taken = true → CompleteAt fs cert κ k.f k.Lin k.args k.Out := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact hok k' hk' ht
  -- the tail, at `fp + fs f`
  obtain ⟨m, Lt, hWt, hT⟩ : ∃ (m : ℕ) (Lt : Layout), Within Lt (fp + fs f) m ∧
      ∀ rd, LowDef κ rd → MemL rd Lt → MemL rd tail.Lin →
        if tail.taken then RelAtIn coreProgram fs cert rd (RegionL tail.Lin) (RegionL []) (fp + fs f) m tail.f
          tail.args tail.rets else m = fs tail.f := by
    by_cases ht : tail.taken = true
    · obtain ⟨m, Lown, rets', Lout, ⟨rfl, rfl⟩, hW, hR⟩ := htail ht (fp + fs f)
      refine ⟨m, Lown, by simpa using hW, fun rd hl hL hL' => ?_⟩
      rw [ite_pos' ht]
      exact hR rd hl (by simpa using Main.memL_append.mpr ⟨hL, hL'⟩)
    · refine ⟨fs tail.f, [], fun q hq => by simp at hq, fun rd _ _ _ => ?_⟩
      rw [ite_neg' ht]
  obtain ⟨N, LK, outs, ho, hW, hK⟩ := LeanVM.Guest.B1.kidsFromIn_of_kids κ _ hok' (fp + fs f + m)
  refine ⟨fs f + m + 0 + N, Lt ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, fun rd hlow hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLt, hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ rd hlow hLin
  obtain ⟨cs, c, hcs, hc1, ⟨ct1, ct2, ct3, -⟩⟩ := callsR_snoc hc
  have hTr := hT rd hlow hLt (hkL tail (by simp))
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion (ks.map KidR.kid) outs i)
    (Rt := fun i => tail.taken = true ∧ RegionL tail.Lin i) (Dt := RegionL []) (fp := fp) (m := m) (N := N) (c := c) (cs := cs) hf hl hp hw hr
    hes hcs ?_ (by rw [hbuf, hal]; rfl) (by rw [ha]; simp) ?_ ?_ ?_ (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [hal] at h
  · by_cases ht : tail.taken = true
    · rw [ct2, ite_pos' ht, ct1, (ct3 ht).1, (ct3 ht).2]
      rw [ite_pos' ht] at hTr
      exact hTr.mono fun i hi => ⟨ht, hi⟩
    · have ht' : tail.taken = false := by simpa using ht
      rw [ct2, ht', ct1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ht'] at hTr
      exact hTr
  · rw [hal, List.sum_nil, Nat.add_zero]
    refine hK rd σ _ _ (fun _ => False) (callsMatch_of hc1 ho) hlow hLK (memL_lins_of fun k hk => ?_)
      (regionsOk_all fun k hk ht i hi => ?_)
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact hkL k' (List.mem_append_left _ hk')
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact Or.inl (hkR k' (List.mem_append_left _ hk') ht i hi)
  · intro i ⟨ht, hi⟩
    exact Or.inl (hkR tail (by simp) ht i hi)
  · intro A hA
    obtain ⟨i, rfl, h⟩ := hload A hA
    exact ⟨i, rfl, Or.inr (Or.inl h)⟩

/-- **A loop helper without buffers, complete from its valuations**, its tail call last. -/
theorem completeAt_loopD {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) (κ : ℕ) (Lin : Layout) (args rets : List E) (ks : List KidR)
    (tail : KidR)
    (hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args (Returns k.rets))
    (htail : tail.taken = true → CompleteAtD fs cert κ tail.f tail.Lin tail.args (Returns tail.rets))
    (hkR : ∀ k ∈ ks ++ [tail], k.taken = true → ∀ i, RegionL k.Lin i → RegionL Lin i)
    (hσ : ∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ k ∈ ks ++ [tail], MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        CallsR σ (calls es) (ks ++ [tail]) ∧ addrs es = [] ∧ allocs σ es = [] ∧ allocDsts es = [] ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ RegionL Lin i) :
    CompleteAtD fs cert κ f Lin args (Returns rets) := by
  intro fp
  classical
  have hok' : ∀ k ∈ ks.map KidR.kid, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact hok k' hk' ht
  -- the tail, at `fp + fs f`
  obtain ⟨m, Lt, hWt, hDt, hT⟩ : ∃ (m : ℕ) (Lt : Layout), Within Lt (fp + fs f) m ∧ DisjL Lt ∧
      ∀ rd, LowDef κ rd → MemL rd Lt → MemL rd tail.Lin →
        if tail.taken then RelAtIn coreProgram fs cert rd (RegionL tail.Lin) (RegionL []) (fp + fs f) m tail.f
          tail.args tail.rets else m = fs tail.f := by
    by_cases ht : tail.taken = true
    · obtain ⟨m, Lown, rets', Lout, ⟨rfl, rfl⟩, hW, hDw, hR⟩ := htail ht (fp + fs f)
      refine ⟨m, Lown, by simpa using hW, by simpa using hDw, fun rd hl hL hL' => ?_⟩
      rw [ite_pos' ht]
      exact hR rd hl (by simpa using Main.memL_append.mpr ⟨hL, hL'⟩)
    · refine ⟨fs tail.f, [], fun q hq => by simp at hq, LeanVM.Guest.B1.disj_nil, fun rd _ _ _ => ?_⟩
      rw [ite_neg' ht]
  obtain ⟨N, LK, outs, ho, hW, hD, -, hK⟩ := LeanVM.Guest.B1.kidsFromIn_of_kidsD κ _ hok' (fp + fs f + m)
  refine ⟨fs f + m + 0 + N, Lt ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, ?_, fun rd hlow hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append hDt hD hWt hW le_rfl
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLt, hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ rd hlow hLin
  obtain ⟨cs, c, hcs, hc1, ⟨ct1, ct2, ct3, -⟩⟩ := callsR_snoc hc
  have hTr := hT rd hlow hLt (hkL tail (by simp))
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion (ks.map KidR.kid) outs i)
    (Rt := fun i => tail.taken = true ∧ RegionL tail.Lin i) (Dt := RegionL []) (fp := fp) (m := m) (N := N) (c := c) (cs := cs) hf hl hp hw hr
    hes hcs ?_ (by rw [hbuf, hal]; rfl) (by rw [ha]; simp) ?_ ?_ ?_ (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [hal] at h
  · by_cases ht : tail.taken = true
    · rw [ct2, ite_pos' ht, ct1, (ct3 ht).1, (ct3 ht).2]
      rw [ite_pos' ht] at hTr
      exact hTr.mono fun i hi => ⟨ht, hi⟩
    · have ht' : tail.taken = false := by simpa using ht
      rw [ct2, ht', ct1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ht'] at hTr
      exact hTr
  · rw [hal, List.sum_nil, Nat.add_zero]
    refine hK rd σ _ _ (fun _ => False) (callsMatch_of hc1 ho) hlow hLK (memL_lins_of fun k hk => ?_)
      (regionsOk_all fun k hk ht i hi => ?_)
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact hkL k' (List.mem_append_left _ hk')
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact Or.inl (hkR k' (List.mem_append_left _ hk') ht i hi)
  · intro i ⟨ht, hi⟩
    exact Or.inl (hkR tail (by simp) ht i hi)
  · intro A hA
    obtain ⟨i, rfl, h⟩ := hload A hA
    exact ⟨i, rfl, Or.inr (Or.inl h)⟩


/-- **A loop helper without buffers, complete from its valuations**, its tail call last. -/
theorem completeAt_loopB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = true) (κ : ℕ) (Lin : Layout) (args rets : List E) (ks : List KidR)
    (tail : KidR)
    (bd : Kid → ℕ) (bt : ℕ)
    (hok : ∀ k ∈ ks, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args (Returns k.rets) (bd k.kid))
    (htail : tail.taken = true → CompleteAtB fs cert κ tail.f tail.Lin tail.args (Returns tail.rets) bt)
    (B : ℕ) (hB : fs f + max bt (fs tail.f) + kidsBound fs bd (ks.map KidR.kid) ≤ B)
    (hkR : ∀ k ∈ ks ++ [tail], k.taken = true → ∀ i, RegionL k.Lin i → RegionL Lin i)
    (hσ : ∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ k ∈ ks ++ [tail], MemL rd k.Lin) ∧ ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        CallsR σ (calls es) (ks ++ [tail]) ∧ addrs es = [] ∧ allocs σ es = [] ∧ allocDsts es = [] ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ RegionL Lin i) :
    CompleteAtB fs cert κ f Lin args (Returns rets) B := by
  intro fp
  classical
  have hok' : ∀ k ∈ ks.map KidR.kid, k.taken = true → CompleteAtB fs cert κ k.f k.Lin k.args k.Out (bd k) := by
    intro k hk ht
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    exact hok k' hk' ht
  -- the tail, at `fp + fs f`
  obtain ⟨m, Lt, hWt, hDt, hmb, hT⟩ : ∃ (m : ℕ) (Lt : Layout), Within Lt (fp + fs f) m ∧ DisjL Lt ∧
      m ≤ max bt (fs tail.f) ∧
      ∀ rd, LowDef κ rd → MemL rd Lt → MemL rd tail.Lin →
        if tail.taken then RelAtIn coreProgram fs cert rd (RegionL tail.Lin) (RegionL []) (fp + fs f) m tail.f
          tail.args tail.rets else m = fs tail.f := by
    by_cases ht : tail.taken = true
    · obtain ⟨m, Lown, rets', Lout, ⟨rfl, rfl⟩, hW, hDw, hmb, hR⟩ := htail ht (fp + fs f)
      refine ⟨m, Lown, by simpa using hW, by simpa using hDw, le_trans hmb (le_max_left _ _), fun rd hl hL hL' => ?_⟩
      rw [ite_pos' ht]
      exact hR rd hl (by simpa using Main.memL_append.mpr ⟨hL, hL'⟩)
    · refine ⟨fs tail.f, [], fun q hq => by simp at hq, LeanVM.Guest.B1.disj_nil, le_max_right _ _, fun rd _ _ _ => ?_⟩
      rw [ite_neg' ht]
  obtain ⟨N, LK, outs, ho, hW, hD, hNb, -, hK⟩ := LeanVM.Guest.B1.kidsFromIn_of_kidsB κ bd _ hok' (fp + fs f + m)
  refine ⟨fs f + m + 0 + N, Lt ++ LK, rets, [], ⟨rfl, rfl⟩, ?_, ?_, le_trans (by omega) hB, fun rd hlow hL => ?_⟩
  · rw [List.nil_append, LeanVM.Guest.B1.within_append]
    exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append hDt hD hWt hW le_rfl
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hLt, hLK⟩ := Main.memL_append.mp hLo
  obtain ⟨hkL, σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ rd hlow hLin
  obtain ⟨cs, c, hcs, hc1, ⟨ct1, ct2, ct3, -⟩⟩ := callsR_snoc hc
  have hTr := hT rd hlow hLt (hkL tail (by simp))
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (rd := rd) coreProgram_wf
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i => False ∨ outRegion (ks.map KidR.kid) outs i)
    (Rt := fun i => tail.taken = true ∧ RegionL tail.Lin i) (Dt := RegionL []) (fp := fp) (m := m) (N := N) (c := c) (cs := cs) hf hl hp hw hr
    hes hcs ?_ (by rw [hbuf, hal]; rfl) (by rw [ha]; simp) ?_ ?_ ?_ (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rwa [hal] at h
  · by_cases ht : tail.taken = true
    · rw [ct2, ite_pos' ht, ct1, (ct3 ht).1, (ct3 ht).2]
      rw [ite_pos' ht] at hTr
      exact hTr.mono fun i hi => ⟨ht, hi⟩
    · have ht' : tail.taken = false := by simpa using ht
      rw [ct2, ht', ct1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ht'] at hTr
      exact hTr
  · rw [hal, List.sum_nil, Nat.add_zero]
    refine hK rd σ _ _ (fun _ => False) (callsMatch_of hc1 ho) hlow hLK (memL_lins_of fun k hk => ?_)
      (regionsOk_all fun k hk ht i hi => ?_)
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact hkL k' (List.mem_append_left _ hk')
    · obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
      exact Or.inl (hkR k' (List.mem_append_left _ hk') ht i hi)
  · intro i ⟨ht, hi⟩
    exact Or.inl (hkR tail (by simp) ht i hi)
  · intro A hA
    obtain ⟨i, rfl, h⟩ := hload A hA
    exact ⟨i, rfl, Or.inr (Or.inl h)⟩

end
end LeanVM.Guest.B1.Digest
