/-
  LeanVM.Guest.B1.Place.OsKids

  The callees of a straight-line body placed in sequence: blocks reading fixed words, and per
  level a loop whose layout depends on where it is placed, then callees reading it. Ported from
  mumbai's `B1/Whir/OsKids.lean`.
-/

module

public import LeanVM.Guest.Memory.Uniform
/-!
# Callees in sequence (TRIAGE #36)

* `os_kids_block`: calls each complete on the words `Lk` are `KidsFromIn` from any `b`, by one
  layout, claiming nothing.
* `OsCompleteAtP`: `CompleteAtD` with the words read and the buffers returned depending on the
  frame pointer (`open_stacked`'s query-position loops, whose decoders' pointers the caller's
  buffer holds); `os_kidsFromIn_oneP` places one.
* `os_levels_kids`: per level, calls on `Lk`, then such a loop at `p` reading `W l p`, then calls
  reading `Lk`, `W l p` and the loop's buffers `S l p`; the positions `ps` are returned.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The callees of the frames `cs`, each reading `Lk` and returning its frame's words. -/
noncomputable def osKidsOf (σ : Val) (Lk : Layout) (cs : List Call) : List Kid :=
  cs.map fun c => ⟨c.f, c.taken, c.args.map σ, Lk, Returns (c.rets.map σ)⟩

private theorem os_callsMatch_map (σ : Val) (Lk : Layout) : ∀ (cs : List Call) (outs : List (List E × Layout)),
    OutsOk (osKidsOf σ Lk cs) outs → CallsMatch σ cs (osKidsOf σ Lk cs) outs
  | [], [], _ => trivial
  | _ :: cs, _ :: os, ⟨ho, hos⟩ => ⟨rfl, rfl, fun ht => ⟨rfl, (ho ht).1.symm⟩, os_callsMatch_map σ Lk cs os hos⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

private theorem os_regionL_append {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) : RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

/-- **Calls complete on fixed words**, placed from `b`. -/
theorem os_kids_block (κ : ℕ) (Lk : Layout) (σ : Val) (cs : List Call)
    (hc : ∀ c ∈ cs, c.taken = true → CompleteAtD fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout), Within L b N ∧ DisjL L ∧ ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd →
      MemL rd L → MemL rd Lk → (∀ i, RegionL Lk i → R i ∨ Dacc i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b N (fun _ => False) := by
  obtain ⟨N, L, outs, ho, hW, hD, -, hK⟩ := kidsFromIn_of_kidsD (fs := fs) (cert := cert) κ (osKidsOf σ Lk cs)
    (fun k hk ht => by
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
      exact hc c hc' ht) b
  refine ⟨N, L, hW, hD, fun rd R Dacc hlow hL hLk hR =>
    kidsFromIn_dend _ _ _ _ (fun _ h => h.elim) (hK rd σ cs R Dacc (os_callsMatch_map σ Lk cs outs ho) hlow hL ?_ ?_)⟩
  · intro q hq
    obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact hLk q hq
  · refine regionsOk_of fun k hk _ i hi => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact hR i hi

/-- **`f` is complete at every frame pointer, on disjoint layouts**, reading `Lin fp` and returning
the buffers `Lout fp`. -/
def OsCompleteAtP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (f : String) (Lin : ℕ → Layout)
    (args rets : List E) (Lout : ℕ → Layout) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout), Within (Lout fp ++ Lown) fp n ∧ DisjL (Lout fp ++ Lown) ∧
    ∀ rd, LowDef κ rd → MemL rd (Lout fp ++ Lown ++ Lin fp) →
      RelAtIn coreProgram fs cert rd (RegionL (Lin fp)) (RegionL (Lout fp)) fp n f args rets

/-- **One such callee**, placed at `b`, claiming its buffers. -/
theorem os_kidsFromIn_oneP {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E} {Lout : ℕ → Layout}
    (h : OsCompleteAtP fs cert κ f Lin args rets Lout) (σ : Val) (c : Call) (hf : c.f = f) (ht : c.taken = true)
    (ha : c.args.map σ = args) (hr : c.rets.map σ = rets) (b : ℕ) :
    ∃ (n : ℕ) (Lown : Layout), Within (Lout b ++ Lown) b n ∧ DisjL (Lout b ++ Lown) ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd (Lout b ++ Lown) → MemL rd (Lin b) →
        (∀ i, RegionL (Lin b) i → R i ∨ Dacc i) →
        KidsFromIn coreProgram fs cert rd σ R Dacc [c] b n (RegionL (Lout b)) := by
  obtain ⟨n, Lown, hW, hD, hrel⟩ := h b
  refine ⟨n, Lown, hW, hD, fun rd R Dacc hlow hL hLin hR =>
    ⟨n, 0, RegionL (Lin b), RegionL (Lout b), by omega, hR, ?_, ⟨rfl, fun i hi => Or.inr ⟨ht, hi⟩⟩⟩⟩
  simp only [ht, ↓reduceIte]
  rw [hf, ha, hr]
  exact hrel rd hlow (Main.memL_append.mpr ⟨hL, hLin⟩)

/-- A level's frames: the calls before the loop, the loop, the calls after it. -/
structure OsLvK where
  A : List Call
  sq : Call
  B : List Call

/-- A level's frames in order. -/
def OsLvK.calls (k : OsLvK) : List Call := k.A ++ k.sq :: k.B

/-- A level's callees: those before the loop on `Lk`, the loop at `p` on `Lk ++ W p` returning
`S p`, those after it on `Lk ++ W p ++ S p` for every `p`. -/
structure OsLvKOk (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (Lk : Layout)
    (W S : ℕ → Layout) (k : OsLvK) : Prop where
  A : ∀ c ∈ k.A, c.taken = true → CompleteAtD fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ))
  taken : k.sq.taken = true
  sq : OsCompleteAtP fs cert κ k.sq.f (fun p => Lk ++ W p) (k.sq.args.map σ) (k.sq.rets.map σ) S
  B : ∀ p, ∀ c ∈ k.B, c.taken = true →
    CompleteAtD fs cert κ c.f (Lk ++ W p ++ S p) (c.args.map σ) (Returns (c.rets.map σ))

/-- **The levels' callees in sequence** from `b`: their total, their layout, the loops' positions. -/
theorem os_levels_kids (κ : ℕ) (σ : Val) (Lk : Layout) (W S : ℕ → ℕ → Layout) :
    ∀ (ks : List OsLvK) (l0 : ℕ), (∀ i (h : i < ks.length), OsLvKOk fs cert κ σ Lk (W (l0 + i)) (S (l0 + i)) ks[i]) →
      ∀ b, ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = ks.length ∧ Within L b N ∧ DisjL L ∧
        ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd Lk →
          (∀ i (h : i < ps.length), MemL rd (W (l0 + i) ps[i])) → (∀ i, RegionL Lk i → R i) →
          (∀ l, l0 ≤ l → l < l0 + ks.length → ∀ p i, RegionL (W l p) i → R i) →
          KidsFromIn coreProgram fs cert rd σ R Dacc (ks.flatMap OsLvK.calls) b N (fun _ => False)
  | [], _, _, b => ⟨0, [], [], rfl, fun _ h => by simp at h, disj_nil, fun _ _ _ _ _ _ _ _ _ =>
      ⟨rfl, fun _ h => h.elim⟩⟩
  | k :: ks, l0, hok, b => by
    have h0 := hok 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    obtain ⟨NA, LA, hWA, hDA, hKA⟩ := os_kids_block (fs := fs) (cert := cert) κ Lk σ k.A h0.A b
    obtain ⟨nS, LS, hWS, hDS, hKS⟩ := os_kidsFromIn_oneP h0.sq σ k.sq rfl h0.taken rfl rfl (b + NA)
    obtain ⟨NB, LB, hWB, hDB, hKB⟩ := os_kids_block (fs := fs) (cert := cert) κ
      (Lk ++ W l0 (b + NA) ++ S l0 (b + NA)) σ k.B (h0.B (b + NA)) (b + NA + nS)
    obtain ⟨Nr, Lr, ps, hps, hWr, hDr, hKr⟩ := os_levels_kids κ σ Lk W S ks (l0 + 1) (fun i hi => by
      have := hok (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, show l0 + (i + 1) = l0 + 1 + i by omega] at this
      exact this) (b + NA + nS + NB)
    have hW3 : Within (LB ++ Lr) (b + NA + nS) (NB + Nr) := by
      rw [within_append]; exact ⟨hWB.mono le_rfl (by omega), hWr.mono (by omega) (by omega)⟩
    have hW2 : Within ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)) (b + NA) (nS + (NB + Nr)) := by
      rw [within_append]; exact ⟨hWS.mono le_rfl (by omega), hW3.mono (by omega) (by omega)⟩
    refine ⟨NA + (nS + (NB + Nr)), LA ++ ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)), (b + NA) :: ps,
      by simp [hps], ?_, disj_append hDA (disj_append hDS (disj_append hDB hDr hWB hWr le_rfl) hWS hW3 le_rfl) hWA
        hW2 le_rfl, ?_⟩
    · rw [within_append]
      exact ⟨hWA.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
    · intro rd R Dacc hlow hL hLk hWm hR hRW
      obtain ⟨hLA, hL'⟩ := Main.memL_append.mp hL
      obtain ⟨hLS, hL''⟩ := Main.memL_append.mp hL'
      obtain ⟨hLB, hLr⟩ := Main.memL_append.mp hL''
      have hW0 : MemL rd (W l0 (b + NA)) := hWm 0 (by simp)
      have hS0 : MemL rd (S l0 (b + NA)) := (Main.memL_append.mp hLS).1
      simp only [List.flatMap_cons, OsLvK.calls, List.append_assoc, List.cons_append]
      refine kidsFromIn_append _ _ _ _ _ _ _ _ (hKA rd R Dacc hlow hLA hLk fun i hi => Or.inl (hR i hi)) ?_
      intro D1 _
      rw [show k.sq :: (k.B ++ ks.flatMap OsLvK.calls) = [k.sq] ++ (k.B ++ ks.flatMap OsLvK.calls) from rfl]
      refine kidsFromIn_append _ _ _ _ _ _ _ _ (hKS rd R D1 hlow hLS (Main.memL_append.mpr ⟨hLk, hW0⟩) fun i hi => ?_) ?_
      · rcases os_regionL_append hi with hi | hi
        · exact Or.inl (hR i hi)
        · exact Or.inl (hRW l0 le_rfl (by simp) _ i hi)
      intro D2 hD2
      refine kidsFromIn_append _ _ _ _ _ _ _ _ (hKB rd R D2 hlow hLB
        (Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨hLk, hW0⟩, hS0⟩) fun i hi => ?_) ?_
      · rcases os_regionL_append hi with hi | hi
        · rcases os_regionL_append hi with hi | hi
          · exact Or.inl (hR i hi)
          · exact Or.inl (hRW l0 le_rfl (by simp) _ i hi)
        · exact Or.inr (hD2 i hi)
      intro D3 _
      exact hKr rd R D3 hlow hLr hLk (fun i hi => by
        have := hWm (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, show l0 + (i + 1) = l0 + 1 + i by omega] at this
        exact this) hR (fun l h1 h2 => hRW l (by omega) (by simp; omega))

end
end LeanVM.Guest.B1
