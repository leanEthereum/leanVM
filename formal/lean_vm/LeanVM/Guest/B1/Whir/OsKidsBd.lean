/-
  LeanVM.Guest.B1.Whir.OsKidsBd

  `OsKids` by bounded trees: the callees' totals bounded by their bounds.
-/

module

public import LeanVM.Guest.B1.Whir.OsKids

/-!
# Callees in sequence, by bounded trees (TRIAGE #36)

`os_kids_blockB`, `OsCompleteAtPB`/`os_kidsFromIn_onePB` and `os_levels_kidsB`: `OsKids`'s
composition with each callee's total at most its bound (a function of its name and arguments, the
the composition's total at most the sum (`osCallsBound`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

private theorem os_regionL_append {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) : RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

/-- The frames' bound: an entered one's `bd` at its arguments, a skipped one's frame. -/
def osCallsBound (fs : String → ℕ) (σ : Val) (bd : String → List E → ℕ) (cs : List Call) : ℕ :=
  (cs.map fun c => if c.taken = true then bd c.f (c.args.map σ) else fs c.f).sum

private theorem os_callsMatch_mapB (σ : Val) (Lk : Layout) : ∀ (cs : List Call) (outs : List (List E × Layout)),
    OutsOk (osKidsOf σ Lk cs) outs → CallsMatch σ cs (osKidsOf σ Lk cs) outs
  | [], [], _ => trivial
  | _ :: cs, _ :: os, ⟨ho, hos⟩ => ⟨rfl, rfl, fun ht => ⟨rfl, (ho ht).1.symm⟩, os_callsMatch_mapB σ Lk cs os hos⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **Calls complete on fixed words by bounded trees**, placed from `b`. -/
theorem os_kids_blockB (κ : ℕ) (Lk : Layout) (σ : Val) (cs : List Call) (bd : String → List E → ℕ)
    (hc : ∀ c ∈ cs, c.taken = true →
      CompleteAtB fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (bd c.f (c.args.map σ)))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout), Within L b N ∧ DisjL L ∧ N ≤ osCallsBound fs σ bd cs ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd →
      MemL rd L → MemL rd Lk → (∀ i, RegionL Lk i → R i ∨ Dacc i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b N (fun _ => False) := by
  obtain ⟨N, L, outs, ho, hW, hD, hN, -, hK⟩ := kidsFromIn_of_kidsB (fs := fs) (cert := cert) κ
    (fun k => bd k.f k.args) (osKidsOf σ Lk cs)
    (fun k hk ht => by
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
      exact hc c hc' ht) b
  refine ⟨N, L, hW, hD, ?_, fun rd R Dacc hlow hL hLk hR =>
    kidsFromIn_dend _ _ _ _ (fun _ h => h.elim) (hK rd σ cs R Dacc (os_callsMatch_mapB σ Lk cs outs ho) hlow hL ?_ ?_)⟩
  · refine le_trans hN (le_of_eq ?_)
    simp [kidsBound, osCallsBound, osKidsOf, List.map_map, Function.comp_def]
  · intro q hq
    obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact hLk q hq
  · refine regionsOk_of fun k hk _ i hi => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact hR i hi

/-- `OsCompleteAtP` by trees of at most `B` words. -/
def OsCompleteAtPB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (f : String) (Lin : ℕ → Layout)
    (args rets : List E) (Lout : ℕ → Layout) (B : ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout), Within (Lout fp ++ Lown) fp n ∧ DisjL (Lout fp ++ Lown) ∧ n ≤ B ∧
    ∀ rd, LowDef κ rd → MemL rd (Lout fp ++ Lown ++ Lin fp) →
      RelAtIn coreProgram fs cert rd (RegionL (Lin fp)) (RegionL (Lout fp)) fp n f args rets

theorem os_kidsFromIn_onePB {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E} {Lout : ℕ → Layout} {B : ℕ}
    (h : OsCompleteAtPB fs cert κ f Lin args rets Lout B) (σ : Val) (c : Call) (hf : c.f = f) (ht : c.taken = true)
    (ha : c.args.map σ = args) (hr : c.rets.map σ = rets) (b : ℕ) :
    ∃ (n : ℕ) (Lown : Layout), Within (Lout b ++ Lown) b n ∧ DisjL (Lout b ++ Lown) ∧ n ≤ B ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd (Lout b ++ Lown) → MemL rd (Lin b) →
        (∀ i, RegionL (Lin b) i → R i ∨ Dacc i) →
        KidsFromIn coreProgram fs cert rd σ R Dacc [c] b n (RegionL (Lout b)) := by
  obtain ⟨n, Lown, hW, hD, hn, hrel⟩ := h b
  refine ⟨n, Lown, hW, hD, hn, fun rd R Dacc hlow hL hLin hR =>
    ⟨n, 0, RegionL (Lin b), RegionL (Lout b), by omega, hR, ?_, ⟨rfl, fun i hi => Or.inr ⟨ht, hi⟩⟩⟩⟩
  simp only [ht, ↓reduceIte]
  rw [hf, ha, hr]
  exact hrel rd hlow (Main.memL_append.mpr ⟨hL, hLin⟩)

/-- A level's callees by bounded trees. -/
structure OsLvKOkB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (Lk : Layout)
    (W S : ℕ → Layout) (bd : String → List E → ℕ) (k : OsLvK) : Prop where
  A : ∀ c ∈ k.A, c.taken = true →
    CompleteAtB fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (bd c.f (c.args.map σ))
  taken : k.sq.taken = true
  sq : OsCompleteAtPB fs cert κ k.sq.f (fun p => Lk ++ W p) (k.sq.args.map σ) (k.sq.rets.map σ) S
    (bd k.sq.f (k.sq.args.map σ))
  B : ∀ p, ∀ c ∈ k.B, c.taken = true →
    CompleteAtB fs cert κ c.f (Lk ++ W p ++ S p) (c.args.map σ) (Returns (c.rets.map σ)) (bd c.f (c.args.map σ))

theorem osCallsBound_append (fs : String → ℕ) (σ : Val) (bd : String → List E → ℕ) (cs cs' : List Call) :
    osCallsBound fs σ bd (cs ++ cs') = osCallsBound fs σ bd cs + osCallsBound fs σ bd cs' := by
  simp [osCallsBound]

theorem osCallsBound_cons (fs : String → ℕ) (σ : Val) (bd : String → List E → ℕ) (c : Call) (cs : List Call) :
    osCallsBound fs σ bd (c :: cs) =
      (if c.taken = true then bd c.f (c.args.map σ) else fs c.f) + osCallsBound fs σ bd cs := by
  simp [osCallsBound]

/-- The frames' bound, by name: an entered one's or a skipped one's, the larger. -/
theorem osCallsBound_le_max (fs : String → ℕ) (σ : Val) (bd : String → ℕ) (cs : List Call) :
    osCallsBound fs σ (fun f _ => bd f) cs ≤ (cs.map fun c => max (bd c.f) (fs c.f)).sum := by
  induction cs with
  | nil => simp [osCallsBound]
  | cons c cs ih =>
    rw [osCallsBound_cons, List.map_cons, List.sum_cons]
    refine Nat.add_le_add ?_ ih
    split
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- **`os_levels_kids` by bounded trees.** -/
theorem os_levels_kidsB (κ : ℕ) (σ : Val) (Lk : Layout) (W S : ℕ → ℕ → Layout) (bd : String → List E → ℕ) :
    ∀ (ks : List OsLvK) (l0 : ℕ), (∀ i (h : i < ks.length), OsLvKOkB fs cert κ σ Lk (W (l0 + i)) (S (l0 + i)) bd ks[i]) →
      ∀ b, ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = ks.length ∧ Within L b N ∧ DisjL L ∧
        N ≤ osCallsBound fs σ bd (ks.flatMap OsLvK.calls) ∧
        ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd Lk →
          (∀ i (h : i < ps.length), MemL rd (W (l0 + i) ps[i])) → (∀ i, RegionL Lk i → R i) →
          (∀ l, l0 ≤ l → l < l0 + ks.length → ∀ p i, RegionL (W l p) i → R i) →
          KidsFromIn coreProgram fs cert rd σ R Dacc (ks.flatMap OsLvK.calls) b N (fun _ => False)
  | [], _, _, b => ⟨0, [], [], rfl, fun _ h => by simp at h, disj_nil, Nat.zero_le _, fun _ _ _ _ _ _ _ _ _ =>
      ⟨rfl, fun _ h => h.elim⟩⟩
  | k :: ks, l0, hok, b => by
    have h0 := hok 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    obtain ⟨NA, LA, hWA, hDA, hNA, hKA⟩ := os_kids_blockB (fs := fs) (cert := cert) κ Lk σ k.A bd h0.A b
    obtain ⟨nS, LS, hWS, hDS, hNS, hKS⟩ := os_kidsFromIn_onePB h0.sq σ k.sq rfl h0.taken rfl rfl (b + NA)
    obtain ⟨NB, LB, hWB, hDB, hNB, hKB⟩ := os_kids_blockB (fs := fs) (cert := cert) κ
      (Lk ++ W l0 (b + NA) ++ S l0 (b + NA)) σ k.B bd (h0.B (b + NA)) (b + NA + nS)
    obtain ⟨Nr, Lr, ps, hps, hWr, hDr, hNr, hKr⟩ := os_levels_kidsB κ σ Lk W S bd ks (l0 + 1) (fun i hi => by
      have := hok (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, show l0 + (i + 1) = l0 + 1 + i by omega] at this
      exact this) (b + NA + nS + NB)
    have hW3 : Within (LB ++ Lr) (b + NA + nS) (NB + Nr) := by
      rw [within_append]; exact ⟨hWB.mono le_rfl (by omega), hWr.mono (by omega) (by omega)⟩
    have hW2 : Within ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)) (b + NA) (nS + (NB + Nr)) := by
      rw [within_append]; exact ⟨hWS.mono le_rfl (by omega), hW3.mono (by omega) (by omega)⟩
    refine ⟨NA + (nS + (NB + Nr)), LA ++ ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)), (b + NA) :: ps,
      by simp [hps], ?_, disj_append hDA (disj_append hDS (disj_append hDB hDr hWB hWr le_rfl) hWS hW3 le_rfl) hWA
        hW2 le_rfl, ?_, ?_⟩
    · rw [within_append]
      exact ⟨hWA.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
    · simp only [List.flatMap_cons, OsLvK.calls, osCallsBound_append, osCallsBound_cons, h0.taken, ↓reduceIte]
      omega
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
