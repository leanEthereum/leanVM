/-
  LeanVM.Guest.B1.Place.OsKidsB

  `OsKids` within bounds: the callees in sequence, each entered one's tree within its name's bound
  `Bk`, so that the total is bounded before the memory. Ported from mumbai's
  `B1/Whir/OsKidsBd.lean`, the bounds by name.
-/

module

public import LeanVM.Guest.B1.Place.OsKids

/-!
# Callees in sequence within bounds

* `os_kids_blockB`: `os_kids_block` with the callees `CompleteAtB … (Bk c.f)`; the total is at most
  the calls' `max (fs c.f) (Bk c.f)` (a skipped call costs its frame).
* `OsCompleteAtPB`: `OsCompleteAtP` within `B`; `os_kidsFromIn_onePB` places one.
* `os_levels_kidsB`: `os_levels_kids` within the levels' calls' `max (fs c.f) (Bk c.f)`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

private theorem os_callsMatch_mapB (σ : Val) (Lk : Layout) : ∀ (cs : List Call) (outs : List (List E × Layout)),
    OutsOk (osKidsOf σ Lk cs) outs → CallsMatch σ cs (osKidsOf σ Lk cs) outs
  | [], [], _ => trivial
  | _ :: cs, _ :: os, ⟨ho, hos⟩ => ⟨rfl, rfl, fun ht => ⟨rfl, (ho ht).1.symm⟩, os_callsMatch_mapB σ Lk cs os hos⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

private theorem os_regionL_appendB {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

/-- The callees' bound is at most the calls' larger of frame and bound. -/
theorem os_kidsBound_le (σ : Val) (Lk : Layout) (Bk : String → ℕ) (cs : List Call) :
    kidsBound fs (fun k => Bk k.f) (osKidsOf σ Lk cs) ≤ (cs.map fun c => max (fs c.f) (Bk c.f)).sum := by
  induction cs with
  | nil => simp [kidsBound, osKidsOf]
  | cons c cs ih =>
    simp only [kidsBound, osKidsOf, List.map_cons, List.sum_cons] at ih ⊢
    refine Nat.add_le_add ?_ ih
    split
    · exact le_max_right _ _
    · exact le_max_left _ _

/-- **Calls complete on fixed words within their bounds**, placed from `b`. -/
theorem os_kids_blockB (κ : ℕ) (Lk : Layout) (σ : Val) (cs : List Call) (Bk : String → ℕ)
    (hc : ∀ c ∈ cs, c.taken = true →
      CompleteAtB fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bk c.f))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout), Within L b N ∧ DisjL L ∧ N ≤ (cs.map fun c => max (fs c.f) (Bk c.f)).sum ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd →
      MemL rd L → MemL rd Lk → (∀ i, RegionL Lk i → R i ∨ Dacc i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b N (fun _ => False) := by
  obtain ⟨N, L, outs, ho, hW, hD, hN, -, hK⟩ := kidsFromIn_of_kidsB (fs := fs) (cert := cert) κ
    (fun k => Bk k.f) (osKidsOf σ Lk cs)
    (fun k hk ht => by
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
      exact hc c hc' ht) b
  refine ⟨N, L, hW, hD, le_trans hN (os_kidsBound_le σ Lk Bk cs), fun rd R Dacc hlow hL hLk hR =>
    kidsFromIn_dend _ _ _ _ (fun _ h => h.elim) (hK rd σ cs R Dacc (os_callsMatch_mapB σ Lk cs outs ho) hlow hL ?_ ?_)⟩
  · intro q hq
    obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact hLk q hq
  · refine regionsOk_of fun k hk _ i hi => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact hR i hi

/-- **`OsCompleteAtP` within `B` words.** -/
def OsCompleteAtPB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (f : String) (Lin : ℕ → Layout)
    (args rets : List E) (Lout : ℕ → Layout) (B : ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout), Within (Lout fp ++ Lown) fp n ∧ DisjL (Lout fp ++ Lown) ∧ n ≤ B ∧
    ∀ rd, LowDef κ rd → MemL rd (Lout fp ++ Lown ++ Lin fp) →
      RelAtIn coreProgram fs cert rd (RegionL (Lin fp)) (RegionL (Lout fp)) fp n f args rets

theorem OsCompleteAtPB.toP {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E}
    {Lout : ℕ → Layout} {B : ℕ} (h : OsCompleteAtPB fs cert κ f Lin args rets Lout B) :
    OsCompleteAtP fs cert κ f Lin args rets Lout := fun fp =>
  let ⟨n, Lown, hW, hD, _, hr⟩ := h fp
  ⟨n, Lown, hW, hD, hr⟩

theorem OsCompleteAtPB.mono {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E}
    {Lout : ℕ → Layout} {B B' : ℕ} (h : OsCompleteAtPB fs cert κ f Lin args rets Lout B) (hB : B ≤ B') :
    OsCompleteAtPB fs cert κ f Lin args rets Lout B' := fun fp =>
  let ⟨n, Lown, hW, hD, hn, hr⟩ := h fp
  ⟨n, Lown, hW, hD, le_trans hn hB, hr⟩

/-- **One such callee within `B`**, placed at `b`, claiming its buffers. -/
theorem os_kidsFromIn_onePB {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E}
    {Lout : ℕ → Layout} {B : ℕ}
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

/-- `OsLvKOk` within the bounds `Bk` by name. -/
structure OsLvKOkB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (Lk : Layout)
    (W S : ℕ → Layout) (Bk : String → ℕ) (k : OsLvK) : Prop where
  A : ∀ c ∈ k.A, c.taken = true →
    CompleteAtB fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bk c.f)
  taken : k.sq.taken = true
  sq : OsCompleteAtPB fs cert κ k.sq.f (fun p => Lk ++ W p) (k.sq.args.map σ) (k.sq.rets.map σ) S
    (Bk k.sq.f)
  B : ∀ p, ∀ c ∈ k.B, c.taken = true →
    CompleteAtB fs cert κ c.f (Lk ++ W p ++ S p) (c.args.map σ) (Returns (c.rets.map σ)) (Bk c.f)

/-- **`os_levels_kids` within the callees' bounds**: the total at most the calls' `max (fs f) (Bk f)`. -/
theorem os_levels_kidsB (κ : ℕ) (σ : Val) (Lk : Layout) (W S : ℕ → ℕ → Layout) (Bk : String → ℕ) :
    ∀ (ks : List OsLvK) (l0 : ℕ), (∀ i (h : i < ks.length), OsLvKOkB fs cert κ σ Lk (W (l0 + i)) (S (l0 + i)) Bk ks[i]) →
      ∀ b, ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = ks.length ∧ Within L b N ∧ DisjL L ∧
        N ≤ ((ks.flatMap OsLvK.calls).map fun c => max (fs c.f) (Bk c.f)).sum ∧
        ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd Lk →
          (∀ i (h : i < ps.length), MemL rd (W (l0 + i) ps[i])) → (∀ i, RegionL Lk i → R i) →
          (∀ l, l0 ≤ l → l < l0 + ks.length → ∀ p i, RegionL (W l p) i → R i) →
          KidsFromIn coreProgram fs cert rd σ R Dacc (ks.flatMap OsLvK.calls) b N (fun _ => False)
  | [], _, _, b => ⟨0, [], [], rfl, fun _ h => by simp at h, disj_nil, Nat.zero_le _, fun _ _ _ _ _ _ _ _ _ =>
      ⟨rfl, fun _ h => h.elim⟩⟩
  | k :: ks, l0, hok, b => by
    have h0 := hok 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    obtain ⟨NA, LA, hWA, hDA, hNA, hKA⟩ := os_kids_blockB (fs := fs) (cert := cert) κ Lk σ k.A Bk h0.A b
    obtain ⟨nS, LS, hWS, hDS, hNS, hKS⟩ := os_kidsFromIn_onePB h0.sq σ k.sq rfl h0.taken rfl rfl (b + NA)
    obtain ⟨NB, LB, hWB, hDB, hNB, hKB⟩ := os_kids_blockB (fs := fs) (cert := cert) κ
      (Lk ++ W l0 (b + NA) ++ S l0 (b + NA)) σ k.B Bk (h0.B (b + NA)) (b + NA + nS)
    obtain ⟨Nr, Lr, ps, hps, hWr, hDr, hNr, hKr⟩ := os_levels_kidsB κ σ Lk W S Bk ks (l0 + 1) (fun i hi => by
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
    · have := le_max_right (fs k.sq.f) (Bk k.sq.f)
      simp only [List.flatMap_cons, OsLvK.calls, List.map_append, List.map_cons, List.sum_append,
        List.sum_cons]
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
      · rcases os_regionL_appendB hi with hi | hi
        · exact Or.inl (hR i hi)
        · exact Or.inl (hRW l0 le_rfl (by simp) _ i hi)
      intro D2 hD2
      refine kidsFromIn_append _ _ _ _ _ _ _ _ (hKB rd R D2 hlow hLB
        (Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨hLk, hW0⟩, hS0⟩) fun i hi => ?_) ?_
      · rcases os_regionL_appendB hi with hi | hi
        · rcases os_regionL_appendB hi with hi | hi
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
