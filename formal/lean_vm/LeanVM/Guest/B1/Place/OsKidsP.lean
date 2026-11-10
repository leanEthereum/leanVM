/-
  LeanVM.Guest.B1.Place.OsKidsP

  The callees of a straight-line body placed in sequence, per level a group of calls whose layout
  depends on where the group is placed (f128's `open_stacked`: the first squeeze's decoder and the
  squeeze loop).
-/

module

public import LeanVM.Guest.B1.Place.OsKidsB

/-!
# Callees in sequence, per level a placed group

* `OsGroupD`, `OsGroupB`: a list of calls placed from any `b`, reading `Lin b` and claiming
  `Lout b` (within `B` words); `os_group_one`, `os_group_oneB`: one call complete at every frame
  pointer (`OsCompleteAtP`, `OsCompleteAtPB`).
* `os_levels_kidsP`, `os_levels_kidsPB`: per level, calls on `Lk`, then a group at `p` reading
  `Lk ++ W p` and claiming `S p`, then calls reading `Lk ++ W p ++ S p`; the groups' positions
  `ps` are returned (`os_levels_kids` with a group in place of one call).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A group of calls placed from any `b`**, reading `Lin b`, claiming `Lout b`. -/
def OsGroupD (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (cs : List Call)
    (Lin Lout : ℕ → Layout) : Prop :=
  ∀ b, ∃ (n : ℕ) (Lown : Layout), Within (Lout b ++ Lown) b n ∧ DisjL (Lout b ++ Lown) ∧
    ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd (Lout b ++ Lown) → MemL rd (Lin b) →
      (∀ i, RegionL (Lin b) i → R i ∨ Dacc i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n (RegionL (Lout b))

/-- **`OsGroupD` within `B` words.** -/
def OsGroupB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (cs : List Call)
    (Lin Lout : ℕ → Layout) (B : ℕ) : Prop :=
  ∀ b, ∃ (n : ℕ) (Lown : Layout), Within (Lout b ++ Lown) b n ∧ DisjL (Lout b ++ Lown) ∧ n ≤ B ∧
    ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd (Lout b ++ Lown) → MemL rd (Lin b) →
      (∀ i, RegionL (Lin b) i → R i ∨ Dacc i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n (RegionL (Lout b))

theorem OsGroupB.toD {κ : ℕ} {σ : Val} {cs : List Call} {Lin Lout : ℕ → Layout} {B : ℕ}
    (h : OsGroupB fs cert κ σ cs Lin Lout B) : OsGroupD fs cert κ σ cs Lin Lout := fun b ↦
  let ⟨n, Lown, hW, hD, _, hK⟩ := h b
  ⟨n, Lown, hW, hD, hK⟩

theorem os_group_one {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E}
    {Lout : ℕ → Layout} (h : OsCompleteAtP fs cert κ f Lin args rets Lout) (σ : Val) (c : Call)
    (hf : c.f = f) (ht : c.taken = true) (ha : c.args.map σ = args) (hr : c.rets.map σ = rets) :
    OsGroupD fs cert κ σ [c] Lin Lout := fun b ↦ os_kidsFromIn_oneP h σ c hf ht ha hr b

theorem os_group_oneB {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E}
    {Lout : ℕ → Layout} {B : ℕ} (h : OsCompleteAtPB fs cert κ f Lin args rets Lout B) (σ : Val)
    (c : Call) (hf : c.f = f) (ht : c.taken = true) (ha : c.args.map σ = args)
    (hr : c.rets.map σ = rets) : OsGroupB fs cert κ σ [c] Lin Lout B := fun b ↦
  os_kidsFromIn_onePB h σ c hf ht ha hr b

theorem os_regionL_append {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

/-- A level's frames: the calls before the group, the group, the calls after it. -/
structure OsLvKP where
  A : List Call
  P : List Call
  B : List Call

/-- A level's frames in order. -/
def OsLvKP.calls (k : OsLvKP) : List Call := k.A ++ (k.P ++ k.B)

/-- A level's callees: those before the group on `Lk`, the group at `p` on `Lk ++ W p` claiming
`S p`, those after it on `Lk ++ W p ++ S p` for every `p`. -/
structure OsLvKPOk (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (Lk : Layout)
    (W S : ℕ → Layout) (k : OsLvKP) : Prop where
  A : ∀ c ∈ k.A, c.taken = true → CompleteAtD fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ))
  P : OsGroupD fs cert κ σ k.P (fun p => Lk ++ W p) S
  B : ∀ p, ∀ c ∈ k.B, c.taken = true →
    CompleteAtD fs cert κ c.f (Lk ++ W p ++ S p) (c.args.map σ) (Returns (c.rets.map σ))

/-- `OsLvKPOk` within the bounds `Bk` by name. -/
structure OsLvKPOkB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (Lk : Layout)
    (W S : ℕ → Layout) (Bk : String → ℕ) (k : OsLvKP) : Prop where
  A : ∀ c ∈ k.A, c.taken = true →
    CompleteAtB fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bk c.f)
  P : OsGroupB fs cert κ σ k.P (fun p => Lk ++ W p) S (k.P.map fun c => max (fs c.f) (Bk c.f)).sum
  B : ∀ p, ∀ c ∈ k.B, c.taken = true →
    CompleteAtB fs cert κ c.f (Lk ++ W p ++ S p) (c.args.map σ) (Returns (c.rets.map σ)) (Bk c.f)

/-- **The levels' callees in sequence** from `b`: their total, their layout, the groups'
positions. -/
theorem os_levels_kidsP (κ : ℕ) (σ : Val) (Lk : Layout) (W S : ℕ → ℕ → Layout) :
    ∀ (ks : List OsLvKP) (l0 : ℕ),
      (∀ i (h : i < ks.length), OsLvKPOk fs cert κ σ Lk (W (l0 + i)) (S (l0 + i)) ks[i]) →
      ∀ b, ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = ks.length ∧ Within L b N ∧ DisjL L ∧
        ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd Lk →
          (∀ i (h : i < ps.length), MemL rd (W (l0 + i) ps[i])) → (∀ i, RegionL Lk i → R i) →
          (∀ l, l0 ≤ l → l < l0 + ks.length → ∀ p i, RegionL (W l p) i → R i) →
          KidsFromIn coreProgram fs cert rd σ R Dacc (ks.flatMap OsLvKP.calls) b N (fun _ => False)
  | [], _, _, b => ⟨0, [], [], rfl, fun _ h => by simp at h, disj_nil, fun _ _ _ _ _ _ _ _ _ =>
      ⟨rfl, fun _ h => h.elim⟩⟩
  | k :: ks, l0, hok, b => by
    have h0 := hok 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    obtain ⟨NA, LA, hWA, hDA, hKA⟩ := os_kids_block (fs := fs) (cert := cert) κ Lk σ k.A h0.A b
    obtain ⟨nS, LS, hWS, hDS, hKS⟩ := h0.P (b + NA)
    obtain ⟨NB, LB, hWB, hDB, hKB⟩ := os_kids_block (fs := fs) (cert := cert) κ
      (Lk ++ W l0 (b + NA) ++ S l0 (b + NA)) σ k.B (h0.B (b + NA)) (b + NA + nS)
    obtain ⟨Nr, Lr, ps, hps, hWr, hDr, hKr⟩ := os_levels_kidsP κ σ Lk W S ks (l0 + 1) (fun i hi => by
      have := hok (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, show l0 + (i + 1) = l0 + 1 + i by omega] at this
      exact this) (b + NA + nS + NB)
    have hW3 : Within (LB ++ Lr) (b + NA + nS) (NB + Nr) := by
      rw [within_append]; exact ⟨hWB.mono le_rfl (by omega), hWr.mono (by omega) (by omega)⟩
    have hW2 : Within ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)) (b + NA) (nS + (NB + Nr)) := by
      rw [within_append]; exact ⟨hWS.mono le_rfl (by omega), hW3.mono (by omega) (by omega)⟩
    refine ⟨NA + (nS + (NB + Nr)), LA ++ ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)), (b + NA) :: ps,
      by simp [hps], ?_, disj_append hDA (disj_append hDS (disj_append hDB hDr hWB hWr le_rfl) hWS hW3
        le_rfl) hWA hW2 le_rfl, ?_⟩
    · rw [within_append]
      exact ⟨hWA.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
    · intro rd R Dacc hlow hL hLk hWm hR hRW
      obtain ⟨hLA, hL'⟩ := Main.memL_append.mp hL
      obtain ⟨hLS, hL''⟩ := Main.memL_append.mp hL'
      obtain ⟨hLB, hLr⟩ := Main.memL_append.mp hL''
      have hW0 : MemL rd (W l0 (b + NA)) := hWm 0 (by simp)
      have hS0 : MemL rd (S l0 (b + NA)) := (Main.memL_append.mp hLS).1
      simp only [List.flatMap_cons, OsLvKP.calls, List.append_assoc]
      refine kidsFromIn_append _ _ _ _ _ _ _ _ (hKA rd R Dacc hlow hLA hLk fun i hi => Or.inl (hR i hi)) ?_
      intro D1 _
      refine kidsFromIn_append _ _ _ _ _ _ _ _ (hKS rd R D1 hlow hLS (Main.memL_append.mpr ⟨hLk, hW0⟩)
        fun i hi => ?_) ?_
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

/-- **`os_levels_kidsP` within the callees' bounds**: the total at most the calls'
`max (fs f) (Bk f)`. -/
theorem os_levels_kidsPB (κ : ℕ) (σ : Val) (Lk : Layout) (W S : ℕ → ℕ → Layout)
    (Bk : String → ℕ) :
    ∀ (ks : List OsLvKP) (l0 : ℕ),
      (∀ i (h : i < ks.length), OsLvKPOkB fs cert κ σ Lk (W (l0 + i)) (S (l0 + i)) Bk ks[i]) →
      ∀ b, ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = ks.length ∧ Within L b N ∧ DisjL L ∧
        N ≤ ((ks.flatMap OsLvKP.calls).map fun c => max (fs c.f) (Bk c.f)).sum ∧
        ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd Lk →
          (∀ i (h : i < ps.length), MemL rd (W (l0 + i) ps[i])) → (∀ i, RegionL Lk i → R i) →
          (∀ l, l0 ≤ l → l < l0 + ks.length → ∀ p i, RegionL (W l p) i → R i) →
          KidsFromIn coreProgram fs cert rd σ R Dacc (ks.flatMap OsLvKP.calls) b N (fun _ => False)
  | [], _, _, b => ⟨0, [], [], rfl, fun _ h => by simp at h, disj_nil, Nat.zero_le _,
      fun _ _ _ _ _ _ _ _ _ => ⟨rfl, fun _ h => h.elim⟩⟩
  | k :: ks, l0, hok, b => by
    have h0 := hok 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    obtain ⟨NA, LA, hWA, hDA, hNA, hKA⟩ := os_kids_blockB (fs := fs) (cert := cert) κ Lk σ k.A Bk h0.A b
    obtain ⟨nS, LS, hWS, hDS, hNS, hKS⟩ := h0.P (b + NA)
    obtain ⟨NB, LB, hWB, hDB, hNB, hKB⟩ := os_kids_blockB (fs := fs) (cert := cert) κ
      (Lk ++ W l0 (b + NA) ++ S l0 (b + NA)) σ k.B Bk (h0.B (b + NA)) (b + NA + nS)
    obtain ⟨Nr, Lr, ps, hps, hWr, hDr, hNr, hKr⟩ := os_levels_kidsPB κ σ Lk W S Bk ks (l0 + 1)
      (fun i hi => by
        have := hok (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, show l0 + (i + 1) = l0 + 1 + i by omega] at this
        exact this) (b + NA + nS + NB)
    have hW3 : Within (LB ++ Lr) (b + NA + nS) (NB + Nr) := by
      rw [within_append]; exact ⟨hWB.mono le_rfl (by omega), hWr.mono (by omega) (by omega)⟩
    have hW2 : Within ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)) (b + NA) (nS + (NB + Nr)) := by
      rw [within_append]; exact ⟨hWS.mono le_rfl (by omega), hW3.mono (by omega) (by omega)⟩
    refine ⟨NA + (nS + (NB + Nr)), LA ++ ((S l0 (b + NA) ++ LS) ++ (LB ++ Lr)), (b + NA) :: ps,
      by simp [hps], ?_, disj_append hDA (disj_append hDS (disj_append hDB hDr hWB hWr le_rfl) hWS hW3
        le_rfl) hWA hW2 le_rfl, ?_, ?_⟩
    · rw [within_append]
      exact ⟨hWA.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
    · simp only [List.flatMap_cons, OsLvKP.calls, List.map_append, List.sum_append]
      omega
    · intro rd R Dacc hlow hL hLk hWm hR hRW
      obtain ⟨hLA, hL'⟩ := Main.memL_append.mp hL
      obtain ⟨hLS, hL''⟩ := Main.memL_append.mp hL'
      obtain ⟨hLB, hLr⟩ := Main.memL_append.mp hL''
      have hW0 : MemL rd (W l0 (b + NA)) := hWm 0 (by simp)
      have hS0 : MemL rd (S l0 (b + NA)) := (Main.memL_append.mp hLS).1
      simp only [List.flatMap_cons, OsLvKP.calls, List.append_assoc]
      refine kidsFromIn_append _ _ _ _ _ _ _ _ (hKA rd R Dacc hlow hLA hLk fun i hi => Or.inl (hR i hi)) ?_
      intro D1 _
      refine kidsFromIn_append _ _ _ _ _ _ _ _ (hKS rd R D1 hlow hLS (Main.memL_append.mpr ⟨hLk, hW0⟩)
        fun i hi => ?_) ?_
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
