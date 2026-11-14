/-
  LeanVM.Guest.B1.Place.OsKidsBT

  `os_levels_kidsB` with each level's calls by trees of predicates of the memory.
-/

module

public import LeanVM.Guest.B1.Place.OsKidsB
public import LeanVM.Guest.Budget.BoundedR

/-!
# The levels' callees in sequence, with tree predicates

* `kidsFromIn_toT`: callees `KidsFromIn` are `KidsFromInT` of predicates every tree satisfies;
* `kidsFromInT_append`: `kidsFromIn_append` with the predicates appended;
* `os_kids_blockBT`: `os_kids_blockB` by trees of `T rd` (`CompleteAtDTBR`);
* `OsCompleteAtPBT`, `os_kidsFromIn_onePBT`: `OsCompleteAtPB`, `os_kidsFromIn_onePB` by a tree of `T rd`;
* `OsLvKOkBT`, `lvTs`, `os_levels_kidsBT`: `OsLvKOkB`, `os_levels_kidsB` with level `l`'s calls before its positions by
  trees of `TA rd`, its positions' by one of `TS rd`, its calls after them by trees of `TB l rd`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **Callees `KidsFromIn` by trees of predicates every tree satisfies.** -/
theorem kidsFromIn_toT {rd : Reader} {σ : Val} {R : ℕ → Prop} : ∀ {cs : List Call} {Dacc : ℕ → Prop} {b n : ℕ}
    {D : ℕ → Prop} (Ts : List (Tree → Prop)), (∀ T ∈ Ts, ∀ t, T t) →
    KidsFromIn coreProgram fs cert rd σ R Dacc cs b n D → KidsFromInT coreProgram fs cert rd σ R Dacc cs Ts b n D
  | [], _, _, _, _, _, _, h => h
  | c :: _, _, _, _, _, Ts, hT, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ => by
    refine ⟨m, n', Rk, Dk, hn, hR, ?_, kidsFromIn_toT Ts.tail (fun T hm ↦ hT T (List.mem_of_mem_tail hm)) hk⟩
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hc ⊢
      obtain ⟨t, h⟩ := hc
      refine ⟨t, h, ?_⟩
      cases Ts with
      | nil => trivial
      | cons T _ => exact hT T List.mem_cons_self t
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc ⊢
      exact hc

/-- **`kidsFromIn_append` with tree predicates.** -/
theorem kidsFromInT_append {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs1 cs2 : List Call) (Ts1 Ts2 : List (Tree → Prop)) (Dacc : ℕ → Prop) (b n1 n2 : ℕ) (D1 D : ℕ → Prop),
      Ts1.length = cs1.length →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs1 Ts1 b n1 D1 →
      (∀ Dacc' : ℕ → Prop, (∀ i, D1 i → Dacc' i) →
        KidsFromInT coreProgram fs cert rd σ R Dacc' cs2 Ts2 (b + n1) n2 D) →
      KidsFromInT coreProgram fs cert rd σ R Dacc (cs1 ++ cs2) (Ts1 ++ Ts2) b (n1 + n2) D
  | [], cs2, [], Ts2, Dacc, b, n1, n2, D1, D, _, ⟨hn, hD⟩, h2 => by
    subst hn; simpa using h2 Dacc hD
  | _ :: cs1, cs2, T :: Ts1, Ts2, Dacc, b, n1, n2, D1, D, hl, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩, h2 =>
    ⟨m, n' + n2, Rk, Dk, by omega, hR, hc,
      kidsFromInT_append cs1 cs2 Ts1 Ts2 _ (b + m) n' n2 D1 D (by simpa using hl) hk fun Dacc' h => by
        rw [show b + m + n' = b + n1 by omega]; exact h2 Dacc' h⟩
  | [], _, _ :: _, _, _, _, _, _, _, _, hl, _, _ | _ :: _, _, [], _, _, _, _, _, _, _, hl, _, _ => by
    simp at hl

private theorem osT_regionL_append {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

private theorem os_callsMatch_mapBT (σ : Val) (Lk : Layout) : ∀ (cs : List Call) (outs : List (List E × Layout)),
    OutsOk (osKidsOf σ Lk cs) outs → CallsMatch σ cs (osKidsOf σ Lk cs) outs
  | [], [], _ => trivial
  | _ :: cs, _ :: os, ⟨ho, hos⟩ => ⟨rfl, rfl, fun ht => ⟨rfl, (ho ht).1.symm⟩, os_callsMatch_mapBT σ Lk cs os hos⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem os_kidsBoundL_le (σ : Val) (Lk : Layout) (Bk : String → ℕ) : ∀ cs : List Call,
    kidsBoundL fs (osKidsOf σ Lk cs) (cs.map fun c => Bk c.f) ≤ (cs.map fun c => max (fs c.f) (Bk c.f)).sum
  | [] => by simp [kidsBoundL, osKidsOf]
  | c :: cs => by
    have ih := os_kidsBoundL_le σ Lk Bk cs
    simp only [kidsBoundL, osKidsOf, List.map_cons, List.sum_cons, List.headD_cons, List.tail_cons] at ih ⊢
    refine Nat.add_le_add ?_ ih
    split
    · exact le_max_right _ _
    · exact le_max_left _ _

theorem os_kidsDTBR (κ : ℕ) (Lk : Layout) (σ : Val) (Bk : String → ℕ) (T : Reader → Tree → Prop) :
    ∀ cs : List Call, (∀ c ∈ cs, c.taken = true →
      CompleteAtDTBR fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) T (Bk c.f)) →
    KidsDTBR fs cert κ (osKidsOf σ Lk cs) (fun rd => cs.map fun _ => T rd) (cs.map fun c => Bk c.f)
  | [], _ => trivial
  | c :: cs, h => ⟨fun ht => h c List.mem_cons_self ht,
      os_kidsDTBR κ Lk σ Bk T cs fun c' hc' ht => h c' (List.mem_cons_of_mem _ hc') ht⟩

/-- **Calls on fixed words within their bounds by trees of `T rd`**, placed from `b`. -/
theorem os_kids_blockBT (κ : ℕ) (Lk : Layout) (σ : Val) (cs : List Call) (Bk : String → ℕ)
    (T : Reader → Tree → Prop)
    (hc : ∀ c ∈ cs, c.taken = true →
      CompleteAtDTBR fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) T (Bk c.f))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout), Within L b N ∧ DisjL L ∧ N ≤ (cs.map fun c => max (fs c.f) (Bk c.f)).sum ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd →
      MemL rd L → MemL rd Lk → (∀ i, RegionL Lk i → R i ∨ Dacc i) →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs (cs.map fun _ => T rd) b N (fun _ => False) := by
  obtain ⟨N, L, outs, hN, ho, hW, hD, -, hK⟩ := kidsFromInT_of_kidsDTBR (fs := fs) (cert := cert) κ
    (osKidsOf σ Lk cs) _ _ (os_kidsDTBR κ Lk σ Bk T cs hc) b
  refine ⟨N, L, hW, hD, le_trans hN (os_kidsBoundL_le σ Lk Bk cs), fun rd R Dacc hlow hL hLk hR =>
    kidsFromInT_dend _ _ _ _ _ (fun _ h => h.elim)
      (hK rd σ cs R Dacc (os_callsMatch_mapBT σ Lk cs outs ho) hlow hL ?_ ?_)⟩
  · intro q hq
    obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact hLk q hq
  · refine regionsOk_of fun k hk _ i hi => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact hR i hi

/-- **`OsCompleteAtPB` by a tree satisfying a predicate of the memory.** -/
def OsCompleteAtPBT (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (f : String) (Lin : ℕ → Layout)
    (args rets : List E) (Lout : ℕ → Layout) (T : Reader → Tree → Prop) (B : ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout), Within (Lout fp ++ Lown) fp n ∧ DisjL (Lout fp ++ Lown) ∧ n ≤ B ∧
    ∀ rd, LowDef κ rd → MemL rd (Lout fp ++ Lown ++ Lin fp) →
      RelAtInT coreProgram fs cert rd (RegionL (Lin fp)) (RegionL (Lout fp)) fp n f args rets (T rd)

theorem OsCompleteAtPBT.toPB {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E}
    {Lout : ℕ → Layout} {T : Reader → Tree → Prop} {B : ℕ} (h : OsCompleteAtPBT fs cert κ f Lin args rets Lout T B) :
    OsCompleteAtPB fs cert κ f Lin args rets Lout B := fun fp =>
  let ⟨n, Lown, hW, hD, hn, hr⟩ := h fp
  ⟨n, Lown, hW, hD, hn, fun rd hl hm => (hr rd hl hm).relAtIn⟩

theorem OsCompleteAtPB.toT {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E}
    {Lout : ℕ → Layout} {B : ℕ} (h : OsCompleteAtPB fs cert κ f Lin args rets Lout B) :
    OsCompleteAtPBT fs cert κ f Lin args rets Lout (fun _ _ => True) B := fun fp =>
  let ⟨n, Lown, hW, hD, hn, hr⟩ := h fp
  ⟨n, Lown, hW, hD, hn, fun rd hl hm => (hr rd hl hm).relAtInT⟩

theorem OsCompleteAtPBT.mono {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E}
    {Lout : ℕ → Layout} {T T' : Reader → Tree → Prop} {B B' : ℕ}
    (h : OsCompleteAtPBT fs cert κ f Lin args rets Lout T B) (hB : B ≤ B') (hT : ∀ rd t, T rd t → T' rd t) :
    OsCompleteAtPBT fs cert κ f Lin args rets Lout T' B' := fun fp =>
  let ⟨n, Lown, hW, hD, hn, hr⟩ := h fp
  ⟨n, Lown, hW, hD, le_trans hn hB, fun rd hl hm =>
    let ⟨t, ht, hTt⟩ := hr rd hl hm
    ⟨t, ht, hT rd t hTt⟩⟩

/-- **One such callee within `B` by a tree of `T rd`**, placed at `b`, claiming its buffers. -/
theorem os_kidsFromIn_onePBT {κ : ℕ} {f : String} {Lin : ℕ → Layout} {args rets : List E}
    {Lout : ℕ → Layout} {T : Reader → Tree → Prop} {B : ℕ}
    (h : OsCompleteAtPBT fs cert κ f Lin args rets Lout T B) (σ : Val) (c : Call) (hf : c.f = f)
    (ht : c.taken = true) (ha : c.args.map σ = args) (hr : c.rets.map σ = rets) (b : ℕ) :
    ∃ (n : ℕ) (Lown : Layout), Within (Lout b ++ Lown) b n ∧ DisjL (Lout b ++ Lown) ∧ n ≤ B ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd (Lout b ++ Lown) → MemL rd (Lin b) →
        (∀ i, RegionL (Lin b) i → R i ∨ Dacc i) →
        KidsFromInT coreProgram fs cert rd σ R Dacc [c] [T rd] b n (RegionL (Lout b)) := by
  obtain ⟨n, Lown, hW, hD, hn, hrel⟩ := h b
  refine ⟨n, Lown, hW, hD, hn, fun rd R Dacc hlow hL hLin hR =>
    ⟨n, 0, RegionL (Lin b), RegionL (Lout b), by omega, hR, ?_, ⟨rfl, fun i hi => Or.inr ⟨ht, hi⟩⟩⟩⟩
  simp only [ht, ↓reduceIte, List.headD_cons]
  rw [hf, ha, hr]
  exact hrel rd hlow (Main.memL_append.mpr ⟨hL, hLin⟩)

/-- `OsLvKOkB` with the calls before the positions by trees of `TA rd`, the positions' by one of `TS rd`, the calls
after them by trees of `TB rd`. -/
structure OsLvKOkBT (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (Lk : Layout)
    (W S : ℕ → Layout) (Bk : String → ℕ) (TA TS TB : Reader → Tree → Prop) (k : OsLvK) : Prop where
  A : ∀ c ∈ k.A, c.taken = true →
    CompleteAtDTBR fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) TA (Bk c.f)
  taken : k.sq.taken = true
  sq : OsCompleteAtPBT fs cert κ k.sq.f (fun p => Lk ++ W p) (k.sq.args.map σ) (k.sq.rets.map σ) S TS
    (Bk k.sq.f)
  B : ∀ p, ∀ c ∈ k.B, c.taken = true →
    CompleteAtDTBR fs cert κ c.f (Lk ++ W p ++ S p) (c.args.map σ) (Returns (c.rets.map σ)) TB (Bk c.f)

/-- The levels' calls' predicates: level `l`'s calls before its positions `TA rd`, its positions' `TS rd`, its calls
after them `TB l rd`. -/
def lvTs (TA TS : Reader → Tree → Prop) (TB : ℕ → Reader → Tree → Prop) (rd : Reader) :
    ℕ → List OsLvK → List (Tree → Prop)
  | _, [] => []
  | l, k :: ks => (k.A.map fun _ => TA rd) ++ (TS rd :: k.B.map fun _ => TB l rd) ++ lvTs TA TS TB rd (l + 1) ks

/-- **`os_levels_kidsB` with level `l`'s calls by trees of `lvTs TA TS TB`.** -/
theorem os_levels_kidsBT (κ : ℕ) (σ : Val) (Lk : Layout) (W S : ℕ → ℕ → Layout) (Bk : String → ℕ)
    (TA TS : Reader → Tree → Prop) (TB : ℕ → Reader → Tree → Prop) :
    ∀ (ks : List OsLvK) (l0 : ℕ),
      (∀ i (h : i < ks.length), OsLvKOkBT fs cert κ σ Lk (W (l0 + i)) (S (l0 + i)) Bk TA TS (TB (l0 + i)) ks[i]) →
      ∀ b, ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = ks.length ∧ Within L b N ∧ DisjL L ∧
        N ≤ ((ks.flatMap OsLvK.calls).map fun c => max (fs c.f) (Bk c.f)).sum ∧
        ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd Lk →
          (∀ i (h : i < ps.length), MemL rd (W (l0 + i) ps[i])) → (∀ i, RegionL Lk i → R i) →
          (∀ l, l0 ≤ l → l < l0 + ks.length → ∀ p i, RegionL (W l p) i → R i) →
          KidsFromInT coreProgram fs cert rd σ R Dacc (ks.flatMap OsLvK.calls) (lvTs TA TS TB rd l0 ks) b N
            (fun _ => False)
  | [], _, _, b => ⟨0, [], [], rfl, fun _ h => by simp at h, disj_nil, Nat.zero_le _, fun _ _ _ _ _ _ _ _ _ =>
      ⟨rfl, fun _ h => h.elim⟩⟩
  | k :: ks, l0, hok, b => by
    have h0 := hok 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    obtain ⟨NA, LA, hWA, hDA, hNA, hKA⟩ := os_kids_blockBT (fs := fs) (cert := cert) κ Lk σ k.A Bk TA h0.A b
    obtain ⟨nS, LS, hWS, hDS, hNS, hKS⟩ := os_kidsFromIn_onePBT h0.sq σ k.sq rfl h0.taken rfl rfl (b + NA)
    obtain ⟨NB, LB, hWB, hDB, hNB, hKB⟩ := os_kids_blockBT (fs := fs) (cert := cert) κ
      (Lk ++ W l0 (b + NA) ++ S l0 (b + NA)) σ k.B Bk (TB l0) (h0.B (b + NA)) (b + NA + nS)
    obtain ⟨Nr, Lr, ps, hps, hWr, hDr, hNr, hKr⟩ := os_levels_kidsBT κ σ Lk W S Bk TA TS TB ks (l0 + 1) (fun i hi => by
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
      simp only [List.flatMap_cons, OsLvK.calls, lvTs, List.append_assoc, List.cons_append]
      refine kidsFromInT_append _ _ _ _ _ _ _ _ _ _ (by simp)
        (hKA rd R Dacc hlow hLA hLk fun i hi => Or.inl (hR i hi)) ?_
      intro D1 _
      rw [show k.sq :: (k.B ++ ks.flatMap OsLvK.calls) = [k.sq] ++ (k.B ++ ks.flatMap OsLvK.calls) from rfl,
        show TS rd :: ((k.B.map fun _ => TB l0 rd) ++ lvTs TA TS TB rd (l0 + 1) ks) =
          [TS rd] ++ ((k.B.map fun _ => TB l0 rd) ++ lvTs TA TS TB rd (l0 + 1) ks) from rfl]
      refine kidsFromInT_append _ _ _ _ _ _ _ _ _ _ rfl
        (hKS rd R D1 hlow hLS (Main.memL_append.mpr ⟨hLk, hW0⟩) fun i hi => ?_) ?_
      · rcases osT_regionL_append hi with hi | hi
        · exact Or.inl (hR i hi)
        · exact Or.inl (hRW l0 le_rfl (by simp) _ i hi)
      intro D2 hD2
      refine kidsFromInT_append _ _ _ _ _ _ _ _ _ _ (by simp) (hKB rd R D2 hlow hLB
        (Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨hLk, hW0⟩, hS0⟩) fun i hi => ?_) ?_
      · rcases osT_regionL_append hi with hi | hi
        · rcases osT_regionL_append hi with hi | hi
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
