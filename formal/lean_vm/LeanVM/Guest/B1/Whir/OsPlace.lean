/-
  LeanVM.Guest.B1.Whir.OsPlace

  A straight-line function returning one of its buffers, complete in the placed form from its
  callees' composition.
-/

module

public import LeanVM.Guest.B1.Uniform

/-!
# Straight-line bodies returning a buffer, placed

`os_completeAt_place`: a function whose body is straight-line statements then a `ret`, with no
`frameAddr`, is `CompleteAtD` returning its buffer `jo`, when at every frame pointer a valuation
satisfies its body with the allocator's pointers on every memory holding its buffers and the
caller's words, and its callees, from after its buffers, are `KidsFromIn` on every memory holding
also their layout. Its loads are in its buffers or the caller's words because they hold on every
such memory (`os_addr_in_regionL`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A word every memory holding `M` holds at `A` lies in `M`'s region.** -/
theorem os_addr_in_regionL {κ : ℕ} {M : Layout} {A : K} {v : E}
    (hall : ∀ rd, LowDef κ rd → MemL rd M → rd A = some v) {rd : Reader} (hlow : LowDef κ rd)
    (hL : MemL rd M) : ∃ i, A = gpow i ∧ RegionL M i := by
  classical
  by_contra hn
  simp only [not_exists, not_and] at hn
  let rd2 : Reader := fun B => if B = A then some (v + 1) else rd B
  have hlow2 : LowDef κ rd2 := fun i hi => by
    simp only [rd2]; split
    · rfl
    · exact hlow i hi
  have hL2 : MemL rd2 M := by
    intro q hq k hk
    refine ⟨(hL q hq k hk).1, ?_⟩
    rw [Main.addr_ofK]
    have hne : gpow (q.1 + k) ≠ A := fun he => hn (q.1 + k) he.symm ⟨q, hq, by omega, by omega⟩
    simp only [rd2, hne, ↓reduceIte]
    rw [← Main.addr_ofK]; exact (hL q hq k hk).2
  have := hall rd2 hlow2 hL2
  simp only [rd2, ↓reduceIte, Option.some.injEq] at this
  exact one_ne_zero (by linear_combination this : (1 : E) = 0)

theorem os_kidsFromIn_rmono {rd : Reader} {σ : Val} {R R' : ℕ → Prop} (hR : ∀ i, R i → R' i) :
    ∀ (cs : List Call) (Dacc : ℕ → Prop) (b n : ℕ) (D : ℕ → Prop),
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n D → KidsFromIn coreProgram fs cert rd σ R' Dacc cs b n D
  | [], _, _, _, _, h => h
  | _ :: cs, _, _, _, _, ⟨m, n', Rk, Dk, hn, hRk, hc, hk⟩ =>
    ⟨m, n', Rk, Dk, hn, fun i hi => (hRk i hi).imp_left (hR i), hc, os_kidsFromIn_rmono hR cs _ _ _ _ hk⟩

theorem os_take_getD_drop {α : Type} : ∀ (l : List α) (j : ℕ) (d : α), j < l.length →
    l = l.take j ++ l.getD j d :: l.drop (j + 1)
  | [], _, _, h => absurd h (by simp)
  | a :: l, 0, _, _ => rfl
  | a :: l, j + 1, d, h => by
    simp only [List.take_succ_cons, List.getD_cons_succ, List.drop_succ_cons, List.cons_append]
    exact congrArg (a :: ·) (os_take_getD_drop l j d (by simpa using h))

theorem os_bases_getD : ∀ (b : ℕ) (sizes : List ℕ) (j : ℕ), j < sizes.length →
    (bases b sizes).getD j 0 = b + (sizes.take j).sum
  | _, [], _, h => absurd h (by simp)
  | b, s :: sizes, 0, _ => by simp [bases]
  | b, s :: sizes, j + 1, h => by
    simp only [bases, List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
    rw [os_bases_getD (b + s) sizes j (by simpa using h)]; ring

theorem os_length_bases : ∀ (b : ℕ) (sizes : List ℕ), (bases b sizes).length = sizes.length
  | _, [] => rfl
  | b, _ :: sizes => by simp [bases, os_length_bases _ sizes]

theorem os_bufL_getD {b : ℕ} {sizes : List ℕ} {own : List (List E)} {j : ℕ}
    (hown : List.Forall₂ (fun c s => c.length ≤ s) own sizes) (hj : j < sizes.length) :
    (bufL b sizes own).getD j default = ((bases b sizes).getD j 0, own.getD j []) := by
  have hl1 : (bases b sizes).length = sizes.length := os_length_bases b sizes
  have hl2 : own.length = sizes.length := hown.length_eq
  simp only [bufL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl1 ▸ hj),
    List.getElem?_eq_getElem (hl2 ▸ hj), Option.getD_some]
  rw [List.getElem?_eq_getElem (by simp [hl1, hl2, hj]), Option.getD_some, List.getElem_zip]

/-- **A straight-line function returning its buffer `jo` is complete, placed.** -/
theorem os_completeAt_place {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E) (Out : List E → Layout → Prop)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Main.Stmt.straight = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (jo : ℕ) (hjo : jo < sizes.length) {C : CallRel}
    (h : ∀ fp, ∃ (σ : Val) (own : List (List E)) (rets : List E) (N : ℕ) (L : Layout) (Dk : ℕ → Prop) (cs : List Call),
      (pre.filterMap Main.Stmt.callS).map (Main.mkCall σ) = cs ∧
      List.Forall₂ (fun c s => c.length ≤ s) own sizes ∧
      Out rets [(fp + fs f + (sizes.take jo).sum, own.getD jo [])] ∧
      Within L (fp + fs f + sizes.sum) N ∧ DisjL L ∧ fn.params.map σ = args ∧
      (∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd Lin →
        Stmt.HoldsList C rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (gpow b))) ∧
      ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd L → MemL rd Lin →
        KidsFromIn coreProgram fs cert rd σ (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes own) i)
          (fun _ => False) cs (fp + fs f + sizes.sum) N Dk) :
    CompleteAtD fs cert κ f Lin args Out := by
  intro fp
  obtain ⟨σ, own, rets, N, L, Dk, cs, hcs, hown, hout, hW, hD, hp, hh, hK⟩ := h fp
  set B := bufL (fp + fs f) sizes own with hB
  have hlen : jo < B.length := by
    simp only [hB, bufL, List.length_zip, os_length_bases, hown.length_eq, Nat.min_self]; exact hjo
  have hq : B.getD jo default = (fp + fs f + (sizes.take jo).sum, own.getD jo []) := by
    rw [hB, os_bufL_getD hown hjo, os_bases_getD _ _ _ hjo]
  have hsplit := os_take_getD_drop B jo default hlen
  rw [hq] at hsplit
  set Lo : Layout := [(fp + fs f + (sizes.take jo).sum, own.getD jo [])]
  set Lr : Layout := B.take jo ++ B.drop (jo + 1)
  have hperm : (Lo ++ (Lr ++ L)).Perm (B ++ L) := by
    rw [← List.append_assoc]
    refine List.Perm.append_right L ?_
    have := (List.perm_middle (l₁ := B.take jo) (l₂ := B.drop (jo + 1))
      (a := (fp + fs f + (sizes.take jo).sum, own.getD jo []))).symm
    rw [← hsplit] at this
    exact this
  have hmem : ∀ q, q ∈ Lo ++ (Lr ++ L) ↔ q ∈ B ++ L := fun q => hperm.mem_iff
  have hBW : Within B (fp + fs f) sizes.sum := bufL_within _ _ _ hown
  have hBD : DisjL B := bufL_disj _ _ _ hown
  have hBL : DisjL (B ++ L) := disj_append hBD hD hBW hW le_rfl
  refine ⟨fs f + sizes.sum + N, Lr ++ L, rets, Lo, hout, fun q hq => ?_, ?_, fun rd hlow hL => ?_⟩
  · rcases List.mem_append.mp ((hmem q).mp hq) with hq | hq
    · have := hBW q hq; omega
    · have := hW q hq; omega
  · exact hBL.perm hperm.symm fun h => Or.symm h
  have hLm : MemL rd (B ++ L) := fun q hq => hL q (List.mem_append_left _ ((hmem q).mpr hq))
  have hLin : MemL rd Lin := fun q hq => hL q (List.mem_append_right _ hq)
  obtain ⟨hB1, hL1⟩ := Main.memL_append.mp hLm
  have hw := Main.walk_straight σ vs pre hst
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ pre hst
  have hsat : ∀ rd', LowDef κ rd' → MemL rd' B → MemL rd' Lin →
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd' σ) ∧ vs.map σ = rets := fun rd' h1 h2 h3 => by
    have hs := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf))
      (hh rd' h1 h2 h3).1
    rw [hw] at hs
    exact ⟨fun e he => (hs.1 e he).1, hs.2⟩
  obtain ⟨hes, hr⟩ := hsat rd hlow hB1 hLin
  obtain ⟨-, hsz, hbuf⟩ := hh rd hlow hB1 hLin
  have hal : allocs σ (pre.flatMap (Main.slEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL B i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (Main.slEvs σ))) (pre.flatMap (Main.slEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ hown i hi)
  have hk := os_kidsFromIn_rmono (fs := fs) (cert := cert)
    (R' := fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (Main.slEvs σ))) (pre.flatMap (Main.slEvs σ)) i)
    (fun i hi => hi.imp_right (hown' i)) _ _ _ _ _ (hK rd hlow hB1 hL1 hLin)
  rw [← hcs, ← i4, show fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (Main.slEvs σ))).sum by rw [hal]] at hk
  have hrel := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL Lo) (Dk := Dk) (N := N) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr hes
    (by rw [hal, i1]; exact hbuf) (by rw [i3, haddrs]; simp) hk (fun A hA => ?_) (fun i hi => ?_)
  · rw [hal] at hrel
    exact hrel
  · obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
    match e, hea with
    | .atom (.load d p off), hea =>
      simp only [Ev.loadAddr?, Option.some.injEq] at hea
      subst hea
      have hall : ∀ rd', LowDef κ rd' → MemL rd' (B ++ Lin) → rd' ((σ p).limb 0 * gpow off) = some (σ d) :=
        fun rd' h1 h2 => by
          obtain ⟨h21, h22⟩ := Main.memL_append.mp h2
          exact ((hsat rd' h1 h21 h22).1 _ he).2
      obtain ⟨i, hi, hreg⟩ := os_addr_in_regionL hall hlow (Main.memL_append.mpr ⟨hB1, hLin⟩)
      refine ⟨i, hi, ?_⟩
      obtain ⟨q, hq, h1, h2⟩ := hreg
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (hown' i ⟨q, hq, h1, h2⟩)
      · exact Or.inr (Or.inl ⟨q, hq, h1, h2⟩)
  · obtain ⟨q, hq, h1, h2⟩ := hi
    have hq' : q = (fp + fs f + (sizes.take jo).sum, own.getD jo []) := by simpa [Lo] using hq
    have hqB : q ∈ B := by rw [hsplit, hq']; simp
    exact Or.inl (hown' i ⟨q, hqB, h1, h2⟩)

end
end LeanVM.Guest.B1
