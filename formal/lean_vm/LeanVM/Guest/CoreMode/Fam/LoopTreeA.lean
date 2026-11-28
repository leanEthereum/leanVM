/-
  LeanVM.Guest.CoreMode.Fam.LoopTreeA

  `LoopTree`'s counter bound on the aligned allocator: every loop instance of `Tree.instsA` has a
  counter `g^e` with `e` plus its subtree's words within the bound, and a tree's words within the
  words its aligned placement uses.
-/

module

public import LeanVM.Guest.CoreMode.Fam.LoopTree
public import LeanVM.Guest.Memory.AllocA

/-!
# A loop's counter on the aligned allocator

`total_le_endA`: placed from `c` with its block before the cursor, a subtree's words fit before its
end, `c + t.total ≤ t.endA d` when `c + t.block ≤ d` (a loop's tail call's block is in its
caller's, `blockLast`). So `total_le_wordsA`: a tree's words are at most the words its aligned
placement uses. `instsA_ctr`: `insts_ctr` over `Tree.instsA`, whose instances are `Tree.insts`'s
trees at other positions.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {lp al : String → Bool}

mutual
/-- **A subtree's words fit before its end**, its block before the cursor. -/
theorem total_le_endA : ∀ (t : Tree) (c d : ℕ), c + t.block fs lp ≤ d → c + t.total fs ≤ t.endA fs lp al d
  | .node f σ bufs kids, c, d, h => by
      rw [endA_node, total_node]
      rw [Tree.block] at h
      by_cases hl : lp f = true
      · simp only [hl, ↓reduceIte] at h ⊢
        have := total_le_endL kids (c + fs f + bufs.sum) (d + bufs.sum) (by omega)
        rw [totalKids_eq_sum]
        omega
      · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
        have := total_le_endF kids (c + fs f + bufs.sum) (d + bufs.sum) (by omega)
        rw [totalKids_eq_sum]
        omega
  | .phantom f σ, c, d, h => by
      rw [endA_phantom, Tree.total]
      rw [Tree.block] at h
      exact h

theorem total_le_endF : ∀ (ks : List Tree) (c d : ℕ), c ≤ d →
    c + (ks.map (Tree.total fs)).sum ≤ Tree.endF fs lp al d ks
  | [], c, d, h => by rw [endF_nil]; simpa using h
  | k :: ks, c, d, h => by
      rw [endF_cons, List.map_cons, List.sum_cons]
      have h1 := total_le_endA k d (allocBase (al k.name) d + k.block fs lp)
        (by have := le_allocBase (al k.name) d; omega)
      have h2 := total_le_endF ks (c + k.total fs) (k.endA fs lp al (allocBase (al k.name) d + k.block fs lp))
        (by omega)
      omega

theorem total_le_endL : ∀ (ks : List Tree) (c d : ℕ), c + Tree.blockLast fs lp ks ≤ d →
    c + (ks.map (Tree.total fs)).sum ≤ Tree.endL fs lp al d ks
  | [], c, d, h => by rw [endL_nil]; rw [Tree.blockLast] at h; simpa using h
  | [k], c, d, h => by
      rw [endL_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [Tree.blockLast] at h
      exact total_le_endA k c d h
  | k :: k' :: ks, c, d, h => by
      rw [endL_cons, List.map_cons, List.sum_cons]
      rw [Tree.blockLast] at h
      have h1 := total_le_endA k d (allocBase (al k.name) d + k.block fs lp)
        (by have := le_allocBase (al k.name) d; omega)
      have h2 := total_le_endL (k' :: ks) (c + k.total fs)
        (k.endA fs lp al (allocBase (al k.name) d + k.block fs lp)) (by omega)
      omega
end

/-- **A tree's words are at most those its aligned placement uses.** -/
theorem total_le_wordsA (t : Tree) : t.total fs ≤ t.wordsA fs lp al := by
  have := total_le_endA (fs := fs) (lp := lp) (al := al) t 0 (t.block fs lp) (by omega)
  rw [Nat.zero_add] at this
  exact this

variable {rd : Reader} {P : Core.Program} {H : Inst → ℕ → E × E}

mutual
/-- **Every loop instance's counter fits**, on the aligned allocator. -/
theorem instsA_ctr (hfs : ∀ f, 1 ≤ fs f) (hP : ProgOk P) {B : ℕ} : ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E)
    {args rets : List E}, t.Valid P rd args rets → t.total fs + 1 ≤ B → CtrOk P fs B t →
      ∀ J ∈ t.instsA fs lp al H p hdr, CtrOk P fs B J.t
  | .node f σ bufs kids, p, hdr, args, rets, hv, hB, hC, J, hJ => by
    rw [instsA_node, List.mem_cons] at hJ
    rcases hJ with rfl | hJ
    · exact hC
    · have hv' := hv
      unfold Tree.Valid at hv'
      obtain ⟨fn, hf, -, es, vs, hw, -, hh, hk⟩ := hv'
      exact instsKidsA_ctr hfs hP kids σ (calls es) _ 0 _ hk (calls_ok hP hf hC hB hw hh)
        (fun k hk' ↦ kid_total_lt hfs hk') hB J hJ
  | .phantom .., _, _, _, _, hv, _, _, _, _ => hv.elim

theorem instsKidsA_ctr (hfs : ∀ f, 1 ≤ fs f) (hP : ProgOk P) {B : ℕ} : ∀ (ks : List Tree) (σ : Val)
    (cs : List Call) (I : Inst) (j : ℕ) (ps : List (ℕ × ℕ)) {T0 : ℕ}, Tree.KidsValid P rd σ cs ks →
      (∀ c ∈ cs, CallOk σ B T0 c) → (∀ k ∈ ks, k.total fs + 1 ≤ T0) → T0 + 1 ≤ B →
      ∀ J ∈ Tree.instsKidsA fs lp al H I j ps ks, CtrOk P fs B J.t
  | [], _, _, _, _, _, _, _, _, _, _, J, hJ => by rw [instsKidsA_nil] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, _, _, _, _, [], _, _, _, _, _, J, hJ => by
    rw [instsKidsA_nil_left] at hJ; exact absurd hJ List.not_mem_nil
  | k :: ks, σ, c :: cs, I, j, p :: ps, T0, ⟨hn, hc, hks⟩, hcs, hkt, hT, J, hJ => by
    rw [instsKidsA_cons, List.mem_append] at hJ
    rcases hJ with hJ | hJ
    · cases ht : c.taken
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hc
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hc
        rw [instsA_phantom, List.mem_singleton] at hJ
        subst hJ
        intro _ _ _ _ _ h; cases h
      · simp only [ht, ↓reduceIte] at hc
        have hk1 := hkt k List.mem_cons_self
        refine instsA_ctr hfs hP k p _ hc (by omega) ?_ J hJ
        intro f' σ' bufs' kids' fn' hk' hf' hl
        subst hk'
        have hc' := hc
        unfold Tree.Valid at hc'
        obtain ⟨fn'', hf'', hpm, -⟩ := hc'
        have hfe := Option.some.inj (hf''.symm.trans hf')
        subst fn''
        obtain ⟨hln, _, -, hs, -⟩ := hP.loop f' fn' hf' hl
        obtain ⟨-, -, p0, prest, hps, -⟩ := loopShape_spec hs
        simp only [Tree.name] at hn
        subst f'
        obtain ⟨a, rest, e, ha, hσa, he⟩ := hcs c List.mem_cons_self hln
        rw [hps, ha] at hpm
        simp only [List.map_cons, List.cons.injEq] at hpm
        exact ⟨p0, prest, e, hps, hpm.1.trans hσa, by omega⟩
    · exact instsKidsA_ctr hfs hP ks σ cs I (j + 1) ps hks (fun c' h ↦ hcs c' (List.mem_cons_of_mem _ h))
        (fun k' h ↦ hkt k' (List.mem_cons_of_mem _ h)) hT J hJ
  | _ :: _, _, [], _, _, _ :: _, _, h, _, _, _, _, _ => h.elim
end

end

end LeanVM.Guest.Res
