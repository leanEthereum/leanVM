/-
  LeanVM.Guest.B1.VsC.CertifyH

  `certify_stack`'s honest words: the group order `stackHints` pushes, its ranking, the buffers.
-/

module

public import LeanVM.Guest.B1.Stack.Certify
public import LeanVM.Guest.B1.VsC.StackOrder
public import LeanVM.Guest.B1.VsC.Vsc8CalleesA

/-!
# `certify_stack`'s honest words

On a layout, `kv` the kappa sources' exponents (`csKv`), the honest prover's group order
(`csOrd`, `stackHints`' `mergeSort`) read as `ρ r` is a `Ranking` (`csRank_ranking`): `stackHints`
sizes a group by its first block's kappa, which is the group's `csKap` (`stackKappas_get`), and
its first blocks are the groups' `b0` (`csStarts_eq`). The node's own words: the keys, the sizes,
the order, each group's offset `group_at`, the outputs (`csWords`), whose outputs place the stack
(`csOut_placed`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Stack
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The groups' sizes and first blocks -/

theorem csStarts_eq : Prover.stackBlockGroups stackBlocks = csGroups.map (·.b0) := by decide +kernel

/-- A block's source and adjustment are its group's. -/
def blockSrcOk (b : ℕ) : Bool :=
  (stackBlocks.getD b default).adj == (csG (grpOf b)).adj &&
    match (stackBlocks.getD b default).source with
    | .memory => (csG (grpOf b)).src == 1
    | .table t => (csG (grpOf b)).src == 2 + t

set_option maxRecDepth 100000 in
theorem blockSrc_ok : ∀ b < 52, blockSrcOk b = true := by decide +kernel

/-- The kappa sources' exponents of a layout. -/
abbrev csKv (layout : Layout) : ℕ → ℕ := kvOf layout.logMemory layout.tableLogHeights

theorem stackKappas_get (layout : Layout) {b : ℕ} (hb : b < 52) :
    (stackKappas layout).getD b 0 = csKap (csKv layout) (grpOf b) := by
  have h := blockSrc_ok b hb
  have hl : b < stackBlocks.length := by rw [stackBlocks_length]; exact hb
  unfold stackKappas
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
  simp only [Option.map_some, Option.getD_some]
  unfold blockSrcOk at h
  rw [List.getD_eq_getElem _ _ hl] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨ha, hs⟩ := h
  unfold csKap
  rw [ha]
  congr 1
  cases hsrc : stackBlocks[b].source with
  | memory =>
    rw [hsrc] at hs; simp only [beq_iff_eq] at hs
    rw [hs]; rfl
  | table t =>
    rw [hsrc] at hs; simp only [beq_iff_eq] at hs
    rw [hs]; show _ = kvOf _ _ _; unfold kvOf
    rw [ite_neg' (by omega), ite_neg' (by omega), Nat.add_sub_cancel_left]

/-! ## The order -/

/-- The honest group order (`stackHints`'). -/
def csOrd (kappas : List ℕ) : List ℕ :=
  let starts := Prover.stackBlockGroups stackBlocks
  let start := fun g ↦ starts.getD g 0
  let size := fun g ↦ kappas.getD (start g) 0
  (List.range starts.length).mergeSort fun g h ↦
    decide (size h < size g) || (decide (size g = size h) && decide (start g ≤ start h))

theorem stackHints_eq (kappas : List ℕ) :
    Prover.stackHints kappas = [("stk_group_order", (csOrd kappas).map Prover.count)] := rfl

/-- The group of rank `r`. -/
def csRho (kappas : List ℕ) (r : ℕ) : ℕ := (csOrd kappas).getD r 0

theorem csStart_get {g : ℕ} (hg : g < 8) : (Prover.stackBlockGroups stackBlocks).getD g 0 = (csG g).b0 := by
  have hl : g < csGroups.length := by simp [csGroups]; exact hg
  rw [csStarts_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
  simp only [Option.map_some, Option.getD_some, csG, List.getD_eq_getElem _ _ hl]

theorem csSize_get' (layout : Layout) {g : ℕ} (hg : g < 8) :
    (stackKappas layout).getD (csG g).b0 0 = csKap (csKv layout) g := by
  have h := grpOf_block g hg 0 (by have := (csGroups_facts g hg).2.2.1; omega)
  rw [Nat.add_zero] at h
  rw [stackKappas_get layout (by have := groups_b0_le g hg; omega), h]

theorem csSize_get (layout : Layout) {g : ℕ} (hg : g < 8) :
    (stackKappas layout).getD ((Prover.stackBlockGroups stackBlocks).getD g 0) 0 = csKap (csKv layout) g := by
  rw [csStart_get hg, csSize_get' layout hg]

/-- **The honest order is a ranking**, its steps below the key bound: on group kappas at most
`33`. -/
theorem csOrd_facts (layout : Layout) (hk : ∀ g < 8, csKap (csKv layout) g ≤ 33) :
    (csOrd (stackKappas layout)).Perm (List.range 8) ∧ Ranking (csKv layout) (csRho (stackKappas layout)) ∧
      ∀ r < 7, csN (csKv layout) (csRho (stackKappas layout) r) <
        csN (csKv layout) (csRho (stackKappas layout) (r + 1)) + 1 + 1802 := by
  obtain ⟨hlen, hnd, hlt⟩ := stackGroups_facts
  set starts := Prover.stackBlockGroups stackBlocks with hst
  have hst8 : ∀ g < 8, starts.getD g 0 < 53 := fun g hg => by
    rw [hst, csStart_get hg]; have := groups_b0_le g hg; omega
  have ho := honestOrder_ok starts.length (fun g ↦ (stackKappas layout).getD (starts.getD g 0) 0)
    (fun g ↦ starts.getD g 0)
    (fun g hg => by
      show (stackKappas layout).getD (starts.getD g 0) 0 ≤ 33
      rw [hlen] at hg; rw [hst, csSize_get layout hg]; exact hk g hg)
    (fun g hg => by rw [hlen] at hg; exact hst8 g hg)
    (fun g hg h hh e => by
      rw [hlen] at hg hh
      simp only [hst, csStart_get hg, csStart_get hh] at e
      exact groups_b0_inj g hg h hh e)
  have hord : csOrd (stackKappas layout) = (List.range starts.length).mergeSort
      (grpCmp (fun g ↦ (stackKappas layout).getD (starts.getD g 0) 0) (fun g ↦ starts.getD g 0)) := rfl
  obtain ⟨hperm, hstep⟩ := ho
  rw [← hord, hlen] at hperm
  have hlen8 : (csOrd (stackKappas layout)).length = 8 := by rw [hperm.length_eq, List.length_range]
  have hmem : ∀ r < 8, csRho (stackKappas layout) r < 8 := fun r hr => by
    unfold csRho
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_range.mp (hperm.subset (List.getElem_mem _))
  have hpair : ∀ r < 7, 53 * csKap (csKv layout) (csRho (stackKappas layout) (r + 1)) +
      (csG (csRho (stackKappas layout) r)).b0 <
        53 * csKap (csKv layout) (csRho (stackKappas layout) r) + (csG (csRho (stackKappas layout) (r + 1))).b0 ∧
      53 * csKap (csKv layout) (csRho (stackKappas layout) r) + (csG (csRho (stackKappas layout) (r + 1))).b0 <
        53 * csKap (csKv layout) (csRho (stackKappas layout) (r + 1)) +
          (csG (csRho (stackKappas layout) r)).b0 + 1 + 1802 := fun r hr => by
    have h := hstep r (by rw [← hord, hlen8]; omega)
    simp only [← hord] at h
    have e1 := hmem r (by omega)
    have e2 := hmem (r + 1) (by omega)
    unfold csRho at e1 e2 ⊢
    rw [List.getD_eq_getElem _ _ (by omega)] at e1 ⊢
    rw [List.getD_eq_getElem _ _ (by omega)] at e2 ⊢
    simp only [hst, csStart_get e1, csStart_get e2, csSize_get' layout e1, csSize_get' layout e2] at h
    exact h
  refine ⟨hperm, ⟨hmem, fun r hr => ?_⟩, fun r hr => ?_⟩
  · have := hpair r hr
    have := groups_b0_le _ (hmem r (by omega))
    have := groups_b0_le _ (hmem (r + 1) (by omega))
    unfold csN; omega
  · have := hpair r hr
    have := groups_b0_le _ (hmem r (by omega))
    have := groups_b0_le _ (hmem (r + 1) (by omega))
    unfold csN; omega

/-- The rank of group `g`. -/
def csRk (kappas : List ℕ) (g : ℕ) : ℕ := (csOrd kappas).idxOf g

theorem csRk_facts {kappas : List ℕ} (hp : (csOrd kappas).Perm (List.range 8)) :
    (∀ g < 8, csRk kappas g < 8 ∧ csRho kappas (csRk kappas g) = g) ∧
      ∀ r < 8, csRk kappas (csRho kappas r) = r := by
  have hl : (csOrd kappas).length = 8 := by rw [hp.length_eq, List.length_range]
  have hnd : (csOrd kappas).Nodup := hp.nodup_iff.mpr List.nodup_range
  refine ⟨fun g hg => ?_, fun r hr => ?_⟩
  · have hm : g ∈ csOrd kappas := hp.symm.subset (List.mem_range.mpr hg)
    have hi := List.idxOf_lt_length_of_mem hm
    refine ⟨by unfold csRk; omega, ?_⟩
    unfold csRho csRk
    rw [List.getD_eq_getElem _ _ hi, List.getElem_idxOf]
  · unfold csRho csRk
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hnd.idxOf_getElem _ _

end
end LeanVM.Guest.B1.VsC
