/-
  LeanVM.Guest.B1.Place.OsRoundE

  `opening_round` complete placed on its regions, bounded, by a tree of honest shape exact at every node.
-/

module

public import LeanVM.Guest.B1.Place.OsRound
public import LeanVM.Guest.B1.Tables.FlatAtTE
public import LeanVM.Guest.B1.Bits.GrindPlaced

/-!
# `opening_round`, placed and exact

`osRound_completeDTBRE`: `osRoundRegD_holds`' statement within its frame and its callee's, by a tree of honest
shape (`osRoundHonest`) whose every node is exact on the memory: its callee `grind_check__L7` by
`grind_check_completeDTBR` (`completeAt_flatDTBRR`), its own body without a computed hint (`round_pinned`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem round_pinned : Stmt.blockNextOk isComputed pinsInverse Whir.roundBody = true := by decide +kernel

/-- **`opening_round`'s honest shape** on the memory `rd`: its callee exact at every node. -/
def osRoundHonest (rd : Reader) : Tree → Prop :=
  Budget.NodeHonest coreProgram "opening_round" (fun _ => True) (flatCalls roundPre) (fun _ => [])
    [fun t => t.Every (ExactAt coreProgram rd)]

/-- **`opening_round` is complete placed on its regions, within its frame and its callee's, exact at every node**,
on memories defined below `2^κ`, `11 ≤ κ`. -/
theorem osRound_completeDTBRE {κ : ℕ} (hκ : 11 ≤ κ) {args rets : List E} {Lin : Layout}
    (hreg : RegPtrs roundSpec args (RegionL Lin))
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin →
      Whir.MeaningOpeningRound rd args rets ∧ WinTabs rd (args.getD 7 0)) :
    CompleteAtDTBR fs cert κ "opening_round" Lin args (Returns rets)
      (fun rd t => osRoundHonest rd t ∧ t.Every (ExactAt coreProgram rd))
      (fs "opening_round" + fs "grind_check__L7") := by
  classical
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  swap
  · intro fp
    exact ⟨0, [], rets, [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL ↦ absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd0, hl0, hL0⟩ := hex
  obtain ⟨hm0, -⟩ := hpre rd0 hl0 hL0
  obtain ⟨xs, hxl, hrd0, p2, -, -⟩ := Whir.round_complete (C := fun _ _ _ ↦ True) hm0
    (fun _ _ ↦ trivial)
  have h9 : (7 : ℕ) ∈ grindBitsDeployed := by decide
  have hname : grindCheckName 7 = "grind_check__L7" := rfl
  -- every memory holding the caller's words reads `xs` and its honest values hold
  have hall : ∀ rd, LowDef κ rd → MemL rd Lin →
      Stmt.HoldsList (coreProgram.Rel rd) rd (fun v ↦ Whir.rdVals args xs v.idx) Whir.roundBody False
        (fun rs ↦ rs = rets) := by
    intro rd hl hL
    obtain ⟨hm, -⟩ := hpre rd hl hL
    obtain ⟨xs', hxl', hrd', -, -, hh⟩ := Whir.round_complete (C := coreProgram.Rel rd) hm
      (fun w hw ↦ by
        have := grind_relAtIn (fs := fs) (cert := cert) h9 hκ (args := [w, args.getD 7 0]) (rets := [])
          (Lin := Lin) (fun rd' hl' hL' ↦ ⟨rfl, w, args.getD 7 0, rfl, (hpre rd' hl' hL').2, hw⟩)
          0 hl hL
        rw [hname] at this
        exact this.relAt.rel)
    rwa [round_words hreg hL0 hL hxl hxl' hrd0 hrd']
  have hcom := completeAt_flatDTBRR (fs := fs) (cert := cert) Whir.find_opening_round round_not_loop κ Lin args
      rets (pre := roundPre) (by rw [Whir.opening_round_body]; exact roundBody_eq) roundPre_flat
      roundPre_addrs [] (fun _ ↦ []) (fun _ ↦ List.Forall₂.nil)
      (fun _ ↦ [⟨"grind_check__L7", true, [Whir.rdCell (Whir.rdS3 args xs) 1, args.getD 7 0], Lin,
        Returns []⟩]) (fun _ _ ↦ True) (fun rd ↦ [fun t ↦ t.Every (ExactAt coreProgram rd)])
      [fs "grind_check__L7"] (fs "grind_check__L7")
      (fun _ ↦ ⟨fun _ ↦ (grind_check_completeDTBR h9 hκ fun rd hl hL ↦
        ⟨rfl, _, _, rfl, (hpre rd hl hL).2, p2⟩).mono le_rfl fun _ _ h ↦ h.2, trivial⟩)
      (fun _ ↦ by simp [kidsBoundL]) (fun _ _ ↦ le_rfl) ?_ ?_ ?_
  · refine (CompleteAtDTBR.nodeEvery Whir.find_opening_round (by rw [Whir.opening_round_body]; exact round_pinned)
      hcom ?_).mono (by simp) fun _ _ h ↦ h
    intro rd σ _ c T hc _ t _ _ hTt
    obtain ⟨-, hT'⟩ := List.of_mem_zip hc
    rw [List.mem_singleton] at hT'
    subst hT'
    exact hTt
  · intro fp k hk _ i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk; exact Or.inl hi
  · intro fp rd _ hL k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    subst hk; exact hL
  · intro fp outs ho rd hl _ hL
    refine ⟨fun v ↦ Whir.rdVals args xs v.idx, ?_, roundPre_disp _, ?_, by rw [roundPre_allocs]; rfl,
      by rw [roundPre_allocs]; rfl, ?_, ?_, trivial⟩
    · rw [Whir.opening_round_params]
      obtain ⟨hm, -⟩ := hpre rd hl hL
      match args, hm with
      | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], _ => simp [Whir.rdVals, List.range_succ]
    · rw [Whir.opening_round_body]; exact hall rd hl hL
    · rw [flatCalls, roundPre_calls]
      match outs, ho with
      | [o1], ho =>
        obtain ⟨h1, -⟩ := ho
        obtain ⟨e1, -⟩ := h1 rfl
        refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
        · simp [Main.mkCall, Whir.rdVals_49, Whir.rdVals_7]
        · simp [Main.mkCall, e1]
    · rw [roundPre_loads]
      intro q hq
      have hv : ∀ j < 10, Whir.rdVals args xs j = args.getD j 0 := fun j hj ↦ by
        simp [Whir.rdVals, hj]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      have r5 := hreg (5, 5) (by simp [roundSpec])
      have r8 := hreg (8, 1) (by simp [roundSpec])
      have r9 := hreg (9, 2) (by simp [roundSpec])
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [hv 5 (by decide), hv 8 (by decide), hv 9 (by decide)]
      · obtain ⟨i, h, r⟩ := r5 0 (by decide); exact ⟨i, h, Or.inl r⟩
      · obtain ⟨i, h, r⟩ := r5 1 (by decide); exact ⟨i, h, Or.inl r⟩
      · obtain ⟨i, h, r⟩ := r5 2 (by decide); exact ⟨i, h, Or.inl r⟩
      · obtain ⟨i, h, r⟩ := r5 3 (by decide); exact ⟨i, h, Or.inl r⟩
      · obtain ⟨i, h, r⟩ := r5 4 (by decide); exact ⟨i, h, Or.inl r⟩
      · obtain ⟨i, h, r⟩ := r8 0 (by decide); exact ⟨i, h, Or.inl r⟩
      · obtain ⟨i, h, r⟩ := r9 0 (by decide); exact ⟨i, h, Or.inl r⟩
      · obtain ⟨i, h, r⟩ := r9 1 (by decide); exact ⟨i, h, Or.inl r⟩
end
end LeanVM.Guest.B1
