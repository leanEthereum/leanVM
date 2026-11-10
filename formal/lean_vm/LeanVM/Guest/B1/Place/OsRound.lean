/-
  LeanVM.Guest.B1.Place.OsRound

  `opening_round` complete placed on its regions: a flat body whose two callees are
  `grind_check__L9`, placed by its own form.
-/

module

public import LeanVM.Guest.B1.Whir.RoundComplete
public import LeanVM.Guest.Lift.OsCallees
public import LeanVM.Guest.B1.Tables.FlatAt

/-!
# `opening_round`, placed

`osRoundRegD_holds`: on memories defined below `2^κ`, `11 ≤ κ`, `opening_round` is
`OsRoundRegD`. Its body is flat (`completeAt_flatD`), with no buffer; the words at the cursor are
the caller's (`RegPtrs roundSpec`), so every memory holding them reads the same seven words and the
honest values (`Whir.rdVals`) are one valuation; its two callees are `grind_check__L9` on the
nonces' permutations' cell `1`, which pass (`Whir.round_complete`), placed by
`grind_check_completeD`; its loads are the cursor's words and the three stores, the spec's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem round_not_loop : coreProgram.loop "opening_round" = false := by
  rw [Program.loop_of_find? Whir.find_opening_round, Fn.loop, Whir.core7_body]
  rfl

/-- The body before its `ret`. -/
abbrev roundPre : List Stmt := Whir.roundBody.dropLast

theorem roundPre_flat : roundPre.all Stmt.flat = true := by decide

theorem roundPre_addrs : roundPre.filterMap Main.Stmt.addrS = [] := by decide

theorem roundPre_allocs : roundPre.filterMap Main.Stmt.allocSz = [] := by decide

theorem roundPre_noDisp : (roundPre.all fun s ↦ match s with
    | .dispatch .. => false
    | _ => true) = true := by decide

theorem roundPre_disp (σ : Val) : ∀ s ∈ roundPre, DispOk σ s := by
  intro s hs
  have h := List.all_eq_true.mp roundPre_noDisp s hs
  cases s <;> simp_all [DispOk]

theorem roundPre_calls (σ : Val) : roundPre.filterMap (Stmt.callSF σ) =
    [(none, "grind_check__L9", [.n 24, .n 7], []), (none, "grind_check__L9", [.n 69, .n 7], [])] :=
  rfl

/-- A statement other than a branch. -/
def Stmt.noIte : Stmt → Bool
  | .ite .. => false
  | _ => true

theorem flatMap_loadsEv_noIte (σ : Val) : ∀ l : List Stmt, l.all Stmt.noIte = true →
    l.flatMap (loadsEv σ) = l.filterMap Stmt.loadS
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.flatMap_cons, List.filterMap_cons, flatMap_loadsEv_noIte σ l h.2]
    cases s with
    | ite => simp [Stmt.noIte] at h
    | _ => cases hs : Stmt.loadS _ <;> simp [loadsEv, hs]

theorem roundPre_noIte : roundPre.all Stmt.noIte = true := by decide +kernel

theorem roundPre_loadsS : roundPre.filterMap Stmt.loadS =
    [(.n 5, 0), (.n 5, 1), (.n 5, 2), (.n 5, 3), (.n 5, 4), (.n 5, 5), (.n 5, 6), (.n 8, 0),
      (.n 9, 0), (.n 9, 1), (.n 9, 2)] := by
  decide +kernel

theorem roundPre_loads (σ : Val) : roundPre.flatMap (loadsEv σ) =
    [(.n 5, 0), (.n 5, 1), (.n 5, 2), (.n 5, 3), (.n 5, 4), (.n 5, 5), (.n 5, 6), (.n 8, 0),
      (.n 9, 0), (.n 9, 1), (.n 9, 2)] := by
  rw [flatMap_loadsEv_noIte σ _ roundPre_noIte, roundPre_loadsS]

theorem roundBody_eq : Whir.roundBody = roundPre ++ [.ret [.n 121, .n 122, .n 123, .n 124, .n 125,
    .n 128, .n 131]] := Whir.roundBody_split

/-- The cursor's seven words, read through the caller's words. -/
theorem round_words {args : List E} {Lin : Layout} (hreg : RegPtrs roundSpec args (RegionL Lin))
    {rd rd' : Reader} (hL : MemL rd Lin) (hL' : MemL rd' Lin) {xs xs' : List E} (hx : xs.length = 7)
    (hx' : xs'.length = 7) (h : ReadsAt rd (args.getD 5 0) xs) (h' : ReadsAt rd' (args.getD 5 0) xs') :
    xs = xs' := by
  refine List.ext_getElem (by rw [hx, hx']) fun t h1 h2 ↦ ?_
  obtain ⟨i, hi, hr⟩ := hreg (5, 7) (by simp [roundSpec]) t (by omega)
  have a := (h t h1).2
  have b := (h' t h2).2
  rw [hi] at a b
  rw [Main.memL_agree hL hL' i hr] at a
  rw [a] at b
  exact Option.some.inj b

/-- **`opening_round` is complete placed on its regions**, on memories defined below `2^κ`,
`11 ≤ κ`. -/
theorem osRoundRegD_holds {κ : ℕ} (hκ : 11 ≤ κ) : OsRoundRegD fs cert κ := by
  intro args rets Lin hreg hpre
  classical
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  swap
  · intro fp
    exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL ↦ absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd0, hl0, hL0⟩ := hex
  obtain ⟨hm0, -⟩ := hpre rd0 hl0 hL0
  obtain ⟨xs, hxl, hrd0, p1, p2, -, -⟩ := Whir.round_complete (C := fun _ _ _ ↦ True) hm0
    (fun _ _ ↦ trivial)
  have h9 : (9 : ℕ) ∈ grindBitsDeployed := by decide
  have hname : grindCheckName 9 = "grind_check__L9" := rfl
  -- every memory holding the caller's words reads `xs` and its honest values hold
  have hall : ∀ rd, LowDef κ rd → MemL rd Lin →
      Stmt.HoldsList (coreProgram.Rel rd) rd (fun v ↦ Whir.rdVals args xs v.idx) Whir.roundBody False
        (fun rs ↦ rs = rets) := by
    intro rd hl hL
    obtain ⟨hm, -⟩ := hpre rd hl hL
    obtain ⟨xs', hxl', hrd', -, -, -, hh⟩ := Whir.round_complete (C := coreProgram.Rel rd) hm
      (fun w hw ↦ by
        have := grind_relAtIn (fs := fs) (cert := cert) h9 hκ (args := [w, args.getD 7 0]) (rets := [])
          (Lin := Lin) (fun rd' hl' hL' ↦ ⟨rfl, w, args.getD 7 0, rfl, (hpre rd' hl' hL').2, hw⟩)
          0 hl hL
        rw [hname] at this
        exact this.relAt.rel)
    rwa [round_words hreg hL0 hL hxl hxl' hrd0 hrd']
  have hcom : CompleteAtD fs cert κ "opening_round" Lin args (Returns rets) := by
    refine completeAt_flatD Whir.find_opening_round round_not_loop κ Lin args rets
      (pre := roundPre) (by rw [Whir.core7_body]; exact roundBody_eq) roundPre_flat roundPre_addrs []
      (fun _ ↦ []) (fun _ ↦ List.Forall₂.nil)
      (fun _ ↦ [⟨"grind_check__L9", true, [Whir.rdCell (Whir.rdS1 args xs) 1, args.getD 7 0], Lin,
        Returns []⟩, ⟨"grind_check__L9", true, [Whir.rdCell (Whir.rdS3 args xs) 1, args.getD 7 0], Lin,
        Returns []⟩]) ?_ ?_ ?_ ?_
    · intro fp k hk _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact (grind_check_completeD h9 hκ) _ _ Lin fun rd hl hL ↦
          ⟨rfl, _, _, rfl, (hpre rd hl hL).2, p1⟩
      · exact (grind_check_completeD h9 hκ) _ _ Lin fun rd hl hL ↦
          ⟨rfl, _, _, rfl, (hpre rd hl hL).2, p2⟩
    · intro fp k hk _ i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> exact Or.inl hi
    · intro fp rd _ hL k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> exact hL
    · intro fp outs ho rd hl _ hL
      refine ⟨fun v ↦ Whir.rdVals args xs v.idx, ?_, roundPre_disp _, ?_, by rw [roundPre_allocs]; rfl,
        by rw [roundPre_allocs]; rfl, ?_, ?_⟩
      · rw [Whir.core7_params]
        obtain ⟨hm, -⟩ := hpre rd hl hL
        match args, hm with
        | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], _ => simp [Whir.rdVals, List.range_succ]
      · rw [Whir.core7_body]; exact hall rd hl hL
      · rw [roundPre_calls]
        match outs, ho with
        | [o1, o2], ho =>
          obtain ⟨h1, h2, -⟩ := ho
          obtain ⟨e1, -⟩ := h1 rfl
          obtain ⟨e2, -⟩ := h2 rfl
          refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
          · simp [Main.mkCall, Whir.rdVals_24, Whir.rdVals_7]
          · simp [Main.mkCall, e1]
          · simp [Main.mkCall, Whir.rdVals_69, Whir.rdVals_7]
          · simp [Main.mkCall, e2]
      · rw [roundPre_loads]
        intro q hq
        have hv : ∀ j < 10, Whir.rdVals args xs j = args.getD j 0 := fun j hj ↦ by
          simp [Whir.rdVals, hj]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        have r5 := hreg (5, 7) (by simp [roundSpec])
        have r8 := hreg (8, 1) (by simp [roundSpec])
        have r9 := hreg (9, 3) (by simp [roundSpec])
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [hv 5 (by decide), hv 8 (by decide), hv 9 (by decide)]
        · obtain ⟨i, h, r⟩ := r5 0 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r5 1 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r5 2 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r5 3 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r5 4 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r5 5 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r5 6 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r8 0 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r9 0 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r9 1 (by decide); exact ⟨i, h, Or.inl r⟩
        · obtain ⟨i, h, r⟩ := r9 2 (by decide); exact ⟨i, h, Or.inl r⟩
  exact hcom

end
end LeanVM.Guest.B1
