/-
  LeanVM.Guest.B1.Selectors.SharedTotal

  Every valid tree of `shared_selector_tables` on a length `g^n`, `n < 64`, allocates at most its
  frame, `__loop8`'s `n / 4` iterations' bound and the partial nibble's bound.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedVals
public import LeanVM.Guest.Budget.Kids
public import LeanVM.Guest.Memory.SizeTotal
public import LeanVM.Guest.Memory.LoopPre

/-!
# `shared_selector_tables` within its words

On a valid tree at arguments whose length is `g^n`, `n < 64` (`TotalLeOn`): the body's atoms
before its loop hold (they are events of its walk), so its loop runs to `g^(n / 4)` and its
dispatch enters `sel_partial_nibble__L{n % 4}` (`ss_body_vals`); its walk's calls are those two
(`ss_calls`). With `__loop8`'s run's bound (`TotalLeOn … LoopPre`: `K9` per iteration and its
one phantom frame) and the partial nibbles' (`TotalLe`), as hypotheses over any frame sizes `fs`,
`ss_totalLeOn` bounds the tree by `fs "shared_selector_tables" + (fs "__loop8" + 15·K9) + Ksp`
(`n / 4 ≤ 15`; `__loop8`'s frame when skipped).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem ssS_straight : ssS.all Main.Stmt.straight = true := by decide

theorem ssS_callS : ssS.filterMap Main.Stmt.callS =
    [(some (.n 44), "__loop8", [.n 45, .n 39, .n 0, .n 2, .n 3, .n 1, .n 4], [])] := rfl

theorem ssS_allocSz : ssS.filterMap Main.Stmt.allocSz = [] := rfl

theorem ssA_atoms : ssA.all (fun s ↦ match s with | .atom _ => true | _ => false) = true := by
  decide

/-- A block of atoms each of which holds holds. -/
theorem holdsList_of_atoms {C : CallRel} {rd : Reader} {σ : Val} :
    ∀ (l : List Stmt), l.all (fun s ↦ match s with | .atom _ => true | _ => false) = true →
      (∀ a, Stmt.atom a ∈ l → a.Holds rd σ) → Stmt.HoldsList C rd σ l True (fun _ ↦ True)
  | [], _, _ => trivial
  | s :: l, hl, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    match s, hl.1 with
    | .atom a, _ =>
      exact ⟨h a List.mem_cons_self,
        holdsList_of_atoms l hl.2 fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

theorem kidsT_true2 : ∀ (cs : List Call) (ks : List Tree),
    KidsT cs [fun _ ↦ True, fun _ ↦ True] ks
  | [], _ => by simp [KidsT]
  | _ :: [], [] => by simp [KidsT]
  | _ :: [], _ :: _ => by simp [KidsT]
  | _ :: _ :: _, [] => by simp [KidsT]
  | _ :: _ :: _, _ :: [] => by simp [KidsT]
  | _ :: _ :: _, _ :: _ :: _ => by simp [KidsT]

theorem lName_sel_ne {j : ℕ} (hj : j < 4) : lName "sel_partial_nibble" j ≠ "__loop8" := by
  interval_cases j <;> decide

variable {fs : String → ℕ}

/-- **`shared_selector_tables` is within its words.** -/
theorem ss_totalLeOn (K9 Ksp : ℕ)
    (h9 : TotalLeOn coreProgram fs "__loop8" LoopPre
      (fun a ↦ logG (a.getD 1 0) * K9 + fs "__loop8"))
    (hsp : ∀ j < 4, TotalLe coreProgram fs (lName "sel_partial_nibble" j) (fun _ ↦ Ksp)) :
    TotalLeOn coreProgram fs "shared_selector_tables" (fun a ↦ ∃ n < 64, a.getD 5 0 = gen ^ n)
      (fun _ ↦ fs "shared_selector_tables" + (fs "__loop8" + 15 * K9) + Ksp) := by
  intro rd t args rets hname ⟨n, hn, h5⟩ hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hname
  subst hname
  obtain ⟨fn, hf, hp, hbody⟩ := ssFound
  have hv' := hv
  obtain ⟨fn', hf', hpar, es, vs, hw, -, hes, -⟩ := hv'
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  have hσ5 : σ (.n 5) = gen ^ n := by
    rw [← h5, ← hpar, hp]; rfl
  -- the walk: the straight statements, then the dispatch
  have hws : walk σ fn.body =
      (walk σ [ssDispV, .ret []]).pre (ssS.flatMap (Main.slEvs σ)) := by
    rw [hbody, ssPre_eq_disp, List.append_assoc]
    exact walk_pre_straight σ _ ssS ssS_straight
  -- the atoms before the loop hold
  have hatoms : ∀ a, Stmt.atom a ∈ ssA → a.Holds rd σ := by
    intro a ha
    have hX : Ev.atom a ∈ ssS.flatMap (Main.slEvs σ) := by
      refine List.mem_flatMap.mpr ⟨.atom a, ?_, by simp [Main.slEvs]⟩
      rw [← ssA_eq_take] at ha
      exact List.mem_of_mem_take ha
    rw [hws] at hw
    cases hd : walk σ [ssDispV, .ret []] with
    | ret es0 vs0 =>
      rw [hd, Out.pre, Out.ret.injEq] at hw
      exact hes _ (hw.1 ▸ List.mem_append_left _ hX)
    | fall _ => rw [hd, Out.pre] at hw; cases hw
    | stuck => rw [hd, Out.pre] at hw; cases hw
  obtain ⟨e39, e20, e44, e45⟩ := ss_body_vals
    (holdsList_of_atoms (C := fun _ _ _ ↦ True) ssA ssA_atoms hatoms) hn hσ5
  -- the dispatch enters `sel_partial_nibble__L{n % 4}`
  have hdisp : walk σ [ssDispV, .ret []] =
      .ret [.call (lName "sel_partial_nibble" (n % 4)) [.n 49, .n 50, .n 51, .n 52, .n 53]
        [.n 54]] [] := by
    have hpk := LeanVM.Guest.B1.pick_eq σ (.n 20) [.n 49, .n 50, .n 51, .n 52, .n 53] [.n 54]
      ["sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2",
        "sel_partial_nibble__L3"] 0 (n % 4) (Nat.zero_le _) (by simp; omega) (by omega)
      (by rw [e20, gen_pow_eq_ofK])
    simp only [Nat.sub_zero] at hpk
    rw [lName_sel_partial (n % 4) (by omega)] at hpk
    simp only [ssDispV, walk, walk1, hpk, Out.seq, Out.pre, List.append_nil]
  have hes : es = ssS.flatMap (Main.slEvs σ) ++
      [.call (lName "sel_partial_nibble" (n % 4)) [.n 49, .n 50, .n 51, .n 52, .n 53] [.n 54]] := by
    rw [hws, hdisp, Out.pre, Out.ret.injEq] at hw
    exact hw.1.symm
  obtain ⟨-, i2, -, i4⟩ := Main.straight_parts σ ssS ssS_straight
  -- the calls
  let cs : List Call := [⟨"__loop8", [.n 45, .n 39, .n 0, .n 2, .n 3, .n 1, .n 4], [],
      decide (σ (.n 44) ≠ 0)⟩,
    ⟨lName "sel_partial_nibble" (n % 4), [.n 49, .n 50, .n 51, .n 52, .n 53], [.n 54], true⟩]
  have hcalls : calls es = cs := by
    rw [hes, calls, List.filterMap_append, ← calls, i4, ssS_callS]
    rfl
  have hbufs : bufs = [] := by
    have := hb.1
    rw [Tree.events, Tree.name, hf] at this
    simp only [Tree.val] at this
    rw [hw, hes, allocs, List.filterMap_append, ← allocs, i2, ssS_allocSz] at this
    exact this.trans rfl
  subst hbufs
  have hq15 : n / 4 ≤ 15 := by omega
  have htot := Budget.node_total_le fs
    (fun c ↦ if c.f = "__loop8" then n / 4 * K9 + fs "__loop8" else Ksp) [fun _ ↦ True, fun _ ↦ True] hv hb
    (fun fn' es' vs' hf'' hw' ↦ by
      rw [hf, Option.some.injEq] at hf''
      subst hf''
      rw [hw, Out.ret.injEq] at hw'
      rw [← hw'.1, hcalls])
    (by simp [cs]) (kidsT_true2 _ _) (fun c Q hc ht t rets' htn htv htb _ ↦ ?_)
  · refine htot.trans ?_
    simp only [Budget.callsT, cs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      lName_sel_ne (show n % 4 < 4 by omega), ↓reduceIte, add_zero]
    have h1 : (if decide (σ (.n 44) ≠ 0) = true then n / 4 * K9 + fs "__loop8" else fs "__loop8") ≤
        fs "__loop8" + 15 * K9 := by
      split
      · have := Nat.mul_le_mul_right K9 hq15; omega
      · omega
    omega
  · simp only [cs, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [decide_eq_true_eq] at ht
      have hq0 : 0 < n / 4 := by
        rcases Nat.eq_zero_or_pos (n / 4) with h0 | h0
        · exfalso; apply ht; rw [e44, h0, pow_zero]; exact e_add_eq_zero_iff.mpr rfl
        · exact h0
      have := h9 rd t _ rets' htn (by
        simp only [List.map_cons, List.map_nil, e45, e39]
        exact loopPre_gen hq0 (by omega) _) htv htb
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, e39,
        gen_pow_eq_ofK, logG_spec (show n / 4 < 2 ^ 64 - 1 by omega)] at this
      simpa using this
    · have := hsp (n % 4) (by omega) rd t _ rets' htn htv htb
      simpa [lName_sel_ne (show n % 4 < 4 by omega)] using this

end
end LeanVM.Guest.B1.Tables
