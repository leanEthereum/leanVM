/-
  LeanVM.Guest.B1.Selectors.SharedTotal

  Every valid tree of `shared_selector_tables` on a length `g^n`, `n < 64`, allocates at most its
  frame, its two tables, `shared_selector_tables_loop0`'s `n / 4` iterations' bound and the partial
  nibble's bound.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedVals
public import LeanVM.Guest.Budget.Kids
public import LeanVM.Core.Memory.SizeTotal
public import LeanVM.Core.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings

/-!
# `shared_selector_tables` within its words

On a valid tree at arguments whose length is `g^n`, `n < 64` (`TotalLeOn`): the body's atoms
before its loop hold (they are events of its walk), so its loop runs to `g^(n / 4)` and its
dispatch enters `sel_partial_nibble__L{n % 4}` (`ss_body_vals`); its walk's calls are those two
(`ssCalls`) and its `HeapBuf`s its two tables, `32 (n / 4 + 1)` and `16 (n / 4 + 1)` words (`ss_node`,
at most `768`). With `shared_selector_tables_loop0`'s run's bound (`TotalLeOn … LoopPre`: `K9` per
iteration and its one phantom frame) and the partial nibbles' (`TotalLe`), as hypotheses over any
frame sizes `fs`, `ss_totalLeOn` bounds the tree by `fs "shared_selector_tables" + (fs
"shared_selector_tables_loop0" + 15·K9) + Ksp + 768` (`n / 4 ≤ 15`; `shared_selector_tables_loop0`'s frame
when skipped).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Guest.Memory LeanVM.Core.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem ssS_straight : ssS.all Main.Stmt.straight = true := by decide

theorem ssS_callS : ssS.filterMap Main.Stmt.callS =
    [(some (.n 51), name% «shared_selector_tables_loop0», [.n 52, .n 37, .n 48, .n 0, .n 1, .n 49,
        .n 2], [])] := rfl

theorem ssS_allocSz : ssS.filterMap Main.Stmt.allocSz = [(.n 48, .inr (.n 47)), (.n 49, .inr (.n 46))] :=
  rfl

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

/-- The body after its straight statements: the dispatch, the copies and the `ret`. -/
def ssRest : List Stmt := [ssDispV, .atom (.copy (.n 62) (.n 48)), .atom (.copy (.n 63) (.n 49)),
  .ret [.n 62, .n 63]]

theorem ss_body_split : ssPre ++ [.ret ssRets] = ssS ++ ssRest := by
  rw [ssPre_eq_disp, List.append_assoc]; rfl

/-- The tables' words: at most `48 · 16`. -/
theorem ss_bufs_le {n : ℕ} (hn : n < 64) : ssEqW n + ssGW n ≤ 768 := by
  simp only [ssEqW, ssGW]; omega

/-- **The walk of a valid node of `shared_selector_tables`** on a length `g^n`, `n < 64`: its
straight statements, the partial nibble `n % 4`, the copies; its loop runs to `g^(n / 4)` from `1`,
its tables are `ssEqW n`, `ssGW n` words. -/
theorem ss_walk {rd : Reader} {σ : Val} {bufs : List ℕ} {ks : List Tree} {args rets : List E}
    (hv : (Memory.Tree.node "shared_selector_tables" σ bufs ks).Valid coreProgram rd args rets) {n : ℕ}
    (hn : n < 64) (h3 : args.getD 3 0 = gen ^ n) :
    walk σ (ssPre ++ [.ret ssRets]) = .ret (ssS.flatMap (Main.slEvs σ) ++
        [.call (lName "sel_partial_nibble" (n % 4)) [.n 56, .n 57, .n 58, .n 59, .n 60] [.n 61],
          .atom (.copy (.n 62) (.n 48)), .atom (.copy (.n 63) (.n 49))]) [.n 62, .n 63] ∧
      σ (.n 37) = gen ^ (n / 4) ∧ σ (.n 51) = 1 + gen ^ (n / 4) ∧ σ (.n 52) = 1 ∧
      σ (.n 47) = gen ^ ssEqW n ∧ σ (.n 46) = gen ^ ssGW n := by
  obtain ⟨fn, hf, hp, hbody⟩ := ssFound
  obtain ⟨fn', hf', hpar, es, vs, hw, -, hes, -⟩ := hv
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  have hσ3 : σ (.n 3) = gen ^ n := by
    rw [← h3, ← hpar, hp]; rfl
  have hws : walk σ (ssPre ++ [.ret ssRets]) = (walk σ ssRest).pre (ssS.flatMap (Main.slEvs σ)) := by
    rw [ss_body_split]
    exact walk_pre_straight σ _ ssS ssS_straight
  rw [hbody] at hw
  -- the atoms before the loop hold
  have hatoms : ∀ a, Stmt.atom a ∈ ssA → a.Holds rd σ := by
    intro a ha
    have hX : Ev.atom a ∈ ssS.flatMap (Main.slEvs σ) :=
      List.mem_flatMap.mpr ⟨.atom a, List.mem_append_left _ ha, by simp [Main.slEvs]⟩
    rw [hws] at hw
    cases hd : walk σ ssRest with
    | ret es0 vs0 =>
      rw [hd, Out.pre, Out.ret.injEq] at hw
      exact hes _ (hw.1 ▸ List.mem_append_left _ hX)
    | fall _ => rw [hd, Out.pre] at hw; cases hw
    | stuck => rw [hd, Out.pre] at hw; cases hw
  obtain ⟨e37, e18, e51, e52, e47, e46⟩ := ss_body_vals
    (holdsList_of_atoms (C := fun _ _ _ ↦ True) ssA ssA_atoms hatoms) hn hσ3
  -- the dispatch enters `sel_partial_nibble__L{n % 4}`
  have hdisp : walk σ ssRest =
      .ret [.call (lName "sel_partial_nibble" (n % 4)) [.n 56, .n 57, .n 58, .n 59, .n 60]
        [.n 61], .atom (.copy (.n 62) (.n 48)), .atom (.copy (.n 63) (.n 49))] [.n 62, .n 63] := by
    have hpk := LeanVM.Guest.B1.pick_eq σ (.n 18) [.n 56, .n 57, .n 58, .n 59, .n 60] [.n 61]
      ["sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2",
        "sel_partial_nibble__L3"] 0 (n % 4) (Nat.zero_le _) (by simp; omega) (by omega)
      (by rw [e18, gen_pow_eq_ofK])
    simp only [Nat.sub_zero] at hpk
    rw [lName_sel_partial (n % 4) (by omega)] at hpk
    simp only [ssRest, ssDispV, walk, walk1, hpk, Out.seq, Out.pre, List.append_nil,
      List.cons_append, List.nil_append]
  rw [hws, hdisp, Out.pre]
  exact ⟨rfl, e37, e51, e52, e47, e46⟩

theorem kidsT_true2 : ∀ (cs : List Call) (ks : List Tree),
    KidsT cs [fun _ ↦ True, fun _ ↦ True] ks
  | [], _ => by simp [KidsT]
  | _ :: [], [] => by simp [KidsT]
  | _ :: [], _ :: _ => by simp [KidsT]
  | _ :: _ :: _, [] => by simp [KidsT]
  | _ :: _ :: _, _ :: [] => by simp [KidsT]
  | _ :: _ :: _, _ :: _ :: _ => by simp [KidsT]

theorem lName_sel_ne {j : ℕ} (hj : j < 4) : lName "sel_partial_nibble" j ≠
    name% «shared_selector_tables_loop0» := by
  interval_cases j <;> decide

variable {fs : String → ℕ}

/-- The calls of `shared_selector_tables`' walk: its loop, its partial nibble. -/
def ssCalls (σ : Val) (n : ℕ) : List Call :=
  [⟨name% «shared_selector_tables_loop0», [.n 52, .n 37, .n 48, .n 0, .n 1, .n 49, .n 2], [],
      decide (σ (.n 51) ≠ 0)⟩,
    ⟨lName "sel_partial_nibble" (n % 4), [.n 56, .n 57, .n 58, .n 59, .n 60], [.n 61], true⟩]

/-- **A valid node's calls and tables**: its walk's calls are `ssCalls`, its `HeapBuf`s the two
tables. -/
theorem ss_node {rd : Reader} {σ : Val} {bufs : List ℕ} {ks : List Tree} {args rets : List E}
    (hv : (Memory.Tree.node "shared_selector_tables" σ bufs ks).Valid coreProgram rd args rets)
    (hb : (Memory.Tree.node "shared_selector_tables" σ bufs ks).BufsOk coreProgram) {n : ℕ}
    (hn : n < 64) (h3 : args.getD 3 0 = gen ^ n) :
    (∀ fn es vs, coreProgram.find? "shared_selector_tables" = some fn → walk σ fn.body = .ret es vs →
      calls es = ssCalls σ n) ∧ bufs = [ssEqW n, ssGW n] ∧
      σ (.n 37) = gen ^ (n / 4) ∧ σ (.n 51) = 1 + gen ^ (n / 4) ∧ σ (.n 52) = 1 := by
  obtain ⟨fn, hf, -, hbody⟩ := ssFound
  obtain ⟨hw, e37, e51, e52, e47, e46⟩ := ss_walk hv hn h3
  obtain ⟨-, i2, -, i4⟩ := Main.straight_parts σ ssS ssS_straight
  have hcalls : ∀ fn' es vs, coreProgram.find? "shared_selector_tables" = some fn' →
      walk σ fn'.body = .ret es vs → calls es = ssCalls σ n := by
    intro fn' es vs hf' hw'
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    rw [hbody, hw, Out.ret.injEq] at hw'
    rw [← hw'.1, calls, List.filterMap_append, ← calls, i4, ssS_callS]
    rfl
  refine ⟨hcalls, ?_, e37, e51, e52⟩
  have := hb.1
  rw [Tree.events, Tree.name, hf] at this
  simp only [Tree.val] at this
  rw [hbody, hw, allocs, List.filterMap_append, ← allocs, i2, ssS_allocSz] at this
  refine this.trans ?_
  simp only [List.map_cons, List.map_nil, Sum.elim_inr, e47, e46, gen_pow_eq_ofK]
  rw [logG_spec (by simp only [ssEqW]; omega), logG_spec (by simp only [ssGW]; omega)]
  rfl

/-- **`shared_selector_tables` is within its words.** -/
theorem ss_totalLeOn (K9 Ksp : ℕ)
    (h9 : TotalLeOn coreProgram fs name% «shared_selector_tables_loop0» LoopPre
      (fun a ↦ logG (a.getD 1 0) * K9 + fs name% «shared_selector_tables_loop0»))
    (hsp : ∀ j < 4, TotalLe coreProgram fs (lName "sel_partial_nibble" j) (fun _ ↦ Ksp)) :
    TotalLeOn coreProgram fs "shared_selector_tables" (fun a ↦ ∃ n < 64, a.getD 3 0 = gen ^ n)
      (fun _ ↦ fs "shared_selector_tables" + (fs name% «shared_selector_tables_loop0» + 15 * K9) +
          Ksp + 768) := by
  intro rd t args rets hname ⟨n, hn, h3⟩ hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hname
  subst hname
  obtain ⟨hcalls, hbufs, e37, e51, e52⟩ := ss_node hv hb hn h3
  have hq15 : n / 4 ≤ 15 := by omega
  have htot := Budget.node_total_le fs
    (fun c ↦ if c.f = name% «shared_selector_tables_loop0» then n / 4 * K9 + fs
        name% «shared_selector_tables_loop0» else Ksp) [fun _ ↦ True, fun _ ↦ True] hv hb
    hcalls (by simp [ssCalls]) (kidsT_true2 _ _) (fun c Q hc ht t rets' htn htv htb _ ↦ ?_)
  · refine htot.trans ?_
    rw [hbufs]
    have hb768 := ss_bufs_le hn
    simp only [Budget.callsT, ssCalls, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      lName_sel_ne (show n % 4 < 4 by omega), ↓reduceIte, add_zero]
    have h1 : (if decide (σ (.n 51) ≠ 0) = true then n / 4 * K9 + fs
        name% «shared_selector_tables_loop0» else fs name% «shared_selector_tables_loop0») ≤
        fs name% «shared_selector_tables_loop0» + 15 * K9 := by
      split
      · have := Nat.mul_le_mul_right K9 hq15; omega
      · omega
    omega
  · simp only [ssCalls, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [decide_eq_true_eq] at ht
      have hq0 : 0 < n / 4 := by
        rcases Nat.eq_zero_or_pos (n / 4) with h0 | h0
        · exfalso; apply ht; rw [e51, h0, pow_zero]; exact e_add_eq_zero_iff.mpr rfl
        · exact h0
      have := h9 rd t _ rets' htn (by
        simp only [List.map_cons, List.map_nil, e52, e37]
        exact loopPre_gen hq0 (by omega) _) htv htb
      simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, e37,
        gen_pow_eq_ofK, logG_spec (show n / 4 < 2 ^ 64 - 1 by omega)] at this
      simpa using this
    · have := hsp (n % 4) (by omega) rd t _ rets' htn htv htb
      simpa [lName_sel_ne (show n % 4 < 4 by omega)] using this

end
end LeanVM.Guest.B1.Tables
