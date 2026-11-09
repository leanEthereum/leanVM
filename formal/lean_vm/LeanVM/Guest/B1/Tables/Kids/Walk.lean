/-
  LeanVM.Guest.B1.Tables.Kids.Walk

  A function's relation loading from a region, from one of its derivations: along the walk its
  derivation takes, its loads in the region and its calls loading from it.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Direct
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# `RelIn` along a derivation

`relIn_of_sem`: if `f` holds of its body with calls by `C`, and along that valuation's walk the
loads lie in `R` and the calls entered load from `R`, then `f`'s relation loads from `R`.
`relIn_of_flat`: the same for a flat body (`Stmt.flat`: atoms, calls, conditional calls,
dispatches, branches of plain atoms), its loads and calls read off its statements. For a loop
calling itself, `relIn_of_flat` at `C = relN rd n` gives the induction on the depth `n`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

/-- **`RelIn` from a derivation by `C`**: along the walk of a valuation satisfying the body, the
loads in `R` and the calls entered `RelIn R`. -/
theorem relIn_of_sem {C : CallRel} {rd : Reader} {R : ℕ → Prop} {f : String} {fn : Fn}
    {args rets : List E} (hf : coreProgram.find? f = some fn) (hsem : fn.Sem C rd args rets)
    (H : ∀ σ, fn.params.map σ = args →
      Stmt.HoldsList C rd σ fn.body False (fun rs ↦ rs = rets) → ∀ es vs,
      walk σ fn.body = .ret es vs →
      (∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧ R i) ∧
        ∀ c ∈ calls es, c.taken = true → coreProgram.RelIn rd R c.f (c.args.map σ) (c.rets.map σ)) :
    coreProgram.RelIn rd R f args rets := by
  obtain ⟨σ, hp, hh⟩ := hsem
  have hsat := walk_sat (P := coreProgram) fn.body
    (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  cases hw : walk σ fn.body with
  | fall es => rw [hw] at hsat; exact hsat.2.elim
  | stuck => rw [hw] at hsat; exact hsat.elim
  | ret es vs =>
    rw [hw] at hsat
    obtain ⟨hok, hr⟩ := hsat
    have hes : ∀ e ∈ es, e.Holds rd σ := fun e he ↦ (hok e he).1
    obtain ⟨hld, hk⟩ := H σ hp hh es vs hw
    exact relIn_of_walk coreProgram_wf hf hp hw hr hes hld hk

/-- **`RelIn` of a flat body**, from a derivation by `C`: for a valuation satisfying the body,
its dispatches name callees, its loads lie in `R` and its calls entered load from `R`. -/
theorem relIn_of_flat {C : CallRel} {rd : Reader} {R : ℕ → Prop} {f : String} {fn : Fn}
    {pre : List Stmt} {vs : List V} {args rets : List E} (hf : coreProgram.find? f = some fn)
    (hb : fn.body = pre ++ [.ret vs]) (hfl : pre.all Stmt.flat = true)
    (hsem : fn.Sem C rd args rets)
    (H : ∀ σ, fn.params.map σ = args →
      Stmt.HoldsList C rd σ fn.body False (fun rs ↦ rs = rets) →
      (∀ s ∈ pre, DispOk σ s) ∧
      (∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i
          ∧ R i) ∧
      ∀ c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ), c.taken = true →
        coreProgram.RelIn rd R c.f (c.args.map σ) (c.rets.map σ))
    (hnl : pre.all noLoadIte = true := by decide +kernel) :
    coreProgram.RelIn rd R f args rets := by
  refine relIn_of_sem hf hsem fun σ hp hh es vs' hw ↦ ?_
  obtain ⟨hd, hld, hk⟩ := H σ hp hh
  have hw' := walk_flat σ vs pre hfl hd
  rw [← hb, hw] at hw'
  injection hw' with hes _
  subst hes
  obtain ⟨-, -, -, hc, hl⟩ := flat_parts σ pre hfl
  refine ⟨fun A hA ↦ ?_, fun c hcm ht ↦ hk c (hc ▸ hcm) ht⟩
  rw [hl, flatMap_loadsEv σ pre hnl] at hA
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
  exact hld q hq

/-- `relIn_of_flat` from `Program.Rel`. -/
theorem relIn_of_flatRel {rd : Reader} {R : ℕ → Prop} {f : String} {fn : Fn}
    {pre : List Stmt} {vs : List V} {args rets : List E} (hf : coreProgram.find? f = some fn)
    (hb : fn.body = pre ++ [.ret vs]) (hfl : pre.all Stmt.flat = true)
    (h : coreProgram.Rel rd f args rets)
    (H : ∀ σ, fn.params.map σ = args →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs ↦ rs = rets) →
      (∀ s ∈ pre, DispOk σ s) ∧
      (∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i
          ∧ R i) ∧
      ∀ c ∈ (pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ), c.taken = true →
        coreProgram.RelIn rd R c.f (c.args.map σ) (c.rets.map σ))
    (hnl : pre.all noLoadIte = true := by decide +kernel) :
    coreProgram.RelIn rd R f args rets := by
  obtain ⟨fn', hf', hsem⟩ := (rel_iff coreProgram f args rets).mp h
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  exact relIn_of_flat hf hb hfl hsem H hnl

/-- A load through a numbered value `.n p` with `(p, B)` in the table, at an offset below `B`;
any other statement. -/
def loadsViaB (tbl : List (ℕ × ℕ)) : Stmt → Bool
  | .atom (.load _ p off) => decide (p = .n p.idx) && tbl.any fun pb ↦ pb.1 == p.idx && decide (off < pb.2)
  | _ => true

/-- **The loads of a block through the table's pointers**, each pointer's run in `R`. -/
theorem loads_via {pre : List Stmt} {tbl : List (ℕ × ℕ)} (h : pre.all (loadsViaB tbl) = true)
    {σ : Val} {R : ℕ → Prop} (hp : ∀ pb ∈ tbl, PtrIn R (σ (.n pb.1)) pb.2) :
    ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧ R
        i := by
  intro q hq
  obtain ⟨s, hs, hsq⟩ := List.mem_filterMap.mp hq
  have hok := List.all_eq_true.mp h s hs
  cases s with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Stmt.loadS, Option.some.injEq] at hsq
      subst hsq
      simp only [loadsViaB, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hok
      obtain ⟨hpn, pb, hpb, he, hoff⟩ := hok
      have := (hp pb hpb).2 off hoff
      rw [he, ← hpn] at this
      exact this
    | _ => simp [Stmt.loadS] at hsq
  | _ => simp [Stmt.loadS] at hsq

/-- An atom, a call, a conditional call or a dispatch. -/
def seqB : Stmt → Bool
  | .atom _ | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

theorem noLoadIte_of_seqB {s : Stmt} (h : seqB s = true) : noLoadIte s = true := by
  cases s <;> simp_all [seqB, noLoadIte]

/-- **A statement of a sequence of such statements holds** when the sequence does. -/
theorem holds_of_mem_seq {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (ss : List Stmt) {next : Prop}, ss.all seqB = true → Stmt.HoldsList C rd σ ss next kret →
      ∀ s ∈ ss, Fwd.SHolds C rd σ s
  | [], _, _, _, _, hs => absurd hs (by simp)
  | s :: ss, next, hok, h, t, ht => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have hrest : Stmt.HoldsList C rd σ ss next kret := by
      cases s with
      | atom _ => exact h.2
      | call _ _ _ => exact h.2
      | callIf _ _ _ => exact h.2.2
      | dispatch _ _ _ _ => exact h.2
      | _ => simp [seqB] at hok
    rcases List.mem_cons.mp ht with he | he
    · subst he
      cases t with
      | atom _ => exact h.1
      | call _ _ _ => exact h.1
      | callIf _ _ _ => exact ⟨h.1, h.2.1⟩
      | dispatch _ _ _ _ => exact h.1
      | _ => simp [seqB] at hok
    · exact holds_of_mem_seq ss hok.2 hrest t he

/-- A statement read at a position of a block is in it. -/
theorem mem_of_slice {ss : List Stmt} {s : Stmt} {i : ℕ}
    (h : tbStmtsEqb [s] ((ss.drop i).take 1) = true) : s ∈ ss := by
  have e := tbStmtsEqb_sound h
  have : s ∈ (ss.drop i).take 1 := by rw [← e]; simp
  exact List.mem_of_mem_drop (List.mem_of_mem_take this)

/-- Neither a call, a conditional call nor a dispatch. -/
def noCallSB : Stmt → Bool
  | .call .. | .callIf .. | .dispatch .. => false
  | _ => true

theorem callSF_none {σ : Val} {s : Stmt} (h : noCallSB s = true) : Stmt.callSF σ s = none := by
  cases s with
  | call => simp [noCallSB] at h
  | callIf => simp [noCallSB] at h
  | dispatch => simp [noCallSB] at h
  | _ => rfl

theorem dispOk_of_noCall {σ : Val} {s : Stmt} (h : noCallSB s = true) : DispOk σ s := by
  cases s with
  | dispatch => simp [noCallSB] at h
  | _ => trivial

end
end LeanVM.Guest.B1.Tables
