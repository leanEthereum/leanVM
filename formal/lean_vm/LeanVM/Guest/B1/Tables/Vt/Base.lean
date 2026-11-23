/-
  LeanVM.Guest.B1.Tables.Vt.Base

  `verify_tables`' body as facts of a valuation: its 14 chunks, read by position.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Tables.Basic
public import LeanVM.Guest.CoreData
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# `verify_tables`' body (TRIAGE G #52)

`verify_tables` is one function of 5241 statements, stored as 14 chunks
(`core% «verify_tables» c0 .. c13`, the last ending in its `ret`). Its soundness reads each fact it
needs off a chunk, by position (`VtH.atom`, `VtH.slice`, …), the kernel checking each statement read
against the chunk: a valuation satisfying every chunk is what `vt_unfold` gives.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Chunk `i` of `verify_tables`' body, the last without its `ret`. -/
noncomputable def vtChunk : ℕ → List Stmt
  | 0 => (core% «verify_tables» c0)
  | 1 => (core% «verify_tables» c1)
  | 2 => (core% «verify_tables» c2)
  | 3 => (core% «verify_tables» c3)
  | 4 => (core% «verify_tables» c4)
  | 5 => (core% «verify_tables» c5)
  | 6 => (core% «verify_tables» c6)
  | 7 => (core% «verify_tables» c7)
  | 8 => (core% «verify_tables» c8)
  | 9 => (core% «verify_tables» c9)
  | 10 => (core% «verify_tables» c10)
  | 11 => (core% «verify_tables» c11)
  | 12 => (core% «verify_tables» c12)
  | _ => (core% «verify_tables» c13).take 420

/-- `verify_tables`' returned values. -/
def vtRets : List V := [.n (val% «verify_tables» "s92#0"), .n (val% «verify_tables» "s92#0[1]"), .n (val% «verify_tables» "s92#0[2]"), .n (val% «verify_tables» "s92#0[3]"), .n (val% «verify_tables» "s92#0[4]"), .n (val% «verify_tables» "s92#0[5]"), .n (val% «verify_tables» "s92#0[6]"),
  .n (val% «verify_tables» "s92#0[7]"), .n (val% «verify_tables» "s92#0[8]"), .n (val% «verify_tables» "s92#0[9]")]

theorem vtChunk_noRet' : ∀ i < 14, Stmt.noRetList (vtChunk i) = true := by decide +kernel

theorem vtChunk_noRet (i : ℕ) : Stmt.noRetList (vtChunk i) = true := by
  rcases Nat.lt_or_ge i 14 with hi | hi
  · exact vtChunk_noRet' i hi
  · have : vtChunk i = vtChunk 13 := by
      match i, hi with
      | n + 14, _ => rfl
    rw [this]; exact vtChunk_noRet' 13 (by omega)

theorem verify_tables_body :
    (core% «verify_tables» body) = ((List.range 14).map vtChunk).flatten ++ [.ret vtRets] := by
  have h13 : (core% «verify_tables» c13) = (core% «verify_tables» c13).take 420 ++ [.ret vtRets] :=
    tbStmtsEqb_sound (by decide +kernel)
  conv_lhs => rw [core_eq% «verify_tables» body, h13]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil, List.nil_append,
    List.append_nil, vtChunk, List.append_assoc]

noncomputable def vtCheck : Bool :=
  match coreProgram.find? name% «verify_tables» with
  | some fn => decide (fn.params = (List.range 21).map V.n) &&
      tbStmtsEqb fn.body (core% «verify_tables» body)
  | none => false

theorem vtCheck_eq : vtCheck = true := by decide +kernel

theorem vtFound : ∃ fn : Fn, coreProgram.find? name% «verify_tables» = some fn ∧
    fn.params = (List.range 21).map V.n ∧
    fn.body = ((List.range 14).map vtChunk).flatten ++ [.ret vtRets] := by
  have h := vtCheck_eq
  unfold vtCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, (tbStmtsEqb_sound h.2).trans verify_tables_body⟩
  · exact absurd h (by simp)

/-- `verify_tables`' statements before its `ret`. -/
noncomputable def vtPre : List Stmt := ((List.range 14).map vtChunk).flatten

theorem vtPre_noRet : Stmt.noRetList vtPre = true :=
  tb_noRetList_flatten_range 14 vtChunk vtChunk_noRet

/-- The lengths of `verify_tables`' chunks. -/
def vtLens : List ℕ :=
  [605, 295, 113, 109, 230, 108, 108, 401, 567, 576, 562, 540, 606, 420]

theorem vtLens_eq : ((List.range 14).map vtChunk).map List.length = vtLens := by decide +kernel

/-- `vtPre` from position `n` (`vtPre_drop`), as the kernel reads it fast: the chunks before `n`
passed by their lengths, not walked statement by statement. Every kernel check of a statement of
`verify_tables` at a position reads it so. -/
noncomputable def vtAt (n : ℕ) : List Stmt := dropFlatL vtLens ((List.range 14).map vtChunk) n

theorem vtPre_drop (n : ℕ) : vtPre.drop n = vtAt n := by
  rw [vtAt, ← vtLens_eq, dropFlatL_eq]
  rfl

/-- A comparison with `vtPre` at a position, read through `vtAt`. -/
theorem vtAt_eqb {l : List Stmt} {n m : ℕ} (h : tbStmtsEqb l ((vtPre.drop n).take m) = true) :
    tbStmtsEqb l ((vtAt n).take m) = true :=
  vtPre_drop n ▸ h

/-- The valuation `σ` satisfies every statement of `verify_tables` before its `ret`. -/
def VtH (rd : Reader) (σ : Val) : Prop :=
  ∃ kret : List E → Prop, Stmt.HoldsList (coreProgram.Rel rd) rd σ vtPre True kret

/-- **`verify_tables` unfolded**: a valuation of its parameters, satisfying its body, returning
`vtRets`. -/
theorem vt_unfold {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd "verify_tables" args rets) :
    ∃ σ : Val, (List.range 21).map (fun k ↦ σ (.n k)) = args ∧ VtH rd σ ∧
      vtRets.map σ = rets := by
  obtain ⟨fn, hf, hpar, hb⟩ := vtFound
  obtain ⟨σ, hp, hbd, hr⟩ := (tb_rel_pre hf hb vtPre_noRet args rets).mp h
  refine ⟨σ, ?_, ⟨_, hbd⟩, hr⟩
  rw [← hp, hpar, List.map_map]
  rfl

section Read

variable {rd : Reader} {σ : Val}

theorem VtH.atom (h : VtH rd σ) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((vtPre.drop n).take 1) = true) : a.Holds rd σ := by
  obtain ⟨k, h⟩ := h
  exact tb_holds_atom vtPre_noRet h n a heq

theorem VtH.slice (h : VtH rd σ) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vtPre.drop n).take blk.length) = true) :
    ∃ kret : List E → Prop, Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True kret := by
  obtain ⟨k, h⟩ := h
  exact ⟨k, tb_holds_slice vtPre_noRet h n blk heq⟩

theorem VtH.call (h : VtH rd σ) (n : ℕ) (f : String) (args rets : List V)
    (heq : tbStmtsEqb [.call f args rets] ((vtPre.drop n).take 1) = true) :
    coreProgram.Rel rd f (args.map σ) (rets.map σ) := by
  obtain ⟨k, h⟩ := h
  exact tb_holds_call vtPre_noRet h n f args rets heq

theorem VtH.callIf (h : VtH rd σ) (n : ℕ) (c : V) (f : String)
    (args : List V) (heq : tbStmtsEqb [.callIf c f args] ((vtPre.drop n).take 1) = true) :
    IsInK (σ c) ∧ (σ c ≠ 0 → coreProgram.Rel rd f (args.map σ) []) := by
  obtain ⟨k, h⟩ := h
  exact tb_holds_callIf vtPre_noRet h n c f args heq

theorem VtH.dispatch (h : VtH rd σ) (n : ℕ) (x : V) (fs : List String)
    (args rets : List V)
    (heq : tbStmtsEqb [.dispatch x fs args rets] ((vtPre.drop n).take 1) = true) :
    ∃ (j : ℕ) (h : j < fs.length), σ x = ofK (Parameters.addressOfIndex j) ∧
      coreProgram.Rel rd fs[j] (args.map σ) (rets.map σ) := by
  obtain ⟨k, h⟩ := h
  exact tb_holds_dispatch vtPre_noRet h n x fs args rets heq

/-! The same at `vtAt`: what a kernel check of a statement at a position evaluates fast. -/

theorem VtH.atomAt (h : VtH rd σ) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((vtAt n).take 1) = true) : a.Holds rd σ :=
  h.atom n a (vtPre_drop n ▸ heq)

theorem VtH.sliceAt (h : VtH rd σ) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vtAt n).take blk.length) = true) :
    ∃ kret : List E → Prop, Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True kret :=
  h.slice n blk (vtPre_drop n ▸ heq)

theorem VtH.callAt (h : VtH rd σ) (n : ℕ) (f : String) (args rets : List V)
    (heq : tbStmtsEqb [.call f args rets] ((vtAt n).take 1) = true) :
    coreProgram.Rel rd f (args.map σ) (rets.map σ) :=
  h.call n f args rets (vtPre_drop n ▸ heq)

theorem VtH.callIfAt (h : VtH rd σ) (n : ℕ) (c : V) (f : String) (args : List V)
    (heq : tbStmtsEqb [.callIf c f args] ((vtAt n).take 1) = true) :
    IsInK (σ c) ∧ (σ c ≠ 0 → coreProgram.Rel rd f (args.map σ) []) :=
  h.callIf n c f args (vtPre_drop n ▸ heq)

theorem VtH.dispatchAt (h : VtH rd σ) (n : ℕ) (x : V) (fs : List String)
    (args rets : List V)
    (heq : tbStmtsEqb [.dispatch x fs args rets] ((vtAt n).take 1) = true) :
    ∃ (j : ℕ) (h : j < fs.length), σ x = ofK (Parameters.addressOfIndex j) ∧
      coreProgram.Rel rd fs[j] (args.map σ) (rets.map σ) :=
  h.dispatch n x fs args rets (vtPre_drop n ▸ heq)

end Read

end
end LeanVM.Guest.B1.Tables
