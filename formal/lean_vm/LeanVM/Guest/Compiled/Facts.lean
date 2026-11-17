/-
  LeanVM.Guest.Compiled.Facts

  The guest's world by function index: halting runs along a reach, function `j` of the bytecode as
  the back end lays it out, the back end's input by index, and its loop table.
-/

module

public import LeanVM.Guest.Logic
public import LeanVM.Guest.NameIndex
public import LeanVM.Guest.CoreNames
public import LeanVM.Guest.Compiled.World
public import Mathlib.Data.List.GetD

/-!
# The guest's world, by function index

* `safe_of_reach`, `safe_of_reach_back`: the run is deterministic, so a state reached from one
  where the run halts halts, and so does one that reaches it.
* `ent_eq`: given `GuestCompiles`, the back end's entry of function `j`'s name is the entry pc of
  `fnOf j` (`Data.functions`), and `fnOf j` is named as `coreOf j` (`fn_names`, decided).
* `guestTraced_getElem`, `mem_guestTraced`: entry `j - 1` of the back end's input is `coreOf j`
  with `infoOf j` (`tfOf j`, `tf_eq`).
* `registered_iff`: a function is a registered loop helper exactly when its name is a loop
  helper's and its `loopSource` says so.

The names live in `LeanVM.Guest`, beside `fnOf` and `coreOf`: `LeanVM.Compiler.infoOf` is the
placement's (`Compiler/Piece.lean`).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Compiler LeanVM.Guest.Compiled

@[expose] public section

/-- What the back end's input holds of function `j ≥ 1` besides its core function. -/
def infoOf (j : ℕ) : Array Event × Nat × Bool × Option Nat := GuestData.guestInfo.getD (j - 1) default

/-! ## Halting runs -/

section Run

variable {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ}

/-- **A state reached from one where the run halts halts.** -/
theorem safe_of_reach {k : ℕ} {s t : Registers K} (hs : Safe prog L k s) (hr : Reach prog L s t) :
    ∃ k', Safe prog L k' t := by
  obtain ⟨n, hn⟩ := hr
  unfold Safe at hs ⊢
  rcases Nat.lt_or_ge k n with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = k + (m + 1) := ⟨n - k - 1, by omega⟩
    rw [run_add, hs] at hn
    simp [run_succ_of_eq rfl] at hn
  · obtain ⟨m, rfl⟩ : ∃ m, k = n + m := ⟨k - n, by omega⟩
    rw [run_add, hn] at hs
    exact ⟨m, hs⟩

/-- **A state that reaches one where the run halts halts.** -/
theorem safe_of_reach_back {k : ℕ} {s t : Registers K} (hr : Reach prog L s t) (hs : Safe prog L k t) :
    ∃ k', Safe prog L k' s := by
  obtain ⟨n, hn⟩ := hr
  refine ⟨n + k, ?_⟩
  unfold Safe at hs ⊢
  rw [run_add, hn]
  exact hs

end Run

/-! ## Function `j` -/

theorem functions_length : Data.functions.length = nFns := by decide +kernel

theorem coreProgram_length_succ : coreProgram.length + 1 = nFns := by
  rw [coreProgram_length]; rfl

theorem fnOf_mem {j : ℕ} (h : j < nFns) : fnOf j ∈ Data.functions := by
  unfold fnOf
  rw [nth_eq (functions_length ▸ h)]
  exact List.getElem_mem _

theorem coreOf_eq {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    coreOf j = coreProgram[j - 1]'(by have := coreProgram_length_succ; omega) := by
  unfold coreOf
  exact nth_eq _

theorem coreOf_find {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    coreProgram.find? (coreOf j).name = some (coreOf j) := by
  rw [coreOf_eq h1 h2]
  exact coreProgram_find_getElem _

theorem nameIndex_coreOf {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) : nameIndex (coreOf j).name = j := by
  have hl : j - 1 < coreProgram.length := by have := coreProgram_length_succ; omega
  unfold nameIndex
  rw [coreOf_eq h1 h2, findIdx_name_of_nodup coreProgram_names_nodup hl]
  omega

/-- The bytecode's functions after `__jump_tables` are named as the core program's. -/
theorem fn_names_all : Data.functions.tail.map (·.name) = coreProgram.map (·.name) := by
  decide +kernel

/-- The core program's functions have fewer than `2^12` parameters. -/
theorem params_small_all : coreProgram.all (fun f => decide (f.params.length < 2 ^ 12)) = true := by
  decide +kernel

theorem fn_names {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    (fnOf j).name = (coreOf j).name ∧ (coreOf j).params.length < 2 ^ 12 := by
  have hl : j - 1 < coreProgram.length := by have := coreProgram_length_succ; omega
  have hF : j < Data.functions.length := by rw [functions_length]; exact h2
  refine ⟨?_, ?_⟩
  · have e := congrArg (·[j - 1]?) fn_names_all
    simp only [List.getElem?_map, List.getElem?_tail, Nat.sub_add_cancel h1,
      List.getElem?_eq_getElem hF, List.getElem?_eq_getElem hl, Option.map_some,
      Option.some.injEq] at e
    unfold fnOf
    rw [nth_eq hF, coreOf_eq h1 h2]
    exact e
  · have := List.all_eq_true.mp params_small_all _ (List.getElem_mem hl)
    rw [coreOf_eq h1 h2]
    exact of_decide_eq_true this

/-- Two functions of one name are one. -/
theorem coreOf_name_inj {j j' : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) (h1' : 1 ≤ j') (h2' : j' < nFns)
    (h : (coreOf j).name = (coreOf j').name) : j = j' := by
  rw [← nameIndex_coreOf h1 h2, ← nameIndex_coreOf h1' h2', h]

theorem coreOf_one : coreOf 1 = Data.core0 := rfl

theorem core0_main : Data.core0.name = "main" ∧ Data.core0.params = [] := by decide +kernel

/-! ## The back end's input -/

theorem zip_map_getElem {α β γ : Type} (F : α × β → γ) (l : List α) (m : List β) {i : ℕ}
    (h1 : i < l.length) (h2 : i < m.length) (h : i < ((l.zip m).map F).length) :
    ((l.zip m).map F)[i] = F (l[i], m[i]) := by
  simp

theorem zip_map_length {α β γ : Type} (F : α × β → γ) (l : List α) (m : List β)
    (h : l.length = m.length) : ((l.zip m).map F).length = l.length := by
  simp [h]

theorem guestTraced_length : guestTraced.length = coreProgram.length := by
  unfold guestTraced
  exact zip_map_length _ _ _ (by rw [coreProgram_length, GuestData.guestInfo_length])

/-- **Entry `j - 1` of the back end's input** is `coreOf j` with `infoOf j`. -/
theorem guestTraced_getElem {i : ℕ} (hi : i < guestTraced.length) :
    guestTraced[i] = ⟨coreOf (i + 1), (infoOf (i + 1)).1, (infoOf (i + 1)).2.1, (infoOf (i + 1)).2.2⟩ := by
  have hc : i < coreProgram.length := by rw [← guestTraced_length]; exact hi
  have hg : i < GuestData.guestInfo.length := by
    rw [GuestData.guestInfo_length]; rw [coreProgram_length] at hc; exact hc
  have e1 : coreOf (i + 1) = coreProgram[i]'hc := by
    rw [coreOf_eq (by omega) (by have := coreProgram_length_succ; omega)]
    simp only [Nat.add_sub_cancel]
  have e2 : infoOf (i + 1) = GuestData.guestInfo[i]'hg := by
    unfold infoOf
    rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ hg]
  rw [e1, e2]
  unfold guestTraced at hi ⊢
  exact zip_map_getElem _ _ _ hc hg hi

/-- **A function of the back end's input** is `coreOf j` with `infoOf j`, `1 ≤ j < nFns`. -/
theorem mem_guestTraced {tf : TracedFn} (h : tf ∈ guestTraced) :
    ∃ j, 1 ≤ j ∧ j < nFns ∧
      tf = ⟨coreOf j, (infoOf j).1, (infoOf j).2.1, (infoOf j).2.2⟩ := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  refine ⟨i + 1, by omega, ?_, guestTraced_getElem hi⟩
  have := coreProgram_length_succ
  rw [guestTraced_length] at hi
  omega

theorem getElem_mem_guestTraced {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    (⟨coreOf j, (infoOf j).1, (infoOf j).2.1, (infoOf j).2.2⟩ : TracedFn) ∈ guestTraced := by
  have hi : j - 1 < guestTraced.length := by
    rw [guestTraced_length]; have := coreProgram_length_succ; omega
  have := guestTraced_getElem hi
  rw [show j - 1 + 1 = j by omega] at this
  exact this ▸ List.getElem_mem hi

/-! ## The loop table -/

theorem loopTable_fold_other {g : String} :
    ∀ (l : List TracedFn) (t : Loops), (∀ x ∈ l, x.core.name ≠ g) →
      (l.foldl (fun table tf => if isLoopName tf.core.name then
        table.insert tf.core.name ⟨tf.loop.1, tf.loop.2⟩ else table) t)[g]? = t[g]?
  | [], _, _ => rfl
  | x :: l, t, h => by
      rw [List.foldl_cons, loopTable_fold_other l _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      split
      · rw [KMap.getElem?_insert, ite_eq_right (Ne.symm (h x List.mem_cons_self))]
      · rfl

/-- **A function's entry in the loop table**: it is a loop helper's name, with its `loopSource`. -/
theorem loopTable_get {p : List TracedFn} (hnd : (p.map (·.core.name)).Nodup) {tf : TracedFn}
    (htf : tf ∈ p) :
    (loopTable p)[tf.core.name]? =
      if isLoopName tf.core.name then some ⟨tf.loop.1, tf.loop.2⟩ else none := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem htf
  have hnd' := hnd
  simp only [List.map_append, List.map_cons] at hnd'
  have hs : ∀ x ∈ s, x.core.name ≠ tf.core.name := fun x hx he =>
    (List.nodup_append.mp hnd').2.2 _ (List.mem_map_of_mem hx) _ List.mem_cons_self he
  have ht : ∀ x ∈ t, x.core.name ≠ tf.core.name := fun x hx he =>
    (List.nodup_cons.mp (List.nodup_append.mp hnd').2.1).1 (he ▸ List.mem_map_of_mem hx)
  unfold loopTable
  rw [List.foldl_append, List.foldl_cons, loopTable_fold_other t _ ht]
  split
  · rw [KMap.getElem?_insert, ite_eq_left rfl]
  · rw [loopTable_fold_other s _ hs]
    rfl

/-- **A registered loop helper** is one whose name is a loop helper's and whose `loopSource` says
its frames are reserved in one run. -/
theorem registered_iff {p : List TracedFn} (hnd : (p.map (·.core.name)).Nodup) {tf : TracedFn}
    (htf : tf ∈ p) :
    ((loopTable p)[tf.core.name]?).any (·.registered) = (isLoopName tf.core.name && tf.loop.1) := by
  rw [loopTable_get hnd htf]
  split <;> simp [*]

/-! ## Entries -/

theorem rangesFrom_getElem? : ∀ (fs : List Lowered) (pc i : ℕ) (hi : i < fs.length),
    (rangesFrom fs pc)[i]? = some (fs[i].name, pc + totalSize (fs.take i), fs[i].code.size)
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | f :: fs, pc, 0, _ => by simp [rangesFrom, totalSize]
  | f :: fs, pc, i + 1, hi => by
      rw [rangesFrom, List.getElem?_cons_succ,
        rangesFrom_getElem? fs (pc + f.code.size) i (by simpa using hi)]
      simp [totalSize, Nat.add_assoc]

theorem rangesFrom_length : ∀ (fs : List Lowered) (pc : ℕ), (rangesFrom fs pc).length = fs.length
  | [], _ => rfl
  | f :: fs, pc => by simp [rangesFrom, rangesFrom_length fs]

variable {κ : ℕ} {fns : List Lowered} {slots : Array KVal} {L : MemoryImage κ}
  {U : String → List E → Prop}

/-- **The back end's entry of function `j`'s name is `fnOf j`'s entry pc.** -/
theorem ent_fnOf (h : GuestCompiles fns slots) {j : ℕ} (hj : j < nFns) :
    (guestWorld fns slots L U).ent (fnOf j).name = (fnOf j).entryPc := by
  have hW := guestWorld_compiled (L := L) (U := U) h
  have hnd := World.nodup hW
  simp only [guestWorld] at hnd
  generalize hwt : (withTables fns slots).1 = wt at hnd
  have hr : (Compiler.assemble fns slots).fns.toList = rangesFrom wt 0 := by
    rw [← hwt, assemble_def, assembleAt_fns]
  have hfun : Data.functions = (rangesFrom wt 0).map (Compiler.assemble fns slots).fnOf := by
    rw [← h.2.1, toFunctions_eq, hr]
  have hlen : j < wt.length := by
    have := congrArg List.length hfun
    rw [List.length_map, rangesFrom_length, functions_length] at this
    omega
  have hf : fnOf j = (Compiler.assemble fns slots).fnOf
      (wt[j].name, 0 + totalSize (wt.take j), wt[j].code.size) := by
    unfold fnOf
    rw [nth_eq (functions_length ▸ hj)]
    have hj' : j < ((rangesFrom wt 0).map (Compiler.assemble fns slots).fnOf).length := by
      rw [List.length_map, rangesFrom_length]; exact hlen
    simp only [hfun, List.getElem_map]
    congr 1
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans (rangesFrom_getElem? wt 0 j hlen))
  have hsplit : wt = wt.take j ++ wt[j] :: wt.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hlen, List.take_append_drop]
  have he := layout_entry (withTables fns slots).2 hnd hsplit
  rw [hf]
  show (layoutOf fns slots).entry.getD wt[j].name 0 = 0 + totalSize (wt.take j)
  rw [KMap.getD_eq_getD_getElem?, layoutOf, hwt, he, Nat.zero_add]
  rfl

/-- **The back end's entry of `coreOf j` is `fnOf j`'s entry pc**, `1 ≤ j < nFns`. -/
theorem ent_eq (h : GuestCompiles fns slots) {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    (guestWorld fns slots L U).ent (coreOf j).name = (fnOf j).entryPc := by
  rw [← (fn_names h1 h2).1]
  exact ent_fnOf h h2

theorem guestProgram_eq (h : GuestCompiles fns slots) :
    (guestWorld fns slots L U).prog = guestProgram := guestWorld_prog h

/-- The guest's function names are distinct. -/
theorem guestTraced_nodup (L : MemoryImage κ) (h : GuestCompiles fns slots) :
    (guestTraced.map (·.core.name)).Nodup :=
  (World.names (guestWorld_compiled (L := L) (U := fun _ _ => True) h)).2.1

/-! ## The functions of the back end's input -/

/-- Function `j` as the back end's input holds it. -/
noncomputable abbrev tfOf (j : ℕ) : TracedFn :=
  ⟨coreOf j, (infoOf j).1, (infoOf j).2.1, (infoOf j).2.2⟩

theorem tf_eq (L : MemoryImage κ) (h : GuestCompiles fns slots) {tf : TracedFn}
    (htf : tf ∈ guestTraced) {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns)
    (hn : tf.core.name = (coreOf j).name) : tf = tfOf j :=
  eq_of_name (guestTraced_nodup L h) htf (getElem_mem_guestTraced h1 h2) hn

theorem name_ne_main {j : ℕ} (h2 : 2 ≤ j) (hj : j < nFns) : (coreOf j).name ≠ "main" := by
  intro he
  have := coreOf_name_inj (j' := 1) (by omega) hj le_rfl (by decide) (he.trans core0_main.1.symm)
  omega

end
end LeanVM.Guest
