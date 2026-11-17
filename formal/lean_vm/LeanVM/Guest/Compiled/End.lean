/-
  LeanVM.Guest.Compiled.End

  The back end's correctness at the guest with every function's obligations discharged: `main`'s
  core body holds at frame `1`, its calls located, given only that the back end compiles the
  guest to the statement's bytecode.
-/

module

public import LeanVM.Guest.Compiled.World
public import LeanVM.Guest.Compiled.Facts
public import LeanVM.Guest.Compiled.Obl.GuestB1

/-!
# The guest, end to end

`guestEnd L` is the guest's world on the memory `L` with the precondition `guestUc L.read`: the
guest's `guestU L.read` (`Obl/GuestU.lean`) and its loop helpers' constant parameters
(`withConsts`), whose obligations follow from `guestU`'s (`guestEnd_obligations`). On it:

* `guest_main_holds`: given `GuestCompiles fns slots`, on a memory of `2^κ` words,
  `minLogMem ≤ κ ≤ maxLogMem`, where a run of `guestProgram` from `(g^0, 1)` halts, `main`'s core
  body holds at frame `1` (`guest_program_sound`, its obligations from `guest_obligations`);
* `guest_main_body`: the same as `main`'s body `Data.core0.body` under the valuation by places at
  frame `1`, returning nothing, its calls located (`World.C`);
* `guest_main_rel`: `coreProgram.Rel L.read "main" [] []`;
* `registered_tfOf`: function `j` is a registered loop helper of the guest's world exactly when
  its name is a loop helper's and its `loopSource` says so.
-/

namespace LeanVM.Guest.Compiled

open LeanVM.Compiler LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core GuestData LeanVM.Compiler.Obl LeanVM.Guest.Compiled.Obl

@[expose] public section

/-- **What the guest's callers are asked for**: the guest's preconditions (`guestU`), and the
arguments its loop helpers' constant parameters name holding their words (`withConsts`). -/
noncomputable abbrev guestUc (rd : Reader) : String → List E → Prop :=
  withConsts (guestU rd) (constsOf (loopTable guestTraced))

/-- **The guest's world on `L`**, its preconditions `guestUc`. -/
noncomputable abbrev guestEnd {κ : ℕ} (fns : List Lowered) (slots : Array KVal) (L : MemoryImage κ) :
    World κ :=
  guestWorld fns slots L (guestUc L.read)

theorem guestTraced_head : ∃ t, guestTraced = ⟨Data.core0, traceOf0, 0, (true, none), []⟩ :: t :=
  ⟨_, rfl⟩

theorem core0_name : Data.core0.name = "main" ∧ Data.core0.params = [] := by decide +kernel

/-- `main` has no precondition in the guest's table. -/
theorem guestTab_main : guestTab.sig "main" = {} := by decide +kernel

theorem guestU_main {rd : Reader} {a : List E} : guestU rd "main" a := by
  refine ⟨⟨fun p hp => ?_, fun m hm => ?_, fun p hp => ?_⟩, fun h => ?_⟩
  all_goals rw [guestTab_main] at *
  all_goals simp at *

variable {κ : ℕ} {fns : List Lowered} {slots : Array KVal} {L : MemoryImage κ}

/-- `main`'s traced function is the head of `guestTraced`. -/
theorem guestTraced_main (L : MemoryImage κ) {tf : TracedFn} (h : GuestCompiles fns slots) (htf : tf ∈ guestTraced)
    (hn : tf.core.name = "main") :
    tf = ⟨Data.core0, traceOf0, 0, (true, none), []⟩ := by
  obtain ⟨t, ht⟩ := guestTraced_head
  have hnd := (World.names (guestWorld_compiled (L := L) (U := guestU L.read) h)).2.1
  rw [guestWorld_p, ht] at hnd
  rw [ht] at htf
  rcases List.mem_cons.mp htf with rfl | htf
  · rfl
  · rw [List.map_cons, List.nodup_cons] at hnd
    exact absurd (List.mem_map_of_mem (f := fun x : TracedFn => x.core.name) htf)
      (by rw [hn, ← core0_name.1]; exact hnd.1)

theorem maxLogMem_lt : maxLogMem < 64 := by decide

/-- **The guest's callers' preconditions carry the constant parameters.** -/
theorem guestEnd_constsIn : (guestEnd fns slots L).ConstsIn := fun _ _ h => h.2

/-- **Every function's obligations on the guest's world** (`guest_obligations`, the constant
parameters' facts from the table being right of the guest, `World.obligations_withConsts`). -/
theorem guestEnd_obligations (h : GuestCompiles fns slots) (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) :
    ∀ tf ∈ guestTraced, (guestEnd fns slots L).Obligations tf := fun tf htf =>
  World.obligations_withConsts (W := guestWorld fns slots L (guestU L.read)) (guestWorld_compiled h)
    (lowerProgram_consts h.1) htf
    (guest_obligations (guestWorld_compiled h) guestTraced_core hκ rfl tf htf)

/-- **`main`'s core body holds at frame `1`**, given that the back end compiles the guest to the
statement's bytecode and a run of `guestProgram` from `(g^0, 1)` halts. -/
theorem guest_main_holds (h : GuestCompiles fns slots) (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) {k : ℕ}
    (hs : Safe guestProgram L k ⟨addressOfIndex 0, 1⟩) : (guestEnd fns slots L).MainHolds :=
  guest_program_sound h (lt_of_le_of_lt hκ.2 maxLogMem_lt) (guestEnd_obligations h hκ)
    (fun _ _ _ => ⟨guestU_main, fun x hx => by
      rw [ConstsOk.main (lowerProgram_consts h.1)] at hx; cases hx⟩) hs

/-- **`main`'s body, certificate-free**: on a memory of `2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`,
where a run of `guestProgram` from `(g^0, 1)` halts, `main`'s core body holds at frame `1` under
the valuation by places, returning nothing, its calls located. -/
theorem guest_main_body (h : GuestCompiles fns slots) :
    ∀ κ (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ k,
      Safe guestProgram L k ⟨addressOfIndex 0, 1⟩ →
      Stmt.HoldsList (guestEnd fns slots L).C L.read ((guestEnd fns slots L).vf "main" 1)
        Data.core0.body False (fun rs => rs = []) := by
  intro κ L h1 h2 k hs
  obtain ⟨tf, htf, hn, -, hb⟩ := guest_main_holds h ⟨h1, h2⟩ hs
  obtain rfl := guestTraced_main L h htf hn
  exact hb

/-- **`main`'s relation**: `coreProgram.Rel L.read "main" [] []`. -/
theorem guest_main_rel (h : GuestCompiles fns slots) (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) {k : ℕ}
    (hs : Safe guestProgram L k ⟨addressOfIndex 0, 1⟩) : coreProgram.Rel L.read "main" [] [] := by
  obtain ⟨tf, htf, hn, hr⟩ := program_rel (guestWorld_compiled h) (guest_main_holds h hκ hs)
  obtain rfl := guestTraced_main L h htf hn
  rw [guestWorld_core] at hr
  simp only [sigOf, core0_name.2, List.length_nil, frameWords, List.range_zero, List.map_nil] at hr
  exact hr

theorem registered_tfOf (h : GuestCompiles fns slots) {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    (guestEnd fns slots L).registered (coreOf j).name ↔
      (isLoopName (coreOf j).name && (infoOf j).2.2.1.1) = true := by
  have := registered_iff (guestTraced_nodup L h) (getElem_mem_guestTraced h1 h2)
  dsimp only [tfOf] at this
  show ((loopTable guestTraced)[(coreOf j).name]?).any (·.registered) = true ↔ _
  rw [this]

end
end LeanVM.Guest.Compiled

/-- info: 'LeanVM.Guest.Compiled.guest_main_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Compiled.guest_main_body

/-- info: 'LeanVM.Guest.Compiled.guest_main_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Compiled.guest_main_rel
