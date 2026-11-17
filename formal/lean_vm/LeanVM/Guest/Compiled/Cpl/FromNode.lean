/-
  LeanVM.Guest.Compiled.Cpl.FromNode
  The core runs `guest_core_complete` takes exist: B1's completeness of `main` at the back end's
  cells gives one for every node relation within the deployed limits, and the compiled guest runs
  on its honest memory.
-/

module

public import LeanVM.Guest.Compiled.Cpl.Complete
public import LeanVM.Guest.Compiled.Cpl.WholeCore
public import LeanVM.Compiler.Complete.CoreCongr
public meta import LeanVM.Guest.KernelLit

/-!
# From the node relation to the compiled guest's run

B1's completeness of `main` (`End.MainComplete`) is generic in the cells (`mainComplete_at`, given
`Lift.RunsFit` and `B1.RunsConsec`), and at the back end's cells `certG` those hold
(`runsFitG`, `runsConsecG`). Its trees are placed at the deployed frame sizes `Deployed.fs`, which
agree with the back end's `W0.fsB` on every function of the guest (`W0_agree`: the per-function
test's frame size, `main`'s with the jump tables, `slotsG_size`), as do `certG` and `W0.cellB`. So
a tree B1 builds is valid, placed and loads in its data at the back end's layout
(`Complete.placed_iff`, `Complete.loadsIn_iff`, `Complete.total_eq`), and is a `CoreRun`:
`guest_core_run`. With `guest_core_complete`, `guest_run_from_node`.
-/

namespace LeanVM.Guest.Compiled.Cpl

open LeanVM.Compiler LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node GuestPiece
open LeanVM.Guest.End (bytecode MainComplete hdrOf work)
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Main (imageOf memL_imageOf imageOf_hdr dischargeAddr)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

/-- The guest's jump table has `Deployed.Data.jtSlots` slots. -/
kernel_rfl slotsG_size : slotsG.size = Deployed.Data.jtSlots

@[expose] public section

theorem W0_core : W0.core = coreProgram := guestWorld_core

/-- **The back end's layout agrees with the deployed frame sizes and the back end's cells** on
every function of the guest. -/
theorem W0_agree : Complete.AgreeOn coreProgram Deployed.fs W0.fsB certG W0.cellB := by
  intro g fn hf
  obtain ⟨i, hix⟩ := ix_of_find hf
  have F := fnAt hix
  have E := entryOk CplEval.cplOkAll F.lt
  rw [← W0_core] at hf
  obtain ⟨tf, htf, rfl, rfl⟩ := Complete.core_find hf
  obtain ⟨pf, hfo, hpa⟩ := Complete.fnOf_of_mem W0_compiled htf
  have hpa' : Complete.World.PlacedAs W0 tf (placedG i) :=
    ⟨E.placedAs.1, E.placedAs.2.trans (by rw [F.core, F.name])⟩
  obtain rfl := placedAs_unique W0_compiled hpa hpa'
  refine ⟨?_, funext fun v => ?_⟩
  · by_cases hm : tf.core.name = "main"
    · have hi0 : i = 0 := (name_main F.lt).mp (by rw [F.core, F.name]; exact hm)
      subst hi0
      have hsl : W0.slots = slotsG := rfl
      rw [F.fs_eq, hm, (Complete.fsB_main W0_compiled hpa hm).2, E.facts.sfacts.frame, hsl,
        slotsG_size]
      rfl
    · have hi0 : i ≠ 0 := fun h => hm (by rw [← F.name, ← F.core]; exact (name_main F.lt).mpr h)
      rw [F.fs_eq, Complete.fsB_fn W0_compiled htf hpa hm, E.facts.sfacts.frame, fsWant_eq hi0]
  · rw [F.cert v]
    unfold World.cellB
    rw [(Complete.fnOf_spec hfo).2.2.2]

/-- **A run of the guest's core IR as `guest_core_complete` takes it**: `main`'s tree `T`, valid on
the memory `M` holding the public input `hdr`, its `HeapBuf`s its paths', its free values where the
back end puts them, its loads in its data or the public input, of at most `2^30` words, its
equations in the memory. -/
def CoreRun (hdr : E × E) (T : Tree) (M : MemoryImage (logMem (T.total W0.fsB))) : Prop :=
  T.name = "main" ∧ T.Valid W0.core M.read [] [] ∧ T.BufsOk W0.core ∧
    T.Placed W0.core W0.fsB W0.cellB 0 ∧ T.LoadsIn W0.core W0.fsB W0.cellB (fun i => i < 2) 0 ∧
    M.read (addressOfIndex 0) = some hdr.1 ∧ M.read (addressOfIndex 1) = some hdr.2 ∧
    T.total W0.fsB ≤ 2 ^ 30 ∧
    ∀ q ∈ T.eqns W0.core, ∃ i : Fin (2 ^ logMem (T.total W0.fsB)), q.1 = addressOfIndex i

/-- **`main`'s completeness at the back end's cells gives core runs**: for the node relation within
the limits and a budget within `2^30` words, a `CoreRun` of the statement's public input within the
budget's words. -/
theorem coreRun_of_main {cnt : Tree → Opcode → ℕ} {b : End.Budget}
    (hm : MainComplete Deployed.fs certG cnt b) :
    ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
      b.size (work s w) ≤ 2 ^ 30 →
      ∃ (T : Tree) (M : MemoryImage (logMem (T.total W0.fsB))),
        CoreRun (hdrOf (statementDigest seed s)) T M ∧ T.total W0.fsB ≤ b.words.eval (work s w) := by
  intro seed s w hrel hlim hok hbs
  have hA := W0_agree
  obtain ⟨N, L, hcons, hin, hN, hNb, hrelL⟩ := hm seed s w hrel hlim hok hbs
  set hdr := hdrOf (statementDigest seed s) with hhdr
  have h64 : logMem N < 64 := by have := logMem_le_maxLogMem hN; unfold maxLogMem at this; omega
  have hlow : LowDef (logMem N) (imageOf (logMem N) L hdr).read := fun i hi => by
    rw [MemoryImage.read_gpow h64 _ ⟨i, hi⟩]; rfl
  have hL := memL_imageOf h64 hcons (fun q hq => ⟨(hin q hq).1,
    le_trans (hin q hq).2 (le_two_pow_logMem N)⟩) hdr
  obtain ⟨hh0, hh1⟩ := imageOf_hdr h64 (le_trans (by decide) (twentyThree_le_logMem N)) L hdr
  generalize imageOf (logMem N) L hdr = M at hlow hL hh0 hh1
  have e0 : (1 : K) = Parameters.addressOfIndex 0 := by simp [Parameters.addressOfIndex]
  have e1 : Parameters.g = Parameters.addressOfIndex 1 := by simp [Parameters.addressOfIndex]
  obtain ⟨t, hn, hv, hb, hp, ht, hl, -⟩ := hrelL M.read hlow hL (by rw [e0]; exact hh0)
    (by rw [e1]; exact hh1)
  have htot : t.total W0.fsB = N := (Complete.total_eq hA hv).symm.trans ht
  subst htot
  have hkf := kFactsAllG CplEval.cplOkAll hdr t hn
  have ha : ∀ q ∈ t.eqns coreProgram, ∃ i : Fin (2 ^ logMem (t.total W0.fsB)),
      q.1 = addressOfIndex i :=
    dischargeAddr (H := HG) (hdr := hdr) h64 hv hp
      fun I hI f σ bufs kids hIt p r rs ha k hk' => by
        have hcl := (hkf.run I hI f σ bufs kids hIt p r rs ha k hk').1
        have hoff := (hkf.cells.off I hI _ hcl).2
        have hw := honest_within (P := coreProgram) hI (by have := hkf.cells.two_le I hI; omega)
        have := le_two_pow_logMem (t.total W0.fsB)
        omega
  refine ⟨t, M, ⟨hn, by rw [W0_core]; exact hv, by rw [W0_core]; exact hb, ?_, ?_, hh0, hh1, hN,
    by rw [W0_core]; exact ha⟩, hNb⟩
  · rw [W0_core]
    exact (Complete.placed_iff hA t 0 hv).mp hp
  · rw [W0_core]
    exact (Complete.loadsIn_iff hA t _ 0 hv).mp hl

/-- **The guest's core runs exist**: for every node relation within the deployed limits and the
deployed budget within `2^30` words, B1's tree of `main` at the back end's cells is a `CoreRun` of
the statement's public input, within the deployed budget's words. -/
theorem guest_core_run : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
    ChildrenOk bytecode seed w →
    (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).size (work s w) ≤ 2 ^ 30 →
    ∃ (T : Tree) (M : MemoryImage (logMem (T.total W0.fsB))),
      CoreRun (hdrOf (statementDigest seed s)) T M ∧
        T.total W0.fsB ≤ (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).words.eval (work s w) :=
  coreRun_of_main (mainComplete_at (runsFitG CplEval.cplOkAll) (runsConsecG CplEval.cplOkAll))

/-- **The compiled guest runs for every node relation**: within the deployed limits and the
deployed budget within `2^30` words, there is a tree of `main` within the budget's words whose
temporaries re-chosen give an honest memory on which the compiled guest runs from `main`'s entry
to the final registers, within each running instance's placed path maxima. -/
theorem guest_run_from_node : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
    ChildrenOk bytecode seed w →
    (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).size (work s w) ≤ 2 ^ 30 →
    ∃ (T : Tree) (ν : ℕ → String → Val → V → E) (c : Opcode → ℕ), T.name = "main" ∧
      T.total W0.fsB ≤ (Budget.deployedBudget (vsBoundAt Count.vsWordsOs vkBound)).words.eval (work s w) ∧
      RunC W0.prog (W0.honestB (hdrOf (statementDigest seed s)) (T.retemp W0.core W0.fsB ν 0))
        ⟨addressOfIndex (W0.ent "main"), 1⟩ (Registers.final W0.prog) c ∧
      ∀ op, c op ≤ W0.progCost (fun _ => false) (T.retemp W0.core W0.fsB ν 0) op := by
  intro seed s w hrel hlim hok hbs
  obtain ⟨T, M, ⟨hn, hv, hb, hp, hl, h0, h1, hs, ha⟩, hw⟩ := guest_core_run seed s w hrel hlim hok hbs
  obtain ⟨ν, c, hr, hc⟩ := guest_core_complete _ T M hn hv hb hp hl h0 h1 hs ha
  exact ⟨T, ν, c, hn, hw, hr, hc⟩

end
end LeanVM.Guest.Compiled.Cpl

/-- info: 'LeanVM.Guest.Compiled.Cpl.guest_core_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Compiled.Cpl.guest_core_run

/-- info: 'LeanVM.Guest.Compiled.Cpl.guest_run_from_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Compiled.Cpl.guest_run_from_node
