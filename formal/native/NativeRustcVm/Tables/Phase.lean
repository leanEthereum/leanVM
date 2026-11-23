module

public import NativeVm.Model.Tables

/-!
# Phase 4 as `table_phase` runs it

`ξ`'s five powers (`size_powers`), the first two the constraints', the last three the forms';
the phase is the grind, then the table sumcheck on them (`tablePhase_run`).
-/

namespace NativeRustcVm.Tables

open NativeVm.Model
open LeanVM.Protocol.Verifier (nTrees)

public section

theorem foldl_powers (b : EW) (n : Nat) (acc : Array EW × EW) :
    ((List.range n).foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * b)) acc).1.size =
      acc.1.size + n := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append]; simp [ih]; omega

theorem size_powers (b : EW) (n : Nat) : (powers b n).size = n := by
  have := foldl_powers b n (#[], 1)
  simpa [powers] using this

theorem grindingBits_four : grindingBits 4 = 0 := by decide +kernel

theorem bitLength_three : LeanVM.Protocol.Verifier.bitLength 3 = 2 := by decide +kernel

theorem nConstraints_eq : (tablesW.map (·.nConstraints)).sum = 2 := by decide +kernel

theorem extract_drop {P : Array EW} (h : P.size = 5) : (P.toList.drop 2).toArray = P.extract 2 5 := by
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract, ← h]

theorem extract_take {P : Array EW} : (P.toList.take 2).toArray = P.extract 0 2 := by
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract]

/-- **Phase 4**: the grind, `ξ`, the table sumcheck on `ξ`'s powers. -/
theorem tablePhase_run (L : LayoutW) (bus : BusResultW) (s : TState) :
    (tablePhase L bus).run s = ((grind (grindingBits 4)).run s).bind fun p ↦
      (tableSumcheck L.tableLogHeights bus.forms ((powers p.2.sponge.squeeze.1 5).extract 0 2)
        ((powers p.2.sponge.squeeze.1 5).extract 2 5) bus.point
        (dot ((powers p.2.sponge.squeeze.1 5).extract 2 5) bus.totals)).run
        { p.2 with sponge := p.2.sponge.squeeze.2 } := by
  have hn : nTrees = 3 := rfl
  simp only [tablePhase, nConstraints_eq, hn, sampleChallenge, size_powers, StateT.run]
  cases h : grind (grindingBits 4) s with
  | none => simp [bind, StateT.bind, h]
  | some p => simp [bind, StateT.bind, h, get, getThe, MonadStateOf.get, StateT.get, set,
      StateT.set, pure, StateT.pure]

end

end NativeRustcVm.Tables
