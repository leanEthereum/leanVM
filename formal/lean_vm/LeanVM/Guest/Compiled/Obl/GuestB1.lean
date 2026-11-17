/-
  LeanVM.Guest.Compiled.Obl.GuestB1

  The guest's obligations with B1's theorems for the facts the analysis takes from outside.
-/

module

public import LeanVM.Guest.Compiled.Obl.Guest
public import LeanVM.Guest.B1.VerifySub.KnownAll
public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.Bits.Tables

/-!
# The bridge to B1

The facts `guest_obligations_of` takes are B1's theorems, stated over the core program and a
valuation, with no certificate:

* `expPost_B1`: `exponent_tables`' relation is the exponent table and its window section (B1-a's
  `exponent_tables_holds`);
* `vsFacts_B1`: `verify_sub`'s first `333` statements bound `dims_g[g^0]` below `g^34`
  (`VerifySub.vsDimsKnown0_holds`), its first `1544` put the window table at `tabs`, `g_squares ·
  g^winTabAt` with `g_squares` its argument `4` (`VerifySub.vsTabsT_holds` on its statements `1542`
  and `1543`), its first `1545` the eight words of `kappa_base` below `kbBound`
  (`VerifySub.vsKnown_holds`, over the exponent table at its argument `4`).

`guest_obligations` is then `guest_obligations_of`: every function's obligations, with no further
hypothesis.
-/

namespace LeanVM.Guest.Compiled.Obl

open LeanVM.Compiler LeanVM.Compiler.Obl LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`exponent_tables` returns the exponent table and its window section** (B1-a). -/
theorem expPost_B1 : ExpPost := by
  intro rd a r h
  have := (B1.exponent_tables_holds rd a r).mp h
  match a, r, this with
  | [], [q], h => exact h

theorem vs_body : (coreProgram.getD vsIdx default).body = Fn.body fn% «verify_sub» := rfl

theorem vs_takeTabs : (coreProgram.getD vsIdx default).body.take 1544 =
    (coreProgram.getD vsIdx default).body.take 1542 ++ B1.VerifySub.vsTabsT 1920 1921 := by
  rw [show 1544 = 1542 + 2 from rfl, List.take_add]
  exact congrArg ((coreProgram.getD vsIdx default).body.take 1542 ++ ·)
    (B1.stmtsEqb_sound (by decide +kernel))

theorem vs_noRetTabs :
    Stmt.noRetList ((coreProgram.getD vsIdx default).body.take 1542) = true := by
  decide +kernel

/-- A bound on the word at `p · g^c`, read, in `MemB`'s form. -/
theorem memB_of {rd : Reader} {p : E} {c n : ℕ}
    (h : ∃ e < n, LoadHolds rd p c (ofK (addressOfIndex e))) : MemB rd p c n := by
  intro v hv
  obtain ⟨e, he, hl⟩ := h
  exact ⟨e, he, B1.loadHolds_unique hv hl⟩

theorem kbBound_lt (c : ℕ) : kbBound c < 2 ^ 16 := by
  unfold kbBound
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | c <;> simp

/-- **`verify_sub`'s facts** (B1-d). -/
theorem vsFacts_B1 : VsFacts := by
  intro κ L h1 h2 σ hex p hp hl
  simp only [vsFacts, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hp
  rcases hp with (rfl | rfl | rfl | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩
  · rw [vs_body] at hl
    exact memB_of (B1.VerifySub.vsDimsKnown0_holds L h1 h2 σ hl)
  · rw [vs_body] at hl
    exact guestRel_memRel (by norm_num) (B1.VerifySub.vsDimsKnown0_holds L h1 h2 σ hl)
  · rw [vs_takeTabs, holdsList_append, holdsList_noRet _ vs_noRetTabs] at hl
    obtain ⟨he, -⟩ := B1.VerifySub.vsTabsT_holds hl.2
    refine ⟨fun h => absurd h (by decide), fun _ n hn => ?_, fun h => absurd h (by decide),
      fun h => absurd h (by decide)⟩
    rw [he]
    exact (B1.loadHolds_mul_gen_pow _ _ _ _ _).mpr (hex.2 n hn)
  · rw [vs_body] at hl
    exact memB_of (B1.VerifySub.vsKnown_holds L h1 h2 σ hex.1 hl c hc)
  · rw [vs_body] at hl
    exact guestRel_memRel (kbBound_lt c) (B1.VerifySub.vsKnown_holds L h1 h2 σ hex.1 hl c hc)

variable {κ : ℕ} {W : World κ}

/-- **The guest's obligations**: every function of a compiled program whose core is the guest's
and whose precondition is `guestU` has its obligations, on a memory of `2^κ` words,
`minLogMem ≤ κ ≤ maxLogMem`. -/
theorem guest_obligations (hW : W.Compiled) (hcore : W.p.map (·.core) = coreProgram)
    (hκ : minLogMem ≤ κ ∧ κ ≤ maxLogMem) (hU : W.U = guestU W.L.read) :
    ∀ tf ∈ W.p, W.Obligations tf :=
  guest_obligations_of hW hcore hκ hU expPost_B1 vsFacts_B1

end
end LeanVM.Guest.Compiled.Obl

/-- info: 'LeanVM.Guest.Compiled.Obl.guest_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Compiled.Obl.guest_obligations
