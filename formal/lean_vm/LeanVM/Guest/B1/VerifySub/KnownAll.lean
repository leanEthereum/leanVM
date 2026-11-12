/-
  LeanVM.Guest.B1.VerifySub.KnownAll

  `VsKnown`: the first `1552` statements of `verify_sub` put `kappa_base`'s entries among `g^e`,
  `e < kbBound i`; `VsDimsKnown`: the first `333` put `dims_g[g^0]` below `g^34`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.B1.Placement.Certify

/-!
# `verify_sub`'s cut obligations

`vsKnown_holds`: `vsKnown_of` with `certify_placement`'s soundness (`certify_placement_holds`):
on a memory image of `2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`, over the exponent table at
`verify_sub`'s argument `4`, its first `1552` statements (up to the call of
`check_opening_terminal`) put the `8` entries of `kappa_base` (`83`) among `g^e`, `e < kbBound i`.

`vsDimsKnown0_holds`: on a memory image of `2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`, the body's
first `333` statements (up to the call of `verify_tables`) put `dims_g[g^0] = g^logMem`,
`logMem ≤ 32`, below `g^34`: the head and the reads hand nothing on, and the sizes
(`vsSizesT_holds`) give it. The other six words (`table_logs`) are a hint there, certified only
inside `verify_tables`, so no such bound holds of them before its call.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem vsFront73_length : (vsHeadT ++ vsReadsT ++ vsSizesT).length = 73 := by decide +kernel

theorem vsT_front73 : vsT = (vsHeadT ++ vsReadsT ++ vsSizesT) ++ (vsPushT ++ vsRootsT ++
    vsPlaceT ++ vsOodT ++ vsBusGrindT ++ vsFpwT ++ vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++
    vsTailT) := by
  simp only [vsT, List.append_assoc]

/-- **`VsKnown`**: `kappa_base`'s entries below `kbBound`. -/
theorem vsKnown_holds {κ : ℕ} (L : MemoryImage κ) (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (σ : Val) (hexp : B1.ExpTables L.read (σ (.n 4)))
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 1552) True
      (fun _ ↦ True)) :
    ∀ i < 8, ∃ e < kbBound i, LoadHolds L.read (σ (.n 83)) i (ofK (addressOfIndex e)) :=
  vsKnown_of L h16 h32 (Tables.certify_placement_holds (h32.trans (by decide)) L) σ hexp h

/-- **`dims_g`'s first word** (the memory's log, G:3578-3581): the body's first `333` statements
(up to the call of `verify_tables`) put `dims_g[g^0] = g^logMem`, `logMem ≤ 32`, below `g^34`. -/
theorem vsDimsKnown0_holds {κ : ℕ} (L : MemoryImage κ) (_hmin : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (σ : Val)
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 333) True
      (fun _ ↦ True)) :
    ∃ e < 34, LoadHolds L.read (σ (.n 71)) 0 (ofK (addressOfIndex e)) := by
  have hκ : κ ≤ 32 := h32.trans (by decide)
  have hle : CallRel.Le (coreProgram.Rel L.read) (coreProgram.Rel L.read) := fun _ _ _ h ↦ h
  rw [show Fn.body Data.core18 = vsT from vs_body, vsT_front73, List.take_append, List.take_of_length_le (by rw [vsFront73_length]; omega),
    holdsList_append, holdsList_append, holdsList_append] at h
  have h := ((holdsList_noRet _ vsHeadT_noRet _ _).1 h).2
  have h := ((holdsList_noRet _ vsReadsT_noRet _ _).1 h).2
  obtain ⟨-, logMem, -, -, -, -, -, hm32, -, -, ds, -, hd, -⟩ := vsSizesT_holds hκ L hle h
  exact ⟨logMem, by omega, by rw [← gen_pow_eq_ofK]; exact hd 0 (by simp)⟩

end
end LeanVM.Guest.B1.VerifySub
