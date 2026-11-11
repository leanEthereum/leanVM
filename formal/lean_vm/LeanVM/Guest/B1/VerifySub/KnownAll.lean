/-
  LeanVM.Guest.B1.VerifySub.KnownAll

  `VsKnown`: the first `1593` statements of `verify_sub` put `kappa_base`'s entries among `g^e`,
  `e < kbBound i`; the first `552` put `dims_g[g^0]` below `g^34`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Known
public import LeanVM.Guest.B1.Tables.HoldsC

/-!
# `VsKnown`

`vsKnown_holds`: on a memory image of `2^κ` words, `minLogMem ≤ κ ≤ maxLogMem`, over the exponent
table at `verify_sub`'s argument `4`, the body's first `1593` statements (up to the call of
`check_opening_terminal`) put the `8` entries of `kappa_base` (`139`) among `g^e`, `e < kbBound i`.
They are the front (`vs_front`, through `verify_tables`: the tables' heights below `29` and
`kappa_base`), the ring map, `c_table` and the batching (no `ret`, skipped), and the first `6`
statements of the tail (`vsKnown_tail`). The callees are B1-c's proved specifications; the
bytecode `verify_tables` is read against is any of `2^23` words (its words do not enter).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`VsKnown`** (G5's obligation on `verify_sub`): `kappa_base`'s entries below `kbBound`. -/
theorem vsKnown_holds {κ : ℕ} (L : MemoryImage κ) (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (σ : Val) (hexp : B1.ExpTables L.read (σ (.n 4)))
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 1593) True
      (fun _ ↦ True)) :
    ∀ i < 8, ∃ e < kbBound i, LoadHolds L.read (σ (.n 139)) i (ofK (addressOfIndex e)) :=
  have hκ : κ ≤ 32 := h32.trans (by decide)
  have hle : CallRel.Le (coreProgram.Rel L.read) (coreProgram.Rel L.read) := fun _ _ _ h ↦ h
  vsKnown_of L h16 h32 (Tables.verify_bus_gkr_holdsC hκ L hle)
    (Tables.verify_tables_holdsC hκ L _ List.length_replicate hle) (Tables.certify_placement_holds hκ L)
    σ hexp h

/-- **`dims_g`'s first word** (the memory's log, G:3367-3370): the body's first `552` statements
(up to the call of `verify_tables`) put `dims_g[g^0] = g^logMem`, `logMem ≤ 32`, below `g^34`.
The other six words (`table_logs`) are a hint there, certified only inside `verify_tables`
(G:2189), so no such bound holds of them before its call. -/
theorem vsDimsKnown0_holds {κ : ℕ} (L : MemoryImage κ) (_hmin : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (σ : Val)
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 552) True
      (fun _ ↦ True)) :
    ∃ e < 34, LoadHolds L.read (σ (.n 127)) 0 (ofK (addressOfIndex e)) := by
  have hκ : κ ≤ 32 := h32.trans (by decide)
  have hle : CallRel.Le (coreProgram.Rel L.read) (coreProgram.Rel L.read) := fun _ _ _ h ↦ h
  have hT : vsT = (vsHeadT ++ vsReadsT ++ vsSizesT) ++ (vsPushT ++ vsRootsT ++ vsAlphasT ++
      vsFpwT ++ vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++ vsTailT) := by
    simp only [vsT, List.append_assoc]
  have hL : (vsHeadT ++ vsReadsT ++ vsSizesT).length = 121 := by decide +kernel
  rw [show Fn.body Data.core18 = vsT from vs_body, hT, List.take_append,
    List.take_of_length_le (by rw [hL]; omega), holdsList_append, holdsList_append,
    holdsList_append] at h
  obtain ⟨-, -, -, -, -, h⟩ := vsHeadT_holds h
  obtain ⟨-, -, -, h⟩ := vsReadsT_holds h
  obtain ⟨-, logMem, -, -, -, -, -, hm32, -, -, ds, -, hd, -⟩ := vsSizesT_holds hκ L hle h
  exact ⟨logMem, by omega, by rw [← gen_pow_eq_ofK]; exact hd 0 (by simp)⟩

end
end LeanVM.Guest.B1.VerifySub
