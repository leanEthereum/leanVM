/-
  LeanVM.Guest.B1.VerifySub.KnownAll

  `VsDimsKnown`: the first `333` statements of `verify_sub` put `dims_g[g^0]` below `g^34`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Mid
public import LeanVM.Guest.B1.VerifySub.Body

/-!
# `verify_sub`'s cut obligations

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

theorem vsHeadT_noRet : Stmt.noRetList vsHeadT = true := by decide +kernel

theorem vsReadsT_noRet : Stmt.noRetList vsReadsT = true := by decide +kernel

theorem vsFront73_length : (vsHeadT ++ vsReadsT ++ vsSizesT).length = 73 := by decide +kernel

theorem vsT_front73 : vsT = (vsHeadT ++ vsReadsT ++ vsSizesT) ++ (vsPushT ++ vsRootsT ++
    vsPlaceT ++ vsOodT ++ vsBusGrindT ++ vsFpwT ++ vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++
    vsTailT) := by
  simp only [vsT, List.append_assoc]

/-- **`dims_g`'s first word** (the memory's log, G:3603-3606): the body's first `333` statements
(up to the call of `verify_tables`) put `dims_g[g^0] = g^logMem`, `logMem ≤ 32`, below `g^34`. -/
theorem vsDimsKnown0_holds {κ : ℕ} (L : MemoryImage κ) (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (σ : Val)
    (h : Stmt.HoldsList (coreProgram.Rel L.read) L.read σ ((Fn.body Data.core18).take 333) True
      (fun _ ↦ True)) :
    ∃ e < 34, LoadHolds L.read (σ (.n 71)) 0 (ofK (addressOfIndex e)) := by
  have hκ : κ ≤ 32 := h32
  have hκ6 : 6 ≤ κ := by have : 16 ≤ κ := h16; omega
  have hle : CallRel.Le (coreProgram.Rel L.read) (coreProgram.Rel L.read) := fun _ _ _ h ↦ h
  rw [vs_body, vsT_front73, List.take_append, List.take_of_length_le (by rw [vsFront73_length]; omega),
    holdsList_append, holdsList_append, holdsList_append] at h
  have h := ((holdsList_noRet _ vsHeadT_noRet _ _).1 h).2
  have h := ((holdsList_noRet _ vsReadsT_noRet _ _).1 h).2
  obtain ⟨-, logMem, -, -, -, -, -, hm32, -, -, ds, -, hd, -⟩ := vsSizesT_holds hκ hκ6 L hle h
  exact ⟨logMem, by omega, by rw [← gen_pow_eq_ofK]; exact hd 0 (by simp)⟩

end
end LeanVM.Guest.B1.VerifySub
