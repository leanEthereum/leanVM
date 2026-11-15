/-
  LeanVM.Guest.Backend.Complete.FrameStmts

  The statements on the path with the primitives' facts discharged.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameSegs
public import LeanVM.Guest.Backend.Complete.FrameAtoms

/-!
# Statements on the path, primitives discharged

`stmtW_atom` and `stmtW_ret` with the flush (`flushSeg_lock`) and the chain flag
(`chainKeep_atom'`, `chainKeep_ret'`) given; the atoms against the current `AtomFAt` and the pools
kept off the temporaries (`PoolKeepStmt`) are the primitives' agent's, named until merged.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Ctx} {I : Inst}

/-- **An atom on the path**, the flush and chain flag given. -/
theorem stmtW_atom' (hpk : PoolKeepStmt) (hat : ∀ a, AtomFAt a) (hok : OpOK Γ I Ag cl)
    (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0)
    (hRd : ∀ rd, I.Rd rd → ∀ e ∈ I.es, evNT rd I.σ e) {a : Atom} {rest tl : List Stmt}
    (hu : ∀ v ∈ Memory.atomUses a, v ∉ I.tmps) (ht : ∀ t ∈ Memory.atomTmps a, t ∈ I.tmps)
    (hnm : ∀ v ∈ Memory.atomUses a, v ∈ I.named) (hfa : ∀ p run, a ≠ .frameAddr p run) :
    StmtW Γ Ag cl ctx I (.atom a) rest tl :=
  stmtW_atom flushSeg_lock hpk hok hI hmain hRd (hat a) chainKeep_atom' hu ht hnm hfa

/-- **A return on the path**, the primitives' facts given. -/
theorem stmtW_ret' (hok : OpOK Γ I Ag cl) (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0)
    {vs : List V} {rest tl : List Stmt}
    (hAg : ∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L → ∀ n < I.size,
      L.read (addressOfIndex (I.fp + n)) = some (fwd I.hdr ⟨patchT I Ψ σ', kh⟩ n))
    (hhdr : ctx.isMain = false → IsInK I.hdr.1 ∧ IsInK I.hdr.2)
    (hkend : IsInK (I.kw .endSentinel)) :
    StmtW Γ Ag cl ctx I (.ret vs) rest tl :=
  stmtW_ret flushSeg_lock hok hI hmain chainKeep_ret' hAg hhdr hkend

end
end LeanVM.Guest.Backend.Complete
