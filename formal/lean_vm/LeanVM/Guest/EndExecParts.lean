/-
  LeanVM.Guest.EndExecParts

  `ExecGaps` with the prologue (`pro`, `init`'s prologue part) and `RefOk` (`ref`) discharged: the
  fields left are the other tracks'.
-/

module

public import LeanVM.Guest.EndExecPro
public import LeanVM.Guest.CoreMode.Fam.RefOk
public import LeanVM.Guest.CoreMode.Sig.«P8»

/-!
# `ExecGaps` from its parts

`ExecGaps Ks Km E0 X (fun _ ↦ ProAt)` from the fields the prologue and the
reference step do not give, `pro` and the prologue's part of `init` from `pro_step` and `pro_init`
(given `MainOk`, which `mainOk_of` reads off `main`'s signature), and `ref` from `refOk_of_pow`,
given that a taken `JUMP`'s frame is a power below `2^62` on the reference (`PtrPow`, what the
honest memory's frame cells hold).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Prover.Exec

@[expose] public section

/-- `main`'s signature: entered at its header alone. -/
theorem mainSig_ok : Fn.«main».csig.entry = [0, 1] ∧ Fn.«main».csig.self = none ∧
    Fn.«main».csig.pre = [] ∧ Fn.«main».csig.preR = [] ∧ Fn.«main».csig.preP = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`MainOk` from `main`'s signature**, entry and the guest's table. -/
theorem mainOk_of {Km : Mode.Cert} {E0 : Mode.Env} (hsig : Km.F.sig = Fn.«main».csig)
    (hent : Km.F.entry = Data.f0.instructionCount) (hpows : E0.pows = Data.powTree) (hjt : E0.jt = Data.jtTrie)
    (hlo : E0.jtLo = Data.mainCells) (hhi : E0.jtHi = Data.mainCells + Data.f0.instructionCount) : MainOk Km E0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mainSig_ok
  have hmc := mainCells_eq
  have hpl : proLen = Data.f0.instructionCount := rfl
  exact ⟨by omega, hpows, hjt, by omega, by omega,
    fun o ho ↦ by rw [hsig, h1] at ho; simp at ho; omega, hsig ▸ h2, hsig ▸ h3, hsig ▸ h4, hsig ▸ h5⟩

end

end LeanVM.Guest.EndExec
