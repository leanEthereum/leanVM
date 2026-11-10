import Rv64Verifier.Proofs.Layout.Evaluate
import Rv64Verifier.Proofs.Layout.BusBridge
import Rv64Verifier.Proofs.Bus.TsTerminalForms

/-!
# `Form::evaluate` for the bus proofs

`table_sumcheck` calls `Form::evaluate` with either slice possibly empty and anywhere
(`FormEvaluateSpecE`); `EvaluateSpec` asks only valid memory, which an empty slice has.
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Model.LayoutMirror

theorem region_vmr {a x : Word} {n m : Nat} (h : Transcript.Region a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 * m ≤ a.toNat + n) (h3 : x.toNat % 8 = 0) : ValidMemRange x m := by
  intro i hi
  have hR := h
  simp only [Transcript.Region, Mapped] at hR
  exact h.valid (by addr_omega [h1, h2, hi, hR]) (by addr_omega [h1, h2, hi, hR])
    (by addr_omega [h3, h2, hi, hR])

theorem evaluatePre_of_e {s : MachineState} (h : Proofs.Bus.TableSumcheck.FormEvaluatePreE s) :
    EvaluatePre s where
  out := region_vmr h.ret (le_refl _) (by omega) h.ret.2
  terms := by
    rcases h.terms with h0 | hR
    · intro i hi; omega
    · exact region_vmr hR (le_refl _) (by omega) hR.2
  column := by
    rcases h.columns with h0 | hR
    · intro i hi; omega
    · exact region_vmr hR (le_refl _) (by omega) hR.2
  stack := h.stack.toStackOk
  outStack := h.retStack
  termsStack := h.termsStack
  columnStack := h.columnsStack
  rodata := h.rodata
  stackRodata := h.stack.rodata

theorem formEvaluateE_spec (hE : EvaluateSpec) : Proofs.Bus.TableSumcheck.FormEvaluateSpecE :=
  fun s hpc hpre ↦ (hE s hpc (evaluatePre_of_e hpre)).imp fun _ ⟨hr, ht⟩ ↦
    ⟨hr, ht.imp_left fun ⟨a, b, c⟩ ↦ ⟨a, b, c.value, fun x hx ↦ by
      have hw := hx 0 (by decide)
      rw [BitVec.add_zero] at hw
      exact c.frame x (fun h' ↦ hw (Or.inl h')) fun h' ↦ hw (Or.inr h')⟩⟩

end Rv64Verifier.Layout
