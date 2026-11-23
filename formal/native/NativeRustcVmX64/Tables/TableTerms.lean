module

public import NativeRustcVmX64.Tables.TableTerms.SumStep
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.ConstraintsW.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Evaluate.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TableTerms.Names

/-!
# `table_terms` meets its contract (x86-64)

`entry` (`b0`), then for each of the six tables: its evaluations (`read_step`, `b1` to `b3`), the
constraints' dot product (`cons_step`, `b4`, `b5`), the forms' (`forms_step`, `b6` to `b9`), its
point (`point_step`, `b10`, `b11`), its sum (`sum_step`, `b12`, `b13`); after the sixth `Some` of
the sum (`exit_some`), on a rejection `None` (`exit_none`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVm.Bus
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.TableTerms

public section

variable [Host] {k : Nat}

/-- **`table_terms` meets its contract.** -/
theorem tableTerms_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hcw : Spec (Labels.label NativeRustcVmX64.Vm.ConstraintsW.entryLabel) ConstraintsWPre ConstraintsWPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmX64.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)} :
    Spec (Labels.label NativeRustcVmX64.Vm.TableTerms.entryLabel) (TableTermsPre a s heights forms)
      (TableTermsPost a s heights forms) := by
  intro m0 h
  rw [lbl_entry hp]
  have hh : heights.size = 6 := (Pre.hts h).1
  have hf : forms.size = 6 := forms_size h
  refine entry hp h fun d H ↦ ?_
  have loop : ∀ n i acc si d, 6 - i = n → i < 6 → Head a s heights forms m0 i acc si d →
      Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.TableTerms.b1Offset)⟩ := by
    intro n
    induction n with
    | zero => intro i _ _ _ hn hi; omega
    | succ n ih =>
      intro i acc si d hn hi H
      obtain ⟨c, f, o⟩ := acc
      refine read_step hp h hh hf hrs hi H fun xs s' d1 R1 ↦ ?_
      refine cons_step hp h hcw hdot hi R1 fun d2 C2 rax2 rdx2 fw2 r12 rbx r13 ↦ ?_
      refine forms_step hp h hev hdot hi C2 rax2 rdx2 fw2 r12 rbx r13
        fun d3 C3 fw3 rax3 rdx3 r12' r13' ↦ ?_
      refine point_step hp h hext hi C3 fw3 rax3 rdx3 r12' r13'
        fun d4 hb4 fw4 it4 pt4 r14 r13'' r15 rbx' rbp r12'' ↦ ?_
      refine sum_step hp h hh hf hmul hi R1.run R1.cur R1.rs hb4 fw4 it4 pt4 r14 r13'' r15 rbx'
        rbp r12'' fun acc' d5 _ H5 ↦ ⟨fun hlt ↦ ih (i + 1) acc' s' d5 (by omega) hlt H5,
          fun heq ↦ ?_⟩
      have H6 : Head a s heights forms m0 6 acc' s' d5 := heq ▸ H5
      exact exit_some hp h hh hf H6
  exact loop 6 0 _ _ d rfl (by omega) H

end

end NativeRustcVmX64.Tables.TableTerms
