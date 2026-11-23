module

public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Code.Vm.ConstraintsW.Names
public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Tables.TableTerms.Read
public import NativeRustcVmArm.Tables.TableTerms.Cons
public import NativeRustcVmArm.Tables.TableTerms.Next

/-!
# `table_terms`: the loop over the six tables

From the head before table `i`: its evaluations (`read_step`), constraints (`cons_step`), forms
(`forms_step`), point (`ext_step`), and the running sum (`next_step`), to the head before table
`i + 1` or, after the sixth, the exit (`body`); all six by induction (`loop`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVmArm.Vm.TableTerms
open NativeRustcVm (BufEWAt)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- The callees' contracts. -/
structure Callees : Prop where
  rs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s)
  cw : Spec (Labels.label NativeRustcVmArm.Vm.ConstraintsW.entryLabel) ConstraintsWPre ConstraintsWPost
  dot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost
  ev : ∀ f, Spec (Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f)
  ext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30)
  mul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost

/-- **Table `i`**, from the head before it. -/
theorem body (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hh : heights.size = 6) (hf : forms.size = 6) (C : Callees) {i : Nat} (hi : i < 6)
    (contL : i + 1 < 6 → ∀ acc si m, Head a s heights forms m0 (i + 1) acc si m →
      Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b1Offset)⟩)
    (acc : Acc) (si : TState) (m : MachineData) (H : Head a s heights forms m0 i acc si m) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b1Offset)⟩ := by
  obtain ⟨c, f, o⟩ := acc
  have hc : c = cursorAt i := H.cur
  subst hc
  refine read_step hp h hh hf C.rs hi H fun xs s' m1 hr It1 hl1 x19 x22 x23 x28 ↦ ?_
  have hxs := NativeRustcVm.Sumcheck.readScalars_size hr
  refine cons_step hp h C.cw C.dot hi It1 hl1 x19 x28 hxs
    fun m2 It2 fw2 _ x28' x22' _ hsm ↦ ?_
  have e22 : rg m1 .X22 = f.c0.toBitVec := congrArg UInt64.toBitVec x22
  have e23 : rg m1 .X23 = f.c1.toBitVec := congrArg UInt64.toBitVec x23
  rw [e22, e23] at fw2
  refine forms_step hp h C.ev C.dot hi It2 fw2 x28' hxs x22' hsm
    fun m3 It3 fw3 x19'' x28'' x23'' x22'' hfd ↦ ?_
  refine ext_step hp h C.ext hi It3 fw3 x19'' x28'' x23'' x22'' hfd
    fun m4 It4 fw4 y19 y28 y23 y22 y24 y25 hpt ↦ ?_
  exact next_step hp h hh hf C.mul hi H.run hr H.osz It4 fw4 y19 y28 y23 y22 y24 y25 hpt
    (fun hi1 m' Hn ↦ contL hi1 _ _ m' Hn) (fun _ m' Hn ↦ exit_some hp h hh hf Hn)

/-- **The tables from `i`.** -/
theorem loop (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hh : heights.size = 6) (hf : forms.size = 6) (C : Callees) :
    ∀ n i, i + n = 5 → ∀ acc si m, Head a s heights forms m0 i acc si m →
      Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b1Offset)⟩ := by
  intro n
  induction n with
  | zero => exact fun i hi ↦ body hp h hh hf C (by omega) fun h' ↦ absurd h' (by omega)
  | succ n ih => exact fun i hi ↦ body hp h hh hf C (by omega) fun _ ↦ ih (i + 1) (by omega)

end

end NativeRustcVmArm.Tables.TableTerms
