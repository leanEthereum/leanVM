/-
  LeanVM.Guest.B1.Selectors.Glue

  The selector functions at the guest's `coreProgram`: the kernel checks that its functions are the
  templates, and the statements they give.
-/

module

public import LeanVM.Guest.B1.Selectors.IndexMle
public import LeanVM.Guest.B1.Selectors.Interface

namespace LeanVM.Guest.B1.Tables

open LeanVM.Guest.Core

@[expose] public section

theorem imCheck_all : (List.range 34).all (imCheckP coreProgram) = true := by decide +kernel

theorem index_mle_holds : index_mle_Spec := index_mle_holdsP coreProgram imCheck_all

end
end LeanVM.Guest.B1.Tables
