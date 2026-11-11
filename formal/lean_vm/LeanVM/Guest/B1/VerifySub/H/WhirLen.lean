/-
  LeanVM.Guest.B1.VerifySub.H.WhirLen

  `open_stacked` on an honest child: its terminal point has `μ` coordinates.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.TermPre
public import LeanVM.Guest.B1.VerifySub.H.Kids
public import LeanVM.Guest.B1.VerifySub.H.WhirPoint

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem w_point_length : S.w.point.length = S.μs := whir_point_length S.runW

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
