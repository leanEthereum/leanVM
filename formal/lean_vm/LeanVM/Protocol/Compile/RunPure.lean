/-
  LeanVM.Protocol.Compile.RunPure

  The verifier program run with every permutation answered by `default` (`Compile.runPure`), and
  the layout and rate a stream announces (`Verifier.announcedLayoutAndRate`), both in
  `Statement/LeanVmVerifier.lean`, where the extractor's budget reads them.
-/

module

public import Statement.LeanVmVerifier

@[expose] public section

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

/-- A run with every permutation answered by `default`, for the steps that only read scalars: what
they read does not depend on the sponge. -/
def runPure {α : Type} (program : VerifierProgram α) (s : VerifierProgramState) : Option
    (α × VerifierProgramState) :=
  Id.run (run (m := Id) (fun _ ↦ default) program s)

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- The announced layout and rate exponent of a stream, read by the program's own
`readAnnouncedSizes` (reads only absorb: no hash or permutation is consulted for a value). -/
def announcedLayoutAndRate (bytecode : List K) (stream : List E) : Option (Layout × ℕ) :=
  (runPure (readAnnouncedSizes bytecode) ⟨⟨default, [], none⟩, stream, [], []⟩).map (·.1)

end LeanVM.Protocol.Verifier

end
