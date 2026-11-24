/-
  LeanVM.Protocol.Compile.RunPure

  The verifier program run with every permutation answered by `default` (`Compile.runPure`), and the
  layout and rate a stream announces (`Verifier.announcedLayoutAndRate`), both in
  `Statement/Verifier/Lib.lean`, which the extractor's budget reads
  (`Statement/LeanVmExtractor.lean`).
-/

module

import Statement.Verifier.Lib
public import CompPoly.Fields.Binary.BF64
