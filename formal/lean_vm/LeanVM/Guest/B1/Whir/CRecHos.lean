/-
  LeanVM.Guest.B1.Whir.CRecHos

  An `open_stacked` tree popping its levels' `level_queries` entries.
-/

module

public import LeanVM.Guest.B1.Whir.CRecChild
public import LeanVM.Guest.B1.VerifySub.CompleteBP
public import LeanVM.Guest.B1.VerifySub.H.WhirLen

/-!
# `open_stacked`'s pops

`OsPopsT`: an `open_stacked` tree pops, stream by stream, its levels' `level_queries` entries (`lvPops`) for levels `Ls` of an honest run (`HonRun`) whose query steps are theirs (`lvSteps`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL)

@[expose] public section

/-- **An `open_stacked` tree pops its levels' `level_queries` entries**, stream by stream, level 0 first, for the
levels of an honest run whose query steps are theirs. -/
def OsPopsT (μ r : ℕ) (target : E) (S : KeccakState) (root : Digest) (xs : List E) (os : List (List Opening))
    (w : Whir.WhirEnd) (rd : Reader) (t : Tree) : Prop :=
  ∃ cfg Ls, Whir.HonRun μ r target S root xs os w cfg Ls ∧
    Limits.queryStepsOf (Whir.whirOpen μ r target) ⟨⟨S, [], none⟩, xs, os, [(root, Whir.stackShape μ r)]⟩ =
      Whir.lvSteps μ 0 Ls ∧
    SameStreams (t.pops coreProgram rd)
      ((List.range (Whir.osCfgR (μ - Whir.minOpenLog) (r - 1)).levels.length).flatMap (Whir.lvPops Ls μ r))

end
end LeanVM.Guest.B1.VerifySub
