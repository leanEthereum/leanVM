module

public import NativeVm.Transcript.Read
public import NativeVm.Transcript.Sample
public import NativeVm.Transcript.Grind
public import NativeVm.Transcript.Commit
public import NativeVm.Transcript.Finish
public import NativeVm.Transcript.SeedState

/-!
# The transcript machine

The compiled reading of the verifier language (`LeanVM.Protocol.Compile.run`) on the QM machine:
the state's memory and the simulation relation `SimState` (`Transcript.Layout`), the gadgets
(`Transcript.Code`), the steps of `run` per constructor (`Transcript.Run`) and the gadgets' specs.

| gadget | spec | `run`'s step |
|---|---|---|
| `readScalar` | `readScalar_spec` | `readStep` |
| `sampleChallenge` | `sampleChallenge_spec` | `sampleStep` |
| `grind` | `grind_spec` | `grindStep` |
| `commit` | `commit_spec` | `commitStep` |
| `finish` | `finish_spec` | `runProof`'s check (`runProof_eq`) |
| `seed` | `seed_spec` | `runProof`'s initial state, `spongeSeedWith` (`initState`) |

Each spec says the gadget ends normally in a state that simulates the step's result, or fails exactly
when the step is `none`. `query` (`queryStep`) is tested against the statement
(`NativeVm.Test.Transcript`, `cli/VmTranscriptTest.lean`), not yet proved.
-/
