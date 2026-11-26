module

public import LeanVM.Cost.ExtractorProgram
public import LeanVM.Cost.Spec
public import LeanVM.Cost.Encoding

/-!
# The extractor's entry

`LeanVM.extractorComputedBy P` (`Statement/CostMachine.lean`), the extractor of the end statement, runs
the program's function `0` on one value, `encodeLeanVmKnowledgeExtractorInput prog input T proof =
.ctor 0 [encodeValue prog, encodeValue input, encodeValue qs, encodeValue proof]` with
`qs = permutationQueries T`, and decodes its output with `decodeExecution prog`, which parses an
execution's encoding. The compiled extractor is a function of four encoded arguments whose output
encodes an `Option (Execution prog)`. The glue is the entry body `entryBody j`
(`Cost/ExtractorProgram.lean`): it destructures the input, calls function `j` on its four fields
and unwraps the option (`none` to `.ctor 0 []`, which no execution decodes from; `some t` to `t`'s
encoding), at most `14` more than the call (`runsBody_entry`: two `case`s and their five fields,
four variables, the call). `decodeExecution_unwrap` decodes the unwrapped option, and
`runsBody_of_outputWithin` reads a run off an output within a budget. The agreement-set
extractor's glue is `Cost/AS/Glue.lean`.
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open Common

public section

/-! ## The entry -/

/-- The value the entry returns for an optional output. -/
@[expose] def unwrapOption {α : Type} [MachineEncoding α] : Option α → MachineValue
  | none => .constructor 0 []
  | some a => encodeValue a

theorem runsBody_entry {P : MachineProgram} {j : ℕ} (hentry : P[0]? = some (entryBody j))
    {α : Type} [MachineEncoding α] {a b c d : MachineValue} {o : Option α} {e : ℕ}
    (h : RunsBody P j [a, b, c, d] (encodeValue o) e) :
    ∃ c', c' ≤ e + 14 ∧ RunsBody P 0 [.constructor 0 [a, b, c, d]] (unwrapOption o) c' := by
  have hargs : RunsList P [a, b, c, d, .constructor 0 [a, b, c, d]] [.position 0, .position 1,
      .position 2, .position 3]
      [a, b, c, d] 4 :=
    RunsList.cons (Runs.var rfl) (RunsList.cons (Runs.var rfl) (RunsList.cons (Runs.var rfl)
      (RunsList.cons (Runs.var rfl) RunsList.nil)))
  have hcall := Runs.call hargs h
  cases o with
  | none =>
    have hcall' : Runs P [a, b, c, d, .constructor 0 [a, b, c, d]]
        (.call j [.position 0, .position 1, .position 2, .position 3]) (.constructor 0 []) (4 + e +
            1) := hcall
    have halt : Runs P ([] ++ [a, b, c, d, .constructor 0 [a, b, c, d]]) (.constructor 0 [])
        (.constructor 0 []) 1 :=
      (Runs.ctor RunsList.nil).cost_eq (by simp)
    have hinner := Runs.case (alts := [.constructor 0 [], .position 0]) hcall' rfl halt
    exact ⟨_, by simp only [List.length_cons, List.length_nil]; omega,
      RunsBody.intro hentry (Runs.case (Runs.var rfl) rfl hinner)⟩
  | some t =>
    have hcall' : Runs P [a, b, c, d, .constructor 0 [a, b, c, d]]
        (.call j [.position 0, .position 1, .position 2, .position 3]) (.constructor 1 [encodeValue
            t]) (4 + e + 1) := hcall
    have halt : Runs P ([encodeValue t] ++ [a, b, c, d, .constructor 0 [a, b, c, d]]) (.position 0) (encodeValue t) 1 :=
      Runs.var rfl
    have hinner := Runs.case (alts := [.constructor 0 [], .position 0]) hcall' rfl halt
    exact ⟨_, by simp only [List.length_cons, List.length_nil]; omega,
      RunsBody.intro hentry (Runs.case (Runs.var rfl) rfl hinner)⟩

theorem decodeExecution_unwrap (prog : Semantics.LeanIsaProgram) (o : Option (Execution prog)) :
    decodeExecution prog (unwrapOption o) = o := by
  cases o with
  | none => rfl
  | some t => exact decodeExecution_enc prog t

/-- An output within a budget is the value of a run. -/
theorem runsBody_of_outputWithin {P : MachineProgram} {s : ℕ} {x v : MachineValue} {b : ℕ}
    (h : outputWithin P s b x = some v) : ∃ c, RunsBody P 0 [x] v c := by
  unfold outputWithin runMachineProgram at h
  split at h
  · split at h
    · rename_i v' c hr
      split at h
      · obtain rfl : v' = v := Option.some.inj h
        exact ⟨c, b + 1, hr⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end

end LeanVM.Cost
