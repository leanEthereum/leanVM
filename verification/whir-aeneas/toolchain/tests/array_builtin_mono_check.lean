import Arrayrepeat
open Aeneas Aeneas.Std

theorem repeat_seed_content (seed : U8) :
    ∃ output, ArrayRepeat.repeat_seed seed = .ok output ∧ output.val = List.replicate 3 seed := by
  refine ⟨Aeneas.Std.Array.repeat 3#usize seed, rfl, ?_⟩
  simp [Aeneas.Std.Array.repeat]
#print axioms repeat_seed_content
#print axioms ArrayRepeat.repeat_seed

def main : IO Unit := do
  for n in [0, 17, 255] do
    match (ArrayRepeat.repeat_seed (⟨BitVec.ofNat 8 n⟩ : U8)).match with
    | .ok result =>
      if result.val.map (fun x => x.val) != List.replicate 3 n then
        throw (IO.userError "extracted repeat disagrees with source")
    | _ => throw (IO.userError "extracted repeat failed")
  IO.println "extracted repeat agrees for seeds 0, 17, 255"
