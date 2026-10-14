import Whir.PCSBCSChallengeOraclePackets

/-! The actual atomic compiler records complete dependent packet answers.
This is a trace identity, not an assertion that native acceptance or every
completion prefix has already been recorded. -/
set_option autoImplicit false
namespace Whir.PCSBCSAtomicAllocationTrace
open FiatShamirGame TypedOracleCompiler RawOracleCoupling PCSBCSChallengeOracle

variable {Raw Packet : Type} {Block : Packet → Type}

def allocation (part : Partition Raw Packet Block)
    (table : (key : part.Key) → part.Answer (D := Digest32) key)
    (raw : Raw) : Sigma (part.Answer (D := Digest32)) :=
  match found : part.recognize raw with
  | some block => ⟨.inl block.1,table (.inl block.1)⟩
  | none => ⟨.inr ⟨raw,found⟩,table (.inr ⟨raw,found⟩)⟩

theorem execute_request (part : Partition Raw Packet Block)
    (table : (key : part.Key) → part.Answer (D := Digest32) key) (raw : Raw) :
    (Sampling.execute table (Atomic.request part raw)).2 = [allocation part table raw] := by
  unfold Atomic.request allocation
  split
  · rename_i first hit
    split
    · rename_i second other
      have same := Option.some.inj (hit.symm.trans other)
      cases same
      rfl
    · rename_i missed
      have impossible := hit.symm.trans missed
      cases impossible
  · rename_i missed
    split
    · rename_i second hit
      have impossible := missed.symm.trans hit
      cases impossible
    · rfl

theorem execute_program (part : Partition Raw Packet Block)
    (table : (key : part.Key) → part.Answer (D := Digest32) key)
    {R : Type} {n : Nat} (program : Sampling Raw (fun _ => Digest32) R n) :
    (Sampling.execute table (Atomic.program part program)).2 =
      ((Sampling.execute (part.join table) program).2.map
        (fun actual => allocation part table actual.1)) := by
  induction program with
  | ret result => rfl
  | draw raw next ih =>
    simp only [Atomic.program,Sampling.execute_pad,Sampling.execute_bind,
      Atomic.eval_request,Sampling.execute,List.map_cons]
    rw [execute_request,ih]
    rfl

theorem recognized_recorded (part : Partition Raw Packet Block)
    (table : (key : part.Key) → part.Answer (D := Digest32) key)
    {R : Type} {n : Nat} (program : Sampling Raw (fun _ => Digest32) R n)
    (raw : Raw) (answer : Digest32) (block : Sigma Block)
    (recorded : (⟨raw,answer⟩ : Sigma (fun _ : Raw => Digest32)) ∈
      (Sampling.execute (part.join table) program).2)
    (recognized : part.recognize raw = some block) :
    (⟨.inl block.1,table (.inl block.1)⟩ : Sigma (part.Answer (D := Digest32))) ∈
      (Sampling.execute table (Atomic.program part program)).2 := by
  rw [execute_program]
  apply List.mem_map.mpr
  refine ⟨⟨raw,answer⟩,recorded,?_⟩
  unfold allocation
  split
  · rename_i actual found
    have same := Option.some.inj (found.symm.trans recognized)
    cases same
    rfl
  · rename_i absent
    have impossible := recognized.symm.trans absent
    cases impossible

#print axioms execute_request
#print axioms execute_program
#print axioms recognized_recorded
end Whir.PCSBCSAtomicAllocationTrace
