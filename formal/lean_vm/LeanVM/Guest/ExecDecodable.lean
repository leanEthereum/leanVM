/-
  LeanVM.Guest.ExecDecodable

  Every instruction of the guest program decodes: its operands are powers below `2^28`.
-/

module

public import LeanVM.Guest.Mode.InvCert

/-!
# The guest program decodes

`functions_offSmall`: every instruction of every guest function has its operands below `2^28`
(`offSmall`, one kernel check over the functions' data). The padding does too, so every slot of the
program does (`offSmall_instructionAtPc`), and every slot decodes (`guest_decodable`), as
`execute_complete` asks.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- **Every instruction of every guest function has its operands below `2^28`.** -/
theorem functions_offSmall : Data.functions.all (fun f ↦ f.chunks.all (·.all offSmall)) = true := by
  decide +kernel

theorem listElementOrDefault_of {α : Type} {p : α → Prop} {d : α} (hd : p d) :
    ∀ (l : List α) (n : ℕ), (∀ x ∈ l, p x) → p (listElementOrDefault l n d)
  | [], _, _ => hd
  | a :: _, 0, h => h a (List.mem_cons_self ..)
  | _ :: as, n + 1, h => listElementOrDefault_of hd as n fun x hx ↦ h x (List.mem_cons_of_mem _ hx)

theorem offSmall_instructionAt {f : CompiledFunction} (hf : f.chunks.all (·.all offSmall) = true)
    (i : ℕ) : offSmall (f.instructionAt i) = true := by
  unfold CompiledFunction.instructionAt
  refine listElementOrDefault_of (p := fun x ↦ offSmall x = true) (by decide) _ _ ?_
  refine listElementOrDefault_of (p := fun c ↦ ∀ x ∈ c, offSmall x = true) (fun _ h ↦ absurd h
    List.not_mem_nil) _ _ fun c hc ↦ ?_
  exact List.all_eq_true.mp (List.all_eq_true.mp hf c hc)

/-- **Every slot of a layout of such functions has its operands below `2^28`.** -/
theorem offSmall_instructionAtPc :
    ∀ (fns : List CompiledFunction), fns.all (fun f ↦ f.chunks.all (·.all offSmall)) = true →
      ∀ pc, offSmall (instructionAtPc fns pc) = true
  | [], _, _ => rfl
  | f :: fs, h, pc => by
    rw [List.all_cons, Bool.and_eq_true] at h
    unfold instructionAtPc
    split
    · exact offSmall_instructionAt h.1 _
    · exact offSmall_instructionAtPc fs h.2 pc

theorem isOff_of {a : ℕ} (h : a < 2 ^ 28) : IsOff (addressOfIndex a) := ⟨a, h, rfl⟩

/-- **An instruction whose operands are below `2^28` decodes.** -/
theorem decodable_of_offSmall {ins : OffsetInstruction} (h : offSmall ins = true) :
    Decodable ins.toLeanIsaInstruction := by
  cases ins with
  | xor a b c =>
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨isOff_of h.1.1, isOff_of h.1.2, isOff_of h.2⟩
  | mul a b c =>
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨isOff_of h.1.1, isOff_of h.1.2, isOff_of h.2⟩
  | set o k0 k1 =>
    simp only [offSmall, decide_eq_true_eq] at h
    exact isOff_of h
  | deref a b c mode =>
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨isOff_of h.1.1, isOff_of h.1.2, isOff_of h.2⟩
  | jump a b c =>
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨isOff_of h.1.1, isOff_of h.1.2, isOff_of h.2⟩
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    refine ⟨fun c ↦ ?_, isOff_of h.2⟩
    rw [keccakInOffset_gpow]
    refine isOff_of (h.1 _ ?_)
    rw [keccakIns]
    exact List.mem_map.mpr ⟨c.val, List.mem_range.mpr c.isLt, rfl⟩

/-- **Every instruction of the guest program decodes.** -/
theorem guest_decodable : ∀ i, Decodable (guestProgram.instructions i) := fun i ↦
  decodable_of_offSmall (offSmall_instructionAtPc _ functions_offSmall i.val)

end

end LeanVM.Guest.Mode
