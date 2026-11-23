/-
  LeanVM.Guest.ExecDecodable

  Every instruction of the guest program decodes: its operands are powers below `2^28`.
-/

module

public import LeanVM.Guest.Mode.InvCert
import all Statement.Data.Bytecode

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

private theorem all_drop_step {α : Type} {p : α → Bool} {l : List α} {n k : ℕ}
    (hc : ((l.drop (n * k)).take n).all p = true) (ht : (l.drop (n * (k + 1))).all p = true) :
    (l.drop (n * k)).all p = true := by
  rw [← List.take_append_drop n (l.drop (n * k)), List.all_append, hc, List.drop_drop, Bool.true_and]
  rwa [Nat.mul_succ] at ht

/-- A function's instructions have their operands below `2^28`. -/
def fnOffSmall (f : CompiledFunction) : Bool := f.chunks.all (·.all offSmall)

private theorem offSmall0 : ((Data.functions.drop (200 * 0)).take 200).all fnOffSmall = true := by
  decide +kernel

private theorem offSmall1 : ((Data.functions.drop (200 * 1)).take 200).all fnOffSmall = true := by
  decide +kernel

private theorem offSmall2 : ((Data.functions.drop (200 * 2)).take 200).all fnOffSmall = true := by
  decide +kernel

private theorem offSmall3 : ((Data.functions.drop (200 * 3)).take 200).all fnOffSmall = true := by
  decide +kernel

private theorem offSmall4 : ((Data.functions.drop (200 * 4)).take 200).all fnOffSmall = true := by
  decide +kernel

private theorem offSmall5 : ((Data.functions.drop (200 * 5)).take 200).all fnOffSmall = true := by
  decide +kernel

private theorem offSmall6 : ((Data.functions.drop (200 * 6)).take 200).all fnOffSmall = true := by
  decide +kernel

private theorem offSmall7 : ((Data.functions.drop (200 * 7)).take 200).all fnOffSmall = true := by
  decide +kernel

private theorem offSmall8 : (Data.functions.drop (200 * 8)).all fnOffSmall = true := by
  decide +kernel

/-- **Every instruction of every guest function has its operands below `2^28`**, 200 functions at a time. -/
theorem functions_offSmall : Data.functions.all (fun f ↦ f.chunks.all (·.all offSmall)) = true :=
  all_drop_step (k := 0) offSmall0 <|
    all_drop_step offSmall1 <|
    all_drop_step offSmall2 <|
    all_drop_step offSmall3 <|
    all_drop_step offSmall4 <|
    all_drop_step offSmall5 <|
    all_drop_step offSmall6 <|
    all_drop_step offSmall7 <|
    offSmall8

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
