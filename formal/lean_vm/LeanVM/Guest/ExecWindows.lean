module

public import LeanVM.Guest.ExecDecodable
public import Statement.LeanVm
import all Statement.Data.Bytecode

/-!
# The guest's `KECCAK`s have their blocks in windows, at aligned frames

`functions_kecOk`: every `KECCAK` of every guest function has its `tail`, its `cap` and the output
cells it writes each in one window of `keccakWindow = 16` cells counted from the frame's start
(`kecOk`, one kernel check over the functions' data): the compiler's aligned layout. So on a run
whose frames at its `KECCAK`s are aligned, multiples of the window below `2^κ`
(`KeccakFramesAligned`), every `KECCAK` has its blocks in windows (`guest_windows`), as
`Execution.KeccakBlocksInWindows` asks.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

private theorem all_drop_step' {α : Type} {p : α → Bool} {l : List α} {n k : ℕ}
    (hc : ((l.drop (n * k)).take n).all p = true) (ht : (l.drop (n * (k + 1))).all p = true) :
    (l.drop (n * k)).all p = true := by
  rw [← List.take_append_drop n (l.drop (n * k)), List.all_append, hc, List.drop_drop, Bool.true_and]
  rwa [Nat.mul_succ] at ht

/-- A `KECCAK`'s `tail`, `cap` and written outputs each lie in one window of `keccakWindow` cells
from the frame's start; any other instruction, trivially. -/
def kecOk : OffsetInstruction → Bool
  | .keccak _ _ _ _ tail _ cap out _ _ outCells =>
    decide (tail % keccakWindow + 4 ≤ keccakWindow) && decide (cap % keccakWindow + 4 ≤ keccakWindow) &&
      decide (out % keccakWindow + outCells.cellCount ≤ keccakWindow)
  | _ => true

/-- A function's `KECCAK`s have their blocks in windows from the frame's start. -/
def fnKecOk (f : CompiledFunction) : Bool := f.chunks.all (·.all kecOk)

private theorem kecOk0 : ((Data.functions.drop (200 * 0)).take 200).all fnKecOk = true := by
  decide +kernel

private theorem kecOk1 : ((Data.functions.drop (200 * 1)).take 200).all fnKecOk = true := by
  decide +kernel

private theorem kecOk2 : ((Data.functions.drop (200 * 2)).take 200).all fnKecOk = true := by
  decide +kernel

private theorem kecOk3 : ((Data.functions.drop (200 * 3)).take 200).all fnKecOk = true := by
  decide +kernel

private theorem kecOk4 : ((Data.functions.drop (200 * 4)).take 200).all fnKecOk = true := by
  decide +kernel

private theorem kecOk5 : ((Data.functions.drop (200 * 5)).take 200).all fnKecOk = true := by
  decide +kernel

private theorem kecOk6 : ((Data.functions.drop (200 * 6)).take 200).all fnKecOk = true := by
  decide +kernel

private theorem kecOk7 : ((Data.functions.drop (200 * 7)).take 200).all fnKecOk = true := by
  decide +kernel

private theorem kecOk8 : (Data.functions.drop (200 * 8)).all fnKecOk = true := by
  decide +kernel

/-- **Every `KECCAK` of every guest function has its blocks in windows from its frame's start**,
200 functions at a time. -/
theorem functions_kecOk : Data.functions.all fnKecOk = true :=
  all_drop_step' (k := 0) kecOk0 <|
    all_drop_step' kecOk1 <|
    all_drop_step' kecOk2 <|
    all_drop_step' kecOk3 <|
    all_drop_step' kecOk4 <|
    all_drop_step' kecOk5 <|
    all_drop_step' kecOk6 <|
    all_drop_step' kecOk7 <|
    kecOk8

theorem kecOk_instructionAt {f : CompiledFunction} (hf : fnKecOk f = true) (i : ℕ) :
    kecOk (f.instructionAt i) = true := by
  unfold CompiledFunction.instructionAt
  refine listElementOrDefault_of (p := fun x ↦ kecOk x = true) (by decide) _ _ ?_
  refine listElementOrDefault_of (p := fun c ↦ ∀ x ∈ c, kecOk x = true) (fun _ h ↦ absurd h
    List.not_mem_nil) _ _ fun c hc ↦ ?_
  exact List.all_eq_true.mp (List.all_eq_true.mp hf c hc)

/-- **Every slot of a layout of such functions has its blocks in windows.** -/
theorem kecOk_instructionAtPc :
    ∀ (fns : List CompiledFunction), fns.all fnKecOk = true → ∀ pc, kecOk (instructionAtPc fns pc) = true
  | [], _, _ => rfl
  | f :: fs, h, pc => by
    rw [List.all_cons, Bool.and_eq_true] at h
    unfold instructionAtPc
    split
    · exact kecOk_instructionAt h.1 _
    · exact kecOk_instructionAtPc fs h.2 pc

/-! ## On a run -/

/-- **The run's frames at its `KECCAK`s are aligned**: at every state of the first `n` steps whose
instruction is a `KECCAK`, the frame is `g^j`, `j` below `2^κ` and a multiple of the window. -/
def KeccakFramesAligned (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (n : ℕ) : Prop :=
  ∀ k < n, ∀ rg, run prog img k Registers.initial = some rg → ∀ ins, prog.fetch rg.pc = some ins →
    ins.opcode = .keccak → ∃ j < 2 ^ κ, rg.fp = g ^ j ∧ j % keccakWindow = 0

/-- A block at offset `t` of an aligned frame `g^j`, in one window from the frame's start, is in one
window. -/
theorem inKeccakWindow_aligned {κ j t c : ℕ} (hκ : κ ≤ 28) (hj : j < 2 ^ κ)
    (hj16 : j % keccakWindow = 0) (ht : t < 2 ^ 28) (hw : t % keccakWindow + c ≤ keccakWindow) :
    InKeccakWindow κ (g ^ j * addressOfIndex t) c := by
  intro i hi
  rw [Option.mem_def, gLog?_spec (by omega), ← pow_add] at hi
  have hi' : (i : ℕ) < 2 ^ 64 - 1 := by
    have := i.isLt
    have : 2 ^ κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
    omega
  have hj' : j < 2 ^ 28 := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hκ)
  have hm : j + t < 2 ^ 64 - 1 := by omega
  have := gpow_injOn hm hi' hi
  rw [← this]
  unfold keccakWindow at *
  omega

/-- A guest slot at an aligned frame has its blocks in windows. -/
theorem windowsAt_guest {κ j : ℕ} (hκ : κ ≤ 28) (hj : j < 2 ^ κ) (hj16 : j % keccakWindow = 0)
    (i : Fin (2 ^ guestProgram.logSize)) :
    KeccakBlocksInWindowsAt κ (g ^ j) (guestProgram.instructions i) := by
  have hs := offSmall_instructionAtPc _ functions_offSmall i.val
  have hk := kecOk_instructionAtPc _ functions_kecOk i.val
  show KeccakBlocksInWindowsAt κ (g ^ j) (instructionAtPc Data.functions i.val).toLeanIsaInstruction
  generalize instructionAtPc Data.functions i.val = x at hs hk
  cases x with
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    simp only [offSmall, kecOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs hk
    have hm : ∀ c ∈ keccakIns m0 m1 m2 m3 tail b8 cap, c < 2 ^ 28 := hs.1
    have htl : tail < 2 ^ 28 := hm _ (List.mem_map.mpr ⟨4, List.mem_range.mpr (by decide),
      by simp [keccakInOff]⟩)
    have hcp : cap < 2 ^ 28 := hm _ (List.mem_map.mpr ⟨9, List.mem_range.mpr (by decide),
      by simp [keccakInOff]⟩)
    exact ⟨inKeccakWindow_aligned hκ hj hj16 htl hk.1.1, inKeccakWindow_aligned hκ hj hj16 hcp hk.1.2,
      inKeccakWindow_aligned hκ hj hj16 hs.2 hk.2⟩
  | _ => trivial

/-- Every `KECCAK` of a run that goes `n` steps has its blocks in windows when each one's does at its
state. -/
theorem windowsInRun_of {κ : ℕ} {prog : LeanIsaProgram} {M : MemoryImage κ} :
    ∀ (n : ℕ) (r : Registers K), (run prog M n r).isSome →
      (∀ k < n, ∀ rg, run prog M k r = some rg → ∀ ins, prog.fetch rg.pc = some ins →
        KeccakBlocksInWindowsAt κ rg.fp ins) →
      keccakBlocksInWindowsInRun prog M n r
  | 0, _, _, _ => trivial
  | n + 1, r, hrun, H => by
    rw [run_succ] at hrun
    split_ifs at hrun with hf
    · cases hrun
    rw [Option.bind_eq_bind, Option.isSome_bind] at hrun
    cases hs : step prog M r with
    | none => rw [hs] at hrun; cases hrun
    | some r1 =>
      rw [hs, Option.any_some] at hrun
      cases hfi : prog.fetch r.pc with
      | none => simp only [keccakBlocksInWindowsInRun, hs, hfi]
      | some ins =>
        simp only [keccakBlocksInWindowsInRun, hs, hfi]
        exact ⟨H 0 (by omega) r rfl ins hfi, windowsInRun_of n r1 hrun fun k hk rg hk' ↦
          H (k + 1) (by omega) rg (by rw [run_succ_of_ne_final hf, hs]; exact hk')⟩

/-- **The guest's `KECCAK`s have their blocks in windows** on a run of `n` steps whose frames at its
`KECCAK`s are aligned. -/
theorem guest_windows {κ n : ℕ} {img : MemoryImage κ} (hκ : κ ≤ 28)
    (hrun : (run guestProgram img n Registers.initial).isSome)
    (hal : KeccakFramesAligned guestProgram img n) :
    (⟨κ, img, n⟩ : Execution guestProgram).KeccakBlocksInWindows := by
  refine windowsInRun_of n _ hrun fun k hk rg hrg ins hins ↦ ?_
  have hins' := hins
  unfold LeanIsaProgram.fetch at hins
  obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.mp hins
  by_cases ho : (guestProgram.instructions i).opcode = .keccak
  · obtain ⟨j, hj, hfp, hj16⟩ := hal k hk rg hrg _ hins' ho
    rw [hfp]
    exact windowsAt_guest hκ hj hj16 i
  · generalize guestProgram.instructions i = x at ho ⊢
    cases x <;> first | exact absurd rfl ho | exact True.intro

end

end LeanVM.Guest.Mode
