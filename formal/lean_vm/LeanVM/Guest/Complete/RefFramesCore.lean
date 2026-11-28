/-
  LeanVM.Guest.Complete.RefFramesCore

  `refFrames_of`'s data facts on the deployed guest: a loop helper's last call is to itself, its
  aligned frames a multiple of the window, and a function whose code holds a `KECCAK` aligned.
-/

module

public import LeanVM.Guest.Complete.RefFrames
public import LeanVM.Guest.B2C.RunsFit
public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.Memory.GuestWordsA
public import LeanVM.Guest.Memory.GuestIdx
import all Statement.Data.Bytecode

/-!
# The reference run's frames on the deployed guest

At the budget's flags `alW` (`Data.walJ` by core index, the flags the frame hints carry, `frAl_of`):
* `lastSelf_core`: a loop helper's last call is its closing call to itself, since each function
  returns only at its end (`B2C.lastBody`, from B2's completeness checks);
* `loopFsAl_core`: an aligned loop helper's frame is a multiple of `16` words (`loopFsChk`, one
  kernel check over the core program, as the compiler asserts);
* `kecAl_core`: at an alignment whose code is the compiled functions' (`AShape`'s first half), a
  function whose code holds a `KECCAK` is aligned (`kecChk`, one kernel check over the compiled
  functions, in chunks).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge hiding St

@[expose] public section

theorem name_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : fn.name = f := by
  have h' : List.find? (fun g : Fn ↦ g.name == f) coreProgram = some fn := h
  exact beq_iff_eq.mp (List.find?_some (p := fun g : Fn ↦ g.name == f) h')

/-- **A loop helper's last call is to itself**, on the deployed guest. -/
theorem lastSelf_core : LastSelf coreProgram := by
  intro f fn σ es vs hf hl hw c hc
  obtain ⟨j, hj, hcj, -, -⟩ := B2C.idx_of_find hf
  obtain ⟨i, rfl, -, -, -, -, -, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hlb := B2C.lastBody (B2C.Cplw.cplOk_all _ h1 h2) (End.winOk_of h1 h2)
  rw [hcj] at hlb
  rw [B2C.lastCall_of hw hl hlb c hc, name_of_find hf]

/-- Core function `i`: a loop helper allocated aligned has a frame of a multiple of `16` words. -/
noncomputable def loopFsI (i : ℕ) : Bool :=
  match coreProgram[i]? with
  | some fn => !fn.loop || !Data.walJ i || B2C.fsN (i + 1) % 16 == 0
  | none => true

theorem loopFs_ok : (List.range coreProgram.length).all loopFsI = true := by decide +kernel

/-- **An aligned loop helper's frame is a multiple of the window**, on the deployed guest. -/
theorem loopFsAl_core : LoopFsAl coreProgram B2C.fs alW := by
  intro f hl ha
  obtain ⟨fn, hf⟩ : ∃ fn, coreProgram.find? f = some fn := by
    unfold Program.loop at hl
    split at hl
    · exact ⟨_, ‹_›⟩
    · cases hl
  have hl' : fn.loop = true := by rw [← Program.loop_of_find? hf]; exact hl
  obtain ⟨j, hj, hcj, hfs, -⟩ := B2C.idx_of_find hf
  obtain ⟨i, rfl, hi, hn, -, hc, -, -, -, -⟩ := B2C.fn_of_idx hj
  have hfn : fn = coreProgram[i] := hcj.symm.trans hc
  have hidx : coreIdx f = i := hn ▸ coreIdx_getElem hi
  have hchk := List.all_eq_true.mp loopFs_ok i (List.mem_range.mpr hi)
  unfold alW at ha
  rw [hidx] at ha
  unfold loopFsI at hchk
  rw [List.getElem?_eq_getElem hi, ← hfn] at hchk
  simp only [hl', ha, Bool.not_true, Bool.false_or, beq_iff_eq] at hchk
  rw [hfs]
  exact hchk

/-- A `KECCAK`. -/
def isKec : OffsetInstruction → Bool
  | .keccak .. => true
  | _ => false

theorem isKec_of {ins : OffsetInstruction} (h : ins.toLeanIsaInstruction.opcode = Opcode.keccak) :
    isKec ins = true := by
  cases ins <;> simp_all [OffsetInstruction.toLeanIsaInstruction, LeanIsaInstruction.opcode, isKec]

/-- Core function `i` (compiled function `i + 1`): allocated aligned when its code holds a
`KECCAK`. -/
noncomputable def kecI (i : ℕ) : Bool := !((fnOf (i + 1)).code.any isKec) || Data.walJ i

theorem kec_ok0 : (List.range' 0 400).all kecI = true := by decide +kernel
theorem kec_ok1 : (List.range' 400 400).all kecI = true := by decide +kernel
theorem kec_ok2 : (List.range' 800 400).all kecI = true := by decide +kernel
theorem kec_ok3 : (List.range' 1200 400).all kecI = true := by decide +kernel
theorem kec_len : coreProgram.length ≤ 1600 := by rw [coreProgram_length]; decide

theorem kec_ok {i : ℕ} (hi : i < coreProgram.length) : kecI i = true := by
  have := kec_len
  have hm : ∀ a, a ≤ i → i < a + 400 → (List.range' a 400).all kecI = true → kecI i = true :=
    fun a h1 h2 h ↦ List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨h1, h2⟩)
  rcases Nat.lt_or_ge i 400 with h | h
  · exact hm 0 (by omega) (by omega) kec_ok0
  rcases Nat.lt_or_ge i 800 with h' | h'
  · exact hm 400 h (by omega) kec_ok1
  rcases Nat.lt_or_ge i 1200 with h'' | h''
  · exact hm 800 h' (by omega) kec_ok2
  · exact hm 1200 h'' (by omega) kec_ok3

/-- **A function whose code holds a `KECCAK` is aligned**, at an alignment whose code is the
compiled functions'. -/
theorem kecAl_core {A : String → FnAl} (hA : ∀ f j, B2C.idxOf f = some j → (A f).code = (fnOf j).code) :
    KecAl alW A := by
  intro f fn hf off ins hins hop
  obtain ⟨j, hj, -, -, -⟩ := B2C.idx_of_find hf
  obtain ⟨i, rfl, hi, hn, -, -, -, -, -, -⟩ := B2C.fn_of_idx hj
  have hk := kec_ok hi
  unfold kecI at hk
  rw [hA f _ hj] at hins
  have hany : (fnOf (i + 1)).code.any isKec = true :=
    List.any_eq_true.mpr ⟨ins, List.mem_of_getElem? hins, isKec_of hop⟩
  rw [hany, Bool.not_true, Bool.false_or] at hk
  have hidx : coreIdx f = i := hn ▸ coreIdx_getElem hi
  unfold alW
  rw [hidx]
  exact hk

/-- **The reference run's frames on the deployed guest**, at the budget's flags: from the program's
alignments, `main`'s entry, the jump cells and an alignment whose code is the compiled functions'. -/
theorem refFrames_core {D : Ref → RefD} {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = proLen) (hJ : JumpCellsV ⟨B2C.fs, alW, B2C.H, B2C.C, B2C.cert⟩ D A)
    (hA : ∀ f j, B2C.idxOf f = some j → (A f).code = (fnOf j).code) :
    ∀ r, RefH ⟨B2C.fs, alW, B2C.H, B2C.C, B2C.cert⟩ (D r) r → ValidExecution guestProgram r.input r.exec →
      FramesIn guestProgram r.img r.n ∧ Mode.KeccakFramesAligned guestProgram r.img r.n :=
  refFrames_of hP hmain hJ (kecAl_core hA) lastSelf_core loopFsAl_core

end

end LeanVM.Guest.EndExec
