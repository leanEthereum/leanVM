/-
  LeanVM.Guest.EndExecHintsG

  The hint bridge's premises at the deployed alignment (`Bridge.alignA`) that its data decides: the
  program's alignment, `main`'s entry, the layout, the advice and the hints' frame cells.
-/

module

public import LeanVM.Guest.EndExecH
public import LeanVM.Guest.EndExecC
public import LeanVM.Guest.EndExecY
public import LeanVM.Guest.Bridge.ProgAl
public import LeanVM.Guest.Bridge.CellsChk
public import LeanVM.Guest.Bridge.PairChk.AdvAll
public import LeanVM.Guest.Mode.HintsData
import all Statement.Data.Bytecode
import all Statement.Data.AdviceHints

/-!
# The bridge's premises at the deployed alignment

`HintHyps L D alignA`'s fields that read the deployed data alone, on any layout `L` with b2c's frame
sizes: `progAl_alignA` (`Bridge.progAl`), `mainAt_alignA` (`main` entered past the prologue),
`alLayout_alignA` (each function's entry and code the compiled function's), `advAl_alignA` (the
check's advice at each offset the executor's hints there: function `j`'s advice the advice's `j`-th,
`PairChk.advJ_all`, whose hints at its pcs are its own, `Mode.hintsAt_fns`) and `cellsAl_alignA` (the
hints' frame cells within the frame, `Bridge.cellsChk_all`). `hintHyps_alignA`: so `HintHyps L D alignA`
from the three fields that read the reference run, `JumpCellsAt`, `WitCells` and `CompRef`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Bridge
open LeanVM.Prover.Exec (Hint)

public section

theorem progAl_alignA : ProgAl guestProgram coreProgram alignA := progAl

/-- **The deployed alignment's code is the compiled function's.** -/
theorem code_alignA : ∀ f j, B2C.idxOf f = some j → (alignA f).code = (fnOf j).code := fun _ _ h ↦ by
  rw [alignA_of h]; rfl

/-- **`main` is entered past the prologue.** -/
theorem mainAt_alignA : entOf alignA "main" = proLen := alignA_main

/-- **The deployed alignment's layout**: each function's entry its compiled function's, its code
theirs. -/
theorem alLayout_alignA : AlLayout alignA := fun f _ hf ↦ by
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
  obtain ⟨i, rfl, -, -, -, -, -, -, -, h2⟩ := B2C.fn_of_idx hj
  have hm := B2C.fnOf_memC h2
  refine ⟨fnOf (i + 1), hm, ?_, ?_⟩
  · rw [entOf, alignA_of hj]; rfl
  · rw [alignA_of hj]
    exact (CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hm)).le

theorem lookup_getD_hintsAt (x : ℕ) : ∀ l : List (ℕ × List Hint), (l.lookup x).getD [] = Mode.hintsAt l x
  | [] => rfl
  | (k, v) :: l => by
    unfold Mode.hintsAt
    rw [List.lookup_cons, List.find?_cons]
    by_cases h : x = k
    · subst h; simp
    · rw [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]
      exact lookup_getD_hintsAt x l

/-- **The deployed alignment reads the executor's hints.** -/
theorem advAl_alignA : AdvAl alignA := by
  intro f fn hf off ins hins
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hok := progAl.ok f fn hf
  rw [alignA_of hj] at hins hok ⊢
  rw [alignOk, AlignCtx.seq_eq] at hok
  simp only [Bool.and_eq_true, Nat.beq_eq] at hok
  obtain ⟨hd, hlen⟩ := PairChk.advJ_all j h1 (by have : nFns = fn_count% := rfl; omega)
  have hcl : (fnOf j).code.length = (fnOf j).instructionCount :=
    CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem (B2C.fnOf_memC h2))
  have hoff : off < (fnOf j).code.length := (List.getElem?_eq_some_iff.mp hins).1
  show ((adviceOf j).2.2.lookup ((ctxOf j).entry + off)).getD [] = _
  have he : (adviceOf j).1 = (ctxOf j).entry := hok.1.1.1.2
  rw [lookup_getD_hintsAt, Mode.adviceHints_eq]
  exact (Mode.hintsAt_fns (d := adviceOf j) Mode.adviceFns_ok (List.mem_of_getElem? hd) (by omega)
    (by omega)).symm

theorem mem_of_lookup_hints {β : Type} : ∀ {l : List (ℕ × β)} {o : ℕ} {c : β}, l.lookup o = some c → (o, c) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | ⟨k, b⟩ :: l, o, c, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      cases h
      have : o = k := by simpa using he
      rw [this]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup_hints h)

/-- **Each function's hints write their frame cells within its frame**, on a layout with b2c's
frame sizes. -/
theorem cellsAl_alignA {L : Lay} (hfs : L.fs = B2C.fs) : CellsAl L alignA := by
  intro f fn hf pc h hh
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
  obtain ⟨-, -, -, -, -, -, hfsj, -, -, h2⟩ := B2C.fn_of_idx hj
  rw [alignA_of hj] at hh
  rw [hfs, hfsj]
  have hc := cellsChk_all j h2
  unfold cellsChk at hc
  cases hl : (fnAl j).d.2.2.lookup pc with
  | none => rw [hl] at hh; cases hh
  | some l =>
    rw [hl, Option.getD_some] at hh
    exact List.all_eq_true.mp (List.all_eq_true.mp hc _ (mem_of_lookup_hints hl)) h hh

/-- **The bridge's premises at the deployed alignment**, from the three that read the reference
run. -/
theorem hintHyps_alignA {L : Lay} {D : Ref → RefD} (hfs : L.fs = B2C.fs) (hJ : JumpCellsAt L D alignA)
    (hW : WitCells L D alignA) (hC : CompRef L D alignA) : HintHyps L D alignA :=
  ⟨progAl_alignA, mainAt_alignA, hJ, alLayout_alignA, advAl_alignA, hW, hC, cellsAl_alignA hfs⟩

end

end LeanVM.Guest.EndExec
