/-
  LeanVM.Guest.EndExecCAlign

  `ExecGaps.hintComputed` on the deployed alignment: its advice the executor's, its computed hints passing the data check, by the generated checks.
-/

module

public import LeanVM.Guest.EndExecC
public import LeanVM.Guest.EndExecCDeref
public import LeanVM.Guest.EndExecJumpCells
public import LeanVM.Guest.Bridge.ProgAl
public import LeanVM.Guest.Bridge.PairChk.All
public import LeanVM.Guest.Mode.HintsData
public import LeanVM.Guest.Bridge.JumpCellsPack

/-!
# The computed hints on the deployed alignment

`hintsAl_alignA`: each function's alignment reads its advice `adviceOf j`, entry `j` of `Data.adviceFns` from its entry over its code's length (`Bridge.PairJ`), whose hints at its pcs are the advice's (`Mode.hintsAt_fns`). `pairOk_alignA`: every function's computed hints pass the data check (`Bridge.PairChk.pairJ_all`). `hintComputed_alignA`: so `ExecGaps.hintComputed` holds on the deployed guest for every `Y`, given the reference holding the hint-only cells' values (`ExtraRef`). `ExecGaps.ofXC`: `ExecGaps.ofX` on the deployed alignment, with `hintComputed` so discharged and `DerefPow` from the reference step (`derefPow_all`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (alignA alignA_of ctxOf adviceOf fnAl)
open LeanVM.Prover.Exec

public section

theorem hintsAt_eq_lookup (x : ℕ) : ∀ (l : List (ℕ × List Prover.Exec.Hint)), Mode.hintsAt l x = (l.lookup x).getD []
  | [] => rfl
  | (k, v) :: l => by
    have ih := hintsAt_eq_lookup x l
    unfold Mode.hintsAt at ih ⊢
    rw [List.find?_cons, List.lookup_cons]
    by_cases hk : k = x
    · subst hk; simp
    · rw [show (k == x) = false from beq_false_of_ne hk, show (x == k) = false from beq_false_of_ne (Ne.symm hk)]
      exact ih

theorem pairJ_of_find {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) :
    ∃ j, B2C.idxOf f = some j ∧ alignA f = fnAl j ∧ Bridge.PairJ j ∧ (coreOf j).body = fn.body ∧ j < nFns := by
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
  obtain ⟨i, -, hi, -, hfi, hc, -, -, h1, h2⟩ := B2C.fn_of_idx hj
  refine ⟨j, hj, alignA_of hj, Bridge.PairChk.pairJ_all j h1 (by have : nFns = 1602 := rfl; omega), ?_, h2⟩
  rw [hc, ← Option.some.inj (hfi.symm.trans hf)]

/-- **The deployed guest's computed hints pass the data check.** -/
theorem pairOk_alignA : PairOk alignA := fun f fn j hf hj ↦ by
  obtain ⟨j', hj', hA, hP, hb, -⟩ := pairJ_of_find hf
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  have hok := Bridge.progAl.ok f fn hf
  rw [hA] at hok ⊢
  change (ctxOf _).seq (fun X ↦ X.locOk && _ && _ && _ && _) = true at hok
  rw [Bridge.AlignCtx.seq_eq] at hok
  simp only [Bool.and_eq_true] at hok
  rw [← hb]
  exact ⟨hP.1, fun i hx hi ↦ Bridge.locAt_ofData hok.1.1.1.1 hx hi⟩

/-- **The deployed alignment reads the advice's hints.** -/
theorem hintsAl_alignA : HintsAl alignA := fun f fn hf off hoff ↦ by
  obtain ⟨j, -, hA, ⟨-, ha, hl⟩, -, hj⟩ := pairJ_of_find hf
  have hok := Bridge.progAl.ok f fn hf
  rw [hA] at hok hoff ⊢
  change (ctxOf j).seq (fun X ↦ X.locOk && Nat.beq (adviceOf j).1 X.entry && _ && _ && _) = true at hok
  rw [Bridge.AlignCtx.seq_eq] at hok
  simp only [Bool.and_eq_true, Nat.beq_eq] at hok
  have he : (adviceOf j).1 = (ctxOf j).entry := hok.1.1.1.2
  have hlen : (fnOf j).code.length = (fnOf j).instructionCount :=
    CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem (B2C.fnOf_memC hj))
  change off < (fnOf j).code.length at hoff
  change Mode.hintsAt Data.adviceHints ((ctxOf j).entry + off) = (((adviceOf j).2.2.lookup ((ctxOf j).entry + off)).getD [])
  rw [Mode.adviceHints_eq, Mode.hintsAt_fns Mode.adviceFns_ok (List.mem_of_getElem? ha) (by omega) (by omega),
    hintsAt_eq_lookup]

/-- **`ExecGaps.hintComputed` on the deployed guest**, for every `Y`, given the reference holding
the hint-only cells' values. -/
theorem hintComputed_alignA {Y : Ref → St → Prop} (hXR : ExtraRef alignA) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun (XOf Y) r s →
      h ∈ (C.hints[s.pc]?).getD [] → isAllocHint h = false → isWitnessHint h = false → ∀ s1,
      Moves (refMem r.img) s s1 → Mode.HintIn s1 h → HintOk C (refMem r.img) s1 h :=
  hintComputed_X Bridge.progAl Bridge.alignA_main jumpCells_at alLayout_alignA hintsAl_alignA pairOk_alignA
    hXR

/-- **`ExecGaps` on the deployed alignment**: `ExecGaps.ofX` with the alignment's premises proved,
`hintComputed` from the hint-only cells' values on the reference, and
`DerefPow` from the reference step. -/
theorem ExecGaps.ofXC {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {Y : Ref → St → Prop}
    (certs : ModeCerts Ks Km E0) (main : MainOk Km E0) (mainExact : Budget.MainExactHyp)
    (hintAlloc : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isAllocHint h = true → Mode.HintIn s1 h → HintOk C (refMem r.img) s1 h)
    (hintWitness : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isWitnessHint h = true → Mode.HintIn s1 h → HintOk C (refMem r.img) s1 h)
    (res : ∀ r, r.Ok → Mode.ResRef guestProgram r.img r.n Ks (XOf Y r)) (termInst : TermInst Ks)
    (entries : ∀ K ∈ Ks, K.F.entry ≠ 0) (extraRef : ExtraRef alignA)
    (hintsUsed : HintsUsed Y) (keepY : KeepY Y) (initY : InitY Y) :
    ExecGaps Ks Km E0 (XOf Y) (fun _ ↦ ProAt) :=
  ExecGaps.ofX certs main mainExact hintAlloc hintWitness (hintComputed_alignA extraRef) res termInst
    Bridge.progAl Bridge.alignA_main alLayout_alignA jumpCells_at entries (derefPow_all Y)
    hintsUsed keepY initY

end

end LeanVM.Guest.EndExec
