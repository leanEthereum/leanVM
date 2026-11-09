/-
  LeanVM.Prover.Bus

  The executable bus phase (`Statement/Prover/Bus.lean`) makes the moves of the specification's
  honest bus phase `hBus`.
-/

module

public import LeanVM.Prover.BusLeaves
public import LeanVM.Prover.Gkr

/-!
# The bus phase

* `toList_pushLeaves`, `toList_pullLeaves`, `toList_countLeaves`: at the verifier's layout, the
  leaves filled into arrays from the columns (`ColsOk`) are the specification's honest leaves;
* `corr_busFast`: **the bus phase makes the moves of `hBus`**: the challenges, the GKR over the
  stored layers (`corr_gkrA`), and the framework values from the arrays (`mleK_col`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol (Column)

@[expose] public section

section Sides

variable {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)} {cols : Array (Array K)}

theorem layout_logMemory (prog : LeanIsaProgram) (s : Sizes) :
    (verifierLayout prog s).logMemory = s.logMem := rfl

theorem layout_logBytecode (prog : LeanIsaProgram) (s : Sizes) :
    (verifierLayout prog s).logBytecode = prog.logSize := rfl

theorem layout_bytecode (prog : LeanIsaProgram) (s : Sizes) :
    (verifierLayout prog s).bytecode = bytecodeWords prog := rfl

theorem getD_onesList_one (n y : ℕ) (hy : y < 2 ^ n) : (onesList n).getD y 0 = 1 := by
  rw [getD_onesList n y hy, ofK_one]

theorem getD_side_mem {l : List BusBlock} {b : ℕ} (hb : b < l.length) : l.getD b default ∈ l := by
  rw [List.getD_eq_getElem _ _ hb]
  exact List.getElem_mem hb

/-- The powers of `g` the framework blocks read. -/
abbrev powsOf (prog : LeanIsaProgram) (s : Sizes) : Array E :=
  powsA gen (2 ^ max (verifierLayout prog s).logMemory (verifierLayout prog s).logBytecode)

/-- **The push side's leaves** are the specification's. -/
theorem toList_pushLeaves (hcols : ColsOk prog s q cols) (alphas : List E) (β : E) :
    (stackA (sideLogs [0, (verifierLayout prog s).logMemory, (verifierLayout prog s).logBytecode]
        (verifierLayout prog s).push)
      (pushTabA cols (verifierLayout prog s) (powsOf prog s) β (eqKernel alphas))
      (busDepth prog s)).toList = pushLeaves prog s q alphas β := by
  rw [toList_stackA, pushLeaves]
  have hsz : sideLogs [0, (verifierLayout prog s).logMemory, (verifierLayout prog s).logBytecode]
      (verifierLayout prog s).push = sideSizes (fwLogs prog s) (pushBlocks s) := by
    rw [layout_push]; rfl
  rw [hsz]
  refine stackLeaves_congr _ fun b hb ↦ ?_
  match b, hb with
  | 0, _ => rfl
  | 1, _ =>
    show (memTabA cols (verifierLayout prog s).logMemory
      (powsA gen (2 ^ max (verifierLayout prog s).logMemory (verifierLayout prog s).logBytecode))
      β (eqKernel alphas)
      fun _ ↦ 1).toList = memTab prog s q β (eqKernel alphas) (onesList s.logMem)
    rw [layout_logMemory, layout_logBytecode]
    exact toList_memTabA hcols (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)) β _ _ _
      fun y hy ↦ (getD_onesList_one _ y hy).symm
  | 2, _ =>
    show (bcTabA (verifierLayout prog s).bytecode.toArray (verifierLayout prog s).logBytecode
      (powsA gen (2 ^ max (verifierLayout prog s).logMemory (verifierLayout prog s).logBytecode))
      β (eqKernel alphas)
      fun _ ↦ 1).toList = bcTab prog β (eqKernel alphas) (onesList prog.logSize)
    rw [layout_logMemory, layout_logBytecode, layout_bytecode]
    exact toList_bcTabA (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)) β _ _ _
      fun y hy ↦ (getD_onesList_one _ y hy).symm
  | b + 3, hb =>
    have hb' : b < (pushBlocks s).length := by simp [sideSizes, fwLogs] at hb; omega
    show (tableTabA cols β _ ((verifierLayout prog s).push.getD b default)).toList = _
    rw [layout_push]
    exact toList_tableTabA_owned hcols _ _ (pushBlocks_owned s _ (getD_side_mem hb'))

/-- **The pull side's leaves** are the specification's. -/
theorem toList_pullLeaves (hcols : ColsOk prog s q cols) (alphas : List E) (β : E) :
    (stackA (sideLogs [0, (verifierLayout prog s).logMemory, (verifierLayout prog s).logBytecode]
        (verifierLayout prog s).pull)
      (pullTabA cols (verifierLayout prog s) (powsOf prog s) β (eqKernel alphas))
      (busDepth prog s)).toList = pullLeaves prog s q alphas β := by
  rw [toList_stackA, pullLeaves]
  have hsz : sideLogs [0, (verifierLayout prog s).logMemory, (verifierLayout prog s).logBytecode]
      (verifierLayout prog s).pull = sideSizes (fwLogs prog s) (pullBlocks s) := by
    rw [layout_pull]; rfl
  rw [hsz]
  refine stackLeaves_congr _ fun b hb ↦ ?_
  match b, hb with
  | 0, _ =>
    show (stateTabA β (eqKernel alphas)
      (Protocol.Verifier.gpow (2 ^ (verifierLayout prog s).logBytecode - 1))).toList =
      stateTab β (eqKernel alphas) (Protocol.Verifier.gpow (2 ^ prog.logSize - 1))
    rw [layout_logBytecode]
    rfl
  | 1, _ =>
    show (memTabA cols (verifierLayout prog s).logMemory
      (powsA gen (2 ^ max (verifierLayout prog s).logMemory (verifierLayout prog s).logBytecode))
      β (eqKernel alphas)
      fun y ↦ ofK ((cols.getD memoryFinalCounters #[]).getD y 0)).toList =
      memTab prog s q β (eqKernel alphas) (colList prog s q (memCol 3))
    rw [layout_logMemory, layout_logBytecode]
    exact toList_memTabA hcols (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)) β _ _ _
      fun y hy ↦ by
      have h := cell_eq hcols (memCol 3) (y := y) hy
      rw [refCol_memCol] at h
      exact h
  | 2, _ =>
    show (bcTabA (verifierLayout prog s).bytecode.toArray (verifierLayout prog s).logBytecode
      (powsA gen (2 ^ max (verifierLayout prog s).logMemory (verifierLayout prog s).logBytecode))
      β (eqKernel alphas)
      fun y ↦ ofK ((cols.getD bytecodeFinalCounters #[]).getD y 0)).toList =
      bcTab prog β (eqKernel alphas) (colList prog s q bfcntCol)
    rw [layout_logMemory, layout_logBytecode, layout_bytecode]
    exact toList_bcTabA (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)) β _ _ _
      fun y hy ↦ by
      have h := cell_eq hcols bfcntCol (y := y) hy
      rw [refCol_bfcntCol] at h
      exact h
  | b + 3, hb =>
    have hb' : b < (pullBlocks s).length := by simp [sideSizes, fwLogs] at hb; omega
    show (tableTabA cols β _ ((verifierLayout prog s).pull.getD b default)).toList = _
    rw [layout_pull]
    exact toList_tableTabA_owned hcols _ _ (pullBlocks_owned s _ (getD_side_mem hb'))

/-- **The count side's leaves** are the specification's. -/
theorem toList_countLeaves (hcols : ColsOk prog s q cols) :
    (stackA (sideLogs [] (verifierLayout prog s).count) (countTabA cols (verifierLayout prog s))
      (busDepth prog s)).toList = countLeaves prog s q := by
  rw [toList_stackA, countLeaves]
  have hsz : sideLogs [] (verifierLayout prog s).count = sideSizes [] (countBlocks s) := by
    rw [layout_count]; rfl
  rw [hsz]
  refine stackLeaves_congr _ fun b hb ↦ ?_
  have hb' : b < (countBlocks s).length := by simpa [sideSizes] using hb
  show (tableTabA cols 0 [1] ((verifierLayout prog s).count.getD b default)).toList = _
  rw [layout_count]
  exact toList_tableTabA_owned hcols _ _ (countBlocks_owned s _ (getD_side_mem hb'))

end Sides

/-! ## The phase -/

/-- **The bus phase makes the moves of `hBus`**, from the instance's columns as arrays. -/
theorem corr_busFast {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {cols : Array (Array K)} (hcols : ColsOk prog s q cols) :
    Corr (fun _ _ ↦ True) (busFast (verifierLayout prog s) cols) (hBus prog s q) := by
  unfold busFast hBus
  refine Corr.bind_same _ fun alphas ↦ ?_
  unfold hBusK1
  refine Corr.bind_same _ fun beta ↦ ?_
  unfold hBusK2
  dsimp only
  rw [busLayout_depth_verifier]
  have hD : 0 < busDepth prog s := lt_of_lt_of_le s.logMem_pos (logMem_le_busDepth prog s)
  refine Corr.bind (fun g g' hg ↦ ?_) _ _
    (corr_gkrA hD (length_pushLeaves prog s q alphas beta) (length_pullLeaves prog s q alphas beta)
      (length_countLeaves prog s q)
      (fun k hk ↦ by rw [getD_treeLayers _ _ k hk, toList_pushLeaves hcols])
      (fun k hk ↦ by rw [getD_treeLayers _ _ k hk, toList_pullLeaves hcols])
      (fun k hk ↦ by rw [getD_treeLayers _ _ k hk, toList_countLeaves hcols]))
  obtain ⟨rfl, -, -⟩ := hg
  have hm : ∀ (i : Fin 4) (z : List E),
      mleK (cols.getD (i : ℕ) #[]) z = multilinearEval (colList prog s q (memCol i)) z :=
    fun i z ↦ by rw [← refCol_memCol]; exact mleK_col hcols _ z
  have h0 : ∀ z, mleK (cols.getD memory0 #[]) z =
      multilinearEval (colList prog s q (memCol 0)) z := hm 0
  have h1 : ∀ z, mleK (cols.getD memory1 #[]) z =
      multilinearEval (colList prog s q (memCol 1)) z := hm 1
  have h2 : ∀ z, mleK (cols.getD memory2 #[]) z =
      multilinearEval (colList prog s q (memCol 2)) z := hm 2
  have h3 : ∀ z, mleK (cols.getD memoryFinalCounters #[]) z =
      multilinearEval (colList prog s q (memCol 3)) z := hm 3
  have hb : ∀ z, mleK (cols.getD bytecodeFinalCounters #[]) z =
      multilinearEval (colList prog s q bfcntCol) z := fun z ↦ by
    rw [← refCol_bfcntCol]; exact mleK_col hcols _ z
  unfold hBusK3 memVals mfVal bfVal
  rw [h0, h1, h2, h3, hb, layout_logMemory, layout_logBytecode]
  refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ ?_
  exact ⟨rfl, trivial⟩

end
end LeanVM.Prover
