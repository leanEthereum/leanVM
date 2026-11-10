/-
  LeanVM.Prover.Bus

  The executable bus phase (`Statement/Prover/Bus.lean`) makes the moves of the specification's
  honest bus phase `hBus`.
-/

module

public import LeanVM.Prover.BusLeaves
public import LeanVM.Prover.Gkr
public import LeanVM.Prover.Ring

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
      (pushTabA cols (verifierLayout prog s) (powsOf prog s) β alphas)
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
      β alphas
      fun _ ↦ 1).toList = memTab prog s q β alphas (onesList s.logMem)
    rw [layout_logMemory, layout_logBytecode]
    exact toList_memTabA hcols (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)) β _ _ _
      fun y hy ↦ (getD_onesList_one _ y hy).symm
  | 2, _ =>
    show (bcTabA (verifierLayout prog s).bytecode.toArray (verifierLayout prog s).logBytecode
      (powsA gen (2 ^ max (verifierLayout prog s).logMemory (verifierLayout prog s).logBytecode))
      β alphas
      fun _ ↦ 1).toList = bcTab prog β alphas (onesList prog.logSize)
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
      (pullTabA cols (verifierLayout prog s) (powsOf prog s) β alphas)
      (busDepth prog s)).toList = pullLeaves prog s q alphas β := by
  rw [toList_stackA, pullLeaves]
  have hsz : sideLogs [0, (verifierLayout prog s).logMemory, (verifierLayout prog s).logBytecode]
      (verifierLayout prog s).pull = sideSizes (fwLogs prog s) (pullBlocks s) := by
    rw [layout_pull]; rfl
  rw [hsz]
  refine stackLeaves_congr _ fun b hb ↦ ?_
  match b, hb with
  | 0, _ =>
    show (stateTabA β alphas
      (Protocol.Verifier.gpow (2 ^ (verifierLayout prog s).logBytecode - 1))).toList =
      stateTab β alphas (Protocol.Verifier.gpow (2 ^ prog.logSize - 1))
    rw [layout_logBytecode]
    rfl
  | 1, _ =>
    show (memTabA cols (verifierLayout prog s).logMemory
      (powsA gen (2 ^ max (verifierLayout prog s).logMemory (verifierLayout prog s).logBytecode))
      β alphas
      fun y ↦ ofK ((cols.getD memoryFinalCounters #[]).getD y 0)).toList =
      memTab prog s q β alphas (colList prog s q (memCol 2))
    rw [layout_logMemory, layout_logBytecode]
    exact toList_memTabA hcols (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)) β _ _ _
      fun y hy ↦ by
      have h := cell_eq hcols (memCol 2) (y := y) hy
      rw [refCol_memCol] at h
      exact h
  | 2, _ =>
    show (bcTabA (verifierLayout prog s).bytecode.toArray (verifierLayout prog s).logBytecode
      (powsA gen (2 ^ max (verifierLayout prog s).logMemory (verifierLayout prog s).logBytecode))
      β alphas
      fun y ↦ ofK ((cols.getD bytecodeFinalCounters #[]).getD y 0)).toList =
      bcTab prog β alphas (colList prog s q bfcntCol)
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

/-! ## The bytecode's share -/

section Share

variable (prog : LeanIsaProgram)

/-- The stacked bytecode's slots, computed, are the specification's `slotList`. -/
theorem toList_bytecodeSlotsA (z : List E) (hz : z.length = prog.logSize) :
    (bytecodeSlotsA (bytecodeWords prog).toArray prog.logSize z).toList = slotList prog z := by
  apply List.ext_getElem (by simp [bytecodeSlotsA, length_slotList, busBits])
  intro x h1 h2
  have hx : x < 16 := by simpa [length_slotList] using h2
  rw [← List.getD_eq_getElem _ (0 : E) h2, getD_slotList prog z hx]
  simp only [bytecodeSlotsA, Array.getElem_toList, Array.getElem_ofFn, mleK_eq]
  have hb : (bytecodeWords prog).length = 2 ^ prog.logSize * 16 := by
    rw [length_bytecodeWords, pow_add]; rfl
  have hlen : ((bytecodeWords prog).toArray.extract (x * 2 ^ prog.logSize)
      ((x + 1) * 2 ^ prog.logSize)).toList.length = 2 ^ prog.logSize := by
    have : (x + 1) * 2 ^ prog.logSize ≤ 2 ^ prog.logSize * 16 := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have h3 : x * 2 ^ prog.logSize + 2 ^ prog.logSize ≤ 2 ^ prog.logSize * 16 := by
      nlinarith
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.length_take, List.length_drop,
      hb, add_mul, one_mul, Nat.add_sub_cancel_left]
    omega
  rw [multilinearEval_eq_sum prog.logSize _ z (by rw [List.length_map, hlen]) hz, bcSlot]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have hy' := Finset.mem_range.mp hy
  congr 1
  have hlt : x * 2 ^ prog.logSize + y < (bytecodeWords prog).length := by
    rw [hb]; nlinarith
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.toList_extract, List.extract_eq_take_drop, List.getElem?_take,
    ite_eq_left (show y < (x + 1) * 2 ^ prog.logSize - x * 2 ^ prog.logSize by
      rw [add_mul, one_mul, Nat.add_sub_cancel_left]; exact hy'),
    List.getElem?_drop, List.toList_toArray,
    show y + 2 ^ prog.logSize * x = x * 2 ^ prog.logSize + y by ring]

/-- The state of the share's sumcheck after the challenges `pre`: both tables folded at them. -/
def ShareInv (w z pre : List E) (st : Array E × Array E) : Prop :=
  st.1.toList = foldAll w pre ∧ st.2.toList = foldAll (slotList prog z) pre

theorem polyEval_three (c0 c1 c2 x : E) : polyEval [c0, c1, c2] x = c0 + x * c1 + x * x * c2 := by
  simp only [polyEval, List.foldr]; ring

theorem sumE_map_range (n : ℕ) (F : ℕ → E) : sumE ((List.range n).map F) = ∑ i ∈ Finset.range n, F i := by
  rw [sumE_eq, sum_range_eq_list]

/-- **The share's round polynomial** evaluates as the next claim. -/
theorem shareRound_eval (w z pre : List E) (hw : w.length = 16) (st : Array E × Array E)
    (h : ShareInv prog w z pre st) (hpre : pre.length < 4) :
    (shareRound st).length = 3 ∧ ∀ x, polyEval (shareRound st) x = shareClaim prog w z (pre ++ [x]) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨rfl, fun x ↦ ?_⟩
  have hs1 : st.1.size = 2 ^ (4 - pre.length) := by
    rw [← Array.length_toList, h1]
    exact length_foldAll pre w _ (by rw [hw, show pre.length + (4 - pre.length) = 4 by omega]; rfl)
  have hm : st.1.size / 2 = 2 ^ (4 - (pre.length + 1)) := by
    rw [hs1, show 4 - pre.length = 4 - (pre.length + 1) + 1 by omega, pow_succ]; omega
  rw [shareClaim_snoc prog w z pre x hw hpre, shareRound, polyEval_three]
  simp only [List.map_map, Function.comp_def, sumE_map_range, hm]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [getD_toList st.1, getD_toList st.1, getD_toList st.2, getD_toList st.2, h1, h2]
  ring

theorem shareInv_fold (w z pre : List E) (st : Array E × Array E) (c : E)
    (h : ShareInv prog w z pre st) : ShareInv prog w z (pre ++ [c]) (shareFold st c) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by rw [shareFold, toList_foldPairsA, h1, foldAll_concat],
    by rw [shareFold, toList_foldPairsA, h2, foldAll_concat]⟩

/-- **The bytecode's share makes the specification's moves.** -/
theorem corr_bytecodeShareA (w z : List E) (hw : w.length = 16) (hz : z.length = prog.logSize) :
    Corr (fun _ _ ↦ True)
      (bytecodeShareA w (bytecodeSlotsA (bytecodeWords prog).toArray prog.logSize z))
      (hShare prog w z) := by
  have hsl := toList_bytecodeSlotsA prog z hz
  have hdot : dot w (bytecodeSlotsA (bytecodeWords prog).toArray prog.logSize z).toList =
      bcShare prog w z := by
    rw [hsl, LeanVM.Protocol.KeccakGkr.dot_eq _ _ (by rw [hw, length_slotList]), hw, bcShare]
    exact Finset.sum_congr rfl fun k hk ↦ by
      rw [getD_slotList prog z (Finset.mem_range.mp hk)]
  unfold bytecodeShareA hShare
  rw [hdot]
  refine Corr.bind_same _ fun _ ↦ ?_
  have hinit : ShareInv prog w z [] (w.toArray, bytecodeSlotsA (bytecodeWords prog).toArray
      prog.logSize z) := ⟨by simp, by rw [hsl]; rfl⟩
  refine Corr.bind (fun a b hab ↦ ?_) _ _
    (corr_sumcheckBy_lt 3 (by norm_num) (by norm_num) (shareClaim prog w z) shareRound shareFold
      (ShareInv prog w z) 4 (fun pre st h hlt ↦ shareRound_eval prog w z pre hw st h hlt)
      (fun pre st c h _ ↦ shareInv_fold prog w z pre st c h) (List.replicate busBits none) []
      _ hinit (by simp [busBits]))
  obtain ⟨h1, -, h3⟩ := hab
  have hfin : (a.2.2.getD 0 0) = multilinearEval (slotList prog z) b.1 := by
    rw [List.nil_append] at h3
    rw [multilinearEval_eq_foldAll, List.headD_eq_getD, ← h1, ← h3.2, getD_toList]
  rw [hfin]
  exact ⟨rfl, trivial⟩

end Share

/-! ## The phase -/

attribute [local irreducible] Corr Script.grindBits in
/-- **The bus phase makes the moves of `hBus`**, from the instance's columns as arrays. -/
theorem corr_busFast {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)}
    {cols : Array (Array K)} (hcols : ColsOk prog s q cols) :
    Corr (fun _ _ ↦ True) (busFast (verifierLayout prog s) cols) (hBus prog s q) := by
  unfold busFast hBus
  dsimp only
  rw [busLayout_depth_verifier]
  refine Corr.bind_same _ fun _ ↦ ?_
  refine Corr.bind (fun w w' hw ↦ ?_) _ _ (corr_sampleN _)
  obtain ⟨rfl, hlen⟩ := hw
  have hw16 : w.length = 16 := hlen
  refine Corr.bind_same _ fun beta ↦ ?_
  have hD : 0 < busDepth prog s := lt_of_lt_of_le s.logMem_pos (logMem_le_busDepth prog s)
  refine Corr.bind (fun g g' hg ↦ ?_) _ _
    (corr_gkrA hD (length_pushLeaves prog s q w beta) (length_pullLeaves prog s q w beta)
      (length_countLeaves prog s q)
      (fun k hk ↦ by rw [getD_treeLayers _ _ k hk, toList_pushLeaves hcols])
      (fun k hk ↦ by rw [getD_treeLayers _ _ k hk, toList_pullLeaves hcols])
      (fun k hk ↦ by rw [getD_treeLayers _ _ k hk, toList_countLeaves hcols]))
  obtain ⟨rfl, hpl, -⟩ := hg
  have hm : ∀ (i : Fin 3) (z : List E),
      mleK (cols.getD (i : ℕ) #[]) z = multilinearEval (colList prog s q (memCol i)) z :=
    fun i z ↦ by rw [← refCol_memCol]; exact mleK_col hcols _ z
  have h0 : ∀ z, mleK (cols.getD memory0 #[]) z =
      multilinearEval (colList prog s q (memCol 0)) z := hm 0
  have h1 : ∀ z, mleK (cols.getD memory1 #[]) z =
      multilinearEval (colList prog s q (memCol 1)) z := hm 1
  have h2 : ∀ z, mleK (cols.getD memoryFinalCounters #[]) z =
      multilinearEval (colList prog s q (memCol 2)) z := hm 2
  have hb : ∀ z, mleK (cols.getD bytecodeFinalCounters #[]) z =
      multilinearEval (colList prog s q bfcntCol) z := fun z ↦ by
    rw [← refCol_bfcntCol]; exact mleK_col hcols _ z
  unfold memVals mfVal bfVal
  rw [h0, h1, h2, hb, layout_logMemory, layout_logBytecode]
  refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun _ ↦ ?_
  have hz : (g.2.1.take prog.logSize).length = prog.logSize :=
    length_take_of_le (hpl ▸ logSize_le_busDepth prog s)
  rw [← Script.bind_ret (bytecodeShareA _ _)]
  exact Corr.bind (fun _ _ _ ↦ Corr.ret_ret trivial) _ _
    (corr_bytecodeShareA prog w _ hw16 hz)

end
end LeanVM.Prover
