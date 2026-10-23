/-
  LeanVM.Guest.B1.VerifySub.CPlaced3

  `verify_sub` placed: the layouts of its own buffers and of the caller's words it reads, the
  honest memory on any memory holding them, and its callees' preconditions there.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced2

/-!
# `verify_sub` placed: the memory and the callees' preconditions

* `expL`: the exponent tables at `lpA`, `sqA`; `vsExtL`: those and `defer_out`'s cells, the words
  of the caller `verify_sub` reads; `vsOwnL`: its own buffers, from `fp + fs "verify_sub"`;
* `vsMem0_of`: a memory holding them holds the run's buffers (`VsMem0`) at `vsPtrsAt`;
* the cursors at their addresses (`cur_eqs`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-! ## The layouts -/

/-- `g_logs_pow2` at `lpA` and `g_squares` at `sqA`. -/
def expL (lpA sqA : ℕ) : Main.Layout :=
  [(lpA, (List.range sizeBits).map fun j => eOfNat (2 ^ j)),
    (sqA, (List.range sizeBits).map fun j => gen ^ 2 ^ j)]

/-- The caller's words `verify_sub` reads: the exponent tables and `defer_out`'s cells. -/
def vsExtL (lpA sqA outA : ℕ) (D : VsData) : Main.Layout :=
  expL lpA sqA ++ [(outA, Node.fixedCells D.fresh)]

/-- `verify_sub`'s own buffers at `fp`. -/
def vsOwnL (fs : String → ℕ) (fp : ℕ) (D : VsData) : Main.Layout :=
  bufL (fp + fs "verify_sub") (vsSizes D) (vsBufs D)

theorem expTables_of {rd : Reader} {lpA sqA : ℕ} (h : MemL rd (expL lpA sqA)) :
    ExpTables rd (ofK (Parameters.gpow lpA)) (ofK (Parameters.gpow sqA)) := by
  have h1 := h _ List.mem_cons_self
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  intro j hj
  have e1 := h1 j (by simpa using hj)
  have e2 := h2 j (by simpa using hj)
  rw [List.getElem_map, List.getElem_range] at e1 e2
  exact ⟨e1, e2⟩

theorem length_bases (b : ℕ) : ∀ sizes : List ℕ, (bases b sizes).length = sizes.length
  | [] => rfl
  | _ :: ss => by simp [bases, length_bases _ ss]

theorem memL_bufL_get {rd : Reader} {b : ℕ} {sizes : List ℕ} {cs : List (List E)}
    (h : MemL rd (bufL b sizes cs)) {i : ℕ} (hi : i < sizes.length) (hc : i < cs.length) :
    ReadsAt rd (ofK (Parameters.gpow ((bases b sizes).getD i 0))) (cs.getD i []) := by
  have hb : i < (bases b sizes).length := by rw [length_bases]; exact hi
  have hz : i < (bufL b sizes cs).length := by simp [bufL, List.length_zip, length_bases]; omega
  have := h _ (List.getElem_mem hz)
  simp only [bufL, List.getElem_zip] at this
  rwa [List.getD_eq_getElem _ _ hb, List.getD_eq_getElem _ _ hc]

/-! ## The honest memory -/

variable {rd : Reader} {D : VsData} {bytecode : List K} {fs : String → ℕ} {fp : ℕ} {off kap pt : E}

/-- **The run's buffers** on a memory holding `verify_sub`'s own words and `defer_out`'s. -/
theorem vsMem0_of {outA : ℕ} (hL : MemL rd (vsOwnL fs fp D))
    (ho : ReadsAt rd (ofK (Parameters.gpow outA)) (Node.fixedCells D.fresh)) :
    VsMem0 rd D (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow outA)) := by
  have g := fun i (hi : i < 19) xs (hx : (vsBufs D).getD i [] = xs) =>
    hx ▸ memL_bufL_get (i := i) hL (by simp [vsSizes]; omega) (by simp [vsBufs]; omega)
  exact ⟨g 2 (by omega) _ (by simp [vsBufs]), g 0 (by omega) _ (by simp [vsBufs]),
    g 3 (by omega) _ (by simp [vsBufs]), g 4 (by omega) _ (by simp [vsBufs]),
    g 5 (by omega) _ (by simp [vsBufs]), g 6 (by omega) _ (by simp [vsBufs]),
    g 7 (by omega) _ (by simp [vsBufs]), g 8 (by omega) _ (by simp [vsBufs]),
    g 9 (by omega) _ (by simp [vsBufs]), g 11 (by omega) _ (by simp [vsBufs]),
    g 12 (by omega) _ (by simp [vsBufs]), g 13 (by omega) _ (by simp [vsBufs]),
    g 14 (by omega) _ (by simp [vsBufs]), g 15 (by omega) _ (by simp [vsBufs]),
    g 16 (by omega) _ (by simp [vsBufs]), g 17 (by omega) _ (by simp [vsBufs]),
    g 18 (by omega) _ (by simp [vsBufs]), ho⟩

theorem cplen_of (hL : MemL rd (vsOwnL fs fp D)) :
    ReadsAt rd (vsPtrsAt fs fp D off kap pt).cplen (cplenWords D) := by
  have g := memL_bufL_get (i := 1) hL (by simp [vsSizes]) (by simp [vsBufs])
  simp only [vsBufs, List.getD_cons_succ, List.getD_cons_zero] at g
  exact g

theorem chis_of (hL : MemL rd (vsOwnL fs fp D)) :
    ReadsAt rd (vsPtrsAt fs fp D off kap pt).chi D.chis := by
  have g := memL_bufL_get (i := 10) hL (by simp [vsSizes]) (by simp [vsBufs])
  simp only [vsBufs, List.getD_cons_succ, List.getD_cons_zero] at g
  exact g

/-! ## The callees' preconditions -/

/-- The address of `verify_sub`'s buffer `i` at `fp`. -/
def vsB (fs : String → ℕ) (fp : ℕ) (D : VsData) (i : ℕ) : ℕ := (vsBases D (fp + fs "verify_sub")).getD i 0

theorem cur_eqs : curG (vsPtrsAt fs fp D off kap pt) = ofK (Parameters.gpow (vsB fs fp D 2 + 10)) ∧
    curT D (vsPtrsAt fs fp D off kap pt) =
      ofK (Parameters.gpow (vsB fs fp D 2 + 10 + D.xsG.length)) ∧
    curF D (vsPtrsAt fs fp D off kap pt) =
      ofK (Parameters.gpow (vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length)) ∧
    curW D (vsPtrsAt fs fp D off kap pt) = ofK (Parameters.gpow
      (vsB fs fp D 2 + 10 + D.xsG.length + D.xsT.length + D.xsF.length)) := by
  have hs : (vsPtrsAt fs fp D off kap pt).stream = ofK (Parameters.gpow (vsB fs fp D 2)) := rfl
  simp only [curW, curF, curT, curG, hs, gen_pow_eq_ofK, ← ofK_mul, Parameters.gpow, ← pow_add,
    and_self]

theorem curW_eq : curW D (vsPtrsAt fs fp D off kap pt) = ofK (Parameters.gpow
    ((vsBases D (fp + fs "verify_sub")).getD 2 0 + 10 + D.xsG.length + D.xsT.length +
      D.xsF.length)) := cur_eqs.2.2.2

theorem hsMap_eq : D.hs.map (gen ^ ·) = D.rows.map fun n ↦ gen ^ log2Ceil n := by
  simp [VsData.hs, List.map_map, Function.comp_def]

variable {P : VsPtrs} {out lp sq : E}

theorem placePre_of (ht : ExpTables rd lp sq) (hm : VsMem0 rd D P out) :
    ExpTables rd lp sq ∧ ReadsAt rd P.kbase (1 :: gen ^ D.logMem :: D.hs.map (gen ^ ·)) :=
  ⟨ht, hm.kbase⟩

end
end LeanVM.Guest.B1.VerifySub
