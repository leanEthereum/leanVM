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
* the callees' preconditions on such a memory (`gkrPre_of`, `tablesPre_of`, `flockPre_of`,
  `placePre_of`, `openPre_of`, `termPre_acc`), and `Log2Pre`, the shape of group 1's
  `log2_ceil_in_the_exponent` this file takes.
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

/-- `log2_ceil_in_the_exponent`'s precondition, floor `lo`: `g^N`, `N < 2^34` with its result
below `2^34`, and the exponent tables; its result returned. -/
def Log2Pre (lo : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∃ (N : ℕ) (lp sq : E), args = [gen ^ N, lp, sq] ∧ rets = [gen ^ max lo (log2Ceil N)] ∧
    N < 2 ^ 34 ∧ max lo (log2Ceil N) < 34 ∧ ExpTables rd lp sq

theorem curW_eq : curW D (vsPtrsAt fs fp D off kap pt) = ofK (Parameters.gpow
    ((vsBases D (fp + fs "verify_sub")).getD 2 0 + 10 + D.xsG.length + D.xsT.length +
      D.xsF.length)) := by
  have hs : (vsPtrsAt fs fp D off kap pt).stream =
      ofK (Parameters.gpow ((vsBases D (fp + fs "verify_sub")).getD 2 0)) := rfl
  simp only [curW, curF, curT, curG, hs, gen_pow_eq_ofK, ← ofK_mul, Parameters.gpow, ← pow_add]

variable {P : VsPtrs} {out lp sq : E}

theorem gkrPre_of (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (hm : VsMem0 rd D P out) :
    GkrPre rd [(digestScalars D.cvB).1, (digestScalars D.cvB).2, curG P, gen ^ log2Ceil D.pushTotal,
      P.zeta] [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P, D.gr.2.2.getD 0 0,
        D.gr.2.2.getD 1 0, D.gr.2.2.getD 2 0] := by
  obtain ⟨hxG, -, -, -⟩ := stream_at hok.rows_length hm.stream
  have := gkrOut_honest hok hm.zeta hxG
  rw [depth_eq hb hok, values_eq hok] at this
  exact this

theorem tablesPre_of (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (htok : D.TOk bytecode)
    (ht : ExpTables rd lp sq) (hm : VsMem0 rd D P out) (hchi : ReadsAt rd P.chi D.chis)
    (hcp : ReadsAt rd P.cplen (cplenWords D)) :
    TablesPreOut bytecode TCtx rd [(digestScalars D.cvG).1, (digestScalars D.cvG).2, curT D P,
      (digestScalars D.pi).1, (digestScalars D.pi).2, P.zeta, gen ^ log2Ceil D.pushTotal, P.dims,
      P.rows, P.bk, sq, P.fpw, D.beta, P.pool, P.cplen, P.chi, D.gr.2.2.getD 0 0, D.gr.2.2.getD 1 0,
      D.gr.2.2.getD 2 0] [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, D.gzcn, D.bv,
        D.rm] := by
  obtain ⟨-, hxT, -, -⟩ := stream_at hok.rows_length hm.stream
  have : TablesPreOut bytecode TCtx rd (tabArgs D P sq) (tabRets D P) :=
    ⟨lp, D.pi, D.logMem, D.alphas, D.gr.2.1, D.gr.2.2, tablesPre_honest hok ht hm,
      tablesOut_honestQ hok hm hxT (tctx_of hok htok hm.zeta hchi hcp)⟩
  rw [tabArgs, depth_eq hb hok] at this
  exact this

theorem flockPre_of (hok : D.Ok bytecode) (hm : VsMem0 rd D P out) :
    FlockPre rd [(digestScalars D.cvT).1, (digestScalars D.cvT).2, curF D P, gen ^ D.tau, P.zchis,
      P.lrs, P.zpart] [(digestScalars D.cvF).1, (digestScalars D.cvF).2, curW D P, D.zSkip, D.alpha,
        D.mv] := by
  obtain ⟨-, -, hxF, -⟩ := stream_at hok.rows_length hm.stream
  exact ⟨D.tau, _, _, _, _, _, _, tau_lt hok, rfl, flockOut_honest hok hm hxF⟩

theorem placePre_of (ht : ExpTables rd lp sq) (hm : VsMem0 rd D P out) :
    ExpTables rd lp sq ∧ ReadsAt rd P.kbase (1 :: gen ^ D.logMem :: D.hs.map (gen ^ ·)) :=
  ⟨ht, hm.kbase⟩

theorem termPre_acc {PC : Reader → List ℕ → E → E → Prop} (hb : bytecode.length = 2 ^ 22)
    (hok : D.Ok bytecode) (htok : D.TOk bytecode) (hm : VsMem0 rd D P out)
    (hchi : ReadsAt rd P.chi D.chis) (hcp : ReadsAt rd P.cplen (cplenWords D))
    (hpc : PC rd (columnKappas D.logMem 18 D.hs) P.off P.kap) (hK : HypKappa PC rd)
    (hpt : ReadsAt rd P.pt (D.w.point ++ List.replicate (pointCap - D.w.point.length) 0)) :
    TermPreAcc TCtx PC rd [P.zeta, P.chi, D.rm, gen ^ log2Ceil D.pushTotal, D.gzcn,
        gen ^ D.logMem, gen ^ D.tau, P.cplen, P.lam, P.off, P.kap, P.zvals, P.ctab, P.pt, D.w.inner,
        D.w.residual, D.w.target] [] := by
  have htc := tctx_of hok htok hm.zeta hchi hcp
  rw [depth_eq hb hok] at htc
  exact ⟨rfl, _, _, _, _, _, _, _, termPre_of hb hok htc hpc hK hm.lam hm.zvals hm.ctab hpt,
    hok.accepts⟩

end
end LeanVM.Guest.B1.VerifySub
