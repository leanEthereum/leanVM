/-
  LeanVM.Guest.B1.VerifySub.CAssemble

  `verify_sub`'s body, complete: its blocks composed, from the arguments to every statement before
  the `ret`, for any relation the calls hold of.
-/

module

public import LeanVM.Guest.B1.VerifySub.CTail

/-!
# The body, complete

`vs_body`: from a valuation of the arguments, the blocks of `vsBody` complete in turn, each from
the values the ones before it leave (the accumulated `Fixes` lists `vsG*`), the memory honest
(`VsMem`) and the calls holding of `C` (`VsCallsOk`). The valuation reached gives every `HeapBuf`
hint its pointer (`allocFix`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

variable {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs} {out lp sq : E} {bytecode : List K}

/-! ## The memory, word by word -/

theorem mem_stream (hl : D.rows.length = 6) (hm : VsMem0 rd D P out) :
    (∀ k < 8, LoadHolds rd P.stream k (D.ann.getD k 0)) ∧ LoadHolds rd P.stream 8 D.x0 ∧
      LoadHolds rd P.stream 9 D.x1 := by
  have h := hm.stream
  rw [VsData.stream] at h
  have ha := readsAt_left h
  have hr := readsAt_right h
  rw [ann_length hl] at hr
  refine ⟨fun k hk => readsAt_getD ha (by rw [ann_length hl]; exact hk), ?_, ?_⟩
  · have := hr 0 (by simp); rw [loadHolds_mul_gen_pow] at this; simpa using this
  · have := hr 1 (by simp); rw [loadHolds_mul_gen_pow] at this; simpa using this

theorem mem_rows (hl : D.rows.length = 6) (hm : VsMem0 rd D P out) :
    ∀ t < 6, LoadHolds rd P.rows t (eOfNat (D.rows.getD t 0)) := fun t ht => by
  have := readsAt_getD hm.rows (k := t) (by simp [hl]; omega)
  rwa [List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_map,
    ← List.getD_eq_getElem _ 0 (by omega)] at this

theorem mem_dims (hok : D.Ok bytecode) (hm : VsMem0 rd D P out) :
    LoadHolds rd P.dims 0 (gen ^ D.logMem) ∧
      ∀ t < 6, LoadHolds rd P.dims (1 + t) (gen ^ D.hs.getD t 0) := by
  have hl := hs_length hok
  refine ⟨by simpa using readsAt_getD hm.dims (k := 0) (by simp), fun t ht => ?_⟩
  have := readsAt_getD hm.dims (k := 1 + t) (by simp [hl]; omega)
  rw [show 1 + t = t + 1 by omega, List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp [hl]; omega),
    List.getElem_map, ← List.getD_eq_getElem _ 0 (by omega)] at this
  rwa [show 1 + t = t + 1 by omega]

theorem mem_kbase (hok : D.Ok bytecode) (hm : VsMem0 rd D P out) :
    LoadHolds rd P.kbase 0 1 ∧ LoadHolds rd P.kbase 1 (gen ^ D.logMem) ∧
      (∀ t < 6, LoadHolds rd P.kbase (2 + t) (gen ^ D.hs.getD t 0)) ∧
      ∀ b < 102, LoadHolds rd P.kbase (blockKappaSrc.getD b 0) (bkSrc D b) := by
  have hl := hs_length hok
  have hlen : (kappaBase (gen ^ D.logMem) (D.hs.map (gen ^ ·))).length = 8 := by
    simp [kappaBase, hl]
  refine ⟨by simpa [kappaBase] using readsAt_getD hm.kbase (k := 0) (by omega),
    by simpa [kappaBase] using readsAt_getD hm.kbase (k := 1) (by omega), fun t ht => ?_,
    fun b hb => readsAt_getD hm.kbase (by rw [hlen]; exact blockKappaSrc_lt b hb)⟩
  have := readsAt_getD hm.kbase (k := 2 + t) (by omega)
  rw [show 2 + t = t + 2 by omega, kappaBase, List.getD_cons_succ, List.getD_cons_succ,
    List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_map,
    ← List.getD_eq_getElem _ 0 (by omega)] at this
  rwa [show 2 + t = t + 2 by omega]

theorem mem_bk (hm : VsMem0 rd D P out) :
    ∀ b < 102, LoadHolds rd P.bk b ((blockKappas (gen ^ D.logMem) (D.hs.map (gen ^ ·))).getD b 0) :=
  fun b hb => readsAt_getD hm.bk (by simp [blockKappas]; omega)

theorem mem_bk_pow (hok : D.Ok bytecode) (hm : VsMem0 rd D P out) :
    ∀ b < 37, LoadHolds rd P.bk b (gen ^ pkap D b) := fun b hb => by
  have := mem_bk hm b (by omega)
  rwa [blockKappas_pow _ _ (hs_length hok) b hb] at this

theorem alphas_eq : D.alphas = [busA D 0, busA D 1, busA D 2, busA D 3] := by
  simp [VsData.alphas, sqAll_eq, busA, List.range_succ]

theorem mem_alpha (hm : VsMem0 rd D P out) : ∀ c < 4, LoadHolds rd P.alpha c (busA D c) := by
  intro c hc
  have := readsAt_getD hm.alpha (k := c) (by rw [alphas_eq]; simp; omega)
  rw [alphas_eq] at this
  interval_cases c <;> simpa using this

theorem mem_fpw (hm : VsMem0 rd D P out) : ∀ x < 16, LoadHolds rd P.fpw x
    (eqFactor (busA D) x 0 * eqFactor (busA D) x 1 * eqFactor (busA D) x 2 * eqFactor (busA D) x 3) := by
  intro x hx
  have := readsAt_getD hm.fpw (k := x) (by rw [alphas_eq]; simp [eqKernel]; omega)
  rwa [alphas_eq, eqKernel4 (busA D) x hx] at this

theorem hs_lt (hok : D.Ok bytecode) : ∀ h ∈ D.hs, h < 29 := by
  intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx; exact hok.rows_log n hn

/-! ## The accumulated values -/

/-- The arguments. -/
def vsG0 (D : VsData) (lp sq out : E) : List (ℕ × E) :=
  [(0, (digestScalars D.pi).1), (1, (digestScalars D.pi).2), (2, (digestScalars D.seed).1),
    (3, (digestScalars D.seed).2), (4, lp), (5, sq), (6, out)]

def vsG1 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := seedOut D P ++ vsG0 D lp sq out
def vsG2 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := readsOut D P ++ vsG1 D P lp sq out
def vsG3 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := sizesOut D P ++ vsG2 D P lp sq out
def vsG4 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := [(155, P.kbase)] ++ vsG3 D P lp sq out
def vsG5 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) :=
  [(155, P.kbase), (163, P.bk)] ++ vsG4 D P lp sq out
def vsG6 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := pushOut D P sq ++ vsG5 D P lp sq out
def vsG7 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := rootOut D ++ vsG6 D P lp sq out
def vsG8 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := busOut D P ++ vsG7 D P lp sq out
def vsG9 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := callsOut D P ++ vsG8 D P lp sq out
def vsG10 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := ringOut D P ++ vsG9 D P lp sq out
def vsG11 (D : VsData) (P : VsPtrs) (lp sq out : E) : List (ℕ × E) := lamOut D P ++ vsG10 D P lp sq out

theorem Fixes.sub {σ : Val} {G L : List (ℕ × E)} (h : Fixes σ G) (hs : ∀ p ∈ L, p ∈ G) : Fixes σ L :=
  fun p hp => h p (hs p hp)

theorem completes_step {lo hi : ℕ} {blk : List Stmt} {σ : Val} {Out G : List (ℕ × E)}
    (h : Completes C rd lo hi blk σ (fun σ' => Fixes σ' Out)) (hG : Fixes σ G)
    (hlo : ∀ p ∈ G, p.1 < lo) : Completes C rd lo hi blk σ (fun σ' => Fixes σ' (Out ++ G)) :=
  (h.keep hG hlo).post fun _ _ ⟨a, b⟩ => a.append b

theorem completes_last {lo hi : ℕ} {blk : List Stmt} {σ : Val} {G : List (ℕ × E)}
    (h : Completes C rd lo hi blk σ (fun _ => True)) (hG : Fixes σ G)
    (hlo : ∀ p ∈ G, p.1 < lo) : Completes C rd lo hi blk σ (fun σ' => Fixes σ' G) :=
  (h.keep hG hlo).post fun _ _ ⟨_, b⟩ => b

/-- The `HeapBuf` hints' pointers. -/
def allocFix (P : VsPtrs) : List (ℕ × E) :=
  [(7, P.pool), (8, P.cplen), (14, P.stream), (30, P.rows), (143, P.dims), (155, P.kbase), (163, P.bk),
    (418, P.zeta), (451, P.alpha), (508, P.fpw), (709, P.chi), (721, P.zchis), (722, P.lrs),
    (723, P.zpart), (732, P.mcs), (733, P.ctab), (734, P.zvals), (1144, P.rs), (1180, P.lam)]

theorem vsBody_eq : vsBody = bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa ++ bPush ++ bRoot ++
    bBus ++ bCalls ++ bRing ++ bLam ++ bOpen ++ bDefer := rfl

theorem numBelow_pre1 : NumBelow 15 (Stmt.valsList (bSeed)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre2 : NumBelow 136 (Stmt.valsList (bSeed ++ bReads)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre3 : NumBelow 155 (Stmt.valsList (bSeed ++ bReads ++ bSizes)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre4 : NumBelow 163 (Stmt.valsList (bSeed ++ bReads ++ bSizes ++ bKBase)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre5 : NumBelow 270 (Stmt.valsList (bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre6 : NumBelow 419 (Stmt.valsList (bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa ++ bPush)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre7 : NumBelow 451 (Stmt.valsList (bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa ++ bPush ++ bRoot)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre8 : NumBelow 701 (Stmt.valsList (bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa ++ bPush ++ bRoot ++ bBus)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre9 : NumBelow 735 (Stmt.valsList (bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa ++ bPush ++ bRoot ++ bBus ++ bCalls)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre10 : NumBelow 1166 (Stmt.valsList (bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa ++ bPush ++ bRoot ++ bBus ++ bCalls ++ bRing)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre11 : NumBelow 1629 (Stmt.valsList (bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa ++ bPush ++ bRoot ++ bBus ++ bCalls ++ bRing ++ bLam)) :=
  numBelow_of_B (by decide +kernel)

theorem numBelow_pre12 : NumBelow 1652 (Stmt.valsList (bSeed ++ bReads ++ bSizes ++ bKBase ++ bBlockKappa ++ bPush ++ bRoot ++ bBus ++ bCalls ++ bRing ++ bLam ++ bOpen)) :=
  numBelow_of_B (by decide +kernel)

/-- Membership in the accumulated lists. -/
macro "vs_mem" : tactic => `(tactic| simp [vsG0, vsG1, vsG2, vsG3, vsG4, vsG5, vsG6, vsG7, vsG8, vsG9,
  vsG10, vsG11, seedOut, readsOut, sizesOut, pushOut, rootOut, busOut, callsOut, ringOut, lamOut, curG,
  deferIn, openIn, lamIn, ringIn, callsIn, pushPtrs, pushK, List.range_succ])

/-! ## The steps -/

section Steps

variable (hlow : LowDef 6 rd) (hb : bytecode.length = 2 ^ 22)
  (hok : D.Ok bytecode) (ht : ExpTables rd lp sq) (hm : VsMem0 rd D P out)
  (hC : VsCallsOk C bytecode D P lp sq)

theorem s_seed (σ : Val) (h : Fixes σ (vsG0 D lp sq out)) :
    Completes C rd 7 15 bSeed σ (fun σ' => Fixes σ' (vsG1 D P lp sq out)) :=
  completes_step (c_seed σ (h.get (by vs_mem)) (h.get (by vs_mem)) (h.get (by vs_mem))
    (h.get (by vs_mem))) h (by vs_mem)

include hok hm in
theorem s_reads (σ : Val) (h : Fixes σ (vsG1 D P lp sq out)) :
    Completes C rd 15 136 bReads σ (fun σ' => Fixes σ' (vsG2 D P lp sq out)) :=
  completes_step (c_reads hok.rows_length σ (h.sub fun _ hp => List.mem_append_left _ hp)
    (mem_stream hok.rows_length hm).1 (mem_rows hok.rows_length hm)) h (by vs_mem)

include hlow hok hm hC in
theorem s_sizes (σ : Val) (h : Fixes σ (vsG2 D P lp sq out)) :
    Completes C rd 136 155 bSizes σ (fun σ' => Fixes σ' (vsG3 D P lp sq out)) :=
  completes_step (c_sizes hlow hok.logMem_ge hok.logMem_le hok.rate_ge hok.rate_le hC
    (mem_dims hok hm).1 σ (h.sub (by vs_mem))) h (by vs_mem)

include hok hm in
theorem s_kbase (σ : Val) (h : Fixes σ (vsG3 D P lp sq out)) :
    Completes C rd 155 163 bKBase σ (fun σ' => Fixes σ' (vsG4 D P lp sq out)) :=
  completes_step (c_kbase σ (h.sub (by vs_mem)) (mem_dims hok hm).2 (mem_kbase hok hm).1
    (mem_kbase hok hm).2.1 (mem_kbase hok hm).2.2.1) h (by vs_mem)

include hok hm in
theorem s_bk (σ : Val) (h : Fixes σ (vsG4 D P lp sq out)) :
    Completes C rd 163 270 bBlockKappa σ (fun σ' => Fixes σ' (vsG5 D P lp sq out)) :=
  completes_step (c_blockKappa σ (h.get (by vs_mem)) (mem_kbase hok hm).2.2.2 (mem_bk hm)) h
    (by vs_mem)

include hb hok ht hm hC in
theorem s_push (σ : Val) (h : Fixes σ (vsG5 D P lp sq out)) :
    Completes C rd 270 419 bPush σ (fun σ' => Fixes σ' (vsG6 D P lp sq out)) :=
  completes_step (c_push ht hok.rows_length hok.logMem_le (hs_lt hok)
    (by rw [← depth_eq hb hok, hok.point_length]; exact hok.depth_lt) (mem_bk_pow hok hm) hC σ
    (h.sub (by vs_mem))) h (by vs_mem)

include hok hm hC in
theorem s_root (σ : Val) (h : Fixes σ (vsG6 D P lp sq out)) :
    Completes C rd 419 451 bRoot σ (fun σ' => Fixes σ' (vsG7 D P lp sq out)) :=
  completes_step (c_root σ (h.get (by vs_mem))
    (by rw [h.get (k := 134) (e := (digestScalars (obsAll D.cv0 D.ann)).1) (by vs_mem),
      h.get (k := 135) (e := (digestScalars (obsAll D.cv0 D.ann)).2) (by vs_mem)])
    (mem_stream hok.rows_length hm).2.1 (mem_stream hok.rows_length hm).2.2 hC) h (by vs_mem)

include hm in
theorem s_bus (σ : Val) (h : Fixes σ (vsG7 D P lp sq out)) :
    Completes C rd 451 701 bBus σ (fun σ' => Fixes σ' (vsG8 D P lp sq out)) :=
  completes_step (c_bus σ (h.sub (by vs_mem)) (mem_alpha hm) (mem_fpw hm)) h (by vs_mem)

include hok hm hC in
theorem s_calls (σ : Val) (h : Fixes σ (vsG8 D P lp sq out)) :
    Completes C rd 701 735 bCalls σ (fun σ' => Fixes σ' (vsG9 D P lp sq out)) :=
  completes_step (c_calls hok hm hC σ (h.sub (by vs_mem))) h (by vs_mem)

include hok hm hC in
theorem s_ring (σ : Val) (h : Fixes σ (vsG9 D P lp sq out)) :
    Completes C rd 735 1166 bRing σ (fun σ' => Fixes σ' (vsG10 D P lp sq out)) :=
  completes_step (c_ring hok hm hC σ (h.sub (by vs_mem))) h (by vs_mem)

include hok hm in
theorem s_lam (σ : Val) (h : Fixes σ (vsG10 D P lp sq out)) :
    Completes C rd 1166 1629 bLam σ (fun σ' => Fixes σ' (vsG11 D P lp sq out)) :=
  completes_step (c_lam hok.claims_length hm σ (h.sub (by vs_mem))) h (by vs_mem)

include hlow hb hok hC in
theorem s_open (σ : Val) (h : Fixes σ (vsG11 D P lp sq out)) :
    Completes C rd 1629 1652 bOpen σ (fun σ' => Fixes σ' (vsG11 D P lp sq out)) :=
  completes_last (c_open hlow hb hok hC σ (h.sub (by vs_mem))) h (by vs_mem)

include hb hok hm in
theorem s_defer (σ : Val) (h : Fixes σ (vsG11 D P lp sq out)) :
    Completes C rd 1652 1754 bDefer σ (fun σ' => Fixes σ' (vsG11 D P lp sq out)) :=
  completes_last (c_defer hb hok hm σ (h.sub (by vs_mem))) h (by vs_mem)

end Steps

/-- **`verify_sub`'s body completes**, for any relation `C` its calls hold of, over the honest
memory. -/
theorem vs_body (hlow : LowDef 6 rd) (hb : bytecode.length = 2 ^ 22)
    (hok : D.Ok bytecode) (ht : ExpTables rd lp sq) (hm : VsMem0 rd D P out)
    (hC : VsCallsOk C bytecode D P lp sq) (σ0 : Val) (h0 : Fixes σ0 (vsG0 D lp sq out)) :
    Completes C rd 7 1754 vsBody σ0 (fun σ' => Fixes σ' (vsG11 D P lp sq out)) := by
  rw [vsBody_eq]
  refine Completes.append (by omega) (by omega) numBelow_pre12 ?_ fun σ _ h =>
    s_defer hb hok hm σ h
  refine Completes.append (by omega) (by omega) numBelow_pre11 ?_ fun σ _ h =>
    s_open hlow hb hok hC σ h
  refine Completes.append (by omega) (by omega) numBelow_pre10 ?_ fun σ _ h =>
    s_lam hok hm σ h
  refine Completes.append (by omega) (by omega) numBelow_pre9 ?_ fun σ _ h =>
    s_ring hok hm hC σ h
  refine Completes.append (by omega) (by omega) numBelow_pre8 ?_ fun σ _ h =>
    s_calls hok hm hC σ h
  refine Completes.append (by omega) (by omega) numBelow_pre7 ?_ fun σ _ h =>
    s_bus hm σ h
  refine Completes.append (by omega) (by omega) numBelow_pre6 ?_ fun σ _ h =>
    s_root hok hm hC σ h
  refine Completes.append (by omega) (by omega) numBelow_pre5 ?_ fun σ _ h =>
    s_push hb hok ht hm hC σ h
  refine Completes.append (by omega) (by omega) numBelow_pre4 ?_ fun σ _ h =>
    s_bk hok hm σ h
  refine Completes.append (by omega) (by omega) numBelow_pre3 ?_ fun σ _ h =>
    s_kbase hok hm σ h
  refine Completes.append (by omega) (by omega) numBelow_pre2 ?_ fun σ _ h =>
    s_sizes hlow hok hm hC σ h
  refine Completes.append (by omega) (by omega) numBelow_pre1 ?_ fun σ _ h =>
    s_reads hok hm σ h
  exact s_seed σ0 h0

end
end LeanVM.Guest.B1.VerifySub
