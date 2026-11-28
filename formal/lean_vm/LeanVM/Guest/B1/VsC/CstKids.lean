/-
  LeanVM.Guest.B1.VsC.CstKids

  Pieces of `check_stack_terminal`'s placed completeness: its template's paths, its callees' regions
  and inputs.
-/

module

public import LeanVM.Guest.B1.VsC.CstMem
public import LeanVM.Guest.B1.VsC.StkSelA
public import LeanVM.Guest.B1.VsC.RingColsA
public import LeanVM.Guest.B1.VsC.EqChainA
public import LeanVM.Guest.Complete.ComposeRd

/-!
# `check_stack_terminal`, placed: the pieces

The path with the dispatch at arm `j` (`cstPreJ j`): its calls (`cst_calls`), its allocations and
buffers (`cst_parts`). A taken call in `KidsAtF` from its words (`kidsAtF_take'`). The cells of the
caller's arrays and of the node's buffers (`cells_arr`, `cells_own`). The node's own words as its
callees read them (`wo_*`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

theorem find_cst : coreProgram.find? "check_stack_terminal" = some fn% «check_stack_terminal» :=
  coreProgram_find?_at (j := idx% «check_stack_terminal») rfl

theorem cst_params : Fn.params fn% «check_stack_terminal» = (List.range 23).map V.n := rfl

theorem cst_loop : coreProgram.loop "check_stack_terminal" = false := by
  rw [Program.loop_of_find? find_cst, Fn.loop, check_stack_terminal_body, cstBody, cstBodyA_eq]
  simp

theorem cstArms_name : ∀ j < 15, cstArms.getD j "" = "stack_selectors__L" ++ natStr ((19 + j) / 4) := by decide

theorem stackCtxAt_length {rd : Reader} {args : List E} {layout : Layout} {link : LinkEnd}
    {chi r qPoint kOut kIn f g x z : List E} {rho lam rm : E} {outputs : List ColumnClaim}
    (h : StackCtxAt rd args layout link chi r qPoint kOut kIn f g x z rho lam rm outputs) : args.length = 23 := by
  unfold StackCtxAt at h
  split at h <;> simp_all

theorem args_eq_cstArgsOf {args : List E} (h : args.length = 23) : ∃ τ : Val, args = cstValArgs τ :=
  ⟨fun v => args.getD v.idx 0, by
    rw [cstArgsOf_eq, List.map_map]
    refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
    simp [List.getElem?_eq_getElem h1]⟩

theorem cstArgsOf_getD (τ : Val) {i : ℕ} (hi : i < 23) : (cstValArgs τ).getD i 0 = τ (.n i) := by
  rw [cstArgsOf_eq, List.getD_eq_getElem _ _ (by simp; exact hi)]
  simp

/-! ## The path at arm `j` -/

theorem cstH0_aoc : cstH0.all atomOrCall = true ∧ cstRest.all atomOrCall = true := by
  have := cstNodeOk_ok
  simp only [cstNodeOk, Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := this
  exact ⟨h1, h2⟩

theorem cstPreJ_aoc (j : ℕ) : (cstPreJ j).all atomOrCall = true := by
  simp only [cstPreJ, List.all_append, List.all_cons, cstH0_aoc.1, cstH0_aoc.2, atomOrCall, Bool.and_self]

/-- The calls of the path at arm `j`. -/
theorem cst_calls (σ : Val) {j : ℕ} (hj : j < 15) :
    calls ((cstPreJ j).flatMap (slEvs σ)) =
      ⟨"stack_selectors__L" ++ natStr ((19 + j) / 4), cstArgsV, [.n 43], true⟩ :: cstRestCalls := by
  have h : callsOfB (cstPreJ j) = callsOfB cstH0 ++ ⟨cstArms.getD j "", cstArgsV, [.n 43], true⟩ :: callsOfB cstRest := by
    simp only [cstPreJ, callsOfB, List.filterMap_append, List.filterMap_cons, callOf?]
  rw [calls_atomOrCall σ _ (cstPreJ_aoc j), h, cstH0_calls, cstRest_calls, cstArms_name j hj, List.nil_append]

theorem cstPreJ_allocSz (j : ℕ) : (cstPreJ j).filterMap Stmt.allocSz = cstAllocs := by
  have := cstNodeOk_ok
  simp only [cstNodeOk, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, -⟩, -⟩, -⟩ := this
  simp only [cstPreJ, List.filterMap_append, List.filterMap_cons, Stmt.allocSz, h3, h4, List.append_nil]

theorem cstPreJ_addrS (j : ℕ) : (cstPreJ j).filterMap Stmt.addrS = [] := by
  have := cstNodeOk_ok
  simp only [cstNodeOk, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h5⟩, h6⟩, -⟩ := this
  simp only [cstPreJ, List.filterMap_append, List.filterMap_cons, Stmt.addrS, h5, h6, List.nil_append]

theorem cst_plain {a : Atom} (h : Stmt.atom a ∈ cstH0 ++ cstRest) : cstPlainB a = true := by
  have := cstNodeOk_ok
  simp only [cstNodeOk, Bool.and_eq_true] at this
  exact List.all_eq_true.mp this.2 a (mem_atomsOf' h)

theorem cst_plain_preJ {j : ℕ} {a : Atom} (h : Stmt.atom a ∈ cstPreJ j) : cstPlainB a = true := by
  refine cst_plain ?_
  simp only [cstPreJ, List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h | h
  · exact Or.inl h
  · cases h
  · exact Or.inr h

/-- The path's allocations, destinations and frame addresses. -/
theorem cst_parts (σ : Val) (j : ℕ) {n : ℕ} (h30 : σ (.n 30) = gen ^ (64 * (n + 1))) (hn : n ≤ 24) :
    allocs σ ((cstPreJ j).flatMap (slEvs σ)) = cstSizes n ∧
      allocDsts ((cstPreJ j).flatMap (slEvs σ)) = (List.range 10).map (fun i => V.n (31 + i)) ∧
      addrs ((cstPreJ j).flatMap (slEvs σ)) = [] := by
  obtain ⟨h1, h2, h3, -⟩ := straight_parts σ (cstPreJ j) (straight_of_atomOrCall _ (cstPreJ_aoc j))
  refine ⟨?_, ?_, by rw [h3, cstPreJ_addrS]⟩
  · rw [h2, cstPreJ_allocSz]
    simp only [cstAllocs, List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, h30,
      logG_gen_pow (show 64 * (n + 1) < 2 ^ 64 - 1 by omega), cstSizes]
  · rw [h1, cstPreJ_allocSz]; rfl

theorem bases_cst (n c : ℕ) : bases c (cstSizes n) = (List.range 10).map (cstBase n c) := by
  simp [bases, cstSizes, cstBase, List.range_succ, Nat.add_assoc]

/-! ## Taken calls, cells -/

theorem kidsAtF_take' {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {σ : Val}
    {R : ℕ → Prop} {Pre O : Reader → Prop} {Dacc : ℕ → Prop} {Qs : List (Reader → Tree → Prop)} {cl : Call}
    {cs : List Call} {cur e : ℕ} {Oend : Reader → Prop} {Dend : ℕ → Prop} (ht : cl.taken = true) {as rs : List E}
    (has : cl.args.map σ = as) (hrs : cl.rets.map σ = rs) {Bc ec : ℕ} {Rc Dc : ℕ → Prop} {Oc : Reader → Prop}
    (hR : ∀ i, Rc i → R i ∨ Dacc i)
    (hc : CallAtA fs al cert k cl.f as rs Rc Dc Oc (fun rd => Pre rd ∧ O rd) (Qs.headD fun _ _ => True) Bc
      (allocBase (al cl.f) cur) (allocBase (al cl.f) cur + Bc) ec)
    (hrest : KidsAtF fs al cert k σ R Pre (fun rd => O rd ∧ Oc rd) (fun i => Dacc i ∨ Dc i) Qs.tail cs ec e Oend Dend) :
    KidsAtF fs al cert k σ R Pre O Dacc Qs (cl :: cs) cur e Oend Dend := by
  rw [KidsAtF]
  simp only [ht, ↓reduceIte]
  rw [has, hrs]
  exact ⟨Bc, ec, Rc, Dc, Oc, hR, hc, hrest⟩

theorem cells_arr {arrs : List (E × ℕ)} {fp : ℕ} (hb : PtrsBelow arrs fp) {Y : ℕ → Prop} {p : E} {len n : ℕ}
    (hq : (p, len) ∈ arrs) (hn : n ≤ len) : PtrCells (fun i => ptrRegion arrs i ∨ Y i) p n := fun off ho => by
  obtain ⟨i, hi, hr⟩ := region_of hb hq (t := off) (by show off < len; omega)
  exact ⟨i, hi, Or.inl hr⟩

theorem cells_own {Y : ℕ → Prop} {c T b e n : ℕ} (h1 : c ≤ b) (h2 : b + e + n ≤ c + T) :
    PtrCells (fun i => Y i ∨ (c ≤ i ∧ i < c + T)) (ptrAtV b * gen ^ e) n := fun off ho =>
  ⟨b + (e + off), by rw [addr_mul_gen, addr_ptr], Or.inr ⟨by omega, by omega⟩⟩

theorem cells_own0 {Y : ℕ → Prop} {c T b n : ℕ} (h1 : c ≤ b) (h2 : b + n ≤ c + T) :
    PtrCells (fun i => Y i ∨ (c ≤ i ∧ i < c + T)) (ptrAtV b) n := fun off ho =>
  ⟨b + off, addr_ptr _ _, Or.inr ⟨by omega, by omega⟩⟩

theorem hptr3 {R : ℕ → Prop} {a0 a1 a2 : E} {n0 n1 n2 : ℕ} (h0 : PtrCells R a0 n0) (h1 : PtrCells R a1 n1)
    (h2 : PtrCells R a2 n2) : ∀ q ∈ [(0, n0), (1, n1), (2, n2)], ∀ off < q.2,
      ∃ i, ([a0, a1, a2].getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i := by
  intro q hq off ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  exacts [h0 off ho, h1 off ho, h2 off ho]

theorem hptr4 {R : ℕ → Prop} {a0 a1 a2 a3 : E} {n0 n2 n3 : ℕ} (h0 : PtrCells R a0 n0) (h2 : PtrCells R a2 n2)
    (h3 : PtrCells R a3 n3) : ∀ q ∈ [(0, n0), (2, n2), (3, n3)], ∀ off < q.2,
      ∃ i, ([a0, a1, a2, a3].getD q.1 0).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i := by
  intro q hq off ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  exacts [h0 off ho, h2 off ho, h3 off ho]

/-- An `eq_prefix_chain`'s inputs from its chain's own words. -/
theorem epc_pre {rd : Reader} {x : List E} {chain a b1 : E} {as : List E} {len : ℕ}
    (hch : ReadsAt rd chain (chainW as x len)) (ha : ReadsAt rd a as)
    (hb : ReadsAt rd b1 (padX1 x)) :
    ReadsAt rd a (as.take len) ∧ ReadsAt rd b1 ((padX1 x).take len) ∧
      ∀ j ≤ len, LoadHolds rd chain j (prefixProd 1 (as.take len) ((padX1 x).take len) j) := by
  refine ⟨readsAt_take' ha len, readsAt_take' hb len, fun j hj => ?_⟩
  have hv := hch j (by rw [chainW, List.length_map, List.length_range]; omega)
  have e : (chainW as x len)[j]'(by rw [chainW, List.length_map, List.length_range]; omega) =
      prefixProd 1 (as.take len) ((padX1 x).take len) j := by
    simp only [chainW, List.getElem_map, List.getElem_range]
    unfold prefixProd
    rw [List.take_take, List.take_take, min_eq_left hj]
  rw [e] at hv
  exact hv

/-! ## The own words, as the callees read them -/

section
variable {rd : Reader} {c : ℕ} {layout : Layout} {chi r qPoint kOut x z f g : List E} {rho rm : E}
variable (hW : HoldsWords rd (cstWords c layout chi r qPoint kOut x z f g rho rm))
include hW

theorem wo0 : ReadsAt rd (ptrAtV (cstBase chi.length c 0))
    (rgRows (ringCoefficients f g) chi ((padX1 x).take chi.length) chi.length) :=
  hW (cstBase chi.length c 0, rgRows (ringCoefficients f g) chi ((padX1 x).take chi.length) chi.length)
    (by simp only [cstWords]; exact List.mem_cons_self)

theorem wo_run {i : ℕ} {ws : List E} (hm : (cstBase chi.length c i, ws) ∈ cstWords c layout chi r qPoint kOut x z f g rho rm) :
    ReadsAt rd (ptrAtV (cstBase chi.length c i)) ws := hW _ hm

/-- A table's row of `rchi`. -/
theorem wo_row {h : ℕ} (hh : h ≤ chi.length) :
    ReadsAt rd (ptrAtV (cstBase chi.length c 0) * gen ^ (64 * h)) (rcRow (ringCoefficients f g) chi x h) := by
  intro k hk
  have hk' : k < 64 := by simpa [rcRow] using hk
  rw [loadHolds_mul_gen_pow]
  simp only [rcRow, List.getElem_map, List.getElem_range]
  exact rgRows_at (wo0 hW) hh hk'

end

end
end LeanVM.Guest.B1.VsC
