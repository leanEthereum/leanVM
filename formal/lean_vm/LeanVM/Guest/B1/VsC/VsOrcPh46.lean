/-
  LeanVM.Guest.B1.VsC.VsOrcPh46

  `wC`'s phases 4 to 6 at the honest context: `Ph4to6S`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh1
public import LeanVM.Guest.B1.VsC.VsOrcPhC
public import LeanVM.Guest.B1.VsC.VsOrcMem

/-!
# `wC`'s phases 4 to 6 at the honest context

`Ph4to6S al` (`VsOrcSpec.lean`), from `x.Hon` (`Bw1`, `Ret1`, `VsFsChecks1`, `fresh`), the callees'
completeness, `Bnd` and the front's `CarryF`:

* `Ph4`: `chunk_d`'s chunk count and `certify_stack` from `VsCalleesCompleteA.certify_stack` at `x.fpc`, on the
  announced layout (`announced_build`), its kappa sources the front's buffer `.n 112` (`Bw1F.b20`);
* `Ph5`: the out-of-domain grind's window by `vsW_gcWin` (the overlay's `fresh`), its low bits and the point and
  message from `VsFsChecks1`, the stream at `.n 55`;
* `Ph6`: the link grind's window, the packing check from the link's shape (`vsPk`), `squeeze_packed` from the
  link callees, narrowed to its output's indices (`CallAtA.idxR`);
* the end: `Bnd` with the posts `[quiet, stack, quiet, quiet, quiet]` against `vsPs`' entries after the front
  (`VsCtx.Bnd.ph46`), the count `x.qs6` (`Carry6`), and `certify_stack`'s data and placed stack (`StkAt`, from
  its pinned call `Ret1.cs` and returns `Ret1.r485 … r487`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Guest.B1.Link
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## The announced layout is `buildLayout`'s -/

theorem sizesOf_build {bytecode : List K} {a : List E} {layout : Layout} {r : ℕ}
    (h : sizesOf bytecode a = some (layout, r)) :
    buildLayout bytecode layout.logMemory layout.tableRows = some layout := by
  unfold sizesOf at h
  split at h
  · dsimp only at h
    split at h
    · obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨e1, e2, -⟩ := buildLayout_fields hl
        rw [e1, e2]
        exact hl
      · cases h
    · cases h
  · cases h

/-- **The announced layout is the one `buildLayout` gives on its sizes.** -/
theorem announced_build {bytecode : List K} {stream : List E} {layout : Layout} {r : ℕ}
    (h : announcedLayoutAndRate bytecode stream = some (layout, r)) :
    buildLayout bytecode layout.logMemory layout.tableRows = some layout :=
  sizesOf_build (announced_words h).2

/-! ## The front's link-shape word -/

/-- `.n 408` is the shape's first word, the tables' largest height. -/
theorem vsVal_408 {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {b9 n wd : ℕ} {flag f4 : E}
    (hw9 : w 9 = ptrAt b9) (r9 : ReadsAt rd0 (ptrAt b9) [gen ^ n, gen ^ wd, flag, f4]) :
    vsVal rd0 w args (.n 408) = gen ^ n := by
  have hg := vsB0_good (rd0 := rd0) (w := w) ha
  have p9 : vsVal rd0 w args (.n 9) = ptrAt b9 :=
    (vsW0_good ha (a := .hint (.alloc (.n 9) 4)) (by simp [vsW0, vsW0a])).trans hw9
  have fr := vsB0_fresh
  rw [Bool.and_eq_true] at fr
  have hn : Atom.load (.n 408) (.n 9) 0 ∉ storesOf 240 vsB := fun h' => by
    have := List.all_eq_true.mp fr.2 (Atom.load (.n 408) (.n 9) 0) (by simp)
    rw [List.contains_iff_mem.mpr h'] at this
    exact absurd this (by decide)
  exact good_loadAt hn (hg _ (vsSh_mem (by simp [vsSh]))) p9 (by simp) r9

/-- `.n 694` points at `.n 10`'s word `89 + n` (the index side's `z` words). -/
theorem vsVal_694 {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {b10 n : ℕ}
    (h10 : vsVal rd0 w args (.n 10) = ptrAt b10) (h408 : vsVal rd0 w args (.n 408) = gen ^ n) :
    vsVal rd0 w args (.n 694) = ptrAt (b10 + 89 + n) := by
  have hgC := vsVal_goodC (rd := rd0) (w := w) ha
  have m7 : ∀ a ∈ vsC7q, Stmt.atom a ∈ vsC := fun a h =>
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [vsC7_eq]; exact List.mem_append_right _ (List.mem_map_of_mem h)))
  have hg7 : ∀ a ∈ vsC7q, Good rd0 (storesOf 482 vsC) w (vsVal rd0 w args) a := fun a h => hgC (.atom a) (m7 a h)
  have m9 : ∀ a ∈ vsC9a, Stmt.atom a ∈ vsC := fun a h =>
    List.mem_of_mem_drop (List.mem_of_mem_take (by
      rw [vsC9_eq]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem h))))
  have hg9 : ∀ a ∈ vsC9a, Good rd0 (storesOf 482 vsC) w (vsVal rd0 w args) a := fun a h => hgC (.atom a) (m9 a h)
  have e679 : vsVal rd0 w args (.n 679) = ptrAt (b10 + 1) := by
    rw [good_mulF (hg7 (.mul (.n 679) (.n 10) (.n 678)) (by simp [vsC7q])) (by omega) (by omega), h10,
      show vsVal rd0 w args (.n 678) = word 2 0 from hg7 (.const (.n 678) (word 2 0)) (by simp [vsC7q]),
      show word 2 0 = gen ^ 1 from wordG (j := 1) (by norm_num), ptrAt_add]
  rw [show b10 + 89 + n = b10 + 1 + 88 + n by omega,
    good_mulF (hg9 (.mul (.n 694) (.n 693) (.n 408)) (by simp [vsC9a])) (by omega) (by omega),
    good_mulF (hg9 (.mul (.n 693) (.n 679) (.n 692)) (by simp [vsC9a])) (by omega) (by omega), e679,
    show vsVal rd0 w args (.n 692) = word 452984832 0 from hg9 (.const (.n 692) _) (by simp [vsC9a]),
    show word 452984832 0 = gen ^ 88 from pkC_eq, h408, ptrAt_add, ptrAt_add]

/-- **The packing check** on the link's shape: `f4^8 / (g^n·c·g^w·g^chunkCount w) = 2^j`, `j < 8`. -/
theorem vsPk {n wd : ℕ} (hn : n ≤ 24) (hw1 : 19 ≤ wd) (hw : wd ≤ 24) :
    (packedChallenges tables n wd + 7) / 8 < 64 ∧
    ∃ jj < 8, (gen ^ ((packedChallenges tables n wd + 7) / 8)) ^ 8 *
      (gen ^ n * pkC * gen ^ wd * gen ^ chunkCount wd)⁻¹ = word (2 ^ jj) 0 := by
  have hc := chal_fits hn hw1 hw
  have h153 : guest_const% LINK_CHAL_CAP = 153 := rfl
  rw [h153] at hc
  have e := packedChallenges_eq n wd
  have h88 : guest_const% LINK_FIXED = 88 := rfl
  rw [h88] at e
  obtain ⟨v1, v2⟩ := packed_vanish (packedChallenges tables n wd)
  refine ⟨by omega, 8 * ((packedChallenges tables n wd + 7) / 8) - packedChallenges tables n wd, v2, ?_⟩
  rw [pkC_eq, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, wordG (by omega),
    show n + 88 + wd + chunkCount wd = packedChallenges tables n wd by omega,
    show (packedChallenges tables n wd + 7) / 8 * 8 = 8 * ((packedChallenges tables n wd + 7) / 8) by ring]
  exact gen_div v1

/-! ## The posts after the front -/

theorem vsPs_drop_take5 (σ : Val) (ch stk mk : List Pop) :
    ((vsPs σ ch stk mk).drop (if σ (.n 471) = 0 then 11 else 10)).take 5 = [[], stk, [], [], []] := by
  unfold vsPs
  split_ifs <;> rfl

/-- **`Bnd` through `Ph4 … Ph6`**: the posts `[quiet, stack, quiet, quiet, quiet]` after the front's. -/
theorem VsCtx.Bnd.ph46 {x : VsCtx} {r : ℕ} (hann : announcedLayoutAndRate guestBytecode x.c.proof.stream = some (x.lay, r))
    {st : St} (hb : x.Bnd st) (hl : st.Qs.length = if x.σ0 (.n 471) = 0 then 11 else 10)
    {kc : ℕ} {O : Reader → Prop} {D : ℕ → Prop} {Qc : Reader → Tree → Prop}
    (hkc : st.kc ≤ kc) (hO : ∀ rd, O rd → st.O rd)
    (hQc : ∀ rd t, Qc rd t →
      t.pops coreProgram rd = Prover.stackHints (stackKappas x.lay) ∧ t.Every (ExactAt coreProgram rd)) :
    x.Bnd ⟨st.a, kc, O, D, st.Qs ++ [PostQuiet, Qc] ++ [PostQuiet, PostQuiet] ++ [PostQuiet]⟩ := by
  refine ⟨hb.ha, le_trans hb.hkc hkc, fun rd h => hb.hO rd (hO rd h), fun rd hl0 hp ho => ?_⟩
  have h := hb.hQ rd hl0 hp (hO rd ho)
  have e : st.Qs ++ [PostQuiet, Qc] ++ [PostQuiet, PostQuiet] ++ [PostQuiet] =
      st.Qs ++ [PostQuiet, Qc, PostQuiet, PostQuiet, PostQuiet] := by simp
  show List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t)
    (st.Qs ++ [PostQuiet, Qc] ++ [PostQuiet, PostQuiet] ++ [PostQuiet])
    ((vsPsH x.seed x.c (rdOver x.σ0 rd)).take
      (st.Qs ++ [PostQuiet, Qc] ++ [PostQuiet, PostQuiet] ++ [PostQuiet]).length)
  rw [e]
  simp only [vsPsH, hann] at h ⊢
  have e471 : rdOver x.σ0 rd (.n 471) = x.σ0 (.n 471) := rdOver_eq (by decide +kernel)
  have hL := vsPs_drop_take5 (rdOver x.σ0 rd) (vsChunks x.c.proof.stream) (Prover.stackHints (stackKappas x.lay))
    (Prover.merkleHints true (Prover.childQueries guestBytecode x.seed x.c) x.c.proof.openings)
  rw [e471, ← hl] at hL
  rw [List.length_append, List.take_add,
    show [PostQuiet, Qc, PostQuiet, PostQuiet, PostQuiet].length = 5 from rfl, hL]
  exact List.rel_append h (.cons (fun _ h => popsPost_quiet h) (.cons (fun t h => popsPost_eq (hQc rd t h))
    (.cons (fun _ h => popsPost_quiet h) (.cons (fun _ h => popsPost_quiet h)
      (.cons (fun _ h => popsPost_quiet h) .nil)))))

/-! ## The phases -/

section
variable {x : VsCtx}

theorem VsCtx.base_4 : x.base 4 = x.cur + 190 := by
  rw [x.base_eq, vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

theorem VsCtx.base_16 : x.base 16 = x.cur + 793 := by
  rw [x.base_eq, vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

theorem VsCtx.base_17 : x.base 17 = x.cur + 823 := by
  rw [x.base_eq, vsBaseF_eq _ _ _ (by norm_num), vsAllocSz_take_sum _ _ (by norm_num)]
  simp only [vsSz0, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, List.sum_cons,
    List.sum_nil]
  omega

theorem VsCtx.allocSz_sum (x : VsCtx) : (vsAllocSz x.p).sum = 982 + 256 * x.p := by
  simp only [vsAllocSz, vsSz0, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]; omega

theorem foldl_add_nat : ∀ (l : List ℕ) (a : ℕ), l.foldl (· + ·) a = a + l.sum
  | [], a => by simp
  | y :: l, a => by rw [List.foldl_cons, foldl_add_nat l, List.sum_cons]; omega

/-- The link shape's fourth word is `g^pk`. -/
theorem VsCtx.f4_eq (x : VsCtx) : x.f4 = gen ^ x.pk := by
  have e : x.lay.tableRows.sum = cyclesOf x.lay := by
    unfold cyclesOf; rw [foldl_add_nat, zero_add]
  have c : ∀ n, Prover.count n = gen ^ n := fun n => by simp [Prover.count, LeanVM.Protocol.Verifier.gpow]
  show (vsLinkShape x.lay).getD 3 0 = _
  rw [vsLinkShape, e]
  exact c _

end

/-- **A table's bits pointer past the previous one**: a run of `vsA` holding `.const (.n m) (g^26)` and
`.mul (.n d) (.n pv) (.n m)` puts `.n d` at `.n pv`'s pointer plus `26`. -/
theorem vsA_ptr26 {rd0 : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) {i n : ℕ} {as : List Atom}
    (h : (vsA.drop i).take n = as.map Stmt.atom) {d pv m c : ℕ}
    (h1 : Atom.const (.n m) (word 67108864 0) ∈ as) (h2 : Atom.mul (.n d) (.n pv) (.n m) ∈ as)
    (hpv : pv < d) (hmd : m < d) (hp : vsVal rd0 w args (.n pv) = ptrAt c) :
    vsVal rd0 w args (.n d) = ptrAt (c + 26) := by
  have g := vsA_run_goodF (rd0 := rd0) (w := w) ha h
  have h14 : vsVal rd0 w args (.n m) = gen ^ 26 := (g _ h1).trans (wordG (j := 26) (by norm_num))
  have := g _ h2
  have hc : (V.n pv).idx < (V.n d).idx ∧ (V.n m).idx < (V.n d).idx := ⟨hpv, hmd⟩
  simp only [fixA, Good, hc, and_self, ↓reduceIte] at this
  rw [this, hp, h14, ptrAt_add]

/-- **`Ph4to6S`**: `wC`'s phases 4 to 6 at every honest context. -/
theorem ph4to6S (al : String → Bool) : Ph4to6S al := by
  intro x hal hx _ Own hown st K hb hF hK
  subst hal
  rcases st with ⟨sa, skc, sO, sD, sQs⟩
  obtain ⟨hkF, hlF⟩ := hF
  dsimp only at hkF hlF
  subst hkF
  obtain ⟨layout, r, hann, hS, hN⟩ := frontNum_of_child hx.ok.child
  have hlay : x.lay = layout := by simp [VsCtx.lay, hann]
  rw [← hlay] at hN hann hS
  have hrr : (announcedLayoutAndRate guestBytecode x.c.proof.stream |>.map Prod.snd |>.getD 0) = r := by
    simp [hann]
  have ha : x.args.length = 6 := rfl
  have hr := hx.hret
  have hb1 := hx.bw1
  have hr1 := hx.ret1
  have F := hx.fs1
  have hR : FrontRet x.ret r x.lay.logMemory x.hg x.rows := by
    have := hr1.front; unfold VsCtx.Ret1F at this; rwa [hrr] at this
  have H := frontHyp_honest (fs := B2C.fs) (al := x.al) (cert := B2C.cert) (k := 17) (rd1 := x.rd1)
    (seed := x.seed) (c := x.c) (qt := x.qt) (qo := x.qo) (nc := x.c.freshClaim.cells.length)
    (f4 := x.f4) (st := x.st0B) hN hr hR (fun i h1 h2 => hown i ⟨h1, h2⟩) rfl (x.pre_rd0F hx)
    (x.front_holds hb1.front fun j hj => x.reads_rd0 hx hj)
    (fun rd hrd => x.front_holds hb1.front fun j hj => readsAt_of_mem hrd (x.mem_WoF hx (by simp at hj; omega)
      (by simp at hj; omega)))
  have h409 := vsVal_409_of_front ha H
  have n408 : vsVal x.rd0 x.w x.args (.n 408) = gen ^ hMax x.lay := vsVal_408 ha H.hw9 H.r0.shape
  obtain ⟨v115, v116, v117, v118, v119, v120, -⟩ := vsW6_vals (rd0 := x.rd0) (w := x.w) (args := x.args) ha H.hw6 H.hw56 (bs := rowsW x.rows)
    (by simp [rowsW]) H.r0.heights H.r0.sizes
  have hp := x.p_leF hx
  have hp1 : 1 ≤ x.p := hN.hp1
  have hcur := hx.ok.hcur
  have hsum := x.allocSz_sum
  have hkc := hb.hkc
  dsimp only at hkc
  have hqt := hx.ok.ht
  have hfc := hx.ok.hfc
  have e4 : expTabLen = 2226 := expTabLen_eq
  have hn24 : hMax x.lay ≤ 24 := by obtain ⟨t, ht, e⟩ := hN.hn; rw [← e]; exact hN.h24 t ht
  have b3 : x.base 3 = x.cur + 186 := vsBaseF_3 _ _
  have b4 : x.base 4 = x.cur + 190 := VsCtx.base_4
  have b16 : x.base 16 = x.cur + 793 := VsCtx.base_16
  have b17 : x.base 17 = x.cur + 823 := VsCtx.base_17
  have b18 : x.base 18 = x.cur + 824 := vsBaseF_18 _ _
  have b20 : x.base 20 = x.cur + (824 + 256 * x.p) + 6 := vsBaseF_20 _ _
  have own : ∀ i, x.cur ≤ i → i < x.cur + 982 + 256 * x.p → Own i := fun i h1 h2 => hown i ⟨h1, by omega⟩
  have hWo : ∀ {rd : Reader} {j : ℕ}, j < 24 → j ≠ 13 → (∀ rd', sO rd' → HoldsWords rd' x.Wo) →
      sO rd → ReadsAt rd (ptrAt (x.base j)) (x.bw.getD j []) := fun hj h13 hO ho =>
    readsAt_of_mem (hO _ ho) (x.mem_WoF hx hj h13)
  have alloc : ∀ {j v n : ℕ}, j < 18 → vsAllocIdx.getD j 0 = v → Atom.hint (.alloc (.n v) n) ∈ vsW0 →
      vsVal x.rd0 x.w x.args (.n v) = ptrAt (x.base j) := fun hj hv hm =>
    (vsW0_good ha hm).trans ((vsW_buf (rd1 := x.rd1) ha hr (j := _) (by omega) hv).trans rfl)
  have h10 : vsVal x.rd0 x.w x.args (.n 10) = ptrAt (x.base 4) :=
    alloc (j := 4) (n := 153) (by norm_num) rfl (by simp [vsW0, vsW0a])
  have hfresh : VsFresh x.rd1 x.rd0 (vsW x.rd1 x.args x.cur x.p x.ret) x.args := hx.fresh
  have win := vsW_gcWin (rd1 := x.rd1) (rd0 := x.rd0) (args := x.args) (cur := x.cur) (p := x.p) (ret := x.ret)
    ha hr hfresh
  have hRq : ∀ j < 2 ^ 11, x.R (x.qt + (j + 178)) := fun j hj => by
    rw [show (2 : ℕ) ^ 11 = 2048 from rfl] at hj
    unfold VsCtx.R vsRegion; left; omega
  -- Ph4: `chunk_d`, `certify_stack`
  have hst : x.frontEnd B2C.fs x.al ≤ x.fpc := by
    unfold VsCtx.fpc; exact le_trans le_leafEnd (le_allocBase _ _)
  have hwt : winTabAt + 2 ^ winTabBits = 2226 := rfl
  have hnt : nTables = 6 := rfl
  have hc4 := hr1.cs
  unfold CsCall at hc4
  have hce4 : x.fpc + B2C.fs "certify_stack" ≤ x.ec 4 := by obtain ⟨_, _, h, _⟩ := hc4; exact h
  refine ⟨widthOf x.lay, ptrAt (x.base 20), ptrAt x.qt, gen ^ x.lay.stackLog,
    ptrAt (csOffsAt (x.fpc + B2C.fs "certify_stack")), ptrAt (csOffsAt (x.fpc + B2C.fs "certify_stack") + 52),
    _, _, _, _, _, x.ec 4, ⟨hN.hw19, hN.hw24, h409, vsW_retC ha hr (by decide) hr1.r484,
      (vsA_run_good ha vsW6_eq vsW6_ne (.hint (.alloc (.n 112) 8)) (by simp [vsW6])).trans
        (vsW_buf (rd1 := x.rd1) ha hr (j := 20) (by norm_num) rfl),
      vsVal_param ha (i := 4) (by norm_num), vsW_retC ha hr (by decide) hr1.r485,
      vsW_retC ha hr (by decide) hr1.r486, vsW_retC ha hr (by decide) hr1.r487,
      hc4, ?_, ?_⟩, ?_⟩
  · rintro i (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [hwt] at h2
      exact Or.inl (Or.inl (Or.inl ⟨h1, by omega⟩))
    · rw [hnt] at h2
      exact Or.inl (Or.inr (own i (by omega) (by omega)))
  · rintro rd ⟨hp0, ho⟩
    refine ⟨(vsPreA_exp hp0).1, ?_⟩
    have := hWo (j := 20) (by norm_num) (by norm_num) hb.hO ho
    rw [hb1.front.b20] at this
    exact this
  -- Ph5: the out-of-domain grind and point, the opening message
  set ws := padStream x.c.proof.stream with hwsd
  have hwsl : ws.length = 256 * x.p := hN.hws
  have hs16 : 16 ≤ x.lay.stackLog := hS.stack_ge
  have hs30 : x.lay.stackLog ≤ 30 := hS.stack_le
  refine ⟨x.lay.stackLog, x.base 18, x.qt, x.base 16, x.base 17, ws, [ws.getD 11 0], ws.getD 12 0,
    ⟨hs16, hs30, vsW_retC ha hr (by decide) hr1.r485,
      (vsVal_55 ha).trans (vsW_buf (rd1 := x.rd1) ha hr (j := 18) (by norm_num) rfl), by omega,
      by have := x.reads_rd0 hx (j := 18) (by simp); rwa [hb1.front.b18] at this,
      fun rd ho => by have := hWo (j := 18) (by norm_num) (by norm_num) hb.hO ho.1; rwa [hb1.front.b18] at this,
      fun j hj => own _ (by omega) (by omega), vsVal_param ha (i := 4) (by norm_num), VsCtx.lowDef_rd0 (x := x) 17,
      (vsPreA_exp (x.pre_rd0F hx)).2, fun rd h => (vsPreA_exp h).2, hRq, win.1, F.hlow5,
      alloc (j := 16) (n := 30) (by norm_num) rfl (by simp [vsW0, vsW0a]),
      fun j hj => own _ (by omega) (by omega), F.hspf, ?_,
      alloc (j := 17) (n := 1) (by norm_num) rfl (by simp [vsW0, vsW0a]), own _ (by omega) (by omega), rfl,
      F.hom, ?_⟩, ?_⟩
  · rintro rd ⟨-, ho⟩
    have R16 := hWo (j := 16) (by norm_num) (by norm_num) hb.hO ho.1
    have := readsAt_sub (j := 0) (ys := x.σ0 (.n 499) :: x.spf.1) R16 fun k hk => by
      rw [Nat.zero_add]; exact F.hP22 k hk
    rwa [Nat.add_zero] at this
  · rintro rd ⟨-, ho⟩
    refine ⟨?_, ?_⟩
    · have R18 := hWo (j := 18) (by norm_num) (by norm_num) hb.hO ho.1
      rw [hb1.front.b18, ← hwsd] at R18
      refine readsAt_sub (j := 11) R18 fun k hk => ?_
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 11 < ws.length by omega)]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 12 < ws.length by omega)]
    · have := hWo (j := 17) (by norm_num) (by norm_num) hb.hO ho.1
      rwa [F.hP23] at this
  -- Ph6: the link grind, the packing check, `squeeze_packed`
  obtain ⟨-, jj, hjj, hpk⟩ := vsPk hn24 hN.hw19 hN.hw24
  have hpk19 : 8 * x.pk ≤ 152 := by
    have := chal_fits hn24 hN.hw19 hN.hw24
    have h153 : guest_const% LINK_CHAL_CAP = 153 := rfl
    rw [h153] at this
    unfold VsCtx.pk; omega
  set st5kc := leafEnd B2C.fs x.al (omName (1, 1)) (leafEnd B2C.fs x.al (spfName x.lay.stackLog) (x.ec 4)) with hst5
  have h5 : x.ec 4 ≤ st5kc := le_trans le_leafEnd le_leafEnd
  have hc6 : SpCall B2C.fs x.al B2C.cert 17 (x.w 575) (x.w 576) (x.w 577) (x.w 578) (x.w 579) (ptrAt (x.base 4 + 1))
      x.pk (allocBase (x.al "squeeze_packed") st5kc) (x.ec 6) := hr1.sp
  unfold SpCall at hc6
  have hce6 : allocBase (x.al "squeeze_packed") st5kc + B2C.fs "squeeze_packed" ≤ x.ec 6 := by
    obtain ⟨_, _, h, _⟩ := hc6; exact h
  have hc6' := CallAtA.idxR (arrs := [(x.base 4 + 1, (pkSqueeze x.pk [x.w 575, x.w 576, x.w 577, x.w 578, x.w 579]).1.length)]) hc6
  rw [← x.f4_eq, ← hr1.r680] at hc6'
  have e574 : vsVal x.rd0 x.w x.args (.n 574) = x.w 574 := (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC6_eq) (.n 574) (by simp)
  have hpk' : x.f4 ^ 8 * (gen ^ hMax x.lay * pkC * gen ^ widthOf x.lay * gen ^ chunkCount (widthOf x.lay))⁻¹ =
      word (2 ^ jj) 0 := by rw [x.f4_eq]; exact hpk
  refine ⟨x.qt, x.base 3, x.base 4, hMax x.lay, widthOf x.lay, chunkCount (widthOf x.lay), jj, x.f4,
    [gen ^ hMax x.lay, gen ^ widthOf x.lay, flagOf x.lay, x.f4], _, _, _, _, _, B2C.fs "squeeze_packed", x.ec 6,
    ⟨vsVal_param ha (i := 4) (by norm_num), VsCtx.lowDef_rd0 (x := x) 17, (vsPreA_exp (x.pre_rd0F hx)).2,
      fun rd h => (vsPreA_exp h).2, hRq, fun j hj => (win.2.1 j hj).trans (congrArg (fun v => gcWin 2 v j) e574), F.hlow6,
      alloc (j := 3) (n := 4) (by norm_num) rfl (by simp [vsW0, vsW0a]), by simp, rfl,
      by have := x.reads_rd0 hx (j := 3) (by simp); rwa [hb1.front.b3] at this,
      fun rd ho => by have := hWo (j := 3) (by norm_num) (by norm_num) hb.hO ho.1; rwa [hb1.front.b3] at this,
      own _ (by omega) (by omega),
      n408, h409, vsW_retC ha hr (by decide) hr1.r484, hjj, hpk',
      alloc (j := 4) (n := 153) (by norm_num) rfl (by simp [vsW0, vsW0a]), own _ (by omega) (by omega),
      fun rd _ ho => ?_, hc6', ?_, ?_⟩, hK _ ?_ ?_⟩
  · have R4 := hWo (j := 4) (by norm_num) (by norm_num) hb.hO ho.1
    obtain ⟨hl4, he4⟩ := List.getElem?_eq_some_iff.mp hb1.b4
    have := R4 0 hl4
    rwa [he4] at this
  · rintro i ⟨q, hq, t, ht, rfl⟩
    simp only [List.mem_singleton] at hq
    subst hq
    dsimp only at ht ⊢
    rw [pkSqueeze_length] at ht
    exact Or.inl (Or.inr (own _ (by omega) (by omega)))
  · rintro rd ⟨-, ho⟩
    have R4 := hWo (j := 4) (by norm_num) (by norm_num) hb.hO ho.1
    have := readsAt_sub (j := 1) (ys := (pkSqueeze x.pk [x.w 575, x.w 576, x.w 577, x.w 578, x.w 579]).1) R4
      fun k hk => by rw [Nat.add_comm]; exact hb1.b4s k hk
    exact this
  · refine VsCtx.Bnd.ph46 hann hb hlF ?_ (fun rd h => h.1.1) ?_
    · exact le_trans hst (le_trans (Nat.le_add_right _ _) (le_trans hce4 (le_trans h5
        (le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) hce6)))))
    · intro rd t h
      exact h
  · have sel : ∀ t, 1 ≤ t → t ≤ 5 → x.σ0 (.n (115 + t)) = gen ^ x.hgS t := by
      intro t h1 h5
      interval_cases t
      exacts [v116, v117, v118, v119, v120]
    have p7 : vsVal x.rd0 x.w x.args (.n 7) = ptrAt (x.base 1) :=
      alloc (j := 1) (n := 156) (by norm_num) rfl (by simp [vsW0, vsW0a])
    obtain ⟨-, e8, -, e10, -, e12, -, e14, -⟩ := vsA_tables_eq
    have p159 := vsA_ptr26 (rd0 := x.rd0) (w := x.w) ha e8 (d := 159) (pv := 7) (m := 158)
      (by simp [tsRun0]) (by simp [tsRun0]) (by norm_num) (by norm_num) p7
    have p175 := vsA_ptr26 (rd0 := x.rd0) (w := x.w) ha e10 (d := 175) (pv := 159) (m := 174)
      (by simp [tsRun, tsChk]) (by simp [tsRun, tsChk]) (by norm_num) (by norm_num) p159
    have p191 := vsA_ptr26 (rd0 := x.rd0) (w := x.w) ha e12 (d := 191) (pv := 175) (m := 190)
      (by simp [tsRun, tsChk]) (by simp [tsRun, tsChk]) (by norm_num) (by norm_num) p175
    have p207 := vsA_ptr26 (rd0 := x.rd0) (w := x.w) ha e14 (d := 207) (pv := 191) (m := 206)
      (by simp [tsRun, tsChk]) (by simp [tsRun, tsChk]) (by norm_num) (by norm_num) p191
    have bv : ∀ t, 1 ≤ t → t ≤ 5 → x.σ0 (.n (tpBv t)) = ptrAt (x.base 1 + 26 * (t - 1)) := by
      intro t h1 h5
      interval_cases t
      · exact p7.trans (congrArg ptrAt (by omega))
      · exact p159.trans (congrArg ptrAt (by omega))
      · exact p175.trans (congrArg ptrAt (by omega))
      · exact p191.trans (congrArg ptrAt (by omega))
      · exact p207.trans (congrArg ptrAt (by omega))
    refine ⟨?_, ⟨n408, h409, vsW_retC ha hr (by decide) hr1.r484, vsVal_694 ha h10 n408,
      (vsVal_call_ret ha vsW5_eq (.n 101) (List.mem_singleton_self _)).trans H.hw101, v115, sel, bv⟩, rfl, ?_⟩
    · show (sQs ++ [PostQuiet, _] ++ [PostQuiet, PostQuiet] ++ [PostQuiet]).length = x.qs6
      simp only [List.length_append, List.length_cons, List.length_nil, hlF, VsCtx.qs6]
      split_ifs <;> rfl
    · -- `certify_stack`'s data and placed stack, at its returns
      have e485 : x.σ0 (.n 485) = gen ^ x.lay.stackLog :=
        (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC2_eq (.n 485) (by simp)).trans
          (vsW_retC ha hr (by decide) hr1.r485)
      have e486 : x.σ0 (.n 486) = ptrAt (csOffsAt (x.fpc + B2C.fs "certify_stack")) :=
        (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC2_eq (.n 486) (by simp)).trans
          (vsW_retC ha hr (by decide) hr1.r486)
      have e487 : x.σ0 (.n 487) = ptrAt (csOffsAt (x.fpc + B2C.fs "certify_stack") + 52) :=
        (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC2_eq (.n 487) (by simp)).trans
          (vsW_retC ha hr (by decide) hr1.r487)
      refine ⟨fun i hi => Or.inl (Or.inr hi), fun rd _ ho => ?_⟩
      obtain ⟨⟨-, h4⟩, -⟩ := ho
      rw [e485, e486, e487]
      exact h4

end
end LeanVM.Guest.B1.VsC
