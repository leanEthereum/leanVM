/-
  LeanVM.Guest.B1.VsC.VsNatHid

  The link terminal's identity at the honest context, from the link section's values.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatLt
public import LeanVM.Guest.B1.Link.Arith.Reads

/-!
# `D3.Ok.hid`, natively

The guest's chains and challenges at the honest context are the native link's:
* **`natChain_last_free`**: a chain's last capacity and claim do not depend on its cursor, so the guest's chains
  (`natLI`, `natLR`, `natLC`, at the stream's cursors) end on the native ends' claims once they start on the
  native claim;
* **`VsCtx.front_nat`**: `opening_message`'s `θ_0` (`w 573`) and capacity (`w 575 … 579`) are the native grind's,
  `squeeze_packed`'s count `pkCount nDrawn`; **`VsCtx.bw4_nat`**: `.n 10`'s words are `θ_0` then the native draws;
* **`VsCtx.zsS_nat`**, **`VsCtx.nu_nat`**: the index side's `ζ` and the terminal's `ν` are `tailLets`';
* **`VsCtx.clI_nat`**: the guest's index claim is `indexClaim` (`claimIdentity`);
* **`VsCtx.w1077_nat`**: the row side's last claim `w 1077` is the native `endC.cl`.

**`VsCtx.hid_nat`**: `D3.Ok.hid` from these and **`LinkSecVals`**, the link section's values at `σ0`: `coef`,
`cert_w·cert`, `rest` and the overlay's shift coefficients are `tailRowSide`'s and `tailLets`' at the native
values (`linkSecStatement`'s conclusions at `rd0`, `σ0`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Protocol.Link
open LeanVM.Guest.B1.Link.Arith (tailRowSide tailLets tailIn claimIdentity gClaim_unfold layoutOf)

@[expose] public section

/-! ## Chains: the last capacity and claim do not depend on the cursor -/

theorem natStep_free (nt bits : ℕ) {a b : RSt} (ws : List E) (hc : a.cap = b.cap) (hl : a.cl = b.cl) :
    (natStep nt bits a ws).2.cap = (natStep nt bits b ws).2.cap ∧
      (natStep nt bits a ws).2.cl = (natStep nt bits b ws).2.cl := by
  refine ⟨?_, ?_⟩ <;> simp only [natStep, natRoundFs, hc, hl]

/-- **A chain's last capacity and claim do not depend on its cursor.** -/
theorem natChain_last_free (nt bits : ℕ) : ∀ (k : ℕ) (a b : RSt) (ws : List E), a.cap = b.cap → a.cl = b.cl →
    (chainLast a (natChain nt bits k a ws)).cap = (chainLast b (natChain nt bits k b ws)).cap ∧
      (chainLast a (natChain nt bits k a ws)).cl = (chainLast b (natChain nt bits k b ws)).cl
  | 0, _, _, _, hc, hl => ⟨hc, hl⟩
  | k + 1, a, b, ws, hc, hl => by
    obtain ⟨h2, h3⟩ := natStep_free nt bits ws hc hl
    exact natChain_last_free nt bits k _ _ _ h2 h3

/-! ## The layout's slices -/

section
variable {layout : Layout} {chunks : Chunks} {theta0 : E} {drawn r : List E} {m1 : E} {fresh : List E}
  {split : Split} {qPoint : List E}

theorem lets_zeta' (htab : layout.tables = tables) (hd : 88 ≤ drawn.length) :
    (tailLets layout chunks theta0 drawn r m1 fresh split qPoint).zeta =
      ((drawn.drop 88).drop (linkRows layout)).take chunks.width := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab
  subst htab
  exact Link.Arith.lets_zeta hd

theorem lets_nu' (htab : layout.tables = tables) (hd : 88 ≤ drawn.length) :
    (tailLets layout chunks theta0 drawn r m1 fresh split qPoint).nu =
      (((drawn.drop 88).drop (linkRows layout)).drop chunks.width).take chunks.d := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab
  subst htab
  exact Link.Arith.lets_nu hd

theorem linkDrawn_eq' (htab : layout.tables = tables) (hch : Chunks.new chunks.width = some chunks) :
    linkDrawn layout chunks = 88 + linkRows layout + chunks.width + chunks.d := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab
  subst htab
  rw [Link.Arith.linkDrawn_eq, hch]
  rfl

end

theorem foldl_add6 {l : List ℕ} (h : l.length = 6) :
    l.foldl (· + ·) 0 = l.getD 0 0 + l.getD 1 0 + l.getD 2 0 + l.getD 3 0 + l.getD 4 0 + l.getD 5 0 := by
  match l, h with
  | [a, b, c, d, e, f], _ => simp [List.foldl]

theorem word_one_eq : word 1 0 = (1 : E) := by decide +kernel

theorem word_gpow19 : word 12261764870545049476 0 = gpowE (2 ^ 19 - 1) := by decide +kernel

theorem lrClaim_eq (a b x6 x7 : E) :
    lrClaim a b x6 x7 = a * (1 + x6 + x7) + b * (1 + x6 * gpowE (2 ^ 19 - 1) + x7) := by
  rw [lrClaim, word_one_eq, word_gpow19]

/-! ## At the context -/

section
variable {x : VsCtx} {L : LinkNat}

set_option maxHeartbeats 1000000 in
/-- **`opening_message`'s `θ_0` and capacity are the native grind's**, `squeeze_packed`'s count the native draws'. -/
theorem VsCtx.front_nat {rest : List E} (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (htab : x.lay.tables = tables) (hch : Chunks.new (linkWidth x.lay) = some L.chunks) (hbits : L.bits x.lay ≠ 0)
    (hfs : VsFsChecks1 x)
    (hood : [x.σ0 (.n 507), x.σ0 (.n 508), x.σ0 (.n 509), x.σ0 (.n 510), x.σ0 (.n 511)] =
      capOf (natOodS x.seed x.c)) :
    x.w 573 = L.theta0 x.lay x.nF ∧ [x.w 575, x.w 576, x.w 577, x.w 578, x.w 579] = L.cap1 x.lay x.nF ∧
      x.pk = pkCount (L.nDrawn x.lay) := by
  have hw' : x.c.proof.stream.drop 12 = L.n0 :: (L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ rest)))) := by
    rw [hw]; simp [LinkNat.words, grindWords, hbits]
  have hl : 13 ≤ x.c.proof.stream.length := by
    have := congrArg List.length hw'; simp at this; omega
  have h11 : (padStream x.c.proof.stream).getD 11 0 = x.c.proof.stream.getD 11 0 := padStream_getDF (by omega)
  have h12 : (padStream x.c.proof.stream).getD 12 0 = L.n0 := by
    rw [padStream_getDF (by omega), show x.c.proof.stream.getD 12 0 = (x.c.proof.stream.drop 12).getD 0 0 by
      simp [List.getD_eq_getElem?_getD], hw']
    rfl
  have hpk : x.pk = pkCount (L.nDrawn x.lay) := by
    unfold VsCtx.pk pkCount LinkNat.nDrawn linkDrawn
    rw [htab, VerifySub.chunks_width hch]
    rfl
  have e1 : (⟨[x.w 566, x.w 567, x.w 568, x.w 569, x.w 570], []⟩ : Fs) =
      ((⟨capOf (natOodS x.seed x.c), []⟩ : Fs).squeezeN (x.lay.stackLog - 1)).2 := by
    rw [hfs.hspf, VsCtx.spf, hood]
    exact (squeezeN_emp _ _).symm
  have hS : omState [x.w 566, x.w 567, x.w 568, x.w 569, x.w 570] [(padStream x.c.proof.stream).getD 11 0]
      (some ((padStream x.c.proof.stream).getD 12 0)) = x.nF.nonceState L.n0 := by
    show (((⟨[x.w 566, x.w 567, x.w 568, x.w 569, x.w 570], []⟩ : Fs).absorbAll _ dsObserve).nonceState _) = _
    rw [e1, h11, h12]
    rfl
  have h := hfs.hom
  rw [omRets_eq, hS] at h
  simp only [List.cons.injEq] at h
  obtain ⟨h573, -, h575, h576, h577, h578, h579, -⟩ := h
  refine ⟨?_, ?_, hpk⟩
  · rw [h573, LinkNat.theta0, Fs.grindSqueeze_pos _ hbits]
    rfl
  · rw [LinkNat.cap1, Fs.grindSqueeze_pos _ hbits, h575, h576, h577, h578, h579]
    rfl

/-- **`.n 10`'s words**: `θ_0`, then the native draws. -/
theorem VsCtx.bw4_nat (hb1 : x.Bw1) (e573 : x.w 573 = L.theta0 x.lay x.nF)
    (ecap : [x.w 575, x.w 576, x.w 577, x.w 578, x.w 579] = L.cap1 x.lay x.nF)
    (hpk : x.pk = pkCount (L.nDrawn x.lay)) :
    (x.bw.getD 4 [])[0]? = some (L.theta0 x.lay x.nF) ∧
      ∀ k < L.nDrawn x.lay, (x.bw.getD 4 [])[k + 1]? = (L.drawn x.lay x.nF)[k]? := by
  refine ⟨by rw [hb1.b4, e573], fun k hk => ?_⟩
  have hl : k < (Link.pkSqueeze x.pk [x.w 575, x.w 576, x.w 577, x.w 578, x.w 579]).1.length := by
    rw [Link.pkSqueeze_length, hpk, pkCount]; omega
  rw [hb1.b4s k hl, ecap, hpk, LinkNat.drawn]
  simp only [List.getElem?_take, hk, ↓reduceIte]

/-- `.n 10`'s word `k + 1` within the draws. -/
theorem VsCtx.bw4_getD (h : ∀ k < L.nDrawn x.lay, (x.bw.getD 4 [])[k + 1]? = (L.drawn x.lay x.nF)[k]?) {k : ℕ}
    (hk : k < L.nDrawn x.lay) : (x.bw.getD 4 []).getD (k + 1) 0 = (L.drawn x.lay x.nF).getD k 0 := by
  show ((x.bw.getD 4 [])[k + 1]?).getD 0 = ((L.drawn x.lay x.nF)[k]?).getD 0
  rw [h k hk]

theorem drawn_length (layout : Layout) (F : Fs) : (L.drawn layout F).length = L.nDrawn layout := by
  rw [LinkNat.drawn, List.length_take, Link.pkSqueeze_length, pkCount]; omega

/-- A slice of `.n 10` past `θ_0` is the draws'. -/
theorem VsCtx.bw4_slice (h : ∀ k < L.nDrawn x.lay, (x.bw.getD 4 [])[k + 1]? = (L.drawn x.lay x.nF)[k]?)
    {a n : ℕ} (ha : a + n ≤ L.nDrawn x.lay) :
    ((x.bw.getD 4 []).drop (a + 1)).take n = ((L.drawn x.lay x.nF).drop a).take n := by
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop]
  split_ifs with hi
  · rw [show a + 1 + i = (a + i) + 1 by omega, h _ (by omega)]
  · rfl

/-- **The index side's `ζ` is `tailLets`'**. -/
theorem VsCtx.zsS_nat {fc : FreshClaim} {link : LinkEnd} (hL : L.Ok x.lay x.nF fc link)
    (htab : x.lay.tables = tables)
    (h : ∀ k < L.nDrawn x.lay, (x.bw.getD 4 [])[k + 1]? = (L.drawn x.lay x.nF)[k]?)
    {theta0 m1 : E} {r fresh qPoint : List E} {split : Split} :
    x.zsS = (tailLets x.lay L.chunks theta0 (L.drawn x.lay x.nF) r m1 fresh split qPoint).zeta := by
  have hw : L.chunks.width = x.wdS := VerifySub.chunks_width hL.chunks
  have hD := linkDrawn_eq' htab (hw ▸ hL.chunks : Chunks.new L.chunks.width = some L.chunks)
  have hdl := drawn_length (L := L) x.lay x.nF
  rw [lets_zeta' htab (by unfold LinkNat.nDrawn at hdl; omega), List.drop_drop, VsCtx.zsS, hw,
    show 89 + x.nS = (88 + linkRows x.lay) + 1 from by rw [VsCtx.nS, hMax_eq_linkRows]; omega]
  exact x.bw4_slice h (a := 88 + linkRows x.lay) (n := x.wdS) (by unfold LinkNat.nDrawn; rw [hD]; omega)

/-- **The terminal's `ν` is `tailLets`'**. -/
theorem VsCtx.nu_nat {fc : FreshClaim} {link : LinkEnd} (hL : L.Ok x.lay x.nF fc link)
    (htab : x.lay.tables = tables)
    (h : ∀ k < L.nDrawn x.lay, (x.bw.getD 4 [])[k + 1]? = (L.drawn x.lay x.nF)[k]?)
    {theta0 m1 : E} {r fresh qPoint : List E} {split : Split} :
    ((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take L.chunks.d =
      (tailLets x.lay L.chunks theta0 (L.drawn x.lay x.nF) r m1 fresh split qPoint).nu := by
  have hw : L.chunks.width = x.wdS := VerifySub.chunks_width hL.chunks
  have hD := linkDrawn_eq' htab (hw ▸ hL.chunks : Chunks.new L.chunks.width = some L.chunks)
  have hdl := drawn_length (L := L) x.lay x.nF
  rw [lets_nu' htab (by unfold LinkNat.nDrawn at hdl; omega), List.drop_drop, List.drop_drop, hw,
    show 89 + x.nS + x.wdS = (88 + linkRows x.lay + x.wdS) + 1 from by rw [VsCtx.nS, hMax_eq_linkRows]; omega]
  rw [show 88 + (linkRows x.lay + x.wdS) = 88 + linkRows x.lay + x.wdS by omega]
  exact x.bw4_slice h (a := 88 + linkRows x.lay + x.wdS) (n := L.chunks.d)
    (by unfold LinkNat.nDrawn; rw [hD]; omega)

/-- **The guest's index claim is `indexClaim`.** -/
theorem VsCtx.clI_nat {fc : FreshClaim} {link : LinkEnd} (hL : L.Ok x.lay x.nF fc link)
    (htab : x.lay.tables = tables) (hlb : x.lay.logBytecode = 19) (hrl : x.lay.tableRows.length = 6)
    (hw24 : x.wdS ≤ 24) (hb1 : x.Bw1) (h : ∀ k < L.nDrawn x.lay, (x.bw.getD 4 [])[k + 1]? = (L.drawn x.lay x.nF)[k]?) :
    x.clI = L.claimI x.lay x.nF := by
  have hw : L.chunks.width = x.wdS := VerifySub.chunks_width hL.chunks
  have hD := linkDrawn_eq' htab (hw ▸ hL.chunks : Chunks.new L.chunks.width = some L.chunks)
  set Lz := (tailLets x.lay L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF) (L.r x.lay x.nF) L.m1
    (L.fresh x.lay x.nF) (Split.ofColumns tables fc.values) (L.qPoint x.lay x.nF)).zeta with hLz
  have hz : x.zsS = Lz := x.zsS_nat hL htab h
  have hdl := drawn_length (L := L) x.lay x.nF
  have hzl : Lz.length = x.wdS := by
    rw [hLz, lets_zeta' htab (by unfold LinkNat.nDrawn at hdl; omega), List.length_take, List.length_drop,
      List.length_drop, hdl, hw]
    unfold LinkNat.nDrawn; rw [hD]; omega
  have hcyc : (x.bw.getD 2 []).take x.wdS = bitsE (linkCycles x.lay) x.wdS := by
    rw [hb1.front.b2, cbL, bitsE, ← List.map_take, List.take_range, Nat.min_eq_left hw24, linkCycles,
      foldl_add6 hrl]
    rfl
  have e6 : (x.bw.getD 4 []).getD 6 0 = (L.drawn x.lay x.nF).getD 5 0 :=
    x.bw4_getD h (by unfold LinkNat.nDrawn; rw [hD]; omega)
  have e7 : (x.bw.getD 4 []).getD 7 0 = (L.drawn x.lay x.nF).getD 6 0 :=
    x.bw4_getD h (by unfold LinkNat.nDrawn; rw [hD]; omega)
  rw [VsCtx.clI, LinkNat.claimI, ← claimIdentity x.lay L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF)
    (L.r x.lay x.nF) L.m1 (L.fresh x.lay x.nF) fc.values (L.chi x.lay x.nF) (L.qPoint x.lay x.nF) L.msg hlb,
    gClaim_unfold, lrClaim_eq, e6, e7, hcyc, hz, ← linkEqAt_zero_eq, ← hzl, ← linkEqAt_eq_endsProd]


theorem take_drop80 {l m : List E} {a : ℕ} (h : (l.drop a).take 144 = m) : (l.drop (a + 80)).take 64 = m.drop 80 := by
  subst h
  refine List.ext_getElem? fun i => ?_
  simp only [List.getElem?_take, List.getElem?_drop]
  by_cases hi : i < 64
  · rw [ite_eq_left hi, ite_eq_left (by omega), Nat.add_assoc]
  · rw [ite_eq_right hi, ite_eq_right (by omega)]

/-- **The row side's last claim is the native `endC.cl`**, once the guest's index claim is the native one: the
guest's chains differ from the native ones only in their cursors. -/
theorem VsCtx.w1077_nat (hret : CausalRule x.ret) (hcl : x.clI = L.claimI x.lay x.nF)
    (hw0 : L.chunks.width ≠ 0) (hR0 : linkRows x.lay ≠ 0) (hq0 : linkQVars x.lay ≠ 0)
    (r1071 : ∀ j < 7, ∀ σ, x.ret (1071 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.getD j 0) :
    x.w 1077 = (L.endC x.lay x.nF).cl := by
  have e : x.w 1077 = (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.getD 6 0 :=
    vsW_retC (rfl : x.args.length = 6) hret (by decide) (r1071 6 (by norm_num))
  have hI : (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl = (L.endI x.lay x.nF).cl := by
    rw [chainLast_ne (l := x.natLI L) (natChain_ne hw0 _ _) _ ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩]
    exact (natChain_last_free 1 0 _ ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩ ⟨L.cap2 x.lay x.nF, 0, L.claimI x.lay x.nF⟩
      L.wsI rfl hcl).2
  have hR : (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cl = (L.endR x.lay x.nF).cl := by
    rw [chainLast_ne (l := x.natLR L) (natChain_ne hR0 _ _) _
      ⟨L.cap4 x.lay x.nF, ptrAt (x.natB772 L + 1), (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl⟩]
    exact (natChain_last_free _ _ _ ⟨L.cap4 x.lay x.nF, ptrAt (x.natB772 L + 1), (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl⟩
      ⟨L.cap4 x.lay x.nF, 0, (L.endI x.lay x.nF).cl⟩ L.wsR rfl hI).2
  have hC : (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cl = (L.endC x.lay x.nF).cl := by
    rw [chainLast_ne (l := x.natLC L) (natChain_ne hq0 _ _) _
      ⟨(L.endR x.lay x.nF).cap, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cur, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cl⟩]
    exact (natChain_last_free _ _ _
      ⟨(L.endR x.lay x.nF).cap, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cur, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cl⟩
      ⟨(L.endR x.lay x.nF).cap, 0, (L.endR x.lay x.nF).cl⟩ L.wsC rfl hR).2
  have hc5 : (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cap.length = 5 := natChain_last_cap hq0 _ _ _
  rw [e, cells_getD_6 hc5, hC]

end

/-! ## The link section's values, and the identity -/

/-- `tailLets` at the native link's values. -/
noncomputable def natLets (x : VsCtx) (L : LinkNat) : Link.Arith.TailLets :=
  tailLets x.lay L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF) (L.r x.lay x.nF) L.m1 (L.fresh x.lay x.nF)
    (Split.ofColumns tables x.c.freshClaim.values) (L.qPoint x.lay x.nF)

/-- `tailRowSide` at the native link's values. -/
noncomputable def natRow (x : VsCtx) (L : LinkNat) :=
  tailRowSide x.lay L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF) (L.r x.lay x.nF) L.m1 (L.fresh x.lay x.nF)
    (Split.ofColumns tables x.c.freshClaim.values) (L.chi x.lay x.nF) (L.qPoint x.lay x.nF) L.msg

/-- **The link section's values at `σ0`** (`linkSecStatement`'s conclusions at `rd0`, `σ0` and the native
link's values): `coef`, `cert_w·cert`, `rest`, and the shift coefficients the overlay writes at `.n 19`. -/
structure LinkSecVals (x : VsCtx) (L : LinkNat) : Prop where
  coef : x.σ0 (.n 2846) = (natRow x L).coef
  certW : x.σ0 (.n 2891) = (natRow x L).certWeight * (natLets x L).cert
  rest : x.σ0 (.n 2890) = prodE ((L.qPoint x.lay x.nF).map (1 + ·)) * (natRow x L).base
  shifts : x.cells19.map Prod.snd = (natRow x L).shifts

section
variable {x : VsCtx} {L : LinkNat}

/-- **`D3.Ok.hid` at the honest context**: from the native link's facts, the honest buffers `4` (vsph1's `Bw1`),
`6` (`BwNat.b6`), `18`, the honest returns `1071 + j`, and the link section's values `LinkSecVals`. -/
theorem VsCtx.hid_nat {rest : List E} {link : LinkEnd} {D : D3}
    (hret : CausalRule x.ret) (hb1 : x.Bw1) (hfs : VsFsChecks1 x)
    (hood : [x.σ0 (.n 507), x.σ0 (.n 508), x.σ0 (.n 509), x.σ0 (.n 510), x.σ0 (.n 511)] =
      capOf (natOodS x.seed x.c))
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest) (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (htab : x.lay.tables = tables) (hlb : x.lay.logBytecode = 19) (hrl : x.lay.tableRows.length = 6)
    (hw19 : 19 ≤ x.wdS) (hw24 : x.wdS ≤ 24) (hR0 : linkRows x.lay ≠ 0)
    (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream) (hb6 : x.bw.getD 6 [] = padTo 24 (L.r x.lay x.nF))
    (r1071 : ∀ j < 7, ∀ σ, x.ret (1071 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cells.getD j 0)
    (hch : Chunks.new x.wdS = some D.ch) (hbm : D.bm = x.natBm L) (hsec : LinkSecVals x L) :
    LtIdentity D.ch x.σ0 (x.w 1077) ((x.bw.getD 6 []).take D.ch.width) (x.sw D.bm 80 64)
      (x.cells19.map Prod.snd) (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take D.ch.d) := by
  have hwd : L.chunks.width = x.wdS := VerifySub.chunks_width hL.chunks
  have hchL : D.ch = L.chunks := Option.some.inj (hch.symm.trans hL.chunks)
  have hbits : L.bits x.lay ≠ 0 :=
    grindingBits_ne (le_trans (by omega : 9 ≤ L.chunks.width + 1) (le_max_right _ _))
  obtain ⟨e573, ecap, hpk⟩ := x.front_nat hw htab hL.chunks hbits hfs hood
  obtain ⟨-, h4⟩ := x.bw4_nat hb1 e573 ecap hpk
  have hcl := x.clI_nat hL htab hlb hrl hw24 hb1 h4
  have h1077 := x.w1077_nat hret hcl (by omega) hR0 (by rw [VerifySub.linkQVars_tables htab]; norm_num) r1071
  have hnu := x.nu_nat hL htab h4 (theta0 := L.theta0 x.lay x.nF) (r := L.r x.lay x.nF) (m1 := L.m1)
    (fresh := L.fresh x.lay x.nF) (split := Split.ofColumns tables x.c.freshClaim.values)
    (qPoint := L.qPoint x.lay x.nF)
  have hr6 : (x.bw.getD 6 []).take L.chunks.width = L.r x.lay x.nF := by
    rw [hb6, hwd]; exact padTo_take (natR_length hL)
  have hmsg : x.sw D.bm 80 64 = L.msg.drop 80 := by
    rw [hbm, VsCtx.sw]
    exact take_drop80 (x.sw_nat hbits hw hb18 hL.lenM).1
  have key := ltIdentity_of_tailLast htab hL.terminal hsec.coef hsec.certW hsec.rest
  rw [hchL, h1077, hr6, hmsg, hsec.shifts, hnu]
  exact key


/-! ## The link section's values, from `linkSecStatement`'s hypotheses -/

/-- `.n 19` points at buffer `13`. -/
theorem VsCtx.ptr19 (hret : CausalRule x.ret) : x.σ0 (.n 19) = ptrAt (x.base 13) := by
  have e := vsW_alloc (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) rfl hret (j := 13) (by omega)
  rw [vsAllocIdx_getD (by norm_num : 13 < 18)] at e
  exact (vsW0_good (rd0 := x.rd0) (w := x.w) rfl
    (by simp [vsW0, vsW0a] : Atom.hint (.alloc (.n (13 + 6)) 12) ∈ vsW0)).trans e

/-- The overlay's run among the node's words. -/
theorem VsCtx.memWo13 (hbw : x.bw.map List.length = vsAllocSz x.p) :
    (x.base 13, x.cells19.map Prod.snd) ∈ x.Wo := by
  have hl : 13 < x.bw.length := by rw [(VsCtx.bwlen (x := x)) hbw]; norm_num
  have e : (x.bw.set 13 (x.cells19.map Prod.snd)).getD 13 [] = x.cells19.map Prod.snd := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hl]
  have h := mem_zip_getD (l1 := bases x.cur (vsAllocSz x.p)) (l2 := x.bw.set 13 (x.cells19.map Prod.snd)) (j := 13)
    (by rw [bases_lengthF, vsAllocSz_lengthF]; norm_num) (by rw [List.length_set]; exact hl)
  rw [e] at h
  exact h

theorem linkDrawn_ge' {layout : Layout} (h : layout.tables = tables) (c : Chunks) : 88 ≤ linkDrawn layout c := by
  have h1 : (tables.map (·.links.memory.length)).sum = 39 := by decide +kernel
  have h2 : (tables.map fun x ↦ x.links.pointers.length).sum = 33 := by decide +kernel
  simp only [linkDrawn, packedChallenges, h, h1, h2, nTables, bytecodeSlotBits]
  omega

theorem tailNValues_le' {layout : Layout} (h : layout.tables = tables) : Link.Arith.tailNValues layout ≤ 144 := by
  unfold Link.Arith.tailNValues
  rw [h]
  decide +kernel

/-- **The native values' lengths** (`TailShape`). -/
theorem VsCtx.natTailShape {fc : FreshClaim} {link : LinkEnd} (hL : L.Ok x.lay x.nF fc link)
    (htab : x.lay.tables = tables) :
    Link.Arith.TailShape x.lay (L.drawn x.lay x.nF) (L.fresh x.lay x.nF) fc.values (L.qPoint x.lay x.nF) L.msg :=
  ⟨htab, by rw [drawn_length]; exact linkDrawn_ge' htab L.chunks, by simp [LinkNat.fresh], hL.values,
    natQ_length htab, by rw [hL.lenM]; exact tailNValues_le' htab⟩

set_option maxHeartbeats 4000000 in
/-- **`LinkSecVals` from `linkSecStatement`'s hypotheses** at `rd0`, `σ0` and the native values: the link
section's atoms holding, its reads the native values (`IRReads` at `tailIn`), and `rd0` holding the node's words. -/
theorem VsCtx.linkSecVals_of {link : LinkEnd} (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (hret : CausalRule x.ret) (hbw : x.bw.map List.length = vsAllocSz x.p) (hW : HoldsWords x.rd0 x.Wo)
    (htab : x.lay.tables = tables) (hlb : x.lay.logBytecode = 19)
    (hA : ∀ a, Stmt.atom a ∈ Link.Arith.linkSec → a.Holds x.rd0 x.σ0)
    (hr : Link.Arith.IRReads x.rd0 x.σ0 (tailIn x.lay L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF)
      (L.r x.lay x.nF) L.m1 (L.fresh x.lay x.nF) x.c.freshClaim.values (L.chi x.lay x.nF) (L.qPoint x.lay x.nF)
      L.msg)) :
    LinkSecVals x L := by
  have hs := x.natTailShape hL htab
  have hst := Link.Arith.linkSecStatement x.rd0 x.σ0 x.lay
    L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF) (L.r x.lay x.nF) L.m1 (L.fresh x.lay x.nF)
    x.c.freshClaim.values (L.chi x.lay x.nF) (L.qPoint x.lay x.nF) L.msg hA hr hs hlb
  dsimp only at hst
  obtain ⟨-, -, -, -, -, -, h2846, -, h2890, -, h2891, hsh⟩ := hst
  have hrow := Link.Arith.rowIdentity x.lay L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF) (L.r x.lay x.nF)
    L.m1 (L.fresh x.lay x.nF) x.c.freshClaim.values (L.chi x.lay x.nF) (L.qPoint x.lay x.nF) L.msg hs
  dsimp only at hrow
  have hR12 : (natRow x L).shifts.length = 12 := by
    unfold natRow
    rw [← hrow.2.1]
    simp [Link.Arith.gShifts]
  have hrd : ReadsAt x.rd0 (ptrAt (x.base 13)) (x.cells19.map Prod.snd) := hW _ (x.memWo13 hbw)
  have hc12 : (x.cells19.map Prod.snd).length = 12 := by simp [VsCtx.cells19, vsCells19]
  refine ⟨h2846, h2891, h2890, List.ext_getElem (hc12.trans hR12.symm) fun i h1 h2 => ?_⟩
  have e := hsh i (by omega)
  rw [x.ptr19 hret, Link.Arith.rdw_of_load (hrd i h1)] at e
  rw [e]
  exact Link.Arith.getD_eq_getElem' h2

end

end
end LeanVM.Guest.B1.VsC
