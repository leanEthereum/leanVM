/-
  LeanVM.Guest.B1.VsC.VsNum6B

  The front's numbers `Num6` at a context with `HonParts`' inputs, without `Hon`.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatFs

/-!
# `Num6` without `Hon`

`ph4to6S` derives `Num6` from `Hon` through vsph1's memory lemmas (`rd0_lowF`, `loadHolds_rd0`, `pre_rd0F`,
`reads_rd0`), which take `Hon` for its placement, buffer sizes, extra cells and causal rule alone. Their copies
here (`*B`) take those inputs. **`VsCtx.num6_of`**: `Num6` from the placement, the buffers' sizes, the extra
cells, a causal rule, the front's buffers `Bw1F`, its returns `Ret1F` and `chunk_d`'s return `484`;
**`VsCtx.num6_of_parts`** from `Bw1` and `Ret1`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash

@[expose] public section

section
variable {x : VsCtx}

/-- **Below the buffers, `rd0` is `rdP`** (vsph1's `rd0_lowF`, from the placement and the extra cells). -/
theorem VsCtx.rd0_lowFB (hok : x.Ok) (hex : ∀ q ∈ x.ex, x.cur + (vsAllocSz x.p).sum ≤ q.1 ∧ q.1 < 2 ^ 63)
    {i : ℕ} (hi : i < x.cur) :
    x.rd0 (addressOfIndex i) = some ((x.rdP (addressOfIndex i)).getD 0) := by
  have hc := hok.hcur
  have hi' : i < 2 ^ 64 - 1 := by omega
  have inj : ∀ j, j < 2 ^ 64 - 1 → addressOfIndex j = addressOfIndex i → j = i := fun j hj he =>
    gpow_injOn (Set.mem_Iio.mpr hj) (Set.mem_Iio.mpr hi') he
  have h19 : x.cells19.find? (fun q => decide (addressOfIndex q.1 = addressOfIndex i)) = none := by
    rw [List.find?_eq_none]
    intro c hcm he
    simp only [VsCtx.cells19, vsCells19, List.mem_map, List.mem_range] at hcm
    obtain ⟨j, hj, rfl⟩ := hcm
    have e := inj _ (by rw [x.base_eq, vsBaseF_13]; omega) (of_decide_eq_true he)
    rw [x.base_eq, vsBaseF_13] at e
    omega
  have hW : rdW (vsRuns x.cur x.bw) (addressOfIndex i) = none := by
    unfold rdW
    split
    · rename_i hh
      exfalso
      obtain ⟨j, hj, he, q, hq, h1, -⟩ := hh
      have e := inj j hj he.symm
      have := bases_zip_in x.cur x.bw q hq
      omega
    · rfl
  have hE : exAt x.ex (addressOfIndex i) = none := by
    unfold exAt
    rw [Option.map_eq_none_iff, List.find?_eq_none]
    intro q hq he
    have hb := hex q hq
    have e := inj _ (by omega) (of_decide_eq_true he)
    omega
  show rdSet x.rd1 x.cells19 (addressOfIndex i) = _
  unfold rdSet
  rw [h19, Option.map_none, Option.none_or]
  unfold VsCtx.rd1 vsRd1
  rw [hW, hE, Option.none_or, Option.none_or]

theorem VsCtx.loadHolds_rd0B (hok : x.Ok) (hex : ∀ q ∈ x.ex, x.cur + (vsAllocSz x.p).sum ≤ q.1 ∧ q.1 < 2 ^ 63)
    {b off : ℕ} {d : E} (hb : b + off < x.cur)
    (h : LoadHolds x.rdP (ptrAt b) off d) : LoadHolds x.rd0 (ptrAt b) off d := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rw [show (ptrAt b).limb 0 * addressOfIndex off = addressOfIndex (b + off) from
    B1.Main.addr_ofK b off] at h2 ⊢
  rw [x.rd0_lowFB hok hex hb, h2]
  rfl

/-- **The evaluation memory satisfies `Pre`** (vsph1's `pre_rd0F`). -/
theorem VsCtx.pre_rd0FB (hok : x.Ok) (hex : ∀ q ∈ x.ex, x.cur + (vsAllocSz x.p).sum ≤ q.1 ∧ q.1 < 2 ^ 63) :
    x.Pre x.rd0 := by
  have hE := vsPreA_exp hok.pre
  have hq := hok.pre.2
  have ht := hok.ht
  have hfc := hok.hfc
  have ho := hok.ho
  have e1 : sizeBits = 34 := rfl
  have e2 : winTabAt = 178 := rfl
  have e3 : winTabBits = 11 := rfl
  have e4 := expTabLen_eq
  refine ⟨?_, fun k hk => x.loadHolds_rd0B hok hex (by omega) (hq k hk)⟩
  show ExpTables x.rd0 (ptrAt x.qt) ∧ ExpWinTab x.rd0 (ptrAt x.qt)
  refine ⟨⟨fun j hj => x.loadHolds_rd0B hok hex ?_ (hE.1.1 j hj),
    fun j hj u hu => x.loadHolds_rd0B hok hex ?_ (hE.1.2 j hj u hu)⟩,
    fun n hn => x.loadHolds_rd0B hok hex ?_ (hE.2 n hn)⟩
  · omega
  · have : selTabNibbles = 9 := rfl
    omega
  · rw [e3] at hn; omega

/-- **`rd0` reads the front's buffers** (vsph1's `reads_rd0`, off `.n 19`'s cells). -/
theorem VsCtx.reads_rd0B (hx : x.HonB) {j : ℕ} (hj : j ∈ [0, 1, 2, 3, 18, 19, 20]) :
    ReadsAt x.rd0 (ptrAt (x.base j)) (x.bw.getD j []) := by
  have hc := hx.ok.hcur
  have hp := x.p_leB hx
  have b13 : x.base 13 = x.cur + 639 := vsBaseF_13 _ _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have e : x.base 0 = x.cur := vsBaseF_0 _ _
    have s : (vsAllocSz x.p).getD 0 0 = 6 := rfl
    exact x.reads_rd0_ofB hx (by norm_num) (by omega) (by omega)
  · have e : x.base 1 = x.cur + 6 := vsBaseF_1 _ _
    have s : (vsAllocSz x.p).getD 1 0 = 156 := rfl
    exact x.reads_rd0_ofB hx (by norm_num) (by omega) (by omega)
  · have e : x.base 2 = x.cur + 162 := vsBaseF_2 _ _
    have s : (vsAllocSz x.p).getD 2 0 = 24 := rfl
    exact x.reads_rd0_ofB hx (by norm_num) (by omega) (by omega)
  · have e : x.base 3 = x.cur + 186 := vsBaseF_3 _ _
    have s : (vsAllocSz x.p).getD 3 0 = 4 := rfl
    exact x.reads_rd0_ofB hx (by norm_num) (by omega) (by omega)
  · have e : x.base 18 = x.cur + 824 := vsBaseF_18 _ _
    have s : (vsAllocSz x.p).getD 18 0 = 256 * x.p := rfl
    exact x.reads_rd0_ofB hx (by norm_num) (by omega) (by omega)
  · have e : x.base 19 = x.cur + (824 + 256 * x.p) := vsBaseF_19 _ _
    have s : (vsAllocSz x.p).getD 19 0 = 6 := rfl
    exact x.reads_rd0_ofB hx (by norm_num) (by omega) (by omega)
  · have e : x.base 20 = x.cur + (824 + 256 * x.p) + 6 := vsBaseF_20 _ _
    have s : (vsAllocSz x.p).getD 20 0 = 8 := rfl
    exact x.reads_rd0_ofB hx (by norm_num) (by omega) (by omega)

/-- **The front's numbers without `Hon`** (`ph4to6S`'s derivation): from the placement, the buffers' sizes,
the extra cells, a causal rule, the front's buffers and returns, and `chunk_d`'s return. -/
theorem VsCtx.num6_of (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p)
    (hex : ∀ q ∈ x.ex, x.cur + (vsAllocSz x.p).sum ≤ q.1 ∧ q.1 < 2 ^ 63) (hret : CausalRule x.ret)
    (hb1 : x.Bw1F) (hr1 : x.Ret1F) (h484 : ∀ σ, x.ret 484 σ = gen ^ chunkCount (widthOf x.lay)) : x.Num6 := by
  obtain ⟨layout, r, hann, -, hN⟩ := frontNum_of_child hok.child
  have hlay : x.lay = layout := by simp [VsCtx.lay, hann]
  rw [← hlay] at hN hann
  have hrr : (announcedLayoutAndRate guestBytecode x.c.proof.stream |>.map Prod.snd |>.getD 0) = r := by
    simp [hann]
  have ha : x.args.length = 6 := rfl
  have hR : FrontRet x.ret r x.lay.logMemory x.hg x.rows := by
    have := hr1; unfold VsCtx.Ret1F at this; rwa [hrr] at this
  have H := frontHyp_honest (fs := B2C.fs) (al := x.al) (cert := B2C.cert) (k := 17) (rd1 := x.rd1)
    (seed := x.seed) (c := x.c) (qt := x.qt) (qo := x.qo) (nc := x.c.freshClaim.cells.length)
    (f4 := x.f4) (Own := fun _ => True) (st := ⟨x.cur, 0, fun _ => False, fun _ => False, []⟩) hN hret hR
    (fun _ _ _ => trivial) rfl (x.pre_rd0FB hok hex)
    (x.front_holds hb1 fun j hj => x.reads_rd0B ⟨hok, hbw, hret⟩ hj) (fun _ h => h.elim)
  have h409 := vsVal_409_of_front ha H
  have n408 : vsVal x.rd0 x.w x.args (.n 408) = gen ^ hMax x.lay := vsVal_408 ha H.hw9 H.r0.shape
  obtain ⟨v115, v116, v117, v118, v119, v120, -⟩ := vsW6_vals (rd0 := x.rd0) (w := x.w) (args := x.args) ha
    H.hw6 H.hw56 (bs := rowsW x.rows) (by simp [rowsW]) H.r0.heights H.r0.sizes
  have alloc : ∀ {j v n : ℕ}, j < 18 → vsAllocIdx.getD j 0 = v → Atom.hint (.alloc (.n v) n) ∈ vsW0 →
      vsVal x.rd0 x.w x.args (.n v) = ptrAt (x.base j) := fun hj hv hm =>
    (vsW0_good ha hm).trans ((vsW_buf (rd1 := x.rd1) ha hret (j := _) (by omega) hv).trans rfl)
  have h10 : vsVal x.rd0 x.w x.args (.n 10) = ptrAt (x.base 4) :=
    alloc (j := 4) (n := 153) (by norm_num) rfl (by simp [vsW0, vsW0a])
  have sel : ∀ t, 1 ≤ t → t ≤ 5 → x.σ0 (.n (115 + t)) = gen ^ x.hgS t := by
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
  exact ⟨n408, h409, vsW_retC ha hret (by decide) h484, vsVal_694 ha h10 n408,
    (vsVal_call_ret ha vsW5_eq (.n 101) (List.mem_singleton_self _)).trans H.hw101, v115, sel, bv⟩

/-- **`Num6` from `HonParts`' fields** that do not take it. -/
theorem VsCtx.num6_of_parts (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p)
    (hex : ∀ q ∈ x.ex, x.cur + (vsAllocSz x.p).sum ≤ q.1 ∧ q.1 < 2 ^ 63) (hret : CausalRule x.ret)
    (hb1 : x.Bw1) (hr1 : x.Ret1) : x.Num6 :=
  x.num6_of hok hbw hex hret hb1.front hr1.front hr1.r484

end

end
end LeanVM.Guest.B1.VsC
