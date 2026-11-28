/-
  LeanVM.Guest.B1.VsC.VsOrcPh1

  The front's statement `FrontS` at the honest context, from vsph1's conditions on the buffers and the return
  rule.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcSpec
public import LeanVM.Guest.B1.VsC.VsOrcFront2

/-!
# The front at the honest context

`FrontS al` (`VsOrcSpec.lean`) asks `FrontOk` from `x.st0`, its continuation at every state with `Bnd` and
`CarryF`. Here, from vsph1's conditions on the context (to become `Bw1`, `Ret1`, `CarryF` once `al` is in
`VsCtx`):

* `Bw1F x`: the front's buffers' honest words (`vsAllocIdx` entries `0 … 3`, `18 … 20`), at the announced
  layout `x.lay`: the heights, each table size's bits at word `26 t` of the bits' buffer, the cycle count's
  bits, the link's shape, the padded stream, the row counts, the eight words `certify_stack` reads;
* `Ret1F x`: the front's callees' returns as `ret`'s rules (`FrontRet`);
* `CarryFA al x st`: the callees' cursor is the front's end `vsFrontEnd al x`.

The memory facts: `rd1` holds the buffers' runs (`holdsWords_vsRd1`), the overlay `rdSet` leaves every cell
off `.n 19`'s twelve (`readsAt_rdSet`), so `rd0` reads the front's runs; `Wo` holds the same runs. The posts:
`hint_stream`'s `hsQ` is `vsChunks`' (`popsPost_hsQ`), the front's leaves are quiet, and `vsPs`' first eleven
entries but the first are `[]` when `.n 471 = 0` (flag set), its first ten always.

**`frontS_of`**: `FrontOk … x.st0 K` from `x.Hon`, `Bw1F x`, `Ret1F x` and `K` on every state with `Bnd` and
`CarryFA`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## Memory runs -/

theorem loadHolds_ptrAt_shift {rd : Reader} {b j k : ℕ} {v : E} :
    LoadHolds rd (ptrAt b) (j + k) v ↔ LoadHolds rd (ptrAt (b + j)) k v := by
  unfold LoadHolds ptrAt
  rw [B1.Main.addr_ofK, B1.Main.addr_ofK, Nat.add_assoc]
  exact ⟨fun h => ⟨Value.ofK_isInK _, h.2⟩, fun h => ⟨Value.ofK_isInK _, h.2⟩⟩

/-- **A run inside a run**: the words `ys` at word `j` of `xs`. -/
theorem readsAt_sub {rd : Reader} {b j : ℕ} {xs ys : List E} (H : ReadsAt rd (ptrAt b) xs)
    (hs : ∀ k < ys.length, xs[j + k]? = ys[k]?) : ReadsAt rd (ptrAt (b + j)) ys := by
  intro k hk
  have e := hs k hk
  rw [List.getElem?_eq_getElem hk] at e
  obtain ⟨hk', e'⟩ := List.getElem?_eq_some_iff.mp e
  have := H (j + k) hk'
  rw [e'] at this
  exact loadHolds_ptrAt_shift.1 this

theorem readsAt_of_mem {rd : Reader} {W : Words} (h : HoldsWords rd W) {b : ℕ} {xs : List E} (hm : (b, xs) ∈ W) :
    ReadsAt rd (ptrAt b) xs := h _ hm

/-- A memory read first from `rd`, then elsewhere, holds what `rd` holds. -/
theorem holdsWords_or {rd rd' : Reader} {W : Words} (h : HoldsWords rd W) :
    HoldsWords (fun A => (rd A).or (rd' A)) W := fun q hq k hk => by
  obtain ⟨h1, h2⟩ := h q hq k hk
  exact ⟨h1, by simp only [h2, Option.some_or]⟩

/-- **The overlay leaves a run off its cells.** -/
theorem readsAt_rdSet {rd : Reader} {cells : List (ℕ × E)} {b : ℕ} {xs : List E} (H : ReadsAt rd (ptrAt b) xs)
    (hb : b + xs.length < 2 ^ 64 - 1) (hc : ∀ c ∈ cells, c.1 < 2 ^ 64 - 1 ∧ (c.1 < b ∨ b + xs.length ≤ c.1)) :
    ReadsAt (rdSet rd cells) (ptrAt b) xs := by
  intro k hk
  obtain ⟨h1, h2⟩ := H k hk
  refine ⟨h1, ?_⟩
  rw [show (ptrAt b).limb 0 * addressOfIndex k = addressOfIndex (b + k) from B1.Main.addr_ofK b k] at h2 ⊢
  unfold rdSet
  rw [show cells.find? (fun q => decide (addressOfIndex q.1 = addressOfIndex (b + k))) = none from ?_]
  · simpa using h2
  · rw [List.find?_eq_none]
    intro c hc' he
    have e := gpow_injOn (Set.mem_Iio.mpr (hc c hc').1) (Set.mem_Iio.mpr (by omega : b + k < 2 ^ 64 - 1))
      (of_decide_eq_true he)
    have := (hc c hc').2
    omega

/-- The entry `j` of a zip. -/
theorem mem_zip_getD {l1 : List ℕ} {l2 : List (List E)} {j : ℕ} (h1 : j < l1.length) (h2 : j < l2.length) :
    (l1.getD j 0, l2.getD j []) ∈ l1.zip l2 := by
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  exact List.mem_iff_getElem.mpr ⟨j, by simp [h1, h2], by simp⟩

/-! ## The context's runs -/

section
variable {x : VsCtx}

theorem VsCtx.bw_lengthF (hx : x.Hon) : x.bw.length = 24 := by
  have := congrArg List.length hx.hbw
  simpa [vsAllocSz_lengthF] using this

theorem VsCtx.base_eq (j : ℕ) : x.base j = vsBaseF x.cur x.p j := rfl

theorem VsCtx.p_leF (hx : x.Hon) : x.p ≤ 32 := by
  obtain ⟨_, _, _, _, hN⟩ := frontNum_of_child hx.ok.child
  exact hN.hp

theorem VsCtx.len_bw (hx : x.Hon) {j : ℕ} (hj : j < 24) : (x.bw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
  have hl : j < x.bw.length := by rw [x.bw_lengthF hx]; exact hj
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by rw [vsAllocSz_lengthF]; exact hj)]
  have := List.getElem_of_eq hx.hbw (by simpa using hl)
  simpa using this

/-- Buffer `j`'s run among `rd1`'s. -/
theorem VsCtx.mem_runs (hx : x.Hon) {j : ℕ} (hj : j < 24) : (x.base j, x.bw.getD j []) ∈ vsRuns x.cur x.bw := by
  unfold vsRuns VsCtx.base
  rw [hx.hbw]
  exact mem_zip_getD (by rw [bases_lengthF, vsAllocSz_lengthF]; exact hj) (by rw [x.bw_lengthF hx]; exact hj)

/-- Buffer `j`'s run among `Wo`'s, off `.n 19`. -/
theorem VsCtx.mem_WoF (hx : x.Hon) {j : ℕ} (hj : j < 24) (h13 : j ≠ 13) : (x.base j, x.bw.getD j []) ∈ x.Wo := by
  have e : (x.bw.set 13 (x.cells19.map Prod.snd)).getD j [] = x.bw.getD j [] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h13)]
  unfold VsCtx.Wo
  rw [← e]
  exact mem_zip_getD (by rw [bases_lengthF, vsAllocSz_lengthF]; exact hj) (by simp [x.bw_lengthF hx]; exact hj)

/-- **`rd1` holds the buffers' runs.** -/
theorem VsCtx.holds_rd1 (hx : x.Hon) : HoldsWords x.rd1 (vsRuns x.cur x.bw) := by
  have hc := hx.ok.hcur
  have hs : (x.bw.map List.length).sum ≤ 2 ^ 14 := by
    rw [hx.hbw]
    have hp := x.p_leF hx
    simp only [vsAllocSz, vsSz0, List.cons_append, List.nil_append, List.sum_cons, List.sum_nil]
    omega
  have h := holdsWords_rdW (bases_zip_pairwise x.cur x.bw) fun q hq => by
    have := bases_zip_in x.cur x.bw q hq; omega
  show HoldsWords (vsRd1 x.rdP x.cur x.bw x.ex) _
  unfold vsRd1
  exact holdsWords_or (rd' := fun A => (exAt x.ex A).or (some ((x.rdP A).getD 0))) h

end


/-! ## The memories off the buffers -/

section
variable {x : VsCtx}

/-- **Below the buffers, `rd0` is `rdP`** (`0` where `rdP` is undefined). -/
theorem VsCtx.rd0_lowF (hx : x.Hon) {i : ℕ} (hi : i < x.cur) :
    x.rd0 (addressOfIndex i) = some ((x.rdP (addressOfIndex i)).getD 0) := by
  have hc := hx.ok.hcur
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
    have hb := hx.hex q hq
    have e := inj _ (by omega) (of_decide_eq_true he)
    omega
  show rdSet x.rd1 x.cells19 (addressOfIndex i) = _
  unfold rdSet
  rw [h19, Option.map_none, Option.none_or]
  unfold VsCtx.rd1 vsRd1
  rw [hW, hE, Option.none_or, Option.none_or]

theorem VsCtx.loadHolds_rd0 (hx : x.Hon) {b off : ℕ} {d : E} (hb : b + off < x.cur)
    (h : LoadHolds x.rdP (ptrAt b) off d) : LoadHolds x.rd0 (ptrAt b) off d := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rw [show (ptrAt b).limb 0 * addressOfIndex off = addressOfIndex (b + off) from
    B1.Main.addr_ofK b off] at h2 ⊢
  rw [x.rd0_lowF hx hb, h2]
  rfl

/-- **The evaluation memory satisfies `Pre`**: the tables and the fresh claim lie below the buffers. -/
theorem VsCtx.pre_rd0F (hx : x.Hon) : x.Pre x.rd0 := by
  have hE := vsPreA_exp hx.ok.pre
  have hq := hx.ok.pre.2
  have ht := hx.ok.ht
  have hfc := hx.ok.hfc
  have ho := hx.ok.ho
  have e1 : sizeBits = 34 := rfl
  have e2 : winTabAt = 178 := rfl
  have e3 : winTabBits = 11 := rfl
  have e4 := expTabLen_eq
  refine ⟨?_, fun k hk => x.loadHolds_rd0 hx (by omega) (hq k hk)⟩
  show ExpTables x.rd0 (ptrAt x.qt) ∧ ExpWinTab x.rd0 (ptrAt x.qt)
  refine ⟨⟨fun j hj => x.loadHolds_rd0 hx ?_ (hE.1.1 j hj), fun j hj u hu => x.loadHolds_rd0 hx ?_ (hE.1.2 j hj u hu)⟩,
    fun n hn => x.loadHolds_rd0 hx ?_ (hE.2 n hn)⟩
  · omega
  · have : selTabNibbles = 9 := rfl
    omega
  · rw [e3] at hn; omega

theorem VsCtx.reads_rd0_of (hx : x.Hon) {j : ℕ} (hj : j < 24)
    (hd : x.base j + (vsAllocSz x.p).getD j 0 ≤ x.base 13 ∨ x.base 13 + 12 ≤ x.base j)
    (hbd : x.base j + (vsAllocSz x.p).getD j 0 < 2 ^ 64 - 1) :
    ReadsAt x.rd0 (ptrAt (x.base j)) (x.bw.getD j []) := by
  have h1 : ReadsAt x.rd1 (ptrAt (x.base j)) (x.bw.getD j []) := x.holds_rd1 hx _ (x.mem_runs hx hj)
  have hc := hx.ok.hcur
  have h13 : x.base 13 = x.cur + 639 := vsBaseF_13 _ _
  refine readsAt_rdSet (rd := x.rd1) (cells := x.cells19) h1 (by rw [x.len_bw hx hj]; exact hbd) ?_
  intro c hcm
  simp only [VsCtx.cells19, vsCells19, List.mem_map, List.mem_range] at hcm
  obtain ⟨i, hi, rfl⟩ := hcm
  rw [x.len_bw hx hj]
  dsimp only
  omega

/-- **`rd0` reads the front's buffers** (off `.n 19`'s cells). -/
theorem VsCtx.reads_rd0 (hx : x.Hon) {j : ℕ} (hj : j ∈ [0, 1, 2, 3, 18, 19, 20]) :
    ReadsAt x.rd0 (ptrAt (x.base j)) (x.bw.getD j []) := by
  have hc := hx.ok.hcur
  have hp := x.p_leF hx
  have b13 : x.base 13 = x.cur + 639 := vsBaseF_13 _ _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have e : x.base 0 = x.cur := vsBaseF_0 _ _
    have s : (vsAllocSz x.p).getD 0 0 = 6 := rfl
    exact x.reads_rd0_of hx (by norm_num) (by omega) (by omega)
  · have e : x.base 1 = x.cur + 6 := vsBaseF_1 _ _
    have s : (vsAllocSz x.p).getD 1 0 = 156 := rfl
    exact x.reads_rd0_of hx (by norm_num) (by omega) (by omega)
  · have e : x.base 2 = x.cur + 162 := vsBaseF_2 _ _
    have s : (vsAllocSz x.p).getD 2 0 = 24 := rfl
    exact x.reads_rd0_of hx (by norm_num) (by omega) (by omega)
  · have e : x.base 3 = x.cur + 186 := vsBaseF_3 _ _
    have s : (vsAllocSz x.p).getD 3 0 = 4 := rfl
    exact x.reads_rd0_of hx (by norm_num) (by omega) (by omega)
  · have e : x.base 18 = x.cur + 824 := vsBaseF_18 _ _
    have s : (vsAllocSz x.p).getD 18 0 = 256 * x.p := rfl
    exact x.reads_rd0_of hx (by norm_num) (by omega) (by omega)
  · have e : x.base 19 = x.cur + (824 + 256 * x.p) := vsBaseF_19 _ _
    have s : (vsAllocSz x.p).getD 19 0 = 6 := rfl
    exact x.reads_rd0_of hx (by norm_num) (by omega) (by omega)
  · have e : x.base 20 = x.cur + (824 + 256 * x.p) + 6 := vsBaseF_20 _ _
    have s : (vsAllocSz x.p).getD 20 0 = 8 := rfl
    exact x.reads_rd0_of hx (by norm_num) (by omega) (by omega)

/-- The front's runs on a memory reading its buffers. -/
theorem VsCtx.front_holds (hb : x.Bw1F) {rd : Reader}
    (H : ∀ j ∈ [0, 1, 2, 3, 18, 19, 20], ReadsAt rd (ptrAt (x.base j)) (x.bw.getD j [])) :
    HoldsWords rd (frontWords x.cur x.p (padStream x.c.proof.stream) x.lay.logMemory x.hg x.rows (hMax x.lay)
      (widthOf x.lay) (flagOf x.lay) x.f4) := by
  have R : ∀ j ∈ [0, 1, 2, 3, 18, 19, 20], ∀ b xs, vsBaseF x.cur x.p j = b → x.bw.getD j [] = xs →
      ReadsAt rd (ptrAt b) xs := fun j hj b xs hb hx => by rw [← hb, ← hx]; exact H j hj
  intro q hq
  simp only [frontWords, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hq
  rcases hq with ((rfl | rfl | rfl | rfl) | ⟨t, ht, rfl⟩) | rfl | rfl
  · exact R 18 (by simp) _ _ (vsBaseF_18 _ _) hb.b18
  · exact R 19 (by simp) _ _ (vsBaseF_19 _ _) hb.b19
  · exact R 0 (by simp) _ _ (vsBaseF_0 _ _) hb.b0
  · exact R 20 (by simp) _ _ (vsBaseF_20 _ _) hb.b20
  · have := readsAt_sub (j := 26 * t) (H 1 (by simp)) (hb.b1 t ht)
    rw [x.base_eq, vsBaseF_1] at this
    exact this
  · exact R 2 (by simp) _ _ (vsBaseF_2 _ _) hb.b2
  · exact R 3 (by simp) _ _ (vsBaseF_3 _ _) hb.b3

end

/-! ## The front's end -/

theorem le_leafEnd {fs : String → ℕ} {al : String → Bool} {g : String} {kc : ℕ} : kc ≤ leafEnd fs al g kc :=
  (le_allocBase _ _).trans (Nat.le_add_right _ _)

theorem le_frontKc {fs : String → ℕ} {al : String → Bool} {p : ℕ} {h : ℕ → ℕ} {kc : ℕ} :
    kc ≤ frontKc fs al p h kc := by
  unfold frontKc tsEnd
  refine le_trans ?_ le_leafEnd; refine le_trans ?_ le_leafEnd; refine le_trans ?_ le_leafEnd
  refine le_trans ?_ le_leafEnd; refine le_trans ?_ le_leafEnd; refine le_trans ?_ le_leafEnd
  refine le_trans ?_ le_leafEnd; refine le_trans ?_ le_leafEnd
  exact le_trans (le_trans (le_allocBase _ kc) (Nat.le_add_right _ _))
    (le_trans (le_allocBase _ _) (Nat.le_add_right _ _))

theorem forall2_quiet (rd : Reader) : ∀ n, List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t)
    (List.replicate n PostQuiet) (List.replicate n ([] : List Pop))
  | 0 => .nil
  | n + 1 => .cons (fun _ h => popsPost_quiet h) (forall2_quiet rd n)

theorem vsPs_take10 (σ : Val) (ch stk mk : List Pop) : (vsPs σ ch stk mk).take 10 = ch :: List.replicate 9 [] := by
  unfold vsPs; split <;> rfl

theorem vsPs_take11 {σ : Val} (h : σ (.n 471) = 0) (ch stk mk : List Pop) :
    (vsPs σ ch stk mk).take 11 = ch :: List.replicate 10 [] := by
  unfold vsPs
  split
  · rfl
  · contradiction

theorem VsCtx.frontEnd_one {x : VsCtx} {fs : String → ℕ} {al : String → Bool} (h : flagOf x.lay = 1) {kc : ℕ}
    (hk : kc = x.cur + (vsAllocSz x.p).sum) :
    leafEnd fs al "assert_small_g_power" (leafEnd fs al "assert_small_g_power" (frontKc fs al x.p x.hg kc)) =
      x.frontEnd fs al := by
  rw [hk]
  exact (ite_eq_left_iff.mpr fun h' => absurd h h').symm

theorem VsCtx.frontEnd_zero {x : VsCtx} {fs : String → ℕ} {al : String → Bool} (h : flagOf x.lay ≠ 1) {kc : ℕ}
    (hk : kc = x.cur + (vsAllocSz x.p).sum) :
    leafEnd fs al "assert_small_g_power" (frontKc fs al x.p x.hg kc) = x.frontEnd fs al := by
  rw [hk]
  exact (ite_eq_right_iff.mpr fun h' => absurd h' h).symm

/-! ## The front's statement -/

/-- **The front at the honest context**: `FrontOk … x.st0B K` from `x.Hon`, the front's conditions on the
buffers and the return rule, own cells containing the buffers, and `K` at every state with `Bnd` and the
front's cursor and posts' count. -/
theorem frontS_of {al : String → Bool} {x : VsCtx} (hx : x.Hon) (hb : x.Bw1F) (hr : x.Ret1F) {Own : ℕ → Prop}
    (hown : ∀ i, x.OwnB i → Own i) {K : St → Prop} (hK : ∀ s, x.Bnd s → x.CarryFA B2C.fs al s → K s) :
    FrontOk B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre x.st0B K := by
  obtain ⟨layout, r, hann, -, hN⟩ := frontNum_of_child hx.ok.child
  have hlay : x.lay = layout := by simp [VsCtx.lay, hann]
  have hrr : (announcedLayoutAndRate guestBytecode x.c.proof.stream |>.map Prod.snd |>.getD 0) = r := by
    simp [hann]
  rw [← hlay] at hN hann
  have hR : FrontRet x.ret r x.lay.logMemory x.hg x.rows := by have := hr; unfold VsCtx.Ret1F at this; rwa [hrr] at this
  have ha : x.args.length = 6 := rfl
  have H := frontHyp_honest (fs := B2C.fs) (al := al) (cert := B2C.cert) (k := 17) (rd1 := x.rd1)
    (seed := x.seed) (c := x.c) (qt := x.qt) (qo := x.qo) (nc := x.c.freshClaim.cells.length)
    (f4 := x.f4) (st := x.st0B) hN hx.hret hR (fun i h1 h2 => hown i ⟨h1, h2⟩) rfl (x.pre_rd0F hx)
    (x.front_holds hb fun j hj => x.reads_rd0 hx hj)
    (fun rd hrd => x.front_holds hb fun j hj => readsAt_of_mem hrd (x.mem_WoF hx (by simp at hj; omega)
      (by simp at hj; omega)))
  have hFl := (vsVal_409_410_of_front ha H).2
  have hkc0 : (x.st0B).kc = x.cur + (vsAllocSz x.p).sum := rfl
  -- the posts so far
  have hQ : ∀ (n : ℕ), (n = 9 ∨ (n = 10 ∧ x.σ0 (.n 471) = 0)) → ∀ rd, LowDef 17 rd → x.Pre rd →
      List.Forall₂ (fun Q P => ∀ t, Q rd t → PopsPost P rd t)
        ((x.st0B).Qs ++ hsQ (padStream x.c.proof.stream) x.p :: List.replicate n PostQuiet)
        ((vsPsH x.seed x.c (rdOver x.σ0 rd)).take ((x.st0B).Qs ++ hsQ (padStream x.c.proof.stream) x.p ::
          List.replicate n PostQuiet).length) := by
    intro n hn rd _ _
    have e0 : (x.st0B).Qs = [] := rfl
    simp only [e0, List.nil_append, List.length_cons, List.length_replicate]
    simp only [vsPsH, hann]
    rcases hn with rfl | ⟨rfl, h0⟩
    · rw [vsPs_take10]
      exact .cons (fun t h => popsPost_hsQ h) (forall2_quiet rd 9)
    · rw [vsPs_take11 (by rw [rdOver_eq (by decide +kernel)]; exact h0)]
      exact .cons (fun t h => popsPost_hsQ h) (forall2_quiet rd 10)
  have e0 : (x.st0B).Qs = [] := rfl
  refine ⟨x.p, r, x.lay.logMemory, hMax x.lay, widthOf x.lay, x.cur, x.cur + 6, x.cur + 162, x.cur + 186, x.qt,
    flagOf x.lay, x.f4, padStream x.c.proof.stream, x.hg, x.rows, H, fun hf => hK _ ?_ ?_, fun hf => hK _ ?_ ?_⟩
  · have h471 : x.σ0 (.n 471) = 0 := by
      have := (vsB2_runHyp (k := 6) (Own := fun _ => True) (R := fun _ => True) (Pre := fun _ => False)
        (a := 0) (D := fun _ => False) (O := fun _ => False) ha (Or.inr hf) hFl).2
      rw [hf] at this
      exact this.trans (Link.add_self_E 1)
    refine ⟨rfl, ?_, fun rd h => h, fun rd hl hp _ => hQ 10 (.inr ⟨rfl, h471⟩) rd hl hp⟩
    rw [← hkc0]; exact le_trans le_frontKc (le_trans le_leafEnd le_leafEnd)
  · have h471 : x.σ0 (.n 471) = 0 := by
      have := (vsB2_runHyp (k := 6) (Own := fun _ => True) (R := fun _ => True) (Pre := fun _ => False)
        (a := 0) (D := fun _ => False) (O := fun _ => False) ha (Or.inr hf) hFl).2
      rw [hf] at this
      exact this.trans (Link.add_self_E 1)
    refine ⟨VsCtx.frontEnd_one hf hkc0, ?_⟩
    simp [e0, h471]
  · refine ⟨rfl, ?_, fun rd h => h, fun rd hl hp _ => hQ 9 (.inl rfl) rd hl hp⟩
    rw [← hkc0]; exact le_trans le_frontKc le_leafEnd
  · have h471 : x.σ0 (.n 471) ≠ 0 := by
      have := (vsB2_runHyp (k := 6) (Own := fun _ => True) (R := fun _ => True) (Pre := fun _ => False)
        (a := 0) (D := fun _ => False) (O := fun _ => False) ha (Or.inl hf) hFl).2
      rw [hf, zero_add] at this
      intro h0
      exact one_ne_zero (this.symm.trans h0)
    refine ⟨VsCtx.frontEnd_zero (by rw [hf]; exact zero_ne_one) hkc0, ?_⟩
    simp [e0, h471]

/-- **`FrontS`** (`VsOrcSpec.lean`): the front at every honest context, from `Bw1`'s and `Ret1`'s front parts. -/
theorem frontS (al : String → Bool) : FrontS al := by
  intro x hal hx _ Own hown K hK
  subst hal
  exact frontS_of hx hx.bw1.front hx.ret1.front hown hK

end
end LeanVM.Guest.B1.VsC
