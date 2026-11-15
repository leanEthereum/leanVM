/-
  LeanVM.Guest.B1.Da.DvAt

  `da_verify` on its honest buffers, placed: complete within its words bound (G:4516-4540).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Da.BlobLAt
public import LeanVM.Guest.B1.Da.BlobAt
public import LeanVM.Guest.B1.Da.VecAt
public import LeanVM.Guest.Value.KeccakDuplex
public import LeanVM.Guest.Data.NameStrings

/-!
# `da_verify`, placed

Its `HeapBuf`, the roots' tree at `bb = fp + fs da_verify` (`rootsCells`). Its callees in call order: the row shape
(`row_shape_completeAtB`), the dual codeword (`vec_completeAtB`), the weights (`ws_completeAtB`, on `da_vector`'s
buffers read off its result, `dvVb`), the blob loop (`blobL_completeAtTB` of `blob_completeAtB`, on the weights read
off their result, `dvW`), the roots' tree's arm (`rt_completeAtB`). `dvNHzC r L z Tb`: its honest shape exposing the
hinted words, its blob loop by a tree of `Tb`; `dv_completeAtB_z`: complete within `dvB`, returning the root's cells
and the challenge.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Kid KidD kidsAt outsL KidsDepBP OutsOk RegionsOk CallsMatch
  Returns completeAt_flatDepRet flatCalls namedP)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Main (Layout MemL RegionL iterK)

@[expose] public section

/-- **`da_verify`'s block, its shape** (kernel evaluation). -/
noncomputable def dvCOk : Bool :=
  dvP.all Core.Stmt.flat && dvP.all B1.notIteB && decide (dvP.filterMap Stmt.addrS = []) &&
  decide (dvP.filterMap Stmt.allocSz = [(.n 17, .inr (.n 16))]) && decide (dvP.filterMap Stmt.loadS = [])

theorem dv_cok : dvCOk = true := by decide +kernel

/-- The dual codeword's buffers' bases, read off `da_vector`'s result. -/
noncomputable def dvVb (z : E) (pv : List (List E × Layout)) : ℕ × ℕ × ℕ × ℕ :=
  outB (fun (q : ℕ × ℕ × ℕ × ℕ) rets Lo => rets = [gen ^ q.1, gen ^ (q.2.1 + 2 ^ 7), gen ^ q.2.2.1,
    gen ^ q.2.2.2] ∧ (q.1, zsCells z) ∈ Lo ∧ (q.2.1, topRun z) ∈ Lo ∧
    (q.2.2.1, facCells (zsVal z) 7 8) ∈ Lo ∧ (q.2.2.2, offCells (zsVal z)) ∈ Lo) (pv.getD 1 ([], []))

theorem dvVb_spec {z : E} {pv : List (List E × Layout)} (h : vecOut z (pv.getD 1 ([], [])).1 (pv.getD 1 ([], [])).2) :
    (pv.getD 1 ([], [])).1 = [gen ^ (dvVb z pv).1, gen ^ ((dvVb z pv).2.1 + 2 ^ 7),
      gen ^ (dvVb z pv).2.2.1, gen ^ (dvVb z pv).2.2.2] ∧
    ((dvVb z pv).1, zsCells z) ∈ (pv.getD 1 ([], [])).2 ∧ ((dvVb z pv).2.1, topRun z) ∈ (pv.getD 1 ([], [])).2 ∧
    ((dvVb z pv).2.2.1, facCells (zsVal z) 7 8) ∈ (pv.getD 1 ([], [])).2 ∧
    ((dvVb z pv).2.2.2, offCells (zsVal z)) ∈ (pv.getD 1 ([], [])).2 := by
  obtain ⟨bz, bt, bc, bo, h1, h2, h3, h4, h5⟩ := h
  exact outB_spec (P := fun (q : ℕ × ℕ × ℕ × ℕ) rets Lo => rets = [gen ^ q.1, gen ^ (q.2.1 + 2 ^ 7),
    gen ^ q.2.2.1, gen ^ q.2.2.2] ∧ (q.1, zsCells z) ∈ Lo ∧ (q.2.1, topRun z) ∈ Lo ∧
    (q.2.2.1, facCells (zsVal z) 7 8) ∈ Lo ∧ (q.2.2.2, offCells (zsVal z)) ∈ Lo)
    ⟨(bz, bt, bc, bo), h1, h2, h3, h4, h5⟩

/-- The weights' base and their columns' expansions' bases, read off `da_weights`' result. -/
noncomputable def dvW (z : E) (pv : List (List E × Layout)) : ℕ × (ℕ → ℕ) :=
  outB (fun (q : ℕ × (ℕ → ℕ)) rets Lo => rets = [gen ^ q.1] ∧ (q.1, wtsCells q.2) ∈ Lo ∧
    ∀ h < 128, (q.2 h, colRun z h) ∈ Lo) (pv.getD 2 ([], []))

theorem dvW_spec {z : E} {pv : List (List E × Layout)} (h : wOut z (pv.getD 2 ([], [])).1 (pv.getD 2 ([], [])).2) :
    (pv.getD 2 ([], [])).1 = [gen ^ (dvW z pv).1] ∧ ((dvW z pv).1, wtsCells (dvW z pv).2) ∈ (pv.getD 2 ([], [])).2 ∧
      ∀ h < 128, ((dvW z pv).2 h, colRun z h) ∈ (pv.getD 2 ([], [])).2 := by
  obtain ⟨b, q, h1, h2, h3⟩ := h
  exact outB_spec (P := fun (q : ℕ × (ℕ → ℕ)) rets Lo => rets = [gen ^ q.1] ∧ (q.1, wtsCells q.2) ∈ Lo ∧
    ∀ h < 128, (q.2 h, colRun z h) ∈ Lo) ⟨(b, q), h1, h2, h3⟩

/-- The blob loop's layout: the weights, the roots' tree at `bb`. -/
def dvBlobLin (z : E) (bw : ℕ) (q : ℕ → ℕ) (bb : ℕ) (roots : List E) : Layout :=
  (bw, wtsCells q) :: ((List.range 128).map fun h => (q h, colRun z h)) ++ [(bb, roots)]

/-- `da_verify`'s callees, on its roots' tree at `bb`. -/
noncomputable def dvKids (r L : ℕ) (syms : ℕ → ℕ → List K) (z : E) (s bb : ℕ) : List KidD :=
  [fun _ => ⟨"da_row_shape", true, [gen ^ r, gen ^ L, gen ^ s], [(s + L, [gen ^ 2 ^ L])],
      Returns [gen ^ 2 ^ L, gen ^ (2 ^ L - r)]⟩,
    fun _ => ⟨"da_vector", true, [z], [], vecOut z⟩,
    fun pv => ⟨"da_weights", true, [gen ^ ((dvVb z pv).2.1 + 2 ^ 7), gen ^ (dvVb z pv).2.2.1,
      gen ^ (dvVb z pv).1, gen ^ (dvVb z pv).2.2.2],
      wsLin z (dvVb z pv).1 (dvVb z pv).2.1 (dvVb z pv).2.2.1 (dvVb z pv).2.2.2, wOut z⟩,
    fun pv => ⟨name% «da_verify_loop0», true, [1, gen ^ r, gen ^ (dvW z pv).1, gen ^ bb],
      dvBlobLin z (dvW z pv).1 (dvW z pv).2 bb (rootsCells r L syms), Returns []⟩,
    fun _ => ⟨rtName L, true, [gen ^ bb, gen ^ r, gen ^ (2 ^ L - r)], [(bb, rootsCells r L syms)],
      Returns (digestCells (daRoot r L syms))⟩]

/-- `da_verify`'s valuation, the range check's words `t1`, `t2`. -/
def dvVals (r L s : ℕ) (t1 t2 z : E) (q : ℕ × ℕ × ℕ × ℕ) (bw bb : ℕ) (c0 c1 : E) : List E :=
  [gen ^ s, gen ^ r, gen ^ L, word 1024 0, gen ^ (10 - L), t1, t2, gen ^ 2 ^ L, gen ^ (2 ^ L - r), z,
    gen ^ q.1, gen ^ (q.2.1 + 2 ^ 7), gen ^ q.2.2.1, gen ^ q.2.2.2, gen ^ bw, gen ^ (2 * 2 ^ L),
    gen ^ (4 * 2 ^ L), gen ^ bb, word 1 0, word 1 0 + gen ^ r, word 1 0, c0, c1, c0, c1, z]

/-- **`da_verify`'s honest valuation exposing its challenge `z`.** -/
def dvQz (r L : ℕ) (z : E) (σ : Val) : Prop := dvQ r L σ ∧ σ (.n 9) = z

/-- The predicates on `da_verify`'s callees' trees, its blob loop by a tree of `Tb`. -/
def dvTsC (r L : ℕ) (Tb : Tree → Prop) : List (Tree → Prop) :=
  [fun _ => True, fun _ => True, fun _ => True, Tb, rtNH L (2 ^ L - r)]

/-- **`da_verify`'s honest shape**, its challenge `z`, its blob loop by a tree of `Tb`. -/
def dvNHzC (r L : ℕ) (z : E) (Tb : Tree → Prop) : Tree → Prop :=
  NodeHonest coreProgram "da_verify" (dvQz r L z) (flatCalls dvP) (fun _ => dvSizes r L) (dvTsC r L Tb)

theorem dvNH_of_zC {r L : ℕ} {z : E} {Tb : Tree → Prop} {t : Tree} (h : dvNHzC r L z Tb t) : dvNH r L t :=
  let ⟨σ, ks, e, hQ, hw, hl, hk⟩ := h
  nodeHonest_mono (Ts := dvTsC r L Tb) ⟨σ, ks, e, hQ.1, hw, hl, hk⟩
    (.cons (fun _ h => h) (.cons (fun _ h => h) (.cons (fun _ h => h) (.cons (fun _ _ => trivial)
      (.cons (fun _ h => h) .nil)))))

set_option maxRecDepth 20000 in
/-- **`da_verify`'s statements hold** on its valuation, the range check's words read. -/
theorem dv_sholds {rd : Reader} (r L s : ℕ) (hL : L ≤ 10) {t1 t2 : E} (h1 : LoadHolds rd (gen ^ L) 0 t1)
    (h2 : LoadHolds rd (gen ^ (10 - L)) 0 t2) (z : E) (q : ℕ × ℕ × ℕ × ℕ) (bw bb : ℕ) (c0 c1 : E) :
    ∀ st ∈ dvP, SHolds (fun _ _ _ => True) rd (Val.ofArgs (dvVals r L s t1 t2 z q bw bb c0 c1)) st := by
  intro st hs
  simp only [dvP, core_eq% «da_verify», core_eq% «da_verify» body, List.dropLast_cons_cons,
      List.dropLast_singleton, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals simp only [SHolds, Atom.Holds, ofArgs_n, dvVals, List.getD_cons_succ, List.getD_cons_zero]
  all_goals first
    | exact ⟨h1, by rw [word_g10, ← pow_add]; congr 1; omega, h2⟩
    | exact ⟨by rw [word_one]; exact one_add_gen_isInK _, fun _ => True.intro⟩
    | exact ⟨L, by simp; omega, by rw [gen_pow_eq_ofK], True.intro⟩
    | (rw [← pow_add]; ring_nf)

set_option maxRecDepth 20000 in
/-- `da_verify`'s dispatch is at `g^L`, `L ≤ 10`. -/
theorem dv_dispOk (r L s : ℕ) (hL : L ≤ 10) (t1 t2 z : E) (q : ℕ × ℕ × ℕ × ℕ) (bw bb : ℕ) (c0 c1 : E) :
    ∀ st ∈ dvP, B1.DispOk (Val.ofArgs (dvVals r L s t1 t2 z q bw bb c0 c1)) st := by
  intro st hs
  simp only [dvP, core_eq% «da_verify», core_eq% «da_verify» body, List.dropLast_cons_cons,
      List.dropLast_singleton, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact True.intro
    | exact ⟨L, by simp; omega, by omega, by simp [ofArgs_n, dvVals, gen_pow_eq_ofK]⟩

theorem kidsAt_lins : ∀ (ks : List KidD) (prev outs : List (List E × Layout)) (q : ℕ × List E),
    q ∈ B1.Kid.lins (kidsAt ks prev outs) →
      ∃ j, ∃ hj : j < ks.length, ∃ _ : j < outs.length, q ∈ (ks[j] (prev ++ outs.take j)).Lin
  | k :: ks, prev, o :: os, q, hq => by
    simp only [kidsAt, B1.Kid.lins, List.flatMap_cons, List.mem_append] at hq
    rcases hq with hq | hq
    · exact ⟨0, by simp, by simp, by simpa using hq⟩
    · obtain ⟨j, hj, ho, hq⟩ := kidsAt_lins ks (prev ++ [o]) os q hq
      exact ⟨j + 1, by simpa using hj, by simpa using ho, by simpa [List.take_succ_cons] using hq⟩
  | [], _, _, _, hq => by simp [kidsAt, B1.Kid.lins] at hq
  | _ :: _, _, [], _, hq => by simp [kidsAt, B1.Kid.lins] at hq

theorem kidsAt_outsOk : ∀ (ks : List KidD) (prev outs : List (List E × Layout)),
    OutsOk (kidsAt ks prev outs) outs → ∀ j (hj : j < ks.length) (ho : j < outs.length),
      (ks[j] (prev ++ outs.take j)).taken = true →
        (ks[j] (prev ++ outs.take j)).Out outs[j].1 outs[j].2
  | k :: ks, prev, o :: os, ⟨h, hs⟩, j, hj, ho, ht => by
    cases j with
    | zero => simpa using h (by simpa using ht)
    | succ j =>
      have := kidsAt_outsOk ks (prev ++ [o]) os hs j (by simpa using hj) (by simpa using ho)
        (by simpa [List.take_succ_cons] using ht)
      simpa [List.take_succ_cons] using this
  | [], _, _, _, _, hj, _, _ => absurd hj (by simp)
  | _ :: _, _, [], _, _, _, ho, _ => absurd ho (by simp)

theorem kidsAt_outsL : ∀ (ks : List KidD) (prev outs : List (List E × Layout)) (j : ℕ)
    (hj : j < ks.length) (ho : j < outs.length), (ks[j] (prev ++ outs.take j)).taken = true →
      ∀ q ∈ outs[j].2, q ∈ outsL (kidsAt ks prev outs) outs
  | k :: ks, prev, o :: os, j, hj, ho, ht, q, hq => by
    simp only [kidsAt, outsL, List.mem_append]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_zero, List.append_nil] at ht hq
      exact Or.inl (by rw [ite_pos' ht]; exact hq)
    | succ j =>
      exact Or.inr (kidsAt_outsL ks (prev ++ [o]) os j (by simpa using hj) (by simpa using ho)
        (by simpa [List.take_succ_cons] using ht) q (by simpa using hq))
  | [], _, _, _, hj, _, _, _, _ => absurd hj (by simp)
  | _ :: _, _, [], _, _, ho, _, _, _ => absurd ho (by simp)

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 20000 in
/-- **`da_verify` is complete, placed, by a tree of its honest shape exposing the hinted words, within `dvB`**, on
`r` blobs of cells `syms` orthogonal to the dual codeword of `z`, the exponent table's `g^(2^L)` at `g^(s + L)`; its
blobs by trees of their honest shape. -/
theorem dv_completeAtB_z (hrf : Lift.RunsFit fs cert) {SB SK : String → ℕ} (hS : DvStaticB fs SB SK)
    {r L : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ LeanDa.maxRows) (hL : 2 ^ L = LeanDa.paddedRowCount r)
    {syms : ℕ → ℕ → List K} (hsl : ∀ i j, (syms i j).length = 256)
    {z : E} (hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      dualAt z (256 * h + e) * ofK ((syms i h).getD e 0) = 0) (s : ℕ) :
    CompleteAtDTB fs cert 16 "da_verify" [(s + L, [gen ^ 2 ^ L])] [gen ^ s]
      (Returns (digestCells (daRoot r L syms) ++ [z]))
      (dvNHzC r L z (blobLFrom r (fun i => blobNH fs SB SK syms i) r 0)) (dvB fs SB SK r L) := by
  -- the shape
  have hr' : r ≤ 1024 := hr
  obtain ⟨hlo, hhi⟩ := nPad_bounds hr1
  have hrL : r ≤ 2 ^ L := hL ▸ hlo
  have hlt : 2 ^ L < 2 ^ 11 := by
    calc 2 ^ L < 2 * r := hL ▸ hhi
      _ ≤ 2 ^ 11 := by norm_num; omega
  have hL10 : L ≤ 10 := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  have hN : 2 ^ L ≤ 1024 := le_trans (Nat.pow_le_pow_right (by norm_num) hL10) (by norm_num)
  have hdlL : TotalLe coreProgram fs (daLevelsName L) (fun _ => SB (daLevelsName L)) := by
    have := hS.dl L hL10; rwa [dlNames_bang hL10] at this
  have hdl7 : TotalLe coreProgram fs "da_levels__L128_L7" (fun _ => SB "da_levels__L128_L7") := by
    have := hS.dl 7 (by norm_num); rwa [dlNames_bang (by norm_num)] at this
  have hcok := dv_cok
  unfold dvCOk at hcok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcok
  obtain ⟨⟨⟨⟨hflat, hni⟩, haddr⟩, halloc⟩, hloads⟩ := hcok
  have hb : Fn.body fn% «da_verify» = dvP ++ [.ret [.n 23, .n 24, .n 25]] := rfl
  have hbufL : ∀ bb, bufL bb (dvSizes r L) [rootsCells r L syms] = [(bb, rootsCells r L syms)] :=
    fun bb => by simp [bufL, bases, dvSizes]
  refine ((completeAt_flatDepRet (fs := fs) (cert := cert) find_da_verify
    (by rw [Program.loop_of_find? find_da_verify]; decide +kernel) 16 [(s + L, [gen ^ 2 ^ L])] [gen ^ s]
    (fun _ _ => digestCells (daRoot r L syms) ++ [z]) _ hb hflat haddr hni (dvSizes r L)
    (fun _ => [rootsCells r L syms]) (fun _ => by simp [dvSizes, length_rootsCells])
    (fun fp => dvKids r L syms z s (fp + fs "da_verify"))
    ["da_row_shape", "da_vector", "da_weights", name% «da_verify_loop0», rtName L]
    (dvKBs fs SB SK r L) (dvTsC r L (blobLFrom r (fun i => blobNH fs SB SK syms i) r 0)) (dvQz r L z)
    (fun _ => .cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl)
      (.cons (fun _ => rfl) .nil)))))
    (fun fp => ?_) (fun _ _ _ _ => rfl) (fun fp outs ho => ?_) (fun fp outs ho rd _ hB hLin hO => ?_)
    (fun fp outs hlen ho rd hlow _ _ _ => ?_)).mono ?_ (fun t ht => nodeHonest_mono ht
      (namedP_forall₂ _ _ _ rfl rfl)))
  · -- the callees, within their bounds
    set bb := fp + fs "da_verify"
    refine ⟨fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩, trivial⟩
    · exact row_shape_completeAtB fs cert hr1 hr hL
    · refine (vec_completeAtB fs cert hrf hS.off [] z).mono ?_ fun _ h => h
      have := hS.vec
      simp only [vecB, vecBs, offKB, List.sum_cons, List.sum_nil] at this ⊢
      omega
    · exact ((ws_completeAtB (fs := fs) (cert := cert) hrf z _ _ _ _).toDTB).mono hS.ws fun _ h => h
    · exact blobL_completeAtTB fs cert hr1 hrL hL10 (List.mem_append_right _ (List.mem_singleton_self _))
        (fun i hi => blob_completeAtB fs cert hS.cell hdl7 hi (hsl i) (hdot i hi)
          (List.mem_append_left _ List.mem_cons_self)
          (fun k hk => List.mem_append_left _ (List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))) hS.blob
    · exact rt_completeAtB fs cert hS.pad hdlL hrL hL10
  · -- the callees' regions
    set bb := fp + fs "da_verify"
    have hown : ∀ i, RegionL [(bb, rootsCells r L syms)] i →
        RegionL (bufL bb (dvSizes r L) [rootsCells r L syms]) i := fun i hi => by rw [hbufL]; exact hi
    match outs, ho with
    | [], _ => trivial
    | o1 :: os, ho =>
    refine ⟨fun _ i hi => Or.inl (Or.inl hi), ?_⟩
    match os, ho with
    | [], _ => trivial
    | o2 :: os, ho =>
    obtain ⟨-, h2, h3o⟩ := ho
    have hv := dvVb_spec (z := z) (pv := [o1, o2]) (h2 rfl)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hv
    refine ⟨fun _ i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq, ?_⟩
    match os, h3o with
    | [], _ => trivial
    | o3 :: os, h3o =>
    refine ⟨fun _ i hi => ?_, ?_⟩
    · obtain ⟨q, hq, h1, h2⟩ := hi
      simp only [List.nil_append, wsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr ⟨rfl, _, hv.2.1, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨rfl, _, hv.2.2.1, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨rfl, _, hv.2.2.2.1, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨rfl, _, hv.2.2.2.2, h1, h2⟩)
    match os, h3o with
    | [], _ => trivial
    | o4 :: os, h3o =>
    have hw := dvW_spec (z := z) (pv := [o1, o2, o3]) (h3o.1 rfl)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hw
    refine ⟨fun _ i hi => ?_, ?_⟩
    · obtain ⟨q, hq, h1, h2⟩ := hi
      simp only [List.nil_append, List.cons_append, dvBlobLin, List.mem_cons, List.mem_append,
        List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | ⟨k, hk, rfl⟩ | rfl
      · exact Or.inr (Or.inr ⟨rfl, _, hw.2.1, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨rfl, _, hw.2.2 k hk, h1, h2⟩)
      · exact Or.inl (Or.inr (hown i ⟨_, List.mem_cons_self, h1, h2⟩))
    match os with
    | [] => trivial
    | o5 :: os =>
    exact ⟨fun _ i hi => Or.inl (Or.inr (hown i hi)), by cases os <;> trivial⟩
  · -- what the callees read
    set bb := fp + fs "da_verify"
    rw [hbufL] at hB
    intro q hq
    obtain ⟨j, hj, hjo, hq⟩ := kidsAt_lins _ [] outs q hq
    simp only [dvKids, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simp only [dvKids, List.getElem_cons_zero, List.mem_singleton] at hq
      subst hq; exact hLin _ List.mem_cons_self
    · simp [dvKids] at hq
    · have h2 : vecOut z outs[1].1 outs[1].2 :=
        kidsAt_outsOk _ [] outs ho 1 (by simp [dvKids]) (by omega) rfl
      have hg : (outs.take 2).getD 1 ([], []) = outs[1] := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take]
      have hv := dvVb_spec (z := z) (pv := outs.take 2) (by rw [hg]; exact h2)
      rw [hg] at hv
      have hO1 : ∀ q ∈ outs[1].2, q ∈ outsL (kidsAt (dvKids r L syms z s bb) [] outs) outs :=
        kidsAt_outsL _ [] outs 1 (by simp [dvKids]) (by omega) rfl
      simp only [dvKids, List.getElem_cons_succ, List.getElem_cons_zero, List.nil_append, wsLin,
        List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hO _ (hO1 _ hv.2.1)
      · exact hO _ (hO1 _ hv.2.2.1)
      · exact hO _ (hO1 _ hv.2.2.2.1)
      · exact hO _ (hO1 _ hv.2.2.2.2)
    · have h3 : wOut z outs[2].1 outs[2].2 :=
        kidsAt_outsOk _ [] outs ho 2 (by simp [dvKids]) (by omega) rfl
      have hg : (outs.take 3).getD 2 ([], []) = outs[2] := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take]
      have hw := dvW_spec (z := z) (pv := outs.take 3) (by rw [hg]; exact h3)
      rw [hg] at hw
      have hO2 : ∀ q ∈ outs[2].2, q ∈ outsL (kidsAt (dvKids r L syms z s bb) [] outs) outs :=
        kidsAt_outsL _ [] outs 2 (by simp [dvKids]) (by omega) rfl
      simp only [dvKids, List.getElem_cons_succ, List.getElem_cons_zero, List.nil_append, dvBlobLin,
        List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil, or_false, or_assoc] at hq
      rcases hq with rfl | ⟨k, hk, rfl⟩ | rfl
      · exact hO _ (hO2 _ hw.2.1)
      · exact hO _ (hO2 _ (hw.2.2 k hk))
      · exact hB _ List.mem_cons_self
    · simp only [dvKids, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_singleton] at hq
      subst hq; exact hB _ List.mem_cons_self
  · -- the valuation
    set bb := fp + fs "da_verify"
    match outs, hlen, ho with
    | [o1, o2, o3, o4, o5], _, ho =>
    have h1 : o1.1 = [gen ^ 2 ^ L, gen ^ (2 ^ L - r)] :=
      (kidsAt_outsOk _ [] _ ho 0 (by simp [dvKids]) (by simp) rfl).1
    have h2 : vecOut z o2.1 o2.2 := kidsAt_outsOk _ [] _ ho 1 (by simp [dvKids]) (by simp) rfl
    have h3 : wOut z o3.1 o3.2 := kidsAt_outsOk _ [] _ ho 2 (by simp [dvKids]) (by simp) rfl
    have h4 : o4.1 = [] := (kidsAt_outsOk _ [] _ ho 3 (by simp [dvKids]) (by simp) rfl).1
    have h5 : o5.1 = digestCells (daRoot r L syms) :=
      (kidsAt_outsOk _ [] _ ho 4 (by simp [dvKids]) (by simp) rfl).1
    have hv := dvVb_spec (z := z) (pv := [o1, o2]) (by simpa using h2)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hv
    have hw := dvW_spec (z := z) (pv := [o1, o2, o3]) (by simpa using h3)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hw
    obtain ⟨t1, t2, ht1, -, ht2⟩ := rc_holds' hlow (k := L) (K := 10) hL10 (by norm_num)
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = Val.ofArgs (dvVals r L s t1 t2 z (dvVb z [o1, o2]) (dvW z [o1, o2, o3]).1 bb
        (digestHalves (daRoot r L syms)).1 (digestHalves (daRoot r L syms)).2) := ⟨_, rfl⟩
    have hall := dv_sholds (rd := rd) r L s hL10 ht1 ht2 z (dvVb z [o1, o2]) (dvW z [o1, o2, o3]).1 bb
      (digestHalves (daRoot r L syms)).1 (digestHalves (daRoot r L syms)).2
    have hdisp := dv_dispOk r L s hL10 t1 t2 z (dvVb z [o1, o2]) (dvW z [o1, o2, o3]).1 bb
      (digestHalves (daRoot r L syms)).1 (digestHalves (daRoot r L syms)).2
    rw [← hσ] at hall hdisp
    have s2 : σ (.n 2) = gen ^ L := by rw [hσ]; rfl
    have hlogL : logG (σ (.n 2)) = L := by rw [s2]; exact logG_gen_pow (by omega)
    have hne : (1 : E) + gen ^ r ≠ 0 := one_add_gen_pow_ne_zero (by omega) (by unfold ordG; omega)
    refine ⟨σ, by rw [hσ]; rfl, hdisp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hb]
      refine holdsList_straight _ _ _ _ hall ?_
      simp [hσ, ofArgs_n, dvVals, digestCells]
    · rw [halloc]
      simp only [List.map_cons, List.map_nil, Sum.elim_inr, hσ, ofArgs_n, dvVals, dvSizes,
        List.getD_cons_succ, List.getD_cons_zero]
      rw [logG_gen_pow (by omega)]
    · rw [halloc]
      simp [hσ, ofArgs_n, dvVals, bases, dvSizes, gen_pow_eq_ofK]
    · simp only [flatCalls, dv_callsSF, hlogL, dvCallsS, List.map_cons, List.map_nil, Main.mkCall, kidsAt,
        dvKids, List.nil_append, List.cons_append]
      refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, ?_,
        fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      all_goals simp [hσ, ofArgs_n, dvVals, h1, hv.1, hw.1, h4, h5, word_one, hne, digestCells]
    · rw [hloads]
      simp
    · exact ⟨⟨by rw [hσ]; rfl, s2, by rw [hσ]; rfl, by rw [hσ]; show word 1 0 + _ = _; rw [word_one],
        by rw [hσ]; exact word_one⟩, by rw [hσ]; rfl⟩
  · simp only [dvB, dvKB, dvKBs, List.sum_cons, List.sum_nil]
    omega

/-- **`da_verify` is complete, placed, by a tree of its honest shape, within `dvB`** (`dv_completeAtB_z`, the
challenge and the blobs' shapes forgotten). -/
theorem dv_completeAtB (hrf : Lift.RunsFit fs cert) {SB SK : String → ℕ} (hS : DvStaticB fs SB SK)
    {r L : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ LeanDa.maxRows) (hL : 2 ^ L = LeanDa.paddedRowCount r)
    {syms : ℕ → ℕ → List K} (hsl : ∀ i j, (syms i j).length = 256)
    {z : E} (hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      dualAt z (256 * h + e) * ofK ((syms i h).getD e 0) = 0) (s : ℕ) :
    CompleteAtDTB fs cert 16 "da_verify" [(s + L, [gen ^ 2 ^ L])] [gen ^ s]
      (Returns (digestCells (daRoot r L syms) ++ [z])) (dvNH r L) (dvB fs SB SK r L) :=
  (dv_completeAtB_z fs cert hrf hS hr1 hr hL hsl hdot s).mono le_rfl fun _ => dvNH_of_zC

end
end LeanVM.Guest.B1.Da
