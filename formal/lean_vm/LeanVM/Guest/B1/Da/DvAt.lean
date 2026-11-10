/-
  LeanVM.Guest.B1.Da.DvAt

  `da_verify` placed (G:4323-4363): the shape, the dual codeword, every blob's region and its
  columns, the blobs' trees and the padding, the tree over the roots, within its words bound
  before the memory (`dvB`), by a tree of its honest shape (`dvNH r L`).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.ColAt
public import LeanVM.Guest.B1.Da.ColLoopAt
public import LeanVM.Guest.B1.Da.AtTB
public import LeanVM.Guest.B1.Da.DvBound
public import LeanVM.Guest.Value.KeccakDuplex

/-!
# `da_verify`, placed

Its buffers at `bb = fp + fs da_verify`: the regions (`blobsCells`), their bases at `bR = bb + 641 r`
(`rowbaseCells`), the roots' tree at `bT = bR + r` (`rootsCells`). Its callees in call order: the
row shape (`row_shape_completeAtB`), the dual codeword (`vec_completeAtB`), the regions' bases
(`l17_rel`), the column loop (`l18_completeAtTB` of `col_completeAtB`, on `da_vector`'s buffers read
off its result, `dvVb`), the blobs' trees (`l19_rel`), the padding (`l20_rel`), the roots' tree
(`dl_rel`). `dvNH r L`: its honest shape; `dv_completeAtB`: complete within `dvB`, returning the
root's cells and the challenge's rate cells.
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

/-- The DA levels' names, as `da_verify`'s dispatch lists them. -/
def dlList : List String :=
  ["da_levels__L1_L0", "da_levels__L2_L1", "da_levels__L4_L2", "da_levels__L8_L3",
    "da_levels__L16_L4", "da_levels__L32_L5", "da_levels__L64_L6", "da_levels__L128_L7",
    "da_levels__L256_L8", "da_levels__L512_L9", "da_levels__L1024_L10"]

theorem dlList_getD {L : ℕ} (hL : L ≤ 10) : dlList.getD L "" = daLevelsName L := by
  interval_cases L <;> rfl

theorem dlNames_bang {L : ℕ} (hL : L ≤ 10) : dlNames[L]! = daLevelsName L := by
  interval_cases L <;> rfl

/-- `da_verify`'s calls, the dispatch at `j`. -/
def dvCallsS (j : ℕ) : List (Option V × String × List V × List V) :=
  [(none, "da_row_shape", [.n 1, .n 2, .n 0], [.n 3, .n 4]),
    (none, "da_vector", [.n 5], [.n 16, .n 17, .n 18, .n 19]),
    (some (.n 34), "__loop21", [.n 35, .n 1, .n 31, .n 32], []),
    (none, "__loop22", [.n 36, .n 1, .n 32, .n 16, .n 17, .n 18, .n 19], []),
    (some (.n 41), "__loop23", [.n 42, .n 1, .n 32, .n 39], []),
    (some (.n 44), "__loop24", [.n 45, .n 4, .n 39, .n 1], []),
    (none, dlList.getD j "", [.n 39], [.n 46, .n 47])]

theorem dv_callsSF (σ : Val) : dvP.filterMap (Stmt.callSF σ) = dvCallsS (logG (σ (.n 2))) := rfl

theorem dv_flatCalls (σ : Val) : flatCalls dvP σ = (dvCallsS (logG (σ (.n 2)))).map (Main.mkCall σ) := by
  rw [flatCalls, dv_callsSF]

/-- **`da_verify`'s block, its shape** (kernel evaluation). -/
noncomputable def dvCOk : Bool :=
  dvP.all Core.Stmt.flat && dvP.all B1.notIteB && decide (dvP.filterMap Stmt.addrS = []) &&
  decide (dvP.filterMap Stmt.allocSz = [(.n 31, .inr (.n 30)), (.n 32, .inr (.n 1)), (.n 39, .inr (.n 38))]) &&
  decide (dvP.filterMap Stmt.loadS = [])

theorem dv_cok : dvCOk = true := by decide +kernel

/-- `da_vector`'s four bases read off its result. -/
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

/-- A column's words bound, its callees' frames and its row loop's `r` iterations and phantom
frame. -/
def colBf (fs : String → ℕ) (SK : String → ℕ) (r : ℕ) : ℕ :=
  fs "da_verify_column" + (fs "da_expand__L7_L8" + (r * iterK fs SK "__loop25" + fs "__loop25"))

/-- `da_verify`'s callees' bounds, in call order, at the frame sizes. -/
def dvBs (fs : String → ℕ) (SB SK : String → ℕ) (r L : ℕ) : List ℕ :=
  [fs "da_row_shape", vecB fs SK, r * iterK fs SK "__loop21" + fs "__loop21",
    clB fs "__loop22" (colBf fs SK r) 128, r * iterK fs SK "__loop23" + fs "__loop23",
    if 2 ^ L - r ≠ 0 then (2 ^ L - r) * iterK fs SK "__loop24" + fs "__loop24" else fs "__loop24",
    SB (daLevelsName L)]

/-- `da_verify`'s callees, on its buffers at `bb`. -/
noncomputable def dvKids (r L : ℕ) (syms : ℕ → ℕ → List K) (z : E) (s bb : ℕ) : List KidD :=
  [fun _ => ⟨"da_row_shape", true, [gen ^ r, gen ^ L, gen ^ s], [(s + L, [gen ^ 2 ^ L])],
      Returns [gen ^ 2 ^ L, gen ^ (2 ^ L - r)]⟩,
    fun _ => ⟨"da_vector", true, [z], [], vecOut z⟩,
    fun _ => ⟨"__loop21", true, [1, gen ^ r, gen ^ bb, gen ^ (bb + 641 * r)],
      [(bb, blobsCells r syms z), (bb + 641 * r, rowbaseCells r bb)], Returns []⟩,
    fun pv => ⟨"__loop22", true, [1, gen ^ r, gen ^ (bb + 641 * r), gen ^ (dvVb z pv).1,
      gen ^ ((dvVb z pv).2.1 + 2 ^ 7), gen ^ (dvVb z pv).2.2.1, gen ^ (dvVb z pv).2.2.2],
      colLin r syms z (dvVb z pv).1 (dvVb z pv).2.1 (dvVb z pv).2.2.1 (dvVb z pv).2.2.2 bb (bb + 641 * r),
      Returns []⟩,
    fun _ => ⟨"__loop23", true, [1, gen ^ r, gen ^ (bb + 641 * r), gen ^ (bb + 641 * r + r)],
      [(bb, blobsCells r syms z), (bb + 641 * r, rowbaseCells r bb),
        (bb + 641 * r + r, rootsCells r L syms)], Returns []⟩,
    fun _ => ⟨"__loop24", decide (2 ^ L - r ≠ 0), [1, gen ^ (2 ^ L - r), gen ^ (bb + 641 * r + r), gen ^ r],
      [(bb + 641 * r + r, rootsCells r L syms)], Returns []⟩,
    fun _ => ⟨daLevelsName L, true, [gen ^ (bb + 641 * r + r)], [(bb + 641 * r + r, rootsCells r L syms)],
      Returns (digestCells (daRoot r L syms))⟩]

/-- The rate cells of the challenge, as `fs_pack` computes them from its top limb. -/
def zCells (z : E) : List E :=
  [z + word 0 0 1 * ofK (z.limb 2), ofK (z.limb 2) + word 0 1 * word 0 0]

theorem zCells_eq (z : E) :
    zCells z = [(scalarCells z 0).1, (scalarCells z 0).2] := by
  have hc := (top_pin_iff z (ofK (z.limb 2))).mpr rfl
  obtain ⟨-, he⟩ := fsPack_cells z (ofK (z.limb 2)) 0 hc.1 hc.2
  rw [← he, zCells, word_yy, word_y, word_eOfNat]

/-- `da_verify`'s valuation. -/
def dvVals (r L s : ℕ) (z : E) (q : ℕ × ℕ × ℕ × ℕ) (bb : ℕ) (c0 c1 : E) : List E :=
  [gen ^ s, gen ^ r, gen ^ L, gen ^ 2 ^ L, gen ^ (2 ^ L - r), z, word 0 0, ofK (z.limb 0),
    ofK (z.limb 1), ofK (z.limb 2), word 0 0 1, word 0 0 1 * ofK (z.limb 2),
    z + word 0 0 1 * ofK (z.limb 2), word 0 1, word 0 1 * word 0 0,
    ofK (z.limb 2) + word 0 1 * word 0 0, gen ^ q.1, gen ^ (q.2.1 + 2 ^ 7), gen ^ q.2.2.1,
    gen ^ q.2.2.2, gen ^ (2 * r), gen ^ (4 * r), gen ^ (5 * r), gen ^ (10 * r), gen ^ (20 * r),
    gen ^ (40 * r), gen ^ (80 * r), gen ^ (160 * r), gen ^ (320 * r), gen ^ (640 * r),
    gen ^ (641 * r), gen ^ bb, gen ^ (bb + 641 * r), word 1 0, word 1 0 + gen ^ r, word 1 0,
    word 1 0, gen ^ (2 * 2 ^ L), gen ^ (4 * 2 ^ L), gen ^ (bb + 641 * r + r), word 1 0,
    word 1 0 + gen ^ r, word 1 0, word 1 0, word 1 0 + gen ^ (2 ^ L - r), word 1 0, c0, c1,
    c0, c1, z + word 0 0 1 * ofK (z.limb 2), ofK (z.limb 2) + word 0 1 * word 0 0]

/-- **`da_verify`'s honest shape**: its counts, its loops' starts and the padding's guard, its
dispatch. -/
def dvQ (r L : ℕ) (σ : Val) : Prop :=
  σ (.n 1) = gen ^ r ∧ σ (.n 2) = gen ^ L ∧ σ (.n 4) = gen ^ (2 ^ L - r) ∧ σ (.n 35) = 1 ∧
    σ (.n 42) = 1 ∧ σ (.n 44) = 1 + gen ^ (2 ^ L - r) ∧ σ (.n 45) = 1

/-- The predicates on `da_verify`'s callees' trees: the column loop's honest shape. -/
def dvTs (r : ℕ) : List (Tree → Prop) :=
  [fun _ => True, fun _ => True, fun _ => True, l18From (colNH r) 128 0, fun _ => True,
    fun _ => True, fun _ => True]

/-- **`da_verify`'s honest shape** on `r` blobs padded to `2^L`. -/
def dvNH (r L : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "da_verify" (dvQ r L) (flatCalls dvP) (fun _ => dvSizes r L) (dvTs r)

theorem pow_mul_eq {a b : ℕ} : gen ^ (a + b) = gen ^ a * gen ^ b := pow_add gen a b

set_option maxRecDepth 20000 in
/-- **`da_verify`'s statements hold** on its valuation. -/
theorem dv_sholds {rd : Reader} (r L s : ℕ) (hL : L ≤ 10) (z : E) (q : ℕ × ℕ × ℕ × ℕ) (bb : ℕ)
    (c0 c1 : E) :
    ∀ st ∈ dvP, SHolds (fun _ _ _ => True) rd (Val.ofArgs (dvVals r L s z q bb c0 c1)) st := by
  intro st hs
  simp only [dvP, Data.core27, Data.core27.body, List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [SHolds, Atom.Holds, ofArgs_n, dvVals, List.getD_cons_succ,
    List.getD_cons_zero]
  all_goals first
    | exact ⟨ofK_isInK _, by rw [word_zero, ← ofK_zero]; exact ofK_isInK 0⟩
    | exact ⟨by rw [word_one]; exact one_add_gen_isInK _, fun _ => True.intro⟩
    | exact ⟨L, by simp; omega, by rw [gen_pow_eq_ofK], True.intro⟩
    | (rw [← pow_add]; ring_nf)

theorem one_add_gen_ne_iff {m : ℕ} (hm : m < ordG) : (1 + gen ^ m ≠ 0) ↔ m ≠ 0 :=
  ⟨fun h hm0 => h (by subst hm0; rw [pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
    fun h => one_add_gen_pow_ne_zero (by omega) hm⟩

set_option maxRecDepth 20000 in
/-- `da_verify`'s dispatch is at `g^L`, `L ≤ 10`. -/
theorem dv_dispOk (r L s : ℕ) (hL : L ≤ 10) (z : E) (q : ℕ × ℕ × ℕ × ℕ) (bb : ℕ) (c0 c1 : E) :
    ∀ st ∈ dvP, B1.DispOk (Val.ofArgs (dvVals r L s z q bb c0 c1)) st := by
  intro st hs
  simp only [dvP, Data.core27, Data.core27.body, List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
/-- **`da_verify` is complete, placed, by a tree of its honest shape, within its frame, its
buffers and its callees' bounds**, on `r` blobs of cells `syms` orthogonal to the dual codeword of
`z`, the exponent table's `g^(2^L)` at `g^(s + L)`. -/
theorem dv_completeAtB (hrf : Lift.RunsFit fs cert) {SB SK : String → ℕ}
    (hT : ∀ b < 7, TotalLeOn coreProgram fs (offLoopName b) LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK (offLoopName b) + fs (offLoopName b)))
    (h17 : TotalLeOn coreProgram fs "__loop21" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop21" + fs "__loop21"))
    (h19 : TotalLeOn coreProgram fs "__loop23" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop23" + fs "__loop23"))
    (h20 : TotalLeOn coreProgram fs "__loop24" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop24" + fs "__loop24"))
    (h21 : TotalLeOn coreProgram fs "__loop25" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop25" + fs "__loop25"))
    {r L : ℕ} (hdl : TotalLe coreProgram fs (daLevelsName L) (fun _ => SB (daLevelsName L)))
    (hr1 : 1 ≤ r) (hr : r ≤ LeanDa.maxRows) (hL : 2 ^ L = LeanDa.paddedRowCount r)
    {syms : ℕ → ℕ → List K} (hsl : ∀ i j, (syms i j).length = 256)
    {z : E} (hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      dualAt z (256 * h + e) * ofK ((syms i h).getD e 0) = 0) (s : ℕ) :
    CompleteAtDTB fs cert 16 "da_verify" [(s + L, [gen ^ 2 ^ L])] [gen ^ s]
      (Returns (digestCells (daRoot r L syms) ++ zCells z)) (dvNH r L)
      (fs "da_verify" + (dvSizes r L).sum + (dvBs fs SB SK r L).sum) := by
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
  have hcok := dv_cok
  unfold dvCOk at hcok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcok
  obtain ⟨⟨⟨⟨hflat, hni⟩, haddr⟩, halloc⟩, hloads⟩ := hcok
  have hb : Fn.body Data.core27 = dvP ++ [.ret [.n 48, .n 49, .n 50, .n 51]] := rfl
  have hbufL : ∀ bb, bufL bb (dvSizes r L) [blobsCells r syms z, rowbaseCells r bb, rootsCells r L syms] =
      [(bb, blobsCells r syms z), (bb + 641 * r, rowbaseCells r bb), (bb + 641 * r + r, rootsCells r L syms)] :=
    fun bb => by simp [bufL, bases, dvSizes]
  refine ((completeAt_flatDepRet (fs := fs) (cert := cert) find_da_verify
    (by rw [Program.loop_of_find? find_da_verify]; decide +kernel) 16 [(s + L, [gen ^ 2 ^ L])] [gen ^ s]
    (fun _ _ => digestCells (daRoot r L syms) ++ zCells z) _ hb hflat haddr hni (dvSizes r L)
    (fun fp => [blobsCells r syms z, rowbaseCells r (fp + fs "da_verify"), rootsCells r L syms])
    (fun _ => by simp [dvSizes, length_blobsCells, rowbaseCells, length_rootsCells])
    (fun fp => dvKids r L syms z s (fp + fs "da_verify"))
    ["da_row_shape", "da_vector", "__loop21", "__loop22", "__loop23", "__loop24", daLevelsName L]
    (dvBs fs SB SK r L) (dvTs r) (dvQ r L)
    (fun _ => .cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl)
      (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)))))))
    (fun fp => ?_) (fun _ _ _ _ => rfl) (fun fp outs ho => ?_) (fun fp outs ho rd _ hB hLin hO => ?_)
    ?_).mono le_rfl (fun t ht => nodeHonest_mono ht (namedP_forall₂ _ _ _ rfl rfl)))
  · -- the callees, within their bounds
    set bb := fp + fs "da_verify"
    refine ⟨fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩,
      fun pv => ⟨fun ht => ?_, fun ht => ?_⟩,
      fun pv => ⟨fun _ => ?_, fun h => absurd h (by simp)⟩, trivial⟩
    · exact row_shape_completeAtB fs cert hr1 hr hL
    · exact vec_completeAtB fs cert hrf hT [] z
    · exact pureB_loop daPure (by simp [daPureSet]) (fun rd hm => l17_rel hr1
        (reads_of_memL hm List.mem_cons_self) (reads_of_memL hm (List.mem_cons_of_mem _
          List.mem_cons_self))) h17 (by omega) (by omega)
    · have := l18_completeAtTB fs cert (ps := [gen ^ r, gen ^ (bb + 641 * r), gen ^ (dvVb z pv).1,
        gen ^ ((dvVb z pv).2.1 + 2 ^ 7), gen ^ (dvVb z pv).2.2.1, gen ^ (dvVb z pv).2.2.2]) rfl
        (Lin := colLin r syms z (dvVb z pv).1 (dvVb z pv).2.1 (dvVb z pv).2.2.1 (dvVb z pv).2.2.2 bb
          (bb + 641 * r)) (a := 0)
        (fun k _ hk => col_completeAtB fs cert hrf h21 hr1 hr' hsl (z := z) (bb := bb) hk) 0 le_rfl
        (by norm_num)
      rw [pow_zero, Nat.sub_zero] at this
      exact this
    · exact pureB_loop daPure (by simp [daPureSet]) (fun rd hm => l19_rel hr1 hrL
        (reads_of_memL hm List.mem_cons_self)
        (reads_of_memL hm (List.mem_cons_of_mem _ List.mem_cons_self))
        (reads_of_memL hm (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) hdot)
        h19 (by omega) (by omega)
    · have h0 : 2 ^ L - r ≠ 0 := by simpa [dvKids] using ht
      simp only [h0, ne_eq, not_false_eq_true, ↓reduceIte]
      exact pureB_loop daPure (by simp [daPureSet]) (fun rd hm => l20_rel (by omega)
        (reads_of_memL hm List.mem_cons_self)) h20 (by omega) (by omega)
    · have h0 : 2 ^ L - r = 0 := by simpa [dvKids] using ht
      simp [h0]
    · exact pureB_static daPure (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨L, List.mem_range.mpr (by omega), rfl⟩)))
        (fun rd hm => dl_rel hL10 (reads_of_memL hm List.mem_cons_self)) hdl
  · -- the callees' regions
    set bb := fp + fs "da_verify"
    have hown : ∀ {xs : List E} {b : ℕ}, (b, xs) ∈ bufL bb (dvSizes r L)
        [blobsCells r syms z, rowbaseCells r bb, rootsCells r L syms] → ∀ i,
        RegionL [(b, xs)] i → RegionL (bufL bb (dvSizes r L)
          [blobsCells r syms z, rowbaseCells r bb, rootsCells r L syms]) i :=
      fun hq i ⟨q, hq', h1, h2⟩ => ⟨q, by rw [List.mem_singleton] at hq'; subst hq'; exact hq, h1, h2⟩
    have hsub : ∀ {Lk : Layout}, (∀ q ∈ Lk, q ∈ bufL bb (dvSizes r L)
        [blobsCells r syms z, rowbaseCells r bb, rootsCells r L syms]) → ∀ i, RegionL Lk i →
        RegionL [(s + L, [gen ^ 2 ^ L])] i ∨ RegionL (bufL bb (dvSizes r L)
          [blobsCells r syms z, rowbaseCells r bb, rootsCells r L syms]) i :=
      fun hk i ⟨q, hq, h1, h2⟩ => Or.inr ⟨q, hk q hq, h1, h2⟩
    rw [hbufL] at hsub
    match outs, ho with
    | [], _ => trivial
    | o1 :: os, ho =>
    refine ⟨fun _ i hi => Or.inl (Or.inl hi), ?_⟩
    match os, ho with
    | [], _ => trivial
    | o2 :: os, ho =>
    obtain ⟨-, h2, -⟩ := ho
    have hv := dvVb_spec (z := z) (pv := [o1, o2]) (h2 rfl)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hv
    refine ⟨fun _ i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq, ?_⟩
    match os with
    | [] => trivial
    | o3 :: os =>
    refine ⟨fun _ i hi => Or.inl (hsub (fun q hq => by simp at hq ⊢; tauto) i hi), ?_⟩
    match os with
    | [] => trivial
    | o4 :: os =>
    refine ⟨fun _ i hi => ?_, ?_⟩
    · have hv3 := dvVb_spec (z := z) (pv := [o1, o2, o3]) (by simpa using h2 rfl)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at hv3
      obtain ⟨q, hq, h1, h2⟩ := hi
      simp only [colLin, List.mem_cons, List.not_mem_nil, or_false, List.nil_append,
        List.cons_append] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (Or.inr ⟨rfl, _, hv3.2.1, h1, h2⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨rfl, _, hv3.2.2.1, h1, h2⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨rfl, _, hv3.2.2.2.1, h1, h2⟩))
      · exact Or.inr (Or.inl (Or.inr ⟨rfl, _, hv3.2.2.2.2, h1, h2⟩))
      · exact Or.inl (hsub (fun q hq => by simp at hq ⊢; tauto) i ⟨_, List.mem_singleton_self _, h1, h2⟩)
      · exact Or.inl (hsub (fun q hq => by simp at hq ⊢; tauto) i ⟨_, List.mem_singleton_self _, h1, h2⟩)
    match os with
    | [] => trivial
    | o5 :: os =>
    refine ⟨fun _ i hi => Or.inl (hsub (fun q hq => by simp at hq ⊢; tauto) i hi), ?_⟩
    match os with
    | [] => trivial
    | o6 :: os =>
    refine ⟨fun _ i hi => Or.inl (hsub (fun q hq => by simp at hq ⊢; tauto) i hi), ?_⟩
    match os with
    | [] => trivial
    | o7 :: os =>
    exact ⟨fun _ i hi => Or.inl (hsub (fun q hq => by simp at hq ⊢; tauto) i hi), by cases os <;> trivial⟩
  · -- what the callees read
    set bb := fp + fs "da_verify"
    rw [hbufL] at hB
    intro q hq
    obtain ⟨j, hj, hjo, hq⟩ := kidsAt_lins _ [] outs q hq
    have hB' : ∀ q ∈ [(bb, blobsCells r syms z), (bb + 641 * r, rowbaseCells r bb),
        (bb + 641 * r + r, rootsCells r L syms)], ∀ k (hk : k < q.2.length),
        LoadHolds rd (ofK (addressOfIndex q.1)) k q.2[k] := hB
    simp only [dvKids, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simp only [dvKids, List.getElem_cons_zero, List.mem_singleton] at hq
      subst hq; exact hLin _ List.mem_cons_self
    · simp [dvKids] at hq
    · simp only [dvKids, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hB' _ List.mem_cons_self
      · exact hB' _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · have h2 : vecOut z outs[1].1 outs[1].2 :=
        kidsAt_outsOk _ [] outs ho 1 (by simp [dvKids]) (by omega) rfl
      have hg : (outs.take 3).getD 1 ([], []) = outs[1] := by
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take]
      have hv := dvVb_spec (z := z) (pv := outs.take 3) (by rw [hg]; exact h2)
      rw [hg] at hv
      have hO1 : ∀ q ∈ outs[1].2, q ∈ outsL (kidsAt (dvKids r L syms z s bb) [] outs) outs :=
        kidsAt_outsL _ [] outs 1 (by simp [dvKids]) (by omega) rfl
      simp only [dvKids, List.getElem_cons_succ, List.getElem_cons_zero, List.nil_append, colLin,
        List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hO _ (hO1 _ hv.2.1)
      · exact hO _ (hO1 _ hv.2.2.1)
      · exact hO _ (hO1 _ hv.2.2.2.1)
      · exact hO _ (hO1 _ hv.2.2.2.2)
      · exact hB' _ List.mem_cons_self
      · exact hB' _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · simp only [dvKids, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hB' _ List.mem_cons_self
      · exact hB' _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact hB' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · simp only [dvKids, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_singleton] at hq
      subst hq; exact hB' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · simp only [dvKids, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_singleton] at hq
      subst hq; exact hB' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · -- the valuation
    intro fp outs hlen ho rd _ _ _ _
    set bb := fp + fs "da_verify"
    match outs, hlen, ho with
    | [o1, o2, o3, o4, o5, o6, o7], _, ho =>
    have h1 : o1.1 = [gen ^ 2 ^ L, gen ^ (2 ^ L - r)] :=
      (kidsAt_outsOk _ [] _ ho 0 (by simp [dvKids]) (by simp) rfl).1
    have h2 : vecOut z o2.1 o2.2 := kidsAt_outsOk _ [] _ ho 1 (by simp [dvKids]) (by simp) rfl
    have h3 : o3.1 = [] := (kidsAt_outsOk _ [] _ ho 2 (by simp [dvKids]) (by simp) rfl).1
    have h4 : o4.1 = [] := (kidsAt_outsOk _ [] _ ho 3 (by simp [dvKids]) (by simp) rfl).1
    have h5 : o5.1 = [] := (kidsAt_outsOk _ [] _ ho 4 (by simp [dvKids]) (by simp) rfl).1
    have h7 : o7.1 = digestCells (daRoot r L syms) :=
      (kidsAt_outsOk _ [] _ ho 6 (by simp [dvKids]) (by simp) rfl).1
    have hv := dvVb_spec (z := z) (pv := [o1, o2]) (by simpa using h2)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hv
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = Val.ofArgs (dvVals r L s z (dvVb z [o1, o2]) bb
        (digestHalves (daRoot r L syms)).1 (digestHalves (daRoot r L syms)).2) := ⟨_, rfl⟩
    have hall := dv_sholds (rd := rd) r L s hL10 z (dvVb z [o1, o2]) bb
      (digestHalves (daRoot r L syms)).1 (digestHalves (daRoot r L syms)).2
    have hdisp := dv_dispOk r L s hL10 z (dvVb z [o1, o2]) bb
      (digestHalves (daRoot r L syms)).1 (digestHalves (daRoot r L syms)).2
    rw [← hσ] at hall hdisp
    have s2 : σ (.n 2) = gen ^ L := by rw [hσ]; rfl
    have hlogL : logG (σ (.n 2)) = L := by rw [s2]; exact logG_gen_pow (by omega)
    have hne : (1 : E) + gen ^ r ≠ 0 := one_add_gen_pow_ne_zero (by omega) (by unfold ordG; omega)
    have he3 : dvVb z [o1, o2, o3] = dvVb z [o1, o2] := by simp [dvVb]
    have h6 : 2 ^ L - r ≠ 0 → o6.1 = [] := fun h =>
      (kidsAt_outsOk _ [] _ ho 5 (by simp [dvKids]) (by simp)
        (by show decide (2 ^ L - r ≠ 0) = true; simpa using h)).1
    have h44 : σ (.n 44) ≠ 0 → 2 ^ L - r ≠ 0 := fun h hz => h (by
      rw [hσ]; show word 1 0 + gen ^ (2 ^ L - r) = 0
      rw [hz, pow_zero, word_one]; exact e_add_eq_zero_iff.mpr rfl)
    refine ⟨σ, by rw [hσ]; rfl, hdisp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hb]
      refine holdsList_straight _ _ _ _ hall ?_
      simp [hσ, ofArgs_n, dvVals, digestCells, zCells]
    · rw [halloc]
      simp only [List.map_cons, List.map_nil, Sum.elim_inr, hσ, ofArgs_n, dvVals, dvSizes,
        List.getD_cons_succ, List.getD_cons_zero]
      rw [logG_gen_pow (by omega), logG_gen_pow (by omega), logG_gen_pow (by omega)]
    · rw [halloc]
      simp [hσ, ofArgs_n, dvVals, bases, dvSizes, gen_pow_eq_ofK]
    · simp only [flatCalls, dv_callsSF, hlogL, dvCallsS, dlList_getD hL10, List.map_cons,
        List.map_nil, Main.mkCall, kidsAt, dvKids, List.nil_append, List.cons_append, he3]
      refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, ?_, fun _ => ⟨?_, ?_⟩,
        rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, ?_, fun _ => ⟨?_, ?_⟩, rfl, ?_, fun ht6 => ⟨?_, ?_⟩,
        rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      all_goals simp [hσ, ofArgs_n, dvVals, h1, hv.1, h3, h4, h5, h7, word_one, hne, digestCells]
      all_goals first
        | exact not_iff_not.mp (one_add_gen_ne_iff (by unfold ordG; omega))
        | exact h6 (by simpa using ht6)
    · rw [hloads]
      simp
    · refine ⟨by rw [hσ]; rfl, s2, by rw [hσ]; rfl, by rw [hσ]; exact word_one, by rw [hσ]; exact word_one,
        by rw [hσ]; show word 1 0 + _ = _; rw [word_one], by rw [hσ]; exact word_one⟩

end
end LeanVM.Guest.B1.Da
