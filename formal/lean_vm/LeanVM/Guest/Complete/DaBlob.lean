module

public import LeanVM.Guest.Complete.Straight
public import LeanVM.Guest.Complete.DaFree
public import LeanVM.Guest.Complete.MainFree
public import LeanVM.Guest.B1.Da.CellComplete
public import LeanVM.Guest.B1.Da.Help
public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.Memory.GuestWf
import LeanVM.Guest.CoreRef
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_cell»
import LeanVM.Guest.Data.ValNames.«da_verify_blob»
import LeanVM.Guest.Data.ValNames.«da_verify_blob_loop0»

/-!
# A blob's check, complete

`da_verify_cell` takes no words of its own: on its column's weights at `lv`, its tree pops the
cell's symbols (`da_verify_cell_completes`, from `Da.da_verify_cell_complete_vals`).
`da_verify_blob`'s cell loop takes none either: from the counter `g^h`, on the weights table
(`WeightsHold`) and the blob's region at `base` (`blobRegion`: the tree over its cells' digests,
two zeros, the running sums), it pops cells `h ..< 128`'s symbols (`blob_loop_completes`).
`da_verify_blob` takes its region as its own words (`da_verify_blob_completes`), a blob orthogonal
to the dual codeword returning the root over its cells' digests.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value

@[expose] public section

set_option linter.constructorNameAsVariable false

/-! ## Statements popping nothing -/

/-- A statement with no witness hint. -/
def Stmt.popsNone : Stmt → Bool
  | .atom (.hint (.witness ..)) => false
  | _ => true

theorem evs_pops_nil {rd : Reader} {σ : Val} {pre : List Stmt} (h : pre.all Stmt.popsNone = true) :
    ∀ e ∈ pre.flatMap (slEvs σ), e.pops rd σ = [] := by
  intro e he
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  have h0 := List.all_eq_true.mp h s hs
  cases s with
  | atom a =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    cases a with
    | hint hh => cases hh <;> simp_all [Stmt.popsNone, Ev.pops, Atom.pops, Hint.pops]
    | _ => rfl
  | call f args rets =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; rfl
  | callIf c f args =>
    simp only [slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rfl
    · split <;> rfl
  | _ => simp [slEvs] at he

/-- **A straight node popping nothing itself** pops its callees' entries in order. -/
theorem pops_straight_none {rd : Reader} {f : String} {fn : Fn} {pre : List Stmt} {vs : List V}
    (hf : coreProgram.find? f = some fn) (hb : fn.body = pre ++ [.ret vs])
    (hs : pre.all Stmt.straight = true) (hn : pre.all Stmt.popsNone = true) {σ : Val} {bufs : List ℕ}
    {ts : List Tree} (hk : Tree.KidsValid coreProgram rd σ ((pre.filterMap Stmt.callS).map (mkCall σ)) ts) :
    (Memory.Tree.node f σ bufs ts).pops coreProgram rd = (Tree.popsKids coreProgram rd ts).flatten := by
  rw [pops_straight hf hb hs, splice_mute _ _ (evs_pops_nil hn)]
  rw [(straight_parts σ pre hs).2.2.2, length_popsKids, kidsValid_len hk]

/-! ## Trees as buffers -/

/-- The cells of the tree over `leaves`, levels `0` to `k`. -/
def treeCells (leaves : List (E × E)) (k : ℕ) : List E :=
  (List.range (k + 1)).flatMap fun l => pairCells (treeLvl leaves l)

theorem readsAt_range_prefix {rd : Reader} {p : E} {f : ℕ → List E} :
    ∀ n, ReadsAt rd p ((List.range n).flatMap f) →
      ∀ l < n, ReadsAt rd (p * gen ^ ((List.range l).map fun m => (f m).length).sum) (f l)
  | 0, _, l, hl => absurd hl (by omega)
  | n + 1, h, l, hl => by
    rw [List.range_succ, List.flatMap_append, readsAt_append] at h
    rcases Nat.lt_or_ge l n with hl' | hl'
    · exact readsAt_range_prefix n h.1 l hl'
    · have e : l = n := by omega
      subst e
      have hlen : ((List.range l).flatMap f).length = ((List.range l).map fun m => (f m).length).sum := by
        rw [List.length_flatMap]
      rw [← hlen]
      simpa using h.2

theorem sum_level_lengths {k : ℕ} : ∀ l ≤ k,
    ((List.range l).map fun m => 2 * 2 ^ (k - m)).sum = off k l
  | 0, _ => by simp [off]
  | l + 1, hl => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_level_lengths l (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, off]
    have e : 2 ^ (k - l) = 2 * 2 ^ (k - (l + 1)) := by
      rw [← pow_succ']; congr 1; omega
    have hle : 2 ^ (k - l) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem length_pairCells_lvl {leaves : List (E × E)} {k : ℕ} (hlen : leaves.length = 2 ^ k)
    {l : ℕ} (hl : l ≤ k) : (pairCells (treeLvl leaves l)).length = 2 * 2 ^ (k - l) := by
  rw [length_pairCells, length_treeLvl hlen l hl]

/-- **The tree's cells as one buffer are `TreeMem`.** -/
theorem treeMem_of_reads {rd : Reader} {tree : E} {k : ℕ} {leaves : List (E × E)}
    (hlen : leaves.length = 2 ^ k) (h : ReadsAt rd tree (treeCells leaves k)) :
    TreeMem rd tree k leaves := by
  intro l hl
  have := readsAt_range_prefix (k + 1) h l (by omega)
  have e : ((List.range l).map fun m => (pairCells (treeLvl leaves m)).length) =
      (List.range l).map fun m => 2 * 2 ^ (k - m) :=
    List.map_congr_left fun m hm => length_pairCells_lvl hlen (by simp at hm; omega)
  rwa [e, sum_level_lengths l hl] at this

theorem length_treeCells {leaves : List (E × E)} {k : ℕ} (hlen : leaves.length = 2 ^ k) :
    (treeCells leaves k).length = 4 * 2 ^ k - 2 := by
  rw [treeCells, List.length_flatMap, List.range_succ, List.map_append, List.sum_append]
  have e : ((List.range k).map fun l => (pairCells (treeLvl leaves l)).length) =
      (List.range k).map fun m => 2 * 2 ^ (k - m) :=
    List.map_congr_left fun m hm => length_pairCells_lvl hlen (by simp at hm; omega)
  rw [e, sum_level_lengths k le_rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    length_pairCells_lvl hlen le_rfl, Nat.sub_self, pow_zero, off]
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- The first words of a tree's cells are its leaves'. -/
theorem treeCells_getD_leaf {leaves : List (E × E)} {k : ℕ} (i : ℕ) (hi : 2 * i + 1 < 2 * leaves.length) :
    (treeCells leaves k).getD (2 * i) 0 = (leaves.getD i 0).1 ∧
      (treeCells leaves k).getD (2 * i + 1) 0 = (leaves.getD i 0).2 := by
  have e : treeCells leaves k = pairCells leaves ++ (List.range k).flatMap fun l => pairCells (treeLvl leaves (l + 1)) := by
    rw [treeCells, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rfl
  have hl := length_pairCells leaves
  rw [e, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  exact pairCells_getD leaves i

/-! ## The cell check -/

/-- `da_verify_cell`'s hint: its `128` symbols. -/
def daSymHint : Atom :=
  .hint (.witness "da_symbols" (.stack ((List.range 128).map fun j => V.n (j + (val% «da_verify_cell» "sym[0]")))))

/-- `da_verify_cell` pops its symbols first, then nothing, calling nothing. -/
noncomputable def cellShapeOk : Bool :=
  stmtsEqb ((Fn.body fn% «da_verify_cell»).take 1) [.atom daSymHint] &&
    Stmt.muteList (fun _ => false) ((Fn.body fn% «da_verify_cell»).drop 1)

set_option maxRecDepth 100000 in
theorem cell_shape_ok : cellShapeOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cell_body_split :
    Fn.body fn% «da_verify_cell» = [.atom daSymHint] ++ (Fn.body fn% «da_verify_cell»).drop 1 := by
  have h := cell_shape_ok
  simp only [cellShapeOk, Bool.and_eq_true] at h
  rw [← stmtsEqb_sound h.1, List.take_append_drop]

set_option maxRecDepth 100000 in
/-- **`da_verify_cell` completes**, taking no words of its own: on its column's weights `ws` at `lv`,
its tree returns the cell's digest's cells and its dot product, popping its symbols. -/
theorem da_verify_cell_completes (k : ℕ) (lv : E) {syms ws : List E} (hsl : syms.length = LeanDa.cellSymbols)
    (hwl : ws.length = LeanDa.cellSymbols) :
    CallCompletes0 k "da_verify_cell" [lv] (cellRets syms ws) (fun rd => ReadsAt rd lv ws)
      (fun rd t => t.pops coreProgram rd = [("da_symbols", syms)]) := by
  refine callCompletes0_node fun rd _ hp => ?_
  obtain ⟨σ, e0, hs, hb⟩ := da_verify_cell_complete_vals rd lv syms ws hsl hwl hp
  have hsat := walk_sat (P := coreProgram) (fn% «da_verify_cell»).body
    (coreProgram_wf _ (List.mem_of_find?_eq_some find_da_verify_cell)) (hb fun _ _ _ => True)
  have hsh := cell_shape_ok
  simp only [cellShapeOk, Bool.and_eq_true] at hsh
  have hw0 : walk σ [.atom daSymHint] = .fall [.atom daSymHint] := rfl
  have hm := walk_mute (rd := rd) (σ := σ) _ hsh.2
  cases hw1 : walk σ ((Fn.body fn% «da_verify_cell»).drop 1) with
  | fall es1 =>
    rw [cell_body_split, walk_append_fall' _ hw0, hw1] at hsat
    exact absurd hsat (by simp [Out.pre, Out.Sat])
  | stuck =>
    rw [cell_body_split, walk_append_fall' _ hw0, hw1] at hsat
    exact absurd hsat (by simp [Out.pre, Out.Sat])
  | ret es1 vs =>
    have hw : walk σ (fn% «da_verify_cell»).body = .ret ([.atom daSymHint] ++ es1) vs := by
      rw [cell_body_split, walk_append_fall' _ hw0, hw1, Out.pre]
    rw [hw] at hsat
    rw [hw1] at hm
    have hc1 := calls_nil_of_mute hm
    have hc : calls ([.atom daSymHint] ++ es1) = [] := by
      rw [calls_append', hc1]; rfl
    have hev : ∀ e ∈ [.atom daSymHint] ++ es1, e.Holds rd σ := fun e he => (hsat.1 e he).1
    have hpar : (fn% «da_verify_cell»).params.map σ = [lv] := by
      rw [da_verify_cell_params, List.map_singleton, e0]
    have hk' : Tree.KidsValid coreProgram rd σ (calls ([.atom daSymHint] ++ es1)) [] := by
      rw [hc]; exact kidsValid_nil
    refine ⟨σ, _, _, vs, [], find_da_verify_cell, hpar, hw, hsat.2, hev, hk', by rw [Tree.BufsOkKids]; trivial, ?_⟩
    rw [pops_node find_da_verify_cell hw, Tree.popsKids, splice_append_of_calls_nil _ _ rfl,
      splice_mute es1 [] (fun e he => (hm e he).1) (by rw [hc1]; rfl)]
    simp only [evPops, List.flatMap_cons, List.flatMap_nil, Ev.pops, daSymHint, Atom.pops, Hint.pops,
      Dest.words, List.flatten_nil, List.append_nil, List.map_map]
    refine congrArg (fun l => [(("da_symbols" : String), l)]) (List.ext_getElem (by simp [hsl, LeanDa.cellSymbols]) fun j h1 h2 => ?_)
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    simp only [Function.comp_apply]
    rw [hs j h1, List.getD_eq_getElem _ _ (by simp only [LeanDa.cellSymbols] at hsl; omega)]

/-! ## A blob's words -/

/-- Column `h`'s weights: the dual codeword on cell `h`. -/
def colWs (z : E) (h : ℕ) : List E := (List.range 128).map fun e => dualAt z (128 * h + e)

theorem length_colWs (z : E) (h : ℕ) : (colWs z h).length = LeanDa.cellSymbols := by
  simp [colWs, LeanDa.cellSymbols]

/-- **The weights table at `wt`**: column `h`'s pointer, holding its weights. -/
def WeightsHold (rd : Reader) (z wt : E) : Prop :=
  ∀ h < 128, ∃ lv, LoadHolds rd (wt * gen ^ h) 0 lv ∧ ReadsAt rd lv (colWs z h)

/-- Cell `h`'s digest. -/
def cellDig (syms : ℕ → List E) (h : ℕ) : Digest := keccak256 ((syms h).flatMap E.toBytes)

/-- Cell `h`'s dot product with its column's weights. -/
def cellDot (z : E) (syms : ℕ → List E) (h : ℕ) : E :=
  ((List.range LeanDa.cellSymbols).map fun e ↦ (colWs z h).getD e 0 * (syms h).getD e 0).sum

/-- A blob's running sum after `h` cells. -/
def runSum (z : E) (syms : ℕ → List E) (h : ℕ) : E := ((List.range h).map (cellDot z syms)).sum

theorem runSum_succ (z : E) (syms : ℕ → List E) (h : ℕ) :
    runSum z syms (h + 1) = runSum z syms h + cellDot z syms h := by
  simp [runSum, List.range_succ]

/-- A blob's leaves: its cells' digests. -/
def blobLeaves (syms : ℕ → List E) : List (E × E) := (List.range 128).map fun h => digestHalves (cellDig syms h)

theorem length_blobLeaves (syms : ℕ → List E) : (blobLeaves syms).length = 2 ^ 7 := by simp [blobLeaves]

/-- **A blob's region** (`641` words): the tree over its leaves, two zeros, its running sums. -/
def blobRegion (z : E) (syms : ℕ → List E) : List E :=
  treeCells (blobLeaves syms) 7 ++ [0, 0] ++ (List.range 129).map (runSum z syms)

theorem length_treeCells_blob (syms : ℕ → List E) : (treeCells (blobLeaves syms) 7).length = 510 := by
  rw [length_treeCells (length_blobLeaves syms)]
  norm_num

theorem length_blobRegion (z : E) (syms : ℕ → List E) : (blobRegion z syms).length = 641 := by
  simp [blobRegion, length_treeCells_blob]

theorem loadHolds_of_readsAt {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {i : ℕ}
    (hi : i < xs.length) : LoadHolds rd p i (xs.getD i 0) := by
  rw [List.getD_eq_getElem _ _ hi]; exact h i hi

theorem blobRegion_sum (z : E) (syms : ℕ → List E) {h : ℕ} (hh : h ≤ 128) :
    (blobRegion z syms).getD (h + 512) 0 = runSum z syms h := by
  rw [blobRegion, List.getD_append_right _ _ _ _
    (by simp only [List.length_append, length_treeCells_blob, List.length_cons, List.length_nil]; omega)]
  simp only [List.length_append, length_treeCells_blob, List.length_cons, List.length_nil]
  rw [show h + 512 - (510 + (0 + 1 + 1)) = h by omega, List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem blobRegion_leaf (z : E) (syms : ℕ → List E) {h : ℕ} (hh : h < 128) :
    (blobRegion z syms).getD (2 * h) 0 = (digestHalves (cellDig syms h)).1 ∧
      (blobRegion z syms).getD (2 * h + 1) 0 = (digestHalves (cellDig syms h)).2 := by
  have hl := length_treeCells_blob syms
  rw [blobRegion, List.append_assoc, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  have e := treeCells_getD_leaf (k := 7) (leaves := blobLeaves syms) h (by rw [length_blobLeaves]; omega)
  rw [e.1, e.2, blobLeaves, List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-! ## The cell loop -/

/-- The cell loop's block. -/
def blLPre : List Stmt := [
  .atom (.mul (.n 3) (.n 1) (.n 0)),
  .atom (.load (.n 4) (.n 3) 0),
  .call "da_verify_cell" [.n 4] [.n 5, .n 6, .n 7],
  .atom (.mul (.n 8) (.n 2) (.n 0)),
  .atom (.load (.n 9) (.n 8) 512),
  .atom (.add (.n 10) (.n 9) (.n 7)),
  .atom (.load (.n 10) (.n 8) 513),
  .atom (.mul (.n 11) (.n 0) (.n 0)),
  .atom (.mul (.n 12) (.n 2) (.n 11)),
  .atom (.load (.n 5) (.n 12) 0),
  .atom (.load (.n 6) (.n 12) 1),
  .atom (.const (.n 13) (word 2 0)),
  .atom (.mul (.n 14) (.n 0) (.n 13)),
  .atom (.const (.n 15) (word 325 0)),
  .atom (.add (.n 16) (.n 14) (.n 15)),
  .atom (.const (.n 17) (word 2 0)),
  .atom (.mul (.n 18) (.n 0) (.n 17)),
  .callIf (.n 16) name% «da_verify_blob_loop0» [.n 18, .n 1, .n 2]]

theorem blL_body : (fn% «da_verify_blob_loop0»).body = blLPre ++ [.ret []] := rfl
theorem blL_params : (fn% «da_verify_blob_loop0»).params = [.n 0, .n 1, .n 2] := rfl

set_option maxRecDepth 100000 in
theorem find_blL : coreProgram.find? name% «da_verify_blob_loop0» = some fn% «da_verify_blob_loop0» :=
  coreProgram_find?_at (j := idx% «da_verify_blob_loop0») rfl

/-- Iteration `h`'s valuation: the column's pointer `lv`, the cell check's returns `cr`, the running
sum `rs`. -/
noncomputable def blLσ (wt base lv : E) (cr : List E) (rs : E) (h : ℕ) : Val := fun v =>
  [gen ^ h, wt, base, wt * gen ^ h, lv, cr.getD 0 0, cr.getD 1 0, cr.getD 2 0, base * gen ^ h, rs,
    rs + cr.getD 2 0, gen ^ h * gen ^ h, base * (gen ^ h * gen ^ h), word 2 0, gen ^ h * word 2 0,
    word 325 0, gen ^ h * word 2 0 + word 325 0, word 2 0, gen ^ h * word 2 0].getD v.idx 0

/-- What the cell loop reads: the weights table and the blob's region. -/
def BlobLPre (z : E) (syms : ℕ → List E) (wt base : E) (rd : Reader) : Prop :=
  WeightsHold rd z wt ∧ ReadsAt rd base (blobRegion z syms)

/-- The cell loop from `g^h` pops cells `h ..< 128`'s symbols. -/
def BlobLPost (syms : ℕ → List E) (h : ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = (List.range' h (128 - h)).map fun j => ("da_symbols", syms j)

theorem loopGuard_taken {i n : ℕ} (hn : n < 2 ^ 34) (hi : i + 1 ≤ n) :
    decide (gen ^ i * word 2 0 + gen ^ n ≠ 0) = decide (i + 1 ≠ n) := by
  rw [word_gen, gen_pow_mul_gen]
  refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
    fun h he => h ?_⟩
  exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)

theorem gen_mul_two (h : ℕ) : gen ^ h * word 2 0 = gen ^ (h + 1) := by rw [word_gen, gen_pow_mul_gen]

theorem gen_sq (h : ℕ) : gen ^ h * gen ^ h = gen ^ (2 * h) := by rw [← pow_add]; congr 1; omega

set_option maxRecDepth 100000 in
/-- **One iteration of the cell loop completes**, given its tail's completeness. -/
theorem blL_step (k : ℕ) (z : E) {syms : ℕ → List E} (hsl : ∀ h, (syms h).length = LeanDa.cellSymbols)
    (wt base : E) {h : ℕ} (hh : h < 128)
    (htail : h + 1 < 128 → CallCompletes0 k name% «da_verify_blob_loop0» [gen ^ (h + 1), wt, base] []
      (BlobLPre z syms wt base) (BlobLPost syms (h + 1))) :
    CallCompletes0 k name% «da_verify_blob_loop0» [gen ^ h, wt, base] [] (BlobLPre z syms wt base)
      (BlobLPost syms h) := by
  refine callCompletes0_straight find_blL blL_body rfl fun rd hl hp => ?_
  obtain ⟨hW, hR⟩ := hp
  obtain ⟨lv, hlv, hws⟩ := hW h hh
  set σ := blLσ wt base lv (cellRets (syms h) (colWs z h)) (runSum z syms h) h with hσ
  have hreg := fun i hi => loadHolds_of_readsAt hR (i := i) (by rw [length_blobRegion]; exact hi)
  -- the cell check
  obtain ⟨tc, hnc, hvc, hbc, hpc⟩ := da_verify_cell_completes k lv (hsl h) (length_colWs z h) rd hl hws
  have e16 : σ (.n 16) = gen ^ (h + 1) + gen ^ 128 := by
    show gen ^ h * word 2 0 + word 325 0 = _; rw [gen_mul_two, word_g128]
  -- the tail
  obtain ⟨t1, hk1, hb1, hp1⟩ : ∃ t1 : Tree,
      Tree.KidsValid coreProgram rd σ [⟨name% «da_verify_blob_loop0», [.n 18, .n 1, .n 2], [],
        decide (σ (.n 16) ≠ 0)⟩] [t1] ∧ t1.BufsOk coreProgram ∧
      t1.pops coreProgram rd = (List.range' (h + 1) (128 - (h + 1))).map fun j => ("da_symbols", syms j) := by
    have hargs : [V.n 18, .n 1, .n 2].map σ = [gen ^ (h + 1), wt, base] := by
      show [gen ^ h * word 2 0, wt, base] = _; rw [gen_mul_two]
    by_cases hlt : h + 1 < 128
    · obtain ⟨t1, hn, hv1, hb, hp'⟩ := htail hlt rd hl ⟨hW, hR⟩
      have htk : decide (σ (.n 16) ≠ 0) = true := by
        rw [e16, ← gen_mul_two, loopGuard_taken (by norm_num) (by omega)]; exact decide_eq_true (by omega)
      exact ⟨t1, kidsValid_cons_taken htk hn (by rw [hargs]; exact hv1) kidsValid_nil, hb, hp'⟩
    · have htk : decide (σ (.n 16) ≠ 0) = false := by
        rw [e16, ← gen_mul_two, loopGuard_taken (by norm_num) (by omega)]; exact decide_eq_false (by omega)
      refine ⟨.phantom name% «da_verify_blob_loop0» (blLσ wt base 0 [] 0 (h + 1)),
        kidsValid_cons_skip htk find_blL ?_ kidsValid_nil, ?_, ?_⟩
      · rw [blL_params, hargs]; rfl
      · rw [Tree.BufsOk]; trivial
      · rw [Tree.pops, show 128 - (h + 1) = 0 by omega]; rfl
  have hk : Tree.KidsValid coreProgram rd σ ((blLPre.filterMap Stmt.callS).map (mkCall σ)) [tc, t1] :=
    kidsValid_cons_taken rfl hnc hvc hk1
  refine ⟨σ, [tc, t1], rfl, rfl, ?_, hk, ⟨hbc, hb1, trivial⟩, ?_⟩
  · intro s hs
    simp only [blLPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact rfl
    · exact hlv
    · trivial
    · exact rfl
    · show LoadHolds rd (base * gen ^ h) 512 (runSum z syms h)
      rw [loadHolds_mul_gen_pow, ← blobRegion_sum z syms (by omega)]; exact hreg _ (by omega)
    · exact rfl
    · show LoadHolds rd (base * gen ^ h) 513 (runSum z syms h + cellDot z syms h)
      rw [loadHolds_mul_gen_pow, ← runSum_succ, show h + 513 = (h + 1) + 512 by omega,
        ← blobRegion_sum z syms (by omega)]
      exact hreg _ (by omega)
    · exact rfl
    · exact rfl
    · show LoadHolds rd (base * (gen ^ h * gen ^ h)) 0 (digestHalves (cellDig syms h)).1
      rw [gen_sq, loadHolds_mul_gen_pow, Nat.add_zero, ← (blobRegion_leaf z syms hh).1]
      exact hreg _ (by omega)
    · show LoadHolds rd (base * (gen ^ h * gen ^ h)) 1 (digestHalves (cellDig syms h)).2
      rw [gen_sq, loadHolds_mul_gen_pow, ← (blobRegion_leaf z syms hh).2]
      exact hreg _ (by omega)
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show IsInK (σ (.n 16)); rw [e16]; exact gen_pow_add_isInK _ _
  · show _ = _
    rw [pops_straight_none find_blL blL_body rfl rfl hk, Tree.popsKids, Tree.popsKids, Tree.popsKids, hpc, hp1,
      show 128 - h = 128 - (h + 1) + 1 by omega, List.range'_succ]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_cons, List.singleton_append]

/-- **The cell loop completes** from every counter below `128`, popping each cell's symbols. -/
theorem blob_loop_completes (k : ℕ) (z : E) {syms : ℕ → List E} (hsl : ∀ h, (syms h).length = LeanDa.cellSymbols)
    (wt base : E) : ∀ h < 128, CallCompletes0 k name% «da_verify_blob_loop0» [gen ^ h, wt, base] []
      (BlobLPre z syms wt base) (BlobLPost syms h) := by
  have key : ∀ t h, h + 1 + t = 128 → CallCompletes0 k name% «da_verify_blob_loop0» [gen ^ h, wt, base] []
      (BlobLPre z syms wt base) (BlobLPost syms h) := by
    intro t
    induction t with
    | zero => intro h hh; exact blL_step k z hsl wt base (by omega) fun h' => absurd h' (by omega)
    | succ t ih => intro h hh; exact blL_step k z hsl wt base (by omega) fun _ => ih (h + 1) (by omega)
  intro h hh
  exact key (128 - h - 1) h (by omega)

/-! ## The blob -/

/-- `da_verify_blob`'s block. -/
def blobPre : List Stmt := [
  .atom (.hint (.alloc (.n 1) 641)),
  .atom (.const (.n 2) (word 0 0)),
  .atom (.load (.n 2) (.n 1) 512),
  .atom (.const (.n 3) (word 1 0)),
  .call name% «da_verify_blob_loop0» [.n 3, .n 0, .n 1] [],
  .atom (.load (.n 4) (.n 1) 640),
  .atom (.const (.n 5) (word 0 0)),
  .atom (.assertEq (.n 4) (.n 5)),
  .call "da_levels__L128_L7" [.n 1] [.n 6, .n 7],
  .atom (.copy (.n 8) (.n 6)),
  .atom (.copy (.n 9) (.n 7))]

theorem blob_body : (fn% «da_verify_blob»).body = blobPre ++ [.ret [.n 8, .n 9]] := rfl

set_option maxRecDepth 100000 in
theorem find_blob : coreProgram.find? name% «da_verify_blob» = some fn% «da_verify_blob» :=
  coreProgram_find?_at (j := idx% «da_verify_blob») rfl

/-- The blob's valuation: the weights `wt`, its region at `g^b`, its root `root`. -/
noncomputable def blobσ (wt : E) (b : ℕ) (root : E × E) : Val := fun v =>
  [wt, gen ^ b, word 0 0, word 1 0, word 0 0, word 0 0, root.1, root.2, root.1, root.2].getD v.idx 0

/-- The root over a blob's cells' digests. -/
def blobRoot (syms : ℕ → List E) : E × E := cellRoot 7 (blobLeaves syms)

/-- The blob pops its cells' symbols in order. -/
def BlobPost (syms : ℕ → List E) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = (List.range 128).map fun h => ("da_symbols", syms h)

theorem readsAt_gen_pow {rd : Reader} {b : ℕ} {xs : List E} :
    HoldsWords rd [(b, xs)] ↔ ReadsAt rd (gen ^ b) xs := by
  simp only [HoldsWords, List.mem_singleton, forall_eq, gen_pow_eq_ofK]

set_option maxRecDepth 100000 in
/-- **`da_verify_blob` completes**, its region its own words: on the weights table of `z`, a blob
of `128` cells orthogonal to the dual codeword returns the root over its cells' digests, popping
the cells' symbols. -/
theorem da_verify_blob_completes (hwf : coreProgram.Wf) (k : ℕ) (z : E) {syms : ℕ → List E}
    (hsl : ∀ h, (syms h).length = LeanDa.cellSymbols) (horth : runSum z syms 128 = 0) (wt : E) :
    CallCompletes k "da_verify_blob" [wt] [(blobRoot syms).1, (blobRoot syms).2]
      (fun rd => WeightsHold rd z wt) (BlobPost syms) := by
  refine callCompletes_straight find_blob blob_body rfl fun b => ?_
  refine ⟨641, [(b, blobRegion z syms)], blobσ wt b (blobRoot syms), [BlobLPost syms 0, FreePost],
    ⟨by simp [length_blobRegion], List.pairwise_singleton _ _⟩, rfl, rfl, ?_, ?_, ?_⟩
  · intro rd _ hw _ s hs
    have hR := readsAt_gen_pow.mp hw
    have hreg := fun i hi => loadHolds_of_readsAt hR (i := i) (by rw [length_blobRegion]; exact hi)
    simp only [blobPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact rfl
    · show LoadHolds rd (gen ^ b) 512 (word 0 0)
      have := hreg 512 (by omega)
      rwa [show 512 = 0 + 512 by rfl, blobRegion_sum z syms (by omega), show runSum z syms 0 = 0 by simp [runSum],
        ← word_zero] at this
    · exact rfl
    · trivial
    · show LoadHolds rd (gen ^ b) 640 (word 0 0)
      have := hreg 640 (by omega)
      rwa [show 640 = 128 + 512 by rfl, blobRegion_sum z syms le_rfl, horth, ← word_zero] at this
    · exact rfl
    · show word 0 0 + word 0 0 = 0
      rw [word_zero, add_zero]
    · trivial
    · exact rfl
    · exact rfl
  · refine kidsCompl_cons_taken rfl rfl (args := [gen ^ 0, wt, gen ^ b]) (by show [word 1 0, wt, gen ^ b] = _; rw [word_one, pow_zero]) rfl ?_
      (kidsCompl_cons_taken rfl (f := daLevelsName 7) rfl rfl rfl ?_ kidsCompl_nil)
    · exact ((blob_loop_completes k z hsl wt (gen ^ b) 0 (by norm_num)).mono
        (fun rd hp => ⟨hp.2, readsAt_gen_pow.mp hp.1⟩) fun _ _ _ h => h).toCallCompletes
    · refine CallCompletes.monoPP (da_levels_completes hwf k (Or.inr rfl) (gen ^ b) (blobLeaves syms)
        (length_blobLeaves syms))
        (fun rd hp => treeMem_of_reads (length_blobLeaves syms) ?_) fun _ _ _ h => h
      have hR := readsAt_gen_pow.mp hp.1
      rw [blobRegion, readsAt_append, readsAt_append] at hR
      exact hR.1.1
  · intro rd ts _ _ _ hv hq
    have hlen := kidsValid_len hv
    rw [show ((blobPre.filterMap Stmt.callS).map (mkCall (blobσ wt b (blobRoot syms)))).length = 2 from rfl] at hlen
    rcases ts with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, ts⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · have h1 : BlobLPost syms 0 rd t1 := hq.1 rfl
      have h2 : FreePost rd t2 := hq.2.1 rfl
      rw [BlobPost, pops_straight_none find_blob blob_body rfl rfl hv, Tree.popsKids, Tree.popsKids,
        Tree.popsKids, h1, h2.1, List.range_eq_range']
      simp
    · simp at hlen

end
end LeanVM.Guest.Complete
