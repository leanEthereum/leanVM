module

public import LeanVM.Guest.Complete.DaWords
public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Da.VerifyMath
public import LeanVM.Guest.B1.Da.Witness
public import LeanVM.Guest.B1.Fwd.Canon
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify»

/-!
# `da_verify`, complete

On a witness opening the claim `(root, z)` (`Da.MatrixWitness.Opens`) and the count table at `bb`
(`CountWords`), `da_verify(bb)` returns the root's cells and `z`, popping the blob count, the
challenge and every blob's cells' symbols (`da_verify_completes`), given `da_vector`'s and
`da_weights`' completeness (`DaVectorComplete`, `DaWeightsComplete`). Its own words, from the base
`b`: the dual codeword's buffers (`vecWords`), the weights table and the columns' runs
(`wsWords`), and the tree over the blob roots (`rootsCells`); its blobs' regions are their checks'.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak

@[expose] public section

set_option linter.constructorNameAsVariable false

/-! ## Runs of words, laid out -/

theorem wordsIn_single (b : ℕ) (xs : List E) : WordsIn [(b, xs)] b xs.length :=
  ⟨by simp, List.pairwise_singleton _ _⟩

theorem WordsIn.cast {W : Words} {b n b' n' : ℕ} (h : WordsIn W b n) (hb : b = b') (hn : n = n') :
    WordsIn W b' n' := hb ▸ hn ▸ h

theorem WordsIn.cons1 {W : Words} {b n : ℕ} {xs : List E} (h : WordsIn W (b + xs.length) n) :
    WordsIn ((b, xs) :: W) b (xs.length + n) := (wordsIn_single b xs).append h

theorem wordsIn_colRuns (z : E) (c : ℕ) : ∀ m,
    WordsIn ((List.range m).map fun h => (c + 256 * h, colRun z h)) c (256 * m)
  | 0 => (wordsIn_nil c).cast rfl rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append]
    exact ((wordsIn_colRuns z c m).append (wordsIn_single (c + 256 * m) (colRun z m))).cast rfl
      (by rw [length_colRun]; ring)

theorem list_sum_range (f : ℕ → E) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]
    simp

/-! ## The tree over the blob roots -/

/-- The blob roots and the padding blobs' roots, `32` leaves. -/
def rootLeaves (r : ℕ) (syms : ℕ → ℕ → List E) : List (E × E) :=
  (List.range 32).map fun i => digestHalves (blobLeaf r syms i)

theorem length_rootLeaves (r : ℕ) (syms : ℕ → ℕ → List E) : (rootLeaves r syms).length = 2 ^ 5 := by
  simp [rootLeaves]

/-- `da_verify`'s roots buffer: the tree over the blob roots, two zeros (`128` words). -/
def rootsCells (r : ℕ) (syms : ℕ → ℕ → List E) : List E := treeCells (rootLeaves r syms) 5 ++ [0, 0]

theorem length_rootsCells (r : ℕ) (syms : ℕ → ℕ → List E) : (rootsCells r syms).length = 128 := by
  rw [rootsCells, List.length_append, length_treeCells (length_rootLeaves r syms)]; rfl

theorem blobRoot_eq (r : ℕ) (syms : ℕ → ℕ → List E) {i : ℕ} (hi : i < r) :
    blobRoot (syms i) = digestHalves (blobLeaf r syms i) := by
  rw [blobLeaf, ite_pos' hi, ← cellRoot_mRoot]
  rfl

theorem rootLeaves_getD (r : ℕ) (syms : ℕ → ℕ → List E) {i : ℕ} (hi : i < 32) :
    (rootLeaves r syms).getD i 0 = digestHalves (blobLeaf r syms i) := by
  rw [rootLeaves, List.getD_eq_getElem _ _ (by simp; omega)]; simp

theorem rootsCells_slot (r : ℕ) (syms : ℕ → ℕ → List E) {i : ℕ} (hi : i < 32) :
    (rootsCells r syms).getD (2 * i) 0 = (digestHalves (blobLeaf r syms i)).1 ∧
      (rootsCells r syms).getD (2 * i + 1) 0 = (digestHalves (blobLeaf r syms i)).2 := by
  have hl := length_treeCells (length_rootLeaves r syms)
  rw [rootsCells, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  have e := treeCells_getD_leaf (k := 5) (leaves := rootLeaves r syms) i (by rw [length_rootLeaves]; omega)
  rw [e.1, e.2, rootLeaves_getD r syms hi]
  exact ⟨rfl, rfl⟩

theorem rootsCells_reads {rd : Reader} {p : E} {r : ℕ} {syms : ℕ → ℕ → List E} (h : ReadsAt rd p (rootsCells r syms))
    {i : ℕ} (hi : i < 32) :
    ReadsAt rd (p * gen ^ (2 * i)) [(digestHalves (blobLeaf r syms i)).1, (digestHalves (blobLeaf r syms i)).2] := by
  refine readsAt_sub h (by rw [length_rootsCells]; simp; omega) fun j hj => ?_
  simp only [List.length_cons, List.length_nil] at hj
  have e := rootsCells_slot r syms hi
  interval_cases j
  · rw [Nat.add_zero, e.1]; rfl
  · rw [e.2]; rfl

/-- The tree over the blob roots' root. -/
theorem rootLeaves_root (r : ℕ) (syms : ℕ → ℕ → List E) :
    cellRoot 5 (rootLeaves r syms) = digestHalves (daTree r 5 syms) := by
  rw [daTree, ← cellRoot_mRoot]; rfl

/-! ## The body -/

/-- `da_verify`'s block. -/
def dvPre : List Stmt := [
  .atom (.hint (.witness "da_n_blobs" (.stack [.n 1]))),
  .call "da_padding" [.n 1] [.n 2],
  .atom (.hint (.witness "da_challenge" (.stack [.n 3]))),
  .call "da_vector" [.n 3] [.n 4, .n 5, .n 6, .n 7],
  .call "da_weights" [.n 5, .n 6, .n 4, .n 7] [.n 8],
  .atom (.const (.n 9) (word 325 0)),
  .atom (.hint (.allocDyn (.n 10) (.n 9))),
  .atom (.const (.n 11) (word 1 0)),
  .atom (.add (.n 12) (.n 11) (.n 1)),
  .atom (.const (.n 13) (word 1 0)),
  .callIf (.n 12) name% «da_verify_loop0» [.n 13, .n 1, .n 8, .n 10],
  .call "da_pad" [.n 10, .n 1, .n 2] [],
  .call "da_levels__L32_L5" [.n 10] [.n 14, .n 15],
  .atom (.mul (.n 16) (.n 0) (.n 1)),
  .atom (.load (.n 17) (.n 16) 0),
  .atom (.const (.n 18) (word 1 0)),
  .atom (.const (.n 19) (word 0 0)),
  .atom (.const (.n 20) (word 0 0)),
  .atom (.const (.n 21) (word 0 0)),
  .atom (.const (.n 22) (word 0 0)),
  .atom (.const (.n 23) (word 9223372036854775808 0)),
  .atom dvKec,
  .atom (.copy (.n 26) (.n 24)),
  .atom (.copy (.n 27) (.n 25)),
  .atom (.copy (.n 28) (.n 3))]
where
  /-- The last `KECCAK`: the tree's root, the count's word, a zero, the padding. -/
  dvKec : Atom := .keccak [.n 14, .n 15, .n 17, .n 19, .n 18, .n 19, .n 20, .n 21, .n 23, .n 19, .n 20, .n 21,
    .n 22] [.n 24, .n 25] false false

theorem dv_body : (fn% «da_verify»).body = dvPre ++ [.ret [.n 26, .n 27, .n 28]] := rfl

/-- The last `KECCAK`'s input words. -/
def dvKIns (r : ℕ) (c0 c1 : E) : List E :=
  [c0, c1, word r 0, word 0 0, word 1 0, word 0 0, word 0 0, word 0 0, word 9223372036854775808 0,
    word 0 0, word 0 0, word 0 0, word 0 0]

/-- `da_verify`'s valuation: the count table `bb`, `r` blobs, the challenge `z`, the dual codeword's
returns `vr`, the weights `bw`, the roots `bR`, the tree's root `c`. -/
noncomputable def dvσ (bb : E) (r : ℕ) (z : E) (vr : List E) (bw bR : ℕ) (c : E × E) : Val :=
  Val.ofArgs [bb, gen ^ r, gen ^ (LeanDa.maxRows - r), z, vr.getD 0 0, vr.getD 1 0, vr.getD 2 0, vr.getD 3 0,
    gen ^ bw, word 325 0, gen ^ bR, word 1 0, word 1 0 + gen ^ r, word 1 0, c.1, c.2, bb * gen ^ r,
    word r 0, word 1 0, word 0 0, word 0 0, word 0 0, word 0 0, word 9223372036854775808 0,
    kecOut (dvKIns r c.1 c.2) false false 0, kecOut (dvKIns r c.1 c.2) false false 1,
    kecOut (dvKIns r c.1 c.2) false false 0, kecOut (dvKIns r c.1 c.2) false false 1, z]

/-- The atoms the last hash's chain reads. -/
def dvKAtoms : List Atom := [.const (.n 18) (word 1 0), .const (.n 19) (word 0 0), .const (.n 20) (word 0 0),
  .const (.n 21) (word 0 0), .const (.n 22) (word 0 0), .const (.n 23) (word 9223372036854775808 0), dvPre.dvKec]

set_option maxRecDepth 100000 in
theorem dvK_ok : pairHashVOk dvKAtoms (.n 14) (.n 15) (.n 17) (.n 19) (.n 24) (.n 25) = true := by
  decide +kernel

theorem dvK_holds {rd : Reader} (bb : E) (r : ℕ) (z : E) (vr : List E) (bw bR : ℕ) (c : E × E) :
    dvPre.dvKec.Holds rd (dvσ bb r z vr bw bR c) := by
  refine holds_of_good (S := []) (w := fun _ => 0) ⟨rfl, Or.inr (Or.inl rfl), fun cc hc => ?_⟩ trivial
  obtain ⟨cc, hc13⟩ := cc
  simp only [List.length_cons, List.length_nil] at hc
  interval_cases cc
  · show kecOut (dvKIns r c.1 c.2) false false 0 = _
    simp only [kecOut, show (0 : ℕ) < 13 by decide, ↓reduceDIte]; rfl
  · show kecOut (dvKIns r c.1 c.2) false false 1 = _
    simp only [kecOut, show (1 : ℕ) < 13 by decide, ↓reduceDIte]; rfl

/-- **The commitment**: the hash of the tree's root's cells, the count's word and a zero. -/
theorem dv_commit (bb : E) {r : ℕ} (hr : r ≤ LeanDa.maxRows) (z : E) (vr : List E) (bw bR : ℕ) (syms : ℕ → ℕ → List E) :
    (kecOut (dvKIns r (digestHalves (daTree r 5 syms)).1 (digestHalves (daTree r 5 syms)).2) false false 0,
      kecOut (dvKIns r (digestHalves (daTree r 5 syms)).1 (digestHalves (daTree r 5 syms)).2) false false 1) =
      digestHalves (daRoot r 5 syms) := by
  have hat : ∀ a ∈ dvKAtoms, a.Holds (fun _ => none) (dvσ bb r z vr bw bR (digestHalves (daTree r 5 syms))) := by
    intro a ha
    simp only [dvKAtoms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact dvK_holds bb r z vr bw bR _ | rfl
  have h := pairHashV_sound dvK_ok hat
  rw [← daRoot_cells hr, ← word_zero]
  exact h

/-! ## `da_verify` -/

/-- The entries `da_verify` pops on a witness of `r` blobs: the count, the challenge, the blobs'
cells. -/
def dvPops' (z : E) (r : ℕ) (syms : ℕ → ℕ → List E) : List Pop :=
  [("da_n_blobs", [gen ^ r]), ("da_challenge", [z])] ++ dvPops syms 0 r

/-- `da_verify`'s words from the base `b`. -/
noncomputable def dvWords (z : E) (r : ℕ) (syms : ℕ → ℕ → List E) (b : ℕ) : Words :=
  vecWords z b (b + 14) (b + 270) (b + 398) ++
    (wsWords z (b + 1294) (fun h => b + 1422 + 256 * h) ++ [(b + 34190, rootsCells r syms)])

theorem dvWords_in (z : E) (r : ℕ) (syms : ℕ → ℕ → List E) (b : ℕ) : WordsIn (dvWords z r syms b) b 34318 := by
  have hc := wordsIn_colRuns z (b + 1422) 128
  have h5 : WordsIn ((List.range 128).map (fun h => (b + 1422 + 256 * h, colRun z h)) ++
      [(b + 34190, rootsCells r syms)]) (b + 1422) (256 * 128 + 128) :=
    hc.append ((wordsIn_single _ _).cast (by ring) (length_rootsCells r syms))
  have hT : (wsTable fun h => b + 1422 + 256 * h).length = 128 := by simp [wsTable]
  have h4 : WordsIn (wsWords z (b + 1294) (fun h => b + 1422 + 256 * h) ++ [(b + 34190, rootsCells r syms)])
      (b + 1294) (128 + (256 * 128 + 128)) := by
    have := WordsIn.cons1 (b := b + 1294) (xs := wsTable fun h => b + 1422 + 256 * h)
      (h5.cast (by rw [hT]) rfl)
    rw [hT] at this
    exact this
  have h3 : WordsIn ((b + 398, offCells (zsVal z)) :: (wsWords z (b + 1294) (fun h => b + 1422 + 256 * h) ++
      [(b + 34190, rootsCells r syms)])) (b + 398) (896 + (128 + (256 * 128 + 128))) := by
    have := WordsIn.cons1 (b := b + 398) (xs := offCells (zsVal z)) (h4.cast (by simp) rfl)
    rwa [length_offCells] at this
  have h2 : WordsIn ((b + 270, facCells (zsVal z) 6 7) :: (b + 398, offCells (zsVal z)) ::
      (wsWords z (b + 1294) (fun h => b + 1422 + 256 * h) ++ [(b + 34190, rootsCells r syms)])) (b + 270)
      (128 + (896 + (128 + (256 * 128 + 128)))) := by
    have := WordsIn.cons1 (b := b + 270) (xs := facCells (zsVal z) 6 7) (h3.cast (by simp) rfl)
    rwa [length_facCells] at this
  have h1 : WordsIn ((b + 14, topRun z) :: (b + 270, facCells (zsVal z) 6 7) :: (b + 398, offCells (zsVal z)) ::
      (wsWords z (b + 1294) (fun h => b + 1422 + 256 * h) ++ [(b + 34190, rootsCells r syms)])) (b + 14)
      (256 + (128 + (896 + (128 + (256 * 128 + 128))))) := by
    have := WordsIn.cons1 (b := b + 14) (xs := topRun z) (h2.cast (by simp) rfl)
    rwa [length_topRun] at this
  have h0 := WordsIn.cons1 (b := b) (xs := zsCells z) (h1.cast (by simp) rfl)
  rw [length_zsCells] at h0
  exact h0.cast rfl (by norm_num)

set_option maxRecDepth 100000 in
theorem find_dv : coreProgram.find? name% «da_verify» = some fn% «da_verify» :=
  coreProgram_find?_at (j := idx% «da_verify») rfl

/-- **The splice of `da_verify`'s events**: its two hints, its callees' entries in order. -/
theorem dv_splice {rd : Reader} {σ : Val} (h12 : σ (.n 12) ≠ 0) (p1 p2 p3 p4 p5 p6 : List Pop) :
    splice rd σ (dvPre.flatMap (slEvs σ)) [p1, p2, p3, p4, p5, p6] =
      [("da_n_blobs", [σ (.n 1)])] ++ p1 ++ [("da_challenge", [σ (.n 3)])] ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 := by
  simp [dvPre, slEvs, splice, Atom.pops, Hint.pops, Dest.words, h12, dvPre.dvKec]

theorem readsAt_of_dvWords {rd : Reader} {z : E} {r : ℕ} {syms : ℕ → ℕ → List E} {b : ℕ}
    (h : HoldsWords rd (dvWords z r syms b)) :
    HoldsWords rd (vecWords z b (b + 14) (b + 270) (b + 398)) ∧
      HoldsWords rd (wsWords z (b + 1294) (fun h => b + 1422 + 256 * h)) ∧
      ReadsAt rd (gen ^ (b + 34190)) (rootsCells r syms) := by
  rw [dvWords, holdsWords_append, holdsWords_append] at h
  exact ⟨h.1, h.2.1, readsAt_gen_pow.mp h.2.2⟩

set_option linter.unusedTactic false in
set_option maxRecDepth 100000 in
/-- **`da_verify` completes** on a witness opening `(root, z)`, given its dual codeword's builders'
completeness: on the count table, it returns the root's cells and `z`, popping the blob count, the
challenge and the blobs' cells, every node exact. -/
theorem da_verify_completes (hwf : coreProgram.Wf) {k : ℕ} (hk : 16 ≤ k) (hV : DaVectorComplete k)
    (hWs : DaWeightsComplete k) {w : LeanVM.Da.MatrixWitness} {root : Digest} {z : E} (hw : w.Opens root z)
    (bb : E) :
    CallCompletes k "da_verify" [bb] (digestCells root ++ [z]) (fun rd => CountWords rd bb)
      (fun rd t => t.pops coreProgram rd = dvPops' z w.rows.length (wSyms w) ∧ t.Every (ExactAt coreProgram rd)) := by
  refine CallCompletes.exact ?_ da_verify_exactFree
  set r := w.rows.length with hrdef
  set syms := wSyms w with hsyms
  have hr1 : 1 ≤ r := hw.1
  have hr : r ≤ LeanDa.maxRows := hw.2.1
  have hr32 : r ≤ 32 := hr
  have hsl : ∀ i h, (syms i h).length = LeanDa.cellSymbols := wSyms_len hw
  have horth : ∀ i < r, runSum z (syms i) 128 = 0 := by
    intro i hi
    have := wDot hw i hi
    rw [← this, runSum, list_sum_range]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [cellDot, show LeanDa.cellSymbols = 128 from rfl, list_sum_range]
    refine Finset.sum_congr rfl fun e he => ?_
    have he' := Finset.mem_range.mp he
    rw [colWs, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  have hroot : root = daRoot r 5 syms := opens_eq hw
  refine callCompletes_straight find_dv dv_body rfl fun b => ?_
  set c := digestHalves (daTree r 5 syms) with hc
  set σ := dvσ bb r z (vecRets b (b + 14) (b + 270) (b + 398)) (b + 1294) (b + 34190) c with hσ
  have h12 : σ (.n 12) ≠ 0 := by
    show word 1 0 + gen ^ r ≠ 0
    have := one_add_gen_pow_ne (d := r) (by omega)
    exact of_decide_eq_true (this.trans (decide_eq_true (by omega)))
  refine ⟨34318, dvWords z r syms b, σ,
    [FreePost, FreePost, FreePost, DvLPost syms 0 r, PopsNil, FreePost], dvWords_in z r syms b, rfl, ?_, ?_, ?_, ?_⟩
  · -- the returns
    show [kecOut (dvKIns r c.1 c.2) false false 0, kecOut (dvKIns r c.1 c.2) false false 1, z] = _
    have := dv_commit bb hr z (vecRets b (b + 14) (b + 270) (b + 398)) (b + 1294) (b + 34190) syms
    simp only [Prod.ext_iff] at this
    rw [hc, this.1, this.2, hroot]; rfl
  · -- the atoms
    intro rd _ hW hp s hs
    have hload : LoadHolds rd (bb * gen ^ r) 0 (word r 0) := by
      rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hp r hr
    have hinK : IsInK (word 1 0 + gen ^ r) := by
      rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _
    simp only [dvPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | trivial
      | exact rfl
      | exact hload
      | exact hinK
      | (show Atom.Holds rd σ dvPre.dvKec
         exact dvK_holds bb r z (vecRets b (b + 14) (b + 270) (b + 398)) (b + 1294) (b + 34190) c)
  · -- the callees
    refine kidsCompl_cons_taken rfl rfl rfl rfl (CallCompletes.monoPP (da_padding_completes hwf hk hr1 hr) (fun _ _ => trivial)
      fun _ _ _ h => h) ?_
    refine kidsCompl_cons_taken rfl rfl rfl rfl (CallCompletes.monoPP (hV z b (b + 14) (b + 270) (b + 398))
      (fun _ hp => (readsAt_of_dvWords hp.1).1) fun _ _ _ h => h) ?_
    refine kidsCompl_cons_taken rfl rfl rfl rfl (CallCompletes.monoPP (hWs z b (b + 14) (b + 270) (b + 398) (b + 1294)
      (fun h => b + 1422 + 256 * h))
      (fun _ hp => ⟨(readsAt_of_dvWords hp.1).1, (readsAt_of_dvWords hp.1).2.1⟩) fun _ _ _ h => h) ?_
    refine kidsCompl_cons_taken (decide_eq_true h12) rfl
      (args := [gen ^ 0, gen ^ r, gen ^ (b + 1294), gen ^ (b + 34190)])
      (by show [word 1 0, gen ^ r, gen ^ (b + 1294), gen ^ (b + 34190)] = _; rw [word_one, pow_zero]) rfl
      (CallCompletes.monoPP (dv_loop_completes hwf k z (by omega) hsl horth (gen ^ (b + 1294)) (gen ^ (b + 34190)) 0 hr1)
        (fun rd hp => ⟨weightsHold_of (readsAt_of_dvWords hp.1).2.1, fun j hj => ?_⟩) fun _ _ _ h => h) ?_
    · rw [blobRoot_eq r syms hj]
      exact rootsCells_reads (readsAt_of_dvWords hp.1).2.2 (by omega)
    refine kidsCompl_cons_taken rfl rfl rfl rfl
      ((da_pad_completes k (r := r) (d := LeanDa.maxRows - r) (by simp [LeanDa.maxRows, LeanDa.logMaxRows]; omega)
        (gen ^ (b + 34190))).mono (fun rd hp j hj => ?_) (fun _ _ _ h => h)).toCallCompletes ?_
    · have := rootsCells_reads (readsAt_of_dvWords hp.1).2.2 (i := r + j)
        (by simp [LeanDa.maxRows, LeanDa.logMaxRows] at hj; omega)
      rwa [blobLeaf, ite_neg' (by omega)] at this
    refine kidsCompl_cons_taken rfl (f := daLevelsName 5) rfl rfl (by rw [rootLeaves_root]; rfl)
      (CallCompletes.monoPP (da_levels_completes hwf k (Or.inl rfl) (gen ^ (b + 34190)) (rootLeaves r syms)
        (length_rootLeaves r syms)) (fun rd hp => treeMem_of_reads (length_rootLeaves r syms) ?_)
        fun _ _ _ h => h) kidsCompl_nil
    have hR := (readsAt_of_dvWords hp.1).2.2
    rw [rootsCells, readsAt_append] at hR
    exact hR.1
  · -- the entries
    intro rd ts _ _ _ hv hq
    have hlen := kidsValid_len hv
    rw [show ((dvPre.filterMap Stmt.callS).map (mkCall σ)).length = 6 from rfl] at hlen
    rcases ts with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, _ | ⟨t4, _ | ⟨t5, _ | ⟨t6, _ | ⟨t7, ts⟩⟩⟩⟩⟩⟩⟩
    all_goals try (simp at hlen; done)
    have h1 : FreePost rd t1 := hq.1 rfl
    have h2 : FreePost rd t2 := hq.2.1 rfl
    have h3 : FreePost rd t3 := hq.2.2.1 rfl
    have h4 : DvLPost syms 0 r rd t4 := hq.2.2.2.1 (decide_eq_true h12)
    have h5 : PopsNil rd t5 := hq.2.2.2.2.1 rfl
    have h6 : FreePost rd t6 := hq.2.2.2.2.2.1 rfl
    rw [pops_straight find_dv dv_body rfl, Tree.popsKids, Tree.popsKids, Tree.popsKids, Tree.popsKids,
      Tree.popsKids, Tree.popsKids, Tree.popsKids, dv_splice h12, h1.1, h2.1, h3.1, h4, h5, h6.1]
    simp only [List.append_nil, Nat.sub_zero, dvPops']
    rfl

end
end LeanVM.Guest.Complete
