/-
  LeanVM.Guest.B1.Da.Complete

  B1 for `da_verify`, completely: a LeanDA witness opening a root and a vector digest, and a memory
  holding the honest words at every choice of `da_verify`'s pointers, give its relation.
-/

module

public import LeanVM.Guest.B1.Da.Witness
public import LeanVM.Guest.B1.Da.ColLoopAt

/-!
# `da_verify`, completely

The honest run of a witness `w` (`daSym`: its rows' cells, `daWs`: its vector's chunks, `daS`: the
vector hash's states, `daA`: the rows' running sums) and the memory it leaves (`DaMem`): at the
`HeapBuf` pointers and frame runs `DaPtrs` (any choice of them), the prefix bases and digests, the
vector hash's states, the counter words, the rows' running sums, the trees (`TreeAt`) and every
column's weights. `da_verify_complete`: on such a memory, `da_verify` returns the root's and the
vector digest's cells.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-! ## The honest run -/

/-- Cell `b` of row `i`. -/
def daSym (w : Da.Witness) (b i : ℕ) : List K := LeanDa.listCell (w.rows.getD i []) b

/-- Chunk `b` of the vector: column `b`'s weights. -/
def daWs (w : Da.Witness) (b : ℕ) : List E := (w.vector.drop (256 * b)).take 256

/-- The vector hash's state before column `b`. -/
def daS (w : Da.Witness) (b : ℕ) : Digest := chainRun paramIv (vecBlocks (daWs w)) vecMd (96 * b)

/-- Cell `b` of row `i`'s inner product with column `b`'s weights. -/
def daCellS (w : Da.Witness) (b i : ℕ) : E :=
  ∑ k ∈ Finset.range 256, (daWs w b).getD k 0 * ofK ((daSym w b i).getD k 0)

/-- Row `i`'s running sum before column `b`. -/
def daA (w : Da.Witness) (i b : ℕ) : E := ∑ c ∈ Finset.range b, daCellS w c i

/-- A tree of depth `k` over `leaf`, every level as `da_levels` lays it out. -/
def TreeAt (rd : Reader) (tree : E) (k : ℕ) (leaf : ℕ → Digest) : Prop :=
  ∀ l ≤ k, ∀ j < 2 ^ (k - l), CellsAt rd (tree * gen ^ (lvOff k l + 2 * j))
    [(digestScalars (nodeD leaf l j)).1, (digestScalars (nodeD leaf l j)).2]

/-- `da_verify`'s pointers: its `HeapBuf`s, the counters' run, every column's tree and weights. -/
structure DaPtrs where
  pb : E
  pd : E
  hs : E
  ctr : E
  acc : E
  rb : E
  ct : E
  rt : E
  node : ℕ → E
  lv : ℕ → E

/-- **The honest memory of `w`'s run** at the pointers `P`. -/
def DaMem (rd : Reader) (P : DaPtrs) (w : Da.Witness) : Prop :=
  (∀ i < w.rows.length, LoadHolds rd (P.pb * gen ^ i) 0 (P.pd * gen ^ (128 * i))) ∧
  (∀ i < w.rows.length, ∀ b < 64, CellsAt rd (P.pd * gen ^ (128 * i + 2 * b))
    [(digestScalars (cellDOf (daSym w) b i)).1, (digestScalars (cellDOf (daSym w) b i)).2]) ∧
  (∀ b ≤ 128, CellsAt rd (P.hs * gen ^ (2 * b)) [(digestScalars (daS w b)).1, (digestScalars (daS w b)).2]) ∧
  CellsAt rd P.ctr ((List.range 385).map fun k => word (k * 2048) 0 0) ∧
  (∀ i < w.rows.length, LoadHolds rd (P.rb * gen ^ i) 0 (P.acc * gen ^ (129 * i))) ∧
  (∀ i < w.rows.length, ∀ b ≤ 128, LoadHolds rd (P.acc * gen ^ (129 * i)) b (daA w i b)) ∧
  TreeAt rd P.ct 7 (fun b => nodeD (colLeafOf w.rows.length (daSym w) b) (LeanDa.logPad w.rows.length) 0) ∧
  TreeAt rd P.rt (LeanDa.logPad w.rows.length) (rowLeafOf w.rows.length (daSym w)) ∧
  (∀ b < 128, TreeAt rd (P.node b) (LeanDa.logPad w.rows.length) (colLeafOf w.rows.length (daSym w) b)) ∧
  (∀ b < 128, CellsAt rd (P.lv b) (daWs w b))

/-! ## Helpers -/

theorem levels_of_treeAt {rd : Reader} {tree : E} {k : ℕ} {leaf : ℕ → Digest} (h : TreeAt rd tree k leaf) :
    Meaning_da_levels k rd [tree] [(digestScalars (nodeD leaf k 0)).1, (digestScalars (nodeD leaf k 0)).2] := by
  refine ⟨tree, _, _, rfl, rfl, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := h 0 le_rfl 0 (by norm_num)
    rw [show lvOff 0 0 + 2 * 0 = 0 by rfl, pow_zero, mul_one] at this
    exact Or.inl ⟨rfl, this⟩
  · exact Or.inr ⟨hk, leaf, h, rfl⟩

/-- A tree's leaf `j`, as the cells at `tree·g^(2j)`. -/
theorem treeAt_leaf {rd : Reader} {tree : E} {k : ℕ} {leaf : ℕ → Digest} (h : TreeAt rd tree k leaf) {j : ℕ}
    (hj : j < 2 ^ k) : CellsAt rd (tree * gen ^ (2 * j)) [(digestScalars (leaf j)).1, (digestScalars (leaf j)).2] := by
  have := h 0 (Nat.zero_le _) j (by simpa using hj)
  rwa [lvOff, Nat.sub_zero, Nat.sub_self, Nat.zero_add] at this

theorem loopTo_of_all {n : ℕ} {B : ℕ → Prop} (hn : 0 < n) (hn' : n < 2 ^ 33) (h : ∀ j < n, B j) :
    LoopTo (gen ^ n) B :=
  ⟨n, hn, rfl, fun j h1 h2 he => by have := gen_pow_inj' (by omega) hn' he; omega, h⟩

theorem frameRun_of_cells {rd : Reader} {p : E} {ws : List E} (hl : 0 < ws.length) (h : CellsAt rd p ws) :
    FrameRun rd p ws := by
  refine ⟨(h 0 hl).1, fun k hk v hv => ?_⟩
  have := (h k hk).2
  rw [hv, List.getD_eq_getElem _ _ hk] at *
  exact Option.some.inj this

theorem decide_gen127 {b : ℕ} (hb : b < 128) : decide (gen ^ b = gen ^ 127) = decide (b = 127) := by
  by_cases h127 : b = 127
  · rw [decide_eq_true h127, decide_eq_true (by rw [h127])]
  · rw [decide_eq_false h127, decide_eq_false fun he => h127 (gen_pow_inj' (by omega) (by omega) he)]

theorem listCell_chunk (row : List K) (b : ℕ) : LeanDa.listCell row b = (row.drop (256 * b)).take 256 := by
  rw [LeanDa.listCell, LeanDa.cellSymbols, mul_comm]

theorem ctr_load {rd : Reader} {ctr : E} (h : CellsAt rd ctr ((List.range 385).map fun k => word (k * 2048) 0 0))
    {k : ℕ} (hk : k < 385) : LoadHolds rd ctr k (word (k * 2048) 0 0) := by
  have := h k (by simpa using hk)
  simpa using this

/-! ## Completeness -/

/-- **What the honest memory holds**, a witness opening `(root, vd)`: every column's memory
(`ColMem`) and its vector hash's chain, and the rest of `DaFacts` at the pointers `P`. -/
theorem daMem_parts {rd : Reader} {root vd : Digest} {w : Da.Witness} (hw : w.Opens root vd) (P : DaPtrs)
    (hP : DaMem rd P w) :
    (∀ b < 128, ColMem (decide (b < 64)) rd b w.rows.length (LeanDa.nPad w.rows.length)
        (LeanDa.logPad w.rows.length) P.pb P.ct P.rb P.hs P.ctr (P.node b) (P.lv b)
        (digestScalars (daS w b)).1 (digestScalars (daS w b)).2 (digestScalars (daS w (b + 1))).1
        (digestScalars (daS w (b + 1))).2
        (digestScalars (nodeD (colLeafOf w.rows.length (daSym w) b) (LeanDa.logPad w.rows.length) 0)).1
        (digestScalars (nodeD (colLeafOf w.rows.length (daSym w) b) (LeanDa.logPad w.rows.length) 0)).2
        (daWs w b) ((List.range 4).map (cvOf b)) ∧
      ChainCells ((digestScalars (daS w b)).1, (digestScalars (daS w b)).2) (vxBlocks ((daWs w b).getD · 0))
        (vxMd (decide (b = 127)) (((List.range 4).map (cvOf b)).getD · 0)) 96
        ((digestScalars (daS w (b + 1))).1, (digestScalars (daS w (b + 1))).2)) ∧
    1 ≤ w.rows.length ∧ w.rows.length ≤ LeanDa.maxRows ∧
    (∀ i < w.rows.length, L88Step rd P.pb P.pd (gen ^ i)) ∧
    LoadHolds rd P.hs 0 (digestScalars paramIv).1 ∧ LoadHolds rd P.hs 1 (digestScalars paramIv).2 ∧
    IsInK P.ctr ∧ (∀ k < 385, ∀ v, rd (P.ctr.limb 0 * Parameters.gpow k) = some v → v = word (k * 2048) 0 0) ∧
    (∀ i < w.rows.length, L89Step rd P.acc P.rb (gen ^ i)) ∧
    (∀ i < w.rows.length, L92Step rd P.rb (gen ^ i)) ∧
    Meaning_da_levels 7 rd [P.ct] [(digestScalars (colRootOf w.rows.length (daSym w))).1,
      (digestScalars (colRootOf w.rows.length (daSym w))).2] ∧
    (∀ i < w.rows.length, L93Step rd P.pb P.rt (gen ^ i)) ∧
    (∀ d < LeanDa.nPad w.rows.length - w.rows.length, L94Step rd P.rt (gen ^ w.rows.length) (gen ^ d)) ∧
    Meaning_da_levels (LeanDa.logPad w.rows.length) rd [P.rt] [(digestScalars (rowRootOf w.rows.length (daSym w))).1,
      (digestScalars (rowRootOf w.rows.length (daSym w))).2] ∧
    CompressCells ![(digestScalars (rowRootOf w.rows.length (daSym w))).1,
      (digestScalars (rowRootOf w.rows.length (daSym w))).2, (digestScalars (colRootOf w.rows.length (daSym w))).1,
      (digestScalars (colRootOf w.rows.length (daSym w))).2] (digestScalars paramIv).1 (digestScalars paramIv).2
      (digestScalars root).1 (digestScalars root).2 (metadataCell 64 true) ∧
    LoadHolds rd P.hs 256 (digestScalars vd).1 ∧ LoadHolds rd P.hs 257 (digestScalars vd).2 := by
  obtain ⟨hr1, hr2, hrl, hcom, hvl, hvd, hdot⟩ := hw
  obtain ⟨m88, mpd, mhs, mctr, m89, macc, mct, mrt, mnode, mlv⟩ := hP
  set r := w.rows.length with hr
  set sym := daSym w
  set lp := LeanDa.logPad r
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp : lp ≤ 10 := logPad_le hr2
  have hN := nPad_le hr2
  obtain ⟨hrN, -⟩ := (logPad_iff (lp := lp) hr1).mp rfl
  have hNdef : LeanDa.nPad r = 2 ^ lp := rfl
  -- the witness in chunks
  have hws : ∀ b < 128, (daWs w b).length = 256 := fun b hb => length_chunk (n := 128) hvl hb
  have hvec : w.vector = (List.range 128).flatMap (daWs w) := (flatMap_chunks _ 256 128 hvl).symm
  have hrowi : ∀ i < r, (w.rows.getD i []).length = 256 * 128 := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact hrl _ (List.getElem_mem _)
  have hsyl : ∀ b < 128, ∀ i < r, (sym b i).length = 256 := fun b hb i hi => by
    show (daSym w b i).length = 256
    rw [daSym, listCell_chunk]; exact length_chunk (hrowi i hi) hb
  have hrow : ∀ i < r, w.rows.getD i [] = (List.range 128).flatMap fun b => sym b i := fun i hi => by
    show _ = (List.range 128).flatMap fun b => LeanDa.listCell (w.rows.getD i []) b
    simp only [listCell_chunk]
    exact (flatMap_chunks _ 256 128 (hrowi i hi)).symm
  -- the root and the vector digest
  have hroot : root = commitOf r sym := toBytes_injective (by
    rw [← hcom, commitCodewords_eq hr1 fun i hi b hb => by
      show _ = LeanDa.listCell (w.rows.getD i []) b
      rw [List.getD_eq_getElem _ _ hi]]
    rfl)
  have hvd' : vd = daS w 128 := toBytes_injective (by
    rw [← hvd, vectorDigest_eq, daS, vectorDigest_chain _ hws, ← hvec])
  -- the rows' sums end at zero
  have hA0 : ∀ i < r, daA w i 128 = 0 := fun i hi => by
    have := hdot _ (List.getElem_mem (show i < w.rows.length from hi))
    rw [← List.getD_eq_getElem _ [] hi,
      dot_eq hvec (hrow i hi) hws (fun b hb => hsyl b hb i hi)] at this
    exact this
  -- every column
  have hcolR : ∀ b < 128, ColMem (decide (b < 64)) rd b r (LeanDa.nPad r) lp P.pb P.ct P.rb P.hs P.ctr
        (P.node b) (P.lv b) (digestScalars (daS w b)).1 (digestScalars (daS w b)).2
        (digestScalars (daS w (b + 1))).1 (digestScalars (daS w (b + 1))).2
        (digestScalars (nodeD (colLeafOf r sym b) lp 0)).1 (digestScalars (nodeD (colLeafOf r sym b) lp 0)).2
        (daWs w b) ((List.range 4).map (cvOf b)) ∧
      ChainCells ((digestScalars (daS w b)).1, (digestScalars (daS w b)).2) (vxBlocks ((daWs w b).getD · 0))
        (vxMd (decide (b = 127)) (((List.range 4).map (cvOf b)).getD · 0)) 96
        ((digestScalars (daS w (b + 1))).1, (digestScalars (daS w (b + 1))).2) := by
    intro b hb
    have hcv : ∀ k < 4, ((List.range 4).map (cvOf b)).getD k 0 = cvOf b k := fun k hk => by
      rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp
    refine ⟨⟨?_, ?_, fun k hk => ?_, fun k hk => (frameRun_of_cells (by rw [hws b hb]; norm_num) (mlv b hb)).2 k
      (by rw [hws b hb]; exact hk),
      fun i hi => ?_, fun d hd => ?_, levels_of_treeAt (mnode b hb), ?_⟩, ?_⟩
    · rw [gen_sq]; exact mhs b (by omega)
    · rw [show gen ^ b * gen * (gen ^ b * gen) = gen ^ (2 * (b + 1)) by rw [← pow_succ, ← pow_add]; congr 1; ring]
      exact mhs (b + 1) (by omega)
    · have hk' : k < 4 := by simpa using hk
      rw [show gen ^ b * gen ^ b * gen ^ b = gen ^ (3 * b) by rw [← pow_add, ← pow_add]; congr 1; ring,
        loadHolds_mul_gen_pow]
      simp only [List.getElem_map, List.getElem_range, cvOf, Nat.add_mul]
      have := ctr_load mctr (k := 3 * b + k) (by omega)
      rwa [Nat.add_mul] at this
    · have hleaf := treeAt_leaf (mnode b hb) (j := i) (by rw [← hNdef]; omega)
      simp only [colLeafOf, hi, ↓reduceIte] at hleaf
      have hsucc : daA w i (b + 1) = daA w i b + daCellS w b i := Finset.sum_range_succ _ _
      refine ⟨(digestScalars (cellDOf sym b i)).1, (digestScalars (cellDOf sym b i)).2, daCellS w b i,
        P.acc * gen ^ (129 * i), daA w i b, ⟨P.lv b, _, _, _, rfl, rfl, sym b i, daWs w b, hsyl b hb i hi,
        hws b hb, mlv b hb, rfl, rfl⟩, m89 i hi, (loadHolds_mul_gen_pow _ b 0 _).mpr (macc i hi b (by omega)),
        (loadHolds_mul_gen_pow _ b 1 _).mpr (by rw [← hsucc]; exact macc i hi (b + 1) (by omega)),
        by rw [gen_sq]; exact hleaf, fun h64 => ⟨P.pd * gen ^ (128 * i), m88 i hi, ?_⟩⟩
      rw [gen_sq, mul_assoc, ← pow_add]
      exact mpd i hi b (of_decide_eq_true h64)
    · unfold GapStep
      rw [pad_ptr]
      have := treeAt_leaf (mnode b hb) (j := r + d) (by rw [← hNdef]; omega)
      simp only [colLeafOf, show ¬(r + d < r) by omega, ↓reduceIte, padCell_cells] at this
      exact this
    · rw [gen_sq]; exact treeAt_leaf mct (j := b) (by norm_num; omega)
    · rw [chainCells_congr (b' := vxBlocks ((daWs w b).getD · 0)) (md' := vxMd (decide (b = 127)) (cvOf b))
        (fun _ _ => rfl) (fun j hj => vxMd_congr hcv hj)]
      refine Or.inr ⟨by norm_num, daS w b, rfl, fun j hj => ⟨vxBlocks_canonical _ _, ?_⟩, ?_⟩
      · rw [vxMd_counters hb hj]; exact isCanonical128_metadataCell _ _
      · rw [daS, daS, vecChain_col _ hb]
  -- the rows' digests
  let cs : ℕ → List E := fun i => (List.range 128).map fun k =>
    if k % 2 = 0 then (digestScalars (cellDOf sym (k / 2) i)).1 else (digestScalars (cellDOf sym (k / 2) i)).2
  have hcsl : ∀ i, (cs i).length = 128 := fun i => by simp [cs]
  have hcsb : ∀ i, (cs i).flatMap cellBytes = (List.range 64).flatMap fun b => digestBytes (cellDOf sym b i) := by
    intro i
    rw [List.flatMap_map, show 128 = 2 * 64 by rfl, flatMap_range_mul 2]
    refine List.flatMap_congr fun b _ => ?_
    rw [show List.range 2 = [0, 1] from rfl, digestBytes_eq]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero,
      show 2 * b % 2 = 0 by omega, show (2 * b + 1) % 2 = 1 by omega, show 2 * b / 2 = b by omega,
      show (2 * b + 1) / 2 = b by omega, ↓reduceIte, one_ne_zero]
  have h93 : ∀ i < r, L93Step rd P.pb P.rt (gen ^ i) := by
    intro i hi
    refine ⟨P.pd * gen ^ (128 * i), cs i, m88 i hi, hcsl i, fun k hk => ?_, fun c hc => ?_, ?_⟩
    · have hk' : k < 128 := by rw [hcsl] at hk; exact hk
      have hl := mpd i hi (k / 2) (by omega)
      rw [pow_add, ← mul_assoc] at hl
      have hl2 := hl (k % 2) (by simp; omega)
      rw [loadHolds_mul_gen_pow, show 2 * (k / 2) + k % 2 = k by omega] at hl2
      simp only [cs, List.getElem_map, List.getElem_range]
      by_cases h2 : k % 2 = 0
      · simp only [h2, ↓reduceIte]
        simpa [h2] using hl2
      · have h1 : k % 2 = 1 := by omega
        simp only [h2, ↓reduceIte]
        simpa [h1] using hl2
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      split_ifs
      exacts [(isCanonical128_digestScalars _).1, (isCanonical128_digestScalars _).2]
    · rw [gen_sq, hcsb i]
      have := treeAt_leaf mrt (j := i) (by rw [← hNdef]; omega)
      simp only [rowLeafOf, hi, ↓reduceIte] at this
      exact this
  refine ⟨hcolR, hr1, hr2,
    fun i hi => ?_, ?_, ?_, (mctr 0 (by simp)).1, fun k hk v hv => ?_, fun i hi => ⟨?_, ?_⟩,
    fun i hi => ⟨P.acc * gen ^ (129 * i), ?_, ?_⟩, levels_of_treeAt mct, h93, fun d hd => ?_, levels_of_treeAt mrt, ?_, ?_, ?_⟩
  · show LoadHolds rd (P.pb * gen ^ i) 0 (P.pd * (gen ^ i) ^ 128)
    rw [← pow_mul, Nat.mul_comm i 128]; exact m88 i hi
  · have := mhs 0 (by norm_num)
    rw [Nat.mul_zero, pow_zero, mul_one] at this
    exact (cellsAt_two.mp this).1
  · have := mhs 0 (by norm_num)
    rw [Nat.mul_zero, pow_zero, mul_one] at this
    exact (cellsAt_two.mp this).2
  · have := (ctr_load mctr hk).2
    rw [hv] at this
    exact Option.some.inj this
  · rw [← pow_mul, Nat.mul_comm i 129]; exact m89 i hi
  · rw [← pow_mul, Nat.mul_comm i 129]
    have := macc i hi 0 (by norm_num)
    rwa [show daA w i 0 = 0 from Finset.sum_range_zero _] at this
  · exact m89 i hi
  · have := macc i hi 128 le_rfl
    rwa [hA0 i hi] at this
  · unfold L94Step
    rw [pad_ptr]
    have := treeAt_leaf mrt (j := r + d) (by rw [← hNdef]; omega)
    simp only [rowLeafOf, show ¬(r + d < r) by omega, ↓reduceIte, padRow_cells] at this
    exact this
  · exact compress_pair.mpr (by rw [hroot]; rfl)
  · have := mhs 128 le_rfl
    obtain ⟨x0, -⟩ := cellsAt_two.mp this
    rw [loadHolds_mul_gen_pow, hvd'] at *
    exact x0
  · have := mhs 128 le_rfl
    obtain ⟨-, x1⟩ := cellsAt_two.mp this
    rw [loadHolds_mul_gen_pow, hvd'] at *
    exact x1

/-- A column's `Meaning` from its memory. -/
theorem colMeaning_of_mem {store : Bool} {rd : Reader} {b r N lp : ℕ} (hb : b < 128) (hr1 : 1 ≤ r)
    (hr33 : r < 2 ^ 33) (hN : N < 2 ^ 33) (hlp : lp < 11)
    {pb ct rb hs ctr node lv h0 h1 o0 o1 c0 c1 : E} {ws cv : List E} (hwl : ws.length = 256) (hcl : cv.length = 4)
    (hm : ColMem store rd b r N lp pb ct rb hs ctr node lv h0 h1 o0 o1 c0 c1 ws cv)
    (hch : ChainCells (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd (decide (b = 127)) (cv.getD · 0)) 96 (o0, o1))
    (hlvK : IsInK lv) :
    Meaning_da_verify_column store rd [gen ^ b, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, pb, ct, rb, hs, ctr] [] := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hm
  refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, h0, h1, o0, o1, lv, node, c0, c1, m1, ?_,
    m2, isInK_gen_pow r, fun _ => loopTo_of_all hr1 hr33 m5, isInK_gen_pow _, fun hne => ?_,
    ⟨lp, hlp, rfl, m7⟩, m8⟩
  · refine ⟨gen ^ b, _, rfl, isInK_gen_pow b, ?_⟩
    rw [decide_gen127 hb]
    exact ⟨_, _, _, _, _, _, _, rfl, rfl, ws, cv, hwl, hcl, m3, hch, hlvK, fun k hk v hv => m4 k (by omega) v hv⟩
  · have hpos : 0 < N - r := by
      by_contra h0
      exact hne (by rw [show N - r = 0 by omega, pow_zero])
    exact loopTo_of_all hpos (by omega) m6

/-- **`da_verify` is complete**: a witness opening `(root, vd)` and, for any choice of the pointers,
a memory holding the honest words there give `da_verify`'s relation returning their cells. -/
theorem da_verify_complete {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {root vd : Digest} {w : Da.Witness} (hw : w.Opens root vd) (P : DaPtrs) (hP : DaMem rd P w) :
    coreProgram.Rel rd "da_verify" [gsq]
      [(digestScalars root).1, (digestScalars root).2, (digestScalars vd).1, (digestScalars vd).2] := by
  obtain ⟨hcol, hr1, hr2, h88, hiv0, hiv1, hkc, hctr, h89, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ :=
    daMem_parts hw P hP
  have hr33 : w.rows.length < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hN := nPad_le hr2
  have hlp := logPad_le hr2
  have hvl := hw.2.2.2.2.1
  refine da_verify_of_facts hm hT ⟨_, P.pb, P.pd, P.hs, P.ctr, P.acc, P.rb, P.ct, P.rt, _, _, _, _, hr1, hr2,
    h88, hiv0, hiv1, hkc, hctr, h89, fun b hb => ?_, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩
  obtain ⟨hcm, hch⟩ := hcol b hb
  have hwl : (daWs w b).length = 256 := length_chunk (n := 128) hvl hb
  exact colMeaning_of_mem hb hr1 hr33 (by omega) (by omega) hwl (by simp) hcm hch
    (hP.2.2.2.2.2.2.2.2.2 b hb 0 (by rw [hwl]; norm_num)).1

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (daSym daWs daS daCellS daA TreeAt DaPtrs DaMem da_verify_complete)
end LeanVM.Guest.B1
