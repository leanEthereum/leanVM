/-
  LeanVM.Guest.B1.Main.AggFs

  The batching (`Node.batch`) on the guest's carried sponge, rows of a sponge in memory, and a
  checker, by kernel evaluation, of a straight-line chain of `KECCAK`s absorbing packed words.
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Sumcheck.Run
public import LeanVM.Guest.Batch.Run
public import LeanVM.Guest.B1.Common.Atoms

/-!
# The batching's sponge

* `batch_fs`: `Node.batch` (N:268) on the carried sponge (`Fs`): the seed's capacity absorbs the
  batching's words (`aggAbs`), one squeeze's powers give the lambdas (`sqLF`, `aggLam`), and
  `bsRun` (B1-a) runs the sumcheck (`aggRun`); from G4's `Batch.batch_eq` and the carried
  sponge's operations (`carries_absorb`, `carries_squeeze`, `batchRounds_run`).
* `RowRel rd p s`: thirteen words at `p` carry the sponge `s`, its capacity cells, then each
  waiting scalar's two rate cells (as `fs_pack` writes them, `PackOf`), zeros past them;
  `rowRel_perm`: a `KECCAK` reading them (canonical) permutes `s`.
* `DupSpec`: a straight-line chain of `KECCAK`s, block `k + 1` reading the packed cells of the
  words `4k .. 4k + 3` and block `k`'s capacity outputs; `DupSpec.check` is evaluated by the
  kernel, and `DupSpec.chain`: from a sponge with four waiting scalars that the first block
  permutes, absorbing the words leaves the last block's capacity and the last four words waiting.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## The batching on the carried sponge -/

/-- The batching's initial sponge, carried: the seed's capacity, nothing waiting. -/
def aggS0 : Fs := ⟨capOf batchSeed, []⟩

theorem carries_aggS0 : aggS0.Carries ⟨batchSeed, [], none⟩ := ⟨rfl, rfl⟩

theorem carries_obsAll : ∀ (xs : List E) {s : Fs} {sp : Sponge}, s.Carries sp →
    (s.absorbAll xs dsObserve).Carries (Batch.obsAll sp xs)
  | [], _, _, h => h
  | x :: xs, _, _, h => carries_obsAll xs (carries_absorb h x dsObserve)

/-- One squeeze on the carried sponge, its powers the lambdas of `n` children: the lambdas and the
sponge after the squeeze. -/
def sqLF (n : ℕ) (s : Fs) : List (E × E) × Fs := (Batch.lambdaPowers s.squeeze.1 n, s.squeeze.2)

theorem carries_sqL (n : ℕ) {s : Fs} {sp : Sponge} (h : s.Carries sp) :
    (Batch.sqL n sp).1 = (sqLF n s).1 ∧ (sqLF n s).2.Carries (Batch.sqL n sp).2 := by
  obtain ⟨e1, h1⟩ := carries_squeeze h
  have e1' : (Batch.sq sp).1 = s.squeeze.1 := e1
  exact ⟨by simp only [Batch.sqL, sqLF, e1'], h1⟩

/-- The sponge after the batching's words. -/
def aggAbs (cs : List ChildClaims) : Fs := aggS0.absorbAll (Batch.cellsBeforeChallenge cs) dsObserve

/-- The lambdas and the sponge after them. -/
def aggLam (cs : List ChildClaims) : List (E × E) × Fs := sqLF cs.length (aggAbs cs)

/-- The sumcheck's run: its challenges and final claim, and the sponge after it. -/
def aggRun (cs : List ChildClaims) (h : BatchingHints) : (List E × E) × Fs :=
  bsRun h.sumcheckMessages (Batch.batchedClaim cs (aggLam cs).1) (aggLam cs).2

/-- **`Node.batch` on the carried sponge.** -/
theorem batch_fs (cs : List ChildClaims) (h : BatchingHints) :
    batch cs h =
      if (aggRun cs h).1.2 = h.finalBytecodeValue * Batch.batchedBytecodeWeight cs (aggLam cs).1 (aggRun cs h).1.1
      then some ⟨(aggRun cs h).1.1, h.finalBytecodeValue⟩ else none := by
  rw [Batch.batch_eq]
  have hc := carries_obsAll (Batch.cellsBeforeChallenge cs) carries_aggS0
  obtain ⟨e1, h1⟩ := carries_sqL cs.length hc
  obtain ⟨sp', -, hr⟩ := B1.batchRounds_run h.sumcheckMessages (Batch.batchedClaim cs (aggLam cs).1)
    (aggLam cs).2 _ h1
  rw [Batch.batchRounds_run] at hr
  have e1' : (Batch.sqL cs.length (Batch.batchSponge cs)).1 = (aggLam cs).1 := e1
  have hr' : (Batch.rsRun h.sumcheckMessages (Batch.batchedClaim cs (aggLam cs).1)
      (Batch.sqL cs.length (Batch.batchSponge cs)).2).1 = (aggRun cs h).1 := congrArg Prod.fst hr
  simp only [e1', hr']

/-! ## Absorbing a block of four -/

/-- Absorbing four scalars on a full queue: one permutation, the four waiting. -/
theorem absorb4_full (s : Fs) (h : s.pend.length = 4) (a b c d : E) (t : ℕ) :
    s.absorbAll [a, b, c, d] t = ⟨capOf s.perm, [(a, t), (b, t), (c, t), (d, t)]⟩ := by
  have h1 : s.absorb a t = ⟨capOf s.perm, [(a, t)]⟩ := by
    simp [Fs.absorb, h, rateScalars]
  show (s.absorb a t).absorbAll [b, c, d] t = _
  rw [h1, absorbAll_short ⟨capOf s.perm, [(a, t)]⟩ [b, c, d] t (by simp)]
  rfl

theorem absorbAll_append (s : Fs) (xs ys : List E) (t : ℕ) :
    s.absorbAll (xs ++ ys) t = (s.absorbAll xs t).absorbAll ys t := List.foldl_append ..

/-! ## Rows -/

/-- `c1`, `c2` are the rate cells of the scalar `x` with tag `1`, once `c1` is canonical (as
`fs_pack` writes them, `fsPackT_cells`). -/
def PackOf (x c1 c2 : E) : Prop := IsCanonical128 c1 → (c1, c2) = Keccak.scalarCells x dsObserve

theorem packOf_of {σ : Val} {x : V} {b : ℕ} (h : FsPackOk σ x b dsObserve) :
    PackOf (σ x) (σ (.n (b + 6))) (σ (.n (b + 8))) := fun hc => fsPackT_cells h hc

/-- The row's eight rate cells, words `5 .. 12`. -/
noncomputable def rowRate (rd : Reader) (p : E) : List E := (List.range 8).map fun c => memAt rd p (5 + c)

/-- The row's five capacity cells, words `0 .. 4`. -/
noncomputable def rowCap (rd : Reader) (p : E) : List E := (List.range 5).map fun i => memAt rd p i

/-- **The row at `p` carries the sponge `s`**: words `0 .. 4` its capacity cells, words
`5 + 2k`, `6 + 2k` waiting scalar `k`'s (tag `1`), zeros past them. -/
def RowRel (rd : Reader) (p : E) (s : Fs) : Prop :=
  s.cap = rowCap rd p ∧ s.pend.length ≤ 4 ∧ ∀ k < 4,
    if h : k < s.pend.length then
      s.pend[k].2 = dsObserve ∧ PackOf s.pend[k].1 (memAt rd p (5 + 2 * k)) (memAt rd p (6 + 2 * k))
    else memAt rd p (5 + 2 * k) = 0 ∧ memAt rd p (6 + 2 * k) = 0

theorem getD_mem {α : Type} {l : List α} {c : ℕ} {d : α} (h : c < l.length) : l.getD c d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem _

theorem list_eq_of_getD {l1 l2 : List E} {n : ℕ} (h1 : l1.length = n) (h2 : l2.length = n)
    (h : ∀ c < n, l1.getD c 0 = l2.getD c 0) : l1 = l2 :=
  List.ext_getElem (by omega) fun c hc1 hc2 => by
    have := h c (by omega)
    rwa [List.getD_eq_getElem _ _ hc1, List.getD_eq_getElem _ _ hc2] at this

/-- The rate cells of waiting scalars of tag `1` whose cells are the packed `cells`
(canonical). -/
theorem rateOf_of_packs {pend : List (E × ℕ)} {cells : List E}
    (hc : cells.length = 8) (hcan : AllCanonical cells)
    (h : ∀ k < 4, if h : k < pend.length then
      pend[k].2 = dsObserve ∧ PackOf pend[k].1 (cells.getD (2 * k) 0) (cells.getD (2 * k + 1) 0)
    else cells.getD (2 * k) 0 = 0 ∧ cells.getD (2 * k + 1) 0 = 0) :
    rateOf pend = cells := by
  refine list_eq_of_getD (n := 8) (by simp [rateOf]) hc fun c hc8 => ?_
  have hr : (rateOf pend).getD c 0 = Keccak.rateCell pend c := by
    simp [rateOf, List.getD_eq_getElem?_getD, hc8]
  rw [hr]
  obtain ⟨j, hj, hcj⟩ : ∃ j < 4, c = 2 * j ∨ c = 2 * j + 1 := ⟨c / 2, by omega, by omega⟩
  have hk := h j hj
  split at hk
  · rename_i hjl
    obtain ⟨ht, hp⟩ := hk
    have e := hp (hcan _ (getD_mem (show 2 * j < cells.length by omega)))
    have e' := Keccak.rateCell_scalar pend j hjl
    rw [ht] at e'
    rcases hcj with rfl | rfl
    · exact congrArg Prod.fst (e'.trans e.symm)
    · exact congrArg Prod.snd (e'.trans e.symm)
  · rename_i hjl
    rcases hcj with rfl | rfl
    · rw [Keccak.rateCell_past pend (c := 2 * j) (by omega)]; exact hk.1.symm
    · rw [Keccak.rateCell_past pend (c := 2 * j + 1) (by omega)]; exact hk.2.symm

theorem rowRate_getD (rd : Reader) (p : E) (c : ℕ) (hc : c < 8) :
    (rowRate rd p).getD c 0 = memAt rd p (5 + c) := by
  simp [rowRate, List.getD_eq_getElem?_getD, hc]

/-- **A row's permutation**: a `KECCAK` reading the row's rate cells (canonical) and capacity
cells permutes the sponge the row carries. -/
theorem rowRel_perm {rd : Reader} {p : E} {s : Fs} (h : RowRel rd p s)
    (hc : AllCanonical (rowRate rd p)) : s.perm = permOf (rowRate rd p ++ rowCap rd p) := by
  obtain ⟨hcap, -, hk⟩ := h
  rw [Fs.perm, hcap, rateOf_of_packs (by simp [rowRate]) hc]
  intro k hk4
  have := hk k hk4
  rw [rowRate_getD rd p (2 * k) (by omega), rowRate_getD rd p (2 * k + 1) (by omega),
    show 5 + (2 * k + 1) = 6 + 2 * k by omega]
  exact this

/-! ## `fs_pack`'s atoms -/

/-- `fsPackT`'s atoms. -/
def fsPackA (x : V) (b t : ℕ) : List Atom :=
  [.hint (.limbs x [.n b, .n (b + 1), .n (b + 2)]),
    .const (.n (b + 3)) (word t 0),
    .assertInK (.n (b + 2)) (.n (b + 3)),
    .const (.n (b + 4)) (word 0 0 1),
    .mul (.n (b + 5)) (.n (b + 4)) (.n (b + 2)),
    .add (.n (b + 6)) x (.n (b + 5)),
    .const (.n (b + 7)) (word 0 t),
    .add (.n (b + 8)) (.n (b + 2)) (.n (b + 7))]

theorem fsPackT_eq_map (x : V) (b t : ℕ) : fsPackT x b t = (fsPackA x b t).map Stmt.atom := rfl

/-- Every atom of `fs_pack(x)` from `b` (tag `1`) is in the list. -/
def packIn (atoms : List Atom) (x : V) (b : ℕ) : Bool :=
  (fsPackA x b dsObserve).all fun a => atoms.any (atomEqb a)

theorem packIn_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x : V} {b : ℕ}
    (h : packIn atoms x b = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) : FsPackOk σ x b dsObserve := by
  have hall : ∀ a ∈ fsPackA x b dsObserve, a.Holds rd σ := by
    intro a ha
    simp only [packIn, List.all_eq_true] at h
    obtain ⟨a', ha', he⟩ := List.any_eq_true.mp (h a ha)
    rw [atomEqb_sound he]
    exact hat a' ha'
  have hA : AllAtoms (fsPackT x b dsObserve) := by
    intro s hs
    rw [fsPackT_eq_map] at hs
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs
    exact ⟨a, rfl⟩
  have hh := (holdsList_atoms (C := fun _ _ _ => True) (rd := rd) (σ := σ) hA True
    (fun _ => True)).mpr ⟨fun a ha => hall a (by
      rw [fsPackT_eq_map] at ha
      obtain ⟨a', ha', he⟩ := List.mem_map.mp ha
      cases he
      exact ha'), trivial⟩
  exact ((holds_fsPackT x b dsObserve True _).mp hh).1

/-! ## Straight-line duplex chains -/

/-- A chain of `KECCAK`s absorbing packed words: the blocks' `KECCAK` inputs and outputs, and
the words with their `fs_pack` bases (`4` per block; the last block's are left waiting). -/
structure DupSpec where
  /-- The blocks' inputs and outputs. -/
  ks : List (List V × List V)
  /-- The words and their `fs_pack` bases. -/
  words : List (V × ℕ)

namespace DupSpec

variable (s : DupSpec)

/-- The number of blocks. -/
def nb : ℕ := s.ks.length

/-- Block `k`'s inputs. -/
def ins (k : ℕ) : List V := (s.ks.getD k ([], [])).1

/-- Block `k`'s outputs. -/
def outs (k : ℕ) : List V := (s.ks.getD k ([], [])).2

/-- Word `w`'s value. -/
def wV (w : ℕ) : V := (s.words.getD w default).1

/-- Word `w`'s `fs_pack` base. -/
def wB (w : ℕ) : ℕ := (s.words.getD w default).2

/-- **The chain's check**: every block a `KECCAK` atom of thirteen cells in the even layouts,
every word packed by its `fs_pack` atoms, block `k + 1`'s inputs the packed cells of words
`4k .. 4k + 3`, then block `k`'s capacity outputs. -/
def check (atoms : List Atom) : Bool :=
  decide (1 ≤ s.nb) && decide (s.words.length = 4 * s.nb) &&
  s.ks.all (fun p => decide (p.1.length = 13) && decide (p.2.length = 13) &&
    atoms.any (isKeccakAt p.1 p.2 false false)) &&
  s.words.all (fun w => packIn atoms w.1 w.2) &&
  (List.range (s.nb - 1)).all fun k =>
    ((List.range 4).all fun j => decide ((s.ins (k + 1)).getD (2 * j) default =
      .n (s.wB (4 * k + j) + 6)) && decide ((s.ins (k + 1)).getD (2 * j + 1) default =
      .n (s.wB (4 * k + j) + 8))) &&
    (List.range 5).all fun i => decide ((s.ins (k + 1)).getD (8 + i) default =
      (s.outs k).getD (8 + i) default)

/-- Block `k`'s words' values. -/
def blk (σ : Val) (k : ℕ) : List E := (List.range 4).map fun j => σ (s.wV (4 * k + j))

/-- The words' values, block by block. -/
def wvals (σ : Val) : List E := (List.range s.nb).flatMap (s.blk σ)

variable {s} {atoms : List Atom} {rd : Reader} {σ : Val}

theorem blk_eq (σ : Val) (k : ℕ) : s.blk σ k = [σ (s.wV (4 * k)), σ (s.wV (4 * k + 1)),
    σ (s.wV (4 * k + 2)), σ (s.wV (4 * k + 3))] := by
  simp [blk, List.range_succ]

/-- The facts of a checked chain. -/
theorem check_facts (h : s.check atoms = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    1 ≤ s.nb ∧ s.words.length = 4 * s.nb ∧
    (∀ k < s.nb, (s.ins k).length = 13 ∧ (s.outs k).length = 13 ∧
      (Atom.keccak (s.ins k) (s.outs k) false false).Holds rd σ) ∧
    (∀ w < s.words.length, FsPackOk σ (s.wV w) (s.wB w) dsObserve) ∧
    ∀ k, k + 1 < s.nb → (∀ j < 4, (s.ins (k + 1)).getD (2 * j) default = .n (s.wB (4 * k + j) + 6) ∧
      (s.ins (k + 1)).getD (2 * j + 1) default = .n (s.wB (4 * k + j) + 8)) ∧
      ∀ i < 5, (s.ins (k + 1)).getD (8 + i) default = (s.outs k).getD (8 + i) default := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, hk⟩, hw⟩, hl⟩ := h
  refine ⟨h1, h2, fun k hk' => ?_, fun w hw' => ?_, fun k hk' => hl k (by omega)⟩
  · have hk'' : k < s.ks.length := hk'
    obtain ⟨⟨a1, a2⟩, a3⟩ := hk _ (getD_mem (d := ([], [])) hk'')
    exact ⟨a1, a2, keccak_sound a3 hat⟩
  · exact packIn_sound (hw _ (getD_mem (d := default) hw')) hat

/-- A `KECCAK` atom's facts: its inputs canonical, its outputs the permutation's cells. -/
theorem keccak_facts {ins outs : List V} (hk : (Atom.keccak ins outs false false).Holds rd σ)
    (ho : outs.length = 13 := by first | rfl | simp) :
    AllCanonical (ins.map σ) ∧ ∀ c (hc : c < 13), σ (outs.getD c default) =
      cellsOfState (permOf (ins.map σ)) false ⟨c, hc⟩ := by
  obtain ⟨-, -, hcan, hc⟩ := keccakA_perm hk ho
  refine ⟨hcan, fun c hc13 => ?_⟩
  rw [List.getD_eq_getElem outs default (by omega : c < outs.length)]
  exact outs_eq hc ⟨c, hc13⟩ (by rw [ho]; exact hc13)

theorem getD_map_val (ins : List V) (c : ℕ) (hc : c < ins.length) :
    (ins.map σ).getD c 0 = σ (ins.getD c default) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getD_eq_getElem _ _ hc]
  simp

/-- One block on: the cells block `k + 1` reads are the packed words of block `k`, then the
capacity of block `k`'s permutation. -/
theorem step_ins (h : s.check atoms = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) {k : ℕ}
    (hk : k + 1 < s.nb) :
    rateOf ((s.blk σ k).map (·, dsObserve)) ++ capOf (permOf ((s.ins k).map σ)) =
      (s.ins (k + 1)).map σ := by
  obtain ⟨-, hwl, hK, hP, hL⟩ := check_facts h hat
  obtain ⟨hl1, ho1, hk1⟩ := hK (k + 1) hk
  obtain ⟨-, ho0, hk0⟩ := hK k (by omega)
  obtain ⟨hcan, -⟩ := keccak_facts hk1 ho1
  have hout := (keccak_facts hk0 ho0).2
  obtain ⟨hr, hc⟩ := hL k hk
  have hR : (rateOf ((s.blk σ k).map (·, dsObserve))).length = 8 := by simp [rateOf]
  refine list_eq_of_getD (n := 13) (by simp [hR, capOf]) (by simp [hl1]) fun c hc13 => ?_
  rw [getD_map_val (s.ins (k + 1)) c (by rw [hl1]; exact hc13)]
  by_cases h8 : c < 8
  · rw [List.getD_append (rateOf ((s.blk σ k).map (·, dsObserve))) _ 0 c (by rw [hR]; exact h8)]
    have hrate : (rateOf ((s.blk σ k).map (·, dsObserve))).getD c 0 =
        Keccak.rateCell ((s.blk σ k).map (·, dsObserve)) c := by
      simp [rateOf, List.getD_eq_getElem?_getD, h8]
    rw [hrate]
    obtain ⟨j, hj, hcj⟩ : ∃ j < 4, c = 2 * j ∨ c = 2 * j + 1 := ⟨c / 2, by omega, by omega⟩
    have hjl : j < ((s.blk σ k).map (·, dsObserve)).length := by simp [blk]; omega
    have e' := Keccak.rateCell_scalar _ j hjl
    have hpj : ((s.blk σ k).map (·, dsObserve))[j] = (σ (s.wV (4 * k + j)), dsObserve) := by
      simp [blk]
    rw [hpj] at e'
    obtain ⟨hr0, hr1⟩ := hr j hj
    have hpk := hP (4 * k + j) (by omega)
    have hcan0 : IsCanonical128 (σ (.n (s.wB (4 * k + j) + 6))) := by
      have := hcan _ (getD_mem (d := 0)
        (show 2 * j < ((s.ins (k + 1)).map σ).length by simp [hl1]; omega))
      rwa [getD_map_val (s.ins (k + 1)) (2 * j) (by rw [hl1]; omega), hr0] at this
    have e := fsPackT_cells hpk hcan0
    rcases hcj with rfl | rfl
    · rw [hr0]; exact congrArg Prod.fst (e'.trans e.symm)
    · rw [hr1]; exact congrArg Prod.snd (e'.trans e.symm)
  · obtain ⟨i, hi, rfl⟩ : ∃ i < 5, c = 8 + i := ⟨c - 8, by omega, by omega⟩
    rw [List.getD_append_right (rateOf ((s.blk σ k).map (·, dsObserve))) _ 0 (8 + i)
      (by rw [hR]; omega), hR, show 8 + i - 8 = i by omega, hc i hi, hout (8 + i) (by omega)]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **A checked chain**: from a sponge with four waiting scalars that the first block permutes,
absorbing the words leaves the last block's capacity cells and the last block's words
waiting. -/
theorem chain (h : s.check atoms = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) (st : Fs)
    (hp : st.pend.length = 4) (h0 : st.perm = permOf ((s.ins 0).map σ)) :
    st.absorbAll (s.wvals σ) dsObserve =
      ⟨(List.range 5).map (fun i => σ ((s.outs (s.nb - 1)).getD (8 + i) default)),
        (s.blk σ (s.nb - 1)).map (·, dsObserve)⟩ := by
  obtain ⟨h1, -, hK, -, -⟩ := check_facts h hat
  have key : ∀ k < s.nb,
      (st.absorbAll ((List.range k).flatMap (s.blk σ)) dsObserve).pend.length = 4 ∧
      (st.absorbAll ((List.range k).flatMap (s.blk σ)) dsObserve).perm =
        permOf ((s.ins k).map σ) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hp, h0⟩
    | succ k ih =>
      intro hk
      obtain ⟨ip, iperm⟩ := ih (by omega)
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, absorbAll_append,
        blk_eq, absorb4_full _ ip]
      refine ⟨rfl, ?_⟩
      rw [← step_ins h hat hk, ← iperm, blk_eq]
      rfl
  obtain ⟨n, hn⟩ : ∃ n, s.nb = n + 1 := ⟨s.nb - 1, by omega⟩
  obtain ⟨ip, iperm⟩ := key n (by omega)
  have hout := (keccak_facts (hK n (by omega)).2.2 (hK n (by omega)).2.1).2
  have hcap : (List.range 5).map (fun i => σ ((s.outs n).getD (8 + i) default)) =
      capOf (permOf ((s.ins n).map σ)) := by
    rw [show (List.range 5).map (fun i => σ ((s.outs n).getD (8 + i) default)) =
      [σ ((s.outs n).getD 8 default), σ ((s.outs n).getD 9 default),
        σ ((s.outs n).getD 10 default), σ ((s.outs n).getD 11 default),
        σ ((s.outs n).getD 12 default)] from rfl, hout 8 (by omega), hout 9 (by omega),
      hout 10 (by omega), hout 11 (by omega), hout 12 (by omega)]
    rfl
  rw [show s.nb - 1 = n by omega, wvals, hn, List.range_succ, List.flatMap_append,
    List.flatMap_singleton, absorbAll_append, blk_eq, absorb4_full _ ip, iperm, Fs.mk.injEq]
  exact ⟨hcap.symm, rfl⟩

end DupSpec

end
end LeanVM.Guest.B1.Main
