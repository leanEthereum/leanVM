/-
  LeanVM.Guest.B1.VerifySub.Front

  `verify_sub`'s front sections: the seed, the announced words, the root's words, squeezes, and
  the lemmas every section uses.
-/

module

public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.Value.KeccakSponge
public import LeanVM.Guest.Word
public import LeanVM.Protocol.KeccakHash

/-!
# The front of `verify_sub`

* `vs_seed`: the seed's `KECCAK` (`keccak_cells([seed_0, seed_1, pi_0, pi_1], sp, final=0)`):
  its capacity is `keccakF (seedInput seed pi)`'s, the digests read off the four cells;
* `vsReadsT_holds`, `vs_absorb8`: the eight announced words read from the stream and absorbed from
  the seed's capacity (the first four permuted in);
* `vsRootsT_holds`, `vs_absorbRoot`: the last four announced words permuted in, the root's two
  words read and waiting;
* `vsSqzT_holds`: a squeeze with nothing waiting; `vsTabsT_holds`: `tabs = g_squares·g^236`;
* `mem_size`, `mem_size_le`: a memory image holding `n` words at one pointer has at least `n`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## Atoms -/

/-- **The capacity a `KECCAK` atom writes**: outputs `8 .. 12`, the capacity of the permutation
of the cells it reads. -/
theorem keccak_cap {ins outs : List V} (hk : (Atom.keccak ins outs false false).Holds rd σ)
    (ho13 : outs.length = 13 := by first | rfl | simp) :
    (outs.drop 8).map σ = capOf (permOf (ins.map σ)) := by
  obtain ⟨-, ho, hout⟩ := keccak_outs hk ho13
  apply List.ext_getElem (by simp [ho, capOf])
  intro k h1 h2
  simp only [List.length_map, List.length_drop, ho] at h1
  have e := hout (8 + k) (by omega)
  rw [List.getD_eq_getElem _ _ (by omega)] at e
  simp only [List.getElem_map, List.getElem_drop, e]
  simp only [capOf]
  interval_cases k <;> rfl

theorem vsRun_drop8 (b : ℕ) :
    ((vsRun b 13).drop 8).map σ =
      [σ (.n (b + 8)), σ (.n (b + 9)), σ (.n (b + 10)), σ (.n (b + 11)), σ (.n (b + 12))] := rfl

theorem holds_ld1 {d p off : ℕ} {X : Prop} :
    Stmt.HoldsList C rd σ [vsLd d p off] X kret ↔ LoadHolds rd (σ (.n p)) off (σ (.n d)) ∧ X :=
  Iff.rfl

theorem holds_atom1 {a : Atom} {X : Prop} :
    Stmt.HoldsList C rd σ [.atom a] X kret ↔ a.Holds rd σ ∧ X := Iff.rfl

theorem readsAt_ext {p : E} {xs ys : List E} (hl : xs.length = ys.length)
    (hx : ReadsAt rd p xs) (hy : ReadsAt rd p ys) : xs = ys :=
  List.ext_getElem hl fun k h1 h2 ↦ loadHolds_unique (hx k h1) (hy k h2)

/-! ## The window table -/

set_option maxRecDepth 100000 in
/-- `tabs = g_squares · g^236`'s word. -/
theorem vsWinWord_eq : vsWinWord = gen ^ winTabAt := by
  rw [vsWinWord, word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound winTabAt; omega)]
  congr 1

/-- `tabs` into `d`: `g_squares · g^236`. -/
theorem vsTabsT_holds {c d : ℕ} {X : Prop}
    (h : Stmt.HoldsList C rd σ (vsTabsT c d) X kret) : σ (.n d) = σ (.n 4) * gen ^ winTabAt ∧ X := by
  simp only [vsTabsT, vsConst, vsMul, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨hc, hm, hX⟩ := h
  exact ⟨by rw [hm, hc, vsWinWord_eq], hX⟩

/-! ## The seed -/

/-- The seed's `KECCAK` atom. -/
abbrev vsSeedAtom : Atom :=
  .keccak [.n 2, .n 3, .n 0, .n 1, .n 8, .n 9, .n 10, .n 11, .n 8, .n 8, .n 9, .n 10, .n 11]
    (vsRun 12 13) false false

/-- The head: the zero cells, the seed's atom. -/
theorem vsHeadT_holds (h : Stmt.HoldsList C rd σ vsHeadT next kret) :
    σ (.n 8) = 0 ∧ σ (.n 9) = 0 ∧ σ (.n 10) = 0 ∧ σ (.n 11) = 0 ∧ vsSeedAtom.Holds rd σ ∧ next := by
  simp only [vsHeadT, vsAlloc, vsConst, keccakA, Stmt.HoldsList, Stmt.Holds] at h
  obtain ⟨-, -, h10, h11, h12, h13, hk, -, -, -, hn⟩ := h
  simp only [Atom.Holds, word_zero] at h10 h11 h12 h13
  exact ⟨h10, h11, h12, h13, hk, hn⟩

/-- **The seed** (G:3557-3561; V:2346): the four cells are two digests' halves, and the capacity
the atom writes is the seed state's. -/
theorem vs_seed (hk : vsSeedAtom.Holds rd σ) (h10 : σ (.n 8) = 0) (h11 : σ (.n 9) = 0)
    (h12 : σ (.n 10) = 0) (h13 : σ (.n 11) = 0) :
    ∃ seed pi : Digest, (σ (.n 2), σ (.n 3)) = digestHalves seed ∧
      (σ (.n 0), σ (.n 1)) = digestHalves pi ∧
      [σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)] =
        capOf (keccakF1600 (seedInput seed pi)) := by
  refine ⟨digestFromHalves (σ (.n 2), σ (.n 3)), digestFromHalves (σ (.n 0), σ (.n 1)),
    (digestScalars_digestOfScalars _).symm, (digestScalars_digestOfScalars _).symm, ?_⟩
  obtain ⟨-, -, hK⟩ := (keccak_holds_13 (outs := vsRun 12 13) (by simp [vsRun])).mp hk
  have hch := Keccak.keccak_chain (P := [σ (.n 2), σ (.n 3), σ (.n 0), σ (.n 1)])
    (S0 := Keccak.zeroState) (B := 1)
    (I := fun _ ↦ cells13 ([.n 2, .n 3, .n 0, .n 1, .n 8, .n 9, .n 10, .n 11, .n 8, .n 8,
      .n 9, .n 10, .n 11].map σ))
    (O := fun k ↦ if k = 0 then cellsOfState Keccak.zeroState false else cells13 ((vsRun 12 13).map σ))
    (by simp)
    (fun k hk c hc ↦ by
      obtain rfl : k = 0 := by omega
      fin_cases c <;> simp_all [cells13, Keccak.cellsOfState_zero])
    (fun k hk c hc ↦ by
      obtain rfl : k = 0 := by omega
      fin_cases c <;> simp_all [cells13, Keccak.cellsOfState_zero])
    (fun k hk ↦ by
      obtain rfl : k = 0 := by omega
      exact hK)
  simp only [one_ne_zero, ↓reduceIte] at hch
  rw [show [σ (.n 2), σ (.n 3), σ (.n 0), σ (.n 1)] =
      [(digestHalves (digestFromHalves (σ (.n 2), σ (.n 3)))).1,
        (digestHalves (digestFromHalves (σ (.n 2), σ (.n 3)))).2,
        (digestHalves (digestFromHalves (σ (.n 0), σ (.n 1)))).1,
        (digestHalves (digestFromHalves (σ (.n 0), σ (.n 1)))).2] by
      simp only [digestScalars_digestOfScalars],
    Keccak.absorbChunks_seed] at hch
  simp only [capOf]
  rw [← congrFun hch 8, ← congrFun hch 9, ← congrFun hch 10, ← congrFun hch 11, ← congrFun hch 12]
  rfl

/-! ## The announced words -/

/-- The values of the eight announced words. -/
def vsX (i : ℕ) : ℕ := [27, 30, 33, 36, 52, 55, 58, 61].getD i 0

/-- The stream word at offset `off` read into `x`, packed (`fs_next`). -/
def WordAt (rd : Reader) (σ : Val) (off x : ℕ) : Prop :=
  LoadHolds rd (σ (.n 25)) off (σ (.n x)) ∧ FsPackOk σ (.n x) (x + 1) dsObserve

/-- The first four announced words' permutation. -/
abbrev vsAtom39 : Atom :=
  .keccak [.n 28, .n 29, .n 31, .n 32, .n 34, .n 35, .n 37, .n 38, .n 20, .n 21, .n 22, .n 23, .n 24]
    (vsRun 39 13) false false

theorem vsReadsT_holds (h : Stmt.HoldsList C rd σ vsReadsT next kret) :
    (∀ i < 8, WordAt rd σ i (vsX i)) ∧
      (∀ i < 6, LoadHolds rd (σ (.n 26)) i (σ (.n (vsX (i + 1))))) ∧ vsAtom39.Holds rd σ ∧ next := by
  rw [vsReadsT] at h
  simp only [holdsList_append] at h
  obtain ⟨w0, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨w1, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r1, h⟩ := holds_ld1.1 h
  obtain ⟨w2, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r2, h⟩ := holds_ld1.1 h
  obtain ⟨w3, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r3, h⟩ := holds_ld1.1 h
  obtain ⟨hk, h⟩ := holds_atom1.1 h
  obtain ⟨w4, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r4, h⟩ := holds_ld1.1 h
  obtain ⟨w5, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r5, h⟩ := holds_ld1.1 h
  obtain ⟨w6, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨r6, h⟩ := holds_ld1.1 h
  obtain ⟨w7, hn⟩ := (holds_fsNextT _ _ _ _ _).1 h
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, hk, hn⟩
  · interval_cases i
    · exact w0
    · exact w1
    · exact w2
    · exact w3
    · exact w4
    · exact w5
    · exact w6
    · exact w7
  · interval_cases i
    · exact r1
    · exact r2
    · exact r3
    · exact r4
    · exact r5
    · exact r6

/-- The eight announced words' values. -/
def vsWords (σ : Val) : List E :=
  [σ (.n 27), σ (.n 30), σ (.n 33), σ (.n 36), σ (.n 52), σ (.n 55), σ (.n 58), σ (.n 61)]

/-- A word's two packed cells. -/
theorem wordAt_cells {off x : ℕ} (h : WordAt rd σ off x) :
    (σ (.n (x + 1)), σ (.n (x + 2))) = Keccak.scalarCells (σ (.n x)) dsObserve :=
  fsPackT_cells h.2

theorem absorb8_shape (cap : List E) (a0 a1 a2 a3 a4 a5 a6 a7 : E) :
    (⟨cap, []⟩ : Fs).absorbAll [a0, a1, a2, a3, a4, a5, a6, a7] dsObserve =
      ⟨capOf (Fs.perm ⟨cap, [(a0, dsObserve), (a1, dsObserve), (a2, dsObserve), (a3, dsObserve)]⟩),
        [(a4, dsObserve), (a5, dsObserve), (a6, dsObserve), (a7, dsObserve)]⟩ := by
  simp [Fs.absorbAll, Fs.absorb, rateScalars]

theorem absorb2_shape (cap : List E) (a4 a5 a6 a7 b0 b1 : E) :
    ((⟨cap, [(a4, dsObserve), (a5, dsObserve), (a6, dsObserve), (a7, dsObserve)]⟩ : Fs).absorb b0
        dsObserve).absorb b1 dsObserve =
      ⟨capOf (Fs.perm ⟨cap, [(a4, dsObserve), (a5, dsObserve), (a6, dsObserve), (a7, dsObserve)]⟩),
        [(b0, dsObserve), (b1, dsObserve)]⟩ := by
  simp [Fs.absorb, rateScalars]

/-- **The announced words absorbed** from the seed's capacity: the first four permuted in by the
atom, the last four waiting. -/
theorem vs_absorb8 (hw : ∀ i < 8, WordAt rd σ i (vsX i)) (hk : vsAtom39.Holds rd σ) :
    (⟨[σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)], []⟩ : Fs).absorbAll (vsWords σ)
        dsObserve =
      ⟨[σ (.n 47), σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51)],
        [(σ (.n 52), dsObserve), (σ (.n 55), dsObserve), (σ (.n 58), dsObserve),
          (σ (.n 61), dsObserve)]⟩ := by
  have hcap := keccak_cap hk
  rw [vsRun_drop8] at hcap
  have c0 := wordAt_cells (hw 0 (by omega))
  have c1 := wordAt_cells (hw 1 (by omega))
  have c2 := wordAt_cells (hw 2 (by omega))
  have c3 := wordAt_cells (hw 3 (by omega))
  simp only [vsX, List.getD_cons_zero, List.getD_cons_succ] at c0 c1 c2 c3
  have e := absorb8_shape [σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)] (σ (.n 27))
    (σ (.n 30)) (σ (.n 33)) (σ (.n 36)) (σ (.n 52)) (σ (.n 55)) (σ (.n 58)) (σ (.n 61))
  have hl : rateOf [(σ (.n 27), dsObserve), (σ (.n 30), dsObserve), (σ (.n 33), dsObserve),
      (σ (.n 36), dsObserve)] ++ [σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)] =
      List.map σ [.n 28, .n 29, .n 31, .n 32, .n 34, .n 35, .n 37, .n 38, .n 20, .n 21, .n 22,
        .n 23, .n 24] := by
    rw [rateOf_four, ← c0, ← c1, ← c2, ← c3]; rfl
  rw [vsWords, e, Fs.perm, hl, ← hcap]

/-! ## The root -/

/-- The last four announced words' permutation. -/
abbrev vsAtom255 : Atom :=
  .keccak [.n 53, .n 54, .n 56, .n 57, .n 59, .n 60, .n 62, .n 63, .n 47, .n 48, .n 49, .n 50,
    .n 51] (vsRun 255 13) false false

theorem vsRootsT_holds (h : Stmt.HoldsList C rd σ vsRootsT next kret) :
    vsAtom255.Holds rd σ ∧ WordAt rd σ 8 268 ∧ WordAt rd σ 9 271 ∧ next := by
  rw [vsRootsT] at h
  simp only [holdsList_append] at h
  obtain ⟨hk, h⟩ := holds_atom1.1 h
  obtain ⟨w8, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨w9, hn⟩ := (holds_fsNextT _ _ _ _ _).1 h
  exact ⟨hk, w8, w9, hn⟩

/-- **The root's words absorbed** after the announced ones: the last four permuted in. -/
theorem vs_absorbRoot (hw : ∀ i < 8, WordAt rd σ i (vsX i)) (hk : vsAtom255.Holds rd σ) :
    (((⟨[σ (.n 47), σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51)],
        [(σ (.n 52), dsObserve), (σ (.n 55), dsObserve), (σ (.n 58), dsObserve),
          (σ (.n 61), dsObserve)]⟩ : Fs).absorb (σ (.n 268)) dsObserve).absorb (σ (.n 271))
        dsObserve) =
      ⟨[σ (.n 263), σ (.n 264), σ (.n 265), σ (.n 266), σ (.n 267)],
        [(σ (.n 268), dsObserve), (σ (.n 271), dsObserve)]⟩ := by
  have hcap := keccak_cap hk
  rw [vsRun_drop8] at hcap
  have c4 := wordAt_cells (hw 4 (by omega))
  have c5 := wordAt_cells (hw 5 (by omega))
  have c6 := wordAt_cells (hw 6 (by omega))
  have c7 := wordAt_cells (hw 7 (by omega))
  simp only [vsX, List.getD_cons_zero, List.getD_cons_succ] at c4 c5 c6 c7
  have e := absorb2_shape [σ (.n 47), σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51)] (σ (.n 52))
    (σ (.n 55)) (σ (.n 58)) (σ (.n 61)) (σ (.n 268)) (σ (.n 271))
  have hl : rateOf [(σ (.n 52), dsObserve), (σ (.n 55), dsObserve), (σ (.n 58), dsObserve),
      (σ (.n 61), dsObserve)] ++ [σ (.n 47), σ (.n 48), σ (.n 49), σ (.n 50), σ (.n 51)] =
      List.map σ [.n 53, .n 54, .n 56, .n 57, .n 59, .n 60, .n 62, .n 63, .n 47, .n 48, .n 49,
        .n 50, .n 51] := by
    rw [rateOf_four, ← c4, ← c5, ← c6, ← c7]; rfl
  rw [e, Fs.perm, hl, ← hcap]

/-! ## Squeezes -/

/-- **A squeeze with nothing waiting** (`vsSqzT`), on the zero cells. -/
theorem vsSqzT_holds {capb o : ℕ} (h10 : σ (.n 8) = 0) (h11 : σ (.n 9) = 0)
    (h12 : σ (.n 10) = 0) (h13 : σ (.n 11) = 0)
    (h : Stmt.HoldsList C rd σ (vsSqzT capb o) next kret) :
    (⟨(vsRun capb 5).map σ, []⟩ : Fs).squeeze =
        (σ (.n (o + 13)), ⟨[σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)),
          σ (.n (o + 12))], []⟩) ∧ next := by
  simp only [vsSqzT, Stmt.HoldsList, Stmt.Holds, keccakA] at h
  obtain ⟨hk, h⟩ := h
  obtain ⟨hch, hn⟩ := (holds_challengeT _ _ _ _).1 h
  have hs := squeeze_atom (s := ⟨(vsRun capb 5).map σ, []⟩) (b := o + 13) hk
    (by simp only [List.map_append, List.map_cons, List.map_nil, h10, h11, h12, h13, rateOf_nil])
    hch
  rw [vsRun_drop8] at hs
  obtain ⟨e1, e2⟩ := hs
  simp only [Fs.squeeze] at e1 e2 ⊢
  rw [← e1, ← e2]
  exact ⟨rfl, hn⟩

/-! ## The memory's size -/

/-- **A memory image holding `n` words at one pointer has at least `n` words.** -/
theorem mem_size_big {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {p : E} {n : ℕ} (hn : n ≤ 2 ^ 33)
    (h : ∀ j < n, ∃ v, LoadHolds L.read p j v) : n ≤ 2 ^ κ := by
  have hκ64 : κ < 64 := by omega
  have hidx : ∀ j : Fin n, ∃ i : Fin (2 ^ κ), p.limb 0 * Parameters.addressOfIndex j =
      Parameters.addressOfIndex i := by
    intro j
    obtain ⟨v, -, hv⟩ := h j j.isLt
    obtain ⟨i, hi, -⟩ := (read_some_iff hκ64 L _ _).mp hv
    exact ⟨i, hi⟩
  choose f hf using hidx
  have hinj : Function.Injective f := by
    intro a b hab
    have ea := hf a
    have eb := hf b
    rw [hab, ← eb] at ea
    have hp : p.limb 0 ≠ 0 := by
      intro h0
      have := hf a
      rw [h0, zero_mul] at this
      exact Parameters.gpow_ne_zero _ this.symm
    have := mul_left_cancel₀ hp ea
    have hlt : ∀ x : Fin n, (x : ℕ) < 2 ^ 64 - 1 := fun x ↦ by have := x.isLt; omega
    exact Fin.ext (gpow_injOn (hlt a) (hlt b) this)
  simpa using Fintype.card_le_of_injective f hinj

theorem mem_size {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {p : E} {n : ℕ} (hn : n ≤ 2 ^ 32)
    (h : ∀ j < n, ∃ v, LoadHolds L.read p j v) : n ≤ 2 ^ κ :=
  mem_size_big hκ L (by omega) h

/-- A run of words read at one pointer is at most `2^32` long. -/
theorem mem_size_le {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {p : E} {xs : List E}
    (h : ReadsAt L.read p xs) : xs.length ≤ 2 ^ 32 := by
  by_contra hlt
  have hb := mem_size_big hκ L (n := 2 ^ 32 + 1) (by norm_num)
    (fun j hj ↦ ⟨xs[j]'(by omega), h j (by omega)⟩)
  have : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hκ
  omega

/-- The window table at `g_squares·g^236` gives the memory at least `2^11` words. -/
theorem winTab_kappa {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {q : E} (h : ExpWinTab L.read q) :
    winTabBits ≤ κ := by
  have hs := mem_size hκ L (p := q * gen ^ winTabAt) (n := 2 ^ winTabBits) (by norm_num)
    (fun j hj ↦ ⟨_, by rw [loadHolds_mul_gen_pow]; exact h j hj⟩)
  by_contra hlt
  have : 2 ^ κ < 2 ^ winTabBits := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

end
end LeanVM.Guest.B1.VerifySub
