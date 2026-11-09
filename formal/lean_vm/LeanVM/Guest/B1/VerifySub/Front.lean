/-
  LeanVM.Guest.B1.VerifySub.Front

  `verify_sub`'s front sections: the seed, the announced words, the root, the bus challenges.
-/

module

public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.Protocol.KeccakHash
public import LeanVM.Guest.Value.KeccakSponge

/-!
# The front of `verify_sub`

* `vs_seed`: the seed's `KECCAK` (`keccak_cells([seed_0, seed_1, pi_0, pi_1], sp, final=0)`):
  the two pairs of cells are digests' and its capacity is `keccakF (seedInput seed pi)`'s;
* `vsReadsT_holds`, `vs_absorb8`: the eight announced words read from the stream and, from the
  seed's capacity, absorbed (the first four permuted in);
* `vsRootsT_holds`, `vs_absorbRoot`: the root's two words read, the last four announced words
  permuted in;
* `vsSqzT_holds`, `vsAlphasT_holds`: squeezes, the four bus challenges.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## A `KECCAK` atom's capacity -/

/-- **The capacity a `KECCAK` atom writes**: outputs `8 .. 12`, the capacity of the permutation
of the cells it reads. -/
theorem keccak_cap {ins outs : List V} (hk : (Atom.keccak ins outs false false).Holds rd σ)
    (ho13 : outs.length = 13 := by first | rfl | simp) :
    (outs.drop 8).map σ = capOf (permOf (ins.map σ)) := by
  obtain ⟨-, ho, -, hout⟩ := keccak_outs hk ho13
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

/-- A digest of two canonical cells. -/
theorem digest_of_canonical {a b : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b) :
    ∃ d : Digest, (a, b) = digestHalves d := by
  obtain ⟨d, hd⟩ : ∃ d, digestFromHalves (a, b) = some d :=
    ⟨_, by simp only [digestFromHalves, ha, hb, and_self, ↓reduceIte]; exact rfl⟩
  exact ⟨d, (digestScalars_digestOfScalars hd).symm⟩

/-- **The seed** (G:3331-3332; V:2338): the four cells are two digests' cells, and the capacity
the atom writes is the seed state's. -/
theorem vs_seed (hk : vsSeedAtom.Holds rd σ) (h10 : σ (.n 8) = 0) (h11 : σ (.n 9) = 0)
    (h12 : σ (.n 10) = 0) (h13 : σ (.n 11) = 0) :
    ∃ seed pi : Digest, (σ (.n 2), σ (.n 3)) = digestHalves seed ∧
      (σ (.n 0), σ (.n 1)) = digestHalves pi ∧
      [σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)] =
        capOf (keccakF1600 (seedInput seed pi)) := by
  obtain ⟨-, -, hc, -⟩ := keccakA_perm hk
  obtain ⟨seed, es⟩ := digest_of_canonical (hc (σ (.n 2)) (by simp)) (hc (σ (.n 3)) (by simp))
  obtain ⟨pi, ep⟩ := digest_of_canonical (hc (σ (.n 0)) (by simp)) (hc (σ (.n 1)) (by simp))
  refine ⟨seed, pi, es, ep, ?_⟩
  obtain ⟨-, -, hK⟩ := (keccak_holds_13 (outs := vsRun 12 13) (by simp [vsRun])).mp hk
  have hch := Keccak.keccak_chain (P := [σ (.n 2), σ (.n 3), σ (.n 0), σ (.n 1)]) (S0 := Keccak.zeroState)
    (B := 1)
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
  rw [show [σ (.n 2), σ (.n 3), σ (.n 0), σ (.n 1)] = [(digestHalves seed).1,
    (digestHalves seed).2, (digestHalves pi).1, (digestHalves pi).2] by rw [← es, ← ep],
    Keccak.absorbChunks_seed] at hch
  simp only [capOf]
  rw [← congrFun hch 8, ← congrFun hch 9, ← congrFun hch 10, ← congrFun hch 11, ← congrFun hch 12]
  rfl

/-! ## The announced words -/

/-- The values of the eight announced words. -/
def vsX (i : ℕ) : ℕ := [27, 37, 47, 57, 80, 90, 100, 110].getD i 0

/-- Word `i` read at stream offset `off` into `x`, packed (`fs_next`). -/
def WordAt (rd : Reader) (σ : Val) (off x : ℕ) : Prop :=
  LoadHolds rd (σ (.n 25)) off (σ (.n x)) ∧ FsPackOk σ (.n x) (x + 1) dsObserve

/-- The announced words' perm atom. -/
abbrev vsAtom50 : Atom :=
  .keccak [.n 34, .n 36, .n 44, .n 46, .n 54, .n 56, .n 64, .n 66, .n 20, .n 21, .n 22, .n 23, .n 24]
    (vsRun 67 13) false false

theorem vsReadsT_holds (h : Stmt.HoldsList C rd σ vsReadsT next kret) :
    (∀ i < 8, WordAt rd σ i (vsX i)) ∧
      (∀ i < 6, LoadHolds rd (σ (.n 26)) i (σ (.n (vsX (i + 1))))) ∧ vsAtom50.Holds rd σ ∧ next := by
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
  [σ (.n 27), σ (.n 37), σ (.n 47), σ (.n 57), σ (.n 80), σ (.n 90), σ (.n 100), σ (.n 110)]

/-- A word's two packed cells, once the first is canonical. -/
theorem wordAt_cells {off x : ℕ} (h : WordAt rd σ off x) (hc : IsCanonical128 (σ (.n (x + 7)))) :
    (σ (.n (x + 7)), σ (.n (x + 9))) = Keccak.scalarCells (σ (.n x)) dsObserve :=
  fsPackT_cells h.2 hc

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
theorem vs_absorb8 (hw : ∀ i < 8, WordAt rd σ i (vsX i)) (hk : vsAtom50.Holds rd σ) :
    (⟨[σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)], []⟩ : Fs).absorbAll (vsWords σ)
        dsObserve =
      ⟨[σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)],
        [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
          (σ (.n 110), dsObserve)]⟩ := by
  have hcap := keccak_cap hk
  rw [vsRun_drop8] at hcap
  obtain ⟨-, -, hc, -⟩ := keccakA_perm hk
  have c0 := wordAt_cells (hw 0 (by omega)) (hc (σ (.n 34)) (List.mem_map_of_mem (by simp)))
  have c1 := wordAt_cells (hw 1 (by omega)) (hc (σ (.n 44)) (List.mem_map_of_mem (by simp)))
  have c2 := wordAt_cells (hw 2 (by omega)) (hc (σ (.n 54)) (List.mem_map_of_mem (by simp)))
  have c3 := wordAt_cells (hw 3 (by omega)) (hc (σ (.n 64)) (List.mem_map_of_mem (by simp)))
  simp only [vsX, List.getD_cons_zero, List.getD_cons_succ] at c0 c1 c2 c3
  have e := absorb8_shape [σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)] (σ (.n 27))
    (σ (.n 37)) (σ (.n 47)) (σ (.n 57)) (σ (.n 80)) (σ (.n 90)) (σ (.n 100)) (σ (.n 110))
  have hl : rateOf [(σ (.n 27), dsObserve), (σ (.n 37), dsObserve), (σ (.n 47), dsObserve),
      (σ (.n 57), dsObserve)] ++ [σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)] =
      List.map σ [.n 34, .n 36, .n 44, .n 46, .n 54, .n 56, .n 64, .n 66, .n 20, .n 21, .n 22,
        .n 23, .n 24] := by
    rw [rateOf_four, ← c0, ← c1, ← c2, ← c3]; rfl
  rw [vsWords, e, Fs.perm, hl, ← hcap]

/-! ## The root -/

/-- The root's perm atom: the last four announced words. -/
abbrev vsAtom649 : Atom :=
  .keccak [.n 87, .n 89, .n 97, .n 99, .n 107, .n 109, .n 117, .n 119, .n 75, .n 76, .n 77, .n 78,
    .n 79] (vsRun 311 13) false false

theorem vsRootsT_holds (h : Stmt.HoldsList C rd σ vsRootsT next kret) :
    vsAtom649.Holds rd σ ∧ WordAt rd σ 8 324 ∧ WordAt rd σ 9 334 ∧
      C "assert_canonical" [σ (.n 324)] [σ (.n 344)] ∧
      C "assert_canonical" [σ (.n 334)] [σ (.n 345)] ∧ next := by
  rw [vsRootsT] at h
  simp only [holdsList_append] at h
  obtain ⟨hk, h⟩ := holds_atom1.1 h
  obtain ⟨w8, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨w9, h⟩ := (holds_fsNextT _ _ _ _ _).1 h
  obtain ⟨c1, c2, -, hn⟩ := h
  exact ⟨hk, w8, w9, c1, c2, hn⟩

/-- **The root's words absorbed** after the announced ones: the last four permuted in. -/
theorem vs_absorbRoot (hw : ∀ i < 8, WordAt rd σ i (vsX i)) (hk : vsAtom649.Holds rd σ) :
    (((⟨[σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)],
        [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
          (σ (.n 110), dsObserve)]⟩ : Fs).absorb (σ (.n 324)) dsObserve).absorb (σ (.n 334))
        dsObserve) =
      ⟨[σ (.n 319), σ (.n 320), σ (.n 321), σ (.n 322), σ (.n 323)],
        [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩ := by
  have hcap := keccak_cap hk
  rw [vsRun_drop8] at hcap
  obtain ⟨-, -, hc, -⟩ := keccakA_perm hk
  have c4 := wordAt_cells (hw 4 (by omega)) (hc (σ (.n 87)) (List.mem_map_of_mem (by simp)))
  have c5 := wordAt_cells (hw 5 (by omega)) (hc (σ (.n 97)) (List.mem_map_of_mem (by simp)))
  have c6 := wordAt_cells (hw 6 (by omega)) (hc (σ (.n 107)) (List.mem_map_of_mem (by simp)))
  have c7 := wordAt_cells (hw 7 (by omega)) (hc (σ (.n 117)) (List.mem_map_of_mem (by simp)))
  simp only [vsX, List.getD_cons_zero, List.getD_cons_succ] at c4 c5 c6 c7
  have e := absorb2_shape [σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)] (σ (.n 80))
    (σ (.n 90)) (σ (.n 100)) (σ (.n 110)) (σ (.n 324)) (σ (.n 334))
  have hl : rateOf [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
      (σ (.n 110), dsObserve)] ++ [σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)] =
      List.map σ [.n 87, .n 89, .n 97, .n 99, .n 107, .n 109, .n 117, .n 119, .n 75, .n 76, .n 77,
        .n 78, .n 79] := by
    rw [rateOf_four, ← c4, ← c5, ← c6, ← c7]; rfl
  rw [e, Fs.perm, hl, ← hcap]

/-! ## Squeezes -/

/-- **A squeeze with nothing waiting** (`vsSqzT`), on the zero cells. -/
theorem vsSqzT_holds {capb o : ℕ} (h10 : σ (.n 8) = 0) (h11 : σ (.n 9) = 0)
    (h12 : σ (.n 10) = 0) (h13 : σ (.n 11) = 0)
    (h : Stmt.HoldsList C rd σ (vsSqzT capb o) next kret) :
    (⟨(vsRun capb 5).map σ, []⟩ : Fs).squeeze =
        (σ (.n (o + 19)), ⟨[σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)),
          σ (.n (o + 12))], []⟩) ∧ next := by
  simp only [vsSqzT, Stmt.HoldsList, Stmt.Holds, keccakA] at h
  obtain ⟨hk, h⟩ := h
  obtain ⟨hch, hn⟩ := (holds_challengeT _ _ _ _ _).1 h
  have hs := squeeze_atom (s := ⟨(vsRun capb 5).map σ, []⟩) (b := o + 13) hk
    (by simp only [List.map_append, List.map_cons, List.map_nil, h10, h11, h12, h13, rateOf_nil])
    hch
  rw [vsRun_drop8] at hs
  obtain ⟨e1, e2⟩ := hs
  simp only [Fs.squeeze] at e1 e2 ⊢
  rw [← e1, ← e2]
  exact ⟨rfl, hn⟩

/-- The second root word's perm atom: the root waiting, the bus's first challenge. -/
abbrev vsAtom671 : Atom :=
  .keccak [.n 331, .n 333, .n 341, .n 343, .n 8, .n 9, .n 10, .n 11, .n 319, .n 320, .n 321,
    .n 322, .n 323] (vsRun 347 13) false false

/-- **The four bus challenges** (G:3226-3232). -/
theorem vsAlphasT_holds (h10 : σ (.n 8) = 0) (h11 : σ (.n 9) = 0) (h12 : σ (.n 10) = 0)
    (h13 : σ (.n 11) = 0) (w8 : WordAt rd σ 8 324) (w9 : WordAt rd σ 9 334)
    (h : Stmt.HoldsList C rd σ vsAlphasT next kret) :
    (⟨[σ (.n 319), σ (.n 320), σ (.n 321), σ (.n 322), σ (.n 323)],
        [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩ : Fs).squeezeN 4 =
      ([σ (.n 366), σ (.n 386), σ (.n 406), σ (.n 426)],
        ⟨[σ (.n 415), σ (.n 416), σ (.n 417), σ (.n 418), σ (.n 419)], []⟩) ∧
      ReadsAt rd (σ (.n 346)) [σ (.n 366), σ (.n 386), σ (.n 406), σ (.n 426)] ∧ next := by
  simp only [vsAlphasT, holdsList_append, Stmt.HoldsList, Stmt.Holds, vsLd] at h
  obtain ⟨hk, h⟩ := h
  obtain ⟨hch, l0, h⟩ := (holds_challengeT _ _ _ _ _).1 h
  obtain ⟨s1, l1, h⟩ := vsSqzT_holds h10 h11 h12 h13 h
  obtain ⟨s2, l2, h⟩ := vsSqzT_holds h10 h11 h12 h13 h
  obtain ⟨s3, l3, hn⟩ := vsSqzT_holds h10 h11 h12 h13 h
  obtain ⟨-, -, hc, -⟩ := keccakA_perm hk
  have c8 := wordAt_cells w8 (hc (σ (.n 331)) (List.mem_map_of_mem (by simp)))
  have c9 := wordAt_cells w9 (hc (σ (.n 341)) (List.mem_map_of_mem (by simp)))
  have hs := squeeze_atom (s := ⟨[σ (.n 319), σ (.n 320), σ (.n 321), σ (.n 322), σ (.n 323)],
    [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩) (b := 360) hk
    (by simp only [List.map_cons, List.map_nil, h10, h11, h12, h13, rateOf_two, ← c8, ← c9]; rfl)
    hch
  rw [vsRun_drop8] at hs
  refine ⟨?_, fun k hk ↦ ?_, hn⟩
  · have e0 : (⟨[σ (.n 319), σ (.n 320), σ (.n 321), σ (.n 322), σ (.n 323)],
        [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩ : Fs).squeeze =
        (σ (.n 366), ⟨[σ (.n 355), σ (.n 356), σ (.n 357), σ (.n 358), σ (.n 359)], []⟩) :=
      Prod.ext hs.1.symm (congrArg (Fs.mk · []) hs.2.symm)
    have e1 : (⟨[σ (.n 355), σ (.n 356), σ (.n 357), σ (.n 358), σ (.n 359)], []⟩ : Fs).squeeze =
        (σ (.n 386), ⟨[σ (.n 375), σ (.n 376), σ (.n 377), σ (.n 378), σ (.n 379)], []⟩) := s1
    have e2 : (⟨[σ (.n 375), σ (.n 376), σ (.n 377), σ (.n 378), σ (.n 379)], []⟩ : Fs).squeeze =
        (σ (.n 406), ⟨[σ (.n 395), σ (.n 396), σ (.n 397), σ (.n 398), σ (.n 399)], []⟩) := s2
    have e3 : (⟨[σ (.n 395), σ (.n 396), σ (.n 397), σ (.n 398), σ (.n 399)], []⟩ : Fs).squeeze =
        (σ (.n 426), ⟨[σ (.n 415), σ (.n 416), σ (.n 417), σ (.n 418), σ (.n 419)], []⟩) := s3
    simp only [Fs.squeezeN, e0, e1, e2, e3]
  · simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3

end
end LeanVM.Guest.B1.VerifySub
