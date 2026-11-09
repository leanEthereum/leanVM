/-
  LeanVM.Guest.B1.VerifySub.H.Sponge

  `verify_sub`'s sponge on its honest valuation: the seed's capacity, the announced words and the
  root absorbed, every squeeze's challenge, from the evaluation alone (no store).
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Body
public import LeanVM.Guest.B1.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.Tail
public import LeanVM.Guest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.VerifySub.Back

/-!
# The sponge, honestly

The honest valuation `vsσ rd w args` carries the Spec's sponge as the soundness proof reads it
(`Front.lean`, `Tail.lean`), with no store of `verify_sub` involved: the stores only check what the
evaluation computed. So the challenges are known before the memory's own buffers are.

* `vs_zero`: the zero cells `8 .. 11`;
* `vs_kecOut`: a `KECCAK` atom's outputs are canonical;
* `vs_sqz`: a squeeze (`vsSqzT`) on canonical capacity cells: its challenge and capacity;
* `vsH_front`: from the stream's first ten words in memory, the seed's capacity, the announced
  words and the root absorbed, the four bus challenges, `β` (`VsFrontS`);
* `vsH_maps`: the ring map's five squeezed challenges; `vsH_lam`: the batching challenge.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
/-- **The zero cells.** -/
theorem vs_zero (hl : args.length = 6) : ∀ i ∈ [8, 9, 10, 11], vsσ rd w args (.n i) = 0 := by
  intro i hi
  have hmc : ∀ i ∈ [8, 9, 10, 11], vsConst i (word 0 0 0) ∈ vsCPre := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact vs_mem_slice (n := 2) (blk := [_]) (by decide +kernel) List.mem_cons_self
    · exact vs_mem_slice (n := 3) (blk := [_]) (by decide +kernel) List.mem_cons_self
    · exact vs_mem_slice (n := 4) (blk := [_]) (by decide +kernel) List.mem_cons_self
    · exact vs_mem_slice (n := 5) (blk := [_]) (by decide +kernel) List.mem_cons_self
  have h := vs_goodS (rd := rd) (w := w) hl (hmc i hi)
  simp only [vsConst, fixNe, GoodS, Good] at h
  rw [h, word_zero]

set_option maxRecDepth 100000 in
/-- **A `KECCAK` atom's outputs are canonical.** -/
theorem vs_kecOut (hl : args.length = 6) {ins : List V} {o : ℕ}
    (hm : keccakA ins (vsRun o 13) ∈ vsCPre) :
    ∀ k < 13, IsCanonical128 (vsσ rd w args (.n (o + k))) := by
  have hg := vs_goodS (rd := rd) (w := w) hl hm
  rw [fixNe_of_noNe (s := keccakA ins (vsRun o 13)) (by simp [keccakA, noNeB])] at hg
  simp only [keccakA, GoodS] at hg
  intro k hk13
  have := (good_keccak13 hg (by simp [vsRun])).2.2 ⟨k, hk13⟩
  simp [cells13, vsRun, List.getD_eq_getElem?_getD, hk13] at this
  rw [this]
  exact canon_cellsOfState _ _ _

/-- **A `KECCAK` atom on canonical inputs holds.** -/
theorem vs_kecHolds (hl : args.length = 6) {ins : List V} {o : ℕ}
    (hm : keccakA ins (vsRun o 13) ∈ vsCPre) (hc : AllCanonical (ins.map (vsσ rd w args))) :
    (Atom.keccak ins (vsRun o 13) false false).Holds rd (vsσ rd w args) := by
  have hg := vs_goodS (rd := rd) (w := w) hl hm
  rw [fixNe_of_noNe (s := keccakA ins (vsRun o 13)) (by simp [keccakA, noNeB])] at hg
  exact keccakA_complete (S := vsSL) (w := w) hg hc

/-- A squeeze's inputs: the zero cells and a canonical capacity. -/
theorem vs_sqzIn (hl : args.length = 6) {capb : ℕ}
    (hc : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (capb + i)))) :
    AllCanonical (([V.n 8, V.n 8, V.n 8, V.n 8, V.n 8, V.n 9, V.n 10, V.n 11] ++
      vsRun capb 5).map (vsσ rd w args)) := by
  have hz := vs_zero (rd := rd) (w := w) hl
  have hz' : ∀ i ∈ [8, 9, 10, 11], IsCanonical128 (vsσ rd w args (.n i)) :=
    fun i hi ↦ by rw [hz i hi]; exact canonical_zero
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
  simp only [vsRun, List.cons_append, List.nil_append, List.mem_cons, List.mem_map,
    List.mem_range] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩
  · exact hz' 8 (by simp)
  · exact hz' 8 (by simp)
  · exact hz' 8 (by simp)
  · exact hz' 8 (by simp)
  · exact hz' 8 (by simp)
  · exact hz' 9 (by simp)
  · exact hz' 10 (by simp)
  · exact hz' 11 (by simp)
  · exact hc i hi

/-- **A squeeze, honestly**: on canonical capacity cells, its challenge and capacity, its outputs
canonical. -/
theorem vs_sqz (hl : args.length = 6) {capb o : ℕ} (hmem : ∀ s ∈ vsSqzT capb o, s ∈ vsCPre)
    (hc : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (capb + i)))) :
    (⟨(vsRun capb 5).map (vsσ rd w args), []⟩ : Fs).squeeze =
        (vsσ rd w args (.n (o + 19)), ⟨[vsσ rd w args (.n (o + 8)), vsσ rd w args (.n (o + 9)),
          vsσ rd w args (.n (o + 10)), vsσ rd w args (.n (o + 11)), vsσ rd w args (.n (o + 12))],
          []⟩) ∧ ∀ k < 13, IsCanonical128 (vsσ rd w args (.n (o + k))) := by
  have hz := vs_zero (rd := rd) (w := w) hl
  have h := vsSqzT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl hmem
    hz hc trivial
  refine ⟨(vsSqzT_holds (hz 8 (by simp)) (hz 9 (by simp)) (hz 10 (by simp)) (hz 11 (by simp))
    h).1, ?_⟩
  exact (kc_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True) hl hmem
    (vs_sqzIn hl hc) trivial).1

/-! ## The front -/

/-- **What the honest valuation's front computes**, the stream's first ten words `ws` in memory. -/
structure VsFrontS (rd : Reader) (σ : Val) (ws : List E) : Prop where
  hz : ∀ i ∈ [8, 9, 10, 11], σ (.n i) = 0
  hseed : vsSeedAtom.Holds rd σ
  hcap22 : ∀ i ∈ [20, 21, 22, 23, 24], IsCanonical128 (σ (.n i))
  hx : ∀ i < 8, σ (.n (vsX i)) = ws.getD i 0
  hw : ∀ i < 8, WordAt rd σ i (vsX i)
  e537 : σ (.n 324) = ws.getD 8 0
  e547 : σ (.n 334) = ws.getD 9 0
  hin : ∀ i ∈ [87, 89, 97, 99, 107, 109, 117, 119, 75, 76, 77, 78, 79],
    IsCanonical128 (σ (.n i))
  hc532 : ∀ i < 5, IsCanonical128 (σ (.n (319 + i)))
  hc628 : ∀ i < 5, IsCanonical128 (σ (.n (415 + i)))
  hab8 : (⟨[σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)], []⟩ : Fs).absorbAll
      (vsWords σ) dsObserve =
    ⟨[σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)],
      [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
        (σ (.n 110), dsObserve)]⟩
  habR : (((⟨[σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)],
      [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
        (σ (.n 110), dsObserve)]⟩ : Fs).absorb (σ (.n 324)) dsObserve).absorb (σ (.n 334))
      dsObserve) =
    ⟨[σ (.n 319), σ (.n 320), σ (.n 321), σ (.n 322), σ (.n 323)],
      [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩
  halpha : (⟨[σ (.n 319), σ (.n 320), σ (.n 321), σ (.n 322), σ (.n 323)],
      [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩ : Fs).squeezeN 4 =
    (vsAlphas σ, ⟨[σ (.n 415), σ (.n 416), σ (.n 417), σ (.n 418), σ (.n 419)], []⟩)
  hbeta : (⟨[σ (.n 415), σ (.n 416), σ (.n 417), σ (.n 418), σ (.n 419)], []⟩ : Fs).squeeze =
    (σ (.n 623), ⟨[σ (.n 612), σ (.n 613), σ (.n 614), σ (.n 615), σ (.n 616)], []⟩)
  hc825 : ∀ i < 5, IsCanonical128 (σ (.n (612 + i)))

set_option maxRecDepth 100000 in
/-- **The front, honestly**: with the statement's and the seed's cells canonical and the stream's
first ten words in memory. -/
theorem vsH_front (hl : args.length = 6) (hc4 : ∀ i < 4, IsCanonical128 (args.getD i 0))
    {ws : List E} (hws : ∀ i < 10, LoadHolds rd (vsσ rd w args (.n 25)) i (ws.getD i 0)) :
    VsFrontS rd (vsσ rd w args) ws := by
  have hz := vs_zero (rd := rd) (w := w) hl
  -- the seed
  have hseed : vsSeedAtom.Holds rd (vsσ rd w args) := by
    have h := vsHeadT_complete (rd := rd) (w := w) hl hc4 (keccakA [.n 2, .n 3, .n 0, .n 1, .n 8,
      .n 9, .n 10, .n 11, .n 8, .n 8, .n 9, .n 10, .n 11] (vsRun 12 13)) (by simp [vsHeadT])
    exact h
  have hc14 := vs_kecOut (rd := rd) (w := w) hl (ins := [.n 2, .n 3, .n 0, .n 1, .n 8, .n 9,
    .n 10, .n 11, .n 8, .n 8, .n 9, .n 10, .n 11]) (o := 12)
    (vs_mem_slice (n := 6) (blk := [_]) (by decide +kernel) List.mem_cons_self)
  have hcap22 : ∀ i ∈ [20, 21, 22, 23, 24], IsCanonical128 (vsσ rd w args (.n i)) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact hc14 8 (by norm_num)
    · exact hc14 9 (by norm_num)
    · exact hc14 10 (by norm_num)
    · exact hc14 11 (by norm_num)
    · exact hc14 12 (by norm_num)
  -- the announced words
  have hws8 : ∀ i < 8, LoadHolds rd (vsσ rd w args (.n 25)) i (ws.getD i 0) :=
    fun i hi ↦ hws i (by omega)
  have W := fun i (hi : i < 8) ↦ vs_word (rd := rd) (w := w) hl hws8 hi
  have hx : ∀ i < 8, vsσ rd w args (.n (vsX i)) = ws.getD i 0 := fun i hi ↦ (W i hi).1
  have hw : ∀ i < 8, WordAt rd (vsσ rd w args) i (vsX i) := fun i hi ↦
    ((holds_fsNextT (C := fun _ _ _ ↦ True) _ _ _ True (fun _ ↦ True)).1
      ((W i hi).2.2.2 trivial)).1
  have mR : ∀ s ∈ vsReadsT, s ∈ vsCPre :=
    fun s hs ↦ vs_mem_slice (n := 10) (blk := vsReadsT) (by decide +kernel) hs
  have m50 : keccakA [.n 34, .n 36, .n 44, .n 46, .n 54, .n 56, .n 64, .n 66, .n 20, .n 21, .n 22,
      .n 23, .n 24] (vsRun 67 13) ∈ vsCPre := mR _ (by
    simp only [vsReadsT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto)
  have hc69 := vs_kecOut (rd := rd) (w := w) hl m50
  have hk50 : vsAtom50.Holds rd (vsσ rd w args) := by
    refine vs_kecHolds hl m50 ?_
    intro x hx'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (W 0 (by norm_num)).2.1
    · exact (W 0 (by norm_num)).2.2.1
    · exact (W 1 (by norm_num)).2.1
    · exact (W 1 (by norm_num)).2.2.1
    · exact (W 2 (by norm_num)).2.1
    · exact (W 2 (by norm_num)).2.2.1
    · exact (W 3 (by norm_num)).2.1
    · exact (W 3 (by norm_num)).2.2.1
    · exact hcap22 20 (by simp)
    · exact hcap22 21 (by simp)
    · exact hcap22 22 (by simp)
    · exact hcap22 23 (by simp)
    · exact hcap22 24 (by simp)
  have hin : ∀ i ∈ [87, 89, 97, 99, 107, 109, 117, 119, 75, 76, 77, 78, 79],
      IsCanonical128 (vsσ rd w args (.n i)) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (W 4 (by norm_num)).2.1
    · exact (W 4 (by norm_num)).2.2.1
    · exact (W 5 (by norm_num)).2.1
    · exact (W 5 (by norm_num)).2.2.1
    · exact (W 6 (by norm_num)).2.1
    · exact (W 6 (by norm_num)).2.2.1
    · exact (W 7 (by norm_num)).2.1
    · exact (W 7 (by norm_num)).2.2.1
    · exact hc69 8 (by norm_num)
    · exact hc69 9 (by norm_num)
    · exact hc69 10 (by norm_num)
    · exact hc69 11 (by norm_num)
    · exact hc69 12 (by norm_num)
  -- the root
  have hRo := vsRootsT_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True)
    (rd := rd) (w := w) hl hin (hws 8 (by norm_num)) (hws 9 (by norm_num)) trivial trivial trivial
  obtain ⟨e537, e547, hcR, hRoH⟩ := hRo
  obtain ⟨hk649, w8, w9, -, -, -⟩ := vsRootsT_holds hRoH
  have mRo : ∀ s ∈ vsRootsT, s ∈ vsCPre :=
    fun s hs ↦ vs_mem_slice (n := 284) (blk := vsRootsT) (by decide +kernel) hs
  have hc524 := vs_kecOut (rd := rd) (w := w) hl (ins := [V.n 87, V.n 89, V.n 97, V.n 99, V.n 107,
    V.n 109, V.n 117, V.n 119, V.n 75, V.n 76, V.n 77, V.n 78, V.n 79]) (o := 311)
    (mRo _ (by simp [vsRootsT]))
  have hc532 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (319 + i))) := fun i hi ↦ by
    have := hc524 (8 + i) (by omega); rwa [← Nat.add_assoc] at this
  -- the bus challenges
  have mA : ∀ s ∈ vsAlphasT, s ∈ vsCPre :=
    fun s hs ↦ vs_mem_slice (n := 306) (blk := vsAlphasT) (by decide +kernel) hs
  have hc1 : AllCanonical ([V.n 331, V.n 333, V.n 341, V.n 343, V.n 8, V.n 9, V.n 10, V.n 11,
      V.n 319, V.n 320, V.n 321, V.n 322, V.n 323].map (vsσ rd w args)) := by
    have hz' : ∀ i ∈ [8, 9, 10, 11], IsCanonical128 (vsσ rd w args (.n i)) :=
      fun i hi ↦ by rw [hz i hi]; exact canonical_zero
    intro x hx'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcR 331 (by simp)
    · exact hcR 333 (by simp)
    · exact hcR 341 (by simp)
    · exact hcR 343 (by simp)
    · exact hz' 8 (by simp)
    · exact hz' 9 (by simp)
    · exact hz' 10 (by simp)
    · exact hz' 11 (by simp)
    · exact hc532 0 (by norm_num)
    · exact hc532 1 (by norm_num)
    · exact hc532 2 (by norm_num)
    · exact hc532 3 (by norm_num)
    · exact hc532 4 (by norm_num)
  obtain ⟨o1, h1⟩ := kc_complete (C := fun _ _ _ ↦ True) (next := True) (kret := fun _ ↦ True)
    (rd := rd) (w := w) hl (ins := [V.n 331, V.n 333, V.n 341, V.n 343, V.n 8, V.n 9, V.n 10,
      V.n 11, V.n 319, V.n 320, V.n 321, V.n 322, V.n 323]) (o := 347)
    (fun s hs ↦ mA s (by rw [vsAlphasT]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hs)))))))) hc1 trivial
  simp only [Stmt.HoldsList, Stmt.Holds, keccakA] at h1
  obtain ⟨hk1, hch1⟩ := h1
  have hch1' := ((holds_challengeT (C := fun _ _ _ ↦ True) _ _ _ True (fun _ ↦ True)).1 hch1).1
  have c8 := wordAt_cells w8 (hcR 331 (by simp))
  have c9 := wordAt_cells w9 (hcR 341 (by simp))
  have hs := squeeze_atom (s := ⟨[vsσ rd w args (.n 319), vsσ rd w args (.n 320),
    vsσ rd w args (.n 321), vsσ rd w args (.n 322), vsσ rd w args (.n 323)],
    [(vsσ rd w args (.n 324), dsObserve), (vsσ rd w args (.n 334), dsObserve)]⟩) (b := 360) hk1
    (by simp only [List.map_cons, List.map_nil, hz 8 (by simp), hz 9 (by simp),
      hz 10 (by simp), hz 11 (by simp), rateOf_two, ← c8, ← c9]; rfl) hch1'
  rw [vsRun_drop8] at hs
  have sub : ∀ capb o, vsSqzT capb o ⊆ vsAlphasT → ∀ s ∈ vsSqzT capb o, s ∈ vsCPre :=
    fun capb o hsub s hs ↦ mA s (hsub hs)
  have q1 := vs_sqz (rd := rd) (w := w) hl (capb := 355) (o := 367)
    (sub _ _ (by intro s hs; rw [vsAlphasT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))))))
    (fun i hi ↦ by have := o1 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q2 := vs_sqz (rd := rd) (w := w) hl (capb := 375) (o := 387)
    (sub _ _ (by intro s hs; rw [vsAlphasT]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))))
    (fun i hi ↦ by have := q1.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q3 := vs_sqz (rd := rd) (w := w) hl (capb := 395) (o := 407)
    (sub _ _ (by intro s hs; rw [vsAlphasT]; exact List.mem_append_left _ (List.mem_append_right _ hs)))
    (fun i hi ↦ by have := q2.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have hc628 : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (415 + i))) := fun i hi ↦ by
    have := q3.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this
  -- `β`
  have qb := vs_sqz (rd := rd) (w := w) hl (capb := 415) (o := 604)
    (fun s hs ↦ vs_mem_slice (n := 346) (blk := vsFpwT) (by decide +kernel)
      (by rw [vsFpwT]; exact List.mem_append_right _ hs)) hc628
  refine ⟨hz, hseed, hcap22, hx, hw, by rw [e537], by rw [e547], hin, hc532, hc628,
    vs_absorb8 hw hk50, vs_absorbRoot hw hk649, ?_, qb.1, fun i hi ↦ by
      have := qb.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this⟩
  generalize vsσ rd w args = σ at hs q1 q2 q3 ⊢
  have e0 : (⟨[σ (.n 319), σ (.n 320), σ (.n 321),
      σ (.n 322), σ (.n 323)],
      [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩ : Fs).squeeze =
      (σ (.n 366), ⟨[σ (.n 355), σ (.n 356),
        σ (.n 357), σ (.n 358), σ (.n 359)], []⟩) :=
    Prod.ext hs.1.symm (congrArg (Fs.mk · []) hs.2.symm)
  have e1 : (⟨[σ (.n 355), σ (.n 356), σ (.n 357),
      σ (.n 358), σ (.n 359)], []⟩ : Fs).squeeze =
      (σ (.n 386), ⟨[σ (.n 375), σ (.n 376),
        σ (.n 377), σ (.n 378), σ (.n 379)], []⟩) := q1.1
  have e2 : (⟨[σ (.n 375), σ (.n 376), σ (.n 377),
      σ (.n 378), σ (.n 379)], []⟩ : Fs).squeeze =
      (σ (.n 406), ⟨[σ (.n 395), σ (.n 396),
        σ (.n 397), σ (.n 398), σ (.n 399)], []⟩) := q2.1
  have e3 : (⟨[σ (.n 395), σ (.n 396), σ (.n 397),
      σ (.n 398), σ (.n 399)], []⟩ : Fs).squeeze =
      (σ (.n 426), ⟨[σ (.n 415), σ (.n 416),
        σ (.n 417), σ (.n 418), σ (.n 419)], []⟩) := q3.1
  simp only [Fs.squeezeN, vsAlphas, e0, e1, e2, e3]

/-! ## The ring map and the batching -/

theorem vsMaps_sub (capb o : ℕ)
    (h : (capb, o) ∈ [(659, 666), (674, 686), (694, 706), (714, 726), (734, 746)]) :
    ∀ s ∈ vsSqzT capb o, s ∈ vsCPre := by
  intro s hs
  refine vs_mem_slice (n := 564) (blk := vsMapsT) (by decide +kernel) ?_
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rw [vsMapsT]
  simp only [List.mem_append]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

set_option maxRecDepth 100000 in
/-- **The ring map's five squeezed challenges, honestly**, from canonical capacity cells. -/
theorem vsH_maps (hl : args.length = 6)
    (hc : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (659 + i)))) :
    (⟨[vsσ rd w args (.n 659), vsσ rd w args (.n 660), vsσ rd w args (.n 661),
        vsσ rd w args (.n 662), vsσ rd w args (.n 663)], []⟩ : Fs).squeezeN 5 =
      (vsChs (vsσ rd w args), ⟨[vsσ rd w args (.n 754), vsσ rd w args (.n 755),
        vsσ rd w args (.n 756), vsσ rd w args (.n 757), vsσ rd w args (.n 758)], []⟩) ∧
      ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (754 + i))) := by
  have q1 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 659 666 (by simp)) hc
  have q2 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 674 686 (by simp))
    (fun i hi ↦ by have := q1.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q3 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 694 706 (by simp))
    (fun i hi ↦ by have := q2.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q4 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 714 726 (by simp))
    (fun i hi ↦ by have := q3.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  have q5 := vs_sqz (rd := rd) (w := w) hl (vsMaps_sub 734 746 (by simp))
    (fun i hi ↦ by have := q4.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
  generalize vsσ rd w args = σ at q1 q2 q3 q4 q5 ⊢
  have e1 : (⟨[σ (.n 659), σ (.n 660), σ (.n 661), σ (.n 662), σ (.n 663)], []⟩ : Fs).squeeze =
      (σ (.n 685), ⟨[σ (.n 674), σ (.n 675), σ (.n 676), σ (.n 677), σ (.n 678)], []⟩) := q1.1
  have e2 : (⟨[σ (.n 674), σ (.n 675), σ (.n 676), σ (.n 677), σ (.n 678)], []⟩ : Fs).squeeze =
      (σ (.n 705), ⟨[σ (.n 694), σ (.n 695), σ (.n 696), σ (.n 697), σ (.n 698)], []⟩) := q2.1
  have e3 : (⟨[σ (.n 694), σ (.n 695), σ (.n 696), σ (.n 697), σ (.n 698)], []⟩ : Fs).squeeze =
      (σ (.n 725), ⟨[σ (.n 714), σ (.n 715), σ (.n 716), σ (.n 717), σ (.n 718)], []⟩) := q3.1
  have e4 : (⟨[σ (.n 714), σ (.n 715), σ (.n 716), σ (.n 717), σ (.n 718)], []⟩ : Fs).squeeze =
      (σ (.n 745), ⟨[σ (.n 734), σ (.n 735), σ (.n 736), σ (.n 737), σ (.n 738)], []⟩) := q4.1
  have e5 : (⟨[σ (.n 734), σ (.n 735), σ (.n 736), σ (.n 737), σ (.n 738)], []⟩ : Fs).squeeze =
      (σ (.n 765), ⟨[σ (.n 754), σ (.n 755), σ (.n 756), σ (.n 757), σ (.n 758)], []⟩) := q5.1
  refine ⟨by simp only [Fs.squeezeN, vsChs, e1, e2, e3, e4, e5], fun i hi ↦ ?_⟩
  have := q5.2 (8 + i) (by omega); rwa [← Nat.add_assoc] at this

/-- **The batching challenge, honestly**, from canonical capacity cells. -/
theorem vsH_lam (hl : args.length = 6)
    (hc : ∀ i < 5, IsCanonical128 (vsσ rd w args (.n (754 + i)))) :
    (⟨[vsσ rd w args (.n 754), vsσ rd w args (.n 755), vsσ rd w args (.n 756),
        vsσ rd w args (.n 757), vsσ rd w args (.n 758)], []⟩ : Fs).squeeze =
      (vsσ rd w args (.n 1111), ⟨[vsσ rd w args (.n 1100), vsσ rd w args (.n 1101),
        vsσ rd w args (.n 1102), vsσ rd w args (.n 1103), vsσ rd w args (.n 1104)], []⟩) := by
  have q := vs_sqz (rd := rd) (w := w) hl (capb := 754) (o := 1092)
    (fun s hs ↦ vs_mem_slice (n := 1007) (blk := vsLamT) (by decide +kernel)
      (by rw [vsLamT]; simp only [List.mem_append]; tauto)) hc
  generalize vsσ rd w args = σ at q ⊢
  exact q.1

end
end LeanVM.Guest.B1.VerifySub
