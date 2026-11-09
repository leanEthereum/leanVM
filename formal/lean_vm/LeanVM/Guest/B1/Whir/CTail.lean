/-
  LeanVM.Guest.B1.Whir.CTail

  The tail rounds, honestly: the rounds, the closing squeeze on the two waiting scalars, the
  final claim, the unused challenge slots zeroed.
-/

module

public import LeanVM.Guest.B1.Whir.CLevels
public import LeanVM.Guest.B1.Whir.Tail

/-!
# The tail rounds, honestly

`osTailEnd_complete`: after the rounds, the capacity copied, the two waiting scalars packed, the
permutation, its challenge (stored at `tail_challenges[yrLog - 1]`), the claim the quadratic at it
and the slots past the challenges zero, at the values `tailEndSegs`. `osTail_complete`: the
buffer allocated at `T`, the rounds (`osFolds_complete`) then the end.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The tail's statements after its rounds, from the rounds' state `f2`, the buffer `tch` and the
zero run at `p`. -/
def tailEnd (c : OsCfg) (tch : ℕ) (f2 : OsSt) (p : ℕ) : List Stmt :=
  let j := f2.k
  (f2.fs.zipIdx.map fun (x, i) ↦ .atom (.copy (.n (j + i)) (.n x))) ++
    fsPackT (.n f2.w0) (j + 5) 1 ++ fsPackT (.n f2.w1) (j + 14) 1 ++
    keccakA ([j + 11, j + 13, j + 20, j + 22, p + 1, p + 2, p + 3, p + 4, j, j + 1, j + 2, j + 3,
      j + 4].map V.n) (osRun (j + 23) 13) ::
    challengeT (.n (j + 23)) (.n (j + 24)) (j + 36) ++
    [.atom (.load (.n (j + 42)) (.n tch) (c.yrLog - 1)),
      .atom (.mul (.n (j + 43)) (.n (j + 42)) (.n f2.b)), .atom (.add (.n (j + 44)) (.n f2.c) (.n (j + 43))),
      .atom (.mul (.n (j + 45)) (.n (j + 42)) (.n (j + 42))),
      .atom (.mul (.n (j + 46)) (.n (j + 45)) (.n f2.a)),
      .atom (.add (.n (j + 47)) (.n (j + 44)) (.n (j + 46)))] ++
    ((List.range (yrLogCap - c.yrLog)).map fun i ↦
      [.atom (.const (.n (j + 48 + i)) (word 0 0 0)),
        .atom (.load (.n (j + 48 + i)) (.n tch) (c.yrLog + i))]).flatten

theorem osTail_eq (c : OsCfg) (st : OsSt) :
    osTail c st = (osHeap yrLogCap st.k ++ (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).1 ++
      tailEnd c (st.k + 1) (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2
        ((osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2.pad.getD 0),
      { (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2 with
        k := (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2.k + 48 +
          (yrLogCap - c.yrLog)
        t := (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2.k + 47 },
      st.k + 1) := by
  simp only [osTail, tailEnd, List.append_assoc, List.cons_append]

/-- The values of the tail's end from its first value. -/
def tailEndSegs (c : OsCfg) (σ : Val) (f2 : OsSt) : List (ℕ × (ℕ → E)) :=
  [(5, fun i ↦ (f2.fsv σ).getD i 0), (9, fsPackVals (σ (.n f2.w0)) 1),
    (9, fsPackVals (σ (.n f2.w1)) 1), (13, cells13F (f2.F σ).perm),
    (7, challengeVals (cells13F (f2.F σ).perm 0) (cells13F (f2.F σ).perm 1)),
    (5, fun i ↦ [challengeOf (f2.F σ).perm * σ (.n f2.b),
      σ (.n f2.c) + challengeOf (f2.F σ).perm * σ (.n f2.b),
      challengeOf (f2.F σ).perm * challengeOf (f2.F σ).perm,
      challengeOf (f2.F σ).perm * challengeOf (f2.F σ).perm * σ (.n f2.a),
      σ (.n f2.c) + challengeOf (f2.F σ).perm * σ (.n f2.b) +
        challengeOf (f2.F σ).perm * challengeOf (f2.F σ).perm * σ (.n f2.a)].getD i 0),
    (yrLogCap - c.yrLog, fun _ ↦ 0)]

/-- **The tail's end, honestly.** -/
theorem osTailEnd_complete {c : OsCfg} {tch : ℕ} {f2 : OsSt} {p : ℕ} (σ : Val)
    (hfs : f2.fs.length = 5) (hb : f2.Below) (htch : tch < f2.k) (hp4 : p + 4 < f2.k)
    (hz : PadOk σ (some p)) (hcan : AllCanonical (f2.fsv σ))
    (hlast : LoadHolds rd (σ (.n tch)) (c.yrLog - 1) (f2.F σ).squeeze.1)
    (hzero : ∀ i < yrLogCap - c.yrLog, LoadHolds rd (σ (.n tch)) (c.yrLog + i) 0) :
    BlkF C rd σ f2.k (f2.k + 48 + (yrLogCap - c.yrLog))
      (fun i ↦ segLookup (tailEndSegs c σ f2) (i - f2.k)) (tailEnd c tch f2 p)
      (fun σ' ↦ σ' (.n (f2.k + 47)) = polyEval (f2.quad σ) (f2.F σ).squeeze.1 ∧
        AgreeBelow f2.k σ σ') := by
  obtain ⟨g0, g1, g2, g3, g4, hg⟩ := fold_args f2 hfs
  set segs := tailEndSegs c σ f2 with hsegs
  have hlen : segLen segs = 48 + (yrLogCap - c.yrLog) := by
    simp only [hsegs, tailEndSegs, segLen, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  intro σ' ha hv
  have HV : ∀ j < segLen segs, σ' (.n (f2.k + j)) = segLookup segs j := fun j hj ↦ by
    rw [hv _ (by omega) (by omega)]
    show segLookup segs (f2.k + j - f2.k) = _
    rw [Nat.add_sub_cancel_left]
  have seg := seg_val HV
  set k := f2.k with hkdef
  have hfl : ∀ f ∈ f2.fs, f < k := hb.fs
  rw [hg] at hfl
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hfl
  set S := (f2.F σ).perm with hS
  set ch := challengeOf S with hch
  have L7 : segs.length = 7 := by simp [hsegs, tailEndSegs]
  have vcp : ∀ i < 5, σ' (.n (k + i)) = (f2.fsv σ).getD i 0 := fun i hi ↦ by
    have := seg 0 (by omega) 0 (by simp [hsegs, segLen]) i (by simp [hsegs, tailEndSegs]; omega)
    simpa [hsegs, tailEndSegs] using this
  have vp0 : ∀ i < 9, σ' (.n (k + 5 + i)) = fsPackVals (σ (.n f2.w0)) 1 i := fun i hi ↦ by
    have := seg 1 (by omega) 5 (by simp [hsegs, segLen, tailEndSegs]) i
      (by simp [hsegs, tailEndSegs]; omega)
    simpa [hsegs, tailEndSegs] using this
  have vp1 : ∀ i < 9, σ' (.n (k + 14 + i)) = fsPackVals (σ (.n f2.w1)) 1 i := fun i hi ↦ by
    have := seg 2 (by omega) 14 (by simp [hsegs, segLen, tailEndSegs]) i
      (by simp [hsegs, tailEndSegs]; omega)
    simpa [hsegs, tailEndSegs] using this
  have vout : ∀ i < 13, σ' (.n (k + 23 + i)) = cells13F S i := fun i hi ↦ by
    have := seg 3 (by omega) 23 (by simp [hsegs, segLen, tailEndSegs]) i
      (by simp [hsegs, tailEndSegs]; omega)
    simpa [hsegs, tailEndSegs] using this
  have vch : ∀ i < 7, σ' (.n (k + 36 + i)) = challengeVals (cells13F S 0) (cells13F S 1) i :=
    fun i hi ↦ by
      have := seg 4 (by omega) 36 (by simp [hsegs, segLen, tailEndSegs]) i
        (by simp [hsegs, tailEndSegs]; omega)
      simpa [hsegs, tailEndSegs] using this
  have vcl : ∀ i < 5, σ' (.n (k + 43 + i)) = [ch * σ (.n f2.b), σ (.n f2.c) + ch * σ (.n f2.b),
      ch * ch, ch * ch * σ (.n f2.a),
      σ (.n f2.c) + ch * σ (.n f2.b) + ch * ch * σ (.n f2.a)].getD i 0 := fun i hi ↦ by
    have := seg 5 (by omega) 43 (by simp [hsegs, segLen, tailEndSegs]) i
      (by simp [hsegs, tailEndSegs]; omega)
    simpa [hsegs, tailEndSegs] using this
  have vz : ∀ i < yrLogCap - c.yrLog, σ' (.n (k + 48 + i)) = 0 := fun i hi ↦ by
    have := seg 6 (by omega) 48 (by simp [hsegs, segLen, tailEndSegs]) i
      (by simp [hsegs, tailEndSegs]; omega)
    simpa [hsegs, tailEndSegs] using this
  have a0 := ha g0 hfl.1; have a1 := ha g1 hfl.2.1; have a2 := ha g2 hfl.2.2.1
  have a3 := ha g3 hfl.2.2.2.1; have a4 := ha g4 hfl.2.2.2.2
  have aw0 := ha _ hb.w0; have aw1 := ha _ hb.w1
  have ab := ha _ hb.b; have ac := ha _ hb.c; have aa := ha _ hb.a
  have atch := ha _ htch
  obtain ⟨z1, z2, z3, z4⟩ := hz
  have zp : ∀ i, 1 ≤ i → i ≤ 4 → σ' (.n (p + i)) = 0 := fun i h1 h2 ↦ by
    rw [ha _ (by omega)]
    interval_cases i <;> assumption
  have hfsv : f2.fsv σ = [σ (.n g0), σ (.n g1), σ (.n g2), σ (.n g3), σ (.n g4)] := by
    simp [OsSt.fsv, hg]
  have hch6 : σ' (.n (k + 42)) = ch := by
    have := vch 6 (by omega)
    rw [show k + 36 + 6 = k + 42 by omega] at this
    rw [this, show cells13F S 0 = cellsOfState S false 0 from rfl,
      show cells13F S 1 = cellsOfState S false 1 from rfl, challengeVals_six]
  refine ⟨?_, ?_, ha⟩
  · simp only [tailEnd, allOk_append, allOk_cons]
    rw [← hkdef]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
    · -- the capacity copied
      rw [hg]
      simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, allOk_cons,
        allOk_nil, and_true, StmtOk, Atom.Holds, Nat.zero_add, Nat.add_zero]
      rw [hfsv] at vcp
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := vcp 0 (by omega); simp at this; rw [this, a0]
      · have := vcp 1 (by omega); simp at this; rw [this, a1]
      · have := vcp 2 (by omega); simp at this; rw [this, a2]
      · have := vcp 3 (by omega); simp at this; rw [this, a3]
      · have := vcp 4 (by omega); simp at this; rw [this, a4]
    · exact (allOk_fsPackT _ _ _).mpr (fsPackOk_of_vals fun i hi ↦ by rw [vp0 i hi, aw0])
    · exact (allOk_fsPackT _ _ _).mpr (fsPackOk_of_vals fun i hi ↦ by rw [vp1 i hi, aw1])
    · -- the permutation
      have c0 := fsPackVals_cells (σ (.n f2.w0)) 1
      have c1 := fsPackVals_cells (σ (.n f2.w1)) 1
      simp only [Prod.ext_iff] at c0 c1
      have e11 := vp0 6 (by omega); have e13 := vp0 8 (by omega)
      have e20 := vp1 6 (by omega); have e22 := vp1 8 (by omega)
      simp only [Nat.add_assoc, Nat.reduceAdd] at e11 e13 e20 e22
      rw [c0.1] at e11; rw [c0.2] at e13; rw [c1.1] at e20; rw [c1.2] at e22
      have hins : ([k + 11, k + 13, k + 20, k + 22, p + 1, p + 2, p + 3, p + 4, k, k + 1, k + 2,
          k + 3, k + 4].map V.n).map σ' =
          pendCells (f2.F σ).pend ++ List.replicate (8 - 2 * (f2.F σ).pend.length) 0 ++
            (f2.F σ).cap := by
        have q0 := vcp 0 (by omega); have q1 := vcp 1 (by omega); have q2 := vcp 2 (by omega)
        have q3 := vcp 3 (by omega); have q4 := vcp 4 (by omega)
        rw [hfsv] at q0 q1 q2 q3 q4
        simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at q0 q1 q2 q3 q4
        simp only [List.map_cons, List.map_nil]
        rw [e11, e13, e20, e22, zp 1 le_rfl (by omega), zp 2 (by omega) (by omega),
          zp 3 (by omega) (by omega), zp 4 (by omega) le_rfl, q0, q1, q2, q3, q4]
        simp [pendCells, OsSt.F, hfsv, dsObserve]
      show (Atom.keccak _ _ false false).Holds rd σ'
      apply keccakA_of (rd := rd) (by rfl) (by rfl)
      · rw [hins]
        intro x hx
        simp only [List.mem_append, List.mem_replicate] at hx
        rcases hx with (hx | hx) | hx
        · exact pendCells_canonical _ x hx
        · rw [hx.2, zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
        · exact hcan x hx
      · rw [hins, ← perm_eq_cells _ (by simp [OsSt.F])]
        funext c'
        simp only [cells13, osRun, List.map_map, Function.comp_def]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range c'.isLt,
          Option.map_some, Option.getD_some]
        have := vout c'.val c'.isLt
        simp only [cells13F, c'.isLt, ↓reduceDIte] at this
        exact this
    · -- the challenge
      rw [allOk_challengeT]
      apply challengeOk_of_vals
      · have := vout 1 (by omega)
        rw [this]; exact cellsOfState_canonical S false ⟨1, by omega⟩
      · intro i hi
        have o0 := vout 0 (by omega); have o1 := vout 1 (by omega)
        rw [Nat.add_zero] at o0
        rw [o0, o1]
        exact vch i hi
    · -- the claim
      simp only [allOk_nil, and_true, StmtOk, Atom.Holds]
      have l0 := vcl 0 (by omega); have l1 := vcl 1 (by omega); have l2 := vcl 2 (by omega)
      have l3 := vcl 3 (by omega); have l4 := vcl 4 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_assoc,
        Nat.reduceAdd] at l0 l1 l2 l3 l4
      refine ⟨by rw [hch6, atch]; exact hlast, by rw [l0, hch6, ab], by rw [l1, ac, l0],
        by rw [l2, hch6], by rw [l3, l2, aa], by rw [l4, l1, l3]⟩
    · -- the zeros
      rw [allOk_flatten]
      intro b hb'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb'
      rw [List.mem_range] at hi
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      refine ⟨by rw [vz i hi, word_zero], by rw [vz i hi, atch]; exact hzero i hi⟩
  · have := vcl 4 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_assoc, Nat.reduceAdd] at this
    have hsq : (f2.F σ).squeeze.1 = ch := rfl
    rw [show k + 47 = k + (43 + 4) by omega, ← Nat.add_assoc, this, hsq]
    simp only [OsSt.quad, polyEval, List.foldr_cons, List.foldr_nil]
    ring

/-- A buffer allocated at `T`: its size and pointer. -/
theorem osHeap_complete {e k : ℕ} (σ : Val) (T : E) :
    BlkF C rd σ k (k + 2) (fun i ↦ [gw e, T].getD (i - k) 0) (osHeap e k)
      (fun σ' ↦ σ' (.n (k + 1)) = T ∧ AgreeBelow k σ σ') := by
  intro σ' ha hv
  have v0 := hv k le_rfl (by omega)
  have v1 := hv (k + 1) (by omega) (by omega)
  simp only [Nat.sub_self, List.getD_cons_zero, Nat.add_sub_cancel_left, List.getD_cons_succ] at v0 v1
  refine ⟨?_, v1, ha⟩
  simp only [osHeap, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
  exact v0

/-- The values of the tail. -/
def tailF (c : OsCfg) (st : OsSt) (σ : Val) (T : E) (xs : List E) : ℕ → E :=
  seqF σ st.k (st.k + 2) (fun i ↦ [gw yrLogCap, T].getD (i - st.k) 0) fun σ1 ↦
  seqF σ1 (st.k + 2) (osFolds (st.k + 1) 0 (c.yrLog - 1) { st with k := st.k + 2 }).2.k
    (foldsF (st.k + 1) (c.yrLog - 1) 0 { st with k := st.k + 2 } σ1 xs) fun σ2 ↦
  fun i ↦ segLookup (tailEndSegs c σ2 (osFolds (st.k + 1) 0 (c.yrLog - 1)
    { st with k := st.k + 2 }).2) (i - (osFolds (st.k + 1) 0 (c.yrLog - 1)
      { st with k := st.k + 2 }).2.k)

/-- **The tail rounds, honestly.** -/
theorem osTail_complete {c : OsCfg} {st : OsSt} (σ : Val)
    (hC : ∀ args rets, MeaningOpeningFold rd args rets → C "opening_fold" args rets)
    {F : Fs} {q : List E} {t cur : E} (hs : LvsSt σ st F q t cur) {p : ℕ} (hp : st.pad = some p)
    (T : E) {xs : List E} (hxl : xs.length = 2 * (c.yrLog - 1)) (hrd : ReadsAt rd cur xs)
    (hT : ∀ j, j < c.yrLog - 1 → LoadHolds rd T j ((foldsTr (c.yrLog - 1) F q t xs).2.1.getD j 0))
    (hlast : LoadHolds rd T (c.yrLog - 1) (foldsTr (c.yrLog - 1) F q t xs).1.squeeze.1)
    (hzero : ∀ i < yrLogCap - c.yrLog, LoadHolds rd T (c.yrLog + i) 0) :
    BlkF C rd σ st.k (osTail c st).2.1.k (tailF c st σ T xs) (osTail c st).1
      (fun σ' ↦ σ' (.n (osTail c st).2.2) = T ∧
        σ' (.n (osTail c st).2.1.t) = polyEval (foldsTr (c.yrLog - 1) F q t xs).2.2.1
          (foldsTr (c.yrLog - 1) F q t xs).1.squeeze.1 ∧ AgreeBelow st.k σ σ') := by
  rw [osTail_eq]
  dsimp only
  rw [List.append_assoc]
  unfold tailF
  set R := foldsTr (c.yrLog - 1) F q t xs with hR
  set st' : OsSt := { st with k := st.k + 2 } with hst'
  set f := osFolds (st.k + 1) 0 (c.yrLog - 1) st' with hf
  have hpk := hs.pk p hp
  have hst'k : st'.k = st.k + 2 := rfl
  have hk2 : st.k + 2 ≤ f.2.k := osFolds_k (st.k + 1) (c.yrLog - 1) 0 st'
  refine BlkF.then (k1 := st.k + 2) (by omega) (by omega) (osHeap_complete σ T)
    fun σ1 ha1 ⟨hT1, ha1'⟩ ↦ ?_
  have ha1'' := ha1'
  obtain ⟨e1, eF, eQ, eT, eC⟩ := OsSt.agree hs.below ha1'
  have hb' : st'.Below := ⟨fun f hf ↦ by have := hs.below.fs f hf; simp [hst']; omega,
    by have := hs.below.w0; simp [hst']; omega, by have := hs.below.w1; simp [hst']; omega,
    by have := hs.below.cb; simp [hst']; omega, by have := hs.below.c; simp [hst']; omega,
    by have := hs.below.b; simp [hst']; omega, by have := hs.below.a; simp [hst']; omega,
    by have := hs.below.t; simp [hst']; omega⟩
  have eF' : st'.F σ1 = F := by rw [show st'.F σ1 = st.F σ1 from rfl, eF, hs.F]
  have eQ' : st'.quad σ1 = q := by rw [show st'.quad σ1 = st.quad σ1 from rfl, eQ, hs.quad]
  have eT' : σ1 (.n st'.t) = t := by rw [show st'.t = st.t from rfl, eT, hs.t]
  have eC' : st'.cur σ1 = cur := by rw [show st'.cur σ1 = st.cur σ1 from rfl, eC, hs.cur]
  have hA := osFolds_complete (C := C) (rd := rd) hC (st.k + 1) (c.yrLog - 1) 0 st' σ1 xs hs.fs
    (by have := hs.co; show st.co < u128Bound; unfold u128Bound; omega) hb' (by simp [hst'])
    (by rw [show st'.fsv σ1 = st.fsv σ1 from rfl, e1]; exact hs.can) hxl (by rw [eC']; exact hrd)
    (fun j hj ↦ by rw [hT1, eF', eQ', eT', Nat.zero_add]; exact hT j hj)
  rw [eF', eQ', eT'] at hA
  refine BlkF.then (k1 := f.2.k) hk2 (by omega) hA fun σ2 ha2 ⟨fo, ha2'⟩ ↦ ?_
  have hpad2 : f.2.pad = some p := by rw [fo.pad]; exact hp
  have e2 : ∀ i, i < st.k + 2 → σ2 (.n i) = σ1 (.n i) := fun i hi ↦ ha2' i hi
  have hB := osTailEnd_complete (C := C) (rd := rd) (c := c) (tch := st.k + 1) (f2 := f.2)
    (p := f.2.pad.getD 0) σ2 fo.fs fo.below (by omega) (by rw [hpad2]; simp; omega)
    (by
      rw [hpad2]
      simp only [Option.getD_some]
      have hpo := hs.pad
      rw [hp] at hpo
      obtain ⟨z1, z2, z3, z4⟩ := hpo
      exact ⟨by rw [e2 (p + 1) (by omega), ha1' (p + 1) (by omega)]; exact z1,
        by rw [e2 (p + 2) (by omega), ha1' (p + 2) (by omega)]; exact z2,
        by rw [e2 (p + 3) (by omega), ha1' (p + 3) (by omega)]; exact z3,
        by rw [e2 (p + 4) (by omega), ha1' (p + 4) (by omega)]; exact z4⟩)
    fo.can (by rw [e2 _ (by omega), hT1, fo.F]; exact hlast)
    (fun i hi ↦ by rw [e2 _ (by omega), hT1]; exact hzero i hi)
  rw [fo.F, fo.quad] at hB
  refine BlkF.mono hB fun σ' ⟨hcl, ha3⟩ ↦ ⟨?_, hcl, ?_⟩
  · show σ' (.n (st.k + 1)) = T
    rw [ha3 (st.k + 1) (by omega), e2 (st.k + 1) (by omega), hT1]
  · intro i hi
    exact (ha3 i (by omega)).trans ((ha2' i (by omega)).trans (ha1' i hi))

end
end LeanVM.Guest.B1.Whir
