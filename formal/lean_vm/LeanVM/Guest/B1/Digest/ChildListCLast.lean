/-
  LeanVM.Guest.B1.Digest.ChildListCLast

  `child_claim_list_any`'s frame loops `__loop17` and `__loop18`: a block's honest valuation, with
  where its loads read.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk1
public import LeanVM.Guest.B1.Digest.ChildListCW0
public import LeanVM.Guest.B1.Digest.ChildListCW1
public import LeanVM.Guest.B1.Digest.ChildListCW2
public import LeanVM.Guest.B1.Digest.ChildListCW3
public import LeanVM.Guest.B1.Digest.ChildListCRec
public import LeanVM.Guest.B1.Digest.PlacedLib
public import LeanVM.Guest.B1.Da.AtBase

/-!
# A frame of child claims, completely

`any_core`: a frame loop's block at the counter `x = g^xj` (`__loop17`, 136 claims, or `__loop18`,
17), from the state after whole blocks `pre` at `chain · x^13`, `m` honest records (`RecMem`:
slots `os j` below the bound `g^L = last · g`, marks `base · x^m · g^j` at `region · g^(os j)`,
cells at `entries · g^(4 os j)`) and the state after their cells at `chain · x^13` from offset
`13`: the body's evaluated valuation (`Fwd.ev`, the slots from `slotW`) holds its atoms, and every
load reads the state's or the next state's words, a record's mark or a record's cells. Soundness's
`anyOk` gives the chain's check, completeness's `anycOk` parts the rest (`blockW_holds`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Da (limb0_gen_pow_mul)

@[expose] public section

variable {rd : Reader}

theorem ccc_all {k : ℕ} (hk : k < 17) : cccOk k (coreProgram.getD (380 + k) default) = true := by
  rcases Nat.lt_or_ge k 9 with h | h
  · exact ccc_lo k h
  · have := ccc_hi (k - 9) (by omega)
    rwa [show 9 + (k - 9) = k by omega, show 389 + (k - 9) = 380 + k by omega] at this

theorem mem_ccA {st : List V} {o0 K i : ℕ} (h : i ∈ ccA st o0 K) :
    (∃ v ∈ st, i = v.idx) ∨ ∃ j < K, ∃ c < 4, i = ccCell o0 j c := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨v, hv, rfl⟩
  · obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact Or.inr ⟨j, List.mem_range.mp hj, c, List.mem_range.mp hc, rfl⟩

/-- The records' message is their cells. -/
theorem ccMsg_vals {σ : Val} {o0 K : ℕ} {cells : List E} (hl : cells.length = 4 * K)
    (hv : ∀ j < K, ∀ c < 4, σ (.n (ccCell o0 j c)) = cells.getD (4 * j + c) 0) :
    (ccMsg o0 K).map (srcVal σ) = cells := by
  refine List.ext_getElem (by simp [ccMsg, hl]) fun i h1 h2 => ?_
  have hi : i < 4 * K := by simpa [ccMsg] using h1
  simp only [ccMsg, List.getElem_map, List.getElem_range, srcVal]
  rw [hv (i / 4) (by omega) (i % 4) (by omega), show 4 * (i / 4) + i % 4 = i by omega,
    List.getD_eq_getElem _ _ h2]

/-- The canonical inputs: the state's cells and the records'. -/
theorem ccA_canon {σ : Val} (hidx : ∀ v, σ v = σ (.n v.idx)) {st : List V} {S : KeccakState}
    {o0 K : ℕ} {cells : List E} (hl : cells.length = 4 * K)
    (hlen : st.length = 13) (vst : ∀ c : Fin 13, σ (st.getD c default) = cellsOfState S false c)
    (vc : ∀ j < K, ∀ c < 4, σ (.n (ccCell o0 j c)) = cells.getD (4 * j + c) 0) :
    ∀ i ∈ ccA st o0 K, IsCanonical128 (σ (.n i)) := by
  intro i hi
  rcases mem_ccA hi with ⟨v, hv, rfl⟩ | ⟨j, hj, c, hc4, rfl⟩
  · obtain ⟨c, hc13, rfl⟩ := List.getElem_of_mem hv
    have := vst ⟨c, by omega⟩
    rw [List.getD_eq_getElem _ _ hc13] at this
    rw [← hidx, this]
    exact canon_cellsOfState _ _ _
  · rw [vc j hj c hc4, List.getD_eq_getElem _ _ (by omega)]
    exact hc _ (List.getElem_mem _)

theorem edge_parts {A S : List Atom} {o0 p0 K stp : ℕ} {outs : List V}
    (h : edgeOk A S o0 p0 K stp outs = true) :
    (∀ a ∈ S, storesOk o0 stp a = true) ∧ markPtrB o0 stp = false ∧
      (∀ a ∈ A.take p0, needsSide a = false) ∧
      ∀ a ∈ A.drop (ccPos p0 K), needsSide a = false ∨ isStLd stp a = true ∨
        isStSt outs stp a = true := by
  simp only [edgeOk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun a ha => (h4 a ha).elim (fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))
    (fun h => Or.inr (Or.inr h))⟩

/-- **A record's load reads** its mark's slot `region · g^(os j)` or a cell at
`entries · g^(4 os j)`. -/
theorem sideW_addr {σ : Val} {F : List Atom} {P : ClaimVs} {o0 j : ℕ} {e rg eP : ℕ} {d p : V}
    {off : ℕ} (hF : ∀ a ∈ F, a.Holds rd σ) (hwit : σ (.n (ccOV o0 j)) = gen ^ e)
    (hrg : σ P.region = gen ^ rg) (hen : σ P.entries = gen ^ eP)
    (h : sideW F P o0 j (.load d p off) = true) :
    (σ p).limb 0 * addressOfIndex off = addressOfIndex (rg + e) ∨
      ∃ c < 4, (σ p).limb 0 * addressOfIndex off = addressOfIndex (eP + 4 * e + c) := by
  simp only [sideW, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨rfl, -⟩, hperm⟩ | ⟨hoff, hc⟩
  · left
    rw [monoPerm_sound hperm hF]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hrg, hwit, ← pow_add, limb0_gen_pow_mul, Nat.add_zero]
  · simp only [isCellLd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hc
    obtain ⟨-, hperm⟩ := hc
    refine Or.inr ⟨off, hoff, ?_⟩
    rw [cells_ptr hperm hF hwit, hen, ← pow_add, limb0_gen_pow_mul]

theorem isStSt_nil {stp : ℕ} {a : Atom} (h : isStSt [] stp a = true) : False := by
  cases a <;> simp only [isStSt, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.length_nil, Nat.add_zero] at h
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **A frame of child claims' honest valuation** (a frame loop's block at `x = g^xj`), with
where its loads read: the state's `13` words and the next state's at `chain · x^13`, a record's
mark at `region · g^(os j)`, a record's cells at `entries · g^(4 os j)`. -/
theorem any_core {j : ℕ} {f : String} {m o0 p0 mk st0 nb : ℕ}
    (hok : anyOk (coreProgram.getD j default) f m o0 p0 mk st0 = true)
    (hhd : anycHead (coreProgram.getD j default) f = true)
    (hcn : anycCanon (coreProgram.getD j default) m o0 st0 = true)
    (hedge : anycEdge (coreProgram.getD j default) m o0 p0 mk st0 = true)
    (hrecs : ∀ i < m,
      recW (ccOwn (loopAtoms (coreProgram.getD j default)) p0 i) (anyP mk) o0 i = true)
    (hnb : (anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    {x N chain entries region base last : E} {xj chP eP rg L : ℕ}
    (hx : x = gen ^ xj) (hch : chain = gen ^ chP) (hen : entries = gen ^ eP)
    (hrg : region = gen ^ rg) {n : ℕ} {pre : List UInt8} (hpre : pre.length = rate * n)
    (hS : StateAt rd (chain * x ^ 13) 0 (absorbChunks n zeroState pre))
    {os : ℕ → ℕ} {cells : List E} (hl : cells.length = 4 * m)
    (hrec : RecMem rd region (gen ^ L) entries (base * x ^ m) m os cells)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L)
    (hS' : StateAt rd (chain * x ^ 13) 13
      (absorbChunks (n + nb) zeroState (pre ++ cellsBytes cells))) :
    ∃ σ : Val, (coreProgram.getD j default).params.map σ =
        [x, N, chain, entries, region, base, last] ∧
      (∀ a ∈ atomsIn (loopPre (coreProgram.getD j default)), a.Holds rd σ) ∧
      ∀ q ∈ (loopPre (coreProgram.getD j default)).filterMap B1.Stmt.loadS,
        (∃ o < 26, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (chP + 13 * xj + o)) ∨
        (∃ i < m, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (rg + os i)) ∨
        (∃ i < m, ∃ c < 4,
          (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex (eP + 4 * os i + c)) := by
  set fn := coreProgram.getD j default
  set A := loopAtoms fn with hAdef
  set S := storesOf 7 fn.body with hSdef
  simp only [anyOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hlen7⟩, hck⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  simp only [anycHead, Bool.and_eq_true, Option.isSome_iff_exists] at hhd
  obtain ⟨⟨⟨⟨hshape, c', hchk⟩, hpreA⟩, heqA⟩, -⟩ := hhd
  have heqA' := atomsEqbL_sound heqA
  simp only [anycEdge, Bool.and_eq_true] at hedge
  obtain ⟨⟨⟨hedge, hst⟩, hm12⟩, hmk⟩ := hedge
  obtain ⟨hSt, hst12, hhd0, htl⟩ := edge_parts hedge
  let args : List E := [x, N, chain, entries, region, base, last]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (slotW o0 os) args fn.body) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (slotW o0 os) fn.body args hchk
  rw [show args.length = 7 from rfl, ← hσ] at hgs
  have hg : ∀ a ∈ A, Good rd S (slotW o0 os) σ a := fun a ha =>
    hgs (.atom a) (cl_pre_mem (cl_atom_mem (by rw [heqA']; exact ha)))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] := by
    have hs2 := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs2
    rw [hs2.1.2, hlen7]; rfl
  have par : ∀ i (hi : i < 7), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have e2 : σ (.n 2) = chain := par 2 (by omega)
  have e3 : σ (.n 3) = entries := par 3 (by omega)
  have e4 : σ (.n 4) = region := par 4 (by omega)
  have e5 : σ (.n 5) = base := par 5 (by omega)
  have e6 : σ (.n 6) = last := par 6 (by omega)
  have hF := pure_holds hg
  have v12 : σ (.n 12) = chain * x ^ 13 := by rw [monoIs_sound hm12 hF, e2, e0]
  have vmk : σ (.n mk) = base * x ^ m := by rw [monoIs_sound hmk hF, e5, e0]
  have hrec' : RecMem rd (σ (anyP mk).region) (gen ^ L) (σ (anyP mk).entries)
      (σ (anyP mk).marks) m os cells := by
    show RecMem rd (σ (.n 4)) (gen ^ L) (σ (.n 3)) (σ (.n mk)) m os cells
    rw [e4, e3, vmk]; exact hrec
  have hlast' : σ (anyP mk).last * gen = gen ^ L := by
    show σ (.n 6) * gen = _; rw [e6]; exact hlast
  obtain ⟨hwit, -, vc, hside⟩ := recsW_holds hrecs hg hSt hrec' hlast' hL33 hdef
  have hpv : ∀ {p : V}, p.idx = 12 → σ p = chain * x ^ 13 := fun hp => by rw [hidx, hp, v12]
  have hnSl : ∀ {d p : V} {off : ℕ}, p.idx = 12 → off < 13 → Atom.load d p off ∉ S :=
    fun hp ho => notS_of_ptr hSt (by rw [hp]; exact hst12) ho
  have vst : ∀ c : Fin 13, σ ((anySt st0).getD c default) =
      cellsOfState (absorbChunks n zeroState pre) false c := by
    intro c
    simp only [stLoadsOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hst
    rw [load_val (hst.2 c c.isLt) hg (hnSl rfl (by have := c.isLt; omega)), v12,
      rdAt_of_load (hS c)]
  have hA := ccA_canon (o0 := o0) hidx hl hc (by simp [anySt]) vst vc
  have hat : ∀ a ∈ A, a.Holds rd σ := by
    refine blockW_holds (c := 7) (ss := fn.body) (p0 := p0) (stp := 12)
      (outs := anyOuts m o0 st0 A) hidx (canonChk_of_canonGoB hcn) hg hA hedge hside ?_ ?_ ?_
    · intro a ha h haS
      cases a <;> simp only [isStLd, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      rename_i d p off
      have hv := hS ⟨off, h.2⟩
      rw [Nat.zero_add, ← hpv h.1] at hv
      exact load_holds_of haS (hg _ ha) hv
    · intro a ha h haS
      cases a <;> simp only [isStSt, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      rename_i d p off
      obtain ⟨⟨⟨hp, ho1⟩, ho2⟩, -⟩ := h
      obtain ⟨c, rfl⟩ : ∃ c, off = 13 + c := ⟨off - 13, by omega⟩
      have hv := hS' ⟨c, by simp [anyOuts] at ho2; omega⟩
      rw [← hpv hp] at hv
      exact load_holds_of haS (hg _ ha) hv
    · intro h1 a ha h haS
      cases a <;> simp only [isStSt, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      rename_i d p off
      obtain ⟨⟨⟨hp, ho1⟩, ho2⟩, hd⟩ := h
      obtain ⟨c, rfl⟩ : ∃ c, off = 13 + c := ⟨off - 13, by omega⟩
      have hc13 : c < 13 := by simp [anyOuts] at ho2; omega
      have hG : ∀ b ∈ A.filter (fun a => decide (a ∉ S)), b.Holds rd σ :=
        fun b hb => h1 b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)
      have hq : ∀ a, isLoadB a = false → decide (a ∉ S) = true := by
        intro a ha'
        simp only [decide_eq_true_eq]
        intro hm
        obtain ⟨_, _, _, rfl⟩ := storesOf_load hm
        simp [isLoadB] at ha'
      have hchk' : (anySpec m o0 st0 A).check (A.filter (fun a => decide (a ∉ S))) = true := by
        rw [check_filter hq]; exact hck
      obtain ⟨hw, -⟩ := chain_whole hchk' rfl hG hpre (fun c => vst c)
      have hv : (anySpec m o0 st0 A).vals σ = cells := ccMsg_vals hl vc
      have hwc := hw ⟨c, hc13⟩
      rw [hv, hnb, show ((⟨c, hc13⟩ : Fin 13) : ℕ) = c from rfl] at hwc
      have hd' : d = (anySpec m o0 st0 A).outV ((anySpec m o0 st0 A).nb - 1) c := by
        rw [hd, show 13 + c - 13 = c by omega]
        simp [anyOuts, List.getD_eq_getElem?_getD, hc13]
      show LoadHolds rd (σ p) (13 + c) (σ d)
      rw [hd', hnb, hwc, hpv hp]
      exact hS' ⟨c, hc13⟩
  have h12g : chain * x ^ 13 = gen ^ (chP + 13 * xj) := by
    rw [hch, hx, ← pow_mul, ← pow_add, mul_comm xj 13]
  refine ⟨σ, ?_, fun a ha => hat a (by rwa [heqA'] at ha), fun q hq => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, par 1 (by omega), e2, e3, e4, e5, e6]
    rfl
  · obtain ⟨s, hs, hsq⟩ := List.mem_filterMap.mp hq
    have := List.all_eq_true.mp hpreA s hs
    cases s <;> simp only [isAtomS, Bool.false_eq_true] at this
    rename_i a
    cases a with
    | load d p off =>
      simp only [B1.Stmt.loadS, Option.some.injEq] at hsq
      subst hsq
      have ha : Atom.load d p off ∈ A := by have := cl_mem_atoms hs; rwa [heqA'] at this
      rcases mem_parts (p0 := p0) (K := m) ha with h | ⟨i, hi, h⟩ | h
      · exact absurd (hhd0 _ h) (by simp [needsSide])
      · have hFi : ∀ b ∈ (ccOwn A p0 i).filter pureB, b.Holds rd σ :=
          fun b hb => hat b (mem_ccOwn (List.mem_filter.mp hb).1)
        rcases sideW_addr hFi (hwit i hi) (show σ (.n 4) = _ by rw [e4, hrg])
            (show σ (.n 3) = _ by rw [e3, hen])
            ((recW_parts (hrecs i hi)).2.2.2 _ h rfl) with h' | ⟨c, hc4, h'⟩
        · exact Or.inr (Or.inl ⟨i, hi, h'⟩)
        · exact Or.inr (Or.inr ⟨i, hi, c, hc4, h'⟩)
      · rcases htl _ h with h' | h' | h'
        · exact absurd h' (by simp [needsSide])
        · simp only [isStLd, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
          refine Or.inl ⟨off, by omega, ?_⟩
          show (σ p).limb 0 * addressOfIndex off = _
          rw [hpv h'.1, h12g, limb0_gen_pow_mul]
        · simp only [isStSt, anyOuts, List.length_map, List.length_range, Bool.and_eq_true,
            beq_iff_eq, decide_eq_true_eq] at h'
          refine Or.inl ⟨off, by omega, ?_⟩
          show (σ p).limb 0 * addressOfIndex off = _
          rw [hpv h'.1.1.1, h12g, limb0_gen_pow_mul]
    | _ => simp [B1.Stmt.loadS] at hsq

/-! ## The two frame loops -/

theorem any136c_recs : ∀ i < 136,
    recW (ccOwn (loopAtoms (coreProgram.getD 378 default)) 15 i) (anyP 21) 22 i = true :=
  recs_of_wins (w := 9) (W := 16) (by norm_num) fun i hi => by
    have hw : ∀ i < 16, anycWin i = true := by
      intro i hi
      interval_cases i
      exacts [anycWin_0, anycWin_1, anycWin_2, anycWin_3, anycWin_4, anycWin_5, anycWin_6,
        anycWin_7, anycWin_8, anycWin_9, anycWin_10, anycWin_11, anycWin_12, anycWin_13,
        anycWin_14, anycWin_15]
    exact hw i hi

theorem any17c_parts : anycHead (coreProgram.getD 379 default) "__loop18" = true ∧
    anycCanon (coreProgram.getD 379 default) 17 19 255 = true ∧
    anycEdge (coreProgram.getD 379 default) 17 19 12 18 255 = true ∧
    ∀ i < 17, recW (ccOwn (loopAtoms (coreProgram.getD 379 default)) 12 i) (anyP 18) 19 i = true := by
  have h := any17c_ok
  simp only [anycOk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, recs_of_wins (w := 17) (W := 1) le_rfl fun i hi => by
    rw [show i = 0 by omega]; exact h.2⟩

end
end LeanVM.Guest.B1.Digest
