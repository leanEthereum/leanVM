/-
  LeanVM.Guest.B1.Gkr.LayerTail

  The tail of a layer of `verify_bus_gkr` (`__loop6`): the rounds between its first and last
  records, the twelve children read and absorbed, their check, the two new coordinates squeezed,
  and the next slot's stores.
-/

module

public import LeanVM.Guest.B1.Gkr.Layer

/-!
# A layer's rounds and children (`__loop6`, G:1865-1927)

* `ly_rounds`: `__loop27`, then `gkr_rounds__L2` at an odd layer index, then `gkr_rounds__L1` at
  an odd depth, run the `L = 2j + sh` rounds from the layer's first record;
* `ly_tail`: the twelve words at the last record's cursor are the three trees' children, their
  products check the last claim, and the sponge after them squeezes the two new coordinates;
* `ly_stores`: the next slot's cells, cursor, values, row, position, `half` and `parity`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Child `i`'s read's first statement in `lyPre`. -/
def lyPos (i : ℕ) : ℕ := 73 + 10 * i + i / 4

theorem lyEvs_check : ∀ i < 12,
    tbStmtsEqb (lyEvT i) ((lyPre.drop (lyPos i)).take (lyEvT i).length) = true := by
  decide +kernel

/-- The words of the children `4m .. 4m + 3`. -/
def lyCh (σ : Val) (m : ℕ) : List E := (List.range 4).map fun i ↦ σ (.n (lyEv (4 * m + i)))

theorem lyCh_length (σ : Val) (m : ℕ) : (lyCh σ m).length = 4 := by simp [lyCh]

theorem lyCh_eq (σ : Val) (m : ℕ) : lyCh σ m = [σ (.n (lyEv (4 * m))), σ (.n (lyEv (4 * m + 1))),
    σ (.n (lyEv (4 * m + 2))), σ (.n (lyEv (4 * m + 3)))] := by
  simp [lyCh, List.range_succ]

/-- Absorbing four scalars at a full queue: one permutation, then the four waiting. -/
theorem tb_absorbAll_full (s : Fs) (hs : s.pend.length = 4) (xs : List E) (hx : xs.length = 4)
    (t : ℕ) : s.absorbAll xs t = ⟨capOf s.perm, xs.map (·, t)⟩ := by
  match xs, hx with
  | x :: rest, hx =>
    simp only [Fs.absorbAll, List.foldl_cons]
    have h1 : s.absorb x t = ⟨capOf s.perm, [(x, t)]⟩ := by
      simp [Fs.absorb, hs, rateScalars]
    rw [h1]
    have := absorbAll_short ⟨capOf s.perm, [(x, t)]⟩ rest t (by simp at hx ⊢; omega)
    simp only [Fs.absorbAll] at this
    rw [this]
    simp

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- A permutation's thirteen outputs from `b`, and its capacity cells. -/
theorem ly_keccak {ins : List V} {b : ℕ} (hk : (Atom.keccak ins (lyOuts b) false false).Holds rd σ) :
    AllCanonical (ins.map σ) ∧
      (∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (permOf (ins.map σ)) := by
  obtain ⟨-, -, hcan, hout⟩ := keccakA_perm hk
  have hP : ∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
    intro k hk
    have := outs_eq hout ⟨k, hk⟩ (by simpa [lyOuts] using hk)
    simpa [lyOuts] using this
  refine ⟨hcan, hP, ?_⟩
  simp only [lyCap, capOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rw [hP (8 + 0) (by omega), hP (8 + 1) (by omega), hP (8 + 2) (by omega), hP (8 + 3) (by omega),
    hP (8 + 4) (by omega)]
  rfl

/-- Child `i`'s read: its word at the cursor, packed, and copied. -/
theorem ly_ev {i : ℕ} (h : Stmt.HoldsList C rd σ (lyEvT i) True kret) :
    LoadHolds rd (σ (.n 83)) i (σ (.n (lyEv i))) ∧
      FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve ∧ σ (.n (lyEv i + 10)) = σ (.n (lyEv i)) := by
  unfold lyEvT at h
  rw [tb_holdsList_append_noRet (by simp [fsNextT, fsPackT]; rfl), holds_fsNextT] at h
  obtain ⟨⟨⟨hl, hp⟩, -⟩, hc⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hc
  exact ⟨hl, hp, hc⟩

/-- **Four children's permutation**: their cells over the carried capacity. -/
theorem ly_perm_block {m b : ℕ} {cap : List V}
    (hp : ∀ i < 4, FsPackOk σ (.n (lyEv (4 * m + i))) (lyEv (4 * m + i) + 1) dsObserve)
    (hk : (Atom.keccak (lyRate m ++ cap) (lyOuts b) false false).Holds rd σ) :
    (∀ k (hk : k < 13), σ (.n (b + k)) =
      cellsOfState (Fs.perm ⟨cap.map σ, (lyCh σ m).map (·, dsObserve)⟩) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (Fs.perm ⟨cap.map σ, (lyCh σ m).map (·, dsObserve)⟩) := by
  obtain ⟨hcan, hP, hcap⟩ := ly_keccak hk
  have hcell : ∀ i < 4, σ (.n (lyEv (4 * m + i) + 7)) =
      (Keccak.scalarCells (σ (.n (lyEv (4 * m + i)))) dsObserve).1 ∧
      σ (.n (lyEv (4 * m + i) + 9)) = (Keccak.scalarCells (σ (.n (lyEv (4 * m + i)))) dsObserve).2 := by
    intro i hi
    have hc : IsCanonical128 (σ (.n (lyEv (4 * m + i) + 7))) := by
      apply hcan
      simp only [List.map_append, List.mem_append, lyRate, List.map_flatMap, List.mem_flatMap,
        List.mem_range, List.map_cons, List.map_nil, List.mem_cons]
      exact Or.inl ⟨i, hi, Or.inl rfl⟩
    have := fsPackT_cells (hp i hi)
      (by rw [show lyEv (4 * m + i) + 1 + 6 = lyEv (4 * m + i) + 7 by omega]; exact hc)
    rw [show lyEv (4 * m + i) + 1 + 6 = lyEv (4 * m + i) + 7 by omega,
      show lyEv (4 * m + i) + 1 + 8 = lyEv (4 * m + i) + 9 by omega] at this
    exact Prod.ext_iff.mp this
  have hrate : (lyRate m).map σ = pendCells ((lyCh σ m).map (·, dsObserve)) := by
    simp only [lyRate, lyCh, pendCells, List.map_flatMap, List.flatMap_map, List.map_cons,
      List.map_nil]
    rw [List.flatMap_def, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [(hcell i hi).1, (hcell i hi).2]
  have hins : (lyRate m ++ cap).map σ =
      rateOf ((lyCh σ m).map (·, dsObserve)) ++ cap.map σ := by
    rw [List.map_append, hrate, rateOf_eq_cells _ (by simp [lyCh_length])]
    simp [lyCh_length]
  rw [hins] at hP hcap
  exact ⟨hP, hcap⟩

/-- A side's new value: its four children's multilinear value at the two new coordinates. -/
theorem ly_val {t b off : ℕ} (h : Stmt.HoldsList C rd σ (lyVal t b off) True kret) :
    σ (.n (b + 8)) = multilinearEval [σ (.n (lyEv (4 * t + 0) + 10)), σ (.n (lyEv (4 * t + 1) + 10)),
      σ (.n (lyEv (4 * t + 2) + 10)), σ (.n (lyEv (4 * t + 3) + 10))]
      [σ (.n 278), σ (.n 298)] ∧ LoadHolds rd (σ (.n 16)) off (σ (.n (b + 8))) := by
  simp only [lyVal, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, l⟩ := h
  refine ⟨?_, l⟩
  rw [e8, e7, e6, e5, e4, e3, e2, e1, e0]
  simp only [multilinearEval, List.foldl, foldPairs, List.headD]
  ring

/-- The sponge after the twelve children, from the last record's capacity. -/
def lySponge (σ : Val) : Fs :=
  (((⟨(List.range 5).map fun k ↦ σ (.n (78 + k)), []⟩ : Fs).absorbAll (lyCh σ 0)
    dsObserve).absorbAll (lyCh σ 1) dsObserve).absorbAll (lyCh σ 2) dsObserve

theorem tb_word_three : word 3 0 0 = 1 + gen := by
  rw [tb_word_eOfNat, show (3 : ℕ) = 1 ^^^ 2 from rfl, eOfNat_xor, eOfNat_one, ← tb_word_eOfNat,
    tb_word_gen]

/-- **The rounds of a layer**: `__loop36` (`8·(j/4)` rounds), `gkr_rounds__L{2r}` at `r = j % 4`,
and `gkr_rounds__L1` at an odd depth are the `2j + sh` rounds from the first record. -/
theorem ly_rounds (hC : CallRel.Le C (coreProgram.Rel rd)) (hGR : tb_gkr_rounds_Spec)
    (h : Stmt.HoldsList C rd σ lyPre True kret) {j sh : ℕ} (hj : j < 2 ^ 30) (hsh : sh < 2)
    (e6 : σ (.n 7) = gen ^ (2 * j)) (e9 : σ (.n 10) = gen ^ (2 * j + sh))
    (e61 : σ (.n 62) = gen ^ (j / 4)) (e62 : σ (.n 63) = gen ^ (j % 4))
    (h0 : TbGkrRoundsOut 0 rd (σ (.n 53)) (σ (.n 51))) :
    TbGkrRoundsOut (2 * j + sh) rd (σ (.n 53)) (σ (.n 51)) := by
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have c63 := a 53 (.const (.n 64) (word 1 0 0)) (by decide +kernel)
  have a64 := a 54 (.add (.n 65) (.n 64) (.n 62)) (by decide +kernel)
  have c65 := a 55 (.const (.n 66) (word 1 0 0)) (by decide +kernel)
  have m67 := a 57 (.mul (.n 67) (.n 62) (.n 62)) (by decide +kernel)
  have m68 := a 58 (.mul (.n 68) (.n 67) (.n 67)) (by decide +kernel)
  have m69 := a 59 (.mul (.n 69) (.n 68) (.n 68)) (by decide +kernel)
  have m70 := a 60 (.mul (.n 70) (.n 53) (.n 69)) (by decide +kernel)
  have m71 := a 61 (.mul (.n 71) (.n 51) (.n 69)) (by decide +kernel)
  have a70 := a 63 (.add (.n 73) (.n 10) (.n 7)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at c63 a64 c65 m67 m68 m69 m70 m71 a70
  obtain ⟨-, hc29⟩ := tb_holds_callIf hnr h 56 (.n 65) "__loop36" [.n 66, .n 62, .n 53, .n 51]
    (by decide +kernel)
  simp only [List.map_cons, List.map_nil, c65] at hc29
  have R8 := l29_loop (h := j / 4) e61 (by omega)
    (fun hne => hC _ _ _ (hc29 (by rw [a64, c63]; exact hne))) h0
  have R2 : TbGkrRoundsOut (2 * j) rd (σ (.n 53)) (σ (.n 51)) := by
    obtain ⟨i, hi, hx, hcall⟩ := tb_holds_dispatch hnr h 62 (.n 63)
      ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"] [.n 70, .n 71]
      [.n 72] (by decide +kernel)
    simp only [List.length_cons, List.length_nil] at hi
    have hij : j % 4 = i := by
      rw [e62, ← gen_pow_eq_ofK] at hx
      exact gen_pow_inj (by omega) (by omega) hx
    have e69 : σ (.n 69) = gen ^ (8 * (j / 4)) := by
      rw [m69, m68, m67, e61, ← pow_add, ← pow_add, ← pow_add]; ring_nf
    rw [show 2 * j = 8 * (j / 4) + 2 * i by omega]
    simp only [List.map_cons, List.map_nil] at hcall
    rw [m70, m71, e69] at hcall
    interval_cases i
    · simpa using R8
    · exact gkrRoundsOut_append R8 (hGR 2 (by decide) rd _ _ _ (hC _ _ _ hcall))
    · exact gkrRoundsOut_append R8 (hGR 4 (by decide) rd _ _ _ (hC _ _ _ hcall))
    · exact gkrRoundsOut_append R8 (hGR 6 (by decide) rd _ _ _ (hC _ _ _ hcall))
  rcases (by omega : sh = 0 ∨ sh = 1) with rfl | rfl
  · simpa using R2
  · have hi := tb_holds_slice hnr h 64 [.ite (.n 73) [] [.atom (.mul (.n 74) (.n 53) (.n 7)),
      .atom (.mul (.n 75) (.n 51) (.n 7)), .call "gkr_rounds__L1" [.n 74, .n 75] [.n 76]]]
      (by decide +kernel)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil] at hi
    obtain ⟨-, -, hodd⟩ := hi
    have hne : σ (.n 73) ≠ 0 := by
      rw [a70, e9, e6]
      intro h0'
      have := gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h0')
      omega
    obtain ⟨m71, m72, hL1⟩ := hodd hne
    have := hGR 1 (by decide) rd _ _ _ (hC _ _ _ hL1)
    rw [m71, m72, e6] at this
    exact gkrRoundsOut_append R2 this

/-- **The children of a layer**: the twelve words at the last record's cursor, their products
checking the last claim at the combiner, the sponge after them squeezing the two new
coordinates, and the three sides' values at them. -/
theorem ly_tail (h : Stmt.HoldsList C rd σ lyPre True kret) :
    TbReadsAt rd (σ (.n 83)) (lyCh σ 0 ++ (lyCh σ 1 ++ lyCh σ 2)) ∧
      σ (.n 84) = polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 50)) ∧
      ((lySponge σ).squeezeN 2).1 = [σ (.n 278), σ (.n 298)] ∧
      ((lySponge σ).squeezeN 2).2 = ⟨(List.range 5).map fun k ↦ σ (.n (287 + k)), []⟩ ∧
      (∀ t < 3, σ (.n (305 + 9 * t + 8)) = multilinearEval (lyCh σ t) [σ (.n 278), σ (.n 298)] ∧
        LoadHolds rd (σ (.n 16)) (40 + t) (σ (.n (305 + 9 * t + 8)))) := by
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have EV : ∀ i < 12, _ := fun i hi => ly_ev (tb_holds_slice hnr h (lyPos i) (lyEvT i)
    (lyEvs_check i hi))
  have cp : ∀ i < 12, σ (.n (lyEv i + 10)) = σ (.n (lyEv i)) := fun i hi => (EV i hi).2.2
  have hp : ∀ m < 3, ∀ i < 4,
      FsPackOk σ (.n (lyEv (4 * m + i))) (lyEv (4 * m + i) + 1) dsObserve :=
    fun m hm i hi => (EV (4 * m + i) (by omega)).2.1
  -- the reads
  have hreads : TbReadsAt rd (σ (.n 83)) (lyCh σ 0 ++ (lyCh σ 1 ++ lyCh σ 2)) := by
    intro k hk
    have hk12 : k < 12 := by simpa [lyCh_length] using hk
    convert (EV k hk12).1 using 1
    simp only [lyCh_eq]
    interval_cases k <;> rfl
  -- the sponge
  have hS0 : ((List.range 5).map fun k ↦ V.n (78 + k)).map σ =
      (List.range 5).map fun k ↦ σ (.n (78 + k)) := by simp
  have A0 : (⟨(List.range 5).map fun k ↦ σ (.n (78 + k)), []⟩ : Fs).absorbAll (lyCh σ 0)
      dsObserve = ⟨(List.range 5).map fun k ↦ σ (.n (78 + k)), (lyCh σ 0).map (·, dsObserve)⟩ := by
    rw [absorbAll_short _ _ _ (by simp [lyCh_length])]
    simp
  have k2 := a 113 (.keccak (lyRate 0 ++ (List.range 5).map fun k ↦ .n (78 + k)) (lyOuts 129)
    false false) (by decide +kernel)
  obtain ⟨-, B0⟩ := ly_perm_block (hp 0 (by omega)) k2
  rw [hS0] at B0
  have k3 := a 154 (.keccak (lyRate 1 ++ lyCap 129) (lyOuts 186) false false) (by decide +kernel)
  obtain ⟨-, B1⟩ := ly_perm_block (hp 1 (by omega)) k3
  have k4 := a 212 (.keccak (lyRate 2 ++ lyCap 186) (lyOuts 259) false false) (by decide +kernel)
  obtain ⟨P2, B2⟩ := ly_perm_block (hp 2 (by omega)) k4
  have hA : lySponge σ = ⟨(lyCap 186).map σ, (lyCh σ 2).map (·, dsObserve)⟩ := by
    unfold lySponge
    rw [A0, tb_absorbAll_full _ (by simp [lyCh_length]) _ (lyCh_length σ 1), ← B0,
      tb_absorbAll_full _ (by simp [lyCh_length]) _ (lyCh_length σ 2), ← B1]
  rw [← hA] at P2 B2
  -- the first new coordinate
  have hch2 := tb_holds_slice hnr h 213 (challengeT (.n 259) (.n 260) 272) (by decide +kernel)
  rw [holds_challengeT] at hch2
  have e274 := challengeT_value hch2.1 (P2 0 (by omega)) (P2 1 (by omega))
  -- the second
  have c26 := a 20 (.const (.n 27) (word 0 0 0)) (by decide +kernel)
  have c27 := a 21 (.const (.n 28) (word 0 0 0)) (by decide +kernel)
  have c28 := a 22 (.const (.n 29) (word 0 0 0)) (by decide +kernel)
  have c29 := a 23 (.const (.n 30) (word 0 0 0)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at c26 c27 c28 c29
  have k5 := a 221 (.keccak ([.n 27, .n 27, .n 27, .n 27, .n 27, .n 28, .n 29, .n 30] ++ lyCap 259)
    (lyOuts 279) false false) (by decide +kernel)
  obtain ⟨-, P3, B3⟩ := ly_keccak k5
  have hz : (([.n 27, .n 27, .n 27, .n 27, .n 27, .n 28, .n 29, .n 30] ++ lyCap 259 : List V).map σ) =
      rateOf [] ++ capOf (lySponge σ).perm := by
    rw [List.map_append, B2, rateOf_eq_cells [] (by simp)]
    simp only [List.map_cons, List.map_nil, c26, c27, c28, c29]
    rfl
  rw [hz] at P3 B3
  have hch3 := tb_holds_slice hnr h 222 (challengeT (.n 279) (.n 280) 292) (by decide +kernel)
  rw [holds_challengeT] at hch3
  have e294 := challengeT_value hch3.1 (P3 0 (by omega)) (P3 1 (by omega))
  have hsq : ((lySponge σ).squeezeN 2).1 = [σ (.n 278), σ (.n 298)] := by
    rw [e274, e294]; rfl
  refine ⟨hreads, ?_, hsq, ?_, ?_⟩
  · -- the check
    have m239 := a 195 (.mul (.n 243) (.n 209) (.n 220)) (by decide +kernel)
    have m240 := a 196 (.mul (.n 244) (.n 243) (.n 231)) (by decide +kernel)
    have m241 := a 197 (.mul (.n 245) (.n 244) (.n 242)) (by decide +kernel)
    have c242 := a 198 (.const (.n 246) (word 0 0 0)) (by decide +kernel)
    have m243 := a 199 (.mul (.n 247) (.n 50) (.n 246)) (by decide +kernel)
    have a244 := a 200 (.add (.n 248) (.n 245) (.n 247)) (by decide +kernel)
    have m245 := a 201 (.mul (.n 249) (.n 152) (.n 163)) (by decide +kernel)
    have m246 := a 202 (.mul (.n 250) (.n 249) (.n 174)) (by decide +kernel)
    have m247 := a 203 (.mul (.n 251) (.n 250) (.n 185)) (by decide +kernel)
    have m248 := a 204 (.mul (.n 252) (.n 50) (.n 248)) (by decide +kernel)
    have a249 := a 205 (.add (.n 253) (.n 251) (.n 252)) (by decide +kernel)
    have m250 := a 206 (.mul (.n 254) (.n 95) (.n 106)) (by decide +kernel)
    have m251 := a 207 (.mul (.n 255) (.n 254) (.n 117)) (by decide +kernel)
    have m252 := a 208 (.mul (.n 256) (.n 255) (.n 128)) (by decide +kernel)
    have m253 := a 209 (.mul (.n 257) (.n 50) (.n 253)) (by decide +kernel)
    have a254 := a 210 (.add (.n 258) (.n 256) (.n 257)) (by decide +kernel)
    have q := a 211 (.assertEq (.n 84) (.n 258)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_zero] at m239 m240 m241 c242 m243 a244 m245 m246 m247 m248 a249
    simp only [Atom.Holds] at m250 m251 m252 m253 a254 q
    rw [e_add_eq_zero_iff.mp q, a254, m253, a249, m248, a244, m243, c242, m241, m240, m239, m247,
      m246, m245, m252, m251, m250,
      show σ (.n 95) = σ (.n 85) from cp 0 (by omega), show σ (.n 106) = σ (.n 96) from cp 1 (by omega),
      show σ (.n 117) = σ (.n 107) from cp 2 (by omega),
      show σ (.n 128) = σ (.n 118) from cp 3 (by omega),
      show σ (.n 152) = σ (.n 142) from cp 4 (by omega),
      show σ (.n 163) = σ (.n 153) from cp 5 (by omega),
      show σ (.n 174) = σ (.n 164) from cp 6 (by omega),
      show σ (.n 185) = σ (.n 175) from cp 7 (by omega),
      show σ (.n 209) = σ (.n 199) from cp 8 (by omega),
      show σ (.n 220) = σ (.n 210) from cp 9 (by omega),
      show σ (.n 231) = σ (.n 221) from cp 10 (by omega),
      show σ (.n 242) = σ (.n 232) from cp 11 (by omega)]
    have hc0 : lyCh σ 0 = [σ (.n 85), σ (.n 96), σ (.n 107), σ (.n 118)] := by rw [lyCh_eq]; rfl
    have hc1 : lyCh σ 1 = [σ (.n 142), σ (.n 153), σ (.n 164), σ (.n 175)] := by rw [lyCh_eq]; rfl
    have hc2 : lyCh σ 2 = [σ (.n 199), σ (.n 210), σ (.n 221), σ (.n 232)] := by rw [lyCh_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  · show (⟨capOf (permOf (rateOf [] ++ capOf (lySponge σ).perm)), []⟩ : Fs) = _
    rw [← B3]
    simp [lyCap]
  · intro t ht
    have hv : ∀ b off, Stmt.HoldsList C rd σ (lyVal t b off) True kret →
        σ (.n (b + 8)) = multilinearEval (lyCh σ t) [σ (.n 278), σ (.n 298)] ∧
          LoadHolds rd (σ (.n 16)) off (σ (.n (b + 8))) := by
      intro b off hv
      obtain ⟨e, l⟩ := ly_val hv
      refine ⟨?_, l⟩
      rw [e, cp (4 * t + 0) (by omega), cp (4 * t + 1) (by omega), cp (4 * t + 2) (by omega),
        cp (4 * t + 3) (by omega), lyCh_eq]
      rfl
    interval_cases t
    · exact hv 305 40 (tb_holds_slice hnr h 248 (lyVal 0 305 40) (by decide +kernel))
    · exact hv 314 41 (tb_holds_slice hnr h 258 (lyVal 1 314 41) (by decide +kernel))
    · exact hv 323 42 (tb_holds_slice hnr h 268 (lyVal 2 323 42) (by decide +kernel))

end Sem

end
end LeanVM.Guest.B1.Tables
