/-
  LeanVM.Guest.B1.Gkr.LayerTail

  The tail of a layer of `verify_bus_gkr` (`verify_bus_gkr_loop0`): the rounds between its first and
  last records, the twelve children read and absorbed, their check, the two new coordinates
  squeezed, and the next slot's stores.
-/

module

public import LeanVM.Guest.B1.Gkr.Layer
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData

/-!
# A layer's rounds and children (`verify_bus_gkr_loop0`)

* `ly_rounds`: `verify_bus_gkr_loop0_loop0`, then `gkr_rounds__L{2r}` at the layer index's `r = k %
  4`, then `gkr_rounds__L1` at an odd depth, run the `L = 2k + sh` rounds from the layer's first
  record;
* `ly_tail`: the twelve words at the last record's cursor are the three trees' children
  (`gkr_children`), their products check the last claim (`gkr_product_check`), and the sponge
  after them squeezes the two new coordinates (`y`'s grind of `0` bits, then a squeeze);
* `ly_stores` (`LayerStep`): the next slot's cells, cursor, values, row, position, `half` and
  `parity`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Children (`gkr_children`)

A layer reads every tree's children, tree by tree, with `fs_next` (`fsNextT`, the word then its
two rate cells) and keeps the word's copy; every four reads the sponge permutes. Child `i`'s
values start at `chB b0 i = b0 + 4i + 13⌊i/4⌋` (four values a read, a permutation's thirteen
outputs every four), its read at statement `4i + ⌊i/4⌋` of the block. -/

/-- The first value of child `i`'s read, the block's first at `b0`. -/
def chB (b0 i : ℕ) : ℕ := b0 + 4 * i + 13 * (i / 4)

/-- Child `i`'s read: `fs_next` at the cursor `cur`, `o + i` words on, its word copied. -/
def chT (cur : V) (o b0 i : ℕ) : List Stmt :=
  fsNextT cur (o + i) (chB b0 i) ++ [.atom (.copy (.n (chB b0 i + 3)) (.n (chB b0 i)))]

/-- The rate cells of children `4m .. 4m + 3`. -/
def chRate (b0 m : ℕ) : List V :=
  (List.range 4).flatMap fun i ↦ [.n (chB b0 (4 * m + i) + 1), .n (chB b0 (4 * m + i) + 2)]

/-- The words of the children `4m .. 4m + 3`. -/
def chWords (σ : Val) (b0 m : ℕ) : List E := (List.range 4).map fun i ↦ σ (.n (chB b0 (4 * m + i)))

theorem chWords_length (σ : Val) (b0 m : ℕ) : (chWords σ b0 m).length = 4 := by simp [chWords]

theorem chWords_eq (σ : Val) (b0 m : ℕ) : chWords σ b0 m = [σ (.n (chB b0 (4 * m))),
    σ (.n (chB b0 (4 * m + 1))), σ (.n (chB b0 (4 * m + 2))), σ (.n (chB b0 (4 * m + 3)))] := by
  simp [chWords, List.range_succ]

/-- The first value of child `i`'s read in `verify_bus_gkr_loop0` (at the tail cursor `σ 86`). -/
abbrev lyEv (i : ℕ) : ℕ := chB 87 i

/-- Child `i`'s read in `verify_bus_gkr_loop0`. -/
abbrev lyEvT (i : ℕ) : List Stmt := chT (.n 86) 0 87 i

/-- Child `i`'s read's first statement in `lyPre`. -/
def lyPos (i : ℕ) : ℕ := 67 + 4 * i + i / 4

theorem lyEvs_check : ∀ i < 12,
    tbStmtsEqb (lyEvT i) ((lyPre.drop (lyPos i)).take (lyEvT i).length) = true := by
  decide +kernel

/-- The rate cells of `verify_bus_gkr_loop0`'s children `4m .. 4m + 3`. -/
abbrev lyRate (m : ℕ) : List V := chRate 87 m

/-- The words of `verify_bus_gkr_loop0`'s children `4m .. 4m + 3`. -/
abbrev lyCh (σ : Val) (m : ℕ) : List E := chWords σ 87 m

theorem lyCh_length (σ : Val) (m : ℕ) : (lyCh σ m).length = 4 := chWords_length σ 87 m

theorem lyCh_eq (σ : Val) (m : ℕ) : lyCh σ m = [σ (.n (lyEv (4 * m))), σ (.n (lyEv (4 * m + 1))),
    σ (.n (lyEv (4 * m + 2))), σ (.n (lyEv (4 * m + 3)))] := chWords_eq σ 87 m

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

/-- Child `i`'s read: its word at the cursor, packed, and copied. -/
theorem ch_ev {cur : V} {o b0 i : ℕ} (h : Stmt.HoldsList C rd σ (chT cur o b0 i) True kret) :
    LoadHolds rd (σ cur) (o + i) (σ (.n (chB b0 i))) ∧
      FsPackOk σ (.n (chB b0 i)) (chB b0 i + 1) dsObserve ∧
      σ (.n (chB b0 i + 3)) = σ (.n (chB b0 i)) := by
  unfold chT at h
  rw [tb_holdsList_append_noRet (by simp [fsNextT, fsPackT]; rfl), holds_fsNextT] at h
  obtain ⟨⟨⟨hl, hp⟩, -⟩, hc⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hc
  exact ⟨hl, hp, hc⟩

/-- Child `i`'s read in `verify_bus_gkr_loop0`. -/
theorem ly_ev {i : ℕ} (h : Stmt.HoldsList C rd σ (lyEvT i) True kret) :
    LoadHolds rd (σ (.n 86)) i (σ (.n (lyEv i))) ∧
      FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve ∧ σ (.n (lyEv i + 3)) = σ (.n (lyEv i)) := by
  have := ch_ev h
  rwa [Nat.zero_add] at this

/-- The rate cells of packed words are their scalars' cells. -/
theorem ch_rate {ws : ℕ → ℕ} {n : ℕ}
    (hp : ∀ i < n, FsPackOk σ (.n (ws i)) (ws i + 1) dsObserve) :
    ((List.range n).flatMap fun i ↦ [V.n (ws i + 1), .n (ws i + 2)]).map σ =
      pendCells (((List.range n).map fun i ↦ σ (.n (ws i))).map (·, dsObserve)) := by
  have hcell : ∀ i < n, σ (.n (ws i + 1)) = (Keccak.scalarCells (σ (.n (ws i))) dsObserve).1 ∧
      σ (.n (ws i + 2)) = (Keccak.scalarCells (σ (.n (ws i))) dsObserve).2 :=
    fun i hi => Prod.ext_iff.mp (fsPackT_cells (hp i hi))
  simp only [pendCells, List.map_flatMap, List.flatMap_map, List.map_cons, List.map_nil]
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [(hcell i hi).1, (hcell i hi).2]

/-- **Four children's permutation**: their cells over the carried capacity. -/
theorem ch_perm_block {b0 m b : ℕ} {cap : List V}
    (hp : ∀ i < 4, FsPackOk σ (.n (chB b0 (4 * m + i))) (chB b0 (4 * m + i) + 1) dsObserve)
    (hk : (Atom.keccak (chRate b0 m ++ cap) (lyOuts b) false false).Holds rd σ) :
    (∀ k (hk : k < 13), σ (.n (b + k)) =
      cellsOfState (Fs.perm ⟨cap.map σ, (chWords σ b0 m).map (·, dsObserve)⟩) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (Fs.perm ⟨cap.map σ, (chWords σ b0 m).map (·, dsObserve)⟩) := by
  obtain ⟨hP, hcap⟩ := ly_keccak hk
  have hins : (chRate b0 m ++ cap).map σ =
      rateOf ((chWords σ b0 m).map (·, dsObserve)) ++ cap.map σ := by
    rw [List.map_append, chRate, ch_rate (ws := fun i ↦ chB b0 (4 * m + i)) hp,
      rateOf_eq_cells _ (by simp [chWords_length])]
    simp [chWords]
  rw [hins] at hP hcap
  exact ⟨hP, hcap⟩

/-- Four of `verify_bus_gkr_loop0`'s children's permutation. -/
theorem ly_perm_block {m b : ℕ} {cap : List V}
    (hp : ∀ i < 4, FsPackOk σ (.n (lyEv (4 * m + i))) (lyEv (4 * m + i) + 1) dsObserve)
    (hk : (Atom.keccak (lyRate m ++ cap) (lyOuts b) false false).Holds rd σ) :
    (∀ k (hk : k < 13), σ (.n (b + k)) =
      cellsOfState (Fs.perm ⟨cap.map σ, (lyCh σ m).map (·, dsObserve)⟩) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (Fs.perm ⟨cap.map σ, (lyCh σ m).map (·, dsObserve)⟩) :=
  ch_perm_block hp hk

/-- Tree `t`'s new value at the two coordinates `c0`, `c1` (`lo + c₁·(lo + hi)`), its children's
reads from `b0`, its values from `b`, stored at `slot`'s `off`. -/
def chValT (b0 c0 c1 slot t b off : ℕ) : List Stmt :=
  let e := fun i ↦ chB b0 (4 * t + i) + 3
  [.atom (.add (.n b) (.n (e 0)) (.n (e 1))), .atom (.mul (.n (b + 1)) (.n c0) (.n b)),
    .atom (.add (.n (b + 2)) (.n (e 0)) (.n (b + 1))),
    .atom (.add (.n (b + 3)) (.n (e 2)) (.n (e 3))), .atom (.mul (.n (b + 4)) (.n c0) (.n (b + 3))),
    .atom (.add (.n (b + 5)) (.n (e 2)) (.n (b + 4))),
    .atom (.add (.n (b + 6)) (.n (b + 2)) (.n (b + 5))), .atom (.mul (.n (b + 7)) (.n c1) (.n (b + 6))),
    .atom (.add (.n (b + 8)) (.n (b + 2)) (.n (b + 7))), .atom (.load (.n (b + 8)) (.n slot) off)]

/-- A tree's new value: its four children's multilinear value at the two new coordinates. -/
theorem ch_val {b0 c0 c1 slot t b off : ℕ}
    (h : Stmt.HoldsList C rd σ (chValT b0 c0 c1 slot t b off) True kret) :
    σ (.n (b + 8)) = multilinearEval [σ (.n (chB b0 (4 * t + 0) + 3)),
      σ (.n (chB b0 (4 * t + 1) + 3)), σ (.n (chB b0 (4 * t + 2) + 3)),
      σ (.n (chB b0 (4 * t + 3) + 3))] [σ (.n c0), σ (.n c1)] ∧
      LoadHolds rd (σ (.n slot)) off (σ (.n (b + 8))) := by
  simp only [chValT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, l⟩ := h
  refine ⟨?_, l⟩
  rw [e8, e7, e6, e5, e4, e3, e2, e1, e0]
  simp only [multilinearEval, List.foldl, foldPairs, List.headD]
  ring

/-- `verify_bus_gkr_loop0`'s tree `t`'s new value. -/
abbrev lyValT (t b off : ℕ) : List Stmt := chValT 87 178 191 17 t b off

theorem ly_val {t b off : ℕ} (h : Stmt.HoldsList C rd σ (lyValT t b off) True kret) :
    σ (.n (b + 8)) = multilinearEval [σ (.n (lyEv (4 * t + 0) + 3)), σ (.n (lyEv (4 * t + 1) + 3)),
      σ (.n (lyEv (4 * t + 2) + 3)), σ (.n (lyEv (4 * t + 3) + 3))]
      [σ (.n 178), σ (.n 191)] ∧ LoadHolds rd (σ (.n 17)) off (σ (.n (b + 8))) :=
  ch_val h

/-- The sponge after the twelve children, from the last record's capacity. -/
def lySponge (σ : Val) : Fs :=
  (((⟨(List.range 5).map fun k ↦ σ (.n (81 + k)), []⟩ : Fs).absorbAll (lyCh σ 0)
    dsObserve).absorbAll (lyCh σ 1) dsObserve).absorbAll (lyCh σ 2) dsObserve

/-- **The rounds of a layer**: `verify_bus_gkr_loop0_loop0` (`8·(k/4)` rounds), `gkr_rounds__L{2r}`
at `r = k % 4` from the record `8·(k/4)` on, and `gkr_rounds__L1` at an odd depth from the record
`2k` on, are the `2k + sh` rounds from the first record. -/
theorem ly_rounds (hC : CallRel.Le C (coreProgram.Rel rd)) (hGR : tb_gkr_rounds_Spec)
    (h : Stmt.HoldsList C rd σ lyPre True kret) {j k sh : ℕ} (hj : j < 2 ^ 30) (hsh : sh < 2)
    (hk : k = j + 1 - sh) (e10 : σ (.n 10) = gen ^ (2 * j)) (e7 : σ (.n 7) = gen ^ sh)
    (e53 : σ (.n 52) = gen ^ (k / 4)) (e54 : σ (.n 53) = gen ^ (k % 4))
    (h0 : TbGkrRoundsOut 0 rd (σ (.n 47)) (σ (.n 45))) :
    TbGkrRoundsOut (2 * k + sh) rd (σ (.n 47)) (σ (.n 45)) := by
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have c54 := a 39 (.const (.n 54) (word 1 0)) (by decide +kernel)
  have a55 := a 40 (.add (.n 55) (.n 54) (.n 52)) (by decide +kernel)
  have c56 := a 41 (.const (.n 56) (word 1 0)) (by decide +kernel)
  have m57 := a 43 (.mul (.n 57) (.n 52) (.n 52)) (by decide +kernel)
  have m58 := a 44 (.mul (.n 58) (.n 57) (.n 57)) (by decide +kernel)
  have m59 := a 45 (.mul (.n 59) (.n 58) (.n 58)) (by decide +kernel)
  have m60 := a 46 (.mul (.n 60) (.n 59) (.n 59)) (by decide +kernel)
  have m61 := a 47 (.mul (.n 61) (.n 60) (.n 59)) (by decide +kernel)
  have m62 := a 48 (.mul (.n 62) (.n 61) (.n 61)) (by decide +kernel)
  have m63 := a 49 (.mul (.n 63) (.n 62) (.n 59)) (by decide +kernel)
  have m64 := a 50 (.mul (.n 64) (.n 47) (.n 63)) (by decide +kernel)
  have m65 := a 51 (.mul (.n 65) (.n 45) (.n 59)) (by decide +kernel)
  have c67 := a 53 (.const (.n 67) (word 1 0)) (by decide +kernel)
  have a68 := a 54 (.add (.n 68) (.n 7) (.n 67)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at c54 a55 c56 m57 m58 m59 m60 m61 m62 m63 m64 m65 c67 a68
  obtain ⟨-, hc36⟩ := tb_holds_callIf hnr h 42 (.n 55) name% «verify_bus_gkr_loop0_loop0» [.n 56,
      .n 52, .n 47, .n 45, .n 4]
    (by decide +kernel)
  simp only [List.map_cons, List.map_nil, c56] at hc36
  have R8 := l29_loop (h := k / 4) e53 (by omega)
    (fun hne => hC _ _ _ (hc36 (by rw [a55, c54]; exact hne))) h0
  have R2 : TbGkrRoundsOut (2 * k) rd (σ (.n 47)) (σ (.n 45)) := by
    obtain ⟨i, hi, hx, hcall⟩ := tb_holds_dispatch hnr h 52 (.n 53)
      ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"] [.n 64, .n 65, .n 4]
      [.n 66] (by decide +kernel)
    simp only [List.length_cons, List.length_nil] at hi
    have hij : k % 4 = i := by
      rw [e54, ← gen_pow_eq_ofK] at hx
      exact gen_pow_inj (by omega) (by omega) hx
    have e59 : σ (.n 59) = gen ^ (8 * (k / 4)) := by
      rw [m59, m58, m57, e53]; ring
    have e63 : σ (.n 63) = gen ^ (7 * (8 * (k / 4))) := by
      rw [m63, m62, m61, m60, e59]; ring
    rw [show 2 * k = 8 * (k / 4) + 2 * i by omega]
    simp only [List.map_cons, List.map_nil] at hcall
    rw [m64, m65, e63, e59] at hcall
    interval_cases i
    · simpa using R8
    · exact gkrRoundsOut_append R8 (hGR 2 (by decide) rd _ _ _ _ (hC _ _ _ hcall))
    · exact gkrRoundsOut_append R8 (hGR 4 (by decide) rd _ _ _ _ (hC _ _ _ hcall))
    · exact gkrRoundsOut_append R8 (hGR 6 (by decide) rd _ _ _ _ (hC _ _ _ hcall))
  rcases (by omega : sh = 0 ∨ sh = 1) with rfl | rfl
  · simpa using R2
  · have hi := tb_holds_slice hnr h 55 [.ite (.n 68) [] [.atom (.mul (.n 69) (.n 10) (.n 10)),
      .atom (.mul (.n 70) (.n 69) (.n 10)), .atom (.mul (.n 71) (.n 70) (.n 70)),
      .atom (.mul (.n 72) (.n 71) (.n 10)), .atom (.mul (.n 73) (.n 47) (.n 72)),
      .atom (.mul (.n 74) (.n 45) (.n 10)), .call "gkr_rounds__L1" [.n 73, .n 74, .n 4] [.n 75]]]
      (by decide +kernel)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil] at hi
    obtain ⟨-, -, hodd⟩ := hi
    have hne : σ (.n 68) ≠ 0 := by
      rw [a68, c67, e7]
      intro h0'
      have := gen_pow_inj (by omega) (by omega) ((e_add_eq_zero_iff.mp h0').trans (pow_zero gen).symm)
      omega
    obtain ⟨m69, m70, m71, m72, m73, m74, hL1⟩ := hodd hne
    have := hGR 1 (by decide) rd _ _ _ _ (hC _ _ _ hL1)
    have e72 : σ (.n 72) = gen ^ (7 * (2 * k)) := by
      rw [m72, m71, m70, m69, e10, show 2 * j = 2 * k by omega]; ring
    rw [m73, m74, e72, e10, show 2 * j = 2 * k by omega] at this
    exact gkrRoundsOut_append R2 this

/-- **The children of a layer**: the twelve words at the last record's cursor, their products
checking the last claim at the combiner, the sponge after them squeezing the two new
coordinates, and the three trees' values at them. -/
theorem ly_tail (h : Stmt.HoldsList C rd σ lyPre True kret) :
    TbReadsAt rd (σ (.n 86)) (lyCh σ 0 ++ (lyCh σ 1 ++ lyCh σ 2)) ∧
      σ (.n 161) = polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 29)) ∧
      ((lySponge σ).squeezeN 2).1 = [σ (.n 178), σ (.n 191)] ∧
      ((lySponge σ).squeezeN 2).2 = ⟨(List.range 5).map fun k ↦ σ (.n (199 + k)), []⟩ ∧
      (∀ t < 3, σ (.n (214 + 9 * t)) = multilinearEval (lyCh σ t) [σ (.n 178), σ (.n 191)] ∧
        LoadHolds rd (σ (.n 17)) (19 + t) (σ (.n (214 + 9 * t)))) := by
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have EV : ∀ i < 12, _ := fun i hi => ly_ev (tb_holds_slice hnr h (lyPos i) (lyEvT i)
    (lyEvs_check i hi))
  have cp : ∀ i < 12, σ (.n (lyEv i + 3)) = σ (.n (lyEv i)) := fun i hi => (EV i hi).2.2
  have hp : ∀ m < 3, ∀ i < 4,
      FsPackOk σ (.n (lyEv (4 * m + i))) (lyEv (4 * m + i) + 1) dsObserve :=
    fun m hm i hi => (EV (4 * m + i) (by omega)).2.1
  -- the reads
  have hreads : TbReadsAt rd (σ (.n 86)) (lyCh σ 0 ++ (lyCh σ 1 ++ lyCh σ 2)) := by
    intro k hk
    have hk12 : k < 12 := by simpa [lyCh_length] using hk
    convert (EV k hk12).1 using 1
    simp only [lyCh_eq]
    interval_cases k <;> rfl
  -- the sponge
  have hS0 : ((List.range 5).map fun k ↦ V.n (81 + k)).map σ =
      (List.range 5).map fun k ↦ σ (.n (81 + k)) := by simp
  have A0 : (⟨(List.range 5).map fun k ↦ σ (.n (81 + k)), []⟩ : Fs).absorbAll (lyCh σ 0)
      dsObserve = ⟨(List.range 5).map fun k ↦ σ (.n (81 + k)), (lyCh σ 0).map (·, dsObserve)⟩ := by
    rw [absorbAll_short _ _ _ (by simp [lyCh_length])]
    simp
  have k1 := a 83 (.keccak (lyRate 0 ++ (List.range 5).map fun k ↦ .n (81 + k)) (lyOuts 103)
    false false) (by decide +kernel)
  obtain ⟨-, B0⟩ := ly_perm_block (hp 0 (by omega)) k1
  rw [hS0] at B0
  have k2 := a 100 (.keccak (lyRate 1 ++ lyCap 103) (lyOuts 132) false false) (by decide +kernel)
  obtain ⟨-, B1⟩ := ly_perm_block (hp 1 (by omega)) k2
  have k3 := a 135 (.keccak (lyRate 2 ++ lyCap 132) (lyOuts 178) false false) (by decide +kernel)
  obtain ⟨P2, B2⟩ := ly_perm_block (hp 2 (by omega)) k3
  have hA : lySponge σ = ⟨(lyCap 132).map σ, (lyCh σ 2).map (·, dsObserve)⟩ := by
    unfold lySponge
    rw [A0, tb_absorbAll_full _ (by simp [lyCh_length]) _ (lyCh_length σ 1), ← B0,
      tb_absorbAll_full _ (by simp [lyCh_length]) _ (lyCh_length σ 2), ← B1]
  rw [← hA] at P2 B2
  -- the first new coordinate: y's grind of `0` bits is the permutation of the waiting children
  have e180 : σ (.n 178) = challengeOf (lySponge σ).perm := by
    rw [P2 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
  -- the second
  have c25 := a 15 (.const (.n 25) (word 0 0)) (by decide +kernel)
  have c26 := a 16 (.const (.n 26) (word 0 0)) (by decide +kernel)
  have c27 := a 17 (.const (.n 27) (word 0 0)) (by decide +kernel)
  have c28 := a 18 (.const (.n 28) (word 0 0)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at c25 c26 c27 c28
  have k4 := a 136 (.keccak ([.n 25, .n 25, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28] ++ lyCap 178)
    (lyOuts 191) false false) (by decide +kernel)
  obtain ⟨P3, B3⟩ := ly_keccak k4
  rw [ly_zero_rate c25 c26 c27 c28, B2] at P3 B3
  have e194 : σ (.n 191) = challengeOf (permOf (rateOf [] ++ capOf (lySponge σ).perm)) := by
    rw [P3 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
  have hsq : ((lySponge σ).squeezeN 2).1 = [σ (.n 178), σ (.n 191)] := by
    rw [e180, e194]; rfl
  refine ⟨hreads, ?_, hsq, ?_, ?_⟩
  · -- the check (`gkr_product_check`, Horner in the combiner from the top tree)
    have l150 := a 117 (.load (.n 161) (.n 80) 6) (by decide +kernel)
    have m151 := a 118 (.mul (.n 162) (.n 148) (.n 152)) (by decide +kernel)
    have m152 := a 119 (.mul (.n 163) (.n 162) (.n 156)) (by decide +kernel)
    have m153 := a 120 (.mul (.n 164) (.n 163) (.n 160)) (by decide +kernel)
    have c154 := a 121 (.const (.n 165) (word 0 0)) (by decide +kernel)
    have m155 := a 122 (.mul (.n 166) (.n 29) (.n 165)) (by decide +kernel)
    have a156 := a 123 (.add (.n 167) (.n 164) (.n 166)) (by decide +kernel)
    have m157 := a 124 (.mul (.n 168) (.n 119) (.n 123)) (by decide +kernel)
    have m158 := a 125 (.mul (.n 169) (.n 168) (.n 127)) (by decide +kernel)
    have m159 := a 126 (.mul (.n 170) (.n 169) (.n 131)) (by decide +kernel)
    have m160 := a 127 (.mul (.n 171) (.n 29) (.n 167)) (by decide +kernel)
    have a161 := a 128 (.add (.n 172) (.n 170) (.n 171)) (by decide +kernel)
    have m162 := a 129 (.mul (.n 173) (.n 90) (.n 94)) (by decide +kernel)
    have m163 := a 130 (.mul (.n 174) (.n 173) (.n 98)) (by decide +kernel)
    have m164 := a 131 (.mul (.n 175) (.n 174) (.n 102)) (by decide +kernel)
    have m165 := a 132 (.mul (.n 176) (.n 29) (.n 172)) (by decide +kernel)
    have a166 := a 133 (.add (.n 177) (.n 175) (.n 176)) (by decide +kernel)
    have q := a 134 (.assertEq (.n 161) (.n 177)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_zero] at m151 m152 m153 c154 m155 a156 m157 m158 m159 m160 a161
    simp only [Atom.Holds] at m162 m163 m164 m165 a166 q
    rw [e_add_eq_zero_iff.mp q, a166, m165, a161, m160, a156, m155, c154, m153, m152, m151, m159,
      m158, m157, m164, m163, m162,
      show σ (.n 90) = σ (.n 87) from cp 0 (by omega), show σ (.n 94) = σ (.n 91) from cp 1 (by omega),
      show σ (.n 98) = σ (.n 95) from cp 2 (by omega),
      show σ (.n 102) = σ (.n 99) from cp 3 (by omega),
      show σ (.n 119) = σ (.n 116) from cp 4 (by omega),
      show σ (.n 123) = σ (.n 120) from cp 5 (by omega),
      show σ (.n 127) = σ (.n 124) from cp 6 (by omega),
      show σ (.n 131) = σ (.n 128) from cp 7 (by omega),
      show σ (.n 148) = σ (.n 145) from cp 8 (by omega),
      show σ (.n 152) = σ (.n 149) from cp 9 (by omega),
      show σ (.n 156) = σ (.n 153) from cp 10 (by omega),
      show σ (.n 160) = σ (.n 157) from cp 11 (by omega)]
    have hc0 : lyCh σ 0 = [σ (.n 87), σ (.n 91), σ (.n 95), σ (.n 99)] := by rw [lyCh_eq]; rfl
    have hc1 : lyCh σ 1 = [σ (.n 116), σ (.n 120), σ (.n 124), σ (.n 128)] := by rw [lyCh_eq]; rfl
    have hc2 : lyCh σ 2 = [σ (.n 145), σ (.n 149), σ (.n 153), σ (.n 157)] := by rw [lyCh_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  · show (⟨capOf (permOf (rateOf [] ++ capOf (lySponge σ).perm)), []⟩ : Fs) = _
    rw [← B3]
    simp [lyCap]
  · intro t ht
    interval_cases t
    · have hs := tb_holds_slice hnr h 147 (lyValT 0 206 19) (by decide +kernel)
      obtain ⟨ev, l⟩ := ly_val hs
      exact ⟨by rw [ev, lyCh_eq, cp 0 (by omega), cp 1 (by omega), cp 2 (by omega),
        cp 3 (by omega)], l⟩
    · have hs := tb_holds_slice hnr h 157 (lyValT 1 215 20) (by decide +kernel)
      obtain ⟨ev, l⟩ := ly_val hs
      exact ⟨by rw [ev, lyCh_eq, cp 4 (by omega), cp 5 (by omega), cp 6 (by omega),
        cp 7 (by omega)], l⟩
    · have hs := tb_holds_slice hnr h 167 (lyValT 2 224 21) (by decide +kernel)
      obtain ⟨ev, l⟩ := ly_val hs
      exact ⟨by rw [ev, lyCh_eq, cp 8 (by omega), cp 9 (by omega), cp 10 (by omega),
        cp 11 (by omega)], l⟩

end Sem

end
end LeanVM.Guest.B1.Tables
