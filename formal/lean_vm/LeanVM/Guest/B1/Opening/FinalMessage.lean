/-
  LeanVM.Guest.B1.Opening.FinalMessage

  B1 for `opening_final_message`: one generic argument over the message's length `4m`.
-/

module

public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `opening_final_message` (G:1246-1265, TRIAGE #37)

Its body at `n = 4m` words (`ofmBody m`): the capacity copied into `9 .. 13`, the waiting `w0`,
`w1` packed (`fsPackT` from `14`, `23`); message word `i` read, packed and stored
(`ofmNext i (msgV i)`, `msgV i = 12 + 53·((i+2)/4) + 10·((i+2)%4)`), the queue permuted after
every fourth waiting scalar (`ofmFirst`, `ofmBlock j` for block `j + 1`, its outputs at
`52 + 53 j`); the last two words, the nonce at `F + 20` (`F = 12 + 53 m`, packed with the tag
`dsPowNonce`), the zero run, the final permutation into `F + 32`, the returns.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Message word `i`: read, packed (cells `b + 7`, `b + 9`) and stored at `out[i]`. -/
def ofmNext (i b : ℕ) : List Stmt := fsNextT (.n 7) i b ++ [.atom (.load (.n b) (.n 8) i)]

/-- The rate cells of a block of four words from `b`. -/
def ofmRate (b : ℕ) : List V := [.n (b + 7), .n (b + 9), .n (b + 17), .n (b + 19), .n (b + 27),
  .n (b + 29), .n (b + 37), .n (b + 39)]

/-- The capacity cells of a permutation's outputs at `o`. -/
def capIns (o : ℕ) : List V := [.n (o + 8), .n (o + 9), .n (o + 10), .n (o + 11), .n (o + 12)]

/-- Thirteen consecutive values. -/
def ofmRun (b : ℕ) : List V := (List.range 13).map fun i ↦ .n (b + i)

/-- Block `j + 1` (`j + 1 < m`): words `4j + 2 .. 4j + 5`, then the permutation. -/
def ofmBlock (j : ℕ) : List Stmt :=
  ofmNext (4 * j + 2) (65 + 53 * j) ++ ofmNext (4 * j + 3) (75 + 53 * j) ++
    ofmNext (4 * j + 4) (85 + 53 * j) ++ ofmNext (4 * j + 5) (95 + 53 * j) ++
    [keccakA (ofmRate (65 + 53 * j) ++ capIns (52 + 53 * j)) (ofmRun (105 + 53 * j))]

/-- The expansion of `opening_final_message` at `4m` words, `m ≥ 1`. -/
def ofmBody (m : ℕ) : List Stmt :=
  [.atom (.copy (.n 9) (.n 0)), .atom (.copy (.n 10) (.n 1)), .atom (.copy (.n 11) (.n 2)),
    .atom (.copy (.n 12) (.n 3)), .atom (.copy (.n 13) (.n 4))] ++
  fsPackT (.n 5) 14 dsObserve ++ fsPackT (.n 6) 23 dsObserve ++
  ofmNext 0 32 ++ ofmNext 1 42 ++
  [keccakA [.n 20, .n 22, .n 29, .n 31, .n 39, .n 41, .n 49, .n 51, .n 9, .n 10, .n 11, .n 12,
    .n 13] (ofmRun 52)] ++
  ((List.range (m - 1)).map ofmBlock).flatten ++
  ofmNext (4 * m - 2) (12 + 53 * m) ++ ofmNext (4 * m - 1) (22 + 53 * m) ++
  [.atom (.load (.n (32 + 53 * m)) (.n 7) (4 * m))] ++
  fsPackT (.n (32 + 53 * m)) (33 + 53 * m) dsPowNonce ++
  [.atom (.const (.n (42 + 53 * m)) (word 0 0 0)), .atom (.const (.n (43 + 53 * m)) (word 0 0 0)),
    keccakA ([.n (19 + 53 * m), .n (21 + 53 * m), .n (29 + 53 * m), .n (31 + 53 * m),
      .n (39 + 53 * m), .n (41 + 53 * m), .n (42 + 53 * m), .n (43 + 53 * m)] ++ capIns (53 * m - 1))
      (ofmRun (44 + 53 * m)),
    .atom (.copy (.n (57 + 53 * m)) (.n (44 + 53 * m))),
    .atom (.copy (.n (58 + 53 * m)) (.n (52 + 53 * m))),
    .atom (.copy (.n (59 + 53 * m)) (.n (53 + 53 * m))),
    .atom (.copy (.n (60 + 53 * m)) (.n (54 + 53 * m))),
    .atom (.copy (.n (61 + 53 * m)) (.n (55 + 53 * m))),
    .atom (.copy (.n (62 + 53 * m)) (.n (56 + 53 * m))),
    .atom (.const (.n (63 + 53 * m)) (word (2 ^ (4 * m)) 0 0)),
    .atom (.mul (.n (64 + 53 * m)) (.n 7) (.n (63 + 53 * m))),
    .atom (.const (.n (65 + 53 * m)) (word 2 0 0)),
    .atom (.mul (.n (66 + 53 * m)) (.n (64 + 53 * m)) (.n (65 + 53 * m))),
    .atom (.copy (.n (67 + 53 * m)) (.n (32 + 53 * m))),
    .ret [.n (57 + 53 * m), .n (58 + 53 * m), .n (59 + 53 * m), .n (60 + 53 * m),
      .n (61 + 53 * m), .n (62 + 53 * m), .n (66 + 53 * m), .n (67 + 53 * m)]]

/-! ## The sponge of the message -/

theorem absorbAll_append' (s : Fs) (xs ys : List E) (t : ℕ) :
    s.absorbAll (xs ++ ys) t = (s.absorbAll xs t).absorbAll ys t := by
  simp [Fs.absorbAll, List.foldl_append]

/-- Four words onto two waiting: the queue fills, permutes, and two wait again. -/
theorem absorbAll_four (c : List E) (a b : E × ℕ) (x0 x1 x2 x3 : E) :
    (⟨c, [a, b]⟩ : Fs).absorbAll [x0, x1, x2, x3] dsObserve =
      ⟨capOf (⟨c, [a, b, (x0, dsObserve), (x1, dsObserve)]⟩ : Fs).perm,
        [(x2, dsObserve), (x3, dsObserve)]⟩ := by
  simp [Fs.absorbAll, Fs.absorb, rateScalars]

/-- The states the message's permutations write. -/
def ofmQ (cap : List E) (w0 w1 : E) (ms : ℕ → E) : ℕ → KeccakState
  | 0 => (⟨cap, [(w0, dsObserve), (w1, dsObserve), (ms 0, dsObserve), (ms 1, dsObserve)]⟩ : Fs).perm
  | j + 1 => (⟨capOf (ofmQ cap w0 w1 ms j), [(ms (4 * j + 2), dsObserve), (ms (4 * j + 3), dsObserve),
      (ms (4 * j + 4), dsObserve), (ms (4 * j + 5), dsObserve)]⟩ : Fs).perm

theorem ofm_absorb (cap : List E) (w0 w1 : E) (ms : ℕ → E) :
    ∀ m, (⟨cap, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll
        ((List.range (4 * (m + 1))).map ms) dsObserve =
      ⟨capOf (ofmQ cap w0 w1 ms m), [(ms (4 * m + 2), dsObserve), (ms (4 * m + 3), dsObserve)]⟩
  | 0 => by
    rw [show (List.range (4 * (0 + 1))).map ms = [ms 0, ms 1, ms 2, ms 3] by simp [List.range_succ],
      absorbAll_four]
    rfl
  | m + 1 => by
    rw [show 4 * (m + 1 + 1) = 4 * (m + 1) + 4 by ring, List.range_add, List.map_append,
      absorbAll_append', ofm_absorb cap w0 w1 ms m]
    rw [show (List.map (fun x ↦ 4 * (m + 1) + x) (List.range 4)).map ms =
      [ms (4 * m + 4), ms (4 * m + 5), ms (4 * m + 6), ms (4 * m + 7)] by
        simp [List.range_succ]; ring_nf; simp,
      absorbAll_four]
    simp only [ofmQ]
    rw [show 4 * (m + 1) + 2 = 4 * m + 6 by ring, show 4 * (m + 1) + 3 = 4 * m + 7 by ring]

/-- Where message word `i` sits. -/
def msgV (i : ℕ) : ℕ := 12 + 53 * ((i + 2) / 4) + 10 * ((i + 2) % 4)

theorem msgV_block (j t : ℕ) (ht : t < 4) : msgV (4 * j + 2 + t) = 65 + 53 * j + 10 * t := by
  unfold msgV
  rw [show (4 * j + 2 + t + 2) / 4 = j + 1 by omega, show (4 * j + 2 + t + 2) % 4 = t by omega]
  ring

/-- What `ofmNext` asks. -/
theorem holds_ofmNext (i b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (ofmNext i b) next kret ↔
      (LoadHolds rd (σ (.n 7)) i (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve ∧
        LoadHolds rd (σ (.n 8)) i (σ (.n b))) ∧ next := by
  rw [ofmNext, holdsList_append, holds_fsNextT]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  tauto

/-- What block `j + 1` asks. -/
theorem holds_ofmBlock (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (ofmBlock j) True kret ↔
      (∀ t < 4, LoadHolds rd (σ (.n 7)) (4 * j + 2 + t) (σ (.n (65 + 53 * j + 10 * t))) ∧
        FsPackOk σ (.n (65 + 53 * j + 10 * t)) (65 + 53 * j + 10 * t + 1) dsObserve ∧
        LoadHolds rd (σ (.n 8)) (4 * j + 2 + t) (σ (.n (65 + 53 * j + 10 * t)))) ∧
      (Atom.keccak (ofmRate (65 + 53 * j) ++ capIns (52 + 53 * j)) (ofmRun (105 + 53 * j))
        false false).Holds rd σ := by
  simp only [ofmBlock, holdsList_append, holds_ofmNext, keccakA, Stmt.HoldsList, Stmt.Holds,
    and_true]
  constructor
  · rintro ⟨h0, h1, h2, h3, hk⟩
    refine ⟨fun t ht => ?_, hk⟩
    interval_cases t
    · simpa using h0
    · simpa [show 4 * j + 2 + 1 = 4 * j + 3 by ring, show 65 + 53 * j + 10 * 1 = 75 + 53 * j by ring]
        using h1
    · simpa [show 4 * j + 2 + 2 = 4 * j + 4 by ring, show 65 + 53 * j + 10 * 2 = 85 + 53 * j by ring]
        using h2
    · simpa [show 4 * j + 2 + 3 = 4 * j + 5 by ring, show 65 + 53 * j + 10 * 3 = 95 + 53 * j by ring]
        using h3
  · rintro ⟨h, hk⟩
    refine ⟨by simpa using h 0 (by omega), ?_, ?_, ?_, hk⟩
    · simpa [show 4 * j + 2 + 1 = 4 * j + 3 by ring, show 65 + 53 * j + 10 * 1 = 75 + 53 * j by ring]
        using h 1 (by omega)
    · simpa [show 4 * j + 2 + 2 = 4 * j + 4 by ring, show 65 + 53 * j + 10 * 2 = 85 + 53 * j by ring]
        using h 2 (by omega)
    · simpa [show 4 * j + 2 + 3 = 4 * j + 5 by ring, show 65 + 53 * j + 10 * 3 = 95 + 53 * j by ring]
        using h 3 (by omega)

/-- A `KECCAK` atom writing thirteen consecutive values. -/
theorem keccak_ofmRun {ins : List V} {b : ℕ}
    (h : (Atom.keccak ins (ofmRun b) false false).Holds rd σ) :
    AllCanonical (ins.map σ) ∧
      ∀ c : Fin 13, σ (.n (b + c.val)) = cellsOfState (permOf (ins.map σ)) false c := by
  obtain ⟨-, -, hcan, hout⟩ := keccakA_perm h
  refine ⟨hcan, fun c => ?_⟩
  have := outs_eq hout c (by simp [ofmRun])
  simpa [ofmRun] using this

/-- The nine parameters. -/
abbrev ofmParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8]

/-- Four packed waiting scalars and a capacity are a sponge's permutation input. -/
theorem perm_four {x0 x1 x2 x3 c0 c1 c2 c3 c4 : E} {a0 a1 a2 a3 b0 b1 b2 b3 : E} {cap : List E}
    (h0 : (a0, b0) = Keccak.scalarCells x0 dsObserve) (h1 : (a1, b1) = Keccak.scalarCells x1 dsObserve)
    (h2 : (a2, b2) = Keccak.scalarCells x2 dsObserve) (h3 : (a3, b3) = Keccak.scalarCells x3 dsObserve)
    (hc : cap = [c0, c1, c2, c3, c4]) :
    permOf [a0, b0, a1, b1, a2, b2, a3, b3, c0, c1, c2, c3, c4] =
      (⟨cap, [(x0, dsObserve), (x1, dsObserve), (x2, dsObserve), (x3, dsObserve)]⟩ : Fs).perm := by
  rw [perm_eq_cells _ (by simp)]
  subst hc
  simp only [pendCells, List.flatMap_cons, List.flatMap_nil, ← h0, ← h1, ← h2, ← h3]
  rfl

/-- **`opening_final_message` at `4m` words is sound.** -/
theorem ofm_sound {name : String} {f : Fn} (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 8)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = ofmParams)
    (hbody : f.body = ofmBody m) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningOpeningFinalMessage (4 * m) rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, ofmBody] at h
  simp only [holdsList_append, holdsList_range_flatten (m - 1) ofmBlock (fun _ => rfl),
    holds_ofmBlock, holds_ofmNext, holds_fsPackT, keccakA, Stmt.HoldsList, Stmt.Holds,
    List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, h9, h10, h11, h12, h13, hp0, hp1, ⟨l0, q0, s0⟩, ⟨l1, q1, s1⟩, hK0, hblocks,
    ⟨lf0, qf0, sf0⟩, ⟨lf1, qf1, sf1⟩, lN, hpN, z42, z43, hKF, c57, c58, c59, c60, c61, c62, k63,
    m64, k65, m66, c67, hret⟩ := h
  subst hp
  have h9 : σ (.n 9) = σ (.n 0) := h9
  have h10 : σ (.n 10) = σ (.n 1) := h10
  have h11 : σ (.n 11) = σ (.n 2) := h11
  have h12 : σ (.n 12) = σ (.n 3) := h12
  have h13 : σ (.n 13) = σ (.n 4) := h13
  have z42 : σ (.n (42 + 53 * m)) = 0 := by rw [← word_zero]; exact z42
  have z43 : σ (.n (43 + 53 * m)) = 0 := by rw [← word_zero]; exact z43
  have lN : LoadHolds rd (σ (.n 7)) (4 * m) (σ (.n (32 + 53 * m))) := lN
  set cap := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] with hcap
  let ms : ℕ → E := fun i ↦ σ (.n (msgV i))
  have hms : ∀ j t, t < 4 → ms (4 * j + 2 + t) = σ (.n (65 + 53 * j + 10 * t)) := fun j t ht ↦ by
    show σ (.n (msgV _)) = _
    rw [msgV_block j t ht]
  set Q := ofmQ cap (σ (.n 5)) (σ (.n 6)) ms with hQ
  obtain ⟨hcan0, hout0⟩ := keccak_ofmRun hK0
  have hQ0 : ∀ c : Fin 13, σ (.n (52 + c.val)) = cellsOfState (Q 0) false c := by
    intro c
    rw [hout0 c]
    refine congrArg (fun S ↦ cellsOfState S false c) ?_
    have e20 : (σ (.n 20), σ (.n 22)) = Keccak.scalarCells (σ (.n 5)) dsObserve :=
      fsPackT_cells hp0 (hcan0 (σ (.n 20)) (by simp))
    have e29 : (σ (.n 29), σ (.n 31)) = Keccak.scalarCells (σ (.n 6)) dsObserve :=
      fsPackT_cells hp1 (hcan0 (σ (.n 29)) (by simp))
    have e39 : (σ (.n 39), σ (.n 41)) = Keccak.scalarCells (ms 0) dsObserve :=
      fsPackT_cells q0 (hcan0 (σ (.n 39)) (by simp))
    have e49 : (σ (.n 49), σ (.n 51)) = Keccak.scalarCells (ms 1) dsObserve :=
      fsPackT_cells q1 (hcan0 (σ (.n 49)) (by simp))
    simp only [List.map_cons, List.map_nil, h9, h10, h11, h12, h13]
    exact perm_four e20 e29 e39 e49 hcap
  have hQs : ∀ j, j < m → ∀ c : Fin 13, σ (.n (52 + 53 * j + c.val)) = cellsOfState (Q j) false c := by
    intro j
    induction j with
    | zero => intro _ c; simpa using hQ0 c
    | succ j ih =>
      intro hj c
      obtain ⟨hb, hK⟩ := hblocks j (by omega)
      obtain ⟨hcan, hout⟩ := keccak_ofmRun hK
      rw [show 52 + 53 * (j + 1) + c.val = 105 + 53 * j + c.val by ring, hout c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      have ep : ∀ t, t < 4 → (σ (.n (65 + 53 * j + 10 * t + 7)), σ (.n (65 + 53 * j + 10 * t + 9))) =
          Keccak.scalarCells (ms (4 * j + 2 + t)) dsObserve := fun t ht ↦ by
        rw [hms j t ht]
        exact fsPackT_cells (hb t ht).2.1 (hcan _ (by
          interval_cases t <;> simp [ofmRate, capIns]))
      have e0 := ep 0 (by omega)
      have e1 := ep 1 (by omega)
      have e2 := ep 2 (by omega)
      have e3 := ep 3 (by omega)
      simp only [Nat.add_zero, Nat.mul_zero, Nat.mul_one] at e0 e1 e2 e3
      have i8 : σ (.n (52 + 53 * j + 8)) = cellsOfState (Q j) false 8 := ih (by omega) 8
      have i9 : σ (.n (52 + 53 * j + 9)) = cellsOfState (Q j) false 9 := ih (by omega) 9
      have i10 : σ (.n (52 + 53 * j + 10)) = cellsOfState (Q j) false 10 := ih (by omega) 10
      have i11 : σ (.n (52 + 53 * j + 11)) = cellsOfState (Q j) false 11 := ih (by omega) 11
      have i12 : σ (.n (52 + 53 * j + 12)) = cellsOfState (Q j) false 12 := ih (by omega) 12
      simp only [ofmRate, capIns, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
        i8, i9, i10, i11, i12]
      rw [hQ, ofmQ, ← hQ]
      rw [show 4 * j + 3 = 4 * j + 2 + 1 by ring, show 4 * j + 4 = 4 * j + 2 + 2 by ring,
        show 4 * j + 5 = 4 * j + 2 + 3 by ring]
      refine perm_four e0 ?_ ?_ ?_ rfl
      · rw [← e1]
      · rw [← e2]
      · rw [← e3]
  -- the final permutation
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmsF0 : ms (4 * (m' + 1) - 2) = σ (.n (12 + 53 * (m' + 1))) := by
    rw [show 4 * (m' + 1) - 2 = 4 * m' + 2 + 0 by omega, hms m' 0 (by omega)]
    congr 2; ring
  have hmsF1 : ms (4 * (m' + 1) - 1) = σ (.n (22 + 53 * (m' + 1))) := by
    rw [show 4 * (m' + 1) - 1 = 4 * m' + 2 + 1 by omega, hms m' 1 (by omega)]
    congr 2; ring
  set nonce := σ (.n (32 + 53 * (m' + 1)))
  let msl := (List.range (4 * (m' + 1))).map ms
  have hs : ((⟨cap, [(σ (.n 5), dsObserve), (σ (.n 6), dsObserve)]⟩ : Fs).absorbAll msl
      dsObserve).absorb nonce dsPowNonce =
      ⟨capOf (Q m'), [(ms (4 * m' + 2), dsObserve), (ms (4 * m' + 3), dsObserve),
        (nonce, dsPowNonce)]⟩ := by
    simp only [msl]
    rw [ofm_absorb]
    simp [Fs.absorb, rateScalars]
    try rfl
  obtain ⟨hcanF, houtF⟩ := keccak_ofmRun hKF
  have eF0 : (σ (.n (19 + 53 * (m' + 1))), σ (.n (21 + 53 * (m' + 1)))) =
      Keccak.scalarCells (ms (4 * m' + 2)) dsObserve := by
    rw [show 4 * m' + 2 = 4 * (m' + 1) - 2 by omega, hmsF0]
    have hc : IsCanonical128 (σ (.n (12 + 53 * (m' + 1) + 1 + 6))) := by
      rw [show 12 + 53 * (m' + 1) + 1 + 6 = 19 + 53 * (m' + 1) by ring]; exact hcanF _ (by simp)
    have := fsPackT_cells qf0 hc
    rwa [show 12 + 53 * (m' + 1) + 1 + 6 = 19 + 53 * (m' + 1) by ring,
      show 12 + 53 * (m' + 1) + 1 + 8 = 21 + 53 * (m' + 1) by ring] at this
  have eF1 : (σ (.n (29 + 53 * (m' + 1))), σ (.n (31 + 53 * (m' + 1)))) =
      Keccak.scalarCells (ms (4 * m' + 3)) dsObserve := by
    rw [show 4 * m' + 3 = 4 * (m' + 1) - 1 by omega, hmsF1]
    have hc : IsCanonical128 (σ (.n (22 + 53 * (m' + 1) + 1 + 6))) := by
      rw [show 22 + 53 * (m' + 1) + 1 + 6 = 29 + 53 * (m' + 1) by ring]; exact hcanF _ (by simp)
    have := fsPackT_cells qf1 hc
    rwa [show 22 + 53 * (m' + 1) + 1 + 6 = 29 + 53 * (m' + 1) by ring,
      show 22 + 53 * (m' + 1) + 1 + 8 = 31 + 53 * (m' + 1) by ring] at this
  have eFN : (σ (.n (39 + 53 * (m' + 1))), σ (.n (41 + 53 * (m' + 1)))) =
      Keccak.scalarCells nonce dsPowNonce := by
    have hc : IsCanonical128 (σ (.n (33 + 53 * (m' + 1) + 6))) := by
      rw [show 33 + 53 * (m' + 1) + 6 = 39 + 53 * (m' + 1) by ring]; exact hcanF _ (by simp)
    have := fsPackT_cells hpN hc
    rwa [show 33 + 53 * (m' + 1) + 6 = 39 + 53 * (m' + 1) by ring,
      show 33 + 53 * (m' + 1) + 8 = 41 + 53 * (m' + 1) by ring] at this
  have hSF : permOf ((([.n (19 + 53 * (m' + 1)), .n (21 + 53 * (m' + 1)), .n (29 + 53 * (m' + 1)),
      .n (31 + 53 * (m' + 1)), .n (39 + 53 * (m' + 1)), .n (41 + 53 * (m' + 1)),
      .n (42 + 53 * (m' + 1)), .n (43 + 53 * (m' + 1))] : List V) ++ capIns (53 * (m' + 1) - 1)).map σ) =
      (((⟨cap, [(σ (.n 5), dsObserve), (σ (.n 6), dsObserve)]⟩ : Fs).absorbAll msl
        dsObserve).absorb nonce dsPowNonce).perm := by
    rw [hs, perm_eq_cells _ (by simp)]
    have i8 : σ (.n (53 * (m' + 1) - 1 + 8)) = cellsOfState (Q m') false 8 := by
      rw [show 53 * (m' + 1) - 1 + 8 = 52 + 53 * m' + 8 by omega]; exact hQs m' (by omega) 8
    have i9 : σ (.n (53 * (m' + 1) - 1 + 9)) = cellsOfState (Q m') false 9 := by
      rw [show 53 * (m' + 1) - 1 + 9 = 52 + 53 * m' + 9 by omega]; exact hQs m' (by omega) 9
    have i10 : σ (.n (53 * (m' + 1) - 1 + 10)) = cellsOfState (Q m') false 10 := by
      rw [show 53 * (m' + 1) - 1 + 10 = 52 + 53 * m' + 10 by omega]; exact hQs m' (by omega) 10
    have i11 : σ (.n (53 * (m' + 1) - 1 + 11)) = cellsOfState (Q m') false 11 := by
      rw [show 53 * (m' + 1) - 1 + 11 = 52 + 53 * m' + 11 by omega]; exact hQs m' (by omega) 11
    have i12 : σ (.n (53 * (m' + 1) - 1 + 12)) = cellsOfState (Q m') false 12 := by
      rw [show 53 * (m' + 1) - 1 + 12 = 52 + 53 * m' + 12 by omega]; exact hQs m' (by omega) 12
    simp only [capIns, List.cons_append, List.nil_append, List.map_cons, List.map_nil, i8, i9, i10,
      i11, i12, z42, z43, pendCells, List.flatMap_cons, List.flatMap_nil, ← eF0, ← eF1, ← eFN]
    rfl
  have oF : ∀ c : Fin 13, σ (.n (44 + 53 * (m' + 1) + c.val)) =
      cellsOfState (((⟨cap, [(σ (.n 5), dsObserve), (σ (.n 6), dsObserve)]⟩ : Fs).absorbAll msl
        dsObserve).absorb nonce dsPowNonce).perm false c := fun c ↦ by rw [houtF c, hSF]
  -- the loads
  have hall : ∀ k, k < 4 * (m' + 1) → LoadHolds rd (σ (.n 7)) k (ms k) ∧
      LoadHolds rd (σ (.n 8)) k (ms k) := by
    intro k hk
    by_cases k0 : k = 0
    · subst k0; exact ⟨l0, s0⟩
    by_cases k1 : k = 1
    · subst k1; exact ⟨l1, s1⟩
    by_cases kf0 : k = 4 * (m' + 1) - 2
    · subst kf0; rw [hmsF0]; exact ⟨lf0, sf0⟩
    by_cases kf1 : k = 4 * (m' + 1) - 1
    · subst kf1; rw [hmsF1]; exact ⟨lf1, sf1⟩
    obtain ⟨j, t, ht, rfl⟩ : ∃ j t, t < 4 ∧ k = 4 * j + 2 + t :=
      ⟨(k - 2) / 4, (k - 2) % 4, by omega, by omega⟩
    have hj : j < m' + 1 - 1 := by omega
    obtain ⟨hb, -⟩ := hblocks j hj
    rw [hms j t ht]
    exact ⟨(hb t ht).1, (hb t ht).2.2⟩
  refine ⟨?_, msl, nonce, by simp [msl], ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · rw [← h9]; exact hcan0 _ (by simp)
    · rw [← h10]; exact hcan0 _ (by simp)
    · rw [← h11]; exact hcan0 _ (by simp)
    · rw [← h12]; exact hcan0 _ (by simp)
    · rw [← h13]; exact hcan0 _ (by simp)
  · intro k hk
    simp only [msl, List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil] at hk
    by_cases hkn : k < 4 * (m' + 1)
    · rw [List.getElem_append_left (by simpa [msl] using hkn)]
      simpa [msl] using (hall k hkn).1
    · rw [List.getElem_append_right (by simp [msl]; omega)]
      have : k = 4 * (m' + 1) := by omega
      subst this
      simpa [msl] using lN
  · intro k hk
    simp only [msl, List.length_map, List.length_range] at hk
    simpa [msl] using (hall k hk).2
  · have c57 : σ (.n (57 + 53 * (m' + 1))) = σ (.n (44 + 53 * (m' + 1))) := c57
    have c58 : σ (.n (58 + 53 * (m' + 1))) = σ (.n (52 + 53 * (m' + 1))) := c58
    have c59 : σ (.n (59 + 53 * (m' + 1))) = σ (.n (53 + 53 * (m' + 1))) := c59
    have c60 : σ (.n (60 + 53 * (m' + 1))) = σ (.n (54 + 53 * (m' + 1))) := c60
    have c61 : σ (.n (61 + 53 * (m' + 1))) = σ (.n (55 + 53 * (m' + 1))) := c61
    have c62 : σ (.n (62 + 53 * (m' + 1))) = σ (.n (56 + 53 * (m' + 1))) := c62
    have k63 : σ (.n (63 + 53 * (m' + 1))) = word (2 ^ (4 * (m' + 1))) 0 0 := k63
    have m64 : σ (.n (64 + 53 * (m' + 1))) = σ (.n 7) * σ (.n (63 + 53 * (m' + 1))) := m64
    have k65 : σ (.n (65 + 53 * (m' + 1))) = word 2 0 0 := k65
    have m66 : σ (.n (66 + 53 * (m' + 1))) =
      σ (.n (64 + 53 * (m' + 1))) * σ (.n (65 + 53 * (m' + 1))) := m66
    have c67 : σ (.n (67 + 53 * (m' + 1))) = σ (.n (32 + 53 * (m' + 1))) := c67
    have o0 := oF 0
    have o8 := oF 8
    have o9 := oF 9
    have o10 := oF 10
    have o11 := oF 11
    have o12 := oF 12
    simp only [Fin.isValue, Fin.val_zero, Nat.add_zero] at o0
    rw [show 44 + 53 * (m' + 1) + (8 : Fin 13).val = 52 + 53 * (m' + 1) by simp; ring] at o8
    rw [show 44 + 53 * (m' + 1) + (9 : Fin 13).val = 53 + 53 * (m' + 1) by simp; ring] at o9
    rw [show 44 + 53 * (m' + 1) + (10 : Fin 13).val = 54 + 53 * (m' + 1) by simp; ring] at o10
    rw [show 44 + 53 * (m' + 1) + (11 : Fin 13).val = 55 + 53 * (m' + 1) by simp; ring] at o11
    rw [show 44 + 53 * (m' + 1) + (12 : Fin 13).val = 56 + 53 * (m' + 1) by simp; ring] at o12
    rw [← hret, c57, c58, c59, c60, c61, c62, m66, m64, k63, k65, c67, o0, o8, o9, o10, o11, o12,
      word_two_pow (by omega), word_gen, mul_assoc, ← pow_succ]
    rfl


/-! ## Completeness -/

/-- A cell index, reduced. -/
def fin13 (x : ℕ) : Fin 13 := ⟨x % 13, Nat.mod_lt _ (by decide)⟩

theorem fin13_eq {x : ℕ} {c : Fin 13} (h : x % 13 = c.val) : fin13 x = c := Fin.ext h

/-- The honest values of `opening_final_message` at `4m` words, by index, on the message `ms`,
the nonce, the block states `Q` and the final state `S`. -/
def ofmVals (as : List E) (ms : ℕ → E) (nonce : E) (m : ℕ) (Q : ℕ → KeccakState) (S : KeccakState)
    (k : ℕ) : E :=
  if k < 9 then as.getD k 0
  else if k < 14 then as.getD (k - 9) 0
  else if k < 23 then fsPackVals (as.getD 5 0) dsObserve (k - 14)
  else if k < 32 then fsPackVals (as.getD 6 0) dsObserve (k - 23)
  else if k < 12 + 53 * m then
    (if (k - 12) % 53 < 40 then
      (if (k - 12) % 53 % 10 = 0 then ms (4 * ((k - 12) / 53) + (k - 12) % 53 / 10 - 2)
      else fsPackVals (ms (4 * ((k - 12) / 53) + (k - 12) % 53 / 10 - 2)) dsObserve
        ((k - 12) % 53 % 10 - 1))
    else cellsOfState (Q ((k - 12) / 53)) false (fin13 ((k - 12) % 53 - 40)))
  else if k - (12 + 53 * m) < 20 then
    (if (k - (12 + 53 * m)) % 10 = 0 then ms (4 * m - 2 + (k - (12 + 53 * m)) / 10)
    else fsPackVals (ms (4 * m - 2 + (k - (12 + 53 * m)) / 10)) dsObserve
      ((k - (12 + 53 * m)) % 10 - 1))
  else if k - (12 + 53 * m) = 20 then nonce
  else if k - (12 + 53 * m) < 30 then fsPackVals nonce dsPowNonce (k - (12 + 53 * m) - 21)
  else if k - (12 + 53 * m) < 32 then 0
  else if k - (12 + 53 * m) < 45 then
    cellsOfState S false (fin13 (k - (12 + 53 * m) - 32))
  else if k - (12 + 53 * m) = 45 then cellsOfState S false 0
  else if k - (12 + 53 * m) < 51 then
    cellsOfState S false (fin13 (k - (12 + 53 * m) - 38))
  else [word (2 ^ (4 * m)) 0 0, as.getD 7 0 * word (2 ^ (4 * m)) 0 0, word 2 0 0,
    as.getD 7 0 * word (2 ^ (4 * m)) 0 0 * word 2 0 0, nonce].getD (k - (12 + 53 * m) - 51) 0

/-- Decide the next `if` of an unfolded index function by `omega`. -/
macro "ofm_if" : tactic => `(tactic| first
  | (rw [ite_eq_right_of_eq_false]; rotate_left; exact eq_false (by omega))
  | (rw [ite_eq_left_of_eq_true]; rotate_left; exact eq_true (by omega)))

section
variable (as : List E) (ms : ℕ → E) (nonce : E) (Q : ℕ → KeccakState) (S : KeccakState)

theorem ofmVals_msg {m j t : ℕ} (hj : j < m) (ht : t < 4) (h0 : j = 0 → 2 ≤ t) :
    ofmVals as ms nonce m Q S (12 + 53 * j + 10 * t) = ms (4 * j + t - 2) := by
  rw [ofmVals, show (12 + 53 * j + 10 * t - 12) / 53 = j by omega,
    show (12 + 53 * j + 10 * t - 12) % 53 = 10 * t by omega]
  repeat ofm_if
  congr 1; omega

theorem ofmVals_pack {m j t u : ℕ} (hj : j < m) (ht : t < 4) (h0 : j = 0 → 2 ≤ t) (hu : u < 9) :
    ofmVals as ms nonce m Q S (12 + 53 * j + 10 * t + 1 + u) =
      fsPackVals (ms (4 * j + t - 2)) dsObserve u := by
  rw [ofmVals, show (12 + 53 * j + 10 * t + 1 + u - 12) / 53 = j by omega,
    show (12 + 53 * j + 10 * t + 1 + u - 12) % 53 = 10 * t + 1 + u by omega]
  repeat ofm_if
  rw [show (10 * t + 1 + u) / 10 = t by omega, show (10 * t + 1 + u) % 10 - 1 = u by omega]

theorem ofmVals_cells {m j : ℕ} (hj : j < m) (c : Fin 13) :
    ofmVals as ms nonce m Q S (52 + 53 * j + c.val) = cellsOfState (Q j) false c := by
  have hc := c.isLt
  rw [ofmVals, show (52 + 53 * j + c.val - 12) / 53 = j by omega,
    show (52 + 53 * j + c.val - 12) % 53 = 40 + c.val by omega]
  repeat ofm_if
  congr 1; apply fin13_eq; simp

theorem ofmVals_fmsg {m t : ℕ} (hm : 1 ≤ m) (ht : t < 2) :
    ofmVals as ms nonce m Q S (12 + 53 * m + 10 * t) = ms (4 * m - 2 + t) := by
  rw [ofmVals, show 12 + 53 * m + 10 * t - (12 + 53 * m) = 10 * t by omega]
  repeat ofm_if
  congr 1; omega

theorem ofmVals_fpack {m t u : ℕ} (hm : 1 ≤ m) (ht : t < 2) (hu : u < 9) :
    ofmVals as ms nonce m Q S (12 + 53 * m + 10 * t + 1 + u) =
      fsPackVals (ms (4 * m - 2 + t)) dsObserve u := by
  rw [ofmVals, show 12 + 53 * m + 10 * t + 1 + u - (12 + 53 * m) = 10 * t + 1 + u by omega]
  repeat ofm_if
  rw [show (10 * t + 1 + u) / 10 = t by omega, show (10 * t + 1 + u) % 10 - 1 = u by omega]

theorem ofmVals_nonce {m : ℕ} : ofmVals as ms nonce m Q S (32 + 53 * m) = nonce := by
  rw [ofmVals, show 32 + 53 * m - (12 + 53 * m) = 20 by omega]
  repeat ofm_if

theorem ofmVals_npack {m u : ℕ} (hu : u < 9) :
    ofmVals as ms nonce m Q S (33 + 53 * m + u) = fsPackVals nonce dsPowNonce u := by
  rw [ofmVals, show 33 + 53 * m + u - (12 + 53 * m) = 21 + u by omega]
  repeat ofm_if
  rw [show 21 + u - 21 = u by omega]

theorem ofmVals_zero {m u : ℕ} (hu : u < 2) : ofmVals as ms nonce m Q S (42 + 53 * m + u) = 0 := by
  rw [ofmVals, show 42 + 53 * m + u - (12 + 53 * m) = 30 + u by omega]
  repeat ofm_if

theorem ofmVals_fcells {m : ℕ} (c : Fin 13) :
    ofmVals as ms nonce m Q S (44 + 53 * m + c.val) = cellsOfState S false c := by
  have hc := c.isLt
  rw [ofmVals, show 44 + 53 * m + c.val - (12 + 53 * m) = 32 + c.val by omega]
  repeat ofm_if
  congr 1; apply fin13_eq; simp

theorem ofmVals_out0 {m : ℕ} : ofmVals as ms nonce m Q S (57 + 53 * m) = cellsOfState S false 0 := by
  rw [ofmVals, show 57 + 53 * m - (12 + 53 * m) = 45 by omega]
  repeat ofm_if

theorem ofmVals_outcap {m i : ℕ} (hi : i < 5) :
    ofmVals as ms nonce m Q S (58 + 53 * m + i) = cellsOfState S false ⟨8 + i, by omega⟩ := by
  rw [ofmVals, show 58 + 53 * m + i - (12 + 53 * m) = 46 + i by omega]
  repeat ofm_if
  congr 1; apply fin13_eq; simp; try omega

theorem ofmVals_tail {m i : ℕ} (hi : i < 5) :
    ofmVals as ms nonce m Q S (63 + 53 * m + i) =
      [word (2 ^ (4 * m)) 0 0, as.getD 7 0 * word (2 ^ (4 * m)) 0 0, word 2 0 0,
        as.getD 7 0 * word (2 ^ (4 * m)) 0 0 * word 2 0 0, nonce].getD i 0 := by
  rw [ofmVals, show 63 + 53 * m + i - (12 + 53 * m) = 51 + i by omega]
  repeat ofm_if
  rw [show 51 + i - 51 = i by omega]

end

theorem cells13_ofmRun (σ : Val) (b : ℕ) (c : Fin 13) :
    cells13 ((ofmRun b).map σ) c = σ (.n (b + c.val)) := by
  simp [cells13, ofmRun, List.getD_eq_getElem?_getD]

theorem zero_canonical : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

/-- **`opening_final_message` at `4m` words is complete.** -/
theorem ofm_complete {name : String} {f : Fn} (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 8)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = ofmParams)
    (hbody : f.body = ofmBody m) (rd : Reader) (args rets : List E)
    (h : MeaningOpeningFinalMessage (4 * m) rd args rets) : coreProgram.Rel rd name args rets := by
  obtain ⟨f0, f1, f2, f3, f4, w0, w1, cur, out, rfl⟩ : ∃ f0 f1 f2 f3 f4 w0 w1 cur out,
      args = [f0, f1, f2, f3, f4, w0, w1, cur, out] := by
    match args, h with
    | [f0, f1, f2, f3, f4, w0, w1, cur, out], _ => exact ⟨f0, f1, f2, f3, f4, w0, w1, cur, out, rfl⟩
  obtain ⟨hcan, msl, nonce, hlen, hrc, hro, hret⟩ := h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  let ms : ℕ → E := fun i ↦ msl.getD i 0
  have hmsl : msl = (List.range (4 * (m' + 1))).map ms := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp [ms, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  let as := [f0, f1, f2, f3, f4, w0, w1, cur, out]
  let Q := ofmQ [f0, f1, f2, f3, f4] w0 w1 ms
  let S := (⟨capOf (Q m'), [(ms (4 * (m' + 1) - 2), dsObserve), (ms (4 * (m' + 1) - 1), dsObserve),
    (nonce, dsPowNonce)]⟩ : Fs).perm
  have hs : ((⟨[f0, f1, f2, f3, f4], [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll msl
      dsObserve).absorb nonce
      dsPowNonce = ⟨capOf (Q m'), [(ms (4 * (m' + 1) - 2), dsObserve),
        (ms (4 * (m' + 1) - 1), dsObserve), (nonce, dsPowNonce)]⟩ := by
    rw [hmsl, ofm_absorb]
    simp [Fs.absorb, rateScalars, show 4 * (m' + 1) - 2 = 4 * m' + 2 by omega,
      show 4 * (m' + 1) - 1 = 4 * m' + 3 by omega]
    rfl
  simp only at hret
  rw [hs] at hret
  let σ : Val := fun v ↦ ofmVals as ms nonce (m' + 1) Q S v.idx
  have ev : ∀ k, σ (.n k) = ofmVals as ms nonce (m' + 1) Q S k := fun _ ↦ rfl
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have vm : ∀ j t, j < m' + 1 → t < 4 → (j = 0 → 2 ≤ t) →
      σ (.n (12 + 53 * j + 10 * t)) = ms (4 * j + t - 2) := fun j t hj ht h0 ↦
    ofmVals_msg as ms nonce Q S hj ht h0
  have vp : ∀ j t u, j < m' + 1 → t < 4 → (j = 0 → 2 ≤ t) → u < 9 →
      σ (.n (12 + 53 * j + 10 * t + 1 + u)) = fsPackVals (ms (4 * j + t - 2)) dsObserve u :=
    fun j t u hj ht h0 hu ↦ ofmVals_pack as ms nonce Q S hj ht h0 hu
  have vc : ∀ j, j < m' + 1 → ∀ c : Fin 13, σ (.n (52 + 53 * j + c.val)) = cellsOfState (Q j) false c :=
    fun j hj c ↦ ofmVals_cells as ms nonce Q S hj c
  have hall : ∀ k, k < 4 * (m' + 1) → LoadHolds rd cur k (ms k) ∧ LoadHolds rd out k (ms k) := by
    intro k hk
    have h1 := hrc k (by simp [hlen]; omega)
    have h2 := hro k (by simp [hlen]; omega)
    rw [List.getElem_append_left (by simp [hlen]; omega)] at h1
    simp only [ms, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < msl.length by
      simp [hlen]; omega), Option.getD_some]
    exact ⟨h1, h2⟩
  have e7 : σ (.n 7) = cur := by simp [ev, ofmVals, as]
  have e8 : σ (.n 8) = out := by simp [ev, ofmVals, as]
  -- a message word, read, packed and stored
  have nextOk : ∀ j t, j < m' + 1 → t < 4 → (j = 0 → 2 ≤ t) → ∀ i b, i = 4 * j + t - 2 →
      b = 12 + 53 * j + 10 * t →
      LoadHolds rd (σ (.n 7)) i (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve ∧
        LoadHolds rd (σ (.n 8)) i (σ (.n b)) := by
    intro j t hj ht h0 i b hi hb
    have eb : σ (.n b) = ms i := by rw [hb, hi]; exact vm j t hj ht h0
    have hik : i < 4 * (m' + 1) := by omega
    refine ⟨by rw [e7, eb]; exact (hall i hik).1, ?_, by rw [e8, eb]; exact (hall i hik).2⟩
    refine fsPackOk_of_vals fun u hu ↦ ?_
    rw [eb, idx _ _ (show b + 1 + u = 12 + 53 * j + 10 * t + 1 + u by omega), vp j t u hj ht h0 hu,
      hi]
  have vf : ∀ t, t < 2 → σ (.n (12 + 53 * (m' + 1) + 10 * t)) = ms (4 * (m' + 1) - 2 + t) :=
    fun t ht ↦ ofmVals_fmsg as ms nonce Q S (by omega) ht
  have vfp : ∀ t u, t < 2 → u < 9 → σ (.n (12 + 53 * (m' + 1) + 10 * t + 1 + u)) =
      fsPackVals (ms (4 * (m' + 1) - 2 + t)) dsObserve u :=
    fun t u ht hu ↦ ofmVals_fpack as ms nonce Q S (by omega) ht hu
  have nextF : ∀ t, t < 2 → ∀ i b, i = 4 * (m' + 1) - 2 + t → b = 12 + 53 * (m' + 1) + 10 * t →
      LoadHolds rd (σ (.n 7)) i (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve ∧
        LoadHolds rd (σ (.n 8)) i (σ (.n b)) := by
    intro t ht i b hi hb
    have eb : σ (.n b) = ms i := by rw [hb, hi]; exact vf t ht
    have hik : i < 4 * (m' + 1) := by omega
    refine ⟨by rw [e7, eb]; exact (hall i hik).1, ?_, by rw [e8, eb]; exact (hall i hik).2⟩
    refine fsPackOk_of_vals fun u hu ↦ ?_
    rw [eb, idx _ _ (show b + 1 + u = 12 + 53 * (m' + 1) + 10 * t + 1 + u by omega), vfp t u ht hu,
      hi]
  have eN : σ (.n (32 + 53 * (m' + 1))) = nonce := ofmVals_nonce as ms nonce Q S
  have vN : ∀ u, u < 9 → σ (.n (32 + 53 * (m' + 1) + 1 + u)) = fsPackVals nonce dsPowNonce u :=
    fun u hu ↦ (idx _ _ (by omega)).trans (ofmVals_npack as ms nonce Q S hu)
  have pc : ∀ x t, (fsPackVals x t 6, fsPackVals x t 8) = Keccak.scalarCells x t := fsPackVals_cells
  have pcan : ∀ x t, IsCanonical128 (fsPackVals x t 6) ∧ IsCanonical128 (fsPackVals x t 8) :=
    fsPackVals_canonical
  rw [rel_iff_sem hfind, hbody, hparams, ofmBody]
  simp only [holdsList_append, holdsList_range_flatten (m' + 1 - 1) ofmBlock (fun _ => rfl),
    holds_ofmBlock, holds_ofmNext, holds_fsPackT, keccakA, Stmt.HoldsList, Stmt.Holds,
    List.map_cons, List.map_nil]
  -- the first permutation
  have hin0 : [σ (.n 20), σ (.n 22), σ (.n 29), σ (.n 31), σ (.n 39), σ (.n 41), σ (.n 49),
      σ (.n 51), σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13)] =
      [fsPackVals w0 dsObserve 6, fsPackVals w0 dsObserve 8, fsPackVals w1 dsObserve 6,
        fsPackVals w1 dsObserve 8, fsPackVals (ms 0) dsObserve 6, fsPackVals (ms 0) dsObserve 8,
        fsPackVals (ms 1) dsObserve 6, fsPackVals (ms 1) dsObserve 8, f0, f1, f2, f3, f4] := by
    have e39 := (idx 39 _ (by omega)).trans (vp 0 2 6 (by omega) (by omega) (by omega) (by omega))
    have e41 := (idx 41 _ (by omega)).trans (vp 0 2 8 (by omega) (by omega) (by omega) (by omega))
    have e49 := (idx 49 _ (by omega)).trans (vp 0 3 6 (by omega) (by omega) (by omega) (by omega))
    have e51 := (idx 51 _ (by omega)).trans (vp 0 3 8 (by omega) (by omega) (by omega) (by omega))
    rw [e39, e41, e49, e51]
    simp [ev, ofmVals, as]
  have hK0 : permOf [fsPackVals w0 dsObserve 6, fsPackVals w0 dsObserve 8, fsPackVals w1 dsObserve 6,
        fsPackVals w1 dsObserve 8, fsPackVals (ms 0) dsObserve 6, fsPackVals (ms 0) dsObserve 8,
        fsPackVals (ms 1) dsObserve 6, fsPackVals (ms 1) dsObserve 8, f0, f1, f2, f3, f4] = Q 0 :=
    perm_four (pc w0 _) (pc w1 _) (pc _ _) (pc _ _) rfl
  -- the blocks
  have hinB : ∀ j, j < m' → (ofmRate (65 + 53 * j) ++ capIns (52 + 53 * j)).map σ =
      [fsPackVals (ms (4 * j + 2)) dsObserve 6, fsPackVals (ms (4 * j + 2)) dsObserve 8,
        fsPackVals (ms (4 * j + 3)) dsObserve 6, fsPackVals (ms (4 * j + 3)) dsObserve 8,
        fsPackVals (ms (4 * j + 4)) dsObserve 6, fsPackVals (ms (4 * j + 4)) dsObserve 8,
        fsPackVals (ms (4 * j + 5)) dsObserve 6, fsPackVals (ms (4 * j + 5)) dsObserve 8,
        cellsOfState (Q j) false 8, cellsOfState (Q j) false 9, cellsOfState (Q j) false 10,
        cellsOfState (Q j) false 11, cellsOfState (Q j) false 12] := by
    intro j hj
    have r : ∀ t u, t < 4 → u < 9 → σ (.n (65 + 53 * j + 10 * t + 1 + u)) =
        fsPackVals (ms (4 * j + 2 + t)) dsObserve u := fun t u ht hu ↦ by
      rw [idx _ _ (show 65 + 53 * j + 10 * t + 1 + u = 12 + 53 * (j + 1) + 10 * t + 1 + u by ring),
        vp (j + 1) t u (by omega) ht (by omega) hu]
      congr 2; omega
    have c : ∀ c : Fin 13, σ (.n (52 + 53 * j + c.val)) = cellsOfState (Q j) false c :=
      vc j (by omega)
    simp only [ofmRate, capIns, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
    rw [show 65 + 53 * j + 7 = 65 + 53 * j + 10 * 0 + 1 + 6 by ring, r 0 6 (by omega) (by omega),
      show 65 + 53 * j + 9 = 65 + 53 * j + 10 * 0 + 1 + 8 by ring, r 0 8 (by omega) (by omega),
      show 65 + 53 * j + 17 = 65 + 53 * j + 10 * 1 + 1 + 6 by ring, r 1 6 (by omega) (by omega),
      show 65 + 53 * j + 19 = 65 + 53 * j + 10 * 1 + 1 + 8 by ring, r 1 8 (by omega) (by omega),
      show 65 + 53 * j + 27 = 65 + 53 * j + 10 * 2 + 1 + 6 by ring, r 2 6 (by omega) (by omega),
      show 65 + 53 * j + 29 = 65 + 53 * j + 10 * 2 + 1 + 8 by ring, r 2 8 (by omega) (by omega),
      show 65 + 53 * j + 37 = 65 + 53 * j + 10 * 3 + 1 + 6 by ring, r 3 6 (by omega) (by omega),
      show 65 + 53 * j + 39 = 65 + 53 * j + 10 * 3 + 1 + 8 by ring, r 3 8 (by omega) (by omega)]
    rw [show (52 + 53 * j + 8) = 52 + 53 * j + (8 : Fin 13).val from rfl, c 8,
      show (52 + 53 * j + 9) = 52 + 53 * j + (9 : Fin 13).val from rfl, c 9,
      show (52 + 53 * j + 10) = 52 + 53 * j + (10 : Fin 13).val from rfl, c 10,
      show (52 + 53 * j + 11) = 52 + 53 * j + (11 : Fin 13).val from rfl, c 11,
      show (52 + 53 * j + 12) = 52 + 53 * j + (12 : Fin 13).val from rfl, c 12]
  -- the final permutation
  have hinF : (([.n (19 + 53 * (m' + 1)), .n (21 + 53 * (m' + 1)), .n (29 + 53 * (m' + 1)),
      .n (31 + 53 * (m' + 1)), .n (39 + 53 * (m' + 1)), .n (41 + 53 * (m' + 1)),
      .n (42 + 53 * (m' + 1)), .n (43 + 53 * (m' + 1))] : List V) ++
      capIns (53 * (m' + 1) - 1)).map σ =
      [fsPackVals (ms (4 * (m' + 1) - 2)) dsObserve 6, fsPackVals (ms (4 * (m' + 1) - 2)) dsObserve 8,
        fsPackVals (ms (4 * (m' + 1) - 1)) dsObserve 6, fsPackVals (ms (4 * (m' + 1) - 1)) dsObserve 8,
        fsPackVals nonce dsPowNonce 6, fsPackVals nonce dsPowNonce 8, 0, 0,
        cellsOfState (Q m') false 8, cellsOfState (Q m') false 9, cellsOfState (Q m') false 10,
        cellsOfState (Q m') false 11, cellsOfState (Q m') false 12] := by
    have r0 : ∀ u, u < 9 → σ (.n (12 + 53 * (m' + 1) + 1 + u)) =
        fsPackVals (ms (4 * (m' + 1) - 2)) dsObserve u := fun u hu ↦
      (idx _ _ (by omega)).trans ((vfp 0 u (by omega) hu).trans (by rw [Nat.add_zero]))
    have r1 : ∀ u, u < 9 → σ (.n (22 + 53 * (m' + 1) + 1 + u)) =
        fsPackVals (ms (4 * (m' + 1) - 1)) dsObserve u := fun u hu ↦
      (idx _ _ (by omega)).trans ((vfp 1 u (by omega) hu).trans (by congr 2))
    have z : ∀ u, u < 2 → σ (.n (42 + 53 * (m' + 1) + u)) = 0 := fun u hu ↦
      ofmVals_zero as ms nonce Q S hu
    have c : ∀ c : Fin 13, σ (.n (52 + 53 * m' + c.val)) = cellsOfState (Q m') false c :=
      vc m' (by omega)
    simp only [capIns, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
    rw [idx (19 + 53 * (m' + 1)) (12 + 53 * (m' + 1) + 1 + 6) (by omega), r0 6 (by omega),
      idx (21 + 53 * (m' + 1)) (12 + 53 * (m' + 1) + 1 + 8) (by omega), r0 8 (by omega),
      idx (29 + 53 * (m' + 1)) (22 + 53 * (m' + 1) + 1 + 6) (by omega), r1 6 (by omega),
      idx (31 + 53 * (m' + 1)) (22 + 53 * (m' + 1) + 1 + 8) (by omega), r1 8 (by omega),
      idx (39 + 53 * (m' + 1)) _ (show _ = 32 + 53 * (m' + 1) + 1 + 6 by omega), vN 6 (by omega),
      idx (41 + 53 * (m' + 1)) _ (show _ = 32 + 53 * (m' + 1) + 1 + 8 by omega), vN 8 (by omega),
      idx (42 + 53 * (m' + 1)) _ (show _ = 42 + 53 * (m' + 1) + 0 by omega), z 0 (by omega),
      idx (43 + 53 * (m' + 1)) _ (show _ = 42 + 53 * (m' + 1) + 1 by omega), z 1 (by omega),
      idx (53 * (m' + 1) - 1 + 8) _ (show _ = 52 + 53 * m' + (8 : Fin 13).val by simp; omega), c 8,
      idx (53 * (m' + 1) - 1 + 9) _ (show _ = 52 + 53 * m' + (9 : Fin 13).val by simp; omega), c 9,
      idx (53 * (m' + 1) - 1 + 10) _ (show _ = 52 + 53 * m' + (10 : Fin 13).val by simp; omega),
      c 10,
      idx (53 * (m' + 1) - 1 + 11) _ (show _ = 52 + 53 * m' + (11 : Fin 13).val by simp; omega),
      c 11,
      idx (53 * (m' + 1) - 1 + 12) _ (show _ = 52 + 53 * m' + (12 : Fin 13).val by simp; omega),
      c 12]
  have hKF : permOf [fsPackVals (ms (4 * (m' + 1) - 2)) dsObserve 6,
      fsPackVals (ms (4 * (m' + 1) - 2)) dsObserve 8,
      fsPackVals (ms (4 * (m' + 1) - 1)) dsObserve 6, fsPackVals (ms (4 * (m' + 1) - 1)) dsObserve 8,
      fsPackVals nonce dsPowNonce 6, fsPackVals nonce dsPowNonce 8, 0, 0,
      cellsOfState (Q m') false 8, cellsOfState (Q m') false 9, cellsOfState (Q m') false 10,
      cellsOfState (Q m') false 11, cellsOfState (Q m') false 12] = S := by
    show _ = Fs.perm _
    rw [perm_eq_cells _ (by simp)]
    simp only [pendCells, List.flatMap_cons, List.flatMap_nil, ← pc]
    rfl
  have cf : ∀ c : Fin 13, σ (.n (44 + 53 * (m' + 1) + c.val)) = cellsOfState S false c :=
    fun c ↦ ofmVals_fcells as ms nonce Q S c
  have kcan : ∀ (L : List E), (∀ x ∈ L, IsCanonical128 x) → ∀ c : Fin 13,
      IsCanonical128 (cells13 L c) := by
    intro L hL c
    simp only [cells13, List.getD_eq_getElem?_getD]
    cases h : L[c.val]? with
    | none => exact zero_canonical
    | some x => exact hL x (List.mem_of_getElem? h)
  have tl : ∀ i, i < 5 → σ (.n (63 + 53 * (m' + 1) + i)) =
      [word (2 ^ (4 * (m' + 1))) 0 0, cur * word (2 ^ (4 * (m' + 1))) 0 0, word 2 0 0,
        cur * word (2 ^ (4 * (m' + 1))) 0 0 * word 2 0 0, nonce].getD i 0 :=
    fun i hi ↦ ofmVals_tail as ms nonce Q S hi
  have e57 : σ (.n (57 + 53 * (m' + 1))) = cellsOfState S false 0 :=
    ofmVals_out0 as ms nonce Q S (m := m' + 1)
  have ecap : ∀ i (hi : i < 5), σ (.n (58 + 53 * (m' + 1) + i)) =
      cellsOfState S false ⟨8 + i, by omega⟩ :=
    fun i hi ↦ ofmVals_outcap as ms nonce Q S (m := m' + 1) hi
  have oc : ∀ i (hi : i < 5), σ (.n (58 + 53 * (m' + 1) + i)) = σ (.n (52 + 53 * (m' + 1) + i)) :=
    fun i hi ↦ (ecap i hi).trans ((idx _ (44 + 53 * (m' + 1) + (⟨8 + i, by omega⟩ : Fin 13).val)
      (by simp; omega)).trans (cf ⟨8 + i, by omega⟩)).symm
  have t : ∀ i (hi : i < 5) k, k = 63 + 53 * (m' + 1) + i → σ (.n k) =
      [word (2 ^ (4 * (m' + 1))) 0 0, cur * word (2 ^ (4 * (m' + 1))) 0 0, word 2 0 0,
        cur * word (2 ^ (4 * (m' + 1))) 0 0 * word 2 0 0, nonce].getD i 0 :=
    fun i hi k hk ↦ by rw [hk]; exact tl i hi
  refine ⟨σ, by simp [ev, ofmVals, as], ?_, ?_, ?_, ?_, ?_,
    fsPackOk_of_vals fun i hi ↦ by interval_cases i <;> simp [ev, ofmVals, as],
    fsPackOk_of_vals fun i hi ↦ by interval_cases i <;> simp [ev, ofmVals, as],
    nextOk 0 2 (by omega) (by omega) (by omega) 0 32 (by omega) (by omega),
    nextOk 0 3 (by omega) (by omega) (by omega) 1 42 (by omega) (by omega),
    keccak13_mk (rd := rd) rfl rfl ?_ ?_, ?_,
    nextF 0 (by omega) _ _ rfl (by omega), nextF 1 (by omega) _ _ (by omega) (by omega),
    ?_, fsPackOk_of_vals fun u hu ↦ ?_, ?_, ?_, keccak13_mk (rd := rd) rfl rfl ?_ ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (show σ _ = σ _; simp [ev, ofmVals, as]; done)
  · simp only [List.map_cons, List.map_nil, hin0]
    refine kcan _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨(pcan _ _).1, (pcan _ _).2, (pcan _ _).1, (pcan _ _).2, (pcan _ _).1, (pcan _ _).2,
      (pcan _ _).1, (pcan _ _).2, hcan _ (by simp), hcan _ (by simp), hcan _ (by simp),
      hcan _ (by simp), hcan _ (by simp)⟩
  · intro c
    simp only [List.map_cons, List.map_nil, hin0, cells13_ofmRun]
    rw [show keccakF1600 (stateOfCells (cells13 _) false) = permOf _ from rfl, hK0]
    exact vc 0 (by omega) c
  · intro j hj
    have hj' : j < m' := by simpa using hj
    refine ⟨fun t ht ↦ nextOk (j + 1) t (by omega) ht (by omega) _ _ (by omega) (by ring),
      keccak13_mk (rd := rd) (by simp [ofmRate, capIns]) (by simp [ofmRun]) ?_ ?_⟩
    · rw [hinB j hj']
      refine kcan _ ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨(pcan _ _).1, (pcan _ _).2, (pcan _ _).1, (pcan _ _).2, (pcan _ _).1, (pcan _ _).2,
        (pcan _ _).1, (pcan _ _).2, cellsOfState_canonical _ _ _, cellsOfState_canonical _ _ _,
        cellsOfState_canonical _ _ _, cellsOfState_canonical _ _ _, cellsOfState_canonical _ _ _⟩
    · intro c
      rw [cells13_ofmRun, hinB j hj',
        show keccakF1600 (stateOfCells (cells13 _) false) = permOf _ from rfl,
        perm_four (pc _ _) (pc _ _) (pc _ _) (pc _ _) rfl,
        idx _ _ (show 105 + 53 * j + c.val = 52 + 53 * (j + 1) + c.val by ring),
        vc (j + 1) (by omega) c]
      rfl
  · show LoadHolds rd (σ (.n 7)) (4 * (m' + 1)) (σ (.n (32 + 53 * (m' + 1))))
    rw [e7, eN]
    have := hrc (4 * (m' + 1)) (by simp [hlen])
    rwa [List.getElem_append_right (by simp [hlen]), List.getElem_singleton] at this
  · rw [idx _ (32 + 53 * (m' + 1) + 1 + u) (by omega), vN u hu, eN]
  · show σ _ = word 0 0 0
    rw [word_zero]; exact ofmVals_zero as ms nonce Q S (m := m' + 1) (u := 0) (by omega)
  · show σ _ = word 0 0 0
    rw [word_zero]
    exact (idx _ (42 + 53 * (m' + 1) + 1) (by omega)).trans
      (ofmVals_zero as ms nonce Q S (m := m' + 1) (u := 1) (by omega))
  · rw [hinF]
    refine kcan _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨(pcan _ _).1, (pcan _ _).2, (pcan _ _).1, (pcan _ _).2, (pcan _ _).1, (pcan _ _).2,
      zero_canonical, zero_canonical, cellsOfState_canonical _ _ _, cellsOfState_canonical _ _ _,
      cellsOfState_canonical _ _ _, cellsOfState_canonical _ _ _, cellsOfState_canonical _ _ _⟩
  · intro c
    rw [cells13_ofmRun, hinF, show keccakF1600 (stateOfCells (cells13 _) false) = permOf _ from rfl,
      hKF, cf c]
  · show σ _ = σ _
    exact (ofmVals_out0 as ms nonce Q S (m := m' + 1)).trans (cf 0).symm
  · exact oc 0 (by omega)
  · exact (idx _ _ (by omega)).trans ((oc 1 (by omega)).trans (idx _ _ (by omega)))
  · exact (idx _ _ (by omega)).trans ((oc 2 (by omega)).trans (idx _ _ (by omega)))
  · exact (idx _ _ (by omega)).trans ((oc 3 (by omega)).trans (idx _ _ (by omega)))
  · exact (idx _ _ (by omega)).trans ((oc 4 (by omega)).trans (idx _ _ (by omega)))
  · exact t 0 (by omega) _ (by omega)
  · show σ _ = σ _ * σ _
    rw [t 1 (by omega) (64 + 53 * (m' + 1)) (by omega), t 0 (by omega) (63 + 53 * (m' + 1)) (by omega), e7]
    rfl
  · exact t 2 (by omega) (65 + 53 * (m' + 1)) (by omega)
  · show σ _ = σ _ * σ _
    rw [t 3 (by omega) (66 + 53 * (m' + 1)) (by omega), t 1 (by omega) (64 + 53 * (m' + 1)) (by omega), t 2 (by omega) (65 + 53 * (m' + 1)) (by omega)]
    rfl
  · show σ _ = σ _
    rw [t 4 (by omega) (67 + 53 * (m' + 1)) (by omega), eN]
    rfl
  · rw [hret, e57, (idx (58 + 53 * (m' + 1)) _ (by omega)).trans (ecap 0 (by omega)),
      (idx (59 + 53 * (m' + 1)) _ (by omega)).trans (ecap 1 (by omega)),
      (idx (60 + 53 * (m' + 1)) _ (by omega)).trans (ecap 2 (by omega)), (idx (61 + 53 * (m' + 1)) _ (by omega)).trans (ecap 3 (by omega)),
      (idx (62 + 53 * (m' + 1)) _ (by omega)).trans (ecap 4 (by omega)), t 3 (by omega) (66 + 53 * (m' + 1)) (by omega),
      t 4 (by omega) (67 + 53 * (m' + 1)) (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [word_two_pow (by omega), word_gen, mul_assoc, ← pow_succ]
    rfl



set_option maxRecDepth 100000 in
theorem core479_body : Fn.body Data.core446 = ofmBody 1 := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem core498_body : Fn.body Data.core495 = ofmBody 2 := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem core444_body : Fn.body Data.core540 = ofmBody 4 := stmtsEqb_sound (by decide +kernel)
set_option maxRecDepth 100000 in
theorem core461_body : Fn.body Data.core586 = ofmBody 8 := stmtsEqb_sound (by decide +kernel)

theorem ofm_iff {name : String} {f : Fn} (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 8)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = ofmParams)
    (hbody : f.body = ofmBody m) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningOpeningFinalMessage (4 * m) rd args rets :=
  ⟨ofm_sound m hm1 hm hfind hparams hbody rd args rets,
    ofm_complete m hm1 hm hfind hparams hbody rd args rets⟩

set_option maxRecDepth 100000 in
theorem ofm_L4_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L4" args rets ↔
      MeaningOpeningFinalMessage 4 rd args rets :=
  ofm_iff 1 (by decide) (by decide) (Program.find?_of_indexOf? (j := 446) (by decide +kernel) rfl)
    rfl core479_body rd args rets

set_option maxRecDepth 100000 in
theorem ofm_L8_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L8" args rets ↔
      MeaningOpeningFinalMessage 8 rd args rets :=
  ofm_iff 2 (by decide) (by decide) (Program.find?_of_indexOf? (j := 495) (by decide +kernel) rfl)
    rfl core498_body rd args rets

set_option maxRecDepth 100000 in
theorem ofm_L16_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L16" args rets ↔
      MeaningOpeningFinalMessage 16 rd args rets :=
  ofm_iff 4 (by decide) (by decide) (Program.find?_of_indexOf? (j := 540) (by decide +kernel) rfl)
    rfl core444_body rd args rets

set_option maxRecDepth 100000 in
theorem ofm_L32_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_final_message__L32" args rets ↔
      MeaningOpeningFinalMessage 32 rd args rets :=
  ofm_iff 8 (by decide) (by decide) (Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl)
    rfl core461_body rd args rets

/-- **`opening_final_message`'s core IR is its meaning**, at every deployed length. -/
theorem opening_final_message_holds : opening_final_message_Spec := by
  intro p hp
  simp only [finalMessageNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  exacts [ofm_L4_iff, ofm_L8_iff, ofm_L16_iff, ofm_L32_iff]

end
end LeanVM.Guest.B1
