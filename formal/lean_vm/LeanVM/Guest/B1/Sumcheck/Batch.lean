/-
  LeanVM.Guest.B1.Sumcheck.Batch

  B1 for `batch_sumcheck`: the claim-batching sumcheck, one generic argument over the rounds.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `batch_sumcheck` (G:1147-1161, TRIAGE #32)

Its body at `n` rounds (`bsBody n`): the capacity copied into `8 .. 12`; round `0` (`bsRound0`):
`g(1)`, `g(∞)` read at `msgs[0]`, `msgs[1]` and packed (`fsNextT` from `13`, `23`), the pad run
`33 .. 37`, the permutation into `38 .. 50`, its challenge (at `57`) stored at `point[0]`, the fold
(`58 .. 64`); round `j + 1` (`bsRound j`): the same from `65 + 47 j`, its permutation into
`85 + 47 j`, reading the zero run `34 .. 37`; the final capacity and claim copied and returned.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Thirteen consecutive values. -/
def bsRun13 (b : ℕ) : List V := (List.range 13).map fun i ↦ .n (b + i)

/-- The fold of round `r` whose permutation writes from `o`, its claim `c`, its words at `b`,
`b + 10`. -/
def bsFold (o c b : ℕ) (r : ℕ) : List Stmt :=
  [.atom (.load (.n (o + 19)) (.n 7) r),
    .atom (.add (.n (o + 20)) (.n c) (.n b)), .atom (.add (.n (o + 21)) (.n (o + 20)) (.n b)),
    .atom (.add (.n (o + 22)) (.n (o + 21)) (.n (b + 10))),
    .atom (.mul (.n (o + 23)) (.n (b + 10)) (.n (o + 19))),
    .atom (.add (.n (o + 24)) (.n (o + 23)) (.n (o + 22))),
    .atom (.mul (.n (o + 25)) (.n (o + 24)) (.n (o + 19))),
    .atom (.add (.n (o + 26)) (.n (o + 25)) (.n (o + 20)))]

/-- Round `0`. -/
def bsRound0 : List Stmt :=
  fsNextT (.n 5) 0 13 ++ fsNextT (.n 5) 1 23 ++
  [.atom (.const (.n 33) (word 1 0 0)), .atom (.const (.n 34) (word 0 0 0)),
    .atom (.const (.n 35) (word 0 0 0)), .atom (.const (.n 36) (word 0 0 0)),
    .atom (.const (.n 37) (word 0 0 0)),
    keccakA [.n 20, .n 22, .n 30, .n 32, .n 34, .n 35, .n 36, .n 37, .n 8, .n 9, .n 10, .n 11, .n 12]
      (bsRun13 38)] ++
  challengeT (.n 38) (.n 39) 51 ++ bsFold 38 6 13 0

/-- Round `j + 1`. -/
def bsRound (j : ℕ) : List Stmt :=
  fsNextT (.n 5) (2 * j + 2) (65 + 47 * j) ++ fsNextT (.n 5) (2 * j + 3) (75 + 47 * j) ++
  [keccakA [.n (72 + 47 * j), .n (74 + 47 * j), .n (82 + 47 * j), .n (84 + 47 * j), .n 34, .n 35,
      .n 36, .n 37, .n (46 + 47 * j), .n (47 + 47 * j), .n (48 + 47 * j), .n (49 + 47 * j),
      .n (50 + 47 * j)] (bsRun13 (85 + 47 * j))] ++
  challengeT (.n (85 + 47 * j)) (.n (86 + 47 * j)) (98 + 47 * j) ++
  bsFold (85 + 47 * j) (64 + 47 * j) (65 + 47 * j) (j + 1)

/-- The expansion of `batch_sumcheck` at `n ≥ 1` rounds. -/
def bsBody (n : ℕ) : List Stmt :=
  [.atom (.copy (.n 8) (.n 0)), .atom (.copy (.n 9) (.n 1)), .atom (.copy (.n 10) (.n 2)),
    .atom (.copy (.n 11) (.n 3)), .atom (.copy (.n 12) (.n 4))] ++
  bsRound0 ++ ((List.range (n - 1)).map bsRound).flatten ++
  [.atom (.copy (.n (18 + 47 * n)) (.n (38 + 47 * (n - 1) + 8))),
    .atom (.copy (.n (19 + 47 * n)) (.n (38 + 47 * (n - 1) + 9))),
    .atom (.copy (.n (20 + 47 * n)) (.n (38 + 47 * (n - 1) + 10))),
    .atom (.copy (.n (21 + 47 * n)) (.n (38 + 47 * (n - 1) + 11))),
    .atom (.copy (.n (22 + 47 * n)) (.n (38 + 47 * (n - 1) + 12))),
    .atom (.copy (.n (23 + 47 * n)) (.n (38 + 47 * (n - 1) + 26))),
    .ret [.n (18 + 47 * n), .n (19 + 47 * n), .n (20 + 47 * n), .n (21 + 47 * n), .n (22 + 47 * n),
      .n (23 + 47 * n)]]

/-! ## The rounds as a sequence -/

/-- The claim and the sponge after the first `j` rounds of `bsRun` on the words `g`. -/
def bsSt (g : ℕ → E × E) (claim : E) (s : Fs) : ℕ → E × Fs
  | 0 => (claim, s)
  | j + 1 =>
    let st := bsSt g claim s j
    let r := ((st.2.absorb (g j).1 dsObserve).absorb (g j).2 dsObserve).squeeze
    let g0 := st.1 + (g j).1
    (((g j).2 * r.1 + (g0 + (g j).1 + (g j).2)) * r.1 + g0, r.2)

/-- Round `j`'s permutation. -/
def bsP (g : ℕ → E × E) (claim : E) (s : Fs) (j : ℕ) : KeccakState :=
  (((bsSt g claim s j).2.absorb (g j).1 dsObserve).absorb (g j).2 dsObserve).perm

theorem bsSt_succ_shift (g : ℕ → E × E) (claim : E) (s : Fs) :
    ∀ j, bsSt g claim s (j + 1) =
      bsSt (fun i ↦ g (i + 1)) (bsSt g claim s 1).1 (bsSt g claim s 1).2 j
  | 0 => rfl
  | j + 1 => by
    rw [bsSt, bsSt_succ_shift g claim s j]
    rfl

theorem range_succ_map {α : Type} (f : ℕ → α) (n : ℕ) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map fun i ↦ f (i + 1) := by
  simp [List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- Round `j`'s challenge. -/
def bsChal (g : ℕ → E × E) (claim : E) (s : Fs) (j : ℕ) : E :=
  (((bsSt g claim s j).2.absorb (g j).1 dsObserve).absorb (g j).2 dsObserve).squeeze.1

theorem bsChal_shift (g : ℕ → E × E) (claim : E) (s : Fs) (j : ℕ) :
    bsChal g claim s (j + 1) =
      bsChal (fun i ↦ g (i + 1)) (bsSt g claim s 1).1 (bsSt g claim s 1).2 j := by
  rw [bsChal, bsChal, bsSt_succ_shift g claim s j]

theorem bsRun_cons1 (g : ℕ → E × E) (L : List (E × E)) (claim : E) (s : Fs) :
    (bsRun (g 0 :: L) claim s).1.1 =
      bsChal g claim s 0 :: (bsRun L (bsSt g claim s 1).1 (bsSt g claim s 1).2).1.1 := rfl

theorem bsRun_cons2 (g : ℕ → E × E) (L : List (E × E)) (claim : E) (s : Fs) :
    (bsRun (g 0 :: L) claim s).1.2 = (bsRun L (bsSt g claim s 1).1 (bsSt g claim s 1).2).1.2 := rfl

theorem bsRun_cons3 (g : ℕ → E × E) (L : List (E × E)) (claim : E) (s : Fs) :
    (bsRun (g 0 :: L) claim s).2 = (bsRun L (bsSt g claim s 1).1 (bsSt g claim s 1).2).2 := rfl

theorem bsRun_range1 : ∀ (n : ℕ) (g : ℕ → E × E) (claim : E) (s : Fs),
    (bsRun ((List.range n).map g) claim s).1.1 = (List.range n).map (bsChal g claim s)
  | 0, _, _, _ => rfl
  | n + 1, g, claim, s => by
    rw [range_succ_map, bsRun_cons1, bsRun_range1 n, range_succ_map]
    exact congrArg (List.cons (bsChal g claim s 0))
      (List.map_congr_left fun i _ ↦ (bsChal_shift g claim s i).symm)

theorem bsRun_range2 : ∀ (n : ℕ) (g : ℕ → E × E) (claim : E) (s : Fs),
    (bsRun ((List.range n).map g) claim s).1.2 = (bsSt g claim s n).1
  | 0, _, _, _ => rfl
  | n + 1, g, claim, s => by
    rw [range_succ_map, bsRun_cons2, bsRun_range2 n, bsSt_succ_shift g claim s n]

theorem bsRun_range3 : ∀ (n : ℕ) (g : ℕ → E × E) (claim : E) (s : Fs),
    (bsRun ((List.range n).map g) claim s).2 = (bsSt g claim s n).2
  | 0, _, _, _ => rfl
  | n + 1, g, claim, s => by
    rw [range_succ_map, bsRun_cons3, bsRun_range3 n, bsSt_succ_shift g claim s n]

theorem absorb2 (cap : List E) (a b : E) :
    ((⟨cap, []⟩ : Fs).absorb a dsObserve).absorb b dsObserve = ⟨cap, [(a, dsObserve), (b, dsObserve)]⟩ := by
  simp [Fs.absorb, rateScalars]

theorem bsSt_empty (g : ℕ → E × E) (claim : E) (cap : List E) :
    ∀ j, (bsSt g claim ⟨cap, []⟩ j).2 = ⟨(bsSt g claim ⟨cap, []⟩ j).2.cap, []⟩
  | 0 => rfl
  | _ + 1 => rfl

theorem bsSt_cap_succ (g : ℕ → E × E) (claim : E) (cap : List E) (j : ℕ) :
    (bsSt g claim ⟨cap, []⟩ (j + 1)).2.cap = capOf (bsP g claim ⟨cap, []⟩ j) := rfl

/-- Round `j`'s permutation, its cells written out. -/
theorem bsP_eq (g : ℕ → E × E) (claim : E) (cap : List E) (j : ℕ) :
    bsP g claim ⟨cap, []⟩ j = permOf (pendCells [((g j).1, dsObserve), ((g j).2, dsObserve)] ++
      [0, 0, 0, 0] ++ (bsSt g claim ⟨cap, []⟩ j).2.cap) := by
  rw [bsP, bsSt_empty, absorb2, perm_eq_cells _ (by simp)]
  rfl

/-! ## Soundness -/

/-- What a round's fold asks. -/
def BsFoldOk (rd : Reader) (σ : Val) (o c b r : ℕ) : Prop :=
  LoadHolds rd (σ (.n 7)) r (σ (.n (o + 19))) ∧ σ (.n (o + 20)) = σ (.n c) + σ (.n b) ∧
    σ (.n (o + 21)) = σ (.n (o + 20)) + σ (.n b) ∧
    σ (.n (o + 22)) = σ (.n (o + 21)) + σ (.n (b + 10)) ∧
    σ (.n (o + 23)) = σ (.n (b + 10)) * σ (.n (o + 19)) ∧
    σ (.n (o + 24)) = σ (.n (o + 23)) + σ (.n (o + 22)) ∧
    σ (.n (o + 25)) = σ (.n (o + 24)) * σ (.n (o + 19)) ∧
    σ (.n (o + 26)) = σ (.n (o + 25)) + σ (.n (o + 20))

theorem holds_bsFold (o c b r : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (bsFold o c b r) next kret ↔ BsFoldOk rd σ o c b r ∧ next := by
  simp only [bsFold, BsFoldOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

/-- The fold's value. -/
theorem bsFold_value {o c b r : ℕ} (h : BsFoldOk rd σ o c b r) :
    σ (.n (o + 26)) = (σ (.n (b + 10)) * σ (.n (o + 19)) + (σ (.n c) + σ (.n b) + σ (.n b) +
      σ (.n (b + 10)))) * σ (.n (o + 19)) + (σ (.n c) + σ (.n b)) := by
  obtain ⟨-, h20, h21, h22, h23, h24, h25, h26⟩ := h
  rw [h26, h25, h24, h23, h22, h21, h20]

/-- What round `j + 1` asks. -/
theorem holds_bsRound (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (bsRound j) True kret ↔
      (LoadHolds rd (σ (.n 5)) (2 * j + 2) (σ (.n (65 + 47 * j))) ∧
        FsPackOk σ (.n (65 + 47 * j)) (65 + 47 * j + 1) dsObserve) ∧
      (LoadHolds rd (σ (.n 5)) (2 * j + 3) (σ (.n (75 + 47 * j))) ∧
        FsPackOk σ (.n (75 + 47 * j)) (75 + 47 * j + 1) dsObserve) ∧
      (Atom.keccak [.n (72 + 47 * j), .n (74 + 47 * j), .n (82 + 47 * j), .n (84 + 47 * j), .n 34,
        .n 35, .n 36, .n 37, .n (46 + 47 * j), .n (47 + 47 * j), .n (48 + 47 * j),
        .n (49 + 47 * j), .n (50 + 47 * j)] (bsRun13 (85 + 47 * j)) false false).Holds rd σ ∧
      ChallengeOk σ (.n (85 + 47 * j)) (.n (86 + 47 * j)) (98 + 47 * j) ∧
      BsFoldOk rd σ (85 + 47 * j) (64 + 47 * j) (65 + 47 * j) (j + 1) := by
  simp only [bsRound, keccakA, holdsList_append, holds_fsNextT, holds_challengeT, holds_bsFold,
    Stmt.HoldsList, Stmt.Holds, and_true]

theorem cells13_bsRun13 (σ : Val) (b : ℕ) (c : Fin 13) :
    cells13 ((bsRun13 b).map σ) c = σ (.n (b + c.val)) := by
  simp [cells13, bsRun13, List.getD_eq_getElem?_getD]

theorem keccak_bsRun13 {ins : List V} {b : ℕ}
    (h : (Atom.keccak ins (bsRun13 b) false false).Holds rd σ) :
    AllCanonical (ins.map σ) ∧
      ∀ c : Fin 13, σ (.n (b + c.val)) = cellsOfState (permOf (ins.map σ)) false c := by
  obtain ⟨-, -, hcan, hout⟩ := keccakA_perm h
  refine ⟨hcan, fun c => ?_⟩
  have := outs_eq hout c (by simp [bsRun13])
  simpa [bsRun13] using this

theorem flatMap_pairs (g : ℕ → E × E) :
    ∀ n, ((List.range n).map g).flatMap (fun p ↦ [p.1, p.2]) =
      (List.range (2 * n)).map fun k ↦ if k % 2 = 0 then (g (k / 2)).1 else (g (k / 2)).2
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatMap_append, flatMap_pairs g n,
      show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, List.append_assoc, List.cons_append, List.nil_append]
    congr 2
    · simp only [show 2 * n % 2 = 0 by omega, show 2 * n / 2 = n by omega, ↓reduceIte]
    · simp only [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega,
        one_ne_zero, ↓reduceIte]

/-- The eight parameters. -/
abbrev bsParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]

/-- Where round `j`'s words sit. -/
def bsG : ℕ → ℕ
  | 0 => 13
  | j + 1 => 65 + 47 * j

/-- Where the claim round `j` starts from sits. -/
def bsC : ℕ → ℕ
  | 0 => 6
  | j + 1 => 64 + 47 * j

theorem bs_sound {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = bsParams)
    (hbody : f.body = bsBody n) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningBatchSumcheck n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, bsBody, bsRound0] at h
  simp only [holdsList_append, holdsList_range_flatten (n - 1) bsRound (fun _ => rfl),
    holds_bsRound, holds_fsNextT, holds_challengeT, holds_bsFold, keccakA, Stmt.HoldsList,
    Stmt.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, h8, h9, h10, h11, h12, ⟨l0, p0⟩, ⟨l1, p1⟩, -, z34, z35, z36, z37, hK0, hch0, hf0,
    hrounds, c0, c1, c2, c3, c4, c5, hret⟩ := h
  subst hp
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have h8 : σ (.n 8) = σ (.n 0) := h8
  have h9 : σ (.n 9) = σ (.n 1) := h9
  have h10 : σ (.n 10) = σ (.n 2) := h10
  have h11 : σ (.n 11) = σ (.n 3) := h11
  have h12 : σ (.n 12) = σ (.n 4) := h12
  have z34 : σ (.n 34) = 0 := by rw [← word_zero]; exact z34
  have z35 : σ (.n 35) = 0 := by rw [← word_zero]; exact z35
  have z36 : σ (.n 36) = 0 := by rw [← word_zero]; exact z36
  have z37 : σ (.n 37) = 0 := by rw [← word_zero]; exact z37
  set g : ℕ → E × E := fun j ↦ (σ (.n (bsG j)), σ (.n (bsG j + 10))) with hg
  set cap0 := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] with hcap0
  set St := bsSt g (σ (.n 6)) ⟨cap0, []⟩ with hSt
  set P := bsP g (σ (.n 6)) ⟨cap0, []⟩ with hP
  -- round j's facts
  have hR : ∀ j, j < n → (∀ c : Fin 13, σ (.n (38 + 47 * j + c.val)) = cellsOfState (P j) false c) →
      σ (.n (38 + 47 * j + 19)) = challengeOf (P j) ∧
        BsFoldOk rd σ (38 + 47 * j) (bsC j) (bsG j) j := by
    intro j hj hB
    cases j with
    | zero =>
      exact ⟨challengeT_value hch0 (hB 0) (hB 1), hf0⟩
    | succ i =>
      obtain ⟨-, -, -, hch, hf⟩ := hrounds i (by omega)
      have e : 38 + 47 * (i + 1) = 85 + 47 * i := by ring
      rw [e] at hB ⊢
      have b0 : σ (.n (85 + 47 * i)) = cellsOfState (P (i + 1)) false 0 := hB 0
      have b1 : σ (.n (86 + 47 * i)) = cellsOfState (P (i + 1)) false 1 :=
        (idx _ (85 + 47 * i + (1 : Fin 13).val) (by simp; ring)).trans (hB 1)
      refine ⟨(idx _ (98 + 47 * i + 6) (by ring)).trans (challengeT_value hch b0 b1), hf⟩
  have hAB : ∀ j, j < n → σ (.n (bsC j)) = (St j).1 ∧
      ∀ c : Fin 13, σ (.n (38 + 47 * j + c.val)) = cellsOfState (P j) false c := by
    intro j
    induction j with
    | zero =>
      intro hj
      refine ⟨rfl, fun c ↦ ?_⟩
      obtain ⟨hcan, hout⟩ := keccak_bsRun13 hK0
      rw [show 38 + 47 * 0 + c.val = 38 + c.val by ring, hout c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      have e20 : (σ (.n 20), σ (.n 22)) = Keccak.scalarCells (σ (.n 13)) dsObserve :=
        fsPackT_cells p0 (hcan (σ (.n 20)) (by simp))
      have e30 : (σ (.n 30), σ (.n 32)) = Keccak.scalarCells (σ (.n 23)) dsObserve :=
        fsPackT_cells p1 (hcan (σ (.n 30)) (by simp))
      rw [hP, bsP_eq]
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
        hg, bsG, ← e20, ← e30, z34, z35, z36, z37, h8, h9, h10, h11, h12]
      rfl
    | succ j ih =>
      intro hj
      obtain ⟨hA, hB⟩ := ih (by omega)
      obtain ⟨hr, hf⟩ := hR j (by omega) hB
      refine ⟨?_, fun c ↦ ?_⟩
      · rw [idx (bsC (j + 1)) (38 + 47 * j + 26) (by simp only [bsC]; ring), bsFold_value hf, hr, hA]
        rfl
      · obtain ⟨⟨-, q0⟩, ⟨-, q1⟩, hK, -, -⟩ := hrounds j (by omega)
        obtain ⟨hcan, hout⟩ := keccak_bsRun13 hK
        rw [idx _ (85 + 47 * j + c.val) (by ring), hout c]
        refine congrArg (fun S ↦ cellsOfState S false c) ?_
        have ea : (σ (.n (72 + 47 * j)), σ (.n (74 + 47 * j))) =
            Keccak.scalarCells (σ (.n (65 + 47 * j))) dsObserve := by
          have hc : IsCanonical128 (σ (.n (65 + 47 * j + 1 + 6))) := by
            rw [idx _ (72 + 47 * j) (by ring)]; exact hcan _ (by simp)
          have := fsPackT_cells q0 hc
          rwa [idx (65 + 47 * j + 1 + 6) (72 + 47 * j) (by ring),
            idx (65 + 47 * j + 1 + 8) (74 + 47 * j) (by ring)] at this
        have eb : (σ (.n (82 + 47 * j)), σ (.n (84 + 47 * j))) =
            Keccak.scalarCells (σ (.n (75 + 47 * j))) dsObserve := by
          have hc : IsCanonical128 (σ (.n (75 + 47 * j + 1 + 6))) := by
            rw [idx _ (82 + 47 * j) (by ring)]; exact hcan _ (by simp)
          have := fsPackT_cells q1 hc
          rwa [idx (75 + 47 * j + 1 + 6) (82 + 47 * j) (by ring),
            idx (75 + 47 * j + 1 + 8) (84 + 47 * j) (by ring)] at this
        have i8 : σ (.n (46 + 47 * j)) = cellsOfState (P j) false 8 :=
          (idx _ (38 + 47 * j + (8 : Fin 13).val) (by simp; ring)).trans (hB 8)
        have i9 : σ (.n (47 + 47 * j)) = cellsOfState (P j) false 9 :=
          (idx _ (38 + 47 * j + (9 : Fin 13).val) (by simp; ring)).trans (hB 9)
        have i10 : σ (.n (48 + 47 * j)) = cellsOfState (P j) false 10 :=
          (idx _ (38 + 47 * j + (10 : Fin 13).val) (by simp; ring)).trans (hB 10)
        have i11 : σ (.n (49 + 47 * j)) = cellsOfState (P j) false 11 :=
          (idx _ (38 + 47 * j + (11 : Fin 13).val) (by simp; ring)).trans (hB 11)
        have i12 : σ (.n (50 + 47 * j)) = cellsOfState (P j) false 12 :=
          (idx _ (38 + 47 * j + (12 : Fin 13).val) (by simp; ring)).trans (hB 12)
        have gb : g (j + 1) = (σ (.n (65 + 47 * j)), σ (.n (75 + 47 * j))) := by
          simp only [hg, bsG]
          rw [idx (65 + 47 * j + 10) (75 + 47 * j) (by ring)]
        rw [hP, bsP_eq, bsSt_cap_succ, ← hP, gb]
        simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
          ← ea, ← eb, z34, z35, z36, z37, i8, i9, i10, i11, i12]
        rfl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hAm, hBm⟩ := hAB m (by omega)
  obtain ⟨hrm, hfm⟩ := hR m (by omega) hBm
  have hAn : σ (.n (bsC (m + 1))) = (St (m + 1)).1 := by
    rw [idx (bsC (m + 1)) (38 + 47 * m + 26) (by simp only [bsC]; ring), bsFold_value hfm, hrm,
      hAm]
    rfl
  obtain ⟨hcan0, -⟩ := keccak_bsRun13 hK0
  refine ⟨?_, (List.range (m + 1)).map g, by simp, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [← h8]; exact hcan0 _ (by simp)
    · rw [← h9]; exact hcan0 _ (by simp)
    · rw [← h10]; exact hcan0 _ (by simp)
    · rw [← h11]; exact hcan0 _ (by simp)
    · rw [← h12]; exact hcan0 _ (by simp)
  · rw [flatMap_pairs]
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    obtain ⟨j, e, he, rfl⟩ : ∃ j e : ℕ, e < 2 ∧ k = 2 * j + e := ⟨k / 2, k % 2, by omega, by omega⟩
    have hj : j < m + 1 := by omega
    interval_cases e
    · simp only [show (2 * j + 0) % 2 = 0 by omega, show (2 * j + 0) / 2 = j by omega, ↓reduceIte]
      cases j with
      | zero => exact l0
      | succ i =>
        obtain ⟨⟨l, -⟩, -, -⟩ := hrounds i (by omega)
        simpa [hg, bsG, show 2 * (i + 1) + 0 = 2 * i + 2 by ring] using l
    · simp only [show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega,
        one_ne_zero, ↓reduceIte]
      cases j with
      | zero => exact l1
      | succ i =>
        obtain ⟨-, ⟨l, -⟩, -, -⟩ := hrounds i (by omega)
        rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring]
        simp only [hg, bsG]
        rw [idx (65 + 47 * i + 10) (75 + 47 * i) (by ring)]
        exact l
  · simp only
    refine ⟨?_, ?_⟩
    · rw [bsRun_range1]
      intro k hk
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨-, hB⟩ := hAB k hk
      obtain ⟨hr, hf⟩ := hR k hk hB
      have := hf.1
      rw [hr] at this
      exact this
    · rw [bsRun_range2, bsRun_range3, ← hAn, bsSt_cap_succ, ← hP, ← hret]
      have c0' : σ (.n (18 + 47 * (m + 1))) = cellsOfState (P m) false 8 := by
        rw [show σ (.n (18 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 8)) from c0]
        exact (idx _ (38 + 47 * m + (8 : Fin 13).val) (by simp)).trans (hBm 8)
      have c1' : σ (.n (19 + 47 * (m + 1))) = cellsOfState (P m) false 9 := by
        rw [show σ (.n (19 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 9)) from c1]
        exact (idx _ (38 + 47 * m + (9 : Fin 13).val) (by simp)).trans (hBm 9)
      have c2' : σ (.n (20 + 47 * (m + 1))) = cellsOfState (P m) false 10 := by
        rw [show σ (.n (20 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 10)) from c2]
        exact (idx _ (38 + 47 * m + (10 : Fin 13).val) (by simp)).trans (hBm 10)
      have c3' : σ (.n (21 + 47 * (m + 1))) = cellsOfState (P m) false 11 := by
        rw [show σ (.n (21 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 11)) from c3]
        exact (idx _ (38 + 47 * m + (11 : Fin 13).val) (by simp)).trans (hBm 11)
      have c4' : σ (.n (22 + 47 * (m + 1))) = cellsOfState (P m) false 12 := by
        rw [show σ (.n (22 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 12)) from c4]
        exact (idx _ (38 + 47 * m + (12 : Fin 13).val) (by simp)).trans (hBm 12)
      have c5' : σ (.n (23 + 47 * (m + 1))) = σ (.n (bsC (m + 1))) := by
        rw [show σ (.n (23 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 26)) from c5]
        exact idx _ _ (by simp only [bsC]; omega)
      rw [c0', c1', c2', c3', c4', c5']
      rfl


/-! ## Completeness -/

/-- A cell index, reduced. -/
def bsFin (x : ℕ) : Fin 13 := ⟨x % 13, Nat.mod_lt _ (by decide)⟩

theorem bsFin_eq {x : ℕ} {c : Fin 13} (h : x % 13 = c.val) : bsFin x = c := Fin.ext h

/-- A fold's seven values from the claim, the words and the challenge. -/
def bsFoldVals (c g1 gInf r : E) : List E :=
  [c + g1, c + g1 + g1, c + g1 + g1 + gInf, gInf * r, gInf * r + (c + g1 + g1 + gInf),
    (gInf * r + (c + g1 + g1 + gInf)) * r, (gInf * r + (c + g1 + g1 + gInf)) * r + (c + g1)]

/-- The honest values of `batch_sumcheck` at `n` rounds, by index, on the rounds' words `g`, the
claims `cl` and the permutations `P`. -/
def bsVals (as : List E) (g : ℕ → E × E) (cl : ℕ → E) (P : ℕ → KeccakState) (n k : ℕ) : E :=
  if k < 8 then as.getD k 0
  else if k < 13 then as.getD (k - 8) 0
  else if k = 13 then (g 0).1
  else if k < 23 then fsPackVals (g 0).1 dsObserve (k - 14)
  else if k = 23 then (g 0).2
  else if k < 33 then fsPackVals (g 0).2 dsObserve (k - 24)
  else if k = 33 then 1
  else if k < 38 then 0
  else if k < 51 then cellsOfState (P 0) false (bsFin (k - 38))
  else if k < 58 then challengeVals (cellsOfState (P 0) false 0) (cellsOfState (P 0) false 1) (k - 51)
  else if k < 65 then (bsFoldVals (cl 0) (g 0).1 (g 0).2 (challengeOf (P 0))).getD (k - 58) 0
  else if (k - 65) / 47 + 1 < n then
    (if (k - 65) % 47 = 0 then (g ((k - 65) / 47 + 1)).1
    else if (k - 65) % 47 < 10 then
      fsPackVals (g ((k - 65) / 47 + 1)).1 dsObserve ((k - 65) % 47 - 1)
    else if (k - 65) % 47 = 10 then (g ((k - 65) / 47 + 1)).2
    else if (k - 65) % 47 < 20 then
      fsPackVals (g ((k - 65) / 47 + 1)).2 dsObserve ((k - 65) % 47 - 11)
    else if (k - 65) % 47 < 33 then
      cellsOfState (P ((k - 65) / 47 + 1)) false (bsFin ((k - 65) % 47 - 20))
    else if (k - 65) % 47 < 40 then
      challengeVals (cellsOfState (P ((k - 65) / 47 + 1)) false 0)
        (cellsOfState (P ((k - 65) / 47 + 1)) false 1) ((k - 65) % 47 - 33)
    else (bsFoldVals (cl ((k - 65) / 47 + 1)) (g ((k - 65) / 47 + 1)).1 (g ((k - 65) / 47 + 1)).2
      (challengeOf (P ((k - 65) / 47 + 1)))).getD ((k - 65) % 47 - 40) 0)
  else if (k - 65) % 47 < 5 then cellsOfState (P (n - 1)) false (bsFin (8 + (k - 65) % 47))
  else cl n

/-- Decide the next `if` of an unfolded index function by `omega`. -/
macro "bs_if" : tactic => `(tactic| first
  | (rw [ite_eq_right_of_eq_false]; rotate_left; exact eq_false (by omega))
  | (rw [ite_eq_left_of_eq_true]; rotate_left; exact eq_true (by omega)))

section
variable (as : List E) (g : ℕ → E × E) (cl : ℕ → E) (P : ℕ → KeccakState)

theorem bsVals_round {n j i : ℕ} (hj : j + 1 < n) (hi : i < 47) :
    bsVals as g cl P n (65 + 47 * j + i) =
      if i = 0 then (g (j + 1)).1
      else if i < 10 then fsPackVals (g (j + 1)).1 dsObserve (i - 1)
      else if i = 10 then (g (j + 1)).2
      else if i < 20 then fsPackVals (g (j + 1)).2 dsObserve (i - 11)
      else if i < 33 then cellsOfState (P (j + 1)) false (bsFin (i - 20))
      else if i < 40 then
        challengeVals (cellsOfState (P (j + 1)) false 0) (cellsOfState (P (j + 1)) false 1) (i - 33)
      else (bsFoldVals (cl (j + 1)) (g (j + 1)).1 (g (j + 1)).2 (challengeOf (P (j + 1)))).getD
        (i - 40) 0 := by
  rw [bsVals, show (65 + 47 * j + i - 65) / 47 = j by omega,
    show (65 + 47 * j + i - 65) % 47 = i by omega]
  repeat bs_if

theorem bsVals_suffix {n i : ℕ} (hn : 1 ≤ n) (hi : i < 6) :
    bsVals as g cl P n (18 + 47 * n + i) =
      if i < 5 then cellsOfState (P (n - 1)) false (bsFin (8 + i)) else cl n := by
  rw [bsVals, show (18 + 47 * n + i - 65) / 47 = n - 1 by omega,
    show (18 + 47 * n + i - 65) % 47 = i by omega]
  repeat bs_if

theorem bsVals_cellsAt {n j : ℕ} (hj : j < n) (c : Fin 13) :
    bsVals as g cl P n (38 + 47 * j + c.val) = cellsOfState (P j) false c := by
  have hc := c.isLt
  cases j with
  | zero =>
    rw [bsVals]
    repeat bs_if
    congr 1; apply bsFin_eq; omega
  | succ i =>
    rw [show 38 + 47 * (i + 1) + c.val = 65 + 47 * i + (20 + c.val) by ring,
      bsVals_round as g cl P hj (by omega)]
    repeat bs_if
    congr 1; apply bsFin_eq; omega

theorem bsVals_chalAt {n j u : ℕ} (hj : j < n) (hu : u < 7) :
    bsVals as g cl P n (38 + 47 * j + 13 + u) =
      challengeVals (cellsOfState (P j) false 0) (cellsOfState (P j) false 1) u := by
  cases j with
  | zero =>
    rw [bsVals]
    repeat bs_if
    congr 1; omega
  | succ i =>
    rw [show 38 + 47 * (i + 1) + 13 + u = 65 + 47 * i + (33 + u) by ring,
      bsVals_round as g cl P hj (by omega)]
    repeat bs_if
    congr 1; omega

theorem bsVals_foldAt {n j u : ℕ} (hj : j < n) (hu : u < 7) :
    bsVals as g cl P n (38 + 47 * j + 20 + u) =
      (bsFoldVals (cl j) (g j).1 (g j).2 (challengeOf (P j))).getD u 0 := by
  cases j with
  | zero =>
    rw [bsVals]
    repeat bs_if
    congr 1; omega
  | succ i =>
    rw [show 38 + 47 * (i + 1) + 20 + u = 65 + 47 * i + (40 + u) by ring,
      bsVals_round as g cl P hj (by omega)]
    repeat bs_if
    congr 1; omega

end

theorem bs_complete {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = bsParams)
    (hbody : f.body = bsBody n) (rd : Reader) (args rets : List E)
    (h : MeaningBatchSumcheck n rd args rets) : coreProgram.Rel rd name args rets := by
  obtain ⟨f0, f1, f2, f3, f4, msgs, running, point, rfl⟩ : ∃ f0 f1 f2 f3 f4 msgs running point,
      args = [f0, f1, f2, f3, f4, msgs, running, point] := by
    match args, h with
    | [f0, f1, f2, f3, f4, msgs, running, point], _ =>
      exact ⟨f0, f1, f2, f3, f4, msgs, running, point, rfl⟩
  obtain ⟨hcan, rounds, hlen, hmsgs, hres⟩ := h
  let g : ℕ → E × E := fun j ↦ rounds.getD j (0, 0)
  have hrounds : rounds = (List.range n).map g := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp [g, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  rw [hrounds, flatMap_pairs] at hmsgs
  have hm : ∀ j, j < n → LoadHolds rd msgs (2 * j) (g j).1 ∧ LoadHolds rd msgs (2 * j + 1) (g j).2 := by
    intro j hj
    have a := hmsgs (2 * j) (by simp; omega)
    have b := hmsgs (2 * j + 1) (by simp; omega)
    simp only [List.getElem_map, List.getElem_range, show 2 * j % 2 = 0 by omega,
      show 2 * j / 2 = j by omega, ↓reduceIte] at a
    simp only [List.getElem_map, List.getElem_range, show (2 * j + 1) % 2 = 1 by omega,
      show (2 * j + 1) / 2 = j by omega, one_ne_zero, ↓reduceIte] at b
    exact ⟨a, b⟩
  let cap := [f0, f1, f2, f3, f4]
  let St := bsSt g running ⟨cap, []⟩
  let P := bsP g running ⟨cap, []⟩
  let cl : ℕ → E := fun j ↦ (St j).1
  simp only [hrounds, bsRun_range1, bsRun_range2, bsRun_range3] at hres
  obtain ⟨hpt, hret⟩ := hres
  have hpt : ∀ j, j < n → LoadHolds rd point j (challengeOf (P j)) := by
    intro j hj
    have := hpt j (by simp; omega)
    simp only [List.getElem_map, List.getElem_range] at this
    exact this
  let as := [f0, f1, f2, f3, f4, msgs, running, point]
  let σ : Val := fun v ↦ bsVals as g cl P n v.idx
  have ev : ∀ k, σ (.n k) = bsVals as g cl P n k := fun _ ↦ rfl
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have pc : ∀ x t, (fsPackVals x t 6, fsPackVals x t 8) = Keccak.scalarCells x t := fsPackVals_cells
  have pcan : ∀ x t, IsCanonical128 (fsPackVals x t 6) ∧ IsCanonical128 (fsPackVals x t 8) :=
    fsPackVals_canonical
  have zc : IsCanonical128 (0 : E) := by
    rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have kcan : ∀ (L : List E), (∀ x ∈ L, IsCanonical128 x) → ∀ c : Fin 13,
      IsCanonical128 (cells13 L c) := by
    intro L hL c
    simp only [cells13, List.getD_eq_getElem?_getD]
    cases h : L[c.val]? with
    | none => exact zc
    | some x => exact hL x (List.mem_of_getElem? h)
  have e5 : σ (.n 5) = msgs := by simp [ev, bsVals, as]
  have e7 : σ (.n 7) = point := by simp [ev, bsVals, as]
  have vr : ∀ j i, j + 1 < n → i < 47 → σ (.n (65 + 47 * j + i)) = _ :=
    fun j i hj hi ↦ bsVals_round as g cl P hj hi
  have vc : ∀ j, j < n → ∀ c : Fin 13, σ (.n (38 + 47 * j + c.val)) = cellsOfState (P j) false c :=
    fun j hj c ↦ bsVals_cellsAt as g cl P hj c
  have vch : ∀ j u, j < n → u < 7 → σ (.n (38 + 47 * j + 13 + u)) =
      challengeVals (cellsOfState (P j) false 0) (cellsOfState (P j) false 1) u :=
    fun j u hj hu ↦ bsVals_chalAt as g cl P hj hu
  have vf : ∀ j u, j < n → u < 7 → σ (.n (38 + 47 * j + 20 + u)) =
      (bsFoldVals (cl j) (g j).1 (g j).2 (challengeOf (P j))).getD u 0 :=
    fun j u hj hu ↦ bsVals_foldAt as g cl P hj hu
  -- what one round asks, on its words at `b`, `b + 10`
  have roundOk : ∀ j, j < n → ∀ b, b = bsG j →
      σ (.n (b + 0)) = (g j).1 → σ (.n (b + 10)) = (g j).2 →
      (∀ u, u < 9 → σ (.n (b + 1 + u)) = fsPackVals (g j).1 dsObserve u) →
      (∀ u, u < 9 → σ (.n (b + 11 + u)) = fsPackVals (g j).2 dsObserve u) →
      (LoadHolds rd (σ (.n 5)) (2 * j) (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve) ∧
      (LoadHolds rd (σ (.n 5)) (2 * j + 1) (σ (.n (b + 10))) ∧
        FsPackOk σ (.n (b + 10)) (b + 10 + 1) dsObserve) ∧
      ChallengeOk σ (.n (38 + 47 * j)) (.n (38 + 47 * j + 1)) (38 + 47 * j + 13) ∧
      BsFoldOk rd σ (38 + 47 * j) (bsC j) b j := by
    intro j hj b hb g1 g2 p1 p2
    have g1' : σ (.n b) = (g j).1 := g1
    have c0 : σ (.n (38 + 47 * j)) = cellsOfState (P j) false 0 := vc j hj 0
    have c1 : σ (.n (38 + 47 * j + 1)) = cellsOfState (P j) false 1 := vc j hj 1
    have hr : σ (.n (38 + 47 * j + 19)) = challengeOf (P j) := by
      rw [← challengeVals_six, ← vch j 6 hj (by omega)]
    have hcl : σ (.n (bsC j)) = cl j := by
      cases j with
      | zero => simp [bsC, ev, bsVals, as, cl, St, bsSt]
      | succ i =>
        rw [show bsC (i + 1) = 38 + 47 * i + 20 + 6 by simp only [bsC]; ring, vf i 6 (by omega) (by omega)]
        rfl
    refine ⟨⟨by rw [e5, g1']; exact (hm j hj).1, fsPackOk_of_vals fun u hu ↦ by rw [p1 u hu, g1']⟩,
      ⟨by rw [e5, g2]; exact (hm j hj).2, fsPackOk_of_vals fun u hu ↦ ?_⟩,
      challengeOk_of_vals (by rw [c1]; exact cellsOfState_canonical _ _ _) fun u hu ↦ ?_, ?_⟩
    · rw [show b + 10 + 1 + u = b + 11 + u by ring, p2 u hu, g2]
    · rw [c0, c1]; exact vch j u hj hu
    · have f : ∀ u, u < 7 → σ (.n (38 + 47 * j + 20 + u)) = _ := fun u hu ↦ vf j u hj hu
      have f0 := f 0 (by omega)
      have f1 := f 1 (by omega)
      have f2 := f 2 (by omega)
      have f3 := f 3 (by omega)
      have f4 := f 4 (by omega)
      have f5 := f 5 (by omega)
      have f6 := f 6 (by omega)
      simp only [bsFoldVals, List.getD_cons_succ, List.getD_cons_zero,
        Nat.add_zero] at f0 f1 f2 f3 f4 f5 f6
      refine ⟨by rw [e7, hr]; exact hpt j hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [f0, hcl, g1']
      · rw [show 38 + 47 * j + 21 = 38 + 47 * j + 20 + 1 by ring, f1, f0, g1']
      · rw [show 38 + 47 * j + 22 = 38 + 47 * j + 20 + 2 by ring, f2,
          show 38 + 47 * j + 21 = 38 + 47 * j + 20 + 1 by ring, f1, g2]
      · rw [show 38 + 47 * j + 23 = 38 + 47 * j + 20 + 3 by ring, f3, g2, hr]
      · rw [show 38 + 47 * j + 24 = 38 + 47 * j + 20 + 4 by ring, f4,
          show 38 + 47 * j + 23 = 38 + 47 * j + 20 + 3 by ring, f3,
          show 38 + 47 * j + 22 = 38 + 47 * j + 20 + 2 by ring, f2]
      · rw [show 38 + 47 * j + 25 = 38 + 47 * j + 20 + 5 by ring, f5,
          show 38 + 47 * j + 24 = 38 + 47 * j + 20 + 4 by ring, f4, hr]
      · rw [show 38 + 47 * j + 26 = 38 + 47 * j + 20 + 6 by ring, f6,
          show 38 + 47 * j + 25 = 38 + 47 * j + 20 + 5 by ring, f5, f0]
  have capCan : ∀ j, j < n → (St j).2.cap.length = 5 ∧ AllCanonical (St j).2.cap := by
    intro j hj
    cases j with
    | zero => exact ⟨rfl, hcan⟩
    | succ i =>
      refine ⟨rfl, fun x hx ↦ ?_⟩
      simp only [St, bsSt_cap_succ, capOf, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact cellsOfState_canonical _ _ _
  have keccakOk : ∀ j, j < n → ∀ ins : List V, ins.map σ =
      [fsPackVals (g j).1 dsObserve 6, fsPackVals (g j).1 dsObserve 8, fsPackVals (g j).2 dsObserve 6,
        fsPackVals (g j).2 dsObserve 8, 0, 0, 0, 0] ++ (St j).2.cap →
      (Atom.keccak ins (bsRun13 (38 + 47 * j)) false false).Holds rd σ := by
    intro j hj ins hins
    obtain ⟨hl, hc⟩ := capCan j hj
    have hlen : ins.length = 13 := by
      have := congrArg List.length hins
      simp only [List.length_map, List.length_append, hl] at this
      simpa using this
    refine keccak13_mk (rd := rd) hlen rfl (kcan _ fun x hx ↦ ?_) fun c ↦ ?_
    · rw [hins] at hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | h
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      all_goals first | exact zc | exact hc x h
    · rw [cells13_bsRun13, vc j hj c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      show _ = permOf _
      rw [hins]
      show bsP g running ⟨cap, []⟩ j = _
      rw [bsP_eq]
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
        ← pc]
      rfl
  have hg0 : ∀ u, u < 9 → σ (.n (13 + 1 + u)) = fsPackVals (g 0).1 dsObserve u := by
    intro u hu; interval_cases u <;> simp [ev, bsVals]
  have hg0' : ∀ u, u < 9 → σ (.n (13 + 11 + u)) = fsPackVals (g 0).2 dsObserve u := by
    intro u hu; interval_cases u <;> simp [ev, bsVals]
  have hgj : ∀ j, j + 1 < n → σ (.n (65 + 47 * j + 0)) = (g (j + 1)).1 ∧
      σ (.n (65 + 47 * j + 10)) = (g (j + 1)).2 ∧
      (∀ u, u < 9 → σ (.n (65 + 47 * j + 1 + u)) = fsPackVals (g (j + 1)).1 dsObserve u) ∧
      (∀ u, u < 9 → σ (.n (65 + 47 * j + 11 + u)) = fsPackVals (g (j + 1)).2 dsObserve u) := by
    intro j hj
    refine ⟨?_, ?_, fun u hu ↦ ?_, fun u hu ↦ ?_⟩
    · rw [vr j 0 hj (by omega)]; simp
    · rw [vr j 10 hj (by omega)]; simp
    · rw [show 65 + 47 * j + 1 + u = 65 + 47 * j + (1 + u) by ring, vr j (1 + u) hj (by omega)]
      simp only [show ¬ (1 + u = 0) by omega, show 1 + u < 10 by omega, ↓reduceIte,
        show 1 + u - 1 = u by omega]
    · rw [show 65 + 47 * j + 11 + u = 65 + 47 * j + (11 + u) by ring, vr j (11 + u) hj (by omega)]
      simp only [show ¬ (11 + u = 0) by omega, show ¬ (11 + u < 10) by omega,
        show ¬ (11 + u = 10) by omega, show 11 + u < 20 by omega, ↓reduceIte,
        show 11 + u - 11 = u by omega]
  rw [rel_iff_sem hfind, hbody, hparams, bsBody, bsRound0]
  simp only [holdsList_append, holdsList_range_flatten (n - 1) bsRound (fun _ => rfl),
    holds_bsRound, holds_fsNextT, holds_challengeT, holds_bsFold, keccakA, Stmt.HoldsList,
    Stmt.Holds, List.map_cons, List.map_nil]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨l0, p0⟩, ⟨l1, p1⟩, ch0, fo0⟩ := roundOk 0 hn 13 rfl (by simp [ev, bsVals])
    (by simp [ev, bsVals]) hg0 hg0'
  have hsuf : ∀ i, i < 6 → σ (.n (18 + 47 * (m + 1) + i)) =
      if i < 5 then cellsOfState (P m) false (bsFin (8 + i)) else cl (m + 1) :=
    fun i hi ↦ bsVals_suffix as g cl P (by omega) hi
  have sc : ∀ i (hi : i < 5), σ (.n (18 + 47 * (m + 1) + i)) = cellsOfState (P m) false ⟨8 + i, by omega⟩ := by
    intro i hi
    rw [hsuf i (by omega)]
    simp only [hi, ↓reduceIte]
    congr 1; apply bsFin_eq; simp; omega
  have scl : σ (.n (18 + 47 * (m + 1) + 5)) = cl (m + 1) := by
    rw [hsuf 5 (by omega)]; rfl
  have fl : σ (.n (38 + 47 * m + 20 + 6)) = cl (m + 1) := by
    rw [vf m 6 (by omega) (by omega)]; rfl
  refine ⟨σ, by simp [ev, bsVals, as], ?_, ?_, ?_, ?_, ?_, ⟨l0, p0⟩, ⟨l1, p1⟩, ?_, ?_, ?_, ?_, ?_,
    keccakOk 0 hn _ (by simp [ev, bsVals, as, St, bsSt, cap]), ch0, fo0, fun j hj ↦ ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (show σ _ = _; simp [ev, bsVals, as, word_one, word_zero]; done)
  · obtain ⟨e0, e10, ep1, ep2⟩ := hgj j (by omega)
    obtain ⟨⟨la, pa⟩, ⟨lb, pb⟩, chj, foj⟩ :=
      roundOk (j + 1) (by omega) (65 + 47 * j) (by simp only [bsG]) e0 e10 ep1 ep2
    have e1 : 38 + 47 * (j + 1) = 85 + 47 * j := by ring
    rw [e1] at chj foj
    refine ⟨⟨by simpa [show 2 * (j + 1) = 2 * j + 2 by ring] using la, pa⟩,
      ⟨by simpa [show 2 * (j + 1) + 1 = 2 * j + 3 by ring,
          show 65 + 47 * j + 10 = 75 + 47 * j by ring] using lb,
        by simpa [show 65 + 47 * j + 10 = 75 + 47 * j by ring] using pb⟩, ?_, ?_, ?_⟩
    · rw [show 85 + 47 * j = 38 + 47 * (j + 1) by ring]
      apply keccakOk (j + 1) (by omega)
      have a6 : σ (.n (72 + 47 * j)) = _ := (idx _ (65 + 47 * j + 1 + 6) (by ring)).trans (ep1 6 (by omega))
      have a8 : σ (.n (74 + 47 * j)) = _ := (idx _ (65 + 47 * j + 1 + 8) (by ring)).trans (ep1 8 (by omega))
      have b6 : σ (.n (82 + 47 * j)) = _ := (idx _ (65 + 47 * j + 11 + 6) (by ring)).trans (ep2 6 (by omega))
      have b8 : σ (.n (84 + 47 * j)) = _ := (idx _ (65 + 47 * j + 11 + 8) (by ring)).trans (ep2 8 (by omega))
      have z : ∀ k, 34 ≤ k → k < 38 → σ (.n k) = 0 := by
        intro k h1 h2; interval_cases k <;> simp [ev, bsVals]
      have q8 : σ (.n (46 + 47 * j)) = cellsOfState (P j) false 8 :=
        (idx _ (38 + 47 * j + (8 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 8)
      have q9 : σ (.n (47 + 47 * j)) = cellsOfState (P j) false 9 :=
        (idx _ (38 + 47 * j + (9 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 9)
      have q10 : σ (.n (48 + 47 * j)) = cellsOfState (P j) false 10 :=
        (idx _ (38 + 47 * j + (10 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 10)
      have q11 : σ (.n (49 + 47 * j)) = cellsOfState (P j) false 11 :=
        (idx _ (38 + 47 * j + (11 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 11)
      have q12 : σ (.n (50 + 47 * j)) = cellsOfState (P j) false 12 :=
        (idx _ (38 + 47 * j + (12 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 12)
      simp only [List.map_cons, List.map_nil, a6, a8, b6, b8, z 34 (by omega) (by omega),
        z 35 (by omega) (by omega), z 36 (by omega) (by omega), z 37 (by omega) (by omega), q8, q9,
        q10, q11, q12]
      rfl
    · simpa [show 85 + 47 * j + 1 = 86 + 47 * j by ring, show 85 + 47 * j + 13 = 98 + 47 * j by ring]
        using chj
    · simpa [bsC] using foj
  · show σ (.n (18 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 8))
    rw [idx (18 + 47 * (m + 1)) (18 + 47 * (m + 1) + 0) (by ring), sc 0 (by omega),
      idx (38 + 47 * (m + 1 - 1) + 8) (38 + 47 * m + (8 : Fin 13).val) (by simp), vc m (by omega)]
    rfl
  · show σ (.n (19 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 9))
    rw [idx (19 + 47 * (m + 1)) (18 + 47 * (m + 1) + 1) (by ring), sc 1 (by omega),
      idx (38 + 47 * (m + 1 - 1) + 9) (38 + 47 * m + (9 : Fin 13).val) (by simp), vc m (by omega)]
    rfl
  · show σ (.n (20 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 10))
    rw [idx (20 + 47 * (m + 1)) (18 + 47 * (m + 1) + 2) (by ring), sc 2 (by omega),
      idx (38 + 47 * (m + 1 - 1) + 10) (38 + 47 * m + (10 : Fin 13).val) (by simp), vc m (by omega)]
    rfl
  · show σ (.n (21 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 11))
    rw [idx (21 + 47 * (m + 1)) (18 + 47 * (m + 1) + 3) (by ring), sc 3 (by omega),
      idx (38 + 47 * (m + 1 - 1) + 11) (38 + 47 * m + (11 : Fin 13).val) (by simp), vc m (by omega)]
    rfl
  · show σ (.n (22 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 12))
    rw [idx (22 + 47 * (m + 1)) (18 + 47 * (m + 1) + 4) (by ring), sc 4 (by omega),
      idx (38 + 47 * (m + 1 - 1) + 12) (38 + 47 * m + (12 : Fin 13).val) (by simp), vc m (by omega)]
    rfl
  · show σ (.n (23 + 47 * (m + 1))) = σ (.n (38 + 47 * (m + 1 - 1) + 26))
    rw [idx (23 + 47 * (m + 1)) (18 + 47 * (m + 1) + 5) (by ring), scl,
      idx (38 + 47 * (m + 1 - 1) + 26) (38 + 47 * m + 20 + 6) (by simp), fl]
  · rw [hret]
    rw [idx (19 + 47 * (m + 1)) (18 + 47 * (m + 1) + 1) (by ring),
      idx (20 + 47 * (m + 1)) (18 + 47 * (m + 1) + 2) (by ring),
      idx (21 + 47 * (m + 1)) (18 + 47 * (m + 1) + 3) (by ring),
      idx (22 + 47 * (m + 1)) (18 + 47 * (m + 1) + 4) (by ring),
      idx (23 + 47 * (m + 1)) (18 + 47 * (m + 1) + 5) (by ring),
      show σ (.n (18 + 47 * (m + 1))) = _ from sc 0 (by omega), sc 1 (by omega), sc 2 (by omega),
      sc 3 (by omega), sc 4 (by omega), scl]
    rfl

set_option maxRecDepth 100000 in
theorem bs23_body : Fn.body Data.core409 = bsBody 23 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **`batch_sumcheck`'s core IR is its meaning.** -/
theorem batch_sumcheck_holds : batch_sumcheck_Spec := by
  intro rd args rets
  have hfind : coreProgram.find? "batch_sumcheck__L23" = some Data.core409 :=
    Program.find?_of_indexOf? (j := 409) (by decide +kernel) rfl
  exact ⟨bs_sound 23 (by decide) hfind rfl bs23_body rd args rets,
    bs_complete 23 (by decide) hfind rfl bs23_body rd args rets⟩

end
end LeanVM.Guest.B1
