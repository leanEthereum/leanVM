/-
  LeanVM.Guest.B1.Sumcheck.Batch

  B1 for `batch_sumcheck`: the claim-batching sumcheck, one generic argument over the rounds.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `batch_sumcheck` (TRIAGE #32)

Its body at `n` rounds (`bsBody n`): the capacity copied into `9 .. 13`; round `0` (`bsRound0`):
`g(1)`, `g(∞)` read at `msgs[0]`, `msgs[1]` and packed (`fsNextT` from `14`, `17`), the pad run
`20 .. 24` (`padRunT`), the permutation into `25 .. 37` (`fs_grind_squeeze` at zero bits), its
challenge (at `38`) stored at `point[0]`, the fold (`39 .. 45`); round `j + 1` (`bsRound j`): the
same from `46 + 27 j`, its permutation into `52 + 27 j`, reading the zero run `21 .. 24`; the
final capacity and claim copied and returned. Round `j`'s permutation writes from `25 + 27 j`.
The window table `.n 8` is not read.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Thirteen consecutive values. -/
def bsRun13 (b : ℕ) : List V := (List.range 13).map fun i ↦ .n (b + i)

/-- The fold of round `r` whose permutation writes from `o` (its challenge at `o + 13`), its
claim `c`, its words at `b`, `b + 3`. -/
def bsFold (o c b : ℕ) (r : ℕ) : List Stmt :=
  [.atom (.load (.n (o + 13)) (.n 7) r),
    .atom (.add (.n (o + 14)) (.n c) (.n b)), .atom (.add (.n (o + 15)) (.n (o + 14)) (.n b)),
    .atom (.add (.n (o + 16)) (.n (o + 15)) (.n (b + 3))),
    .atom (.mul (.n (o + 17)) (.n (b + 3)) (.n (o + 13))),
    .atom (.add (.n (o + 18)) (.n (o + 17)) (.n (o + 16))),
    .atom (.mul (.n (o + 19)) (.n (o + 18)) (.n (o + 13))),
    .atom (.add (.n (o + 20)) (.n (o + 19)) (.n (o + 14)))]

/-- Round `0`. -/
def bsRound0 : List Stmt :=
  fsNextT (.n 5) 0 14 ++ fsNextT (.n 5) 1 17 ++ padRunT 20 ++
  [keccakA [.n 15, .n 16, .n 18, .n 19, .n 21, .n 22, .n 23, .n 24, .n 9, .n 10, .n 11, .n 12, .n 13]
      (bsRun13 25)] ++
  challengeT (.n 25) 38 ++ bsFold 25 6 14 0

/-- Round `j + 1`. -/
def bsRound (j : ℕ) : List Stmt :=
  fsNextT (.n 5) (2 * j + 2) (46 + 27 * j) ++ fsNextT (.n 5) (2 * j + 3) (49 + 27 * j) ++
  [keccakA [.n (47 + 27 * j), .n (48 + 27 * j), .n (50 + 27 * j), .n (51 + 27 * j), .n 21, .n 22,
      .n 23, .n 24, .n (33 + 27 * j), .n (34 + 27 * j), .n (35 + 27 * j), .n (36 + 27 * j),
      .n (37 + 27 * j)] (bsRun13 (52 + 27 * j))] ++
  challengeT (.n (52 + 27 * j)) (65 + 27 * j) ++
  bsFold (52 + 27 * j) (45 + 27 * j) (46 + 27 * j) (j + 1)

/-- The expansion of `batch_sumcheck` at `n ≥ 1` rounds. -/
def bsBody (n : ℕ) : List Stmt :=
  [.atom (.copy (.n 9) (.n 0)), .atom (.copy (.n 10) (.n 1)), .atom (.copy (.n 11) (.n 2)),
    .atom (.copy (.n 12) (.n 3)), .atom (.copy (.n 13) (.n 4))] ++
  bsRound0 ++ ((List.range (n - 1)).map bsRound).flatten ++
  [.atom (.copy (.n (19 + 27 * n)) (.n (25 + 27 * (n - 1) + 8))),
    .atom (.copy (.n (20 + 27 * n)) (.n (25 + 27 * (n - 1) + 9))),
    .atom (.copy (.n (21 + 27 * n)) (.n (25 + 27 * (n - 1) + 10))),
    .atom (.copy (.n (22 + 27 * n)) (.n (25 + 27 * (n - 1) + 11))),
    .atom (.copy (.n (23 + 27 * n)) (.n (25 + 27 * (n - 1) + 12))),
    .atom (.copy (.n (24 + 27 * n)) (.n (25 + 27 * (n - 1) + 20))),
    .ret [.n (19 + 27 * n), .n (20 + 27 * n), .n (21 + 27 * n), .n (22 + 27 * n), .n (23 + 27 * n),
      .n (24 + 27 * n)]]

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
  LoadHolds rd (σ (.n 7)) r (σ (.n (o + 13))) ∧ σ (.n (o + 14)) = σ (.n c) + σ (.n b) ∧
    σ (.n (o + 15)) = σ (.n (o + 14)) + σ (.n b) ∧
    σ (.n (o + 16)) = σ (.n (o + 15)) + σ (.n (b + 3)) ∧
    σ (.n (o + 17)) = σ (.n (b + 3)) * σ (.n (o + 13)) ∧
    σ (.n (o + 18)) = σ (.n (o + 17)) + σ (.n (o + 16)) ∧
    σ (.n (o + 19)) = σ (.n (o + 18)) * σ (.n (o + 13)) ∧
    σ (.n (o + 20)) = σ (.n (o + 19)) + σ (.n (o + 14))

theorem holds_bsFold (o c b r : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (bsFold o c b r) next kret ↔ BsFoldOk rd σ o c b r ∧ next := by
  simp only [bsFold, BsFoldOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

/-- The fold's value. -/
theorem bsFold_value {o c b r : ℕ} (h : BsFoldOk rd σ o c b r) :
    σ (.n (o + 20)) = (σ (.n (b + 3)) * σ (.n (o + 13)) + (σ (.n c) + σ (.n b) + σ (.n b) +
      σ (.n (b + 3)))) * σ (.n (o + 13)) + (σ (.n c) + σ (.n b)) := by
  obtain ⟨-, h14, h15, h16, h17, h18, h19, h20⟩ := h
  rw [h20, h19, h18, h17, h16, h15, h14]

/-- What round `j + 1` asks. -/
theorem holds_bsRound (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (bsRound j) True kret ↔
      (LoadHolds rd (σ (.n 5)) (2 * j + 2) (σ (.n (46 + 27 * j))) ∧
        FsPackOk σ (.n (46 + 27 * j)) (46 + 27 * j + 1) dsObserve) ∧
      (LoadHolds rd (σ (.n 5)) (2 * j + 3) (σ (.n (49 + 27 * j))) ∧
        FsPackOk σ (.n (49 + 27 * j)) (49 + 27 * j + 1) dsObserve) ∧
      (Atom.keccak [.n (47 + 27 * j), .n (48 + 27 * j), .n (50 + 27 * j), .n (51 + 27 * j), .n 21,
        .n 22, .n 23, .n 24, .n (33 + 27 * j), .n (34 + 27 * j), .n (35 + 27 * j),
        .n (36 + 27 * j), .n (37 + 27 * j)] (bsRun13 (52 + 27 * j)) false false).Holds rd σ ∧
      ChallengeOk σ (.n (52 + 27 * j)) (65 + 27 * j) ∧
      BsFoldOk rd σ (52 + 27 * j) (45 + 27 * j) (46 + 27 * j) (j + 1) := by
  simp only [bsRound, keccakA, holdsList_append, holds_fsNextT, holds_challengeT, holds_bsFold,
    Stmt.HoldsList, Stmt.Holds, and_true]

theorem cells13_bsRun13 (σ : Val) (b : ℕ) (c : Fin 13) :
    cells13 ((bsRun13 b).map σ) c = σ (.n (b + c.val)) := by
  simp [cells13, bsRun13, List.getD_eq_getElem?_getD]

theorem keccak_bsRun13 {ins : List V} {b : ℕ}
    (h : (Atom.keccak ins (bsRun13 b) false false).Holds rd σ) :
    ∀ c : Fin 13, σ (.n (b + c.val)) = cellsOfState (permOf (ins.map σ)) false c := by
  obtain ⟨-, -, hout⟩ := keccakA_perm h
  intro c
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

/-- The nine parameters. -/
abbrev bsParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8]

/-- Where round `j`'s words sit. -/
def bsG : ℕ → ℕ
  | 0 => 14
  | j + 1 => 46 + 27 * j

/-- Where the claim round `j` starts from sits. -/
def bsC : ℕ → ℕ
  | 0 => 6
  | j + 1 => 45 + 27 * j

/-- The rate cells of a round's two words. -/
theorem bs_pend (a b : E) :
    pendCells [(a, dsObserve), (b, dsObserve)] = [a, word 0 dsObserve, b, word 0 dsObserve] := rfl

theorem bs_sound {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = bsParams)
    (hbody : f.body = bsBody n) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningBatchSumcheck n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, bsBody, bsRound0] at h
  simp only [holdsList_append, holdsList_range_flatten (n - 1) bsRound (fun _ => rfl),
    holds_bsRound, holds_fsNextT, holds_padRunT, holds_challengeT, holds_bsFold, keccakA,
    Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, h9, h10, h11, h12, h13, ⟨l0, p0⟩, ⟨l1, p1⟩, ⟨-, z21, z22, z23, z24⟩, hK0, hch0,
    hf0, hrounds, c0, c1, c2, c3, c4, c5, hret⟩ := h
  subst hp
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have h9 : σ (.n 9) = σ (.n 0) := h9
  have h10 : σ (.n 10) = σ (.n 1) := h10
  have h11 : σ (.n 11) = σ (.n 2) := h11
  have h12 : σ (.n 12) = σ (.n 3) := h12
  have h13 : σ (.n 13) = σ (.n 4) := h13
  have z21 : σ (.n 21) = 0 := z21
  have z22 : σ (.n 22) = 0 := z22
  have z23 : σ (.n 23) = 0 := z23
  have z24 : σ (.n 24) = 0 := z24
  set g : ℕ → E × E := fun j ↦ (σ (.n (bsG j)), σ (.n (bsG j + 3))) with hg
  set cap0 := [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] with hcap0
  set St := bsSt g (σ (.n 6)) ⟨cap0, []⟩ with hSt
  set P := bsP g (σ (.n 6)) ⟨cap0, []⟩ with hP
  -- round j's facts
  have hR : ∀ j, j < n → (∀ c : Fin 13, σ (.n (25 + 27 * j + c.val)) = cellsOfState (P j) false c) →
      σ (.n (25 + 27 * j + 13)) = challengeOf (P j) ∧
        BsFoldOk rd σ (25 + 27 * j) (bsC j) (bsG j) j := by
    intro j hj hB
    cases j with
    | zero => exact ⟨challengeT_value hch0 (hB 0), hf0⟩
    | succ i =>
      obtain ⟨-, -, -, hch, hf⟩ := hrounds i (by omega)
      have e : 25 + 27 * (i + 1) = 52 + 27 * i := by ring
      rw [e] at hB ⊢
      have b0 : σ (.n (52 + 27 * i)) = cellsOfState (P (i + 1)) false 0 := hB 0
      exact ⟨(idx _ (65 + 27 * i) (by ring)).trans (challengeT_value hch b0), hf⟩
  have hAB : ∀ j, j < n → σ (.n (bsC j)) = (St j).1 ∧
      ∀ c : Fin 13, σ (.n (25 + 27 * j + c.val)) = cellsOfState (P j) false c := by
    intro j
    induction j with
    | zero =>
      intro hj
      refine ⟨rfl, fun c ↦ ?_⟩
      have hout := keccak_bsRun13 hK0
      rw [show 25 + 27 * 0 + c.val = 25 + c.val by ring, hout c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      have e15 : σ (.n 15) = σ (.n 14) := p0.1
      have e16 : σ (.n 16) = word 0 dsObserve := p0.2
      have e18 : σ (.n 18) = σ (.n 17) := p1.1
      have e19 : σ (.n 19) = word 0 dsObserve := p1.2
      rw [hP, bsP_eq, bs_pend]
      simp only [List.map_cons, List.map_nil, hg, bsG, e15, e16, e18, e19, z21, z22, z23, z24,
        h9, h10, h11, h12, h13]
      rfl
    | succ j ih =>
      intro hj
      obtain ⟨hA, hB⟩ := ih (by omega)
      obtain ⟨hr, hf⟩ := hR j (by omega) hB
      refine ⟨?_, fun c ↦ ?_⟩
      · rw [idx (bsC (j + 1)) (25 + 27 * j + 20) (by simp only [bsC]; ring), bsFold_value hf, hr,
          hA]
        rfl
      · obtain ⟨⟨-, q0⟩, ⟨-, q1⟩, hK, -, -⟩ := hrounds j (by omega)
        have hout := keccak_bsRun13 hK
        rw [idx _ (52 + 27 * j + c.val) (by ring), hout c]
        refine congrArg (fun S ↦ cellsOfState S false c) ?_
        have ea : σ (.n (47 + 27 * j)) = σ (.n (46 + 27 * j)) :=
          (idx _ (46 + 27 * j + 1) (by ring)).trans q0.1
        have ea' : σ (.n (48 + 27 * j)) = word 0 dsObserve :=
          (idx _ (46 + 27 * j + 1 + 1) (by ring)).trans q0.2
        have eb : σ (.n (50 + 27 * j)) = σ (.n (49 + 27 * j)) :=
          (idx _ (49 + 27 * j + 1) (by ring)).trans q1.1
        have eb' : σ (.n (51 + 27 * j)) = word 0 dsObserve :=
          (idx _ (49 + 27 * j + 1 + 1) (by ring)).trans q1.2
        have i8 : σ (.n (33 + 27 * j)) = cellsOfState (P j) false 8 :=
          (idx _ (25 + 27 * j + (8 : Fin 13).val) (by simp; ring)).trans (hB 8)
        have i9 : σ (.n (34 + 27 * j)) = cellsOfState (P j) false 9 :=
          (idx _ (25 + 27 * j + (9 : Fin 13).val) (by simp; ring)).trans (hB 9)
        have i10 : σ (.n (35 + 27 * j)) = cellsOfState (P j) false 10 :=
          (idx _ (25 + 27 * j + (10 : Fin 13).val) (by simp; ring)).trans (hB 10)
        have i11 : σ (.n (36 + 27 * j)) = cellsOfState (P j) false 11 :=
          (idx _ (25 + 27 * j + (11 : Fin 13).val) (by simp; ring)).trans (hB 11)
        have i12 : σ (.n (37 + 27 * j)) = cellsOfState (P j) false 12 :=
          (idx _ (25 + 27 * j + (12 : Fin 13).val) (by simp; ring)).trans (hB 12)
        have gb : g (j + 1) = (σ (.n (46 + 27 * j)), σ (.n (49 + 27 * j))) := by
          simp only [hg, bsG]
          rw [idx (46 + 27 * j + 3) (49 + 27 * j) (by ring)]
        rw [hP, bsP_eq, bsSt_cap_succ, ← hP, gb, bs_pend]
        simp only [List.map_cons, List.map_nil, ea, ea', eb, eb', z21, z22, z23, z24, i8, i9, i10,
          i11, i12]
        rfl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hAm, hBm⟩ := hAB m (by omega)
  obtain ⟨hrm, hfm⟩ := hR m (by omega) hBm
  have hAn : σ (.n (bsC (m + 1))) = (St (m + 1)).1 := by
    rw [idx (bsC (m + 1)) (25 + 27 * m + 20) (by simp only [bsC]; ring), bsFold_value hfm, hrm,
      hAm]
    rfl
  refine ⟨(List.range (m + 1)).map g, by simp, ?_, ?_⟩
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
        rw [idx (46 + 27 * i + 3) (49 + 27 * i) (by ring)]
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
      have c0' : σ (.n (19 + 27 * (m + 1))) = cellsOfState (P m) false 8 := by
        rw [show σ (.n (19 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 8)) from c0]
        exact (idx _ (25 + 27 * m + (8 : Fin 13).val) (by simp)).trans (hBm 8)
      have c1' : σ (.n (20 + 27 * (m + 1))) = cellsOfState (P m) false 9 := by
        rw [show σ (.n (20 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 9)) from c1]
        exact (idx _ (25 + 27 * m + (9 : Fin 13).val) (by simp)).trans (hBm 9)
      have c2' : σ (.n (21 + 27 * (m + 1))) = cellsOfState (P m) false 10 := by
        rw [show σ (.n (21 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 10)) from c2]
        exact (idx _ (25 + 27 * m + (10 : Fin 13).val) (by simp)).trans (hBm 10)
      have c3' : σ (.n (22 + 27 * (m + 1))) = cellsOfState (P m) false 11 := by
        rw [show σ (.n (22 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 11)) from c3]
        exact (idx _ (25 + 27 * m + (11 : Fin 13).val) (by simp)).trans (hBm 11)
      have c4' : σ (.n (23 + 27 * (m + 1))) = cellsOfState (P m) false 12 := by
        rw [show σ (.n (23 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 12)) from c4]
        exact (idx _ (25 + 27 * m + (12 : Fin 13).val) (by simp)).trans (hBm 12)
      have c5' : σ (.n (24 + 27 * (m + 1))) = σ (.n (bsC (m + 1))) := by
        rw [show σ (.n (24 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 20)) from c5]
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

/-- A round's six word values: `g(1)`, its copy and tag cell, `g(∞)`, its copy and tag cell. -/
def bsWordVals (w : E × E) : List E := [w.1, w.1, word 0 dsObserve, w.2, w.2, word 0 dsObserve]

/-- Round `j + 1`'s values, by offset from `46 + 27 j`. -/
def bsRoundVal (g : ℕ → E × E) (cl : ℕ → E) (P : ℕ → KeccakState) (j i : ℕ) : E :=
  if i < 6 then (bsWordVals (g (j + 1))).getD i 0
  else if i < 19 then cellsOfState (P (j + 1)) false (bsFin (i - 6))
  else if i = 19 then challengeOf (P (j + 1))
  else (bsFoldVals (cl (j + 1)) (g (j + 1)).1 (g (j + 1)).2 (challengeOf (P (j + 1)))).getD
    (i - 20) 0

/-- The honest values of `batch_sumcheck` at `n` rounds, by index, on the rounds' words `g`, the
claims `cl` and the permutations `P`. -/
def bsVals (as : List E) (g : ℕ → E × E) (cl : ℕ → E) (P : ℕ → KeccakState) (n k : ℕ) : E :=
  if k < 9 then as.getD k 0
  else if k < 14 then as.getD (k - 9) 0
  else if k < 20 then (bsWordVals (g 0)).getD (k - 14) 0
  else if k = 20 then word 1 0
  else if k < 25 then 0
  else if k < 38 then cellsOfState (P 0) false (bsFin (k - 25))
  else if k = 38 then challengeOf (P 0)
  else if k < 46 then (bsFoldVals (cl 0) (g 0).1 (g 0).2 (challengeOf (P 0))).getD (k - 39) 0
  else if (k - 46) / 27 + 1 < n then bsRoundVal g cl P ((k - 46) / 27) ((k - 46) % 27)
  else if (k - 46) % 27 < 5 then cellsOfState (P (n - 1)) false (bsFin (8 + (k - 46) % 27))
  else cl n

/-- Decide the next `if` of an unfolded index function by `omega`. -/
macro "bs_if" : tactic => `(tactic| first
  | (rw [ite_eq_right_of_eq_false]; rotate_left; exact eq_false (by omega))
  | (rw [ite_eq_left_of_eq_true]; rotate_left; exact eq_true (by omega)))

section
variable (as : List E) (g : ℕ → E × E) (cl : ℕ → E) (P : ℕ → KeccakState)

theorem bsVals_round {n j i : ℕ} (hj : j + 1 < n) (hi : i < 27) :
    bsVals as g cl P n (46 + 27 * j + i) = bsRoundVal g cl P j i := by
  rw [bsVals, show (46 + 27 * j + i - 46) / 27 = j by omega,
    show (46 + 27 * j + i - 46) % 27 = i by omega]
  repeat bs_if

theorem bsVals_suffix {n i : ℕ} (hn : 1 ≤ n) (hi : i < 6) :
    bsVals as g cl P n (19 + 27 * n + i) =
      if i < 5 then cellsOfState (P (n - 1)) false (bsFin (8 + i)) else cl n := by
  rw [bsVals, show (19 + 27 * n + i - 46) / 27 = n - 1 by omega,
    show (19 + 27 * n + i - 46) % 27 = i by omega]
  repeat bs_if

theorem bsVals_wordsAt {n j u : ℕ} (hj : j < n) (hu : u < 6) :
    bsVals as g cl P n (bsG j + u) = (bsWordVals (g j)).getD u 0 := by
  cases j with
  | zero =>
    simp only [bsG]
    rw [bsVals]
    repeat bs_if
    congr 1; omega
  | succ i =>
    rw [show bsG (i + 1) + u = 46 + 27 * i + u by simp only [bsG],
      bsVals_round as g cl P hj (by omega), bsRoundVal]
    repeat bs_if

theorem bsVals_cellsAt {n j : ℕ} (hj : j < n) (c : Fin 13) :
    bsVals as g cl P n (25 + 27 * j + c.val) = cellsOfState (P j) false c := by
  have hc := c.isLt
  cases j with
  | zero =>
    rw [bsVals]
    repeat bs_if
    congr 1; apply bsFin_eq; omega
  | succ i =>
    rw [show 25 + 27 * (i + 1) + c.val = 46 + 27 * i + (6 + c.val) by ring,
      bsVals_round as g cl P hj (by omega), bsRoundVal]
    repeat bs_if
    congr 1; apply bsFin_eq; omega

theorem bsVals_chalAt {n j : ℕ} (hj : j < n) :
    bsVals as g cl P n (25 + 27 * j + 13) = challengeOf (P j) := by
  cases j with
  | zero =>
    rw [bsVals]
    repeat bs_if
  | succ i =>
    rw [show 25 + 27 * (i + 1) + 13 = 46 + 27 * i + 19 by ring,
      bsVals_round as g cl P hj (by omega), bsRoundVal]
    repeat bs_if

theorem bsVals_foldAt {n j u : ℕ} (hj : j < n) (hu : u < 7) :
    bsVals as g cl P n (25 + 27 * j + 14 + u) =
      (bsFoldVals (cl j) (g j).1 (g j).2 (challengeOf (P j))).getD u 0 := by
  cases j with
  | zero =>
    rw [bsVals]
    repeat bs_if
    congr 1; omega
  | succ i =>
    rw [show 25 + 27 * (i + 1) + 14 + u = 46 + 27 * i + (20 + u) by ring,
      bsVals_round as g cl P hj (by omega), bsRoundVal]
    repeat bs_if
    congr 1; omega

end

theorem bs_complete {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = bsParams)
    (hbody : f.body = bsBody n) (rd : Reader) (args rets : List E)
    (h : MeaningBatchSumcheck n rd args rets) : coreProgram.Rel rd name args rets := by
  obtain ⟨f0, f1, f2, f3, f4, msgs, running, point, tabs, rfl⟩ :
      ∃ f0 f1 f2 f3 f4 msgs running point tabs,
        args = [f0, f1, f2, f3, f4, msgs, running, point, tabs] := by
    match args, h with
    | [f0, f1, f2, f3, f4, msgs, running, point, tabs], _ =>
      exact ⟨f0, f1, f2, f3, f4, msgs, running, point, tabs, rfl⟩
  obtain ⟨rounds, hlen, hmsgs, hres⟩ := h
  let g : ℕ → E × E := fun j ↦ rounds.getD j (0, 0)
  have hrounds : rounds = (List.range n).map g := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp [g, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  rw [hrounds, flatMap_pairs] at hmsgs
  have hm : ∀ j, j < n → LoadHolds rd msgs (2 * j) (g j).1 ∧
      LoadHolds rd msgs (2 * j + 1) (g j).2 := by
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
  let as := [f0, f1, f2, f3, f4, msgs, running, point, tabs]
  let σ : Val := fun v ↦ bsVals as g cl P n v.idx
  have ev : ∀ k, σ (.n k) = bsVals as g cl P n k := fun _ ↦ rfl
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have e5 : σ (.n 5) = msgs := by simp [ev, bsVals, as]
  have e7 : σ (.n 7) = point := by simp [ev, bsVals, as]
  have vw : ∀ j u, j < n → u < 6 → σ (.n (bsG j + u)) = (bsWordVals (g j)).getD u 0 :=
    fun j u hj hu ↦ bsVals_wordsAt as g cl P hj hu
  have vc : ∀ j, j < n → ∀ c : Fin 13, σ (.n (25 + 27 * j + c.val)) = cellsOfState (P j) false c :=
    fun j hj c ↦ bsVals_cellsAt as g cl P hj c
  have vch : ∀ j, j < n → σ (.n (25 + 27 * j + 13)) = challengeOf (P j) :=
    fun j hj ↦ bsVals_chalAt as g cl P hj
  have vf : ∀ j u, j < n → u < 7 → σ (.n (25 + 27 * j + 14 + u)) =
      (bsFoldVals (cl j) (g j).1 (g j).2 (challengeOf (P j))).getD u 0 :=
    fun j u hj hu ↦ bsVals_foldAt as g cl P hj hu
  -- what one round asks, on its words at `bsG j`
  have roundOk : ∀ j, j < n →
      (LoadHolds rd (σ (.n 5)) (2 * j) (σ (.n (bsG j))) ∧
        FsPackOk σ (.n (bsG j)) (bsG j + 1) dsObserve) ∧
      (LoadHolds rd (σ (.n 5)) (2 * j + 1) (σ (.n (bsG j + 3))) ∧
        FsPackOk σ (.n (bsG j + 3)) (bsG j + 3 + 1) dsObserve) ∧
      ChallengeOk σ (.n (25 + 27 * j)) (25 + 27 * j + 13) ∧
      BsFoldOk rd σ (25 + 27 * j) (bsC j) (bsG j) j := by
    intro j hj
    have w0 : σ (.n (bsG j)) = (g j).1 := by
      have := vw j 0 hj (by omega); simpa [bsWordVals] using this
    have w1 : σ (.n (bsG j + 1)) = (g j).1 := by
      have := vw j 1 hj (by omega); simpa [bsWordVals] using this
    have w2 : σ (.n (bsG j + 1 + 1)) = word 0 dsObserve := by
      have := vw j 2 hj (by omega); simpa [bsWordVals] using this
    have w3 : σ (.n (bsG j + 3)) = (g j).2 := by
      have := vw j 3 hj (by omega); simpa [bsWordVals] using this
    have w4 : σ (.n (bsG j + 3 + 1)) = (g j).2 := by
      have := vw j 4 hj (by omega); simpa [bsWordVals] using this
    have w5 : σ (.n (bsG j + 3 + 1 + 1)) = word 0 dsObserve := by
      have := vw j 5 hj (by omega); simpa [bsWordVals] using this
    have c0 : σ (.n (25 + 27 * j)) = cellsOfState (P j) false 0 := vc j hj 0
    have hr : σ (.n (25 + 27 * j + 13)) = challengeOf (P j) := vch j hj
    have hcl : σ (.n (bsC j)) = cl j := by
      cases j with
      | zero => simp [bsC, ev, bsVals, as, cl, St, bsSt]
      | succ i =>
        rw [show bsC (i + 1) = 25 + 27 * i + 14 + 6 by simp only [bsC]; ring,
          vf i 6 (by omega) (by omega)]
        rfl
    refine ⟨⟨by rw [e5, w0]; exact (hm j hj).1, by rw [w1, w0], w2⟩,
      ⟨by rw [e5, w3]; exact (hm j hj).2, by rw [w4, w3], w5⟩,
      by rw [ChallengeOk, hr, c0, Keccak.challengeOf_cells], ?_⟩
    have f : ∀ u, u < 7 → σ (.n (25 + 27 * j + 14 + u)) = _ := fun u hu ↦ vf j u hj hu
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
    · rw [f0, hcl, w0]
    · rw [show 25 + 27 * j + 15 = 25 + 27 * j + 14 + 1 by ring, f1, f0, w0]
    · rw [show 25 + 27 * j + 16 = 25 + 27 * j + 14 + 2 by ring, f2,
        show 25 + 27 * j + 15 = 25 + 27 * j + 14 + 1 by ring, f1, w3]
    · rw [show 25 + 27 * j + 17 = 25 + 27 * j + 14 + 3 by ring, f3, w3, hr]
    · rw [show 25 + 27 * j + 18 = 25 + 27 * j + 14 + 4 by ring, f4,
        show 25 + 27 * j + 17 = 25 + 27 * j + 14 + 3 by ring, f3,
        show 25 + 27 * j + 16 = 25 + 27 * j + 14 + 2 by ring, f2]
    · rw [show 25 + 27 * j + 19 = 25 + 27 * j + 14 + 5 by ring, f5,
        show 25 + 27 * j + 18 = 25 + 27 * j + 14 + 4 by ring, f4, hr]
    · rw [show 25 + 27 * j + 20 = 25 + 27 * j + 14 + 6 by ring, f6,
        show 25 + 27 * j + 19 = 25 + 27 * j + 14 + 5 by ring, f5, f0]
  have keccakOk : ∀ j, j < n → ∀ ins : List V, ins.map σ =
      [(g j).1, word 0 dsObserve, (g j).2, word 0 dsObserve, 0, 0, 0, 0] ++ (St j).2.cap →
      (Atom.keccak ins (bsRun13 (25 + 27 * j)) false false).Holds rd σ := by
    intro j hj ins hins
    have hlen : ins.length = 13 := by
      have := congrArg List.length hins
      simp only [List.length_map, List.length_append] at this
      rw [this]
      cases j with
      | zero => rfl
      | succ i => rfl
    refine keccak13_mk (rd := rd) hlen rfl fun c ↦ ?_
    rw [cells13_bsRun13, vc j hj c]
    refine congrArg (fun S ↦ cellsOfState S false c) ?_
    show _ = permOf _
    rw [hins]
    show bsP g running ⟨cap, []⟩ j = _
    rw [bsP_eq, bs_pend]
    rfl
  rw [rel_iff_sem hfind, hbody, hparams, bsBody, bsRound0]
  simp only [holdsList_append, holdsList_range_flatten (n - 1) bsRound (fun _ => rfl),
    holds_bsRound, holds_fsNextT, holds_padRunT, holds_challengeT, holds_bsFold, keccakA,
    Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨⟨l0, p0⟩, ⟨l1, p1⟩, ch0, fo0⟩ := roundOk 0 hn
  have hsuf : ∀ i, i < 6 → σ (.n (19 + 27 * (m + 1) + i)) =
      if i < 5 then cellsOfState (P m) false (bsFin (8 + i)) else cl (m + 1) :=
    fun i hi ↦ bsVals_suffix as g cl P (by omega) hi
  have sc : ∀ i (hi : i < 5), σ (.n (19 + 27 * (m + 1) + i)) =
      cellsOfState (P m) false ⟨8 + i, by omega⟩ := by
    intro i hi
    rw [hsuf i (by omega)]
    simp only [hi, ↓reduceIte]
    congr 1; apply bsFin_eq; simp; omega
  have scl : σ (.n (19 + 27 * (m + 1) + 5)) = cl (m + 1) := by
    rw [hsuf 5 (by omega)]; rfl
  have fl : σ (.n (25 + 27 * m + 14 + 6)) = cl (m + 1) := by
    rw [vf m 6 (by omega) (by omega)]; rfl
  refine ⟨σ, by simp [ev, bsVals, as], ?_, ?_, ?_, ?_, ?_, ⟨l0, p0⟩, ⟨l1, p1⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, keccakOk 0 hn _ ?_, ch0, fo0, fun j hj ↦ ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (show σ _ = _; simp [ev, bsVals, as]; done)
  · simp [ev, bsVals, as, St, bsSt, cap, bsWordVals, g]
  · obtain ⟨⟨la, pa⟩, ⟨lb, pb⟩, chj, foj⟩ := roundOk (j + 1) (by omega)
    simp only [bsG] at la pa lb pb foj
    have e1 : 25 + 27 * (j + 1) = 52 + 27 * j := by ring
    rw [e1] at chj foj
    refine ⟨⟨by simpa [show 2 * (j + 1) = 2 * j + 2 by ring] using la, pa⟩,
      ⟨by simpa [show 2 * (j + 1) + 1 = 2 * j + 3 by ring,
          show 46 + 27 * j + 3 = 49 + 27 * j by ring] using lb,
        by simpa [show 46 + 27 * j + 3 = 49 + 27 * j by ring] using pb⟩, ?_, ?_, ?_⟩
    · rw [show 52 + 27 * j = 25 + 27 * (j + 1) by ring]
      apply keccakOk (j + 1) (by omega)
      have w : ∀ u, u < 6 → σ (.n (46 + 27 * j + u)) = (bsWordVals (g (j + 1))).getD u 0 :=
        fun u hu ↦ vw (j + 1) u (by omega) hu
      have a1 : σ (.n (47 + 27 * j)) = (g (j + 1)).1 := by
        rw [idx _ (46 + 27 * j + 1) (by ring), w 1 (by omega)]; rfl
      have a2 : σ (.n (48 + 27 * j)) = word 0 dsObserve := by
        rw [idx _ (46 + 27 * j + 2) (by ring), w 2 (by omega)]; rfl
      have b1 : σ (.n (50 + 27 * j)) = (g (j + 1)).2 := by
        rw [idx _ (46 + 27 * j + 4) (by ring), w 4 (by omega)]; rfl
      have b2 : σ (.n (51 + 27 * j)) = word 0 dsObserve := by
        rw [idx _ (46 + 27 * j + 5) (by ring), w 5 (by omega)]; rfl
      have z : ∀ k, 21 ≤ k → k < 25 → σ (.n k) = 0 := by
        intro k h1 h2; interval_cases k <;> simp [ev, bsVals]
      have q8 : σ (.n (33 + 27 * j)) = cellsOfState (P j) false 8 :=
        (idx _ (25 + 27 * j + (8 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 8)
      have q9 : σ (.n (34 + 27 * j)) = cellsOfState (P j) false 9 :=
        (idx _ (25 + 27 * j + (9 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 9)
      have q10 : σ (.n (35 + 27 * j)) = cellsOfState (P j) false 10 :=
        (idx _ (25 + 27 * j + (10 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 10)
      have q11 : σ (.n (36 + 27 * j)) = cellsOfState (P j) false 11 :=
        (idx _ (25 + 27 * j + (11 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 11)
      have q12 : σ (.n (37 + 27 * j)) = cellsOfState (P j) false 12 :=
        (idx _ (25 + 27 * j + (12 : Fin 13).val) (by simp; ring)).trans (vc j (by omega) 12)
      simp only [List.map_cons, List.map_nil, a1, a2, b1, b2, z 21 (by omega) (by omega),
        z 22 (by omega) (by omega), z 23 (by omega) (by omega), z 24 (by omega) (by omega), q8, q9,
        q10, q11, q12]
      rfl
    · simpa [show 52 + 27 * j + 13 = 65 + 27 * j by ring] using chj
    · simpa [bsC] using foj
  · show σ (.n (19 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 8))
    rw [idx (19 + 27 * (m + 1)) (19 + 27 * (m + 1) + 0) (by ring), sc 0 (by omega),
      idx (25 + 27 * (m + 1 - 1) + 8) (25 + 27 * m + (8 : Fin 13).val) (by simp), vc m (by omega)]
    rfl
  · show σ (.n (20 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 9))
    rw [idx (20 + 27 * (m + 1)) (19 + 27 * (m + 1) + 1) (by ring), sc 1 (by omega),
      idx (25 + 27 * (m + 1 - 1) + 9) (25 + 27 * m + (9 : Fin 13).val) (by simp), vc m (by omega)]
    rfl
  · show σ (.n (21 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 10))
    rw [idx (21 + 27 * (m + 1)) (19 + 27 * (m + 1) + 2) (by ring), sc 2 (by omega),
      idx (25 + 27 * (m + 1 - 1) + 10) (25 + 27 * m + (10 : Fin 13).val) (by simp),
      vc m (by omega)]
    rfl
  · show σ (.n (22 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 11))
    rw [idx (22 + 27 * (m + 1)) (19 + 27 * (m + 1) + 3) (by ring), sc 3 (by omega),
      idx (25 + 27 * (m + 1 - 1) + 11) (25 + 27 * m + (11 : Fin 13).val) (by simp),
      vc m (by omega)]
    rfl
  · show σ (.n (23 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 12))
    rw [idx (23 + 27 * (m + 1)) (19 + 27 * (m + 1) + 4) (by ring), sc 4 (by omega),
      idx (25 + 27 * (m + 1 - 1) + 12) (25 + 27 * m + (12 : Fin 13).val) (by simp),
      vc m (by omega)]
    rfl
  · show σ (.n (24 + 27 * (m + 1))) = σ (.n (25 + 27 * (m + 1 - 1) + 20))
    rw [idx (24 + 27 * (m + 1)) (19 + 27 * (m + 1) + 5) (by ring), scl,
      idx (25 + 27 * (m + 1 - 1) + 20) (25 + 27 * m + 14 + 6) (by simp), fl]
  · rw [hret]
    rw [idx (20 + 27 * (m + 1)) (19 + 27 * (m + 1) + 1) (by ring),
      idx (21 + 27 * (m + 1)) (19 + 27 * (m + 1) + 2) (by ring),
      idx (22 + 27 * (m + 1)) (19 + 27 * (m + 1) + 3) (by ring),
      idx (23 + 27 * (m + 1)) (19 + 27 * (m + 1) + 4) (by ring),
      idx (24 + 27 * (m + 1)) (19 + 27 * (m + 1) + 5) (by ring),
      show σ (.n (19 + 27 * (m + 1))) = _ from sc 0 (by omega), sc 1 (by omega), sc 2 (by omega),
      sc 3 (by omega), sc 4 (by omega), scl]
    rfl

set_option maxRecDepth 100000 in
theorem bs23_body : Fn.body Data.core446 = bsBody 23 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **`batch_sumcheck`'s core IR is its meaning.** -/
theorem batch_sumcheck_holds : batch_sumcheck_Spec := by
  intro rd args rets
  have hfind : coreProgram.find? "batch_sumcheck__L23" = some Data.core446 :=
    Program.find?_of_indexOf? (j := 446) (by decide +kernel) rfl
  exact ⟨bs_sound 23 (by decide) hfind rfl bs23_body rd args rets,
    bs_complete 23 (by decide) hfind rfl bs23_body rd args rets⟩

end
end LeanVM.Guest.B1
