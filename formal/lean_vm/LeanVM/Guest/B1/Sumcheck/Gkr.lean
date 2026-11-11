/-
  LeanVM.Guest.B1.Sumcheck.Gkr

  B1 for `gkr_rounds`: equality-mode sumcheck rounds between GKR round records.
-/

module

public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run

/-!
# `gkr_rounds` (G:1121-1144, TRIAGE #31)

Its body at `n` rounds (`gkBody n`): the record's capacity, cursor and claim loaded into `2 .. 8`;
round `q` (`gkRound q`, from `9 + 74 q`): four stream words read and packed, the permutation of
the four waiting with the previous capacity into `49 + 74 q`, its challenge (at `68 + 74 q`), the
previous coordinate `pt[q]`, the derived `c0`, the challenge stored at `pt[42 + q]`, the claim at
the challenge (at `82 + 74 q`); the next record's capacity, cursor and claim stored.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Thirteen consecutive values. -/
def gkRun13 (b : ℕ) : List V := (List.range 13).map fun i ↦ .n (b + i)

/-- Where round `q` reads the previous capacity. -/
def gkCapPrev : ℕ → ℕ
  | 0 => 2
  | q + 1 => 57 + 74 * q

/-- Round `q`. -/
def gkRound (q : ℕ) : List Stmt :=
  fsNextT (.n 7) (4 * q) (9 + 74 * q) ++ fsNextT (.n 7) (4 * q + 1) (19 + 74 * q) ++
  fsNextT (.n 7) (4 * q + 2) (29 + 74 * q) ++ fsNextT (.n 7) (4 * q + 3) (39 + 74 * q) ++
  [keccakA [.n (16 + 74 * q), .n (18 + 74 * q), .n (26 + 74 * q), .n (28 + 74 * q),
      .n (36 + 74 * q), .n (38 + 74 * q), .n (46 + 74 * q), .n (48 + 74 * q),
      .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
      .n (gkCapPrev q + 4)] (gkRun13 (49 + 74 * q))] ++
  challengeT (.n (49 + 74 * q)) (.n (50 + 74 * q)) (62 + 74 * q) ++
  [.atom (.load (.n (69 + 74 * q)) (.n 1) q),
    .atom (.add (.n (70 + 74 * q)) (.n (9 + 74 * q)) (.n (19 + 74 * q))),
    .atom (.add (.n (71 + 74 * q)) (.n (70 + 74 * q)) (.n (29 + 74 * q))),
    .atom (.add (.n (72 + 74 * q)) (.n (71 + 74 * q)) (.n (39 + 74 * q))),
    .atom (.mul (.n (73 + 74 * q)) (.n (69 + 74 * q)) (.n (72 + 74 * q))),
    .atom (.add (.n (74 + 74 * q)) (.n (8 + 74 * q)) (.n (73 + 74 * q))),
    .atom (.load (.n (68 + 74 * q)) (.n 1) (42 + q)),
    .atom (.mul (.n (75 + 74 * q)) (.n (68 + 74 * q)) (.n (39 + 74 * q))),
    .atom (.add (.n (76 + 74 * q)) (.n (29 + 74 * q)) (.n (75 + 74 * q))),
    .atom (.mul (.n (77 + 74 * q)) (.n (68 + 74 * q)) (.n (76 + 74 * q))),
    .atom (.add (.n (78 + 74 * q)) (.n (19 + 74 * q)) (.n (77 + 74 * q))),
    .atom (.mul (.n (79 + 74 * q)) (.n (68 + 74 * q)) (.n (78 + 74 * q))),
    .atom (.add (.n (80 + 74 * q)) (.n (9 + 74 * q)) (.n (79 + 74 * q))),
    .atom (.mul (.n (81 + 74 * q)) (.n (68 + 74 * q)) (.n (80 + 74 * q))),
    .atom (.add (.n (82 + 74 * q)) (.n (74 + 74 * q)) (.n (81 + 74 * q)))]

/-- The expansion of `gkr_rounds` at `n ≥ 1` rounds. -/
def gkBody (n : ℕ) : List Stmt :=
  [.atom (.load (.n 2) (.n 0) 0), .atom (.load (.n 3) (.n 0) 862), .atom (.load (.n 4) (.n 0) 1724),
    .atom (.load (.n 5) (.n 0) 2586), .atom (.load (.n 6) (.n 0) 3448),
    .atom (.load (.n 7) (.n 0) 4310), .atom (.load (.n 8) (.n 0) 5172)] ++
  ((List.range n).map gkRound).flatten ++
  [.atom (.load (.n (57 + 74 * (n - 1))) (.n 0) n),
    .atom (.load (.n (58 + 74 * (n - 1))) (.n 0) (n + 862)),
    .atom (.load (.n (59 + 74 * (n - 1))) (.n 0) (n + 1724)),
    .atom (.load (.n (60 + 74 * (n - 1))) (.n 0) (n + 2586)),
    .atom (.load (.n (61 + 74 * (n - 1))) (.n 0) (n + 3448)),
    .atom (.const (.n (9 + 74 * n)) (word (2 ^ (4 * n)) 0 0)),
    .atom (.mul (.n (10 + 74 * n)) (.n 7) (.n (9 + 74 * n))),
    .atom (.load (.n (10 + 74 * n)) (.n 0) (n + 4310)),
    .atom (.load (.n (82 + 74 * (n - 1))) (.n 0) (n + 5172)),
    .atom (.const (.n (11 + 74 * n)) (word 0 0 0)),
    .ret [.n (11 + 74 * n)]]

/-! ## The rounds as a sequence -/

/-- The claim and the sponge after the first `q` rounds of `gkrRun`, round `q` on the words
`Cf q` and the coordinate `ef q`. -/
def gkSt (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs) : ℕ → E × Fs
  | 0 => (claim, s)
  | q + 1 =>
    let st := gkSt Cf ef claim s q
    let r := (st.2.absorbAll (Cf q) dsObserve).squeeze
    (polyEval ((st.1 + ef q * sumE (Cf q)) :: Cf q) r.1, r.2)

/-- Round `q`'s permutation. -/
def gkP (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs) (q : ℕ) : KeccakState :=
  ((gkSt Cf ef claim s q).2.absorbAll (Cf q) dsObserve).perm

theorem gkSt_shift (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs) :
    ∀ q, gkSt Cf ef claim s (q + 1) =
      gkSt (fun i ↦ Cf (i + 1)) (fun i ↦ ef (i + 1)) (gkSt Cf ef claim s 1).1
        (gkSt Cf ef claim s 1).2 q
  | 0 => rfl
  | q + 1 => by
    rw [gkSt, gkSt_shift Cf ef claim s q]
    rfl

theorem gk_range_succ_map {α : Type} (f : ℕ → α) (n : ℕ) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map fun i ↦ f (i + 1) := by
  simp [List.range_succ_eq_map, List.map_map, Function.comp_def]

theorem gkrRun_cons (Cf : ℕ → List E) (ef : ℕ → E) (L : List (List E)) (M : List E) (claim : E)
    (s : Fs) :
    gkrRun (Cf 0 :: L) (ef 0 :: M) claim s =
      (((s.absorbAll (Cf 0) dsObserve).squeeze.1 ::
        (gkrRun L M (gkSt Cf ef claim s 1).1 (gkSt Cf ef claim s 1).2).1,
        (gkrRun L M (gkSt Cf ef claim s 1).1 (gkSt Cf ef claim s 1).2).2)) := rfl

theorem gkrRun_range1 : ∀ (n : ℕ) (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs),
    (gkrRun ((List.range n).map Cf) ((List.range n).map ef) claim s).1 =
      (List.range n).map fun q ↦ challengeOf (gkP Cf ef claim s q)
  | 0, _, _, _, _ => rfl
  | n + 1, Cf, ef, claim, s => by
    rw [gk_range_succ_map Cf, gk_range_succ_map ef, gkrRun_cons, gkrRun_range1 n,
      gk_range_succ_map]
    refine congrArg (List.cons _) (List.map_congr_left fun i _ ↦ ?_)
    simp only [gkP]
    rw [gkSt_shift Cf ef claim s i]

theorem gkrRun_range2 : ∀ (n : ℕ) (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (s : Fs),
    (gkrRun ((List.range n).map Cf) ((List.range n).map ef) claim s).2 = gkSt Cf ef claim s n
  | 0, _, _, _, _ => rfl
  | n + 1, Cf, ef, claim, s => by
    rw [gk_range_succ_map Cf, gk_range_succ_map ef, gkrRun_cons, gkrRun_range2 n,
      gkSt_shift Cf ef claim s n]

theorem gkSt_empty (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (cap : List E) :
    ∀ q, (gkSt Cf ef claim ⟨cap, []⟩ q).2 = ⟨(gkSt Cf ef claim ⟨cap, []⟩ q).2.cap, []⟩
  | 0 => rfl
  | _ + 1 => rfl

/-- Round `q`'s permutation, its cells written out, on four words. -/
theorem gkP_eq (Cf : ℕ → List E) (ef : ℕ → E) (claim : E) (cap : List E) (q : ℕ) {a b c d : E}
    (hC : Cf q = [a, b, c, d]) :
    gkP Cf ef claim ⟨cap, []⟩ q = permOf (pendCells [(a, dsObserve), (b, dsObserve), (c, dsObserve),
      (d, dsObserve)] ++ (gkSt Cf ef claim ⟨cap, []⟩ q).2.cap) := by
  rw [gkP, gkSt_empty, hC, absorbAll_short _ _ _ (by simp), perm_eq_cells _ (by simp)]
  simp

/-- The guest's Horner form of a round polynomial. -/
theorem gk_eval (claim e c1 c2 c3 c4 r : E) :
    claim + e * (c1 + c2 + c3 + c4) + r * (c1 + r * (c2 + r * (c3 + r * c4))) =
      polyEval ((claim + e * sumE [c1, c2, c3, c4]) :: [c1, c2, c3, c4]) r := by
  simp only [polyEval, List.foldr, sumE, List.foldl, zero_add, zero_mul]
  ring

/-! ## Soundness -/

/-- What the arithmetic of round `q` asks. -/
def GkFoldOk (rd : Reader) (σ : Val) (q : ℕ) : Prop :=
  LoadHolds rd (σ (.n 1)) q (σ (.n (69 + 74 * q))) ∧
    σ (.n (70 + 74 * q)) = σ (.n (9 + 74 * q)) + σ (.n (19 + 74 * q)) ∧
    σ (.n (71 + 74 * q)) = σ (.n (70 + 74 * q)) + σ (.n (29 + 74 * q)) ∧
    σ (.n (72 + 74 * q)) = σ (.n (71 + 74 * q)) + σ (.n (39 + 74 * q)) ∧
    σ (.n (73 + 74 * q)) = σ (.n (69 + 74 * q)) * σ (.n (72 + 74 * q)) ∧
    σ (.n (74 + 74 * q)) = σ (.n (8 + 74 * q)) + σ (.n (73 + 74 * q)) ∧
    LoadHolds rd (σ (.n 1)) (42 + q) (σ (.n (68 + 74 * q))) ∧
    σ (.n (75 + 74 * q)) = σ (.n (68 + 74 * q)) * σ (.n (39 + 74 * q)) ∧
    σ (.n (76 + 74 * q)) = σ (.n (29 + 74 * q)) + σ (.n (75 + 74 * q)) ∧
    σ (.n (77 + 74 * q)) = σ (.n (68 + 74 * q)) * σ (.n (76 + 74 * q)) ∧
    σ (.n (78 + 74 * q)) = σ (.n (19 + 74 * q)) + σ (.n (77 + 74 * q)) ∧
    σ (.n (79 + 74 * q)) = σ (.n (68 + 74 * q)) * σ (.n (78 + 74 * q)) ∧
    σ (.n (80 + 74 * q)) = σ (.n (9 + 74 * q)) + σ (.n (79 + 74 * q)) ∧
    σ (.n (81 + 74 * q)) = σ (.n (68 + 74 * q)) * σ (.n (80 + 74 * q)) ∧
    σ (.n (82 + 74 * q)) = σ (.n (74 + 74 * q)) + σ (.n (81 + 74 * q))

/-- What round `q` asks. -/
theorem holds_gkRound (q : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gkRound q) True kret ↔
      (∀ t < 4, LoadHolds rd (σ (.n 7)) (4 * q + t) (σ (.n (9 + 74 * q + 10 * t))) ∧
        FsPackOk σ (.n (9 + 74 * q + 10 * t)) (9 + 74 * q + 10 * t + 1) dsObserve) ∧
      (Atom.keccak [.n (16 + 74 * q), .n (18 + 74 * q), .n (26 + 74 * q), .n (28 + 74 * q),
        .n (36 + 74 * q), .n (38 + 74 * q), .n (46 + 74 * q), .n (48 + 74 * q),
        .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
        .n (gkCapPrev q + 4)] (gkRun13 (49 + 74 * q)) false false).Holds rd σ ∧
      ChallengeOk σ (.n (49 + 74 * q)) (.n (50 + 74 * q)) (62 + 74 * q) ∧ GkFoldOk rd σ q := by
  simp only [gkRound, keccakA, holdsList_append, holds_fsNextT, holds_challengeT, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, GkFoldOk, and_true]
  constructor
  · rintro ⟨h0, h1, h2, h3, hk, hc, hf⟩
    refine ⟨fun t ht ↦ ?_, hk, hc, hf⟩
    interval_cases t
    · simpa using h0
    · simpa [show 4 * q + 1 = 4 * q + 1 by rfl, show 9 + 74 * q + 10 * 1 = 19 + 74 * q by ring]
        using h1
    · simpa [show 9 + 74 * q + 10 * 2 = 29 + 74 * q by ring] using h2
    · simpa [show 9 + 74 * q + 10 * 3 = 39 + 74 * q by ring] using h3
  · rintro ⟨h, hk, hc, hf⟩
    refine ⟨by simpa using h 0 (by omega), ?_, ?_, ?_, hk, hc, hf⟩
    · simpa [show 9 + 74 * q + 10 * 1 = 19 + 74 * q by ring] using h 1 (by omega)
    · simpa [show 9 + 74 * q + 10 * 2 = 29 + 74 * q by ring] using h 2 (by omega)
    · simpa [show 9 + 74 * q + 10 * 3 = 39 + 74 * q by ring] using h 3 (by omega)

theorem cells13_gkRun13 (σ : Val) (b : ℕ) (c : Fin 13) :
    cells13 ((gkRun13 b).map σ) c = σ (.n (b + c.val)) := by
  simp [cells13, gkRun13, List.getD_eq_getElem?_getD]

theorem keccak_gkRun13 {ins : List V} {b : ℕ}
    (h : (Atom.keccak ins (gkRun13 b) false false).Holds rd σ) :
    AllCanonical (ins.map σ) ∧
      ∀ c : Fin 13, σ (.n (b + c.val)) = cellsOfState (permOf (ins.map σ)) false c := by
  obtain ⟨-, -, hcan, hout⟩ := keccakA_perm h
  refine ⟨hcan, fun c => ?_⟩
  have := outs_eq hout c (by simp [gkRun13])
  simpa [gkRun13] using this

theorem readsAt_flatten4 {p : E} (Cf : ℕ → List E) (h4 : ∀ q, (Cf q).length = 4) :
    ∀ n, (∀ q < n, ∀ t < 4, LoadHolds rd p (4 * q + t) ((Cf q).getD t 0)) →
      ReadsAt rd p ((List.range n).map Cf).flatten
  | 0, _ => readsAt_nil rd p
  | n + 1, h => by
    intro k hk
    have hlen : ((List.range n).map Cf).flatten.length = 4 * n := by
      clear hk h
      induction n with
      | zero => rfl
      | succ n ih => simp [List.range_succ, h4, ih]; ring
    simp only [List.range_succ, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil] at hk ⊢
    rw [List.getElem_append]
    split_ifs with hkn
    · exact readsAt_flatten4 Cf h4 n (fun q hq t ht ↦ h q (by omega) t ht) k hkn
    · have hk' : k < 4 * n + 4 := by simpa [hlen, h4] using hk
      rw [hlen] at hkn
      have := h n (by omega) (k - 4 * n) (by omega)
      rw [show 4 * n + (k - 4 * n) = k by omega] at this
      convert this using 1
      simp [List.getD_eq_getElem?_getD, hlen, List.getElem?_eq_getElem (show k - 4 * n < (Cf n).length by rw [h4]; omega)]

/-- The two parameters. -/
abbrev gkParams : List V := [.n 0, .n 1]

theorem gk_sound {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n) (hn2 : n ≤ 6)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = gkParams)
    (hbody : f.body = gkBody n) (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd name args rets) : MeaningGkrRounds n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, gkBody] at h
  simp only [holdsList_append, holdsList_range_flatten n gkRound (fun _ => rfl), holds_gkRound,
    Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, l2, l3, l4, l5, l6, l7, l8, hrounds, s0, s1, s2, s3, s4, k, m, sc, sl, z, hret⟩ := h
  subst hp
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  set Cf : ℕ → List E := fun q ↦ [σ (.n (9 + 74 * q)), σ (.n (19 + 74 * q)), σ (.n (29 + 74 * q)),
    σ (.n (39 + 74 * q))] with hCf
  set ef : ℕ → E := fun q ↦ σ (.n (69 + 74 * q)) with hef
  set cap := [σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] with hcap
  set St := gkSt Cf ef (σ (.n 8)) ⟨cap, []⟩ with hSt
  set P := gkP Cf ef (σ (.n 8)) ⟨cap, []⟩ with hP
  have cells : ∀ q, q < n → ∀ t < 4,
      (σ (.n (9 + 74 * q + 10 * t + 7)), σ (.n (9 + 74 * q + 10 * t + 9))) =
        Keccak.scalarCells (σ (.n (9 + 74 * q + 10 * t))) dsObserve ∧
      LoadHolds rd (σ (.n 7)) (4 * q + t) (σ (.n (9 + 74 * q + 10 * t))) := by
    intro q hq t ht
    obtain ⟨hn, hk, -, -⟩ := hrounds q hq
    obtain ⟨hcan, -⟩ := keccak_gkRun13 hk
    obtain ⟨hl, hpk⟩ := hn t ht
    refine ⟨fsPackT_cells hpk (hcan _ ?_), hl⟩
    interval_cases t <;> simp <;> ring_nf <;> simp
  have hAB : ∀ q, q < n → σ (.n (8 + 74 * q)) = (St q).1 ∧
      ∀ c : Fin 13, σ (.n (49 + 74 * q + c.val)) = cellsOfState (P q) false c := by
    intro q
    induction q with
    | zero =>
      intro hq
      refine ⟨rfl, fun c ↦ ?_⟩
      obtain ⟨-, hk, -, -⟩ := hrounds 0 hq
      obtain ⟨-, hout⟩ := keccak_gkRun13 hk
      rw [hout c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      rw [hP, gkP_eq Cf ef _ cap 0 rfl]
      have e0 := (cells 0 hq 0 (by omega)).1
      have e1 := (cells 0 hq 1 (by omega)).1
      have e2 := (cells 0 hq 2 (by omega)).1
      have e3 := (cells 0 hq 3 (by omega)).1
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at e0 e1 e2 e3
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
        gkCapPrev, ← e0, ← e1, ← e2, ← e3]
      rfl
    | succ q ih =>
      intro hq
      obtain ⟨hA, hB⟩ := ih (by omega)
      obtain ⟨-, -, hch, hf⟩ := hrounds q (by omega)
      have b0 : σ (.n (49 + 74 * q)) = cellsOfState (P q) false 0 := hB 0
      have b1 : σ (.n (50 + 74 * q)) = cellsOfState (P q) false 1 :=
        (idx _ (49 + 74 * q + (1 : Fin 13).val) (by simp; ring)).trans (hB 1)
      have hr : σ (.n (68 + 74 * q)) = challengeOf (P q) :=
        (idx _ (62 + 74 * q + 6) (by ring)).trans (challengeT_value hch b0 b1)
      obtain ⟨-, f70, f71, f72, f73, f74, -, f75, f76, f77, f78, f79, f80, f81, f82⟩ := hf
      refine ⟨?_, fun c ↦ ?_⟩
      · rw [idx _ (82 + 74 * q) (by ring), f82, f81, f80, f79, f78, f77, f76, f75, f74, f73, f72,
          f71, f70, hA, hr]
        show _ = polyEval (((St q).1 + ef q * sumE (Cf q)) :: Cf q) (challengeOf (P q))
        rw [← gk_eval]
      · obtain ⟨-, hk, -, -⟩ := hrounds (q + 1) hq
        obtain ⟨-, hout⟩ := keccak_gkRun13 hk
        rw [hout c]
        refine congrArg (fun S ↦ cellsOfState S false c) ?_
        rw [hP, gkP_eq Cf ef _ cap (q + 1) rfl]
        have e0 := (cells (q + 1) hq 0 (by omega)).1
        have e1 := (cells (q + 1) hq 1 (by omega)).1
        have e2 := (cells (q + 1) hq 2 (by omega)).1
        have e3 := (cells (q + 1) hq 3 (by omega)).1
        rw [idx (9 + 74 * (q + 1) + 10 * 0) (9 + 74 * (q + 1)) (by ring)] at e0
        rw [idx (9 + 74 * (q + 1) + 10 * 1) (19 + 74 * (q + 1)) (by ring)] at e1
        rw [idx (9 + 74 * (q + 1) + 10 * 2) (29 + 74 * (q + 1)) (by ring)] at e2
        rw [idx (9 + 74 * (q + 1) + 10 * 3) (39 + 74 * (q + 1)) (by ring)] at e3
        have i8 : σ (.n (49 + 74 * q + 8)) = cellsOfState (P q) false 8 := hB 8
        have i9 : σ (.n (49 + 74 * q + 9)) = cellsOfState (P q) false 9 := hB 9
        have i10 : σ (.n (49 + 74 * q + 10)) = cellsOfState (P q) false 10 := hB 10
        have i11 : σ (.n (49 + 74 * q + 11)) = cellsOfState (P q) false 11 := hB 11
        have i12 : σ (.n (49 + 74 * q + 12)) = cellsOfState (P q) false 12 := hB 12
        simp only [gkCapPrev, List.map_cons, List.map_nil]
        rw [idx (16 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 0 + 7 by ring),
          idx (18 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 0 + 9 by ring),
          idx (26 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 1 + 7 by ring),
          idx (28 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 1 + 9 by ring),
          idx (36 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 2 + 7 by ring),
          idx (38 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 2 + 9 by ring),
          idx (46 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 3 + 7 by ring),
          idx (48 + 74 * (q + 1)) _ (show _ = 9 + 74 * (q + 1) + 10 * 3 + 9 by ring)]
        rw [idx (57 + 74 * q) _ (show _ = 49 + 74 * q + 8 by ring), i8,
          idx (57 + 74 * q + 1) _ (show _ = 49 + 74 * q + 9 by ring), i9,
          idx (57 + 74 * q + 2) _ (show _ = 49 + 74 * q + 10 by ring), i10,
          idx (57 + 74 * q + 3) _ (show _ = 49 + 74 * q + 11 by ring), i11,
          idx (57 + 74 * q + 4) _ (show _ = 49 + 74 * q + 12 by ring), i12]
        simp only [pendCells, List.flatMap_cons, List.flatMap_nil, ← e0, ← e1, ← e2, ← e3]
        rfl
  have hR : ∀ q, q < n → σ (.n (68 + 74 * q)) = challengeOf (P q) ∧ GkFoldOk rd σ q := by
    intro q hq
    obtain ⟨-, hB⟩ := hAB q hq
    obtain ⟨-, -, hch, hf⟩ := hrounds q hq
    have b0 : σ (.n (49 + 74 * q)) = cellsOfState (P q) false 0 := hB 0
    have b1 : σ (.n (50 + 74 * q)) = cellsOfState (P q) false 1 :=
      (idx _ (49 + 74 * q + (1 : Fin 13).val) (by simp; ring)).trans (hB 1)
    exact ⟨(idx _ (62 + 74 * q + 6) (by ring)).trans (challengeT_value hch b0 b1), hf⟩
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
  have hAn : σ (.n (82 + 74 * m')) = (St (m' + 1)).1 := by
    obtain ⟨hA, -⟩ := hAB m' (by omega)
    obtain ⟨hr, hf⟩ := hR m' (by omega)
    obtain ⟨-, f70, f71, f72, f73, f74, -, f75, f76, f77, f78, f79, f80, f81, f82⟩ := hf
    rw [f82, f81, f80, f79, f78, f77, f76, f75, f74, f73, f72, f71, f70, hA, hr]
    show _ = polyEval (((St m').1 + ef m' * sumE (Cf m')) :: Cf m') (challengeOf (P m'))
    rw [← gk_eval]
  obtain ⟨-, hBm⟩ := hAB m' (by omega)
  refine ⟨by rw [← hret]; exact congrArg (· :: []) ((show σ (.n (11 + 74 * (m' + 1))) = word 0 0 0 from z).trans word_zero), cap, σ (.n 7), σ (.n 8), (List.range (m' + 1)).map Cf,
    (List.range (m' + 1)).map ef, ⟨rfl, fun j hj ↦ ?_⟩, ?_, l7, l8, by simp, ?_, ?_, by simp, ?_, ?_⟩
  · simp only [hcap, List.length_cons, List.length_nil] at hj
    interval_cases j
    · exact l2
    · exact l3
    · exact l4
    · exact l5
    · exact l6
  · obtain ⟨-, hk, -, -⟩ := hrounds 0 (by omega)
    obtain ⟨hcan, -⟩ := keccak_gkRun13 hk
    intro x hx
    simp only [hcap, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact hcan _ (by simp [gkCapPrev])
  · intro c hc
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hc
    rfl
  · refine readsAt_flatten4 Cf (fun _ ↦ rfl) (m' + 1) fun q hq t ht ↦ ?_
    have := (cells q hq t ht).2
    interval_cases t
    · simpa [hCf] using this
    · simpa [hCf, show 9 + 74 * q + 10 * 1 = 19 + 74 * q by ring] using this
    · simpa [hCf, show 9 + 74 * q + 10 * 2 = 29 + 74 * q by ring] using this
    · simpa [hCf, show 9 + 74 * q + 10 * 3 = 39 + 74 * q by ring] using this
  · intro q hq
    simp only [List.length_map, List.length_range] at hq
    simp only [List.getElem_map, List.getElem_range, hef]
    exact (hR q hq).2.1
  · simp only
    rw [gkrRun_range1, gkrRun_range2]
    refine ⟨fun q hq ↦ ?_, ⟨rfl, fun j hj ↦ ?_⟩, ?_, ?_⟩
    · simp only [List.length_map, List.length_range] at hq
      simp only [List.getElem_map, List.getElem_range]
      obtain ⟨hr, -, -, -, -, -, -, hst, -⟩ := hR q hq
      rw [loadHolds_mul_gen_pow, ← hr]
      exact hst
    · simp only [gkSt, Fs.squeeze, capOf, List.length_cons, List.length_nil] at hj
      have st : ∀ i (hi : i < 5), LoadHolds rd (σ (.n 0)) (m' + 1 + i * 862)
          (cellsOfState (P m') false ⟨8 + i, by omega⟩) := by
        intro i hi
        have e := hBm ⟨8 + i, by omega⟩
        rw [← e, idx (49 + 74 * m' + (8 + i)) (57 + 74 * (m' + 1 - 1) + i) (by simp; ring)]
        interval_cases i
        · exact s0
        · rw [idx (57 + 74 * (m' + 1 - 1) + 1) (58 + 74 * (m' + 1 - 1)) (by ring), show m' + 1 + 1 * 862 = m' + 1 + 862 by ring]
          exact s1
        · rw [idx (57 + 74 * (m' + 1 - 1) + 2) (59 + 74 * (m' + 1 - 1)) (by ring), show m' + 1 + 2 * 862 = m' + 1 + 1724 by ring]
          exact s2
        · rw [idx (57 + 74 * (m' + 1 - 1) + 3) (60 + 74 * (m' + 1 - 1)) (by ring), show m' + 1 + 3 * 862 = m' + 1 + 2586 by ring]
          exact s3
        · rw [idx (57 + 74 * (m' + 1 - 1) + 4) (61 + 74 * (m' + 1 - 1)) (by ring), show m' + 1 + 4 * 862 = m' + 1 + 3448 by ring]
          exact s4
      interval_cases j
      · exact st 0 (by omega)
      · exact st 1 (by omega)
      · exact st 2 (by omega)
      · exact st 3 (by omega)
      · exact st 4 (by omega)
    · have k : σ (.n (9 + 74 * (m' + 1))) = word (2 ^ (4 * (m' + 1))) 0 0 := k
      have m : σ (.n (10 + 74 * (m' + 1))) = σ (.n 7) * σ (.n (9 + 74 * (m' + 1))) := m
      have sc : LoadHolds rd (σ (.n 0)) (m' + 1 + 4310) (σ (.n (10 + 74 * (m' + 1)))) := sc
      rw [m, k, word_two_pow (by omega)] at sc
      exact sc
    · have sl : LoadHolds rd (σ (.n 0)) (m' + 1 + 5172) (σ (.n (82 + 74 * (m' + 1 - 1)))) := sl
      rw [show m' + 1 - 1 = m' by omega, hAn] at sl
      exact sl

/-! ## Completeness -/

/-- A cell index, reduced. -/
def gkFin (x : ℕ) : Fin 13 := ⟨x % 13, Nat.mod_lt _ (by decide)⟩

theorem gkFin_eq {x : ℕ} {c : Fin 13} (h : x % 13 = c.val) : gkFin x = c := Fin.ext h

/-- A round's arithmetic, `70 .. 82`, from its claim, coordinate, words and challenge. -/
def gkArith (c e : E) (C : List E) (r : E) : List E :=
  let c1 := C.getD 0 0
  let c2 := C.getD 1 0
  let c3 := C.getD 2 0
  let c4 := C.getD 3 0
  [c1 + c2, c1 + c2 + c3, c1 + c2 + c3 + c4, e * (c1 + c2 + c3 + c4),
    c + e * (c1 + c2 + c3 + c4), r * c4, c3 + r * c4, r * (c3 + r * c4),
    c2 + r * (c3 + r * c4), r * (c2 + r * (c3 + r * c4)), c1 + r * (c2 + r * (c3 + r * c4)),
    r * (c1 + r * (c2 + r * (c3 + r * c4))),
    c + e * (c1 + c2 + c3 + c4) + r * (c1 + r * (c2 + r * (c3 + r * c4)))]

/-- The honest values of `gkr_rounds` at `n` rounds, by index. -/
def gkVals (as cap : List E) (cur : E) (Cf : ℕ → List E) (ef cl : ℕ → E) (P : ℕ → KeccakState)
    (n k : ℕ) : E :=
  if k < 2 then as.getD k 0
  else if k < 7 then cap.getD (k - 2) 0
  else if k = 7 then cur
  else if k = 8 then cl 0
  else if (k - 9) / 74 < n then
    (if (k - 9) % 74 < 40 then
      (if (k - 9) % 74 % 10 = 0 then (Cf ((k - 9) / 74)).getD ((k - 9) % 74 / 10) 0
      else fsPackVals ((Cf ((k - 9) / 74)).getD ((k - 9) % 74 / 10) 0) dsObserve
        ((k - 9) % 74 % 10 - 1))
    else if (k - 9) % 74 < 53 then cellsOfState (P ((k - 9) / 74)) false (gkFin ((k - 9) % 74 - 40))
    else if (k - 9) % 74 < 60 then
      challengeVals (cellsOfState (P ((k - 9) / 74)) false 0)
        (cellsOfState (P ((k - 9) / 74)) false 1) ((k - 9) % 74 - 53)
    else if (k - 9) % 74 = 60 then ef ((k - 9) / 74)
    else (gkArith (cl ((k - 9) / 74)) (ef ((k - 9) / 74)) (Cf ((k - 9) / 74))
      (challengeOf (P ((k - 9) / 74)))).getD ((k - 9) % 74 - 61) 0)
  else if k = 9 + 74 * n then word (2 ^ (4 * n)) 0 0
  else if k = 10 + 74 * n then cur * word (2 ^ (4 * n)) 0 0
  else 0

/-- Decide the next `if` of an unfolded index function by `omega`. -/
macro "gk_if" : tactic => `(tactic| first
  | (rw [ite_eq_right_of_eq_false]; rotate_left; exact eq_false (by omega))
  | (rw [ite_eq_left_of_eq_true]; rotate_left; exact eq_true (by omega)))

section
variable (as cap : List E) (cur : E) (Cf : ℕ → List E) (ef cl : ℕ → E) (P : ℕ → KeccakState)

theorem gkVals_word {n q t : ℕ} (hq : q < n) (ht : t < 4) :
    gkVals as cap cur Cf ef cl P n (9 + 74 * q + 10 * t) = (Cf q).getD t 0 := by
  rw [gkVals, show (9 + 74 * q + 10 * t - 9) / 74 = q by omega,
    show (9 + 74 * q + 10 * t - 9) % 74 = 10 * t by omega]
  repeat gk_if
  congr 1; omega

theorem gkVals_pack {n q t u : ℕ} (hq : q < n) (ht : t < 4) (hu : u < 9) :
    gkVals as cap cur Cf ef cl P n (9 + 74 * q + 10 * t + 1 + u) =
      fsPackVals ((Cf q).getD t 0) dsObserve u := by
  rw [gkVals, show (9 + 74 * q + 10 * t + 1 + u - 9) / 74 = q by omega,
    show (9 + 74 * q + 10 * t + 1 + u - 9) % 74 = 10 * t + 1 + u by omega]
  repeat gk_if
  rw [show (10 * t + 1 + u) / 10 = t by omega, show (10 * t + 1 + u) % 10 - 1 = u by omega]

theorem gkVals_cells {n q : ℕ} (hq : q < n) (c : Fin 13) :
    gkVals as cap cur Cf ef cl P n (49 + 74 * q + c.val) = cellsOfState (P q) false c := by
  have hc := c.isLt
  rw [gkVals, show (49 + 74 * q + c.val - 9) / 74 = q by omega,
    show (49 + 74 * q + c.val - 9) % 74 = 40 + c.val by omega]
  repeat gk_if
  congr 1; apply gkFin_eq; omega

theorem gkVals_chal {n q u : ℕ} (hq : q < n) (hu : u < 7) :
    gkVals as cap cur Cf ef cl P n (62 + 74 * q + u) =
      challengeVals (cellsOfState (P q) false 0) (cellsOfState (P q) false 1) u := by
  rw [gkVals, show (62 + 74 * q + u - 9) / 74 = q by omega,
    show (62 + 74 * q + u - 9) % 74 = 53 + u by omega]
  repeat gk_if
  rw [show 53 + u - 53 = u by omega]

theorem gkVals_e {n q : ℕ} (hq : q < n) : gkVals as cap cur Cf ef cl P n (69 + 74 * q) = ef q := by
  rw [gkVals, show (69 + 74 * q - 9) / 74 = q by omega, show (69 + 74 * q - 9) % 74 = 60 by omega]
  repeat gk_if

theorem gkVals_arith {n q u : ℕ} (hq : q < n) (hu : u < 13) :
    gkVals as cap cur Cf ef cl P n (70 + 74 * q + u) =
      (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD u 0 := by
  rw [gkVals, show (70 + 74 * q + u - 9) / 74 = q by omega,
    show (70 + 74 * q + u - 9) % 74 = 61 + u by omega]
  repeat gk_if
  rw [show 61 + u - 61 = u by omega]

theorem gkVals_tail0 {n : ℕ} : gkVals as cap cur Cf ef cl P n (9 + 74 * n) = word (2 ^ (4 * n)) 0 0 := by
  rw [gkVals, show (9 + 74 * n - 9) / 74 = n by omega]
  repeat gk_if

theorem gkVals_tail1 {n : ℕ} :
    gkVals as cap cur Cf ef cl P n (10 + 74 * n) = cur * word (2 ^ (4 * n)) 0 0 := by
  rw [gkVals, show (10 + 74 * n - 9) / 74 = n by omega]
  repeat gk_if

theorem gkVals_tail2 {n : ℕ} : gkVals as cap cur Cf ef cl P n (11 + 74 * n) = 0 := by
  rw [gkVals, show (11 + 74 * n - 9) / 74 = n by omega]
  repeat gk_if

end

theorem flatten4_get (Cf : ℕ → List E) (h4 : ∀ q, (Cf q).length = 4) :
    ∀ n q t, q < n → t < 4 → ((List.range n).map Cf).flatten.getD (4 * q + t) 0 = (Cf q).getD t 0
  | 0, _, _, hq, _ => absurd hq (by omega)
  | n + 1, q, t, hq, ht => by
    have hlen : ((List.range n).map Cf).flatten.length = 4 * n := by
      clear hq
      induction n with
      | zero => rfl
      | succ n ih => simp [List.range_succ, h4, ih]; ring
    simp only [List.range_succ, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.getD_eq_getElem?_getD]
    by_cases hqn : q < n
    · rw [List.getElem?_append_left (by rw [hlen]; omega)]
      have := flatten4_get Cf h4 n q t hqn ht
      simpa [List.getD_eq_getElem?_getD] using this
    · rw [List.getElem?_append_right (by rw [hlen]; omega), hlen,
        show 4 * q + t - 4 * n = t by omega, show q = n by omega]

theorem flatten4_length (Cf : ℕ → List E) (h4 : ∀ q, (Cf q).length = 4) :
    ∀ n, ((List.range n).map Cf).flatten.length = 4 * n
  | 0 => rfl
  | n + 1 => by
    simp [List.range_succ, h4, flatten4_length Cf h4 n]; ring

theorem list4_eq {l : List E} (h : l.length = 4) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] := by
  match l, h with
  | [a, b, c, d], _ => rfl

theorem gk_complete {name : String} {f : Fn} (n : ℕ) (hn : 1 ≤ n) (hn2 : n ≤ 6)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = gkParams)
    (hbody : f.body = gkBody n) (rd : Reader) (args rets : List E)
    (h : MeaningGkrRounds n rd args rets) : coreProgram.Rel rd name args rets := by
  obtain ⟨rec, pt, rfl⟩ : ∃ rec pt, args = [rec, pt] := by
    match args, h with
    | [rec, pt], _ => exact ⟨rec, pt, rfl⟩
  obtain ⟨hr0, cap, cur, claim, cs, es, ⟨hcl, hcap⟩, hcan, hcur, hclaim, hlen, h4, hflat, hles,
    hpt, hres⟩ := h
  let Cf : ℕ → List E := fun q ↦ [(cs.getD q []).getD 0 0, (cs.getD q []).getD 1 0,
    (cs.getD q []).getD 2 0, (cs.getD q []).getD 3 0]
  let ef : ℕ → E := fun q ↦ es.getD q 0
  have hcs : cs = (List.range n).map Cf := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Cf, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, Option.getD_some]
    exact list4_eq (h4 _ (List.getElem_mem h1))
  have hes : es = (List.range n).map ef := by
    apply List.ext_getElem (by simp [hles])
    intro i h1 h2
    simp [ef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  have hC4 : ∀ q, (Cf q).length = 4 := fun _ ↦ rfl
  have hm : ∀ q, q < n → ∀ t, t < 4 → LoadHolds rd cur (4 * q + t) ((Cf q).getD t 0) := by
    intro q hq t ht
    rw [hcs] at hflat
    have hk : 4 * q + t < ((List.range n).map Cf).flatten.length := by
      rw [flatten4_length Cf hC4]; omega
    have := hflat _ hk
    rwa [show ((List.range n).map Cf).flatten[4 * q + t] =
        ((List.range n).map Cf).flatten.getD (4 * q + t) 0 by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk],
      flatten4_get Cf hC4 n q t hq ht] at this
  rcases cap with _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, cap⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hcl <;> try omega
  let cap := [a2, a3, a4, a5, a6]
  let St := gkSt Cf ef claim ⟨cap, []⟩
  let P := gkP Cf ef claim ⟨cap, []⟩
  let cl : ℕ → E := fun q ↦ (St q).1
  simp only [hcs, hes, gkrRun_range1, gkrRun_range2] at hres
  obtain ⟨hres1, ⟨-, hres2⟩, hres3, hres4⟩ := hres
  let σ : Val := fun v ↦ gkVals [rec, pt] cap cur Cf ef cl P n v.idx
  have ev : ∀ k, σ (.n k) = gkVals [rec, pt] cap cur Cf ef cl P n k := fun _ ↦ rfl
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have pcan : ∀ x t, IsCanonical128 (fsPackVals x t 6) ∧ IsCanonical128 (fsPackVals x t 8) :=
    fsPackVals_canonical
  have pc : ∀ x t, (fsPackVals x t 6, fsPackVals x t 8) = Keccak.scalarCells x t := fsPackVals_cells
  have zc : IsCanonical128 (0 : E) := by
    rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have kcan : ∀ (L : List E), (∀ x ∈ L, IsCanonical128 x) → ∀ c : Fin 13,
      IsCanonical128 (cells13 L c) := by
    intro L hL c
    simp only [cells13, List.getD_eq_getElem?_getD]
    cases h : L[c.val]? with
    | none => exact zc
    | some x => exact hL x (List.mem_of_getElem? h)
  have e0 : σ (.n 0) = rec := by simp [ev, gkVals]
  have e1 : σ (.n 1) = pt := by simp [ev, gkVals]
  have e7 : σ (.n 7) = cur := by simp [ev, gkVals]
  have vw : ∀ q t, q < n → t < 4 → σ (.n (9 + 74 * q + 10 * t)) = (Cf q).getD t 0 :=
    fun q t hq ht ↦ gkVals_word _ _ _ _ _ _ _ hq ht
  have vp : ∀ q t u, q < n → t < 4 → u < 9 →
      σ (.n (9 + 74 * q + 10 * t + 1 + u)) = fsPackVals ((Cf q).getD t 0) dsObserve u :=
    fun q t u hq ht hu ↦ gkVals_pack _ _ _ _ _ _ _ hq ht hu
  have vc : ∀ q, q < n → ∀ c : Fin 13, σ (.n (49 + 74 * q + c.val)) = cellsOfState (P q) false c :=
    fun q hq c ↦ gkVals_cells _ _ _ _ _ _ _ hq c
  have va : ∀ q u, q < n → u < 13 → σ (.n (70 + 74 * q + u)) =
      (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD u 0 :=
    fun q u hq hu ↦ gkVals_arith _ _ _ _ _ _ _ hq hu
  have hcl : ∀ q, q ≤ n → σ (.n (8 + 74 * q)) = cl q := by
    intro q hq
    cases q with
    | zero => simp [ev, gkVals, cl, St, gkSt]
    | succ q =>
      rw [idx _ (70 + 74 * q + 12) (by ring), va q 12 (by omega) (by omega)]
      show _ = polyEval ((cl q + ef q * sumE (Cf q)) :: Cf q) (challengeOf (P q))
      rw [show Cf q = [(Cf q).getD 0 0, (Cf q).getD 1 0, (Cf q).getD 2 0, (Cf q).getD 3 0] from rfl,
        ← gk_eval]
      rfl
  have capq : ∀ q, q < n → [σ (.n (gkCapPrev q)), σ (.n (gkCapPrev q + 1)), σ (.n (gkCapPrev q + 2)),
      σ (.n (gkCapPrev q + 3)), σ (.n (gkCapPrev q + 4))] = (St q).2.cap := by
    intro q hq
    cases q with
    | zero => simp [ev, gkVals, gkCapPrev, St, gkSt, cap]
    | succ q =>
      have c : ∀ i (hi : i < 5), σ (.n (gkCapPrev (q + 1) + i)) = cellsOfState (P q) false ⟨8 + i, by omega⟩ :=
        fun i hi ↦ (idx _ (49 + 74 * q + (⟨8 + i, by omega⟩ : Fin 13).val)
          (show 57 + 74 * q + i = 49 + 74 * q + (8 + i) by ring)).trans (vc q (by omega) _)
      rw [show σ (.n (gkCapPrev (q + 1))) = _ from c 0 (by omega), c 1 (by omega), c 2 (by omega),
        c 3 (by omega), c 4 (by omega)]
      rfl
  rw [rel_iff_sem hfind, hbody, hparams, gkBody]
  simp only [holdsList_append, holdsList_range_flatten n gkRound (fun _ => rfl), holds_gkRound,
    Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
  refine ⟨σ, by rw [e0, e1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · show LoadHolds rd (σ (.n 0)) 0 (σ (.n 2))
    rw [e0, show σ (.n 2) = a2 by simp [ev, gkVals, cap]]
    exact hcap 0 (by simp)
  · show LoadHolds rd (σ (.n 0)) 862 (σ (.n 3))
    rw [e0, show σ (.n 3) = a3 by simp [ev, gkVals, cap]]
    exact hcap 1 (by simp)
  · show LoadHolds rd (σ (.n 0)) 1724 (σ (.n 4))
    rw [e0, show σ (.n 4) = a4 by simp [ev, gkVals, cap]]
    exact hcap 2 (by simp)
  · show LoadHolds rd (σ (.n 0)) 2586 (σ (.n 5))
    rw [e0, show σ (.n 5) = a5 by simp [ev, gkVals, cap]]
    exact hcap 3 (by simp)
  · show LoadHolds rd (σ (.n 0)) 3448 (σ (.n 6))
    rw [e0, show σ (.n 6) = a6 by simp [ev, gkVals, cap]]
    exact hcap 4 (by simp)
  · show LoadHolds rd (σ (.n 0)) 4310 (σ (.n 7)); rw [e0, e7]; exact hcur
  · show LoadHolds rd (σ (.n 0)) 5172 (σ (.n 8))
    rw [e0, hcl 0 (by omega)]; exact hclaim
  · have w0 : σ (.n (9 + 74 * q)) = (Cf q).getD 0 0 := (idx _ _ (by ring)).trans (vw q 0 hq (by omega))
    have w1 : σ (.n (19 + 74 * q)) = (Cf q).getD 1 0 := (idx _ _ (by ring)).trans (vw q 1 hq (by omega))
    have w2 : σ (.n (29 + 74 * q)) = (Cf q).getD 2 0 := (idx _ _ (by ring)).trans (vw q 2 hq (by omega))
    have w3 : σ (.n (39 + 74 * q)) = (Cf q).getD 3 0 := (idx _ _ (by ring)).trans (vw q 3 hq (by omega))
    have b0 : σ (.n (49 + 74 * q)) = cellsOfState (P q) false 0 := vc q hq 0
    have b1 : σ (.n (50 + 74 * q)) = cellsOfState (P q) false 1 :=
      (idx _ (49 + 74 * q + (1 : Fin 13).val) (by simp; ring)).trans (vc q hq 1)
    have hr : σ (.n (68 + 74 * q)) = challengeOf (P q) := by
      rw [idx _ (62 + 74 * q + 6) (by ring), ev, gkVals_chal _ _ _ _ _ _ _ hq (u := 6) (by omega),
        challengeVals_six]
    have he : σ (.n (69 + 74 * q)) = ef q := gkVals_e _ _ _ _ _ _ _ hq
    have a0 : σ (.n (70 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 0 0 :=
      (idx _ (70 + 74 * q + 0) (by ring)).trans (va q 0 hq (by omega))
    have a1 : σ (.n (71 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 1 0 :=
      (idx _ (70 + 74 * q + 1) (by ring)).trans (va q 1 hq (by omega))
    have a2 : σ (.n (72 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 2 0 :=
      (idx _ (70 + 74 * q + 2) (by ring)).trans (va q 2 hq (by omega))
    have a3 : σ (.n (73 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 3 0 :=
      (idx _ (70 + 74 * q + 3) (by ring)).trans (va q 3 hq (by omega))
    have a4 : σ (.n (74 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 4 0 :=
      (idx _ (70 + 74 * q + 4) (by ring)).trans (va q 4 hq (by omega))
    have a5 : σ (.n (75 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 5 0 :=
      (idx _ (70 + 74 * q + 5) (by ring)).trans (va q 5 hq (by omega))
    have a6 : σ (.n (76 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 6 0 :=
      (idx _ (70 + 74 * q + 6) (by ring)).trans (va q 6 hq (by omega))
    have a7 : σ (.n (77 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 7 0 :=
      (idx _ (70 + 74 * q + 7) (by ring)).trans (va q 7 hq (by omega))
    have a8 : σ (.n (78 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 8 0 :=
      (idx _ (70 + 74 * q + 8) (by ring)).trans (va q 8 hq (by omega))
    have a9 : σ (.n (79 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 9 0 :=
      (idx _ (70 + 74 * q + 9) (by ring)).trans (va q 9 hq (by omega))
    have a10 : σ (.n (80 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 10 0 :=
      (idx _ (70 + 74 * q + 10) (by ring)).trans (va q 10 hq (by omega))
    have a11 : σ (.n (81 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 11 0 :=
      (idx _ (70 + 74 * q + 11) (by ring)).trans (va q 11 hq (by omega))
    have a12 : σ (.n (82 + 74 * q)) = (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD 12 0 :=
      (idx _ (70 + 74 * q + 12) (by ring)).trans (va q 12 hq (by omega))
    simp only [gkArith, List.getD_cons_succ,
      List.getD_cons_zero] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    have hin : ([.n (16 + 74 * q), .n (18 + 74 * q), .n (26 + 74 * q), .n (28 + 74 * q),
        .n (36 + 74 * q), .n (38 + 74 * q), .n (46 + 74 * q), .n (48 + 74 * q),
        .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
        .n (gkCapPrev q + 4)] : List V).map σ =
        [fsPackVals ((Cf q).getD 0 0) dsObserve 6, fsPackVals ((Cf q).getD 0 0) dsObserve 8,
          fsPackVals ((Cf q).getD 1 0) dsObserve 6, fsPackVals ((Cf q).getD 1 0) dsObserve 8,
          fsPackVals ((Cf q).getD 2 0) dsObserve 6, fsPackVals ((Cf q).getD 2 0) dsObserve 8,
          fsPackVals ((Cf q).getD 3 0) dsObserve 6, fsPackVals ((Cf q).getD 3 0) dsObserve 8] ++
          (St q).2.cap := by
      rw [← capq q hq]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [idx (16 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 0 + 1 + 6 by ring), vp q 0 6 hq (by omega) (by omega),
        idx (18 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 0 + 1 + 8 by ring), vp q 0 8 hq (by omega) (by omega),
        idx (26 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 1 + 1 + 6 by ring), vp q 1 6 hq (by omega) (by omega),
        idx (28 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 1 + 1 + 8 by ring), vp q 1 8 hq (by omega) (by omega),
        idx (36 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 2 + 1 + 6 by ring), vp q 2 6 hq (by omega) (by omega),
        idx (38 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 2 + 1 + 8 by ring), vp q 2 8 hq (by omega) (by omega),
        idx (46 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 3 + 1 + 6 by ring), vp q 3 6 hq (by omega) (by omega),
        idx (48 + 74 * q) _ (show _ = 9 + 74 * q + 10 * 3 + 1 + 8 by ring), vp q 3 8 hq (by omega) (by omega)]
    have hcanq : AllCanonical (St q).2.cap := by
      cases q with
      | zero => simpa [St, gkSt, cap] using hcan
      | succ q =>
        intro x hx
        simp only [St, gkSt, Fs.squeeze, capOf, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact cellsOfState_canonical _ _ _
    refine ⟨fun t ht ↦ ⟨?_, fsPackOk_of_vals fun u hu ↦ ?_⟩, keccak13_mk (rd := rd) rfl rfl (kcan _ ?_) fun c ↦ ?_,
      challengeOk_of_vals (by rw [b1]; exact cellsOfState_canonical _ _ _) fun u hu ↦ ?_, ?_⟩
    · rw [e7, vw q t hq ht]; exact hm q hq t ht
    · rw [vp q t u hq ht hu, vw q t hq ht]
    · rw [hin]
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | h
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      · exact (pcan _ _).1
      · exact (pcan _ _).2
      · exact hcanq x h
    · rw [cells13_gkRun13, vc q hq c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      show _ = permOf _
      rw [hin]
      show gkP Cf ef claim ⟨cap, []⟩ q = _
      rw [gkP_eq Cf ef claim cap q rfl]
      simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
        ← pc]
      rfl
    · rw [b0, b1]; exact gkVals_chal _ _ _ _ _ _ _ hq hu
    · have hpe : LoadHolds rd pt q (ef q) := by
        have := hpt q (by rw [hles]; omega)
        rwa [show es[q] = ef q by simp [ef, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show q < es.length by rw [hles]; omega)]] at this
      refine ⟨by rw [e1, he]; exact hpe, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [a0, w0, w1]
      · rw [a1, a0, w2]
      · rw [a2, a1, w3]
      · rw [a3, he, a2]
      · rw [a4, hcl q hq.le, a3]
      · rw [e1, hr]
        have := hres1 q (by simp; omega)
        simp only [List.getElem_map, List.getElem_range] at this
        rwa [loadHolds_mul_gen_pow] at this
      · rw [a5, hr, w3]
      · rw [a6, w2, a5]
      · rw [a7, hr, a6]
      · rw [a8, w1, a7]
      · rw [a9, hr, a8]
      · rw [a10, w0, a9]
      · rw [a11, hr, a10]
      · rw [a12, a4, a11]
  · show LoadHolds rd (σ (.n 0)) (m' + 1) (σ (.n (57 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (8 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 0 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 862) (σ (.n (58 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (9 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 1 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 1724) (σ (.n (59 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (10 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 2 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 2586) (σ (.n (60 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (11 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 3 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 3448) (σ (.n (61 + 74 * (m' + 1 - 1))))
    rw [e0, idx _ (49 + 74 * m' + (12 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    have := hres2 4 (by simp [gkSt, Fs.squeeze, capOf])
    exact this
  · show σ (.n (9 + 74 * (m' + 1))) = word (2 ^ (4 * (m' + 1))) 0 0
    exact gkVals_tail0 _ _ _ _ _ _ _
  · show σ (.n (10 + 74 * (m' + 1))) = σ (.n 7) * σ (.n (9 + 74 * (m' + 1)))
    rw [ev, gkVals_tail1, e7, ev, gkVals_tail0]
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 4310) (σ (.n (10 + 74 * (m' + 1))))
    rw [e0, ev, gkVals_tail1, word_two_pow (by omega)]
    exact hres3
  · show LoadHolds rd (σ (.n 0)) (m' + 1 + 5172) (σ (.n (82 + 74 * (m' + 1 - 1))))
    rw [e0, show m' + 1 - 1 = m' by omega, idx _ (8 + 74 * (m' + 1)) (by ring), hcl (m' + 1) (by omega)]
    exact hres4
  · show σ (.n (11 + 74 * (m' + 1))) = word 0 0 0
    rw [ev, gkVals_tail2, word_zero]
  · show [σ (.n (11 + 74 * (m' + 1)))] = rets
    rw [hr0, ev, gkVals_tail2]


set_option maxRecDepth 100000 in
theorem gkr_rounds_body1 : Fn.body Data.core411 = gkBody 1 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gkr_rounds_body2 : Fn.body Data.core408 = gkBody 2 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gkr_rounds_body4 : Fn.body Data.core409 = gkBody 4 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem gkr_rounds_body6 : Fn.body Data.core410 = gkBody 6 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **`gkr_rounds`' core IR is its meaning**, at one, two, four and six rounds, and at none it
returns `0`. -/
theorem gkr_rounds_holds : gkr_rounds_Spec := by
  have h1 : coreProgram.find? "gkr_rounds__L1" = some Data.core411 :=
    Program.find?_of_indexOf? (j := 411) (by decide +kernel) rfl
  have h2 : coreProgram.find? "gkr_rounds__L2" = some Data.core408 :=
    Program.find?_of_indexOf? (j := 408) (by decide +kernel) rfl
  have h4 : coreProgram.find? "gkr_rounds__L4" = some Data.core409 :=
    Program.find?_of_indexOf? (j := 409) (by decide +kernel) rfl
  have h6 : coreProgram.find? "gkr_rounds__L6" = some Data.core410 :=
    Program.find?_of_indexOf? (j := 410) (by decide +kernel) rfl
  have h0 : coreProgram.find? "gkr_rounds__L0" = some Data.core407 :=
    Program.find?_of_indexOf? (j := 407) (by decide +kernel) rfl
  refine ⟨fun n hn rd args rets ↦ ?_, fun rd args rets ↦ ?_⟩
  · simp only [gkrRoundsCounts, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact ⟨gk_sound 1 (by decide) (by decide) h1 rfl gkr_rounds_body1 rd args rets,
        gk_complete 1 (by decide) (by decide) h1 rfl gkr_rounds_body1 rd args rets⟩
    · exact ⟨gk_sound 2 (by decide) (by decide) h2 rfl gkr_rounds_body2 rd args rets,
        gk_complete 2 (by decide) (by decide) h2 rfl gkr_rounds_body2 rd args rets⟩
    · exact ⟨gk_sound 4 (by decide) (by decide) h4 rfl gkr_rounds_body4 rd args rets,
        gk_complete 4 (by decide) (by decide) h4 rfl gkr_rounds_body4 rd args rets⟩
    · exact ⟨gk_sound 6 (by decide) (by decide) h6 rfl gkr_rounds_body6 rd args rets,
        gk_complete 6 (by decide) (by decide) h6 rfl gkr_rounds_body6 rd args rets⟩
  · rw [rel_iff_sem h0]
    simp only [Data.core407, Data.core407.body, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil]
    constructor
    · rintro ⟨σ, rfl, hc, rfl⟩
      simp only [MeaningGkrRounds0, hc, word_zero]
    · intro h
      match args, h with
      | [a, b], h =>
        refine ⟨fun v ↦ if v = .n 0 then a else if v = .n 1 then b else 0, by simp, ?_, ?_⟩
        · simp [word_zero]
        · simpa [MeaningGkrRounds0] using h.symm

end
end LeanVM.Guest.B1
