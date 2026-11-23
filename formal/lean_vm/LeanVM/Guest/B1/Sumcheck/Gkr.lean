/-
  LeanVM.Guest.B1.Sumcheck.Gkr

  Equality-mode sumcheck rounds between GKR round records (the rounds template).
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Sumcheck.Meaning
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Common.Find

/-!
# GKR rounds between records

The rounds of a radix-four GKR layer's loop iteration at `n` rounds (`gkPre lc n`; its values `0 .. 4` the record, the point, the cursor, the
window table and the stream): the record's capacity and claim loaded into `5 .. 10`; round `q`
(`gkRound q`, from `B = 11 + 39 q`): four stream words read and packed (`B + 3 t`, its cells
`B + 3 t + 1`, `B + 3 t + 2`), the permutation of the four waiting with the previous capacity
into `B + 12` (`fs_grind_squeeze` at zero bits), its challenge the permutation's first cell
`B + 12`, the previous coordinate `pt[q]` (at `B + 25`), the derived `c0`, the challenge stored at
`pt[42 + q]`, the claim at the challenge (at `B + 38`); at an odd `n` a zero stored at `pt[42 + n]` (`gkPad`); the
next record's capacity, cursor and claim stored. The window table and the stream are not read.
`gkPre true n` also loads the cursor from the record (`gkCurLoad`), as the loop iteration does.

`gk_pre_holds`: the honest valuation (`gkVals`) satisfies `gkPre lc n` over any call relation
(`B1/Gkr/GlCLoop.lean` renames it into the loop's iteration).
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
  | 0 => 5
  | q + 1 => 31 + 39 * q

/-- Round `q`. -/
def gkRound (q : ℕ) : List Stmt :=
  fsNextT (.n 2) (4 * q) (11 + 39 * q) ++ fsNextT (.n 2) (4 * q + 1) (14 + 39 * q) ++
  fsNextT (.n 2) (4 * q + 2) (17 + 39 * q) ++ fsNextT (.n 2) (4 * q + 3) (20 + 39 * q) ++
  [keccakA [.n (12 + 39 * q), .n (13 + 39 * q), .n (15 + 39 * q), .n (16 + 39 * q),
      .n (18 + 39 * q), .n (19 + 39 * q), .n (21 + 39 * q), .n (22 + 39 * q),
      .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
      .n (gkCapPrev q + 4)] (gkRun13 (23 + 39 * q))] ++
  [.atom (.load (.n (36 + 39 * q)) (.n 1) q),
    .atom (.add (.n (37 + 39 * q)) (.n (11 + 39 * q)) (.n (14 + 39 * q))),
    .atom (.add (.n (38 + 39 * q)) (.n (37 + 39 * q)) (.n (17 + 39 * q))),
    .atom (.add (.n (39 + 39 * q)) (.n (38 + 39 * q)) (.n (20 + 39 * q))),
    .atom (.mul (.n (40 + 39 * q)) (.n (36 + 39 * q)) (.n (39 + 39 * q))),
    .atom (.add (.n (41 + 39 * q)) (.n (10 + 39 * q)) (.n (40 + 39 * q))),
    .atom (.load (.n (23 + 39 * q)) (.n 1) (42 + q)),
    .atom (.mul (.n (42 + 39 * q)) (.n (23 + 39 * q)) (.n (20 + 39 * q))),
    .atom (.add (.n (43 + 39 * q)) (.n (17 + 39 * q)) (.n (42 + 39 * q))),
    .atom (.mul (.n (44 + 39 * q)) (.n (23 + 39 * q)) (.n (43 + 39 * q))),
    .atom (.add (.n (45 + 39 * q)) (.n (14 + 39 * q)) (.n (44 + 39 * q))),
    .atom (.mul (.n (46 + 39 * q)) (.n (23 + 39 * q)) (.n (45 + 39 * q))),
    .atom (.add (.n (47 + 39 * q)) (.n (11 + 39 * q)) (.n (46 + 39 * q))),
    .atom (.mul (.n (48 + 39 * q)) (.n (23 + 39 * q)) (.n (47 + 39 * q))),
    .atom (.add (.n (49 + 39 * q)) (.n (41 + 39 * q)) (.n (48 + 39 * q)))]

/-- The cursor's load from the record, in the layer loop's iteration only. -/
def gkCurLoad : Bool → List Stmt
  | true => [.atom (.load (.n 2) (.n 0) 4310)]
  | false => []

/-- The record's capacity and claim (and, `lc`, its cursor). -/
def gkHead (lc : Bool) : List Stmt :=
  [.atom (.load (.n 5) (.n 0) 0), .atom (.load (.n 6) (.n 0) 862), .atom (.load (.n 7) (.n 0) 1724),
    .atom (.load (.n 8) (.n 0) 2586), .atom (.load (.n 9) (.n 0) 3448)] ++ gkCurLoad lc ++
  [.atom (.load (.n 10) (.n 0) 5172)]

/-- The zero after an odd count's challenges. -/
def gkPad (n : ℕ) : List Stmt :=
  if n % 2 = 1 then
    [.atom (.const (.n (11 + 39 * n)) (word 0 0)), .atom (.load (.n (11 + 39 * n)) (.n 1) (42 + n))]
  else []

/-- The rounds and the next record, up to the returned `0`. -/
def gkPre (lc : Bool) (n : ℕ) : List Stmt :=
  gkHead lc ++ ((List.range n).map gkRound).flatten ++ gkPad n ++
  [.atom (.load (.n (31 + 39 * (n - 1))) (.n 0) 1),
    .atom (.load (.n (32 + 39 * (n - 1))) (.n 0) 863),
    .atom (.load (.n (33 + 39 * (n - 1))) (.n 0) 1725),
    .atom (.load (.n (34 + 39 * (n - 1))) (.n 0) 2587),
    .atom (.load (.n (35 + 39 * (n - 1))) (.n 0) 3449),
    .atom (.const (.n (11 + 39 * n + n % 2)) (word (2 ^ (4 * n)) 0)),
    .atom (.mul (.n (12 + 39 * n + n % 2)) (.n 2) (.n (11 + 39 * n + n % 2))),
    .atom (.load (.n (12 + 39 * n + n % 2)) (.n 0) 4311),
    .atom (.load (.n (49 + 39 * (n - 1))) (.n 0) 5173)]

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

/-! ## What each part asks -/

/-- What the arithmetic of round `q` asks. -/
def GkFoldOk (rd : Reader) (σ : Val) (q : ℕ) : Prop :=
  LoadHolds rd (σ (.n 1)) q (σ (.n (36 + 39 * q))) ∧
    σ (.n (37 + 39 * q)) = σ (.n (11 + 39 * q)) + σ (.n (14 + 39 * q)) ∧
    σ (.n (38 + 39 * q)) = σ (.n (37 + 39 * q)) + σ (.n (17 + 39 * q)) ∧
    σ (.n (39 + 39 * q)) = σ (.n (38 + 39 * q)) + σ (.n (20 + 39 * q)) ∧
    σ (.n (40 + 39 * q)) = σ (.n (36 + 39 * q)) * σ (.n (39 + 39 * q)) ∧
    σ (.n (41 + 39 * q)) = σ (.n (10 + 39 * q)) + σ (.n (40 + 39 * q)) ∧
    LoadHolds rd (σ (.n 1)) (42 + q) (σ (.n (23 + 39 * q))) ∧
    σ (.n (42 + 39 * q)) = σ (.n (23 + 39 * q)) * σ (.n (20 + 39 * q)) ∧
    σ (.n (43 + 39 * q)) = σ (.n (17 + 39 * q)) + σ (.n (42 + 39 * q)) ∧
    σ (.n (44 + 39 * q)) = σ (.n (23 + 39 * q)) * σ (.n (43 + 39 * q)) ∧
    σ (.n (45 + 39 * q)) = σ (.n (14 + 39 * q)) + σ (.n (44 + 39 * q)) ∧
    σ (.n (46 + 39 * q)) = σ (.n (23 + 39 * q)) * σ (.n (45 + 39 * q)) ∧
    σ (.n (47 + 39 * q)) = σ (.n (11 + 39 * q)) + σ (.n (46 + 39 * q)) ∧
    σ (.n (48 + 39 * q)) = σ (.n (23 + 39 * q)) * σ (.n (47 + 39 * q)) ∧
    σ (.n (49 + 39 * q)) = σ (.n (41 + 39 * q)) + σ (.n (48 + 39 * q))

/-- What round `q` asks. -/
theorem holds_gkRound (q : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gkRound q) True kret ↔
      (∀ t < 4, LoadHolds rd (σ (.n 2)) (4 * q + t) (σ (.n (11 + 39 * q + 3 * t))) ∧
        FsPackOk σ (.n (11 + 39 * q + 3 * t)) (11 + 39 * q + 3 * t + 1) dsObserve) ∧
      (Atom.keccak [.n (12 + 39 * q), .n (13 + 39 * q), .n (15 + 39 * q), .n (16 + 39 * q),
        .n (18 + 39 * q), .n (19 + 39 * q), .n (21 + 39 * q), .n (22 + 39 * q),
        .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
        .n (gkCapPrev q + 4)] (gkRun13 (23 + 39 * q)) false false).Holds rd σ ∧
      GkFoldOk rd σ q := by
  simp only [gkRound, keccakA, holdsList_append, holds_fsNextT, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, GkFoldOk, and_true]
  constructor
  · rintro ⟨h0, h1, h2, h3, hk, hf⟩
    refine ⟨fun t ht ↦ ?_, hk, hf⟩
    interval_cases t
    · simpa using h0
    · simpa [show 11 + 39 * q + 3 * 1 = 14 + 39 * q by ring] using h1
    · simpa [show 11 + 39 * q + 3 * 2 = 17 + 39 * q by ring] using h2
    · simpa [show 11 + 39 * q + 3 * 3 = 20 + 39 * q by ring] using h3
  · rintro ⟨h, hk, hf⟩
    refine ⟨by simpa using h 0 (by omega), ?_, ?_, ?_, hk, hf⟩
    · simpa [show 11 + 39 * q + 3 * 1 = 14 + 39 * q by ring] using h 1 (by omega)
    · simpa [show 11 + 39 * q + 3 * 2 = 17 + 39 * q by ring] using h 2 (by omega)
    · simpa [show 11 + 39 * q + 3 * 3 = 20 + 39 * q by ring] using h 3 (by omega)

/-- What the cursor's load asks. -/
theorem holds_gkCurLoad (lc : Bool) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gkCurLoad lc) next kret ↔
      (lc = true → LoadHolds rd (σ (.n 0)) 4310 (σ (.n 2))) ∧ next := by
  cases lc <;> simp [gkCurLoad, Stmt.HoldsList, Stmt.Holds, Atom.Holds]

/-- What the pad asks. -/
def GkPadOk (rd : Reader) (σ : Val) (n : ℕ) : Prop :=
  n % 2 = 1 → σ (.n (11 + 39 * n)) = word 0 0 ∧
    LoadHolds rd (σ (.n 1)) (42 + n) (σ (.n (11 + 39 * n)))

theorem holds_gkPad (n : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gkPad n) next kret ↔ GkPadOk rd σ n ∧ next := by
  unfold gkPad GkPadOk
  split_ifs with h
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, h, forall_const, and_assoc]
  · simp [Stmt.HoldsList, h]

theorem cells13_gkRun13 (σ : Val) (b : ℕ) (c : Fin 13) :
    cells13 ((gkRun13 b).map σ) c = σ (.n (b + c.val)) := by
  simp [cells13, gkRun13, List.getD_eq_getElem?_getD]

/-- The rate cells of a round's four words. -/
theorem gk_pend (a b c d : E) :
    pendCells [(a, dsObserve), (b, dsObserve), (c, dsObserve), (d, dsObserve)] =
      [a, word 0 dsObserve, b, word 0 dsObserve, c, word 0 dsObserve, d, word 0 dsObserve] := rfl

/-! ## Completeness -/

/-- A cell index, reduced. -/
def gkFin (x : ℕ) : Fin 13 := ⟨x % 13, Nat.mod_lt _ (by decide)⟩

theorem gkFin_eq {x : ℕ} {c : Fin 13} (h : x % 13 = c.val) : gkFin x = c := Fin.ext h

/-- A round's arithmetic, `B + 26 .. B + 38`, from its claim, coordinate, words and challenge. -/
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

/-- A round's word values by offset `i < 12`: word `i / 3`, its copy, its tag cell. -/
def gkWordVal (C : List E) (i : ℕ) : E :=
  if i % 3 = 2 then word 0 dsObserve else C.getD (i / 3) 0

/-- The honest values of `gkPre lc n`, by index (the pad's zero is the default). -/
def gkVals (as cap : List E) (cur : E) (Cf : ℕ → List E) (ef cl : ℕ → E) (P : ℕ → KeccakState)
    (n k : ℕ) : E :=
  if k < 5 then as.getD k 0
  else if k < 10 then cap.getD (k - 5) 0
  else if k = 10 then cl 0
  else if (k - 11) / 39 < n then
    (if (k - 11) % 39 < 12 then gkWordVal (Cf ((k - 11) / 39)) ((k - 11) % 39)
    else if (k - 11) % 39 < 25 then cellsOfState (P ((k - 11) / 39)) false (gkFin ((k - 11) % 39 - 12))
    else if (k - 11) % 39 = 25 then ef ((k - 11) / 39)
    else (gkArith (cl ((k - 11) / 39)) (ef ((k - 11) / 39)) (Cf ((k - 11) / 39))
      (challengeOf (P ((k - 11) / 39)))).getD ((k - 11) % 39 - 26) 0)
  else if k = 11 + 39 * n + n % 2 then word (2 ^ (4 * n)) 0
  else if k = 12 + 39 * n + n % 2 then cur * word (2 ^ (4 * n)) 0
  else 0

/-- Decide the next `if` of an unfolded index function by `omega`. -/
macro "gk_if" : tactic => `(tactic| first
  | (rw [ite_eq_right_of_eq_false]; rotate_left; exact eq_false (by omega))
  | (rw [ite_eq_left_of_eq_true]; rotate_left; exact eq_true (by omega)))

section
variable (as cap : List E) (cur : E) (Cf : ℕ → List E) (ef cl : ℕ → E) (P : ℕ → KeccakState)

theorem gkVals_word {n q t r : ℕ} (hq : q < n) (ht : t < 4) (hr : r < 3) :
    gkVals as cap cur Cf ef cl P n (11 + 39 * q + 3 * t + r) =
      if r = 2 then word 0 dsObserve else (Cf q).getD t 0 := by
  rw [gkVals, show (11 + 39 * q + 3 * t + r - 11) / 39 = q by omega,
    show (11 + 39 * q + 3 * t + r - 11) % 39 = 3 * t + r by omega]
  repeat gk_if
  rw [gkWordVal, show (3 * t + r) % 3 = r by omega, show (3 * t + r) / 3 = t by omega]

theorem gkVals_cells {n q : ℕ} (hq : q < n) (c : Fin 13) :
    gkVals as cap cur Cf ef cl P n (23 + 39 * q + c.val) = cellsOfState (P q) false c := by
  have hc := c.isLt
  rw [gkVals, show (23 + 39 * q + c.val - 11) / 39 = q by omega,
    show (23 + 39 * q + c.val - 11) % 39 = 12 + c.val by omega]
  repeat gk_if
  congr 1; apply gkFin_eq; omega

theorem gkVals_chal {n q : ℕ} (hq : q < n) :
    gkVals as cap cur Cf ef cl P n (23 + 39 * q) = challengeOf (P q) := by
  have h := gkVals_cells as cap cur Cf ef cl P hq (0 : Fin 13)
  rw [show (0 : Fin 13).val = 0 from rfl, Nat.add_zero] at h
  rw [h, Keccak.challengeOf_cells]

theorem gkVals_e {n q : ℕ} (hq : q < n) : gkVals as cap cur Cf ef cl P n (36 + 39 * q) = ef q := by
  rw [gkVals, show (36 + 39 * q - 11) / 39 = q by omega, show (36 + 39 * q - 11) % 39 = 25 by omega]
  repeat gk_if

theorem gkVals_arith {n q u : ℕ} (hq : q < n) (hu : u < 13) :
    gkVals as cap cur Cf ef cl P n (37 + 39 * q + u) =
      (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD u 0 := by
  rw [gkVals, show (37 + 39 * q + u - 11) / 39 = q by omega,
    show (37 + 39 * q + u - 11) % 39 = 26 + u by omega]
  repeat gk_if
  rw [show 26 + u - 26 = u by omega]

theorem gkVals_pad {n : ℕ} (h : n % 2 = 1) : gkVals as cap cur Cf ef cl P n (11 + 39 * n) = 0 := by
  rw [gkVals, show (11 + 39 * n - 11) / 39 = n by omega]
  repeat gk_if

theorem gkVals_tail0 {n : ℕ} :
    gkVals as cap cur Cf ef cl P n (11 + 39 * n + n % 2) = word (2 ^ (4 * n)) 0 := by
  rw [gkVals, show (11 + 39 * n + n % 2 - 11) / 39 = n by omega]
  repeat gk_if

theorem gkVals_tail1 {n : ℕ} :
    gkVals as cap cur Cf ef cl P n (12 + 39 * n + n % 2) = cur * word (2 ^ (4 * n)) 0 := by
  rw [gkVals, show (12 + 39 * n + n % 2 - 11) / 39 = n by omega]
  repeat gk_if

theorem gkVals_tail2 {n : ℕ} : gkVals as cap cur Cf ef cl P n (13 + 39 * n + n % 2) = 0 := by
  rw [gkVals, show (13 + 39 * n + n % 2 - 11) / 39 = n by omega]
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

/-- **The rounds, completely**: from `GkrRoundsOut n` (and, `lc`, the cursor in the record), the
honest valuation (`gkVals`) satisfies `gkPre lc n` before anything, over any call relation (the
rounds have no call), and is `0` at the returned value. -/
theorem gk_pre_holds (lc : Bool) (n : ℕ) (hn : 1 ≤ n) (hn2 : n < 16) (C : CallRel) (rd : Reader)
    (rec pt cur tabs stream : E) (h : GkrRoundsOut n rd rec pt cur)
    (hlc : lc = true → LoadHolds rd rec 4310 cur) :
    ∃ σ : Val, (∀ v, σ v = σ (.n v.idx)) ∧ σ (.n 0) = rec ∧ σ (.n 1) = pt ∧ σ (.n 2) = cur ∧
      σ (.n 3) = tabs ∧ σ (.n 4) = stream ∧ σ (.n (13 + 39 * n + n % 2)) = 0 ∧
      ∀ (next : Prop) (kret : List E → Prop), next →
        Stmt.HoldsList C rd σ (gkPre lc n) next kret := by
  obtain ⟨cap, claim, cs, es, ⟨hcl, hcap⟩, hclaim, hlen, h4, hflat, hles,
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
  rcases cap with _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, cap⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hcl <;> try omega
  let cap := [a5, a6, a7, a8, a9]
  let St := gkSt Cf ef claim ⟨cap, []⟩
  let P := gkP Cf ef claim ⟨cap, []⟩
  let cl : ℕ → E := fun q ↦ (St q).1
  simp only [hcs, hes, gkrRun_range1, gkrRun_range2] at hres
  obtain ⟨hres1, hpad, ⟨-, hres2⟩, hres3, hres4⟩ := hres
  let σ : Val := fun v ↦ gkVals [rec, pt, cur, tabs, stream] cap cur Cf ef cl P n v.idx
  have ev : ∀ k, σ (.n k) = gkVals [rec, pt, cur, tabs, stream] cap cur Cf ef cl P n k :=
    fun _ ↦ rfl
  have idx : ∀ a b, a = b → σ (.n a) = σ (.n b) := fun a b h ↦ by rw [h]
  have e0 : σ (.n 0) = rec := by simp [ev, gkVals]
  have e1 : σ (.n 1) = pt := by simp [ev, gkVals]
  have e2 : σ (.n 2) = cur := by simp [ev, gkVals]
  have e3 : σ (.n 3) = tabs := by simp [ev, gkVals]
  have e4 : σ (.n 4) = stream := by simp [ev, gkVals]
  have vw : ∀ q t r, q < n → t < 4 → r < 3 → σ (.n (11 + 39 * q + 3 * t + r)) =
      if r = 2 then word 0 dsObserve else (Cf q).getD t 0 :=
    fun q t r hq ht hr ↦ gkVals_word _ _ _ _ _ _ _ hq ht hr
  have vc : ∀ q, q < n → ∀ c : Fin 13, σ (.n (23 + 39 * q + c.val)) = cellsOfState (P q) false c :=
    fun q hq c ↦ gkVals_cells _ _ _ _ _ _ _ hq c
  have va : ∀ q u, q < n → u < 13 → σ (.n (37 + 39 * q + u)) =
      (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD u 0 :=
    fun q u hq hu ↦ gkVals_arith _ _ _ _ _ _ _ hq hu
  have hcl : ∀ q, q ≤ n → σ (.n (10 + 39 * q)) = cl q := by
    intro q hq
    cases q with
    | zero => simp [ev, gkVals, cl, St, gkSt]
    | succ q =>
      rw [idx _ (37 + 39 * q + 12) (by ring), va q 12 (by omega) (by omega)]
      show _ = polyEval ((cl q + ef q * sumE (Cf q)) :: Cf q) (challengeOf (P q))
      rw [show Cf q = [(Cf q).getD 0 0, (Cf q).getD 1 0, (Cf q).getD 2 0, (Cf q).getD 3 0] from rfl,
        ← gk_eval]
      rfl
  have capq : ∀ q, q < n → [σ (.n (gkCapPrev q)), σ (.n (gkCapPrev q + 1)),
      σ (.n (gkCapPrev q + 2)), σ (.n (gkCapPrev q + 3)), σ (.n (gkCapPrev q + 4))] =
        (St q).2.cap := by
    intro q hq
    cases q with
    | zero => simp [ev, gkVals, gkCapPrev, St, gkSt, cap]
    | succ q =>
      have c : ∀ i (hi : i < 5), σ (.n (gkCapPrev (q + 1) + i)) =
          cellsOfState (P q) false ⟨8 + i, by omega⟩ :=
        fun i hi ↦ (idx _ (23 + 39 * q + (⟨8 + i, by omega⟩ : Fin 13).val)
          (show 31 + 39 * q + i = 23 + 39 * q + (8 + i) by ring)).trans (vc q (by omega) _)
      rw [show σ (.n (gkCapPrev (q + 1))) = _ from c 0 (by omega), c 1 (by omega), c 2 (by omega),
        c 3 (by omega), c 4 (by omega)]
      rfl
  refine ⟨σ, fun v => rfl, e0, e1, e2, e3, e4, gkVals_tail2 _ _ _ _ _ _ _, fun next kret hnx ↦ ?_⟩
  rw [gkPre, gkHead]
  simp only [holdsList_append, holdsList_range_flatten n gkRound (fun _ => rfl), holds_gkRound,
    holds_gkCurLoad, holds_gkPad, Stmt.HoldsList, Stmt.Holds]
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, fun hl ↦ ?_, ?_, fun q hq ↦ ?_, fun hodd ↦ ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hnx⟩
  · show LoadHolds rd (σ (.n 0)) 0 (σ (.n 5))
    rw [e0, show σ (.n 5) = a5 by simp [ev, gkVals, cap]]
    exact hcap 0 (by simp)
  · show LoadHolds rd (σ (.n 0)) 862 (σ (.n 6))
    rw [e0, show σ (.n 6) = a6 by simp [ev, gkVals, cap]]
    exact hcap 1 (by simp)
  · show LoadHolds rd (σ (.n 0)) 1724 (σ (.n 7))
    rw [e0, show σ (.n 7) = a7 by simp [ev, gkVals, cap]]
    exact hcap 2 (by simp)
  · show LoadHolds rd (σ (.n 0)) 2586 (σ (.n 8))
    rw [e0, show σ (.n 8) = a8 by simp [ev, gkVals, cap]]
    exact hcap 3 (by simp)
  · show LoadHolds rd (σ (.n 0)) 3448 (σ (.n 9))
    rw [e0, show σ (.n 9) = a9 by simp [ev, gkVals, cap]]
    exact hcap 4 (by simp)
  · rw [e0, e2]; exact hlc hl
  · show LoadHolds rd (σ (.n 0)) 5172 (σ (.n 10))
    rw [e0, idx 10 (10 + 39 * 0) (by ring), hcl 0 (by omega)]; exact hclaim
  · have w : ∀ t, t < 4 → σ (.n (11 + 39 * q + 3 * t)) = (Cf q).getD t 0 := fun t ht ↦ by
      rw [idx _ (11 + 39 * q + 3 * t + 0) (by ring), vw q t 0 hq ht (by omega)]; rfl
    have w0 : σ (.n (11 + 39 * q)) = (Cf q).getD 0 0 := (idx _ _ (by ring)).trans (w 0 (by omega))
    have w1 : σ (.n (14 + 39 * q)) = (Cf q).getD 1 0 := (idx _ _ (by ring)).trans (w 1 (by omega))
    have w2 : σ (.n (17 + 39 * q)) = (Cf q).getD 2 0 := (idx _ _ (by ring)).trans (w 2 (by omega))
    have w3 : σ (.n (20 + 39 * q)) = (Cf q).getD 3 0 := (idx _ _ (by ring)).trans (w 3 (by omega))
    have wc : ∀ t, t < 4 → σ (.n (11 + 39 * q + 3 * t + 1)) = (Cf q).getD t 0 := fun t ht ↦ by
      rw [vw q t 1 hq ht (by omega)]; rfl
    have wt : ∀ t, t < 4 → σ (.n (11 + 39 * q + 3 * t + 1 + 1)) = word 0 dsObserve := fun t ht ↦ by
      rw [idx _ (11 + 39 * q + 3 * t + 2) (by ring), vw q t 2 hq ht (by omega)]; rfl
    have hr : σ (.n (23 + 39 * q)) = challengeOf (P q) := gkVals_chal _ _ _ _ _ _ _ hq
    have he : σ (.n (36 + 39 * q)) = ef q := gkVals_e _ _ _ _ _ _ _ hq
    have a : ∀ u, u < 13 → σ (.n (37 + 39 * q + u)) =
        (gkArith (cl q) (ef q) (Cf q) (challengeOf (P q))).getD u 0 := fun u hu ↦ va q u hq hu
    have a0 := (idx (37 + 39 * q) (37 + 39 * q + 0) (by ring)).trans (a 0 (by omega))
    have a1 := (idx (38 + 39 * q) (37 + 39 * q + 1) (by ring)).trans (a 1 (by omega))
    have a2 := (idx (39 + 39 * q) (37 + 39 * q + 2) (by ring)).trans (a 2 (by omega))
    have a3 := (idx (40 + 39 * q) (37 + 39 * q + 3) (by ring)).trans (a 3 (by omega))
    have a4 := (idx (41 + 39 * q) (37 + 39 * q + 4) (by ring)).trans (a 4 (by omega))
    have a5 := (idx (42 + 39 * q) (37 + 39 * q + 5) (by ring)).trans (a 5 (by omega))
    have a6 := (idx (43 + 39 * q) (37 + 39 * q + 6) (by ring)).trans (a 6 (by omega))
    have a7 := (idx (44 + 39 * q) (37 + 39 * q + 7) (by ring)).trans (a 7 (by omega))
    have a8 := (idx (45 + 39 * q) (37 + 39 * q + 8) (by ring)).trans (a 8 (by omega))
    have a9 := (idx (46 + 39 * q) (37 + 39 * q + 9) (by ring)).trans (a 9 (by omega))
    have a10 := (idx (47 + 39 * q) (37 + 39 * q + 10) (by ring)).trans (a 10 (by omega))
    have a11 := (idx (48 + 39 * q) (37 + 39 * q + 11) (by ring)).trans (a 11 (by omega))
    have a12 := (idx (49 + 39 * q) (37 + 39 * q + 12) (by ring)).trans (a 12 (by omega))
    simp only [gkArith, List.getD_cons_succ,
      List.getD_cons_zero] at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    have hin : ([.n (12 + 39 * q), .n (13 + 39 * q), .n (15 + 39 * q), .n (16 + 39 * q),
        .n (18 + 39 * q), .n (19 + 39 * q), .n (21 + 39 * q), .n (22 + 39 * q),
        .n (gkCapPrev q), .n (gkCapPrev q + 1), .n (gkCapPrev q + 2), .n (gkCapPrev q + 3),
        .n (gkCapPrev q + 4)] : List V).map σ =
        [(Cf q).getD 0 0, word 0 dsObserve, (Cf q).getD 1 0, word 0 dsObserve,
          (Cf q).getD 2 0, word 0 dsObserve, (Cf q).getD 3 0, word 0 dsObserve] ++
          (St q).2.cap := by
      rw [← capq q hq]
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rw [idx (12 + 39 * q) _ (show _ = 11 + 39 * q + 3 * 0 + 1 by ring), wc 0 (by omega),
        idx (13 + 39 * q) _ (show _ = 11 + 39 * q + 3 * 0 + 1 + 1 by ring), wt 0 (by omega),
        idx (15 + 39 * q) _ (show _ = 11 + 39 * q + 3 * 1 + 1 by ring), wc 1 (by omega),
        idx (16 + 39 * q) _ (show _ = 11 + 39 * q + 3 * 1 + 1 + 1 by ring), wt 1 (by omega),
        idx (18 + 39 * q) _ (show _ = 11 + 39 * q + 3 * 2 + 1 by ring), wc 2 (by omega),
        idx (19 + 39 * q) _ (show _ = 11 + 39 * q + 3 * 2 + 1 + 1 by ring), wt 2 (by omega),
        idx (21 + 39 * q) _ (show _ = 11 + 39 * q + 3 * 3 + 1 by ring), wc 3 (by omega),
        idx (22 + 39 * q) _ (show _ = 11 + 39 * q + 3 * 3 + 1 + 1 by ring), wt 3 (by omega)]
    refine ⟨fun t ht ↦ ⟨?_, ⟨by rw [wc t ht, w t ht], wt t ht⟩⟩, keccakA_of (rd := rd) rfl rfl ?_, ?_⟩
    · rw [e2, w t ht]; exact hm q hq t ht
    · funext c
      rw [cells13_gkRun13, vc q hq c]
      refine congrArg (fun S ↦ cellsOfState S false c) ?_
      show _ = permOf _
      rw [hin]
      show gkP Cf ef claim ⟨cap, []⟩ q = _
      rw [gkP_eq Cf ef claim cap q rfl, gk_pend]
      rfl
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
  · have hz : σ (.n (11 + 39 * (m' + 1))) = 0 := gkVals_pad _ _ _ _ _ _ _ hodd
    refine ⟨by rw [hz, word_zero], ?_⟩
    rw [e1, hz]
    exact hpad hodd
  · show LoadHolds rd (σ (.n 0)) 1 (σ (.n (31 + 39 * (m' + 1 - 1))))
    rw [e0, idx _ (23 + 39 * m' + (8 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 0 (by simp [gkSt, Fs.squeeze, capOf])
  · show LoadHolds rd (σ (.n 0)) 863 (σ (.n (32 + 39 * (m' + 1 - 1))))
    rw [e0, idx _ (23 + 39 * m' + (9 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 1 (by simp [gkSt, Fs.squeeze, capOf])
  · show LoadHolds rd (σ (.n 0)) 1725 (σ (.n (33 + 39 * (m' + 1 - 1))))
    rw [e0, idx _ (23 + 39 * m' + (10 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 2 (by simp [gkSt, Fs.squeeze, capOf])
  · show LoadHolds rd (σ (.n 0)) 2587 (σ (.n (34 + 39 * (m' + 1 - 1))))
    rw [e0, idx _ (23 + 39 * m' + (11 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 3 (by simp [gkSt, Fs.squeeze, capOf])
  · show LoadHolds rd (σ (.n 0)) 3449 (σ (.n (35 + 39 * (m' + 1 - 1))))
    rw [e0, idx _ (23 + 39 * m' + (12 : Fin 13).val) (by simp; omega), vc m' (by omega)]
    exact hres2 4 (by simp [gkSt, Fs.squeeze, capOf])
  · show σ (.n (11 + 39 * (m' + 1) + (m' + 1) % 2)) = word (2 ^ (4 * (m' + 1))) 0
    exact gkVals_tail0 _ _ _ _ _ _ _
  · show σ (.n (12 + 39 * (m' + 1) + (m' + 1) % 2)) =
      σ (.n 2) * σ (.n (11 + 39 * (m' + 1) + (m' + 1) % 2))
    rw [ev, gkVals_tail1, e2, ev, gkVals_tail0]
  · show LoadHolds rd (σ (.n 0)) 4311 (σ (.n (12 + 39 * (m' + 1) + (m' + 1) % 2)))
    rw [e0, ev, gkVals_tail1, word_two_pow (by omega)]
    exact hres3
  · show LoadHolds rd (σ (.n 0)) 5173 (σ (.n (49 + 39 * (m' + 1 - 1))))
    rw [e0, show m' + 1 - 1 = m' by omega, idx _ (10 + 39 * (m' + 1)) (by ring),
      hcl (m' + 1) (by omega)]
    exact hres4

end
end LeanVM.Guest.B1
