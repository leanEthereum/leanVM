/-
  LeanVM.Guest.B1.Tables.Placement

  B1 for `certify_placement`: the committed columns' log sizes, their hinted order certified to
  be `stackOffsets`'s, and the offsets laid out along it.
-/

module

public import LeanVM.Guest.B1.Tables.Common

/-!
# `certify_placement` (TRIAGE #41)

`certify_placement(kappa_base, g_squares)` (G:1966-1999) builds each committed column's `g^κ`
from its source in `kappa_base` (`COL_KAPPA_SRC`, `COL_KAPPA_ADJ`, `cpSrc`, `cpAdj`), reads the
hinted order `col_sort_order`, range-checks each entry into the 92 columns and its size below
34, checks that the sizes do not increase and that ties ascend, stores the running offset
`g^(Σ 2^κ)` of each column write-once, and returns the total. Write-once makes the order
injective, so a bijection (`Value.writeOnce_bijective`); the adjacent checks make it
`stackOffsets`'s `mergeSort` (`Value.eq_mergeSort_of_adjacent`), and the stored offsets are
`stackOffsets`'s (V:877-884).

The expansion is `cpBody`: the 92 columns' sizes (`cpInit`), the order hint, rank `0`, ranks
`1 .. 91` (`cpRank`, from value `90 + 26·r`) and the returns.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The columns' sources -/

/-- `COL_KAPPA_SRC[c]`: the `kappa_base` entry of committed column `c` (`0` the constant, `1`
the memory, `2 + t` table `t`). -/
def cpSrc (c : ℕ) : ℕ :=
  if c < 4 then 1 else if c = 4 then 0 else if c = 5 then 7 else if c < 21 then 2
  else if c < 36 then 3 else if c < 44 then 4 else if c < 59 then 5 else if c < 73 then 6 else 7

/-- `COL_KAPPA_ADJ[c]`: the bytecode's log size `18`, and `q_flock`'s slot bits `8`. -/
def cpAdj (c : ℕ) : ℕ := if c = 4 then 18 else if c = 5 then 8 else 0

/-! ## The template -/

/-- Column `c`'s size, `col_kappa_g[g^c] = kappa_base[g^src] · g^adj`. -/
def cpInit (c : ℕ) : List Stmt :=
  if c < 4 then [.atom (.load (.n (3 + c)) (.n 0) 1), .atom (.load (.n (3 + c)) (.n 2) c)]
  else if c = 4 then
    [.atom (.load (.n 7) (.n 0) 0), .atom (.const (.n 8) (word (2 ^ 18) 0 0)),
      .atom (.mul (.n 9) (.n 7) (.n 8)), .atom (.load (.n 9) (.n 2) 4)]
  else if c = 5 then
    [.atom (.load (.n 10) (.n 0) 7), .atom (.const (.n 11) (word (2 ^ 8) 0 0)),
      .atom (.mul (.n 12) (.n 10) (.n 11)), .atom (.load (.n 12) (.n 2) 5)]
  else [.atom (.load (.n (c + 7)) (.n 0) (cpSrc c)), .atom (.load (.n (c + 7)) (.n 2) c)]

/-- `g^91`, the range check against the 92 columns. -/
abbrev w91 : E := word 3623878656 0 0

/-- `g^33`, the range check against `SIZE_BITS = 34`. -/
abbrev w33 : E := word 8589934592 0 0

/-- Rank `0`, values `101 .. 115`. -/
def cpRank0 : List Stmt :=
  [.atom (.load (.n 101) (.n 99) 0), .atom (.const (.n 102) w91),
    .atom (.rangeCheck (.n 101) (.n 103) (.n 104) (.n 105) (.n 102)),
    .atom (.mul (.n 106) (.n 2) (.n 101)), .atom (.load (.n 107) (.n 106) 0),
    .atom (.const (.n 108) (word 1 0 0)), .atom (.mul (.n 109) (.n 100) (.n 101)),
    .atom (.load (.n 108) (.n 109) 0), .atom (.const (.n 110) w33),
    .atom (.rangeCheck (.n 107) (.n 111) (.n 112) (.n 113) (.n 110)),
    .atom (.mul (.n 114) (.n 1) (.n 107)), .atom (.load (.n 115) (.n 114) 0)]

/-- The previous rank's column, by its value number. -/
def cpPc (r : ℕ) : ℕ := if r = 1 then 101 else 64 + 26 * r

/-- The previous rank's size, by its value number. -/
def cpPk (r : ℕ) : ℕ := if r = 1 then 107 else 70 + 26 * r

/-- Rank `r ≥ 1`, from value `B = 90 + 26·r`; the running offset is `B - 1`. -/
def cpRank (r : ℕ) : List Stmt :=
  let B := 90 + 26 * r
  [.atom (.load (.n B) (.n 99) r), .atom (.const (.n (B + 1)) w91),
    .atom (.rangeCheck (.n B) (.n (B + 2)) (.n (B + 3)) (.n (B + 4)) (.n (B + 1))),
    .atom (.mul (.n (B + 5)) (.n 2) (.n B)), .atom (.load (.n (B + 6)) (.n (B + 5)) 0),
    .atom (.const (.n (B + 7)) w33), .atom (.mul (.n (cpPk r)) (.n (B + 8)) (.n (B + 6))),
    .atom (.rangeCheck (.n (B + 8)) (.n (B + 9)) (.n (B + 10)) (.n (B + 11)) (.n (B + 7))),
    .atom (.add (.n (B + 12)) (.n (cpPk r)) (.n (B + 6))),
    .ite (.n (B + 12))
      [.atom (.const (.n (B + 13)) w91), .atom (.mul (.n B) (.n (B + 14)) (.n (cpPc r))),
        .atom (.rangeCheck (.n (B + 14)) (.n (B + 15)) (.n (B + 16)) (.n (B + 17)) (.n (B + 13)))]
      [],
    .atom (.mul (.n (B + 18)) (.n 100) (.n B)), .atom (.load (.n (B - 1)) (.n (B + 18)) 0),
    .atom (.const (.n (B + 19)) w33),
    .atom (.rangeCheck (.n (B + 6)) (.n (B + 20)) (.n (B + 21)) (.n (B + 22)) (.n (B + 19))),
    .atom (.mul (.n (B + 23)) (.n 1) (.n (B + 6))), .atom (.load (.n (B + 24)) (.n (B + 23)) 0),
    .atom (.mul (.n (B + 25)) (.n (B - 1)) (.n (B + 24)))]

/-- The expansion of `certify_placement`. -/
def cpBody : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 92))] ++ ((List.range 92).map cpInit).flatten ++
    [.atom (.hint (.alloc (.n 99) 92)),
      .atom (.hint (.witness "col_sort_order" (.heap (.n 99) 0 92))),
      .atom (.hint (.alloc (.n 100) 92))] ++
    cpRank0 ++ ((List.range 91).map fun r => cpRank (r + 1)).flatten ++
    [.atom (.copy (.n 2482) (.n 2481)), .atom (.copy (.n 2483) (.n 100)),
      .atom (.copy (.n 2484) (.n 2)), .ret [.n 2482, .n 2483, .n 2484]]

theorem core13_body : Fn.body Data.core13 = cpBody := stmtsEqb_sound (by decide +kernel)

/-! ## The template's conditions -/

/-- The value number of column `c`'s source word. -/
def cpW (c : ℕ) : ℕ := if c < 4 then 3 + c else if c = 4 then 7 else if c = 5 then 10 else c + 7

/-- The value number of column `c`'s size. -/
def cpV (c : ℕ) : ℕ := if c < 4 then 3 + c else if c = 4 then 9 else if c = 5 then 12 else c + 7

/-- Rank `r`'s column, size and running offset, by their value numbers. -/
def cpCol (r : ℕ) : ℕ := if r = 0 then 101 else 90 + 26 * r
def cpKap (r : ℕ) : ℕ := if r = 0 then 107 else 96 + 26 * r
def cpG (r : ℕ) : ℕ := if r = 0 then 108 else 89 + 26 * r

/-- A range check's atom holds. -/
def RcHolds (rd : Reader) (σ : Val) (x y t1 t2 k : ℕ) : Prop :=
  LoadHolds rd (σ (.n x)) 0 (σ (.n t1)) ∧ σ (.n k) = σ (.n x) * σ (.n y) ∧
    LoadHolds rd (σ (.n y)) 0 (σ (.n t2))

/-- What rank `r ≥ 1` asks of a valuation. -/
def CpRankOk (rd : Reader) (σ : Val) (r : ℕ) : Prop :=
  let B := 90 + 26 * r
  LoadHolds rd (σ (.n 99)) r (σ (.n B)) ∧ σ (.n (B + 1)) = w91 ∧
    RcHolds rd σ B (B + 2) (B + 3) (B + 4) (B + 1) ∧ σ (.n (B + 5)) = σ (.n 2) * σ (.n B) ∧
    LoadHolds rd (σ (.n (B + 5))) 0 (σ (.n (B + 6))) ∧ σ (.n (B + 7)) = w33 ∧
    σ (.n (cpPk r)) = σ (.n (B + 8)) * σ (.n (B + 6)) ∧
    RcHolds rd σ (B + 8) (B + 9) (B + 10) (B + 11) (B + 7) ∧
    σ (.n (B + 12)) = σ (.n (cpPk r)) + σ (.n (B + 6)) ∧
    (IsInK (σ (.n (B + 12))) ∧ (σ (.n (B + 12)) = 0 → σ (.n (B + 13)) = w91 ∧
      σ (.n B) = σ (.n (B + 14)) * σ (.n (cpPc r)) ∧
      RcHolds rd σ (B + 14) (B + 15) (B + 16) (B + 17) (B + 13))) ∧
    σ (.n (B + 18)) = σ (.n 100) * σ (.n B) ∧
    LoadHolds rd (σ (.n (B + 18))) 0 (σ (.n (B - 1))) ∧ σ (.n (B + 19)) = w33 ∧
    RcHolds rd σ (B + 6) (B + 20) (B + 21) (B + 22) (B + 19) ∧
    σ (.n (B + 23)) = σ (.n 1) * σ (.n (B + 6)) ∧
    LoadHolds rd (σ (.n (B + 23))) 0 (σ (.n (B + 24))) ∧
    σ (.n (B + 25)) = σ (.n (B - 1)) * σ (.n (B + 24))

section
variable {C : CallRel} {rd : Reader} {σ : Val}

theorem holds_cpRank (r : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (cpRank r) True kret ↔ CpRankOk rd σ r := by
  simp only [cpRank, CpRankOk, RcHolds]
  rw [Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
    Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList, Stmt.HoldsList,
    holds_ite_noRet _ _ _ rfl rfl]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, implies_true]

/-- What column `c`'s size asks of a valuation. -/
def CpInitOk (rd : Reader) (σ : Val) (c : ℕ) : Prop :=
  LoadHolds rd (σ (.n 0)) (cpSrc c) (σ (.n (cpW c))) ∧
    (cpAdj c ≠ 0 → σ (.n (cpW c + 1)) = word (2 ^ cpAdj c) 0 0 ∧
      σ (.n (cpV c)) = σ (.n (cpW c)) * σ (.n (cpW c + 1))) ∧
    LoadHolds rd (σ (.n 2)) c (σ (.n (cpV c)))

theorem holds_cpInit (c : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (cpInit c) True kret ↔ CpInitOk rd σ c := by
  unfold cpInit CpInitOk cpW cpV cpAdj cpSrc
  split_ifs <;> subst_vars <;>
    simp_all [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_assoc]

/-- The function's body, simplified to its conditions. -/
theorem cp_unfold (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "certify_placement" args rets ↔ ∃ σ : Val, [σ (.n 0), σ (.n 1)] = args ∧
      (∀ c < 92, CpInitOk rd σ c) ∧
      LoadHolds rd (σ (.n 99)) 0 (σ (.n 101)) ∧ σ (.n 102) = w91 ∧
      RcHolds rd σ 101 103 104 105 102 ∧ σ (.n 106) = σ (.n 2) * σ (.n 101) ∧
      LoadHolds rd (σ (.n 106)) 0 (σ (.n 107)) ∧ σ (.n 108) = word 1 0 0 ∧
      σ (.n 109) = σ (.n 100) * σ (.n 101) ∧ LoadHolds rd (σ (.n 109)) 0 (σ (.n 108)) ∧
      σ (.n 110) = w33 ∧ RcHolds rd σ 107 111 112 113 110 ∧
      σ (.n 114) = σ (.n 1) * σ (.n 107) ∧ LoadHolds rd (σ (.n 114)) 0 (σ (.n 115)) ∧
      (∀ r < 91, CpRankOk rd σ (r + 1)) ∧
      σ (.n 2482) = σ (.n 2481) ∧ σ (.n 2483) = σ (.n 100) ∧ σ (.n 2484) = σ (.n 2) ∧
      [σ (.n 2482), σ (.n 2483), σ (.n 2484)] = rets := by
  rw [rel_iff_sem (by exact Program.find?_of_indexOf? (j := 13) (by decide +kernel) rfl),
    core13_body, show Fn.params Data.core13 = [.n 0, .n 1] from rfl, cpBody]
  simp only [holdsList_append, holdsList_range_flatten 92 cpInit (fun c => by
      unfold cpInit; split_ifs <;> rfl),
    holdsList_range_flatten 91 (fun r => cpRank (r + 1)) (fun _ => rfl), holds_cpInit,
    holds_cpRank, cpRank0, RcHolds, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil, true_and]

end

/-! ## The meaning -/

/-- `stackOffsets`'s order of the sizes `κs` (V:878-879): larger first, ties by index. -/
def stackOrder (κs : List ℕ) : List ℕ :=
  (List.range κs.length).mergeSort (stackLe (κs.getD · 0))

/-- **`certify_placement(kappa_base, g_squares)`** (G:1966-1999; TRIAGE #41): the committed
columns' log sizes `κs`, each below 34 and `kappa_base[src]·g^adj` (`cpSrc`, `cpAdj`), are laid
out by `stackOffsets` (V:877): a run holds the hinted order, `stackOrder κs`, the returned `kaps`
holds `g^κ` per column, `offs` holds `g^offset` per column, and the total is
`g^(Σ 2^κ)`. -/
def MeaningCertifyPlacement (rd : Reader) : List E → List E → Prop
  | [kb, _], [gT, offs, kaps] => ∃ κs : List ℕ, κs.length = 92 ∧
      (∀ c < 92, κs.getD c 0 < 34 ∧
        ∃ w, LoadHolds rd kb (cpSrc c) w ∧ w * gen ^ cpAdj c = gen ^ κs.getD c 0) ∧
      (∃ so, ReadsAt rd so ((stackOrder κs).map (gen ^ ·))) ∧
      ReadsAt rd kaps (κs.map (gen ^ ·)) ∧ ReadsAt rd offs ((stackOffsets κs).1.map (gen ^ ·)) ∧
      gT = gen ^ (κs.map (2 ^ ·)).sum
  | _, _ => False

/-! ## Soundness -/

/-- What rank `r` gives, uniformly. -/
def CpFacts (rd : Reader) (σ : Val) (r : ℕ) : Prop :=
  (∃ p < 92, σ (.n (cpCol r)) = gen ^ p) ∧ LoadHolds rd (σ (.n 99)) r (σ (.n (cpCol r))) ∧
    (∃ k < 34, σ (.n (cpKap r)) = gen ^ k) ∧
    LoadHolds rd (σ (.n 2) * σ (.n (cpCol r))) 0 (σ (.n (cpKap r))) ∧
    LoadHolds rd (σ (.n 100) * σ (.n (cpCol r))) 0 (σ (.n (cpG r))) ∧
    (∃ t, LoadHolds rd (σ (.n 1) * σ (.n (cpKap r))) 0 t ∧
      σ (.n (cpG (r + 1))) = σ (.n (cpG r)) * t) ∧
    (1 ≤ r → (∃ d < 34, σ (.n (cpKap (r - 1))) = gen ^ d * σ (.n (cpKap r))) ∧
      (σ (.n (cpKap (r - 1))) + σ (.n (cpKap r)) = 0 →
        ∃ e < 92, σ (.n (cpCol r)) = gen ^ e * σ (.n (cpCol (r - 1)))))

section
variable {μ : ℕ} (hμ7 : 7 ≤ μ) (hμ : μ ≤ 32) (Lm : MemImage μ)
include hμ7 hμ

theorem rc92 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w91) (h : RcHolds Lm.read σ x y t1 t2 k) :
    ∃ e < 92, σ (.n x) = gen ^ e :=
  rc_sound hμ Lm (K := 92) (by omega) (le_trans (by decide) (Nat.pow_le_pow_right (by omega) hμ7))
    (by rw [hk]; exact word_g91) h.1 h.2.1 h.2.2

theorem rc34 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w33) (h : RcHolds Lm.read σ x y t1 t2 k) :
    ∃ e < 34, σ (.n x) = gen ^ e :=
  rc_sound hμ Lm (K := 34) (by omega) (le_trans (by decide) (Nat.pow_le_pow_right (by omega) hμ7))
    (by rw [hk]; exact word_g33) h.1 h.2.1 h.2.2

theorem cpFacts_succ {σ : Val} {r : ℕ} (h : CpRankOk Lm.read σ (r + 1)) : CpFacts Lm.read σ (r + 1) := by
  obtain ⟨l0, c1, rc0, m5, l6, c7, m8, rc8, a12, ⟨hK, hz⟩, m18, l18, c19, rc6, m23, l24, m25⟩ := h
  have hB : ∀ j, 90 + 26 * (r + 1) + j = 116 + 26 * r + j := fun j => by ring
  have ecol : cpCol (r + 1) = 90 + 26 * (r + 1) := by
    simp only [cpCol, Nat.add_one_ne_zero, ↓reduceIte]
  have ekap : cpKap (r + 1) = 90 + 26 * (r + 1) + 6 := by
    simp only [cpKap, Nat.add_one_ne_zero, ↓reduceIte]; omega
  have eG : cpG (r + 1) = 90 + 26 * (r + 1) - 1 := by
    simp only [cpG, Nat.add_one_ne_zero, ↓reduceIte]; omega
  have eG1 : cpG (r + 1 + 1) = 90 + 26 * (r + 1) + 25 := by
    simp only [cpG, Nat.add_one_ne_zero, ↓reduceIte]; omega
  have ePk : cpPk (r + 1) = cpKap r := by unfold cpPk cpKap; split_ifs <;> omega
  have ePc : cpPc (r + 1) = cpCol r := by unfold cpPc cpCol; split_ifs <;> omega
  unfold CpFacts
  rw [ecol, ekap, eG, eG1]
  refine ⟨rc92 hμ7 hμ Lm c1 rc0, l0, rc34 hμ7 hμ Lm c19 rc6, by rw [← m5]; exact l6,
    by rw [← m18]; exact l18, ⟨_, by rw [← m23]; exact l24, m25⟩, fun _ => ⟨?_, fun h0 => ?_⟩⟩
  · obtain ⟨d, hd, hq⟩ := rc34 hμ7 hμ Lm c7 rc8
    refine ⟨d, hd, ?_⟩
    rw [Nat.add_sub_cancel, ← ePk, m8, hq]
  · rw [Nat.add_sub_cancel, ← ePk, ← a12] at h0
    obtain ⟨c13, m14, rc14⟩ := hz h0
    obtain ⟨e, he, hq⟩ := rc92 hμ7 hμ Lm c13 rc14
    exact ⟨e, he, by rw [m14, hq, Nat.add_sub_cancel, ePc]⟩

end

/-- Choices below `n` as a function. -/
theorem exists_fun_of_forall {α : Type} [Inhabited α] {n : ℕ} {P : ℕ → α → Prop}
    (h : ∀ r < n, ∃ a, P r a) : ∃ f : ℕ → α, ∀ r < n, P r (f r) := by
  classical
  exact ⟨fun r => if hr : r < n then Classical.choose (h r hr) else default,
    fun r hr => by simp only [hr, ↓reduceDIte]; exact Classical.choose_spec (h r hr)⟩

theorem prefixSize_map (s : ℕ → ℕ) (l : List ℕ) (r : ℕ) :
    prefixSize s l r = prefixSize id (l.map s) r := by
  simp [prefixSize, List.map_take, List.map_map, Function.comp_def]

theorem prefixSize_le (k : ℕ → ℕ) (hk : ∀ r < 92, k r < 34) :
    ∀ r ≤ 92, prefixSize id ((List.range 92).map k) r ≤ r * 2 ^ 33
  | 0, _ => by simp [prefixSize]
  | r + 1, hr => by
    rw [prefixSize_succ _ _ _ (by simp; omega)]
    have := prefixSize_le k hk r (by omega)
    simp only [id, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show r < 92 by omega), Option.map_some, Option.getD_some]
    have : 2 ^ k r ≤ 2 ^ 33 := Nat.pow_le_pow_right (by decide) (by have := hk r (by omega); omega)
    nlinarith

theorem prefixSize_strict (k : ℕ → ℕ) :
    ∀ r r', r < r' → r' ≤ 92 →
      prefixSize id ((List.range 92).map k) r < prefixSize id ((List.range 92).map k) r'
  | r, r' + 1, h, h' => by
    rw [prefixSize_succ _ _ _ (by simp; omega)]
    rcases Nat.lt_or_ge r r' with hlt | hge
    · have := prefixSize_strict k r r' hlt (by omega)
      have : 0 < 2 ^ (((List.range 92).map k).getD r' 0) := Nat.two_pow_pos _
      simp only [id]; omega
    · obtain rfl : r = r' := by omega
      have : 0 < 2 ^ (((List.range 92).map k).getD r 0) := Nat.two_pow_pos _
      simp only [id]; omega

theorem cp_sound {μ : ℕ} (hμ7 : 7 ≤ μ) (hμ : μ ≤ 32) (Lm : MemImage μ) {kb sq : E}
    (hsq : ∀ j < 34, LoadHolds Lm.read sq j (gen ^ 2 ^ j)) (rets : List E)
    (h : coreProgram.Rel Lm.read "certify_placement" [kb, sq] rets) :
    MeaningCertifyPlacement Lm.read [kb, sq] rets := by
  rw [cp_unfold] at h
  obtain ⟨σ, hp, hinit, l101, c102, rc101, m106, l107, c108, m109, l108, c110, rc107, m114, l115,
    hranks, e2482, e2483, e2484, hret⟩ := h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1⟩ := hp
  -- the uniform facts of every rank
  have hf : ∀ r < 92, CpFacts Lm.read σ r := fun r hr => by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · show CpFacts Lm.read σ 0
      unfold CpFacts
      simp only [cpCol, cpKap, cpG, ↓reduceIte, Nat.zero_add, one_ne_zero, Nat.reduceMul,
        Nat.reduceAdd]
      refine ⟨rc92 hμ7 hμ Lm c102 rc101, l101, rc34 hμ7 hμ Lm c110 rc107, by rw [← m106]; exact l107,
        by rw [← m109]; exact l108, ⟨_, by rw [← m114]; exact l115, ?_⟩, fun h => absurd h (by omega)⟩
      rw [c108, word_one, one_mul]
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      exact cpFacts_succ hμ7 hμ Lm (hranks r' (by omega))
  obtain ⟨π, hπ⟩ := exists_fun_of_forall (n := 92) (fun r hr => (hf r hr).1)
  obtain ⟨k, hk⟩ := exists_fun_of_forall (n := 92) (fun r hr => (hf r hr).2.2.1)
  set S := fun r => prefixSize id ((List.range 92).map k) r
  have hS92 : ∀ r ≤ 92, S r < 2 ^ 62 := fun r hr => by
    show prefixSize id ((List.range 92).map k) r < 2 ^ 62
    have := prefixSize_le k (fun r hr => (hk r hr).1) r hr
    have : r * 2 ^ 33 ≤ 92 * 2 ^ 33 := Nat.mul_le_mul_right _ hr
    omega
  -- the running offsets
  have hG : ∀ r ≤ 92, σ (.n (cpG r)) = gen ^ S r := fun r hr => by
    induction r with
    | zero => show σ (.n 108) = gen ^ 0; rw [c108, word_one, pow_zero]
    | succ r ih =>
      obtain ⟨-, -, -, -, -, ⟨t, lt, et⟩, -⟩ := hf r (by omega)
      rw [(hk r (by omega)).2, loadHolds_mul_gen_pow, h1, Nat.add_zero] at lt
      rw [et, ih (by omega), loadHolds_unique lt (hsq _ (hk r (by omega)).1), ← pow_add]
      simp only [S]
      rw [prefixSize_succ _ _ _ (by simp; omega)]
      simp [List.getElem?_range (show r < 92 by omega)]
  -- write-once: the order is injective
  have hoff : ∀ r < 92, LoadHolds Lm.read (σ (.n 100)) (π r) (gen ^ S r) := fun r hr => by
    have := (hf r hr).2.2.2.2.1
    rw [(hπ r hr).2, loadHolds_mul_gen_pow, Nat.add_zero, hG r (by omega)] at this
    exact this
  have hinj : ∀ r < 92, ∀ r' < 92, π r = π r' → r = r' := fun r hr r' hr' he => by
    have e := loadHolds_unique (hoff r hr) (he ▸ hoff r' hr')
    have := gen_pow_inj' (by have := hS92 r (by omega); omega) (by have := hS92 r' (by omega); omega) e
    rcases Nat.lt_trichotomy r r' with h | h | h
    · exact absurd this (Nat.ne_of_lt (prefixSize_strict k r r' h (by omega)))
    · exact h
    · exact absurd this (Nat.ne_of_gt (prefixSize_strict k r' r h (by omega)))
  -- pigeonhole: a bijection
  have hsurj : ∀ c < 92, ∃ r < 92, π r = c := by
    let f : Fin 92 → Fin 92 := fun r => ⟨π r, (hπ r r.2).1⟩
    have hfi : Function.Injective f := fun a b hab =>
      Fin.ext (hinj a a.2 b b.2 (congrArg Fin.val hab))
    have hfb := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi, rfl⟩
    intro c hc
    obtain ⟨r, hr⟩ := hfb.2 ⟨c, hc⟩
    exact ⟨r, r.2, congrArg Fin.val hr⟩
  obtain ⟨πi, hπi⟩ := exists_fun_of_forall (n := 92) (fun c hc => (hsurj c hc))
  have hπiπ : ∀ r < 92, πi (π r) = r := fun r hr =>
    hinj _ (hπi _ (hπ r hr).1).1 _ hr (hπi _ (hπ r hr).1).2
  set κs := (List.range 92).map fun c => k (πi c)
  have hlen : κs.length = 92 := by simp [κs]
  have hsize : ∀ c < 92, κs.getD c 0 = k (πi c) := fun c hc => by
    simp [κs, List.getElem?_range hc]
  have hsizeπ : ∀ r < 92, κs.getD (π r) 0 = k r := fun r hr => by
    rw [hsize _ (hπ r hr).1, hπiπ r hr]
  -- the order is stackOffsets's
  set ord := (List.range 92).map π
  have hordget : ∀ r < 92, ord.getD r 0 = π r := fun r hr => by
    simp [ord, List.getElem?_range hr]
  have hperm : ord.Perm (List.range 92) := by
    rw [List.perm_ext_iff_of_nodup _ List.nodup_range]
    · intro a
      simp only [ord, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨r, hr, rfl⟩; exact (hπ r hr).1
      · intro ha; obtain ⟨r, hr, he⟩ := hsurj a ha; exact ⟨r, hr, he⟩
    · exact (List.nodup_map_iff_inj_on List.nodup_range).mpr fun a ha b hb he =>
        hinj a (List.mem_range.mp ha) b (List.mem_range.mp hb) he
  have hord : ord = stackOrder κs := by
    rw [stackOrder, hlen]
    refine eq_mergeSort_of_adjacent (κs.getD · 0) hperm fun i hi => ?_
    have hi' : i + 1 < 92 := by simpa [ord] using hi
    simp only [ord, List.getElem_map, List.getElem_range]
    rw [hsizeπ i (by omega), hsizeπ (i + 1) hi']
    obtain ⟨-, -, -, -, -, -, hadj⟩ := hf (i + 1) hi'
    obtain ⟨⟨d, hd, hdk⟩, htie⟩ := hadj (by omega)
    rw [Nat.add_sub_cancel, (hk i (by omega)).2, (hk (i + 1) hi').2] at hdk htie
    have e1 := gen_pow_eq_mul (by have := (hk i (by omega)).1; omega)
      (by have := (hk (i + 1) hi').1; omega) (by omega) hdk
    refine ⟨by omega, fun heq => ?_⟩
    have h0 : gen ^ k i + gen ^ k (i + 1) = 0 := by rw [heq]; exact e_add_self _
    obtain ⟨e, he, hcol⟩ := htie h0
    rw [(hπ (i + 1) hi').2, (hπ i (by omega)).2] at hcol
    have := gen_pow_eq_mul (by have := (hπ (i + 1) hi').1; omega)
      (by have := (hπ i (by omega)).1; omega) (by omega) hcol
    omega
  -- the sums
  have hSord : ∀ r ≤ 92, prefixSize (κs.getD · 0) ord r = S r := fun r hr => by
    have hmap : ord.map (κs.getD · 0) = (List.range 92).map k := by
      rw [List.map_map]
      exact List.map_congr_left fun r hr => hsizeπ r (List.mem_range.mp hr)
    rw [prefixSize_map, hmap]
  have hkaps : ∀ r < 92, LoadHolds Lm.read (σ (.n 2)) (π r) (gen ^ k r) := fun r hr => by
    have := (hf r hr).2.2.2.1
    rw [(hπ r hr).2, (hk r hr).2, loadHolds_mul_gen_pow, Nat.add_zero] at this
    exact this
  have hκc : ∀ r < 92, κs.getD (π r) 0 = k r := hsizeπ
  subst hret
  refine ⟨κs, hlen, fun c hc => ⟨?_, ?_⟩, ⟨σ (.n 99), readsAt_map_iff.mpr fun r hr => ?_⟩,
    readsAt_map_iff.mpr fun c hc => ?_, readsAt_map_iff.mpr fun c hc => ?_, ?_⟩
  · rw [hsize c hc]; exact (hk _ (hπi c hc).1).1
  · obtain ⟨lw, hadj, lv⟩ := hinit c hc
    have hv : σ (.n (cpV c)) = gen ^ κs.getD c 0 := by
      obtain ⟨r, hr, hrc⟩ : ∃ r, r < 92 ∧ π r = c := ⟨πi c, hπi c hc⟩
      have := hkaps _ hr
      rw [hrc] at this
      rw [loadHolds_unique lv this, hsize c hc, ← hrc, hπiπ r hr]
    refine ⟨σ (.n (cpW c)), by rw [← h0]; exact lw, ?_⟩
    by_cases ha : cpAdj c = 0
    · rw [ha, pow_zero, mul_one, ← hv]
      unfold cpAdj at ha; unfold cpV cpW
      split_ifs at ha ⊢ <;> rfl
    · obtain ⟨ew, ev⟩ := hadj ha
      rw [← hv, ev, ew, word_two_pow (by unfold cpAdj; split_ifs <;> omega)]
  · have hr' : r < 92 := by rwa [← hord, List.length_map, List.length_range] at hr
    rw [← hord, hordget r hr', ← (hπ r hr').2]
    exact (hf r hr').2.1
  · have hc' : c < 92 := by rwa [hlen] at hc
    obtain ⟨r, hr, hrc⟩ : ∃ r, r < 92 ∧ π r = c := ⟨πi c, hπi c hc'⟩
    rw [hsize c hc', e2484, ← hrc, hπiπ r hr]
    exact hkaps r hr
  · have hc' : c < 92 := by rwa [stackOffsets_length, hlen] at hc
    obtain ⟨r, hr, hrc⟩ : ∃ r, r < 92 ∧ π r = c := ⟨πi c, hπi c hc'⟩
    rw [e2483, ← hrc, ← hordget r hr, hord, stackOrder, stackOffsets_fst κs r (by omega),
      ← stackOrder, ← hord, hSord r (by omega), hordget r hr]
    exact hoff r hr
  · have hfull : prefixSize (κs.getD · 0) ord 92 = (ord.map fun i => 2 ^ κs.getD i 0).sum := by
      have := prefixSize_full (κs.getD · 0) ord
      rwa [show ord.length = 92 by simp [ord]] at this
    rw [e2482, show σ (.n 2481) = σ (.n (cpG 92)) from rfl, hG 92 le_rfl, ← hSord 92 le_rfl, hfull]
    refine congrArg (fun x => gen ^ x) ?_
    rw [(hperm.map _).sum_eq]
    simp only [κs, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun c hc => by
      simp only [Function.comp_apply]; rw [hsize c (List.mem_range.mp hc)])

end
end LeanVM.Guest.B1
