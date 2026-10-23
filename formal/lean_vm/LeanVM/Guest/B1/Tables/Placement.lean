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
variable {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ)
include hμ

theorem rc92 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w91) (h : RcHolds Lm.read σ x y t1 t2 k) :
    ∃ e < 92, σ (.n x) = gen ^ e :=
  rc_sound' hμ Lm (K := 92) (by omega) (by decide) (by rw [hk]; exact word_g91) h.1 h.2.1 h.2.2

theorem rc34 {σ : Val} {x y t1 t2 k : ℕ} (hk : σ (.n k) = w33) (h : RcHolds Lm.read σ x y t1 t2 k) :
    ∃ e < 34, σ (.n x) = gen ^ e :=
  rc_sound' hμ Lm (K := 34) (by omega) (by decide) (by rw [hk]; exact word_g33) h.1 h.2.1 h.2.2

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
  refine ⟨rc92 hμ Lm c1 rc0, l0, rc34 hμ Lm c19 rc6, by rw [← m5]; exact l6,
    by rw [← m18]; exact l18, ⟨_, by rw [← m23]; exact l24, m25⟩, fun _ => ⟨?_, fun h0 => ?_⟩⟩
  · obtain ⟨d, hd, hq⟩ := rc34 hμ Lm c7 rc8
    refine ⟨d, hd, ?_⟩
    rw [Nat.add_sub_cancel, ← ePk, m8, hq]
  · rw [Nat.add_sub_cancel, ← ePk, ← a12] at h0
    obtain ⟨c13, m14, rc14⟩ := hz h0
    obtain ⟨e, he, hq⟩ := rc92 hμ Lm c13 rc14
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

theorem cp_sound {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemImage μ) {kb sq : E}
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
      refine ⟨rc92 hμ Lm c102 rc101, l101, rc34 hμ Lm c110 rc107, by rw [← m106]; exact l107,
        by rw [← m109]; exact l108, ⟨_, by rw [← m114]; exact l115, ?_⟩, fun h => absurd h (by omega)⟩
      rw [c108, word_one, one_mul]
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      exact cpFacts_succ hμ Lm (hranks r' (by omega))
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

/-! ## Completeness -/

section
variable (A B C D : ℕ → E × E × E) (κs : List ℕ)

/-- Rank `r`'s column in `stackOffsets`'s order. -/
def cpPi (r : ℕ) : ℕ := (stackOrder κs).getD r 0

/-- Rank `r`'s size. -/
def cpK (r : ℕ) : ℕ := κs.getD (cpPi κs r) 0

/-- The running offset before rank `r`. -/
def cpS (r : ℕ) : ℕ := prefixSize (κs.getD · 0) (stackOrder κs) r

/-- Rank `r ≥ 1`'s honest values, from `B = 90 + 26·r`. -/
def cpRankVals (sq p2 p100 : E) (r : ℕ) : List E :=
  let x := gen ^ cpPi κs r
  let kv := gen ^ cpK κs r
  let q := gen ^ (cpK κs (r - 1) - cpK κs r)
  let q' := gen ^ (cpPi κs r - cpPi κs (r - 1))
  [x, w91, (A r).1, (A r).2.1, (A r).2.2, p2 * x, kv, w33, q,
    (B r).1, (B r).2.1, (B r).2.2, gen ^ cpK κs (r - 1) + kv, w91, q',
    (C r).1, (C r).2.1, (C r).2.2, p100 * x, w33,
    (D r).1, (D r).2.1, (D r).2.2, sq * kv, gen ^ 2 ^ cpK κs r,
    gen ^ cpS κs (r + 1)]

/-- Rank `0`'s honest values, from `101`. -/
def cpRank0Vals (sq p2 p100 : E) : List E :=
  let x := gen ^ cpPi κs 0
  let kv := gen ^ cpK κs 0
  [x, w91, (A 0).1, (A 0).2.1, (A 0).2.2, p2 * x, kv, word 1 0 0,
    p100 * x, w33, (D 0).1, (D 0).2.1, (D 0).2.2, sq * kv,
    gen ^ 2 ^ cpK κs 0]

/-- The columns' sizes' honest values, `3 .. 98`. -/
noncomputable def cpInitVals (w : ℕ → E) (i : ℕ) : E :=
  if i < 7 then w (i - 3) else if i = 7 then w 4 else if i = 8 then word (2 ^ 18) 0 0
  else if i = 9 then w 4 * word (2 ^ 18) 0 0 else if i = 10 then w 5
  else if i = 11 then word (2 ^ 8) 0 0 else if i = 12 then w 5 * word (2 ^ 8) 0 0 else w (i - 7)

/-- The honest valuation's value `i`. -/
noncomputable def cpF (kb sq p2 p99 p100 : E) (w : ℕ → E) (i : ℕ) : E :=
  if i < 3 then [kb, sq, p2].getD i 0
  else if i < 99 then cpInitVals w i
  else if i = 99 then p99 else if i = 100 then p100
  else if i < 116 then (cpRank0Vals A D κs sq p2 p100).getD (i - 101) 0
  else if i < 2482 then (cpRankVals A B C D κs sq p2 p100 ((i - 90) / 26)).getD ((i - 90) % 26) 0
  else if i = 2482 then gen ^ cpS κs 92 else if i = 2483 then p100 else p2

variable {kb sq p2 p99 p100 : E} {w : ℕ → E}

theorem cpF_rank {i r j : ℕ} (hi : i = 90 + 26 * r + j) (hr1 : 1 ≤ r) (hr : r ≤ 91) (hj : j < 26) :
    cpF A B C D κs kb sq p2 p99 p100 w i = (cpRankVals A B C D κs sq p2 p100 r).getD j 0 := by
  subst hi
  rw [cpF, ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_neg' (by omega), ite_pos' (by omega), show (90 + 26 * r + j - 90) / 26 = r by omega,
    show (90 + 26 * r + j - 90) % 26 = j by omega]

theorem cpF_rank0 {i j : ℕ} (hi : i = 101 + j) (hj : j < 15) :
    cpF A B C D κs kb sq p2 p99 p100 w i = (cpRank0Vals A D κs sq p2 p100).getD j 0 := by
  subst hi
  rw [cpF, ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_pos' (by omega), Nat.add_sub_cancel_left]

theorem stackOrder_length : (stackOrder κs).length = κs.length := by
  rw [stackOrder, List.length_mergeSort, List.length_range]

theorem cpS_succ {r : ℕ} (hr : r < κs.length) : cpS κs (r + 1) = cpS κs r + 2 ^ cpK κs r := by
  rw [cpS, cpS, prefixSize_succ _ _ _ (by rw [stackOrder_length]; exact hr)]; rfl

/-- The running offset at rank `r`'s store. -/
theorem cpF_G (hlen : κs.length = 92) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ 91) :
    cpF A B C D κs kb sq p2 p99 p100 w (90 + 26 * r - 1) = gen ^ cpS κs r := by
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    rw [cpF_rank0 A B C D κs (j := 14) rfl (by omega)]
    simp only [cpRank0Vals, List.getD_cons_succ, List.getD_cons_zero]
    rw [cpS_succ κs (by omega), cpS, prefixSize, List.take_zero, List.map_nil, List.sum_nil,
      Nat.zero_add]
  · rw [cpF_rank A B C D κs (r := r - 1) (j := 25) (by omega) (by omega) (by omega) (by omega)]
    simp only [cpRankVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [Nat.sub_add_cancel (by omega)]

end

/-- `stackOrder` is sorted on adjacent entries: sizes do not increase, ties ascend. -/
theorem stackOrder_adj (κs : List ℕ) {r : ℕ} (hr : r + 1 < κs.length) :
    cpK κs (r + 1) ≤ cpK κs r ∧ (cpK κs r = cpK κs (r + 1) → cpPi κs r ≤ cpPi κs (r + 1)) := by
  have htrans : ∀ a b c, stackLe (κs.getD · 0) a b = true → stackLe (κs.getD · 0) b c = true →
      stackLe (κs.getD · 0) a c = true := by
    intro a b c hab hbc
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
    omega
  have htotal : ∀ a b, (stackLe (κs.getD · 0) a b || stackLe (κs.getD · 0) b a) = true := by
    intro a b
    simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    omega
  have hp := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort htrans htotal
    (List.range κs.length))
  have hl : (stackOrder κs).length = κs.length := stackOrder_length κs
  have h := hp r (r + 1) (by rw [← stackOrder, hl]; omega) (by rw [← stackOrder, hl]; omega)
    (by omega)
  simp only [stackLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  simp only [cpK, cpPi, List.getD_eq_getElem _ _ (show r < (stackOrder κs).length by omega),
    List.getD_eq_getElem _ _ (show r + 1 < (stackOrder κs).length by omega)]
  unfold stackOrder at *
  omega

theorem cpF_init {A B C D : ℕ → E × E × E} {κs : List ℕ} {kb sq p2 p99 p100 : E} {w : ℕ → E}
    {i : ℕ} (h3 : 3 ≤ i) (h99 : i < 99) : cpF A B C D κs kb sq p2 p99 p100 w i = cpInitVals w i := by
  rw [cpF, ite_neg' (by omega), ite_pos' h99]

theorem cpInitVals_W (w : ℕ → E) {c : ℕ} (hc : c < 92) : cpInitVals w (cpW c) = w c := by
  unfold cpW cpInitVals
  split_ifs <;> first | omega | (congr 1; omega) | rfl

/-- Column `c`'s size holds of the honest valuation. -/
theorem cp_init_ok (rd : Reader) {A B C D : ℕ → E × E × E} {kb sq : E} (κs : List ℕ)
    {p2 p99 p100 : E}
    {w : ℕ → E} {F : ℕ → E} (hF : F = cpF A B C D κs kb sq p2 p99 p100 w)
    (hw : ∀ c < 92, LoadHolds rd kb (cpSrc c) (w c) ∧ w c * gen ^ cpAdj c = gen ^ κs.getD c 0)
    (l2 : ∀ c < 92, LoadHolds rd p2 c (gen ^ κs.getD c 0)) (c : ℕ) (hc : c < 92) :
    CpInitOk rd (fun v => F v.idx) c := by
  have f0 : F 0 = kb := by rw [hF]; rfl
  have f2 : F 2 = p2 := by rw [hF]; rfl
  have hW : F (cpW c) = w c := by
    rw [hF, cpF_init (by unfold cpW; split_ifs <;> omega) (by unfold cpW; split_ifs <;> omega),
      cpInitVals_W w hc]
  have hV : F (cpV c) = gen ^ κs.getD c 0 := by
    by_cases ha : cpAdj c = 0
    · have : cpV c = cpW c := by
        unfold cpAdj at ha; unfold cpV cpW; split_ifs at ha ⊢ <;> rfl
      rw [this, hW, ← (hw c hc).2, ha, pow_zero, mul_one]
    · have hc45 : c = 4 ∨ c = 5 := by unfold cpAdj at ha; split_ifs at ha <;> omega
      rcases hc45 with rfl | rfl
      · rw [← (hw 4 hc).2, show cpV 4 = 9 from rfl, hF]
        show w 4 * word (2 ^ 18) 0 0 = _
        rw [word_two_pow (by omega)]; rfl
      · rw [← (hw 5 hc).2, show cpV 5 = 12 from rfl, hF]
        show w 5 * word (2 ^ 8) 0 0 = _
        rw [word_two_pow (by omega)]; rfl
  refine ⟨by show LoadHolds _ (F 0) _ (F (cpW c)); rw [f0, hW]; exact (hw c hc).1, fun ha => ?_,
    by show LoadHolds _ (F 2) _ (F (cpV c)); rw [f2, hV]; exact l2 c hc⟩
  have hc45 : c = 4 ∨ c = 5 := by unfold cpAdj at ha; split_ifs at ha <;> omega
  rcases hc45 with rfl | rfl
  · rw [hF]; exact ⟨rfl, rfl⟩
  · rw [hF]; exact ⟨rfl, rfl⟩

/-- A range check's auxiliary words `a` pass for `x` against `K`. -/
def RcOk (rd : Reader) (x : E) (K : ℕ) (a : E × E × E) : Prop :=
  LoadHolds rd x 0 a.2.1 ∧ ofK (Parameters.gpow (K - 1)) = x * a.1 ∧ LoadHolds rd a.1 0 a.2.2

/-- Rank `r + 1` holds of the honest valuation. -/

theorem cp_rank_ok (rd : Reader) {A B C D : ℕ → E × E × E} {kb sq : E}
    (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j)) (κs : List ℕ) (hlen : κs.length = 92)
    {p2 p99 p100 : E} {w : ℕ → E} {F : ℕ → E} (hF : F = cpF A B C D κs kb sq p2 p99 p100 w)
    (hπ : ∀ r < 92, cpPi κs r < 92) (hk : ∀ r < 92, cpK κs r < 34)
    (l99 : ∀ r < 92, LoadHolds rd p99 r (gen ^ cpPi κs r))
    (l2 : ∀ c < 92, LoadHolds rd p2 c (gen ^ κs.getD c 0))
    (l100 : ∀ r < 92, LoadHolds rd p100 (cpPi κs r) (gen ^ cpS κs r))
    (hA : ∀ r < 92, RcOk rd (gen ^ cpPi κs r) 92 (A r))
    (hB : ∀ r < 92, RcOk rd (gen ^ (cpK κs (r - 1) - cpK κs r)) 34 (B r))
    (hC : ∀ r < 92, RcOk rd (gen ^ (cpPi κs r - cpPi κs (r - 1))) 92 (C r))
    (hD : ∀ r < 92, RcOk rd (gen ^ cpK κs r) 34 (D r)) (r : ℕ) (hr : r < 91) :
    CpRankOk rd (fun v => F v.idx) (r + 1) := by
  have hR : ∀ R, 1 ≤ R → R ≤ 91 → ∀ j < 26,
      F (90 + 26 * R + j) = (cpRankVals A B C D κs sq p2 p100 R).getD j 0 := fun R h1 h2 j hj => by
    rw [hF]; exact cpF_rank A B C D κs rfl h1 h2 hj
  have h0 : ∀ j < 15, F (101 + j) = (cpRank0Vals A D κs sq p2 p100).getD j 0 := fun j hj => by
    rw [hF]; exact cpF_rank0 A B C D κs rfl hj
  have hG : ∀ R, 1 ≤ R → R ≤ 91 → F (90 + 26 * R - 1) = gen ^ cpS κs R := fun R h1 h2 => by
    rw [hF]; exact cpF_G A B C D κs hlen h1 h2
  have f1 : F 1 = sq := by rw [hF]; rfl
  have f2 : F 2 = p2 := by rw [hF]; rfl
  have f99 : F 99 = p99 := by rw [hF]; rfl
  have f100 : F 100 = p100 := by rw [hF]; rfl
  have hpkr : F (cpPk (r + 1)) = gen ^ cpK κs r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · exact h0 6 (by omega)
    · rw [show cpPk (r + 1) = 90 + 26 * r + 6 by unfold cpPk; rw [ite_neg' (by omega)]; omega]
      exact hR r hr0 (by omega) 6 (by omega)
  have hpcr : F (cpPc (r + 1)) = gen ^ cpPi κs r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · exact h0 0 (by omega)
    · rw [show cpPc (r + 1) = 90 + 26 * r by unfold cpPc; rw [ite_neg' (by omega)]; omega]
      exact hR r hr0 (by omega) 0 (by omega)
  have h1 : 1 ≤ r + 1 := by omega
  have h2 : r + 1 ≤ 91 := by omega
  have u := hR (r + 1) h1 h2
  have hS := cpS_succ κs (r := r + 1) (by omega)
  have adj := stackOrder_adj κs (r := r) (by omega)
  have hπ1 := hπ (r + 1) (by omega)
  have hk0 := hk r (by omega)
  have hk1 := hk (r + 1) (by omega)
  have hGr := hG (r + 1) h1 h2
  have g : ∀ j (hj : j < 26), F (90 + 26 * (r + 1) + j) =
      (cpRankVals A B C D κs sq p2 p100 (r + 1)).getD j 0 := u
  simp only [cpRankVals, Nat.add_sub_cancel] at g
  have u0 : F (90 + 26 * (r + 1)) = gen ^ cpPi κs (r + 1) := g 0 (by omega)
  have u1 : F (90 + 26 * (r + 1) + 1) = w91 := g 1 (by omega)
  have u2 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 2 (by omega)
  have u3 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 3 (by omega)
  have u4 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 4 (by omega)
  have u5 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 5 (by omega)
  have u6 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 6 (by omega)
  have u7 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 7 (by omega)
  have u8 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 8 (by omega)
  have u9 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 9 (by omega)
  have u10 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 10 (by omega)
  have u11 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 11 (by omega)
  have u12 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 12 (by omega)
  have u13 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 13 (by omega)
  have u14 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 14 (by omega)
  have u15 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 15 (by omega)
  have u16 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 16 (by omega)
  have u17 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 17 (by omega)
  have u18 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 18 (by omega)
  have u19 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 19 (by omega)
  have u20 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 20 (by omega)
  have u21 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 21 (by omega)
  have u22 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 22 (by omega)
  have u23 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 23 (by omega)
  have u24 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 24 (by omega)
  have u25 := by simpa only [List.getD_cons_succ, List.getD_cons_zero] using g 25 (by omega)
  obtain ⟨a0, b0, c0⟩ := hA (r + 1) (by omega)
  obtain ⟨a1, b1, c1⟩ := hB (r + 1) (by omega)
  obtain ⟨a3, b3, c3⟩ := hD (r + 1) (by omega)
  rw [Nat.add_sub_cancel] at a1 b1
  unfold CpRankOk RcHolds
  dsimp only
  refine ⟨?_, u1, ?_, ?_, ?_, u7, ?_, ?_, ?_, ⟨?_, fun hz => ?_⟩, ?_, ?_, u19, ?_, ?_, ?_, ?_⟩
  · rw [f99, u0]; exact l99 _ (by omega)
  · rw [u0, u1, u2, u3, u4]; exact ⟨a0, word_g91.trans b0, c0⟩
  · rw [u5, f2, u0]
  · rw [u5, u6, loadHolds_mul_gen_pow, Nat.add_zero]; exact l2 _ hπ1
  · rw [hpkr, u8, u6, ← pow_add, Nat.sub_add_cancel adj.1]
  · rw [u8, u7, u9, u10, u11]; exact ⟨a1, word_g33.trans b1, c1⟩
  · rw [u12, hpkr, u6]
  · rw [u12]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  · rw [u12] at hz
    have heq : cpK κs r = cpK κs (r + 1) :=
      gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp hz)
    have hle := adj.2 heq
    obtain ⟨a2, b2, c2⟩ := hC (r + 1) (by omega)
    rw [Nat.add_sub_cancel] at a2 b2
    refine ⟨u13, ?_, ?_⟩
    · rw [u0, u14, hpcr, ← pow_add, Nat.sub_add_cancel hle]
    · rw [u14, u13, u15, u16, u17]; exact ⟨a2, word_g91.trans b2, c2⟩
  · rw [u18, f100, u0]
  · rw [u18, hGr, loadHolds_mul_gen_pow, Nat.add_zero]; exact l100 _ (by omega)
  · rw [u6, u19, u20, u21, u22]; exact ⟨a3, word_g33.trans b3, c3⟩
  · rw [u23, f1, u6]
  · rw [u23, u24, loadHolds_mul_gen_pow, Nat.add_zero]; exact hsq _ hk1
  · rw [u25, hGr, u24, ← pow_add, hS]

theorem cp_complete {μ : ℕ} (hμ7 : 7 ≤ μ) (hμ : μ ≤ 32) (Lm : MemImage μ) {kb sq : E}
    (hsq : ∀ j < 34, LoadHolds Lm.read sq j (gen ^ 2 ^ j)) (κs : List ℕ) (hlen : κs.length = 92)
    (hκ : ∀ c < 92, κs.getD c 0 < 34 ∧
      ∃ w, LoadHolds Lm.read kb (cpSrc c) w ∧ w * gen ^ cpAdj c = gen ^ κs.getD c 0)
    (p2 p99 p100 : E) (h99 : ReadsAt Lm.read p99 ((stackOrder κs).map (gen ^ ·)))
    (h2 : ReadsAt Lm.read p2 (κs.map (gen ^ ·)))
    (h100 : ReadsAt Lm.read p100 ((stackOffsets κs).1.map (gen ^ ·))) :
    coreProgram.Rel Lm.read "certify_placement" [kb, sq]
      [gen ^ (κs.map (2 ^ ·)).sum, p100, p2] := by
  obtain ⟨w, hw⟩ := exists_fun_of_forall (n := 92) (fun c hc => (hκ c hc).2)
  have hK92 : 92 ≤ 2 ^ μ := le_trans (by decide) (Nat.pow_le_pow_right (by omega) hμ7)
  have hK34 : 34 ≤ 2 ^ μ := le_trans (by decide) (Nat.pow_le_pow_right (by omega) hμ7)
  have hol : (stackOrder κs).length = 92 := by rw [stackOrder_length, hlen]
  have hperm : (stackOrder κs).Perm (List.range 92) := by
    rw [← hlen]; exact List.mergeSort_perm _ _
  have hπ : ∀ r < 92, cpPi κs r < 92 := fun r hr => by
    have := hperm.subset (List.getElem_mem (show r < (stackOrder κs).length by omega))
    rw [cpPi, List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_range.mp this
  have hk : ∀ r < 92, cpK κs r < 34 := fun r hr => (hκ _ (hπ r hr)).1
  have l99 : ∀ r < 92, LoadHolds Lm.read p99 r (gen ^ cpPi κs r) := fun r hr =>
    readsAt_map_iff.mp h99 r (by omega)
  have l2 : ∀ c < 92, LoadHolds Lm.read p2 c (gen ^ κs.getD c 0) := fun c hc =>
    readsAt_map_iff.mp h2 c (by omega)
  have l100 : ∀ r < 92, LoadHolds Lm.read p100 (cpPi κs r) (gen ^ cpS κs r) := fun r hr => by
    have := readsAt_map_iff.mp h100 (cpPi κs r) (by rw [stackOffsets_length, hlen]; exact hπ r hr)
    rwa [cpPi, stackOrder, stackOffsets_fst κs r (by omega)] at this
  obtain ⟨A, hA⟩ := exists_fun_of_forall (n := 92) (α := E × E × E)
    (P := fun r a => RcOk Lm.read (gen ^ cpPi κs r) 92 a)
    fun r hr => ⟨_, rc_complete hμ Lm (K := 92) (e := cpPi κs r) (by omega) hK92 (hπ r hr)⟩
  obtain ⟨B, hB⟩ := exists_fun_of_forall (n := 92) (α := E × E × E)
    (P := fun r a => RcOk Lm.read (gen ^ (cpK κs (r - 1) - cpK κs r)) 34 a)
    fun r hr => ⟨_, rc_complete hμ Lm (K := 34) (e := cpK κs (r - 1) - cpK κs r) (by omega) hK34
      (lt_of_le_of_lt (Nat.sub_le _ _) (hk (r - 1) (by omega)))⟩
  obtain ⟨C, hC⟩ := exists_fun_of_forall (n := 92) (α := E × E × E)
    (P := fun r a => RcOk Lm.read (gen ^ (cpPi κs r - cpPi κs (r - 1))) 92 a)
    fun r hr => ⟨_, rc_complete hμ Lm (K := 92) (e := cpPi κs r - cpPi κs (r - 1)) (by omega)
      hK92 (lt_of_le_of_lt (Nat.sub_le _ _) (hπ r hr))⟩
  obtain ⟨D, hD⟩ := exists_fun_of_forall (n := 92) (α := E × E × E)
    (P := fun r a => RcOk Lm.read (gen ^ cpK κs r) 34 a)
    fun r hr => ⟨_, rc_complete hμ Lm (K := 34) (e := cpK κs r) (by omega) hK34 (hk r hr)⟩
  obtain ⟨F, hF⟩ : ∃ F, F = cpF A B C D κs kb sq p2 p99 p100 w := ⟨_, rfl⟩
  have hR : ∀ R, 1 ≤ R → R ≤ 91 → ∀ j < 26,
      F (90 + 26 * R + j) = (cpRankVals A B C D κs sq p2 p100 R).getD j 0 := fun R h1 h2 j hj => by
    rw [hF]; exact cpF_rank A B C D κs rfl h1 h2 hj
  have h0 : ∀ j < 15, F (101 + j) = (cpRank0Vals A D κs sq p2 p100).getD j 0 := fun j hj => by
    rw [hF]; exact cpF_rank0 A B C D κs rfl hj
  have hG : ∀ R, 1 ≤ R → R ≤ 91 → F (90 + 26 * R - 1) = gen ^ cpS κs R := fun R h1 h2 => by
    rw [hF]; exact cpF_G A B C D κs hlen h1 h2
  have f0 : F 0 = kb := by rw [hF]; rfl
  have f1 : F 1 = sq := by rw [hF]; rfl
  have f2 : F 2 = p2 := by rw [hF]; rfl
  have f99 : F 99 = p99 := by rw [hF]; rfl
  have f100 : F 100 = p100 := by rw [hF]; rfl
  have hsum : cpS κs 92 = (κs.map (2 ^ ·)).sum := by
    have hfull := prefixSize_full (κs.getD · 0) (stackOrder κs)
    rw [hol] at hfull
    rw [cpS, hfull, (hperm.map _).sum_eq]
    congr 1
    refine List.ext_getElem (by simp [hlen]) fun c h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; simpa using h1)]
  rw [cp_unfold]
  refine ⟨fun v => F v.idx, by show [F 0, F 1] = _; rw [f0, f1], fun c hc => ?_, ?_⟩
  · exact cp_init_ok Lm.read κs hF hw l2 c hc
  · have v := fun j hj => h0 j hj
    have v0 : F 101 = gen ^ cpPi κs 0 := v 0 (by omega)
    have v1 : F 102 = w91 := v 1 (by omega)
    have v2 : F 103 = (A 0).1 := v 2 (by omega)
    have v3 : F 104 = (A 0).2.1 := v 3 (by omega)
    have v4 : F 105 = (A 0).2.2 := v 4 (by omega)
    have v5 : F 106 = p2 * gen ^ cpPi κs 0 := v 5 (by omega)
    have v6 : F 107 = gen ^ cpK κs 0 := v 6 (by omega)
    have v7 : F 108 = word 1 0 0 := v 7 (by omega)
    have v8 : F 109 = p100 * gen ^ cpPi κs 0 := v 8 (by omega)
    have v9 : F 110 = w33 := v 9 (by omega)
    have v10 : F 111 = (D 0).1 := v 10 (by omega)
    have v11 : F 112 = (D 0).2.1 := v 11 (by omega)
    have v12 : F 113 = (D 0).2.2 := v 12 (by omega)
    have v13 : F 114 = sq * gen ^ cpK κs 0 := v 13 (by omega)
    have v14 : F 115 = gen ^ 2 ^ cpK κs 0 := v 14 (by omega)
    obtain ⟨a0, b0, c0⟩ := hA 0 (by omega)
    obtain ⟨a1, b1, c1⟩ := hD 0 (by omega)
    refine ⟨?_, v1, ?_, ?_, ?_, v7, ?_, ?_, v9, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · show LoadHolds _ (F 99) 0 (F 101); rw [f99, v0]; exact l99 0 (by omega)
    · show LoadHolds _ (F 101) 0 (F 104) ∧ F 102 = F 101 * F 103 ∧ LoadHolds _ (F 103) 0 (F 105)
      rw [v0, v1, v2, v3, v4]; exact ⟨a0, word_g91.trans b0, c0⟩
    · show F 106 = F 2 * F 101; rw [v5, f2, v0]
    · show LoadHolds _ (F 106) 0 (F 107)
      rw [v5, v6, loadHolds_mul_gen_pow, Nat.add_zero]; exact l2 _ (hπ 0 (by omega))
    · show F 109 = F 100 * F 101; rw [v8, f100, v0]
    · show LoadHolds _ (F 109) 0 (F 108)
      rw [v8, v7, loadHolds_mul_gen_pow, Nat.add_zero, word_one]
      have := l100 0 (by omega)
      rwa [show cpS κs 0 = 0 by simp [cpS, prefixSize], pow_zero] at this
    · show LoadHolds _ (F 107) 0 (F 112) ∧ F 110 = F 107 * F 111 ∧ LoadHolds _ (F 111) 0 (F 113)
      rw [v6, v9, v10, v11, v12]; exact ⟨a1, word_g33.trans b1, c1⟩
    · show F 114 = F 1 * F 107; rw [v13, f1, v6]
    · show LoadHolds _ (F 114) 0 (F 115)
      rw [v13, v14, loadHolds_mul_gen_pow, Nat.add_zero]; exact hsq _ (hk 0 (by omega))
    · exact cp_rank_ok Lm.read hsq κs hlen hF hπ hk l99 l2 l100 hA hB hC hD r hr
    · show F 2482 = F 2481
      rw [show F 2482 = gen ^ cpS κs 92 by rw [hF]; rfl]
      have := hR 91 (by omega) (by omega) 25 (by omega)
      simp only [cpRankVals, List.getD_cons_succ, List.getD_cons_zero] at this
      exact this.symm
    · show F 2483 = F 100; rw [f100, hF]; rfl
    · show F 2484 = F 2; rw [f2, hF]; rfl
    · show [F 2482, F 2483, F 2484] = _
      rw [show F 2482 = gen ^ cpS κs 92 by rw [hF]; rfl, show F 2483 = p100 by rw [hF]; rfl,
        show F 2484 = p2 by rw [hF]; rfl, hsum]

end
end LeanVM.Guest.B1
