/-
  LeanVM.Guest.B1.VsC.SuffixesC

  `one_plus_suffixes__L{n}` completes, layout-free.
-/

module

public import LeanVM.Guest.B1.VsC.StateEndsC
public import LeanVM.Guest.B1.Link.Suffixes
import LeanVM.Guest.CoreRef

/-!
# `one_plus_suffixes`, complete

`one_plus_suffixes(chain, a, n)` stores `chain[n] = 1` and, from `k = n - 1` down, the running
product `chain[k] = Π_{k ≤ i < n} (1 + a_i)` (`belowE as k`); it returns `0`. Its body is `opsBody n`
(`Link/Suffixes.lean`), atoms only; its stores are loads of the caller's words at `chain`.
`opsVal`: the honest valuation. `one_plus_suffixes_complete`: every `n ≤ 40`, on a memory holding
the `n` words `as` at `a` and their suffix products at `chain`, the call returns `[0]` by a tree
that pops nothing, exact.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Protocol.Verifier

@[expose] public section

/-- Block `kk` of `opsLoop o c a n`, as atoms. -/
def opsBlkA (o c a n kk : ℕ) : List Atom :=
  if kk = 0 then
    [.const (.n (o + 3)) (word 1 0), .load (.n (o + 4)) (.n a) (n - 1),
      .add (.n (o + 5)) (.n (o + 3)) (.n (o + 4)), .load (.n (o + 5)) (.n c) (n - 1)]
  else
    [.const (.n (o + 4 * kk + 2)) (word 1 0), .load (.n (o + 4 * kk + 3)) (.n a) (n - 1 - kk),
      .add (.n (o + 4 * kk + 4)) (.n (o + 4 * kk + 2)) (.n (o + 4 * kk + 3)),
      .mul (.n (o + 4 * kk + 5)) (.n (opsV o (kk - 1))) (.n (o + 4 * kk + 4)),
      .load (.n (o + 4 * kk + 5)) (.n c) (n - 1 - kk)]

theorem opsBlk_eq (o c a n kk : ℕ) : opsBlk o c a n kk = (opsBlkA o c a n kk).map Stmt.atom := by
  unfold opsBlk opsBlkA; split <;> rfl

/-- `opsBody`'s atoms. -/
def opsAtoms (n : ℕ) : List Atom :=
  [.const (.n (0 + 2)) (word 1 0), .load (.n (0 + 2)) (.n 0) n] ++
    ((List.range n).map (opsBlkA 0 0 1 n)).flatten ++ [.const (.n (opsEnd n)) (word 0 0)]

theorem opsBody_eq (n : ℕ) : opsBody n = (opsAtoms n).map Stmt.atom ++ [.ret [.n (opsEnd n)]] := by
  unfold opsBody opsLoop opsAtoms
  simp only [List.map_append, List.map_flatten, List.map_map, List.append_assoc, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append]
  congr 3
  rw [List.map_congr_left (fun k _ ↦ opsBlk_eq 0 0 1 n k)]
  rfl

theorem opsAtoms_quiet (n : ℕ) : (opsAtoms n).all noHint = true := by
  unfold opsAtoms
  simp only [List.all_append, List.all_flatten, List.all_map, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, Function.comp_apply]
  refine ⟨⟨by simp [noHint], fun k _ ↦ ?_⟩, by simp [noHint]⟩
  unfold opsBlkA; split <;> simp [noHint]

/-- **The honest word of value `i`** of `one_plus_suffixes__L{n}` at `chain`, `a` holding `as`. -/
def opsVal (chain a : E) (as : List E) (n i : ℕ) : E :=
  if i = opsEnd n then 0 else if i = 0 then chain else if i = 1 then a else if i = 2 then 1 else
  if i = 3 then 1 else if i = 4 then as.getD (n - 1) 0 else if i = 5 then belowE as (n - 1) else
  if (i - 2) % 4 = 0 then 1 else if (i - 2) % 4 = 1 then as.getD (n - 1 - (i - 2) / 4) 0 else
  if (i - 2) % 4 = 2 then 1 + as.getD (n - 1 - (i - 2) / 4) 0 else belowE as (n - 1 - (i - 2) / 4)

/-- The honest valuation. -/
def opsSigma (chain a : E) (as : List E) (n : ℕ) : Val := fun v ↦ opsVal chain a as n v.idx

section Holds

variable {chain a : E} {as : List E} {n : ℕ}

theorem opsVal_ne_end {i : ℕ} (h : i ≠ opsEnd n) : opsVal chain a as n i =
    if i = 0 then chain else if i = 1 then a else if i = 2 then 1 else
    if i = 3 then 1 else if i = 4 then as.getD (n - 1) 0 else if i = 5 then belowE as (n - 1) else
    if (i - 2) % 4 = 0 then 1 else if (i - 2) % 4 = 1 then as.getD (n - 1 - (i - 2) / 4) 0 else
    if (i - 2) % 4 = 2 then 1 + as.getD (n - 1 - (i - 2) / 4) 0 else belowE as (n - 1 - (i - 2) / 4) := by
  unfold opsVal; rw [ite_eq_right_of_eq_false _ _ (eq_false h)]

theorem opsEnd_ge (n : ℕ) : 3 ≤ opsEnd n := by unfold opsEnd; split <;> omega

theorem opsVal_blk {kk j : ℕ} (hk : 1 ≤ kk) (hkn : kk < n) (hj : j < 4) :
    opsVal chain a as n (4 * kk + 2 + j) = if j = 0 then 1 else if j = 1 then as.getD (n - 1 - kk) 0
      else if j = 2 then 1 + as.getD (n - 1 - kk) 0 else belowE as (n - 1 - kk) := by
  have he : 4 * kk + 2 + j ≠ opsEnd n := by unfold opsEnd; split <;> omega
  rw [opsVal_ne_end he]
  have h1 : (4 * kk + 2 + j - 2) / 4 = kk := by omega
  have h2 : (4 * kk + 2 + j - 2) % 4 = j := by omega
  have n' : ∀ m, 4 * kk + 2 + j ≠ m → (4 * kk + 2 + j = m) = False := fun m h ↦ eq_false h
  rw [ite_eq_right_of_eq_false _ _ (n' _ (by omega)), ite_eq_right_of_eq_false _ _ (n' _ (by omega)),
    ite_eq_right_of_eq_false _ _ (n' _ (by omega)), ite_eq_right_of_eq_false _ _ (n' _ (by omega)),
    ite_eq_right_of_eq_false _ _ (n' _ (by omega)), ite_eq_right_of_eq_false _ _ (n' _ (by omega)), h1, h2]

theorem opsVal_V {kk : ℕ} (hkn : kk < n) : opsVal chain a as n (opsV 0 kk) = belowE as (n - 1 - kk) := by
  unfold opsV
  rcases Nat.eq_zero_or_pos kk with h | h
  · subst h
    rw [opsVal_ne_end (by have := opsEnd_ge n; unfold opsEnd; split <;> omega)]
    rfl
  · rw [show 0 + 4 * kk + 5 = 4 * kk + 2 + 3 by omega, opsVal_blk h hkn (by norm_num)]; rfl

theorem opsVal_small {i : ℕ} (hn : 1 ≤ n) (hi : i < 6) :
    opsVal chain a as n i = [chain, a, 1, 1, as.getD (n - 1) 0, belowE as (n - 1)].getD i 0 := by
  rw [opsVal_ne_end (by unfold opsEnd; split <;> omega)]
  interval_cases i <;> rfl

theorem readsAt_get {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

/-- **The atoms hold** on a memory holding `as` at `a` and the suffix products at `chain`. -/
theorem opsAtoms_holds {rd : Reader} (ha : ReadsAt rd a as)
    (hc : ReadsAt rd chain ((List.range (n + 1)).map (belowE as))) (hl : as.length = n) :
    ∀ x ∈ opsAtoms n, x.Holds rd (opsSigma chain a as n) := by
  have sv : ∀ i, opsSigma chain a as n (.n i) = opsVal chain a as n i := fun _ ↦ rfl
  have hck : ∀ k ≤ n, LoadHolds rd chain k (belowE as k) := fun k hk ↦ by
    have := readsAt_get hc (k := k) (by simp; omega)
    rwa [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range] at this
  have hak : ∀ k < n, LoadHolds rd a k (as.getD k 0) := fun k hk ↦ readsAt_get ha (by omega)
  have hs0 : opsSigma chain a as n (.n 0) = chain := by
    rw [sv, opsVal_ne_end (by have := opsEnd_ge n; omega)]; rfl
  have hs1 : opsSigma chain a as n (.n 1) = a := by
    rw [sv, opsVal_ne_end (by have := opsEnd_ge n; omega)]; rfl
  have hs2 : opsSigma chain a as n (.n (0 + 2)) = 1 := by
    rw [sv, opsVal_ne_end (by have := opsEnd_ge n; omega)]; rfl
  have hbl : belowE as n = 1 := by rw [← hl, belowE_length]
  intro x hx
  unfold opsAtoms at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ((rfl | rfl) | hx) | rfl
  · simp only [Atom.Holds, hs2, word_one]
  · simp only [Atom.Holds, hs2, hs0]; rw [← hbl]; exact hck n le_rfl
  · obtain ⟨l, hl', hxl⟩ := List.mem_flatten.mp hx
    obtain ⟨kk, hkk, rfl⟩ := List.mem_map.mp hl'
    have hkk := List.mem_range.mp hkk
    have hn : 1 ≤ n := by omega
    unfold opsBlkA at hxl
    split at hxl
    · next h0 =>
      subst h0
      have v : ∀ i (hi : i < 6), opsSigma chain a as n (.n i) =
          [chain, a, 1, 1, as.getD (n - 1) 0, belowE as (n - 1)].getD i 0 := fun i hi ↦ by
        rw [sv, opsVal_small hn hi]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxl
      rcases hxl with rfl | rfl | rfl | rfl <;>
        simp only [Atom.Holds, Nat.zero_add, v _ (by norm_num : (0 : ℕ) < 6),
          v _ (by norm_num : (1 : ℕ) < 6), v _ (by norm_num : (3 : ℕ) < 6),
          v _ (by norm_num : (4 : ℕ) < 6), v _ (by norm_num : (5 : ℕ) < 6),
          List.getD_cons_zero, List.getD_cons_succ, word_one]
      · exact hak _ (by omega)
      · rw [belowE_eq_cons as _ (by omega), show n - 1 + 1 = n by omega, hbl, mul_one,
          List.getD_eq_getElem _ _ (by omega)]
      · exact hck _ (by omega)
    · next h0 =>
      have vb : ∀ j (hj : j < 4), opsSigma chain a as n (.n (0 + 4 * kk + 2 + j)) =
          opsVal chain a as n (4 * kk + 2 + j) := fun j _ ↦ by rw [sv, Nat.zero_add]
      have v2 : opsSigma chain a as n (.n (0 + 4 * kk + 2)) = 1 := by
        rw [show 0 + 4 * kk + 2 = 0 + 4 * kk + 2 + 0 from rfl, vb 0 (by norm_num),
          opsVal_blk (by omega) hkk (by norm_num)]; rfl
      have v3 : opsSigma chain a as n (.n (0 + 4 * kk + 3)) = as.getD (n - 1 - kk) 0 := by
        rw [show 0 + 4 * kk + 3 = 0 + 4 * kk + 2 + 1 by omega, vb 1 (by norm_num),
          opsVal_blk (by omega) hkk (by norm_num)]; rfl
      have v4 : opsSigma chain a as n (.n (0 + 4 * kk + 4)) = 1 + as.getD (n - 1 - kk) 0 := by
        rw [show 0 + 4 * kk + 4 = 0 + 4 * kk + 2 + 2 by omega, vb 2 (by norm_num),
          opsVal_blk (by omega) hkk (by norm_num)]; rfl
      have v5 : opsSigma chain a as n (.n (0 + 4 * kk + 5)) = belowE as (n - 1 - kk) := by
        rw [show 0 + 4 * kk + 5 = 0 + 4 * kk + 2 + 3 by omega, vb 3 (by norm_num),
          opsVal_blk (by omega) hkk (by norm_num)]; rfl
      have vp : opsSigma chain a as n (.n (opsV 0 (kk - 1))) = belowE as (n - 1 - (kk - 1)) := by
        rw [sv, opsVal_V (by omega)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxl
      rcases hxl with rfl | rfl | rfl | rfl | rfl <;>
        simp only [Atom.Holds, v2, v3, v4, v5, vp, hs0, hs1, word_one]
      · exact hak _ (by omega)
      · rw [belowE_eq_cons as (n - 1 - kk) (by omega), show n - 1 - kk + 1 = n - 1 - (kk - 1) by omega,
          List.getD_eq_getElem _ _ (by omega), mul_comm]
      · exact hck _ (by omega)
  · simp only [Atom.Holds, sv]
    unfold opsVal
    simp only [↓reduceIte, word_zero]

/-- **`one_plus_suffixes`' template completes.** -/
theorem ops_complete {kd : ℕ} (n : ℕ) {name : String} {f : Fn}
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = opsBody n) (chain a : E) (as : List E) (hl : as.length = n) :
    CallCompletes0 kd name [chain, a] [0]
      (fun rd ↦ ReadsAt rd a as ∧ ReadsAt rd chain ((List.range (n + 1)).map (belowE as)))
      PostQuiet := by
  have sv : ∀ i, opsSigma chain a as n (.n i) = opsVal chain a as n i := fun _ ↦ rfl
  refine callCompletes0_atoms (opsSigma chain a as n) hfind (by rw [hbody, opsBody_eq]) ?_ ?_
    (opsAtoms_quiet n) fun rd _ ⟨ha, hc⟩ ↦ opsAtoms_holds ha hc hl
  · rw [hparams]
    simp only [List.map_cons, List.map_nil, sv]
    rw [opsVal_ne_end (by have := opsEnd_ge n; omega), opsVal_ne_end (by have := opsEnd_ge n; omega)]
    rfl
  · simp only [List.map_cons, List.map_nil, sv]
    unfold opsVal
    simp only [↓reduceIte]

end Holds


/-! ## The specializations -/

/-- What `one_plus_suffixes__L{n}`'s completeness gives, its arguments and memory. -/
def SuffixesComplete (kd n : ℕ) (name : String) : Prop :=
  ∀ (chain a : E) (as : List E), as.length = n →
    CallCompletes0 kd name [chain, a] [0]
      (fun rd ↦ ReadsAt rd a as ∧ ReadsAt rd chain ((List.range (n + 1)).map (belowE as))) PostQuiet

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L0_complete (kd : ℕ) : SuffixesComplete kd 0 (opsNames.getD 0 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 0 (f := fn% «one_plus_suffixes__L0»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L0») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L1_complete (kd : ℕ) : SuffixesComplete kd 1 (opsNames.getD 1 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 1 (f := fn% «one_plus_suffixes__L1»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L1») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L2_complete (kd : ℕ) : SuffixesComplete kd 2 (opsNames.getD 2 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 2 (f := fn% «one_plus_suffixes__L2»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L2») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L3_complete (kd : ℕ) : SuffixesComplete kd 3 (opsNames.getD 3 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 3 (f := fn% «one_plus_suffixes__L3»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L3») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L4_complete (kd : ℕ) : SuffixesComplete kd 4 (opsNames.getD 4 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 4 (f := fn% «one_plus_suffixes__L4»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L4») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L5_complete (kd : ℕ) : SuffixesComplete kd 5 (opsNames.getD 5 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 5 (f := fn% «one_plus_suffixes__L5»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L5») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L6_complete (kd : ℕ) : SuffixesComplete kd 6 (opsNames.getD 6 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 6 (f := fn% «one_plus_suffixes__L6»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L7_complete (kd : ℕ) : SuffixesComplete kd 7 (opsNames.getD 7 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 7 (f := fn% «one_plus_suffixes__L7»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L8_complete (kd : ℕ) : SuffixesComplete kd 8 (opsNames.getD 8 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 8 (f := fn% «one_plus_suffixes__L8»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L9_complete (kd : ℕ) : SuffixesComplete kd 9 (opsNames.getD 9 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 9 (f := fn% «one_plus_suffixes__L9»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L10_complete (kd : ℕ) : SuffixesComplete kd 10 (opsNames.getD 10 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 10 (f := fn% «one_plus_suffixes__L10»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L10») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L11_complete (kd : ℕ) : SuffixesComplete kd 11 (opsNames.getD 11 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 11 (f := fn% «one_plus_suffixes__L11»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L11») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L12_complete (kd : ℕ) : SuffixesComplete kd 12 (opsNames.getD 12 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 12 (f := fn% «one_plus_suffixes__L12»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L12») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L13_complete (kd : ℕ) : SuffixesComplete kd 13 (opsNames.getD 13 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 13 (f := fn% «one_plus_suffixes__L13»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L13») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L14_complete (kd : ℕ) : SuffixesComplete kd 14 (opsNames.getD 14 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 14 (f := fn% «one_plus_suffixes__L14»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L14») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L15_complete (kd : ℕ) : SuffixesComplete kd 15 (opsNames.getD 15 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 15 (f := fn% «one_plus_suffixes__L15»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L15») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L16_complete (kd : ℕ) : SuffixesComplete kd 16 (opsNames.getD 16 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 16 (f := fn% «one_plus_suffixes__L16»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L16») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L17_complete (kd : ℕ) : SuffixesComplete kd 17 (opsNames.getD 17 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 17 (f := fn% «one_plus_suffixes__L17»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L17») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L18_complete (kd : ℕ) : SuffixesComplete kd 18 (opsNames.getD 18 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 18 (f := fn% «one_plus_suffixes__L18»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L18») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L19_complete (kd : ℕ) : SuffixesComplete kd 19 (opsNames.getD 19 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 19 (f := fn% «one_plus_suffixes__L19»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L20_complete (kd : ℕ) : SuffixesComplete kd 20 (opsNames.getD 20 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 20 (f := fn% «one_plus_suffixes__L20»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L21_complete (kd : ℕ) : SuffixesComplete kd 21 (opsNames.getD 21 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 21 (f := fn% «one_plus_suffixes__L21»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L22_complete (kd : ℕ) : SuffixesComplete kd 22 (opsNames.getD 22 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 22 (f := fn% «one_plus_suffixes__L22»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L23_complete (kd : ℕ) : SuffixesComplete kd 23 (opsNames.getD 23 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 23 (f := fn% «one_plus_suffixes__L23»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L24_complete (kd : ℕ) : SuffixesComplete kd 24 (opsNames.getD 24 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 24 (f := fn% «one_plus_suffixes__L24»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L25_complete (kd : ℕ) : SuffixesComplete kd 25 (opsNames.getD 25 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 25 (f := fn% «one_plus_suffixes__L25»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L25») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L26_complete (kd : ℕ) : SuffixesComplete kd 26 (opsNames.getD 26 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 26 (f := fn% «one_plus_suffixes__L26»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L26») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L27_complete (kd : ℕ) : SuffixesComplete kd 27 (opsNames.getD 27 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 27 (f := fn% «one_plus_suffixes__L27»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L27») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L28_complete (kd : ℕ) : SuffixesComplete kd 28 (opsNames.getD 28 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 28 (f := fn% «one_plus_suffixes__L28»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L28») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L29_complete (kd : ℕ) : SuffixesComplete kd 29 (opsNames.getD 29 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 29 (f := fn% «one_plus_suffixes__L29»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L29») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L30_complete (kd : ℕ) : SuffixesComplete kd 30 (opsNames.getD 30 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 30 (f := fn% «one_plus_suffixes__L30»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L30») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L31_complete (kd : ℕ) : SuffixesComplete kd 31 (opsNames.getD 31 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 31 (f := fn% «one_plus_suffixes__L31»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L31») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L32_complete (kd : ℕ) : SuffixesComplete kd 32 (opsNames.getD 32 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 32 (f := fn% «one_plus_suffixes__L32»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L32») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L33_complete (kd : ℕ) : SuffixesComplete kd 33 (opsNames.getD 33 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 33 (f := fn% «one_plus_suffixes__L33»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L33») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L34_complete (kd : ℕ) : SuffixesComplete kd 34 (opsNames.getD 34 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 34 (f := fn% «one_plus_suffixes__L34»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L34») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L35_complete (kd : ℕ) : SuffixesComplete kd 35 (opsNames.getD 35 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 35 (f := fn% «one_plus_suffixes__L35»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L35») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L36_complete (kd : ℕ) : SuffixesComplete kd 36 (opsNames.getD 36 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 36 (f := fn% «one_plus_suffixes__L36»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L36») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L37_complete (kd : ℕ) : SuffixesComplete kd 37 (opsNames.getD 37 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 37 (f := fn% «one_plus_suffixes__L37»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L37») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L38_complete (kd : ℕ) : SuffixesComplete kd 38 (opsNames.getD 38 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 38 (f := fn% «one_plus_suffixes__L38»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L38») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L39_complete (kd : ℕ) : SuffixesComplete kd 39 (opsNames.getD 39 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 39 (f := fn% «one_plus_suffixes__L39»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L39») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

set_option maxRecDepth 100000 in
theorem one_plus_suffixes_L40_complete (kd : ℕ) : SuffixesComplete kd 40 (opsNames.getD 40 "") :=
  fun chain a as hl ↦ ops_complete (kd := kd) 40 (f := fn% «one_plus_suffixes__L40»)
    (coreProgram_find?_at (j := idx% «one_plus_suffixes__L40») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) chain a as hl

/-- **Every `one_plus_suffixes__L{n}` completes**, `n ≤ 40`. -/
theorem one_plus_suffixes_complete (kd : ℕ) : ∀ n ≤ 40, SuffixesComplete kd n (opsNames.getD n "") := by
  intro n hn
  interval_cases n
  · exact one_plus_suffixes_L0_complete kd
  · exact one_plus_suffixes_L1_complete kd
  · exact one_plus_suffixes_L2_complete kd
  · exact one_plus_suffixes_L3_complete kd
  · exact one_plus_suffixes_L4_complete kd
  · exact one_plus_suffixes_L5_complete kd
  · exact one_plus_suffixes_L6_complete kd
  · exact one_plus_suffixes_L7_complete kd
  · exact one_plus_suffixes_L8_complete kd
  · exact one_plus_suffixes_L9_complete kd
  · exact one_plus_suffixes_L10_complete kd
  · exact one_plus_suffixes_L11_complete kd
  · exact one_plus_suffixes_L12_complete kd
  · exact one_plus_suffixes_L13_complete kd
  · exact one_plus_suffixes_L14_complete kd
  · exact one_plus_suffixes_L15_complete kd
  · exact one_plus_suffixes_L16_complete kd
  · exact one_plus_suffixes_L17_complete kd
  · exact one_plus_suffixes_L18_complete kd
  · exact one_plus_suffixes_L19_complete kd
  · exact one_plus_suffixes_L20_complete kd
  · exact one_plus_suffixes_L21_complete kd
  · exact one_plus_suffixes_L22_complete kd
  · exact one_plus_suffixes_L23_complete kd
  · exact one_plus_suffixes_L24_complete kd
  · exact one_plus_suffixes_L25_complete kd
  · exact one_plus_suffixes_L26_complete kd
  · exact one_plus_suffixes_L27_complete kd
  · exact one_plus_suffixes_L28_complete kd
  · exact one_plus_suffixes_L29_complete kd
  · exact one_plus_suffixes_L30_complete kd
  · exact one_plus_suffixes_L31_complete kd
  · exact one_plus_suffixes_L32_complete kd
  · exact one_plus_suffixes_L33_complete kd
  · exact one_plus_suffixes_L34_complete kd
  · exact one_plus_suffixes_L35_complete kd
  · exact one_plus_suffixes_L36_complete kd
  · exact one_plus_suffixes_L37_complete kd
  · exact one_plus_suffixes_L38_complete kd
  · exact one_plus_suffixes_L39_complete kd
  · exact one_plus_suffixes_L40_complete kd

end
end LeanVM.Guest.B1.VsC
