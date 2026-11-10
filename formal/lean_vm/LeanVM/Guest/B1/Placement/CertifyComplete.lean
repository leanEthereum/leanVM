/-
  LeanVM.Guest.B1.Placement.CertifyComplete

  `certify_placement`, completely: on a memory holding the base, the squares table and the rank
  keys, and its five buffers holding the groups' keys, sizes, `stackOffsets`'s group order, the
  groups' bases and the columns' `g^offset`, the honest valuation satisfies every statement, with
  the stack's total and the offsets' buffer as returns.
-/

module

public import LeanVM.Guest.B1.Placement.Certify
public import LeanVM.Guest.B1.Placement.Kappas
public import LeanVM.Guest.B1.Selectors.LayoutBasic

/-!
# `certify_placement`, completely (TRIAGE G #67)

The inputs are the runs `cpLin`: `kappa_base = [1, g^log_mem, g^τ_0, …, g^τ_5]` at `ekb`, the
squares table at `esq` and the rank keys at `esq + 178` (`rankKeysList`). The buffers (`cpOwn`),
at any bases `e10`, `e11`, `e136`, `e137`, `e293` (named by the values holding them): the groups'
keys `g^(κ·247)·INV_GEN^c₀` (`cpKey`), their sizes `g^(#columns·2^κ)` (`cpSize`), the group
order (`cpGOrd`, `stackOffsets`'s order of the groups: descending `κ`, ties by ascending group,
the honest `col_group_order` witness), each group's base `g^(sizes before it)` (`cpGP`) and the
columns' `g^offset`.

The honest valuation `cpσ` is written out value by value (`cpF`): the base's words, each group's
values (`cpGrpV`: its `g^κ`, range check, rank key, key, chain of its size), rank `0`
(`cpRank0V`), ranks `1 .. 8` (`cpRankV`: the group, its range check, its key, the key step `e`
to the previous rank and its range check, the base, the size and the running total) and each
group's columns (`cpColV`). The range checks read the memory at `g^a`, `a ≤ 8397`: the memory is
defined below `2^14` (`LowDefB 14`).

The columns' offsets are `stackOffsets`'s (`cp_offsets`), by `tb_group_stack_cert` on a memory
that holds the group-wise offsets (`cpOffRd`).

`cp_body_holds`: the relation holds with the returns `[g^stackTotal, off]`; `cp_ctx`: the offsets'
buffer satisfies `PCtx`. Hypotheses beyond the precondition of `certify_placement_Spec`:
`τ_5 ≤ 27` (every committed column's `κ = τ_5 + 6` of `q_keccak` below `SIZE_BITS = 34`, which
the guest range-checks; the deployed limits give `τ_5 ≤ 22`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The memory is defined below `2^k`. -/
def LowDefB (k : ℕ) (rd : Reader) : Prop := ∀ i < 2 ^ k, (rd (addressOfIndex i)).isSome

/-- The word at `g^a`, or `0`. -/
noncomputable def rdv (rd : Reader) (a : ℕ) : E := (rd (addressOfIndex a)).getD 0

theorem tb_ite_neg {c : Prop} [Decidable c] (h : ¬c) {α : Type} {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem tb_ite_pos {c : Prop} [Decidable c] (h : c) {α : Type} {a b : α} :
    (if c then a else b) = a := by simp [h]

/-! ## The honest data -/

section
variable (lm : ℕ) (hs : List ℕ)

/-- The committed columns' sizes. -/
def cpKs : List ℕ := committedKappas (columnKappas lm guestLogBytecode hs)

/-- The base's exponents `[0, log_mem, τ_0, …, τ_5]`. -/
def cpEb (i : ℕ) : ℕ := (0 :: lm :: hs).getD i 0

/-- Column `c`'s size, from its source and adjustment. -/
def cpKc (c : ℕ) : ℕ := cpEb lm hs (colKappaSrc c) + colKappaAdj c

/-- Group `gi`'s size, its first column's. -/
def cpKg (gi : ℕ) : ℕ := cpKc lm hs (cpC0 gi)

/-- `stackOffsets`'s order of the groups: larger first, ties by ascending group. -/
def cpGOrd : List ℕ := (List.range 9).mergeSort (stackLe (cpKg lm hs))

/-- Rank `r`'s group. -/
def cpPi (r : ℕ) : ℕ := (cpGOrd lm hs).getD r 0

/-- Group `gi`'s rank. -/
def cpRho (gi : ℕ) : ℕ := (cpGOrd lm hs).idxOf gi

/-- The sizes of the groups of ranks below `r`. -/
def cpGP (r : ℕ) : ℕ := tbGroupPrefix cpC0 (cpKc lm hs) (cpPi lm hs) r

/-- Group `gi`'s rank key `g^(κ·247)·INV_GEN^c₀`. -/
noncomputable def cpKey (gi : ℕ) : E :=
  gen ^ (cpKg lm hs gi * rankStride) * word (cpInvWords.getD gi 0) 0

/-- Group `gi`'s size, `#columns·2^κ`. -/
def cpSize (gi : ℕ) : ℕ := cpLen gi * 2 ^ cpKg lm hs gi

/-- The key step from rank `r - 1` to rank `r`: `κ_prev·247 + c₀ = κ·247 + c₀_prev + e + 1`. -/
def cpE (r : ℕ) : ℕ :=
  cpKg lm hs (cpPi lm hs (r - 1)) * rankStride + cpC0 (cpPi lm hs r) -
    cpKg lm hs (cpPi lm hs r) * rankStride - cpC0 (cpPi lm hs (r - 1)) - 1

/-- The inputs: the base, the squares table and the rank keys. -/
def cpLin (ekb esq : ℕ) : TLay :=
  [(ekb, 1 :: gen ^ lm :: hs.map (gen ^ ·)), (esq, gSquaresList), (esq + 178, rankKeysList)]

/-- The buffers: the groups' keys, sizes, order and bases, and `g^offset` per column. -/
noncomputable def cpOwn (e10 e11 e136 e137 e293 : ℕ) : TLay :=
  [(e10, (List.range 9).map (cpKey lm hs)), (e11, (List.range 9).map fun g ↦ gen ^ cpSize lm hs g),
    (e136, (cpGOrd lm hs).map (gen ^ ·)),
    (e137, (List.range 9).map fun g ↦ gen ^ cpGP lm hs (cpRho lm hs g)),
    (e293, (stackOffsets (cpKs lm hs)).1.map (gen ^ ·))]

end

/-! ## The value map -/

/-- Group `gi`'s first value, then `136`. -/
def cpBx (gi : ℕ) : ℕ := [12, 22, 34, 46, 61, 76, 90, 105, 120, 136].getD gi 0

/-- The group whose values hold `v`. -/
def cpGOf (v : ℕ) : ℕ := ((List.range 8).filter fun g ↦ cpBx (g + 1) ≤ v).length

/-- The group whose columns' values hold `v`. -/
def cpCOf (v : ℕ) : ℕ := ((List.range 8).filter fun g ↦ cpD (g + 1) ≤ v).length

/-- The group of column `c`. -/
def cpCGrp (c : ℕ) : ℕ := ((List.range 8).filter fun g ↦ cpC0 (g + 1) ≤ c).length

theorem cpBx_eq : ∀ gi < 9, cpBx gi = cpB gi := by decide +kernel

theorem cpGOf_eq : ∀ gi < 9, ∀ v < 136, cpB gi ≤ v → v < cpBx (gi + 1) → cpGOf v = gi := by
  decide +kernel

theorem cpCOf_eq : ∀ gi < 9, ∀ v < 406, cpD gi ≤ v → v < cpD (gi + 1) → cpCOf v = gi := by
  decide +kernel

theorem cpCGrp_eq : ∀ gi < 9, ∀ c < 94, cpC0 gi ≤ c → c < cpC0 (gi + 1) → cpCGrp c = gi := by
  decide +kernel

/-- The groups' values lie in `12 .. 135`, in order. -/
theorem cp_grp_geom : ∀ gi < 9, 12 ≤ cpB gi ∧ cpZ gi + 1 + (cpCh gi).length < cpBx (gi + 1) ∧
    cpBx (gi + 1) ≤ 136 := by decide +kernel

/-- The columns' values lie in `294 .. 405`, in order. -/
theorem cp_col_geom : ∀ gi < 9, 294 ≤ cpD gi ∧ cpD (gi + 1) = cpD gi + 2 + cpLen gi ∧
    cpD (gi + 1) ≤ 406 := by decide +kernel

theorem cpC0_lt99 : ∀ gi < 9, cpC0 gi ≤ 66 := by decide +kernel

theorem cpC0_strict : ∀ a < 9, ∀ b < 9, a < b → cpC0 a < cpC0 b := by decide +kernel

theorem cpLen_pos : ∀ gi < 9, 1 ≤ cpLen gi := by decide +kernel

/-! ## The honest valuation -/

section
variable (lm : ℕ) (hs : List ℕ) (ekb esq e10 e11 e136 e137 e293 : ℕ) (rd : Reader)

/-- Group `gi`'s value `cpQ gi + t`, below its `cpZ gi`. -/
noncomputable def cpGrpQ (gi t : ℕ) : E :=
  match t with
  | 0 => w33
  | 1 => gen ^ (33 - cpKg lm hs gi)
  | 2 => rdv rd (cpKg lm hs gi)
  | 3 => rdv rd (33 - cpKg lm hs gi)
  | 4 => ofK (addressOfIndex esq) * gen ^ cpKg lm hs gi
  | 5 => gen ^ (cpKg lm hs gi * rankStride)
  | 6 => word (cpInvWords.getD gi 0) 0
  | _ => cpKey lm hs gi

/-- Group `gi`'s value `v`. -/
noncomputable def cpGrpV (gi v : ℕ) : E :=
  if v < cpQ gi then (if v = cpB gi then word (2 ^ cpAdj gi) 0 else gen ^ cpKg lm hs gi)
  else if v < cpZ gi then cpGrpQ lm hs esq rd gi (v - cpQ gi)
  else if v = cpZ gi then ofK (addressOfIndex esq) * gen ^ cpKg lm hs gi
  else (gen ^ 2 ^ cpKg lm hs gi) ^ cpChainExp ((cpCh gi).take (v - cpZ gi - 1))

/-- Rank `0`, values `138 .. 148`. -/
noncomputable def cpRank0V (j : ℕ) : E :=
  let p := cpPi lm hs 0
  match j with
  | 0 => gen ^ p
  | 1 => w8
  | 2 => gen ^ (8 - p)
  | 3 => rdv rd p
  | 4 => rdv rd (8 - p)
  | 5 => ofK (addressOfIndex e10) * gen ^ p
  | 6 => cpKey lm hs p
  | 7 => word 1 0
  | 8 => ofK (addressOfIndex e137) * gen ^ p
  | 9 => ofK (addressOfIndex e11) * gen ^ p
  | _ => gen ^ cpGP lm hs 1

/-- Rank `r ≥ 1`, value `131 + 18·r + j`. -/
noncomputable def cpRankV (r j : ℕ) : E :=
  let p := cpPi lm hs r
  let e := cpE lm hs r
  match j with
  | 0 => gen ^ p
  | 1 => w8
  | 2 => gen ^ (8 - p)
  | 3 => rdv rd p
  | 4 => rdv rd (8 - p)
  | 5 => ofK (addressOfIndex e10) * gen ^ p
  | 6 => cpKey lm hs p
  | 7 => wRankBound
  | 8 => gen ^ (e + 1)
  | 9 => wInvGen
  | 10 => gen ^ e
  | 11 => gen ^ (8397 - e)
  | 12 => rdv rd e
  | 13 => rdv rd (8397 - e)
  | 14 => ofK (addressOfIndex e137) * gen ^ p
  | 15 => ofK (addressOfIndex e11) * gen ^ p
  | 16 => gen ^ cpSize lm hs p
  | _ => gen ^ cpGP lm hs (r + 1)

/-- Group `gi`'s columns' value `v`: the step's pointer, the step, and the offsets. -/
noncomputable def cpColV (gi v : ℕ) : E :=
  if v = cpD gi then ofK (addressOfIndex esq) * gen ^ cpEb lm hs (cpSrc gi)
  else if v = cpD gi + 1 then gen ^ 2 ^ cpKg lm hs gi
  else gen ^ (cpGP lm hs (cpRho lm hs gi) + (v - cpD gi - 2) * 2 ^ cpKg lm hs gi)

/-- The honest words, by value number. -/
noncomputable def cpF (v : ℕ) : E :=
  if v = 0 then ofK (addressOfIndex ekb)
  else if v = 1 then ofK (addressOfIndex esq)
  else if v < 10 then gen ^ cpEb lm hs (v - 2)
  else if v = 10 then ofK (addressOfIndex e10)
  else if v = 11 then ofK (addressOfIndex e11)
  else if v < 136 then cpGrpV lm hs esq rd (cpGOf v) v
  else if v = 136 then ofK (addressOfIndex e136)
  else if v = 137 then ofK (addressOfIndex e137)
  else if v < 149 then cpRank0V lm hs e10 e11 e137 rd (v - 138)
  else if v < 293 then cpRankV lm hs e10 e11 e137 rd ((v - 131) / 18) ((v - 131) % 18)
  else if v = 293 then ofK (addressOfIndex e293)
  else if v < 406 then cpColV lm hs esq (cpCOf v) v
  else if v = 406 then gen ^ cpGP lm hs 9
  else ofK (addressOfIndex e293)

/-- **The honest valuation.** -/
noncomputable def cpσ : Val := fun v => cpF lm hs ekb esq e10 e11 e136 e137 e293 rd v.idx

theorem cpσ_kb {i : ℕ} (hi : i < 8) :
    cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n (2 + i)) = gen ^ cpEb lm hs i := by
  show cpF lm hs ekb esq e10 e11 e136 e137 e293 rd (2 + i) = _
  unfold cpF
  rw [tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_pos (by omega), Nat.add_sub_cancel_left]

theorem cpσ_grp {gi v : ℕ} (hgi : gi < 9) (h1 : cpB gi ≤ v) (h2 : v < cpBx (gi + 1)) :
    cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n v) = cpGrpV lm hs esq rd gi v := by
  show cpF lm hs ekb esq e10 e11 e136 e137 e293 rd v = _
  obtain ⟨g1, -, g3⟩ := cp_grp_geom gi hgi
  unfold cpF
  rw [tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
    tb_ite_neg (by omega), tb_ite_pos (by omega), cpGOf_eq gi hgi v (by omega) h1 h2]

theorem cpσ_rank0 {j : ℕ} (hj : j < 11) :
    cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n (138 + j)) =
      cpRank0V lm hs e10 e11 e137 rd j := by
  show cpF lm hs ekb esq e10 e11 e136 e137 e293 rd (140 + j) = _
  unfold cpF
  rw [tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
    tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
    tb_ite_pos (by omega), Nat.add_sub_cancel_left]

theorem cpσ_rank {r j : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ 8) (hj : j < 18) :
    cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n (131 + 18 * r + j)) =
      cpRankV lm hs e10 e11 e137 rd r j := by
  show cpF lm hs ekb esq e10 e11 e136 e137 e293 rd (133 + 18 * r + j) = _
  have e1 : (131 + 18 * r + j - 131) / 18 = r := by omega
  have e2 : (131 + 18 * r + j - 131) % 18 = j := by omega
  unfold cpF
  rw [tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
    tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
    tb_ite_neg (by omega), tb_ite_pos (by omega), e1, e2]

theorem cpσ_col {gi v : ℕ} (hgi : gi < 9) (h1 : cpD gi ≤ v) (h2 : v < cpD (gi + 1)) :
    cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n v) = cpColV lm hs esq gi v := by
  show cpF lm hs ekb esq e10 e11 e136 e137 e293 rd v = _
  obtain ⟨g1, -, g3⟩ := cp_col_geom gi hgi
  unfold cpF
  rw [tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
    tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega),
    tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_pos (by omega),
    cpCOf_eq gi hgi v (by omega) h1 h2]

/-- Group `gi`'s pointers into the rank keys and the squares. -/
theorem cpσ_grp_ptrs {gi : ℕ} (hgi : gi < 9) :
    cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n (cpQ gi + 4)) =
        ofK (addressOfIndex esq) * gen ^ cpKg lm hs gi ∧
      cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n (cpZ gi)) =
        ofK (addressOfIndex esq) * gen ^ cpKg lm hs gi := by
  obtain ⟨g1, g2, g3⟩ := cp_grp_geom gi hgi
  have hQ : cpB gi ≤ cpQ gi := by unfold cpQ; split_ifs <;> omega
  have hZ : cpQ gi + 6 ≤ cpZ gi := by unfold cpZ; split_ifs <;> omega
  constructor
  · rw [cpσ_grp lm hs ekb esq e10 e11 e136 e137 e293 rd hgi (by omega) (by omega), cpGrpV,
      tb_ite_neg (by omega), tb_ite_pos (by omega), Nat.add_sub_cancel_left]
    rfl
  · rw [cpσ_grp lm hs ekb esq e10 e11 e136 e137 e293 rd hgi (by omega) (by omega), cpGrpV,
      tb_ite_neg (by omega), tb_ite_neg (by omega), tb_ite_pos rfl]

end

/-! ## The honest data's facts -/

section
variable {lm : ℕ} {hs : List ℕ}

theorem cpKs_length : (cpKs lm hs).length = 94 :=
  committedKappas_length _ (columnKappas_length _ _ _)

theorem cpKs_eq (hl : hs.length = 6) : cpKs lm hs = (List.range 94).map (cpKc lm hs) :=
  committedKappas_columnKappas lm hs hl

theorem cpKs_getD (hl : hs.length = 6) {c : ℕ} (hc : c < 94) :
    (cpKs lm hs).getD c 0 = cpKc lm hs c := by
  rw [cpKs_eq hl, List.getD_eq_getElem _ _ (by simpa using hc)]
  simp

theorem cp_base_lt (hl : hs.length = 6) (hlm : lm ≤ 32) (hhs : ∀ h ∈ hs, h < 29) {s : ℕ}
    (hs8 : s < 8) : cpEb lm hs s < 33 := by
  unfold cpEb
  rcases Nat.lt_or_ge s 2 with h2 | h2
  · interval_cases s
    · simp
    · simp; omega
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    simp only [List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by omega)]
    have := hhs _ (List.getElem_mem (by omega : t < hs.length))
    omega

theorem colKappaSrc_lt {c : ℕ} : colKappaSrc c < 8 := by unfold colKappaSrc; split_ifs <;> omega

theorem cpKc_lt (hl : hs.length = 6) (hlm : lm ≤ 32) (hhs : ∀ h ∈ hs, h < 29)
    (h5 : hs.getD 5 0 ≤ 27) (c : ℕ) : cpKc lm hs c < 34 := by
  unfold cpKc
  have hb := cp_base_lt hl hlm hhs (colKappaSrc_lt (c := c))
  by_cases h45 : c = 4 ∨ c = 5
  · rcases h45 with rfl | rfl
    · simp [colKappaSrc, colKappaAdj, cpEb]
    · show (0 :: lm :: hs).getD 7 0 + 6 < 34
      simp only [List.getD_cons_succ]
      omega
  · have : colKappaAdj c = 0 := by unfold colKappaAdj; split_ifs <;> omega
    omega

theorem cpGOrd_perm : (cpGOrd lm hs).Perm (List.range 9) := List.mergeSort_perm _ _

theorem cpGOrd_length : (cpGOrd lm hs).length = 9 := by
  rw [(cpGOrd_perm).length_eq, List.length_range]

theorem cpGOrd_nodup : (cpGOrd lm hs).Nodup := (cpGOrd_perm).nodup_iff.mpr List.nodup_range

theorem cpPi_lt {r : ℕ} (hr : r < 9) : cpPi lm hs r < 9 := by
  have hm : (cpGOrd lm hs).getD r 0 ∈ cpGOrd lm hs := by
    rw [List.getD_eq_getElem _ _ (by rw [cpGOrd_length]; exact hr)]; exact List.getElem_mem _
  exact List.mem_range.mp ((cpGOrd_perm).subset hm)

theorem cpGOrd_sorted :
    (cpGOrd lm hs).Pairwise fun a b => stackLe (cpKg lm hs) a b = true := by
  unfold cpGOrd
  apply List.pairwise_mergeSort
  · intro a b c; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · intro a b; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **Adjacent ranks**: sizes do not increase, ties ascend by group. -/
theorem cpPi_adj {r : ℕ} (hr : r + 1 < 9) :
    cpKg lm hs (cpPi lm hs (r + 1)) ≤ cpKg lm hs (cpPi lm hs r) ∧
      (cpKg lm hs (cpPi lm hs (r + 1)) = cpKg lm hs (cpPi lm hs r) →
        cpPi lm hs r < cpPi lm hs (r + 1)) := by
  have hlen := cpGOrd_length (lm := lm) (hs := hs)
  have hp := List.pairwise_iff_getElem.mp (cpGOrd_sorted (lm := lm) (hs := hs)) r (r + 1)
    (by omega) (by omega) (by omega)
  have hne : (cpGOrd lm hs)[r]'(by omega) ≠ (cpGOrd lm hs)[r + 1]'(by omega) := fun he =>
    absurd ((List.Nodup.getElem_inj_iff (cpGOrd_nodup (lm := lm) (hs := hs))).mp he) (by omega)
  simp only [cpPi, List.getD_eq_getElem _ _ (show r < (cpGOrd lm hs).length by omega),
    List.getD_eq_getElem _ _ (show r + 1 < (cpGOrd lm hs).length by omega)]
  simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  omega

theorem cpRho_pi {r : ℕ} (hr : r < 9) : cpRho lm hs (cpPi lm hs r) = r := by
  have hlen := cpGOrd_length (lm := lm) (hs := hs)
  have hmem : (cpGOrd lm hs)[r]'(by omega) ∈ cpGOrd lm hs := List.getElem_mem _
  have hi : (cpGOrd lm hs).idxOf ((cpGOrd lm hs)[r]'(by omega)) < (cpGOrd lm hs).length :=
    List.idxOf_lt_length_of_mem hmem
  have hg := List.getElem_idxOf hi
  rw [cpRho, cpPi, List.getD_eq_getElem _ _ (by omega)]
  exact (List.Nodup.getElem_inj_iff (cpGOrd_nodup (lm := lm) (hs := hs))).mp hg

theorem cpGP_zero : cpGP lm hs 0 = 0 := by simp [cpGP, tbGroupPrefix]

theorem cpGP_succ (r : ℕ) : cpGP lm hs (r + 1) = cpGP lm hs r + cpSize lm hs (cpPi lm hs r) := by
  rw [cpGP, tb_groupPrefix_succ]; rfl

/-- **The key step**: between adjacent ranks it is a natural below `8398`. -/
theorem cpE_spec (hl : hs.length = 6) (hlm : lm ≤ 32) (hhs : ∀ h ∈ hs, h < 29)
    (h5 : hs.getD 5 0 ≤ 27) {r : ℕ} (hr : r + 1 < 9) :
    cpE lm hs (r + 1) ≤ 8397 ∧
      cpKg lm hs (cpPi lm hs r) * rankStride + cpC0 (cpPi lm hs (r + 1)) =
        cpE lm hs (r + 1) + 1 + cpKg lm hs (cpPi lm hs (r + 1)) * rankStride +
          cpC0 (cpPi lm hs r) := by
  have ha := cpPi_lt (lm := lm) (hs := hs) (r := r) (by omega)
  have hb := cpPi_lt (lm := lm) (hs := hs) (r := r + 1) hr
  obtain ⟨hle, htie⟩ := cpPi_adj (lm := lm) (hs := hs) hr
  have k1 : cpKg lm hs (cpPi lm hs r) < 34 := cpKc_lt hl hlm hhs h5 _
  have c1 := cpC0_lt99 _ ha
  have c2 := cpC0_lt99 _ hb
  have hs' : cpC0 (cpPi lm hs r) < cpC0 (cpPi lm hs (r + 1)) ∨
      cpKg lm hs (cpPi lm hs (r + 1)) < cpKg lm hs (cpPi lm hs r) := by
    rcases Nat.lt_or_ge (cpKg lm hs (cpPi lm hs (r + 1))) (cpKg lm hs (cpPi lm hs r)) with h | h
    · exact Or.inr h
    · exact Or.inl (cpC0_strict _ ha _ hb (htie (by omega)))
  unfold cpE
  rw [Nat.add_sub_cancel]
  simp only [show rankStride = 247 from rfl]
  generalize cpKg lm hs (cpPi lm hs r) = A at *
  generalize cpKg lm hs (cpPi lm hs (r + 1)) = B at *
  generalize cpC0 (cpPi lm hs r) = a at *
  generalize cpC0 (cpPi lm hs (r + 1)) = b at *
  rcases hs' with h | h
  · constructor <;> omega
  · have : (B + 1) * 247 ≤ A * 247 := Nat.mul_le_mul_right _ h
    constructor <;> omega

/-- **The keys of adjacent ranks**: `key_prev = g^(e+1)·key`. -/
theorem cpKey_step (hl : hs.length = 6) (hlm : lm ≤ 32) (hhs : ∀ h ∈ hs, h < 29)
    (h5 : hs.getD 5 0 ≤ 27) {r : ℕ} (hr : r + 1 < 9) :
    cpKey lm hs (cpPi lm hs r) = gen ^ (cpE lm hs (r + 1) + 1) * cpKey lm hs (cpPi lm hs (r + 1)) := by
  obtain ⟨-, hE⟩ := cpE_spec hl hlm hhs h5 hr
  have h1 := cpInvWord_mul (cpPi_lt (lm := lm) (hs := hs) (r := r) (by omega))
  have h2 := cpInvWord_mul (cpPi_lt (lm := lm) (hs := hs) (r := r + 1) hr)
  unfold cpKey
  set A := cpKg lm hs (cpPi lm hs r) * rankStride
  set B := cpKg lm hs (cpPi lm hs (r + 1)) * rankStride
  set a := cpC0 (cpPi lm hs r)
  set b := cpC0 (cpPi lm hs (r + 1))
  set Wp := word (cpInvWords.getD (cpPi lm hs r) 0) 0
  set W := word (cpInvWords.getD (cpPi lm hs (r + 1)) 0) 0 0
  set e := cpE lm hs (r + 1)
  calc gen ^ A * Wp = gen ^ A * Wp * (W * gen ^ b) := by rw [h2, mul_one]
    _ = gen ^ (A + b) * W * Wp := by ring
    _ = gen ^ (e + 1 + B + a) * W * Wp := by rw [hE]
    _ = gen ^ (e + 1) * (gen ^ B * W) * (Wp * gen ^ a) := by ring
    _ = gen ^ (e + 1) * (gen ^ B * W) := by rw [h1, mul_one]

end

/-! ## The columns' offsets -/

/-- A memory holding `g^Q c` at column `c < 94` from `g^0`. -/
noncomputable def cpOffRd (Q : ℕ → ℕ) : Reader := fun x ↦
  if h : ∃ c, c < 94 ∧ addressOfIndex c = x then some (gen ^ Q (Classical.choose h)) else none

theorem cpOffRd_load (Q : ℕ → ℕ) {c : ℕ} (hc : c < 94) :
    LoadHolds (cpOffRd Q) (ofK (addressOfIndex 0)) c (gen ^ Q c) := by
  refine ⟨tb_isInK_ofK _, ?_⟩
  rw [tb_addr_ofK, Nat.zero_add]
  have h : ∃ c', c' < 94 ∧ addressOfIndex c' = addressOfIndex c := ⟨c, hc, rfl⟩
  have he : ∀ h' : ∃ c', c' < 94 ∧ addressOfIndex c' = addressOfIndex c,
      Classical.choose h' = c := fun h' ↦ by
    have hs := Classical.choose_spec h'
    exact gpow_injOn (show Classical.choose h' ∈ Set.Iio (2 ^ 64 - 1) by
      simp only [Set.mem_Iio]; omega) (show c ∈ Set.Iio (2 ^ 64 - 1) by
      simp only [Set.mem_Iio]; omega) hs.2
  simp only [cpOffRd, h, ↓reduceDIte, he]

section
variable {lm : ℕ} {hs : List ℕ}

/-- **The columns' offsets are `stackOffsets`'s** along the honest group order, and the groups'
sizes sum to the stack's total. -/
theorem cp_offsets (hl : hs.length = 6) :
    (∀ gi < 9, ∀ j < cpLen gi, gen ^ (stackOffsets (cpKs lm hs)).1.getD (cpC0 gi + j) 0 =
      gen ^ (cpGP lm hs (cpRho lm hs gi) + j * 2 ^ cpKg lm hs gi)) ∧
      cpGP lm hs 9 = stackTotal (columnKappas lm guestLogBytecode hs) := by
  set Q : ℕ → ℕ := fun c ↦ cpGP lm hs (cpRho lm hs (cpCGrp c)) +
    (c - cpC0 (cpCGrp c)) * 2 ^ cpKg lm hs (cpCGrp c) with hQ
  have hQg : ∀ gi < 9, ∀ j < cpLen gi,
      Q (cpC0 gi + j) = cpGP lm hs (cpRho lm hs gi) + j * 2 ^ cpKg lm hs gi := by
    intro gi hgi j hj
    have := cpC0_mono gi hgi
    have h99 := cpC0_le gi hgi
    rw [hQ]
    simp only
    rw [cpCGrp_eq gi hgi _ (by unfold cpLen at hj; omega) (by omega) (by unfold cpLen at hj; omega),
      Nat.add_sub_cancel_left]
  have hconst : ∀ g < 9, ∀ c, cpC0 g ≤ c → c < cpC0 (g + 1) → cpKc lm hs c = cpKc lm hs (cpC0 g) :=
    fun g hg c hc1 hc2 ↦ by
      obtain ⟨e1, e2⟩ := cp_group_const g hg c (by have := cpC0_le g hg; omega) hc1 hc2
      simp only [cpKc, e1, e2, cpSrc, cpAdj]
  have hoff : ∀ r < 9, ∀ i, cpC0 (cpPi lm hs r) + i < cpC0 (cpPi lm hs r + 1) →
      LoadHolds (cpOffRd Q) (ofK (addressOfIndex 0)) (cpC0 (cpPi lm hs r) + i)
        (gen ^ (tbGroupPrefix cpC0 (cpKc lm hs) (cpPi lm hs) r +
          i * 2 ^ cpKc lm hs (cpC0 (cpPi lm hs r)))) := fun r hr i hi ↦ by
    have hg := cpPi_lt (lm := lm) (hs := hs) hr
    have h := cpOffRd_load Q (c := cpC0 (cpPi lm hs r) + i) (by have := cpC0_le _ hg; omega)
    rw [hQg _ hg i (by unfold cpLen; omega), cpRho_pi hr] at h
    exact h
  obtain ⟨hoffs, htot⟩ := tb_group_stack_cert (rd := cpOffRd Q) (off := ofK (addressOfIndex 0))
    (m := 9) cpC0 (cpKc lm hs) (cpPi lm hs) cpC0_zero cpC0_mono hconst (fun r hr ↦ cpPi_lt hr)
    (fun r hr ↦ cpPi_adj hr) hoff
  rw [cpC0_nine] at hoffs htot
  refine ⟨fun gi hgi j hj ↦ ?_, ?_⟩
  · have hc : cpC0 gi + j < 94 := by
      have := cpC0_le gi hgi; unfold cpLen at hj; omega
    have h1 := hoffs _ hc
    rw [← cpKs_eq hl] at h1
    rw [tb_loadHolds_unique h1 (cpOffRd_load Q hc), hQg gi hgi j hj]
  · rw [stackTotal, ← cpKs, cpKs_eq hl, List.map_map]
    exact htot

end

/-! ## Reads -/

theorem ldef_load {k : ℕ} {rd : Reader} (hlow : LowDefB k rd) {a : ℕ} (ha : a < 2 ^ k) :
    LoadHolds rd (gen ^ a) 0 (rdv rd a) := by
  rw [gen_pow_eq_ofK]
  refine ⟨tb_isInK_ofK _, ?_⟩
  rw [tb_addr_ofK, Nat.add_zero]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hlow a ha)
  rw [rdv, hv]; rfl

/-- **A range check of `g^a` against `g^K` passes**, on a memory defined below `2^14`. -/
theorem rc_ok {rd : Reader} (hlow : LowDefB 14 rd) {a K : ℕ} (ha : a ≤ K) (hK : K < 2 ^ 14) :
    LoadHolds rd (gen ^ a) 0 (rdv rd a) ∧ gen ^ K = gen ^ a * gen ^ (K - a) ∧
      LoadHolds rd (gen ^ (K - a)) 0 (rdv rd (K - a)) :=
  ⟨ldef_load hlow (by omega), by rw [← pow_add, Nat.add_sub_cancel' ha], ldef_load hlow (by omega)⟩

theorem w8_eq : w8 = gen ^ 8 := by rw [w8, word_g8, gen_pow_eq_ofK]

theorem w33_eq : w33 = gen ^ 33 := by rw [w33, word_g33, gen_pow_eq_ofK]

theorem wRankBound_eq : wRankBound = gen ^ 8397 := by
  rw [wRankBound, word_g8397, gen_pow_eq_ofK]

theorem isInK_gen_pow (a : ℕ) : IsInK (gen ^ a) := by rw [gen_pow_eq_ofK]; exact tb_isInK_ofK _

theorem tb_load_ofK_add {rd : Reader} {a b k : ℕ} {w : E} :
    LoadHolds rd (ofK (addressOfIndex (a + b))) k w ↔
      LoadHolds rd (ofK (addressOfIndex a)) (b + k) w := by
  simp only [LoadHolds, tb_addr_ofK, tb_isInK_ofK, true_and, Nat.add_assoc]

section
variable {lm : ℕ} {hs : List ℕ} {ekb esq e10 e11 e136 e137 e293 : ℕ} {rd : Reader}

/-- What the memory holds, entry by entry. -/
structure CpReads (lm : ℕ) (hs : List ℕ) (ekb esq e10 e11 e136 e137 e293 : ℕ) (rd : Reader) :
    Prop where
  kb : ∀ s < 8, LoadHolds rd (ofK (addressOfIndex ekb)) s (gen ^ cpEb lm hs s)
  sq : ∀ k < 34, LoadHolds rd (ofK (addressOfIndex esq)) k (gen ^ 2 ^ k)
  rk : ∀ k < 34, LoadHolds rd (ofK (addressOfIndex esq)) (178 + k) (gen ^ (k * rankStride))
  key : ∀ g < 9, LoadHolds rd (ofK (addressOfIndex e10)) g (cpKey lm hs g)
  size : ∀ g < 9, LoadHolds rd (ofK (addressOfIndex e11)) g (gen ^ cpSize lm hs g)
  ord : ∀ r < 9, LoadHolds rd (ofK (addressOfIndex e136)) r (gen ^ cpPi lm hs r)
  base : ∀ g < 9, LoadHolds rd (ofK (addressOfIndex e137)) g
    (gen ^ cpGP lm hs (cpRho lm hs g))
  off : ∀ c < 94, LoadHolds rd (ofK (addressOfIndex e293)) c
    (gen ^ (stackOffsets (cpKs lm hs)).1.getD c 0)

theorem cp_reads (hl : hs.length = 6)
    (hm : MemLay rd (cpOwn lm hs e10 e11 e136 e137 e293 ++ cpLin lm hs ekb esq)) :
    CpReads lm hs ekb esq e10 e11 e136 e137 e293 rd := by
  obtain ⟨ho, hi⟩ := memLay_append.mp hm
  have r10 := ho (e10, (List.range 9).map (cpKey lm hs)) (by simp [cpOwn])
  have r11 := tbReadsAt_map_iff.mp
    (ho (e11, (List.range 9).map fun g ↦ gen ^ cpSize lm hs g) (by simp [cpOwn]))
  have r138 := tbReadsAt_map_iff.mp (ho (e136, (cpGOrd lm hs).map (gen ^ ·)) (by simp [cpOwn]))
  have r139 := tbReadsAt_map_iff.mp
    (ho (e137, (List.range 9).map fun g ↦ gen ^ cpGP lm hs (cpRho lm hs g)) (by simp [cpOwn]))
  have r295 := tbReadsAt_map_iff.mp
    (ho (e293, (stackOffsets (cpKs lm hs)).1.map (gen ^ ·)) (by simp [cpOwn]))
  have rkb := hi (ekb, 1 :: gen ^ lm :: hs.map (gen ^ ·)) (by simp [cpLin])
  have rsq := hi (esq, gSquaresList) (by simp [cpLin])
  have rrk := hi (esq + 178, rankKeysList) (by simp [cpLin])
  refine ⟨fun s hs8 => ?_, fun k hk => ?_, fun k hk => ?_, fun g hg => ?_,
    fun g hg => ?_, fun r hr => ?_, fun g hg => ?_,
    fun c hc => r295 c (by rw [tb_stackOffsets_length, cpKs_length]; exact hc)⟩
  · have := rkb s (by simp [hl]; omega)
    have hb : (1 :: gen ^ lm :: hs.map (gen ^ ·))[s]'(by simp [hl]; omega) =
        gen ^ cpEb lm hs s := by
      unfold cpEb
      rcases Nat.lt_or_ge s 2 with h2 | h2
      · interval_cases s <;> simp
      · obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
        simp only [List.getElem_cons_succ, List.getElem_map, List.getD_cons_succ]
        rw [List.getD_eq_getElem _ _ (by omega)]
    rwa [hb] at this
  · have := rsq k (by simp [gSquaresList]; exact hk)
    simpa [gSquaresList] using this
  · have := rrk k (by simp [rankKeysList]; exact hk)
    rw [tb_load_ofK_add] at this
    simpa [rankKeysList] using this
  · have := r10 g (by simp; exact hg)
    simpa using this
  · have := r11 g (by simp; exact hg)
    rwa [List.getD_eq_getElem _ _ (by simp; exact hg), List.getElem_range] at this
  · exact r138 r (by rw [cpGOrd_length]; exact hr)
  · have := r139 g (by simp; exact hg)
    rwa [List.getD_eq_getElem _ _ (by simp; exact hg), List.getElem_range] at this

end

/-! ## Every statement -/

section
variable {lm : ℕ} {hs : List ℕ} {ekb esq e10 e11 e136 e137 e293 : ℕ} {rd : Reader}
variable {C : CallRel} {kret : List E → Prop}

/-- Group `gi`'s statements hold. -/
theorem cp_group_holds (hl : hs.length = 6) (hlm : lm ≤ 32) (hhs : ∀ h ∈ hs, h < 29)
    (h5 : hs.getD 5 0 ≤ 27) (hlow : LowDefB 14 rd)
    (R : CpReads lm hs ekb esq e10 e11 e136 e137 e293 rd) {gi : ℕ} (hgi : gi < 9) :
    Stmt.HoldsList C rd (cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd) (cpGroup gi) True kret := by
  set σ := cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd with hσ
  obtain ⟨g1, g2, g3⟩ := cp_grp_geom gi hgi
  have hsrc := cpSrc_lt gi hgi
  have hadj := cpAdj_le gi hgi
  set κ := cpKg lm hs gi with hκd
  have hκ : κ < 34 := cpKc_lt hl hlm hhs h5 (cpC0 gi)
  have hκe : κ = cpEb lm hs (cpSrc gi) + cpAdj gi := rfl
  have hQ : cpB gi ≤ cpQ gi := by unfold cpQ; split_ifs <;> omega
  have hZ : cpQ gi + 6 ≤ cpZ gi := by unfold cpZ; split_ifs <;> omega
  have vG : ∀ v, cpB gi ≤ v → v < cpBx (gi + 1) → σ (.n v) = cpGrpV lm hs esq rd gi v :=
    fun v h1 h2 ↦ cpσ_grp lm hs ekb esq e10 e11 e136 e137 e293 rd hgi h1 h2
  have vQ : ∀ t, cpQ gi + t < cpZ gi → σ (.n (cpQ gi + t)) = cpGrpQ lm hs esq rd gi t := by
    intro t ht
    rw [vG _ (by omega) (by omega), cpGrpV, tb_ite_neg (by omega), tb_ite_pos ht,
      Nat.add_sub_cancel_left]
  have vkb : σ (.n (2 + cpSrc gi)) = gen ^ cpEb lm hs (cpSrc gi) :=
    cpσ_kb lm hs ekb esq e10 e11 e136 e137 e293 rd hsrc
  have vKv : σ (.n (cpKv gi)) = gen ^ κ := by
    unfold cpKv
    split_ifs with ha
    · rw [vkb, hκe, ha, Nat.add_zero]
    · have hq : cpQ gi = cpB gi + 2 := by unfold cpQ; rw [tb_ite_neg ha]
      rw [vG _ (by omega) (by omega), cpGrpV, tb_ite_pos (by omega), tb_ite_neg (by omega)]
  have vZ : σ (.n (cpZ gi)) = ofK (addressOfIndex esq) * gen ^ κ := by
    rw [vG _ (by omega) (by omega), cpGrpV, tb_ite_neg (by omega), tb_ite_neg (by omega),
      tb_ite_pos rfl]
  have vCh : ∀ j ≤ (cpCh gi).length,
      σ (.n (cpZ gi + 1 + j)) = (gen ^ 2 ^ κ) ^ cpChainExp ((cpCh gi).take j) := by
    intro j hj
    rw [vG _ (by omega) (by omega), cpGrpV, tb_ite_neg (by omega), tb_ite_neg (by omega),
      tb_ite_neg (by omega), show cpZ gi + 1 + j - cpZ gi - 1 = j by omega]
  have vKey : σ (.n (cpZ gi - 1)) = cpKey lm hs gi := by
    unfold cpZ
    split_ifs with hc
    · rw [show cpQ gi + 6 - 1 = cpQ gi + 5 by omega, vQ 5 (by unfold cpZ; rw [tb_ite_pos hc]; omega)]
      rw [cpKey, cpInvWords_zero gi hgi hc, tb_word_one, mul_one]
      rfl
    · rw [show cpQ gi + 8 - 1 = cpQ gi + 7 by omega,
        vQ 7 (by unfold cpZ; rw [tb_ite_neg hc]; omega)]
      rfl
  obtain ⟨c1, c2, c3⟩ := rc_ok hlow (a := κ) (K := 33) (by omega) (by norm_num)
  rw [cpGroup, tb_holdsList_append_noRet (by
      simp only [tb_noRetList_append, cpKapS, cpKeyS]; split_ifs <;> rfl),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, cpKapS]; split_ifs <;> rfl),
    tb_holdsList_append_noRet (by simp only [cpKapS]; split_ifs <;> rfl), cpSizeS,
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, cpChain_noRet]; rfl),
    tb_holdsList_append_noRet rfl]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · -- `g^κ = kb[src]·g^adj`
    unfold cpKapS
    split_ifs with ha
    · trivial
    · have hq : cpQ gi = cpB gi + 2 := by unfold cpQ; rw [tb_ite_neg ha]
      have v0 : σ (.n (cpB gi)) = word (2 ^ cpAdj gi) 0 := by
        rw [vG _ le_rfl (by omega), cpGrpV, tb_ite_pos (by omega), tb_ite_pos rfl]
      have v1 : σ (.n (cpB gi + 1)) = gen ^ κ := by
        rw [vG _ (by omega) (by omega), cpGrpV, tb_ite_pos (by omega), tb_ite_neg (by omega)]
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      refine ⟨v0, ?_⟩
      rw [v1, v0, vkb, tb_word_two_pow (by omega), ← pow_add, hκe]
  · -- the range check and the rank key
    simp only [cpRcS, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    have q0 := vQ 0 (by omega)
    have q1 := vQ 1 (by omega)
    have q2 := vQ 2 (by omega)
    have q3 := vQ 3 (by omega)
    have q4 := vQ 4 (by omega)
    have q5 := vQ 5 (by omega)
    rw [Nat.add_zero] at q0
    simp only [cpGrpQ, ← hκd] at q0 q1 q2 q3 q4 q5
    refine ⟨q0, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [vKv, q2]; exact c1
    · rw [q0, vKv, q1, w33_eq, c2]
    · rw [q1, q3]; exact c3
    · rw [q4, vKv]; rfl
    · rw [q4, q5, tb_loadHolds_mul_gen_pow, add_comm]; exact R.rk κ (by omega)
  · -- the key
    unfold cpKeyS
    split_ifs with hc
    · trivial
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      have q6 := vQ 6 (by unfold cpZ; rw [tb_ite_neg hc]; omega)
      have q7 := vQ 7 (by unfold cpZ; rw [tb_ite_neg hc]; omega)
      have q5 := vQ 5 (by omega)
      simp only [cpGrpQ] at q5 q6 q7
      refine ⟨q6, ?_⟩
      rw [q7, q5, q6]; rfl
  · -- the key's store, the size's base
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    have q1 : cpZ gi + 1 = cpZ gi + 1 + 0 := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [vKey]; exact R.key gi hgi
    · rw [vZ, vKv]; rfl
    · rw [vZ, q1, vCh 0 (by omega), List.take_zero, show cpChainExp [] = 1 from rfl, pow_one,
        tb_loadHolds_mul_gen_pow, Nat.add_zero]
      exact R.sq κ (by omega)
  · -- the chain
    rw [cpChain, tb_holdsList_flatten_range _ _ fun _ ↦ rfl]
    intro j hj
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    have e1 : cpZ gi + 1 + 1 + j = cpZ gi + 1 + (j + 1) := by omega
    have hj' : j < (cpCh gi).length := hj
    rw [e1, vCh (j + 1) (by omega), vCh j (by omega)]
    have e : cpChainExp ((cpCh gi).take (j + 1)) =
        if (cpCh gi)[j] then 2 * cpChainExp ((cpCh gi).take j)
        else cpChainExp ((cpCh gi).take j) + 1 := by
      rw [cpChainExp, cpChainExp, List.take_add_one, List.getElem?_eq_getElem hj',
        Option.toList_some, List.foldl_append]
      rfl
    rw [e, List.getD_eq_getElem _ _ hj']
    cases (cpCh gi)[j]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have v0 : σ (.n (cpZ gi + 1)) = (gen ^ 2 ^ κ) ^ cpChainExp ((cpCh gi).take 0) :=
        vCh 0 (by omega)
      rw [v0, List.take_zero, show cpChainExp [] = 1 from rfl, pow_one, pow_succ]
    · simp only [↓reduceIte]
      rw [vCh j (by omega), two_mul, pow_add]
  · -- the size's store
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    rw [vCh _ le_rfl, List.take_length, cpChainExp_eq gi hgi, ← pow_mul, mul_comm]
    exact R.size gi hgi

/-- The honest valuation at rank `r`'s key and running total. -/
theorem cp_rankKey {r : ℕ} (hr : r < 9) :
    cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n (cpRK r)) = cpKey lm hs (cpPi lm hs r) ∧
      cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd (.n (cpRT r)) = gen ^ cpGP lm hs (r + 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · exact ⟨cpσ_rank0 lm hs ekb esq e10 e11 e136 e137 e293 rd (j := 6) (by norm_num),
      cpσ_rank0 lm hs ekb esq e10 e11 e136 e137 e293 rd (j := 10) (by norm_num)⟩
  · have eK : cpRK r = 131 + 18 * r + 6 := by
      unfold cpRK; rw [tb_ite_neg (by omega)]; omega
    have eT : cpRT r = 131 + 18 * r + 17 := by unfold cpRT; omega
    rw [eK, eT]
    exact ⟨cpσ_rank lm hs ekb esq e10 e11 e136 e137 e293 rd hr0 (by omega) (by norm_num),
      cpσ_rank lm hs ekb esq e10 e11 e136 e137 e293 rd hr0 (by omega) (by norm_num)⟩

/-- Rank `r + 1`'s statements hold. -/
theorem cp_rank (hl : hs.length = 6) (hlm : lm ≤ 32) (hhs : ∀ h ∈ hs, h < 29)
    (h5 : hs.getD 5 0 ≤ 27) (hlow : LowDefB 14 rd)
    (R : CpReads lm hs ekb esq e10 e11 e136 e137 e293 rd) {r : ℕ} (hr : r < 8) :
    CpRankOk rd (cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd) (r + 1) := by
  set σ := cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd with hσ
  have vR : ∀ j < 18, σ (.n (131 + 18 * (r + 1) + j)) = cpRankV lm hs e10 e11 e137 rd (r + 1) j :=
    fun j hj ↦ cpσ_rank lm hs ekb esq e10 e11 e136 e137 e293 rd (by omega) (by omega) hj
  have vB : σ (.n (131 + 18 * (r + 1))) = gen ^ cpPi lm hs (r + 1) := vR 0 (by norm_num)
  obtain ⟨vK, vT⟩ : σ (.n (cpRK r)) = cpKey lm hs (cpPi lm hs r) ∧
      σ (.n (cpRT r)) = gen ^ cpGP lm hs (r + 1) := cp_rankKey (lm := lm) (hs := hs) (ekb := ekb) (esq := esq) (e10 := e10)
    (e11 := e11) (e136 := e136) (e137 := e137) (e293 := e293) (rd := rd) (r := r) (by omega)
  have eT : cpRT r = 131 + 18 * (r + 1) - 1 := by unfold cpRT; omega
  rw [eT] at vT
  have v10 : σ (.n 10) = ofK (addressOfIndex e10) := rfl
  have v11 : σ (.n 11) = ofK (addressOfIndex e11) := rfl
  have v136 : σ (.n 136) = ofK (addressOfIndex e136) := rfl
  have v137 : σ (.n 137) = ofK (addressOfIndex e137) := rfl
  have hp := cpPi_lt (lm := lm) (hs := hs) (r := r + 1) (by omega)
  obtain ⟨hE, -⟩ := cpE_spec hl hlm hhs h5 (r := r) (by omega)
  simp only [CpRankOk, TbRcHolds, Nat.add_sub_cancel]
  rw [vB, vR 1 (by norm_num), vR 2 (by norm_num), vR 3 (by norm_num), vR 4 (by norm_num),
    vR 5 (by norm_num), vR 6 (by norm_num), vR 7 (by norm_num), vR 8 (by norm_num),
    vR 9 (by norm_num), vR 10 (by norm_num), vR 11 (by norm_num), vR 12 (by norm_num),
    vR 13 (by norm_num), vR 14 (by norm_num), vR 15 (by norm_num), vR 16 (by norm_num),
    vR 17 (by norm_num), vK, vT, v10, v11, v136, v137]
  simp only [cpRankV]
  obtain ⟨c1, c2, c3⟩ := rc_ok hlow (a := cpPi lm hs (r + 1)) (K := 8) (by omega) (by norm_num)
  obtain ⟨d1, d2, d3⟩ := rc_ok hlow (a := cpE lm hs (r + 1)) (K := 8397) hE (by norm_num)
  refine ⟨R.ord _ (by omega), trivial, ⟨c1, by rw [w8_eq, c2], c3⟩, trivial, ?_, trivial,
    cpKey_step hl hlm hhs h5 (by omega), trivial, ?_, ⟨d1, by rw [wRankBound_eq, d2], d3⟩,
    trivial, ?_, trivial, ?_, ?_⟩
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact R.key _ hp
  · rw [pow_succ, mul_assoc, mul_comm gen wInvGen, wInvGen_mul_gen, mul_one]
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := R.base _ hp
    rwa [cpRho_pi (by omega)] at this
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact R.size _ hp
  · rw [cpGP_succ, pow_add]

/-- Group `gi`'s columns' statements hold. -/
theorem cp_cols_holds (hl : hs.length = 6) (hlm : lm ≤ 32) (hhs : ∀ h ∈ hs, h < 29)
    (h5 : hs.getD 5 0 ≤ 27) (R : CpReads lm hs ekb esq e10 e11 e136 e137 e293 rd) {gi : ℕ}
    (hgi : gi < 9) :
    Stmt.HoldsList C rd (cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd) (cpCols gi) True kret := by
  set σ := cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd with hσ
  obtain ⟨g1, g2, g3⟩ := cp_col_geom gi hgi
  have hκ := cpKc_lt hl hlm hhs h5 (cpC0 gi)
  have hsrc := cpSrc_lt gi hgi
  have hlen := cpLen_pos gi hgi
  obtain ⟨hoffs, -⟩ := cp_offsets (lm := lm) hl
  have vC : ∀ v, cpD gi ≤ v → v < cpD (gi + 1) → σ (.n v) = cpColV lm hs esq gi v :=
    fun v h1 h2 ↦ cpσ_col lm hs ekb esq e10 e11 e136 e137 e293 rd hgi h1 h2
  have v0 : σ (.n (cpD gi)) = ofK (addressOfIndex esq) * gen ^ cpEb lm hs (cpSrc gi) := by
    rw [vC _ le_rfl (by omega), cpColV, tb_ite_pos rfl]
  have v1 : σ (.n (cpD gi + 1)) = gen ^ 2 ^ cpKg lm hs gi := by
    rw [vC _ (by omega) (by omega), cpColV, tb_ite_neg (by omega), tb_ite_pos rfl]
  have vO : ∀ j < cpLen gi, σ (.n (cpD gi + 2 + j)) =
      gen ^ (cpGP lm hs (cpRho lm hs gi) + j * 2 ^ cpKg lm hs gi) := by
    intro j hj
    rw [vC _ (by omega) (by omega), cpColV, tb_ite_neg (by omega), tb_ite_neg (by omega),
      show cpD gi + 2 + j - cpD gi - 2 = j by omega]
  have hO : ∀ j < cpLen gi, LoadHolds rd (σ (.n 293)) (cpC0 gi + j) (σ (.n (cpD gi + 2 + j))) := by
    intro j hj
    rw [vO j hj, ← hoffs gi hgi j hj]
    exact R.off _ (by have := cpC0_le gi hgi; unfold cpLen at hj; omega)
  rw [cpCols, tb_holdsList_append_noRet rfl, tb_holdsList_flatten_range _ _ fun _ ↦ rfl]
  refine ⟨?_, fun j hj ↦ ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have vkb : σ (.n (2 + cpSrc gi)) = gen ^ cpEb lm hs (cpSrc gi) :=
        cpσ_kb lm hs ekb esq e10 e11 e136 e137 e293 rd hsrc
      rw [v0, vkb]; rfl
    · rw [v0, v1, tb_loadHolds_mul_gen_pow]; exact R.sq _ hκ
    · rw [show σ (.n 137) = ofK (addressOfIndex e137) from rfl,
        show cpD gi + 2 = cpD gi + 2 + 0 from rfl, vO 0 (by omega), Nat.zero_mul, Nat.add_zero]
      exact R.base gi hgi
    · have := hO 0 (by omega)
      simp only [Nat.add_zero] at this
      exact this
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    have hj' : j + 1 < cpLen gi := by omega
    have e1 : cpD gi + 3 + j = cpD gi + 2 + (j + 1) := by omega
    refine ⟨?_, ?_⟩
    · rw [e1, vO _ hj', vO j (by omega), v1, ← pow_add]
      congr 1; ring
    · rw [e1, show cpC0 gi + 1 + j = cpC0 gi + (j + 1) by omega]
      exact hO _ hj'

end

/-- **`certify_placement`'s body holds** of the honest valuation: on a memory holding its base,
squares table and rank keys, its five buffers holding the groups' keys, sizes, order and bases and
the columns' `g^offset`, defined below `2^14`, the relation holds with the stack's total and the
offsets' buffer. -/
theorem cp_body_holds {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6) (hlm : lm ≤ 32)
    (hhs : ∀ h ∈ hs, h < 29) (h5 : hs.getD 5 0 ≤ 27) (ekb esq e10 e11 e136 e137 e293 : ℕ)
    (rd : Reader)
    (hm : MemLay rd (cpOwn lm hs e10 e11 e136 e137 e293 ++ cpLin lm hs ekb esq))
    (hlow : LowDefB 14 rd) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd)
      (cpPre ++ [.ret [.n 406, .n 407]]) False
      (fun rs => rs = [gen ^ stackTotal (columnKappas lm guestLogBytecode hs),
        ofK (addressOfIndex e293)]) := by
  have R := cp_reads hl hm
  set σ := cpσ lm hs ekb esq e10 e11 e136 e137 e293 rd with hσ
  have r0 : ∀ j < 11, σ (.n (138 + j)) = cpRank0V lm hs e10 e11 e137 rd j := fun j hj =>
    cpσ_rank0 lm hs ekb esq e10 e11 e136 e137 e293 rd hj
  have hp0 := cpPi_lt (lm := lm) (hs := hs) (r := 0) (by norm_num)
  obtain ⟨-, htot⟩ := cp_offsets (lm := lm) hl
  obtain ⟨c1, c2, c3⟩ := rc_ok hlow (a := cpPi lm hs 0) (K := 8) (by omega) (by norm_num)
  have s138 : σ (.n 138) = gen ^ cpPi lm hs 0 := r0 0 (by norm_num)
  have s406 : σ (.n 406) = gen ^ cpGP lm hs 9 := rfl
  have s292 : σ (.n 292) = gen ^ cpGP lm hs 9 :=
    (cp_rankKey (lm := lm) (hs := hs) (ekb := ekb) (esq := esq) (e10 := e10) (e11 := e11)
      (e136 := e136) (e137 := e137) (e293 := e293) (rd := rd) (r := 8) (by norm_num)).2
  rw [holdsList_append, holdsList_noRet _ cpPre_noRet]
  refine ⟨?_, ?_⟩
  · simp only [cpPre, holdsList_append,
      tb_holdsList_range_flatten 8 (fun i ↦ [Stmt.atom (.load (.n (2 + i)) (.n 0) i)])
        (fun _ ↦ rfl),
      tb_holdsList_range_flatten 9 cpGroup cpGroup_noRet,
      tb_holdsList_range_flatten 8 (fun r ↦ cpRank (r + 1)) (fun _ ↦ rfl),
      tb_holdsList_range_flatten 9 cpCols cpCols_noRet, holds_cpRank, cpRank0,
      Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and]
    refine ⟨fun i hi ↦ ?_, fun gi hgi ↦ cp_group_holds hl hlm hhs h5 hlow R hgi, ?_, r0 1 (by norm_num),
      ⟨?_, ?_, ?_⟩, r0 5 (by norm_num), ?_, r0 7 (by norm_num), r0 8 (by norm_num), ?_,
      r0 9 (by norm_num), ?_, fun r hr ↦ cp_rank hl hlm hhs h5 hlow R hr,
      fun gi hgi ↦ cp_cols_holds hl hlm hhs h5 R hgi, by rw [s406, s292], rfl⟩
    · have vkb : σ (.n (2 + i)) = gen ^ cpEb lm hs i :=
        cpσ_kb lm hs ekb esq e10 e11 e136 e137 e293 rd hi
      rw [vkb]; exact R.kb i hi
    · rw [s138]; exact R.ord 0 (by norm_num)
    · rw [s138, show σ (.n 141) = rdv rd (cpPi lm hs 0) from r0 3 (by norm_num)]; exact c1
    · rw [show σ (.n 139) = w8 from r0 1 (by norm_num), s138,
        show σ (.n 140) = gen ^ (8 - cpPi lm hs 0) from r0 2 (by norm_num), w8_eq, c2]
    · rw [show σ (.n 140) = gen ^ (8 - cpPi lm hs 0) from r0 2 (by norm_num),
        show σ (.n 142) = rdv rd (8 - cpPi lm hs 0) from r0 4 (by norm_num)]
      exact c3
    · rw [show σ (.n 143) = ofK (addressOfIndex e10) * gen ^ cpPi lm hs 0 from r0 5 (by norm_num),
        show σ (.n 144) = cpKey lm hs (cpPi lm hs 0) from r0 6 (by norm_num),
        tb_loadHolds_mul_gen_pow, Nat.add_zero]
      exact R.key _ hp0
    · have h0 := R.base _ hp0
      rw [cpRho_pi (by norm_num), cpGP_zero, pow_zero] at h0
      rw [show σ (.n 146) = ofK (addressOfIndex e137) * gen ^ cpPi lm hs 0 from r0 8 (by norm_num),
        show σ (.n 145) = word 1 0 from r0 7 (by norm_num), tb_loadHolds_mul_gen_pow,
        Nat.add_zero, tb_word_one]
      exact h0
    · rw [show σ (.n 147) = ofK (addressOfIndex e11) * gen ^ cpPi lm hs 0 from r0 9 (by norm_num),
        show σ (.n 148) = gen ^ cpGP lm hs 1 from r0 10 (by norm_num), tb_loadHolds_mul_gen_pow,
        Nat.add_zero, cpGP_succ, cpGP_zero, Nat.zero_add]
      exact R.size _ hp0
  · show [σ (.n 406), σ (.n 407)] = _
    rw [s406, htot, show σ (.n 407) = ofK (addressOfIndex e293) from rfl]

/-- **The offsets' buffer satisfies `PCtx`** on any memory holding the buffers. -/
theorem cp_ctx {lm : ℕ} {hs : List ℕ} {e10 e11 e136 e137 e293 : ℕ} {rd : Reader}
    (hm : MemLay rd (cpOwn lm hs e10 e11 e136 e137 e293)) :
    PCtx rd (columnKappas lm guestLogBytecode hs) (ofK (addressOfIndex e293)) :=
  ⟨columnKappas_length _ _ _, hm (e293, (stackOffsets (cpKs lm hs)).1.map (gen ^ ·))
    (by simp [cpOwn])⟩

end
end LeanVM.Guest.B1.Tables
