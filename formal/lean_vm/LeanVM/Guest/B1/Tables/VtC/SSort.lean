/-
  LeanVM.Guest.B1.Tables.VtC.SSort

  `verify_tables`' block certification holds on the honest valuation: the groups' keys and sizes
  stored, each side's ranks reading its groups in the honest order, the groups' bases stored, every
  block's offset `g^stackOffsets`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SGrpT

/-!
# The block certification, honestly (G:2239-2276)

The honest buffers, for the memory's log-size `lm` and the tables' heights `τ` (`vtKg`: a group's
log-size, `vtGsz`: its size in the exponent): `vtGKeyW` (`group_key`: `g^(247 κ - b0)`),
`vtGSizeW` (`group_size`), `vtGOrdW` (`group_order`: each side's groups sorted by `stackLe`,
`vtOrd`, the push side's at `0 .. 8`, the count side's at `18 .. 23`), `vtGBaseW` (`group_base`:
the prefix sums of the sizes in that order, `vtGP`).

`rank0_ok`, `rank_ok`: a rank's statements hold from its equations and the memory; `boff_ok`: a
group's block offsets. `vtS_sort`: statements `0 ..< 563` hold and every push and count block's
offset is its side's `stackOffsets` offset.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open Finset (range)

@[expose] public section

/-! ## The honest order -/

/-- Group `gi`'s log-size. -/
def vtKg (lm : ℕ) (τ : ℕ → ℕ) (gi : ℕ) : ℕ := vtKap lm τ (blockGroupStart.getD gi 0)

/-- Group `gi`'s size, in the exponent. -/
def vtGsz (lm : ℕ) (τ : ℕ → ℕ) (gi : ℕ) : ℕ :=
  (blockGroupStart.getD (gi + 1) 0 - blockGroupStart.getD gi 0) * 2 ^ vtKg lm τ gi

/-- Side `s`'s first group and its number of groups (push `0`, count `2`). -/
def vtG0 (s : ℕ) : ℕ := if s = 0 then 0 else 18
def vtGm (s : ℕ) : ℕ := if s = 0 then 9 else 6

/-- **Side `s`'s groups in rank order**, by index in the side: larger first, ties by index. -/
def vtOrd (lm : ℕ) (τ : ℕ → ℕ) (s : ℕ) : List ℕ :=
  (List.range (vtGm s)).mergeSort (stackLe fun j ↦ vtKg lm τ (vtG0 s + j))

/-- Rank `r`'s group, in the side. -/
def vtPi (lm : ℕ) (τ : ℕ → ℕ) (s r : ℕ) : ℕ := (vtOrd lm τ s).getD r 0

/-- Group `j`'s rank, in the side. -/
def vtRho (lm : ℕ) (τ : ℕ → ℕ) (s j : ℕ) : ℕ := (vtOrd lm τ s).idxOf j

/-- The sizes of the first `r` ranks' groups. -/
def vtGP (lm : ℕ) (τ : ℕ → ℕ) (s r : ℕ) : ℕ :=
  ∑ r' ∈ range r, vtGsz lm τ (vtG0 s + vtPi lm τ s r')

/-- `group_key`'s honest words. -/
noncomputable def vtGKeyW (lm : ℕ) (τ : ℕ → ℕ) : List E := (List.range 24).map fun gi ↦
  gen ^ (vtKg lm τ gi * 247) * (gen ^ blockGroupStart.getD gi 0)⁻¹

/-- `group_size`'s honest words. -/
noncomputable def vtGSizeW (lm : ℕ) (τ : ℕ → ℕ) : List E :=
  (List.range 24).map fun gi ↦ gen ^ vtGsz lm τ gi

/-- `group_order`'s honest words (the pull side's slots unread). -/
noncomputable def vtGOrdW (lm : ℕ) (τ : ℕ → ℕ) : List E := (List.range 24).map fun i ↦
  if i < 9 then gen ^ vtPi lm τ 0 i else if i < 18 then 0 else gen ^ (18 + vtPi lm τ 2 (i - 18))

/-- `group_base`'s honest words (the pull side's slots unwritten). -/
noncomputable def vtGBaseW (lm : ℕ) (τ : ℕ → ℕ) : List E := (List.range 24).map fun gi ↦
  if gi < 9 then gen ^ vtGP lm τ 0 (vtRho lm τ 0 gi)
  else if gi < 18 then 0 else gen ^ vtGP lm τ 2 (vtRho lm τ 2 (gi - 18))

section Order
variable {lm : ℕ} {τ : ℕ → ℕ} {s : ℕ}

theorem vtOrd_perm : (vtOrd lm τ s).Perm (List.range (vtGm s)) := List.mergeSort_perm _ _

theorem vtOrd_length : (vtOrd lm τ s).length = vtGm s := by
  rw [vtOrd_perm.length_eq, List.length_range]

theorem vtOrd_nodup : (vtOrd lm τ s).Nodup := vtOrd_perm.nodup_iff.mpr List.nodup_range

theorem vtPi_lt {r : ℕ} (hr : r < vtGm s) : vtPi lm τ s r < vtGm s := by
  have hm : (vtOrd lm τ s).getD r 0 ∈ vtOrd lm τ s := by
    rw [List.getD_eq_getElem _ _ (by rw [vtOrd_length]; exact hr)]; exact List.getElem_mem _
  exact List.mem_range.mp (vtOrd_perm.subset hm)

theorem vtOrd_sorted :
    (vtOrd lm τ s).Pairwise fun a b ↦ stackLe (fun j ↦ vtKg lm τ (vtG0 s + j)) a b = true := by
  unfold vtOrd
  apply List.pairwise_mergeSort
  · intro a b c; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · intro a b; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **Adjacent ranks**: sizes do not increase, ties ascend by group. -/
theorem vtPi_adj {r : ℕ} (hr : r + 1 < vtGm s) :
    vtKg lm τ (vtG0 s + vtPi lm τ s (r + 1)) ≤ vtKg lm τ (vtG0 s + vtPi lm τ s r) ∧
      (vtKg lm τ (vtG0 s + vtPi lm τ s (r + 1)) = vtKg lm τ (vtG0 s + vtPi lm τ s r) →
        vtPi lm τ s r < vtPi lm τ s (r + 1)) := by
  have hlen := vtOrd_length (lm := lm) (τ := τ) (s := s)
  have hp := List.pairwise_iff_getElem.mp (vtOrd_sorted (lm := lm) (τ := τ) (s := s)) r (r + 1)
    (by omega) (by omega) (by omega)
  have hne : (vtOrd lm τ s)[r]'(by omega) ≠ (vtOrd lm τ s)[r + 1]'(by omega) := fun he ↦
    absurd ((List.Nodup.getElem_inj_iff (vtOrd_nodup (lm := lm) (τ := τ) (s := s))).mp he)
      (by omega)
  simp only [vtPi, List.getD_eq_getElem _ _ (show r < (vtOrd lm τ s).length by omega),
    List.getD_eq_getElem _ _ (show r + 1 < (vtOrd lm τ s).length by omega)]
  simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  omega

theorem vtRho_pi {r : ℕ} (hr : r < vtGm s) : vtRho lm τ s (vtPi lm τ s r) = r := by
  have hlen := vtOrd_length (lm := lm) (τ := τ) (s := s)
  have hmem : (vtOrd lm τ s)[r]'(by omega) ∈ vtOrd lm τ s := List.getElem_mem _
  have hi : (vtOrd lm τ s).idxOf ((vtOrd lm τ s)[r]'(by omega)) < (vtOrd lm τ s).length :=
    List.idxOf_lt_length_of_mem hmem
  have hg := List.getElem_idxOf hi
  rw [vtRho, vtPi, List.getD_eq_getElem _ _ (by omega)]
  exact (List.Nodup.getElem_inj_iff (vtOrd_nodup (lm := lm) (τ := τ) (s := s))).mp hg

end Order

/-! ## The rank templates -/

section
variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val}

theorem goodL_iff : ∀ {l : List Stmt}, GoodL rd w σ l ↔ ∀ s ∈ l, GoodS rd vtSL w σ (fixNe s)
  | [] => by simp [GoodL]
  | s :: l => by simp [GoodL, goodL_iff]

/-- **A side's first rank, honestly.** -/
theorem rank0_ok (hlow : LowDefB 14 rd) {v R s gi : ℕ} (hv : 37 ≤ v)
    (hg : GoodL rd w σ (vtRank0T v R s))
    (s0 : Atom.load (.n v) (.n 36) R ∉ vtSL) (s8 : Atom.load (.n (v + 8)) (.n (v + 7)) 0 ∉ vtSL)
    (s12 : Atom.load (.n (v + 12)) (.n (v + 11)) 0 ∉ vtSL)
    (hord : LoadHolds rd (σ (.n 36)) R (gen ^ gi)) (hgi : gi ≤ 23)
    (hside : LoadHolds rd (σ (.n 12) * gen ^ gi) 212 (word s 0))
    {key sz : E} (hkey : LoadHolds rd (σ (.n 33) * gen ^ gi) 0 key)
    (hbase : LoadHolds rd (σ (.n 35) * gen ^ gi) 0 1)
    (hsz : LoadHolds rd (σ (.n 34) * gen ^ gi) 0 sz) :
    (∀ st ∈ vtRank0T v R s, VSH C rd σ st) ∧ σ (.n v) = gen ^ gi ∧ σ (.n (v + 8)) = key ∧
      σ (.n (v + 12)) = sz ∧ σ (.n (v + 9)) = 1 := by
  simp only [vtRank0T, GoodL, GoodS, fixNe, Good, and_true] at hg
  obtain ⟨g0, g1, g2, g3, g4, -, g6, g7, g8, g9, -, g11, g12⟩ := hg
  simp only [show (12 : ℕ) < v + 6 ∧ v < v + 6 from ⟨by omega, by omega⟩,
    show (33 : ℕ) < v + 7 ∧ v < v + 7 from ⟨by omega, by omega⟩,
    show (35 : ℕ) < v + 10 ∧ v < v + 10 from ⟨by omega, by omega⟩,
    show (34 : ℕ) < v + 11 ∧ v < v + 11 from ⟨by omega, by omega⟩,
    show v + 1 < v + 2 by omega, ↓reduceIte] at g4 g6 g9 g11 g2
  obtain ⟨r1, r2, r3⟩ := g2
  obtain ⟨ev, l0⟩ := read_of (g0.resolve_left s0) hord
  obtain ⟨hrc, -⟩ := rc_holds (κ := 14) hlow r1 r2 r3 ev (by rw [g1, vtW23_gen]) hgi
    (by norm_num)
  have m6 : σ (.n (v + 6)) = σ (.n 12) * gen ^ gi := by rw [g4, ev]
  have m7 : σ (.n (v + 7)) = σ (.n 33) * gen ^ gi := by rw [g6, ev]
  obtain ⟨e8, l8⟩ := read_of (g7.resolve_left s8) (by rw [m7]; exact hkey)
  have m10 : σ (.n (v + 10)) = σ (.n 35) * gen ^ gi := by rw [g9, ev]
  have m11 : σ (.n (v + 11)) = σ (.n 34) * gen ^ gi := by rw [g11, ev]
  obtain ⟨e12, l12⟩ := read_of (g12.resolve_left s12) (by rw [m11]; exact hsz)
  refine ⟨?_, ev, e8, e12, by rw [g8, tb_word_one]⟩
  simp only [vtRank0T, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom]
  refine ⟨l0, g1, hrc, g3, g4, ?_, g6, l8, g8, g9, ?_, g11, l12⟩
  · show LoadHolds rd _ _ _
    rw [m6, g3]; exact hside
  · show LoadHolds rd _ _ _
    rw [m10, g8, tb_word_one]; exact hbase

/-- **A later rank, honestly**: the previous rank's key `g^(d+1)` times this one's. -/
theorem rank_ok (hlow : LowDefB 14 rd) {v R s pk gin gi d : ℕ} (hv : 37 ≤ v) (hpk : pk < v)
    (hgin : gin < v) (hg : GoodL rd w σ (vtRankT v R s pk gin))
    (s0 : Atom.load (.n v) (.n 36) R ∉ vtSL) (s8 : Atom.load (.n (v + 8)) (.n (v + 7)) 0 ∉ vtSL)
    (s18 : Atom.load (.n (v + 18)) (.n (v + 17)) 0 ∉ vtSL)
    (hord : LoadHolds rd (σ (.n 36)) R (gen ^ gi)) (hgi : gi ≤ 23)
    (hside : LoadHolds rd (σ (.n 12) * gen ^ gi) 212 (word s 0))
    {key sz : E} (hkey : LoadHolds rd (σ (.n 33) * gen ^ gi) 0 key)
    (hbase : LoadHolds rd (σ (.n 35) * gen ^ gi) 0 (σ (.n gin)))
    (hsz : LoadHolds rd (σ (.n 34) * gen ^ gi) 0 sz)
    (hpkv : σ (.n pk) = gen ^ (d + 1) * key) (hd : d ≤ 8397) (hk0 : key ≠ 0) :
    (∀ st ∈ vtRankT v R s pk gin, VSH C rd σ st) ∧ σ (.n v) = gen ^ gi ∧
      σ (.n (v + 8)) = key ∧ σ (.n (v + 18)) = sz ∧ σ (.n (v + 19)) = σ (.n gin) * sz := by
  simp only [vtRankT, GoodL, GoodS, fixNe, Good, and_true] at hg
  obtain ⟨g0, g1, g2, g3, g4, -, g6, g7, g8, g9, g10, g11, g12, g13, -, g15, g16, g17⟩ := hg
  simp only [show (12 : ℕ) < v + 6 ∧ v < v + 6 from ⟨by omega, by omega⟩,
    show (33 : ℕ) < v + 7 ∧ v < v + 7 from ⟨by omega, by omega⟩,
    show ¬ (v + 10 < pk ∧ v + 8 < pk) from fun h ↦ by omega,
    show v + 10 < v + 12 ∧ v + 11 < v + 12 from ⟨by omega, by omega⟩,
    show (35 : ℕ) < v + 16 ∧ v < v + 16 from ⟨by omega, by omega⟩,
    show (34 : ℕ) < v + 17 ∧ v < v + 17 from ⟨by omega, by omega⟩,
    show gin < v + 19 ∧ v + 18 < v + 19 from ⟨by omega, by omega⟩,
    show v + 1 < v + 2 by omega, show v + 9 < v + 13 by omega, ↓reduceIte]
    at g4 g6 g9 g11 g13 g15 g17 g2 g12
  obtain ⟨r1, r2, r3⟩ := g2
  obtain ⟨ev, l0⟩ := read_of (g0.resolve_left s0) hord
  obtain ⟨hrc, -⟩ := rc_holds (κ := 14) hlow r1 r2 r3 ev (by rw [g1, vtW23_gen]) hgi
    (by norm_num)
  have m6 : σ (.n (v + 6)) = σ (.n 12) * gen ^ gi := by rw [g4, ev]
  have m7 : σ (.n (v + 7)) = σ (.n 33) * gen ^ gi := by rw [g6, ev]
  obtain ⟨e8, l8⟩ := read_of (g7.resolve_left s8) (by rw [m7]; exact hkey)
  have e10 : σ (.n (v + 10)) = gen ^ (d + 1) := by
    rw [g9, hpkv, e8, mul_assoc, mul_inv_cancel₀ hk0, mul_one]
  have e12 : σ (.n (v + 12)) = gen ^ d := by
    rw [g11, e10, g10, pow_succ, mul_assoc, mul_comm gen, ← pow_one gen,
      vt_wInv (W := 9223372036854775821) (b := 1) (by decide +kernel), mul_one]
  obtain ⟨q1, q2, q3⟩ := g12
  obtain ⟨hrc12, -⟩ := rc_holds (κ := 14) hlow q1 q2 q3 e12 (by rw [g8, vtW8397_gen]) hd
    (by norm_num)
  have m16 : σ (.n (v + 16)) = σ (.n 35) * gen ^ gi := by rw [g13, ev]
  have m17 : σ (.n (v + 17)) = σ (.n 34) * gen ^ gi := by rw [g15, ev]
  obtain ⟨e18, l18⟩ := read_of (g16.resolve_left s18) (by rw [m17]; exact hsz)
  refine ⟨?_, ev, e8, e18, by rw [g17, e18]⟩
  simp only [vtRankT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom]
  refine ⟨l0, g1, hrc, g3, g4, ?_, g6, l8, g8, mulDiv_holds g9 (by rw [e8]; exact hk0), g10, g11,
    hrc12, g13, ?_, g15, l18, g17⟩
  · show LoadHolds rd _ _ _
    rw [m6, g3]; exact hside
  · show LoadHolds rd _ _ _
    rw [m16]; exact hbase

/-- **A group's block offsets, honestly**: the step `g_squares[κ]` and the base read, each block
one step on. -/
theorem boff_ok {kv off gi bv len : ℕ} (hkv : kv + 2 < bv) (h12 : 14 < bv)
    (hg : GoodL rd w σ (vtBoffT kv off gi bv len))
    (s1 : Atom.load (.n (bv - 1)) (.n (bv - 2)) off ∉ vtSL) (s2 : Atom.load (.n bv) (.n 35) gi ∉ vtSL)
    {step base : E} (hst : LoadHolds rd (σ (.n 12) * σ (.n kv)) off step)
    (hb : LoadHolds rd (σ (.n 35)) gi base) :
    (∀ st ∈ vtBoffT kv off gi bv len, VSH C rd σ st) ∧ σ (.n (bv - 1)) = step ∧
      σ (.n bv) = base ∧ ∀ i < len - 1, σ (.n (bv + 1 + i)) = σ (.n (bv + i)) * step := by
  rw [goodL_iff] at hg
  have h0 := hg (.atom (.mul (.n (bv - 2)) (.n 12) (.n kv))) (by simp [vtBoffT])
  have h1 := hg (.atom (.load (.n (bv - 1)) (.n (bv - 2)) off)) (by simp [vtBoffT])
  have h2 := hg (.atom (.load (.n bv) (.n 35) gi)) (by simp [vtBoffT])
  simp only [GoodS, fixNe, Good,
    show (12 : ℕ) < bv - 2 ∧ kv < bv - 2 from ⟨by omega, by omega⟩] at h0
  simp only [GoodS, fixNe, Good] at h1 h2
  obtain ⟨e1, l1⟩ := read_of (h1.resolve_left s1) (by rw [h0]; exact hst)
  obtain ⟨e2, l2⟩ := read_of (h2.resolve_left s2) hb
  have hm : ∀ i < len - 1, σ (.n (bv + 1 + i)) = σ (.n (bv + i)) * σ (.n (bv - 1)) := by
    intro i hi
    have := hg (.atom (.mul (.n (bv + 1 + i)) (.n (bv + i)) (.n (bv - 1))))
      (by simp only [vtBoffT, List.mem_append, List.mem_cons, List.mem_map, List.mem_range]
          exact Or.inr ⟨i, hi, rfl⟩)
    simpa only [GoodS, fixNe, fixA, Good,
      show bv + i < bv + 1 + i ∧ bv - 1 < bv + 1 + i from ⟨by omega, by omega⟩, and_self,
      ↓reduceIte] using this
  refine ⟨?_, e1, e2, fun i hi ↦ by rw [hm i hi, e1]⟩
  intro st hst'
  simp only [vtBoffT, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hst'
  rcases hst' with (rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  · exact h0
  · exact l1
  · exact l2
  · exact hm i hi

end

/-! ## A side -/

theorem vtRv_ge (v0 r : ℕ) : v0 ≤ vtRv v0 r := by unfold vtRv; split <;> omega

theorem vtRv_prev {v0 r : ℕ} (hr : 1 ≤ r) : vtRv v0 (r - 1) + 8 < vtRv v0 r := by
  unfold vtRv; split_ifs <;> omega

theorem vtGin_lt {v0 r : ℕ} (hr : 1 ≤ r) : vtGin v0 r < vtRv v0 r := by
  unfold vtGin vtRv; split_ifs <;> omega

theorem vtRankAt_length (v0 R0 s r : ℕ) : (vtRankAt v0 R0 s r).length = 18 := rfl

theorem vtRank0T_length (v R s : ℕ) : (vtRank0T v R s).length = 13 := rfl

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "σv" => vtσ rd w args

/-- **A side's ranks, honestly**: rank `r` reads group `g^(gi r)`, its key `key r` and size
`g^(S r)`; the keys descend by `g^(d+1)`, `d ≤ 8397`; the bases hold the sizes' prefix sums. Every
rank's statements hold and give `VtRankFacts`, the running offset the prefix sum. -/
theorem side_ok (hl : args.length = 20) (hlow : LowDefB 14 rd) {v0 p0 R0 s m : ℕ}
    (hv : 37 ≤ v0) (hm : 1 ≤ m)
    (h0 : tbStmtsEqb (vtRank0T v0 R0 s) ((vtAt p0).take (vtRank0T v0 R0 s).length) = true)
    (hr : ∀ r < m, 1 ≤ r →
      tbStmtsEqb (vtRankAt v0 R0 s r) ((vtAt (vtRp p0 r)).take (vtRankAt v0 R0 s r).length) = true)
    (hS0 : ∀ a ∈ [Atom.load (.n v0) (.n 36) R0, .load (.n (v0 + 8)) (.n (v0 + 7)) 0,
      .load (.n (v0 + 12)) (.n (v0 + 11)) 0], a ∉ vtSL)
    (hS : ∀ r < m, 1 ≤ r → ∀ a ∈ [Atom.load (.n (vtRv v0 r)) (.n 36) (R0 + r),
      .load (.n (vtRv v0 r + 8)) (.n (vtRv v0 r + 7)) 0,
      .load (.n (vtRv v0 r + 18)) (.n (vtRv v0 r + 17)) 0], a ∉ vtSL)
    (gi : ℕ → ℕ) (key : ℕ → E) (S : ℕ → ℕ)
    (hord : ∀ r < m, LoadHolds rd (σv (.n 36)) (R0 + r) (gen ^ gi r)) (hgi : ∀ r < m, gi r ≤ 23)
    (hside : ∀ r < m, LoadHolds rd (σv (.n 12) * gen ^ gi r) 212 (word s 0))
    (hkey : ∀ r < m, LoadHolds rd (σv (.n 33) * gen ^ gi r) 0 (key r))
    (hsz : ∀ r < m, LoadHolds rd (σv (.n 34) * gen ^ gi r) 0 (gen ^ S r))
    (hbase : ∀ r < m, LoadHolds rd (σv (.n 35) * gen ^ gi r) 0 (gen ^ ∑ r' ∈ range r, S r'))
    (hstep : ∀ r, r + 1 < m → ∃ d ≤ 8397, key r = gen ^ (d + 1) * key (r + 1))
    (hk0 : ∀ r < m, key r ≠ 0) :
    (∀ st ∈ (vtPre.drop p0).take (13 + 18 * (m - 1)), VSH (coreProgram.Rel rd) rd σv st) ∧
      ∀ r < m, VtRankFacts rd σv v0 s r ∧ σv (.n (vtGin v0 r)) = gen ^ ∑ r' ∈ range r, S r' := by
  -- rank by rank
  have P : ∀ r < m, (∀ st ∈ (if r = 0 then vtRank0T v0 R0 s else vtRankAt v0 R0 s r),
      VSH (coreProgram.Rel rd) rd σv st) ∧ VtRankFacts rd σv v0 s r ∧
      σv (.n (vtGin v0 r)) = gen ^ ∑ r' ∈ range r, S r' ∧ σv (.n (vtRv v0 r + 8)) = key r ∧
      σv (.n (vtSz v0 r)) = gen ^ S r := by
    intro r
    induction r with
    | zero =>
      intro hr0
      have hg := vt_goodL (rd := rd) (w := w) hl p0 _ (vtPre_drop p0 ▸ h0)
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS0
      obtain ⟨hst, ev, e8, e12, e9⟩ := rank0_ok (C := coreProgram.Rel rd) hlow hv hg hS0.1 hS0.2.1
        hS0.2.2 (hord 0 hr0) (hgi 0 hr0) (hside 0 hr0) (hkey 0 hr0)
        (by simpa using hbase 0 hr0) (hsz 0 hr0)
      simp only [↓reduceIte]
      refine ⟨hst, ?_, by simp [vtGin, e9], by simp [vtRv, e8], by simp [vtSz, e12]⟩
      simp only [VtRankFacts, vtRv, vtGin, vtSz, vtGout, ↓reduceIte]
      refine ⟨⟨gi 0, by have := hgi 0 hr0; omega, ev⟩, by rw [ev]; exact hside 0 hr0,
        by rw [ev, e8]; exact hkey 0 hr0, by rw [ev, e9]; simpa using hbase 0 hr0,
        by rw [ev, e12]; exact hsz 0 hr0, by rw [e9, one_mul], fun _ ↦ e9,
        fun h ↦ absurd h (by omega)⟩
    | succ k ih =>
      intro hr1
      obtain ⟨-, hFk, hgk, hkk, hzk⟩ := ih (by omega)
      have hgo : σv (.n (vtGout v0 k)) = gen ^ ∑ r' ∈ range (k + 1), S r' := by
        rw [hFk.2.2.2.2.2.1, hgk, hzk, ← pow_add, Finset.sum_range_succ]
      have hg := vt_goodL (rd := rd) (w := w) hl _ _ (vtPre_drop _ ▸ hr (k + 1) hr1 (by omega))
      have hS' := hS (k + 1) hr1 (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS'
      obtain ⟨d, hd, hdk⟩ := hstep k hr1
      have hgin : σv (.n (vtGin v0 (k + 1))) = gen ^ ∑ r' ∈ range (k + 1), S r' := by
        rw [vt_gin_succ]; exact hgo
      rw [vtRankAt, Nat.add_sub_cancel] at hg
      have hpk : vtRv v0 k + 8 < vtRv v0 (k + 1) := by
        have := vtRv_prev (v0 := v0) (r := k + 1) (by omega)
        rwa [Nat.add_sub_cancel] at this
      obtain ⟨hst, ev, e8, e18, e19⟩ := rank_ok (C := coreProgram.Rel rd) (d := d) hlow
        (le_trans hv (vtRv_ge v0 (k + 1))) hpk (vtGin_lt (by omega)) hg hS'.1 hS'.2.1 hS'.2.2
        (hord _ hr1) (hgi _ hr1) (hside _ hr1) (hkey _ hr1) (by rw [hgin]; exact hbase _ hr1)
        (hsz _ hr1) (by rw [hkk]; exact hdk) hd (hk0 _ hr1)
      have hsz' : vtSz v0 (k + 1) = vtRv v0 (k + 1) + 18 := by simp [vtSz]
      have hgo' : vtGout v0 (k + 1) = vtRv v0 (k + 1) + 19 := by simp [vtGout]
      simp only [show k + 1 ≠ 0 by omega, ↓reduceIte]
      refine ⟨by rw [vtRankAt, Nat.add_sub_cancel]; exact hst, ?_, hgin, e8,
        by rw [hsz', e18]⟩
      rw [VtRankFacts, hsz', hgo']
      refine ⟨⟨gi (k + 1), by have := hgi _ hr1; omega, ev⟩, by rw [ev]; exact hside _ hr1,
        by rw [ev, e8]; exact hkey _ hr1, by rw [ev, hgin]; exact hbase _ hr1,
        by rw [ev, e18]; exact hsz _ hr1, by rw [e19, e18], fun h ↦ absurd h (by omega), fun _ ↦ ?_⟩
      refine ⟨d, by omega, ?_⟩
      rw [Nat.add_sub_cancel, hkk, e8, hdk]
  refine ⟨?_, fun r hr ↦ ⟨(P r hr).2.1, (P r hr).2.2.1⟩⟩
  -- the statements, rank by rank
  have hall : ∀ k, k + 1 ≤ m → ∀ st ∈ (vtPre.drop p0).take (13 + 18 * k),
      VSH (coreProgram.Rel rd) rd σv st := by
    intro k
    induction k with
    | zero =>
      intro _ st hst
      have e := tbStmtsEqb_sound (vtPre_drop p0 ▸ h0)
      rw [vtRank0T_length] at e
      have := (P 0 (by omega)).1
      simp only [↓reduceIte] at this
      exact this st (by rw [e]; simpa using hst)
    | succ k ih =>
      intro hk st hst
      rw [show 13 + 18 * (k + 1) = (13 + 18 * k) + 18 by ring] at hst
      refine forall_slice_join (ih (by omega)) ?_ st hst
      intro st' hst'
      have e := tbStmtsEqb_sound (vtPre_drop _ ▸ hr (k + 1) (by omega) (by omega))
      rw [vtRankAt_length, show vtRp p0 (k + 1) = p0 + (13 + 18 * k) by simp [vtRp]; omega] at e
      have := (P (k + 1) (by omega)).1
      simp only [show k + 1 ≠ 0 by omega, ↓reduceIte] at this
      exact this st' (by rw [e]; exact hst')
  exact hall (m - 1) (by omega)

end

end
end LeanVM.Guest.B1.Tables
