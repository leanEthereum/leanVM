/-
  LeanVM.Guest.B1.Tables.VtC.SP2

  `verify_tables`' statements `563 ..< 765` hold on the honest valuation: the six
  tables' heights and padding weights, `idxc_tab`, `zeta1` and the shared selector tables.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SPads
public import LeanVM.Guest.B1.Tables.VtC.SShT
public import LeanVM.Guest.B1.Tables.VtC.SSortAll

/-!
# Statements `563 ..< 765` (G:2333-2355)

`vtS_p2`: for the bus point (`|point| = μ < 33`), the tables' heights at `kappa_base[2 + t]`,
`τ t = max (log2Ceil (n t)) floor < 29`, `τ t ≤ μ`, on a memory holding `table_rows`, the squares,
`idxc_tab`, `zeta1` and the shared tables, the oracle returning `padding_weight`'s outcomes and
`plus_one_run`'s `0`, every statement holds; the padding weights and `shared_len` are the honest
ones.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open Finset (range)

@[expose] public section

theorem vtPad_read : ∀ t < 5, Atom.load (.n (578 + 13 * t + 4)) (.n 11) t ∉ vtSL := by
  decide +kernel

theorem vtPad5_read : Atom.load (.n (643 + 4)) (.n 11) 5 ∉ vtSL := by decide +kernel

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "σv" => vtσ rd w args

/-- A slice of one hint. -/
theorem vt_hintSlice (n : ℕ) {h : Hint}
    (heq : tbStmtsEqb [.atom (.hint h)] ((vtAt n).take 1) = true) :
    ∀ s ∈ (vtPre.drop n).take 1, VSH (coreProgram.Rel rd) rd σv s := by
  rw [vtPre_drop, ← tbStmtsEqb_sound heq]
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  trivial

/-- A template read at `vtAt`, holding, gives its slice. -/
theorem vt_tmplSlice {P : Stmt → Prop} {n : ℕ} {blk : List Stmt}
    (heq : tbStmtsEqb blk ((vtAt n).take blk.length) = true) (h : ∀ s ∈ blk, P s) :
    ∀ s ∈ (vtPre.drop n).take blk.length, P s := by
  rw [vtPre_drop, ← tbStmtsEqb_sound heq]; exact h

set_option maxRecDepth 10000 in
/-- **Statements `563 ..< 765`.** -/
theorem vtS_p2 (hl : args.length = 20) (hlow : LowDefB 14 rd) (point : List E)
    (hμ33 : point.length < 33) (τ n : ℕ → ℕ)
    (hτ : ∀ t < 6, τ t = max (log2Ceil (n t)) (tableLogFloors.getD t 0))
    (hτ29 : ∀ t < 6, τ t < 29) (hτμ : ∀ t < 6, τ t ≤ point.length)
    (hkb : ∀ t < 6, σv (.n (27 + t)) = gen ^ τ t)
    (hz : TbReadsAt rd (σv (.n 8)) point) (h9 : σv (.n 9) = gen ^ point.length)
    (hrows : ∀ t < 6, LoadHolds rd (σv (.n 11)) t (eOfNat (n t)))
    (hsq : TbReadsAt rd (σv (.n 12)) gSquaresList)
    (hwp : ∀ t < 6, w (vtPadV t) = paddingWeight (point.take (τ t)) (n t) ∧
      w (vtPadV t + 1) = PadLead (τ t) (n t) ∧ w (vtPadV t + 2) = PadRest (τ t) (n t))
    (hidxc : TbReadsAt rd (w 664) vtIdxcW) (hz1 : TbReadsAt rd (w 699) (point.map (1 + ·)))
    (hw704 : w 700 = 0)
    (hrun : ∀ t < 6, RunTables rd (w 701 * gen ^ (288 * t)) (w 702 * gen ^ (144 * t))
      (point.length - τ t) (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t))
      ((gSquaresList.drop (τ t)).take (point.length - τ t))) :
    (∀ s ∈ (vtPre.drop 563).take 202, VSH (coreProgram.Rel rd) rd σv s) ∧
      (∀ t < 6, σv (.n (vtPadV t)) = paddingWeight (point.take (τ t)) (n t)) ∧
      (∀ t < 6, σv (.n (vtShLen t)) = gen ^ (point.length - τ t)) ∧
      σv (.n 664) = w 664 ∧ σv (.n 699) = w 699 ∧
      σv (.n 701) = w 701 ∧ σv (.n 702) = w 702 := by
  have e668 : σv (.n 664) = w 664 := vt_allocAt hl 624 (k := 34) (by decide +kernel)
  have e703 : σv (.n 699) = w 699 := vt_allocDynAt hl 693 (s := .n 9) (by decide +kernel)
  have e705 : σv (.n 701) = w 701 := vt_allocAt hl 695 (k := 1728) (by decide +kernel)
  have e706 : σv (.n 702) = w 702 := vt_allocAt hl 696 (k := 864) (by decide +kernel)
  have hz1' : TbReadsAt rd (σv (.n 699)) (point.map (1 + ·)) := by rw [e703]; exact hz1
  -- the pads
  have hpad : ∀ t < 5, (∀ st ∈ vtPadT (578 + 13 * t) t, VSH (coreProgram.Rel rd) rd σv st) ∧
      σv (.n (578 + 13 * t + 5)) = paddingWeight (point.take (τ t)) (n t) := by
    intro t ht
    have hf : tableLogFloors.getD t 0 = 0 := by interval_cases t <;> rfl
    have hτt := hτ t (by omega)
    rw [hf] at hτt
    obtain ⟨w5, w6, w7⟩ := hwp t (by omega)
    rw [show vtPadV t = 578 + 13 * t + 5 by unfold vtPadV; ring] at w5 w6 w7
    exact pad_ok hlow (vt_goodL hl _ _ (vtPre_drop _ ▸ vtPad_check t ht)) (vtPad_read t ht)
      (hkb t (by omega)) (hrows t (by omega))
      (tbReadsAt_take hz (τ t)) (by simp; exact hτμ t (by omega)) (hτ29 t (by omega))
      (by omega) w5 w6 (by rw [show 578 + 13 * t + 7 = 578 + 13 * t + 5 + 2 by ring]; exact w7)
  have hpad5 : (∀ st ∈ vtPad5T 643, VSH (coreProgram.Rel rd) rd σv st) ∧
      σv (.n (643 + 5)) = paddingWeight (point.take (τ 5)) (n 5) := by
    obtain ⟨w5, w6, w7⟩ := hwp 5 (by norm_num)
    have hm : Stmt.ite (.n (643 + 15)) [] [.atom (.const (.n (643 + 16)) (word 1 0)),
      .atom (.assertEq (.n (643 + 6)) (.n (643 + 16))),
      .atom (.const (.n (643 + 17)) (word 0 0)),
      .atom (.add (.n (643 + 18)) (.n (643 + 7)) (.n (643 + 17))),
      .atom (.hint (.inverse (.n (643 + 18)) (.n (643 + 19)))),
      .atom (.assertNe (.n (643 + 18)) (.n (643 + 19)) (.n (643 + 20)))] ∈ vtPre :=
      vt_mem_slice (vtPre_drop _ ▸ vtPad5_check) (by simp [vtPad5T])
    have hgb := vt_goodIte' (rd := rd) (w := w) hl hm
    rw [List.nil_append] at hgb
    exact pad5_ok hlow (by norm_num) (vt_goodL hl _ _ (vtPre_drop _ ▸ vtPad5_check)) hgb vtPad5_read
      (hkb 5 (by norm_num)) (hrows 5 (by norm_num))
      (tbReadsAt_take hz (τ 5)) (by simp; exact hτμ 5 (by norm_num)) (hτ29 5 (by norm_num))
      (hτ 5 (by norm_num)) w5 w6 w7
  -- the shared tables
  have hsh : ∀ t < 6, (∀ s ∈ (vtPre.drop ([697, 705, 717, 729, 741, 753].getD t 0)).take
        ([8, 12, 12, 12, 12, 12].getD t 0), VSH (coreProgram.Rel rd) rd σv s) ∧
      σv (.n (vtShLen t)) = gen ^ (point.length - τ t) := by
    intro t ht
    have hr := hrun t ht
    rw [← e705, ← e706] at hr
    interval_cases t
    · exact vtc_sh0 hl hlow (hkb 0 (by norm_num)) h9 rfl hμ33 (hτμ 0 (by norm_num)) hz hz1' hsq hr
    · exact vtc_sh1 hl hlow (hkb 1 (by norm_num)) h9 rfl hμ33 (hτμ 1 (by norm_num)) hz hz1' hsq hr
    · exact vtc_sh2 hl hlow (hkb 2 (by norm_num)) h9 rfl hμ33 (hτμ 2 (by norm_num)) hz hz1' hsq hr
    · exact vtc_sh3 hl hlow (hkb 3 (by norm_num)) h9 rfl hμ33 (hτμ 3 (by norm_num)) hz hz1' hsq hr
    · exact vtc_sh4 hl hlow (hkb 4 (by norm_num)) h9 rfl hμ33 (hτμ 4 (by norm_num)) hz hz1' hsq hr
    · exact vtc_sh5 hl hlow (hkb 5 (by norm_num)) h9 rfl hμ33 (hτμ 5 (by norm_num)) hz hz1' hsq hr
  refine ⟨?_, ?_, fun t ht ↦ (hsh t ht).2, e668, e703, e705, e706⟩
  · have s2 : ∀ s ∈ (vtPre.drop 563).take 50, VSH (coreProgram.Rel rd) rd σv s := by
      have := forall_slices (fun t ↦ 563 + 10 * t) (fun _ ↦ 10) 5 (by decide)
        (fun t ht ↦ by
          have h := vt_tmplSlice (vtPad_check t ht) (hpad t ht).1
          rwa [show (vtPadT (578 + 13 * t) t).length = 10 from rfl] at h)
      simpa using this
    have s3 : ∀ s ∈ (vtPre.drop 613).take 11, VSH (coreProgram.Rel rd) rd σv s :=
      vt_tmplSlice vtPad5_check hpad5.1
    have s4 := vt_hintSlice (rd := rd) (w := w) (args := args) 624 (h := .alloc (.n 664) 34) (by decide +kernel)
    have s5 : ∀ s ∈ (vtPre.drop 625).take 68, VSH (coreProgram.Rel rd) rd σv s := by
      have h := vt_tmplSlice vtIdxc_check (idxc_ok hl (by rw [e668]; exact hidxc))
      rwa [show vtIdxcT.length = 68 by decide +kernel] at h
    have s6 := vt_hintSlice (rd := rd) (w := w) (args := args) 693 (h := .allocDyn (.n 699) (.n 9))
      (by decide +kernel)
    have s7 : ∀ s ∈ (vtPre.drop 694).take 1, VSH (coreProgram.Rel rd) rd σv s := by
      have h := vt_tmplSlice (P := VSH (coreProgram.Rel rd) rd σv) vtZeta1_check (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst hs
        exact zeta1_ok hl h9 (by omega) hz hz1' hw704)
      exact h
    have s8 := vt_hintSlice (rd := rd) (w := w) (args := args) 695 (h := .alloc (.n 701) 1728)
      (by decide +kernel)
    have s9 := vt_hintSlice (rd := rd) (w := w) (args := args) 696 (h := .alloc (.n 702) 864)
      (by decide +kernel)
    have s10 : ∀ s ∈ (vtPre.drop 697).take 68, VSH (coreProgram.Rel rd) rd σv s := by
      have := forall_slices (fun t ↦ [697, 705, 717, 729, 741, 753].getD t 0)
        (fun t ↦ [8, 12, 12, 12, 12, 12].getD t 0) 6 (by decide)
        (fun t ht ↦ (hsh t ht).1)
      rwa [show ∑ t ∈ range 6, [8, 12, 12, 12, 12, 12].getD t 0 = 68 by decide] at this
    have j2 := forall_slice_join (a := 563) (l1 := 50) (l2 := 11) s2 s3
    have j3 := forall_slice_join (a := 563) (l1 := 61) (l2 := 1) j2 s4
    have j4 := forall_slice_join (a := 563) (l1 := 62) (l2 := 68) j3 s5
    have j5 := forall_slice_join (a := 563) (l1 := 130) (l2 := 1) j4 s6
    have j6 := forall_slice_join (a := 563) (l1 := 131) (l2 := 1) j5 s7
    have j7 := forall_slice_join (a := 563) (l1 := 132) (l2 := 1) j6 s8
    have j8 := forall_slice_join (a := 563) (l1 := 133) (l2 := 1) j7 s9
    exact forall_slice_join (a := 563) (l1 := 134) (l2 := 68) j8 s10
  · intro t ht
    rcases Nat.lt_or_ge t 5 with h5 | h5
    · rw [show vtPadV t = 578 + 13 * t + 5 by unfold vtPadV; ring]; exact (hpad t h5).2
    · obtain rfl : t = 5 := by omega
      exact hpad5.2

end

end
end LeanVM.Guest.B1.Tables
