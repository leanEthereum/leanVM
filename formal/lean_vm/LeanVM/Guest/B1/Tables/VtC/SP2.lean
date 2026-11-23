/-
  LeanVM.Guest.B1.Tables.VtC.SP2

  `verify_tables`' statements `s17.u0.s0#0 ..< block_index_mle` hold on the honest valuation: the six
  tables' shared tables' allocations, heights and padding weights, `idxc_tab`, `zeta1` and the shared
  selector tables.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SPads
public import LeanVM.Guest.B1.Tables.VtC.SShared
public import LeanVM.Guest.B1.Tables.VtC.SSortAll
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# Statements `s17.u0.s0#0 ..< block_index_mle`

`vtS_p2`: for the bus point (`|point| = μ < 33`), the tables' heights at `kappa_base[2 + t]`,
`τ t = max (log2Ceil (n t)) floor < 31`, `τ t ≤ μ`, on a memory holding `table_rows`, the squares,
`idxc_tab`, `zeta1` and the shared tables, the oracle returning `padding_weight`'s outcomes and
`plus_one_run`'s `0`, every statement holds; the padding weights, `shared_len` and the shared
tables' sizes and pointers are the honest ones.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open Finset (range)

@[expose] public section

theorem vtPad_read : ∀ t < 5, Atom.load (.n (681 + 13 * t + 4)) (.n (val% «verify_tables» "table_rows")) t ∉ vtSL := by
  decide +kernel

theorem vtPad5_read : Atom.load (.n (val% «verify_tables» "rows@6")) (.n (val% «verify_tables» "table_rows")) 5 ∉ vtSL := by decide +kernel

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

local notation "σv" => vtσ rd w args

/-- A slice of one hint. -/
theorem vt_hintSlice (n : ℕ) {h : Hint}
    (heq : stmtsEqb [.atom (.hint h)] ((vtAt n).take 1) = true) :
    ∀ s ∈ (vtPre.drop n).take 1, VSH (coreProgram.Rel rd) rd σv s := by
  rw [vtPre_drop, ← stmtsEqb_sound heq]
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  trivial

/-- A template read at `vtAt`, holding, gives its slice. -/
theorem vt_tmplSlice {P : Stmt → Prop} {n : ℕ} {blk : List Stmt}
    (heq : stmtsEqb blk ((vtAt n).take blk.length) = true) (h : ∀ s ∈ blk, P s) :
    ∀ s ∈ (vtPre.drop n).take blk.length, P s := by
  rw [vtPre_drop, ← stmtsEqb_sound heq]; exact h

set_option maxRecDepth 10000 in
/-- **Statements `s17.u0.s0#0 ..< block_index_mle`.** -/
theorem vtS_p2 (hl : args.length = 21) (hlow : LowDefB 14 rd) (point : List E)
    (hμ33 : point.length < 33) (τ n : ℕ → ℕ)
    (hτ : ∀ t < 6, τ t = max (log2Ceil (n t)) (tableLogFloors.getD t 0))
    (hτ31 : ∀ t < 6, τ t < 31) (hτμ : ∀ t < 6, τ t ≤ point.length)
    (hkb : ∀ t < 6, σv (.n ((val% «verify_tables» "kb[2]") + t)) = gen ^ τ t)
    (hz : ReadsAt rd (σv (.n (val% «verify_tables» "zeta"))) point) (h9 : σv (.n (val% «verify_tables» "g_bus_mu")) = gen ^ point.length)
    (hrows : ∀ t < 6, LoadHolds rd (σv (.n (val% «verify_tables» "table_rows"))) t (eOfNat (n t)))
    (hsq : ReadsAt rd (σv (.n (val% «verify_tables» "g_squares"))) gSquaresList)
    (hwp : ∀ t < 6, w (vtPadV t) = paddingWeight (point.take (τ t)) (n t) ∧
      w (vtPadV t + 1) = PadLead (τ t) (n t) ∧ w (vtPadV t + 2) = PadRest (τ t) (n t))
    (hidxc : ReadsAt rd (w 767) vtIdxcW) (hz1 : ReadsAt rd (w 802) (point.map (1 + ·)))
    (hw704 : w 803 = 0)
    (hrun : ∀ t < 6, RunTables rd (w (vtShV t + 11)) (w (vtShV t + 15))
      (point.length - τ t) (point.drop (τ t)) ((point.map (1 + ·)).drop (τ t))
      ((gSquaresList.drop (τ t)).take (point.length - τ t)))
    (hrpad : ∀ t < 6, RunPads rd (w (vtShV t + 11)) (w (vtShV t + 15))
      (point.length - τ t) (point.drop (τ t))) :
    (∀ s ∈ (vtPre.drop (pos% «verify_tables» "s17.u0.s0#0")).take (span% «verify_tables» "s17.u0.s0#0" "block_index_mle"), VSH (coreProgram.Rel rd) rd σv s) ∧
      (∀ t < 6, σv (.n (vtPadV t)) = paddingWeight (point.take (τ t)) (n t)) ∧
      (∀ t < 6, σv (.n (vtShLen t)) = gen ^ (point.length - τ t)) ∧
      σv (.n (val% «verify_tables» "idxc_tab")) = w 767 ∧ σv (.n (val% «verify_tables» "zeta1")) = w 802 ∧
      (∀ t < 6, σv (.n (vtShV t + 10)) = gen ^ (8 * (point.length - τ t + 1)) ∧
        σv (.n (vtShV t + 14)) = gen ^ (4 * (point.length - τ t + 1))) ∧
      ∀ t < 6, σv (.n (vtEqV t)) = w (vtShV t + 11) ∧ σv (.n (vtGV t)) = w (vtShV t + 15) := by
  have e668 : σv (.n (val% «verify_tables» "idxc_tab")) = w 767 := vt_allocAt hl 714 (k := 34) (by decide +kernel)
  have e703 : σv (.n (val% «verify_tables» "zeta1")) = w 802 := vt_allocDynAt hl 783 (s := .n (val% «verify_tables» "g_bus_mu")) (by decide +kernel)
  have hz1' : ReadsAt rd (σv (.n (val% «verify_tables» "zeta1"))) (point.map (1 + ·)) := by rw [e703]; exact hz1
  -- the pads
  have hpad : ∀ t < 5, (∀ st ∈ vtPadT (681 + 13 * t) t, VSH (coreProgram.Rel rd) rd σv st) ∧
      σv (.n (681 + 13 * t + 5)) = paddingWeight (point.take (τ t)) (n t) := by
    intro t ht
    have hf : tableLogFloors.getD t 0 = 0 := by interval_cases t <;> rfl
    have hτt := hτ t (by omega)
    rw [hf] at hτt
    obtain ⟨w5, w6, w7⟩ := hwp t (by omega)
    rw [show vtPadV t = 681 + 13 * t + 5 by unfold vtPadV; ring] at w5 w6 w7
    exact pad_ok hlow (vt_goodL hl _ _ (vtPre_drop _ ▸ vtPad_check t ht)) (vtPad_read t ht)
      (hkb t (by omega)) (hrows t (by omega))
      (tbReadsAt_take hz (τ t)) (by simp; exact hτμ t (by omega)) (hτ31 t (by omega))
      (by omega) w5 w6 (by rw [show 681 + 13 * t + 7 = 681 + 13 * t + 5 + 2 by ring]; exact w7)
  have hpad5 : (∀ st ∈ vtPad5T 746, VSH (coreProgram.Rel rd) rd σv st) ∧
      σv (.n (val% «verify_tables» "pad_weight[5]")) = paddingWeight (point.take (τ 5)) (n 5) := by
    obtain ⟨w5, w6, w7⟩ := hwp 5 (by norm_num)
    have hm : Stmt.ite (.n (val% «verify_tables» "s19.u5.s4.e.s1#1")) [] [.atom (.const (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s0#0")) (word 1 0)),
      .atom (.assertEq (.n (val% «verify_tables» "lead@6")) (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s0#0"))),
      .atom (.const (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s1#0")) (word 0 0)),
      .atom (.add (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s1#1")) (.n (val% «verify_tables» "rest@6")) (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s1#0"))),
      .atom (.hint (.inverse (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s1#1")) (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s1#2")))),
      .atom (.assertNe (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s1#1")) (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s1#2")) (.n (val% «verify_tables» "s19.u5.s4.e.s1.t.s1#3")))] ∈ vtPre :=
      vt_mem_slice (vtPre_drop _ ▸ vtPad5_check) (by simp [vtPad5T])
    have hgb := vt_goodIte' (rd := rd) (w := w) hl hm
    rw [List.nil_append] at hgb
    exact pad5_ok hlow (by norm_num) (vt_goodL hl _ _ (vtPre_drop _ ▸ vtPad5_check)) hgb vtPad5_read
      (hkb 5 (by norm_num)) (hrows 5 (by norm_num))
      (tbReadsAt_take hz (τ 5)) (by simp; exact hτμ 5 (by norm_num)) (hτ31 5 (by norm_num))
      (hτ 5 (by norm_num)) w5 w6 w7
  -- the shared tables
  -- the shared tables
  have hA := fun t (ht : t < 6) ↦ vtc_shA (w := w) hl hlow ht (hkb t ht) h9 hμ33 (hτμ t ht)
  have hC : ∀ t < 6, ∀ s ∈ (vtPre.drop (vtShC t)).take 4, VSH (coreProgram.Rel rd) rd σv s := by
    intro t ht
    obtain ⟨-, hlen, -, -, pe, pg⟩ := hA t ht
    have hr := hrun t ht
    have hp := hrpad t ht
    rw [← pe, ← pg] at hr hp
    exact vtc_shC hl ht rfl hμ33 (hτμ t ht) (hkb t ht) hlen hz hz1' hsq hr hp
  refine ⟨?_, ?_, fun t ht ↦ (hA t ht).2.1, e668, e703, fun t ht ↦ ⟨(hA t ht).2.2.1, (hA t ht).2.2.2.1⟩,
    fun t ht ↦ (hA t ht).2.2.2.2⟩
  · have s1 : ∀ s ∈ (vtPre.drop (pos% «verify_tables» "s17.u0.s0#0")).take (span% «verify_tables» "s17.u0.s0#0" "s19.u0.s1#0"), VSH (coreProgram.Rel rd) rd σv s := by
      have := forall_slices (fun t ↦ 563 + 15 * t) (fun _ ↦ 15) 6 (by decide)
        (fun t ht ↦ (hA t ht).1)
      simpa using this
    have s2 : ∀ s ∈ (vtPre.drop (pos% «verify_tables» "s19.u0.s1#0")).take (span% «verify_tables» "s19.u0.s1#0" "s19.u5.s1#0"), VSH (coreProgram.Rel rd) rd σv s := by
      have := forall_slices (fun t ↦ 653 + 10 * t) (fun _ ↦ 10) 5 (by decide)
        (fun t ht ↦ by
          have h := vt_tmplSlice (vtPad_check t ht) (hpad t ht).1
          rwa [show (vtPadT (681 + 13 * t) t).length = 10 from rfl] at h)
      simpa using this
    have s3 : ∀ s ∈ (vtPre.drop (pos% «verify_tables» "s19.u5.s1#0")).take (span% «verify_tables» "s19.u5.s1#0" "idxc_tab"), VSH (coreProgram.Rel rd) rd σv s :=
      vt_tmplSlice vtPad5_check hpad5.1
    have s4 := vt_hintSlice (rd := rd) (w := w) (args := args) 714 (h := .alloc (.n (val% «verify_tables» "idxc_tab")) 34) (by decide +kernel)
    have s5 : ∀ s ∈ (vtPre.drop (pos% «verify_tables» "s21.u0.s0#0")).take (span% «verify_tables» "s21.u0.s0#0" "zeta1"), VSH (coreProgram.Rel rd) rd σv s := by
      have h := vt_tmplSlice vtIdxc_check (idxc_ok hl (by rw [e668]; exact hidxc))
      rwa [show vtIdxcT.length = 68 by decide +kernel] at h
    have s6 := vt_hintSlice (rd := rd) (w := w) (args := args) 783 (h := .allocDyn (.n (val% «verify_tables» "zeta1")) (.n (val% «verify_tables» "g_bus_mu")))
      (by decide +kernel)
    have s7 : ∀ s ∈ (vtPre.drop (pos% «verify_tables» "zeta1_done")).take 1, VSH (coreProgram.Rel rd) rd σv s := by
      have h := vt_tmplSlice (P := VSH (coreProgram.Rel rd) rd σv) vtZeta1_check (by
        intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst hs
        exact zeta1_ok hl h9 (by omega) hz hz1' hw704)
      exact h
    have s8 : ∀ s ∈ (vtPre.drop (pos% «verify_tables» "s24.u0.s1#0")).take (span% «verify_tables» "s24.u0.s1#0" "block_index_mle"), VSH (coreProgram.Rel rd) rd σv s := by
      have := forall_slices (fun t ↦ 785 + 4 * t) (fun _ ↦ 4) 6 (by decide) hC
      simpa using this
    have j1 := forall_slice_join (a := 563) (l1 := 90) (l2 := 50) s1 s2
    have j2 := forall_slice_join (a := 563) (l1 := 140) (l2 := 11) j1 s3
    have j3 := forall_slice_join (a := 563) (l1 := 151) (l2 := 1) j2 s4
    have j4 := forall_slice_join (a := 563) (l1 := 152) (l2 := 68) j3 s5
    have j5 := forall_slice_join (a := 563) (l1 := 220) (l2 := 1) j4 s6
    have j6 := forall_slice_join (a := 563) (l1 := 221) (l2 := 1) j5 s7
    exact forall_slice_join (a := 563) (l1 := 222) (l2 := 24) j6 s8
  · intro t ht
    rcases Nat.lt_or_ge t 5 with h5 | h5
    · rw [show vtPadV t = 681 + 13 * t + 5 by unfold vtPadV; ring]; exact (hpad t h5).2
    · obtain rfl : t = 5 := by omega
      exact hpad5.2

end

end
end LeanVM.Guest.B1.Tables
