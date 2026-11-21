module

public import NativeVm.Code.Phase5.Claim

/-!
# Phase 5's set-up

`pubSetup`, after the challenge `c` (`r9`, `r10`): `c` saved in `r14`, `r15`; `r12` at the first
free claim slot (`claimsR`'s count `n`, slot `n` at word `1 + 76 n`, `76 n` words as three shifts);
the count raised by the two claims; `r13` the point's coordinates `1 + (κ − 1)`, `κ` memory column
`0`'s variable count, `0` without a placement (`vcount`, from `LayoutAt`'s placement words).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters LeanVM.Protocol.Verifier

variable {env : Env} {inp : Input} {s0 s : QState}

/-- The phase's regions. -/
abbrev rs5 : List Region := [claimsR, scratchR]

theorem rs5_regions : ∀ r ∈ rs5, r ∈ regions := by decide +kernel

/-! ## The point's coordinates -/

/-- `r13 := 1 + (κ − 1)`, `κ` the placement's variable count at layout word `16`, `0` without
one. -/
def vcount : Stmt := blk [
  I (.load .rax (at_ .rsi (wdisp (layoutR.off + 16)))),
  I (.movi .r13 0),
  .ite (.cmp .ne .rax (.imm 0)) (blk [I (.load .r13 (at_ .rsi (wdisp (layoutR.off + 17))))])
    (blk []),
  .ite (.cmp .eq .r13 (.imm 0)) (blk [I (.movi .r13 1)]) (blk [])]

theorem cond_eq_zero {s : QState} {r : Reg64} {n : Nat} (h : s.reg r = n.toUInt64)
    (hn : n < 2 ^ 64) : (Cond.cmp .eq r (.imm 0)).eval s = decide (n = 0) := by
  rw [cond_eq, rhs_imm, h, show ((0 : Int64).toUInt64) = (0 : Nat).toUInt64 from rfl]
  by_cases h0 : n = 0
  · subst h0; rfl
  · rw [decide_eq_false h0, beq_eq_false_iff_ne, ne_eq, toUInt64_inj hn (by omega)]
    exact h0

theorem vcount_spec {pl : Option Placement} (hrsi : s.reg .rsi = env.work)
    (hpl : PlacementAt s.mem (wd env.work (layoutR.off + 16)) pl) {E : QState → Prop} :
    WP vcount s (fun s' ↦ s'.mem = s.mem ∧ RegsFrame [.rax, .r13] s s' ∧
      s'.reg .r13 = (1 + ((pl.getD default).variableCount - 1)).toUInt64) E := by
  unfold vcount
  cases pl with
  | none =>
    refine wp_load (eval_work hrsi _) hpl (wp_reg rfl ?_)
    refine WP.blk_cons (wp_ite_false (by reg_simp; rfl) (WP.blk_nil ?_))
    refine WP.blk_cons (wp_ite_true (by reg_simp; rfl) (wp_reg rfl (WP.blk_nil (WP.blk_nil ?_))))
    exact ⟨rfl, by rf_tac, by reg_simp; rfl⟩
  | some p =>
    obtain ⟨h1, ⟨hv1, hv2⟩, -⟩ := hpl
    rw [wd_wd] at hv2
    refine wp_load (eval_work hrsi _) h1 (wp_reg rfl ?_)
    refine WP.blk_cons (wp_ite_true (by reg_simp; rfl)
      (wp_load (eval_work (by reg_simp; exact hrsi) _) (by simpa using hv2) (WP.blk_nil ?_)))
    have hc := cond_eq_zero (s := ((s.setReg .rax 1).setReg .r13 (0 : Int64).toUInt64).setReg .r13
      p.variableCount.toUInt64) (r := .r13) (by reg_simp) hv1
    by_cases h0 : p.variableCount = 0
    · refine WP.blk_cons (wp_ite_true (by rw [hc, h0]; rfl)
        (wp_reg rfl (WP.blk_nil (WP.blk_nil ?_))))
      refine ⟨rfl, by rf_tac, ?_⟩
      reg_simp
      simp [h0]
    · refine WP.blk_cons (wp_ite_false (by rw [hc]; simp [h0]) (WP.blk_nil (WP.blk_nil ?_)))
      refine ⟨rfl, by rf_tac, ?_⟩
      reg_simp
      simp only [Option.getD_some]
      congr 1
      omega

/-! ## The set-up -/

/-- `r14`, `r15 := c`; `r12` at slot `n`; the count `n + 2`; `r13` the point's coordinates. -/
def pubSetup : Stmt := blk [
  I (.mov .r14 .r9), I (.mov .r15 .r10),
  I (.load .rsi (cw ctxWork)),
  I (.load .rax (at_ .rsi (wdisp claimsR.off))),
  I (.mov .rcx .rax), I (.shli .rcx 9), I (.mov .rbx .rax), I (.shli .rbx 6), I (.add .rcx .rbx),
  I (.mov .rbx .rax), I (.shli .rbx 5), I (.add .rcx .rbx),
  I (.lea .r12 (at_ .rsi (wdisp (claimsR.off + 1)))), I (.add .r12 .rcx),
  I (.addi .rax 2), I (.store (at_ .rsi (wdisp claimsR.off)) .rax),
  vcount]

theorem placement_memory0 (layout : LayoutW) :
    layout.placement memory0 = (layout.placements.getD 0 none).getD default := by
  rw [LayoutW.placement, Array.getD_eq_getD_getElem?]
  rfl

theorem slot_sum (n : Nat) :
    n.toUInt64 <<< (9 : Nat).toUInt64 + n.toUInt64 <<< (6 : Nat).toUInt64 +
      n.toUInt64 <<< (5 : Nat).toUInt64 = (8 * (claimWords * n)).toUInt64 := by
  rw [toUInt64_shl _ _ (by omega), toUInt64_shl _ _ (by omega), toUInt64_shl _ _ (by omega),
    toUInt64_add, toUInt64_add, claimWords_val]
  congr 1
  omega

/-- **`pubSetup`.** -/
theorem pubSetup_spec {t : TState} {acc : Array ColumnClaimW} {layout : LayoutW} {rate : Nat}
    {c : EW} (hin : Inputs env inp s0.mem)
    (hlay : LayoutAt s0.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hc : CodeRel env t s) (hb : Base env rs5 s0 s) (hcl : ClaimsAt s.mem (claimsR.at env.work) acc)
    (h9 : s.reg .r9 = c.c0) (h10 : s.reg .r10 = c.c1) {E : QState → Prop} :
    WP pubSetup s (fun s' ↦ CodeRel env t s' ∧ Base env rs5 s0 s' ∧
      s'.reg .r12 = wd env.work (claimsR.off + (1 + claimWords * acc.size)) ∧
      s'.reg .r13 = (1 + ((layout.placement memory0).variableCount - 1)).toUInt64 ∧
      s'.reg .r14 = c.c0 ∧ s'.reg .r15 = c.c1 ∧
      s'.mem (wd env.work claimsR.off) = some (acc.size + 2).toUInt64 ∧
      ∀ k, 0 < k → k < claimsR.size →
        s'.mem (wd env.work (claimsR.off + k)) = s.mem (wd env.work (claimsR.off + k))) E := by
  have hO := claimsR_off
  have hcs := claimsR_size
  have hww := workWords_lt hin
  have hlt : claimsR.off + claimsR.size ≤ 2 ^ 61 := by
    have := region_lt (inp := inp) claimsR_mem (j := claimsR.size - 1) (by omega)
    omega
  have hn : acc.size < 2 ^ 32 := by have := hcl.1; rw [claimCap_val] at this; omega
  have hcnt : s.mem (wd env.work claimsR.off) = some acc.size.toUInt64 := hcl.2.1.2
  have hpl : PlacementAt s.mem (wd env.work (layoutR.off + 16)) (layout.placements.getD 0 none) := by
    have hS := hb.same hin rs5_regions (q := layoutR) (by decide +kernel) (by decide +kernel)
    have := (hlay.placements 0 (by rw [columnCount_val]; omega)).congr
      (hS.sub (a := 16) (m := 3) (by rw [layoutR_size]; omega))
    rwa [Region.at, wd_wd] at this
  unfold pubSetup
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_load_rel (eval_cw (by reg_simp; exact hb.1.1) _) hc.layout.workPtr (by decide) hc hb
    fun hc hb ↦ ?_
  refine wp_load_rel (eval_work (w := env.work) (by reg_simp) _)
    (by simp only [QState.setReg_mem]; exact hcnt) (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_reg_rel rfl (by decide) hc hb fun hc hb ↦ ?_
  refine wp_store_rel (by simp) claimsR_mem hin (j := 0) (by omega)
    ((eval_work (w := env.work) (by reg_simp) _).trans (by rw [Nat.add_zero])) hc hb
    fun hc hb ↦ ?_
  have hL := layoutR_off
  refine wp_then (vcount_spec (by reg_simp) (hpl.congr fun k hk ↦ by
    rw [wd_wd]
    simp (disch := omega) only [setMem_wd_ne, QState.setReg_mem])) fun s' ⟨hm', hf', h13'⟩ ↦ ?_
  have hrdi' : s'.reg .rdi = _ := hf' .rdi (by decide)
  refine wp_done ⟨hc.of_mem hm' hrdi', hb.of_mem hm' hrdi', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf' .r12 (by decide)]
    simp only [QState.setMem_reg, eval_at]
    reg_simp
    rw [wdisp_toUInt64, slot_sum, ← wd_add]
    simp only [wd, Nat.toUInt64_eq, UInt64.ofNat_add, UInt64.ofNat_mul, Nat.mul_add, Nat.mul_one,
      UInt64.add_assoc]
  · rw [h13', placement_memory0]
  · rw [hf' .r14 (by decide)]
    reg_simp
    exact h9
  · rw [hf' .r15 (by decide)]
    reg_simp
    exact h10
  · rw [hm', setMem_wd_eq _ _ (by omega)]
    reg_simp
    rw [show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, toUInt64_add]
  · intro k hk0 hk
    rw [hm']
    simp (disch := omega) only [setMem_wd_ne, QState.setReg_mem]

end NativeVm.Code
