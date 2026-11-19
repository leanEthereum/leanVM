module

public import NativeVm.Code.Phase6.FirstKit

/-!
# Phase 6's start: the scratch, then `KECCAK`'s evaluations

`setup_st`: `ldSb` from a state of the model gives a state of phase 6, its scratch whatever the
memory holds there (`scrOf`). `cpyC` copies `KECCAK`'s point (`30` elements, `0` past its end) to
`eInst` and its size to `eInstN`, its output lanes' evaluations (`keccakOut + l`, `l < 25`) to
`eOut`, and `packBits` (`KECCAK`'s log-height minus `4`, truncated) to `ePB` (`pure_cpy`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wdisp Env cw ctxWork)
open NativeVm.Field (eOf eOf_zero)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-! ## The scratch from memory -/

/-- The scratch at `p` in `mem`, element by element. -/
def scrOf (mem : UInt64 → Option UInt64) (p : UInt64) (k : Nat) : EW :=
  ⟨(mem (wd p (2 * k))).getD 0, (mem (wd p (2 * k + 1))).getD 0⟩

theorem scr_scrOf (hin : Inputs env inp s0.mem) : Scr s0.mem (sb env) (scrOf s0.mem (sb env)) := by
  have hN := scrN_val
  intro k hk
  have h0 := hin.workSome _ (scratch_in_work (inp := inp) (k := 2 * k) (by omega))
  have h1 := hin.workSome _ (scratch_in_work (inp := inp) (k := 2 * k + 1) (by omega))
  rw [← sb_wd] at h0 h1
  obtain ⟨v0, e0⟩ := Option.isSome_iff_exists.mp h0
  obtain ⟨v1, e1⟩ := Option.isSome_iff_exists.mp h1
  simp only [scrOf, e0, e1, Option.getD_some]
  exact ⟨trivial, trivial⟩

/-- **`ldSb` from the model's state**: a state of phase 6. -/
theorem setup_st (hc : CodeRel env t s0) {xs : List Stmt}
    {P : QState → Prop}
    (k : WP (blk xs) (s0.setReg .rbp (sb env)) P fun _ ↦ False) :
    WP (blk (ldSb ++ xs)) s0 P fun _ ↦ False :=
  ldSb_spec hc hc.rdi k

theorem setup_st' (hin : Inputs env inp s0.mem) (hc : CodeRel env t s0) :
    St env s0 (scrOf s0.mem (sb env)) t (s0.setReg .rbp (sb env)) :=
  ⟨hc.setReg (by decide) _, (Base.start hc.rdi).setReg (by decide) _, by simp,
    (scr_scrOf hin).congr fun _ _ ↦ rfl⟩

/-! ## `KECCAK`'s point's size and `packBits` -/

/-- `(r9, r10) :=` `KECCAK`'s point's size. -/
def instNV : Stmt := blk [I (.load .rsi (cw ctxWork)), I (.load .r9 (at_ .rsi (wdisp evK))),
  I (.movi .r10 0)]

theorem pure_instN (hin : Inputs env inp s0.mem) {ev : Array (Array EW × Array EW)}
    (hev : EvalsAt s0.mem (evalsR.at env.work) ev) :
    Pure6 env s0 (blk (instNV :: stEl eInstN)) g
      (Function.update g eInstN (EW.ofK (ev.getD opKeccak (#[], #[])).1.size.toUInt64)) :=
  pure_elS hin (L := [.rsi, .r9, .r10]) (by p6_omega) (by decide) fun _ s h ↦ by
    have hv := (evalsK_st hin hev h.2.1).1
    unfold instNV
    refine NativeVm.Transcript.wp_load (NativeVm.Transcript.eval_cw h.2.1.1.1 _)
      h.1.layout.workPtr ?_
    refine NativeVm.Transcript.wp_load (eval_work (w := env.work) (by simp) _)
      (by rw [QState.setReg_mem]; exact hv.2.1.2) ?_
    refine NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_)
    refine ⟨?_, rfl, by rf_tac⟩
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rfl

/-- `(r9, r10) :=` `packBits`: `KECCAK`'s log-height minus `4`, `0` below `4`. -/
def pbV : Stmt := blk [I (.load .rsi (cw ctxWork)),
  I (.load .rax (at_ .rsi (wdisp (layoutR.off + 9)))),
  .ite (.cmp .ltu .rax (.imm 4)) (I (.movi .r9 0)) (blk [I (.mov .r9 .rax), I (.subi .r9 4)]),
  I (.movi .r10 0)]

theorem toUInt64_sub' {a b : Nat} (ha : a < 2 ^ 64) (h : b ≤ a) :
    a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hb : b < 2 ^ 64 := by omega
  have hab : a - b < 2 ^ 64 := by omega
  rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, toNat_toUInt64' hb, toNat_toUInt64' ha]; exact h),
    toNat_toUInt64' hb, toNat_toUInt64' ha, toNat_toUInt64' hab]

theorem pure_pb (hin : Inputs env inp s0.mem) {layout : LayoutW} {rate : Nat}
    (hlay : LayoutAt s0.mem (layoutR.at env.work) inp.bytecode layout rate) :
    Pure6 env s0 (blk (pbV :: stEl ePB)) g
      (Function.update g ePB (EW.ofK (layout.tableLogHeights.getD opKeccak 0 - 4).toUInt64)) :=
  pure_elS hin (L := [.rsi, .rax, .r9, .r10]) (by p6_omega) (by decide) fun _ s h ↦ by
    obtain ⟨hlt, hv⟩ := heightK_st hin hlay h.2.1
    have hbd := hlay.heightsBound 5 (by decide)
    unfold pbV
    refine NativeVm.Transcript.wp_load (NativeVm.Transcript.eval_cw h.2.1.1.1 _)
      h.1.layout.workPtr ?_
    refine NativeVm.Transcript.wp_load (eval_work (w := env.work) (by simp) _)
      (by rw [QState.setReg_mem]; exact hv) ?_
    apply WP.blk_cons
    apply WP.ite
    generalize layout.tableLogHeights.getD opKeccak 0 = h4 at hlt hbd ⊢
    unfold tablePointCap at hbd
    by_cases h0 : h4 < 4
    · have hc : decide (h4.toUInt64 < (4 : Int64).toUInt64) = true := by
        rw [decide_eq_true_eq]
        exact (toUInt64_lt' (b := 4) (by omega) (by omega)).mpr h0
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte, hc]
      refine WP.ins (by rfl) (NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_))
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [show h4 - 4 = 0 by omega]
      rfl
    · have hc : decide (h4.toUInt64 < (4 : Int64).toUInt64) = false := by
        rw [decide_eq_false_iff_not]
        exact fun e ↦ h0 ((toUInt64_lt' (b := 4) (by omega) (by omega)).mp e)
      simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte, hc, Bool.false_eq_true]
      refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
        (WP.blk_nil (NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_))))
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [show (4 : Int64).toUInt64 = (4 : Nat).toUInt64 from rfl, toUInt64_sub' (by omega) (by omega)]
      rfl

/-! ## The copy -/

theorem keccakOut_val' : keccakOut = 40 := by decide +kernel

/-- `KECCAK`'s point and its size, its output lanes' evaluations, `packBits`. -/
def cpyC : List Stmt := [blk (instNV :: stEl eInstN),
  blk [I (.movi .r14 0), tab eInst (.imm (Int64.ofNat 30)) (vecEl evK 0)],
  blk [I (.movi .r14 0), tab eOut (.imm (Int64.ofNat 25)) (vecEl evKV 40)],
  blk (pbV :: stEl ePB)]

theorem pure_cpy (hin : Inputs env inp s0.mem) {layout : LayoutW} {rate : Nat}
    {ev : Array (Array EW × Array EW)}
    (hlay : LayoutAt s0.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hev : EvalsAt s0.mem (evalsR.at env.work) ev) (g : Nat → EW) :
    ∃ g', Pure6 env s0 (blk cpyC) g g' ∧
      (∀ i, ¬ (i = eInstN ∨ i = ePB ∨ (eInst ≤ i ∧ i < eInst + 32) ∨ (eOut ≤ i ∧ i < eOut + 25)) →
        g' i = g i) ∧
      g' eInstN = EW.ofK (ev.getD opKeccak (#[], #[])).1.size.toUInt64 ∧
      (∀ i < 30, g' (eInst + i) = (ev.getD opKeccak (#[], #[])).1.getD i 0) ∧
      (∀ l < 25, g' (eOut + l) = (ev.getD opKeccak (#[], #[])).2.getD (keccakOut + l) 0) ∧
      g' ePB = EW.ofK (layout.tableLogHeights.getD opKeccak 0 - 4).toUInt64 := by
  set pt := (ev.getD opKeccak (#[], #[])).1
  set vs := (ev.getD opKeccak (#[], #[])).2
  set g1 := Function.update g eInstN (EW.ofK pt.size.toUInt64)
  set g2 := ovr g1 eInst 30 fun m ↦ pt.getD (0 + m) 0
  set g3 := ovr g2 eOut 25 fun m ↦ vs.getD (40 + m) 0
  have p2 : Pure6 env s0 (blk [I (.movi .r14 0), tab eInst (.imm (Int64.ofNat 30)) (vecEl evK 0)])
      g1 g2 :=
    pure_tabS hin (Lv := vRegs) (by p6_omega) (by decide) fun m hm _ s h h15 ↦
      vecEl_spec h.1 h.2.1.1.1 (evalsK_st hin hev h.2.1).1 h15 (by omega)
  have p3 : Pure6 env s0 (blk [I (.movi .r14 0), tab eOut (.imm (Int64.ofNat 25)) (vecEl evKV 40)])
      g2 g3 :=
    pure_tabS hin (Lv := vRegs) (by p6_omega) (by decide) fun m hm _ s h h15 ↦
      vecEl_spec h.1 h.2.1.1.1 (evalsK_st hin hev h.2.1).2 h15 (by omega)
  refine ⟨_, Pure6.cons (pure_instN hin hev) (Pure6.cons p2 (Pure6.cons p3
    (Pure6.single (pure_pb hin hlay)))), fun i hi ↦ ?_, ?_, fun i hi ↦ ?_, fun l hl ↦ ?_, ?_⟩
  · simp only [not_or, not_and, Nat.not_lt] at hi
    simp only [g3, g2, g1]
    rw [Function.update_of_ne hi.2.1, ovr_out (by p6_omega), ovr_out (by p6_omega),
      Function.update_of_ne hi.1]
  · simp only [g3, g2, g1]
    rw [Function.update_of_ne (by p6_ne), ovr_out (by p6_omega), ovr_out (by p6_omega),
      Function.update_self]
  · simp only [g3, g2]
    rw [Function.update_of_ne (by p6_omega), ovr_out (by p6_omega), ovr_in (by p6_omega)
      (by p6_omega), Nat.add_sub_cancel_left, Nat.zero_add]
  · simp only [g3]
    rw [Function.update_of_ne (by p6_omega), ovr_in (by p6_omega) (by p6_omega),
      Nat.add_sub_cancel_left, keccakOut_val']
  · rw [Function.update_self]

end NativeVm.Code.P6
