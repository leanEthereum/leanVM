module

public import NativeVm.Code.Phase3.BcMleCarry

/-!
# The bytecode's multilinear extension: one word

`bcWord` reads word `i` of the bytecode, carries it up the stack while the counter's bits are set
and stores it at the first clear bit (`bcWord_spec`): the stack of `i` words (`BcStack`) becomes the
stack of `i + 1`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code
open LeanVM.Parameters

/-- The bytecode's words as the statement's table. -/
def bcL (bc : Array UInt64) : List E := (bc.map EW.ofK).toList.map EW.toE

theorem bcL_getD {bc : Array UInt64} {i : Nat} (h : i < bc.size) : (bcL bc).getD i 0 = eOf bc[i] 0 := by
  rw [bcL, List.getD_eq_getElem _ _ (by simpa using h)]
  simp
  rfl

/-- The stack after `i` words: level `l` holds the pending left node when bit `l` of `i` is set. -/
def BcStack (mem : UInt64 → Option UInt64) (work : UInt64) (L R : List E) (m i : Nat) : Prop :=
  ∀ l ≤ m, i / 2 ^ l % 2 = 1 →
    SAt mem (wd work (bcStW + 2 * l)) (bcNode L R l (2 * (i / 2 ^ (l + 1))))

theorem bc_and1 {n : Nat} (hn : n < 2 ^ 64) : n.toUInt64 &&& 1 = (n % 2).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, Transcript.toNat_toUInt64 hn, Transcript.toNat_toUInt64 (by omega),
    show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]

theorem bc_test_bit {u : QState} {r : Reg64} {n : Nat} (h : u.reg r = n.toUInt64) (hn : n < 2 ^ 64) :
    (Cond.test false r (.imm 1)).eval u = decide (n % 2 = 1) := by
  simp only [Cond.eval, Rhs.eval, h, int64One_toUInt64, bc_and1 hn]
  rcases Nat.mod_two_eq_zero_or_one n with e | e <;> rw [e] <;> rfl

theorem bc_getD_toE {pt : Array EW} {l : Nat} (h : l < pt.size) :
    (pt.toList.map EW.toE).getD l 0 = pt[l].toE := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem bc_mem2 (u : QState) (p : UInt64) {a k : Nat} (v0 v1 : UInt64) (ha : a + 1 < 2 ^ 61)
    (hk : k < 2 ^ 61) :
    ((u.setMem (wd p a) v0).setMem (wd p (a + 1)) v1).mem (wd p k) =
      if k = a then some v0 else if k = a + 1 then some v1 else u.mem (wd p k) := by
  simp only [QState.setMem_mem, wd_inj hk ha, wd_inj hk (show a < 2 ^ 61 by omega)]
  by_cases h1 : k = a
  · subst h1; simp
  · by_cases h2 : k = a + 1 <;> simp [h1, h2]

theorem bc_mem2_ne (u : QState) (p : UInt64) {a k : Nat} (v0 v1 : UInt64) (ha : a + 1 < 2 ^ 61)
    (hk : k < 2 ^ 61) (h0 : k ≠ a) (h1 : k ≠ a + 1) :
    ((u.setMem (wd p a) v0).setMem (wd p (a + 1)) v1).mem (wd p k) = u.mem (wd p k) := by
  rw [bc_mem2 u p v0 v1 ha hk]; simp [h0, h1]

theorem bc_mem2_0 (u : QState) (p : UInt64) {a : Nat} (v0 v1 : UInt64) (ha : a + 1 < 2 ^ 61) :
    ((u.setMem (wd p a) v0).setMem (wd p (a + 1)) v1).mem (wd p a) = some v0 := by
  rw [bc_mem2 u p v0 v1 ha (by omega)]; simp

theorem bc_mem2_1 (u : QState) (p : UInt64) {a : Nat} (v0 v1 : UInt64) (ha : a + 1 < 2 ^ 61) :
    ((u.setMem (wd p a) v0).setMem (wd p (a + 1)) v1).mem (wd p (a + 1)) = some v1 := by
  rw [bc_mem2 u p v0 v1 ha ha]; simp

variable {env : Env} {inp : Input} {s0 s : QState}

/-- **One word**: the stack of `i` words becomes the stack of `i + 1`. -/
theorem bcWord_spec {pt : Array EW} {m i : Nat} {F : QState → Prop} (hw : Wrote env [tmpR] s0 s)
    (hi : Inputs env inp s0.mem) (hrdi : s0.reg .rdi = env.ctx)
    (hwk : s0.mem (wd env.ctx ctxWork) = some env.work) (hm : pt.size = m) (hm34 : m ≤ 34)
    (hbc : 2 ^ m ≤ inp.bytecode.size) (hi' : i < 2 ^ m)
    (h13 : s.reg .r13 = wd inp.bcA i) (hbp : s.reg .rbp = i.toUInt64)
    (h14 : s.reg .r14 = (2 ^ m - i).toUInt64) (hpt : EWArr s.mem (wd env.work bcPtW) pt)
    (hst : BcStack s.mem env.work (bcL inp.bytecode) (pt.toList.map EW.toE) m i) :
    WP bcWord s (fun s' ↦ Wrote env [tmpR] s0 s' ∧ s'.reg .r13 = wd inp.bcA (i + 1) ∧
      s'.reg .rbp = (i + 1).toUInt64 ∧ s'.reg .r14 = (2 ^ m - (i + 1)).toUInt64 ∧
      EWArr s'.mem (wd env.work bcPtW) pt ∧
      BcStack s'.mem env.work (bcL inp.bytecode) (pt.toList.map EW.toE) m (i + 1)) F := by
  set L := bcL inp.bytecode
  set R := pt.toList.map EW.toE
  have hww := bc_work_le hi
  have hpm : 2 ^ m ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hm34
  have hsz : i < inp.bytecode.size := by omega
  unfold bcWord
  refine wp_load (bc_eval0 h13) (bc_word hw hi hsz) ?_
  fstep; fstep
  refine wp_load (eval_cw (by rsimp; exact hw.rdi.trans hrdi) _)
    (by rsimp; rw [bc_ctx hw hi (by lay_omega)]; exact hwk) ?_
  fstep
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ l ≤ m, i % 2 ^ l = 2 ^ l - 1 ∧ u.reg .r15 = (i / 2 ^ l).toUInt64 ∧
      u.reg .rsi = wd env.work (bcStW + 2 * l) ∧
      eOf (u.reg .r9) (u.reg .r10) = bcNode L R l (i / 2 ^ l) ∧ u.mem = s.mem ∧
      u.reg .r13 = s.reg .r13 ∧ u.reg .rbp = s.reg .rbp ∧ u.reg .r14 = s.reg .r14 ∧
      u.reg .rdi = s.reg .rdi)
    (fun u ↦ (u.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, by rw [pow_zero, Nat.mod_one]; rfl, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩ <;> rsimp
    · rw [hbp, pow_zero, Nat.div_one]
    · rw [wdisp_toUInt64]; rfl
    · rw [pow_zero, Nat.div_one, bcNode, bcL_getD hsz]
  · rintro u ⟨l, hl, hlow, u15, usi, uv, um, u13, ubp, u14, urdi⟩ hc
    have hil : i / 2 ^ l < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [bc_test_bit u15 hil, decide_eq_true_iff] at hc
    have hlm : l < m := bc_bit_lt hi' hc
    obtain ⟨S0, S1⟩ := hst l hl hc
    have hpl := hpt l (by omega)
    rw [wd_wd] at hpl
    refine WP.mono (bcCarry_spec (S := bcNode L R l (2 * (i / 2 ^ (l + 1)))) (r := pt[l]) usi
      ⟨by rw [um]; exact S0, by rw [um]; exact S1⟩ (by rw [um]; exact hpl) u15 hil)
      (fun u' ⟨m', v', si', r15', f'⟩ ↦ ⟨⟨l + 1, hlm, bc_low_succ hlow hc, ?_, si', ?_, m'.trans um,
        ?_, ?_, ?_, ?_⟩, ?_⟩) (fun _ h ↦ h)
    · rw [r15', Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [v', uv, ← bc_getD_toE (by omega), bc_carry L R hc]
    · rw [f' .r13 (by simp)]; exact u13
    · rw [f' .rbp (by simp)]; exact ubp
    · rw [f' .r14 (by simp)]; exact u14
    · rw [f' .rdi (by simp)]; exact urdi
    · rw [r15', u15, Transcript.toNat_toUInt64 (lt_of_le_of_lt (Nat.div_le_self _ _) hil),
        Transcript.toNat_toUInt64 hil]
      exact Nat.div_lt_self (Nat.pos_of_ne_zero fun h0 ↦ by rw [h0] at hc; exact absurd hc (by decide))
        (by norm_num)
  · rintro u ⟨l, hl, hlow, u15, usi, uv, um, u13, ubp, u14, urdi⟩ hc
    have hil : i / 2 ^ l < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [bc_test_bit u15 hil, decide_eq_false_iff_not] at hc
    have hc0 : i / 2 ^ l % 2 = 0 := by omega
    have hwu : Wrote env [tmpR] s0 u :=
      ⟨urdi.trans hw.rdi, fun a ha ↦ by rw [um]; exact hw.mem a ha, fun a ↦ by rw [um]; exact hw.dom a⟩
    refine wp_store (bc_eval0 usi) (bc_some hwu hi (by bc_omega)) ?_
    refine wp_store (bc_eval8 (by rsimp; exact usi))
      (by rw [QState.setMem_mem]; split; rfl; exact bc_some hwu hi (by bc_omega)) ?_
    fstep; fstep; fstep; fdone
    have hA : bcStW + 2 * l + 1 < 2 ^ 61 := by bc_omega
    obtain ⟨v0, v1⟩ := eOf_eq_iff.mp uv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (bc_set (bc_set hwu hi (k := bcStW + 2 * l) (by bc_omega) (by bc_omega) _) hi
        (k := bcStW + 2 * l + 1) (by bc_omega) (by bc_omega) _).setReg (r := .r13) (by decide) _
        |>.setReg (r := .rbp) (by decide) _ |>.setReg (r := .r14) (by decide) _
    · rw [u13, h13, bc_wd8]
    · rw [ubp, hbp, toUInt64_succ]
    · rw [u14, h14, show 2 ^ m - i = (2 ^ m - (i + 1)) + 1 by omega, toUInt64_succ_sub]
    · intro j hj
      have := hpt j hj
      simp only [EWAt, wd_wd] at this ⊢
      rw [bc_mem2_ne _ _ _ _ hA (by bc_omega) (by bc_omega) (by bc_omega),
        bc_mem2_ne _ _ _ _ hA (by bc_omega) (by bc_omega) (by bc_omega), um]
      exact this
    · intro l' hl' hb'
      simp only [SAt, wd_wd]
      rcases lt_trichotomy l' l with hlt | rfl | hlt
      · rw [bc_div_succ_low hlow hlt] at hb'; exact absurd hb' (by decide)
      · rw [(bc_div_succ_store hlow hc0).2, bc_mem2_0 _ _ _ _ hA, bc_mem2_1 _ _ _ _ hA, v0, v1]
        exact ⟨rfl, rfl⟩
      · rw [bc_div_succ_high hlow hc0 hlt] at hb'
        rw [bc_div_succ_high hlow hc0 (by omega : l < l' + 1)]
        obtain ⟨w0, w1⟩ := hst l' hl' hb'
        rw [wd_wd] at w1
        rw [bc_mem2_ne _ _ _ _ hA (by bc_omega) (by omega) (by omega),
          bc_mem2_ne _ _ _ _ hA (by bc_omega) (by omega) (by omega), um]
        exact ⟨w0, w1⟩

end NativeVm.Code.P3
