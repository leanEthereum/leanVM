module

public import NativeVm.Code.Phase3.BcMleBase

/-!
# The bytecode's multilinear extension: the point's copy

`bcPrep` copies `point' = point[0 .. min(logBytecode, |point|)) ++ slot` into `tmpR` from word
`bcPtW` and leaves `2^|point'|` in `r14` (`bcPrep_spec`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code

variable {env : Env} {inp : Input} {s0 s : QState}

theorem bc_shl1 {k : Nat} (_hk : k < 2 ^ 62) : k.toUInt64 <<< 1 = (2 * k).toUInt64 := by
  have := toUInt64_shl k 1 (by omega)
  rwa [show (1 : Nat).toUInt64 = 1 from rfl, pow_one] at this

theorem bc_and63 {m : Nat} (hm : m < 64) : m.toUInt64 &&& 63 = m.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, Transcript.toNat_toUInt64 (by omega),
    show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bc_pow_shl {m : Nat} (hm : m < 64) : (1 : UInt64) <<< (m.toUInt64 &&& 63) = (2 ^ m).toUInt64 := by
  rw [bc_and63 hm, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, toUInt64_shl 1 m hm, Nat.mul_one]

/-- The element `x` from the words `a`, `a + 1` of the working area. -/
theorem bc_ewat {mem : UInt64 → Option UInt64} {p : UInt64} {a : Nat} {x : EW}
    (h0 : mem (wd p a) = some x.c0) (h1 : mem (wd p (a + 1)) = some x.c1) : EWAt mem (wd p a) x :=
  ⟨h0, by rw [wd_wd]; exact h1⟩

/-- **`bcPrep`**: `point'` from word `bcPtW`, `r14 = 2^|point'|`. -/
theorem bcPrep_spec {logB : Nat} {point slot : Array EW} {E : QState → Prop}
    (hw : Wrote env [tmpR] s0 s) (hi : Inputs env inp s0.mem) (hrdi : s0.reg .rdi = env.ctx)
    (hwk : s0.mem (wd env.ctx ctxWork) = some env.work)
    (hl : NatAt s0.mem (wd env.work (layoutR.off + 1)) logB) (hlb : logB ≤ 30)
    (hdw : NatAt s0.mem (wd env.work depthR.off) point.size) (hps : point.size < 64)
    (hp : EWArr s0.mem (pointR.at env.work) point)
    (hs : EWArr s0.mem (slotR.at env.work) slot) (hss : slot.size = 4) :
    WP bcPrep s (fun s' ↦ Wrote env [tmpR] s0 s' ∧
      s'.reg .r14 = (2 ^ (point.extract 0 logB ++ slot).size).toUInt64 ∧
      EWArr s'.mem (wd env.work bcPtW) (point.extract 0 logB ++ slot)) E := by
  have hww := bc_work_le hi
  have hrdi' : s.reg .rdi = env.ctx := hw.rdi.trans hrdi
  have hwk' : s.mem (wd env.ctx ctxWork) = some env.work := by
    rw [bc_ctx hw hi (by lay_omega)]; exact hwk
  have hl' : NatAt s.mem (wd env.work (layoutR.off + 1)) logB :=
    hl.congr (bc_out hw (by bc_omega) (by bc_omega))
  have hdw' : NatAt s.mem (wd env.work depthR.off) point.size :=
    hdw.congr (bc_out hw (by bc_omega) (by bc_omega))
  set k := min logB point.size with hk
  have hek : (point.extract 0 logB).size = k := by simp [hk]
  have hpt : (point.extract 0 logB ++ slot).size = k + 4 := by simp [hek, hss]
  unfold bcPrep
  refine wp_then (bcMin_spec hrdi' hwk' hl' hdw') fun s1 ⟨m1, r1, w1, f1⟩ ↦ ?_
  rw [← hk] at r1
  have hw1 : Wrote env [tmpR] s0 s1 := ⟨(f1 .rdi (by simp)).trans hw.rdi,
    fun a ha ↦ by rw [m1]; exact hw.mem a ha, fun a ↦ by rw [m1]; exact hw.dom a⟩
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  set s2 := (((s1.setReg .rcx (s1.reg .rax)).setReg .rcx
    ((s1.setReg .rcx (s1.reg .rax)).reg .rcx <<< (1 : Nat).toUInt64)).setReg .rsi
    ((at_ .r11 (wdisp pointR.off)).eval ((s1.setReg .rcx (s1.reg .rax)).setReg .rcx
      ((s1.setReg .rcx (s1.reg .rax)).reg .rcx <<< (1 : Nat).toUInt64)))).setReg .rdx
    ((at_ .r11 (wdisp bcPtW)).eval (((s1.setReg .rcx (s1.reg .rax)).setReg .rcx
      ((s1.setReg .rcx (s1.reg .rax)).reg .rcx <<< (1 : Nat).toUInt64)).setReg .rsi
    ((at_ .r11 (wdisp pointR.off)).eval ((s1.setReg .rcx (s1.reg .rax)).setReg .rcx
      ((s1.setReg .rcx (s1.reg .rax)).reg .rcx <<< (1 : Nat).toUInt64))))) with hs2
  have w2 : Wrote env [tmpR] s0 s2 :=
    hw1.setReg (r := .rcx) (by decide) _ |>.setReg (r := .rcx) (by decide) _
      |>.setReg (r := .rsi) (by decide) _ |>.setReg (r := .rdx) (by decide) _
  have h2si : s2.reg .rsi = wd env.work pointR.off := by
    rw [hs2]; rsimp; exact eval_work (by rsimp; exact w1) _
  have h2dx : s2.reg .rdx = wd env.work bcPtW := by
    rw [hs2]; rsimp; exact eval_work (by rsimp; exact w1) _
  have h2cx : s2.reg .rcx = (2 * k).toUInt64 := by
    rw [hs2]; rsimp; rw [r1]; exact bc_shl1 (by omega)
  have h2ax : s2.reg .rax = k.toUInt64 := by rw [hs2]; rsimp; exact r1
  have h2r11 : s2.reg .r11 = env.work := by rw [hs2]; rsimp; exact w1
  refine wp_then (bcCopy_spec w2 hi h2si h2dx h2cx (by bc_omega) (by bc_omega) (by bc_omega))
    fun s3 ⟨w3, c3, k3, si3, dx3, f3⟩ ↦ ?_
  have h3r11 : s3.reg .r11 = env.work := (f3 .r11 (by simp)).trans h2r11
  have h3ax : s3.reg .rax = k.toUInt64 := (f3 .rax (by simp)).trans h2ax
  refine wp_reg rfl (wp_reg rfl ?_)
  set s4 := ((s3.setReg .rsi ((at_ .r11 (wdisp slotR.off)).eval s3)).setReg .rcx
    (8 : Int64).toUInt64) with hs4
  have w4 : Wrote env [tmpR] s0 s4 :=
    w3.setReg (r := .rsi) (by decide) _ |>.setReg (r := .rcx) (by decide) _
  have h4si : s4.reg .rsi = wd env.work slotR.off := by
    rw [hs4]; rsimp; exact eval_work h3r11 _
  have h4dx : s4.reg .rdx = wd env.work (bcPtW + 2 * k) := by rw [hs4]; rsimp; exact dx3
  have h4cx : s4.reg .rcx = (8 : Nat).toUInt64 := by rw [hs4]; rsimp
  refine wp_then (bcCopy_spec w4 hi h4si h4dx h4cx (by bc_omega) (by bc_omega) (by bc_omega))
    fun s5 ⟨w5, c5, k5, _, _, f5⟩ ↦ ?_
  have h5ax : s5.reg .rax = k.toUInt64 := by
    rw [f5 .rax (by simp), hs4]; rsimp; exact h3ax
  fstep; fstep; fstep; fstep
  have e4 : k.toUInt64 + 4 = (k + 4).toUInt64 := by rw [← toUInt64_add]; rfl
  rw [h5ax, e4, bc_pow_shl (by omega)]
  refine WP.blk_nil ⟨?_, by rsimp; rw [hpt], ?_⟩
  · exact w5.setReg (r := .rax) (by decide) _ |>.setReg (r := .rcx) (by decide) _
      |>.setReg (r := .r14) (by decide) _ |>.setReg (r := .r14) (by decide) _
  · have e3 : ∀ j < 2 * k, s5.mem (wd env.work (bcPtW + j)) = s0.mem (wd env.work (pointR.off + j)) := by
      intro j hj
      rw [k5 _ fun j' _ e ↦ by rw [wd_inj (by bc_omega) (by bc_omega)] at e; omega]
      show s3.mem _ = _
      rw [c3 j hj]
      show s1.mem _ = _
      rw [m1, bc_out hw (by bc_omega) (by bc_omega)]
    have e4 : ∀ j < 8, s5.mem (wd env.work (bcPtW + 2 * k + j)) =
        s0.mem (wd env.work (slotR.off + j)) := by
      intro j hj
      rw [c5 j hj]
      show s3.mem _ = _
      rw [k3 _ fun j' _ e ↦ by rw [wd_inj (by bc_omega) (by bc_omega)] at e; bc_omega]
      show s1.mem _ = _
      rw [m1, bc_out hw (by bc_omega) (by bc_omega)]
    intro i hi'
    simp only [QState.setReg_mem]
    rw [hpt] at hi'
    by_cases hik : i < k
    · rw [Array.getElem_append_left (by rw [hek]; exact hik), Array.getElem_extract]
      obtain ⟨p0, p1⟩ := hp i (by omega)
      simp only [Region.at, wd_wd] at p0 p1
      simp only [Nat.zero_add]
      rw [wd_wd]
      refine bc_ewat ?_ ?_
      · rw [e3 _ (by omega)]; exact p0
      · rw [show bcPtW + 2 * i + 1 = bcPtW + (2 * i + 1) by omega, e3 _ (by omega)]
        rw [Nat.add_assoc] at p1; exact p1
    · rw [Array.getElem_append_right (by rw [hek]; omega)]
      simp only [hek]
      obtain ⟨p0, p1⟩ := hs (i - k) (by omega)
      simp only [Region.at, wd_wd] at p0 p1
      rw [wd_wd]
      refine bc_ewat ?_ ?_
      · rw [show bcPtW + 2 * i = bcPtW + 2 * k + 2 * (i - k) by omega, e4 _ (by omega)]; exact p0
      · rw [show bcPtW + 2 * i + 1 = bcPtW + 2 * k + (2 * (i - k) + 1) by omega, e4 _ (by omega)]
        rw [Nat.add_assoc] at p1; exact p1

end NativeVm.Code.P3
