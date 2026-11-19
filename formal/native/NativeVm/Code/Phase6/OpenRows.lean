module

public import NativeVm.Code.Phase6.OpenCol

/-!
# An opening's slot weights

The table of `keccakSlotWeights`, column by column: the element `eRows + 64 z + r` is the row
`r`'s segment weight (`rowW`: the claim's segment weight `r / 25 - first`, `0` outside its
segments) times the bit weight `64 (r mod 25) + z` (`rowsC`, `pure_rows`). The row is `m mod 64`
and the column `m / 64` for the table's index `m`; `r mod 25` by two conditional subtractions.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol
open NativeVm.Transcript (wd wdisp Env wd_inj rf_trans)
open NativeVm.Field (eOf emul emul_spec eRegs)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW} {p : UInt64}

/-- Row `r`'s segment weight, the segment weights at `sw`. -/
def rowW (first sw : Nat) (g : Nat → EW) (r : Nat) : EW :=
  if r < 25 then (if first = 0 then g sw else 0) else if r < 50 then g (sw + 1 - first) else 0

/-- The table's element `m`. -/
def rowF (first sw wb : Nat) (g : Nat → EW) (m : Nat) : EW :=
  EW.ofE ((g (wb + (m / 64 + 64 * (m % 64 % 25)))).toE * (rowW first sw g (m % 64)).toE)

/-- `B :=` the element `o` when `b`, else `0`. -/
def segLd (b : Bool) (o : Nat) : Stmt :=
  if b then blk (ldB o) else blk [I (.movi .r11 0), I (.movi .r12 0)]

/-- `B :=` row `rdx`'s segment weight. -/
def rowLd (first sw : Nat) : Stmt :=
  .ite (.cmp .ltu .rdx (.imm (Int64.ofNat 25))) (segLd (decide (first = 0)) sw)
    (.ite (.cmp .ltu .rdx (.imm (Int64.ofNat 50))) (segLd true (sw + 1 - first)) (segLd false 0))

/-- `rdx := rdx - 25` when `25 ≤ rdx`. -/
def subIf : Stmt :=
  .ite (.cmp .geu .rdx (.imm (Int64.ofNat 25))) (I (.subi .rdx (Int64.ofNat 25))) .skip

/-- The table's element `m` (in `r15`) into `A`. -/
def rowVal (first sw wb : Nat) : Stmt := blk [I (.mov .rdx .r15), I (.andi .rdx 63), rowLd first sw,
  subIf, subIf, I (.shli .rdx 6), I (.mov .rax .r15), I (.shri .rax 6), I (.add .rax .rdx),
  I (.shli .rax 4), I (.load .r9 (ix (2 * wb))), I (.load .r10 (ix (2 * wb + 1))), emul]

/-- The slot weights' table. -/
def rowsC (first sw wb : Nat) : List Stmt :=
  [I (.movi .r14 0), tab eRows (.imm (Int64.ofNat 4096)) (rowVal first sw wb)]

theorem ltu_rdx {r n : Nat} (h : s.reg .rdx = r.toUInt64) (hr : r < 2 ^ 63) (hn : n < 2 ^ 63) :
    (Cond.cmp .ltu .rdx (.imm (Int64.ofNat n))).eval s = decide (r < n) := by
  simp only [Cond.eval, h, Rhs.eval]
  rw [show (Int64.ofNat n).toUInt64 = n.toUInt64 from rfl, Bool.eq_iff_iff, decide_eq_true_iff,
    decide_eq_true_iff]
  exact toUInt64_lt' (by omega) (by omega)

theorem segLd_spec {b : Bool} {o : Nat} {E : QState → Prop} (hp : s.reg .rbp = p)
    (hs : Scr s.mem p g) (ho : o < scrN) :
    WP (segLd b o) s (fun s' ↦ s'.reg .r11 = (if b then g o else 0).c0 ∧
      s'.reg .r12 = (if b then g o else 0).c1 ∧ s'.mem = s.mem ∧ RegsFrame [.r11, .r12] s s') E := by
  cases b
  · simp only [segLd, Bool.false_eq_true, ite_false]
    fstep; fstep; fdone
    refine ⟨?_, ?_, ?_, by rf_tac⟩ <;> trivial
  · simp only [segLd, ite_true]
    rw [← List.append_nil (ldB o)]
    exact ldB_spec hp hs ho (WP.blk_nil ⟨by simp, by simp, rfl, by rf_tac⟩)

theorem rowLd_spec {first sw r : Nat} {E : QState → Prop} (hp : s.reg .rbp = p)
    (hs : Scr s.mem p g) (hsw : sw + 1 < scrN) (hrdx : s.reg .rdx = r.toUInt64) (hr : r < 64) :
    WP (rowLd first sw) s (fun s' ↦ s'.reg .r11 = (rowW first sw g r).c0 ∧
      s'.reg .r12 = (rowW first sw g r).c1 ∧ s'.mem = s.mem ∧ RegsFrame [.r11, .r12] s s') E := by
  unfold rowLd
  apply WP.ite
  rw [ltu_rdx hrdx (by omega) (by omega)]
  by_cases h25 : r < 25
  · simp only [h25, decide_true, ite_true]
    refine WP.mono (segLd_spec hp hs (by omega)) (fun s' ⟨h1, h2, h3, h4⟩ ↦ ⟨?_, ?_, h3, h4⟩)
      (fun _ h ↦ h)
    · rw [h1]; simp [rowW, h25]
    · rw [h2]; simp [rowW, h25]
  · simp only [h25, decide_false, Bool.false_eq_true, ite_false]
    apply WP.ite
    rw [ltu_rdx hrdx (by omega) (by omega)]
    by_cases h50 : r < 50
    · simp only [h50, decide_true, ite_true]
      refine WP.mono (segLd_spec hp hs (by omega)) (fun s' ⟨h1, h2, h3, h4⟩ ↦ ⟨?_, ?_, h3, h4⟩)
        (fun _ h ↦ h)
      · rw [h1]; simp [rowW, h25, h50]
      · rw [h2]; simp [rowW, h25, h50]
    · simp only [h50, decide_false, Bool.false_eq_true, ite_false]
      refine WP.mono (segLd_spec (b := false) (o := 0) hp hs (by p6_omega))
        (fun s' ⟨h1, h2, h3, h4⟩ ↦ ⟨?_, ?_, h3, h4⟩) (fun _ h ↦ h)
      · rw [h1]; simp [rowW, h25, h50]
      · rw [h2]; simp [rowW, h25, h50]

theorem subIf_spec {x : Nat} {E : QState → Prop} (h : s.reg .rdx = x.toUInt64) (hx : x < 2 ^ 62) :
    WP subIf s (fun s' ↦ s'.reg .rdx = (if 25 ≤ x then x - 25 else x).toUInt64 ∧
      s'.mem = s.mem ∧ RegsFrame [.rdx] s s') E := by
  unfold subIf
  apply WP.ite
  have hc : (Cond.cmp .geu .rdx (.imm (Int64.ofNat 25))).eval s = decide (25 ≤ x) := by
    simp only [Cond.eval, h, Rhs.eval]
    rw [show (Int64.ofNat 25).toUInt64 = (25 : Nat).toUInt64 from rfl, Bool.eq_iff_iff,
      decide_eq_true_iff, decide_eq_true_iff]
    exact NativeVm.Transcript.toUInt64_le (by omega) (by omega)
  rw [hc]
  by_cases h25 : 25 ≤ x
  · simp only [h25, decide_true, ite_true]
    refine WP.ins (s' := s.setReg .rdx (s.reg .rdx - (Int64.ofNat 25).toUInt64)) rfl
      ⟨?_, rfl, by rf_tac⟩
    simp only [QState.setReg_reg, ↓reduceIte, h]
    rw [show (Int64.ofNat 25).toUInt64 = (25 : Nat).toUInt64 from rfl]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ ((NativeVm.Transcript.toUInt64_le (by omega) (by omega)).mpr
      h25), toNat_toUInt64' (by omega), toNat_toUInt64' (by omega), toNat_toUInt64' (by omega)]
  · simp only [h25, decide_false, Bool.false_eq_true, ite_false]
    exact WP.skip ⟨h, rfl, by rf_tac⟩

theorem shr6' {m : Nat} (hm : m < 2 ^ 64) : m.toUInt64 >>> (6 : Nat).toUInt64 = (m / 64).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, toNat_toUInt64' hm, toNat_toUInt64' (by omega)]
  simp [Nat.shiftRight_eq_div_pow]
  omega

theorem shl6 {x : Nat} : x.toUInt64 <<< (6 : Nat).toUInt64 = (64 * x).toUInt64 :=
  NativeVm.Transcript.toUInt64_shl x 6 (by omega)

theorem and63' {m : Nat} (hm : m < 2 ^ 64) :
    m.toUInt64 &&& (63 : Int64).toUInt64 = (m % 64).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, toNat_toUInt64' hm, toNat_toUInt64' (by omega)]
  show m &&& 63 = m % 64
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem mod25 {r : Nat} (hr : r < 64) :
    (if 25 ≤ (if 25 ≤ r then r - 25 else r) then (if 25 ≤ r then r - 25 else r) - 25
      else (if 25 ≤ r then r - 25 else r)) = r % 25 := by
  split_ifs <;> omega

/-- **The table's element `m`**, the scratch `f`. -/
theorem rowVal_spec {first sw wb m : Nat} {E : QState → Prop} (hp : s.reg .rbp = p)
    (hs : Scr s.mem p g) (hsw : sw + 1 < scrN) (hwb : wb + 1600 ≤ scrN) (hm : m < 4096)
    (h15 : s.reg .r15 = m.toUInt64) :
    WP (rowVal first sw wb) s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
        (g (wb + (m / 64 + 64 * (m % 64 % 25)))).toE * (rowW first sw g (m % 64)).toE ∧
      s'.mem = s.mem ∧ RegsFrame dRegs s s') E := by
  have hN := scrN_lt
  unfold rowVal
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
  set s1 := ((s.setReg .rdx (s.reg .r15)).setReg .rdx
    ((s.setReg .rdx (s.reg .r15)).reg .rdx &&& (63 : Int64).toUInt64)) with hs1
  have r1 : s1.reg .rdx = (m % 64).toUInt64 := by
    rw [hs1]; simp only [QState.setReg_reg, ↓reduceIte, h15]; exact and63' (by omega)
  have p1 : s1.reg .rbp = p := by rw [hs1]; simpa using hp
  have f1 : RegsFrame [.rdx] s s1 := by rw [hs1]; rf_tac
  refine NativeVm.Field.WP.then (rowLd_spec (first := first) p1 (hs.congr fun _ _ ↦ rfl) hsw r1
    (by omega)) fun s2 ⟨a1, a2, a3, a4⟩ ↦ ?_
  have r2 : s2.reg .rdx = (m % 64).toUInt64 := by rw [a4 .rdx (by decide), r1]
  refine NativeVm.Field.WP.then (subIf_spec r2 (by omega)) fun s3 ⟨b1, b2, b3⟩ ↦ ?_
  refine NativeVm.Field.WP.then (subIf_spec b1 (by split <;> omega)) fun s4 ⟨c1, c2, c3⟩ ↦ ?_
  rw [mod25 (by omega)] at c1
  have f4 : RegsFrame [.rdx, .r11, .r12] s s4 :=
    rf_trans (l'' := [.rdx, .r11, .r12]) (rf_trans (l'' := [.rdx, .r11, .r12])
      (rf_trans (l'' := [.rdx, .r11, .r12]) f1 a4) b3) c3
  have r15 : s4.reg .r15 = m.toUInt64 := by rw [f4 .r15 (by decide), h15]
  have p4 : s4.reg .rbp = p := by rw [f4 .rbp (by decide), hp]
  have m4 : s4.mem = s.mem := by rw [c2, b2, a3, hs1]; rfl
  have k11 : s4.reg .r11 = (rowW first sw g (m % 64)).c0 := by
    rw [c3 .r11 (by decide), b3 .r11 (by decide), a1]
  have k12 : s4.reg .r12 = (rowW first sw g (m % 64)).c1 := by
    rw [c3 .r12 (by decide), b3 .r12 (by decide), a2]
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
    (NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
      (NativeVm.Transcript.wp_reg (by rfl) ?_))))
  have hix : ((s4.reg .r15 >>> (6 : Nat).toUInt64) + s4.reg .rdx <<< (6 : Nat).toUInt64) <<<
      (4 : Nat).toUInt64 = (8 * (2 * (m / 64 + 64 * (m % 64 % 25)))).toUInt64 := by
    rw [r15, c1, shr6' (by omega), shl6, NativeVm.Transcript.toUInt64_add]
    exact rax16 _
  have hs4 : Scr s4.mem p g := hs.congr fun a _ ↦ by rw [m4]
  refine ldi0 (o := wb) (i := m / 64 + 64 * (m % 64 % 25)) (by simpa using p4)
    (by simp only [QState.setReg_reg, ↓reduceIte, reduceCtorEq]; exact hix) hs4 (by omega) ?_
  refine ldi1 (o := wb) (i := m / 64 + 64 * (m % 64 % 25)) (by simpa using p4)
    (by simp only [QState.setReg_reg, ↓reduceIte, reduceCtorEq]; exact hix)
    (hs4.congr fun _ _ ↦ rfl) (by omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s5 ⟨e1, e2, e3⟩ ↦ WP.blk_nil ⟨?_, ?_, ?_⟩)
    (fun _ h ↦ h))
  · rw [e1]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, k11, k12, eOf_toE]
  · rw [e2]; simpa using m4
  · exact rf_trans (l := [.rdx, .r11, .r12, .rax, .r9, .r10]) (l' := eRegs) (l'' := dRegs)
      (rf_trans (l := [.rdx, .r11, .r12]) (l' := [.rdx, .rax, .r9, .r10]) f4 (by rf_tac)) e3

/-- **The slot weights' table.** -/
theorem pure_rows (hin : Inputs env inp s0.mem) {first sw wb : Nat} (hsw : sw + 1 < eRows)
    (hwb : ∀ j < 1600, wb + j < eRows ∨ eRows + 4096 ≤ wb + j) (hwb' : wb + 1600 ≤ scrN) :
    Pure6 env s0 (blk (rowsC first sw wb)) g (ovr g eRows 4096 (rowF first sw wb g)) := by
  refine pure_tab hin (Lv := dRegs) (by p6_omega) (by decide) fun m hm s hp hs h15 ↦ ?_
  refine WP.mono (rowVal_spec (first := first) hp hs (by p6_omega) hwb' hm h15)
    (fun s' ⟨h1, h2, h3⟩ ↦ ⟨?_, h2, h3⟩) (fun _ h ↦ h)
  have hi : m / 64 + 64 * (m % 64 % 25) < 1600 := by omega
  have hrw : rowW first sw (ovr g eRows m (rowF first sw wb g)) (m % 64) = rowW first sw g (m % 64) := by
    unfold rowW
    rw [ovr_out (by omega), ovr_out (by omega)]
  rw [h1, hrw, ovr_out (by have := hwb _ hi; omega), rowF, NativeVm.Equiv.EW.toE_ofE]

end NativeVm.Code.P6
