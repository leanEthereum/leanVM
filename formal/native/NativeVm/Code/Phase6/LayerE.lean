module

public import NativeVm.Code.Phase6.LayerD2

/-!
# `linear_transpose` and the next claim's value

`lintC`: `g` (`pure_g`), its columns (`colVal`), the map's output over the claim's weights at `eW`
(`outVal`; `pure_lt`, against `keccakLinearTranspose`); `newVC`: the next claim's value
`t_0 + β (t_1 + β t_2)` at `eCV` (`pure_newV`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec eOf_add eOf_zero)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW} {p : UInt64}

/-! ## The columns -/

/-- The element `eG + 320 y + m` into `d0`, `d1`, `16 m` in `rax`. -/
def colLd (y : Nat) (d0 d1 : Reg64) : List Stmt :=
  [I (.load d0 (ix (2 * (eG + 320 * y)))), I (.load d1 (ix (2 * (eG + 320 * y) + 1)))]

theorem colLd_spec {y m : Nat} {d0 d1 : Reg64} {xs : List Stmt} {P E : QState → Prop}
    (h0 : d0 ≠ .rax ∧ d0 ≠ .rbp) (hp : s.reg .rbp = p) (hi : s.reg .rax = (8 * (2 * m)).toUInt64)
    (hs : Scr s.mem p g) (hm : eG + 320 * y + m < scrN)
    (k : WP (blk xs) ((s.setReg d0 (g (eG + 320 * y + m)).c0).setReg d1
      (g (eG + 320 * y + m)).c1) P E) :
    WP (blk (colLd y d0 d1 ++ xs)) s P E := by
  unfold colLd
  simp only [List.cons_append, List.nil_append]
  exact ldi0 hp hi hs hm (ldi1 (by simp [hp, Ne.symm h0.2]) (by simp [hi, Ne.symm h0.1])
    (hs.congr fun _ _ ↦ rfl) hm k)

/-- Column entry `m`, `m` in `r15`: the elements `eG + m + 320 y`, `y < 5`, summed. -/
def colVal : Stmt := blk (idx16 ++ colLd 0 .r9 .r10 ++ colLd 1 .r11 .r12 ++ colLd 2 .rbx .rcx ++
  colLd 3 .rdx .r8 ++ colLd 4 .rsi .r13 ++ [I (.xor .r9 .r11), I (.xor .r10 .r12), I (.xor .r9 .rbx),
    I (.xor .r10 .rcx), I (.xor .r9 .rdx), I (.xor .r10 .r8), I (.xor .r9 .rsi), I (.xor .r10 .r13)])

/-- The registers `colVal` writes. -/
abbrev cRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .rsi, .r13]

/-- Column entry `m = 64 x + z`. -/
def colF (W : Array EW) (m : Nat) : EW := EW.ofE (ltC W (m / 64) (m % 64))

theorem g_ltG {W : Array EW} {m y : Nat} (hm : m < 320) (hy : y < 5)
    (hG : ∀ i < 1600, g (eG + i) = W.getD (gIdx i) 0) :
    (g (eG + 320 * y + m)).toE = ltG W (m / 64 + 5 * y) (m % 64) := by
  rw [show eG + 320 * y + m = eG + (m + 320 * y) by omega, hG _ (by omega), gIdx, ltG,
    show (m + 320 * y) / 64 = m / 64 + 5 * y by omega, show (m + 320 * y) % 64 = m % 64 by omega]

theorem colVal_spec {W : Array EW} {m : Nat} (hm : m < 320) (hp : s.reg .rbp = p)
    (hs : Scr s.mem p g) (h15 : s.reg .r15 = m.toUInt64)
    (hG : ∀ i < 1600, g (eG + i) = W.getD (gIdx i) 0) {E : QState → Prop} :
    WP colVal s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = (colF W m).toE ∧
      s'.mem = s.mem ∧ RegsFrame cRegs s s') E := by
  unfold colVal
  simp only [List.append_assoc]
  refine idx16_spec h15 ?_
  have hr := rax16 m
  refine colLd_spec (y := 0) (by decide) (by simpa using hp) (by simpa using hr)
    (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine colLd_spec (y := 1) (by decide) (by simpa using hp) (by simpa using hr)
    (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine colLd_spec (y := 2) (by decide) (by simpa using hp) (by simpa using hr)
    (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine colLd_spec (y := 3) (by decide) (by simpa using hp) (by simpa using hr)
    (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine colLd_spec (y := 4) (by decide) (by simpa using hp) (by simpa using hr)
    (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep; fdone
  refine ⟨?_, trivial, by rf_tac⟩
  rw [eOf_add, eOf_add, eOf_add, eOf_add, eOf_toE, eOf_toE, eOf_toE, eOf_toE, eOf_toE,
    g_ltG hm (by decide) hG, g_ltG hm (by decide) hG, g_ltG hm (by decide) hG,
    g_ltG hm (by decide) hG, g_ltG hm (by decide) hG, colF, NativeVm.Equiv.EW.toE_ofE, ltC]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.mul_zero, Nat.add_zero]

/-! ## The output -/

/-- Output entry `m = 64 lane + z`, `m` in `r15`: `g[m] + col[C1[lane] + z] +
col[C4[lane] + (z + 1) mod 64]`. -/
def outVal : Stmt := blk (lk eC1 eCol false .r9 .r10 ++ lk eC4 eCol true .r11 .r12 ++ [eadd] ++
  idx16 ++ [I (.load .r11 (ix (2 * eG))), I (.load .r12 (ix (2 * eG + 1))), eadd])

theorem col_ltC {W : Array EW} {x z : Nat} (hx : x < 5) (hz : z < 64)
    (hC : ∀ i < 320, g (eCol + i) = colF W i) :
    (g (eCol + (64 * x + z))).toE = ltC W x z := by
  rw [hC _ (by omega), colF, NativeVm.Equiv.EW.toE_ofE, show (64 * x + z) / 64 = x by omega,
    show (64 * x + z) % 64 = z by omega]

theorem outVal_spec {W : Array EW} {m : Nat} (hm : m < 1600) (hp : s.reg .rbp = p)
    (hs : Scr s.mem p g) (h15 : s.reg .r15 = m.toUInt64) (hc : Cn g)
    (hG : ∀ i < 1600, g (eG + i) = W.getD (gIdx i) 0)
    (hC : ∀ i < 320, g (eCol + i) = colF W i) {E : QState → Prop} :
    WP outVal s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
      ((keccakLinearTranspose W).getD m 0).toE ∧ s'.mem = s.mem ∧ RegsFrame lRegs s s') E := by
  have hl : m / 64 < 25 := by omega
  have w1 := hc.2.2.2.2.2.1 (m / 64) (lt_of_lt_of_eq hl rfl)
  have w4 := hc.2.2.2.2.2.2.1 (m / 64) (lt_of_lt_of_eq hl rfl)
  have c1 := tC1_spec _ hl
  have c4 := tC4_spec _ hl
  unfold outVal
  simp only [List.append_assoc]
  refine lk_spec (w := tC1.getD (m / 64) 0) (by omega) (by decide) (by decide) hp hs h15 (by p6_omega)
    (by rw [w1]; rfl) (by simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; p6_omega)
    fun s1 m1 f1 v9 v10 ↦ ?_
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at v9 v10
  have hs1 : Scr s1.mem p g := hs.congr fun a _ ↦ by rw [m1]
  have hp1 : s1.reg .rbp = p := by rw [f1 .rbp (by decide), hp]
  have h151 : s1.reg .r15 = m.toUInt64 := by rw [f1 .r15 (by decide), h15]
  refine lk_spec (w := tC4.getD (m / 64) 0) (by omega) (by decide) (by decide) hp1 hs1 h151
    (by p6_omega) (by rw [w4]; rfl) (by simp only [↓reduceIte]; p6_omega)
    fun s2 m2 f2 v11 v12 ↦ ?_
  simp only [↓reduceIte] at v11 v12
  refine WP.blk_cons (WP.mono (eadd_spec _) (fun s3 ⟨k1, k2, k3⟩ ↦ ?_) (fun _ h ↦ h))
  have hs3 : Scr s3.mem p g := hs1.congr fun a _ ↦ by rw [k2, m2]
  have hp3 : s3.reg .rbp = p := by rw [k3 .rbp (by decide), f2 .rbp (by decide), hp1]
  have h153 : s3.reg .r15 = m.toUInt64 := by
    rw [k3 .r15 (by decide), f2 .r15 (by decide), h151]
  refine idx16_spec h153 ?_
  refine ldi0 (o := eG) (i := m) (by simpa using hp3) (by rax_tac) (hs3.congr fun _ _ ↦ rfl)
    (by p6_omega) ?_
  refine ldi1 (o := eG) (i := m) (by simpa using hp3) (by rax_tac) (hs3.congr fun _ _ ↦ rfl)
    (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (eadd_spec _) (fun s4 ⟨q1, q2, q3⟩ ↦ WP.blk_nil ⟨?_, ?_, ?_⟩)
    (fun _ h ↦ h))
  · rw [q1]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [k1, f2 .r9 (by decide), f2 .r10 (by decide), v9, v10, v11, v12]
    simp only [eOf_toE]
    have hm' : m = 64 * (m / 64) + m % 64 := by omega
    rw [hm', linearTranspose_getD W hl (Nat.mod_lt _ (by decide)), ← hm', c1, c4,
      col_ltC (by omega) (Nat.mod_lt _ (by decide)) hC,
      show (m + 1) % 64 = (m % 64 + 1) % 64 by omega,
      col_ltC (by omega) (Nat.mod_lt _ (by decide)) hC, hG _ hm]
    rw [show ltG W (m / 64) (m % 64) = (W.getD (gIdx m) 0).toE from rfl]
    ring
  · rw [q2]; simp [k2, m2, m1]
  · exact rf_trans (l'' := lRegs) f1 (rf_trans (l'' := lRegs) f2 (rf_trans (l'' := lRegs) k3
      (rf_trans (l := [.rax, .r11, .r12]) (l'' := lRegs) (by rf_tac) q3)))

/-! ## `linear_transpose` -/

/-- `linear_transpose` of the weights at `eW2`: `g` at `eG`, its columns at `eCol`, the output at
`eW`. -/
def lintC : List Stmt :=
  [blk [I (.movi .r14 0), tab eG (.imm (Int64.ofNat 1600)) gVal],
    blk [I (.movi .r14 0), tab eCol (.imm (Int64.ofNat 320)) colVal],
    blk [I (.movi .r14 0), tab eW (.imm (Int64.ofNat 1600)) outVal]]

theorem pure_lt (hin : Inputs env inp s0.mem) (hc : Cn g) {W : Array EW}
    (hW : ∀ i < 1600, g (eW2 + i) = W.getD i 0) :
    ∃ g', Pure6 env s0 (blk lintC) g g' ∧
      (∀ i, ¬ (eG ≤ i ∧ i < eCol + 320) → ¬ (eW ≤ i ∧ i < eW + 1600) → g' i = g i) ∧
      ∀ i < 1600, g' (eW + i) = (keccakLinearTranspose W).getD i 0 := by
  have p1 := pure_g hin hc hW
  generalize hg1 : ovr g eG 1600 (fun m ↦ W.getD (gIdx m) 0) = g1 at p1
  have hG1 : ∀ i < 1600, g1 (eG + i) = W.getD (gIdx i) 0 := fun i hi ↦ by
    rw [← hg1, ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hc1 : Cn g1 := hc.congr fun i h1 h2 ↦ by rw [← hg1, ovr_out (by p6_omega)]
  have p2 := pure_tab (env := env) (inp := inp) (s0 := s0) (g := g1) (o := eCol) (N := 320)
    (val := colVal) (Lv := cRegs) (F := colF W) hin (by p6_omega) (by decide)
    fun m hm s hp hs h15 ↦ colVal_spec hm hp hs h15 fun i hi ↦ by
      rw [ovr_out (by p6_omega), hG1 i hi]
  generalize hg2 : ovr g1 eCol 320 (colF W) = g2 at p2
  have hG2 : ∀ i < 1600, g2 (eG + i) = W.getD (gIdx i) 0 := fun i hi ↦ by
    rw [← hg2, ovr_out (by p6_omega), hG1 i hi]
  have hC2 : ∀ i < 320, g2 (eCol + i) = colF W i := fun i hi ↦ by
    rw [← hg2, ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have hc2 : Cn g2 := hc1.congr fun i h1 h2 ↦ by rw [← hg2, ovr_out (by p6_omega)]
  have p3 := pure_tab (env := env) (inp := inp) (s0 := s0) (g := g2) (o := eW) (N := 1600)
    (val := outVal) (Lv := lRegs) (F := fun m ↦ (keccakLinearTranspose W).getD m 0) hin
    (by p6_omega) (by decide) fun m hm s hp hs h15 ↦ outVal_spec hm hp hs h15
      (hc2.congr fun i h1 h2 ↦ ovr_out (by p6_omega))
      (fun i hi ↦ by rw [ovr_out (by p6_omega), hG2 i hi])
      (fun i hi ↦ by rw [ovr_out (by p6_omega), hC2 i hi])
  refine ⟨_, p1.cons (p2.cons p3.single), fun i h1 h2 ↦ ?_, fun i hi ↦ ?_⟩
  · rw [ovr_out (by p6_omega), ← hg2, ovr_out (by p6_omega), ← hg1, ovr_out (by p6_omega)]
  · rw [ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]

/-! ## The next claim's value -/

/-- The next claim's value, `t_0 + β (t_1 + β t_2)`, at `eCV`. -/
def newVC : List Stmt :=
  blk (ldA (eT + 2) ++ ldB eBeta ++ [emul] ++ ldB (eT + 1) ++ [eadd] ++ ldB eBeta ++ [emul] ++
    ldB eT ++ [eadd]) :: stEl eCV

theorem pure_newV (hin : Inputs env inp s0.mem) :
    Pure6 env s0 (blk newVC) g
      (Function.update g eCV (g eT + g eBeta * (g (eT + 1) + g eBeta * g (eT + 2)))) := by
  refine pure_el hin (by p6_omega) (L := lRegs) (by decide) fun s hp hs ↦ ?_
  simp only [List.append_assoc]
  refine ldA_spec hp hs (by p6_omega) ?_
  refine ldB_spec (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s2 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  have hs2 : Scr s2.mem (sb env) g := hs.congr fun a _ ↦ by rw [e2]; rfl
  have hp2 : s2.reg .rbp = sb env := by rw [e3 .rbp (by decide)]; simpa using hp
  refine ldB_spec hp2 hs2 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (eadd_spec _) (fun s3 ⟨k1, k2, k3⟩ ↦ ?_) (fun _ h ↦ h))
  have hs3 : Scr s3.mem (sb env) g := hs2.congr fun a _ ↦ by rw [k2]; rfl
  have hp3 : s3.reg .rbp = sb env := by rw [k3 .rbp (by decide)]; simpa using hp2
  refine ldB_spec hp3 hs3 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s4 ⟨n1, n2, n3⟩ ↦ ?_) (fun _ h ↦ h))
  have hs4 : Scr s4.mem (sb env) g := hs3.congr fun a _ ↦ by rw [n2]; rfl
  have hp4 : s4.reg .rbp = sb env := by rw [n3 .rbp (by decide)]; simpa using hp3
  refine ldB_spec hp4 hs4 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (eadd_spec _) (fun s5 ⟨q1, q2, q3⟩ ↦ WP.blk_nil ⟨?_, ?_, ?_⟩)
    (fun _ h ↦ h))
  · rw [q1]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [n1]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [k1]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [e1]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, eOf_toE, NativeVm.Equiv.EW.toE_add,
      NativeVm.Equiv.EW.toE_mul]
    ring
  · rw [q2]; simp [n2, k2, e2]
  · exact rf_trans (l := [.r9, .r10, .r11, .r12]) (l'' := lRegs) (by rf_tac)
      (rf_trans (l'' := lRegs) e3 (rf_trans (l := [.r11, .r12]) (l'' := lRegs) (by rf_tac)
      (rf_trans (l'' := lRegs) k3 (rf_trans (l := [.r11, .r12]) (l'' := lRegs) (by rf_tac)
      (rf_trans (l'' := lRegs) n3 (rf_trans (l := [.r11, .r12]) (l'' := lRegs) (by rf_tac)
      q3))))))

end NativeVm.Code.P6
