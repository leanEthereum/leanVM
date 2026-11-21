module

public import NativeVm.Code.Phase6.Lookup

/-!
# A layer's next weights

From the equality weights at `eEq` and `β`: the weights before the linear map at `eW2`
(`pure_w2`), `linear_transpose`'s `g` at `eG` (`pure_g`), its columns at `eCol` (`pure_col`), the
next claim's weights at `eW` (`pure_out`), and its value (`pure_newV`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec eOf_zero)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW} {p : UInt64}

/-- The weights before the linear map, as the layer computes them. -/
def w2Arr (eq : Array EW) (beta : EW) : Array EW :=
  (Array.range Verifier.keccakBits).map fun j ↦
    eq.getD j 0 + beta * (eq.getD (Verifier.keccakAlong j 4) 0 + beta * eq.getD (Verifier.keccakAlong j 3) 0)

theorem w2Arr_getD (eq : Array EW) (beta : EW) {j : Nat} (hj : j < 1600) :
    (w2Arr eq beta).getD j 0 = eq.getD j 0 + beta * (eq.getD (Verifier.keccakAlong j 4) 0 +
      beta * eq.getD (Verifier.keccakAlong j 3) 0) := by
  simp [w2Arr, Array.getD_eq_getD_getElem?, Verifier.keccakBits, hj]

theorem along_eq {j k : Nat} :
    Verifier.keccakAlong j k = 64 * ((j / 64 % 5 + k) % 5 + 5 * (j / 64 / 5)) + j % 64 := rfl

/-- Weight `j`, `j` in `r15`. -/
def w2Val : Stmt := blk (lk eA3 eEq false .r9 .r10 ++ ldB eBeta ++ [emul] ++ lk eA4 eEq false .r11 .r12 ++
  [eadd] ++ ldB eBeta ++ [emul] ++ idx16 ++ [I (.load .r11 (ix (2 * eEq))),
    I (.load .r12 (ix (2 * eEq + 1))), eadd])

/-- The registers the layer's lookups write. -/
abbrev lRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12]

theorem w2Val_spec {eq : Array EW} {m : Nat} (hm : m < 1600) (hp : s.reg .rbp = p)
    (hs : Scr s.mem p g) (h15 : s.reg .r15 = m.toUInt64) (hc : Cn g)
    (heq : ∀ i < 2048, g (eEq + i) = eq.getD i 0) {E : QState → Prop} :
    WP w2Val s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = ((w2Arr eq (g eBeta)).getD m 0).toE ∧
      s'.mem = s.mem ∧ RegsFrame lRegs s s') E := by
  have hl : m / 64 < 25 := by omega
  have w3 := hc.2.2.1 (m / 64) (lt_of_lt_of_eq hl rfl)
  have w4 := hc.2.1 (m / 64) (lt_of_lt_of_eq hl rfl)
  have a3 := tA3_spec _ hl
  have a4 := tA4_spec _ hl
  have hal3 : Verifier.keccakAlong m 3 = tA3.getD (m / 64) 0 + m % 64 := by rw [along_eq, a3]
  have hal4 : Verifier.keccakAlong m 4 = tA4.getD (m / 64) 0 + m % 64 := by rw [along_eq, a4]
  have b3 : tA3.getD (m / 64) 0 + m % 64 < 1600 := by rw [a3]; omega
  have b4 : tA4.getD (m / 64) 0 + m % 64 < 1600 := by rw [a4]; omega
  unfold w2Val
  simp only [List.append_assoc]
  refine lk_spec (w := tA3.getD (m / 64) 0) (by omega) (by decide) (by decide) hp hs h15 (by p6_omega)
    (by rw [w3]; rfl) (by simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; p6_omega)
    fun s1 m1 f1 v9 v10 ↦ ?_
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at v9 v10
  have hs1 : Scr s1.mem p g := hs.congr fun a _ ↦ by rw [m1]
  have hp1 : s1.reg .rbp = p := by rw [f1 .rbp (by decide), hp]
  refine ldB_spec hp1 hs1 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s2 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  have hs2 : Scr s2.mem p g := hs1.congr fun a _ ↦ by rw [e2]; rfl
  have hp2 : s2.reg .rbp = p := by rw [e3 .rbp (by decide)]; simpa using hp1
  have h152 : s2.reg .r15 = m.toUInt64 := by
    rw [e3 .r15 (by decide)]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [f1 .r15 (by decide), h15]
  refine lk_spec (w := tA4.getD (m / 64) 0) (by omega) (by decide) (by decide) hp2 hs2 h152
    (by p6_omega) (by rw [w4]; rfl) (by simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; p6_omega)
    fun s3 m3 f3 v11 v12 ↦ ?_
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at v11 v12
  refine WP.blk_cons (WP.mono (eadd_spec _) (fun s4 ⟨k1, k2, k3⟩ ↦ ?_) (fun _ h ↦ h))
  have hs4 : Scr s4.mem p g := hs2.congr fun a _ ↦ by rw [k2, m3]
  have hp4 : s4.reg .rbp = p := by rw [k3 .rbp (by decide), f3 .rbp (by decide), hp2]
  refine ldB_spec hp4 hs4 (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s5 ⟨n1, n2, n3⟩ ↦ ?_) (fun _ h ↦ h))
  have hs5 : Scr s5.mem p g := hs4.congr fun a _ ↦ by rw [n2]; rfl
  have hp5 : s5.reg .rbp = p := by rw [n3 .rbp (by decide)]; simpa using hp4
  have h155 : s5.reg .r15 = m.toUInt64 := by
    rw [n3 .r15 (by decide)]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [k3 .r15 (by decide), f3 .r15 (by decide), h152]
  refine idx16_spec h155 ?_
  refine ldi0 (o := eEq) (i := m) (by simpa using hp5) (by rax_tac) (hs5.congr fun _ _ ↦ rfl)
    (by p6_omega) ?_
  refine ldi1 (o := eEq) (i := m) (by simpa using hp5) (by rax_tac) (hs5.congr fun _ _ ↦ rfl)
    (by p6_omega) ?_
  refine WP.mono (eadd_spec _) (fun s6 ⟨q1, q2, q3⟩ ↦ ⟨?_, ?_, ?_⟩) (fun _ h ↦ h)
  · rw [q1]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [n1]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [k1, f3 .r9 (by decide), f3 .r10 (by decide), e1, v11, v12]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, v9, v10, eOf_toE]
    rw [w2Arr_getD eq _ hm, hal3, hal4, ← heq _ (by omega), ← heq _ (by omega), ← heq _ (by omega)]
    simp only [NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_mul]
    ring
  · rw [q2]; simp [n2, k2, m3, e2, m1]
  · exact rf_trans (l'' := lRegs) f1 (rf_trans (l := [.r11, .r12]) (l'' := lRegs) (by rf_tac)
      (rf_trans (l'' := lRegs) e3 (rf_trans (l'' := lRegs) f3 (rf_trans (l'' := lRegs) k3
      (rf_trans (l := [.r11, .r12]) (l'' := lRegs) (by rf_tac) (rf_trans (l'' := lRegs) n3
      (rf_trans (l := [.rax, .r11, .r12]) (l'' := lRegs) (by rf_tac) q3)))))))

end NativeVm.Code.P6
