module

public import NativeVm.Code.Phase6.LayerD

/-!
# `linear_transpose` in the scratch

The tables of a layer's next weights: the weights before the map (`pure_w2`) and `g` (`pure_g`);
its columns and the map's output are `LayerE`'s.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec eOf_zero)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW} {p : UInt64}

theorem pure_w2 (hin : Inputs env inp s0.mem) (hc : Cn g) {eq : Array EW}
    (heq : ∀ i < 2048, g (eEq + i) = eq.getD i 0) :
    Pure6 env s0 (blk [I (.movi .r14 0), tab eW2 (.imm (Int64.ofNat 1600)) w2Val]) g
      (ovr g eW2 1600 fun m ↦ (w2Arr eq (g eBeta)).getD m 0) := by
  have h := pure_tab (env := env) (inp := inp) (s0 := s0) (g := g) (o := eW2) (N := 1600) (val := w2Val)
    (Lv := lRegs) (F := fun m ↦ (w2Arr eq (g eBeta)).getD m 0) hin (by p6_omega) (by decide)
    fun m hm s hp hs h15 ↦ ?_
  · exact h
  have hc' : Cn (ovr g eW2 m fun m ↦ (w2Arr eq (g eBeta)).getD m 0) :=
    hc.congr fun i h1 h2 ↦ ovr_out (by p6_omega)
  have hb : (ovr g eW2 m fun m ↦ (w2Arr eq (g eBeta)).getD m 0) eBeta = g eBeta := ovr_out (by p6_ne)
  have := w2Val_spec (eq := eq) hm hp hs h15 hc' (fun i hi ↦ by rw [ovr_out (by p6_omega), heq i hi])
    (E := fun _ ↦ False)
  rwa [hb] at this

/-- `g` at position `m`: the weight it copies. -/
def gIdx (m : Nat) : Nat := 64 * keccakPi (m / 64) + (m % 64 + keccakRho.getD (m / 64) 0) % 64

/-- Entry `m` of `g`, `m` in `r15`. -/
def gVal : Stmt := blk ([I (.mov .rax .r15), I (.shri .rax 6), I (.shli .rax 4),
  I (.load .rcx (ix (2 * eRho))), I (.load .rbx (ix (2 * ePi)))] ++ zpos false ++
  [I (.add .rdx .rcx), I (.andi .rdx 63), I (.add .rbx .rdx), I (.shli .rbx 4), I (.mov .rax .rbx),
    I (.load .r9 (ix (2 * eW2))), I (.load .r10 (ix (2 * eW2 + 1)))])

theorem tPi_le : ∀ l < 25, tPi.getD l 0 ≤ 1536 := by decide

theorem gVal_spec {W : Array EW} {m : Nat} (hm : m < 1600) (hp : s.reg .rbp = p)
    (hs : Scr s.mem p g) (h15 : s.reg .r15 = m.toUInt64) (hc : Cn g)
    (hW : ∀ i < 1600, g (eW2 + i) = W.getD i 0) {E : QState → Prop} :
    WP gVal s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = (W.getD (gIdx m) 0).toE ∧
      s'.mem = s.mem ∧ RegsFrame lRegs s s') E := by
  have hl : m / 64 < 25 := by omega
  have wr := hc.2.2.2.2.1 (m / 64) (lt_of_lt_of_eq hl rfl)
  have wp := hc.2.2.2.1 (m / 64) (lt_of_lt_of_eq hl rfl)
  have rlt := tRho_lt _ hl
  have ple := tPi_le _ hl
  have hidx : tPi.getD (m / 64) 0 + (m % 64 + tRho.getD (m / 64) 0) % 64 = gIdx m := by
    rw [gIdx, tPi_spec _ hl, tRho_spec _ hl]
  unfold gVal
  simp only [List.cons_append, List.nil_append]
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
    (NativeVm.Transcript.wp_reg (by rfl) ?_))
  have hrax : ((s.setReg .rax (s.reg .r15)).setReg .rax ((s.setReg .rax (s.reg .r15)).reg .rax >>>
      (6 : Nat).toUInt64) |>.setReg .rax (((s.setReg .rax (s.reg .r15)).setReg .rax
      ((s.setReg .rax (s.reg .r15)).reg .rax >>> (6 : Nat).toUInt64)).reg .rax <<<
      (4 : Nat).toUInt64)).reg .rax = (8 * (2 * (m / 64))).toUInt64 := by
    simp only [QState.setReg_reg, ↓reduceIte, h15]; exact shr6 (by omega)
  refine ldi0 (o := eRho) (i := m / 64) (by simpa using hp) hrax hs (by p6_omega) ?_
  refine ldi0 (o := ePi) (i := m / 64) (by simpa using hp) (by simpa using hrax)
    (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  rw [wr, wp]
  refine zpos_spec (m := m) (by omega) (by simpa using h15) fun s1 m1 f1 r1 ↦ ?_
  have r1c : s1.reg .rcx = (tRho.getD (m / 64) 0).toUInt64 := by rw [f1 .rcx (by decide)]; simp; rfl
  have r1b : s1.reg .rbx = (tPi.getD (m / 64) 0).toUInt64 := by rw [f1 .rbx (by decide)]; simp; rfl
  have r1p : s1.reg .rbp = p := by rw [f1 .rbp (by decide)]; simpa using hp
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at r1
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
    (NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
    (NativeVm.Transcript.wp_reg (by rfl) ?_))))
  have hix : (s1.reg .rbx + ((s1.reg .rdx + s1.reg .rcx) &&& (63 : Int64).toUInt64)) <<<
      (4 : Nat).toUInt64 = (8 * (2 * gIdx m)).toUInt64 := by
    rw [r1c, r1b, r1, NativeVm.Transcript.toUInt64_add, and63 (by omega),
      NativeVm.Transcript.toUInt64_add, ← hidx]
    exact rax16 _
  have hg : gIdx m < 1600 := by omega
  have hs1 : Scr s1.mem p g := hs.congr fun a _ ↦ by rw [m1]; rfl
  refine ldi0 (o := eW2) (i := gIdx m) (by simpa using r1p)
    (by simp only [QState.setReg_reg, ↓reduceIte, reduceCtorEq]; exact hix) hs1 (by p6_omega) ?_
  refine ldi1 (o := eW2) (i := gIdx m) (by simpa using r1p)
    (by simp only [QState.setReg_reg, ↓reduceIte, reduceCtorEq]; exact hix) hs1 (by p6_omega) ?_
  refine WP.blk_nil ⟨?_, by simp [m1], ?_⟩
  · simp only [QState.setReg_reg, ↓reduceIte, reduceCtorEq, eOf_toE]
    rw [hW _ hg]
  · exact rf_trans (l := [.rax, .rcx, .rbx]) (l'' := lRegs) (by rf_tac)
      (rf_trans (l := [.rdx]) (l' := [.r10, .r9, .rax, .rbx, .rdx]) (l'' := lRegs) f1 (by rf_tac))

theorem pure_g (hin : Inputs env inp s0.mem) (hc : Cn g) {W : Array EW}
    (hW : ∀ i < 1600, g (eW2 + i) = W.getD i 0) :
    Pure6 env s0 (blk [I (.movi .r14 0), tab eG (.imm (Int64.ofNat 1600)) gVal]) g
      (ovr g eG 1600 fun m ↦ W.getD (gIdx m) 0) := by
  refine pure_tab (Lv := lRegs) hin (by p6_omega) (by decide) fun m hm s hp hs h15 ↦ ?_
  have hc' : Cn (ovr g eG m fun m ↦ W.getD (gIdx m) 0) :=
    hc.congr fun i h1 h2 ↦ ovr_out (by p6_omega)
  exact gVal_spec hm hp hs h15 hc' fun i hi ↦ by rw [ovr_out (by p6_omega), hW i hi]

end NativeVm.Code.P6
