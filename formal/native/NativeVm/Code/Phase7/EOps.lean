module

public import NativeVm.Code.Phase7.Base
public import NativeVm.Field.E
public import NativeVm.Equiv.Field

/-!
# `E` arithmetic on the working area's words

Straight-line `E` arithmetic for phase 7, on `A = (r9, r10)` with operands in the working area
(`rbp` at it): `ldA k` (`A := word pair k`), `stA k` (`word pair k := A`), `mulM k` (`A := A ·
pair k`), `addM k` (`A := A + pair k`), `scaleM k` (`A := A · ofK (word k)`), `sqA` (`A := A²`).
Each spec is in continuation form and on the model's `EW` values, so a computation is a chain of
`refine op_wp ... fun s₁ ... ↦ ?_` and its value an `EW` expression (`toE` turns it into `E`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model NativeVm.Field LeanVM.Parameters NativeVm.Equiv
open NativeVm.Transcript (wd Env wdisp)

def ldA (k : Nat) : List Stmt := [ldw .r9 k, ldw .r10 (k + 1)]
def stA (k : Nat) : List Stmt := [stw k .r9, stw (k + 1) .r10]
def mulM (k : Nat) : List Stmt := [ldw .r11 k, ldw .r12 (k + 1), emul]
def addM (k : Nat) : List Stmt := [ldw .r11 k, ldw .r12 (k + 1), eadd]
def scaleM (k : Nat) : List Stmt := [ldw .r11 k, escale]
def sqA : List Stmt := [esq]

variable {env : Env} {s : QState} {P E : QState → Prop} {rest : List Stmt}

theorem eOf_eq_toE (x : EW) : eOf x.c0 x.c1 = x.toE := rfl

/-- Lanes whose element is `x.toE` are `x`'s. -/
theorem lanes_of_eOf {a b : UInt64} {x : EW} (h : eOf a b = x.toE) : a = x.c0 ∧ b = x.c1 := by
  have : EW.mk a b = x := EW.toE_injective h
  subst this
  exact ⟨rfl, rfl⟩

theorem ldw_wp {d : Reg64} {k : Nat} {v : UInt64} (hW : s.reg .rbp = env.work)
    (hv : s.mem (wd env.work k) = some v) (h : WP (blk rest) (s.setReg d v) P E) :
    WP (blk (ldw d k :: rest)) s P E :=
  NativeVm.Transcript.wp_load (eval_w hW k) hv h

theorem stw_wp {r : Reg64} {k : Nat} (hW : s.reg .rbp = env.work)
    (hk : (s.mem (wd env.work k)).isSome)
    (h : WP (blk rest) (s.setMem (wd env.work k) (s.reg r)) P E) :
    WP (blk (stw k r :: rest)) s P E :=
  NativeVm.Transcript.wp_store (eval_w hW k) hk h

/-- `A := pair k`. -/
theorem ldA_wp {k : Nat} {x : EW} (hW : s.reg .rbp = env.work) (hx : EWAt s.mem (wd env.work k) x)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = x.c0 → s₁.reg .r10 = x.c1 →
      RegsFrame [.r9, .r10] s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (ldw .r9 k :: ldw .r10 (k + 1) :: rest)) s P E := by
  refine ldw_wp hW hx.1 (ldw_wp (by rsimp; exact hW) (by rsimp; rw [← wd_wd]; exact hx.2) ?_)
  exact h _ rfl (by rsimp) (by rsimp) (by rf_tac)

/-- `pair k := A`. -/
theorem stA_wp {k : Nat} (hW : s.reg .rbp = env.work) (h0 : (s.mem (wd env.work k)).isSome)
    (h1 : (s.mem (wd env.work (k + 1))).isSome)
    (h : WP (blk rest) ((s.setMem (wd env.work k) (s.reg .r9)).setMem (wd env.work (k + 1))
      (s.reg .r10)) P E) :
    WP (blk (stw k .r9 :: stw (k + 1) .r10 :: rest)) s P E := by
  refine stw_wp hW h0 (stw_wp (by rsimp; exact hW) ?_ h)
  rw [QState.setMem_mem]
  split
  · rfl
  · exact h1

/-- `A := A · pair k`. -/
theorem mulM_wp {k : Nat} {a b : EW} (hW : s.reg .rbp = env.work) (h9 : s.reg .r9 = a.c0)
    (h10 : s.reg .r10 = a.c1) (hb : EWAt s.mem (wd env.work k) b)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = (a * b).c0 → s₁.reg .r10 = (a * b).c1 →
      RegsFrame (eRegs ++ [.r11, .r12]) s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (ldw .r11 k :: ldw .r12 (k + 1) :: emul :: rest)) s P E := by
  refine ldw_wp hW hb.1 (ldw_wp (by rsimp; exact hW) (by rsimp; rw [← wd_wd]; exact hb.2) ?_)
  refine WP.then (emul_spec _) fun s₁ ⟨e1, m1, f1⟩ ↦ ?_
  rsimp at e1
  rw [h9, h10, eOf_eq_toE, eOf_eq_toE, ← EW.toE_mul] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  refine h s₁ m1 l0 l1 fun r hr ↦ ?_
  rw [f1 r (fun h ↦ hr (List.mem_append_left _ h))]
  have : r ≠ .r11 ∧ r ≠ .r12 := ⟨fun e ↦ hr (by simp [e]), fun e ↦ hr (by simp [e])⟩
  rsimp
  simp [this.1, this.2]

/-- `A := A + pair k`. -/
theorem addM_wp {k : Nat} {a b : EW} (hW : s.reg .rbp = env.work) (h9 : s.reg .r9 = a.c0)
    (h10 : s.reg .r10 = a.c1) (hb : EWAt s.mem (wd env.work k) b)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = (a + b).c0 → s₁.reg .r10 = (a + b).c1 →
      RegsFrame [.r9, .r10, .r11, .r12] s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (ldw .r11 k :: ldw .r12 (k + 1) :: eadd :: rest)) s P E := by
  refine ldw_wp hW hb.1 (ldw_wp (by rsimp; exact hW) (by rsimp; rw [← wd_wd]; exact hb.2) ?_)
  refine WP.then (eadd_spec _) fun s₁ ⟨e1, m1, f1⟩ ↦ ?_
  rsimp at e1
  rw [h9, h10, eOf_eq_toE, eOf_eq_toE, ← EW.toE_add] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  refine h s₁ m1 l0 l1 fun r hr ↦ ?_
  have : r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 :=
    ⟨fun e ↦ hr (by simp [e]), fun e ↦ hr (by simp [e]), fun e ↦ hr (by simp [e]),
      fun e ↦ hr (by simp [e])⟩
  rw [f1 r (by simp [this.1, this.2.1])]
  rsimp
  simp [this.2.2.1, this.2.2.2]

/-- `A := A · ofK (word k)`. -/
theorem scaleM_wp {k : Nat} {a : EW} {b : UInt64} (hW : s.reg .rbp = env.work)
    (h9 : s.reg .r9 = a.c0) (h10 : s.reg .r10 = a.c1) (hb : s.mem (wd env.work k) = some b)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = (EW.scale b a).c0 →
      s₁.reg .r10 = (EW.scale b a).c1 → RegsFrame (sqRegs ++ [.r11]) s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (ldw .r11 k :: escale :: rest)) s P E := by
  refine ldw_wp hW hb ?_
  refine WP.then (escale_spec _) fun s₁ ⟨e1, m1, f1⟩ ↦ ?_
  rsimp at e1
  rw [h9, h10, eOf_eq_toE, mul_comm, ← EW.toE_scale] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  refine h s₁ m1 l0 l1 fun r hr ↦ ?_
  rw [f1 r (fun h ↦ hr (List.mem_append_left _ h))]
  have : r ≠ .r11 := fun e ↦ hr (by simp [e])
  rsimp
  simp [this]

/-- `A := A²`. -/
theorem sqA_wp {a : EW} (h9 : s.reg .r9 = a.c0) (h10 : s.reg .r10 = a.c1)
    (h : ∀ s₁ : QState, s₁.mem = s.mem → s₁.reg .r9 = (a * a).c0 → s₁.reg .r10 = (a * a).c1 →
      RegsFrame sqRegs s s₁ → WP (blk rest) s₁ P E) :
    WP (blk (esq :: rest)) s P E := by
  refine WP.then (esq_spec _) fun s₁ ⟨e1, m1, f1⟩ ↦ ?_
  rw [h9, h10, eOf_eq_toE, sq, ← EW.toE_mul] at e1
  obtain ⟨l0, l1⟩ := lanes_of_eOf e1
  exact h s₁ m1 l0 l1 f1

end NativeVm.Code.P7
