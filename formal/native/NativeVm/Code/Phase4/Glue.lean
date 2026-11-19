module

public import NativeVm.Code.Phase4.Step

/-!
# Facts through writes

What a block that writes the working area's words `W` (`Wr`) keeps: the context's word `ctxWork`
(`Wr.ctx`), a word, an element or an array of elements outside `W` (`Wr.word'`, `EWAt.wr`,
`EWArr.wr`), and `Wr` from a kernel's frame (`Wr.ofRange`).
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env} {w : UInt64} {W : Nat → Prop} {s s' : QState}

/-- The context's word `ctxWork` is kept by writes inside the working area's first words. -/
theorem Wr.ctx (h4 : Env4 env) (h : Wr env.work W s s') (hW : ∀ k, W k → k < 85438) :
    s'.mem (wd env.ctx ctxWork) = s.mem (wd env.ctx ctxWork) :=
  h _ fun k hk e ↦ h4.ctxNe k ctxWork (by rw [dataEnd_val]; exact hW k hk) (by decide) e.symm

/-- A word outside `W` is kept. -/
theorem Wr.word' (h : Wr w W s s') {j : Nat} (hj : j < 2305843009213693952)
    (hW : ∀ k, W k → k ≠ j ∧ k < 2305843009213693952) : s'.mem (wd w j) = s.mem (wd w j) :=
  h.word hj fun k hk ↦ ⟨(hW k hk).1.symm, (hW k hk).2⟩

/-- An element outside `W` is kept. -/
theorem EWAt.wr (h : Wr w W s s') {j : Nat} {x : EW} (hx : EWAt s.mem (wd w j) x)
    (hj : j + 1 < 2305843009213693952)
    (hW : ∀ k, W k → (k < j ∨ j + 1 < k) ∧ k < 2305843009213693952) : EWAt s'.mem (wd w j) x := by
  unfold EWAt at hx ⊢
  rw [wd_wd] at hx ⊢
  refine ⟨?_, ?_⟩
  · rw [h.word' (by omega) fun k hk ↦ ⟨by have := hW k hk; omega, (hW k hk).2⟩]; exact hx.1
  · rw [h.word' (by omega) fun k hk ↦ ⟨by have := hW k hk; omega, (hW k hk).2⟩]; exact hx.2

/-- An array of elements outside `W` is kept. -/
theorem EWArr.wr (h : Wr w W s s') {j : Nat} {xs : Array EW} (hx : EWArr s.mem (wd w j) xs)
    (hj : j + 2 * xs.size < 2305843009213693952)
    (hW : ∀ k, W k → (k < j ∨ j + 2 * xs.size ≤ k) ∧ k < 2305843009213693952) :
    EWArr s'.mem (wd w j) xs := fun i hi ↦ by
  have h0 := hx i hi
  rw [wd_wd] at h0 ⊢
  have := hW
  exact EWAt.wr h h0 (by have : i < xs.size := hi; omega) fun k hk ↦
    ⟨by have := hW k hk; omega, (hW k hk).2⟩

/-- A number outside `W` is kept. -/
theorem NatAt.wr (h : Wr w W s s') {j n : Nat} (hx : NatAt s.mem (wd w j) n)
    (hj : j < 2305843009213693952) (hW : ∀ k, W k → k ≠ j ∧ k < 2305843009213693952) :
    NatAt s'.mem (wd w j) n :=
  ⟨hx.1, by rw [h.word' hj hW]; exact hx.2⟩

/-- `Wr` from a frame over a range of words. -/
theorem Wr.ofRange {a n : Nat}
    (hm : ∀ x, (∀ k < n, x ≠ wd w (a + k)) → s'.mem x = s.mem x) (hW : ∀ k < n, W (a + k)) :
    Wr w W s s' := fun x hx ↦ hm x fun k hk ↦ hx _ (hW k hk)

/-- `Wr` of a block that writes no memory. -/
theorem Wr.ofEq (hm : s'.mem = s.mem) : Wr w W s s' := fun x _ ↦ by rw [hm]

/-- A word exists after writes. -/
theorem WS.wr {s s' : QState} (h : WS env s) (hd : ∀ a, (s'.mem a).isSome = (s.mem a).isSome) :
    WS env s' := fun k h1 h2 ↦ by rw [hd]; exact h k h1 h2

theorem WS.setMem {s : QState} (h : WS env s) (a v : UInt64) : WS env (s.setMem a v) :=
  fun k h1 h2 ↦ isSome_setMem a v _ (h k h1 h2)

theorem WS.setReg {s : QState} (h : WS env s) (r : Reg64) (v : UInt64) : WS env (s.setReg r v) := h

theorem DomEq.ofEq {s s' : QState} (hm : s'.mem = s.mem) : DomEq s s' := fun a ↦ by rw [hm]

/-- A run keeps which words exist: the normal exit's form. -/
theorem WP.dom {c : Stmt} {s : QState} {P E : QState → Prop} (h : WP c s P E) :
    WP c s (fun s' ↦ P s' ∧ DomEq s s') E :=
  WP.mono (WP.frame h) (fun _ h ↦ ⟨h.1, h.2.1⟩) fun _ h ↦ h.1

theorem not_arrRegs {r : Reg64} (h : r ∉ arrRegs) : r = .rdi ∨ r = .rsp := by
  cases r <;> simp_all

/-- `RegsFrame arrRegs` from `rdi` and `rsp`. -/
theorem rf_arr_of {s s' : QState} (h1 : s'.reg .rdi = s.reg .rdi) (h2 : s'.reg .rsp = s.reg .rsp) :
    RegsFrame arrRegs s s' := fun r hr ↦ by
  rcases not_arrRegs hr with rfl | rfl
  · exact h1
  · exact h2

theorem setReg_setReg (s : QState) (r : Reg64) (a b : UInt64) :
    (s.setReg r a).setReg r b = s.setReg r b := by
  cases s; simp [QState.setReg, Function.update_idem]

/-- Element `m` of an array of `E` from `wd w j`: `rax := (r - 1) · 16 + rbp`, `r = m + 1`. -/
theorem wp_elemSub {s : QState} {P E : QState → Prop} {xs : List Stmt} {r : Reg64} {w : UInt64}
    {j m : Nat} (hb : s.reg .rbp = wd w j) (hr : s.reg r = (m + 1).toUInt64)
    (h : WP (blk xs) (s.setReg .rax (wd w (j + 2 * m))) P E) :
    WP (blk (I (.mov .rax r) :: I (.subi .rax 1) :: I (.shli .rax 4) :: I (.add .rax .rbp) :: xs))
      s P E := by
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  simp only [setReg_setReg, QState.setReg_reg, ↓reduceIte, reduceCtorEq, hr, hb]
  rw [Field.int64One_toUInt64, Field.toUInt64_succ_sub,
    show ((4 : Nat).toUInt64) = (4 : Nat).toUInt64 from rfl, shl4_add]
  exact h

/-- Element `m` of an array of `E` from `wd w j`: `rax := r · 16 + rbp`, `r = m`. -/
theorem wp_elem {s : QState} {P E : QState → Prop} {xs : List Stmt} {r : Reg64} {w : UInt64}
    {j m : Nat} (hb : s.reg .rbp = wd w j) (hr : s.reg r = m.toUInt64)
    (h : WP (blk xs) (s.setReg .rax (wd w (j + 2 * m))) P E) :
    WP (blk (I (.mov .rax r) :: I (.shli .rax 4) :: I (.add .rax .rbp) :: xs)) s P E := by
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))
  simp only [setReg_setReg, QState.setReg_reg, ↓reduceIte, reduceCtorEq, hr, hb]
  rw [shl4_add]
  exact h

/-- Register frames compose into `arrRegs`. -/
theorem rf_arr {rs : List Reg64} {s₁ s₂ s₃ : QState} (h : RegsFrame arrRegs s₁ s₂)
    (h' : RegsFrame rs s₂ s₃) (hrs : ∀ r ∈ rs, r ∈ arrRegs := by decide) :
    RegsFrame arrRegs s₁ s₃ :=
  fun r hr ↦ (h' r fun hm ↦ hr (hrs r hm)).trans (h r hr)

end NativeVm.Code.P4
