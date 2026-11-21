module

public import NativeVm.Code.Phase6.SC
public import NativeVm.Code.Phase6.Kern
public import NativeVm.Field.Powers

/-!
# Phase 6's blocks without a transcript step

`Pure6 c g g'`: from every state of phase 6 with the scratch `g`, `c` ends, never failing, with the
scratch `g'`; they compose (`Pure6.cons`) and precede a refinement (`Pure6.then`). Their builders:
`pure_el` (a value computed into `A`, stored), `pure_tab` (a table by `tab`), `pure_setW` (a word
constant), `pure_cp` (an element copied), `pure_pow` (`powers` by `epowers`). `chkEl o`: fail unless
`A` is the element `o` (`chkEl_refines`, against `Model.require`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code
open NativeVm.Transcript (wd wdisp Env)
open NativeVm.Field (eOf eOf_inj EArr epowers epowers_spec powRegs ew)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g g' g'' : Nat → EW}

/-- **A block with no transcript step**: from the scratch `g` to `g'`. -/
def Pure6 (env : Env) (s0 : QState) (c : Stmt) (g g' : Nat → EW) : Prop :=
  ∀ t s, St env s0 g t s → WP c s (St env s0 g' t) fun _ ↦ False

theorem Pure6.cons {c : Stmt} {cs : List Stmt} (h₁ : Pure6 env s0 c g g')
    (h₂ : Pure6 env s0 (blk cs) g' g'') : Pure6 env s0 (blk (c :: cs)) g g'' :=
  fun t s h ↦ WP.blk_cons (WP.mono (h₁ t s h) (fun s₁ h₁ ↦ h₂ t s₁ h₁) (fun _ h ↦ h))

theorem Pure6.nil : Pure6 env s0 (blk []) g g := fun _ _ h ↦ WP.blk_nil h

theorem Pure6.single {c : Stmt} (h : Pure6 env s0 c g g') : Pure6 env s0 (blk [c]) g g' := h

/-- A pure block, then a refinement. -/
theorem Pure6.then {α : Type} {c : Stmt} {cs : List Stmt} {m : VM α}
    {Q : α → TState → QState → Prop} {E : QState → Prop} (h₁ : Pure6 env s0 c g g')
    (h₂ : Refines (St env s0 g') (blk cs) m Q E) : Refines (St env s0 g) (blk (c :: cs)) m Q E :=
  Refines.pre_blk (fun t s h ↦ h₁ t s h) h₂

/-- **A value into an element**: `c` computes `x` into `A` from the scratch, writing no memory and
neither `rdi` nor `rbp`. -/
theorem pure_el (hin : Inputs env inp s0.mem) {c : Stmt} {o : Nat} {x : EW} {L : List Reg64}
    (ho : o < scrN) (hL : Reg64.rdi ∉ L ∧ Reg64.rbp ∉ L)
    (hc : ∀ s, s.reg .rbp = sb env → Scr s.mem (sb env) g →
      WP c s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = x.toE ∧ s'.mem = s.mem ∧
        RegsFrame L s s') fun _ ↦ False) :
    Pure6 env s0 (blk (c :: stEl o)) g (Function.update g o x) := by
  intro t s h
  refine WP.blk_cons (WP.mono (hc s h.2.2.1 h.2.2.2) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  obtain ⟨v9, v10⟩ := regs_of_eOf e1
  have hp1 : s1.reg .rbp = sb env := (e3 .rbp hL.2).trans h.2.2.1
  rw [← List.append_nil (stEl o)]
  refine stEl_spec ho hp1 (h.2.2.2.congr fun a _ ↦ by rw [e2]) v9 v10 fun s' h1 h2 h3 ↦
    WP.blk_nil (St.mk' hin h h1 (fun a ha ↦ by rw [h2 a ha, e2]) ?_ ?_)
  · rw [h3, e3 .rdi hL.1]
  · rw [h3, hp1, h.2.2.1]

/-- **A table by `tab`**, `r14` cleared first: the element `o + m` is `F m`, `m < N`. -/
theorem pure_tab (hin : Inputs env inp s0.mem) {o N : Nat} {val : Stmt} {Lv : List Reg64}
    {F : Nat → EW} (hN : o + N ≤ scrN)
    (hLv : Reg64.rbp ∉ Lv ∧ Reg64.r15 ∉ Lv ∧ Reg64.r14 ∉ Lv ∧ Reg64.rdi ∉ Lv)
    (hval : ∀ m < N, ∀ s, s.reg .rbp = sb env → Scr s.mem (sb env) (ovr g o m F) →
      s.reg .r15 = m.toUInt64 →
      WP val s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = (F m).toE ∧ s'.mem = s.mem ∧
        RegsFrame Lv s s') fun _ ↦ False) :
    Pure6 env s0 (blk [I (.movi .r14 0), tab o (.imm (Int64.ofNat N)) val]) g (ovr g o N F) := by
  intro t s h
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  have h' : St env s0 g t (s.setReg .r14 (Int64.toUInt64 0)) :=
    St.mk' hin h (h.2.2.2.congr fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by simp) (by simp)
  have := tab_spec (o := o) (d := 0) (N := N) (bound := .imm (Int64.ofNat N)) (val := val) (Lv := Lv)
    (F := F) (f0 := g) (E := fun _ ↦ False) (by omega) h'.2.2.1 (by simp; rfl) h'.2.2.2
    ⟨hLv.1, hLv.2.1, hLv.2.2.1⟩ (fun _ _ ↦ rfl) (fun m hm u hu h15 hS hM ↦ hval m hm u
      ((hu .rbp (by simp [hLv.1])).trans h'.2.2.1) (by simpa using hS) h15)
  refine WP.mono this (fun s' ⟨h1, h2, h3, _⟩ ↦ St.mk' hin h' (by simpa using h1) h2
    (h3 .rdi (by simp [hLv.2.2.2])) (h3 .rbp (by simp [hLv.1]))) (fun _ h ↦ h)

/-! ## Loads into `A` and `B` -/

/-- `A :=` the element `o`. -/
def ldA (o : Nat) : List Stmt :=
  [I (.load .r9 (at_ .rbp (wdisp (2 * o)))), I (.load .r10 (at_ .rbp (wdisp (2 * o + 1))))]

/-- `B :=` the element `o`. -/
def ldB (o : Nat) : List Stmt :=
  [I (.load .r11 (at_ .rbp (wdisp (2 * o)))), I (.load .r12 (at_ .rbp (wdisp (2 * o + 1))))]

theorem ldA_spec {o : Nat} {p : UInt64} {xs : List Stmt} {P E : QState → Prop}
    (hp : s.reg .rbp = p) (hs : Scr s.mem p g) (ho : o < scrN)
    (k : WP (blk xs) ((s.setReg .r9 (g o).c0).setReg .r10 (g o).c1) P E) :
    WP (blk (ldA o ++ xs)) s P E :=
  ld0 hp hs ho (ld1 (by simpa using hp) (hs.congr fun _ _ ↦ rfl) ho k)

theorem ldB_spec {o : Nat} {p : UInt64} {xs : List Stmt} {P E : QState → Prop}
    (hp : s.reg .rbp = p) (hs : Scr s.mem p g) (ho : o < scrN)
    (k : WP (blk xs) ((s.setReg .r11 (g o).c0).setReg .r12 (g o).c1) P E) :
    WP (blk (ldB o ++ xs)) s P E :=
  ld0 hp hs ho (ld1 (by simpa using hp) (hs.congr fun _ _ ↦ rfl) ho k)

/-! ## Constants and copies -/

/-- A word constant into the element `o`. -/
def setW (o : Nat) (w : Nat) : List Stmt :=
  blk [I (.movi .r9 (Int64.ofNat w)), I (.movi .r10 0)] :: stEl o

theorem pure_setW (hin : Inputs env inp s0.mem) {o w : Nat} (ho : o < scrN) :
    Pure6 env s0 (blk (setW o w)) g (Function.update g o (EW.ofK w.toUInt64)) :=
  pure_el hin ho (L := [.r9, .r10]) (by decide) fun s _ _ ↦ by
    fstep; fstep; fdone
    exact ⟨rfl, trivial, by rf_tac⟩

/-- The element `src` copied to `dst`. -/
def cpEl (src dst : Nat) : List Stmt := blk (ldA src) :: stEl dst

theorem pure_cp (hin : Inputs env inp s0.mem) {src dst : Nat} (hs : src < scrN) (hd : dst < scrN) :
    Pure6 env s0 (blk (cpEl src dst)) g (Function.update g dst (g src)) :=
  pure_el hin hd (L := [.r9, .r10]) (by decide) fun s hp hS ↦ by
    rw [← List.append_nil (ldA src)]
    refine ldA_spec hp hS hs (WP.blk_nil ⟨?_, rfl, by rf_tac⟩)
    simp; rfl

/-! ## Powers -/

/-- `powers` of the element `base`, `n` terms, from the element `o`. -/
def powEl (o n base : Nat) : List Stmt :=
  [I (.lea .r14 (at_ .rbp (wdisp (2 * o)))), I (.movi .r15 (Int64.ofNat n))] ++ ldB base ++ [epowers]

theorem scr_of_earr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {o n : Nat} {F : Nat → EW}
    (hs : Scr mem p g) (hn : o + n ≤ scrN)
    (he : EArr mem' (wd p (2 * o)) ((List.range n).map fun b ↦ (F b).toE))
    (hm : ∀ a, (∀ k < 2 * n, a ≠ wd (wd p (2 * o)) k) → mem' a = mem a) :
    Scr mem' p (ovr g o n F) := by
  have hN := scrN_lt
  intro k hk
  by_cases hko : o ≤ k ∧ k < o + n
  · rw [ovr_in hko.1 hko.2]
    have := he (k - o) (by simp; omega)
    simp only [List.getElem_map, List.getElem_range] at this
    have e0 : wd p (2 * o) + (16 * (k - o)).toUInt64 = wd p (2 * k) := by
      rw [show 16 * (k - o) = 8 * (2 * (k - o)) by omega, NativeVm.Transcript.wd_add]
      congr 1; omega
    simp only [NativeVm.Field.EAt, NativeVm.Code.EW.toE_limb0, NativeVm.Code.EW.toE_limb1] at this
    rw [e0, show wd p (2 * k) + 8 = wd p (2 * k + 1) by
      rw [← NativeVm.Transcript.wd_add]; rfl] at this
    exact this
  · rw [ovr_out (by omega)]
    have nk : ∀ l < 2, ∀ j, j < 2 * n → wd p (2 * k + l) ≠ wd (wd p (2 * o)) j := fun l hl j hj e ↦ by
      rw [NativeVm.Code.wd_wd] at e
      have := (NativeVm.Transcript.wd_inj (by omega) (by omega)).mp e
      omega
    have n0 := nk 0 (by omega)
    rw [Nat.add_zero] at n0
    rw [hm _ n0, hm _ (nk 1 (by omega))]
    exact hs k hk

theorem pure_pow (hin : Inputs env inp s0.mem) {o n base : Nat} (hn : o + n ≤ scrN)
    (hb : base < scrN) :
    Pure6 env s0 (blk (powEl o n base)) g
      (ovr g o n fun b ↦ EW.ofE ((g base).toE ^ b)) := by
  have hN := scrN_lt
  intro t s h
  obtain ⟨_, _, hp, hs⟩ := h
  unfold powEl
  simp only [List.cons_append, List.nil_append]
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
  rw [← List.singleton_append]
  refine ldB_spec (by simpa using hp) (hs.congr fun _ _ ↦ rfl) hb ?_
  have hdst : ((((s.setReg .r14 ((at_ .rbp (wdisp (2 * o))).eval s)).setReg .r15
      (Int64.ofNat n).toUInt64).setReg .r11 (g base).c0).setReg .r12 (g base).c1).reg .r14 =
      wd (sb env) (2 * o) := by simp [eval_el hp]
  refine WP.blk_cons (WP.mono (epowers_spec (n := n) hdst (by simp) (by omega)
    (fun k hk ↦ ?_)) (fun s' ⟨h1, h2, _, h4⟩ ↦ WP.blk_nil ?_) (fun _ h ↦ h))
  · simp only [QState.setReg_mem]
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show j + j = 2 * j by omega, ew, ← NativeVm.Transcript.wd, NativeVm.Code.wd_wd,
        show 2 * o + 2 * j = 2 * (o + j) by omega, (hs _ (by omega)).1]; rfl
    · rw [ew, ← NativeVm.Transcript.wd, NativeVm.Code.wd_wd,
        show 2 * o + (2 * j + 1) = 2 * (o + j) + 1 by omega, (hs _ (by omega)).2]; rfl
  · have hL : LeanVM.Protocol.Verifier.powers (eOf (g base).c0 (g base).c1) n =
        (List.range n).map fun b ↦ (EW.ofE ((g base).toE ^ b)).toE := by
      apply List.ext_getElem (by simp [LeanVM.Protocol.Verifier.powers,
        NativeVm.Field.powersFrom_length])
      intro i h1' h2'
      simp only [List.getElem_map, List.getElem_range, NativeVm.Equiv.EW.toE_ofE]
      rw [← List.getD_eq_getElem (d := 0), LeanVM.Protocol.Verifier.powers,
        NativeVm.Field.powersFrom_getD _ _ _ _ (by simpa using h2'), one_mul, eOf_toE]
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, hL] at h1
    have hout : ∀ a, ¬ InScr (sb env) a → ∀ k < 2 * n, a ≠ ew (wd (sb env) (2 * o)) k :=
      fun a ha k hk e ↦ ha ⟨2 * o + k, by omega, by rw [e, ew, ← NativeVm.Transcript.wd,
        NativeVm.Code.wd_wd]⟩
    refine St.mk' hin ⟨‹_›, ‹_›, hp, hs⟩ (scr_of_earr (n := n) hs hn h1 fun a ha ↦ ?_)
      (fun a ha ↦ by rw [h2 a (hout a ha)]; rfl) (h4 .rdi (by decide)) ?_
    · rw [h2 a fun k hk ↦ ha k hk]; rfl
    · rw [h4 .rbp (by decide)]; simp

/-! ## Checks -/

/-- Fail unless `A` is the element `o`. -/
def chkEl (o : Nat) : List Stmt := [I (.load .rax (at_ .rbp (wdisp (2 * o)))),
  failIf (.cmp .ne .r9 (.reg .rax)), I (.load .rax (at_ .rbp (wdisp (2 * o + 1)))),
  failIf (.cmp .ne .r10 (.reg .rax))]

theorem ew_beq {y z : EW} : (y == z) = true ↔ y.c0 = z.c0 ∧ y.c1 = z.c1 := by
  rw [NativeVm.Equiv.EW.beq_iff_toE, NativeVm.Equiv.EW.toE_inj]
  cases y; cases z; simp

theorem St.setReg (h : St env s0 g t s) {r : Reg64} (h1 : r ≠ .rdi) (h2 : r ≠ .rbp) (v : UInt64) :
    St env s0 g t (s.setReg r v) :=
  ⟨h.1.setReg h1 v, h.2.1.setReg h1 v, by
    rw [QState.setReg_reg, NativeVm.Transcript.ite_of_not (Ne.symm h2)]; exact h.2.2.1,
    h.2.2.2.congr fun _ _ ↦ rfl⟩

/-- A state of phase 6 through a run that writes no memory, `rdi` nor `rbp`. -/
theorem St.frame (hin : Inputs env inp s0.mem) {s s' : QState} (h : St env s0 g t s)
    (hm : s'.mem = s.mem) {L : List Reg64} (hL : RegsFrame L s s') (h1 : Reg64.rdi ∉ L := by decide)
    (h2 : Reg64.rbp ∉ L := by decide) : St env s0 g t s' :=
  St.mk' hin h (h.2.2.2.congr fun a _ ↦ by rw [hm]) (fun a _ ↦ by rw [hm]) (hL .rdi h1) (hL .rbp h2)

theorem kept_setReg {s : QState} (h : Kept env rs6 s0 s) (v : UInt64) :
    Kept env rs6 s0 (s.setReg .rax v) :=
  ⟨by rw [QState.setReg_reg, NativeVm.Transcript.ite_of_not (by decide)]; exact h.1, h.2⟩

/-- **A check against an element**, as `Model.require`. -/
theorem chkEl_refines {o : Nat} (ho : o < scrN) (y : EW) :
    Refines (fun t s ↦ St env s0 g t s ∧ eOf (s.reg .r9) (s.reg .r10) = y.toE) (blk (chkEl o))
      (Model.require (y == g o)) (fun _ t s ↦ St env s0 g t s) (Kept env rs6 s0) := by
  refine Refines.require fun t s ⟨h, hy⟩ ↦ ?_
  obtain ⟨v9, v10⟩ := regs_of_eOf hy
  have hk : Kept env rs6 s0 s := h.2.1.1
  unfold chkEl
  refine ld0 h.2.2.1 h.2.2.2 ho ?_
  by_cases e0 : y.c0 = (g o).c0
  · refine NativeVm.Transcript.wp_failIf (by simp [Cond.eval, Rhs.eval, v9, e0]) ?_
    refine ld1 (by simpa using h.2.2.1) (h.2.2.2.congr fun _ _ ↦ rfl) ho ?_
    by_cases e1 : y.c1 = (g o).c1
    · refine NativeVm.Transcript.wp_failIf (by simp [Cond.eval, Rhs.eval, v10, e1]) (WP.blk_nil ?_)
      refine ⟨ew_beq.mpr ⟨e0, e1⟩, ?_⟩
      exact (h.setReg (by decide) (by decide) _).setReg (by decide) (by decide) _
    · exact NativeVm.Transcript.wp_failIf_fail (by simp [Cond.eval, Rhs.eval, v10, e1])
        ⟨by rw [Bool.eq_false_iff]; exact fun hb ↦ e1 (ew_beq.mp hb).2,
          kept_setReg (kept_setReg hk _) _⟩
  · exact NativeVm.Transcript.wp_failIf_fail (by simp [Cond.eval, Rhs.eval, v9, e0])
      ⟨by rw [Bool.eq_false_iff]; exact fun hb ↦ e0 (ew_beq.mp hb).1, kept_setReg hk _⟩

end NativeVm.Code.P6
