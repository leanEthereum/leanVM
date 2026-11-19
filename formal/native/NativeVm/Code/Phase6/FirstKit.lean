module

public import NativeVm.Code.Phase6.Claim

/-!
# Phase 6's start: blocks that read the phase's state

`pure_elS` and `pure_tabS` are `pure_el` and `pure_tab` whose value code may read the whole state of
phase 6 (`St`): the context, the working area's regions outside the phase's. `vecEl B off`: the
element `off + m` (`m` in `r15`) of the `EVec` at word `B` of the working area, `0` past its end
(`vecEl_spec`). `evalsK_st`, `heightK_st`: `KECCAK`'s point and evaluations, and its log-height,
where a state of phase 6 reads them.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wdisp Env cw ctxWork)
open NativeVm.Field (eOf eOf_zero)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-! ## Blocks whose values read the phase's state -/

/-- `pure_el`, the value code run from a state of phase 6. -/
theorem pure_elS (hin : Inputs env inp s0.mem) {c : Stmt} {o : Nat} {x : EW} {L : List Reg64}
    (ho : o < scrN) (hL : Reg64.rdi ∉ L ∧ Reg64.rbp ∉ L)
    (hc : ∀ t s, St env s0 g t s →
      WP c s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = x.toE ∧ s'.mem = s.mem ∧
        RegsFrame L s s') fun _ ↦ False) :
    Pure6 env s0 (blk (c :: stEl o)) g (Function.update g o x) := by
  intro t s h
  refine WP.blk_cons (WP.mono (hc t s h) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  obtain ⟨v9, v10⟩ := regs_of_eOf e1
  have hp1 : s1.reg .rbp = sb env := (e3 .rbp hL.2).trans h.2.2.1
  rw [← List.append_nil (stEl o)]
  refine stEl_spec ho hp1 (h.2.2.2.congr fun a _ ↦ by rw [e2]) v9 v10 fun s' h1 h2 h3 ↦
    WP.blk_nil (St.mk' hin h h1 (fun a ha ↦ by rw [h2 a ha, e2]) ?_ ?_)
  · rw [h3, e3 .rdi hL.1]
  · rw [h3, hp1, h.2.2.1]

/-- `pure_tab`, the value code run from a state of phase 6. -/
theorem pure_tabS (hin : Inputs env inp s0.mem) {o N : Nat} {val : Stmt} {Lv : List Reg64}
    {F : Nat → EW} (hN : o + N ≤ scrN)
    (hLv : Reg64.rbp ∉ Lv ∧ Reg64.r15 ∉ Lv ∧ Reg64.r14 ∉ Lv ∧ Reg64.rdi ∉ Lv)
    (hval : ∀ m < N, ∀ t s, St env s0 (ovr g o m F) t s → s.reg .r15 = m.toUInt64 →
      WP val s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = (F m).toE ∧ s'.mem = s.mem ∧
        RegsFrame Lv s s') fun _ ↦ False) :
    Pure6 env s0 (blk [I (.movi .r14 0), tab o (.imm (Int64.ofNat N)) val]) g (ovr g o N F) := by
  intro t s h
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  have h' : St env s0 g t (s.setReg .r14 (Int64.toUInt64 0)) :=
    St.mk' hin h (h.2.2.2.congr fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (by simp) (by simp)
  have := tab_spec (o := o) (d := 0) (N := N) (bound := .imm (Int64.ofNat N)) (val := val) (Lv := Lv)
    (F := F) (f0 := g) (E := fun _ ↦ False) (by omega) h'.2.2.1 (by simp; rfl) h'.2.2.2
    ⟨hLv.1, hLv.2.1, hLv.2.2.1⟩ (fun _ _ ↦ rfl) (fun m hm u hu h15 hS hM ↦ hval m hm t u
      (St.mk' hin h' (by simpa using hS) hM (hu .rdi (by simp [hLv.2.2.2]))
        (hu .rbp (by simp [hLv.1]))) h15)
  refine WP.mono this (fun s' ⟨h1, h2, h3, _⟩ ↦ St.mk' hin h' (by simpa using h1) h2
    (h3 .rdi (by simp [hLv.2.2.2])) (h3 .rbp (by simp [hLv.1]))) (fun _ h ↦ h)

/-! ## An element of a vector in the working area -/

/-- `(r9, r10) :=` the element `off + m` (`m` in `r15`) of the `EVec` at word `B` of the working
area, `0` past its end. -/
def vecEl (B off : Nat) : Stmt := blk [I (.load .rsi (cw ctxWork)),
  I (.load .rdx (at_ .rsi (wdisp B))), I (.mov .rax .r15), I (.addi .rax (Int64.ofNat off)),
  .ite (.cmp .ltu .rax (.reg .rdx))
    (blk [I (.shli .rax 4),
      I (.load .r9 { base := .rsi, idx := some (.rax, .W8), disp := wdisp (B + 1) }),
      I (.load .r10 { base := .rsi, idx := some (.rax, .W8), disp := wdisp (B + 2) })])
    (blk [I (.movi .r9 0), I (.movi .r10 0)])]

/-- The registers `vecEl` writes. -/
abbrev vRegs : List Reg64 := [.rax, .rdx, .rsi, .r9, .r10]

theorem vecEl_spec {B off m cap : Nat} {xs : Array EW} {E : QState → Prop} (h : CodeRel env t s)
    (hrdi : s.reg .rdi = env.ctx) (hv : EVec s.mem (wd env.work B) cap xs)
    (h15 : s.reg .r15 = m.toUInt64) (hm : off + m < 2 ^ 32) :
    WP (vecEl B off) s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = (xs.getD (off + m) 0).toE ∧
      s'.mem = s.mem ∧ RegsFrame vRegs s s') E := by
  obtain ⟨hsz, ⟨_, hn⟩, harr⟩ := hv
  unfold vecEl
  refine NativeVm.Transcript.wp_load (NativeVm.Transcript.eval_cw hrdi _) h.layout.workPtr ?_
  refine NativeVm.Transcript.wp_load (eval_work (w := env.work) (by simp) _)
    (by rw [QState.setReg_mem]; exact hn) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
  have hrax : m.toUInt64 + (Int64.ofNat off).toUInt64 = (off + m).toUInt64 := by
    rw [show (Int64.ofNat off).toUInt64 = off.toUInt64 from rfl, NativeVm.Transcript.toUInt64_add,
      Nat.add_comm]
  apply WP.blk_cons
  apply WP.ite
  by_cases hlt : off + m < xs.size
  · have hc : decide ((off + m).toUInt64 < xs.size.toUInt64) = true := by
      rw [decide_eq_true_eq]; exact (toUInt64_lt' (by omega) (by omega)).mpr hlt
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ↓reduceIte, h15, hrax, hc]
    refine NativeVm.Transcript.wp_reg (by rfl) ?_
    have e := harr (off + m) hlt
    have hix : ((off + m).toUInt64 <<< (4 : Nat).toUInt64) = (8 * (2 * (off + m))).toUInt64 :=
      shl4_toUInt64 _
    refine NativeVm.Transcript.wp_load (v := xs[off + m].c0)
      (NativeVm.Transcript.eval_idx8 (b := env.work) (j := 0)
      (i := 2 * (off + m)) (by simp [NativeVm.Transcript.wd_zero])
      (by simp only [QState.setReg_reg, ↓reduceIte]; exact hix) _) ?_ ?_
    · simp only [QState.setReg_mem]
      rw [show 0 + 2 * (off + m) + (B + 1) = B + (1 + 2 * (off + m)) by omega, ← wd_wd, ← wd_wd]
      exact e.1
    refine NativeVm.Transcript.wp_load (v := xs[off + m].c1)
      (NativeVm.Transcript.eval_idx8 (b := env.work) (j := 0)
      (i := 2 * (off + m)) (by simp [NativeVm.Transcript.wd_zero])
      (by simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]; exact hix) _) ?_ ?_
    · simp only [QState.setReg_mem]
      rw [show 0 + 2 * (off + m) + (B + 2) = B + (1 + (2 * (off + m) + 1)) by omega, ← wd_wd,
        ← wd_wd, ← wd_wd]
      exact e.2
    refine WP.blk_nil (WP.blk_nil ⟨?_, rfl, by rf_tac⟩)
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
    rfl
  · have hc : decide ((off + m).toUInt64 < xs.size.toUInt64) = false := by
      rw [decide_eq_false_iff_not]
      exact fun h' ↦ hlt ((toUInt64_lt' (by omega) (by omega)).mp h')
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ↓reduceIte, h15, hrax, hc,
      Bool.false_eq_true]
    refine NativeVm.Transcript.wp_reg (by rfl) ?_
    refine NativeVm.Transcript.wp_reg (by rfl) ?_
    refine WP.blk_nil (WP.blk_nil ⟨?_, rfl, by rf_tac⟩)
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none,
      NativeVm.Equiv.EW.toE_zero]
    exact eOf_zero

/-! ## `KECCAK`'s evaluations and log-height where phase 6 reads them -/

/-- Phase 6's regions are regions. -/
theorem rs6_regions : ∀ r ∈ rs6, r ∈ regions := by decide +kernel

/-- Where `KECCAK`'s point starts in the working area. -/
abbrev evK : Nat := evalsR.off + evalStride * 5

/-- Where `KECCAK`'s evaluations start in the working area. -/
abbrev evKV : Nat := evalsR.off + (evalStride * 5 + vecWords tablePointCap)

theorem evalsK_st (hin : Inputs env inp s0.mem) {ev : Array (Array EW × Array EW)}
    (hev : EvalsAt s0.mem (evalsR.at env.work) ev) (hb : Base env rs6 s0 s) :
    EVec s.mem (wd env.work evK) tablePointCap (ev.getD opKeccak (#[], #[])).1 ∧
      EVec s.mem (wd env.work evKV) widthCap (ev.getD opKeccak (#[], #[])).2 := by
  have hS := hb.same hin rs6_regions (q := evalsR) (by decide +kernel) (by decide +kernel)
  have hsz : evalsR.size = evalStride * 6 := rfl
  have hst : evalStride = vecWords tablePointCap + vecWords widthCap := rfl
  obtain ⟨h1, h2⟩ := hev.2 5 (by decide)
  refine ⟨?_, ?_⟩
  · have := h1.congr (hS.sub (a := evalStride * 5) (m := vecWords tablePointCap) (by omega))
    rwa [Region.at, wd_wd] at this
  · have := h2.congr (hS.sub (a := evalStride * 5 + vecWords tablePointCap) (m := vecWords widthCap)
      (by omega))
    rwa [Region.at, wd_wd] at this

theorem heightK_st (hin : Inputs env inp s0.mem) {layout : LayoutW} {rate : Nat}
    (hlay : LayoutAt s0.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hb : Base env rs6 s0 s) :
    NatAt s.mem (wd env.work (layoutR.off + 9)) (layout.tableLogHeights.getD opKeccak 0) := by
  have hS := hb.same hin rs6_regions (q := layoutR) (by decide +kernel) (by decide +kernel)
  have := (hlay.heights 5 (by decide)).congr (hS (4 + 5) (by rw [layoutR_size]; omega))
  rwa [Region.at, wd_wd] at this

end NativeVm.Code.P6
