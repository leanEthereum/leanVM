module

public import NativeVm.Code.Phase3.ShareCode
public import NativeVm.Code.Phase3.ShareMath

/-!
# The bytecode share: what its parts keep

The share writes `shareR`, `valueR`, `slotR` and `tmpR` (`shW`); its parts write smaller regions
inside them (`step3_within`), and keep the elements of the regions apart from those
(`ewat_keep`, `ewarr_keep`). `sh_storePair`: two stores of `A = (r9, r10)` into a region.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code

/-- The regions the share writes. -/
abbrev shW : List Region := [shareR, valueR, slotR, tmpR]

/-- Region facts: unfold the regions, then `omega`. -/
scoped macro "sh_reg" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Region.Apart, Region.stop, Within, Ok3, shClaimR, shConstR, shTailR, shFoldR, shareR, valueR,
    slotR, tmpR, wR, sreg, scratchR_off, busR_off, busR_size, claimsR_off, claimsR_size,
    scratchR_size, exists_eq_or_imp, exists_eq_left, shClaimW, shConstW, shTailW, shFoldW] <;> omega))

/-- `sh_reg` with the hypotheses unfolded too. -/
scoped macro "sh_reg_at" : tactic => `(tactic| (
  simp only [Region.Apart, Region.stop, Within, Ok3, shClaimR, shConstR, shTailR, shFoldR, shareR,
    valueR, slotR, tmpR, wR, sreg, scratchR_off, busR_off, busR_size, claimsR_off, claimsR_size,
    scratchR_size, shClaimW, shConstW, shTailW, shFoldW] at * <;> omega))

variable {env : Env} {inp : Input} {s s' : QState}

/-- A run writing regions inside others writes those. -/
theorem step3_within {regs : List Reg64} {ws ws' : List Region} (h : Step3 env regs ws s s')
    (hw : ∀ r ∈ ws, ∃ q ∈ ws', Within r q) : Step3 env regs ws' s s' :=
  ⟨h.rdi, h.regs, fun a hf ha ↦ h.mem a hf fun r hr hin ↦ by
    obtain ⟨q, hq, hrq⟩ := hw r hr
    exact ha q hq (in_within hin hrq), h.dom⟩

/-- An element in a region apart from those a run writes is kept. -/
theorem ewat_keep {regs : List Reg64} {ws : List Region} (hs : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r) {q : Region} (hq : Ok3 q)
    (hap : ∀ r ∈ ws, q.Apart r) {k : Nat} (hk : q.off ≤ k) (hk2 : k + 2 ≤ q.stop) {x : EW}
    (hx : EWAt s.mem (wd env.work k) x) : EWAt s'.mem (wd env.work k) x := by
  have hsm := hs.same hi hws hq.ok0 hap
  unfold Region.stop at hk2
  refine hx.congr fun j hj ↦ ?_
  have := hsm (k - q.off + j) (by omega)
  rwa [Region.at, wd_wd, show q.off + (k - q.off + j) = k + j by omega, ← wd_wd] at this

/-- An array in a region apart from those a run writes is kept. -/
theorem ewarr_keep {regs : List Reg64} {ws : List Region} (hs : Step3 env regs ws s s')
    (hi : Inputs env inp s.mem) (hws : ∀ r ∈ ws, Ok3 r) {q : Region} (hq : Ok3 q)
    (hap : ∀ r ∈ ws, q.Apart r) {k : Nat} {xs : Array EW} (hk : q.off ≤ k)
    (hk2 : k + 2 * xs.size ≤ q.stop) (hx : EWArr s.mem (wd env.work k) xs) :
    EWArr s'.mem (wd env.work k) xs := by
  have hsm := hs.same hi hws hq.ok0 hap
  unfold Region.stop at hk2
  refine hx.congr (n := 2 * xs.size) (fun j hj ↦ ?_) le_rfl
  have := hsm (k - q.off + j) (by omega)
  rwa [Region.at, wd_wd, show q.off + (k - q.off + j) = k + j by omega, ← wd_wd] at this

/-- **Two stores of `A`** into words `a`, `a + 1` of a region. -/
theorem sh_storePair {A0 A1 : Addr} {a : Nat} {r : Region} {xs : List Stmt} {P E : QState → Prop}
    (hr : Ok3 r) (ha : r.off ≤ a) (ha2 : a + 2 ≤ r.stop) (e0 : A0.eval s = wd env.work a)
    (e1 : A1.eval s = wd env.work (a + 1)) (hi : Inputs env inp s.mem)
    (k : ∀ s', Wrote env [r] s s' → EWAt s'.mem (wd env.work a) ⟨s.reg .r9, s.reg .r10⟩ →
      s'.reg = s.reg → WP (blk xs) s' P E) :
    WP (blk (I (.store A0 .r9) :: I (.store A1 .r10) :: xs)) s P E := by
  have hbd := hr.bounds
  have hdl := dataEnd_le inp.bytecode.size
  have hww := workWords_lt hi
  unfold Region.stop at ha2 hbd
  have hs0 := hi.ok3_some' hr (a := a) (by unfold Region.stop; omega)
  have hs1 := hi.ok3_some' hr (a := a + 1) (by unfold Region.stop; omega)
  refine wp_store e0 hs0 ?_
  have hne : wd env.work (a + 1) ≠ wd env.work a := fun e ↦ by
    rw [wd_inj (by omega) (by omega)] at e; omega
  have hs1' : ((s.setMem (wd env.work a) (s.reg .r9)).mem (wd env.work (a + 1))).isSome := by
    rw [QState.setMem_mem]; simp only [hne, ↓reduceIte]; exact hs1
  refine wp_store e1 hs1' ?_
  have hw := ((Wrote.refl env [r] s).setMem (r := r) (by simp) (k := a - r.off) (by omega)
    (by rwa [show r.off + (a - r.off) = a by omega]) (s.reg .r9)).setMem (r := r) (by simp)
    (k := a + 1 - r.off) (by omega)
    (by rw [show r.off + (a + 1 - r.off) = a + 1 by omega, show r.off + (a - r.off) = a by omega]
        exact hs1')
    ((s.setMem (wd env.work a) (s.reg .r9)).reg .r10)
  rw [show r.off + (a - r.off) = a by omega, show r.off + (a + 1 - r.off) = a + 1 by omega] at hw
  refine k _ hw ⟨?_, ?_⟩ (by simp)
  · simp only [QState.setMem_mem, Ne.symm hne, ↓reduceIte]
  · simp only [wd_wd, QState.setMem_mem, ↓reduceIte, QState.setMem_reg]

theorem sh_check_iff {x v : EW} {a b : UInt64} (h : eOf a b = x.toE) :
    (v == x) = true ↔ a = v.c0 ∧ b = v.c1 := by
  obtain ⟨rfl, rfl⟩ := eOf_eq_toE.mp h
  rw [beq_iff_eq]
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; cases x; cases v; simp_all

end NativeVm.Code.P3
