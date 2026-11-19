module

public import NativeVm.Code.Phase6.Loops
public import NativeVm.Code.Phase6.Sums
public import NativeVm.Code.Phase6.Lay
public import NativeVm.Code.Phase6.Pure
public import NativeVm.Field.Arrays

/-!
# Phase 6's sumchecks

`scP c co n`: `sumcheck claim c (replicate n none)` (plain mode, `n` rounds); `scE c co`: the
equality mode over the claim's point at `ePt`, its size the word `ePtN`. The claim is the element
`eSC`, the round's message the elements from `eMsg`, its challenge `eCh`, the round the word `eRK`;
round `k`'s challenge is written to the element `co + k`. Phase 6's rounds grind nothing
(`grindingBits` of their degrees is `0`).

A round: the message read (`rdEl`, `rdN`), the coefficient the claim fixes (`mid1`, plain; `mid0`,
equality), the challenge sampled (`smpEl`) and stored (`chSt`), the claim's next value
(`peval`, by `epolyEval`), the round counted (`incRK`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code
open NativeVm.Transcript (wd wd_add wd_zero wd_inj wdisp wdisp_toUInt64 Env Foot clobbers Keeps)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eOf_add eOf_zero epolyEval epolyEval_spec
  polyRegs)
open Finset

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-! ## Words of the scratch -/

/-- A store of word `0` of element `k`. -/
theorem Scr.store0 {mem : UInt64 → Option UInt64} {p : UInt64} {f : Nat → EW} (h : Scr mem p f)
    {k : Nat} (hk : k < scrN) (w : UInt64) :
    Scr (Function.update mem (wd p (2 * k)) (some w)) p (Function.update f k ⟨w, (f k).c1⟩) := by
  have hN := scrN_lt
  intro j hj
  rw [Function.update_apply, Function.update_apply, Function.update_apply]
  by_cases hjk : j = k
  · subst hjk
    simp only [wd_ne_el (p := p) (a := 2 * j + 1) (b := 2 * j) (by omega) (by omega) (by omega),
      ite_true, ite_false]
    exact ⟨trivial, (h j hj).2⟩
  · have e2 := wd_ne_el (p := p) (a := 2 * j) (b := 2 * k) (by omega) (by omega) (by omega)
    have e4 := wd_ne_el (p := p) (a := 2 * j + 1) (b := 2 * k) (by omega) (by omega) (by omega)
    simp only [e2, e4, hjk, ite_false]
    exact h j hj

/-! ## The code -/

/-- `(r9, r10) += eSC`. -/
def addSC : List Stmt := [I (.load .rax (at_ .rbp (wdisp (2 * eSC)))), I (.xor .r9 .rax),
  I (.load .rax (at_ .rbp (wdisp (2 * eSC + 1)))), I (.xor .r10 .rax)]

/-- Plain mode: `msg[1] := claim + Σ msg[2 ..]`. -/
def mid1 (c : Nat) : Stmt :=
  blk (ssum (.imm (Int64.ofNat (c - 2))) (lterm (eMsg + 2)) :: addSC ++ stEl (eMsg + 1))

/-- Equality mode: `msg[0] := claim + point[k] · Σ msg[1 ..]`. -/
def mid0 (c : Nat) : Stmt :=
  blk (ssum (.imm (Int64.ofNat (c - 1))) (lterm (eMsg + 1)) ::
    [I (.load .rax (at_ .rbp (wdisp (2 * eRK)))), I (.shli .rax 4), I (.load .r11 (ix (2 * ePt))),
      I (.load .r12 (ix (2 * ePt + 1))), emul] ++ addSC ++ stEl eMsg)

/-- The challenge into element `co + k`. -/
def chSt (co : Nat) : Stmt :=
  blk ([I (.load .r15 (at_ .rbp (wdisp (2 * eRK)))), I (.movi .r14 0),
    I (.load .r9 (at_ .rbp (wdisp (2 * eCh)))), I (.load .r10 (at_ .rbp (wdisp (2 * eCh + 1))))] ++
    tabStore co)

/-- The claim's next value: the message at the challenge. -/
def peval (c : Nat) : Stmt :=
  blk ([I (.lea .r13 (at_ .rbp (wdisp (2 * eMsg)))), I (.movi .r15 (Int64.ofNat c)),
    I (.load .r11 (at_ .rbp (wdisp (2 * eCh)))), I (.load .r12 (at_ .rbp (wdisp (2 * eCh + 1)))),
    epolyEval] ++ stEl eSC)

/-- The round counted; `r15` the next round, and in equality mode `r13` the rounds. -/
def incRK (eqm : Bool) : Stmt :=
  blk ([I (.load .r15 (at_ .rbp (wdisp (2 * eRK)))), I (.addi .r15 1),
    I (.store (at_ .rbp (wdisp (2 * eRK))) .r15)] ++
    if eqm then [I (.load .r13 (at_ .rbp (wdisp (2 * ePtN))))] else [])

/-- A plain round of `c` coefficients. -/
def roundP (c co : Nat) : Stmt :=
  blk [rdEl eMsg, rdN (eMsg + 2) (c - 2), mid1 c, smpEl eCh, chSt co, peval c, incRK false]

/-- An equality-mode round of `c` coefficients. -/
def roundE (c co : Nat) : Stmt :=
  blk [rdN (eMsg + 1) (c - 1), mid0 c, smpEl eCh, chSt co, peval c, incRK true]

/-- The round counter cleared. -/
def scInit : List Stmt := [I (.movi .r15 0), I (.storei (at_ .rbp (wdisp (2 * eRK))) 0),
  I (.storei (at_ .rbp (wdisp (2 * eRK + 1))) 0)]

/-- **Plain mode**, `n` rounds. -/
def scP (c co n : Nat) : Stmt :=
  blk (scInit ++ [.loop (.cmp .ltu .r15 (.imm (Int64.ofNat n))) (roundP c co)])

/-- **Equality mode** over the point at `ePt`, `ePtN` rounds. -/
def scE (c co : Nat) : Stmt :=
  blk (scInit ++ [I (.load .r13 (at_ .rbp (wdisp (2 * ePtN)))),
    .loop (.cmp .ltu .r15 (.reg .r13)) (roundE c co)])

/-! ## The steps -/

theorem rf_rdi_rbp {L : List Reg64} {s s' : QState} (h : RegsFrame L s s')
    (h1 : Reg64.rdi ∉ L := by decide) (h2 : Reg64.rbp ∉ L := by decide) :
    s'.reg .rdi = s.reg .rdi ∧ s'.reg .rbp = s.reg .rbp := ⟨h .rdi h1, h .rbp h2⟩

/-- `addSC`. -/
theorem addSC_spec {p : UInt64} {xs : List Stmt} {P E : QState → Prop} (hp : s.reg .rbp = p)
    (hs : Scr s.mem p g)
    (k : WP (blk xs) ((((s.setReg .rax (g eSC).c0).setReg .r9 (s.reg .r9 ^^^ (g eSC).c0)).setReg
      .rax (g eSC).c1).setReg .r10 (s.reg .r10 ^^^ (g eSC).c1)) P E) :
    WP (blk (addSC ++ xs)) s P E := by
  unfold addSC
  simp only [List.cons_append, List.nil_append]
  refine ld0 hp hs (by p6_omega) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine ld1 (by simp [hp]) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  simpa using k

variable (env inp s0)

/-- **`mid1`**: the plain round's second coefficient. -/
theorem mid1_spec (hin : Inputs env inp s0.mem) {c : Nat} (hc : 2 ≤ c ∧ c ≤ 4)
    (h : St env s0 g t s) {x : EW}
    (hx : x.toE = (g eSC).toE + ∑ i ∈ range (c - 2), (g (eMsg + 2 + i)).toE) :
    WP (mid1 c) s (fun s' ↦ St env s0 (Function.update g (eMsg + 1) x) t s') (fun _ ↦ False) := by
  obtain ⟨hc', hb, hp, hs⟩ := h
  refine WP.mono (St.step (f' := Function.update g (eMsg + 1) x) (R := fun _ ↦ True) hin
    ⟨hc', hb, hp, hs⟩ ?_) (fun _ h ↦ h.1) (fun _ h ↦ h)
  unfold mid1
  refine WP.blk_cons (WP.mono (ssum_spec (T := fun i ↦ (g (eMsg + 2 + i)).toE)
    (Lt := [.rax, .r9, .r10]) (by decide) (by omega) (fun _ _ ↦ rfl)
    (fun i hi t' ht h15 hm ↦ lterm_spec (by rw [ht .rbp (by decide)]; exact hp)
      (hs.congr fun a _ ↦ by rw [hm]) (by p6_omega) h15)) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_)
    (fun _ h ↦ h))
  have hs1 : Scr s1.mem (sb env) g := hs.congr fun a _ ↦ by rw [e2]
  have hp1 : s1.reg .rbp = sb env := by rw [e3 .rbp (by decide)]; exact hp
  refine addSC_spec hp1 hs1 ?_
  have hv : eOf (s1.reg .r9 ^^^ (g eSC).c0) (s1.reg .r10 ^^^ (g eSC).c1) = x.toE := by
    rw [eOf_add, e1, hx, eOf_toE, add_comm]
  obtain ⟨v9, v10⟩ := regs_of_eOf hv
  rw [← List.append_nil (stEl _)]
  refine stEl_spec (by p6_omega) (by simp [hp1]) (hs1.congr fun _ _ ↦ rfl) (by simp [v9])
    (by simp [v10]) fun s' h1 h2 h3 ↦ WP.blk_nil ⟨h1, fun a ha ↦ by rw [h2 a ha]; simp only [QState.setReg_mem]; rw [e2], ?_, ?_, trivial⟩
  · rw [h3]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]; exact e3 .rdi (by decide)
  · rw [h3]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]; exact e3 .rbp (by decide)

/-- **`mid0`**: the equality-mode round's first coefficient, `k` the round. -/
theorem mid0_spec (hin : Inputs env inp s0.mem) {c k : Nat} (hc : 1 ≤ c ∧ c ≤ 4) (hk : k < 32)
    (h : St env s0 g t s) (hrk : g eRK = EW.ofK k.toUInt64) {x : EW}
    (hx : x.toE = (g eSC).toE + (g (ePt + k)).toE * ∑ i ∈ range (c - 1), (g (eMsg + 1 + i)).toE) :
    WP (mid0 c) s (fun s' ↦ St env s0 (Function.update g eMsg x) t s') (fun _ ↦ False) := by
  obtain ⟨hc', hb, hp, hs⟩ := h
  refine WP.mono (St.step (f' := Function.update g eMsg x) (R := fun _ ↦ True) hin
    ⟨hc', hb, hp, hs⟩ ?_) (fun _ h ↦ h.1) (fun _ h ↦ h)
  unfold mid0
  refine WP.blk_cons (WP.mono (ssum_spec (T := fun i ↦ (g (eMsg + 1 + i)).toE)
    (Lt := [.rax, .r9, .r10]) (by decide) (by omega) (fun _ _ ↦ rfl)
    (fun i hi t' ht h15 hm ↦ lterm_spec (by rw [ht .rbp (by decide)]; exact hp)
      (hs.congr fun a _ ↦ by rw [hm]) (by p6_omega) h15)) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_)
    (fun _ h ↦ h))
  have hs1 : Scr s1.mem (sb env) g := hs.congr fun a _ ↦ by rw [e2]
  have hp1 : s1.reg .rbp = sb env := by rw [e3 .rbp (by decide)]; exact hp
  refine ld0 hp1 hs1 (by p6_omega) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine ldi0 (o := ePt) (i := k) (by simp [hp1]) (by simp only [QState.setReg_reg, ↓reduceIte, hrk, EW.ofK]; exact rax16 k)
    (hs1.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine ldi1 (o := ePt) (i := k) (by simp [hp1]) (by simp only [QState.setReg_reg, ↓reduceIte, hrk, EW.ofK]; exact rax16 k)
    (hs1.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s2 ⟨f1, f2, f3⟩ ↦ ?_) (fun _ h ↦ h))
  simp only [QState.setReg_reg, QState.setReg_mem, reduceCtorEq, ↓reduceIte] at f1 f2
  have hs2 : Scr s2.mem (sb env) g := hs1.congr fun a _ ↦ by rw [f2]
  have hp2 : s2.reg .rbp = sb env := by rw [f3 .rbp (by decide)]; simpa using hp1
  refine addSC_spec hp2 hs2 ?_
  have hv : eOf (s2.reg .r9 ^^^ (g eSC).c0) (s2.reg .r10 ^^^ (g eSC).c1) = x.toE := by
    rw [eOf_add, f1, e1, hx, eOf_toE, eOf_toE, add_comm, mul_comm]
  obtain ⟨v9, v10⟩ := regs_of_eOf hv
  rw [← List.append_nil (stEl _)]
  refine stEl_spec (by p6_omega) (by simp [hp2]) (hs2.congr fun _ _ ↦ rfl) (by simp [v9])
    (by simp [v10]) fun s' h1 h2 h3 ↦ WP.blk_nil ⟨h1, fun a ha ↦ by
      rw [h2 a ha]; simp only [QState.setReg_mem]; rw [f2, e2], ?_, ?_, trivial⟩
  · rw [h3]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [f3 .rdi (by decide)]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    exact e3 .rdi (by decide)
  · rw [h3]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]; rw [hp2, hp]

/-- **`chSt`**: the challenge into element `co + k`, `k` the round. -/
theorem chSt_spec (hin : Inputs env inp s0.mem) {co k : Nat} (hk : co + k < scrN)
    (h : St env s0 g t s) (hrk : g eRK = EW.ofK k.toUInt64) :
    WP (chSt co) s (fun s' ↦ St env s0 (Function.update g (co + k) (g eCh)) t s') (fun _ ↦ False) := by
  obtain ⟨hc', hb, hp, hs⟩ := h
  refine WP.mono (St.step (f' := Function.update g (co + k) (g eCh)) (R := fun _ ↦ True) hin
    ⟨hc', hb, hp, hs⟩ ?_) (fun _ h ↦ h.1) (fun _ h ↦ h)
  unfold chSt
  simp only [List.cons_append, List.nil_append]
  refine ld0 hp hs (by p6_omega) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine ld0 (by simp [hp]) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine ld1 (by simp [hp]) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine WP.mono (tabStore_spec (o := co) (d := 0) (m := k) (p := sb env) (f := g) (by omega)
    ?_ ?_ ?_ ?_ (g eCh) ?_ ?_)
    (fun s' ⟨h1, h2, h3, _⟩ ↦ ⟨by simpa using h1, fun a ha ↦ by rw [h2 a ha]; simp, ?_, ?_, trivial⟩)
    (fun _ h ↦ h)
  · simp [hp]
  · simp; rfl
  · simp [hrk, EW.ofK]
  · exact hs.congr fun _ _ ↦ rfl
  · simp
  · simp
  · rw [h3 .rdi (by decide)]; simp
  · rw [h3 .rbp (by decide)]; simp

/-- The elements `[o, o + n)` as values. -/
def vals (g : Nat → EW) (o n : Nat) : List LeanVM.Parameters.E := (List.range n).map fun i ↦ (g (o + i)).toE

/-- **`peval`**: the claim's next value, the message at the challenge. -/
theorem peval_spec (hin : Inputs env inp s0.mem) {c : Nat} (hc : c ≤ 4) (h : St env s0 g t s)
    {x : EW} (hx : x.toE = LeanVM.Protocol.Verifier.polyEval (vals g eMsg c) (g eCh).toE) :
    WP (peval c) s (fun s' ↦ St env s0 (Function.update g eSC x) t s') (fun _ ↦ False) := by
  obtain ⟨hc', hb, hp, hs⟩ := h
  refine WP.mono (St.step (f' := Function.update g eSC x) (R := fun _ ↦ True) hin
    ⟨hc', hb, hp, hs⟩ ?_) (fun _ h ↦ h.1) (fun _ h ↦ h)
  unfold peval
  simp only [List.cons_append, List.nil_append]
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine ld0 (by simp [hp]) hs (by p6_omega) ?_
  refine ld1 (by simp [hp]) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  have hE := hs.earr (o := eMsg) (n := c) (by p6_omega)
  refine WP.blk_cons (WP.mono (epolyEval_spec (cs := vals g eMsg c) ?_ ?_ ?_)
    (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  · simp only [QState.setReg_reg, QState.setReg_mem, reduceCtorEq, ↓reduceIte, eval_el hp]
    exact hE
  · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, vals, List.length_map,
      List.length_range]
    rfl
  · simp [vals]; omega
  simp only [QState.setReg_reg, QState.setReg_mem, reduceCtorEq, ↓reduceIte] at e1 e2
  rw [eOf_toE, ← hx] at e1
  obtain ⟨v9, v10⟩ := regs_of_eOf e1
  have hp1 : s1.reg .rbp = sb env := by rw [e3 .rbp (by decide)]; simpa using hp
  rw [← List.append_nil (stEl _)]
  refine stEl_spec (by p6_omega) hp1 (hs.congr fun a _ ↦ by rw [e2]) v9 v10
    fun s' h1 h2 h3 ↦ WP.blk_nil ⟨h1, fun a ha ↦ by rw [h2 a ha, e2], ?_, ?_, trivial⟩
  · rw [h3, e3 .rdi (by decide)]; rfl
  · rw [h3, hp1, hp]

theorem mem_setMem (u : QState) (a x : UInt64) :
    (u.setMem a x).mem = Function.update u.mem a (some x) := rfl

/-- **`incRK`**: the round counted. -/
theorem incRK_spec (hin : Inputs env inp s0.mem) {eqm : Bool} {k n : Nat}
    (h : St env s0 g t s) (hrk : g eRK = EW.ofK k.toUInt64) (hn : g ePtN = EW.ofK n.toUInt64) :
    WP (incRK eqm) s (fun s' ↦ St env s0 (Function.update g eRK (EW.ofK (k + 1).toUInt64)) t s' ∧
      s'.reg .r15 = (k + 1).toUInt64 ∧ (eqm = true → s'.reg .r13 = n.toUInt64)) (fun _ ↦ False) := by
  obtain ⟨hc', hb, hp, hs⟩ := h
  refine St.step (f' := Function.update g eRK (EW.ofK (k + 1).toUInt64)) hin ⟨hc', hb, hp, hs⟩ ?_
  unfold incRK
  simp only [List.cons_append, List.nil_append]
  refine ld0 hp hs (by p6_omega) ?_
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine NativeVm.Transcript.wp_store (eval_el (p := sb env) (by simpa using hp) _)
    (by rw [QState.setReg_mem, QState.setReg_mem, (hs _ (by p6_omega)).1]; rfl) ?_
  have r15 : (g eRK).c0 + Int64.toUInt64 1 = (k + 1).toUInt64 := by
    rw [hrk]; exact NativeVm.Transcript.toUInt64_succ k
  have hs' : Scr (Function.update s.mem (wd (sb env) (2 * eRK)) (some (k + 1).toUInt64)) (sb env)
      (Function.update g eRK (EW.ofK (k + 1).toUInt64)) := by
    have := hs.store0 (k := eRK) (by p6_omega) ((k + 1).toUInt64)
    rwa [hrk] at this
  have hreg : ((s.setReg .r15 (g eRK).c0).setReg .r15
      ((s.setReg .r15 (g eRK).c0).reg .r15 + Int64.toUInt64 1)).reg .r15 = (k + 1).toUInt64 := by
    simp only [QState.setReg_reg, ↓reduceIte]; exact r15
  have hmem : ∀ a, ¬ InScr (sb env) a →
      Function.update s.mem (wd (sb env) (2 * eRK)) (some (k + 1).toUInt64) a = s.mem a :=
    fun a ha ↦ Function.update_of_ne (fun e ↦ ha ⟨_, by p6_omega, e⟩) _ _
  cases eqm
  · refine WP.blk_nil ⟨?_, fun a ha ↦ ?_, rfl, rfl, ?_, fun h ↦ absurd h (by decide)⟩
    · rw [mem_setMem, QState.setReg_mem, QState.setReg_mem, hreg]; exact hs'
    · rw [mem_setMem, QState.setReg_mem, QState.setReg_mem, hreg]; exact hmem a ha
    · rw [QState.setMem_reg]; exact hreg
  · have hs2 : Scr ((((s.setReg .r15 (g eRK).c0).setReg .r15
        ((s.setReg .r15 (g eRK).c0).reg .r15 + Int64.toUInt64 1)).setMem (wd (sb env) (2 * eRK))
        (((s.setReg .r15 (g eRK).c0).setReg .r15
        ((s.setReg .r15 (g eRK).c0).reg .r15 + Int64.toUInt64 1)).reg .r15)).mem) (sb env)
        (Function.update g eRK (EW.ofK (k + 1).toUInt64)) := by
      rw [mem_setMem, QState.setReg_mem, QState.setReg_mem, hreg]; exact hs'
    refine ld0 (p := sb env) (by simpa using hp) hs2 (by p6_omega)
      (WP.blk_nil ⟨?_, fun a ha ↦ ?_, rfl, ?_, ?_, ?_⟩)
    · rw [QState.setReg_mem]; exact hs2
    · rw [QState.setReg_mem, mem_setMem, QState.setReg_mem, QState.setReg_mem, hreg]
      exact hmem a ha
    · simp
    · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, QState.setMem_reg]; exact r15
    · intro _
      simp only [QState.setReg_reg, ↓reduceIte]
      rw [Function.update_of_ne (by p6_omega), hn]; rfl

end NativeVm.Code.P6
