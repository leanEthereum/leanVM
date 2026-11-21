module

public import NativeVm.Code.Phase6.Tables

/-!
# A layer's first check: `projected`, the segment weights, `iota`

The values a layer computes before its first check, each a block with no transcript step
(`Pure6`): `projected` (`pure_proj`), the claim's two segment weights (`pure_segW`), `iota`
(`pure_iota`), the sum of the instance weights (`pure_sumMu`); then the check (`chk1`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW} {p : UInt64}

/-! ## Code -/

/-- `mu_i · Σ_c [bit c of RMFE_PROJECT[i]] product_c`, `i` in `r15`. -/
def projTerm : Stmt := blk (idx16 ++ [I (.load .rbx (ix (2 * eProject))), msum eProd 47,
  I (.mov .r11 .r9), I (.mov .r12 .r10)] ++ idx16 ++
  [I (.load .r9 (ix (2 * eMu))), I (.load .r10 (ix (2 * eMu + 1))), emul])

/-- `projected`. -/
def projC : Stmt := blk [I (.load .r14 (at_ .rbp (wdisp (2 * eMuN)))), ssum (.reg .r14) projTerm]

/-- The registers `projTerm` writes. -/
abbrev pRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12]

/-- `rax` holds `16 i` through register updates. -/
macro "rax_tac" : tactic => `(tactic| (
  simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ↓reduceIte]; exact rax16 _))

theorem rax_idx (s : QState) (i : Nat) :
    ((s.setReg .rax (s.reg .r15)).setReg .rax (i.toUInt64 <<< (4 : Nat).toUInt64)).reg .rax =
      (8 * (2 * i)).toUInt64 := by
  simp only [QState.setReg_reg, ↓reduceIte]; exact rax16 i

theorem projTerm_spec {i : Nat} (hp : s.reg .rbp = p) (hs : Scr s.mem p g) (hi : i < 16)
    (h15 : s.reg .r15 = i.toUInt64) {E : QState → Prop} :
    WP projTerm s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = (g (eMu + i)).toE *
      ∑ c ∈ range 47, (if testBitW (g (eProject + i)).c0 c then (g (eProd + c)).toE else 0) ∧
      s'.mem = s.mem ∧ RegsFrame pRegs s s') E := by
  unfold projTerm
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [← List.cons_append, ← List.cons_append]
  refine idx16_spec h15 ?_
  refine ldi0 (o := eProject) (i := i) (by simpa using hp) (rax_idx s i) hs (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (msum_spec (src := eProd) (n := 47) (f := g) (p := p) (mask := (g (eProject + i)).c0)
    (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega) (by omega) (by simp))
    (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  have hp1 : s1.reg .rbp = p := by rw [e3 .rbp (by decide)]; simpa using hp
  have h15' : s1.reg .r15 = i.toUInt64 := by rw [e3 .r15 (by decide)]; simpa using h15
  fstep; fstep
  refine idx16_spec (by simpa using h15') ?_
  refine ldi0 (o := eMu) (i := i) (by simpa using hp1) (rax_idx _ i)
    (hs.congr fun a _ ↦ by simp [e2]) (by p6_omega) ?_
  refine ldi1 (o := eMu) (i := i) (by simpa using hp1) (by rax_tac)
    (hs.congr fun a _ ↦ by simp [e2]) (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s2 ⟨f1, f2, f3⟩ ↦ WP.blk_nil ⟨?_, ?_, ?_⟩)
    (fun _ h ↦ h))
  · rw [f1]; simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    rw [e1]; rfl
  · rw [f2]; simp [e2]
  · intro r hr
    simp only [pRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f3 r (by simp [eRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1])]
    simp only [QState.setReg_reg, hr.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2, ↓reduceIte]
    rw [e3 r (by simp [mRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1])]
    simp [hr.1, hr.2.1]

/-- The value `projC` computes. -/
def projV (g : Nat → EW) (n : Nat) : LeanVM.Parameters.E :=
  ∑ i ∈ range n, (g (eMu + i)).toE *
    ∑ c ∈ range 47, (if testBitW (g (eProject + i)).c0 c then (g (eProd + c)).toE else 0)

theorem sum_frame {L : List Reg64} {s t : QState} (h : RegsFrame (sumRegs ++ L) s t) {r : Reg64}
    (hr : r ∉ sumRegs ++ L) : t.reg r = s.reg r := h r hr

theorem projC_spec {n : Nat} (hp : s.reg .rbp = p) (hs : Scr s.mem p g)
    (hn : g eMuN = EW.ofK n.toUInt64) (hn16 : n ≤ 16) {E : QState → Prop} :
    WP projC s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = projV g n ∧ s'.mem = s.mem ∧
      RegsFrame (.r14 :: sumRegs ++ pRegs) s s') E := by
  unfold projC
  refine ld0 hp hs (by p6_omega) ?_
  rw [hn]
  refine WP.blk_cons (WP.mono (ssum_spec (N := n) (Lt := pRegs) (T := fun i ↦ (g (eMu + i)).toE *
    ∑ c ∈ range 47, (if testBitW (g (eProject + i)).c0 c then (g (eProd + c)).toE else 0))
    (by decide) (by omega) (fun t ht ↦ ?_) (fun i hi t ht h15 hm ↦ projTerm_spec
      (by rw [sum_frame ht (by decide)]; simpa using hp) (hs.congr fun a _ ↦ by rw [hm]; rfl)
      (by omega) h15)) (fun s1 ⟨e1, e2, e3⟩ ↦ WP.blk_nil ⟨e1, e2, ?_⟩) (fun _ h ↦ h))
  · rw [Rhs.eval, sum_frame ht (by decide)]; simp [EW.ofK]
  · intro r hr
    rw [e3 r (fun h ↦ hr (List.mem_cons_of_mem _ h))]
    simp only [QState.setReg_reg]
    rw [NativeVm.Transcript.ite_of_not (fun (h : r = .r14) ↦ hr (h ▸ List.mem_cons_self))]

theorem pure_proj (hin : Inputs env inp s0.mem) {n : Nat} (hn : g eMuN = EW.ofK n.toUInt64)
    (hn16 : n ≤ 16) :
    Pure6 env s0 (blk (projC :: stEl eProj)) g (Function.update g eProj (EW.ofE (projV g n))) :=
  pure_el hin (L := .r14 :: sumRegs ++ pRegs) (by p6_omega) (by decide) fun s hp hs ↦ by
    refine WP.mono (projC_spec hp hs hn hn16) (fun s' ⟨h1, h2, h3⟩ ↦ ⟨?_, h2, h3⟩) (fun _ h ↦ h)
    rw [h1, NativeVm.Equiv.EW.toE_ofE]

end NativeVm.Code.P6
