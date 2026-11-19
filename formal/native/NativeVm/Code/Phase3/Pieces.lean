module

public import NativeVm.Code.Phase3.Frame
public import NativeVm.Code.Phase3.Fp

/-!
# Phase 3's small parts

`lensCode`: the memory's and the bytecode's point lengths, `min(log, depth)`, into `lenW 0`,
`lenW 1`; `formsInit`: every bus form empty; `pcCode`: `g^(2^logBytecode − 1)` into slot `5`;
`busTail`: the GKR point and the totals into `busR`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

variable {env : Env} {inp : Input} {s : QState} {E : QState → Prop}

/-- The words of the two lengths. -/
def lenW (i : Nat) : Nat := 52924 + i

/-- Length `i`'s word as a region. -/
def lenR (i : Nat) : Region := ⟨lenW i, 1⟩

theorem pc_depthR_off : depthR.off = 52879 := by decide

/-- `min(layout word i, depth)` into `lenW i`. -/
def lenCode (i : Nat) : Stmt := blk [
  I (.load .rax (at_ .r14 (wdisp (layoutR.off + i)))), I (.load .rcx (at_ .r14 (wdisp 52879))),
  .ite (.cmp .ltu .rcx (.reg .rax)) (I (.mov .rax .rcx)) .skip,
  I (.store (at_ .r14 (wdisp (lenW i))) .rax)]

/-- Both lengths. -/
def lensCode : Stmt := blk [I (.load .r14 (cw ctxWork)), lenCode 0, lenCode 1]

theorem valsR_stop : valsR.stop = 52926 := by decide

theorem valsR_ok : Ok3 valsR := ok3_sreg (by norm_num)

theorem lenCode_spec {i a d : Nat} (h14 : s.reg .r14 = env.work) (hi : Inputs env inp s.mem)
    (ha : NatAt s.mem (wd env.work (layoutR.off + i)) a) (hd : NatAt s.mem (wd env.work 52879) d)
    (hi2 : i < 2) :
    WP (lenCode i) s (fun s' ↦ NatAt s'.mem (wd env.work (lenW i)) (min a d) ∧
      Wrote env [lenR i] s s' ∧ RegsFrame [.rax, .rcx] s s') E := by
  have hs := hi.ok3_some' valsR_ok (a := lenW i) (by rw [valsR_stop]; unfold lenW; omega)
  unfold lenCode
  refine wp_load (eval_work h14 _) ha.2 ?_
  refine wp_load (eval_work (by rsimp; exact h14) _) hd.2 ?_
  have key : ∀ s1 : QState, s1.mem = s.mem → s1.reg .r14 = env.work → s1.reg .rdi = s.reg .rdi →
      RegsFrame [.rax, .rcx] s s1 → s1.reg .rax = (min a d).toUInt64 →
      WP (blk [I (.store (at_ .r14 (wdisp (lenW i))) .rax)]) s1
        (fun s' ↦ NatAt s'.mem (wd env.work (lenW i)) (min a d) ∧
          Wrote env [lenR i] s s' ∧ RegsFrame [.rax, .rcx] s s') E := by
    intro s1 hm h14' hrdi hf hax
    refine wp_store (eval_work h14' _) (by rw [hm]; exact hs) (WP.blk_nil ⟨⟨by have := ha.1; have := hd.1; omega, ?_⟩, ?_, hf⟩)
    · rw [QState.setMem_mem, ite_eq_left_of_eq_true _ _ (eq_true rfl), hax]
    · exact wrote_store (r := lenR i) (by simp) le_rfl (by simp [lenR, Region.stop]) hm hrdi hs _
  refine WP.blk_cons (WP.ite ?_)
  rw [cond_ltu, rhs_reg]
  rsimp
  by_cases hlt : d < a
  · rw [decide_eq_true ((toUInt64_lt hd.1 ha.1).mpr hlt)]
    refine WP.ins rfl (key _ rfl (by rsimp; exact h14) (by rsimp) (by rf_tac) ?_)
    rsimp; rw [Nat.min_eq_right (by omega)]
  · rw [decide_eq_false (fun h ↦ hlt ((toUInt64_lt hd.1 ha.1).mp h))]
    refine WP.skip (key _ rfl (by rsimp; exact h14) (by rsimp) (by rf_tac) ?_)
    rsimp; rw [Nat.min_eq_left (by omega)]

theorem lensCode_spec {d : Nat} {layout : LayoutW} {rate : Nat} (hrdi : s.reg .rdi = env.ctx)
    (hwp : s.mem (wd env.ctx ctxWork) = some env.work) (hi : Inputs env inp s.mem)
    (hl : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hd : NatAt s.mem (depthR.at env.work) d) :
    WP lensCode s (fun s' ↦ NatAt s'.mem (wd env.work (lenW 0)) (min layout.logMemory d) ∧
      NatAt s'.mem (wd env.work (lenW 1)) (min layout.logBytecode d) ∧
      Wrote env [valsR] s s' ∧ RegsFrame [.r14, .rax, .rcx] s s') E := by
  unfold lensCode
  rw [Region.at, pc_depthR_off] at hd
  have hl0 : NatAt s.mem (wd env.work (layoutR.off + 0)) layout.logMemory := by
    have := hl.logMemory; rwa [Region.at] at this
  have hl1 : NatAt s.mem (wd env.work (layoutR.off + 1)) layout.logBytecode := by
    have := hl.logBytecode; rwa [Region.at, wd_wd] at this
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  refine WP.blk_cons (WP.mono (lenCode_spec (by rsimp) hi hl0 hd (by norm_num)) ?_ fun _ h ↦ h)
  rintro s1 ⟨h0, hw1, hf1⟩
  have hb : ∀ r ∈ [lenR 0], r.stop ≤ 2 ^ 61 := by simp [lenR, lenW, Region.stop]
  have hb1 : ∀ r ∈ [lenR 1], r.stop ≤ 2 ^ 61 := by simp [lenR, lenW, Region.stop]
  have lo : layoutR.off = 69 := by decide
  have hi1 : Inputs env inp s1.mem := (show Inputs env inp (s.setReg .r14 env.work).mem from hi).step3
    (fun r hr ↦ (List.mem_singleton.mp hr) ▸ ok3_sreg (off := 254) (size := 1) (by norm_num)) hw1.step (by rsimp; exact hrdi)
  refine WP.blk_cons (WP.mono (lenCode_spec (s := s1) ((hf1 .r14 (by decide)).trans (by rsimp)) hi1
    (hl1.congr (hw1.word (by simp [lo, lenR, lenW, Region.stop]) (by rw [lo]; norm_num) hb))
    (hd.congr (hw1.word (by simp [lenR, lenW, Region.stop]) (by norm_num) hb)) (by norm_num)) ?_
    fun _ h ↦ h)
  rintro s2 ⟨h1, hw2, hf2⟩
  have w01 : ∀ i < 2, ∀ r ∈ [lenR i], ∃ q ∈ [valsR], Within r q := fun i hi r hr ↦
    ⟨valsR, by simp, by
      rw [List.mem_singleton.mp hr]
      exact ⟨by rw [valsR_off]; simp only [lenR, lenW]; omega, by rw [valsR_stop]; simp [lenR, lenW, Region.stop]; omega⟩⟩
  refine WP.blk_nil ⟨h0.congr (hw2.word (by simp [lenR, lenW, Region.stop]) (by simp [lenW]) hb1),
    h1, (((Wrote.refl env [valsR] s).setReg (r := .r14) (by decide) env.work).trans
      (hw1.widen (w01 0 (by norm_num)))).trans (hw2.widen (w01 1 (by norm_num))), fun r hr ↦ ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [hf2 r (by simp [hr.2.1, hr.2.2]), hf1 r (by simp [hr.2.1, hr.2.2])]
  rsimp
  simp [hr.1]

/-- `g^(2^logBytecode − 1)` into slot `5`, from `g` in slot `1`; `r14` at the working area. -/
def pcCode : Stmt := blk [
  I (.load .rcx (at_ .r14 (wdisp (layoutR.off + 1)))), I (.movi .r13 1), I (.shlcl .r13),
  I (.subi .r13 1), I (.load .r9 (at_ .r14 (wdisp sGen))), I (.load .r10 (at_ .r14 (wdisp (sGen + 1)))),
  NativeVm.Field.epow,
  I (.store (at_ .r14 (wdisp sPc)) .r9), I (.store (at_ .r14 (wdisp (sPc + 1))) .r10)]

theorem pcR_ok : Ok3 ⟨sPc, 2⟩ := .inr (.inr ⟨by decide, by decide⟩)

theorem pcCode_spec {lb : Nat} (h14 : s.reg .r14 = env.work) (hi : Inputs env inp s.mem)
    (hlb : NatAt s.mem (wd env.work (layoutR.off + 1)) lb) (hlb' : lb ≤ 30)
    (hg : EWAt s.mem (wd env.work sGen) gen) :
    WP pcCode s (fun s' ↦ EWAt s'.mem (wd env.work sPc) (gpow (2 ^ lb - 1)) ∧
      Wrote env [⟨sPc, 2⟩] s s' ∧ RegsFrame NativeVm.Field.epowRegs s s') E := by
  unfold pcCode
  refine wp_load (eval_work h14 _) hlb.2 ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))
  refine wp_load (eval_work (by rsimp; exact h14) _) hg.1 ?_
  refine wp_load (eval_work (by rsimp; exact h14) _) (ewat_hi hg) ?_
  refine WP.blk_cons (WP.mono (NativeVm.Field.epow_spec _) ?_ fun _ h ↦ h)
  rintro s1 ⟨he, hm, hf⟩
  have h14' : s1.reg .r14 = env.work := by rw [hf .r14 (by decide)]; rsimp; exact h14
  have hs0 := hi.ok3_some' pcR_ok (a := sPc) (by decide)
  have hs1 := hi.ok3_some' pcR_ok (a := sPc + 1) (by decide)
  have hval : (⟨s1.reg .r9, s1.reg .r10⟩ : EW) = gpow (2 ^ lb - 1) := by
    refine ew_of_eOf ?_
    rw [he]
    rsimp
    have e13 : ((1 : UInt64) <<< ((lb.toUInt64) &&& 63) - 1).toNat = 2 ^ lb - 1 := by
      rw [show ((lb.toUInt64) &&& 63) = lb.toUInt64 by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_and, toNat_toUInt64 (by omega)]
        rw [show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_eq_of_lt (by omega)]
      rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, toUInt64_shl _ _ (by omega),
        Nat.mul_one]
      have hp : 1 ≤ 2 ^ lb := Nat.one_le_two_pow
      have hp' : 2 ^ lb ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hlb'
      have e : (2 ^ lb).toUInt64 = (2 ^ lb - 1).toUInt64 + (1 : Nat).toUInt64 := by
        rw [toUInt64_add, Nat.sub_add_cancel hp]
      rw [e, UInt64.add_sub_cancel]
      exact toNat_toUInt64 (by omega)
    rw [e13, Equiv.toE_gpow, LeanVM.Protocol.Verifier.gpow, ← Equiv.toE_gen]
    rfl
  refine wp_store (eval_work h14' _) (by rw [hm]; rsimp; exact hs0) ?_
  refine wp_store (eval_work (by rsimp; exact h14') _) (by
    rw [QState.setMem_mem, hm]; rsimp
    have : wd env.work (sPc + 1) ≠ wd env.work sPc := fun e ↦ by
      rw [wd_inj (by decide) (by decide)] at e; omega
    simp only [this, ↓reduceIte]; exact hs1) (WP.blk_nil ⟨?_, ?_, ?_⟩)
  · have ne : wd env.work (sPc + 1) ≠ wd env.work sPc := fun e ↦ by
      rw [wd_inj (by decide) (by decide)] at e; omega
    refine ⟨?_, ?_⟩
    · simp only [QState.setMem_mem, Ne.symm ne, ↓reduceIte]
      rw [← hval]
    · rw [wd_wd]; simp only [QState.setMem_mem, ↓reduceIte, QState.setMem_reg]
      rw [← hval]
  · have hm' : s1.mem = s.mem := by rw [hm]; rfl
    have w1 := wrote_store (env := env) (ws := [⟨sPc, 2⟩]) (r := ⟨sPc, 2⟩) (by simp) le_rfl
      (by simp [Region.stop]) hm' ((hf .rdi (by decide)).trans (by rsimp)) hs0 (s1.reg .r9)
    refine w1.trans ?_
    have hs1' : ((s1.setMem (wd env.work sPc) (s1.reg .r9)).mem (wd env.work (sPc + 1))).isSome := by
      rw [QState.setMem_mem, hm']
      have : wd env.work (sPc + 1) ≠ wd env.work sPc := fun e ↦ by
        rw [wd_inj (by decide) (by decide)] at e; omega
      simp only [this, ↓reduceIte]; exact hs1
    exact wrote_store (r := ⟨sPc, 2⟩) (by simp) (by simp) (by simp [Region.stop]) rfl rfl hs1' _
  · intro r hr
    simp only [QState.setMem_reg]
    rw [hf r hr]
    simp only [NativeVm.Field.epowRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨-, -, hc, -, -, -, -, h9, h10, -, -, h13⟩ := hr
    rsimp
    simp [hc, h9, h10, h13]

/-! ## The column claims -/

/-- Claim `i`'s first word. -/
def claimW (i : Nat) : Nat := 15570 + 76 * i

/-- Claim `i`'s words. -/
def claimR (i : Nat) : Region := ⟨claimW i, 76⟩

theorem claimR_ok {i : Nat} (hi : i < 4) : Ok3 (claimR i) :=
  .inr (.inl ⟨by rw [claimsR_off]; simp [claimR, claimW]; omega, by
    rw [Region.stop, Region.stop, claimsR_off, claimsR_size]; simp [claimR, claimW]; omega⟩)

/-- Claim `i`: its column, the first `lenW li` coordinates of the GKR point, the element at `vw`. -/
def claimOne (i col li vw : Nat) : Stmt := blk [
  I (.storei (at_ .r14 (wdisp (claimW i))) (Int64.ofNat col)),
  I (.load .r15 (at_ .r14 (wdisp (lenW li)))), I (.store (at_ .r14 (wdisp (claimW i + 1))) .r15),
  I (.mov .r13 .r14), I (.addi .r13 (wdisp 52704)), I (.mov .rbx .r14),
  I (.addi .r14 (wdisp (claimW i + 2))), copyE, I (.mov .r14 .rbx),
  opsCode [.copy vw (claimW i + 74)]]

theorem pc_pointR_off : pointR.off = 52704 := by decide

/-- The length, the point's prefix and the value of claim `i`, its column stored. -/
def claimRest (i li vw : Nat) : List Stmt := [
  I (.load .r15 (at_ .r14 (wdisp (lenW li)))), I (.store (at_ .r14 (wdisp (claimW i + 1))) .r15),
  I (.mov .r13 .r14), I (.addi .r13 (wdisp 52704)), I (.mov .rbx .r14),
  I (.addi .r14 (wdisp (claimW i + 2))), copyE, I (.mov .r14 .rbx),
  opsCode [.copy vw (claimW i + 74)]]

theorem claimOne_eq (i col li vw : Nat) : claimOne i col li vw =
    blk (I (.storei (at_ .r14 (wdisp (claimW i))) (Int64.ofNat col)) :: claimRest i li vw) := rfl

theorem claimRest_spec {i li vw n : Nat} {pt : Array EW} {v : EW} (hi4 : i < 4)
    (hrdi : s.reg .rdi = env.ctx) (h14 : s.reg .r14 = env.work) (hi : Inputs env inp s.mem)
    (hpt : EWArr s.mem (wd env.work 52704) pt) (hps : pt.size ≤ 63)
    (hn : NatAt s.mem (wd env.work (lenW li)) n) (hnp : n ≤ pt.size) (hn30 : n ≤ 30)
    (hv : EWAt s.mem (wd env.work vw) v) (hvw : vw % 2 = 0 ∧ vw + 1 < 2 ^ 60)
    (hvc : vw + 2 ≤ claimW i ∨ claimW i + 76 ≤ vw) :
    WP (blk (claimRest i li vw)) s (fun s' ↦
      NatAt s'.mem (wd env.work (claimW i + 1)) n ∧
      EWArr s'.mem (wd env.work (claimW i + 2)) (pt.extract 0 n) ∧
      EWAt s'.mem (wd env.work (claimW i + 74)) v ∧
      s'.mem (wd env.work (claimW i)) = s.mem (wd env.work (claimW i)) ∧
      Wrote env [claimR i] s s' ∧ RegsFrame (opRegs ++ [.r13, .r14, .r15]) s s') E := by
  have hok := claimR_ok hi4
  have hcw : claimW i + 76 ≤ 15569 + 12161 := by unfold claimW; omega
  have hsm : ∀ k, claimW i ≤ k → k < claimW i + 76 → (s.mem (wd env.work k)).isSome :=
    fun k h1 h2 ↦ hi.ok3_some' hok (a := k) (by simp [claimR, Region.stop]; omega)
  have hbd : ∀ r ∈ [claimR i], r.stop ≤ 2 ^ 61 := by simp [claimR, claimW, Region.stop]; omega
  unfold claimRest
  refine wp_load (eval_work h14 _) hn.2 ?_
  refine wp_store (eval_work (by rsimp; exact h14) _) (hsm _ (by omega) (by omega)) ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  -- the state before the copy
  generalize hs2 : (((((s.setReg .r15 n.toUInt64).setMem (wd env.work (claimW i + 1))
    ((s.setReg .r15 n.toUInt64).reg .r15)).setReg .r13 _).setReg .r13 _).setReg .rbx _).setReg .r14 _ = s2
  have hm2 : s2.mem = (s.setMem (wd env.work (claimW i + 1)) n.toUInt64).mem := by
    rw [← hs2]; rfl
  have w2 : Wrote env [claimR i] s s2 := by
    have := wrote_store (env := env) (s := s) (s1 := s) (ws := [claimR i]) (r := claimR i) (by simp)
      (k := claimW i + 1) (by simp [claimR]) (by simp [claimR, Region.stop]) rfl rfl
      (hsm _ (by omega) (by omega)) n.toUInt64
    exact ⟨by rw [← hs2]; rsimp, fun a ha ↦ by rw [hm2]; exact this.mem a ha,
      fun a ↦ by rw [hm2]; exact this.dom a⟩
  have r13 : s2.reg .r13 = wd env.work 52704 := by rw [← hs2]; rsimp; rw [h14]; rfl
  have r14 : s2.reg .r14 = wd env.work (claimW i + 2) := by rw [← hs2]; rsimp; rw [h14]; rfl
  have rbx : s2.reg .rbx = env.work := by rw [← hs2]; rsimp; exact h14
  have r15 : s2.reg .r15 = n.toUInt64 := by rw [← hs2]; rsimp
  have hpt2 : EWArr s2.mem (wd env.work 52704) pt := by
    refine hpt.congr (n := 2 * pt.size) (fun k hk ↦ ?_) le_rfl
    rw [wd_wd, w2.word (by simp [claimR, Region.stop]; omega) (by omega) hbd]
  refine WP.blk_cons (WP.mono (copyE_spec (w := env.work) hnp r13 r14 r15 hpt2 (by right; unfold claimW; omega)
    ⟨by omega, by unfold claimW; omega⟩ (fun k hk ↦ by
      rw [w2.dom]; exact hsm _ (by omega) (by omega))) ?_ fun _ h ↦ h)
  rintro s3 ⟨harr, hout, hsome, hf3⟩
  have w3 : Wrote env [claimR i] s2 s3 := ⟨by rw [hf3 .rdi (by decide)], fun a ha ↦ hout a
    fun k hk e ↦ ha (claimR i) (by simp) ⟨k + 2, by simp only [claimR]; omega,
      by rw [e]; simp only [claimR]; congr 1; omega⟩, hsome⟩
  refine wp_reg rfl ?_
  have h14' : (s3.setReg .r14 (s3.reg .rbx)).reg .r14 = env.work := by
    rsimp; rw [hf3 .rbx (by decide), rbx]
  have hw4 : Wrote env [claimR i] s (s3.setReg .r14 (s3.reg .rbx)) :=
    (w2.trans w3).setReg (by decide) _
  have hi4' : Inputs env inp (s3.setReg .r14 (s3.reg .rbx)).mem :=
    hi.step3 (fun r hr ↦ (List.mem_singleton.mp hr) ▸ hok) hw4.step hrdi
  have hv4 : EWAt (s3.setReg .r14 (s3.reg .rbx)).mem (wd env.work vw) v := by
    have hc : ∀ r ∈ [claimR i], vw + 2 ≤ r.off ∨ r.stop ≤ vw := by
      simp only [List.mem_singleton, forall_eq, claimR, Region.stop]; omega
    refine ⟨?_, ?_⟩
    · rw [hw4.word (fun r hr ↦ by have := hc r hr; omega) (by omega) hbd]; exact hv.1
    · rw [wd_wd, hw4.word (fun r hr ↦ by have := hc r hr; omega) (by omega) hbd]
      exact ewat_hi hv
  have hokv : Ok3 ⟨claimW i + 74, 2⟩ := .inr (.inl ⟨by rw [claimsR_off]; unfold claimW; simp; omega, by
    rw [Region.stop, Region.stop, claimsR_off, claimsR_size]; unfold claimW; simp; omega⟩)
  refine WP.blk_cons (WP.mono (ops_wrote (r := ⟨claimW i + 74, 2⟩) [.copy vw (claimW i + 74)] (S := [vw])
    (v := vOf [(vw, v)]) hokv hi4' h14'
    (holds_vOf [(vw, v)] (by simp) (by simpa using hv4)) (by simpa using ⟨hvw.1, by omega⟩)
    (by simp [opsValid, EOp.srcs])
    (by simp [opsDsts, EOp.dst, Region.stop]; unfold claimW; omega)) ?_ fun _ h ↦ h)
  rintro s5 ⟨hH, w5, hf5⟩
  have hbd5 : ∀ r ∈ [(⟨claimW i + 74, 2⟩ : Region)], r.stop ≤ 2 ^ 61 := by
    simp [Region.stop, claimW]; omega
  have hbig : Wrote env [claimR i] s s5 := hw4.trans (w5.widen fun r hr ↦ ⟨claimR i, by simp, by
    rw [List.mem_singleton.mp hr]; exact ⟨by simp [claimR], by simp [claimR, Region.stop]⟩⟩)
  have k5 : ∀ k, k < claimW i + 74 → s5.mem (wd env.work k) = s3.mem (wd env.work k) := fun k hk ↦
    w5.word (fun r hr ↦ by rw [List.mem_singleton.mp hr]; left; exact hk) (by unfold claimW at hk; omega) hbd5
  have k3 : ∀ k, k < claimW i + 2 → s3.mem (wd env.work k) = s2.mem (wd env.work k) := fun k hk ↦
    hout _ fun j hj e ↦ by rw [wd_inj (by unfold claimW at hk; omega) (by unfold claimW; omega)] at e; omega
  refine WP.blk_nil ⟨?_, ?_, ?_, ?_, hbig, ?_⟩
  · refine ⟨hn.1, ?_⟩
    rw [k5 _ (by omega), k3 _ (by omega), hm2]
    simp only [QState.setMem_mem, ↓reduceIte]
  · refine harr.congr (n := 2 * n) (fun k hk ↦ ?_) (by simp)
    rw [wd_wd, k5 _ (by omega)]
  · have := hH (claimW i + 74) (by simp [opsDsts, EOp.dst])
    simpa [opsRun, EOp.dst, EOp.eval, vOf_cons] using this
  · rw [k5 _ (by unfold claimW; omega), k3 _ (by unfold claimW; omega), hm2]
    exact setMem_wd_ne _ _ (by omega) (by unfold claimW; omega) (by unfold claimW; omega)
  · intro r hr
    have hro : r ∉ opRegs := fun m ↦ hr (List.mem_append_left _ m)
    have h13 : r ≠ .r13 := fun e ↦ hr (by simp [e])
    have h14 : r ≠ .r14 := fun e ↦ hr (by simp [e])
    have h15 : r ≠ .r15 := fun e ↦ hr (by simp [e])
    have hbx : r ≠ .rbx := fun e ↦ hro (by simp [e])
    have hax : r ≠ .rax := fun e ↦ hro (by simp [e])
    have hc : r ∉ copyRegs := by simp [copyRegs, h13, h14, h15, hax]
    rw [hf5 r hro, QState.setReg_reg, ite_eq_right_of_eq_false _ _ (eq_false h14), hf3 r hc, ← hs2]
    simp [QState.setReg_reg, h13, h14, h15, hbx]

end NativeVm.Code.P3
