module

public import NativeVm.Code.Phase6.LayerH

/-!
# The layers

`layerC` refines `verifyKeccakLayer` (`layer_refines`, through its three parts, `layer_eq`), and
`layersC`, a loop over the step kept in the scratch (`eStep`, its word in `r9` at the loop's test),
refines `keccakLayers` (`layers_refines`): the scratch holding the first claim, it ends holding the
last, which has `16` instance weights.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm NativeVm.Model NativeVm.Code LeanVM.Parameters
open NativeVm.Transcript (wd wdisp Env)
open NativeVm.Field (eOf)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- The layer in three parts. -/
def layerM (pb step : Nat) (c : KeccakClaimW) : VM KeccakClaimW :=
  l1M c pb step >>= fun product ↦ l2M c product >>= fun r ↦ l3M c r.1 r.2.1.1 r.2.2.1 r.2.2.2

theorem layer_eq (logSteps step : Nat) (c : KeccakClaimW) :
    Model.verifyKeccakLayer logSteps step c = layerM (logSteps - 4) step c := by
  have h3 : Model.grindingBits (LeanVM.Protocol.Verifier.productBits - 1) = 3 := by decide
  have h0 : Model.grind (Model.grindingBits 2) = pure () := grind_small (by decide)
  simp only [Model.verifyKeccakLayer, layerM, l1M, l2M, l3M, h3, h0, bind_assoc, pure_bind]
  rfl

/-- A layer. -/
def layerC : Stmt := blk [blk L1C, blk L2C, blk L3C]

/-- `pure_el`, the value's low word left in `r9`. -/
theorem el_r9 (hin : Inputs env inp s0.mem) {c : Stmt} {o : Nat} {x : EW} {L : List Reg64}
    (ho : o < scrN) (hL : Reg64.rdi ∉ L ∧ Reg64.rbp ∉ L)
    (hc : ∀ s, s.reg .rbp = sb env → Scr s.mem (sb env) g →
      WP c s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = x.toE ∧ s'.mem = s.mem ∧
        RegsFrame L s s') fun _ ↦ False) (h : St env s0 g t s) :
    WP (blk (c :: stEl o)) s (fun s' ↦ St env s0 (Function.update g o x) t s' ∧
      s'.reg .r9 = x.c0) fun _ ↦ False := by
  refine WP.blk_cons (WP.mono (hc s h.2.2.1 h.2.2.2) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  obtain ⟨v9, v10⟩ := regs_of_eOf e1
  have hp1 : s1.reg .rbp = sb env := (e3 .rbp hL.2).trans h.2.2.1
  rw [← List.append_nil (stEl o)]
  refine stEl_spec ho hp1 (h.2.2.2.congr fun a _ ↦ by rw [e2]) v9 v10 fun s' h1 h2 h3 ↦
    WP.blk_nil ⟨St.mk' hin h h1 (fun a ha ↦ by rw [h2 a ha, e2]) ?_ ?_, by rw [h3, v9]⟩
  · rw [h3, e3 .rdi hL.1]
  · rw [h3, hp1, h.2.2.1]

/-- The step counted: `eStep := eStep + 1`, its word left in `r9`. -/
def incC : List Stmt :=
  blk [I (.load .r9 (at_ .rbp (wdisp (2 * eStep)))), I (.addi .r9 1), I (.movi .r10 0)] :: stEl eStep

theorem inc_spec (hin : Inputs env inp s0.mem) {k : Nat}
    (hst : g eStep = EW.ofK k.toUInt64) (h : St env s0 g t s) :
    WP (blk incC) s (fun s' ↦ St env s0 (Function.update g eStep (EW.ofK (k + 1).toUInt64)) t s' ∧
      s'.reg .r9 = (k + 1).toUInt64) fun _ ↦ False :=
  el_r9 hin (L := [.r9, .r10]) (by p6_omega) (by decide) (fun s hp hs ↦ by
    refine ld0 hp hs (by p6_omega) ?_
    rw [hst]
    fstep; fstep; fdone
    refine ⟨?_, trivial, by rf_tac⟩
    rw [← NativeVm.Transcript.toUInt64_succ]
    rfl) h

/-- The layers, the step from `0`. -/
def layersC : Stmt := blk [blk (setW eStep 0),
  .loop (.cmp .ltu .r9 (.imm 12)) (blk [layerC, blk incC])]

/-- The loop's state after `k` layers, from the scratch `g0` holding the claim `c0`. -/
structure LInv (g0 : Nat → EW) (c0 : KeccakClaimW) (pb k : Nat) (c : KeccakClaimW) (g : Nat → EW) :
    Prop where
  claim : ClaimIn g c
  cn : Cn g
  stepW : g eStep = EW.ofK k.toUInt64
  ptSize : c.point.size = c0.point.size
  muSize : k = 0 ∨ c.mu.size = 16
  fr : ∀ i, ¬ LW i → i ≠ eStep → g i = g0 i

variable (env inp s0)

/-- **A layer** against `verifyKeccakLayer`. -/
theorem layer_refines (hin : Inputs env inp s0.mem) {c : KeccakClaimW} {logSteps step : Nat}
    (g0 : Nat → EW) (hpre : LPre g0 c (logSteps - 4) step) :
    Refines (St env s0 g0) layerC (Model.verifyKeccakLayer logSteps step c)
      (fun c' t s ↦ ∃ g', St env s0 g' t s ∧ LFr g' g0 ∧ ClaimIn g' c' ∧
        c'.point.size = c.point.size ∧ c'.mu.size = 16) (Kept env rs6 s0) := by
  rw [layer_eq]
  unfold layerC layerM
  refine Refines.blk_cons (l1_refines env inp s0 hin g0 hpre) fun product ↦
    Refines.exSt fun g1 ⟨h1fr, h1cl, h1ps, h1p⟩ ↦ ?_
  refine Refines.blk_cons (l2_refines env inp s0 hin g0 g1 hpre.cn h1fr h1cl h1ps h1p) fun r ↦
    Refines.exSt fun g2 ⟨h2fr, h2p⟩ ↦ ?_
  exact l3_refines env inp s0 hin g0 g2 hpre.cn h2fr h1cl.ptSize h1cl.wSize h2p

/-- **The layers** against `keccakLayers`. -/
theorem layers_refines (hin : Inputs env inp s0.mem) {c0 : KeccakClaimW} {logSteps : Nat}
    (g0 : Nat → EW) (hcl : ClaimIn g0 c0) (hcn : Cn g0)
    (hpb : g0 ePB = EW.ofK (logSteps - 4).toUInt64) (hpbLe : logSteps - 4 ≤ 26)
    (hseg : g0 eSegN = EW.ofK (c0.point.size - (logSteps - 4)).toUInt64) :
    Refines (St env s0 g0) layersC (keccakLayers logSteps c0)
      (fun c t s ↦ ∃ g, St env s0 g t s ∧ LInv g0 c0 (logSteps - 4) 12 c g) (Kept env rs6 s0) := by
  unfold layersC keccakLayers
  rw [show LeanVM.Protocol.Verifier.keccakDepth = 12 from rfl]
  intro t s h
  refine WP.blk_cons (WP.mono (el_r9 hin (L := [.r9, .r10]) (by p6_omega) (by decide)
    (x := EW.ofK (0 : Nat).toUInt64) (fun s _ _ ↦ by
      fstep; fstep; fdone
      exact ⟨rfl, trivial, by rf_tac⟩) h) (fun s1 ⟨h1, h9⟩ ↦ ?_) (fun _ h ↦ h.elim))
  set g1 := Function.update g0 eStep (EW.ofK (0 : Nat).toUInt64) with hg1
  have k1 : ∀ i, i ≠ eStep → g1 i = g0 i := fun i hi ↦ Function.update_of_ne hi _ _
  refine WP.blk_cons (WP.mono (Refines.foldlM (l := List.range 12) (init := c0)
    (cond := .cmp .ltu .r9 (.imm 12)) (body := blk [layerC, blk incC])
    (Inv := fun k c t s ↦ k ≤ 12 ∧ s.reg .r9 = k.toUInt64 ∧ ∃ g, St env s0 g t s ∧
      LInv g0 c0 (logSteps - 4) k c g)
    (fun k c t s ⟨hk, h9, _⟩ ↦ by
      rw [List.length_range]
      simp only [Cond.eval, h9, Rhs.eval, decide_eq_true_eq]
      rw [show (12 : Int64).toUInt64 = (12 : Nat).toUInt64 from rfl]
      exact toUInt64_lt' (by omega) (by omega)) ?_ t s1
    ⟨Nat.zero_le _, h9, g1, h1, ⟨hcl.congr fun i hi ↦ k1 i (by unfold CW at hi; p6_omega),
      hcn.congr fun i h1 h2 ↦ k1 i (by p6_omega), Function.update_self .., rfl, Or.inl rfl,
      fun i _ hi ↦ k1 i hi⟩⟩) (fun s' ⟨c, t', hr, _, _, g, hg, hl⟩ ↦
      WP.blk_nil ⟨c, t', hr, g, hg, by simpa using hl⟩) (fun _ h ↦ h))
  intro k hk c t s ⟨_, _, g, hst, hl⟩
  rw [List.length_range] at hk
  rw [List.getElem_range]
  have hpre : LPre g c (logSteps - 4) k :=
    ⟨hl.claim, hl.cn, (hl.fr _ (by unfold LW; p6_omega) (by p6_ne)).trans hpb, hpbLe,
      by rw [hl.fr _ (by unfold LW; p6_omega) (by p6_ne), hseg, hl.ptSize], hl.stepW, hk⟩
  refine Refines.then_blk (layer_refines env inp s0 hin g hpre) (fun c' t' s' ⟨g', h1, h2, h3, h4, h5⟩ ↦
    WP.mono (inc_spec hin (k := k)
      ((h2 _ (by unfold LW; p6_omega)).trans hl.stepW) h1) (fun s'' ⟨q1, q2⟩ ↦
        ⟨by omega, q2, _, q1, ⟨h3.congr fun i hi ↦ Function.update_of_ne (by unfold CW at hi; p6_omega) _ _,
          (h2.cn hl.cn).congr fun i h1 h2 ↦ Function.update_of_ne (by p6_omega) _ _,
          Function.update_self .., by rw [h4, hl.ptSize], Or.inr h5, fun i hi hi' ↦ by
            rw [Function.update_of_ne hi', h2 i hi, hl.fr i hi hi']⟩⟩) (fun _ h ↦ h)) t s hst

end NativeVm.Code.P6
