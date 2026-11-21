module

public import NativeVm.Code.Phase7.Push

/-!
# A level's fold rounds, against `foldRounds`

`roundC`: four scalars into the temporaries, a grind, `α` and `β`, the claim's update (`claimC`) and
the bookkeeping (`pushC`); `foldRoundsC` runs it `n` times (`n` at `cFold`), the rounds' count first
cleared. The words written are `roundW`: the temporaries, WHIR's claim and `α`s, the rounds.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wdisp wd_inj wd_zero eval_cw wp_load wp_store wp_reg ctxWork wp_then
  toUInt64_succ)

/-- One fold round. -/
def roundC : Stmt := blk [readTo tmpO, readTo (tmpO + 2), readTo (tmpO + 4), readTo (tmpO + 6),
  I (.movi .rsi 7), Transcript.grind, sampleTo (tmpO + 8), sampleTo (tmpO + 10), claimC, pushC]

/-- `n` fold rounds, `n` at `cFold`. -/
def foldRoundsC : Stmt := blk [ldW, ldw .r15 cFold, stwi roundsR.off 0,
  .loop (.cmp .ne .r15 (.imm 0)) (blk [roundC, I (.subi .r15 1)])]

/-- The words the fold rounds write. -/
def roundW (k : Nat) : Prop :=
  (tmpO ≤ k ∧ k < tmpO + 14) ∨ (whirR.off ≤ k ∧ k < whirR.off + whirGluedOff) ∨
    (roundsR.off ≤ k ∧ k < roundsR.off + roundsWords)

/-- Unfold the words' predicates, then `oomega`. -/
macro "romega" : tactic => `(tactic| ((try simp only [roundW, pushWritten, claimWritten] at *); oomega))

variable {p : Par}

/-- The state a round starts from. -/
abbrev RX (p : Par) (m0 : UInt64 → Option UInt64) (sW : WhirStateW) (rs : Array FoldRoundW)
    (m : UInt64 → Option UInt64) : Prop :=
  WhirAt m (whirR.at p.env.work) sW ∧ RoundsAt m (roundsR.at p.env.work) rs ∧ Only p.env roundW m0 m

theorem dep_RX (m0 : UInt64 → Option UInt64) (sW : WhirStateW) (rs : Array FoldRoundW) :
    Dep p.env (RX p m0 sW rs) (fun k ↦ (whirR.off ≤ k ∧ k < whirR.off + whirWords) ∨
      (roundsR.off ≤ k ∧ k < roundsR.off + roundsWords) ∨
      (mineLo ≤ k ∧ k < dataEnd ∧ ¬ roundW k)) :=
  (dep_whir sW).and ((dep_rounds rs).and (dep_only roundW m0))

theorem foldGrind : Whir.foldGrindingBits = 7 := rfl

/-- **One round** against `foldRound`. -/
theorem roundC_b {m0 : UInt64 → Option UInt64} {sW : WhirStateW} {rs : Array FoldRoundW} {c : UInt64}
    (hα : sW.alphas.size < stackCap) (hrs : rs.size < roundCap) :
    Refines (fun t s ↦ Base p t s ∧ RX p m0 sW rs s.mem ∧ s.reg .r15 = c) roundC (foldRound sW)
      (fun r t s ↦ Base p t s ∧ RX p m0 r.1 (rs.push r.2) s.mem ∧ s.reg .r15 = c ∧
        r.1.glued = sW.glued ∧ r.1.alphas = sW.alphas.push r.2.alpha) (Err p) := by
  have hRg : RegOk fun f ↦ f .r15 = c := RegOk.eq (by decide) c
  have hD0 := dep_RX (p := p) m0 sW rs
  unfold roundC foldRound
  refine readTo_then hD0 (by intro j hj; romega) (by romega) (by romega) hRg fun u0 ↦ ?_
  refine readTo_then (hD0.and (dep_ewat _ u0)) (by intro j hj; romega) (by romega) (by romega) hRg
    fun w ↦ ?_
  refine readTo_then ((hD0.and (dep_ewat _ u0)).and (dep_ewat _ w)) (by intro j hj; romega)
    (by romega) (by romega) hRg fun c0 ↦ ?_
  refine readTo_then (((hD0.and (dep_ewat _ u0)).and (dep_ewat _ w)).and (dep_ewat _ c0))
    (by intro j hj; romega) (by romega) (by romega) hRg fun c1 ↦ ?_
  refine grind_then (by decide) (by decide) (by rfl)
    ((((hD0.and (dep_ewat _ u0)).and (dep_ewat _ w)).and (dep_ewat _ c0)).and (dep_ewat _ c1))
    (by intro j hj; romega) hRg ?_
  refine sampleTo_then
    ((((hD0.and (dep_ewat _ u0)).and (dep_ewat _ w)).and (dep_ewat _ c0)).and (dep_ewat _ c1))
    (by intro j hj; romega) (by romega) (by romega) hRg fun alpha ↦ ?_
  refine sampleTo_then
    (((((hD0.and (dep_ewat _ u0)).and (dep_ewat _ w)).and (dep_ewat _ c0)).and (dep_ewat _ c1)).and
      (dep_ewat _ alpha))
    (by intro j hj; romega) (by romega) (by romega) hRg fun beta ↦ ?_
  refine Refines.pure fun t s ⟨hb, ⟨⟨⟨⟨⟨⟨⟨hw, hr, ho⟩, hu0⟩, hw'⟩, hc0⟩, hc1⟩, ha⟩, hbe⟩, h15⟩ ↦ ?_
  have hc : EWAt s.mem (wd p.env.work whirR.off) sW.claim := hw.1
  refine wp_then (claimC_spec hb.rdi hb.workPtr (fun k hk ↦ hb.some (by romega) (by romega))
    ⟨hu0, hw', hc0, hc1, ha, hbe⟩ hc) fun s1 ⟨h1, _, hreg1, hmem1, hdom1⟩ ↦ ?_
  have hU1 : ∀ k, ¬ claimWritten k → k < 2 ^ 61 → s1.mem (wd p.env.work k) = s.mem (wd p.env.work k) :=
    fun k hk hk' ↦ hmem1 _ fun j hj e ↦ hk (by
      have : j < 2 ^ 61 := by romega
      rw [(wd_inj hk' this).mp e]; exact hj)
  have sm1 : ∀ o len, (∀ j < len, ¬ claimWritten (o + j) ∧ o + j < 2 ^ 61) →
      Same s.mem s1.mem (wd p.env.work o) len := fun o len h j hj ↦ by
    rw [wd_wd]; exact hU1 _ (h j hj).1 (h j hj).2
  have fr1 : FrM p.env s s1 := frM_of (hreg1 .rdi (by decide)) hdom1 hmem1 (fun k hk ↦ by romega)
  have hb1 := hb.frM fr1
  have hw1 : WhirAt s1.mem (whirR.at p.env.work)
      { sW with claim := roundClaim sW.claim u0 w c0 c1 alpha beta } := by
    refine hw.update (by rw [Region.at, wd_wd]; exact sm1 _ _ fun j hj ↦ ⟨by romega, by romega⟩) h1 ?_
    exact hw.2.1.congr (by rw [Region.at, wd_wd]; exact sm1 _ _ fun j hj ↦ ⟨by romega, by romega⟩)
  have hr1 : RoundsAt s1.mem (roundsR.at p.env.work) rs :=
    hr.congr (by rw [Region.at]; exact sm1 _ _ fun j hj ↦ ⟨by romega, by romega⟩)
  have ha1 : EWAt s1.mem (wd p.env.work (tmpO + 8)) alpha :=
    ha.congr (sm1 _ _ fun j hj ↦ ⟨by romega, by romega⟩)
  have hbe1 : EWAt s1.mem (wd p.env.work (tmpO + 10)) beta :=
    hbe.congr (sm1 _ _ fun j hj ↦ ⟨by romega, by romega⟩)
  refine wp_then (pushC_spec hb1.rdi hb1.workPtr (fun k hk ↦ hb1.some (by romega) (by romega))
    hw1 hr1 ha1 hbe1 hα hrs) fun s2 ⟨h2w, h2r, hmem2, hdom2, hreg2⟩ ↦ ?_
  have fr2 : FrM p.env s1 s2 := frM_of (hreg2 .rdi (by decide)) hdom2 hmem2 (fun k hk ↦ by romega)
  refine WP.blk_nil ⟨hb1.frM fr2, ⟨h2w, h2r, ?_⟩, ?_, rfl, rfl⟩
  · exact (ho.frame hmem1 (fun k hk ↦ by romega) (fun k hk ↦ by romega)).frame hmem2
      (fun k hk ↦ by romega) (fun k hk ↦ by romega)
  · rw [hreg2 .r15 (by decide), hreg1 .r15 (by decide)]; exact h15

/-- The rounds loop's invariant after `k` rounds. -/
def RInv (p : Par) (m0 : UInt64 → Option UInt64) (sW : WhirStateW) (n k : Nat)
    (acc : WhirStateW × Array FoldRoundW) (t : TState) (s : QState) : Prop :=
  Base p t s ∧ RX p m0 acc.1 acc.2 s.mem ∧ s.reg .r15 = (n - k).toUInt64 ∧
    acc.1.glued = sW.glued ∧ acc.1.alphas.size = sW.alphas.size + k ∧ acc.2.size = k

theorem toUInt64_ne_zero {a : Nat} (h : a < 2 ^ 64) : a.toUInt64 ≠ 0 ↔ a ≠ 0 := by
  constructor
  · intro h0 e; exact h0 (by rw [e]; rfl)
  · intro h0 e
    have := congrArg UInt64.toNat e
    rw [NativeVm.Transcript.toNat_toUInt64 h] at this
    exact h0 this

/-- **`n` fold rounds** against `foldRounds n`. -/
theorem foldRoundsC_b {m0 : UInt64 → Option UInt64} {sW : WhirStateW} {n : Nat} (hn : n ≤ roundCap)
    (hα : sW.alphas.size + n ≤ stackCap) :
    Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ NatAt s.mem (wd p.env.work cFold) n ∧
        WhirAt s.mem (whirR.at p.env.work) sW)
      foldRoundsC (foldRounds n sW)
      (fun r t s ↦ Base p t s ∧ RX p m0 r.1 r.2 s.mem ∧ r.1.glued = sW.glued ∧
        r.1.alphas.size = sW.alphas.size + n ∧ r.2.size = n) (Err p) := by
  have hn6 : n ≤ 6 := hn
  unfold foldRoundsC ldW
  refine Refines.pre_blk (P' := fun t s ↦ Base p t s ∧ s.mem = m0 ∧ NatAt s.mem (wd p.env.work cFold) n ∧
      WhirAt s.mem (whirR.at p.env.work) sW ∧ s.reg .rbp = p.env.work)
    (fun t s ⟨hb, hm, hn', hw⟩ ↦ wp_load (eval_cw hb.rdi _) hb.workPtr
      (WP.blk_nil ⟨hb.frM (frM_setReg (by decide) _), hm, hn', hw, by simp⟩)) ?_
  refine Refines.pre_blk (P' := fun t s ↦ Base p t s ∧ s.mem = m0 ∧
      WhirAt s.mem (whirR.at p.env.work) sW ∧ s.reg .rbp = p.env.work ∧ s.reg .r15 = n.toUInt64)
    (fun t s ⟨hb, hm, hn', hw, hbp⟩ ↦ ldw_wp (env := p.env) hbp hn'.2
      (WP.blk_nil ⟨hb.frM (frM_setReg (by decide) _), hm, hw, by simp [hbp], by simp⟩)) ?_
  refine Refines.pre_blk (P' := fun t s ↦ RInv p m0 sW n 0 (sW, #[]) t s)
    (fun t s ⟨hb, hm, hw, hbp, h15⟩ ↦ ?_) ?_
  · have hk : (s.mem (wd p.env.work roundsR.off)).isSome := hb.some (by romega) (by romega)
    refine NativeVm.Transcript.wp_storei (eval_w hbp _) hk (WP.blk_nil ?_)
    have hb' := hb.frM (frM_store (by romega) (by romega) hk (0 : Int64).toUInt64)
    refine ⟨hb', ⟨?_, ⟨by simp, ⟨by simp, by simp [Region.at]; rfl⟩, fun i hi ↦ absurd hi (by simp)⟩, ?_⟩,
      by simp [h15], rfl, rfl, rfl⟩
    · exact hw.congr fun j hj ↦ by
        rw [Region.at, wd_wd, QState.setMem_mem, ite_no]
        intro e
        have := (wd_inj (by romega) (by romega)).mp e
        romega
    · intro k h1 h2 hk
      rw [QState.setMem_mem, ite_no, hm]
      intro e
      have := (wd_inj (by romega) (by romega)).mp e
      romega
  · unfold foldRounds
    refine (Refines.foldlM (l := List.range n) (Inv := RInv p m0 sW n)
      (cond := .cmp .ne .r15 (.imm 0)) (body := blk [roundC, I (.subi .r15 1)])
      (fun k acc t s ⟨_, _, h15, _⟩ ↦ ?_) (fun k hk acc ↦ ?_)).mono (fun _ _ h ↦ h)
      (fun acc t s h ↦ ?_) (fun _ h ↦ h)
    · rw [List.length_range, NativeVm.Transcript.cond_ne, h15, NativeVm.Transcript.rhs_imm]
      simp only [bne_iff_ne, ne_eq]
      rw [show ((0 : Int64).toUInt64) = (0 : UInt64) from rfl]
      rw [← ne_eq, toUInt64_ne_zero (by omega)]
      omega
    · rw [List.length_range] at hk
      intro t s hinv
      obtain ⟨-, -, -, -, hal, hsz⟩ := id hinv
      have hα' : acc.1.alphas.size < stackCap := by rw [hal]; omega
      have hrs' : acc.2.size < roundCap := by rw [hsz]; omega
      refine Refines.blk_cons (P := RInv p m0 sW n k acc) ((roundC_b (c := (n - k).toUInt64) hα' hrs').mono
        (fun t s ⟨hb, hx, h15, _⟩ ↦ ⟨hb, hx, h15⟩) (fun _ _ _ h ↦ h) (fun _ h ↦ h)) (fun x ↦ ?_) t s hinv
      obtain ⟨s', r⟩ := x
      refine Refines.pure fun t s ⟨hb, hx, h15, hg, ha⟩ ↦ ?_
      refine NativeVm.Transcript.wp_reg rfl (WP.blk_nil ⟨hb.frM (frM_setReg (by decide) _), hx, ?_, ?_, ?_, ?_⟩)
      · simp only [QState.setReg_reg, ite_true, h15]
        rw [show (n - k) = (n - (k + 1)) + 1 by omega, ← NativeVm.Transcript.toUInt64_succ,
          show (1 : Int64).toUInt64 = 1 from rfl, UInt64.add_sub_cancel]
      · rw [hg]; exact hinv.2.2.2.1
      · simp only at ha ⊢
        rw [ha, Array.size_push, hal]; omega
      · simp [hsz]
    · rw [List.length_range] at h
      exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end NativeVm.Code.P7
