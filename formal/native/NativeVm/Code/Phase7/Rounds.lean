module

public import NativeVm.Code.Phase7.Preds
public import NativeVm.Code.Phase7.EOps

/-!
# A level's fold rounds

`foldRoundsC` refines `foldRounds n s` (`n` at the scratch word `cFold`): each round (`roundC`)
reads `u0, w, c0, c1` into the temporaries, grinds, samples `α` and `β`, then (`claimC`, `pushC`)
updates WHIR's running claim to `u0 + α(u0 + claim) + α²w + βc0 + αβ(c0 + c1)` (computed as
`u0 + α(u0 + claim + αw + β(c0 + c1)) + βc0`), appends `α` to its `α`s and `(α, β)` to the level's
rounds (`roundsR`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model NativeVm.Field LeanVM.Parameters NativeVm.Equiv
open NativeVm.Transcript (wd Env wdisp Keeps clobbers wd_inj wd_zero eval_idx64)

/-! ## Numbers -/

/-- Unfold phase 7's offsets, then `omega`. -/
macro "oomega" : tactic => `(tactic| first
  | omega
  | (simp only [sc, cIdx, cN, cLogN, cMu, cDepth, cI, cJ, cK, levO, cFold, cRate, cQ, cNFold, cNRate,
      tmpO, hiO, tabO, layO, whatO, novO, foldO, indO, ptO, xO, ringO, mleO, spO, scratch_off,
      whir_off, basis_off, rounds_off, queries_off, rows_off, mineLo_val, dataEnd_val,
      gluedWords_val, gluedQOff_val, gluedWOff_val, whirGluedOff_val, whirWords_val,
      vecWords_stackCap, wvecWords_queryCap, vecWords_queryCap, roundsWords_val, stackCap_val,
      gluedCap_val, roundCap_val, queryCap_val, vecWords, wvecWords] at *; omega))

/-- Read words through stores to other words of the working area. -/
theorem setMem_wd {s : QState} {b : UInt64} {k k' : Nat} (v : UInt64) (hk : k < 2 ^ 61)
    (hk' : k' < 2 ^ 61) : (s.setMem (wd b k) v).mem (wd b k') = if k' = k then some v else
      s.mem (wd b k') := by
  rw [QState.setMem_mem]
  by_cases h : k' = k
  · subst h; simp
  · rw [ite_no (fun e ↦ h ((wd_inj hk' hk).mp e)), ite_no h]

/-- Read a word through stores: each store's index compared by `oomega`. -/
macro "msimp" : tactic => `(tactic|
  simp (disch := oomega) only [QState.setReg_mem, setMem_wd, QState.setReg_reg, QState.setMem_reg,
    reduceCtorEq, ↓reduceIte, ite_true, ite_false])

/-! ## The model -/

/-- A fold round's new claim (`foldRound`). -/
def roundClaim (claim u0 w c0 c1 alpha beta : EW) : EW :=
  u0 + alpha * (u0 + claim) + alpha * alpha * w + beta * c0 + alpha * beta * (c0 + c1)

/-! ## The claim -/

/-- The new running claim from the temporaries (`u0, w, c0, c1, α, β` at pairs `0, 2, 4, 6, 8,
10`), through the temporary pair `12`. -/
def claimC : Stmt := blk [ldW,
  ldw .r9 (tmpO + 4), ldw .r10 (tmpO + 4 + 1),
  ldw .r11 (tmpO + 6), ldw .r12 (tmpO + 6 + 1), eadd,
  ldw .r11 (tmpO + 10), ldw .r12 (tmpO + 10 + 1), emul,
  ldw .r11 whirR.off, ldw .r12 (whirR.off + 1), eadd,
  ldw .r11 tmpO, ldw .r12 (tmpO + 1), eadd,
  stw (tmpO + 12) .r9, stw (tmpO + 12 + 1) .r10,
  ldw .r9 (tmpO + 8), ldw .r10 (tmpO + 8 + 1),
  ldw .r11 (tmpO + 2), ldw .r12 (tmpO + 2 + 1), emul,
  ldw .r11 (tmpO + 12), ldw .r12 (tmpO + 12 + 1), eadd,
  ldw .r11 (tmpO + 8), ldw .r12 (tmpO + 8 + 1), emul,
  ldw .r11 tmpO, ldw .r12 (tmpO + 1), eadd,
  stw (tmpO + 12) .r9, stw (tmpO + 12 + 1) .r10,
  ldw .r9 (tmpO + 10), ldw .r10 (tmpO + 10 + 1),
  ldw .r11 (tmpO + 4), ldw .r12 (tmpO + 4 + 1), emul,
  ldw .r11 (tmpO + 12), ldw .r12 (tmpO + 12 + 1), eadd,
  stw whirR.off .r9, stw (whirR.off + 1) .r10]

/-- The temporaries of a round. -/
structure Tmps (mem : UInt64 → Option UInt64) (W : UInt64) (u0 w c0 c1 alpha beta : EW) : Prop where
  u0 : EWAt mem (wd W tmpO) u0
  w : EWAt mem (wd W (tmpO + 2)) w
  c0 : EWAt mem (wd W (tmpO + 4)) c0
  c1 : EWAt mem (wd W (tmpO + 6)) c1
  alpha : EWAt mem (wd W (tmpO + 8)) alpha
  beta : EWAt mem (wd W (tmpO + 10)) beta

theorem ewat_wd {mem : UInt64 → Option UInt64} {W : UInt64} {k : Nat} {x : EW}
    (h : EWAt mem (wd W k) x) : mem (wd W k) = some x.c0 ∧ mem (wd W (k + 1)) = some x.c1 := by
  rw [← wd_wd]; exact h

/-- The words `claimC` writes. -/
def claimWritten (k : Nat) : Prop :=
  k = tmpO + 12 ∨ k = tmpO + 12 + 1 ∨ k = whirR.off ∨ k = whirR.off + 1

theorem claimC_spec {env : Env} {s : QState} {F : QState → Prop} {claim u0 w c0 c1 alpha beta : EW}
    (hrdi : s.reg .rdi = env.ctx) (hwp : s.mem (wd env.ctx NativeVm.Transcript.ctxWork) = some env.work)
    (hsome : ∀ k, claimWritten k → (s.mem (wd env.work k)).isSome)
    (ht : Tmps s.mem env.work u0 w c0 c1 alpha beta) (hc : EWAt s.mem (wd env.work whirR.off) claim) :
    WP claimC s (fun s' ↦ EWAt s'.mem (wd env.work whirR.off) (roundClaim claim u0 w c0 c1 alpha beta) ∧
      s'.reg .rbp = env.work ∧ (∀ r, r ∉ [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .rbp] →
        s'.reg r = s.reg r) ∧
      (∀ a, (∀ k, claimWritten k → a ≠ wd env.work k) → s'.mem a = s.mem a) ∧
      (∀ a, (s'.mem a).isSome = (s.mem a).isSome)) F := by
  unfold claimC ldW
  refine NativeVm.Transcript.wp_load (NativeVm.Transcript.eval_cw hrdi _) hwp ?_
  set s0 := s.setReg .rbp env.work with hs0
  have hW0 : s0.reg .rbp = env.work := by rw [hs0]; rsimp
  have m0 : s0.mem = s.mem := rfl
  -- x1 = ((c0 + c1)·β + claim) + u0
  refine ldA_wp hW0 (m0 ▸ ht.c0) fun s1 m1 h9 h10 f1 ↦ ?_
  have hW1 : s1.reg .rbp = env.work := by rw [f1 .rbp (by decide)]; exact hW0
  refine addM_wp hW1 h9 h10 (by rw [m1, m0]; exact ht.c1) fun s2 m2 h9 h10 f2 ↦ ?_
  have hW2 : s2.reg .rbp = env.work := by rw [f2 .rbp (by decide)]; exact hW1
  refine mulM_wp hW2 h9 h10 (by rw [m2, m1, m0]; exact ht.beta) fun s3 m3 h9 h10 f3 ↦ ?_
  have hW3 : s3.reg .rbp = env.work := by rw [f3 .rbp (by decide)]; exact hW2
  refine addM_wp hW3 h9 h10 (by rw [m3, m2, m1, m0]; exact hc) fun s4 m4 h9 h10 f4 ↦ ?_
  have hW4 : s4.reg .rbp = env.work := by rw [f4 .rbp (by decide)]; exact hW3
  refine addM_wp hW4 h9 h10 (by rw [m4, m3, m2, m1, m0]; exact ht.u0) fun s5 m5 h9 h10 f5 ↦ ?_
  have hW5 : s5.reg .rbp = env.work := by rw [f5 .rbp (by decide)]; exact hW4
  have e5 : s5.mem = s.mem := by rw [m5, m4, m3, m2, m1, m0]
  refine stA_wp hW5 (by rw [e5]; exact hsome _ (.inl rfl)) (by rw [e5]; exact hsome _ (.inr (.inl rfl)))
    ?_
  set x1 := (c0 + c1) * beta + claim + u0 with hx1
  set s6 := (s5.setMem (wd env.work (tmpO + 12)) (s5.reg .r9)).setMem
    (wd env.work (tmpO + 12 + 1)) (s5.reg .r10) with hs6
  have hW6 : s6.reg .rbp = env.work := by rw [hs6]; rsimp; exact hW5
  have r6 : ∀ k, k ≠ tmpO + 12 → k ≠ tmpO + 12 + 1 → k < 2 ^ 61 →
      s6.mem (wd env.work k) = s.mem (wd env.work k) := fun k h1 h2 hk ↦ by
    rw [hs6, setMem_wd _ (by oomega) hk, ite_no h2, setMem_wd _ (by oomega) hk, ite_no h1, e5]
  have x6 : EWAt s6.mem (wd env.work (tmpO + 12)) x1 := by
    rw [EWAt, wd_wd, hs6, setMem_wd _ (by oomega) (by oomega), ite_no (by oomega),
      setMem_wd _ (by oomega) (by oomega), ite_yes rfl, setMem_wd _ (by oomega) (by oomega),
      ite_yes rfl, h9, h10]
    exact ⟨rfl, rfl⟩
  have tk : ∀ {j : Nat} {x : EW}, j + 1 < 12 → EWAt s.mem (wd env.work (tmpO + j)) x →
      EWAt s6.mem (wd env.work (tmpO + j)) x := fun hj hx ↦ by
    obtain ⟨a0, a1⟩ := ewat_wd hx
    refine ⟨by rw [r6 _ (by oomega) (by oomega) (by oomega)]; exact a0, ?_⟩
    rw [wd_wd, r6 _ (by oomega) (by oomega) (by oomega)]
    exact a1
  -- x2 = (α·w + x1)·α + u0
  refine ldA_wp hW6 (tk (j := 8) (by omega) ht.alpha) fun s7 m7 h9 h10 f7 ↦ ?_
  have hW7 : s7.reg .rbp = env.work := by rw [f7 .rbp (by decide)]; exact hW6
  refine mulM_wp hW7 h9 h10 (by rw [m7]; exact tk (j := 2) (by omega) ht.w) fun s8 m8 h9 h10 f8 ↦ ?_
  have hW8 : s8.reg .rbp = env.work := by rw [f8 .rbp (by decide)]; exact hW7
  refine addM_wp hW8 h9 h10 (by rw [m8, m7]; exact x6) fun s9 m9 h9 h10 f9 ↦ ?_
  have hW9 : s9.reg .rbp = env.work := by rw [f9 .rbp (by decide)]; exact hW8
  refine mulM_wp hW9 h9 h10 (by rw [m9, m8, m7]; exact tk (j := 8) (by omega) ht.alpha)
    fun s10 m10 h9 h10 f10 ↦ ?_
  have hW10 : s10.reg .rbp = env.work := by rw [f10 .rbp (by decide)]; exact hW9
  refine addM_wp hW10 h9 h10 (by rw [m10, m9, m8, m7]; exact tk (j := 0) (by omega) ht.u0)
    fun s11 m11 h9 h10 f11 ↦ ?_
  have hW11 : s11.reg .rbp = env.work := by rw [f11 .rbp (by decide)]; exact hW10
  have e11 : s11.mem = s6.mem := by rw [m11, m10, m9, m8, m7]
  have d6 : ∀ a, (s6.mem a).isSome = (s.mem a).isSome := fun a ↦ by
    rw [hs6, NativeVm.Transcript.isSome_setMem _ _ (by
        rw [NativeVm.Transcript.isSome_setMem _ _ (by rw [e5]; exact hsome _ (.inl rfl)), e5]
        exact hsome _ (.inr (.inl rfl))),
      NativeVm.Transcript.isSome_setMem _ _ (by rw [e5]; exact hsome _ (.inl rfl)), e5]
  refine stA_wp hW11 (by rw [e11, d6]; exact hsome _ (.inl rfl))
    (by rw [e11, d6]; exact hsome _ (.inr (.inl rfl))) ?_
  set x2 := (alpha * w + x1) * alpha + u0 with hx2
  set s12 := (s11.setMem (wd env.work (tmpO + 12)) (s11.reg .r9)).setMem
    (wd env.work (tmpO + 12 + 1)) (s11.reg .r10) with hs12
  have hW12 : s12.reg .rbp = env.work := by rw [hs12]; rsimp; exact hW11
  have r12 : ∀ k, k ≠ tmpO + 12 → k ≠ tmpO + 12 + 1 → k < 2 ^ 61 →
      s12.mem (wd env.work k) = s.mem (wd env.work k) := fun k h1 h2 hk ↦ by
    rw [hs12, setMem_wd _ (by oomega) hk, ite_no h2, setMem_wd _ (by oomega) hk, ite_no h1, e11,
      r6 k h1 h2 hk]
  have x12 : EWAt s12.mem (wd env.work (tmpO + 12)) x2 := by
    rw [EWAt, wd_wd, hs12, setMem_wd _ (by oomega) (by oomega), ite_no (by oomega),
      setMem_wd _ (by oomega) (by oomega), ite_yes rfl, setMem_wd _ (by oomega) (by oomega),
      ite_yes rfl, h9, h10]
    exact ⟨rfl, rfl⟩
  have tk' : ∀ {j : Nat} {x : EW}, j + 1 < 12 → EWAt s.mem (wd env.work (tmpO + j)) x →
      EWAt s12.mem (wd env.work (tmpO + j)) x := fun hj hx ↦ by
    obtain ⟨a0, a1⟩ := ewat_wd hx
    refine ⟨by rw [r12 _ (by oomega) (by oomega) (by oomega)]; exact a0, ?_⟩
    rw [wd_wd, r12 _ (by oomega) (by oomega) (by oomega)]
    exact a1
  -- β·c0 + x2
  refine ldA_wp hW12 (tk' (j := 10) (by omega) ht.beta) fun s13 m13 h9 h10 f13 ↦ ?_
  have hW13 : s13.reg .rbp = env.work := by rw [f13 .rbp (by decide)]; exact hW12
  refine mulM_wp hW13 h9 h10 (by rw [m13]; exact tk' (j := 4) (by omega) ht.c0)
    fun s14 m14 h9 h10 f14 ↦ ?_
  have hW14 : s14.reg .rbp = env.work := by rw [f14 .rbp (by decide)]; exact hW13
  refine addM_wp hW14 h9 h10 (by rw [m14, m13]; exact x12) fun s15 m15 h9 h10 f15 ↦ ?_
  have hW15 : s15.reg .rbp = env.work := by rw [f15 .rbp (by decide)]; exact hW14
  have e15 : s15.mem = s12.mem := by rw [m15, m14, m13]
  have d12 : ∀ a, (s12.mem a).isSome = (s.mem a).isSome := fun a ↦ by
    rw [hs12, NativeVm.Transcript.isSome_setMem _ _ (by
        rw [NativeVm.Transcript.isSome_setMem _ _ (by rw [e11, d6]; exact hsome _ (.inl rfl)),
          e11, d6]
        exact hsome _ (.inr (.inl rfl))),
      NativeVm.Transcript.isSome_setMem _ _ (by rw [e11, d6]; exact hsome _ (.inl rfl)), e11, d6]
  refine stA_wp hW15 (by rw [e15, d12]; exact hsome _ (.inr (.inr (.inl rfl))))
    (by rw [e15, d12]; exact hsome _ (.inr (.inr (.inr rfl)))) ?_
  refine WP.blk_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [EWAt, wd_wd, setMem_wd _ (by oomega) (by oomega), ite_no (by oomega),
      setMem_wd _ (by oomega) (by oomega), ite_yes rfl, setMem_wd _ (by oomega) (by oomega),
      ite_yes rfl, h9, h10]
    have : beta * c0 + x2 = roundClaim claim u0 w c0 c1 alpha beta := by
      apply EW.toE_injective
      simp only [hx2, hx1, roundClaim, EW.toE_add, EW.toE_mul]
      ring
    rw [this]
    exact ⟨rfl, rfl⟩
  · rsimp; exact hW15
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨ha, hb, hc', hd, h8, h9', h10', h11, h12, hbp⟩ := hr
    rsimp
    rw [f15 r (by simp [*]), f14 r (by simp [eRegs, *]), f13 r (by simp [*]), hs12]
    rsimp
    rw [f11 r (by simp [*]), f10 r (by simp [eRegs, *]), f9 r (by simp [*]),
      f8 r (by simp [eRegs, *]), f7 r (by simp [*]), hs6]
    rsimp
    rw [f5 r (by simp [*]), f4 r (by simp [*]), f3 r (by simp [eRegs, *]), f2 r (by simp [*]),
      f1 r (by simp [*]), hs0]
    rsimp
    simp [hbp]
  · intro a ha
    simp only [QState.setMem_mem]
    rw [ite_no (ha _ (.inr (.inr (.inr rfl)))), ite_no (ha _ (.inr (.inr (.inl rfl)))), e15, hs12]
    simp only [QState.setMem_mem]
    rw [ite_no (ha _ (.inr (.inl rfl))), ite_no (ha _ (.inl rfl)), e11, hs6]
    simp only [QState.setMem_mem]
    rw [ite_no (ha _ (.inr (.inl rfl))), ite_no (ha _ (.inl rfl)), e5]
  · intro a
    rw [NativeVm.Transcript.isSome_setMem _ _ (by
        rw [NativeVm.Transcript.isSome_setMem _ _ (by rw [e15, d12]; exact hsome _ (.inr (.inr (.inl rfl)))),
          e15, d12]
        exact hsome _ (.inr (.inr (.inr rfl)))),
      NativeVm.Transcript.isSome_setMem _ _ (by rw [e15, d12]; exact hsome _ (.inr (.inr (.inl rfl)))),
      e15, d12]

end NativeVm.Code.P7
