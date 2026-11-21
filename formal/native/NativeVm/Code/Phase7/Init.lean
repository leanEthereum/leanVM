module

public import NativeVm.Code.Phase7.Chunk
public import NativeVm.Code.Phase7.Ladder

/-!
# The opening's start

`initC`: the ladder of the stack's log-size and the rate exponent (`ladderC`) at `levO`, the
log-size at `cLogN`, WHIR's state with no `α`s and no glued claims (its claim, the batched
target, already at `whirR`), the level index `0` at `cIdx` and the non-final levels' count at `cN`
and in `r15`.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wdisp wd_inj wd_zero eval_cw wp_load wp_store wp_storei wp_reg ctxWork
  toUInt64_succ)

/-- The opening's start. -/
def initC : Stmt := blk [ldW, ldw .rcx (layoutR.off + 2), ldw .rdx (layoutR.off + 3),
  leaw .r14 levO, ladderC,
  stw cLogN .rcx, stwi (whirR.off + 2) 0, stwi (whirR.off + whirGluedOff) 0, stwi cIdx 0,
  ldw .r15 levO, I (.subi .r15 1), stw cN .r15]

/-- The words `initC` writes. -/
def initW (k : Nat) : Prop :=
  (levO ≤ k ∧ k < levO + levelsWords) ∨ k = cLogN ∨ k = cIdx ∨ k = cN ∨ k = whirR.off + 2 ∨
    k = whirR.off + whirGluedOff

variable {p : Par} {s : QState} {F : QState → Prop}

theorem levelsWords_val : levelsWords = 19 := rfl

theorem LevelsAt.congr {mem mem' : UInt64 → Option UInt64} {q : UInt64} {L : List Whir.Level}
    (h : Same mem mem' q levelsWords) (hl : L.length ≤ 6) (hL : LevelsAt mem q L) :
    LevelsAt mem' q L := by
  rw [levelsWords_val] at h
  refine ⟨hL.1.congr (h.base (by omega) rfl), fun k hk ↦ ?_⟩
  obtain ⟨a, b, c⟩ := hL.2 k hk
  exact ⟨a.congr (h _ (by omega)), b.congr (h _ (by omega)), c.congr (h _ (by omega))⟩

theorem ladderC_writes (r : Reg64) : ladderC.writes r = false := by
  cases r <;> decide +kernel

/-- **The opening's start.** -/
theorem initC_core {bc : Array UInt64} {layout : LayoutW} {rate : Nat} {target : EW}
    (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hlay : LayoutAt s.mem (layoutR.at p.env.work) bc layout rate)
    (hc : EWAt s.mem (wd p.env.work whirR.off) target) :
    WP initC s (fun s' ↦ ∃ L, Whir.ladder layout.stackLog rate = some L ∧
      LevelsAt s'.mem (wd p.env.work levO) L ∧ NatAt s'.mem (wd p.env.work cLogN) layout.stackLog ∧
      WhirAt s'.mem (whirR.at p.env.work) ⟨target, #[], #[]⟩ ∧ NatAt s'.mem (wd p.env.work cIdx) 0 ∧
      NatAt s'.mem (wd p.env.work cN) (L.length - 1) ∧ s'.reg .r15 = (L.length - 1).toUInt64 ∧
      (∀ a, (∀ k, initW k → a ≠ wd p.env.work k) → s'.mem a = s.mem a) ∧
      Only p.env initW s.mem s'.mem) F := by
  have hsome : ∀ k, mineLo ≤ k → k < dataEnd → (s.mem (wd p.env.work k)).isSome := fun k h1 h2 ↦
    hin.workSome k (by have := workWords_ge p.inp.bytecode.size; rw [dataEnd_val] at h2; omega)
  have hadm : Whir.Admissible layout.stackLog rate :=
    ⟨hlay.stackLogBound.1, hlay.stackLogBound.2, hlay.rateBound.1, hlay.rateBound.2⟩
  have hsl := hlay.stackLog
  have hrt := hlay.rateWord
  simp only [Region.at, wd_wd] at hsl hrt
  unfold initC ldW
  refine wp_load (eval_cw hrdi _) hwp ?_
  refine ldw_wp (env := p.env) (by simp) (by simpa using hsl.2) ?_
  refine ldw_wp (env := p.env) (by simp) (by simpa using hrt.2) ?_
  refine wp_reg rfl ?_
  refine WP.blk_cons (WP.mono (NativeVm.Transcript.WP.frame (ladderC_spec
      (D := wd p.env.work levO) hadm (by simp) (by simp) (by simp only [QState.setReg_reg, ite_true, ite_false, reduceCtorEq]; exact eval_w (env := p.env) (by simp) levO)
      (fun k hk ↦ by rw [wd_wd]; simp only [QState.setReg_mem]; exact hsome _ (by oomega) (by
        rw [levelsWords_val] at hk; oomega)))) (fun s1 h1 ↦ ?_) (fun _ h ↦ h.1))
  obtain ⟨⟨L, hL, hLv, hfr⟩, hd1, hr1⟩ := h1
  have hok := ladder_ok hadm hL
  have hlen := hok.len
  have r1 : ∀ r, s1.reg r = _ := fun r ↦ hr1 r (ladderC_writes r)
  have h1k : ∀ k, ¬ (levO ≤ k ∧ k < levO + 19) → k < 2 ^ 61 →
      s1.mem (wd p.env.work k) = s.mem (wd p.env.work k) := fun k hk hk' ↦ by
    rw [hfr _ fun j hj e ↦ hk (by
      rw [wd_wd] at e
      have := (wd_inj hk' (by rw [levelsWords_val] at hj; oomega)).mp e
      rw [levelsWords_val] at hj; omega)]
    rfl
  have s1some : ∀ k, mineLo ≤ k → k < dataEnd → (s1.mem (wd p.env.work k)).isSome := fun k h1 h2 ↦ by
    rw [hd1]; exact hsome k h1 h2
  have hW1 : s1.reg .rbp = p.env.work := by rw [r1]; simp
  refine stw_wp (env := p.env) hW1 (s1some _ (by oomega) (by oomega)) ?_
  refine wp_storei (eval_w (by simpa using hW1) _) (by wsimp; exact s1some _ (by oomega) (by oomega)) ?_
  refine wp_storei (eval_w (by simpa using hW1) _) (by wsimp; exact s1some _ (by oomega) (by oomega)) ?_
  refine wp_storei (eval_w (by simpa using hW1) _) (by wsimp; exact s1some _ (by oomega) (by oomega)) ?_
  refine ldw_wp (env := p.env) (by simpa using hW1) (by wsimp; exact hLv.1.2) ?_
  refine wp_reg rfl ?_
  refine stw_wp (env := p.env) (by simpa using hW1) (by wsimp; exact s1some _ (by oomega) (by oomega)) ?_
  refine NativeVm.Transcript.wp_done_gen fun s' hs' ↦ ?_
  have hU : ∀ k, ¬ initW k → k < 2 ^ 61 → s'.mem (wd p.env.work k) = s.mem (wd p.env.work k) := by
    intro k hk hk'
    simp only [initW, levelsWords_val, not_or] at hk
    rw [← hs']; wsimp
    exact h1k k (by omega) hk'
  have hlen1 : (L.length - 1).toUInt64 = L.length.toUInt64 - 1 := by
    rw [show L.length = (L.length - 1) + 1 by omega, ← toUInt64_succ]; simp
  have hsl' : layout.stackLog < 2 ^ 64 := hsl.1
  refine ⟨L, hL, ?_, ⟨hsl', ?_⟩, ⟨?_, ⟨by simp, ⟨by simp, ?_⟩, fun i hi ↦ absurd hi (by simp)⟩, by simp, ⟨by simp, ?_⟩,
    fun i hi ↦ absurd hi (by simp)⟩, ⟨by simp, ?_⟩, ⟨by omega, ?_⟩, ?_, ?_, ?_⟩
  · refine LevelsAt.congr (fun j hj ↦ ?_) (by omega) hLv
    rw [levelsWords_val] at hj
    rw [wd_wd, ← hs']; wsimp
  · rw [← hs']; wsimp; rw [r1]; simp
  · refine hc.congr (fun j hj ↦ ?_)
    rw [Region.at, wd_wd, hU _ (by simp only [initW, levelsWords_val]; oomega) (by oomega)]
  · rw [Region.at, wd_wd, ← hs']; wsimp; rfl
  · rw [Region.at, wd_wd, ← hs']; wsimp; rfl
  · rw [← hs']; wsimp; rfl
  · rw [← hs']; wsimp; rw [hlen1]; rfl
  · rw [← hs']; simp; rw [show (1 : Int64).toUInt64 = 1 from rfl]; exact hlen1.symm
  · intro a ha
    rw [← hs']
    repeat (first | rw [QState.setReg_mem] | rw [setMem_ne _ _ ?_])
    · rw [hfr _ fun j hj e ↦ ha (levO + j) (by simp only [initW, levelsWords_val] at hj ⊢; omega)
        (by rw [e, wd_wd])]
      rfl
    all_goals (refine ha _ ?_; unfold initW; oomega)
  · intro k h1 h2 hk
    exact hU k hk (by oomega)

theorem initC_writes_rdi : initC.writes .rdi = false := by
  unfold initC; simp only [blk, Stmt.writes, ladderC_writes]; decide

/-- **The opening's start**, with its frame. -/
theorem initC_spec {bc : Array UInt64} {layout : LayoutW} {rate : Nat} {target : EW}
    (hrdi : s.reg .rdi = p.env.ctx) (hin : Inputs p.env p.inp s.mem)
    (hwp : s.mem (wd p.env.ctx ctxWork) = some p.env.work)
    (hlay : LayoutAt s.mem (layoutR.at p.env.work) bc layout rate)
    (hc : EWAt s.mem (wd p.env.work whirR.off) target) :
    WP initC s (fun s' ↦ ∃ L, Whir.ladder layout.stackLog rate = some L ∧
      LevelsAt s'.mem (wd p.env.work levO) L ∧ NatAt s'.mem (wd p.env.work cLogN) layout.stackLog ∧
      WhirAt s'.mem (whirR.at p.env.work) ⟨target, #[], #[]⟩ ∧ NatAt s'.mem (wd p.env.work cIdx) 0 ∧
      NatAt s'.mem (wd p.env.work cN) (L.length - 1) ∧ s'.reg .r15 = (L.length - 1).toUInt64 ∧
      FrM p.env s s' ∧ Only p.env initW s.mem s'.mem) F :=
  WP.mono (NativeVm.Transcript.WP.frame (initC_core hrdi hin hwp hlay hc))
    (fun _ ⟨⟨L, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hd, hr⟩ ↦ ⟨L, h1, h2, h3, h4, h5, h6, h7,
      frM_of (hr .rdi initC_writes_rdi) hd h8 (fun k hk ↦ by simp only [initW, levelsWords_val] at hk; oomega),
      h9⟩) fun _ h ↦ h.1

end NativeVm.Code.P7
