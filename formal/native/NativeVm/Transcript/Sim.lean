module

public import NativeVm.Transcript.Sponge

/-!
# The simulation across a gadget

What a gadget that writes only its footprint (`Foot`) keeps of `SimState`: the areas (`Layout`),
the decoded proof (`Decoded.congr`), the context's pointers; and how the work area's words read
(`eval_work`). `SimState.mk'` rebuilds the relation from the parts a gadget changes.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile

theorem openingWords_val : openingWords = 193 := (rfl)
theorem phaseWords_val : phaseWords = 49411 := (rfl)
theorem wireMaxLeafWords_val : wireMaxLeafWords = 64 := (rfl)
theorem wireMaxHeight_val : wireMaxHeight = 32 := (rfl)
theorem wireMaxQueries_val : wireMaxQueries = 256 := (rfl)
theorem wireMaxPhases_val : wireMaxPhases = 8 := (rfl)

theorem phaseBase_eq (L k : Nat) : phaseBase L k = 2 + 2 * (L / 16) + 49411 * k := by
  simp only [phaseBase, streamEnd, maxStream, phaseWords_val]
  omega

theorem decodedWords_eq (L : Nat) : decodedWords L = 2 + 2 * (L / 16) + 49411 * 8 := by
  simp only [decodedWords, phaseBase_eq, wireMaxPhases_val]

theorem streamEnd_eq (L : Nat) : streamEnd L = 1 + 2 * (L / 16) := (rfl)

/-- **The decoded proof, kept** where its area's words are. -/
theorem Decoded.congr {m m' : UInt64 → Option UInt64} {a : UInt64} {L : Nat} {π : Proof}
    (h : Decoded m a L π) (hm : ∀ i < decodedWords L, m' (wd a i) = m (wd a i)) :
    Decoded m' a L π := by
  have hd := decodedWords_eq L
  obtain ⟨hs, h0, hel, hp, hpc, hph⟩ := h
  have hs' : π.stream.length ≤ L / 16 := hs
  refine ⟨hs, (hm 0 (by omega)).trans h0, fun i hi l hl ↦ ?_, hp, ?_, fun k hk ↦ ?_⟩
  · exact (hm _ (by omega)).trans (hel i hi l hl)
  · exact (hm _ (by rw [streamEnd_eq]; omega)).trans hpc
  · obtain ⟨hh, width, h1, h2, h3, h4, h5, h6, h7⟩ := hph k hk
    have hk8 : k < 8 := lt_of_lt_of_le hk hp
    have hb := phaseBase_eq L k
    simp only [wireMaxHeight_val, wireMaxLeafWords_val, wireMaxQueries_val] at h1 h2 h3
    refine ⟨hh, width, h1, h2, h3, (hm _ (by omega)).trans h4, (hm _ (by omega)).trans h5,
      (hm _ (by omega)).trans h6, fun j hj ↦ ?_⟩
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h7 j hj
    have hj' : j < 256 := by omega
    refine ⟨g1, g2, g3, (hm _ ?_).trans g4, fun t ht ↦ (hm _ ?_).trans (g5 t ht),
      fun d hd' l hl ↦ (hm _ ?_).trans (g6 d hd' l hl)⟩
    · rw [openingWords_val]; nlinarith
    · rw [openingWords_val]; nlinarith
    · rw [openingWords_val, wireMaxLeafWords_val]; nlinarith

/-! ## Words outside the footprint -/

variable {env : Env} {mem : UInt64 → Option UInt64}

theorem Layout.dec_not_foot (h : Layout env mem) {i : Nat} (hi : i < decodedWords env.L) :
    ¬ Foot env (wd env.dec i) := by
  rintro (⟨k, h1, h2, e⟩ | ⟨k, hk, e⟩)
  · exact wd_ne_of_disj h.fitDec h.fitCtx h.disjCD.symm hi h2 e
  · exact wd_ne_of_disj h.fitDec h.fitWork h.disjDW hi hk e

theorem Layout.ctx_not_foot (h : Layout env mem) {k : Nat} (hk : k < scratchW) :
    ¬ Foot env (wd env.ctx k) := by
  rintro (⟨k', h1, h2, e⟩ | ⟨k', hk', e⟩)
  · rw [wd_inj (by lay_omega) (by lay_omega)] at e
    omega
  · exact wd_ne_of_disj h.fitCtx h.fitWork h.disjCW (by lay_omega) hk' e

/-- The context's words from `lo` to `hi`. -/
theorem foot_ctx {lo hi : Nat} {a : UInt64} (h : CtxIn env.ctx lo hi a) (hlo : scratchW ≤ lo)
    (hhi : hi ≤ ctxEnd) : Foot env a := by
  obtain ⟨k, h1, h2, rfl⟩ := h
  exact .inl ⟨k, by omega, by omega, rfl⟩

/-- The working area's word `k`. -/
theorem foot_work {k : Nat} (hk : k < workWords) : Foot env (wd env.work k) := .inr ⟨k, hk, rfl⟩

/-- A word of the working area other than `k`'s. -/
theorem Layout.work_ne_ctx (h : Layout env mem) {k j : Nat} (hk : k < workWords) (hj : j < ctxEnd) :
    wd env.work k ≠ wd env.ctx j :=
  fun e ↦ wd_ne_of_disj h.fitCtx h.fitWork h.disjCW hj hk e.symm

/-! ## The working area's words exist -/

/-- The working area's words exist. -/
def WDom (env : Env) (mem : UInt64 → Option UInt64) : Prop :=
  ∀ k < workWords, (mem (wd env.work k)).isSome

theorem WDom.setMem {s : QState} (h : WDom env s.mem) (a v : UInt64) : WDom env (s.setMem a v).mem :=
  fun k hk ↦ by
    rw [QState.setMem_mem]
    split
    · rfl
    · exact h k hk

theorem WDom.setReg {s : QState} (h : WDom env s.mem) (r : Reg64) (v : UInt64) :
    WDom env (s.setReg r v).mem := h

theorem WDom.isSome (h : WDom env mem) {k : Nat} (hk : k < workWords) : (mem (wd env.work k)).isSome :=
  h k hk

/-- A word of the working area exists, through register and memory updates. -/
macro "wsome_tac" : tactic => `(tactic| (
  refine WDom.isSome ?_ (by lay_omega)
  repeat (first
    | with_reducible refine WDom.setMem ?_ _ _
    | with_reducible refine WDom.setReg ?_ _ _
    | exact SimState.wdom (by assumption)
    | with_reducible assumption)))

/-- Keep the words outside the footprint through register updates and stores to the working area. -/
macro "keep_tac" : tactic => `(tactic| (
  repeat (first
    | with_reducible refine Keep.setMem ?_ (foot_work (by lay_omega)) _
    | with_reducible refine Keep.setReg ?_ _ _
    | exact Keep.refl _ _)))

/-- Which words exist, through register updates and stores to the working area. -/
macro "wisSome_tac" : tactic => `(tactic| (
  repeat (first
    | rw [QState.setReg_mem]
    | rw [isSome_setMem _ _ (by wsome_tac)])))

/-! ## The relation rebuilt -/

theorem Layout.congr (h : Layout env mem) {mem' : UInt64 → Option UInt64}
    (hs : ∀ a, (mem' a).isSome = (mem a).isSome) (hk : Keep (Foot env) mem mem') :
    Layout env mem' where
  fitCtx := h.fitCtx
  fitDec := h.fitDec
  fitWork := h.fitWork
  disjCD := h.disjCD
  disjCW := h.disjCW
  disjDW := h.disjDW
  ctxSome k hk' := by rw [hs]; exact h.ctxSome k hk'
  workSome k hk' := by rw [hs]; exact h.workSome k hk'
  decPtr := by rw [hk _ (h.ctx_not_foot (by lay_omega))]; exact h.decPtr
  workPtr := by rw [hk _ (h.ctx_not_foot (by lay_omega))]; exact h.workPtr

theorem Layout.dom (h : Layout env mem) : Dom env.ctx mem := h.ctxSome

theorem Layout.wdom (h : Layout env mem) : WDom env mem := h.workSome

/-- **`SimState` after a gadget**: what the gadget writes stays in its footprint, so the areas and
the decoded proof are kept; the sponge, the cursors and the roots are the gadget's to give. -/
theorem SimState.mk' {st st' : VerifierProgramState} {s s' : QState} (h : SimState env st s)
    (hrdi : s'.reg .rdi = env.ctx) (hs : ∀ a, (s'.mem a).isSome = (s.mem a).isSome)
    (hk : Keep (Foot env) s.mem s'.mem) (hsp : SpongeAt s'.mem env.ctx st'.sponge)
    (hcur : ∃ c ≤ env.proof.stream.length, s'.mem (wd env.work workCursor) = some c.toUInt64 ∧
      st'.stream = env.proof.stream.drop c)
    (hph : ∃ p ≤ env.proof.openings.length, s'.mem (wd env.work workPhase) = some p.toUInt64 ∧
      s'.mem (wd env.work workPhasePtr) = some (wd env.dec (phaseBase env.L p)) ∧
      st'.openings = env.proof.openings.drop p)
    (hpc : s'.mem (wd env.work workPhaseCount) = some env.proof.openings.length.toUInt64)
    (hrl : st'.roots.length ≤ maxRoots)
    (hrc : s'.mem (wd env.work workRootCount) = some st'.roots.length.toUInt64)
    (hroots : ∀ j (hj : j < st'.roots.length), RootAt s'.mem env.work j st'.roots[j]) :
    SimState env st' s' where
  rdi := hrdi
  layout := h.layout.congr hs hk
  decoded := Decoded.congr h.decoded fun _ hi ↦ hk _ (h.layout.dec_not_foot hi)
  sponge := hsp
  cursor := hcur
  phase := hph
  phaseCount := hpc
  rootsLen := hrl
  rootCount := hrc
  roots := hroots

theorem SimState.wdom {st : VerifierProgramState} {s : QState} (h : SimState env st s) :
    WDom env s.mem := h.layout.workSome

/-! ## The working area's words -/

theorem work_reg {s : QState} {r : Reg64} (hr : s.reg r = env.work) (k : Nat) : (at_ r (wdisp k)).eval s = wd env.work k := by
  rw [eval_wd (j := 0) (by rw [hr, wd_zero]), Nat.zero_add]

/-- A word of the working area, kept where the footprint leaves it. -/
theorem keep_work {s s' : QState} {W : UInt64 → Prop} (hk : Keep W s.mem s'.mem) {k : Nat}
    (h : ¬ W (wd env.work k)) : s'.mem (wd env.work k) = s.mem (wd env.work k) := hk _ h

end NativeVm.Transcript
