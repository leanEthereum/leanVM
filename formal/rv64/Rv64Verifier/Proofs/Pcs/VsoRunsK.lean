import Rv64Verifier.Proofs.Pcs.VsoLevelQ
import Rv64Verifier.Proofs.Pcs.VsoMerkleSrc

/-!
# `verify_stacked_opening`'s level loop: the mirror past the Merkle checks

The Merkle checks count a phase of openings read, so from them on the opening offset is `k` past
the level's (`RunsK`, `RunsC` at `k = 0`). `RunsK.merkle` is the mirror's `TM.merkleLeaves`, from
`merkle_model`: the root the level opens is `R[ℓ]`, at the stack's shape at level `0`
(`stackShape_eq`) and at `rootShape` beyond.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `RunsC`, the opening offset `k` past the level's. -/
def RunsK (s u : MachineState) (ℓ k : ℕ) (m : Model.TM Unit) (nx : List (Digest × ℕ × ℕ)) :
    Prop :=
  ∀ T, TranscriptAt s (s.getReg .x10) T → VsoOpeningsAt s (s.getReg .x10) T →
    T.roots = [(digestAt s (s.getReg .x11),
      Model.stackShape (s.getReg .x12).toNat (s.getReg .x13).toNat)] →
    ∃ T' R, (Model.Pcs.verifyStackedOpeningRust (s.getReg .x12).toNat (s.getReg .x13).toNat
        (claimsOf s)).run T = m.run T' ∧
      TranscriptAt u (s.getReg .x10) T' ∧ T'.proof = T.proof ∧
      T'.openingOffset = T.openingOffset + ℓ + k ∧ T'.roots = R ++ nx ∧ R.length = ℓ + 1 ∧
      (R[ℓ]?).map Prod.fst = some (digestAt u (s.getReg .x11)) ∧
      (ℓ = 0 → R = T.roots) ∧ (0 < ℓ → (R[ℓ]?).map Prod.snd = some (rootShape s ℓ))

theorem RunsC.toK {s u : MachineState} {ℓ : ℕ} {m : Model.TM Unit}
    {nx : List (Digest × ℕ × ℕ)} (h : RunsC s u ℓ m nx) : RunsK s u ℓ 0 m nx := h

/-- A step of the mirror that keeps the proof, the roots and the opening offset. -/
theorem RunsK.step {s u v : MachineState} {ℓ k : ℕ} {m m' : Model.TM Unit}
    {nx : List (Digest × ℕ × ℕ)} (h : RunsK s u ℓ k m nx)
    (hd : digestAt v (s.getReg .x11) = digestAt u (s.getReg .x11))
    (hstep : ∀ T, TranscriptAt u (s.getReg .x10) T → ∃ T', m.run T = m'.run T' ∧
      TranscriptAt v (s.getReg .x10) T' ∧ T'.proof = T.proof ∧ T'.roots = T.roots ∧
      T'.openingOffset = T.openingOffset) : RunsK s v ℓ k m' nx := by
  intro T hT hO hr
  obtain ⟨T₁, R, e₁, hT₁, p₁, o₁, r₁, l₁, d₁, z₁, sh₁⟩ := h T hT hO hr
  obtain ⟨T₂, e₂, hT₂, p₂, r₂, o₂⟩ := hstep T₁ hT₁
  exact ⟨T₂, R, e₁.trans e₂, hT₂, p₂.trans p₁, by rw [o₂, o₁], by rw [r₂, r₁], l₁,
    by rw [hd, d₁], z₁, sh₁⟩

/-- A step of the machine alone. -/
theorem RunsK.same {s u v : MachineState} {ℓ k : ℕ} {m : Model.TM Unit}
    {nx : List (Digest × ℕ × ℕ)} (h : RunsK s u ℓ k m nx)
    (hd : digestAt v (s.getReg .x11) = digestAt u (s.getReg .x11))
    (hT : ∀ T, TranscriptAt u (s.getReg .x10) T → TranscriptAt v (s.getReg .x10) T) :
    RunsK s v ℓ k m nx :=
  h.step hd fun T hT' ↦ ⟨T, rfl, hT T hT', rfl, rfl, rfl⟩

/-- A frame within `NS` that misses the root keeps the mirror. -/
theorem RunsK.keep {s u v : MachineState} {ℓ k : ℕ} {m : Model.TM Unit}
    {nx : List (Digest × ℕ × ℕ)} {n : Word} {X : Word → Prop} (hpre : VsoPre s)
    (h : RunsK s u ℓ k m nx) (hinv : InvR s u n) (hX : DFrame u v X) (hXs : ∀ a, X a → NS s a)
    (hr : ∀ y, Within y (s.getReg .x11) 32 → ¬ X y) : RunsK s v ℓ k m nx :=
  h.same (digest_keep hX (root_bound hpre) hr) fun _ hT ↦ tr_keep hpre hinv hT hX hXs

/-- A value the mirror draws, the same on every transcript the memory stands for. -/
theorem RunsK.bind {α : Type} {s u v : MachineState} {ℓ k : ℕ} {m : Model.TM α}
    {f : α → Model.TM Unit} {nx : List (Digest × ℕ × ℕ)} (a : α) (h : RunsK s u ℓ k (m >>= f) nx)
    (hd : digestAt v (s.getReg .x11) = digestAt u (s.getReg .x11))
    (hstep : ∀ T, TranscriptAt u (s.getReg .x10) T → ∃ T', m.run T = some (a, T') ∧
      TranscriptAt v (s.getReg .x10) T' ∧ T'.proof = T.proof ∧ T'.roots = T.roots ∧
      T'.openingOffset = T.openingOffset) : RunsK s v ℓ k (f a) nx :=
  h.step hd fun T hT ↦ by
    obtain ⟨T', e, hT', p, r, o⟩ := hstep T hT
    exact ⟨T', run_bind_of e, hT', p, r, o⟩

/-! ## The level's stages in the mirror -/

theorem afterCommit_split {logN : ℕ} {config : Model.Pcs.WhirConfigRust}
    {basis : List E → Option E} {level fc rt cnt : ℕ} {rest : List (ℕ × ℕ)}
    {S : Model.Pcs.WhirLocals} {lf res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} (h : config.queries[level]? = some cnt) :
    Model.Pcs.afterCommit logN config basis level fc rt rest S lf (res, pend) =
      (Model.TM.grind Model.Pcs.queryGrindingBitsRust >>= fun _ ↦
        Model.Pcs.sampleQueriesRust (1#64 <<< ((logN - S.folds.length + rt) % 64)) cnt) >>=
        Model.Pcs.afterQueries logN config basis level fc rest S lf res pend := by
  simp only [Model.Pcs.afterCommit, Model.Pcs.afterGrind, h, Model.TM.ofOption, pure_bind,
    bind_assoc]

theorem sample_run (T : Model.TState) :
    Model.TM.sample.run T = some ((spSqueeze T.sponge).1, { T with sponge := spDuplex T.sponge }) :=
  rfl

/-! ## The root a level opens -/

/-- Level `0`'s tree, at the stack's shape. -/
def stackShapeB (μ r : ℕ) : Bool := Model.stackShape μ r == (μ - 6 + r, 64)

theorem stackShape_window : ∀ μ < 29, ∀ r < 5, 15 ≤ μ → 1 ≤ r → stackShapeB μ r = true := by
  decide +kernel

theorem stackShape_eq {μ r : ℕ} (hμ : 15 ≤ μ ∧ μ ≤ 28) (hr : 1 ≤ r ∧ r ≤ 4) :
    Model.stackShape μ r = (μ - 6 + r, 64) := by
  have h := stackShape_window μ (by omega) r (by omega) hμ.1 hr.1
  simp only [stackShapeB, beq_iff_eq] at h
  exact h

/-- A leaf's width in words: `2 ^ fc` at level `0`, three times that beyond. -/
theorem widthW_toNat {ℓ fc : ℕ} (h : fc < 62) :
    (widthW ℓ fc).toNat = if ℓ = 0 then 2 ^ (fc % 64) else 3 * 2 ^ (fc % 64) := by
  have hm : fc % 64 = fc := Nat.mod_eq_of_lt (by omega)
  have hp : 2 ^ fc ≤ 2 ^ 61 := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [widthW, hm]
  split
  · rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt] <;> simp; omega
  · rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt] <;> simp; omega

/-- The shape of level `ℓ`'s root: at height `ml + rt`, its leaves `widthW` words. -/
theorem levelShape_eq {s : MachineState} {QP QL : Word} (hc : Cfg s QP QL) {ℓ n : ℕ}
    (hlt : ℓ < K0 s + 2) (hn : n = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum + fcOf s ℓ) :
    (ℓ = 0 → Model.stackShape (s.getReg .x12).toNat (s.getReg .x13).toNat =
      ((s.getReg .x12).toNat - n + rtOf s ℓ, (widthW ℓ (fcOf s ℓ)).toNat)) ∧
    (0 < ℓ → rootShape s ℓ =
      ((s.getReg .x12).toNat - n + rtOf s ℓ, (widthW ℓ (fcOf s ℓ)).toNat)) := by
  have hf := fcOf_eq s hlt
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · subst h0
    rw [stackShape_eq hc.logN hc.rate, hn]
    simp only [hf, ite_true]
    rfl
  · have hne : ℓ ≠ 0 := by omega
    have hm : fcOf s ℓ % 64 = fcOf s ℓ := by rw [hf, ite_eq_right hne]
    rw [widthW_toNat (by rw [hf, ite_eq_right hne]; omega), ite_eq_right hne, hm]
    simp only [rootShape, take_succ_sum, hn]
    rfl

/-! ## The Merkle checks -/

/-- **The mirror's Merkle step**: the phase's leaves, one phase more read. -/
theorem RunsK.merkle {s w m : MachineState} {ℓ fc d : ℕ} {lam : E} {qs : List Word}
    {logN : ℕ} {config : Model.Pcs.WhirConfigRust} {basis : List E → Option E}
    {rest : List (ℕ × ℕ)} {S : Model.Pcs.WhirLocals} {lfs res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {nx : List (Digest × ℕ × ℕ)}
    (hpre : VsoPre s) (hm : MerkleIn s w ℓ fc) (hout : MerkleOut s w m ℓ fc)
    (h : RunsK s w ℓ 0 (Model.Pcs.afterLam logN config basis ℓ fc rest S lfs res pend lam qs) nx)
    (hqs : w.readWords (w.getMem (s.getReg .x2 - 824)) (w.getReg .x26).toNat = qs)
    (hfc : fc < 62) (hd : d < 64) (hx8 : w.getReg .x8 = BitVec.ofNat 64 d)
    (hsh : (ℓ = 0 → Model.stackShape (s.getReg .x12).toNat (s.getReg .x13).toNat =
        (d, (widthW ℓ fc).toNat)) ∧ (0 < ℓ → rootShape s ℓ = (d, (widthW ℓ fc).toNat))) :
    RunsK s m ℓ 1 (Model.Pcs.afterWords logN config basis ℓ rest S lfs res pend lam qs
      ((phaseAt w (proofAt w (s.getReg .x10)) (w.getMem (s.getReg .x10 + 352)).toNat).map
        (·.leaf))) nx := by
  intro T hT hO hr
  obtain ⟨T₁, R, e₁, hT₁, p₁, o₁, r₁, l₁, d₁, z₁, sh₁⟩ := h T hT hO hr
  have hd8 : (w.getReg .x8).toNat = d := by rw [hx8]; exact Nat.mod_eq_of_lt (by omega)
  have hRl : ℓ < R.length := by omega
  obtain ⟨⟨dg, ht, wd⟩, hR⟩ : ∃ r, R[ℓ]? = some r := ⟨R[ℓ], List.getElem?_eq_getElem hRl⟩
  have hdg : dg = digestAt w (s.getReg .x11) := by
    rw [hR] at d₁; simpa using d₁
  have hshp : (ht, wd) = (d, (widthW ℓ fc).toNat) := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · subst h0
      rw [z₁ rfl, hr] at hR
      simp only [List.length_cons, List.length_nil, Nat.lt_add_one, getElem?_pos,
        List.getElem_cons_zero, Option.some.injEq, Prod.mk.injEq] at hR
      rw [← hR.2, hsh.1 rfl]
    · have := sh₁ h0
      rw [hR] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [this, hsh.2 h0]
  simp only [Prod.mk.injEq] at hshp
  have hroot : T₁.roots[ℓ]? =
      some (digestAt w (s.getReg .x11), (w.getReg .x8).toNat, (widthW ℓ fc).toNat) := by
    rw [r₁, List.getElem?_append_left hRl, hR, hdg, hshp.1, hshp.2, hd8]
  have hbl : Model.log2StrictRust (1#64 <<< (d % 64)) = some (w.getReg .x8).toNat := by
    rw [hd8]; exact Model.Pcs.log2StrictRust_one_shiftLeft hd
  obtain ⟨hrun, hT₂⟩ := merkle_model hpre hm hout hO hT₁ p₁ hroot hbl
  rw [hqs, widthW_toNat hfc] at hrun
  refine ⟨{ T₁ with openingOffset := T₁.openingOffset + 1 }, R, ?_, hT₂, p₁, by
    show T₁.openingOffset + 1 = _; rw [o₁], r₁, l₁, ?_, z₁, sh₁⟩
  · rw [e₁, Model.Pcs.afterLam]
    exact run_bind_of hrun
  · rw [digest_keep hout.fr (root_bound hpre) fun y hy hw ↦
      Clear.misses hpre (clear_of_outside hpre.root.stack hpre.root.free hpre.rootSponge
        hm.inv.mono) (hout.inv.heap hpre.heap).hi y hy hw, d₁]

end Rv64Verifier.Proofs.Pcs.Vso
