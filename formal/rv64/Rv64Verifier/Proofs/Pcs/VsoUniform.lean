import Rv64Verifier.Proofs.Pcs.VsoOpenCommitE
import Rv64Verifier.Proofs.Pcs.VsoLamPowers

/-!
# `verify_stacked_opening`'s level loop: the queries for every transcript

`TranscriptAt` pins a transcript's stream, sponge and offsets; its openings and roots are free
(`withOR`). The grinding and `sample_queries` neither read nor write them (`Indep`), so the
queries drawn from one transcript the memory stands for are drawn from every one (`queriesU`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  Rv64Verifier.MultilinearContracts LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `t` with `o`'s openings and roots. -/
def withOR (t o : Model.TState) : Model.TState :=
  { t with proof := { t.proof with openings := o.proof.openings }, roots := o.roots }

/-- `m` neither reads nor writes the openings and the roots. -/
def Indep {α : Type} (m : Model.TM α) : Prop :=
  ∀ t o, m.run (withOR t o) = (m.run t).map fun p ↦ (p.1, withOR p.2 o)

theorem Indep.pure {α : Type} (a : α) : Indep (Pure.pure a : Model.TM α) := fun _ _ ↦ rfl

theorem Indep.bind {α β : Type} {m : Model.TM α} {k : α → Model.TM β} (hm : Indep m)
    (hk : ∀ a, Indep (k a)) : Indep (m >>= k) := by
  intro t o
  rw [StateT.run_bind, StateT.run_bind, hm t o]
  cases m.run t with
  | none => rfl
  | some p => exact hk p.1 p.2 o

theorem Indep.ofOption {α : Type} (x : Option α) : Indep (Model.TM.ofOption x) := by
  cases x <;> intro t o <;> rfl

theorem Indep.sample : Indep Model.TM.sample := fun _ _ ↦ rfl

theorem Indep.grind (bits : ℕ) : Indep (Model.TM.grind bits) := by
  intro t o
  show Model.TM.grind bits (withOR t o) = (Model.TM.grind bits t).map _
  simp only [Model.TM.grind, withOR]
  cases t.proof.stream[t.streamOffset]? with
  | none => rfl
  | some n =>
    dsimp only
    split <;> rename_i hp <;> simp only [hp, ↓reduceIte] <;> rfl

theorem Indep.sampleQueriesLoop (bl : BitVec 64) (depth count : ℕ) :
    ∀ fuel r, Indep (Model.Pcs.sampleQueriesLoop bl depth count fuel r) := by
  intro fuel
  induction fuel with
  | zero => intro r; exact Indep.pure r
  | succ f ih =>
    intro r
    simp only [Model.Pcs.sampleQueriesLoop]
    split
    · exact Indep.sample.bind fun _ ↦ ih _
    · exact Indep.pure r

theorem Indep.sampleQueriesRust (bl : BitVec 64) (count : ℕ) :
    Indep (Model.Pcs.sampleQueriesRust bl count) :=
  (Indep.ofOption _).bind fun _ ↦ Indep.sampleQueriesLoop _ _ _ _ _

theorem tr_withOR {u : MachineState} {p : Word} {T : Model.TState} (o : Model.TState)
    (h : TranscriptAt u p T) : TranscriptAt u p (withOR T o) :=
  ⟨h.stream, h.sponge, h.streamOffset, h.openingOffset⟩

/-- Two transcripts the memory stands for differ in their openings and roots alone. -/
theorem eq_withOR {u : MachineState} {p : Word} {T T₀ : Model.TState} (h : TranscriptAt u p T)
    (h₀ : TranscriptAt u p T₀) : T = withOR T₀ T := by
  obtain ⟨⟨st, op⟩, sp, so, oo, ro⟩ := T
  obtain ⟨⟨st₀, op₀⟩, sp₀, so₀, oo₀, ro₀⟩ := T₀
  have e1 : st = st₀ := h.stream.symm.trans h₀.stream
  have e2 : sp = sp₀ := h.sponge.symm.trans h₀.sponge
  have e3 : so = so₀ := h.streamOffset.symm.trans h₀.streamOffset
  have e4 : oo = oo₀ := h.openingOffset.symm.trans h₀.openingOffset
  subst e1 e2 e3 e4
  rfl

/-- **The grinding and the queries**, for every transcript the memory at `0x8000a790` stands
for; the residual's buffer and length spilled at `S - 968` and `S - 960`. -/
theorem queriesU (hD : DuplexSpec) (hA : AbsorbSpec) (hTA : TryAllocZeroedSpec)
    {s u : MachineState} {QP QL : Word} {ℓ ml rt : ℕ} (hpre : VsoPre s)
    (hc : Cfg s QP QL)
    (hconf : Model.Pcs.deriveConfigRust (s.getReg .x12).toNat (s.getReg .x13).toNat =
      some (cfgOf s))
    (hinv : InvR s u (u.getMem nextAddr)) (hpc : u.pc = 0x8000a790) (hlt : ℓ < K0 s + 2)
    (hmr : ml + rt < 64)
    (h184 : u.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ)
    (h240 : u.getMem (s.getReg .x2 - 800) = QL)
    (h192 : u.getMem (s.getReg .x2 - 848) = QP)
    (h208 : u.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 (8 * ℓ))
    (h168 : u.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 ml)
    (h216 : u.getMem (s.getReg .x2 - 824) = BitVec.ofNat 64 rt)
    (h224 : u.getMem (s.getReg .x2 - 816) = s.getReg .x10)
    (h248 : u.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8) :
    ∃ v, Reaches Image.code u v ∧ (FailR s v ∨ ∃ cnt qs,
      (cfgOf s).queries[ℓ]? = some cnt ∧ qs.length = cnt ∧ 0 < ml + rt ∧
      QOut s u v (ml + rt) qs ∧
      (∀ T, TranscriptAt u (s.getReg .x10) T → ∃ T',
        (∀ k : List Word → Model.TM Unit,
          (Model.TM.grind Model.Pcs.queryGrindingBitsRust >>= fun _ ↦
            Model.Pcs.sampleQueriesRust (1#64 <<< ((ml + rt) % 64)) cnt >>= k).run T =
            (k qs).run T') ∧
        TranscriptAt v (s.getReg .x10) T' ∧ T'.proof = T.proof ∧ T'.roots = T.roots ∧
        T'.openingOffset = T.openingOffset) ∧
      v.getMem (s.getReg .x2 - 968) = u.getReg .x1 ∧ v.getMem (s.getReg .x2 - 960) = u.getReg .x31) := by
  obtain ⟨T₀, hT₀⟩ := exists_TA u (s.getReg .x10)
  obtain ⟨v, hr, hv⟩ := queries hD hA hTA hpre hc hconf hinv hpc hlt hmr h184 h240 h192 h208 h168
    h216 h224 h248 hT₀
  rcases hv with hf | ⟨cnt, qs, T₀', hcnt, hql, hpos, hq, hrun, hT₀', p, ro, o, s1, s2⟩
  · exact ⟨v, hr, Or.inl hf⟩
  refine ⟨v, hr, Or.inr ⟨cnt, qs, hcnt, hql, hpos, hq, fun T hT ↦ ?_, s1, s2⟩⟩
  have hP : (Model.TM.grind Model.Pcs.queryGrindingBitsRust >>= fun _ ↦
      Model.Pcs.sampleQueriesRust (1#64 <<< ((ml + rt) % 64)) cnt).run T₀ = some (qs, T₀') := by
    have h := hrun fun q ↦ Model.TM.require (q = qs)
    rw [← bind_assoc, StateT.run_bind] at h
    rcases e : (Model.TM.grind Model.Pcs.queryGrindingBitsRust >>= fun _ ↦
      Model.Pcs.sampleQueriesRust (1#64 <<< ((ml + rt) % 64)) cnt).run T₀ with _ | ⟨q', T''⟩
    · rw [e] at h
      change (none : Option (Unit × Model.TState)) =
        (if qs = qs then some ((), T₀') else none) at h
      simp at h
    · rw [e] at h
      change (if q' = qs then some ((), T'') else none) =
        (if qs = qs then some ((), T₀') else none) at h
      by_cases hq : q' = qs
      · subst hq
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and] at h
        rw [h]
      · simp only [hq, ↓reduceIte] at h
        simp at h
  have hI := (Indep.grind Model.Pcs.queryGrindingBitsRust).bind fun _ ↦
    Indep.sampleQueriesRust (1#64 <<< ((ml + rt) % 64)) cnt
  have eT := eq_withOR hT hT₀
  have hPT := hI T₀ T
  rw [hP, ← eT] at hPT
  change _ = some (qs, withOR T₀' T) at hPT
  refine ⟨withOR T₀' T, fun k ↦ ?_, tr_withOR T hT₀', ?_, rfl, ?_⟩
  · rw [← bind_assoc]
    exact run_bind_of hPT
  · show { T₀'.proof with openings := T.proof.openings } = T.proof
    rw [p]
    exact (congrArg Model.TState.proof eT).symm
  · show T₀'.openingOffset = T.openingOffset
    rw [o, congrArg Model.TState.openingOffset eT]
    rfl

/-- **`lam` drawn and its powers**, for every transcript the memory at `0x8000a9d8` stands for. -/
theorem lamPowersU (hD : DuplexSpec) (hP : PowersSpec) {s u : MachineState} (hpre : VsoPre s)
    (hinv : InvR s u (u.getMem nextAddr)) (hpc : u.pc = 0x8000a9d8)
    (h248 : u.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8)
    (hx20 : u.getReg .x20 = s.getReg .x10) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨
      ∀ T, TranscriptAt u (s.getReg .x10) T → LamOut s u w T) := by
  obtain ⟨T₀, hT₀⟩ := exists_TA u (s.getReg .x10)
  obtain ⟨w, hr, hw⟩ := lamPowers hD hP hpre hinv hpc h248 hx20 hT₀
  rcases hw with hd | hl
  · exact ⟨w, hr, Or.inl hd⟩
  refine ⟨w, hr, Or.inr fun T hT ↦ ?_⟩
  have e := eq_withOR hT hT₀
  have hsp : T.sponge = T₀.sponge := by rw [e]; rfl
  exact { hl with
    tr := by
      have := tr_withOR T hl.tr
      rw [e]
      exact this
    lam := by rw [hsp]; exact hl.lam
    elems := by rw [hsp]; exact hl.elems }

end Rv64Verifier.Proofs.Pcs.Vso
