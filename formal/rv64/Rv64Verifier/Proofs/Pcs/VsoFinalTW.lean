import Rv64Verifier.Proofs.Pcs.VsoFinalTail
import Rv64Verifier.Proofs.Pcs.VsoCalls

/-!
# `verify_stacked_opening`'s final level: what the tail writes

From `VsoFinalIn`'s state `u` (`0x8000b8ec`) on, the tail writes `TW`: the frame's scratch slots
`S - 920`..`S - 776` and `S - 464`..`S - 104`, the callees' stacks, `NEXT`, the heap allocated
since `u`, the sponge and offsets. `TI` is the tail's invariant at `v`: `VsoFinalIn` at `u`, and
`v` changed from `u` only there. The mirror's rest after the tail's rounds is `afterTail`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the tail writes from `u` on, `NEXT` at `hi`. -/
def TW (s u : MachineState) (hi a : Word) : Prop :=
  Within a (s.getReg .x2 - 920) 144 ∨ Within a (s.getReg .x2 - 464) 360 ∨
    Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨
    (heapNext u ≤ a.toNat ∧ a.toNat < hi.toNat) ∨ W s a

theorem TW.mono {s u : MachineState} {hi hi' a : Word} (hle : hi.toNat ≤ hi'.toNat)
    (h : TW s u hi a) : TW s u hi' a := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- The tail's invariant at `v`. -/
structure TI (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) : Prop where
  fin : VsoFinalIn OA s x u Wl residual
  fr : DFrame u v (TW s u (v.getMem nextAddr))
  heap : HeapOk v
  mono : heapNext u ≤ heapNext v
  sp : v.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040

section
variable {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
  {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E}

theorem VsoFinalIn.hs (h : VsoFinalIn OA s x u Wl residual) : heapNext s ≤ x.L := by
  have := h.cfg.nxs; have := h.mark; omega

theorem VsoFinalIn.su (h : VsoFinalIn OA s x u Wl residual) : heapNext s ≤ heapNext u := by
  have := h.hs; have := h.mark; have := h.mono; omega

theorem VsoFinalIn.invR (hpre : VsoPre s) (h : VsoFinalIn OA s x u Wl residual) :
    InvR s u (u.getMem nextAddr) :=
  LM.inv hpre h.cfg.inv h.hs h.fr h.heap h.mono (h.sp.trans h.cfg.inv.sp.symm)

theorem TI.su (h : TI OA s x u v Wl residual) : heapNext s ≤ heapNext v :=
  Nat.le_trans h.fin.su h.mono

theorem TI.inv (hpre : VsoPre s) (h : TI OA s x u v Wl residual) :
    InvR s v (v.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsu := h.fin.su
  have hhi := h.heap.hi
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  refine Inv.step' hpre (h.fin.invR hpre) h.fr (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl h.mono hhi
    (h.sp.trans h.fin.sp.symm)
  · rcases ha with ha | ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨Nat.le_trans hsu ha.1, ha.2⟩))
    · exact Or.inl (Or.inl ha)
  · rcases ha with ha | ha | ha | ha | ha | ha
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · addr_omega [ha.2, hb, hhi]
    · simp only [W] at ha; addr_omega [ha, hIs, hS, hb]

/-- The tail's writes but the sponge are in `NS`. -/
theorem TW.ns (hpre : VsoPre s) (hsu : heapNext s ≤ heapNext u) {hi a : Word}
    (hhi : hi.toNat ≤ heapEnd) (ha : TW s u hi a) (hW : ¬ W s a) : NS s a := by
  have hb := bounds hpre
  rcases ha with ha | ha | ha | ha | ha | ha
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inl (by addr_omega [ha, hb])
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ⟨Nat.le_trans hsu ha.1, by omega⟩))
  · exact absurd ha hW

/-- The tail's writes miss the root. -/
theorem TW.root (hpre : VsoPre s) (hsu : heapNext s ≤ heapNext u) {hi : Word}
    (hhi : hi.toNat ≤ heapEnd) : ∀ y, Within y (s.getReg .x11) 32 → ¬ TW s u hi y := by
  have hb := bounds hpre
  have hr := hpre.root
  have hrs := hpre.rootSponge
  have hst := hr.stack
  have hfr := hr.free
  rw [stackLo_vso, vso_stack] at hst
  simp only [Outside] at hfr
  intro y hy ha
  rcases ha with ha | ha | ha | ha | ha | ha
  · addr_omega [hy, ha, hst, hb]
  · addr_omega [hy, ha, hst, hb]
  · addr_omega [hy, ha, hst, hb]
  · addr_omega [hy, ha, hfr.2]
  · rcases hfr.1 with h1 | h1
    · addr_omega [hy, ha.1, h1, hsu]
    · addr_omega [hy, ha.2, h1, hhi]
  · simp only [W] at ha; addr_omega [hy, ha, hrs]

theorem TI.ns (hpre : VsoPre s) (h : TI OA s x u v Wl residual) {a : Word}
    (ha : TW s u (v.getMem nextAddr) a) (hW : ¬ W s a) : NS s a :=
  TW.ns hpre h.fin.su h.heap.hi ha hW

/-- One more step whose writes are the tail's. -/
theorem TI.trans {w : MachineState} {X : Word → Prop} (h : TI OA s x u v Wl residual)
    (hX : DFrame v w X) (hXs : ∀ a, X a → TW s u (w.getMem nextAddr) a) (hheap : HeapOk w)
    (hmono : heapNext v ≤ heapNext w) (hsp : w.getReg .x2 = v.getReg .x2) :
    TI OA s x u w Wl residual :=
  ⟨h.fin, (h.fr.mono fun _ ha ↦ TW.mono hmono ha).trans hX hXs, hheap,
    Nat.le_trans h.mono hmono, hsp.trans h.sp⟩

/-- A word the tail does not write since `u`. -/
theorem TI.keep (h : TI OA s x u v Wl residual) {y : Word}
    (hy : ∀ i < 8, ¬ TW s u (v.getMem nextAddr) (y + BitVec.ofNat 64 i)) :
    v.getMem y = u.getMem y :=
  h.fr y hy

/-- A frame slot the tail keeps. -/
theorem TI.keepStk (hpre : VsoPre s) (h : TI OA s x u v Wl residual) {y : Word}
    (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 920).toNat ∨
      (s.getReg .x2 - 776).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat) :
    v.getMem y = u.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hhi := h.heap.hi
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  refine h.fr y fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw
  · addr_omega [hw, hi, hb, hy]
  · addr_omega [hw, hi, hb, hy]
  · addr_omega [hw, hi, hb, hy]
  · addr_omega [hw, hi, hb, hy, hnx]
  · simp only [heapEnd] at hhi hab; addr_omega [hw.2, hi, hb, hy, hhi, hab]
  · simp only [W] at hw; addr_omega [hw, hi, hb, hy, hIs, hS]

/-- The heap allocated between the entry and `u` misses the tail's writes. -/
theorem TW.heap_miss (hpre : VsoPre s) (hu : heapNext u ≤ heapEnd) {hi y : Word}
    (h1 : heapNext s ≤ y.toNat) (h2 : y.toNat < heapNext u) : ¬ TW s u hi y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hf := hI.free
  simp only [Outside] at hf
  simp only [heapEnd] at hu hab
  intro hw
  rcases hw with hw | hw | hw | hw | hw | hw
  · addr_omega [hw, hb, h2, hu, hab]
  · addr_omega [hw, hb, h2, hu, hab]
  · addr_omega [hw, hb, h2, hu, hab]
  · addr_omega [hw, h2, hu, hnx, hab, hb]
  · omega
  · simp only [W] at hw
    rcases hf.1 with h0 | h0
    · addr_omega [hw, h0, h1, hS]
    · simp only [heapEnd] at h0; addr_omega [hw, h0, h2, hu, hS]

/-- A heap word allocated between the entry and `u`, the tail keeps. -/
theorem TI.keepHeap (hpre : VsoPre s) (h : TI OA s x u v Wl residual) {y : Word}
    (h1 : heapNext s ≤ y.toNat) (h2 : y.toNat + 8 ≤ heapNext u) :
    v.getMem y = u.getMem y := by
  have hhu := h.fin.heap.hi
  simp only [heapEnd] at hhu
  exact h.fr y fun i hi ↦ TW.heap_miss hpre h.fin.heap.hi (by addr_omega [h1, h2, hi, hhu])
    (by addr_omega [h1, h2, hi, hhu])

/-- `n` elements from `p`, between the entry's `NEXT` and `u`'s, the tail keeps. -/
theorem TI.eList (hpre : VsoPre s) (h : TI OA s x u v Wl residual) {p : Word} {n : ℕ}
    (hn : n = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + 24 * n ≤ heapNext u) :
    eListAt v p n = eListAt u p n := by
  have hhu := h.fin.heap.hi
  simp only [heapEnd] at hhu
  rcases hn with h0 | h0
  · subst h0; rfl
  · exact DFrame.eList h.fr (fun y hy ↦ TW.heap_miss hpre h.fin.heap.hi
      (by simp only [Within] at hy; omega) (by simp only [Within] at hy; omega)) (Or.inr (by omega))

/-! ## The mirror -/

/-- What runs as `RunsF` on, step by step. -/
theorem RunsF.step {m m' : Model.TM Unit} {w : MachineState} (h : RunsF OA s v m)
    (hstep : ∀ T, TranscriptAt v (s.getReg .x10) T → ∃ T', m.run T = m'.run T' ∧
      TranscriptAt w (s.getReg .x10) T') : RunsF OA s w m' := fun T hT hO hr ↦ by
  obtain ⟨T₁, e₁, hT₁⟩ := h T hT hO hr
  obtain ⟨T₂, e₂, hT₂⟩ := hstep T₁ hT₁
  exact ⟨T₂, e₁.trans e₂, hT₂⟩

/-- A step missing the transcript keeps the mirror. -/
theorem RunsF.keep {m : Model.TM Unit} {w : MachineState} {nx : Word} {X : Word → Prop}
    (hpre : VsoPre s) (h : RunsF OA s v m) (hinv : InvR s v nx) (hX : DFrame v w X)
    (hXs : ∀ a, X a → NS s a) : RunsF OA s w m :=
  h.step fun T hT ↦ ⟨T, rfl, tr_keep hpre hinv hT hX hXs⟩

end

/-- After the tail's rounds: the terminal weight, then the check. -/
def afterTail (config : Model.Pcs.WhirConfigRust) (basis : List E → Option E)
    (residual : List E) (Wl : Model.Pcs.WhirLocals) (tf : List E) (rt : E) : Model.TM Unit := do
  let laneFolds ← Model.TM.ofOption config.folds[0]?
  let weight ← Model.TM.ofOption
    (Model.Pcs.terminalWeightRust basis laneFolds Wl.glued (Wl.folds ++ tf))
  terminalCheckM residual tf weight rt

/-- The tail's rounds from `i` on, then the rest. -/
def roundsK (config : Model.Pcs.WhirConfigRust) (basis : List E → Option E)
    (residual : List E) (Wl : Model.Pcs.WhirLocals) (ml i : ℕ) (st : List E × List E × E) :
    Model.TM Unit :=
  Model.Pcs.TM.forRange (Model.Pcs.tailRoundRust ml) i (ml - i) st >>= fun st ↦
    afterTail config basis residual Wl st.2.1 st.2.2

theorem finalTailM_eq (config : Model.Pcs.WhirConfigRust) (basis : List E → Option E)
    (residual : List E) (ml : ℕ) (Wl : Model.Pcs.WhirLocals) :
    finalTailM config basis residual ml Wl = roundsK config basis residual Wl ml 0
      (Wl.runningQuad, [], 0) := by
  unfold finalTailM roundsK
  rw [Nat.sub_zero]
  congr 1

/-- Round `i`'s rest, its challenge `c` drawn. -/
def sampledK (config : Model.Pcs.WhirConfigRust) (basis : List E → Option E)
    (residual : List E) (Wl : Model.Pcs.WhirLocals) (ml i : ℕ) (q tf : List E) (c : E) :
    Model.TM Unit :=
  (if i + 1 < ml then do
      let q' ← Model.TM.sumcheckRoundPoly 3 (Model.polyEvalRust q c) none
      pure (q', tf ++ [c], Model.polyEvalRust q c)
    else pure (q, tf ++ [c], Model.polyEvalRust q c)) >>= roundsK config basis residual Wl ml (i + 1)

theorem roundsK_succ (config : Model.Pcs.WhirConfigRust) (basis : List E → Option E)
    (residual : List E) (Wl : Model.Pcs.WhirLocals) {ml i : ℕ} (hi : i < ml) (q tf : List E)
    (rt : E) : roundsK config basis residual Wl ml i (q, tf, rt) =
      Model.TM.sample >>= sampledK config basis residual Wl ml i q tf := by
  unfold roundsK sampledK
  rw [show ml - i = ml - (i + 1) + 1 by omega]
  simp only [Model.Pcs.TM.forRange, Model.Pcs.tailRoundRust, bind_assoc]
  congr 1

theorem sampledK_more (config : Model.Pcs.WhirConfigRust) (basis : List E → Option E)
    (residual : List E) (Wl : Model.Pcs.WhirLocals) {ml i : ℕ} (hi : i + 1 < ml) (q tf : List E)
    (c : E) : sampledK config basis residual Wl ml i q tf c =
      Model.TM.sumcheckRoundPoly 3 (Model.polyEvalRust q c) none >>= fun q' ↦
        roundsK config basis residual Wl ml (i + 1) (q', tf ++ [c], Model.polyEvalRust q c) := by
  unfold sampledK
  simp only [hi, ↓reduceIte, bind_assoc, pure_bind]

theorem sampledK_last (config : Model.Pcs.WhirConfigRust) (basis : List E → Option E)
    (residual : List E) (Wl : Model.Pcs.WhirLocals) {ml i : ℕ} (hi : i + 1 = ml) (q tf : List E)
    (c : E) : sampledK config basis residual Wl ml i q tf c =
      afterTail config basis residual Wl (tf ++ [c]) (Model.polyEvalRust q c) := by
  unfold sampledK roundsK
  have hn : ¬ i + 1 < ml := by omega
  rw [show ml - (i + 1) = 0 by omega]
  simp only [hn, ↓reduceIte, Model.Pcs.TM.forRange, pure_bind]

end Rv64Verifier.Proofs.Pcs.Vso
