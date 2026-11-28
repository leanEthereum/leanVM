module

public import LeanVM.Guest.EndExecH

/-!
# The residuals and termination facts at the tree track's frames

On the references of the honest tree (`RefH`), past the prologue each state of the run has the tree
track at its pc and frame (`trackAt`), its top frame an honest instance. So `ExecGaps`' `res` and
`term`, statements about the executor's states, come from statements about the honest tree:

* `ResTrack L D A R Ks`: each residual of a certificate at an offset holds of the reference at the
  top frame of a state of the tree track there (`res_of_track`);
* `TermNodeA L D A R Ks`: each termination fact of a certificate holds of the reference at every
  honest `node` instance of the function the alignment enters at its entry (`term_of_nodeA`).

A certificate's entry is never `__jump_tables`'s (`0`), so its offsets are past the prologue.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core
open LeanVM.Guest.Bridge (FnAl ProgAl entOf alOf EntOk AtPc)
open LeanVM.Prover.Exec

@[expose] public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop}

/-- **The residuals at the tree track's frames**: on each reference, at a state of the track at an
offset of a certificate's code, each residual there whose bases have words holds of the reference at
the top frame. -/
def ResTrack (L : Lay) (D : Ref → RefD) (A : String → FnAl) (R : Ref → Prop) (Ks : List Cert) : Prop :=
  ∀ r, R r → r.Ok → ∀ K ∈ Ks, ∀ i < K.code.length, ∀ fp done e st,
    RefTrack L D A r (K.F.entry + i) fp (done, e :: st) →
    ∀ x ∈ (K.F.res.get i).getD [], RIn (refMem r.img) fp x → RRes (refMem r.img) fp x

/-- **The termination facts at the entered honest instances**: on each reference, at each honest
`node` instance whose function the alignment enters at a certificate's entry, each of its
termination facts whose bases have words holds of the reference at the instance's frame. -/
def TermNodeA (L : Lay) (D : Ref → RefD) (A : String → FnAl) (R : Ref → Prop) (Ks : List Cert) : Prop :=
  ∀ r, R r → r.Ok → ∀ K ∈ Ks, ∀ I ∈ instsOf L (D r) r, (∃ f σ bufs kids, I.t = .node f σ bufs kids) →
    entOf A I.t.name = K.F.entry → ∀ p ∈ K.F.sig.term,
      RIn (refMem r.img) I.fp (.lt p.1 p.2) → RRes (refMem r.img) I.fp (.lt p.1 p.2)

/-- A certificate's offset past the prologue is a state past it: a state at an offset of a
certificate whose entry is not `0` has run the prologue. -/
theorem past_pro {Ks : List Cert} {Km : Cert} {E0 : Env} (certs : ModeCerts Ks Km E0)
    (hKs : ∀ K ∈ Ks, K.F.entry ≠ 0) {r : Ref} (hR : RefH L (D r) r) {Y : Ref → St → Prop} {s : St}
    (hon : OnRun (XOf Y) r s) {K : Cert} (hK : K ∈ Ks) {i : ℕ} (hi : i < K.code.length)
    (hpc : s.pc = K.F.entry + i) : proLen ≤ s.steps ∧ s.pc < 2 ^ guestProgram.logSize := by
  obtain ⟨f, hf, hcode, hentry, -⟩ := certs.fn K hK
  have hif : i < f.instructionCount := by
    rw [← CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hf), ← hcode]; exact hi
  have hpcf := guest_pc_lt hf hif
  refine ⟨?_, by rw [hpc, hentry]; omega⟩
  by_contra hlt
  have hpc62 : s.pc < 2 ^ 62 := by rw [hpc, hentry]; rw [guest_logSize] at hpcf; omega
  have h0 := ((posAt hR hon.1.1 hpc62 hon.2.1.fp).1 (by omega)).1
  have := consecutive_entry functions_consecutive _ f0_mem f hf (by rw [f0_entry']; omega)
    (by rw [f0_entry']; show f.entryPc < 0 + proLen; omega)
  rw [f0_entry'] at this
  exact hKs K hK (hentry.trans this)

/-- **`ExecGaps.res` from the tree track's frames.** -/
theorem res_of_track {Ks Ks0 : List Cert} {Km : Cert} {E0 : Env} {Y : Ref → St → Prop}
    (certs : ModeCerts Ks0 Km E0) (hsub : ∀ K ∈ Ks, K ∈ Ks0) (hKs : ∀ K ∈ Ks0, K.F.entry ≠ 0)
    (hH : HintHyps L D A) (hRH : ∀ r, R r → RefH L (D r) r) (h : ResTrack L D A R Ks) :
    ∀ r, R r → r.Ok → ResRef guestProgram r.img r.n Ks (fun s ↦ XOf Y r s) := by
  intro r hR0 hr K hK s i hX hs hon hi hpc x hx hin
  have hR := hRH r hR0
  have hon' : OnRun (XOf Y) r s := ⟨hX, hs, hon⟩
  obtain ⟨hge, hlt⟩ := past_pro certs hKs hR hon' (hsub K hK) hi hpc
  obtain ⟨done, e, st, htr⟩ :=
    trackAt hH.progAl hH.mainAt hH.jumpCells hH.layout hR hr hX.1 hs hon hge hlt
  rw [hpc] at htr
  exact h r hR0 hr K hK i hi s.fp done e st htr x hx hin

/-- **`ExecGaps.term` from the entered honest instances.** -/
theorem term_of_nodeA {Ks Ks0 : List Cert} {Km : Cert} {E0 : Env} {Y : Ref → St → Prop}
    (certs : ModeCerts Ks0 Km E0) (hsub : ∀ K ∈ Ks, K ∈ Ks0) (hKs : ∀ K ∈ Ks0, K.F.entry ≠ 0)
    (hH : HintHyps L D A) (hRH : ∀ r, R r → RefH L (D r) r) (h : TermNodeA L D A R Ks) :
    TermRef R Ks (XOf Y) := by
  intro r hR0 hr K hK s hon hpc p hp hin
  have hR := hRH r hR0
  obtain ⟨f, hf, hcode, hentry, -⟩ := certs.fn K (hsub K hK)
  have hne : 0 < K.code.length := certs.ne K (hsub K hK)
  obtain ⟨hge, hlt⟩ := past_pro certs hKs hR hon (hsub K hK) hne (by rw [hpc, Nat.add_zero])
  obtain ⟨done, e, st, htr⟩ :=
    trackAt hH.progAl hH.mainAt hH.jumpCells hH.layout hR hr hon.1.1 hon.2.1 hon.2.2 hge hlt
  obtain ⟨e', st', hst, hE, hfp, hat⟩ := htr.top
  obtain ⟨g', bufs, kids, hn⟩ := hE.node
  have hent : entOf A e'.I.t.name = K.F.entry := by
    rw [← hpc]
    exact (entry_of_atPc hH.progAl hH.layout hE hat).2 f hf (by rw [hpc, hentry])
  rw [← hfp] at hin ⊢
  exact h r hR0 hr K hK e'.I hE.mem ⟨g', e'.σ, bufs, kids, hn⟩ hent p hp hin

end

end LeanVM.Guest.EndExec
