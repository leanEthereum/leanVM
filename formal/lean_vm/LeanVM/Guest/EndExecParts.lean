/-
  LeanVM.Guest.EndExecParts

  `ExecGaps` with the prologue (`pro`, `init`'s prologue part) and `RefOk` (`ref`) discharged: the
  fields left are the other tracks'.
-/

module

public import LeanVM.Guest.EndExecPro
public import LeanVM.Guest.EndExecRefOk
public import LeanVM.Guest.Pack.P8.ModeSig

/-!
# `ExecGaps` from its parts

`ExecGaps.ofParts`: `ExecGaps Ks Km E0 X (fun _ ↦ ProAt)` from the fields the prologue and the
reference step do not give, `pro` and the prologue's part of `init` from `pro_step` and `pro_init`
(given `MainOk`, which `mainOk_of` reads off `main`'s signature), and `ref` from `refOk_of_pow`,
given that the pointers each instruction follows are powers below `2^62` on the reference (`PtrPow`,
what the honest memory's pointer cells hold).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Prover.Exec

@[expose] public section

/-- `main`'s signature: entered at its header alone. -/
theorem mainSig_ok : Fn.«main».modeSig.entry = [0, 1] ∧ Fn.«main».modeSig.self = none ∧
    Fn.«main».modeSig.pre = [] ∧ Fn.«main».modeSig.preR = [] ∧ Fn.«main».modeSig.preP = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`MainOk` from `main`'s signature**, entry and the guest's table. -/
theorem mainOk_of {Km : Mode.Cert} {E0 : Mode.Env} (hsig : Km.F.sig = Fn.«main».modeSig)
    (hent : Km.F.entry = 13937) (hpows : E0.pows = Data.powTree) (hjt : E0.jt = Data.jtTrie)
    (hlo : E0.jtLo = 430) (hhi : E0.jtHi = 14367) : MainOk Km E0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mainSig_ok
  have hmc := mainCells_eq
  have hpl := proLen_eq
  exact ⟨by omega, hpows, hjt, by omega, by omega,
    fun o ho ↦ by rw [hsig, h1] at ho; simp at ho; omega, hsig ▸ h2, hsig ▸ h3, hsig ▸ h4, hsig ▸ h5⟩

/-- **The termination facts of the honest instances**: each instance of the node's honest tree of
`K`'s function has `K`'s termination facts in the reference memory at its frame. -/
def TermInst (Ks : List Mode.Cert) : Prop :=
  ∀ r : Ref, r.Ok → ∀ K ∈ Ks, ∀ I ∈ Memory.honestInsts coreProgram B2C.fs B2C.H r.hdr r.T,
    B2C.entryOf I.t.name = K.F.entry → ∀ p ∈ K.F.sig.term,
      RIn (refMem r.img) I.fp (.lt p.1 p.2) → RRes (refMem r.img) I.fp (.lt p.1 p.2)

/-- **The frame-to-instance map at entries**: at a function's entry on the reference run, the frame
is an honest instance's of that function. -/
def EntryInst (Ks : List Mode.Cert) (X : Ref → St → Prop) : Prop :=
  ∀ r, r.Ok → ∀ K ∈ Ks, ∀ s, OnRun X r s → s.pc = K.F.entry →
    ∃ I ∈ Memory.honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, B2C.entryOf I.t.name = K.F.entry ∧
      I.fp = s.fp

/-- **`TermRef` from the instances**, through the frame-to-instance map. -/
theorem termRef_of {Ks : List Mode.Cert} {X : Ref → St → Prop} (hT : TermInst Ks) (hE : EntryInst Ks X) :
    TermRef Ks X := fun r hr K hK s hon hpc p hp hin ↦ by
  obtain ⟨I, hI, hn, hfp⟩ := hE r hr K hK s hon hpc
  rw [← hfp] at hin ⊢
  exact hT r hr K hK I hI hn p hp hin

/-- **`ExecGaps` from its parts**: the prologue and `RefOk` discharged, the pointers each instruction
follows powers below `2^62` on the reference. -/
theorem ExecGaps.ofParts {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {X : Ref → St → Prop}
    (certs : ModeCerts Ks Km E0) (main : MainOk Km E0) (mainExact : Budget.MainExactHyp)
    (hintAlloc : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun X r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isAllocHint h = true → HintIn s1 h → HintOk C (refMem r.img) s1 h)
    (hintWitness : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun X r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isWitnessHint h = true → HintIn s1 h → HintOk C (refMem r.img) s1 h)
    (hintComputed : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun X r s →
      h ∈ (C.hints[s.pc]?).getD [] → isAllocHint h = false → isWitnessHint h = false → ∀ s1,
      Moves (refMem r.img) s s1 → HintIn s1 h → HintOk C (refMem r.img) s1 h)
    (res : ∀ r, r.Ok → ResRef guestProgram r.img r.n Ks (X r))
    (termInst : TermInst Ks) (entryInst : EntryInst Ks X)
    (ptr : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op, OnRun X r s →
      C.ops[s.pc]? = some op → PtrPow (refMem r.img) s op)
    (keepOp : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op s1 s', OnRun X r s →
      C.ops[s.pc]? = some op → ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → runOp C s1 op = .ok s' → X r { s' with steps := s'.steps + 1 })
    (initX : ∀ r, r.Ok → ∀ C m, Ctx.of guestProgram r.adv = .ok C → initMem r.adv r.input = .ok m →
      X r (initSt C r.adv m))
    (used : ∀ r, r.Ok → ∀ s, X r s → s.mem.used ≤ 2 ^ r.κ) :
    ExecGaps Ks Km E0 X (fun _ ↦ ProAt) where
  certs := certs
  mainExact := mainExact
  hintAlloc := hintAlloc
  hintWitness := hintWitness
  hintComputed := hintComputed
  res := res
  term := termRef_of termInst entryInst
  ref r hr C hC s op hon hop :=
    refOk_of_pow (logMemorySize_le_28 (e := r.exec) hr.size) hC hon.2.1 hon.2.2 hop
      (ptr r hr C hC s op hon hop)
  keepOp := keepOp
  pro _ _ _ hC _ _ hon hP hop :=
    pro_step main certs.pows (certs.env Km certs.main).2.2.1 (certs.env Km certs.main).2.2.2.1
      certs.mainTerm hC rfl hP hon.2.1 hop
  init r hr C m hC hm := ⟨initX r hr C m hC hm, pro_init hm⟩
  used := used

end

end LeanVM.Guest.EndExec
