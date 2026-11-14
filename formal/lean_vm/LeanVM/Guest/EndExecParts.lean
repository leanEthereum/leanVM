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

`TermRef`: the termination facts as values of the reference memory, the form the frame-to-instance
map gives; `term_of_ref`: they hold of a state whose termination facts' cells are written, and
`term_of_ref_entry`: of a function's entry whose entry cells are written, its termination facts
read off them (`termFr`).
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

/-- **The termination facts on the reference**: at each function's entry on the reference run, each
termination fact holds of the reference memory at the frame. -/
def TermRef (Ks : List Mode.Cert) (X : Ref → St → Prop) : Prop :=
  ∀ r, r.Ok → ∀ K ∈ Ks, ∀ s, OnRun X r s → s.pc = K.F.entry → ∀ p ∈ K.F.sig.term,
    RIn (refMem r.img) s.fp (.lt p.1 p.2) → RRes (refMem r.img) s.fp (.lt p.1 p.2)

/-- **A termination fact from the reference**, its cells written. -/
theorem term_of_ref {Ks : List Mode.Cert} {X : Ref → St → Prop} (h : TermRef Ks X) {r : Ref} (hr : r.Ok)
    {K : Mode.Cert} (hK : K ∈ Ks) {s : St} (hon : OnRun X r s) (hpc : s.pc = K.F.entry)
    {p : Mode.Idx × Mode.Idx} (hp : p ∈ K.F.sig.term) (hin : ResIn s (.lt p.1 p.2)) : LTF s p.1 p.2 :=
  resHolds_of_ref hon.2.1.agree hin (h r hr K hK s hon hpc p hp (rin_of hon.2.1.agree hin))

/-- An exponent read off the entry cells `es`: a constant, or an entry cell's. -/
def idxFr (es : List ℕ) : Mode.Idx → Bool
  | .num _ => true
  | .ex (.fr o) _ => decide (o ∈ es)
  | .ex (.hp _ _) _ => false

/-- Each termination fact read off the signature's entry cells. -/
def termFr (G : Sig) : Bool := G.term.all fun p ↦ idxFr G.entry p.1 && idxFr G.entry p.2

theorem idxIn_fr {es : List ℕ} {s : St} (hw : ∀ o ∈ es, s.mem.written (s.fp + o) = true) :
    ∀ {i : Mode.Idx}, idxFr es i = true → IdxIn s i
  | .num _, _ => trivial
  | .ex (.fr o) _, h => Mem.get_of_written (hw o (of_decide_eq_true h))
  | .ex (.hp _ _) _, h => absurd h (by simp [idxFr])

/-- **The termination facts at an entry from the reference**, read off its written entry cells. -/
theorem term_of_ref_entry {Ks : List Mode.Cert} {X : Ref → St → Prop} (h : TermRef Ks X) {r : Ref}
    (hr : r.Ok) {K : Mode.Cert} (hK : K ∈ Ks) (hfr : termFr K.F.sig = true) {s : St} (hon : OnRun X r s)
    (hpc : s.pc = K.F.entry) (hw : ∀ o ∈ K.F.sig.entry, s.mem.written (s.fp + o) = true) :
    ∀ p ∈ K.F.sig.term, LTF s p.1 p.2 := fun p hp ↦ by
  have := List.all_eq_true.mp hfr p hp
  rw [Bool.and_eq_true] at this
  exact term_of_ref h hr hK hon hpc hp ⟨idxIn_fr hw this.1, idxIn_fr hw this.2⟩

/-- **`ExecGaps` from its parts**: the prologue and `RefOk` discharged, the pointers each instruction
follows powers below `2^62` on the reference. -/
theorem ExecGaps.ofParts {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {X : Ref → St → Prop}
    (certs : ModeCerts Ks Km E0) (main : MainOk Km E0) (mainExact : Budget.MainExactHyp)
    (hintAlloc : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun X r s →
      h ∈ (C.hints[s.pc]?).getD [] → isAllocHint h = true → HintIn s h → HintOk C (refMem r.img) s h)
    (hintWitness : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun X r s →
      h ∈ (C.hints[s.pc]?).getD [] → isWitnessHint h = true → HintIn s h → HintOk C (refMem r.img) s h)
    (hintComputed : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun X r s →
      h ∈ (C.hints[s.pc]?).getD [] → isAllocHint h = false → isWitnessHint h = false → HintIn s h →
      HintOk C (refMem r.img) s h)
    (res : ∀ r, r.Ok → ResRef guestProgram r.img r.n Ks (X r))
    (term : ∀ r, r.Ok → ∀ K ∈ Ks, ∀ s, OnRun X r s → s.pc = K.F.entry → ∀ p ∈ K.F.sig.term,
      LTF s p.1 p.2)
    (ptr : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op, OnRun X r s →
      C.ops[s.pc]? = some op → PtrPow (refMem r.img) s op)
    (keepHint : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h s', OnRun X r s →
      h ∈ (C.hints[s.pc]?).getD [] → runHint C s h = .ok s' → X r s')
    (keepOp : ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op s', OnRun X r s →
      C.ops[s.pc]? = some op → runOp C s op = .ok s' → X r { s' with steps := s'.steps + 1 })
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
  term := term
  ref r hr C hC s op hon hop :=
    refOk_of_pow (logMemorySize_le_28 (e := r.exec) hr.size) hC hon.2.1 hon.2.2 hop
      (ptr r hr C hC s op hon hop)
  keepHint := keepHint
  keepOp := keepOp
  pro _ _ _ hC _ _ hon hP hop :=
    pro_step main certs.pows (certs.env Km certs.main).2.2.1 (certs.env Km certs.main).2.2.2.1
      certs.mainTerm hC rfl hP hon.2.1 hop
  init r hr C m hC hm := ⟨initX r hr C m hC hm, pro_init hm⟩
  used := used

end

end LeanVM.Guest.EndExec
