module

public import LeanVM.Guest.Mode.InvRule
public import LeanVM.Guest.Mode.InvCode
public import LeanVM.Guest.Mode.HintsCtx
public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.CoreMode.CoreSound
public import LeanVM.Guest.CoreMode.Contracts

/-!
# A guest function's certificate, tied to the executor

`FnSpec`: a guest function's frame interface on the executor's
tables for the guest's advice, the core route's (`FnSpecC`, from its kernel checks by `fnSpecC_of`),
for its frame predicate `guestQ` (`frameSpec_guest`).
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Each function's frame interface -/

/-- **A function on the core route meets its frame interface**, its core data `Cf`: on the
executor's tables for any advice with the guest's hints, its code the executor's, on a reference
image within `2^28` words, at states on its run where its frames have honest valuations
(`CoreHon`), `CoreAt` meets `FrameSpec`. -/
def FnSpecC (K : Cert) (Cf : CoreMode.CFun) : Prop :=
  ∀ adv C, Ctx.of guestProgram adv = .ok C → adv.hints = Data.adviceHints → CodeOk C K →
    ∀ {κ : ℕ} (img : MemoryImage κ) (Y : St → Prop) (Ct : Cts), κ ≤ 28 →
      (∀ s, Y s → ∃ n, OnRef guestProgram img n s) → CoreMode.CoreHon img Y K Cf → CoreMode.UsedNext C img Y →
        CoreMode.CtOk img Ct K Cf → FrameSpec C (refMem img) Y Ct K (CoreMode.CoreAt img Cf K.code)

/-- **A guest function's frame interface**, at the heap contracts' table `tab`: the core route's, with core data
among `T` at its entry agreeing with the table (`ctB`). -/
def FnSpec (tab : List CoreMode.HcEnt) (T : List CoreMode.CFun) (K : Cert) : Prop :=
  ∃ Cf ∈ T, Cf.frame.entry = K.F.entry ∧ FnSpecC K Cf ∧ CoreMode.ctB tab K Cf = true

/-- **A guest function's frame predicate** at the reference image `img`, the core data `T`, the table `tab`: the
core route's (`CoreAt`, at core data among `T` at its entry meeting its interface and agreeing with the table). -/
def guestQ (tab : List CoreMode.HcEnt) (T : List CoreMode.CFun) {κ : ℕ} (img : MemoryImage κ)
    (K : Cert) : ℕ → St → Prop :=
  fun i s ↦ ∃ Cf ∈ T, Cf.frame.entry = K.F.entry ∧ FnSpecC K Cf ∧ CoreMode.ctB tab K Cf = true ∧
    CoreMode.CoreAt img Cf K.code i s

theorem Resume.imp {Ct : Cts} {Q Q' : ℕ → St → Prop} (h : ∀ i s, Q i s → Q' i s) {fpC ro t : ℕ} {G : Sig}
    {fpE : ℕ} {m0 : Mem} (hr : Resume Ct Q fpC ro t G fpE m0) : Resume Ct Q' fpC ro t G fpE m0 :=
  fun m h1 h2 h3 h4 h5 h6 h7 ↦ h _ _ (hr m h1 h2 h3 h4 h5 h6 h7)

theorem Out.imp {Ct : Cts} {K : Cert} {Q Q' : ℕ → St → Prop} (h : ∀ i s, Q i s → Q' i s) {i : ℕ} {s1 s' : St}
    (ho : Out Ct K Q i s1 s') : Out Ct K Q' i s1 s' := by
  cases ho with
  | move j h1 h2 h3 h4 => exact .move j h1 h2 h3 (h _ _ h4)
  | ret c h1 h2 h3 h4 h5 => exact .ret c h1 h2 h3 h4 h5
  | halt h1 h2 h3 => exact .halt h1 h2 h3
  | tail h1 h2 => exact .tail h1 h2
  | call h1 =>
    exact .call fun hT ↦ by
      obtain ⟨G, ro, a1, a2, a3, a4, a5, a6, a7⟩ := h1 hT
      exact ⟨G, ro, a1, a2, a3, a4, a5, a6, a7.imp h⟩

/-- **A guest function's frame predicate meets its interface**, at the table's contracts, on a reference image
within `2^28` words, at states on its run where the frames of a core function have honest valuations. -/
theorem frameSpec_guest {tab : List CoreMode.HcEnt} {T : List CoreMode.CFun} {K : Cert} (h : FnSpec tab T K)
    {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints)
    (hK : CodeOk C K) {κ : ℕ} (img : MemoryImage κ) (Y : St → Prop) (hκ : κ ≤ 28)
    (hY : ∀ s, Y s → ∃ n, OnRef guestProgram img n s)
    (hH : ∀ Cf ∈ T, Cf.frame.entry = K.F.entry → CoreMode.CoreHon img Y K Cf) (hU : CoreMode.UsedNext C img Y) :
    FrameSpec C (refMem img) Y (CoreMode.ctOf img tab) K (guestQ tab T img K) := by
  have hS : ∀ Cf ∈ T, Cf.frame.entry = K.F.entry → FnSpecC K Cf → CoreMode.ctB tab K Cf = true →
      FrameSpec C (refMem img) Y (CoreMode.ctOf img tab) K (CoreMode.CoreAt img Cf K.code) :=
    fun Cf hCf he hs hb ↦ hs adv C hC ha hK img Y _ hκ hY (hH Cf hCf he) hU (CoreMode.ctOk_of_ctB hb)
  obtain ⟨Cf0, hCf0, he0, hs0, hb0⟩ := h
  refine ⟨fun hle hfp ⟨Cf, hCf, he, hs, hb, hq⟩ ↦ ⟨Cf, hCf, he, hs, hb, (hS Cf hCf he hs hb).mono hle hfp hq⟩,
    fun hA hf ↦ ⟨Cf0, hCf0, he0, hs0, hb0, (hS Cf0 hCf0 he0 hs0 hb0).entry hA hf⟩, ?_⟩
  intro s i hi hpc ⟨Cf, hCf, he, hs, hb, hq⟩ hf hy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 Inv k
  exact (hS Cf hCf he hs hb).step hi hpc hq hf hy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    fun s1 s' e1 hm hmo e hf' hle hout ↦ k s1 s' e1 hm hmo e hf' hle
      (hout.imp fun j s hq' ↦ ⟨Cf, hCf, he, hs, hb, hq'⟩)

/-- An instruction's operands below `2^28` are small. -/
theorem smallOps_of {code : List OffsetInstruction} (h : code.all offSmall = true) :
    ∀ i (hi : i < code.length), CoreMode.SmallOps code[i] := by
  intro i hi
  have hs := List.all_eq_true.mp h _ (List.getElem_mem hi)
  generalize code[i] = ins at hs ⊢
  cases ins <;> simp_all [offSmall, CoreMode.SmallOps]

/-- **The advice's hints at a function's pcs** are its entry's, `d` the `j`-th of the advice's
functions, at the function's entry and covering its code. -/
theorem hintsEq_of_fn {K : Cert} {Fh : List (ℕ × List Hint)} {j : ℕ} {d : ℕ × ℕ × List (ℕ × List Hint)}
    (hj : Data.adviceFns[j]? = some d) (he : d.1 = K.F.entry) (hn : K.code.length ≤ d.2.1) (hF : Fh = d.2.2) :
    ∀ i < K.code.length, hintsAt Data.adviceHints (K.F.entry + i) = hintsAt Fh (K.F.entry + i) := by
  intro i hi
  rw [adviceHints_eq, hintsAt_fns adviceFns_ok (List.mem_of_getElem? hj) (by omega) (by omega), hF]

/-- **A function on the core route meets its frame interface**, from the kernel's checks. -/
theorem fnSpecC_of {K : Cert} {Cf : CoreMode.CFun} (hok : CoreMode.CoreOk K Cf) : FnSpecC K Cf :=
  fun _ _ hC ha hK _ _ _ _ hκ hY hH hU hCt ↦ CoreMode.frameSpec_core hok hC ha hK hκ hY hH hU hCt

end

end LeanVM.Guest.Mode
