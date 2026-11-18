module

public import LeanVM.Guest.Mode.InvWalk
public import LeanVM.Guest.Mode.HintsCtx
public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.CoreMode.CoreSound

/-!
# A guest function's certificate, tied to the executor

`certOk_fn`: a guest function's mode walk (`walk`), its length, its operands below `2^28`
(`offSmall`) and its hints the advice's (`HintsOk`) make its certificate one `ProgOk` takes
(`CertOk`): the executor's instruction at each of its pcs is its code's (`ctx_op_off`, from the fetch
lemma and the decoder's `OpOf`), and its hints the advice's (`ctx_hintsOk`); `codeOk_fn`, its code
alone the executor's (`CodeOk`). `FnSpec`: a guest function's frame interface on the executor's
tables for the guest's advice, for its frame predicate `guestQ` (the walk's, `coreRoute` being
empty); `fnSpec_of_walk`, from its walk. `guest_inv_rule`, `guest_inv_init`: `inv_rule` and
`inv_init` on the guest program.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-- An instruction's operands, a `KECCAK`'s thirteen cells among them, are below `2^28`. -/
def offSmall : OffsetInstruction → Bool
  | .xor a b c => decide (a < 2 ^ 28) && decide (b < 2 ^ 28) && decide (c < 2 ^ 28)
  | .mul a b c => decide (a < 2 ^ 28) && decide (b < 2 ^ 28) && decide (c < 2 ^ 28)
  | .set o _ _ => decide (o < 2 ^ 28)
  | .deref a b c _ => decide (a < 2 ^ 28) && decide (b < 2 ^ 28) && decide (c < 2 ^ 28)
  | .jump a b c => decide (a < 2 ^ 28) && decide (b < 2 ^ 28) && decide (c < 2 ^ 28)
  | .keccak m0 m1 m2 m3 tail b8 cap out _ _ _ =>
    (keccakIns m0 m1 m2 m3 tail b8 cap).all (fun x ↦ decide (x < 2 ^ 28)) && decide (out < 2 ^ 28)

theorem gpow_eq {a b : ℕ} (ha : a < 2 ^ 28) (hb : b < 2 ^ 28) (h : g ^ a = g ^ b) : a = b :=
  gpow_inj (by omega) (by omega) h

/-- **The decoder's instruction is the code's**, its operands small. -/
theorem opOf_eq {ins : OffsetInstruction} {op : Op} (hs : offSmall ins = true)
    (hop : OpOf ins.toLeanIsaInstruction op) (hsm : OpSmall op) : op = opOfOff ins := by
  cases ins with
  | xor a b c =>
    cases op <;> simp only [OffsetInstruction.toLeanIsaInstruction, OpOf] at hop
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨h1, h2, h3⟩ := hop
    obtain ⟨s1, s2, s3⟩ := hsm
    rw [gpow_eq s1 hs.1.1 h1, gpow_eq s2 hs.1.2 h2, gpow_eq s3 hs.2 h3]
    rfl
  | mul a b c =>
    cases op <;> simp only [OffsetInstruction.toLeanIsaInstruction, OpOf] at hop
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨h1, h2, h3⟩ := hop
    obtain ⟨s1, s2, s3⟩ := hsm
    rw [gpow_eq s1 hs.1.1 h1, gpow_eq s2 hs.1.2 h2, gpow_eq s3 hs.2 h3]
    rfl
  | set o k0 k1 =>
    cases op <;> simp only [OffsetInstruction.toLeanIsaInstruction, OpOf] at hop
    simp only [offSmall, decide_eq_true_eq] at hs
    obtain ⟨h1, rfl⟩ := hop
    rw [gpow_eq hsm hs h1]
    rfl
  | deref a b c mode =>
    cases op <;> simp only [OffsetInstruction.toLeanIsaInstruction, OpOf] at hop
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨h1, h2, h3, rfl⟩ := hop
    obtain ⟨s1, s2, s3⟩ := hsm
    rw [gpow_eq s1 hs.1.1 h1, gpow_eq s2 hs.1.2 h2, gpow_eq s3 hs.2 h3]
    rfl
  | jump a b c =>
    cases op <;> simp only [OffsetInstruction.toLeanIsaInstruction, OpOf] at hop
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨h1, h2, h3⟩ := hop
    obtain ⟨s1, s2, s3⟩ := hsm
    rw [gpow_eq s1 hs.1.1 h1, gpow_eq s2 hs.1.2 h2, gpow_eq s3 hs.2 h3]
    rfl
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    cases op <;> simp only [OffsetInstruction.toLeanIsaInstruction, OpOf] at hop
    simp only [offSmall, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
    obtain ⟨rfl, rfl, rfl, h1, l, rfl, hl⟩ := hop
    obtain ⟨s1, s2⟩ := hsm
    have hl' : l = keccakIns m0 m1 m2 m3 tail b8 cap := by
      have hlen : l.length = 13 := by rw [← hl.length_eq, List.length_finRange]
      refine List.ext_getElem (by rw [hlen]; simp [keccakIns]) fun c h1 h2 ↦ ?_
      have hc : c < 13 := by omega
      have hR := hl.get (show c < (List.finRange 13).length by simp; omega) h1
      simp only [List.get_eq_getElem, List.getElem_finRange] at hR
      have hk := keccakInOffset_gpow m0 m1 m2 m3 tail b8 cap ⟨c, hc⟩
      have he : (keccakIns m0 m1 m2 m3 tail b8 cap)[c]'h2 = keccakInOff m0 m1 m2 m3 tail b8 cap c := by
        simp [keccakIns]
      have hm := hs.1 _ (List.getElem_mem h2)
      rw [he] at hm ⊢
      refine gpow_eq (s1 _ (by simp)) hm ?_
      simp only [Fin.cast_mk] at hR
      rw [hR]
      exact hk
    rw [gpow_eq s2 hs.2 h1, hl']
    rfl

/-- **The executor's instruction at a pc** is the code's there, its operands small. -/
theorem ctx_op_off {prog : LeanIsaProgram} {adv : Advice} {C : Ctx} (hC : Ctx.of prog adv = .ok C)
    {pc : ℕ} (hpc : pc < 2 ^ prog.logSize) {ins : OffsetInstruction}
    (hins : prog.instructions ⟨pc, hpc⟩ = ins.toLeanIsaInstruction) (hs : offSmall ins = true) :
    C.ops[pc]? = some (opOfOff ins) := by
  obtain ⟨hsize, hdec⟩ := ctx_of_spec hC
  have hpc' : pc < C.ops.size := hsize ▸ hpc
  rw [Array.getElem?_eq_getElem hpc']
  have h := hdec pc hpc hpc'
  rw [hins] at h
  rw [opOf_eq hs h (ctx_small hC pc hpc')]

/-- **A certificate's code is the executor's**: its instructions the program's at its pcs, small. -/
theorem codeOk_of {prog : LeanIsaProgram} {adv : Advice} {C : Ctx} (hC : Ctx.of prog adv = .ok C)
    {K : Cert} (hins : ∀ i (hi : i < K.code.length), ∃ hpc : K.F.entry + i < 2 ^ prog.logSize,
      prog.instructions ⟨_, hpc⟩ = K.code[i].toLeanIsaInstruction)
    (hs : K.code.all offSmall = true) : CodeOk C K :=
  ⟨fun i hi ↦ by
    obtain ⟨hpc, he⟩ := hins i hi
    exact ctx_op_off hC hpc he (List.all_eq_true.mp hs _ (List.getElem_mem _))⟩

/-- **A certificate tied to the executor**: its walk, its length, its instructions the program's at
its pcs, small, and its hints the advice's. -/
theorem certOk_of {prog : LeanIsaProgram} {adv : Advice} {C : Ctx} (hC : Ctx.of prog adv = .ok C)
    (ha : adv.hints = Data.adviceHints) {K : Cert} (hw : walk K.E K.F K.code = true)
    (hlen : K.F.len = K.code.length)
    (hins : ∀ i (hi : i < K.code.length), ∃ hpc : K.F.entry + i < 2 ^ prog.logSize,
      prog.instructions ⟨_, hpc⟩ = K.code[i].toLeanIsaInstruction)
    (hs : K.code.all offSmall = true) (hh : HintsOk K.F Data.adviceHints) : CertOk C K :=
  ⟨hw, hlen, fun i hi ↦ by
    obtain ⟨hpc, he⟩ := hins i hi
    exact ctx_op_off hC hpc he (List.all_eq_true.mp hs _ (List.getElem_mem _)),
   fun i hi ↦ by
    obtain ⟨hpc, -⟩ := hins i hi
    exact (ctx_hintsOk hC ha hh (hlen ▸ hi) hpc).symm⟩

/-- A guest function's instructions are the program's at its pcs. -/
theorem fn_ins {f : CompiledFunction} (hf : f ∈ Data.functions) {K : Cert} (hcode : K.code = f.code)
    (hentry : K.F.entry = f.entryPc) : ∀ i (hi : i < K.code.length),
      ∃ hpc : K.F.entry + i < 2 ^ guestProgram.logSize,
        guestProgram.instructions ⟨_, hpc⟩ = K.code[i].toLeanIsaInstruction := by
  intro i hi
  have hwc := CompiledFunction.wellChunked_of_mem hf
  have hi' : i < f.instructionCount := by
    rw [← CompiledFunction.length_code hwc, ← hcode]; exact hi
  have hpc : K.F.entry + i < 2 ^ guestProgram.logSize := by
    have := guest_pc_lt hf hi'; omega
  refine ⟨hpc, ?_⟩
  have hfe := guest_fetch hf hi'
  rw [← hentry, show addressOfIndex (K.F.entry + i) =
    addressOfIndex ((⟨K.F.entry + i, hpc⟩ : Fin (2 ^ guestProgram.logSize)) : ℕ) from rfl,
    guestProgram.fetch_gpow, Option.some.injEq] at hfe
  rw [hfe]
  have hc := CompiledFunction.getElem?_code hwc hi'
  rw [← hcode, List.getElem?_eq_getElem hi, Option.some.injEq] at hc
  rw [hc]

/-- **A guest function's certificate** is tied to the executor run on the guest's advice: its walk,
its length, its operands small and its hints the advice's. -/
theorem certOk_fn {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C)
    (ha : adv.hints = Data.adviceHints) {f : CompiledFunction} (hf : f ∈ Data.functions) {K : Cert}
    (hcode : K.code = f.code) (hentry : K.F.entry = f.entryPc) (hw : walk K.E K.F K.code = true)
    (hlen : K.F.len = K.code.length) (hs : K.code.all offSmall = true)
    (hh : HintsOk K.F Data.adviceHints) : CertOk C K :=
  certOk_of hC ha hw hlen (fn_ins hf hcode hentry) hs hh

/-- **A guest function's code is the executor's**, run on any advice, its operands small. -/
theorem codeOk_fn {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C)
    {f : CompiledFunction} (hf : f ∈ Data.functions) {K : Cert} (hcode : K.code = f.code)
    (hentry : K.F.entry = f.entryPc) (hs : K.code.all offSmall = true) : CodeOk C K :=
  codeOk_of hC (fn_ins hf hcode hentry) hs

/-! ## Each function's frame interface -/

/-- **A function on the walk meets its frame interface**: on the executor's tables for any advice
with the guest's hints, its code the executor's, the walk's frame predicate `AtOff` meets
`FrameSpec` for any memory and states. -/
def FnSpecW (K : Cert) : Prop :=
  ∀ adv C, Ctx.of guestProgram adv = .ok C → adv.hints = Data.adviceHints → CodeOk C K →
    ∀ M Y, FrameSpec C M Y K (AtOff K.E K.F K.code)

/-- **A function on the core route meets its frame interface**, its core data `Cf`: on the
executor's tables for any advice with the guest's hints, its code the executor's, on a reference
image within `2^28` words, at states on its run where its frames have honest valuations
(`CoreHon`), `CoreAt` meets `FrameSpec`. -/
def FnSpecC (K : Cert) (Cf : CoreMode.CFun) : Prop :=
  ∀ adv C, Ctx.of guestProgram adv = .ok C → adv.hints = Data.adviceHints → CodeOk C K →
    ∀ {κ : ℕ} (img : MemoryImage κ) (Y : St → Prop), κ ≤ 28 → (∀ s, Y s → ∃ n, OnRef guestProgram img n s) →
      CoreMode.CoreHon img Y K Cf → FrameSpec C (refMem img) Y K (CoreMode.CoreAt img Cf K.code)

/-- **A guest function's frame interface**: the walk's, or the core route's with core data among
`T` at its entry. -/
def FnSpec (T : List CoreMode.CFun) (K : Cert) : Prop :=
  FnSpecW K ∨ ∃ Cf ∈ T, Cf.frame.entry = K.F.entry ∧ FnSpecC K Cf

open Classical in
/-- **A guest function's frame predicate** at the reference image `img`, the core data `T`: the core
route's (`CoreAt`, at core data among `T` at its entry meeting its interface), if any, else the
walk's (`AtOff`). -/
noncomputable def guestQ (T : List CoreMode.CFun) {κ : ℕ} (img : MemoryImage κ) (K : Cert) : ℕ → St → Prop :=
  if ∃ Cf ∈ T, Cf.frame.entry = K.F.entry ∧ FnSpecC K Cf then
    fun i s ↦ ∃ Cf ∈ T, Cf.frame.entry = K.F.entry ∧ FnSpecC K Cf ∧ CoreMode.CoreAt img Cf K.code i s
  else AtOff K.E K.F K.code

theorem Resume.imp {Q Q' : ℕ → St → Prop} (h : ∀ i s, Q i s → Q' i s) {fpC ro : ℕ} {G : Sig} {fpE : ℕ}
    {m0 : Mem} (hr : Resume Q fpC ro G fpE m0) : Resume Q' fpC ro G fpE m0 :=
  fun m h1 h2 h3 h4 h5 h6 h7 h8 h9 ↦ h _ _ (hr m h1 h2 h3 h4 h5 h6 h7 h8 h9)

theorem Out.imp {K : Cert} {Q Q' : ℕ → St → Prop} (h : ∀ i s, Q i s → Q' i s) {i : ℕ} {s1 s' : St}
    (ho : Out K Q i s1 s') : Out K Q' i s1 s' := by
  cases ho with
  | move j h1 h2 h3 h4 => exact .move j h1 h2 h3 (h _ _ h4)
  | ret c h1 h2 h3 h4 h5 => exact .ret c h1 h2 h3 h4 h5
  | halt h1 h2 h3 => exact .halt h1 h2 h3
  | tail h1 h2 => exact .tail h1 h2
  | call h1 =>
    exact .call fun hT ↦ by
      obtain ⟨G, ro, a1, a2, a3, a4, a5, a6, a7⟩ := h1 hT
      exact ⟨G, ro, a1, a2, a3, a4, a5, a6, a7.imp h⟩

/-- **A guest function's frame predicate meets its interface**, on a reference image within
`2^28` words, at states on its run where the frames of a core function have honest valuations. -/
theorem frameSpec_guest {T : List CoreMode.CFun} {K : Cert} (h : FnSpec T K) {adv : Advice} {C : Ctx}
    (hC : Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints) (hK : CodeOk C K)
    {κ : ℕ} (img : MemoryImage κ) (Y : St → Prop) (hκ : κ ≤ 28)
    (hY : ∀ s, Y s → ∃ n, OnRef guestProgram img n s)
    (hH : ∀ Cf ∈ T, Cf.frame.entry = K.F.entry → CoreMode.CoreHon img Y K Cf) :
    FrameSpec C (refMem img) Y K (guestQ T img K) := by
  by_cases hc : ∃ Cf ∈ T, Cf.frame.entry = K.F.entry ∧ FnSpecC K Cf
  · have hq : guestQ T img K = fun i s ↦ ∃ Cf ∈ T, Cf.frame.entry = K.F.entry ∧ FnSpecC K Cf ∧
        CoreMode.CoreAt img Cf K.code i s := by
      unfold guestQ; rw [ite_eq_left hc]
    rw [hq]
    have hS : ∀ Cf ∈ T, Cf.frame.entry = K.F.entry → FnSpecC K Cf →
        FrameSpec C (refMem img) Y K (CoreMode.CoreAt img Cf K.code) := fun Cf hCf he hs ↦
      hs adv C hC ha hK img Y hκ hY (hH Cf hCf he)
    obtain ⟨Cf0, hCf0, he0, hs0⟩ := hc
    refine ⟨fun hle hfp ⟨Cf, hCf, he, hs, hq⟩ ↦ ⟨Cf, hCf, he, hs, (hS Cf hCf he hs).mono hle hfp hq⟩,
      fun hA hf ↦ ⟨Cf0, hCf0, he0, hs0, (hS Cf0 hCf0 he0 hs0).entry hA hf⟩, ?_⟩
    intro s i hi hpc ⟨Cf, hCf, he, hs, hq⟩ hf hy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 Inv k
    exact (hS Cf hCf he hs).step hi hpc hq hf hy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      fun s1 s' e1 hm hmo e hf' hle hout ↦ k s1 s' e1 hm hmo e hf' hle
        (hout.imp fun j s hq' ↦ ⟨Cf, hCf, he, hs, hq'⟩)
  · have hq : guestQ T img K = AtOff K.E K.F K.code := by
      unfold guestQ; rw [ite_eq_right hc]
    rw [hq]
    rcases h with h | h
    · exact h adv C hC ha hK _ Y
    · exact absurd h hc

/-- **A function on the walk meets its frame interface**: its walk, its length, its hints the
advice's and its loop's runs over its termination facts. -/
theorem fnSpecW_of_walk {K : Cert} (hw : walk K.E K.F K.code = true) (hlen : K.F.len = K.code.length)
    (hh : HintsOk K.F Data.adviceHints)
    (hrng : ∀ r ∈ K.F.sig.postL ++ K.F.sig.postLP.map (·.1), (r.lo, r.hi) ∈ K.F.sig.term) : FnSpecW K := by
  intro adv C hC ha hK M Y
  obtain ⟨hsize, -⟩ := ctx_of_spec hC
  refine frameSpec_walk ⟨hw, hlen, hK.ops, fun i hi ↦ ?_⟩ hrng
  have hpc := code_pc hK hi
  rw [hsize] at hpc
  exact (ctx_hintsOk hC ha hh (hlen ▸ hi) hpc).symm

/-- A function on the walk, for any core data. -/
theorem fnSpec_of_walk {K : Cert} (hw : walk K.E K.F K.code = true) (hlen : K.F.len = K.code.length)
    (hh : HintsOk K.F Data.adviceHints)
    (hrng : ∀ r ∈ K.F.sig.postL ++ K.F.sig.postLP.map (·.1), (r.lo, r.hi) ∈ K.F.sig.term)
    (T : List CoreMode.CFun) : FnSpec T K :=
  .inl (fnSpecW_of_walk hw hlen hh hrng)

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
  fun _ _ hC ha hK _ _ _ hκ hY hH ↦ CoreMode.frameSpec_core hok hC ha hK hκ hY hH

/-! ## On the guest -/

/-- **The invariant rule on the guest program.** -/
theorem guest_inv_rule {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx} {Ks : List Cert}
    {Km : Cert} {E0 : Env} {X Pro : St → Prop} (hκ : κ ≤ 28) (hC : Ctx.of guestProgram adv = .ok C)
    (P : ProgOk guestProgram C Ks Km E0)
    (hW : ∀ K ∈ Ks, CertOk C K ∧ ∀ r ∈ K.F.sig.postL ++ K.F.sig.postLP.map (·.1), (r.lo, r.hi) ∈ K.F.sig.term)
    (R : Prem guestProgram img n C Ks X)
    (hpro : ∀ s op, X s → Pro s → Fine (refMem img) s → OnRef guestProgram img n s →
      C.ops[s.pc]? = some op →
      StepOk C (refMem img) (fun s' ↦ Pro s' ∨ StartMain Km E0 s') op ((C.hints[s.pc]?).getD []) s) :
    InvRule guestProgram img n C (refMem img)
      (guestInv guestProgram Ks Km E0 (fun K ↦ AtOff K.E K.F K.code) X Pro) :=
  inv_rule hκ hC P hW R hpro

/-- **The invariant holds at the guest's initial state.** -/
theorem guest_inv_init {adv : Advice} {input : PublicInput} {Ks : List Cert} {Km : Cert} {E0 : Env}
    {Q : Cert → ℕ → St → Prop} {X Pro : St → Prop}
    (hinit : ∀ C m, Ctx.of guestProgram adv = .ok C → initMem adv input = .ok m →
      X (initSt C adv m) ∧ Pro (initSt C adv m)) :
    ∀ C m, Ctx.of guestProgram adv = .ok C → initMem adv input = .ok m →
      guestInv guestProgram Ks Km E0 Q X Pro (initSt C adv m) :=
  fun C m hC hm ↦ inv_init (hinit C m hC hm).1 (hinit C m hC hm).2

end

end LeanVM.Guest.Mode
