module

public import LeanVM.Guest.Mode.InvRule
public import LeanVM.Guest.Mode.HintsCtx
public import LeanVM.Guest.Bytecode

/-!
# A guest function's certificate, tied to the executor

`certOk_fn`: a guest function's mode walk (`walk`), its length, its operands below `2^28`
(`offSmall`) and its hints the advice's (`HintsOk`) make its certificate one `ProgOk` takes
(`CertOk`): the executor's instruction at each of its pcs is its code's (`ctx_op_off`, from the fetch
lemma and the decoder's `OpOf`), and its hints the advice's (`ctx_hintsOk`). `guest_inv_rule`,
`guest_inv_init`: `inv_rule` and `inv_init` on the guest program.
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

/-- **A guest function's certificate** is tied to the executor run on the guest's advice: its walk,
its length, its operands small and its hints the advice's. -/
theorem certOk_fn {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C)
    (ha : adv.hints = Data.adviceHints) {f : CompiledFunction} (hf : f ∈ Data.functions) {K : Cert}
    (hcode : K.code = f.code) (hentry : K.F.entry = f.entryPc) (hw : walk K.E K.F K.code = true)
    (hlen : K.F.len = K.code.length) (hs : K.code.all offSmall = true)
    (hh : HintsOk K.F Data.adviceHints) : CertOk C K := by
  have hwc := CompiledFunction.wellChunked_of_mem hf
  refine certOk_of hC ha hw hlen (fun i hi ↦ ?_) hs hh
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

/-! ## On the guest -/

/-- **The invariant rule on the guest program.** -/
theorem guest_inv_rule {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx} {Ks : List Cert}
    {Km : Cert} {E0 : Env} {X Pro : St → Prop} (hκ : κ ≤ 28) (hC : Ctx.of guestProgram adv = .ok C)
    (P : ProgOk guestProgram C Ks Km E0) (R : Prem guestProgram img n C Ks X)
    (hpro : ∀ s op, X s → Pro s → Fine (refMem img) s → OnRef guestProgram img n s →
      C.ops[s.pc]? = some op →
      StepOk C (refMem img) (fun s' ↦ Pro s' ∨ StartMain Km E0 s') op ((C.hints[s.pc]?).getD []) s) :
    InvRule guestProgram img n C (refMem img) (guestInv guestProgram Ks Km E0 X Pro) :=
  inv_rule hκ hC P R hpro

/-- **The invariant holds at the guest's initial state.** -/
theorem guest_inv_init {adv : Advice} {input : PublicInput} {Ks : List Cert} {Km : Cert} {E0 : Env}
    {X Pro : St → Prop}
    (hinit : ∀ C m, Ctx.of guestProgram adv = .ok C → initMem adv input = .ok m →
      X (initSt C adv m) ∧ Pro (initSt C adv m)) :
    ∀ C m, Ctx.of guestProgram adv = .ok C → initMem adv input = .ok m →
      guestInv guestProgram Ks Km E0 X Pro (initSt C adv m) :=
  fun C m hC hm ↦ inv_init (hinit C m hC hm).1 (hinit C m hC hm).2

end

end LeanVM.Guest.Mode
