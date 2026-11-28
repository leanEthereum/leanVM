module

public import LeanVM.Guest.Mode.InvDefs
public import LeanVM.Guest.Bytecode

/-!
# A guest function's code, tied to the executor

`codeOk_fn`: a guest function's code, its operands below `2^28` (`offSmall`), is the executor's
(`CodeOk`): the executor's instruction at each of its pcs is its code's (`ctx_op_off`, from the fetch
lemma and the decoder's `OpOf`).
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

/-- **A guest function's code is the executor's**, run on any advice, its operands small. -/
theorem codeOk_fn {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C)
    {f : CompiledFunction} (hf : f ∈ Data.functions) {K : Cert} (hcode : K.code = f.code)
    (hentry : K.F.entry = f.entryPc) (hs : K.code.all offSmall = true) : CodeOk C K :=
  codeOk_of hC (fn_ins hf hcode hentry) hs

end

end LeanVM.Guest.Mode
