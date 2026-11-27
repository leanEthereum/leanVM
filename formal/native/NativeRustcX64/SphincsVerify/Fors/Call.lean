module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.KeccakF.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names
public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.SphincsVerify.Fors.Glue
public import NativeRustcX64.SphincsVerify.Digest.Call

/-!
# The FORS region's calls (x86-64)

From a block's end at a call (`PcOk` of `call l`, `KeepC`): the callee's contract, then the proof
continues at the return with `Keep`, the callee-saved registers (`Saved`), the frame's bytes apart
from what the callee changed (`KC`) and the callee's result: `memset_then`, `memcpy_then`,
`update_then`, `finalize_then`, `keccakF_then`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash
open NativeRustcX64.SphincsVerifyProof.Digest (HasherAt)

@[expose] public section

/-- The frame's bytes apart from `a .. a + n` are kept from `m₁` to `m₂`. -/
def KC (r : Run) (m₁ m₂ : MachineData) (a n : Nat) : Prop :=
  ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 21624 → (o + bs.length ≤ a ∨ a + n ≤ o) →
    BytesAt m₁.dmem (r.off o) bs → BytesAt m₂.dmem (r.off o) bs

end

public section

variable [ElfHost] {r : Run}

omit [ElfHost] in
theorem kc_of [Labels] (hpre : r.Pre) {m₁ m₂ : MachineData} (hc : r.AtCall m₁) {a n N : Nat}
    (ha : Scratch a n) (hN : N ≤ finalizeStack)
    (hout : SameOutside m₁.dmem m₂.dmem (r.CallOut m₁ a n N)) : KC r m₁ m₂ a n :=
  fun ho hd h ↦ r.bytesAt_of_call hpre hc (by unfold Scratch at ha; omega) hN hout ho hd h

/-- **`memset(a, 0, n)`** at a call, then on at `next`. -/
theorem memset_then (hpre : r.Pre) (hc : Callees) {c : Nat} {env : Env} {next : Int64}
    {st : MachineState} (hpc : PcOk env (.call NativeRustcX64.Common.Memset.entryLabel) next st) (hK : KeepC r c st.data)
    {a n : Nat} (h0 : Run.RegIs st.data .rdi (r.off a)) (h1 : (reg st.data .rsi).toNat = 0)
    (h2 : (reg st.data .rdx).toNat = n) (ha : Scratch a n) {R : MachineState → Prop}
    (k : ∀ m₂, Keep r c m₂ → Saved st.data m₂ → KC r st.data m₂ a n →
      BytesAt m₂.dmem (r.off a) (List.replicate n 0) → Eventually (elfStep1 ElfHost.exe) R ⟨m₂, next⟩) :
    Eventually (elfStep1 ElfHost.exe) R st :=
  call_then_elf hpc hc.2.1 (r.memset_pre hpre hK.1 h0 h2 (by unfold Scratch at ha; omega))
    fun st₂ hpc₂ hrsp hpost ↦ by
      obtain ⟨hz, hout, hS⟩ := r.memset_out h0 h2 hpost
      rw [h1] at hz
      exact Chains.pc_at hpc₂ (k _ (Keep.of_call hpre hK hS hrsp ha (by decide) hout) hS
        (kc_of hpre hK.1 ha (by decide) hout) hz)

/-- **`memcpy(a, b, n)`** at a call, the bytes `bs` at `b`, then on at `next`. -/
theorem memcpy_then (hpre : r.Pre) (hc : Callees) {c : Nat} {env : Env} {next : Int64}
    {st : MachineState} (hpc : PcOk env (.call NativeRustcX64.Common.Memcpy.entryLabel) next st) (hK : KeepC r c st.data)
    {a b n : Nat} (h0 : Run.RegIs st.data .rdi (r.off a)) (h1 : Run.RegIs st.data .rsi (r.off b))
    (h2 : (reg st.data .rdx).toNat = n) (ha : Scratch a n) (hb : b + n ≤ 21624)
    (hd : a + n ≤ b ∨ b + n ≤ a) {bs : List UInt8} (hl : bs.length = n)
    (hbs : BytesAt st.data.dmem (r.off b) bs) {R : MachineState → Prop}
    (k : ∀ m₂, Keep r c m₂ → Saved st.data m₂ → KC r st.data m₂ a n →
      BytesAt m₂.dmem (r.off a) bs → Eventually (elfStep1 ElfHost.exe) R ⟨m₂, next⟩) :
    Eventually (elfStep1 ElfHost.exe) R st :=
  call_then_elf hpc hc.1 (r.memcpy_pre hpre hK.1 h0 h1 h2 (by unfold Scratch at ha; omega) hb hd)
    fun st₂ hpc₂ hrsp hpost ↦ by
      obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
      rw [← hl, bytesOf_of_bytesAt hbs] at hB
      exact Chains.pc_at hpc₂ (k _ (Keep.of_call hpre hK hS hrsp ha (by decide) hout) hS
        (kc_of hpre hK.1 ha (by decide) hout) hB)

/-- **`memcpy(a, b, n)`** at a call, then on at `next` with the copy. -/
theorem memcpy_then' (hpre : r.Pre) (hc : Callees) {c : Nat} {env : Env} {next : Int64}
    {st : MachineState} (hpc : PcOk env (.call NativeRustcX64.Common.Memcpy.entryLabel) next st) (hK : KeepC r c st.data)
    {a b n : Nat} (h0 : Run.RegIs st.data .rdi (r.off a)) (h1 : Run.RegIs st.data .rsi (r.off b))
    (h2 : (reg st.data .rdx).toNat = n) (ha : Scratch a n) (hb : b + n ≤ 21624)
    (hd : a + n ≤ b ∨ b + n ≤ a) {R : MachineState → Prop}
    (k : ∀ m₂, Keep r c m₂ → Saved st.data m₂ → KC r st.data m₂ a n →
      BytesAt m₂.dmem (r.off a) (bytesOf st.data.dmem (r.off b) n) →
      Eventually (elfStep1 ElfHost.exe) R ⟨m₂, next⟩) :
    Eventually (elfStep1 ElfHost.exe) R st :=
  call_then_elf hpc hc.1 (r.memcpy_pre hpre hK.1 h0 h1 h2 (by unfold Scratch at ha; omega) hb hd)
    fun st₂ hpc₂ hrsp hpost ↦ by
      obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
      exact Chains.pc_at hpc₂ (k _ (Keep.of_call hpre hK hS hrsp ha (by decide) hout) hS
        (kc_of hpre hK.1 ha (by decide) hout) hB)

/-- **`Hasher::update(a, b, n)`** at a call, the hasher at `a` having absorbed `x`, the bytes
`bs` at `b`, then on at `next`. -/
theorem update_then (hpre : r.Pre) (hc : Callees) {c : Nat} {env : Env} {next : Int64}
    {st : MachineState} (hpc : PcOk env (.call NativeRustcX64.Common.Update.entryLabel) next st) (hK : KeepC r c st.data)
    {a b n : Nat} (h0 : Run.RegIs st.data .rdi (r.off a)) (h1 : Run.RegIs st.data .rsi (r.off b))
    (h2 : (reg st.data .rdx).toNat = n) (ha : Scratch a 344) (hb : b + n ≤ 21624)
    (hd : a + 344 ≤ b ∨ b + n ≤ a) {x bs : List UInt8} (hl : bs.length = n)
    (hH : HasherAt r st.data a x) (hbs : BytesAt st.data.dmem (r.off b) bs)
    {R : MachineState → Prop}
    (k : ∀ m₂, Keep r c m₂ → Saved st.data m₂ → KC r st.data m₂ a 344 →
      HasherAt r m₂ a (x ++ bs) → Eventually (elfStep1 ElfHost.exe) R ⟨m₂, next⟩) :
    Eventually (elfStep1 ElfHost.exe) R st :=
  call_then_elf hpc hc.2.2.1
    (r.update_pre hpre hK.1 h0 h1 h2 (by unfold Scratch at ha; omega) hb hd hH.holds_some)
    fun st₂ hpc₂ hrsp hpost ↦ by
      obtain ⟨hA, hout, hS⟩ := r.update_out h0 h1 h2 hpost
      have hK₂ := Keep.of_call hpre hK hS hrsp ha (by decide) hout
      have hA' := hA x hH.holds
      rw [← hl, bytesOf_of_bytesAt hbs] at hA'
      exact Chains.pc_at hpc₂ (k _ hK₂ hS (kc_of hpre hK.1 ha (by decide) hout)
        ⟨_, Digest.bytesAt_bytesOf (r.frame_mapped hpre hK₂.1.2.2.2
          (by unfold Scratch at ha; omega)).1, hA'⟩)

/-- **`Hasher::finalize(o, a)`** at a call, the hasher at `a` having absorbed `x`, then on at
`next`. -/
theorem finalize_then (hpre : r.Pre) (hc : Callees) {c : Nat} {env : Env} {next : Int64}
    {st : MachineState} (hpc : PcOk env (.call NativeRustcX64.Common.Finalize.entryLabel) next st) (hK : KeepC r c st.data)
    {o a : Nat} (h0 : Run.RegIs st.data .rdi (r.off o)) (h1 : Run.RegIs st.data .rsi (r.off a))
    (ho : Scratch o 32) (ha : a + 344 ≤ 21624) (hd : o + 32 ≤ a ∨ a + 344 ≤ o) {x : List UInt8}
    (hH : HasherAt r st.data a x) {R : MachineState → Prop}
    (k : ∀ m₂, Keep r c m₂ → Saved st.data m₂ → KC r st.data m₂ o 32 →
      BytesAt m₂.dmem (r.off o) (Keccak.hashBytes x) → Eventually (elfStep1 ElfHost.exe) R ⟨m₂, next⟩) :
    Eventually (elfStep1 ElfHost.exe) R st :=
  call_then_elf hpc hc.2.2.2.1
    (r.finalize_pre hpre hK.1 h0 h1 (by unfold Scratch at ho; omega) ha hd hH.holds_some)
    fun st₂ hpc₂ hrsp hpost ↦ by
      obtain ⟨hB, hout, hS⟩ := r.finalize_out h0 h1 hpost
      rw [Keccak.finalize_eq hH.holds] at hB
      exact Chains.pc_at hpc₂ (k _ (Keep.of_call hpre hK hS hrsp ho (by decide) hout) hS
        (kc_of hpre hK.1 ho (by decide) hout) hB)

/-- **`keccak_f(a)`** at a call, then on at `next`. -/
theorem keccakF_then (hpre : r.Pre) (hc : Callees) {c : Nat} {env : Env} {next : Int64}
    {st : MachineState} (hpc : PcOk env (.call NativeRustcX64.Common.KeccakF.entryLabel) next st) (hK : KeepC r c st.data)
    {a : Nat} (h0 : Run.RegIs st.data .rdi (r.off a)) (ha : Scratch a 200)
    {R : MachineState → Prop}
    (k : ∀ m₂, Keep r c m₂ → Saved st.data m₂ → KC r st.data m₂ a 200 →
      BytesAt m₂.dmem (r.off a) (Keccak.keccakF (bytesOf st.data.dmem (r.off a) 200)) →
      Eventually (elfStep1 ElfHost.exe) R ⟨m₂, next⟩) :
    Eventually (elfStep1 ElfHost.exe) R st :=
  call_then_elf hpc hc.2.2.2.2 (r.keccakF_pre hpre hK.1 h0 (by unfold Scratch at ha; omega))
    fun st₂ hpc₂ hrsp hpost ↦ by
      obtain ⟨hB, hout, hS⟩ := r.keccakF_out h0 hpost
      exact Chains.pc_at hpc₂ (k _ (Keep.of_call hpre hK hS hrsp ha (by decide) hout) hS
        (kc_of hpre hK.1 ha (by decide) hout) hB)

end

end NativeRustcX64.SphincsVerifyProof.Fors
