module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.SphincsVerify.Encode.Key
public import NativeRustcX64.SphincsVerify.Encode.Num
public import NativeRustc.Sphincs.Digest
public import NativeRustcX64.Sym
meta import NativeRustcX64.Code.Sphincs.SphincsVerify.Part2
meta import NativeRustcX64.SphincsVerify.Frame

/-!
# The encoder's digest: `b105 .. b112`

From `b105` (directive 1173, hasher A new, the encoder's address at `2048`): hasher A absorbs
`PK.seed` and the address (`update`, `b105`, `b106`), is cloned into hasher B (`memcpy`, `b107`),
which absorbs the message (`b108`) and is cloned back (`b109`); the counter, big-endian, is
written over the address and absorbed (`b110`), and `finalize` writes the digest at `576`
(`b111`); `b112` loads its first 16 bytes as the 128-bit number `rax · 2⁶⁴ + rdx` (`hash_spec`):
`u128::from_be_bytes` of `encode`'s digest.
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs NativeRustc.Keccak LeanVM.Protocol.KeccakHash
open NativeRustcX64.Sym

@[expose] public section

set_option Elab.async false

/-- The start of a block of the hashing: RSP the frame's base. -/
def sCall : SState := Run.frameState [(.r14, .label "memcpy")]

sym_block b105_exec := exec Sphincs.SphincsVerify.b105 sCall
sym_block b106_exec := exec Sphincs.SphincsVerify.b106 sCall
sym_block b107_exec := exec Sphincs.SphincsVerify.b107 sCall
sym_block b108_exec := exec Sphincs.SphincsVerify.b108 sCall
sym_block b109_exec := exec Sphincs.SphincsVerify.b109 sCall
sym_block b110_exec := exec Sphincs.SphincsVerify.b110 sCall
sym_block b111_exec := exec Sphincs.SphincsVerify.b111 sCall
sym_block b112_exec := exec Sphincs.SphincsVerify.b112 sCall

/-- The 128-bit digest the loop takes apart: `rax · 2⁶⁴ + rdx`. -/
def digest128 (m : MachineData) : Nat := (reg m .rax).toNat * 2 ^ 64 + (reg m .rdx).toNat

namespace Run

variable (r : Run) [Labels]

omit [Labels] in
theorem bytesAt_bytesOf {d : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n) :
    BytesAt d a (bytesOf d a n) := fun i hi ↦ by
  simp only [bytesOf, List.length_map, List.length_range] at hi
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h i hi)
  rw [hv]
  rfl

omit [Labels] in
theorem bytesOf_of_bytesAt' {d : DataMem} {a : BitVec 64} {bs : List UInt8} {n : Nat}
    (h : BytesAt d a bs) (hn : bs.length = n) : bytesOf d a n = bs := by
  subst hn
  exact bytesOf_of_bytesAt h

/-- **The frame's bytes a block does not write**, as `bytesOf` reads them. -/
theorem bytesOf_kept (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) (hk : Kept r.m0.dmem m.dmem) {o n : Nat} (ho : o + n ≤ 29384)
    (hn : noWriteIn S o n = true) : bytesOf m'.dmem (r.off o) n = bytesOf m.dmem (r.off o) n := by
  have hb := bytesAt_bytesOf (r.frame_mapped hpre hk ho).1
  have hl : (bytesOf m.dmem (r.off o) n).length = n := by simp [bytesOf]
  exact bytesOf_of_bytesAt' (r.bytesAt_kept hpre hm hwf (by rw [hl]; exact ho) hb
    (by rw [hl]; exact hn)) hl

end Run

namespace Run

variable (r : Run) [Labels]

omit [Labels] in
theorem rdx_of {m : MachineData} {v : BitVec 64} {n : Nat} (h : reg m .rdx = v)
    (hv : v = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) : (reg m .rdx).toNat = n := by
  rw [h, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

omit [Labels] in
theorem length_seed : r.seed.length = 16 := by
  simp [seed, pk, PublicKey.fromBytes, r.length_pkBytes]

omit [Labels] in
/-- **`PK.seed`** in the frame, as `bytesOf` reads it. -/
theorem seed_bytes {m : MachineData} (hI : r.Inputs m) : bytesOf m.dmem (r.off 112) 16 = r.seed :=
  bytesOf_of_bytesAt' (fun i hi ↦ by
    have := hI.1 i (by rw [r.length_pkBytes]; rw [length_seed] at hi; omega)
    rw [this]
    simp [seed, pk, PublicKey.fromBytes, List.getElem_take]) r.length_seed

end Run


variable [Host]

theorem goto {R : MachineState → Prop} {st : MachineState} {p : Int64} (hpc : st.pc = p)
    (h : Eventually (step1 Host.exe) R ⟨st.data, p⟩) : Eventually (step1 Host.exe) R st := by
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  exact h

theorem pc_step (r : Run) {j n j' : Nat} {b : List Directive} (hn : b.length = n)
    (hj : j + n = j') : Host.addrOf (r.k + j + b.length) = r.pc j' := by
  rw [hn, Nat.add_assoc, hj]
  rfl

/-- **A block of the hashing**: run from a state of the invariant, it keeps the data. -/
theorem enc_block (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {b : List Directive} {j : Nat} (hb : b.IsInfixAt Sphincs.SphincsVerify.code j) (hne : b ≠ [])
    {S : SState} {x : Exit} (hx : exec b sCall = some (S, x)) (hS : encKeeps S = true)
    {l : Nat} {s : List UInt8} {c : UInt32} {m : MachineData} (h : r.EncBase l s c m)
    {R : MachineState → Prop}
    (cont : ∀ st, (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + j + b.length)).toBitVec).WF →
      Match (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + j + b.length)).toBitVec) S
      st.data → PcOk (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + j + b.length)).toBitVec) x
        (Host.addrOf (r.k + j + b.length)) st →
      r.EncData l s c st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ := by
  have hk := hb.trans hp.1 hne
  have hwf := r.frame_wf hpre h.2.2.1.2.2.2 (fun _ ↦ 0) (Host.addrOf (r.k + j + b.length)).toBitVec
  have hm := r.match_frame hpre h.2.2.1 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (r.k + j + b.length)).toBitVec)
    (known := [(.r14, .label "memcpy")]) (labels := [])
    (bounds := []) (aliases := []) ⟨Run.EncData.memcpy r h.2.2.2, trivial⟩ trivial trivial trivial
  exact Sym.exec_then hk hx hwf (fun _ _ ↦ rfl) hm fun st hm' hpc ↦
    cont st hwf hm' hpc (r.encData_of_block hpre h.2.2.2 h.2.1 hm' hwf hS)

/-- **A block of the hashing that swaps the counter**: it keeps the data, EBX's counter
changed. -/
theorem enc_block' (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {b : List Directive} {j : Nat} (hb : b.IsInfixAt Sphincs.SphincsVerify.code j) (hne : b ≠ [])
    {S : SState} {x : Exit} (hx : exec b sCall = some (S, x)) (hS : encKeepsNoBx S = true)
    {l : Nat} {s : List UInt8} {c : UInt32} {m : MachineData} (h : r.EncBase l s c m)
    {R : MachineState → Prop}
    (cont : ∀ st, (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + j + b.length)).toBitVec).WF →
      Match (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + j + b.length)).toBitVec) S
      st.data → PcOk (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + j + b.length)).toBitVec) x
        (Host.addrOf (r.k + j + b.length)) st →
      r.EncData l s (UInt32.ofNat (reg st.data .rbx).toNat) st.data →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ := by
  have hk := hb.trans hp.1 hne
  have hwf := r.frame_wf hpre h.2.2.1.2.2.2 (fun _ ↦ 0) (Host.addrOf (r.k + j + b.length)).toBitVec
  have hm := r.match_frame hpre h.2.2.1 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (r.k + j + b.length)).toBitVec)
    (known := [(.r14, .label "memcpy")]) (labels := [])
    (bounds := []) (aliases := []) ⟨Run.EncData.memcpy r h.2.2.2, trivial⟩ trivial trivial trivial
  exact Sym.exec_then hk hx hwf (fun _ _ ↦ rfl) hm fun st hm' hpc ↦
    cont st hwf hm' hpc (r.encData_of_block' hpre h.2.2.2 h.2.1 hm' hwf hS)

/-- **`Hasher::update(a, b, n)`** on hasher A or B, at a call with the data. -/
theorem call_update (r : Run) (hc : Callees) (hpre : r.Pre) {st : MachineState} {next : Int64}
    (hpc : st.pc = Labels.label NativeRustcX64.Common.Update.entryLabel ∧ retOf st.data = next) {l : Nat} {s : List UInt8}
    {c : UInt32} (hl : l < 3) (hs : s.length = 16) (hcall : r.AtCall st.data)
    (h : r.EncData l s c st.data) {a b n : Nat} {x : List UInt8}
    (h0 : Run.RegIs st.data .rdi (r.off a)) (h1 : Run.RegIs st.data .rsi (r.off b))
    (h2 : (reg st.data .rdx).toNat = n)
    (ha : (4096 ≤ a ∧ a + 344 ≤ 4440) ∨ (576 ≤ a ∧ a + 344 ≤ 920)) (hb : b + n ≤ 29384)
    (hd : a + 344 ≤ b ∨ b + n ≤ a) (hh : HasherHolds (bytesOf st.data.dmem (r.off a) 344) x)
    {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → r.EncBase l s c st'.data →
      HasherHolds (bytesOf st'.data.dmem (r.off a) 344) (x ++ bytesOf st.data.dmem (r.off b) n) →
      SameOutside st.data.dmem st'.data.dmem (r.CallOut st.data a 344 updateStack) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hc.2.2.1 hpc.1
    (r.update_pre hpre hcall h0 h1 h2 (by omega) hb hd ⟨x, hh⟩)) fun st' h' ↦ by
    obtain ⟨hH, hout, hS⟩ := r.update_out h0 h1 h2 h'.2.2
    exact cont st' (h'.1.trans hpc.2)
      ⟨hl, hs, r.frame_of_call hpre hcall hS h'.2.1 (by omega) (by decide) hout,
        r.encData_of_call hpre hcall h hs hS ha (by decide) hout⟩ (hH x hh) hout

/-- **`memcpy(a, b, 344)`** between the hashers, at a call with the data. -/
theorem call_memcpy (r : Run) (hc : Callees) (hpre : r.Pre) {st : MachineState} {next : Int64}
    (hpc : st.pc = Labels.label NativeRustcX64.Common.Memcpy.entryLabel ∧ retOf st.data = next) {l : Nat} {s : List UInt8}
    {c : UInt32} (hl : l < 3) (hs : s.length = 16) (hcall : r.AtCall st.data)
    (h : r.EncData l s c st.data) {a b : Nat}
    (h0 : Run.RegIs st.data .rdi (r.off a)) (h1 : Run.RegIs st.data .rsi (r.off b))
    (h2 : (reg st.data .rdx).toNat = 344)
    (ha : (4096 ≤ a ∧ a + 344 ≤ 4440) ∨ (576 ≤ a ∧ a + 344 ≤ 920)) (hb : b + 344 ≤ 29384)
    (hd : a + 344 ≤ b ∨ b + 344 ≤ a) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → r.EncBase l s c st'.data →
      bytesOf st'.data.dmem (r.off a) 344 = bytesOf st.data.dmem (r.off b) 344 →
      SameOutside st.data.dmem st'.data.dmem (r.CallOut st.data a 344 0) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hc.1 hpc.1
    (r.memcpy_pre hpre hcall h0 h1 h2 (by omega) hb hd)) fun st' h' ↦ by
    obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 h'.2.2
    exact cont st' (h'.1.trans hpc.2)
      ⟨hl, hs, r.frame_of_call hpre hcall hS h'.2.1 (by omega) (Nat.zero_le _) hout,
        r.encData_of_call hpre hcall h hs hS ha (Nat.zero_le _) hout⟩
      (Run.bytesOf_of_bytesAt' hB (by simp [bytesOf])) hout

/-- **`Hasher::finalize(576, 4096)`**: hasher A's digest into hasher B's place. -/
theorem call_finalize (r : Run) (hc : Callees) (hpre : r.Pre) {st : MachineState} {next : Int64}
    (hpc : st.pc = Labels.label NativeRustcX64.Common.Finalize.entryLabel ∧ retOf st.data = next) {l : Nat} {s : List UInt8}
    {c : UInt32} (hl : l < 3) (hs : s.length = 16) (hcall : r.AtCall st.data)
    (h : r.EncData l s c st.data)
    (h0 : Run.RegIs st.data .rdi (r.off 576)) (h1 : Run.RegIs st.data .rsi (r.off 4096))
    {x : List UInt8} (hh : HasherHolds (bytesOf st.data.dmem (r.off 4096) 344) x)
    {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → r.EncBase l s c st'.data →
      BytesAt st'.data.dmem (r.off 576) (hashBytes x) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  Eventually.bind (Spec.apply hc.2.2.2.1 hpc.1
    (r.finalize_pre hpre hcall h0 h1 (by omega) (by omega) (.inl (by omega)) ⟨x, hh⟩))
    fun st' h' ↦ by
    obtain ⟨hD, hout, hS⟩ := r.finalize_out h0 h1 h'.2.2
    rw [finalize_eq hh] at hD
    exact cont st' (h'.1.trans hpc.2)
      ⟨hl, hs, r.frame_of_call hpre hcall hS h'.2.1 (by omega) (le_refl _) hout,
        r.encData_of_call hpre hcall h hs hS (.inr ⟨le_refl _, by omega⟩) (le_refl _) hout⟩ hD

/-- **The encoder's digest**: from `b105`, hasher A new and the address at `2048`, the machine
reaches the codeword's loop with `rax · 2⁶⁴ + rdx` the big-endian number of `encode`'s digest. -/
theorem hash_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {l : Nat} {s : List UInt8} {c : UInt32} {m : MachineData}
    (h : r.EncBase l s c m) (hA : r.EncAdrs l m)
    (hh : HasherHolds (bytesOf m.dmem (r.off 4096) 344) []) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b113Offset ∧ (∃ c', r.EncBase l s c' st.data) ∧
      digest128 st.data = beNat (encodeDigest r.seed (r.key l) s c) ∧
      Run.RegIs st.data .rdi 0 ∧ Run.RegIs st.data .rsi (r.off 577)) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b105Offset⟩ := by
  have hl := h.1
  have hs := h.2.1
  -- b105, update(A, PK.seed)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b105_in_code (List.cons_ne_nil _ _) b105_exec
    rfl h fun st1 hwf1 hm1 hpc1 hd1 ↦ ?_
  have hc1 := Run.AtCall.of_match r hpre h.2.2.1 hm1 hwf1 rfl rfl
  have hk1 := fun {o n : Nat} ho hn ↦
    r.bytesOf_kept hpre hm1 hwf1 h.2.2.1.2.2.2 (o := o) (n := n) ho hn
  have hA1 : r.EncAdrs l st1.data :=
    r.bytesAt_kept hpre hm1 hwf1 (by rw [length_adrs7]; omega) hA (by rw [length_adrs7]; rfl)
  refine call_update r hc hpre hpc1 hl hs hc1 hd1 (a := 4096) (b := 112) (n := 16)
    ((hm1.regs .rdi _ rfl).trans h.2.2.2.2.2.1) ((hm1.regs .rsi _ rfl).trans (r.ptr_eval _ _ _ 112))
    (Run.rdx_of (hm1.regs .rdx _ rfl) rfl (by decide))
    (.inl ⟨le_refl _, le_refl _⟩) (by omega) (.inr (by omega))
    (by rw [hk1 (by decide) rfl]; exact hh) fun st2 hpc2 h2 hH2 hout2 ↦ ?_
  rw [hk1 (by decide) rfl, r.seed_bytes h.2.2.2.1, List.nil_append] at hH2
  have hA2 : r.EncAdrs l st2.data := r.bytesAt_of_call hpre hc1 (by omega) (by decide) hout2
    (by rw [length_adrs7]; omega) (by rw [length_adrs7]; omega) hA1
  refine goto (hpc2.trans (pc_step r NativeRustcX64.Sphincs.SphincsVerify.b105_length rfl)) ?_
  -- b106, update(A, address)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b106_in_code (List.cons_ne_nil _ _) b106_exec
    rfl h2 fun st3 hwf3 hm3 hpc3 hd3 ↦ ?_
  have hc3 := Run.AtCall.of_match r hpre h2.2.2.1 hm3 hwf3 rfl rfl
  have hk3 := fun {o n : Nat} ho hn ↦
    r.bytesOf_kept hpre hm3 hwf3 h2.2.2.1.2.2.2 (o := o) (n := n) ho hn
  refine call_update r hc hpre hpc3 hl hs hc3 hd3 (a := 4096) (b := 2048) (n := 32)
    ((hm3.regs .rdi _ rfl).trans h2.2.2.2.2.2.1) ((hm3.regs .rsi _ rfl).trans h2.2.2.2.2.2.2.2.1)
    (Run.rdx_of (hm3.regs .rdx _ rfl) rfl (by decide))
    (.inl ⟨le_refl _, le_refl _⟩) (by omega) (.inr (by omega))
    (by rw [hk3 (by decide) rfl]; exact hH2) fun st4 hpc4 h4 hH4 _ ↦ ?_
  rw [hk3 (by decide) rfl, Run.bytesOf_of_bytesAt' hA2 (length_adrs7 _)] at hH4
  refine goto (hpc4.trans (pc_step r NativeRustcX64.Sphincs.SphincsVerify.b106_length rfl)) ?_
  -- b107, memcpy(B, A)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b107_in_code (List.cons_ne_nil _ _) b107_exec
    rfl h4 fun st5 hwf5 hm5 hpc5 hd5 ↦ ?_
  have hc5 := Run.AtCall.of_match r hpre h4.2.2.1 hm5 hwf5 rfl rfl
  have hk5 := fun {o n : Nat} ho hn ↦
    r.bytesOf_kept hpre hm5 hwf5 h4.2.2.1.2.2.2 (o := o) (n := n) ho hn
  refine call_memcpy r hc hpre hpc5 hl hs hc5 hd5 (a := 576) (b := 4096)
    ((hm5.regs .rdi _ rfl).trans h4.2.2.2.2.2.2.1) ((hm5.regs .rsi _ rfl).trans h4.2.2.2.2.2.1)
    (Run.rdx_of (hm5.regs .rdx _ rfl) rfl (by decide))
    (.inr ⟨le_refl _, le_refl _⟩) (by omega) (.inl (by omega)) fun st6 hpc6 h6 hB6 _ ↦ ?_
  have hHB6 : HasherHolds (bytesOf st6.data.dmem (r.off 576) 344)
      (r.seed ++ (r.key l).adrs 7) := by
    rw [hB6, hk5 (by decide) rfl]; exact hH4
  refine goto (hpc6.trans (pc_step r NativeRustcX64.Sphincs.SphincsVerify.b107_length rfl)) ?_
  -- b108, update(B, message)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b108_in_code (List.cons_ne_nil _ _) b108_exec
    rfl h6 fun st7 hwf7 hm7 hpc7 hd7 ↦ ?_
  have hc7 := Run.AtCall.of_match r hpre h6.2.2.1 hm7 hwf7 rfl rfl
  have hk7 := fun {o n : Nat} ho hn ↦
    r.bytesOf_kept hpre hm7 hwf7 h6.2.2.1.2.2.2 (o := o) (n := n) ho hn
  refine call_update r hc hpre hpc7 hl hs hc7 hd7 (a := 576) (b := 144) (n := 16)
    ((hm7.regs .rdi _ rfl).trans h6.2.2.2.2.2.2.1)
    ((hm7.regs .rsi _ rfl).trans h6.2.2.2.2.2.2.2.2.1)
    (Run.rdx_of (hm7.regs .rdx _ rfl) rfl (by decide))
    (.inr ⟨le_refl _, le_refl _⟩) (by omega) (.inr (by omega))
    (by rw [hk7 (by decide) rfl]; exact hHB6) fun st8 hpc8 h8 hH8 _ ↦ ?_
  rw [hk7 (by decide) rfl, Run.bytesOf_of_bytesAt' h6.2.2.2.2.2.2.2.2.2.1 h6.2.1] at hH8
  refine goto (hpc8.trans (pc_step r NativeRustcX64.Sphincs.SphincsVerify.b108_length rfl)) ?_
  -- b109, memcpy(A, B)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b109_in_code (List.cons_ne_nil _ _) b109_exec
    rfl h8 fun st9 hwf9 hm9 hpc9 hd9 ↦ ?_
  have hc9 := Run.AtCall.of_match r hpre h8.2.2.1 hm9 hwf9 rfl rfl
  have hk9 := fun {o n : Nat} ho hn ↦
    r.bytesOf_kept hpre hm9 hwf9 h8.2.2.1.2.2.2 (o := o) (n := n) ho hn
  refine call_memcpy r hc hpre hpc9 hl hs hc9 hd9 (a := 4096) (b := 576)
    ((hm9.regs .rdi _ rfl).trans h8.2.2.2.2.2.1) ((hm9.regs .rsi _ rfl).trans h8.2.2.2.2.2.2.1)
    (Run.rdx_of (hm9.regs .rdx _ rfl) rfl (by decide))
    (.inl ⟨le_refl _, le_refl _⟩) (by omega) (.inr (by omega)) fun st10 hpc10 h10 hB10 _ ↦ ?_
  have hHA10 : HasherHolds (bytesOf st10.data.dmem (r.off 4096) 344)
      (r.seed ++ (r.key l).adrs 7 ++ s) := by
    rw [hB10, hk9 (by decide) rfl]; exact hH8
  refine goto (hpc10.trans (pc_step r NativeRustcX64.Sphincs.SphincsVerify.b109_length rfl)) ?_
  -- b110, the counter written, update(A, counter)
  refine enc_block' r hp hpre Sphincs.SphincsVerify.b110_in_code (List.cons_ne_nil _ _) b110_exec
    rfl h10 fun st11 hwf11 hm11 hpc11 hd11 ↦ ?_
  have hc11 := Run.AtCall.of_match r hpre h10.2.2.1 hm11 hwf11 rfl rfl
  have hk11 := fun {o n : Nat} ho hn ↦
    r.bytesOf_kept hpre hm11 hwf11 h10.2.2.1.2.2.2 (o := o) (n := n) ho hn
  have hcb : BytesAt st11.data.dmem (r.off 2048) (be32 c) := by
    have := hm11.bytesAt_write (r := 0) (b := r.base) (sz := frameRegion) rfl (by decide)
      (o := 2048) (n := 4) (v := .un .trunc .W32 (.un .bswap .W32 (.reg .rbx)))
      (fun i hi ↦ by interval_cases i <;> rfl)
    simp only [Sym.eval] at this
    rw [bytes_trunc32, bytes_bswap32] at this
    rw [← h10.2.2.2.2.2.2.2.2.2.2.1]
    exact this
  refine call_update r hc hpre hpc11 hl hs hc11 hd11 (a := 4096) (b := 2048) (n := 4)
    ((hm11.regs .rdi _ rfl).trans h10.2.2.2.2.2.1)
    ((hm11.regs .rsi _ rfl).trans h10.2.2.2.2.2.2.2.1)
    (Run.rdx_of (hm11.regs .rdx _ rfl) rfl (by decide))
    (.inl ⟨le_refl _, le_refl _⟩) (by omega) (.inr (by omega))
    (by rw [hk11 (by decide) rfl]; exact hHA10) fun st12 hpc12 h12 hH12 _ ↦ ?_
  rw [Run.bytesOf_of_bytesAt' (n := 4) hcb rfl] at hH12
  refine goto (hpc12.trans (pc_step r NativeRustcX64.Sphincs.SphincsVerify.b110_length rfl)) ?_
  -- b111, finalize(B's place, A)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b111_in_code (List.cons_ne_nil _ _) b111_exec
    rfl h12 fun st13 hwf13 hm13 hpc13 hd13 ↦ ?_
  have hc13 := Run.AtCall.of_match r hpre h12.2.2.1 hm13 hwf13 rfl rfl
  have hk13 := fun {o n : Nat} ho hn ↦
    r.bytesOf_kept hpre hm13 hwf13 h12.2.2.1.2.2.2 (o := o) (n := n) ho hn
  refine call_finalize r hc hpre hpc13 hl hs hc13 hd13
    ((hm13.regs .rdi _ rfl).trans h12.2.2.2.2.2.2.1) ((hm13.regs .rsi _ rfl).trans h12.2.2.2.2.2.1)
    (by rw [hk13 (by decide) rfl]; exact hH12) fun st14 hpc14 h14 hD14 ↦ ?_
  refine goto (hpc14.trans (pc_step r NativeRustcX64.Sphincs.SphincsVerify.b111_length rfl)) ?_
  -- b112, the digest's number
  refine enc_block r hp hpre Sphincs.SphincsVerify.b112_in_code (List.cons_ne_nil _ _) b112_exec
    rfl h14 fun st15 hwf15 hm15 hpc15 hd15 ↦ .done _ ⟨hpc15.trans (pc_step r NativeRustcX64.Sphincs.SphincsVerify.b112_length rfl),
      ⟨_, hl, hs, Run.Frame.of_match r hpre h14.2.2.1 hm15 hwf15 rfl rfl, hd15⟩, ?_, ?_, ?_⟩
  · have hlen : (hashBytes (r.seed ++ (r.key l).adrs 7 ++ s ++ be32 c)).length = 32 :=
      length_hashBytes _
    have hA' := bytesAt_slice hD14 0 8 (by omega)
    have hB' := bytesAt_slice hD14 8 8 (by omega)
    rw [Run.off_add] at hA' hB'
    unfold digest128
    rw [show reg st15.data .rax = _ from hm15.regs .rax _ rfl,
      show reg st15.data .rdx = _ from hm15.regs .rdx _ rfl]
    simp only [Sym.eval]
    have h8 : ∀ k, k + 8 ≤ 32 →
        (((hashBytes (r.seed ++ (r.key l).adrs 7 ++ s ++ be32 c)).drop k).take 8).length = 8 :=
      fun k hk ↦ by simp only [List.length_take, List.length_drop, hlen]; omega
    rw [Sym.Env.load_of_bytesAt (h8 0 (by decide)) hA',
      Sym.Env.load_of_bytesAt (h8 8 (by decide)) hB', beNat_split _ _ (h8 0 (by decide))
        (h8 8 (by decide)),
      List.drop_zero, ← List.take_add, encodeDigest]
  · exact hm15.regs .rdi _ rfl
  · exact (hm15.regs .rsi _ rfl).trans (r.ptr_eval _ _ _ 577)

end

end NativeRustcX64.SphincsVerifyProof
