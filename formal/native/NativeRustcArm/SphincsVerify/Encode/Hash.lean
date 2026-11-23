module

public import NativeRustcArm.Code.Common.Finalize.Names
public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Update.Names

public import NativeRustcArm.SphincsVerify.Encode.Key
public import NativeRustcArm.SphincsVerify.Encode.Num
public import NativeRustcArm.SphincsVerify.Encode.Loop
public import NativeRustc.Sphincs.Digest
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify.Part2

/-!
# The encoder's digest: `b102 .. b109`

From `b102` (directive 1343, hasher A new, the encoder's address at `24720`): hasher A absorbs
`PK.seed` and the address (`update`, `b102`, `b103`), is cloned into hasher B (`memcpy`, `b104`),
which absorbs the message (`b105`) and is cloned back (`b106`); the counter, big-endian, is
written over the address and absorbed (`b107`), and `finalize` writes the digest at `26768`
(`b108`); `b109` loads its first 16 bytes as the 128-bit number `x9 · 2⁶⁴ + x10` (`hash_spec`):
`u128::from_be_bytes` of `encode`'s digest.
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs NativeRustc.Keccak LeanVM.Protocol.KeccakHash
open NativeRustcArm.Sym

@[expose] public section

set_option Elab.async false

/-- The start of a block of the hashing: X29 the saved registers, X20 `base + 21648`. -/
def sCall : SState :=
  init [(29376, true)] (.ptr 0 0) [(.X29, .ptr 0 29280)] [] [] [(.reg .X20, 0, 21648)]

sym_block b102_exec := exec Sphincs.SphincsVerify.b102 sCall
sym_block b103_exec := exec Sphincs.SphincsVerify.b103 sCall
sym_block b104_exec := exec Sphincs.SphincsVerify.b104 sCall
sym_block b105_exec := exec Sphincs.SphincsVerify.b105 sCall
sym_block b106_exec := exec Sphincs.SphincsVerify.b106 sCall
sym_block b107_exec := exec Sphincs.SphincsVerify.b107 sCall
sym_block b108_exec := exec Sphincs.SphincsVerify.b108 sCall
sym_block b109_exec := exec Sphincs.SphincsVerify.b109 sCall

namespace Run

variable (r : Run) [Labels]

/-- A frame pointer's value. -/
theorem ptr_eval0 (m : MachineData) (vars : Nat → BitVec 64) (o : Nat) :
    (Sym.ptr 0 (o : Int)).eval (r.env m vars) = r.off o := by
  show r.base + BitVec.ofInt 64 (o : Int) = r.base + BitVec.ofNat 64 o
  rw [BitVec.ofInt_natCast]

omit [Labels] in
theorem x2_of {m : MachineData} {v : BitVec 64} {n : Nat} (h : (m.regs.getXReg .X2).toBitVec = v)
    (hv : v = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) : m.regs.X2.toNat = n := by
  rw [show m.regs.X2.toNat = (m.regs.getXReg .X2).toBitVec.toNat from rfl, h, hv,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

omit [Labels] in
theorem bytesAt_bytesOf {d : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n) :
    BytesAt d a (bytesOf d a n) := fun i hi ↦ by
  simp only [bytesOf, List.length_map, List.length_range] at hi
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h i hi)
  rw [hv]
  rfl

end Run

variable [NativeRustcArm.Host]

/-- **A block of the hashing**: run from a state of the invariant, it keeps the invariant. -/
theorem enc_block (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {b : List Directive} {j : Nat} (hb : b.IsInfixAt Sphincs.SphincsVerify.code j) (hne : b ≠ [])
    {S : SState} {x : Exit} (hx : exec b sCall = some (S, x)) (hS : encKeeps S = true)
    {l : Nat} {s : List UInt8} {c : UInt32} {m : MachineData} (h : r.EncBase l s c m)
    {R : MachineState → Prop}
    (cont : ∀ st, Match (r.env m) S st.data →
      PcOk (r.env m) x (NativeRustcArm.Host.addrOf (r.k + j + b.length)) st →
      r.EncBase l s c st.data → Eventually (step1 NativeRustcArm.Host.exe) R st) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc j⟩ := by
  have hk := hb.trans hp.1 hne
  have hwf := r.frame_wf hpre h.2.2.1 (fun _ ↦ 0)
  have hm := r.match_frame hpre h.2.2.1 (vars := fun _ ↦ 0) (known := [(.X29, .ptr 0 29280)])
    (labels := []) (bounds := []) (aliases := [(.reg .X20, 0, 21648)])
    ⟨h.2.2.1.2.1.trans (r.ptr_eval0 m _ 29280).symm, trivial⟩ trivial trivial
    ⟨h.2.2.2.2.2.1.trans (r.ptr_eval0 m _ 21648).symm, trivial⟩
  exact Sym.exec_then hk hx hwf hm fun st hm' hpc ↦
    cont st hm' hpc (Run.EncBase.of_block r hpre h hm' hwf hS)

/-- **`Hasher::update(a, b, n)`** on hasher A or B, from the invariant. -/
theorem call_update (r : Run) (hc : Callees) (hpre : r.Pre) {st : MachineState} {next : Int64}
    (hpc : st.pc = Labels.label NativeRustcArm.Common.Update.entryLabel ∧ retOf st.data = next) {l : Nat} {s : List UInt8}
    {c : UInt32} (h : r.EncBase l s c st.data) {a b n : Nat} {x : List UInt8}
    (h0 : Run.RegIs st.data .X0 (r.off a)) (h1 : Run.RegIs st.data .X1 (r.off b))
    (h2 : st.data.regs.X2.toNat = n)
    (ha : (16400 ≤ a ∧ a + 344 ≤ 16744) ∨ (26768 ≤ a ∧ a + 344 ≤ 27112)) (hb : b + n ≤ 29376)
    (hd : a + 344 ≤ b ∨ b + n ≤ a) (hh : HasherHolds (bytesOf st.data.dmem (r.off a) 344) x)
    {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → r.EncBase l s c st'.data →
      HasherHolds (bytesOf st'.data.dmem (r.off a) 344) (x ++ bytesOf st.data.dmem (r.off b) n) →
      SameOutside st.data.dmem st'.data.dmem (r.CallOut st.data a 344 updateStack) →
      Eventually (step1 NativeRustcArm.Host.exe) R st') :
    Eventually (step1 NativeRustcArm.Host.exe) R st :=
  NativeRustcArm.Eventually.bind (Spec.apply hc.2.2.1 hpc.1
    (r.update_pre hpre h.2.2.1 h0 h1 h2 (by omega) hb hd ⟨x, hh⟩)) fun st' h' ↦ by
    obtain ⟨hH, hout, hS⟩ := r.update_out h0 h1 h2 h'.2
    exact cont st' (h'.1.trans hpc.2) (Run.EncBase.of_call r hpre h hS ha (by decide) hout)
      (hH x hh) hout

/-- **`memcpy(a, b, 344)`** between the hashers, from the invariant. -/
theorem call_memcpy (r : Run) (hc : Callees) (hpre : r.Pre) {st : MachineState} {next : Int64}
    (hpc : st.pc = Labels.label NativeRustcArm.Common.Memcpy.entryLabel ∧ retOf st.data = next) {l : Nat} {s : List UInt8}
    {c : UInt32} (h : r.EncBase l s c st.data) {a b : Nat}
    (h0 : Run.RegIs st.data .X0 (r.off a)) (h1 : Run.RegIs st.data .X1 (r.off b))
    (h2 : st.data.regs.X2.toNat = 344)
    (ha : (16400 ≤ a ∧ a + 344 ≤ 16744) ∨ (26768 ≤ a ∧ a + 344 ≤ 27112)) (hb : b + 344 ≤ 29376)
    (hd : a + 344 ≤ b ∨ b + 344 ≤ a) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → r.EncBase l s c st'.data →
      bytesOf st'.data.dmem (r.off a) 344 = bytesOf st.data.dmem (r.off b) 344 →
      SameOutside st.data.dmem st'.data.dmem (r.CallOut st.data a 344 0) →
      Eventually (step1 NativeRustcArm.Host.exe) R st') :
    Eventually (step1 NativeRustcArm.Host.exe) R st :=
  NativeRustcArm.Eventually.bind (Spec.apply hc.1 hpc.1
    (r.memcpy_pre hpre h.2.2.1 h0 h1 h2 (by omega) hb hd)) fun st' h' ↦ by
    obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 h'.2
    have := bytesOf_of_bytesAt hB
    rw [show (bytesOf st.data.dmem (r.off b) 344).length = 344 by simp [bytesOf]] at this
    exact cont st' (h'.1.trans hpc.2) (Run.EncBase.of_call r hpre h hS ha (by decide) hout) this
      hout

/-- **`Hasher::finalize(o, a)`** of hasher A into hasher B's place, from the invariant. -/
theorem call_finalize (r : Run) (hc : Callees) (hpre : r.Pre) {st : MachineState} {next : Int64}
    (hpc : st.pc = Labels.label NativeRustcArm.Common.Finalize.entryLabel ∧ retOf st.data = next) {l : Nat} {s : List UInt8}
    {c : UInt32} (h : r.EncBase l s c st.data)
    (h0 : Run.RegIs st.data .X0 (r.off 26768)) (h1 : Run.RegIs st.data .X1 (r.off 16400))
    {x : List UInt8} (hh : HasherHolds (bytesOf st.data.dmem (r.off 16400) 344) x)
    {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → r.EncBase l s c st'.data →
      BytesAt st'.data.dmem (r.off 26768) (hashBytes x) →
      Eventually (step1 NativeRustcArm.Host.exe) R st') :
    Eventually (step1 NativeRustcArm.Host.exe) R st :=
  NativeRustcArm.Eventually.bind (Spec.apply hc.2.2.2.1 hpc.1
    (r.finalize_pre hpre h.2.2.1 h0 h1 (by omega) (by omega) (.inr (by omega)) ⟨x, hh⟩))
    fun st' h' ↦ by
    obtain ⟨hD, hout, hS⟩ := r.finalize_out h0 h1 h'.2
    rw [finalize_eq hh] at hD
    exact cont st' (h'.1.trans hpc.2)
      (Run.EncBase.of_call r hpre h hS (.inr ⟨le_refl _, by omega⟩) (le_refl _) hout) hD

theorem goto {R : MachineState → Prop} {st : MachineState} {p : Int64} (hpc : st.pc = p)
    (h : Eventually (step1 NativeRustcArm.Host.exe) R ⟨st.data, p⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R st := by
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  exact h

theorem pc_step (r : Run) {j n j' : Nat} {b : List Directive} (hn : b.length = n)
    (hj : j + n = j') : NativeRustcArm.Host.addrOf (r.k + j + b.length) = r.pc j' := by
  rw [hn, Nat.add_assoc, hj]
  rfl

/-- The hasher's bytes, where a change of the frame's `a .. a + n` does not reach. -/
theorem hasher_kept (r : Run) (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {a n N o : Nat}
    (ha : a + n ≤ 29376) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) (ho : o + 344 ≤ 29376)
    (hd : o + 344 ≤ a ∨ a + n ≤ o) {x : List UInt8}
    (hh : HasherHolds (bytesOf m.dmem (r.off o) 344) x) :
    HasherHolds (bytesOf m'.dmem (r.off o) 344) x := by
  rwa [r.bytesOf_of_call hpre hF ha hN hout ho hd]

omit [NativeRustcArm.Host] in
theorem bytesOf_of_bytesAt' {d : DataMem} {a : BitVec 64} {bs : List UInt8} {n : Nat}
    (h : BytesAt d a bs) (hn : bs.length = n) : bytesOf d a n = bs := by
  subst hn
  exact bytesOf_of_bytesAt h

/-- **The encoder's digest**: from `b102`, hasher A new and the address at `24720`, the machine
reaches the codeword's loop with `x9 · 2⁶⁴ + x10` the big-endian number of `encode`'s digest. -/
theorem hash_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {l : Nat} {s : List UInt8} {c : UInt32} {m : MachineData}
    (h : r.EncBase l s c m) (hA : r.EncAdrs l m)
    (hh : HasherHolds (bytesOf m.dmem (r.off 16400) 344) []) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b110Offset ∧ r.EncBase l s c st.data ∧
      digest128 st.data = beNat (encodeDigest r.seed (r.key l) s c) ∧
      Run.RegIs st.data .X8 0 ∧ Run.RegIs st.data .X11 (r.off 26769)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b102Offset⟩ := by
  have hseed : bytesOf m.dmem (r.off 8208) 16 = r.seed :=
    bytesOf_of_bytesAt' (r.seed_at h.2.2.2.1) r.length_seed
  -- b102, update(A, PK.seed)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b102_in_code (List.cons_ne_nil _ _) b102_exec
    rfl h fun st1 hm1 hpc1 h1 ↦ ?_
  have hd1 : st1.data.dmem = m.dmem := hm1.dmem_eq (r.frame_wf hpre h.2.2.1 _) rfl
  refine call_update r hc hpre hpc1 h1 ((hm1.regs .X0 _ rfl).trans (r.ptr_eval0 m _ 16400))
    ((hm1.regs .X1 _ rfl).trans (r.ptr_eval0 m _ 8208)) (Run.x2_of (hm1.regs .X2 _ rfl) rfl
    (by decide)) (.inl ⟨le_refl _, le_refl _⟩) (by omega) (.inr (by omega)) (by rwa [hd1])
    fun st2 hpc2 h2 hH2 hout2 ↦ ?_
  rw [hd1, hseed, List.nil_append] at hH2
  have hA2 : r.EncAdrs l st2.data := r.bytesAt_of_call hpre h1.2.2.1 (by omega) (by decide) hout2
    (by rw [length_adrs7]; omega) (by rw [length_adrs7]; omega) (by rw [hd1]; exact hA)
  refine goto (hpc2.trans (pc_step r rfl rfl)) ?_
  -- b103, update(A, address)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b103_in_code (List.cons_ne_nil _ _) b103_exec
    rfl h2 fun st3 hm3 hpc3 h3 ↦ ?_
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (r.frame_wf hpre h2.2.2.1 _) rfl
  refine call_update r hc hpre hpc3 h3 ((hm3.regs .X0 _ rfl).trans (r.ptr_eval0 _ _ 16400))
    ((hm3.regs .X1 _ rfl).trans (r.ptr_eval0 _ _ 24720)) (Run.x2_of (hm3.regs .X2 _ rfl) rfl
    (by decide)) (.inl ⟨le_refl _, le_refl _⟩) (by omega) (.inl (by omega)) (by rwa [hd3])
    fun st4 hpc4 h4 hH4 hout4 ↦ ?_
  rw [hd3, bytesOf_of_bytesAt' hA2 (length_adrs7 _)] at hH4
  refine goto (hpc4.trans (pc_step r rfl rfl)) ?_
  -- b104, memcpy(B, A)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b104_in_code (List.cons_ne_nil _ _) b104_exec
    rfl h4 fun st5 hm5 hpc5 h5 ↦ ?_
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq (r.frame_wf hpre h4.2.2.1 _) rfl
  refine call_memcpy r hc hpre hpc5 h5 ((hm5.regs .X0 _ rfl).trans (r.ptr_eval0 _ _ 26768))
    ((hm5.regs .X1 _ rfl).trans (r.ptr_eval0 _ _ 16400)) (Run.x2_of (hm5.regs .X2 _ rfl) rfl
    (by decide)) (.inr ⟨le_refl _, le_refl _⟩) (by omega) (.inr (by omega))
    fun st6 hpc6 h6 hB6 hout6 ↦ ?_
  have hHB6 : HasherHolds (bytesOf st6.data.dmem (r.off 26768) 344)
      (r.seed ++ (r.key l).adrs 7) := by
    rw [hB6, hd5]; exact hH4
  refine goto (hpc6.trans (pc_step r rfl rfl)) ?_
  -- b105, update(B, message)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b105_in_code (List.cons_ne_nil _ _) b105_exec
    rfl h6 fun st7 hm7 hpc7 h7 ↦ ?_
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq (r.frame_wf hpre h6.2.2.1 _) rfl
  refine call_update r hc hpre hpc7 h7 ((hm7.regs .X0 _ rfl).trans (r.ptr_eval0 _ _ 26768))
    ((hm7.regs .X1 _ rfl).trans (r.ptr_eval0 _ _ 27792)) (Run.x2_of (hm7.regs .X2 _ rfl) rfl
    (by decide)) (.inr ⟨le_refl _, le_refl _⟩) (by omega) (.inl (by omega)) (by rwa [hd7])
    fun st8 hpc8 h8 hH8 hout8 ↦ ?_
  rw [hd7, bytesOf_of_bytesAt' h6.2.2.2.2.2.2.2.2.2.2.1 h6.2.1] at hH8
  refine goto (hpc8.trans (pc_step r rfl rfl)) ?_
  -- b106, memcpy(A, B)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b106_in_code (List.cons_ne_nil _ _) b106_exec
    rfl h8 fun st9 hm9 hpc9 h9 ↦ ?_
  have hd9 : st9.data.dmem = st8.data.dmem := hm9.dmem_eq (r.frame_wf hpre h8.2.2.1 _) rfl
  refine call_memcpy r hc hpre hpc9 h9 ((hm9.regs .X0 _ rfl).trans (r.ptr_eval0 _ _ 16400))
    ((hm9.regs .X1 _ rfl).trans (r.ptr_eval0 _ _ 26768)) (Run.x2_of (hm9.regs .X2 _ rfl) rfl
    (by decide)) (.inl ⟨le_refl _, le_refl _⟩) (by omega) (.inl (by omega))
    fun st10 hpc10 h10 hB10 hout10 ↦ ?_
  have hHA10 : HasherHolds (bytesOf st10.data.dmem (r.off 16400) 344)
      (r.seed ++ (r.key l).adrs 7 ++ s) := by
    rw [hB10, hd9]; exact hH8
  refine goto (hpc10.trans (pc_step r rfl rfl)) ?_
  -- b107, the counter written, update(A, counter)
  have hwf10 := r.frame_wf hpre h10.2.2.1 (fun _ ↦ 0)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b107_in_code (List.cons_ne_nil _ _) b107_exec
    rfl h10 fun st11 hm11 hpc11 h11 ↦ ?_
  have hout11 : SameOutside st10.data.dmem st11.data.dmem (r.CallOut st10.data 24720 4 0) :=
    SameOutside.mono (hm11.sameOutside hwf10) fun p hp' ↦
      .inl (r.written_inRange hpre (by omega) (by decide) hp')
  have hc11 : BytesAt st11.data.dmem (r.off 24720) (be32 c) := by
    have := hm11.bytesAt_write (r := 0) (b := r.base) (sz := 29376) rfl (by omega)
      (fun i hi ↦ findWrite_head hi)
    simp only [Sym.eval, Env.ofMachine_regs] at this
    rw [bytes_rev32, h10.2.2.2.2.2.2.2.2.2.2.2] at this
    exact this
  refine call_update r hc hpre hpc11 h11 ((hm11.regs .X0 _ rfl).trans (r.ptr_eval0 _ _ 16400))
    ((hm11.regs .X1 _ rfl).trans (r.ptr_eval0 _ _ 24720)) (Run.x2_of (hm11.regs .X2 _ rfl) rfl
    (by decide)) (.inl ⟨le_refl _, le_refl _⟩) (by omega) (.inl (by omega))
    (hasher_kept r hpre h10.2.2.1 (by omega) (Nat.zero_le _) hout11 (by omega) (.inl (by omega))
      hHA10)
    fun st12 hpc12 h12 hH12 hout12 ↦ ?_
  rw [bytesOf_of_bytesAt' (n := 4) hc11 rfl] at hH12
  refine goto (hpc12.trans (pc_step r rfl rfl)) ?_
  -- b108, finalize(B's place, A)
  refine enc_block r hp hpre Sphincs.SphincsVerify.b108_in_code (List.cons_ne_nil _ _) b108_exec
    rfl h12 fun st13 hm13 hpc13 h13 ↦ ?_
  have hd13 : st13.data.dmem = st12.data.dmem := hm13.dmem_eq (r.frame_wf hpre h12.2.2.1 _) rfl
  refine call_finalize r hc hpre hpc13 h13 ((hm13.regs .X0 _ rfl).trans (r.ptr_eval0 _ _ 26768))
    ((hm13.regs .X1 _ rfl).trans (r.ptr_eval0 _ _ 16400)) (by rwa [hd13])
    fun st14 hpc14 h14 hD14 ↦ ?_
  refine goto (hpc14.trans (pc_step r rfl rfl)) ?_
  -- b109, the digest's number
  refine enc_block r hp hpre Sphincs.SphincsVerify.b109_in_code (List.cons_ne_nil _ _) b109_exec
    rfl h14 fun st15 hm15 hpc15 h15 ↦ .done _ ⟨hpc15.trans (pc_step r rfl rfl), h15, ?_, ?_, ?_⟩
  · have hlen : (hashBytes (r.seed ++ (r.key l).adrs 7 ++ s ++ be32 c)).length = 32 :=
      length_hashBytes _
    have hA' := bytesAt_slice hD14 0 8 (by omega)
    have hB' := bytesAt_slice hD14 8 8 (by omega)
    rw [r.off_add] at hA' hB'
    unfold digest128
    rw [hm15.regs .X9 _ rfl, hm15.regs .X10 _ rfl]
    simp only [Sym.eval]
    have h8 : ∀ k, k + 8 ≤ 32 →
        (((hashBytes (r.seed ++ (r.key l).adrs 7 ++ s ++ be32 c)).drop k).take 8).length = 8 :=
      fun k hk ↦ by simp only [List.length_take, List.length_drop, hlen]; omega
    rw [Sym.Env.load_of_bytesAt (h8 0 (by decide)) hA',
      Sym.Env.load_of_bytesAt (h8 8 (by decide)) hB', beNat_split _ _ (h8 0 (by decide))
        (h8 8 (by decide)), List.drop_zero, ← List.take_add, encodeDigest]
  · exact hm15.regs .X8 _ rfl
  · exact (hm15.regs .X11 _ rfl).trans h14.2.2.2.2.2.2.2.1

end

end NativeRustcArm.SphincsVerifyProof
