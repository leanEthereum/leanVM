module

public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names

public import NativeRustcArm.SphincsVerify.Frame
public import NativeRustc.Sphincs.ParseBytes
public import NativeRustcArm.LayerRead.Glue

/-!
# What the parse's proof shares

- frame bytes kept by a change elsewhere in the frame (`keep`), a block's writes inside an
  interval of its region 0 (`sameOutside_hull`), bytes a block stored from loads (`copies`,
  `copy`);
- registers stored whole (`holdsReg`, `bytesAt_reg`), loaded words (`load_word`), words' bytes
  (`bytesAt_words`), region pointers (`eval_ptr`, `eval_ptr_off`);
- the frame before the invariant holds (`frame_mapped0`), external `pk` / `sig` input slices and
  environments (`wf_frame_pk`, `wf_frame_sig`, `wf_frame2`);
- `memcpy` and `memset` between frame offsets (`memcpy_frame`, `memset_frame`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash Native.Keccak

public section

theorem off_add (r : Run) (a i : Nat) : r.off a + BitVec.ofNat 64 i = r.off (a + i) := by
  unfold Run.off
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Bytes kept -/

section
variable (r : Run) [Labels]

/-- **Frame bytes kept** by a change in another range of the frame. -/
theorem keep (hpre : r.Pre) {d d' : DataMem} {o a n L : Nat} {bs : List UInt8}
    (h : BytesAt d (r.off o) bs) (hs : SameOutside d d' (InRange (r.off a) n)) (hl : bs.length = L)
    (hd : o + L ≤ a ∨ a + n ≤ o) (ho : o + L ≤ 21616) (ha : a + n ≤ 21616) :
    BytesAt d' (r.off o) bs :=
  bytesAt_of_sameOutside h hs fun i hi hin => by
    subst hl
    have hb := r.base_toNat hpre
    have := r.m0.regs.SP.toNat_lt
    rw [off_add, Sym.inRange_iff (by rw [r.off_toNat hpre (by omega)]; omega),
      r.off_toNat hpre (by omega), r.off_toNat hpre (by omega)] at hin
    omega

/-- A change in the frame's range `a .. a + n` before the saved registers keeps the invariant. -/
theorem inRange_off' (hpre : r.Pre) {a n : Nat} (ha : a + n ≤ 21520) :
    ∀ p, InRange (r.off a) n p → r.StackArea p ∧ ¬InRange (r.off 21520) 96 p :=
  fun _ h => r.inRange_off hpre ha h

end

/-! ## After a block -/

section
variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **A block's writes in an interval of region 0**: memory changed only there. -/
theorem sameOutside_hull (hm : Match env S m) (hwf : env.WF) {B : BitVec 64} {sz lo hi : Nat}
    (hb : env.regions[0]? = some (B, sz)) (hhi : hi ≤ sz)
    (hall : S.mem.all (fun w => w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) =
      true) :
    SameOutside env.mem0 m.dmem (InRange (B + BitVec.ofNat 64 lo) (hi - lo)) := by
  have hnw := hwf.noWrap 0 B sz hb
  intro p hp
  apply hm.get?_mem0 hwf
  rintro ⟨w, hw, b, sz', hb', h1, h2⟩
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨⟨hr, hlo⟩, hhi'⟩ := this
  rw [hr, hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  apply hp
  rw [Sym.inRange_iff (by rw [Sym.toNat_add_ofNat _ _ (by omega)]; omega),
    Sym.toNat_add_ofNat _ _ (by omega)]
  omega

/-- A region pointer's value. -/
theorem eval_ptr {m : MachineData} {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {i : Nat} {b : BitVec 64} {n : Nat} (h : regions[i]? = some (b, n)) (o : Int) :
    Sym.eval (Env.ofMachine m regions vars) (.ptr i o) = b + BitVec.ofInt 64 o := by
  show Env.base _ i + _ = _
  rw [Env.base_ofMachine m regions vars h]

/-- A region pointer at a nonnegative offset. -/
theorem eval_ptr_nat {m : MachineData} {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {i : Nat} {b : BitVec 64} {n : Nat} (h : regions[i]? = some (b, n)) (o : Nat) :
    Sym.eval (Env.ofMachine m regions vars) (.ptr i (o : Int)) = b + BitVec.ofNat 64 o := by
  rw [eval_ptr h, BitVec.ofInt_natCast]

/-- A pointer into a frame range. -/
theorem eval_ptr_off (r : Run) {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {i a n : Nat} (h : regions[i]? = some (r.off a, n)) (o : Nat) :
    Sym.eval (Env.ofMachine m regions vars) (.ptr i (o : Int)) = r.off (a + o) := by
  rw [eval_ptr h, BitVec.ofInt_natCast, off_add]

/-- Byte `i` of region `r` holds the byte at `o' + i` of region `r'` that a load read. -/
@[expose] def copies (ws : List Write) (r o r' o' n : Nat) : Bool :=
  (List.range n).all fun i =>
    match findWrite r (o + i) ws with
    | some (.load r'' off k, u) => r'' == r' && off + u == o' + i && decide (u < k) && decide (k ≤ 8)
    | _ => false

/-- **Bytes stored from loads**: where the newest write of each byte of `o .. o + n` in region
`r` is a load of the bytes `o' .. o' + n` of region `r'` (`copies`), they hold what those held. -/
theorem copy (hm : Match env S m) {r o r' o' n : Nat} {B : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (B, sz)) (hle : o + n ≤ sz) (hc : copies S.mem r o r' o' n = true)
    {bs : List UInt8} (hl : bs.length = n) (h : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 o') bs) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) bs := by
  intro i hi
  have hc := List.all_eq_true.mp hc i (List.mem_range.mpr (hl ▸ hi))
  rw [addr_add, hm.mem r B sz hb (o + i) (by omega)]
  unfold memByte
  split at hc
  · rename_i r'' off k u hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hoff⟩, hu⟩, hk⟩ := hc
    rw [hf]
    simp only [Sym.eval, Option.some.injEq]
    rw [byteOf_load hu hk, hoff, ← addr_add, h i hi]
    rfl
  · cases hc

/-- The 8 bytes at `o` of region `r` are register `x`'s, stored whole. -/
@[expose] def holdsReg (ws : List Write) (r o : Nat) (x : XReg) : Bool :=
  (List.range 8).all fun i =>
    match findWrite r (o + i) ws with
    | some (.reg y, u) => y == x && u == i
    | _ => false

omit [Labels] in
theorem getElem_wordBytes (v : BitVec 64) {i : Nat} (hi : i < (wordBytes (UInt64.ofBitVec v)).length) :
    (wordBytes (UInt64.ofBitVec v))[i] = byteOf v i := by
  have h := regBytes_eq_wordBytes v
  have hl : i < (regBytes v).length := by rw [h]; exact hi
  simp only [← h, regBytes, List.getElem_map, List.getElem_range]

/-- **A register stored whole**: its bytes. -/
theorem bytesAt_reg (hm : Match env S m) {r o : Nat} {B : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (B, sz)) (hle : o + 8 ≤ sz) {x : XReg}
    (hc : holdsReg S.mem r o x = true) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) (wordBytes (UInt64.ofBitVec (env.regs x))) := by
  intro i hi
  have hi8 : i < 8 := by rwa [length_wordBytes] at hi
  have hc := List.all_eq_true.mp hc i (List.mem_range.mpr hi8)
  rw [addr_add, hm.mem r B sz hb (o + i) (by omega)]
  unfold memByte
  split at hc
  · rename_i y u hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hy, rfl⟩ := hc
    cases XReg.eq_of_beq hy
    rw [hf, getElem_wordBytes]
    rfl
  · cases hc

omit [Labels] in
/-- An 8-byte load of a word's bytes is the word. -/
theorem load_word {r o : Nat} {x : UInt64}
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o) (wordBytes x)) :
    env.load r o 8 = x.toBitVec := by
  rw [Env.load_of_bytesAt (length_wordBytes x) h]
  have := ofBytes_regBytes x.toBitVec
  rwa [regBytes_eq_wordBytes] at this

omit [Labels] in
/-- Words' bytes from each word's. -/
theorem bytesAt_words {d : DataMem} :
    ∀ (ws : List UInt64) {a : BitVec 64},
      (∀ i (h : i < ws.length), BytesAt d (a + BitVec.ofNat 64 (8 * i)) (wordBytes ws[i])) →
      BytesAt d a (wordsBytes ws)
  | [], _, _ => fun i hi => by simp [wordsBytes] at hi
  | w :: ws, a, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, List.getElem_cons_zero] at h0
    rw [show a + BitVec.ofNat 64 0 = a by simp] at h0
    have : wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws := rfl
    rw [this]
    refine BytesAt.append h0 (bytesAt_words ws fun i hi => ?_)
    have := h (i + 1) (by simp; omega)
    rw [List.getElem_cons_succ] at this
    rw [length_wordBytes, addr_add, show 8 + 8 * i = 8 * (i + 1) by omega]
    exact this

end

/-! ## Sub-slices and environments -/

theorem bytesAt_sub {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) {k n : Nat}
    (hk : k + n ≤ bs.length) : BytesAt d (a + BitVec.ofNat 64 k) (slice bs k n) := by
  intro i hi
  have hl : (slice bs k n).length = n := by simp [slice]; omega
  rw [addr_add, h (k + i) (by omega)]
  simp [slice]

section
variable (r : Run) [Labels]

/-- The saved registers are in the stack area. -/
theorem saved_area (hpre : r.Pre) {p : BitVec 64} (h : InRange (r.off 21520) 96 p) : r.StackArea p := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have hs := r.off_toNat hpre (a := 21520) (by decide)
  rw [Sym.inRange_iff (by rw [hs]; omega), hs] at h
  rw [r.stackArea_iff hpre]
  omega

/-- **The frame's bytes** `a .. a + n` are mapped in a state keeping the entry's, and do not wrap. -/
theorem frame_mapped0 (hpre : r.Pre) {d : DataMem} (hk : Kept r.m0.dmem d) {a n : Nat}
    (h : a + n ≤ 21616) : Mapped d (r.off a) n ∧ NoWrap (r.off a) n := by
  have hb := r.base_toNat hpre
  have hw : (r.m0.regs.SP.toBitVec - BitVec.ofNat 64 sphincsStack).toNat + 576 = r.base.toNat :=
    r.below_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have ho := r.off_toNat hpre (a := a) (by omega)
  refine ⟨fun i hi ↦ hk _ ?_, by unfold NoWrap; omega⟩
  have hm := hpre.1.2.2 (576 + a + i) (by simp only [Run.sphincsStack_eq]; omega)
  have he : r.m0.regs.SP.toBitVec - BitVec.ofNat 64 sphincsStack + BitVec.ofNat 64 (576 + a + i) =
      r.off a + BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    rw [Sym.toNat_add_ofNat (r.off a) i (by omega), ho, Sym.toNat_add_ofNat _ _ (by omega)]
    omega
  rwa [he] at hm

/-- The public key bytes in a state changed only in the stack area. -/
theorem bytesAt_pk (hpre : r.Pre) {d : DataMem} (hS : SameOutside r.m0.dmem d r.StackArea) :
    BytesAt d r.pkPtr r.pkBytes := by
  obtain ⟨h, hw, hA⟩ := r.pre_pk hpre
  exact bytesAt_of_sameOutside h hS fun _ hi ↦ r.not_area_of_apart hpre (r.hpk ▸ hA) (r.hpk ▸ hw) hi

/-- The raw signature bytes in a state changed only in the stack area. -/
theorem bytesAt_sig (hpre : r.Pre) {d : DataMem} (hS : SameOutside r.m0.dmem d r.StackArea) :
    BytesAt d r.sigPtr r.sigBytes := by
  obtain ⟨h, hw, hA⟩ := r.pre_sig hpre
  exact bytesAt_of_sameOutside h hS fun _ hi ↦ r.not_area_of_apart hpre (r.hsig ▸ hA) (r.hsig ▸ hw) hi

/-- A slice of the raw signature bytes `s .. s + k`. -/
theorem bytesAt_sig_sub (hpre : r.Pre) {d : DataMem} (hS : SameOutside r.m0.dmem d r.StackArea)
    {s k : Nat} (h : s + k ≤ 7740) :
    BytesAt d (r.sigPtr + BitVec.ofNat 64 s) (slice r.sigBytes s k) :=
  bytesAt_sub (bytesAt_sig r hpre hS) (by rw [r.hsig]; exact h)

/-- A slice of the raw signature bytes is mapped and does not wrap. -/
theorem sig_reg (hpre : r.Pre) {d : DataMem} (hS : SameOutside r.m0.dmem d r.StackArea)
    {s k : Nat} (h : s + k ≤ 7740) (hk : 0 < k) :
    Mapped d (r.sigPtr + BitVec.ofNat 64 s) k ∧ NoWrap (r.sigPtr + BitVec.ofNat 64 s) k := by
  have hw := (r.pre_sig hpre).2.1
  have hm := bytesAt_sig r hpre hS
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [addr_add, hm (s + i) (by rw [r.hsig]; omega)]
    rfl
  · unfold NoWrap at *
    rw [Sym.toNat_add_ofNat _ _ (by omega)]
    omega

/-- Frame bytes are apart from a slice of the raw signature. -/
theorem apart_sig (hpre : r.Pre) {a n s k : Nat} (ha : a + n ≤ 21616) (hs : s + k ≤ 7740)
    (hk : 0 < k) : Apart (r.off a) n (r.sigPtr + BitVec.ofNat 64 s) k := by
  have hA := (r.pre_sig hpre).2.2
  have hw := (r.pre_sig hpre).2.1
  have := r.below_toNat hpre
  have := r.off_toNat hpre (a := a) (by omega)
  unfold Apart NoWrap at *
  simp only [Run.sphincsStack_eq] at *
  rw [Sym.toNat_add_ofNat _ _ (by omega)]
  omega

/-- **A frame range and the public key** make a well-formed environment. -/
theorem wf_frame_pk (hpre : r.Pre) {m : MachineData}
    (hS : SameOutside r.m0.dmem m.dmem r.StackArea) (hK : Kept r.m0.dmem m.dmem) {a n : Nat}
    (ha : a + n ≤ 21616) (vars : Nat → BitVec 64) :
    (Env.ofMachine m [(r.off a, n), (r.pkPtr, 32)] vars).WF := by
  have hpk := bytesAt_pk r hpre hS
  have hpm : Mapped m.dmem r.pkPtr 32 := fun i hi ↦ by rw [hpk i (by rw [r.hpk]; exact hi)]; rfl
  exact Env.wf_of ⟨frame_mapped0 r hpre hK ha, ⟨hpm, (r.pre_pk hpre).2.1⟩, trivial⟩
    (List.pairwise_pair.mpr (r.apart_off_ext hpre ha (r.pre_pk hpre).2.2))

/-- **A frame range and a raw signature slice** make a well-formed environment. -/
theorem wf_frame_sig (hpre : r.Pre) {m : MachineData}
    (hS : SameOutside r.m0.dmem m.dmem r.StackArea) (hK : Kept r.m0.dmem m.dmem) {a n s k : Nat}
    (ha : a + n ≤ 21616) (hs : s + k ≤ 7740) (hk : 0 < k) (vars : Nat → BitVec 64) :
    (Env.ofMachine m [(r.off a, n), (r.sigPtr + BitVec.ofNat 64 s, k)] vars).WF :=
  Env.wf_of ⟨frame_mapped0 r hpre hK ha, sig_reg r hpre hS hs hk, trivial⟩
    (List.pairwise_pair.mpr (apart_sig r hpre ha hs hk))

/-- **Two apart frame ranges** make a well-formed environment. -/
theorem wf_frame2 (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a n a' n' : Nat}
    (ha : a + n ≤ 21616) (ha' : a' + n' ≤ 21616) (h : a + n ≤ a' ∨ a' + n' ≤ a)
    (vars : Nat → BitVec 64) :
    (Env.ofMachine m [(r.off a, n), (r.off a', n')] vars).WF :=
  Env.wf_of ⟨r.frame_mapped hpre hF ha, r.frame_mapped hpre hF ha', trivial⟩
    (List.pairwise_pair.mpr (r.apart_off hpre ha ha' h))

theorem off_aligned (hpre : r.Pre) {a : Nat} (ha : a ≤ 21616) (h16 : a % 16 = 0) :
    (r.off a).toNat % 16 = 0 := by
  rw [r.off_toNat hpre ha]
  have := r.base_aligned hpre
  omega

end

/-! ## Calls -/

section
variable (r : Run) [NativeRustcArm.Host]

/-- **`memcpy` between frame offsets**: from `b .. b + n` to `a .. a + n`, below the saved
registers. -/
theorem memcpy_frame (hpre : r.Pre) (hc : Callees) {env : Env} {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (hpc : PcOk env (.call NativeRustcArm.Common.Memcpy.entryLabel) next st) (hF : r.Frame st.data)
    {a b n : Nat} (h0 : (st.data.regs.getXReg .X0).toBitVec = r.off a)
    (h1 : (st.data.regs.getXReg .X1).toBitVec = r.off b) (h2 : (st.data.regs.getXReg .X2).toNat = n)
    (ha : a + n ≤ 21520) (hb : b + n ≤ 21616) (hab : a + n ≤ b ∨ b + n ≤ a)
    (cont : ∀ st', st'.pc = next → r.Frame st'.data → Saved st.data st'.data →
      BytesAt st'.data.dmem (r.off a) (bytesOf st.data.dmem (r.off b) n) →
      SameOutside st.data.dmem st'.data.dmem (InRange (r.off a) n) → Eventually (step1 NativeRustcArm.Host.exe) R st') :
    Eventually (step1 NativeRustcArm.Host.exe) R st := by
  have h0' : st.data.regs.X0.toBitVec = r.off a := h0
  have h1' : st.data.regs.X1.toBitVec = r.off b := h1
  have h2' : st.data.regs.X2.toNat = n := h2
  obtain ⟨hma, hwa⟩ := r.frame_mapped hpre hF (a := a) (n := n) (by omega)
  obtain ⟨hmb, hwb⟩ := r.frame_mapped hpre hF (a := b) (n := n) hb
  refine call_then hpc hc.1 ?_ fun st' hpc' ⟨_, hbytes, hout, hS⟩ => ?_
  · simp only [MemcpyPre, h0', h1', h2']
    exact ⟨hma, hmb, hwa, hwb, r.apart_off hpre (by omega) hb hab⟩
  · simp only [h0', h1', h2'] at hbytes hout
    exact cont st' hpc' (hF.of_post hS hout (inRange_off' r hpre ha)) hS hbytes hout

/-- **`memset` of frame offsets** `a .. a + n`, below the saved registers. -/
theorem memset_frame (hpre : r.Pre) (hc : Callees) {env : Env} {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (hpc : PcOk env (.call NativeRustcArm.Common.Memset.entryLabel) next st) (hF : r.Frame st.data)
    {a n : Nat} (h0 : (st.data.regs.getXReg .X0).toBitVec = r.off a)
    (h2 : (st.data.regs.getXReg .X2).toNat = n) (ha : a + n ≤ 21520)
    (cont : ∀ st', st'.pc = next → r.Frame st'.data → Saved st.data st'.data →
      SameOutside st.data.dmem st'.data.dmem (InRange (r.off a) n) → Eventually (step1 NativeRustcArm.Host.exe) R st') :
    Eventually (step1 NativeRustcArm.Host.exe) R st := by
  have h0' : st.data.regs.X0.toBitVec = r.off a := h0
  have h2' : st.data.regs.X2.toNat = n := h2
  obtain ⟨hma, hwa⟩ := r.frame_mapped hpre hF (a := a) (n := n) (by omega)
  refine call_then hpc hc.2.1 ?_ fun st' hpc' ⟨_, _, hout, hS⟩ => ?_
  · simp only [MemsetPre, h0', h2']
    exact ⟨hma, hwa⟩
  · simp only [h0', h2'] at hout
    exact cont st' hpc' (hF.of_post hS hout (inRange_off' r hpre ha)) hS hout

end

end

end NativeRustcArm.SphincsVerifyProof.Parse
