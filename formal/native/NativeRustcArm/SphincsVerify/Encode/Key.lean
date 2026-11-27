module

public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.SphincsVerify.Encode.KeyEnv
public import NativeRustcArm.SphincsVerify.Encode.KeyMath
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The key and the encoder's address: `b92`

`b92` (`.LSphincsVerify_32`) computes layer `l`'s key from the index and
`LAYER_HEIGHTS`, spills the layer loop's words (`LayerSpills`), writes the encoder's address
`OtsKey::adrs(7)` at `16960`, loads the counter into W20 and calls `memset` on hasher A. For each
of the three layers the executor's result is checked by the kernel against its expected writes
(`b92Ok_all`); `b92_spec` runs the block and the call: the invariant `EncBase` with the
counter, the address at `16960` (`Run.EncAdrs`), hasher A new.
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs LeanVM.Protocol.KeccakHash NativeRustcArm.Sym

@[expose] public section

set_option Elab.async false

/-! ## The block, checked -/

/-- The index, loaded. -/
def idxS : Sym := .load 0 400 8
/-- Layer `l`'s height, loaded from `LAYER_HEIGHTS`. -/
def hS (l : Nat) : Sym := .load 1 (8 * l) 8
/-- The index without the layers below. -/
def eS (l : Nat) : Sym := .bin .lsrv .W64 idxS (.lit (shOf l))
/-- The key's leaf. -/
def leafS (l : Nat) : Sym :=
  .bin .bic .W64 (eS l) (.bin .lslv .W64 (.lit 18446744073709551615) (hS l))
/-- The key's tree. -/
def treeS (l : Nat) : Sym := .bin .lsrv .W64 (eS l) (hS l)
/-- The layer as a big-endian `u32`, in a register. -/
def revL (l : Nat) : Nat := (UnOp.apply .rev .W32 (BitVec.ofNat 64 l)).toNat

/-- The newest writes of `S` at `o .. o + n` in the frame are `v`'s bytes. -/
def wr (S : SState) (o n : Nat) (v : Sym) : Bool :=
  (List.range n).all fun i ↦ findWrite 0 (o + i) S.mem == some (v, i)

/-- `b92`'s start for layer `l`: `AtLayer`'s registers and the spilled layer pointer at `408`. -/
def s92 (l : Nat) : SState :=
  { init [(21616, true), (24, false)] (.ptr 0 0)
      [(.X10, .lit l), (.X8, .label NativeRustcArm.layerHeightsLabel),
        (.X11, .lit (4656 + 1028 * l)), (.X12, .lit 8), (.X23, .lit 16), (.X13, .lit 0x07000000),
        (.X22, .ptr 0 15936), (.X29, .ptr 0 21520)] [(NativeRustcArm.layerHeightsLabel, 1)] with
    mem := [⟨0, 408, 8, .ptr 0 ((5140 + 1028 * l : Nat) : Int)⟩] }

/-- `b92` for layer `l` as the executor runs it. -/
def b92Ok (l : Nat) : Bool :=
  match exec Sphincs.SphincsVerify.b92 (s92 l) with
  | some (S, x) =>
    x == .call NativeRustcArm.Common.Memset.entryLabel && S.reg .X0 == some (.ptr 0 8640) && S.reg .X1 == some (.lit 0) &&
      S.reg .X2 == some (.lit 344) && S.reg .X20 == some (.load 0 (6164 + 1028 * l) 4) &&
      S.sp == .ptr 0 0 && S.reg .X29 == some (.ptr 0 21520) &&
      S.reg .X22 == some (.ptr 0 15936) && S.reg .X21 == some (.reg .X21) &&
      S.reg .X24 == some (.reg .X24) && S.reg .X25 == some (.reg .X25) &&
      S.reg .X19 == some (.reg .X19) && S.reg .X27 == some (.reg .X27) &&
      Run.frameWrites S && Run.noWriteIn S 8 8 &&
      Run.noWriteIn S 392 16 && Run.noWriteIn S 448 7776 && Run.noWriteIn S 20032 16 &&
      wr S 16 8 (.lit (l + 1)) && wr S 24 8 (.lit (4656 + 1028 * (l + 1))) && wr S 32 8 (.lit l) &&
      wr S 40 8 (leafS l) && wr S 48 8 (hS l) &&
      wr S 408 8 (.ptr 0 ((5140 + 1028 * l : Nat) : Int)) &&
      wr S 424 4 (.un .rev .W32 (leafS l)) && wr S 432 4 (.lit (revL l)) &&
      wr S 440 8 (.un .rev .W64 (treeS l)) && wr S 16960 4 (.lit (revL l)) &&
      wr S 16964 4 (.lit 0) && wr S 16968 8 (.un .rev .W64 (treeS l)) &&
      wr S 16976 4 (.lit 117440512) && wr S 16980 4 (.un .rev .W32 (leafS l)) &&
      wr S 16984 8 (.lit 0)
  | none => false

theorem b92Ok_all : ∀ l < 3, b92Ok l = true := by decide +kernel

/-! ## Bytes -/

theorem wr_spec {S : SState} {o n : Nat} {v : Sym} (h : wr S o n v = true) :
    ∀ i < n, findWrite 0 (o + i) S.mem = some (v, i) := by
  intro i hi
  simp only [wr, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi

theorem bytesAt_append_of {d : DataMem} {a : BitVec 64} {p q : List UInt8} (hp : BytesAt d a p)
    (hq : BytesAt d (a + BitVec.ofNat 64 p.length) q) : BytesAt d a (p ++ q) := by
  intro i hi
  by_cases h : i < p.length
  · rw [List.getElem_append_left h]
    exact hp i h
  · rw [List.getElem_append_right (by omega)]
    have := hq (i - p.length) (by simp at hi; omega)
    rwa [BitVec.add_assoc, ← BitVec.ofNat_add, show p.length + (i - p.length) = i by omega] at this

theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- A counter's bytes, loaded as a word: the counter. -/
theorem le32_load (c : UInt32) :
    UInt32.ofNat (BitVec.ofInt 64 (Int.ofBytes (le32 c))).toNat = c := by
  have hx : (BitVec.ofNat 64 c.toNat).toNat = c.toNat := by
    rw [BitVec.toNat_ofNat]; have := c.toNat_lt; omega
  have hle : le32 c = (List.range 4).map (byteOf (BitVec.ofNat 64 c.toNat)) := by
    rw [show List.range 4 = [0, 1, 2, 3] from rfl]
    simp only [List.map_cons, List.map_nil, byteOf_eq_toUInt32 _ (show (0 : Nat) < 4 by decide),
      byteOf_eq_toUInt32 _ (show (1 : Nat) < 4 by decide),
      byteOf_eq_toUInt32 _ (show (2 : Nat) < 4 by decide),
      byteOf_eq_toUInt32 _ (show (3 : Nat) < 4 by decide), hx, UInt32.ofNat_toNat]
    simp [le32, be32]
  have hb := Sym.ofBytes_byteOf (BitVec.ofNat 64 c.toNat) 0 4
  simp only [Nat.zero_add] at hb
  rw [hle, hb, BitVec.ofInt_natCast, BitVec.toNat_ofNat, hx]
  have := c.toNat_lt
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat']
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

theorem lit_word (n : Nat) :
    (List.range 8).map (byteOf (BitVec.ofNat 64 n)) = wordBytes n.toUInt64 :=
  bytes_word _

/-! ## The state after the block and `memset` -/

namespace Run

variable (r : Run) [Labels]

/-- The encoder's address at `16960`. -/
def EncAdrs (l : Nat) (m : MachineData) : Prop := BytesAt m.dmem (r.off 16960) ((r.key l).adrs 7)

/-- A write of the block, in the frame. -/
theorem write_at {m m' : MachineData} {S : SState} (hm : Match (r.envL m) S m') {o n : Nat}
    {v : Sym} (hle : o + n ≤ 21616) (h : wr S o n v = true) :
    BytesAt m'.dmem (r.off o) ((List.range n).map (byteOf (v.eval (r.envL m)))) :=
  hm.bytesAt_write (r := 0) (b := r.base) (sz := 21616) rfl hle (wr_spec h)

omit [Labels] in
theorem bytesAt_app_off {d : DataMem} {o o' : Nat} {p q : List UInt8} (hp : BytesAt d (r.off o) p)
    (hq : BytesAt d (r.off o') q) (ho : o' = o + p.length) : BytesAt d (r.off o) (p ++ q) :=
  bytesAt_append_of hp (by rw [off_add, ← ho]; exact hq)

/-- A frame pointer's value. -/
theorem ptr_eval (m : MachineData) (o : Nat) : (Sym.ptr 0 (o : Int)).eval (r.envL m) = r.off o := by
  show r.base + BitVec.ofInt 64 (o : Int) = r.base + BitVec.ofNat 64 o
  rw [BitVec.ofInt_natCast]

end Run


theorem zeros4 : (List.range 4).map (byteOf (BitVec.ofNat 64 0)) = [0, 0, 0, 0] := by decide
theorem zeros8 : (List.range 8).map (byteOf (BitVec.ofNat 64 0)) = List.replicate 8 0 := by decide
theorem type7 : (List.range 4).map (byteOf (BitVec.ofNat 64 117440512)) = be32 7 := by decide

theorem be32_layer {l : Nat} (hl : l < 3) :
    (List.range 4).map (byteOf (BitVec.ofNat 64 (revL l))) = be32 l.toUInt32 := by
  rw [revL, ofNat_toNat_self, bytes_rev32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

variable [ElfHost]

/-- **`b92` and `memset`**: from layer `l`'s state, the machine reaches `b93` with the
invariant (the counter in W20), the encoder's address at `16960` and hasher A new. -/
theorem b92_spec (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees)
    (hpre : r.Pre) {l : Nat} {s : List UInt8} {m : MachineData} (h : r.AtLayer l s m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b93Offset ∧
      r.EncBase l s (r.layerSig l).counter st.data ∧ r.EncAdrs l st.data ∧
      Keccak.HasherHolds (bytesOf st.data.dmem (r.off 8640) 344) []) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b92Offset⟩ := by
  obtain ⟨hl, hs, hF, hI, h10, h8, h11, h12, h23, h13, h22, h19, h21, h24, h25, h27, hsm, h8s,
    h400, h408⟩ := h
  have hok := b92Ok_all l hl
  rw [b92Ok] at hok
  rcases hx : exec Sphincs.SphincsVerify.b92 (s92 l) with _ | ⟨S, x⟩
  · rw [hx] at hok
    exact absurd hok Bool.false_ne_true
  rw [hx] at hok
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
  obtain ⟨rfl, hX0, hX1, hX2, hX20, hsp, h29, hX22, hX21, hX24, hX25, hX19, hX27, hfw, k8, k392, k448,
    k20032, w16, w24, w32, w40, w48, w408, w424, w432, w440, a0, a4, a8, a16, a20, a24⟩ := hok
  have hk := Sphincs.SphincsVerify.b92_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.envL_wf hpre hF
  have hm := r.match_frameL_word hpre hF (known := [(.X10, .lit l), (.X8, .label NativeRustcArm.layerHeightsLabel),
      (.X11, .lit (4656 + 1028 * l)), (.X12, .lit 8), (.X23, .lit 16), (.X13, .lit 0x07000000),
      (.X22, .ptr 0 15936), (.X29, .ptr 0 21520)])
    ⟨h10, h8, h11, h12, h23, h13,
      h22.trans (r.ptr_eval m 15936).symm, hF.2.1.trans (r.ptr_eval m 21520).symm, trivial⟩
    (o := 408) (v := .ptr 0 ((5140 + 1028 * l : Nat) : Int)) (by
      rw [r.ptr_eval m _, bytes_word]
      exact h408)
  refine Sym.exec_then_elf hk hx hwf hm fun st hm' hpc ↦ ?_
  have hF1 := Run.Frame.of_matchL r hpre hF hm' hwf hsp h29 hfw
  have hidx : (r.envL m).load 0 400 8 = r.idx.toBitVec := r.load_word rfl rfl h400
  have hH := r.load_height hpre hF hl
  have hleaf : (leafS l).eval (r.envL m) = BinOp.apply .bic .W64 (BinOp.apply .lsrv .W64
      r.idx.toBitVec (BitVec.ofNat 64 (shOf l))) (BinOp.apply .lslv .W64
      (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 (layerHeights.getD l 0))) := by
    simp only [leafS, eS, idxS, hS, Sym.eval, hidx, hH]
  have htree : (treeS l).eval (r.envL m) = BinOp.apply .lsrv .W64 (BinOp.apply .lsrv .W64
      r.idx.toBitVec (BitVec.ofNat 64 (shOf l))) (BitVec.ofNat 64 (layerHeights.getD l 0)) := by
    simp only [treeS, eS, idxS, hS, Sym.eval, hidx, hH]
  -- the writes
  have e16 := r.write_at hm' (by omega) w16
  have e24 := r.write_at hm' (by omega) w24
  have e32 := r.write_at hm' (by omega) w32
  have e40 := r.write_at hm' (by omega) w40
  have e48 := r.write_at hm' (by omega) w48
  have e408 := r.write_at hm' (by omega) w408
  have e424 := r.write_at hm' (by omega) w424
  have e432 := r.write_at hm' (by omega) w432
  have e440 := r.write_at hm' (by omega) w440
  have ea0 := r.write_at hm' (by omega) a0
  have ea4 := r.write_at hm' (by omega) a4
  have ea8 := r.write_at hm' (by omega) a8
  have ea16 := r.write_at hm' (by omega) a16
  have ea20 := r.write_at hm' (by omega) a20
  have ea24 := r.write_at hm' (by omega) a24
  simp only [Sym.eval] at e16 e24 e32 e48 e408 e424 e432 e440 ea0 ea4 ea8 ea16 ea20 ea24
  rw [bytes_word] at e16 e24 e32 e40 e48 e408
  rw [hleaf, key_leaf hl] at e40
  simp only [hS, Sym.eval] at e48
  rw [hH] at e48
  rw [show (r.envL m).base 0 + BitVec.ofInt 64 ((5140 + 1028 * l : Nat) : Int) =
    r.off (5140 + 1028 * l) from r.ptr_eval m _] at e408
  rw [hleaf, bytes_rev32, key_leaf32 hl] at e424 ea20
  rw [be32_layer hl] at e432 ea0
  rw [htree, bytes_rev64, key_tree] at e440 ea8
  rw [zeros4] at ea4
  rw [type7] at ea16
  rw [zeros8] at ea24
  have hadrs : r.EncAdrs l st.data := by
    unfold Run.EncAdrs
    rw [adrs7_eq]
    refine r.bytesAt_app_off (r.bytesAt_app_off (r.bytesAt_app_off (r.bytesAt_app_off
      (r.bytesAt_app_off ea0 ea4 rfl) ea8 rfl) ea16 rfl) ea20 rfl) ea24 rfl
  have kept := fun {o : Nat} {bs : List UInt8} ho hb hn ↦
    r.bytesAt_keptL (m := m) (m' := st.data) hpre hm' hwf hfw (o := o) (bs := bs) ho hb hn
  have hc20 : UInt32.ofNat (st.data.regs.getXReg .X20).toBitVec.toNat = (r.layerSig l).counter := by
    rw [hm'.regs .X20 _ hX20]
    have hcb := r.counter_at hI hl
    rw [show 5140 + 1028 * l + 1024 = 6164 + 1028 * l by omega] at hcb
    show UInt32.ofNat ((r.envL m).load 0 (6164 + 1028 * l) 4).toNat = _
    rw [Sym.Env.load_of_bytesAt (by simp [le32, be32]) hcb, le32_load]
  have hbase : r.EncBase l s (r.layerSig l).counter st.data := by
    unfold Run.EncBase Run.Inputs Run.LayerSpills
    refine ⟨hl, hs, hF1, ⟨kept (by rw [r.hpk]; omega) hI.1
      (noWriteIn_mono k448 (by omega) (by rw [r.hpk]; omega)),
      kept (by rw [r.length_sigMem']; omega) hI.2.1
        (noWriteIn_mono k448 (by omega) (by rw [r.length_sigMem'])),
      kept (by rw [length_wordBytes]; omega) hI.2.2
        (noWriteIn_mono k392 (by omega) (by rw [length_wordBytes]; omega))⟩,
      ⟨kept (by rw [length_wordBytes]; omega) h8s
        (noWriteIn_mono k8 (by omega) (by rw [length_wordBytes])), e16, e24, e32, e40, e48,
      kept (by rw [length_wordBytes]; omega) h400
        (noWriteIn_mono k392 (by omega) (by rw [length_wordBytes])), e408, e424, e432,
      e440⟩, ?_, ?_, ?_, ?_, ?_, ?_, kept (by rw [hs]; omega) hsm (by rw [hs]; exact k20032), hc20⟩
    · exact (hm'.regs .X22 _ hX22).trans (r.ptr_eval m 15936)
    · rw [Run.RegIs, hm'.regs .X21 _ hX21]; exact h21
    · rw [Run.RegIs, hm'.regs .X24 _ hX24]; exact h24
    · rw [Run.RegIs, hm'.regs .X25 _ hX25]; exact h25
    · rw [Run.RegIs, hm'.regs .X19 _ hX19]; exact h19
    · rw [Run.RegIs, hm'.regs .X27 _ hX27]; exact h27
  have hR0 : Run.RegIs st.data .X0 (r.off 8640) :=
    (hm'.regs .X0 _ hX0).trans (r.ptr_eval m 8640)
  have hR2 : st.data.regs.X2.toNat = 344 := by
    have := hm'.regs .X2 _ hX2
    exact congrArg BitVec.toNat this
  have hR1 : st.data.regs.X1 = 0 := UInt64.toBitVec_inj.mp (hm'.regs .X1 _ hX1)
  refine Sym.call_then_elf hpc hc.2.1 (r.memset_pre hpre hF1 hR0 hR2 (by decide))
    fun st' hpc' hpost ↦ .done _ ?_
  obtain ⟨hB, hout, hS⟩ := r.memset_out hR0 hR2 hpost
  refine ⟨by simpa only [Run.pc, Nat.add_assoc, NativeRustcArm.Sphincs.SphincsVerify.b92_next] using hpc',
    Run.EncBase.of_call r hpre hbase hS (.inl ⟨le_refl _, le_refl _⟩) (Nat.zero_le _) hout,
    r.bytesAt_of_call hpre hF1 (by omega) (Nat.zero_le _) hout
      (by rw [length_adrs7]; omega) (by rw [length_adrs7]; omega) hadrs, ?_⟩
  rw [hR1] at hB
  have := bytesOf_of_bytesAt hB
  rw [List.length_replicate] at this
  rw [this]
  exact Keccak.holds_new

end

end NativeRustcArm.SphincsVerifyProof
