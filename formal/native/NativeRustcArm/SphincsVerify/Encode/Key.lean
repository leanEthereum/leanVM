module

public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.SphincsVerify.Encode.KeyEnv
public import NativeRustcArm.SphincsVerify.Encode.KeyMath
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify.Part2

/-!
# The key and the encoder's address: `b101`

`b101` (`.LSphincsVerify_40`, directive 1306) computes layer `l`'s key from the index and
`LAYER_HEIGHTS`, spills the layer loop's words (`LayerSpills`), writes the encoder's address
`OtsKey::adrs(7)` at `24720`, loads the counter into W19 and calls `memset` on hasher A. For each
of the three layers the executor's result is checked by the kernel against its expected writes
(`b101Ok_all`); `b101_spec` runs the block and the call: the invariant `EncBase` with the
counter, the address at `24720` (`Run.EncAdrs`), hasher A new.
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs LeanVM.Protocol.KeccakHash NativeRustcArm.Sym

@[expose] public section

set_option Elab.async false

/-! ## The block, checked -/

/-- The index, loaded. -/
def idxS : Sym := .load 0 384 8
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

/-- `b101`'s start for layer `l`: `AtLayer`'s registers. -/
def s101 (l : Nat) : SState :=
  init [(29376, true), (24, false)] (.ptr 0 0)
    [(.X10, .lit l), (.X8, .label NativeRustcArm.layerHeightsLabel), (.X11, .ptr 0 ((12900 + 1028 * l : Nat) : Int)),
      (.X12, .lit (4656 + 1028 * l)), (.X13, .lit 8), (.X22, .lit 16), (.X14, .lit 0x07000000),
      (.X20, .ptr 0 21648), (.X29, .ptr 0 29280)] [(NativeRustcArm.layerHeightsLabel, 1)]

/-- `b101` for layer `l` as the executor runs it. -/
def b101Ok (l : Nat) : Bool :=
  match exec Sphincs.SphincsVerify.b101 (s101 l) with
  | some (S, x) =>
    x == .call NativeRustcArm.Common.Memset.entryLabel && S.reg .X0 == some (.ptr 0 16400) && S.reg .X1 == some (.lit 0) &&
      S.reg .X2 == some (.lit 344) && S.reg .X19 == some (.load 0 (13924 + 1028 * l) 4) &&
      S.sp == .ptr 0 0 && S.reg .X29 == some (.ptr 0 29280) &&
      S.reg .X20 == some (.ptr 0 21648) && S.reg .X21 == some (.reg .X21) &&
      S.reg .X23 == some (.reg .X23) && S.reg .X25 == some (.reg .X25) &&
      S.reg .X26 == some (.reg .X26) && Run.frameWrites S && Run.noWriteIn S 0 8 &&
      Run.noWriteIn S 376 16 && Run.noWriteIn S 8208 7776 && Run.noWriteIn S 27792 16 &&
      wr S 8 8 (.lit (l + 1)) && wr S 16 8 (.lit (4656 + 1028 * (l + 1))) && wr S 24 8 (.lit l) &&
      wr S 32 8 (leafS l) && wr S 40 8 (hS l) &&
      wr S 392 8 (.ptr 0 ((12900 + 1028 * l : Nat) : Int)) &&
      wr S 408 4 (.un .rev .W32 (leafS l)) && wr S 416 4 (.lit (revL l)) &&
      wr S 424 8 (.un .rev .W64 (treeS l)) && wr S 24720 4 (.lit (revL l)) &&
      wr S 24724 4 (.lit 0) && wr S 24728 8 (.un .rev .W64 (treeS l)) &&
      wr S 24736 4 (.lit 117440512) && wr S 24740 4 (.un .rev .W32 (leafS l)) &&
      wr S 24744 8 (.lit 0)
  | none => false

theorem b101Ok_all : ∀ l < 3, b101Ok l = true := by decide +kernel

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

/-- The encoder's address at `24720`. -/
def EncAdrs (l : Nat) (m : MachineData) : Prop := BytesAt m.dmem (r.off 24720) ((r.key l).adrs 7)

/-- A write of the block, in the frame. -/
theorem write_at {m m' : MachineData} {S : SState} (hm : Match (r.envL m) S m') {o n : Nat}
    {v : Sym} (hle : o + n ≤ 29376) (h : wr S o n v = true) :
    BytesAt m'.dmem (r.off o) ((List.range n).map (byteOf (v.eval (r.envL m)))) :=
  hm.bytesAt_write (r := 0) (b := r.base) (sz := 29376) rfl hle (wr_spec h)

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

variable [NativeRustcArm.Host]

/-- **`b101` and `memset`**: from layer `l`'s state, the machine reaches `b102` with the
invariant (the counter in W19), the encoder's address at `24720` and hasher A new. -/
theorem b101_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {l : Nat} {s : List UInt8} {m : MachineData} (h : r.AtLayer l s m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b102Offset ∧
      r.EncBase l s (r.layerSig l).counter st.data ∧ r.EncAdrs l st.data ∧
      Keccak.HasherHolds (bytesOf st.data.dmem (r.off 16400) 344) []) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b101Offset⟩ := by
  obtain ⟨hl, hs, hF, hI, h10, h8, h11, h12, h13, h22, h14, h20, h26, h21, h23, h25, hsm, h0,
    h384⟩ := h
  have hok := b101Ok_all l hl
  rw [b101Ok] at hok
  rcases hx : exec Sphincs.SphincsVerify.b101 (s101 l) with _ | ⟨S, x⟩
  · rw [hx] at hok
    exact absurd hok Bool.false_ne_true
  rw [hx] at hok
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
  obtain ⟨rfl, hX0, hX1, hX2, hX19, hsp, h29, hX20, hX21, hX23, hX25, hX26, hfw, k0, k376, k8208,
    k27792, w8, w16, w24, w32, w40, w392, w408, w416, w424, a0, a4, a8, a16, a20, a24⟩ := hok
  have hk := Sphincs.SphincsVerify.b101_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hwf := r.envL_wf hpre hF
  have hm := r.match_frameL hpre hF (known := [(.X10, .lit l), (.X8, .label NativeRustcArm.layerHeightsLabel),
      (.X11, .ptr 0 ((12900 + 1028 * l : Nat) : Int)), (.X12, .lit (4656 + 1028 * l)),
      (.X13, .lit 8), (.X22, .lit 16), (.X14, .lit 0x07000000), (.X20, .ptr 0 21648),
      (.X29, .ptr 0 29280)])
    ⟨h10, h8, h11.trans (r.ptr_eval m _).symm, h12, h13, h22, h14,
      h20.trans (r.ptr_eval m 21648).symm, hF.2.1.trans (r.ptr_eval m 29280).symm, trivial⟩
  refine Sym.exec_then hk hx hwf hm fun st hm' hpc ↦ ?_
  have hF1 := Run.Frame.of_matchL r hpre hF hm' hwf hsp h29 hfw
  have hidx : (r.envL m).load 0 384 8 = r.idx.toBitVec := r.load_word rfl rfl h384
  have hH := r.load_height hpre hF hl
  have hleaf : (leafS l).eval (r.envL m) = BinOp.apply .bic .W64 (BinOp.apply .lsrv .W64
      r.idx.toBitVec (BitVec.ofNat 64 (shOf l))) (BinOp.apply .lslv .W64
      (BitVec.ofNat 64 18446744073709551615) (BitVec.ofNat 64 (layerHeights.getD l 0))) := by
    simp only [leafS, eS, idxS, hS, Sym.eval, hidx, hH]
  have htree : (treeS l).eval (r.envL m) = BinOp.apply .lsrv .W64 (BinOp.apply .lsrv .W64
      r.idx.toBitVec (BitVec.ofNat 64 (shOf l))) (BitVec.ofNat 64 (layerHeights.getD l 0)) := by
    simp only [treeS, eS, idxS, hS, Sym.eval, hidx, hH]
  -- the writes
  have e8 := r.write_at hm' (by omega) w8
  have e16 := r.write_at hm' (by omega) w16
  have e24 := r.write_at hm' (by omega) w24
  have e32 := r.write_at hm' (by omega) w32
  have e40 := r.write_at hm' (by omega) w40
  have e392 := r.write_at hm' (by omega) w392
  have e408 := r.write_at hm' (by omega) w408
  have e416 := r.write_at hm' (by omega) w416
  have e424 := r.write_at hm' (by omega) w424
  have ea0 := r.write_at hm' (by omega) a0
  have ea4 := r.write_at hm' (by omega) a4
  have ea8 := r.write_at hm' (by omega) a8
  have ea16 := r.write_at hm' (by omega) a16
  have ea20 := r.write_at hm' (by omega) a20
  have ea24 := r.write_at hm' (by omega) a24
  simp only [Sym.eval] at e8 e16 e24 e40 e392 e408 e416 e424 ea0 ea4 ea8 ea16 ea20 ea24
  rw [bytes_word] at e8 e16 e24 e32 e40 e392
  rw [hleaf, key_leaf hl] at e32
  simp only [hS, Sym.eval] at e40
  rw [hH] at e40
  rw [show (r.envL m).base 0 + BitVec.ofInt 64 ((12900 + 1028 * l : Nat) : Int) =
    r.off (12900 + 1028 * l) from r.ptr_eval m _] at e392
  rw [hleaf, bytes_rev32, key_leaf32 hl] at e408 ea20
  rw [be32_layer hl] at e416 ea0
  rw [htree, bytes_rev64, key_tree] at e424 ea8
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
  have hc19 : UInt32.ofNat (st.data.regs.getXReg .X19).toBitVec.toNat = (r.layerSig l).counter := by
    rw [hm'.regs .X19 _ hX19]
    have hcb := r.counter_at hI hl
    rw [show 12900 + 1028 * l + 1024 = 13924 + 1028 * l by omega] at hcb
    show UInt32.ofNat ((r.envL m).load 0 (13924 + 1028 * l) 4).toNat = _
    rw [Sym.Env.load_of_bytesAt (by simp [le32, be32]) hcb, le32_load]
  have hbase : r.EncBase l s (r.layerSig l).counter st.data := by
    unfold Run.EncBase Run.Inputs Run.LayerSpills
    refine ⟨hl, hs, hF1, ⟨kept (by rw [r.length_pkBytes]; omega) hI.1
      (noWriteIn_mono k8208 (by omega) (by rw [r.length_pkBytes]; omega)),
      kept (by rw [r.length_sigMem']; omega) hI.2.1
        (noWriteIn_mono k8208 (by omega) (by rw [r.length_sigMem'])),
      kept (by rw [length_wordBytes]; omega) hI.2.2
        (noWriteIn_mono k376 (by omega) (by rw [length_wordBytes]; omega))⟩,
      ⟨kept (by rw [length_wordBytes]; omega) h0
        (noWriteIn_mono k0 (by omega) (by rw [length_wordBytes])), e8, e16, e24, e32, e40,
      kept (by rw [length_wordBytes]; omega) h384
        (noWriteIn_mono k376 (by omega) (by rw [length_wordBytes])), e392, e408, e416,
      e424⟩, ?_, ?_, ?_, ?_, ?_, kept (by rw [hs]; omega) hsm (by rw [hs]; exact k27792), hc19⟩
    · exact (hm'.regs .X20 _ hX20).trans (r.ptr_eval m 21648)
    · rw [Run.RegIs, hm'.regs .X21 _ hX21]; exact h21
    · rw [Run.RegIs, hm'.regs .X23 _ hX23]; exact h23
    · rw [Run.RegIs, hm'.regs .X25 _ hX25]; exact h25
    · rw [Run.RegIs, hm'.regs .X26 _ hX26]; exact h26
  have hR0 : Run.RegIs st.data .X0 (r.off 16400) :=
    (hm'.regs .X0 _ hX0).trans (r.ptr_eval m 16400)
  have hR2 : st.data.regs.X2.toNat = 344 := by
    have := hm'.regs .X2 _ hX2
    exact congrArg BitVec.toNat this
  have hR1 : st.data.regs.X1 = 0 := UInt64.toBitVec_inj.mp (hm'.regs .X1 _ hX1)
  refine Sym.call_then hpc hc.2.1 (r.memset_pre hpre hF1 hR0 hR2 (by decide))
    fun st' hpc' hpost ↦ .done _ ?_
  obtain ⟨hB, hout, hS⟩ := r.memset_out hR0 hR2 hpost
  refine ⟨by simpa only [Run.pc, Nat.add_assoc, NativeRustcArm.Sphincs.SphincsVerify.b101_next] using hpc',
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
