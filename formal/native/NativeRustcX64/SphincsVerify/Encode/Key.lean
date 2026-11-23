module

public import NativeRustcX64.Code.Common.Memset.Names
public import NativeRustcX64.Rodata.Names

public import NativeRustcX64.SphincsVerify.Encode.KeyEnv
public import NativeRustcX64.SphincsVerify.Encode.KeyMath

/-!
# The key and the encoder's address: `b104`

`b104` (`.LSphincsVerify_38`, directive 1129) computes layer `l`'s key from the index and
`LAYER_HEIGHTS`, spills the layer loop's words (`LayerSpills`), writes the encoder's address
`OtsKey::adrs(7)` at `2048`, loads the counter into EBX and calls `memset` on hasher A. For each
of the three layers the executor's result is checked by the kernel against its expected writes
(`b104Ok_all`); `b104_spec` runs the block and the call: the invariant `EncBase` with the
counter, the address at `2048` (`Run.EncAdrs`), hasher A new.
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs LeanVM.Protocol.KeccakHash NativeRustcX64.Sym

@[expose] public section

set_option Elab.async false

/-! ## The block, checked -/

/-- The index, loaded. -/
def idxS : Sym := .load 0 568 8
/-- Layer `l`'s height, loaded from `LAYER_HEIGHTS`. -/
def hS (l : Nat) : Sym := .load 2 (8 * l) 8
/-- The byte register `b104` sets to the layers below's heights, from `setne` (`b = l - 1`). -/
def cntS (b : Nat) : Sym :=
  let x : Sym := .bin .merge .W8 (.reg .rax) (.lit b)
  let y : Sym := .bin .merge .W8 x (.bin .shl .W8 x (.lit 3))
  .un (.zext .W8) .W32 (.bin .merge .W8 y (.bin .add .W8 (.lit 8) y))
/-- The shift count of the layers below. -/
def shS (l : Nat) : Sym := if l = 0 then .lit 0 else cntS (l - 1)
/-- The index without the layers below. -/
def eS (l : Nat) : Sym := .bin .shr .W64 idxS (shS l)
/-- The key's leaf. -/
def leafS (l : Nat) : Sym :=
  .bin .and .W32 (eS l) (.un .not .W32 (.bin .shl .W64 (.lit 18446744073709551615) (hS l)))
/-- The key's tree. -/
def treeS (l : Nat) : Sym := .bin .shr .W64 (eS l) (hS l)
/-- The key's leaf, big-endian. -/
def leafBE (l : Nat) : Sym := .un .trunc .W32 (.un .bswap .W32 (leafS l))
/-- The layer as a big-endian `u32`, in a register. -/
def revL (l : Nat) : Nat := (UnOp.apply .bswap .W32 (BitVec.ofNat 64 l)).toNat

/-- The newest writes of `S` at `o .. o + n` in the frame are `v`'s bytes. -/
def wr (S : SState) (o n : Nat) (v : Sym) : Bool :=
  (List.range n).all fun i ↦ findWrite 0 (o + i) S.mem == some (v, i)

/-- `b104`'s start for layer `l`: `AtLayer`'s registers, the chain values' address at `176`. -/
def s104 (l : Nat) : SState :=
  Run.frameStateL
    [(.rcx, .lit (4656 + 1028 * l)), (.rsi, .lit l), (.rdx, .label NativeRustcX64.layerHeightsLabel),
      (.rbx, .lit 0), (.r12, .ptr 0 4096), (.rbp, .ptr 0 576), (.r13, .ptr 0 2048),
      (.r15, .ptr 0 144)]
    [(.load 0 176 8, 0, ((25196 + 1028 * l : Nat) : Int))]

/-- `b104` for layer `l` as the executor runs it. -/
def b104Ok (l : Nat) : Bool :=
  match exec Sphincs.SphincsVerify.b104 (s104 l) with
  | some (S, x) =>
    x == .call NativeRustcX64.Common.Memset.entryLabel && S.reg .rdi == some (.ptr 0 4096) && S.reg .rsi == some (.lit 0) &&
      S.reg .rdx == some (.lit 344) && S.reg .rbx == some (.load 0 (26220 + 1028 * l) 4) &&
      S.reg .rsp == some (.ptr 0 (-8)) && S.reg .r12 == some (.ptr 0 4096) &&
      S.reg .rbp == some (.ptr 0 576) && S.reg .r13 == some (.ptr 0 2048) &&
      S.reg .r15 == some (.ptr 0 144) && Run.frameWrites S && Run.noWriteIn S 112 32 &&
      Run.noWriteIn S 144 16 && Run.noWriteIn S 176 8 && Run.noWriteIn S 568 8 &&
      Run.noWriteIn S 20540 7740 &&
      wr S 96 8 (.lit l) && wr S 200 8 (.lit (l + 1)) &&
      wr S 208 8 (.lit (4656 + 1028 * (l + 1))) &&
      wr S 160 8 (hS l) && wr S 216 8 (leafS l) && wr S 104 4 (.lit (revL l)) &&
      wr S 88 8 (.un .bswap .W64 (treeS l)) && wr S 60 4 (leafBE l) &&
      wr S 2048 4 (.lit (revL l)) && wr S 2052 4 (.lit 0) &&
      wr S 2056 8 (.un .bswap .W64 (treeS l)) && wr S 2064 4 (.lit 117440512) &&
      wr S 2068 4 (leafBE l) && wr S 2072 8 (.lit 0) && S.reg .r14 == some (.reg .r14)
  | none => false

theorem b104Ok_all : ∀ l < 3, b104Ok l = true := by decide +kernel

/-! ## Values -/

theorem wr_spec {S : SState} {o n : Nat} {v : Sym} (h : wr S o n v = true) :
    ∀ i < n, findWrite 0 (o + i) S.mem = some (v, i) := by
  intro i hi
  simp only [wr, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi

theorem ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- The bytes of a 32-bit truncation are the value's. -/
theorem bytes_trunc32 (x : BitVec 64) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 x)) = (List.range 4).map (byteOf x) := by
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  apply byteOf_eq_of_getLsbD
  intro j hj
  simp only [UnOp.apply, ext, low, Width.bits, BitVec.getLsbD_setWidth]
  simp [show 8 * t + j < 32 by omega, show 8 * t + j < 64 by omega]

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

theorem zeros4 : (List.range 4).map (byteOf (BitVec.ofNat 64 0)) = [0, 0, 0, 0] := by decide
theorem zeros8 : (List.range 8).map (byteOf (BitVec.ofNat 64 0)) = List.replicate 8 0 := by decide
theorem type7 : (List.range 4).map (byteOf (BitVec.ofNat 64 117440512)) = be32 7 := by decide

theorem be32_layer {l : Nat} (hl : l < 3) :
    (List.range 4).map (byteOf (BitVec.ofNat 64 (revL l))) = be32 l.toUInt32 := by
  rw [revL, ofNat_toNat_self, bytes_bswap32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The mask `b104` computes from the height: `~(-1 << h)`, `2 ^ h - 1`. -/
theorem mask_val {l : Nat} (hl : l < 3) :
    UnOp.apply .not .W32 (BinOp.apply .shl .W64 (BitVec.ofNat 64 18446744073709551615)
      (BitVec.ofNat 64 (layerHeights.getD l 0))) =
      BitVec.ofNat 64 (2 ^ layerHeights.getD l 0 - 1) := by
  interval_cases l <;> decide

/-- The shift count of the layers below, whatever the register's other bits. -/
theorem shiftCount_shS [Labels] (env : Env) {l : Nat} (hl : l < 3) :
    shiftCount .W64 ((shS l).eval env) = shOf l := by
  interval_cases l
  · exact shiftCount_ofNat (n := 0) (by decide)
  · exact shiftCount_of_low8 (low8_shift (env.regs .rax) (b := 0) (by decide)) (by decide)
  · exact shiftCount_of_low8 (low8_shift (env.regs .rax) (b := 1) (by decide)) (by decide)

theorem and_mask_toNat (e : BitVec 64) {h : Nat} (hh : h ≤ 10) :
    (BinOp.apply .and .W32 e (BitVec.ofNat 64 (2 ^ h - 1))).toNat = e.toNat % 2 ^ h := by
  have hp : 2 ^ h ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hh
  simp only [BinOp.apply, toNat_ext, BitVec.toNat_and, toNat_low, Width.bits, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ h - 1 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ h - 1 < 2 ^ 32 by omega), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : h ≤ 32))]

namespace Run

variable (r : Run) [Labels]

/-- The encoder's address at `2048`. -/
def EncAdrs (l : Nat) (m : MachineData) : Prop := BytesAt m.dmem (r.off 2048) ((r.key l).adrs 7)

/-- A write of the block, in the frame. -/
theorem write_at {m m' : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (r.envL m ret) S m') {o n : Nat} {v : Sym} (hle : o + n ≤ 29392)
    (h : wr S o n v = true) :
    BytesAt m'.dmem (r.off o) ((List.range n).map (byteOf (v.eval (r.envL m ret)))) :=
  hm.bytesAt_write (r := 0) (b := r.base) (sz := frameRegion) rfl hle (wr_spec h)

end Run


namespace Run

variable (r : Run) [Labels]

omit [Labels] in
/-- **Layer `l`'s counter in the frame**: at `26220 + 1028 l`, little-endian. -/
theorem counter_at {m : MachineData} (hI : r.Inputs m) {l : Nat} (hl : l < 3) :
    BytesAt m.dmem (r.off (26220 + 1028 * l)) (le32 (r.layerSig l).counter) := by
  have h := bytesAt_slice hI.2 (4656 + 1028 * l + 1024) 4 (by rw [r.length_sigMem]; omega)
  rw [show r.sig = sigOf r.w from rfl, SigMem.sigMem_counter r.w hl] at h
  rwa [off_add, show 20540 + (4656 + 1028 * l + 1024) =
    26220 + 1028 * l by omega] at h

omit [Labels] in
theorem word_lit (n : Nat) :
    (List.range 8).map (byteOf (BitVec.ofNat 64 n)) = wordBytes n.toUInt64 :=
  bytes_word _

/-- The index without the layers below, its number. -/
theorem eS_toNat {m : MachineData} {ret : BitVec 64} (h568 : r.WordAt m 568 r.idx) {l : Nat}
    (hl : l < 3) : ((eS l).eval (r.envL m ret)).toNat = r.idx.toNat / 2 ^ shOf l := by
  simp only [eS, Sym.eval]
  rw [shr_toNat, shiftCount_shS _ hl]
  simp only [idxS, Sym.eval]
  rw [r.load_word rfl rfl h568]
  rfl

end Run

variable [Host]

/-- **`b104` and `memset`**: from layer `l`'s state, the machine reaches `b105` with the
invariant (the counter in EBX), the encoder's address at `2048` and hasher A new. -/
theorem b104_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) {l : Nat} {s : List UInt8} {m : MachineData} (h : r.AtLayer l s m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b105Offset ∧
      r.EncBase l s (r.layerSig l).counter st.data ∧ r.EncAdrs l st.data ∧
      Keccak.HasherHolds (bytesOf st.data.dmem (r.off 4096) 344) []) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b104Offset⟩ := by
  obtain ⟨hl, hs, hF, hI, hcx, hsi, hdx, hbx, h12, hbp, h13, h15, hsm, h176, h568, h14⟩ := h
  have hok := b104Ok_all l hl
  rw [b104Ok] at hok
  rcases hx : exec Sphincs.SphincsVerify.b104 (s104 l) with _ | ⟨S, x⟩
  · rw [hx] at hok
    exact absurd hok Bool.false_ne_true
  rw [hx] at hok
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
  obtain ⟨rfl, hX0, hX1, hX2, hX19, hsp, hX12, hXbp, hX13, hX15, hfw, k112, k144, k176, k568,
    ksig, w96, w200, w208, w160, w216, w104, w88, w60, a0, a4, a8, a16, a20, a24, hX14⟩ := hok
  have hk := Sphincs.SphincsVerify.b104_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let ret : BitVec 64 := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b104Offset + Sphincs.SphincsVerify.b104.length)).toBitVec
  have hwf := r.envL_wf hpre hF ret
  have hm := r.match_frameL hpre hF (ret := ret) (known := [(.rcx, .lit (4656 + 1028 * l)),
      (.rsi, .lit l), (.rdx, .label NativeRustcX64.layerHeightsLabel), (.rbx, .lit 0), (.r12, .ptr 0 4096),
      (.rbp, .ptr 0 576), (.r13, .ptr 0 2048), (.r15, .ptr 0 144)])
    (aliases := [(.load 0 176 8, 0, ((25196 + 1028 * l : Nat) : Int))])
    ⟨hcx, hsi, hdx, hbx, h12.trans (r.ptr_evalL m ret _).symm,
      hbp.trans (r.ptr_evalL m ret _).symm, h13.trans (r.ptr_evalL m ret _).symm,
      h15.trans (r.ptr_evalL m ret _).symm, trivial⟩
    ⟨(r.load_word rfl rfl h176).trans (r.ptr_evalL m ret _), trivial⟩
  refine Sym.exec_then hk hx hwf (fun _ _ ↦ rfl) hm fun st hm' hpc ↦ ?_
  have hc1 := Run.AtCall.of_matchL r hpre hF hm' hwf hsp hfw
  have hH := r.load_height hpre ret hF hl
  have hE := r.eS_toNat (ret := ret) h568 hl
  have hhl := height_lt hl
  have hleafV : ((leafS l).eval (r.envL m ret)).toNat = (r.key l).leaf.toNat := by
    simp only [leafS, Sym.eval]
    simp only [hS, Sym.eval] at hH ⊢
    rw [hH, mask_val hl, and_mask_toNat _ (height_le hl), hE, Run.key, leaf_toNat hl]
  have htreeV : ((treeS l).eval (r.envL m ret)).toNat = (r.key l).tree.toNat := by
    simp only [treeS, Sym.eval]
    rw [shr_toNat]
    simp only [hS, Sym.eval] at hH ⊢
    rw [hH, shiftCount_ofNat hhl, hE, Run.key, tree_toNat hl]
  have hleaf64 : UInt64.ofBitVec ((leafS l).eval (r.envL m ret)) = (r.key l).leaf.toUInt64 :=
    UInt64.toNat_inj.mp (by rw [UInt64.toNat_ofBitVec, hleafV]; rfl)
  have hleaf32 : UInt32.ofNat ((leafS l).eval (r.envL m ret)).toNat = (r.key l).leaf :=
    UInt32.toNat_inj.mp (by
      rw [UInt32.toNat_ofNat', hleafV]; exact Nat.mod_eq_of_lt (UInt32.toNat_lt _))
  have htree64 : UInt64.ofBitVec ((treeS l).eval (r.envL m ret)) = (r.key l).tree :=
    UInt64.toNat_inj.mp (by rw [UInt64.toNat_ofBitVec, htreeV])
  -- the writes
  have e96 := r.write_at hm' (by decide) w96
  have e200 := r.write_at hm' (by decide) w200
  have e208 := r.write_at hm' (by decide) w208
  have e160 := r.write_at hm' (by decide) w160
  have e216 := r.write_at hm' (by decide) w216
  have e104 := r.write_at hm' (by decide) w104
  have e88 := r.write_at hm' (by decide) w88
  have e60 := r.write_at hm' (by decide) w60
  have ea0 := r.write_at hm' (by decide) a0
  have ea4 := r.write_at hm' (by decide) a4
  have ea8 := r.write_at hm' (by decide) a8
  have ea16 := r.write_at hm' (by decide) a16
  have ea20 := r.write_at hm' (by decide) a20
  have ea24 := r.write_at hm' (by decide) a24
  simp only [Sym.eval] at e96 e200 e208 e104 ea0 ea4 ea16 ea24
  rw [Run.word_lit] at e96 e200 e208
  rw [bytes_word, hleaf64] at e216
  simp only [hS, Sym.eval] at e160
  rw [hH, Run.word_lit] at e160
  rw [be32_layer hl] at e104 ea0
  simp only [Sym.eval] at e88 ea8
  rw [bytes_bswap64, htree64] at e88 ea8
  simp only [leafBE, Sym.eval] at e60 ea20
  rw [bytes_trunc32, bytes_bswap32, hleaf32] at e60 ea20
  rw [zeros4] at ea4
  rw [type7] at ea16
  rw [zeros8] at ea24
  have hadrs : r.EncAdrs l st.data := by
    unfold Run.EncAdrs
    rw [adrs7_eq]
    exact r.bytesAt_app_off (r.bytesAt_app_off (r.bytesAt_app_off (r.bytesAt_app_off
      (r.bytesAt_app_off ea0 ea4 rfl) ea8 rfl) ea16 rfl) ea20 rfl) ea24 rfl
  have kept := fun {o : Nat} {bs : List UInt8} ho hb hn ↦
    r.bytesAt_keptL (m := m) (m' := st.data) hpre hm' hwf (o := o) (bs := bs) ho hb hn
  have hc19 : UInt32.ofNat (reg st.data .rbx).toNat = (r.layerSig l).counter := by
    rw [show reg st.data .rbx = _ from hm'.regs .rbx _ hX19]
    show UInt32.ofNat ((r.envL m ret).load 0 (26220 + 1028 * l) 4).toNat = _
    rw [Sym.Env.load_of_bytesAt (by simp [le32, be32]) (r.counter_at hI hl), le32_load]
  have hdata : r.EncData l s (r.layerSig l).counter st.data :=
    ⟨⟨kept (by rw [r.length_pkBytes]; omega) hI.1 (by rw [r.length_pkBytes]; exact k112),
      kept (by rw [r.length_sigMem]; omega) hI.2 (by rw [r.length_sigMem]; exact ksig)⟩,
      ⟨e96, e200, e208, e160, e216, e104, e88, e60,
        kept (by rw [length_wordBytes]; omega) h568 (by rw [length_wordBytes]; exact k568),
        kept (by rw [length_wordBytes]; omega) h176 (by rw [length_wordBytes]; exact k176)⟩,
      (hm'.regs .r12 _ hX12).trans (r.ptr_evalL m ret _),
      (hm'.regs .rbp _ hXbp).trans (r.ptr_evalL m ret _),
      (hm'.regs .r13 _ hX13).trans (r.ptr_evalL m ret _),
      (hm'.regs .r15 _ hX15).trans (r.ptr_evalL m ret _),
      kept (by rw [hs]; omega) hsm (by rw [hs]; exact k144), hc19,
      (hm'.regs .r14 _ hX14).trans h14⟩
  have hR0 : Run.RegIs st.data .rdi (r.off 4096) :=
    (hm'.regs .rdi _ hX0).trans (r.ptr_evalL m ret _)
  have hR2 : (reg st.data .rdx).toNat = 344 := by
    rw [show reg st.data .rdx = _ from hm'.regs .rdx _ hX2]
    rfl
  have hR1 : UInt8.ofNat (reg st.data .rsi).toNat = 0 := by
    rw [show reg st.data .rsi = _ from hm'.regs .rsi _ hX1]
    rfl
  refine Sym.call_then hpc hc.2.1 (r.memset_pre hpre hc1 hR0 hR2 (by decide))
    fun st' hpc' hrsp hpost ↦ .done _ ?_
  obtain ⟨hB, hout, hS⟩ := r.memset_out hR0 hR2 hpost
  refine ⟨by simpa only [Run.pc, Nat.add_assoc, NativeRustcX64.Sphincs.SphincsVerify.b104_next] using hpc',
    ⟨hl, hs, r.frame_of_call hpre hc1 hS hrsp (by decide) (Nat.zero_le _) hout,
      r.encData_of_call hpre hc1 hdata hs hS (.inl ⟨le_refl _, le_refl _⟩) (Nat.zero_le _) hout⟩,
    r.bytesAt_of_call hpre hc1 (by decide) (Nat.zero_le _) hout
      (by rw [length_adrs7]; omega) (by rw [length_adrs7]; omega) hadrs, ?_⟩
  rw [hR1] at hB
  have := bytesOf_of_bytesAt hB
  rw [List.length_replicate] at this
  rw [this]
  exact Keccak.holds_new

end

end NativeRustcX64.SphincsVerifyProof
