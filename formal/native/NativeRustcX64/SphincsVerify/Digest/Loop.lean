module

public import NativeRustcX64.SphincsVerify.Digest.Leaf
public import NativeRustcX64.SphincsVerify.Digest.Hash
public import NativeRustcX64.SphincsVerify.Bswap

/-!
# `digest_fields`' leaves: the loop `b55` (x86-64)

`.LSphincsVerify_17` (directive 517): turn `c` (R12 `10 c`, R13 `base + 4104 + 8 c`) reads bits
`10 c .. 10 c + 9` of `h_msg` (`H`, at `2056`) and stores leaf `c` at R13 (`LoopInv`); after 24
turns it falls through to `b56` (directive 653) with the 24 leaves' words at `4104`
(`AfterLoop`, `loop_spec`). The turn runs in its own regions (`loopRegs`: `h_msg`, the leaf, the
spill `8(%rsp)`, the pushes' slots below the frame).
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- The first `c` leaves' words. -/
def leavesBytes (H : List UInt8) (c : Nat) : List UInt8 :=
  wordsBytes ((List.range c).map fun i ↦ (leafOf H i).toUInt64)

/-- **At the loop's head, turn `c`**: what the digest keeps, R12 and R13, `H` at `2024`, the
first `c` leaves at `4072`. -/
def LoopInv (r : Run) (H : List UInt8) (c : Nat) (m : MachineData) : Prop :=
  c < 24 ∧ Keep r m ∧ Run.RegIs m .r12 (BitVec.ofNat 64 (10 * c)) ∧
    Run.RegIs m .r13 (r.off (4072 + 8 * c)) ∧ BytesAt m.dmem (r.off 2024) H ∧
    BytesAt m.dmem (r.off 4072) (leavesBytes H c)

/-- **After the loop**: what the digest keeps, `H` at `2024`, the 24 leaves at `4072`. -/
def AfterLoop (r : Run) (H : List UInt8) (m : MachineData) : Prop :=
  Keep r m ∧ BytesAt m.dmem (r.off 2024) H ∧ BytesAt m.dmem (r.off 4072) (leavesBytes H 24)

/-- A turn's regions: `h_msg`, the leaf, the spill, the pushes' slots. -/
abbrev loopRegs (r : Run) (c : Nat) : List (BitVec 64 × Nat) :=
  [(r.off 2024, 64), (r.off (4072 + 8 * c), 8), (r.off 8, 8), (r.base - 16#64, 16)]

end

public section

theorem length_leavesBytes (H : List UInt8) (c : Nat) : (leavesBytes H c).length = 8 * c := by
  simp [leavesBytes, Native.Keccak.Proof.length_wordsBytes]

theorem leavesBytes_succ (H : List UInt8) (c : Nat) :
    leavesBytes H (c + 1) = leavesBytes H c ++ wordBytes (leafOf H c).toUInt64 := by
  rw [leavesBytes, leavesBytes, List.range_succ, List.map_append]
  simp [Native.Keccak.wordsBytes]

section
variable [Labels]

/-- The loop's byte indices are below `30`. -/
theorem bix_lt (env : Env) {c : Nat} (hc : c < 24) (hx : env.regs .r12 = BitVec.ofNat 64 (10 * c))
    {j : Nat} (hj : j < 10) : ((bix j).eval env).toNat < 30 := by
  interval_cases j <;>
  · simp only [bix, ↓reduceIte, Nat.reduceEqDiff]
    sym_simp
    rw [hx]
    clear hx
    revert c
    decide

/-- The loop's branch back: another turn while `c + 1 < 24`. -/
theorem cond_eval (env : Env) {c : Nat} (hc : c < 24) (hx : env.regs .r12 = BitVec.ofNat 64 (10 * c)) :
    (SBool.not (.cmp .eq .W64 (.bin .add .W64 (.lit 10) (.reg .r12)) (.lit 240))).eval env =
      decide (c + 1 < 24) := by
  sym_simp
  rw [hx]
  clear hx
  revert c
  decide

/-- The bit index's next value. -/
theorem add10_eval (env : Env) {c : Nat} (hx : env.regs .r12 = BitVec.ofNat 64 (10 * c)) :
    (Sym.bin .add .W64 (.lit 10) (.reg .r12)).eval env = BitVec.ofNat 64 (10 * (c + 1)) := by
  sym_simp
  rw [hx, Nat.mul_succ, BitVec.ofNat_add, BitVec.add_comm]

omit [Labels] in
/-- A byte of region 0 holding `H`. -/
theorem load_byte {env : Env} {H : List UInt8} (h : BytesAt env.mem0 (env.base 0) H) {k : Nat}
    (hk : k < H.length) : env.load 0 k 1 = BitVec.setWidth 64 (H.getD k 0).toBitVec := by
  rw [Env.load_of_bytesAt (n := 1) (bs := [H.getD k 0]) rfl ?_]
  · apply BitVec.eq_of_toNat_eq
    simp [Int.ofBytes]
  · intro i hi
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff] at hi
    subst hi
    have := h k hk
    simpa [List.getD_eq_getElem?_getD, hk] using this

end

section
variable {r : Run} [Labels]

/-- The loop's regions are well formed. -/
theorem loop_wf (hpre : r.Pre) {m : MachineData} (hK : Keep r m) {c : Nat} (hc : c < 24) :
    (Env.ofMachine m (loopRegs r c) (fun _ ↦ 0) 0).WF := by
  have hb := r.base_toNat hpre
  have hk := hK.1.2.2.2
  have o2 := r.off_toNat hpre (a := 2024) (by omega)
  have o4 := r.off_toNat hpre (a := 4072 + 8 * c) (by omega)
  have o8 := r.off_toNat hpre (a := 8) (by omega)
  have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
  have h3 : Mapped m.dmem (r.base - 16#64) 16 ∧ NoWrap (r.base - 16#64) 16 := by
    refine ⟨fun i hi ↦ r.area_mapped hpre hk ?_ ?_, ?_⟩
    · rw [Sym.toNat_add_ofNat _ _ (by omega), hlo]
      omega
    · rw [Sym.toNat_add_ofNat _ _ (by omega), hlo]
      omega
    · unfold NoWrap
      omega
  refine Env.wf_of ⟨r.frame_mapped hpre hk (by omega), r.frame_mapped hpre hk (by omega),
    r.frame_mapped hpre hk (by omega), h3, trivial⟩ ?_
  show List.Pairwise (fun e e' ↦ Apart e.1 e.2 e'.1 e'.2) (loopRegs r c)
  simp [Apart, o2, o4, o8, hlo]
  omega

/-- What a turn writes: the leaf, the spill, the pushes' slots. -/
def Wr (r : Run) (c : Nat) (p : BitVec 64) : Prop :=
  (r.base.toNat + 4072 + 8 * c ≤ p.toNat ∧ p.toNat < r.base.toNat + 4072 + 8 * c + 8) ∨
    (r.base.toNat + 8 ≤ p.toNat ∧ p.toNat < r.base.toNat + 16) ∨
    (r.base.toNat ≤ p.toNat + 16 ∧ p.toNat < r.base.toNat)

/-- The writes in regions 1 to 3 are where `Wr` says. -/
theorem written_wr (hpre : r.Pre) {m : MachineData} {c : Nat} (hc : c < 24) {S : SState}
    (hall : S.mem.all (fun w ↦ w.r != 0 && decide (w.off + w.n ≤ [64, 8, 8, 16].getD w.r 0)) = true)
    {p : BitVec 64} (hp : Written (Env.ofMachine m (loopRegs r c) (fun _ ↦ 0) 0) S p) : Wr r c p := by
  have hb := r.base_toNat hpre
  have o4 := r.off_toNat hpre (a := 4072 + 8 * c) (by omega)
  have o8 := r.off_toNat hpre (a := 8) (by omega)
  have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
  obtain ⟨w, hw, b, sz, hr, h1, h2⟩ := hp
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  obtain ⟨h0, hn⟩ := this
  unfold Wr
  rcases hwr : w.r with _ | _ | _ | _ | k
  · exact absurd hwr h0
  · rw [hwr] at hr hn
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp at hn
    omega
  · rw [hwr] at hr hn
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp at hn
    omega
  · rw [hwr] at hr hn
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp at hn
    omega
  · rw [hwr] at hr
    simp at hr

/-- A frame byte apart from what a turn writes is kept. -/
theorem keep_turn (hpre : r.Pre) {d d' : DataMem} {c : Nat} (hc : c < 24)
    (hs : SameOutside d d' (Wr r c)) {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
    (hd : (o + bs.length ≤ 8 ∨ 16 ≤ o) ∧ (o + bs.length ≤ 4072 + 8 * c ∨ 4072 + 8 * c + 8 ≤ o))
    (h : BytesAt d (r.off o) bs) : BytesAt d' (r.off o) bs :=
  bytesAt_of_sameOutside h hs fun i hi hw ↦ by
    have hb := r.base_toNat hpre
    have := r.off_toNat hpre (a := o) (by omega)
    unfold Wr at hw
    rw [Sym.toNat_add_ofNat _ _ (by omega), this] at hw
    omega

/-- What a turn writes is in the stack area, off the saved registers. -/
theorem wr_area (hpre : r.Pre) {c : Nat} (hc : c < 24) :
    ∀ p, Wr r c p → r.StackArea p ∧ ¬InRange (r.off 21576) 48 p := by
  intro p hp
  have hb := r.base_toNat hpre
  have hs := r.off_toNat hpre (a := 21576) (by decide)
  unfold Wr at hp
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  omega

end

variable [ElfHost]

/-- **A turn of the loop**: leaf `c` stored, then the next turn or `b47`. -/
theorem loop_step (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {H : List UInt8} (hH : H.length = 64) {c : Nat} {m : MachineData} (hI : LoopInv r H c m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ (st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b47Offset ∧ AfterLoop r H st.data) ∨
      (st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b46Offset ∧ LoopInv r H (c + 1) st.data)) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b46Offset⟩ := by
  obtain ⟨hc, hK, h13, hbp, hHb, hL⟩ := hI
  have hF := hK.1
  have hwf := loop_wf hpre hK hc
  have hb := r.base_toNat hpre
  have hx13 : (Env.ofMachine m (loopRegs r c) (fun _ ↦ 0) 0).regs .r12 = BitVec.ofNat 64 (10 * c) :=
    h13
  have hm : Match (Env.ofMachine m (loopRegs r c) (fun _ ↦ 0) 0) s46 m := by
    refine match_ofMachine ⟨rfl, rfl, rfl, rfl, trivial⟩ ⟨?_, ?_, trivial⟩ trivial ?_ ?_
    · show rspOf m = r.off 2024 + BitVec.ofInt 64 (-2024)
      rw [hF.1, Run.off, BitVec.add_assoc, show BitVec.ofNat 64 2024 + BitVec.ofInt 64 (-2024) = 0#64
        by decide, BitVec.add_zero]
    · show reg m .r13 = r.off (4072 + 8 * c) + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 by decide, BitVec.add_zero]
      exact hbp
    · simp only [List.map_cons, List.map_nil, AllOf]
      exact ⟨bix_lt _ hc hx13 (by decide), bix_lt _ hc hx13 (by decide),
        bix_lt _ hc hx13 (by decide), bix_lt _ hc hx13 (by decide), bix_lt _ hc hx13 (by decide),
        bix_lt _ hc hx13 (by decide), bix_lt _ hc hx13 (by decide), bix_lt _ hc hx13 (by decide),
        bix_lt _ hc hx13 (by decide), trivial⟩
    · refine ⟨?_, ?_, ?_, trivial⟩
      · show r.off 2024 + BitVec.ofInt 64 (-2016) = r.off 8 + BitVec.ofInt 64 0
        simp only [Run.off, BitVec.add_assoc]
        congr 1
      · show r.off 2024 + BitVec.ofInt 64 (-2032) = (r.base - 16#64) + BitVec.ofInt 64 8
        simp only [Run.off]
        rw [BitVec.add_assoc, show BitVec.ofNat 64 2024 + BitVec.ofInt 64 (-2032) = -8#64 by decide,
          show BitVec.ofInt 64 8 = 8#64 by decide]
        bv_omega
      · show r.off 2024 + BitVec.ofInt 64 (-2040) = (r.base - 16#64) + BitVec.ofInt 64 0
        simp only [Run.off]
        rw [BitVec.add_assoc, show BitVec.ofNat 64 2024 + BitVec.ofInt 64 (-2040) = -16#64 by decide,
          show BitVec.ofInt 64 0 = 0#64 by decide]
        bv_omega
  have hk := Sphincs.SphincsVerify.b46_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then_elf hk run_b46 hwf (fun _ h ↦ nomatch h) hm fun st hm' hpc ↦ ?_
  obtain ⟨m', pc⟩ := st
  simp only [PcOk] at hpc
  rw [cond_eval _ hc hx13] at hpc
  simp only at hm'
  -- memory: what the turn writes
  have hso : SameOutside m.dmem m'.dmem (Wr r c) := fun p hp ↦
    hm'.sameOutside hwf p fun hw ↦ hp (written_wr hpre hc rfl hw)
  have hk' : Kept m.dmem m'.dmem := hm'.kept hwf
  have hsp : rspOf m' = r.base := by
    rw [rspOf, show m'.regs.get64 .rsp = _ from hm'.regs .rsp _ rfl]
    show r.off 2024 + BitVec.ofInt 64 (-2024) = r.base
    rw [Run.off, BitVec.add_assoc, show BitVec.ofNat 64 2024 + BitVec.ofInt 64 (-2024) = 0#64
      by decide, BitVec.add_zero]
  have hF' : r.Frame m' := Run.Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 hsp hso (wr_area hpre hc) hk'
  have hpk := r.hpk
  have hsl := length_sigMem' r
  have hw8 := NativeRustc.length_wordBytes (r.addr 17436)
  have hK' : Keep r m' :=
    ⟨hF', ⟨keep_turn hpre hc hso (by omega) (by omega) hK.2.1.1,
      keep_turn hpre hc hso (by omega) (by omega) hK.2.1.2⟩,
      keep_turn hpre hc hso (by omega) (by omega) hK.2.2⟩
  have hbl : ∀ k < 30, (Env.ofMachine m (loopRegs r c) (fun _ ↦ 0) 0).load 0 k 1 =
      BitVec.setWidth 64 (H.getD k 0).toBitVec := fun k hk ↦ load_byte hHb (by omega)
  have hleaf : BytesAt m'.dmem (r.off (4072 + 8 * c)) (wordBytes (leafOf H c).toUInt64) := by
    have := hm'.bytesAt_write (r := 1) (o := 0) (n := 8) (b := r.off (4072 + 8 * c)) (sz := 8)
      rfl (by decide) (v := leafSym)
      (fun i hi ↦ by rw [leafSym, run_b46]; exact findWrite_head hi)
    rw [leaf_eval _ H hc hx13 hbl, bytes_word,
      show r.off (4072 + 8 * c) + BitVec.ofNat 64 0 = r.off (4072 + 8 * c) by simp] at this
    exact this
  have hLl := length_leavesBytes H c
  have hH' := keep_turn hpre hc hso (by omega) (by omega) hHb
  have hL' := keep_turn hpre hc hso (by omega) (by omega) hL
  have hL'' : BytesAt m'.dmem (r.off 4072) (leavesBytes H (c + 1)) := by
    rw [leavesBytes_succ]
    exact bytesAt_cat hL' hLl rfl hleaf
  by_cases hlast : c + 1 < 24
  · refine .done _ (.inr ⟨?_, hlast, hK', ?_, ?_, hH', hL''⟩)
    · rw [hpc, decide_eq_true hlast]
      simp only [↓reduceIte]
      exact Run.label_of_block r hp Sphincs.SphincsVerify.b46_in_code rfl
    · unfold Run.RegIs
      rw [show reg m' .r12 = _ from hm'.regs .r12 _ rfl, add10_eval _ hx13]
    · unfold Run.RegIs
      rw [show reg m' .r13 = _ from hm'.regs .r13 _ rfl]
      show r.off (4072 + 8 * c) + BitVec.ofInt 64 8 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 by decide, Run.off_add,
        show 4072 + 8 * c + 8 = 4072 + 8 * (c + 1) by omega]
  · have hc23 : c = 23 := by omega
    subst hc23
    refine .done _ (.inl ⟨?_, hK', hH', hL''⟩)
    rw [hpc, decide_eq_false hlast]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Run.pc, Nat.add_assoc, NativeRustcX64.Sphincs.SphincsVerify.b46_next]

/-- **The loop**: from turn `c`, the machine reaches `b47` with the 24 leaves. -/
theorem loop_spec (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {H : List UInt8} (hH : H.length = 64) {c : Nat} {m : MachineData} (hI : LoopInv r H c m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b47Offset ∧ AfterLoop r H st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b46Offset⟩ := by
  refine Sym.loop (fun n st ↦ ∃ c, n = 24 - c ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b46Offset ∧ LoopInv r H c st.data)
    (fun n st ⟨c, hn, hpc, hI⟩ ↦ ?_) ⟨c, rfl, rfl, hI⟩
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  refine Eventually.mono_elf (loop_step r hp hpre hH hI) fun st h ↦ ?_
  rcases h with h | ⟨hpc, hI'⟩
  · exact .inl h
  · exact .inr ⟨24 - (c + 1), by have := hI.1; have := hI'.1; omega, c + 1, rfl, hpc, hI'⟩

/-- **`h_msg` in place, the loop's first turn** (`b45`). -/
theorem hMsg_spec (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hpre : r.Pre)
    {m : MachineData} (hH : Hashed1 r m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b46Offset ∧ LoopInv r (hMsgBytes r) 0 st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b45Offset⟩ := by
  obtain ⟨hK, h13, hbp, hD0, hD1⟩ := hH
  refine Run.frameFall r hp hpre Sphincs.SphincsVerify.b45_in_code rfl (List.cons_ne_nil _ _)
    run_b45 rfl rfl hK (knownOK_nil m _) fun m₁ hm₁ hK₁ hkb₁ ↦ .done _ ⟨rfl, by decide, hK₁,
      regIs_keep hm₁ rfl h13, regIs_keep hm₁ rfl hbp, ?_, fun i hi ↦ absurd hi (by
        rw [length_leavesBytes]; omega)⟩
  exact bytesAt_cat (hkb₁ 2024 _ (by rw [length_hCall]; omega) (by rw [length_hCall]; rfl) hD0)
    (length_hCall r 0) rfl (copy32 hm₁ (o := 2056) (o' := 10344) (by decide) rfl (length_hCall r 1) hD1)

end

end NativeRustcX64.SphincsVerifyProof.Digest
