module

public import NativeRustcArm.SphincsVerify.Fors.Glue

/-!
# A FORS node, part 1: its inputs (`b58` and `memset`)

At a node's head (`AtNode`, `b58`, `.LSphincsVerify_14`): tree `c`, height `z < 10`, its value
after `z` steps at `12864`. `b58` copies the value to `13888`, loads the two children (the value
and the path's node, bit `z` of the leaf index saying which is left: X8 and X10 point to them),
writes them to `14912` and the node's address to `15936`, and calls `memset` on hasher A
(`N1` at `b59`). `b58` runs in five pieces, its two `ldp`s each in an environment whose one
region is the child's 16 bytes.
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- **At a node's head** `b58`: tree `c`, height `z`, the value after `z` steps at `12864`. -/
structure AtNode (r : Run) (c z : Nat) (m : MachineData) : Prop where
  tree : TreeSt r c m
  hz : z < 10
  x19 : Run.RegIs m .X19 (BitVec.ofNat 64 c)
  x21 : Run.RegIs m .X21 (BitVec.ofNat 64 z)
  x20 : wordBytes (m.regs.getXReg .X20) = be64 (r.key 0).tree
  x25 : Run.RegIs m .X25 (kpW r)
  cur : BytesAt m.dmem (r.off 12864) (r.forsUpTo c z)

/-- **At `b59`**: hasher A zero, the children at `14912`, the node's address at `15936`. -/
structure N1 (r : Run) (c z : Nat) (m : MachineData) : Prop where
  tree : TreeSt r c m
  hz : z < 10
  x19 : Run.RegIs m .X19 (BitVec.ofNat 64 c)
  x21 : Run.RegIs m .X21 (BitVec.ofNat 64 (z + 1))
  x25 : Run.RegIs m .X25 (kpW r)
  a : BytesAt m.dmem (r.off 8640) (List.replicate 344 0)
  ch : BytesAt m.dmem (r.off 14912) (r.childrenOf c z)
  ad : BytesAt m.dmem (r.off 15936) (r.nodeAdrsOf c z)

end

public section

/-! ## Bits and words -/

/-- The branch's test of bit `z` of the leaf index. -/
theorem bit_test : ∀ z < 10, ∀ leaf < 1024,
    (BinOp.apply .and .W64 (BinOp.apply .lslv .W64 (BitVec.ofNat 64 1) (BitVec.ofNat 64 z))
      (BitVec.ofNat 64 leaf) == BitVec.ofNat 64 0) = decide (leaf >>> z &&& 1 = 0) := by
  decide +kernel

theorem shl4 (z : Nat) :
    UnOp.apply (.shift .LSL 4) .W64 (BitVec.ofNat 64 z) = BitVec.ofNat 64 (16 * z) := by
  apply BitVec.eq_of_toNat_eq
  simp only [UnOp.apply, low_W64, ext_W64, shiftW, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  omega

/-- **The node's index**, as `b58` computes it: `c << (9 - z)` plus the leaf index's bits above
`z`, big-endian. -/
theorem bytes_index {c z leaf : Nat} (hz : z < 10) (hl : leaf < 1024) :
    (List.range 4).map (byteOf (UnOp.apply .rev .W32 (BinOp.apply .add .W32
      (BinOp.apply .lslv .W32 (BitVec.ofNat 64 c)
        (BinOp.apply .sub .W64 (BitVec.ofNat 64 9) (BitVec.ofNat 64 z)))
      (UnOp.apply .trunc .W32 (BinOp.apply .lsrv .W64 (BitVec.ofNat 64 leaf)
        (BinOp.apply .add .W64 (BitVec.ofNat 64 z) (BitVec.ofNat 64 1))))))) =
      be32 ((c <<< (10 - (z + 1))) + (leaf >>> (z + 1))).toUInt32 := by
  rw [bytes_rev32]
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.toUInt32_eq, UInt32.toNat_ofNat']
  simp only [BinOp.apply, UnOp.apply, low_W64, ext_W64, ext_W32, low_W32, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  interval_cases z <;> simp <;> omega

/-- The height's word. -/
theorem bytes_height (z : Nat) :
    (List.range 4).map (byteOf (UnOp.apply .rev .W32
      (BinOp.apply .add .W64 (BitVec.ofNat 64 z) (BitVec.ofNat 64 1)))) = be32 (z + 1).toUInt32 := by
  rw [bytes_rev32]
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.toUInt32_eq, UInt32.toNat_ofNat']
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem bytes_typeW : (List.range 4).map (byteOf (BitVec.ofNat 64 typeW)) = be32 3 := by
  decide

theorem bytes_zero8 : (List.range 8).map (byteOf (BitVec.ofNat 64 0)) = be32 0 ++ be32 0 := by
  decide

/-- A node's address, in the pieces `b58` writes. -/
theorem nodeAdrsOf_eq (r : Run) (c z : Nat) :
    r.nodeAdrsOf c z = (be32 0 ++ be32 0) ++ (be64 (r.key 0).tree ++ (be32 3 ++
      (be32 (r.key 0).leaf ++ (be32 (z + 1).toUInt32 ++
        be32 ((c <<< (10 - (z + 1))) + (r.leafOf c >>> (z + 1))).toUInt32)))) := by
  rw [Run.nodeAdrsOf, forsNodeAdrs_eq, adrsBytes, List.append_assoc]
  rfl

/-! ## Reading a child -/

variable {r : Run}

/-- The bytes of a load from a frame range's environment. -/
theorem bytes_load_off {m : MachineData} {vars : Nat → BitVec 64} {a o n : Nat} {bs : List UInt8}
    (h : BytesAt m.dmem (r.off (a + o)) bs) (hl : bs.length = n) (hn : n ≤ 8) :
    (List.range n).map (byteOf ((Env.ofMachine m [(r.off a, 16)] vars).load 0 o n)) = bs := by
  subst hl
  apply List.ext_getElem (by simp)
  intro t h1 h2
  rw [List.getElem_map, List.getElem_range, byteOf_load h2 hn]
  show (m.dmem.get? (r.off a + BitVec.ofNat 64 (o + t))).getD 0 = _
  rw [Run.off_add, show a + (o + t) = a + o + t by omega, ← Run.off_add, h t h2]
  rfl

/-- **A child's `ldp`**: in the environment of its 16 bytes at `a`, the block loads its two
words. -/
theorem ldp_child [ElfHost] {sec : Nat} (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {x : XReg}
    {a : Nat} (ha : a + 16 ≤ 21616) (hx : Run.RegIs m x (r.off a)) {ds : List Directive} {j : Nat}
    (hk : ds.IsInfixAt (ElfHost.sectionProg sec) j) {S' : SState} {e : Exit} (hrun : exec ds (ldS x) = some (S', e)) (hmem : S'.mem = [])
    {R : MachineState → Prop}
    (cont : ∀ st, Match (Env.ofMachine m [(r.off a, 16)]) S' st.data →
      PcOk (Env.ofMachine m [(r.off a, 16)]) e (ElfHost.addrOf sec (j + ds.length)) st →
      st.data.dmem = m.dmem → Eventually (elfStep1 ElfHost.exe) R st) :
    Eventually (elfStep1 ElfHost.exe) R ⟨m, ElfHost.addrOf sec j⟩ := by
  have hwf : (Env.ofMachine m [(r.off a, 16)]).WF :=
    Env.wf_of ⟨r.frame_mapped hpre hF ha, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m [(r.off a, 16)]) (ldS x) m :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by
        show _ = r.off a + BitVec.ofInt 64 0
        rw [hx]
        simp, trivial⟩ trivial trivial trivial
  exact exec_then_elf hk hrun hwf hm fun st hm' hpc ↦ cont st hm' hpc (hm'.dmem_eq hwf hmem)

/-- `Base` where memory, SP and the region's registers are as they were. -/
theorem Base.of_eq {m m' : MachineData} (hB : Base r m) (hd : m'.dmem = m.dmem)
    (hsp : m'.regs.SP = m.regs.SP) (h28 : m'.regs.getXReg .X28 = m.regs.getXReg .X28)
    (h26 : m'.regs.getXReg .X26 = m.regs.getXReg .X26)
    (h22 : m'.regs.getXReg .X22 = m.regs.getXReg .X22)
    (h29 : m'.regs.getXReg .X29 = m.regs.getXReg .X29) : Base r m' :=
  hB.of_keep (Keep.of_eq hd).low
    ⟨by rw [hsp]; exact hB.frame.1, by rw [h29]; exact hB.frame.2.1, by rw [hd]; exact hB.frame.2.2.1,
      by rw [hd]; exact hB.frame.2.2.2.1, by rw [hd]; exact hB.frame.2.2.2.2⟩ h28 h26 h22

end

/-! ## The node's inputs -/

public section

variable {r : Run}

theorem length_pathNode {c z : Nat} (hc : c < 24) (hz : z < 10) : (r.pathNode c z).length = 16 :=
  r.length_forsPath_getD hc hz

/-- The path's node at height `z`, in the frame. -/
theorem bytesAt_pathNode {m : MachineData} (h : r.Inputs m) {c z : Nat} (hc : c < 24) (hz : z < 10) :
    BytesAt m.dmem (r.off (484 + 16 * z + 176 * c)) (r.pathNode c z) := by
  have := bytesAt_slice h.2.1 (176 * c + 16 * z) 16
  rw [r.sigMem_path hc hz, show 484 + (176 * c + 16 * z) = 484 + 16 * z + 176 * c by omega] at this
  exact this

theorem split16 {L : List UInt8} (h : L.length = 16) : L = L.take 8 ++ (L.drop 8).take 8 := by
  rw [List.take_of_length_le (l := L.drop 8) (by simp [h]), List.take_append_drop]

theorem pieces16 {d : DataMem} {o : Nat} {L : List UInt8} (h : L.length = 16)
    (h1 : BytesAt d (r.off o) (L.take 8)) (h2 : BytesAt d (r.off (o + 8)) ((L.drop 8).take 8)) :
    BytesAt d (r.off o) L := by
  rw [split16 h]
  exact bytesAt_cat (by simp [h]) h1 h2

variable [ElfHost]

/-- **A node's inputs** (`b58` and `memset`): from a node's head, `N1` at `b59`. -/
theorem node_s1 (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {c z : Nat} {m : MachineData}
    (h : AtNode r c z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b59Offset ∧ N1 r c z st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b58Offset⟩ := by
  obtain ⟨hT, hz, h19, h21, h20, h25, hcur⟩ := h
  have hB := hT.base
  have hc24 := hT.hc
  have hl := r.leafOf_lt hc24
  have hcurl : (r.forsUpTo c z).length = 16 := length_forsUpTo c z
  have hpl : (r.pathNode c z).length = 16 := length_pathNode hc24 hz
  -- which child is left
  let offL := if r.leafOf c >>> z &&& 1 = 0 then 13888 else 484 + 16 * z + 176 * c
  let offR := if r.leafOf c >>> z &&& 1 = 0 then 484 + 16 * z + 176 * c else 13888
  let Lc := if r.leafOf c >>> z &&& 1 = 0 then r.forsUpTo c z else r.pathNode c z
  let Rc := if r.leafOf c >>> z &&& 1 = 0 then r.pathNode c z else r.forsUpTo c z
  have hoffL : offL + 16 ≤ 21616 := by simp only [offL]; split <;> omega
  have hoffR : offR + 16 ≤ 21616 := by simp only [offR]; split <;> omega
  have hLl : Lc.length = 16 := by simp only [Lc]; split <;> assumption
  have hRl : Rc.length = 16 := by simp only [Rc]; split <;> assumption
  have hch : r.childrenOf c z = Lc ++ Rc := by
    simp only [Run.childrenOf, Lc, Rc]; split <;> rfl
  -- piece a: the value's copy, the children's addresses
  have hwf0 := r.frame_wf hpre hB.frame (fun _ ↦ 0)
  have hm0 : Match (r.env m) s0 m := match_frameS hpre hB trivial trivial
  refine exec_then_elf (hb58a hp) run_b58a hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hB1, hk1⟩ := hB.of_match hpre hm1 hwf0 rfl rfl rfl rfl rfl rfl
  have h21' : (m.regs.getXReg .X21).toBitVec = BitVec.ofNat 64 z := h21
  have hl440 : (r.env m).load 0 440 8 = BitVec.ofNat 64 (r.leafOf c) := load_word hT.w440
  have hl432 : (r.env m).load 0 432 8 = r.off (484 + 176 * c) := load_word hT.w432
  have hcond : (SBool.cmp .eq .W64 (.bin .and .W64 (.bin .lslv .W64 (.lit 1) (.reg .X21))
      (.load 0 440 8)) (.lit 0)).eval (r.env m) = decide (r.leafOf c >>> z &&& 1 = 0) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs, h21', hl440]
    exact bit_test z hz _ hl
  have hpath : r.off (484 + 176 * c) + UnOp.apply (.shift .LSL 4) .W64 (BitVec.ofNat 64 z) =
      r.off (484 + 16 * z + 176 * c) := by
    rw [shl4, Run.off_add]
    congr 1
    omega
  have hx8 : Run.RegIs st1.data .X8 (r.off offL) := by
    rw [Run.RegIs, hm1.regs .X8 _ rfl]
    simp only [Sym.eval, hcond, Env.ofMachine_regs, h21', hl432, offL]
    by_cases hb : r.leafOf c >>> z &&& 1 = 0
    · simp only [hb, decide_true, ↓reduceIte]
      exact eval_ptr 13888
    · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, BinOp.apply, low_W64, ext_W64]
      exact hpath
  have hx10 : Run.RegIs st1.data .X10 (r.off offR) := by
    rw [Run.RegIs, hm1.regs .X10 _ rfl]
    simp only [Sym.eval, hcond, Env.ofMachine_regs, h21', hl432, offR]
    by_cases hb : r.leafOf c >>> z &&& 1 = 0
    · simp only [hb, decide_true, ↓reduceIte, BinOp.apply, low_W64, ext_W64]
      exact hpath
    · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact eval_ptr 13888
  have hcopy : BytesAt st1.data.dmem (r.off 13888) (r.forsUpTo c z) := by
    have hc1 := bytesAt_slice hcur 0 8
    have hc2 := bytesAt_slice hcur 8 8
    rw [List.drop_zero, Nat.add_zero] at hc1
    exact pieces16 hcurl (write_load hm1 (o := 13888) (o' := 12864) (by decide) le_rfl (by decide)
      (by simp [hcurl]) hc1) (write_load hm1 (o := 13896) (o' := 12872) (by decide) le_rfl
      (by decide) (by simp [hcurl]) hc2)
  have hLc : BytesAt st1.data.dmem (r.off offL) Lc := by
    simp only [offL, Lc]
    split
    · exact hcopy
    · exact bytesAt_pathNode hB1.inputs hc24 hz
  -- piece b: the left child's words
  refine ev_at (hpc1.trans (pc_after (by rfl)))
    (ldp_child hpre hB1.frame hoffL hx8 (hb58b hp) run_b58b rfl fun st2 hm2 hpc2 hd2 ↦ ?_)
  have hB2 : Base r st2.data := hB1.of_eq hd2 (sp_of hm2 rfl) (reg_of hm2 rfl) (reg_of hm2 rfl)
    (reg_of hm2 rfl) (reg_of hm2 rfl)
  -- piece c: the address's first words, the left child's first word
  refine ev_at (hpc2.trans (pc_after (by rfl))) ?_
  have hwf2 := r.frame_wf hpre hB2.frame (fun _ ↦ 0)
  have h11 : Run.RegIs st2.data .X11 (r.off 12288) := by
    rw [Run.RegIs, reg_of hm2 rfl]; exact (hm1.regs .X11 _ rfl).trans (eval_ptr 12288)
  have h0 : Run.RegIs st2.data .X0 (r.off 8192) := by
    rw [Run.RegIs, reg_of hm2 rfl]; exact (hm1.regs .X0 _ rfl).trans (eval_ptr 8192)
  have hm2' : Match (r.env st2.data) s58c st2.data :=
    match_frameS hpre hB2 ⟨known_ptr h11, known_ptr h0, trivial⟩ trivial
  refine exec_then_elf (hb58c hp) run_b58c hwf2 hm2' fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hB3, hk3⟩ := hB2.of_match hpre hm3 hwf2 rfl rfl rfl rfl rfl rfl
  -- piece d: the right child's words
  have hx10' : Run.RegIs st3.data .X10 (r.off offR) := by
    rw [Run.RegIs, reg_of hm3 rfl, reg_of hm2 rfl]; exact hx10
  have hRc : BytesAt st3.data.dmem (r.off offR) Rc := by
    simp only [offR, Rc]
    split
    · exact bytesAt_pathNode hB3.inputs hc24 hz
    · exact keep_blk hpre hm3 hwf2 hcurl (by decide) rfl (hd2 ▸ hcopy)
  refine ev_at (hpc3.trans (pc_after (by rfl)))
    (ldp_child hpre hB3.frame hoffR hx10' (hb58d hp) run_b58d rfl fun st4 hm4 hpc4 hd4 ↦ ?_)
  have hB4 : Base r st4.data := hB3.of_eq hd4 (sp_of hm4 rfl) (reg_of hm4 rfl) (reg_of hm4 rfl)
    (reg_of hm4 rfl) (reg_of hm4 rfl)
  -- piece e: the rest of the children and of the address, `memset`
  refine ev_at (hpc4.trans (pc_after (by rfl))) ?_
  have hwf4 := r.frame_wf hpre hB4.frame (fun _ ↦ 0)
  have h11' : Run.RegIs st4.data .X11 (r.off 14912) := by
    rw [Run.RegIs, reg_of hm4 rfl]; exact (hm3.regs .X11 _ rfl).trans (eval_ptr 14912)
  have hm4' : Match (r.env st4.data) s58e st4.data :=
    match_frameS hpre hB4 ⟨known_ptr h11', trivial⟩ trivial
  refine exec_then_elf (hb58e hp) run_b58e hwf4 hm4' fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hB5, hk5⟩ := hB4.of_match hpre hm5 hwf4 rfl rfl rfl rfl rfl rfl
  -- registers through the pieces
  have e19 : st5.data.regs.getXReg .X19 = m.regs.getXReg .X19 := by
    rw [reg_of hm5 rfl, reg_of hm4 rfl, reg_of hm3 rfl, reg_of hm2 rfl, reg_of hm1 rfl]
  have e25 : st5.data.regs.getXReg .X25 = m.regs.getXReg .X25 := by
    rw [reg_of hm5 rfl, reg_of hm4 rfl, reg_of hm3 rfl, reg_of hm2 rfl, reg_of hm1 rfl]
  have e21 : st4.data.regs.getXReg .X21 = m.regs.getXReg .X21 := by
    rw [reg_of hm4 rfl, reg_of hm3 rfl, reg_of hm2 rfl, reg_of hm1 rfl]
  have e12 : (st4.data.regs.getXReg .X12).toBitVec = BitVec.ofNat 64 (r.leafOf c) := by
    rw [reg_of hm4 rfl, reg_of hm3 rfl, reg_of hm2 rfl, hm1.regs .X12 _ rfl]
    exact hl440
  have h19' : (st4.data.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 c := by
    rw [reg_of hm4 rfl, reg_of hm3 rfl, reg_of hm2 rfl, reg_of hm1 rfl]; exact h19
  have h21'' : (st4.data.regs.getXReg .X21).toBitVec = BitVec.ofNat 64 z := by rw [e21]; exact h21
  have h25' : (st4.data.regs.getXReg .X25).toBitVec = kpW r := by
    rw [reg_of hm4 rfl, reg_of hm3 rfl, reg_of hm2 rfl, reg_of hm1 rfl]; exact h25
  have h0' : Run.RegIs st5.data .X0 (r.off 8640) := by
    rw [Run.RegIs, reg_of hm5 rfl, reg_of hm4 rfl]; exact (hm3.regs .X0 _ rfl).trans (eval_ptr 8640)
  have h1' : st5.data.regs.X1 = 0 := by
    show st5.data.regs.getXReg .X1 = 0
    rw [reg_of hm5 rfl, reg_of hm4 rfl, reg_of hm3 rfl, reg_of hm2 rfl]
    exact UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)
  have h2' : st5.data.regs.X2.toNat = 344 := by
    show (st5.data.regs.getXReg .X2).toNat = 344
    rw [reg_of hm5 rfl, reg_of hm4 rfl, reg_of hm3 rfl, reg_of hm2 rfl]
    exact regIs_toNat (hm1.regs .X2 _ rfl) (by decide)
  -- the children in `st5`
  have hLc0 := bytesAt_slice hLc 0 8
  have hLc8 := bytesAt_slice hLc 8 8
  have hRc0 := bytesAt_slice hRc 0 8
  have hRc8 := bytesAt_slice hRc 8 8
  rw [List.drop_zero] at hLc0 hRc0
  have hch5 : BytesAt st5.data.dmem (r.off 14912) (r.childrenOf c z) := by
    rw [hch]
    refine bytesAt_cat (n := 16) hLl (pieces16 hLl ?_ ?_) (pieces16 hRl ?_ ?_)
    · refine keep_blk hpre hm5 hwf4 (n := 8) (by simp [hLl]) (by decide) rfl (hd4 ▸ ?_)
      refine write_reg hm3 (o := 14912) (n := 8) (x := .X9) (by decide) (by decide) ?_
      rw [hm2.regs .X9 _ rfl]
      exact bytes_load_off hLc0 (by simp [hLl]) le_rfl
    · refine write_reg hm5 (o := 14920) (n := 8) (x := .X8) (by decide) (by decide) ?_
      rw [reg_of hm4 rfl, reg_of hm3 rfl, hm2.regs .X8 _ rfl]
      exact bytes_load_off hLc8 (by simp [hLl]) le_rfl
    · refine write_reg hm5 (o := 14912 + 16) (n := 8) (x := .X9) (by decide) (by decide) ?_
      rw [hm4.regs .X9 _ rfl]
      exact bytes_load_off hRc0 (by simp [hRl]) le_rfl
    · refine write_reg hm5 (o := 14912 + 16 + 8) (n := 8) (x := .X10) (by decide) (by decide) ?_
      rw [hm4.regs .X10 _ rfl]
      exact bytes_load_off hRc8 (by simp [hRl]) le_rfl
  -- the address in `st5`
  have had5 : BytesAt st5.data.dmem (r.off 15936) (r.nodeAdrsOf c z) := by
    rw [nodeAdrsOf_eq]
    refine bytesAt_cat (n := 8) rfl ?_ (bytesAt_cat (n := 8) rfl ?_ (bytesAt_cat (n := 4) rfl ?_
      (bytesAt_cat (n := 4) rfl ?_ (bytesAt_cat (n := 4) rfl ?_ ?_))))
    · refine keep_blk hpre hm5 hwf4 (n := 8) rfl (by decide) rfl (hd4 ▸ ?_)
      exact write_val hm3 (o := 15936) (n := 8) rfl (by decide) (by decide) bytes_zero8
    · refine keep_blk hpre hm5 hwf4 (n := 8) rfl (by decide) rfl (hd4 ▸ ?_)
      refine write_reg hm3 (o := 15936 + 8) (n := 8) (x := .X20) (by decide) (by decide) ?_
      rw [bytes_reg, reg_of hm2 rfl, reg_of hm1 rfl]
      exact h20
    · exact write_val hm5 (o := 15936 + 8 + 8) (n := 4) rfl (by decide) (by decide) bytes_typeW
    · refine write_reg hm5 (o := 15936 + 8 + 8 + 4) (n := 4) (x := .X25) (by decide) (by decide) ?_
      rw [h25']
      exact bytes_kpW r
    · refine write_val hm5 (o := 15936 + 8 + 8 + 4 + 4) (n := 4) rfl (by decide) (by decide) ?_
      simp only [Sym.eval, Env.ofMachine_regs, h21'']
      exact bytes_height z
    · refine write_val hm5 (o := 15936 + 8 + 8 + 4 + 4 + 4) (n := 4) rfl (by decide) (by decide) ?_
      simp only [Sym.eval, Env.ofMachine_regs, h21'', h19', e12]
      exact bytes_index hz hl
  -- `memset` of hasher A
  refine call_then_elf hpc5 hc.2.1 (r.memset_pre hpre hB5.frame h0' h2' (by decide)) fun st6 hpc6 hpost ↦ ?_
  obtain ⟨hz6, hout6, hS6⟩ := r.memset_out h0' h2' hpost
  obtain ⟨hB6, hk6⟩ := hB5.of_call hpre hS6 (a := 8640) (n := 344) (N := 0) (by decide) (by decide)
    hout6 (fun o h1 h2 ↦ by unfold Scr; omega)
  have hkeep := hk1.trans ((Keep.of_eq hd2).trans (hk3.trans ((Keep.of_eq hd4).trans (hk5.trans hk6))))
  have hkc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21616)
      (hd : o + bs.length ≤ 8640 ∨ 8640 + 344 ≤ o) (h : BytesAt st5.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hB5.frame (a := 8640) (n := 344) (N := 0) (by decide) (by decide) hout6
      ho hd h
  have hchl : (r.childrenOf c z).length = 32 := by rw [hch]; simp [hLl, hRl]
  have hadl : (r.nodeAdrsOf c z).length = 32 := by rw [nodeAdrsOf_eq]; rfl
  refine .done _ ⟨hpc6.trans (pc_after (by rfl)), TreeSt.of_keep hT hB6 hkeep, hz, ?_, ?_, ?_, ?_,
    hkc (by rw [hchl]; omega) (by rw [hchl]; omega) hch5,
    hkc (by rw [hadl]; omega) (by rw [hadl]; omega) had5⟩
  · rw [Run.RegIs, hS6.1 .X19 rfl, e19]; exact h19
  · rw [Run.RegIs, hS6.1 .X21 rfl, hm5.regs .X21 _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h21'', BitVec.ofNat_add]
  · rw [Run.RegIs, hS6.1 .X25 rfl, e25]; exact h25
  · rw [h1'] at hz6; exact hz6

end

end NativeRustcArm.SphincsVerifyProof.Fors
