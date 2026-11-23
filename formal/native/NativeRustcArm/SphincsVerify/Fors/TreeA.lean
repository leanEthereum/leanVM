module

public import NativeRustcArm.SphincsVerify.Fors.Node4

/-!
# A FORS tree's leaf, part 1: the loop's set-up and the leaf's address (`b59`, `b60`)

`b59` (from `AtFors`) spills the index (`384`), the leaves' copy (`400`) and the tree's word
(`408`), and sets up the trees' loop: `AtTree 0` at `b60` (`.LSphincsVerify_21`). At a tree's head
`b60` loads its leaf index (spilled at `424`), writes the leaf's address at `24720` and calls
`memset` on hasher A (`T1` at `b61`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- What the trees' loop keeps besides `Base`: the roots before tree `c`. -/
structure Roots (r : Run) (c : Nat) (m : MachineData) : Prop where
  base : Base r m
  hc : c < 24
  roots : BytesAt m.dmem (r.off 27808) ((List.range c).map r.forsRoot).flatten

/-- **At a tree's head** `b60`. -/
structure AtTree (r : Run) (c : Nat) (m : MachineData) : Prop where
  rs : Roots r c m
  x19 : Run.RegIs m .X19 (BitVec.ofNat 64 c)
  x24 : Run.RegIs m .X24 (r.off 25752)
  x9 : Run.RegIs m .X9 (r.off 8244)
  x8 : Run.RegIs m .X8 (BitVec.ofNat 64 176)
  x23 : Run.RegIs m .X23 (r.off 21648)
  x25 : Run.RegIs m .X25 (BitVec.ofNat 64 typeW)
  x26 : Run.RegIs m .X26 (kpW r)
  x27 : wordBytes (m.regs.getXReg .X27) = be64 (r.key 0).tree

/-- **At `b61`**: hasher A zero, the leaf's address at `24720`, the leaf index at `424`; X24 the
tree's opening. -/
structure T1 (r : Run) (c : Nat) (m : MachineData) : Prop where
  rs : Roots r c m
  x19 : Run.RegIs m .X19 (BitVec.ofNat 64 c)
  x24 : Run.RegIs m .X24 (r.off (8244 + 176 * c))
  x23 : Run.RegIs m .X23 (r.off 21648)
  x25 : Run.RegIs m .X25 (BitVec.ofNat 64 typeW)
  x26 : Run.RegIs m .X26 (kpW r)
  x27 : wordBytes (m.regs.getXReg .X27) = be64 (r.key 0).tree
  w424 : r.WordAt m 424 (r.leafOf c).toUInt64
  a : BytesAt m.dmem (r.off 16400) (List.replicate 344 0)
  ad : BytesAt m.dmem (r.off 24720) (forsNodeAdrs r.idx c 0 (r.leafOf c))

end

public section

variable {r : Run}

theorem length_leaves : r.leaves.length = 24 := by
  show (digestFields _).2.length = 24
  simp [digestFields]

/-- Tree `c`'s leaf index in the leaves' copy. -/
theorem wordAt_leaf {m : MachineData} (h : BytesAt m.dmem (r.off 25752)
    (wordsBytes (r.leaves.map Nat.toUInt64))) {c : Nat} (hc : c < 24) :
    r.WordAt m (25752 + 8 * c) (r.leafOf c).toUInt64 := by
  have := bytesAt_slice h (8 * c) (8 * 1)
  rw [slice_wordsBytes] at this
  have e : ((r.leaves.map Nat.toUInt64).drop c).take 1 = [(r.leafOf c).toUInt64] := by
    have hl : c < (r.leaves.map Nat.toUInt64).length := by simp [length_leaves, hc]
    rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem hl, Option.toList_some,
      List.getElem_map, Run.leafOf, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [length_leaves]; exact hc), Option.getD_some]
  rw [e] at this
  show BytesAt m.dmem (r.off (25752 + 8 * c)) (wordBytes (r.leafOf c).toUInt64)
  simpa [Native.Keccak.wordsBytes] using this

theorem bytes_zero4 : (List.range 4).map (byteOf (BitVec.ofNat 64 0)) = be32 0 := by
  decide

theorem memExt3 : ∀ c < 24,
    (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 (BitVec.ofNat 64 c)).toNat = 8 * c := by
  decide +kernel

/-- The leaf's index word, as `b60` computes it. -/
theorem bytes_leafIndex {c l : Nat} (hc : c < 24) (x : BitVec 64)
    (hx : x.toNat = l) :
    (List.range 4).map (byteOf (UnOp.apply .rev .W32 (BinOp.apply .add .W32 x
      (UnOp.apply (.shift .LSL 10) .W32 (BitVec.ofNat 64 c))))) =
      be32 ((c <<< (10 - 0)) + l).toUInt32 := by
  rw [bytes_rev32]
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.toUInt32_eq, UInt32.toNat_ofNat']
  simp only [BinOp.apply, UnOp.apply, shiftW, ext_W32, low_W32, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, hx]
  rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
  omega

/-- The leaf's address, in the pieces `b60` writes. -/
theorem leafAdrs_eq (r : Run) (c l : Nat) :
    forsNodeAdrs r.idx c 0 l = (be32 0 ++ be32 0) ++ (be64 (r.key 0).tree ++ (be32 3 ++
      (be32 (r.key 0).leaf ++ (be32 0 ++ be32 ((c <<< (10 - 0)) + l).toUInt32)))) := by
  rw [forsNodeAdrs_eq, adrsBytes, List.append_assoc]
  rfl

theorem length_forsNodeAdrs (idx : UInt64) (c z j : Nat) : (forsNodeAdrs idx c z j).length = 32 := by
  rw [forsNodeAdrs_eq]; rfl

theorem length_rootsMem {c : Nat} (hc : c ≤ 24) :
    ((List.range c).map r.forsRoot).flatten.length = 16 * c :=
  length_roots c fun i hi ↦ length_forsRoot (by omega)

/-- The roots kept by a block that does not write their 384 bytes. -/
theorem roots_blk [Labels] (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (r.env m vars) S m') (hwf : (r.env m vars).WF) {c : Nat} (hc : c ≤ 24)
    (hn : Run.noWriteIn S 27808 384 = true)
    (h : BytesAt m.dmem (r.off 27808) ((List.range c).map r.forsRoot).flatten) :
    BytesAt m'.dmem (r.off 27808) ((List.range c).map r.forsRoot).flatten := by
  have hl := length_rootsMem (r := r) hc
  refine r.bytesAt_kept hpre hm hwf (by rw [hl]; omega) h ?_
  simp only [Run.noWriteIn, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hn ⊢
  intro w hw
  rcases hn w hw with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (by rw [hl]; omega)

/-- The roots kept by a call writing in the scratch. -/
theorem roots_call [Labels] (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m) {a n N : Nat}
    (ha : a + n ≤ 27808) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) {c : Nat} (hc : c ≤ 24)
    (h : BytesAt m.dmem (r.off 27808) ((List.range c).map r.forsRoot).flatten) :
    BytesAt m'.dmem (r.off 27808) ((List.range c).map r.forsRoot).flatten := by
  have hl := length_rootsMem (r := r) hc
  exact r.bytesAt_of_call hpre hF (by omega) hN hout (by rw [hl]; omega) (Or.inr ha) h

variable [Host]

/-- **A tree's head** (`b60` and `memset`): from `AtTree`, `T1` at `b61`. -/
theorem tree_s1 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c : Nat} {m : MachineData}
    (h : AtTree r c m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b61Offset ∧ T1 r c st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b60Offset⟩ := by
  obtain ⟨⟨hB, hc24, hroots⟩, h19, h24, h9, h8, h23, h25, h26, h27⟩ := h
  have hwf := r.frame_wf hpre hB.frame (fun _ ↦ 0)
  have h19' : (m.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 c := h19
  have hm : Match (r.env m) s60 m :=
    match_frameS hpre hB ⟨known_ptr h24, known_ptr h9, h8, known_ptr h23, h25, trivial⟩
      ⟨by show (m.regs.getXReg .X19).toBitVec.toNat < 24; rw [h19', BitVec.toNat_ofNat]; omega,
        trivial⟩
  refine exec_then (hb60 hp) run_b60 hwf hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hB1, hk1⟩ := hB.of_matchLow hpre hm1 hwf rfl rfl rfl rfl rfl rfl
  have hleaf := r.leafOf_lt hc24
  have hload : (r.env m).load 0 (25752 + (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64
      (m.regs.getXReg .X19).toBitVec).toNat) 8 = (r.leafOf c).toUInt64.toBitVec := by
    rw [h19', memExt3 c hc24]
    exact load_word (wordAt_leaf hB.leaves hc24)
  have hlx : (r.leafOf c).toUInt64.toBitVec.toNat = r.leafOf c := by
    rw [UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  have h0 : Run.RegIs st1.data .X0 (r.off 16400) := (hm1.regs .X0 _ rfl).trans (eval_ptr 16400)
  have h1 : st1.data.regs.X1 = 0 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)
  have h2 : st1.data.regs.X2.toNat = 344 := regIs_toNat (hm1.regs .X2 _ rfl) (by decide)
  have hw424 : r.WordAt st1.data 424 (r.leafOf c).toUInt64 := by
    refine write_val hm1 (o := 424) (n := 8) rfl (by decide) (by decide) ?_
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hload]
    exact bytes_reg _
  have had : BytesAt st1.data.dmem (r.off 24720) (forsNodeAdrs r.idx c 0 (r.leafOf c)) := by
    rw [leafAdrs_eq]
    refine bytesAt_cat (n := 8) rfl ?_ (bytesAt_cat (n := 8) rfl ?_ (bytesAt_cat (n := 4) rfl ?_
      (bytesAt_cat (n := 4) rfl ?_ (bytesAt_cat (n := 4) rfl ?_ ?_))))
    · exact write_val hm1 (o := 24720) (n := 8) rfl (by decide) (by decide) bytes_zero8
    · refine write_reg hm1 (o := 24720 + 8) (n := 8) (x := .X27) (by decide) (by decide) ?_
      rw [bytes_reg]
      exact h27
    · exact write_val hm1 (o := 24720 + 8 + 8) (n := 4) rfl (by decide) (by decide) bytes_typeW
    · refine write_reg hm1 (o := 24720 + 8 + 8 + 4) (n := 4) (x := .X26) (by decide) (by decide) ?_
      rw [h26]
      exact bytes_kpW r
    · exact write_val hm1 (o := 24720 + 8 + 8 + 4 + 4) (n := 4) rfl (by decide) (by decide)
        bytes_zero4
    · refine write_val hm1 (o := 24720 + 8 + 8 + 4 + 4 + 4) (n := 4) rfl (by decide) (by decide) ?_
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [hload, h19']
      exact bytes_leafIndex hc24 _ hlx
  have hroots1 := roots_blk hpre hm1 hwf hc24.le rfl hroots
  refine call_then hpc1 hc.2.1 (r.memset_pre hpre hB1.frame h0 h2 (by decide)) fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hz, hout, hS⟩ := r.memset_out h0 h2 hpost
  obtain ⟨hB2, -⟩ := hB1.of_call hpre hS (a := 16400) (n := 344) (N := 0) (by decide) (by decide)
    hout (fun o h1 h2 ↦ by unfold Scr; omega)
  have hkc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29376)
      (hd : o + bs.length ≤ 16400 ∨ 16400 + 344 ≤ o) (h : BytesAt st1.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hB1.frame (a := 16400) (n := 344) (N := 0) (by decide) (by decide) hout
      ho hd h
  refine .done _ ⟨hpc2.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b60_next), ⟨⟨hB2, hc24, roots_call hpre hB1.frame
    (by decide) (by decide) hout hc24.le hroots1⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    hkc (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; decide) hw424, ?_,
    hkc (by rw [length_forsNodeAdrs]; decide) (by rw [length_forsNodeAdrs]; decide) had⟩⟩
  · rw [Run.RegIs, hS.1 .X19 rfl, reg_of hm1 rfl]; exact h19
  · rw [Run.RegIs, hS.1 .X24 rfl, hm1.regs .X24 _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h19']
    show BitVec.ofNat 64 c * BitVec.ofNat 64 176 + (r.base + BitVec.ofInt 64 8244) = _
    simp only [Run.off]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  · rw [Run.RegIs, hS.1 .X23 rfl]; exact (hm1.regs .X23 _ rfl).trans (eval_ptr 21648)
  · rw [Run.RegIs, hS.1 .X25 rfl]; exact hm1.regs .X25 _ rfl
  · rw [Run.RegIs, hS.1 .X26 rfl, reg_of hm1 rfl]; exact h26
  · rw [hS.1 .X27 rfl, reg_of hm1 rfl]; exact h27
  · rw [h1] at hz; exact hz

end

end NativeRustcArm.SphincsVerifyProof.Fors
