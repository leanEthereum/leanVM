module

public import NativeRustcVmX64.Wire.PhaseM.Rows
public import NativeRustcVmX64.Spec.Keccak
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords.Names

/-!
# `phase_m`: the first level's nodes (x86-64)

`hash_run`: from the first leaf's hash (`HashSt … 0`), each leaf `i` hashed by
`keccak256_words::<hash_words's closure>` into the frame's byte `80` (`b26`, the position to the
frame's byte `72`), and its node, the position and the digest, stored at the working area's byte
`4096 + 40 i` (`b27`), to the climb's set-up (`Climb0`, `b28`).
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write load_ofMachine
  stackOk_callee mapped_off frame_mapped RcAt.callee eval_ptr0)
open NativeRustcVmX64.Sumcheck (wordsAt_written wordAt_written)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off Mapped.keeps)
open NativeRustcVmX64.Wire.Decode (eqv_eval)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **The climb's set-up** (`b28`): every leaf hashed. -/
structure Climb0 [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8)
    (c k count : Nat) (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 : Nat)
    (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b28Offset)
  bod : Bod m0 8 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  rd : ReaderAt st.data.dmem (RD m0) bp B c6
  rbp : (reg st.data .rbp).toNat = (sortD qs).length
  rbx : reg st.data .rbx = wa m0 2048
  r9 : (reg st.data .r9).toNat = lw
  nodes : NodesAt st.data.dmem (wa m0 4096) (nodes0 qs lw rows)

end

public section

theorem apartN {a a' : BitVec 64} {n n' : Nat}
    (h : a.toNat + n ≤ a'.toNat ∨ a'.toNat + n' ≤ a.toNat) : NativeRustcX64.Apart a n a' n' := h

theorem noWrapN {a : BitVec 64} {n : Nat} (h : a.toNat + n ≤ 2 ^ 64) : NativeRustcX64.NoWrap a n := h

/-- Numerical GOT separation for the hash call, independent of its symbolic machine state. -/
private theorem got_hash_apart {p s : Nat} (hsp : 1216 ≤ s)
    (h : p + 8 ≤ s - 1216 ∨ s - 1216 + 1224 ≤ p) :
    (p + 8 ≤ s - 160 - 768 ∨ s - 160 - 768 + (768 + 8) ≤ p) ∧
    (p + 8 ≤ s - 160 + 80 ∨ s - 160 + 80 + 32 ≤ p) := by
  have h928 : 928 ≤ s := Nat.le_trans (by decide) hsp
  have h160 : 160 ≤ s := Nat.le_trans (by decide) hsp
  rw [Nat.sub_sub]
  rcases h with h | h
  · constructor
    · exact Or.inl (Nat.le_trans h (Nat.sub_le_sub_left (by decide) s))
    · exact Or.inl (Nat.le_trans h (Nat.le_trans
        (Nat.sub_le_sub_left (by decide : 160 ≤ 1216) s) (Nat.le_add_right _ _)))
  · have hp : s + 8 ≤ p := by
      have he : s - 1216 + 1224 = s + 8 := by
        change s - 1216 + (1216 + 8) = s + 8
        rw [← Nat.add_assoc, Nat.sub_add_cancel hsp]
      exact he ▸ h
    constructor
    · apply Or.inr
      apply Nat.le_trans _ hp
      calc
        s - 928 + (768 + 8) ≤ s - 928 + 928 := Nat.add_le_add_left (by decide) _
        _ = s := Nat.sub_add_cancel h928
        _ ≤ s + 8 := Nat.le_add_right _ _
    · apply Or.inr
      apply Nat.le_trans _ hp
      calc
        s - 160 + 80 + 32 = s - 160 + 112 := Nat.add_assoc _ _ _
        _ ≤ s - 160 + 160 := Nat.add_le_add_left (by decide) _
        _ = s := Nat.sub_add_cancel h160
        _ ≤ s + 8 := Nat.le_add_right _ _

theorem length_nodes0 {qs : List Nat} {lw : Nat} {rows : List (List K)}
    (h : rows.length = (sortD qs).length) : (nodes0 qs lw rows).length = (sortD qs).length := by
  simp [h]

theorem nodes0_get {qs : List Nat} {lw : Nat} {rows : List (List K)} {i : Nat}
    (hl : rows.length = (sortD qs).length) (hi : i < (sortD qs).length) :
    (nodes0 qs lw rows)[i]'(by simp [hl]; omega) = ((sortD qs)[i],
      NativeVm.Model.hashWords
        (((leavesOf lw rows)[i]'(by simp [hl]; omega)).map K.lane).toArray) := by
  simp only [nodes0, List.getElem_zip, List.getElem_map, leaf_hash]

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

omit [Host] in
/-- **A reader kept** by a change in the stack and the working area. -/
theorem reader_sw [Labels] (G : Geo m0 bp B.length) {d d' : Mem 64} {c' : Nat}
    (h : ReaderAt d (RD m0) bp B c') {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → (SP0 m0 - 1216 ≤ q.toNat ∧ q.toNat < SP0 m0) ∨
      ((WK m0).toNat ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 483584)) :
    ReaderAt d' (RD m0) bp B c' := by
  have := G.sR; have := G.sB; have := G.rW; have := G.bW
  exact reader_keep h hs (fun q hq ↦ by have := hR q hq; omega)
    (fun q hq ↦ by have := hR q hq; omega)

/-- **A leaf hashed**: from leaf `i`'s head, to the next one's or to the climb's set-up. -/
theorem hash_step (hp : Placed code k) (G : Geo m0 bp B.length)
    (hkw : Spec (Labels.label NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost)
    {count : Nat} {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 i : Nat}
    {st : MachineState} (h : HashSt m0 bp B c k count qs height lw rows c6 i st) :
    Eventually (step1 Host.exe) (fun st' ↦
      HashSt m0 bp B c k count qs height lw rows c6 (i + 1) st' ∨
      Climb0 m0 bp B c k count qs height lw rows c6 st') st := by
  obtain ⟨hpc, hbod, hM, hrd, hbp, hbx, h9, h13, h15, hcx, hf64, hi, hnd⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsW := G.sW
  have hsC := G.sC
  have hcn := G.cNw
  have hps := hM.ps256
  have hl := hM.rlen
  have hlw := hM.lw64
  set n := (sortD qs).length with hn
  have hw2 := G.wa (o := 2048) (by omega)
  have hwi := G.wa (o := 8 * i) (by omega)
  have hwl := G.wa (o := 352512 + 512 * i) (by omega)
  have hwn4 := G.wa (o := 4096) (by omega)
  have hwnd := G.wa (o := 4096 + 40 * i) (by omega)
  have hfr80 : (off (stackBelow m0 160) 80).toNat = SP0 m0 - 160 + 80 := G.fr (by omega)
  -- `b26`: the position to `72`, the call's arguments.
  have h15' : reg st.data .r15 = BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    rw [h15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm26 : Match (aEnv m0 st.data (8 * i) 2056 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b26Offset + b26.length)).toBitVec)
      posS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st.data .r14)
            (BinOp.apply .mul .W64 (reg st.data .r15) (BitVec.ofNat 64 8)) =
          wa m0 (8 * i) + BitVec.ofInt 64 0
        rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero]
        apply BitVec.eq_of_toNat_eq
        simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_mul,
          BitVec.toNat_ofNat, hbod.r14, h15', hwi]
        rw [Nat.mod_eq_of_lt (a := i) (by omega)]
        omega, trivial⟩
  obtain ⟨hmid26, hw26, hp72, h24, hdi26, hsi26, hdx26, hcx26, hr826, h1526, hk26⟩ := ok_b26
  refine ablk hp G b26_in_code (by simp [b26]) exit_b26 (by omega) (by omega) hmid26
    (fun w hw ↦ .inl ⟨(hw26 w hw).1, by have := (hw26 w hw).2; omega,
      by have := (hw26 w hw).2; omega⟩)
    (hk26 .r12 (by simp)) (hk26 .r14 (by simp)) hpc hbod hm26
    fun s1 hb1 _ hkeep1 hsw1 hm1 hpc1 ↦ ?_
  have hs1 : NativeRustcVm.SameOutside st.data.dmem s1.data.dmem (fun q ↦
      (SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 152) ∨
      (SP0 m0 - 136 ≤ q.toNat ∧ q.toNat < SP0 m0 - 128) ∨
      (SP0 m0 - 88 ≤ q.toNat ∧ q.toNat < SP0 m0 - 80)) := hsw1.mono fun q ⟨w, hw, h⟩ ↦ by
    have := hw26 w hw
    rcases h with ⟨-, h1, h2⟩ | ⟨h, -⟩ <;> omega
  have env26 : ∀ x, (aEnv m0 st.data (8 * i) 2056
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b26Offset + b26.length)).toBitVec).regs x = reg st.data x := fun _ ↦ rfl
  have h9' : (reg st.data .r9).toNat = lw := h9
  have hl64 : ((aEnv m0 st.data (8 * i) 2056
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b26Offset + b26.length)).toBitVec).load 0 64 8) = (8 * lw).toUInt64.toBitVec :=
    load_ofMachine (o := 64) rfl hf64
  have hdi1 : reg s1.data .rdi = off (stackBelow m0 160) 80 :=
    (hm1.regs .rdi _ hdi26).trans (eval_ptr0 80)
  have hsi1 : (reg s1.data .rsi).toNat = lw := by
    rw [show reg s1.data .rsi = _ from hm1.regs .rsi _ hsi26]; exact h9'
  have hr81 : (reg s1.data .r8).toNat = lw := by
    rw [show reg s1.data .r8 = _ from hm1.regs .r8 _ hr826]; exact h9'
  have hdx1 : (reg s1.data .rdx).toNat = 8 * lw := by
    rw [show reg s1.data .rdx = _ from hm1.regs .rdx _ hdx26]
    simp only [Sym.eval]
    rw [hl64, UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have hcx1 : reg s1.data .rcx = wa m0 (352512 + 512 * i) :=
    (hm1.regs .rcx _ hcx26).trans hcx
  have hpos : NativeRustcVm.WordAt s1.data.dmem (off (stackBelow m0 160) 72)
      ((sortD qs)[i]'hi).toUInt64 := by
    refine wordAt_written hm1 (r := 0) rfl (by omega) hp72 ?_
    show (aEnv m0 st.data (8 * i) 2056 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b26Offset + b26.length)).toBitVec).load 1 2048 8
      = _
    refine load_ofMachine (o := 2048) (b := wa m0 (8 * i)) rfl ?_
    have := NativeRustcVm.WordsAt.getElem hM.psW (i := i) (by simp; omega)
    simp only [List.getElem_map] at this
    rw [off_off, show 8 * i + 2048 = 2048 + 8 * i by omega]
    simpa [wa, off_off] using this
  have hsp1 : rspOf s1.data = stackBelow m0 160 := by rw [hb1.fr.sp, off_zero]
  have hKS : keccak256WordsStack = 768 := rfl
  obtain ⟨hcs1, -⟩ := callee_toNat (n := keccak256WordsStack) hsp1 (by rw [hKS]; omega)
  have hrcs := G.rc_keep (hbod.chg.trans hs1 |>.mono fun q hq ↦ hq.elim id fun h ↦ .inl (by omega))
  have hpre : Keccak256WordsHashPre s1.data := by
    unfold Keccak256WordsHashPre
    rw [hdi1, hcx1, hr81]
    refine ⟨stackOk_callee G.st hb1.fr.kept hsp1 (by rw [hKS]; omega),
      RcAt.callee G.rc hrcs hsp1 G.sp (by rw [hKS]; omega), hsi1, hdx1,
      mapped_off (N := 483584) (o := 352512 + 512 * i) (k := 8 * lw)
        (Mapped.keeps G.wOk.1 hb1.fr.kept) (by omega), noWrapN (by rw [hwl]; omega),
      mapped_off (N := 168) (o := 80) (k := 32)
        (Mapped.keeps (frame_mapped G.st (by omega)) hb1.fr.kept) (by omega),
      noWrapN (by rw [hfr80]; omega), fun _ ↦ apartN ?_, apartN ?_, apartN ?_, ?_⟩
    · rw [hwl, hcs1, hKS]; omega
    · rw [hfr80, hcs1, hKS]; omega
    · rw [hfr80]; omega
    · refine G.got.transport (G.got_keep hb1.chg) ?_ ?_
      · intro l hl
        have hs := (G.got.1 l hl).2.2.1
        change Apart (gotAddr l) 8 (stackBelow m0 1216) 1224 at hs
        change Apart (gotAddr l) 8 (stackBelow s1.data keccak256WordsStack)
          (keccak256WordsStack + 8)
        unfold NativeRustcX64.Apart at hs ⊢
        rw [stackBelow_toNat G.sp] at hs
        rw [hcs1, hKS]
        exact (got_hash_apart hsp hs).1
      · intro l hl a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · have hs := (G.got.1 l hl).2.2.1
          change Apart (gotAddr l) 8 (stackBelow m0 1216) 1224 at hs
          change Apart (gotAddr l) 8 (off (stackBelow m0 160) 80) 32
          unfold NativeRustcX64.Apart at hs ⊢
          rw [stackBelow_toNat G.sp] at hs
          rw [hfr80]
          exact (got_hash_apart hsp hs).2
        · exact (G.got.1 l hl).2.2.2 (rcAddr, 192) (by simp)
  have hlv1 : NativeRustcVm.WordsAt s1.data.dmem (wa m0 (352512 + 512 * i))
      (((leavesOf lw rows)[i]'(by simp [hl]; omega)).map K.lane) := by
    have := hM.lvW i (by simp [hl]; omega)
    rw [off_off] at this
    have hlen : (((leavesOf lw rows)[i]'(by simp [hl]; omega)).map K.lane).length = lw := by
      simp only [List.length_map, leavesOf, List.getElem_map]
      exact length_paddedLeaf (hM.rw _ (List.getElem_mem _))
    refine wordsAt_keep this hs1 (by rw [hlen, hwl]; omega) fun q hq ↦ ?_
    rw [hlen, hwl]; omega
  simp only [PcOk] at hpc1
  refine call_then (env := aEnv m0 st.data (8 * i) 2056 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b26Offset + b26.length)).toBitVec)
    (l := NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel)
    ⟨hpc1.1, hpc1.2⟩ hkw hpre fun s2 hpc2 hrsp2 ⟨hpost, hso2, hsv2⟩ ↦ ?_
  rw [hdi1, hcx1, hr81] at hpost
  rw [hdi1] at hso2
  have hdig := hpost _ (by
    simp only [List.length_map, leavesOf, List.getElem_map]
    exact length_paddedLeaf (hM.rw _ (List.getElem_mem _))) hlv1
  have hso2' : NativeRustcVm.SameOutside s1.data.dmem s2.data.dmem (fun q ↦
      (SP0 m0 - 80 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) ∨
      (SP0 m0 - 928 ≤ q.toNat ∧ q.toNat < SP0 m0 - 160)) :=
    NativeRustcVm.SameOutside.mono hso2 fun q hq ↦ by
    rcases hq with hq | hq
    · have := iv_of_inRange (by rw [hfr80]; omega) hq
      rw [hfr80] at this; exact .inl ⟨by omega, by omega⟩
    · have := iv_of_inRange (by rw [hcs1, hKS]; omega) hq
      rw [hcs1, hKS] at this; exact .inr ⟨by omega, by omega⟩
  have hb2 : Bod m0 8 s2.data := Bod.call G hb1 hsv2 hrsp2 hso2' fun q hq ↦
    ⟨by unfold Chg; omega, by omega⟩
  have hs12 : NativeRustcVm.SameOutside st.data.dmem s2.data.dmem (fun q ↦
      (SP0 m0 - 928 ≤ q.toNat ∧ q.toNat < SP0 m0 - 152) ∨
      (SP0 m0 - 136 ≤ q.toNat ∧ q.toNat < SP0 m0 - 128) ∨
      (SP0 m0 - 88 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48)) :=
    (hs1.trans hso2').mono fun q hq ↦ by omega
  have hpos2 : FW m0 s2.data.dmem 72 ((sortD qs)[i]'hi).toUInt64 :=
    FW.keep G (by omega) hpos hso2' fun q hq ↦ by omega
  have hf64' : FW m0 s2.data.dmem 64 (8 * lw).toUInt64 :=
    FW.keep G (by omega) hf64 hs12 fun q hq ↦ by omega
  have hW12 : ∀ q : BitVec 64, ((SP0 m0 - 928 ≤ q.toNat ∧ q.toNat < SP0 m0 - 152) ∨
      (SP0 m0 - 136 ≤ q.toNat ∧ q.toNat < SP0 m0 - 128) ∨
      (SP0 m0 - 88 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48)) → Wr m0 q := fun q hq ↦ by
    unfold Wr
    rcases hq with hq | hq | hq
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr (.inl hq)
    · exact .inr (.inr (.inl ⟨by omega, by omega⟩))
  have hM2 : Mid m0 B c count qs height lw rows c6 s2.data.dmem := Mid.keep G hM hs12 hW12
  have hrd2 : ReaderAt s2.data.dmem (RD m0) bp B c6 :=
    reader_sw G hrd hs12 fun q hq ↦ .inl (by omega)
  have hnd2 : NodesAt s2.data.dmem (wa m0 4096) ((nodes0 qs lw rows).take i) := by
    have hti : ((nodes0 qs lw rows).take i).length = i := by
      rw [List.length_take, length_nodes0 hl]; omega
    refine nodes_keep hnd hs12 (by rw [hti, hwn4]; omega) fun q hq ↦ ?_
    rw [hti, hwn4]; omega
  have rk2 : ∀ x ∈ [Reg64.rbp, .rbx, .r13, .r15], reg s2.data x = reg s1.data x := fun x hx ↦ by
    have hc : calleeSaved x = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> rfl
    exact hsv2.1 x hc
  have e13 : (reg s2.data .r13).toNat = 513 + 5 * i := by
    rw [rk2 .r13 (by simp), show reg s1.data .r13 = _ from hm1.regs .r13 _ (hk26 .r13 (by simp))]
    exact h13
  have e15 : (reg s2.data .r15).toNat = i + 1 := by
    rw [rk2 .r15 (by simp), show reg s1.data .r15 = _ from hm1.regs .r15 _ h1526]
    show (BinOp.apply .add .W64 (reg st.data .r15) (BitVec.ofNat 64 1)).toNat = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, h15]
    omega
  have ebp : (reg s2.data .rbp).toNat = n := by
    rw [rk2 .rbp (by simp), show reg s1.data .rbp = _ from hm1.regs .rbp _ (hk26 .rbp (by simp))]
    exact hbp
  have ebx : reg s2.data .rbx = wa m0 2048 := by
    rw [rk2 .rbx (by simp), show reg s1.data .rbx = reg st.data .rbx from
      hm1.regs .rbx (.reg .rbx) (by decide +kernel)]
    exact hbx
  -- `b27`: the node.
  have hm27 : Match (aEnv m0 s2.data (4096 + 40 * i) 40 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b27Offset + b27.length)).toBitVec)
      nodeS s2.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb2.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg s2.data .r14)
            (BinOp.apply .mul .W64 (reg s2.data .r13) (BitVec.ofNat 64 8)) =
          wa m0 (4096 + 40 * i) + BitVec.ofInt 64 8
        rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
        apply BitVec.eq_of_toNat_eq
        simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_mul,
          BitVec.toNat_ofNat, hb2.r14, e13, hwnd]
        omega, trivial⟩
  have hwf27 := aEnv_wf G hb2.fr.kept (o := 4096 + 40 * i) (n := 40) (by omega) (by omega)
    (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b27Offset + b27.length)).toBitVec
  obtain ⟨hmid27, hw27, hkey27, hdg27, hcx27, hr927, h1327, hk27⟩ := ok_b27
  refine ablk hp G b27_in_code (by simp [b27]) exit_b27 (by omega) (by omega) hmid27
    (fun w hw ↦ .inr (hw27 w hw)) (hk27 .r12 (by simp)) (hk27 .r14 (by simp))
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b26_next)) hb2 hm27
    fun s3 hb3 _ _ hsw3 hm3 hpc3 ↦ ?_
  have hs3 : NativeRustcVm.SameOutside s2.data.dmem s3.data.dmem (fun q ↦
      (WK m0).toNat + (4096 + 40 * i) ≤ q.toNat ∧ q.toNat < (WK m0).toNat + (4096 + 40 * i) + 40) :=
    hsw3.mono fun q ⟨w, hw, h⟩ ↦ by
      have := hw27 w hw
      rcases h with ⟨h, -⟩ | ⟨-, h1, h2⟩ <;> omega
  have env27 : ∀ o v, FW m0 s2.data.dmem o v → (aEnv m0 s2.data (4096 + 40 * i) 40
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b27Offset + b27.length)).toBitVec).load 0 o 8 = v.toBitVec :=
    fun o v h ↦ load_ofMachine (o := o) rfl h
  have hdl : (NativeVm.Model.hashWords (((leavesOf lw rows)[i]'(by simp [hl]; omega)).map
      K.lane).toArray).toList.length = 4 := by simp
  have hnode : NodeAt s3.data.dmem (wa m0 (4096 + 40 * i))
      ((nodes0 qs lw rows)[i]'(by simp [hl]; omega)) := by
    rw [nodes0_get hl hi]
    refine ⟨by have := sortD_lt hM.qlt _ (List.getElem_mem hi); omega, ?_, ?_⟩
    · have := wordAt_written hm3 (r := 1) (o := 0) rfl (by omega) hkey27
        (w := ((sortD qs)[i]'hi).toUInt64) (by simp only [Sym.eval]; exact env27 72 _ hpos2)
      rwa [off_zero] at this
    · refine wordsAt_written hm3 (r := 1) (o := 8) rfl (by omega) hdg27 fun j hj ↦ ?_
      simp only [Sym.eval]
      refine env27 (80 + 8 * j) _ ?_
      have := NativeRustcVm.WordsAt.getElem hdig (i := j) (by rw [hdl]; exact hj)
      rw [show off (stackBelow m0 160) 80 + BitVec.ofNat 64 (8 * j) =
        off (stackBelow m0 160) (80 + 8 * j) from off_add _ _ _] at this
      exact this
  have hti : ((nodes0 qs lw rows).take i).length = i := by
    rw [List.length_take, length_nodes0 hl]; omega
  have hnd3 : NodesAt s3.data.dmem (wa m0 4096) ((nodes0 qs lw rows).take (i + 1)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_nodes0 hl]; omega),
      Option.toList_some]
    refine nodes_snoc ?_ ?_
    · refine nodes_keep hnd2 hs3 (by rw [hti, hwn4]; omega) fun q hq ↦ ?_
      rw [hti, hwn4]; omega
    · rw [hti, off_off]; exact hnode
  have hM3 : Mid m0 B c count qs height lw rows c6 s3.data.dmem :=
    Mid.keep G hM2 hs3 fun q hq ↦ by
      unfold Wr
      exact .inr (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩))))
  have hrd3 : ReaderAt s3.data.dmem (RD m0) bp B c6 :=
    reader_sw G hrd2 hs3 fun q hq ↦ .inr (by omega)
  have hf64'' : FW m0 s3.data.dmem 64 (8 * lw).toUInt64 :=
    FW.keep G (by omega) hf64' hs3 fun q hq ↦ by omega
  -- the registers
  have rk3 : ∀ x ∈ [Reg64.rbp, .r15], reg s3.data x = reg s2.data x := fun x hx ↦
    hm3.regs x _ (hk27 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> simp))
  have ebx3 : reg s3.data .rbx = wa m0 2048 := by
    rw [show reg s3.data .rbx = reg s2.data .rbx from hm3.regs .rbx (.reg .rbx) (by decide +kernel)]
    exact ebx
  have e9 : (reg s3.data .r9).toNat = lw := by
    rw [show reg s3.data .r9 = _ from hm3.regs .r9 _ hr927]
    simp only [Sym.eval]
    rw [env27 16 _ hM2.f16, UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have e13' : (reg s3.data .r13).toNat = 513 + 5 * (i + 1) := by
    rw [show reg s3.data .r13 = _ from hm3.regs .r13 _ h1327]
    show (BinOp.apply .add .W64 (BitVec.ofNat 64 5) (reg s2.data .r13)).toNat = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, e13]
    omega
  have hcx2 : FW m0 s2.data.dmem 24 (UInt64.ofBitVec (wa m0 (352512 + 512 * i))) := by
    have h24' := wordAt_write hm1 (r := 0) (o := 24) rfl (by omega) h24
    have e : (Sym.reg .rcx).eval (aEnv m0 st.data (8 * i) 2056
        (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b26Offset + b26.length)).toBitVec) = wa m0 (352512 + 512 * i) := hcx
    rw [e] at h24'
    exact FW.keep G (by omega) h24' hso2' fun q hq ↦ by omega
  have ecx : reg s3.data .rcx = wa m0 (352512 + 512 * (i + 1)) := by
    rw [show reg s3.data .rcx = _ from hm3.regs .rcx _ hcx27]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 512) ((aEnv m0 s2.data (4096 + 40 * i) 40
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b27Offset + b27.length)).toBitVec).load 0 24 8) = _
    rw [env27 24 _ hcx2, add_off']
    show off (wa m0 (352512 + 512 * i)) 512 = _
    rw [off_off, show 352512 + 512 * i + 512 = 352512 + 512 * (i + 1) by omega]
  simp only [PcOk] at hpc3
  have hc : (SBool.cmp .eq .W64 (.reg .rbp) (.reg .r15)).not.eval (aEnv m0 s2.data
      (4096 + 40 * i) 40 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b27Offset + b27.length)).toBitVec) = !decide (n = i + 1) := by
    show (!CmpOp.apply .eq .W64 (reg s2.data .rbp) (reg s2.data .r15)) = _
    rw [eqv_eval, ebp, e15]
  rw [hc] at hpc3
  by_cases hlast : n = i + 1
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    rw [List.take_of_length_le (by rw [length_nodes0 hl]; omega)] at hnd3
    exact .done _ (.inr ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b27_next), hb3, hM3, hrd3,
      by rw [rk3 .rbp (by simp)]; exact ebp, ebx3, e9, hnd3⟩)
  · simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc3
    exact .done _ (.inl ⟨hpc3.trans (hp.label NativeRustcVmX64.Vm.PhaseM.label_17_at), hb3, hM3, hrd3,
      by rw [rk3 .rbp (by simp)]; exact ebp, ebx3, e9, e13', by rw [rk3 .r15 (by simp)]; exact e15,
      ecx, hf64'', by omega, hnd3⟩)

/-- **The leaves hashed.** -/
theorem hash_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hkw : Spec (Labels.label NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre
      Keccak256WordsHashPost)
    {count : Nat} {qs : List Nat} {height lw : Nat} {rows : List (List K)} {c6 : Nat}
    {st : MachineState} (h : HashSt m0 bp B c k count qs height lw rows c6 0 st) :
    Eventually (step1 Host.exe) (Climb0 m0 bp B c k count qs height lw rows c6) st :=
  Sym.loop (tr := step1 Host.exe)
    (fun n st ↦ ∃ i, n = (sortD qs).length - i ∧
      HashSt m0 bp B c k count qs height lw rows c6 i st)
    (fun _ _ ⟨i, hn, hi⟩ ↦ Eventually.mono (hash_step hp G hkw hi) fun _ h' ↦ by
      rcases h' with h' | h'
      · exact .inr ⟨_, by have := hi.ilt; omega, i + 1, rfl, h'⟩
      · exact .inl h')
    ⟨0, rfl, h⟩

end

end NativeRustcVmX64.Wire.PhaseM
