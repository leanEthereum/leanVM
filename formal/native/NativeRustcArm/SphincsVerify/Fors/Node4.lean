module

public import NativeRustcArm.SphincsVerify.Fors.Node3

/-!
# A FORS node, part 4: the final absorb and the next value (`b82`, `b83`)

From `N6`: `b82` pads the final block (`0x01` after the input, `0x80` at its end) and XORs it into
hasher A's zero state (`InlineTh.xorFinal`), `keccak_f` permutes it: its first 16 bytes are the
node, `th` of the node's input (`InlineTh.th_short`), the value after `z + 1` steps. `b83` copies
it to `12864` and goes back to the next node's head (`AtNode`), or after the tenth on to `b84`
(`TEnd`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify
open NativeRustcArm.SphincsVerifyProof.InlineTh

@[expose] public section

/-- **At `b84`** (after a tree's tenth node): the root at `12864`. -/
structure TEnd (r : Run) (c : Nat) (m : MachineData) : Prop where
  tree : TreeSt r c m
  x19 : Run.RegIs m .X19 (BitVec.ofNat 64 c)
  x25 : Run.RegIs m .X25 (kpW r)
  x23 : Run.RegIs m .X23 (r.off 15936)
  x20 : wordBytes (m.regs.getXReg .X20) = be64 (r.key 0).tree
  x27 : Run.RegIs m .X27 (r.off 19008)
  cur : BytesAt m.dmem (r.off 12864) (r.forsUpTo c 10)

end

public section

variable {r : Run}

theorem ofNat_beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · rintro rfl
    rfl

/-- **The node** is the first 16 bytes of the permuted padded input. -/
theorem forsUpTo_succ_eq {c z : Nat} (hc : c < 24) (hz : z < 10) :
    r.forsUpTo c (z + 1) =
      (Keccak.keccakF (Keccak.xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn c z)))).take 16 := by
  rw [Run.forsUpTo_succ, Run.forsStep_eq]
  exact th_short (by show (r.nodeIn c z).length < 136; rw [length_nodeIn hc hz]; decide)

theorem length_xorBlock (st blk : List UInt8) : (Keccak.xorBlock st blk).length = 200 := by
  rw [Keccak.xorBlock, length_stateBytes]

/-- A 16-byte value from its two words. -/
theorem copy16 [Labels] {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o o' : Nat} (hle : o + 16 ≤ 21616) {L : List UInt8}
    (hl : L.length = 16)
    (hw1 : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.load 0 o' 8, i))
    (hw2 : ∀ i < 8, findWrite 0 (o + 8 + i) S.mem = some (.load 0 (o' + 8) 8, i))
    (h : BytesAt m.dmem (r.off o') L) : BytesAt m'.dmem (r.off o) L := by
  have h0 := bytesAt_slice h 0 8
  have h8 := bytesAt_slice h 8 8
  rw [List.drop_zero, Nat.add_zero] at h0
  exact pieces16 hl (write_load hm (by omega) le_rfl hw1 (by simp [hl]) h0)
    (write_load hm (by omega) le_rfl hw2 (by simp [hl]) h8)

variable [ElfHost]

/-- **The final absorb and the next value** (`b82`, `keccak_f`, `b83`): from `N6`, the next
node's head, or after the tenth, `b84`. -/
theorem node_s7 (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {c z : Nat} {m : MachineData}
    (h : N6 r c z m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st ↦ (z + 1 < 10 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b58Offset ∧ AtNode r c (z + 1) st.data) ∨
        (z + 1 = 10 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b84Offset ∧ TEnd r c st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b82Offset⟩ := by
  obtain ⟨hT, hz, h27, h19, h21, h25, hst, hblk⟩ := h
  have hB := hT.base
  have hwf := r.frame_wf hpre hB.frame (fun _ ↦ 0)
  have hm : Match (r.env m) s80 m := match_frameS hpre hB ⟨h25, trivial⟩ trivial
  refine exec_then_elf (hb82 hp) run_b82 hwf hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hB1, hk1⟩ := hB.of_match hpre hm1 hwf rfl rfl rfl rfl rfl rfl
  have hil := length_nodeIn (r := r) hT.hc hz
  have hx := xorFinal hm1 hwf (r := 0) (b := r.base) (sz := 21616) rfl (oA := 8640) (oK := 16960)
    (L := 80) (by decide) (by decide +kernel) hil (by decide) hblk
  change BytesAt st1.data.dmem (r.off 8640) (Keccak.xorBlock (bytesOf m.dmem (r.off 8640) 200)
    (finalBlock (r.nodeIn c z))) at hx
  rw [bytesOf_of_bytesAt' hst (List.length_replicate ..)] at hx
  have h0 : Run.RegIs st1.data .X0 (r.off 8640) := (hm1.regs .X0 _ rfl).trans (eval_ptr 8640)
  refine call_then_elf hpc1 hc.2.2.2.2 (keccakF_pre hpre hB1.frame h0 (by decide)) fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hK, hout, hS⟩ := keccakF_out h0 hpost
  obtain ⟨hB2, hk2⟩ := hB1.of_call hpre hS (a := 8640) (n := 200) (N := keccakFStack) (by decide)
    (by decide) hout (fun o h1 h2 ↦ by unfold Scr; omega)
  rw [bytesOf_of_bytesAt' hx (length_xorBlock _ _)] at hK
  have hA : BytesAt st2.data.dmem (r.off 8640) (r.forsUpTo c (z + 1)) := by
    have := bytesAt_slice hK 0 16
    rwa [List.drop_zero, Nat.add_zero, ← forsUpTo_succ_eq hT.hc hz] at this
  -- `b83`
  refine ev_at (hpc2.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b82_next)) ?_
  have hwf2 := r.frame_wf hpre hB2.frame (fun _ ↦ 0)
  have hm2 : Match (r.env st2.data) s0 st2.data := match_frameS hpre hB2 trivial trivial
  refine exec_then_elf (hb83 hp) run_b83 hwf2 hm2 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hB3, hk3⟩ := hB2.of_match hpre hm3 hwf2 rfl rfl rfl rfl rfl rfl
  have hT3 := TreeSt.of_keep hT hB3 (hk1.trans (hk2.trans hk3))
  have hcur : BytesAt st3.data.dmem (r.off 12864) (r.forsUpTo c (z + 1)) :=
    copy16 hm3 (by decide) (length_forsUpTo c (z + 1)) (by decide) (by decide) hA
  have e21 : (st2.data.regs.getXReg .X21).toBitVec = BitVec.ofNat 64 (z + 1) := by
    rw [hS.1 .X21 rfl, reg_of hm1 rfl]; exact h21
  have h19' : Run.RegIs st3.data .X19 (BitVec.ofNat 64 c) := by
    rw [Run.RegIs, hm3.regs .X19 _ rfl]
    show (st2.data.regs.getXReg .X27).toBitVec = _
    rw [hS.1 .X27 rfl, reg_of hm1 rfl]; exact h27
  have h25' : Run.RegIs st3.data .X25 (kpW r) := by
    rw [Run.RegIs, hm3.regs .X25 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hS.1 .X19 rfl, reg_of hm1 rfl, h19]
    exact trunc_kpW
  have h23' : Run.RegIs st3.data .X23 (r.off 15936) := by
    rw [Run.RegIs, reg_of hm3 rfl, hS.1 .X23 rfl]
    exact (hm1.regs .X23 _ rfl).trans (eval_ptr 15936)
  have h27' : Run.RegIs st3.data .X27 (r.off 19008) := (hm3.regs .X27 _ rfl).trans (eval_ptr 19008)
  have e20 : wordBytes (st3.data.regs.getXReg .X20) = be64 (r.key 0).tree := by
    have e := bytes_load (vars := fun _ ↦ 0) hB2.w424 (length_be64 _) le_rfl
    rw [bytes_reg] at e
    rw [show st3.data.regs.getXReg .X20 = UInt64.ofBitVec ((r.env st2.data).load 0 424 8) from
      UInt64.toBitVec_inj.mp (hm3.regs .X20 _ rfl)]
    exact e
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, low_W64, Env.ofMachine_regs, e21] at hpc3
  rw [ofNat_beq_ofNat (by omega) (by decide)] at hpc3
  by_cases hz9 : z + 1 = 10
  · rw [decide_eq_true hz9] at hpc3
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    exact .done _ (Or.inr ⟨hz9, hpc3.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b83_next),
      ⟨hT3, h19', h25', h23', e20, h27', hz9 ▸ hcur⟩⟩)
  · rw [decide_eq_false hz9] at hpc3
    simp only [Bool.not_false, ↓reduceIte] at hpc3
    refine .done _ (Or.inl ⟨by omega, hpc3.trans (lbl_14 hp), ⟨hT3, by omega, h19', ?_,
      e20, h25', hcur⟩⟩)
    rw [Run.RegIs, reg_of hm3 rfl]; exact e21

/-- **A node** (`b58 .. b83`): from its head, the next node's head, or after the tenth, `b84`. -/
theorem node_spec (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {c z : Nat}
    {m : MachineData} (h : AtNode r c z m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st ↦ (z + 1 < 10 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b58Offset ∧ AtNode r c (z + 1) st.data) ∨
        (z + 1 = 10 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b84Offset ∧ TEnd r c st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b58Offset⟩ := by
  refine Eventually.bind_elf (node_s1 hp hc hpre h) fun st ⟨hpc, h1⟩ ↦ ev_at hpc ?_
  refine Eventually.bind_elf (node_s2 hp hc hpre h1) fun st ⟨hpc, h2⟩ ↦ ev_at hpc ?_
  refine Eventually.bind_elf (node_s3 hp hc hpre h2) fun st ⟨hpc, h3⟩ ↦ ev_at hpc ?_
  refine Eventually.bind_elf (node_s4 hp hc hpre h3) fun st ⟨hpc, h4⟩ ↦ ev_at hpc ?_
  refine Eventually.bind_elf (node_s5 hp hc hpre h4) fun st ⟨hpc, h5⟩ ↦ ev_at hpc ?_
  refine Eventually.bind_elf (node_s6 hp hc hpre h5) fun st ⟨hpc, h6⟩ ↦ ev_at hpc ?_
  exact node_s7 hp hc hpre h6

/-- **A tree's nodes**: from its node `z`'s head, `b84` with the root. -/
theorem nodes_spec (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {c : Nat} :
    ∀ n z, z + n = 10 → ∀ m, AtNode r c z m →
      Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b84Offset ∧ TEnd r c st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b58Offset⟩ := by
  intro n
  induction n with
  | zero => intro z hn m h; exact absurd h.hz (by omega)
  | succ n ih =>
    intro z hn m h
    refine Eventually.bind_elf (node_spec hp hc hpre h) fun st hst ↦ ?_
    rcases hst with ⟨-, hpc, h'⟩ | ⟨-, hpc, h'⟩
    · exact ev_at hpc (ih (z + 1) (by omega) _ h')
    · exact .done _ ⟨hpc, h'⟩

end

end NativeRustcArm.SphincsVerifyProof.Fors
