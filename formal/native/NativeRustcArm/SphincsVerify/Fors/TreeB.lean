module

public import NativeRustcArm.SphincsVerify.Fors.TreeA

/-!
# A FORS tree's leaf, part 2: the leaf's `th` with calls (`b52 .. b57`)

From `T1`: `update` of hasher A with `PK.seed` (`b52`) and the leaf's address (`b53`), the clone
into hasher B (`b54`), `update` of B with the tree's secret (`b55`, the opening spilled at `432`),
`finalize` of B to `12864` (`b56`): the leaf, `forsLeaf`, the value after no step; `b57` starts
the nodes: `AtNode c 0` at `b58`. What the stages keep: `TH`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- What the leaf's stages keep: the roots, the registers, the leaf index at `440`. -/
structure TH (r : Run) (c : Nat) (m : MachineData) : Prop where
  rs : Roots r c m
  x19 : Run.RegIs m .X19 (BitVec.ofNat 64 c)
  x21 : Run.RegIs m .X21 (r.off (484 + 176 * c))
  x25 : Run.RegIs m .X25 (kpW r)
  x20 : wordBytes (m.regs.getXReg .X20) = be64 (r.key 0).tree
  w440 : r.WordAt m 440 (r.leafOf c).toUInt64

/-- The leaf's address. -/
def _root_.NativeRustcArm.SphincsVerifyProof.Run.leafAdrs (r : Run) (c : Nat) : List UInt8 := forsNodeAdrs r.idx c 0 (r.leafOf c)

end

public section

variable {r : Run}

/-- `TH` after a call writing the frame's `a .. a + n` in the scratch. -/
theorem TH.of_call [Labels] (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hT : TH r c m) (hS : Saved m m')
    {a n N : Nat} (hs : (8640 ≤ a ∧ a + n ≤ 17992) ∨ (19008 ≤ a ∧ a + n ≤ 20064))
    (hN : N ≤ finalizeStack) (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) :
    TH r c m' := by
  have hB := hT.rs.base
  obtain ⟨hB', -⟩ := hB.of_call hpre hS (a := a) (n := n) (N := N) (by omega) hN hout
    (fun o h1 h2 ↦ by unfold Scr; omega)
  refine ⟨⟨hB', hT.rs.hc, roots_call hpre hB.frame (by omega) hN hout hT.rs.hc.le hT.rs.roots⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Run.RegIs, hS.1 .X19 rfl]; exact hT.x19
  · rw [Run.RegIs, hS.1 .X21 rfl]; exact hT.x21
  · rw [Run.RegIs, hS.1 .X25 rfl]; exact hT.x25
  · rw [hS.1 .X20 rfl]; exact hT.x20
  · exact r.bytesAt_of_call hpre hB.frame (by omega) hN hout (by rw [length_wordBytes]; omega)
      (by rw [length_wordBytes]; omega) hT.w440

/-- `TH` after a block in the frame keeping its registers and writing off its bytes. -/
theorem TH.of_block [Labels] (hpre : r.Pre) {c : Nat} {m m' : MachineData} (hT : TH r c m)
    {S : SState} (hm : Match (r.env m) S m') (hwf : (r.env m).WF)
    (hsp : S.sp = .ptr 0 0) (hx29 : S.reg .X29 = some (.ptr 0 21520)) (hw : lowW S = true)
    (h28 : S.reg .X28 = some (.lit 136)) (h26 : S.reg .X26 = some (.ptr 0 8840))
    (h22 : S.reg .X22 = some (.ptr 0 19208)) (hr : Run.noWriteIn S 20064 384 = true)
    (h440 : Run.noWriteIn S 440 8 = true)
    (r19 : S.reg .X19 = some (.reg .X19)) (r21 : S.reg .X21 = some (.reg .X21))
    (r25 : S.reg .X25 = some (.reg .X25)) (r20 : S.reg .X20 = some (.reg .X20)) : TH r c m' := by
  obtain ⟨hB', -⟩ := hT.rs.base.of_matchLow hpre hm hwf hsp hx29 hw h28 h26 h22
  refine ⟨⟨hB', hT.rs.hc, roots_blk hpre hm hwf hT.rs.hc.le hr hT.rs.roots⟩, ?_, ?_, ?_, ?_,
    keep_blk hpre hm hwf (length_wordBytes _) (by decide) h440 hT.w440⟩
  · rw [Run.RegIs, reg_of hm r19]; exact hT.x19
  · rw [Run.RegIs, reg_of hm r21]; exact hT.x21
  · rw [Run.RegIs, reg_of hm r25]; exact hT.x25
  · rw [reg_of hm r20]; exact hT.x20

theorem holds_zero {d : DataMem} {a : BitVec 64} (h : BytesAt d a (List.replicate 344 0)) :
    HasherHolds (bytesOf d a 344) [] := by
  rw [bytesOf_of_bytesAt' h (List.length_replicate ..)]
  exact holds_new

variable [ElfHost]

/-- **The leaf's `th`** (`b52 .. b57`): from `T1`, the first node's head. -/
theorem tree_s2 (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {c : Nat} {m : MachineData}
    (h : T1 r c m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b58Offset ∧ AtNode r c 0 st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b52Offset⟩ := by
  obtain ⟨hrs, h19, h21, h25, h20, h440, hA, had⟩ := h
  have hT : TH r c m := ⟨hrs, h19, h21, h25, h20, h440⟩
  have hc24 := hrs.hc
  have hadl : (r.leafAdrs c).length = 32 := length_forsNodeAdrs r.idx c 0 (r.leafOf c)
  -- `b52`: `update(A, PK.seed, 16)`
  have hwf := r.frame_wf hpre hrs.base.frame (fun _ ↦ 0)
  have hm : Match (r.env m) s0 m := match_frameS hpre hrs.base trivial trivial
  refine exec_then_elf (hb52 hp) run_b52 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hT1 := hT.of_block hpre hm1 hwf rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hd1 : st1.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have h0 : Run.RegIs st1.data .X0 (r.off 8640) := (hm1.regs .X0 _ rfl).trans (eval_ptr 8640)
  have h1 : Run.RegIs st1.data .X1 (r.off 448) := (hm1.regs .X1 _ rfl).trans (eval_ptr 448)
  have h2 : st1.data.regs.X2.toNat = 16 := regIs_toNat (hm1.regs .X2 _ rfl) (by decide)
  have hH1 : HasherHolds (bytesOf st1.data.dmem (r.off 8640) 344) [] := holds_zero (hd1 ▸ hA)
  refine call_then_elf hpc1 hc.2.2.1 (r.update_pre hpre hT1.rs.base.frame h0 h1 h2 (a := 8640)
    (b := 448) (by decide) (by decide) (by decide) ⟨_, hH1⟩) fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hh2, hout2, hS2⟩ := r.update_out h0 h1 h2 hpost
  have hT2 := hT1.of_call hpre hS2 (a := 8640) (n := 344) (Or.inl (by decide)) (by decide) hout2
  have hseed : bytesOf st1.data.dmem (r.off 448) 16 = r.seed :=
    bytesOf_of_bytesAt' (bytesAt_seed hT1.rs.base.inputs) length_seed
  have hH2 := hh2 [] hH1
  rw [List.nil_append, hseed] at hH2
  have had2 : BytesAt st2.data.dmem (r.off 16960) (r.leafAdrs c) :=
    r.bytesAt_of_call hpre hT1.rs.base.frame (by decide) (by decide) hout2 (by rw [hadl]; decide)
      (by rw [hadl]; decide) (hd1 ▸ had)
  -- `b53`: `update(A, address, 32)`
  refine ev_at (hpc2.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b52_next)) ?_
  have hwf2 := r.frame_wf hpre hT2.rs.base.frame (fun _ ↦ 0)
  have hm2 : Match (r.env st2.data) s0 st2.data := match_frameS hpre hT2.rs.base trivial trivial
  refine exec_then_elf (hb53 hp) run_b53 hwf2 hm2 fun st3 hm3 hpc3 ↦ ?_
  have hT3 := hT2.of_block hpre hm3 hwf2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 rfl
  have h0 : Run.RegIs st3.data .X0 (r.off 8640) := (hm3.regs .X0 _ rfl).trans (eval_ptr 8640)
  have h1 : Run.RegIs st3.data .X1 (r.off 16960) := (hm3.regs .X1 _ rfl).trans (eval_ptr 16960)
  have h2 : st3.data.regs.X2.toNat = 32 := regIs_toNat (hm3.regs .X2 _ rfl) (by decide)
  have hH3 : HasherHolds (bytesOf st3.data.dmem (r.off 8640) 344) r.seed := hd3 ▸ hH2
  refine call_then_elf hpc3 hc.2.2.1 (r.update_pre hpre hT3.rs.base.frame h0 h1 h2 (a := 8640)
    (b := 16960) (by decide) (by decide) (by decide) ⟨_, hH3⟩) fun st4 hpc4 hpost ↦ ?_
  obtain ⟨hh4, hout4, hS4⟩ := r.update_out h0 h1 h2 hpost
  have hT4 := hT3.of_call hpre hS4 (a := 8640) (n := 344) (Or.inl (by decide)) (by decide) hout4
  have hH4 := hh4 _ hH3
  rw [bytesOf_of_bytesAt' (hd3 ▸ had2) hadl] at hH4
  -- `b54`: the clone into B
  refine ev_at (hpc4.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b53_next)) ?_
  have hwf4 := r.frame_wf hpre hT4.rs.base.frame (fun _ ↦ 0)
  have hm4 : Match (r.env st4.data) s0 st4.data := match_frameS hpre hT4.rs.base trivial trivial
  refine exec_then_elf (hb54 hp) run_b54 hwf4 hm4 fun st5 hm5 hpc5 ↦ ?_
  have hT5 := hT4.of_block hpre hm5 hwf4 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 rfl
  have h0 : Run.RegIs st5.data .X0 (r.off 19008) := (hm5.regs .X0 _ rfl).trans (eval_ptr 19008)
  have h1 : Run.RegIs st5.data .X1 (r.off 8640) := (hm5.regs .X1 _ rfl).trans (eval_ptr 8640)
  have h2 : st5.data.regs.X2.toNat = 344 := regIs_toNat (hm5.regs .X2 _ rfl) (by decide)
  refine call_then_elf hpc5 hc.1 (r.memcpy_pre hpre hT5.rs.base.frame h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st6 hpc6 hpost ↦ ?_
  obtain ⟨hcp6, hout6, hS6⟩ := r.memcpy_out h0 h1 h2 hpost
  have hT6 := hT5.of_call hpre hS6 (a := 19008) (n := 344) (Or.inr (by decide)) (by decide) hout6
  have hH6 : HasherHolds (bytesOf st6.data.dmem (r.off 19008) 344) (r.seed ++ r.leafAdrs c) := by
    rw [bytesOf_of_bytesAt' hcp6 (Hasher.length_bytesOf ..), hd5]
    exact hH4
  -- `b55`: `update(B, secret, 16)`, the opening spilled
  refine ev_at (hpc6.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b54_next)) ?_
  have hwf6 := r.frame_wf hpre hT6.rs.base.frame (fun _ ↦ 0)
  have hm6 : Match (r.env st6.data) s0 st6.data := match_frameS hpre hT6.rs.base trivial trivial
  refine exec_then_elf (hb55 hp) run_b55 hwf6 hm6 fun st7 hm7 hpc7 ↦ ?_
  have hT7 := hT6.of_block hpre hm7 hwf6 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st7.data .X0 (r.off 19008) := (hm7.regs .X0 _ rfl).trans (eval_ptr 19008)
  have h1 : Run.RegIs st7.data .X1 (r.off (484 + 176 * c + 160)) := by
    rw [Run.RegIs, hm7.regs .X1 _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [hT6.x21, Run.off_add]
  have h2 : st7.data.regs.X2.toNat = 16 := regIs_toNat (hm7.regs .X2 _ rfl) (by decide)
  have hw432 : r.WordAt st7.data 432 (r.addr (484 + 176 * c)) := by
    refine write_reg hm7 (o := 432) (n := 8) (x := .X21) (by decide) (by decide) ?_
    rw [bytes_reg, hT6.x21]
    rfl
  have hH7 : HasherHolds (bytesOf st7.data.dmem (r.off 19008) 344) (r.seed ++ r.leafAdrs c) := by
    rw [bytesOf_blk hpre hT6.rs.base.frame hm7 hwf6 (by decide) rfl]
    exact hH6
  have hsec : bytesOf st7.data.dmem (r.off (484 + 176 * c + 160)) 16 = (r.openingOf c).secret := by
    have := bytesAt_slice hT7.rs.base.inputs.2.1 (176 * c + 160) 16
    rw [r.sigMem_secret hc24, show 484 + (176 * c + 160) = 484 + 176 * c + 160 by omega] at this
    exact bytesOf_of_bytesAt' this (r.length_forsSecret hc24)
  refine call_then_elf hpc7 hc.2.2.1 (r.update_pre hpre hT7.rs.base.frame h0 h1 h2 (a := 19008)
    (b := 484 + 176 * c + 160) (by decide) (by omega) (by omega) ⟨_, hH7⟩) fun st8 hpc8 hpost ↦ ?_
  obtain ⟨hh8, hout8, hS8⟩ := r.update_out h0 h1 h2 hpost
  have hT8 := hT7.of_call hpre hS8 (a := 19008) (n := 344) (Or.inr (by decide)) (by decide) hout8
  have hH8 := hh8 _ hH7
  rw [hsec] at hH8
  have hw4a : r.WordAt st8.data 432 (r.addr (484 + 176 * c)) :=
    r.bytesAt_of_call hpre hT7.rs.base.frame (by decide) (by decide) hout8
      (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; decide) hw432
  -- `b56`: `finalize(12864, B)`
  refine ev_at (hpc8.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b55_next)) ?_
  have hwf8 := r.frame_wf hpre hT8.rs.base.frame (fun _ ↦ 0)
  have hm8 : Match (r.env st8.data) s0 st8.data := match_frameS hpre hT8.rs.base trivial trivial
  refine exec_then_elf (hb56 hp) run_b56 hwf8 hm8 fun st9 hm9 hpc9 ↦ ?_
  have hT9 := hT8.of_block hpre hm9 hwf8 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st9.data .X0 (r.off 12864) := (hm9.regs .X0 _ rfl).trans (eval_ptr 12864)
  have h1 : Run.RegIs st9.data .X1 (r.off 19008) := (hm9.regs .X1 _ rfl).trans (eval_ptr 19008)
  have hH9 : HasherHolds (bytesOf st9.data.dmem (r.off 19008) 344)
      (r.seed ++ r.leafAdrs c ++ (r.openingOf c).secret) := by
    rw [bytesOf_blk hpre hT8.rs.base.frame hm9 hwf8 (by decide) rfl]
    exact hH8
  have hw4b := keep_blk hpre hm9 hwf8 (length_wordBytes _) (by decide) rfl hw4a
  refine call_then_elf hpc9 hc.2.2.2.1 (r.finalize_pre hpre hT9.rs.base.frame h0 h1 (by decide)
    (by decide) (by decide) ⟨_, hH9⟩) fun st10 hpc10 hpost ↦ ?_
  obtain ⟨hfin, hout10, hS10⟩ := r.finalize_out h0 h1 hpost
  have hT10 := hT9.of_call hpre hS10 (a := 12864) (n := 32) (Or.inl (by decide)) (by decide) hout10
  rw [finalize_eq hH9] at hfin
  have hcur : BytesAt st10.data.dmem (r.off 12864) (r.forsUpTo c 0) := by
    have := bytesAt_slice hfin 0 16
    rw [List.drop_zero, Nat.add_zero] at this
    exact this
  have hw4c : r.WordAt st10.data 432 (r.addr (484 + 176 * c)) :=
    r.bytesAt_of_call hpre hT9.rs.base.frame (by decide) (by decide) hout10
      (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; decide) hw4b
  -- `b57`: the first node
  refine ev_at (hpc10.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b56_next)) ?_
  have hwf10 := r.frame_wf hpre hT10.rs.base.frame (fun _ ↦ 0)
  have hm10 : Match (r.env st10.data) s0 st10.data := match_frameS hpre hT10.rs.base trivial trivial
  refine exec_then_elf (hb57 hp) run_b57 hwf10 hm10 fun st11 hm11 hpc11 ↦ ?_
  obtain ⟨hB11, -⟩ := hT10.rs.base.of_matchLow hpre hm11 hwf10 rfl rfl rfl rfl rfl rfl
  have hd11 : st11.data.dmem = st10.data.dmem := hm11.dmem_eq hwf10 rfl
  have hw4d : r.WordAt st11.data 432 (r.addr (484 + 176 * c)) := by
    unfold Run.WordAt; rw [hd11]; exact hw4c
  have hw440' : r.WordAt st11.data 440 (r.leafOf c).toUInt64 := by
    unfold Run.WordAt; rw [hd11]; exact hT10.w440
  have hroots11 : BytesAt st11.data.dmem (r.off 20064) ((List.range c).map r.forsRoot).flatten := by
    rw [hd11]; exact hT10.rs.roots
  have hcur' : BytesAt st11.data.dmem (r.off 12864) (r.forsUpTo c 0) := by rw [hd11]; exact hcur
  refine .done _ ⟨hpc11.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b57_next), ⟨⟨hB11, hc24, hw4d,
    hw440', hroots11⟩, by decide, ?_, hm11.regs .X21 _ rfl, ?_, ?_, hcur'⟩⟩
  · rw [Run.RegIs, reg_of hm11 rfl]; exact hT10.x19
  · rw [reg_of hm11 rfl]; exact hT10.x20
  · rw [Run.RegIs, reg_of hm11 rfl]; exact hT10.x25

end

end NativeRustcArm.SphincsVerifyProof.Fors
