module

public import NativeRustcVmArm.Arrays.MultilinearEvalByOfMultilinearEval.Loop

/-!
# `multilinear_eval_by` (`multilinear_eval`'s closure): an entry waits

`push`: at `.LMultilinearEvalByOfMultilinearEval_9` (`b12`) nothing waits at level `k`: the value
is stored at `pending[k]`, `full[k] = 1` (`pendOf_set`), and the stream goes on with entry `i + 1`
at the outer loop's head, or ends after the last entry (`b13`, the epilogue, `0`).
-/

namespace NativeRustcVmArm.Arrays.MleOfMultilinearEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval
open NativeVm.Model NativeRustcArm NativeRustcVmArm.Arrays.MleFrame
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (stream cont setP)

public section

variable [Host] {k : Nat}

/-- **`v` waits at level `kk`** (`b12`): stored, flagged; entry `i + 1` next, or the end. -/
theorem push (hp : Placed code k) {m0 : MachineData} (hpre : MleOfMultilinearEvalPre m0)
    {i kk : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b12Offset))
    (hI : Inner m0 i kk s.data) (hnone : pendOf s.data.dmem (fbOf m0) kk = none) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b3Offset) ∧ Outer m0 (i + 1) s'.data)) s := by
  obtain ⟨hS, h02, h64, -, -⟩ := hpre
  obtain ⟨fr, hi, hk, -, h20, h21, -, h29, hval⟩ := hI
  obtain ⟨st, pc⟩ := s
  simp only at hpc hnone fr h20 h21 h29 hval
  have hk64 : kk < 64 := by simp only [mm] at hk; omega
  have hsl := frame_piece hS fr.body.kept (o := 48 + 16 * kk) (n := 16) (by omega)
  have hfl := frame_piece hS fr.body.kept (o := 1072 + kk) (n := 1) (by omega)
  have hhd := frame_piece hS fr.body.kept (o := 0) (n := 48) (by omega)
  rw [add_ofNat_zero] at hhd
  have a1 := frame_apart hS (o := 48 + 16 * kk) (n := 16) (o' := 1072 + kk) (n' := 1)
    (by omega) (by omega)
  have a2 := frame_apart hS (o := 0) (n := 48) (o' := 48 + 16 * kk) (n' := 16) (by omega) (by omega)
  have a3 := frame_apart hS (o := 0) (n := 48) (o' := 1072 + kk) (n' := 1) (by omega) (by omega)
  rw [add_ofNat_zero] at a2 a3
  have hwf := wf3 (st := st) hsl hfl hhd a1 (apart_comm a2) (apart_comm a3)
  have hm : Match (Env.ofMachine st [(fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk), 16),
      (fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1), (fbOf m0, 48)]) pushS st :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, rfl, fun _ ↦ frame_aligned hS (by decide) rfl, trivial⟩
      (fr.body.sp.trans (BitVec.add_zero _).symm)
      ⟨h21.trans (BitVec.add_zero _).symm, h20.trans (BitVec.add_zero _).symm,
        trivial⟩ trivial trivial trivial
  refine exec_at (hb12 hp) run_b12 hwf hpc hm fun s2 hm2 hpc2 ↦ ?_
  have e0 := fb_add_toNat hS (o := 48 + 16 * kk) (by omega)
  have e1 := fb_add_toNat hS (o := 1072 + kk) (by omega)
  have ef := (fb_toNat hS).1
  -- the bytes the block wrote: `pending[kk]`, `full[kk]`
  have hW : ∀ p, Written (Env.ofMachine st [(fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk), 16),
      (fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1), (fbOf m0, 48)]) (after b12 pushS) p →
      (fbOf m0).toNat + (48 + 16 * kk) ≤ p.toNat ∧ p.toNat < (fbOf m0).toNat + (64 + 16 * kk) ∨
        p.toNat = (fbOf m0).toNat + (1072 + kk) := by
    rw [after_eq run_b12]
    intro p ⟨w, hw, b, sz, hb, hlo, hhi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;>
      simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb <;> obtain ⟨rfl, rfl⟩ := hb <;> simp only at hlo hhi <;>
      omega
  rw [after_eq run_b12] at hW
  have hnw : ∀ j, j < 1232 → j ≠ 1072 + kk → (j < 48 + 16 * kk ∨ 64 + 16 * kk ≤ j) →
      s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) = st.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := by
    intro j hj h1 h2
    refine hm2.get?_mem0 hwf fun hw ↦ ?_
    have := hW _ hw
    rw [fb_add_toNat hS (by omega)] at this
    omega
  have hflag : s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 (1072 + kk)) = some 1 := by
    have := hm2.mem 1 (fbOf m0 + BitVec.ofNat 64 (1072 + kk)) 1 rfl 0 (by decide)
    rw [add_ofNat_zero] at this
    rw [this]
    simp [memByte, findWrite, Sym.eval, byteOf]
  have hv : ewOf s2.data.dmem (fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk)) =
      ⟨st.regs.X23, st.regs.X24⟩ := by
    have h0 := wordAt_of_write (o := 0) (r := .X23) hm2 (by decide) (by decide)
    have h8 := wordAt_of_write (o := 8) (r := .X24) hm2 (by decide) (by decide)
    rw [add_ofNat_zero] at h0
    unfold ewOf
    rw [NativeRustcVm.wordOf_of_wordAt h0, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      NativeRustcVm.wordOf_of_wordAt h8]
    rfl
  have hP : pendOf s2.data.dmem (fbOf m0) = setP (pendOf st.dmem (fbOf m0)) kk
      (some ⟨st.regs.X23, st.regs.X24⟩) :=
    pendOf_set hk64 hflag hv fun j _ hj h1 h2 ↦ hnw j (by omega) h1 h2
  have hkP : kk < (pts m0).length := by simp only [pts, NativeRustcVm.length_ewsOf]; exact hk
  have hval' : stream (pts m0) ((ents m0).drop (i + 1)) (pendOf s2.data.dmem (fbOf m0)) =
      target m0 := by
    rw [hP, ← NativeRustcVm.Mle.cont_none _ hkP hnone]; exact hval
  have hx29 : s2.data.regs.getXReg .X29 = st.regs.getXReg .X29 := Match.reg_eq hm hm2 rfl rfl
  -- the test `i + 1 = n`
  simp only [PcOk] at hpc2
  sym_simp at hpc2
  have hx8 : (Env.ofMachine st [(fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk), 16),
      (fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1), (fbOf m0, 48)]).load 2 16 8 =
      (m0.regs.getXReg .X0).toBitVec :=
    slot_load (r := 2) (o := 16) (x := .X0) fr.body.frame (by simp [slots])
  rw [hx8] at hpc2
  have heq : (st.regs.getXReg .X29).toBitVec = (m0.regs.getXReg .X0).toBitVec ↔ i + 1 = nn m0 := by
    have e29 : (st.regs.getXReg .X29).toBitVec.toNat = i + 1 := h29
    have e0 : (m0.regs.getXReg .X0).toBitVec.toNat = nn m0 := congrArg UInt64.toNat h02
    constructor
    · intro h; rw [← e29, ← e0, h]
    · intro h; apply BitVec.eq_of_toNat_eq; rw [e29, e0, h]
  have hpc2' := pc_ne hpc2
  by_cases hlast : i + 1 = nn m0
  · have hpc3 := hpc2'.2 (heq.mpr hlast)
    simp only [NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b12_length, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b12Length] at hpc3
    refine exec_at (hb13 hp) run_b13 (Env.wf_nil _) hpc3 (match_nil _) fun s3 hm3 hpc3' ↦ ?_
    have fr2 : Body m0 1232 mleStack slots 0 0 s2.data :=
      body_of_frame_write fr.body hS hm hm2 hwf rfl
        (by rw [kept_nil.1]; exact after_eq run_b12 ▸ keeps.2.2.2.2.2.2.2.2.1)
        (fun p hp' ↦ by
          rcases hW p hp' with ⟨h1, h2⟩ | h1
          · exact frame_addr hS (lo := 48) (hi := 1136) (by omega) (by omega) (by decide)
          · exact frame_addr hS (lo := 48) (hi := 1136) (by omega) (by omega) (by decide))
        (by decide)
    have bd3 := fr2.of_block (match_nil _) hm3 (Env.wf_nil _) rfl
      (by rw [kept_nil.1]; exact after_eq run_b13 ▸ keeps.2.2.2.2.2.2.2.2.2.1)
    simp only [PcOk] at hpc3'
    refine Eventually.mono (finish hp hS b17_restores.2 (by simp [slots, slots0])
      (hpc3'.trans (lbl_13 hp)) bd3 ?_)
      fun _ h ↦ Or.inl h
    rw [← hval', List.drop_of_length_le (by
      simp only [ents, nn, NativeRustcVm.length_ewsOf] at hlast ⊢; omega)]
    show (⟨s3.data.regs.getXReg .X23, s3.data.regs.getXReg .X24⟩ : EW) = 0
    rw [Match.reg_eq (match_nil _) hm3 rfl rfl, Match.reg_eq (r := .X24) (match_nil _) hm3 rfl rfl,
      reg_of hm2 (r := .X23) rfl, reg_of hm2 (r := .X24) rfl]
    rfl
  · have hpc3 := hpc2'.1 (fun h ↦ hlast (heq.mp h))
    refine .done _ (Or.inr ⟨hpc3.trans (lbl_3 hp), ⟨⟨?_, ?_, ?_⟩, by omega, by omega, ?_, hval'⟩⟩)
    · exact body_of_frame_write fr.body hS hm hm2 hwf rfl
        (by rw [kept_nil.1]; exact after_eq run_b12 ▸ keeps.2.2.2.2.2.2.2.2.1)
        (fun p hp' ↦ by
          rcases hW p hp' with ⟨h1, h2⟩ | h1
          · exact frame_addr hS (lo := 48) (hi := 1136) (by omega) (by omega) (by decide)
          · exact frame_addr hS (lo := 48) (hi := 1136) (by omega) (by omega) (by decide))
        (by decide)
    · rw [NativeRustcVm.wordOf_congr (d := st.dmem) fun j hj ↦ by
        rw [NativeRustcVm.addr_add]; exact hnw (24 + j) (by omega) (by omega) (by omega)]
      exact fr.w24
    · exact flagsOk_set fr.flags hflag hk64 fun j _ hj h1 h2 ↦ hnw j (by omega) h1 h2
    · show (s2.data.regs.getXReg .X29).toNat = _
      rw [hx29]; exact h29

end

end NativeRustcVmArm.Arrays.MleOfMultilinearEval
