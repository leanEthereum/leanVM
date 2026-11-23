module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Entry1

/-!
# `keccak_open`: the fold's start

`b4` loads the first challenge, saves the value, the result's, the slot point's and the rows'
addresses in the frame and sets the first round's registers: the state `AtFold` at `b5`
(`fold_start`), what `fold_run` starts from.
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (DecArea tstateBytes TStateAt)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes)

@[expose] public section

/-- **The fold's start**, at `b5`: what `fold_run` takes. -/
structure AtFold [Labels] (c : Cx) (m0 : MachineData) (rows : Array (Array EW))
    (st : MachineData) : Prop where
  mid : Mid c m0 st
  x29 : st.regs.X29.toBitVec = rwA m0
  x27 : st.regs.X27.toBitVec = fbA m0 + BitVec.ofNat 64 80
  x28 : st.regs.X28.toBitVec = fbA m0 + BitVec.ofNat 64 1104
  x22 : st.regs.X22 = (c.sl.getD 0 0).c0
  x23 : st.regs.X23 = (c.sl.getD 0 0).c1
  x25 : st.regs.X25 = 0
  x26 : st.regs.X26 = 0
  rw : ElemsAt st.dmem (rwA m0) (Fr c.sl rows 0) 4096

end

public section

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- The rows' elements, one by one. -/
theorem elems_rows {d : DataMem} {p : BitVec 64} {sl : Array EW} {rows : Array (Array EW)}
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    (h : NativeRustcVm.EWsAt d p (rowsFlat rows)) : ElemsAt d p (Fr sl rows 0) 4096 := by
  have hl : (rowsFlat rows).length = 4096 := by
    rw [rowsFlat, NativeRustcVm.KeccakGkr.rowsFlat_length rows (fun r hr ↦ hrow r (by omega)),
      hsz]
  intro i hi
  have := NativeRustcVm.EWsAt.getElem h (i := i) (by omega)
  show NativeRustcVm.EWAt d _ ((rowsFlat rows).getD i 0)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact this

/-- A byte of the frame's first `2128` is `Free` and not the slot point's nor the rows'. -/
theorem frame_low (hn : Nums a m0) {q : BitVec 64} (h : InRange (fbA m0) 2128 q) :
    spN m0 - 2224 ≤ q.toNat ∧ q.toNat < spN m0 - 96 := by
  have hN := hn.hN
  have hlt : spN m0 < 2 ^ 64 := m0.regs.SP.toBitVec.isLt
  have hf := fb_toNat (m0 := m0) (by omega)
  rw [inRange_nat (by rw [hf]; omega), hf] at h
  omega

variable [Host] {k : Nat}

/-- **The fold's start**: `b4`. -/
theorem fold_start (hp : Placed code k) (h : KeccakOpenPre a s c m0) {s1 : TState}
    {sl : Array EW} {v : EW} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b4Offset))
    (hsw : Sw a c m0 s1 sl v st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b5Offset) ∧
      AtFold ⟨a, s1, sl, v⟩ m0 (swOf c m0) st'.data) st := by
  have ok := ok_of h
  have hn := ok.nums
  have hS := h.1
  have hN := hn.hN
  have hlt : spN m0 < 2 ^ 64 := m0.regs.SP.toBitVec.isLt
  have h2224 : 2224 ≤ keccakOpenStack := by rw [stack_eq]; decide
  have hfN := fb_toNat (m0 := m0) (by omega)
  have hnw : (fbA m0).toNat + 2224 ≤ 2 ^ 64 := by rw [hfN]; omega
  have hb := hsw.body
  have hwf : (Env.ofMachine st.data (envR m0)).WF := wf_fold ok hb
  have hal : (fbA m0).toNat % 16 = 0 := frame_aligned hS h2224 rfl
  have hm : Match (Env.ofMachine st.data (envR m0)) b4S st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ hal, rfl, nofun, rfl, nofun, trivial⟩
      (by
        rw [hb.sp]
        show fbA m0 = fbA m0 + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero])
      ⟨by
        show st.data.regs.X28.toBitVec = slA m0 + BitVec.ofInt 64 0
        rw [hsw.x28, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero],
      by
        show st.data.regs.X29.toBitVec = rwA m0 + BitVec.ofInt 64 0
        rw [hsw.x29, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
      trivial trivial trivial
  refine exec_at (b4_in_code.trans hp.1 (by simp [b4])) run_b4 hwf hpc hm
    fun s2 hm2 hpc2 ↦ .done _ ⟨hpc2, ?_⟩
  have hb2 : Body m0 s2.data :=
    hb.write_local (lo := 2128) hS h2224 slots_le (by decide) (wsOff h) hm hm2 hwf rfl
      all_slots (by decide) fun p hw ↦ .inr (KeccakGkr.Written.inRange_le (r := 0)
        (b := fbA m0) (sz := 2224) rfl hnw (L := 2128) (by decide) (by decide +kernel) hw)
  have hso : SameOutside st.data.dmem s2.data.dmem (InRange (fbA m0) 2128) :=
    fun p hp ↦ hm2.sameOutside hwf p fun hw ↦ hp (KeccakGkr.Written.inRange_le (r := 0)
      (b := fbA m0) (sz := 2224) rfl hnw (L := 2128) (by decide) (by decide +kernel) hw)
  have hk : Kept st.data.dmem s2.data.dmem := hm2.kept hwf
  have := hn.sW; have := hn.sS; have := hn.rW; have := hn.rS
  have e0 : BitVec.ofInt 64 0 = 0#64 := rfl
  have hev0 := ewsAt_getD hsw.slot (i := 0) (by rw [hsw.sl_size]; decide)
  obtain ⟨l0, l1⟩ := KeccakGkr.load_ew (env := Env.ofMachine st.data (envR m0)) (r := 1) (o := 0)
    hev0
  obtain ⟨hsz, hrow⟩ := NativeVm.Math.Keccak.slotWeights_size m0.regs.X2.toNat c m0.regs.X6.toNat
    m0.regs.X7.toNat
  refine ⟨⟨hb2, ?_, ?_, ?_, ?_, ?_, hsw.sl_size, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := Sumcheck.Match.wordAt_write hm2 (r := 0) (b := fbA m0) (sz := 2224) (o := 16)
      (v := .reg .X21) rfl (by decide) (by decide +kernel)
    rwa [show (Sym.reg .X21).eval (Env.ofMachine st.data (envR m0)) =
      (st.data.regs.getXReg .X21).toBitVec from rfl, UInt64.ofBitVec_toBitVec,
      show st.data.regs.getXReg .X21 = v.c0 from hsw.x21] at this
  · have := Sumcheck.Match.wordAt_write hm2 (r := 0) (b := fbA m0) (sz := 2224) (o := 24)
      (v := .reg .X20) rfl (by decide) (by decide +kernel)
    rwa [show (Sym.reg .X20).eval (Env.ofMachine st.data (envR m0)) =
      (st.data.regs.getXReg .X20).toBitVec from rfl, UInt64.ofBitVec_toBitVec,
      show st.data.regs.getXReg .X20 = v.c1 from hsw.x20] at this
  · have := Sumcheck.Match.wordAt_write hm2 (r := 0) (b := fbA m0) (sz := 2224) (o := 32)
      (v := .reg .X19) rfl (by decide) (by decide +kernel)
    rwa [show (Sym.reg .X19).eval (Env.ofMachine st.data (envR m0)) =
      (st.data.regs.getXReg .X19).toBitVec from rfl, UInt64.ofBitVec_toBitVec,
      show st.data.regs.getXReg .X19 = m0.regs.X0 from hsw.x19] at this
  · have := Sumcheck.Match.wordAt_write hm2 (r := 0) (b := fbA m0) (sz := 2224) (o := 40)
      (v := .ptr 1 0) rfl (by decide) (by decide +kernel)
    rwa [show (Sym.ptr 1 0).eval (Env.ofMachine st.data (envR m0)) =
      slA m0 + BitVec.ofInt 64 0 from rfl, e0, BitVec.add_zero] at this
  · have := Sumcheck.Match.wordAt_write hm2 (r := 0) (b := fbA m0) (sz := 2224) (o := 48)
      (v := .ptr 2 0) rfl (by decide) (by decide +kernel)
    rwa [show (Sym.ptr 2 0).eval (Env.ofMachine st.data (envR m0)) =
      rwA m0 + BitVec.ofInt 64 0 from rfl, e0, BitVec.add_zero] at this
  · refine NativeRustcVm.BytesAt.of_sameOutside hsw.slot hso fun i hi hq ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsw.sl_size] at hi
    have := frame_low hn hq
    rw [toNat_add_ofNat' (by omega)] at this
    omega
  · exact ts_keep hn hsw.ts hk hso fun q hq ↦ by
      have := frame_low hn hq
      exact .inl ⟨by omega, by omega⟩
  · show (s2.data.regs.getXReg .X29).toBitVec = _
    rw [hm2.regs .X29 _ rfl]
    show rwA m0 + BitVec.ofInt 64 0 = _
    rw [e0, BitVec.add_zero]
  · refine (hm2.regs .X27 _ rfl).trans ?_
    show fbA m0 + BitVec.ofInt 64 80 = _
    rw [show BitVec.ofInt 64 80 = BitVec.ofNat 64 80 from rfl]
  · refine (hm2.regs .X28 _ rfl).trans ?_
    show fbA m0 + BitVec.ofInt 64 1104 = _
    rw [show BitVec.ofInt 64 1104 = BitVec.ofNat 64 1104 from rfl]
  · exact UInt64.toBitVec_inj.mp ((hm2.regs .X22 _ rfl).trans l0)
  · exact UInt64.toBitVec_inj.mp ((hm2.regs .X23 _ rfl).trans l1)
  · exact UInt64.toBitVec_inj.mp (hm2.regs .X25 _ rfl)
  · exact UInt64.toBitVec_inj.mp (hm2.regs .X26 _ rfl)
  · refine elems_rows hsz hrow (NativeRustcVm.BytesAt.of_sameOutside hsw.rows hso
      fun i hi hq ↦ ?_)
    rw [NativeRustcVm.length_ewsBytes, rowsFlat, NativeRustcVm.KeccakGkr.rowsFlat_length _
      (fun r hr ↦ hrow r (by omega)), hsz] at hi
    have := frame_low hn hq
    rw [toNat_add_ofNat' (by omega)] at this
    omega

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
