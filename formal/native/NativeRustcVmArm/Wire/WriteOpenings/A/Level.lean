module

public import NativeRustcVmArm.Wire.WriteOpenings.A.Defs

/-!
# `write_openings`' levels (`h > 0`)

From the levels' loop head (`LevA`, `b16`): the level's count read and checked (`b16_step`), the
sibling found (`call_step`, `b17` and `find`), its digest or zeros in X11, X10, X9, X8
(`dig_step`, `b18`, `b14`, `b19`, `b20`), written (`b15_step`); after the last level, the next
query or the end (`next_step`, `b21`, `b22`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

@[expose] public section

/-- The registers the levels' loop keeps. -/
abbrev levRegs : List XReg := [.X19, .X21, .X22, .X23, .X26, .X29, .X20, .X25, .X27, .X28]

section
variable [Host]

/-- After opening `j`: the next query's loop head, or the end. -/
def NextA (R : Run) (j : Nat) (st : MachineState) : Prop := Post R st ∨ HeadA R (j + 1) st

/-- The call of `find` (`b17`), the level's count in X24. -/
structure C17 (R : Run) (j l : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b17Offset
  s : LevS R j l st.data
  x24 : rv st.data .X24 = (R.cw l).toBitVec
  cle : (R.cw l).toNat ≤ 256

/-- Back from `find` (`b18`). -/
structure F18 (R : Run) (j l : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b18Offset
  s : LevS R j l st.data
  x24 : rv st.data .X24 = (R.cw l).toBitVec
  cle : (R.cw l).toNat ≤ 256
  some : ∀ n, (R.keys l).findIdx? (· == skey (R.qw j) l) = some n →
    st.data.regs.X0 = 1 ∧ st.data.regs.X1.toNat = n
  none : (R.keys l).findIdx? (· == skey (R.qw j) l) = none → st.data.regs.X0 = 0

/-- The level's digest in X11, X10, X9, X8 (`b15`). -/
structure DigA (R : Run) (j l : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b15Offset
  s : LevS R j l st.data
  dg : R.digest l (R.qw j) = [UInt64.ofBitVec (rv st.data .X11), UInt64.ofBitVec (rv st.data .X10),
    UInt64.ofBitVec (rv st.data .X9), UInt64.ofBitVec (rv st.data .X8)]

/-- Opening `j` written (`b21`). -/
structure EndA (R : Run) (j : Nat) (st : MachineState) : Prop where
  pc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b21Offset
  fr : Frm R st.data
  cs : Cs R st.data
  lt : j < R.nq
  h0 : 0 < R.h
  w1 : FrW1 R j st.data.dmem
  w2 : FrW2 R j st.data.dmem
  done : R.Done st.data.dmem (j + 1)

end

end

public section

variable {R : Run} {j l : Nat}

theorem sub_levRegs_cs : [XReg.X19, .X21, .X22, .X23, .X26, .X29] ⊆ levRegs := by decide

theorem LevS.keep {m m' : MachineData} (h : LevS R j l m) (hfr : Frm R m') (hd : m'.dmem = m.dmem)
    (hk : ∀ r ∈ levRegs, m'.regs.getXReg r = m.regs.getXReg r) : LevS R j l m' where
  fr := hfr
  cs := h.cs.keep fun r hr ↦ hk r (sub_levRegs_cs hr)
  x20 := by rw [hk .X20 (by simp)]; exact h.x20
  x25 := by rw [hk .X25 (by simp)]; exact h.x25
  x27 := by rw [hk .X27 (by simp)]; exact h.x27
  x28 := by rw [hk .X28 (by simp)]; exact h.x28
  lt := h.lt
  llt := h.llt
  w1 := hd ▸ h.w1
  w2 := hd ▸ h.w2
  mem := hd ▸ h.mem
  leaf := hd ▸ h.leaf
  path := hd ▸ h.path

variable [Host]

/-- **The level's count** (`b16`): more than `256`, a rejection; else the call. -/
theorem b16_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : LevA R j l st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ C17 R j l st') st := by
  have S := H.s
  have hl := S.llt
  have hh := G.h32
  have hin : Inside (R.cnt + BitVec.ofNat 64 (8 * l)) 8 (R.big 6) :=
    inside_off (G.noWrap (by omega)) (by show 8 * l + 8 ≤ 8 * R.h; omega) (by omega)
  have hwf := G.wf1 S.fr.kept (by omega) (by omega) hin
  have hm : Match (envOf R st.data [(R.cnt + BitVec.ofNat 64 (8 * l), 8)])
      (pS (idxAddr .X29 .X27)) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, trivial⟩ (by rw [S.fr.sp]; simp [Sym.eval])
      trivial trivial trivial ⟨by
        simp only [idxAddr, Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64,
          Env.ofMachine_regs, memExt3]
        rw [S.cs.x29, S.x27, ofNat_toNat (by omega), base1, show BitVec.ofInt 64 0 = 0#64 from rfl,
          BitVec.add_zero], trivial⟩
  refine run_block G hp b16_in_code (by simp [b16]) run_b16 S.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun st' hfr' hm' hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  have hw : (envOf R st.data [(R.cnt + BitVec.ofNat 64 (8 * l), 8)]).load 1 0 8 =
      (R.cw l).toBitVec := by
    rw [envLoad rfl 0, NativeRustcVm.addr_add_zero, G.wordOf_keep S.fr (by omega) (by omega) hin]
    rfl
  have e24 : rv st'.data .X24 = (R.cw l).toBitVec := by
    rw [hm'.regs .X24 _ rfl]
    exact hw
  simp only [PcOk, SBool.eval, ult_apply, eq_apply, Sym.eval, hw, UInt64.toNat_toBitVec,
    BitVec.toNat_ofNat] at hpc'
  have hk := regs_keep hm hm' (rs := levRegs) (by decide)
  split at hpc'
  · rename_i hc
    rw [hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b45Offset) NativeRustcVmArm.Vm.WriteOpenings.label_38_at] at hpc'
    have hbad : 256 < (R.cw l).toNat := by simp at hc; omega
    exact Eventually.mono (fail_spec hp G hpc' hfr' (.inr ⟨l, hl, hbad⟩)) fun _ h ↦ .inl h
  · rename_i hc
    have hle : (R.cw l).toNat ≤ 256 := by simp at hc; omega
    exact .done _ (.inr ⟨hpc'.trans (congrArg Host.addrOf rfl), S.keep hfr' hd hk, e24, hle⟩)

end

end NativeRustcVmArm.Wire.WriteOpenings
