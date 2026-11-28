module

public import NativeRustcVmArm.Wire.WriteOpenings.A.Find

/-!
# `write_openings`' digest of a level

Back from `find` (`F18`): no sibling, zeros (`b18`, `b14`: `zero_step`); the sibling `n`, its
node's four digest words (`b18`, `b19`, `b20`: `node_step`). Either way `DigA` at `b15`.
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} {j l : Nat}

theorem digest_none {q : UInt64} (h : (R.keys l).findIdx? (· == skey q l) = none) :
    R.digest l q = [0, 0, 0, 0] := by
  unfold Run.digest; rw [h]

theorem digest_some {q : UInt64} {n : Nat} (h : (R.keys l).findIdx? (· == skey q l) = some n) :
    R.digest l q = [wordOf R.d0 (R.na l n + BitVec.ofNat 64 8),
      wordOf R.d0 (R.na l n + BitVec.ofNat 64 16), wordOf R.d0 (R.na l n + BitVec.ofNat 64 24),
      wordOf R.d0 (R.na l n + BitVec.ofNat 64 32)] := by
  unfold Run.digest; rw [h]; rfl

theorem findIdx_lt {K : List UInt64} {p : UInt64 → Bool} {n : Nat} (h : K.findIdx? p = some n) :
    n < K.length := (List.findIdx?_eq_some_iff_getElem.mp h).1

theorem keys_length : (R.keys l).length = (R.cw l).toNat := by simp [Run.keys]

theorem ofBitVec_zero : UInt64.ofBitVec (BitVec.ofNat 64 0) = 0 := rfl

variable [Host]

/-- **No sibling** (`b14`): zeros. -/
theorem zero_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (hpc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b14Offset)
    (S : LevS R j l st.data) (h8 : rv st.data .X8 = 0#64)
    (hn : (R.keys l).findIdx? (· == skey (R.qw j) l) = none) :
    Eventually (step1 Host.exe) (DigA R j l) st := by
  have hwf := G.wf0 S.fr.kept
  have hm := frMatch G S.fr
  refine run_block G hp b14_in_code (by simp [b14]) run_b14 S.fr hpc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ .done _ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := levRegs) (by decide)
  have e : ∀ x ∈ [XReg.X8, .X9, .X10, .X11], UInt64.ofBitVec (rv s1.data x) = 0 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
    · rw [hm1.regs _ _ rfl]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [h8]; rfl
  refine ⟨hpc1.trans (congrArg Host.addrOf rfl), S.keep hfr1 hd1 hk1, ?_⟩
  rw [digest_none hn, e .X11 (by simp), e .X10 (by simp), e .X9 (by simp), e .X8 (by simp)]

omit [Host] in
/-- Word `8 + 8 u` of node `n` of level `l`. -/
theorem node_word (G : Geo R) (hl : l < R.h) {n : Nat} (hn : n < 256) {m : MachineData}
    (hfr : Frm R m) {u : Nat} (hu : u < 4) :
    wordOf m.dmem (R.na l n + BitVec.ofNat 64 (8 + 8 * u)) =
      wordOf R.d0 (R.na l n + BitVec.ofNat 64 (8 + 8 * u)) := by
  have hw : R.sb.toNat + 10240 * R.h ≤ 2 ^ 64 := G.noWrap (i := 5) (by omega)
  have : 10240 * l + 10240 ≤ 10240 * R.h := by omega
  have h1 : (R.na l n).toNat = R.sb.toNat + (10240 * l + 40 * n) := by
    unfold Run.na; rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  refine G.wordOf_keep hfr (i := 5) (by omega) (by omega) ?_
  show R.sb.toNat ≤ _ ∧ _ ≤ R.sb.toNat + 10240 * R.h
  rw [NativeRustcVm.toNat_add_ofNat (by omega), h1]
  omega

/-- **The sibling `n`** (`b20`): its digest's words. -/
theorem node_step (hp : Placed code R.k) (G : Geo R) {st : MachineState}
    (hpc : st.pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b20Offset) (S : LevS R j l st.data) {n : Nat}
    (hx1 : (rv st.data .X1).toNat = n) (hc : (R.cw l).toNat ≤ 256) (hnc : n < (R.cw l).toNat)
    (hn : (R.keys l).findIdx? (· == skey (R.qw j) l) = some n) :
    Eventually (step1 Host.exe) (DigA R j l) st := by
  have hl := S.llt
  have hin := node_inside G hl (n := n) (by omega)
  have hwf := G.wf1 S.fr.kept (by omega) (by omega) hin
  have hm : Match (envOf R st.data [(R.na l n, 40)])
      (init [(176, true), (40, false)] (.ptr 0 0) [] [] [] [(nodeAddr, 1, 0)]) st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ G.aligned, rfl, nofun, trivial⟩ (by rw [S.fr.sp]; simp [Sym.eval])
      trivial trivial trivial ⟨by
        simp only [nodeAddr, Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
        rw [S.cs.x23, S.x28, base1, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        have e1 : rv st.data .X1 = BitVec.ofNat 64 n := by
          apply BitVec.eq_of_toNat_eq; rw [hx1, ofNat_toNat (by omega)]
        rw [e1]
        unfold Run.na
        apply BitVec.eq_of_toNat_eq
        have hw : R.sb.toNat + 10240 * R.h ≤ 2 ^ 64 := G.noWrap (i := 5) (by omega)
        have : 10240 * l + 10240 ≤ 10240 * R.h := by omega
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
          show (2 : Nat) ^ MemWidth.W64.bits = 2 ^ 64 from rfl]
        rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (a := 40) (by omega),
          Nat.mod_eq_of_lt (a := n * 40) (by omega), Nat.mod_eq_of_lt (a := 10240 * l) (by omega),
          Nat.mod_eq_of_lt (a := 10240 * l + 40 * n) (by omega)]
        omega, trivial⟩
  refine run_block G hp b20_in_code (by simp [b20]) run_b20 S.fr hpc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ .done _ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := levRegs) (by decide)
  have e : ∀ (x : XReg) (u : Nat), u < 4 → (after b20 (init [(176, true), (40, false)] (.ptr 0 0)
      [] [] [] [(nodeAddr, 1, 0)])).reg x = some (.load 1 (8 + 8 * u) 8) →
      UInt64.ofBitVec (rv s1.data x) = wordOf R.d0 (R.na l n + BitVec.ofNat 64 (8 + 8 * u)) := by
    intro x u hu hx
    rw [after_eq run_b20] at hx
    rw [hm1.regs _ _ hx]
    simp only [Sym.eval]
    rw [envLoad (a := R.na l n) (sz := 40) rfl, node_word G hl (by omega) S.fr hu]
  refine ⟨hpc1.trans (by rw [hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b15Offset) NativeRustcVmArm.Vm.WriteOpenings.label_14_at]), S.keep hfr1 hd1 hk1, ?_⟩
  rw [digest_some hn, e .X11 0 (by omega) rfl, e .X10 1 (by omega) rfl, e .X9 2 (by omega) rfl,
    e .X8 3 (by omega) rfl]

end

end NativeRustcVmArm.Wire.WriteOpenings
