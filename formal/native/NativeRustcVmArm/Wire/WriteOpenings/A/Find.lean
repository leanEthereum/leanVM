module

public import NativeRustcVmArm.Code.Vm.Find.Names
public import NativeRustcVmArm.Wire.WriteOpenings.A.Level

/-!
# `write_openings`' sibling lookup

The call of `find` (`b17`, `call_step`): back with the index of the first node of key
`skey q l` (`F18`). Its digest, or zeros (`dig_step`: `b18`, `b19`, `b20`, or `b14`).
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} {j l : Nat}

/-- Level `l`'s nodes are in the siblings' region. -/
theorem level_inside (G : Geo R) (hl : l < R.h) {n : Nat} (hn : n ≤ 256) :
    Inside (R.sb + BitVec.ofNat 64 (10240 * l)) (40 * n) (R.big 5) := by
  have hw : R.sb.toNat + 10240 * R.h ≤ 2 ^ 64 := G.noWrap (i := 5) (by omega)
  have : 10240 * l + 10240 ≤ 10240 * R.h := by omega
  show R.sb.toNat ≤ _ ∧ _ ≤ R.sb.toNat + 10240 * R.h
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- Node `n` of level `l` is in the siblings' region. -/
theorem node_inside (G : Geo R) (hl : l < R.h) {n : Nat} (hn : n < 256) :
    Inside (R.na l n) 40 (R.big 5) := by
  have hw : R.sb.toNat + 10240 * R.h ≤ 2 ^ 64 := G.noWrap (i := 5) (by omega)
  have : 10240 * l + 10240 ≤ 10240 * R.h := by omega
  show R.sb.toNat ≤ _ ∧ _ ≤ R.sb.toNat + 10240 * R.h
  unfold Run.na
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

theorem skey_toBitVec (q : UInt64) (l : Nat) (hl : l < 64) :
    (q.toBitVec.ushiftRight ((BitVec.ofNat 64 l).toNat % 64)) = (skey q l).toBitVec := by
  rw [ofNat_toNat (by omega), Nat.mod_eq_of_lt hl]
  rfl

/-- Level `l`'s keys in memory, at its nodes. -/
theorem keys_at (G : Geo R) (hl : l < R.h) (hc : (R.cw l).toNat ≤ 256) {m : MachineData}
    (hfr : Frm R m) (i : Nat) (h : i < (R.keys l).length) :
    WordAt m.dmem (R.sb + BitVec.ofNat 64 (10240 * l) + BitVec.ofNat 64 (40 * i))
      (R.keys l)[i] := by
  have hi : i < (R.cw l).toNat := by simpa [Run.keys] using h
  have hn := node_inside G hl (n := i) (by omega)
  have h8 := Inside.take hn (m := 8) (by omega)
  have hw : WordAt m.dmem (R.na l i) (wordOf m.dmem (R.na l i)) :=
    wordAt_wordOf fun t ht ↦ hfr.kept _ (h8.mapped (G.ok 5 (by omega)) t ht)
  rw [G.wordOf_keep hfr (by omega) (by omega) h8] at hw
  rw [NativeRustcVm.addr_add_add]
  simp only [Run.keys, List.getElem_map, List.getElem_range]
  exact hw

variable [Host]

/-- **The call of `find`** (`b17`). -/
theorem call_step (hp : Placed code R.k) (G : Geo R)
    (hfind : Spec (Labels.label NativeRustcVmArm.Vm.Find.entryLabel) FindPre FindPost) {st : MachineState}
    (H : C17 R j l st) : Eventually (step1 Host.exe) (F18 R j l) st := by
  have S := H.s
  have hl := S.llt
  have hh := G.h32
  have hc := H.cle
  have hwf := G.wf0 S.fr.kept
  have hm := frMatch G S.fr
  refine run_block G hp b17_in_code (by simp [b17]) run_b17 S.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := .X24 :: levRegs) (by decide)
  have S1 : LevS R j l s1.data := S.keep hfr1 hd1 fun r hr ↦ hk1 r (List.mem_cons_of_mem _ hr)
  have x0 : rv s1.data .X0 = R.sb + BitVec.ofNat 64 (10240 * l) := by
    rw [hm1.regs .X0 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [S.cs.x23, S.x28]
  have x1 : rv s1.data .X1 = (R.cw l).toBitVec := by
    rw [hm1.regs .X1 _ rfl]
    exact H.x24
  have x2 : s1.data.regs.X2 = skey (R.qw j) l := by
    apply UInt64.toBitVec_inj.mp
    rw [show s1.data.regs.X2 = s1.data.regs.getXReg .X2 from rfl, hm1.regs .X2 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [S.x25, S.x27]
    exact skey_toBitVec _ _ (by omega)
  have hin := level_inside G hl hc
  have hpre : FindPre s1.data := by
    refine ⟨hfr1.stackOk G.st (by decide) (by unfold findStack; omega), ?_⟩
    show NativeRustcVm.Region.Ok _ ⟨rv s1.data .X0, 40 * (rv s1.data .X1).toNat⟩
    rw [x0, x1]
    exact ⟨fun t ht ↦ hfr1.kept _ (hin.mapped (G.ok 5 (by omega)) t ht),
      hin.noWrap (G.noWrap (by omega))⟩
  refine Fr.leaf hfr1 G.st.2.1 (N' := findStack) (by unfold findStack; omega) (by simp)
    (by decide) (fun q hq ↦ G.not_in (i := 7) (j := 0) (by omega) (by omega) (by omega)
      ⟨le_refl _, le_refl _⟩ hq) hfind
    (fun m m' hq ↦ ⟨NativeRustcVm.SameOutside.of_eq hq.2.1 _, hq.2.2⟩) hpc1 hpre
    fun m2 hfr2 hq hcs ↦ ?_
  have hd2 : m2.dmem = st.data.dmem := hq.2.1.trans hd1
  have hk2 : ∀ r ∈ .X24 :: levRegs, m2.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦
    (hcs r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> rfl)).trans (hk1 r hr)
  obtain ⟨K, hK⟩ : ∃ K, R.keys l = K := ⟨_, rfl⟩
  have hks : ∀ (i : Nat) (h : i < K.length),
      WordAt s1.data.dmem (s1.data.regs.X0.toBitVec + BitVec.ofNat 64 (40 * i)) K[i] := by
    subst hK
    intro i h
    rw [show s1.data.regs.X0.toBitVec = rv s1.data .X0 from rfl, x0]
    exact keys_at G hl hc hfr1 i h
  have hlen : K.length = s1.data.regs.X1.toNat := by
    subst hK
    simp only [Run.keys, List.length_map, List.length_range]
    rw [show s1.data.regs.X1.toNat = (rv s1.data .X1).toNat from rfl, x1, UInt64.toNat_toBitVec]
  have hres := hq.1 K hlen hks
  rw [x2] at hres
  have S2 : LevS R j l m2 := S.keep hfr2 hd2 fun r hr ↦ hk2 r (List.mem_cons_of_mem _ hr)
  have e24 : rv m2 .X24 = (R.cw l).toBitVec := by rw [hk2 .X24 List.mem_cons_self]; exact H.x24
  have hpc : (⟨m2, Host.addrOf (R.k + NativeRustcVmArm.Vm.WriteOpenings.b17Offset + b17.length)⟩ : MachineState).pc = pcOf R NativeRustcVmArm.Vm.WriteOpenings.b18Offset :=
    congrArg Host.addrOf (show R.k + NativeRustcVmArm.Vm.WriteOpenings.b17Offset + 4 = R.k + NativeRustcVmArm.Vm.WriteOpenings.b18Offset from rfl)
  refine .done _ ⟨hpc, S2, e24, hc, fun n hn ↦ ?_, fun hn ↦ ?_⟩
  · rw [hK] at hn; rw [hn] at hres; exact hres
  · rw [hK] at hn; rw [hn] at hres; exact hres

end

end NativeRustcVmArm.Wire.WriteOpenings
