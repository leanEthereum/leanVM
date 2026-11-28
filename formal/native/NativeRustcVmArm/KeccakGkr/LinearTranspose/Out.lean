module

public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Columns

/-!
# `linear_transpose`: an element of the output

The output loop (`.LLinearTranspose_19`, `b22`), for lane `l` at position `z`: `g`'s element plus
column `ca l` at `z` (X14 - 8) and column `cb l` at `(z + 1) % 64` (X15 the column, X18 & 63 the
index) stored at X17 - 8 (`Out`, `out_step`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (gW colW outW weightsBytes)

@[expose] public section

/-- The column one along from lane `l`'s. -/
abbrev ca (l : Nat) : Nat := (l % 5 + 1) % 5
/-- The column four along from lane `l`'s. -/
abbrev cb (l : Nat) : Nat := (l % 5 + 4) % 5

/-- What the output loop's memory holds: `g`, the columns, the output's first `n` elements. -/
structure OutMem [Labels] (m0 : MachineData) (ws : Array EW) (n : Nat) (st : MachineData) :
    Prop where
  g : ElemsAt st.dmem (gA m0) (gF ws) 1600
  c : ElemsAt st.dmem (cA m0) (cF ws) 320
  o : ElemsAt st.dmem (oA m0) (oF ws) n

/-- The output loop's registers for lane `l`. -/
structure OutRegs [Labels] (m0 st : MachineData) (l : Nat) : Prop where
  ctx : Ctx m0 st
  lt : l < 25
  x8 : st.regs.X8.toNat = l
  x9 : st.regs.X9.toBitVec = cA m0 + BitVec.ofNat 64 8
  x10 : st.regs.X10.toBitVec = oA m0 + BitVec.ofNat 64 (8 + 1024 * l)
  x11 : st.regs.X11.toBitVec = gA m0 + BitVec.ofNat 64 (8 + 1024 * l)
  x12 : st.regs.X12.toBitVec = BitVec.ofNat 64 14757395258967641293
  x13 : st.regs.X13.toBitVec = BitVec.ofNat 64 4096

/-- **The output loop's head** at lane `l`, position `z`. -/
structure Out [Labels] (m0 : MachineData) (ws : Array EW) (l z : Nat) (st : MachineData) :
    Prop where
  regs : OutRegs m0 st l
  mem : OutMem m0 ws (64 * l + z) st
  z_lt : z < 64
  x14 : st.regs.X14.toBitVec = cA m0 + BitVec.ofNat 64 (8 + 1024 * ca l + 16 * z)
  x15 : st.regs.X15.toBitVec = cA m0 + BitVec.ofNat 64 (1024 * cb l)
  x16 : st.regs.X16.toBitVec = gA m0 + BitVec.ofNat 64 (8 + 1024 * l + 16 * z)
  x17 : st.regs.X17.toBitVec = oA m0 + BitVec.ofNat 64 (8 + 1024 * l + 16 * z)
  x18 : st.regs.X18.toNat = z + 1

/-- The output loop's environment: the two columns' elements, `g`'s, the output's. -/
def envO (m0 s : MachineData) (l z : Nat) : Env :=
  Env.ofMachine s [(cA m0 + BitVec.ofNat 64 (16 * (64 * ca l + z)), 16),
    (gA m0 + BitVec.ofNat 64 (16 * (64 * l + z)), 16), (cA m0 + BitVec.ofNat 64 (1024 * cb l), 1024),
    (oA m0 + BitVec.ofNat 64 (16 * (64 * l + z)), 16)]

end

public section

variable [Labels] {ws : Array EW} {m0 st st' : MachineData}

/-- `OutRegs` of a body with the same X8 to X13 and X19 to X22. -/
theorem OutRegs.keep {l : Nat} (h : OutRegs m0 st l) (hb : Body m0 st')
    (e : ∀ r ∈ [XReg.X8, .X9, .X10, .X11, .X12, .X13, .X19, .X20, .X21, .X22],
      st'.regs.getXReg r = st.regs.getXReg r) : OutRegs m0 st' l := by
  have e' : ∀ r ∈ [XReg.X19, .X20, .X21, .X22], st'.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact e _ (by simp)
  refine ⟨ctx_keep h.ctx hb e', h.lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (st'.regs.getXReg .X8).toNat = l; rw [e .X8 (by simp)]; exact h.x8
  · show (st'.regs.getXReg .X9).toBitVec = _; rw [e .X9 (by simp)]; exact h.x9
  · show (st'.regs.getXReg .X10).toBitVec = _; rw [e .X10 (by simp)]; exact h.x10
  · show (st'.regs.getXReg .X11).toBitVec = _; rw [e .X11 (by simp)]; exact h.x11
  · show (st'.regs.getXReg .X12).toBitVec = _; rw [e .X12 (by simp)]; exact h.x12
  · show (st'.regs.getXReg .X13).toBitVec = _; rw [e .X13 (by simp)]; exact h.x13

omit [Labels] in
/-- The output element as the loop's `eor`s. -/
theorem out_ew (g a b : EW) :
    (⟨UInt64.ofBitVec ((a.c0.toBitVec ^^^ g.c0.toBitVec) ^^^ b.c0.toBitVec),
      UInt64.ofBitVec ((a.c1.toBitVec ^^^ g.c1.toBitVec) ^^^ b.c1.toBitVec)⟩ : EW) = g + a + b := by
  show EW.mk _ _ = EW.mk ((g.c0 ^^^ a.c0) ^^^ b.c0) ((g.c1 ^^^ a.c1) ^^^ b.c1)
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;> simp only [UInt64.toBitVec_xor] <;> ac_rfl

omit [Labels] in
theorem oF_eq (ws : Array EW) {l z : Nat} (hz : z < 64) :
    oF ws (64 * l + z) =
      gF ws (64 * l + z) + cF ws (64 * ca l + z) + cF ws (64 * cb l + (z + 1) % 64) := by
  have h1 : (z + 1) % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [oF, gF, cF, outW]
  rw [show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega,
    show (64 * ca l + z) / 64 = ca l by omega, show (64 * ca l + z) % 64 = z by omega,
    show (64 * cb l + (z + 1) % 64) / 64 = cb l by omega,
    show (64 * cb l + (z + 1) % 64) % 64 = (z + 1) % 64 by omega]

omit [Labels] in
/-- Elements kept by a write of sixteen bytes apart from them. -/
theorem elems_keep_apart {d d' : DataMem} {a b : BitVec 64} {f : Nat → EW} {N A M o : Nat}
    (h : ElemsAt d a f N) (hN : 16 * N ≤ A) (hab : Apart a A b M) (ha : NoWrap a A)
    (hb : NoWrap b M) (ho : o + 16 ≤ M)
    (hs : SameOutside d d' (InRange (b + BitVec.ofNat 64 o) 16)) : ElemsAt d' a f N :=
  h.keep hs (fun p hp hc ↦ NativeRustcVm.Apart.not_inRange hab ha hb
      (show (p - a).toNat < A from Nat.lt_of_lt_of_le hp hN) (inRange_mono hc ho))
    (show a.toNat + 16 * N ≤ 2 ^ 64 by have : a.toNat + A ≤ 2 ^ 64 := ha; omega)

/-- The output loop's regions: data memory, apart. -/
theorem out_env_wf (hpre : LinearTransposePre ws m0) {s : MachineData} (hb : Body m0 s) {l z : Nat}
    (hl : l < 25) (hz : z < 64) : (envO m0 s l z).WF := by
  have hA := pre_areas hpre
  have hgok := Areas.ok hA (r := ⟨gA m0, weightsBytes⟩) (Or.inl (by simp [wsR]))
  have hcok := Areas.ok hA (r := ⟨cA m0, 5120⟩) (Or.inl (by simp [wsR]))
  have hook := Areas.ok hA (r := ⟨oA m0, weightsBytes⟩) (Or.inl (by simp [wsR]))
  have hgc := Areas.apart_ws hA (i := 0) (j := 1) (by simp [wsR]) (by simp [wsR]) (by decide)
  have hgo := Areas.apart_ws hA (i := 0) (j := 2) (by simp [wsR]) (by simp [wsR]) (by decide)
  have hco := Areas.apart_ws hA (i := 1) (j := 2) (by simp [wsR]) (by simp [wsR]) (by decide)
  simp only [wsR, List.getElem_cons_zero, List.getElem_cons_succ] at hgc hgo hco
  have hca : ca l < 5 := Nat.mod_lt _ (by decide)
  have hcb : cb l < 5 := Nat.mod_lt _ (by decide)
  obtain ⟨hm0, hnw0⟩ := sub_ok hcok (o := 16 * (64 * ca l + z)) (n := 16)
    (by show 16 * (64 * ca l + z) + 16 ≤ 5120; omega)
  obtain ⟨hm1, hnw1⟩ := sub_ok hgok (o := 16 * (64 * l + z)) (n := 16)
    (by show 16 * (64 * l + z) + 16 ≤ 25600; omega)
  obtain ⟨hm2, hnw2⟩ := sub_ok hcok (o := 1024 * cb l) (n := 1024)
    (by show 1024 * cb l + 1024 ≤ 5120; omega)
  obtain ⟨hm3, hnw3⟩ := sub_ok hook (o := 16 * (64 * l + z)) (n := 16)
    (by show 16 * (64 * l + z) + 16 ≤ 25600; omega)
  have h01 : Apart (cA m0 + BitVec.ofNat 64 (16 * (64 * ca l + z))) 16
      (gA m0 + BitVec.ofNat 64 (16 * (64 * l + z))) 16 :=
    Apart.sub (NativeRustcVm.Apart.symm hgc) hcok.2 hgok.2
      (by show 16 * (64 * ca l + z) + 16 ≤ 5120; omega)
      (by show 16 * (64 * l + z) + 16 ≤ 25600; omega) (by decide) (by decide)
  have h02 : Apart (cA m0 + BitVec.ofNat 64 (16 * (64 * ca l + z))) 16
      (cA m0 + BitVec.ofNat 64 (1024 * cb l)) 1024 :=
    have hne : ca l ≠ cb l := by simp only [ca, cb]; omega
    NativeRustcVm.apart_of_le (N := 5120) hcok.2 (by omega) (by omega) (by omega)
  have h03 : Apart (cA m0 + BitVec.ofNat 64 (16 * (64 * ca l + z))) 16
      (oA m0 + BitVec.ofNat 64 (16 * (64 * l + z))) 16 :=
    Apart.sub hco hcok.2 hook.2 (by show 16 * (64 * ca l + z) + 16 ≤ 5120; omega)
      (by show 16 * (64 * l + z) + 16 ≤ 25600; omega) (by decide) (by decide)
  have h12 : Apart (gA m0 + BitVec.ofNat 64 (16 * (64 * l + z))) 16
      (cA m0 + BitVec.ofNat 64 (1024 * cb l)) 1024 :=
    Apart.sub hgc hgok.2 hcok.2 (by show 16 * (64 * l + z) + 16 ≤ 25600; omega)
      (by show 1024 * cb l + 1024 ≤ 5120; omega) (by decide) (by decide)
  have h13 : Apart (gA m0 + BitVec.ofNat 64 (16 * (64 * l + z))) 16
      (oA m0 + BitVec.ofNat 64 (16 * (64 * l + z))) 16 :=
    Apart.sub hgo hgok.2 hook.2 (by show 16 * (64 * l + z) + 16 ≤ 25600; omega)
      (by show 16 * (64 * l + z) + 16 ≤ 25600; omega) (by decide) (by decide)
  have h23 : Apart (cA m0 + BitVec.ofNat 64 (1024 * cb l)) 1024
      (oA m0 + BitVec.ofNat 64 (16 * (64 * l + z))) 16 :=
    Apart.sub hco hcok.2 hook.2 (by show 1024 * cb l + 1024 ≤ 5120; omega)
      (by show 16 * (64 * l + z) + 16 ≤ 25600; omega) (by decide) (by decide)
  refine Env.wf_of ⟨⟨Mapped.kept' hm0 hb.kept, hnw0⟩, ⟨Mapped.kept' hm1 hb.kept, hnw1⟩,
    ⟨Mapped.kept' hm2 hb.kept, hnw2⟩, ⟨Mapped.kept' hm3 hb.kept, hnw3⟩, trivial⟩ ?_
  simp only [envO, Env.ofMachine_regions, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
  exact ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23, fun _ h ↦ h.elim⟩

end

public section

variable [NativeRustcArm.Host] {ws : Array EW} {m0 : MachineData} {k : Nat}

/-- **One element of the output loop**. -/
theorem out_step (hp : Placed code k) (hpre : LinearTransposePre ws m0) {l z : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b22Offset)) (hI : Out m0 ws l z s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b22Offset) ∧ Out m0 ws l (z + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b23Offset) ∧ OutRegs m0 s'.data l ∧
        OutMem m0 ws (64 * l + 64) s'.data)) s := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hl := hI.regs.lt
  have hz := hI.z_lt
  have hca : ca l < 5 := Nat.mod_lt _ (by decide)
  have hcb : cb l < 5 := Nat.mod_lt _ (by decide)
  have hq : (z + 1) % 64 < 64 := Nat.mod_lt _ (by decide)
  have hgok := Areas.ok hA (r := ⟨gA m0, weightsBytes⟩) (Or.inl (by simp [wsR]))
  have hcok := Areas.ok hA (r := ⟨cA m0, 5120⟩) (Or.inl (by simp [wsR]))
  have hook := Areas.ok hA (r := ⟨oA m0, weightsBytes⟩) (Or.inl (by simp [wsR]))
  have hgo := Areas.apart_ws hA (i := 0) (j := 2) (by simp [wsR]) (by simp [wsR]) (by decide)
  have hco := Areas.apart_ws hA (i := 1) (j := 2) (by simp [wsR]) (by simp [wsR]) (by decide)
  simp only [wsR, List.getElem_cons_zero, List.getElem_cons_succ] at hgo hco
  have hnw3 := (sub_ok hook (o := 16 * (64 * l + z)) (n := 16)
    (by show 16 * (64 * l + z) + 16 ≤ 25600; omega)).2
  have hwf := out_env_wf hpre hI.regs.ctx.body hl hz
  have hm : Match (envO m0 s.data l z) outS s.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s.data.regs.getXReg .X14).toBitVec =
          (cA m0 + BitVec.ofNat 64 (16 * (64 * ca l + z))) + BitVec.ofInt 64 8
        rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
          show (s.data.regs.getXReg .X14) = s.data.regs.X14 from rfl, hI.x14]
        congr 2; omega,
       by
        show (s.data.regs.getXReg .X16).toBitVec =
          (gA m0 + BitVec.ofNat 64 (16 * (64 * l + z))) + BitVec.ofInt 64 8
        rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
          show (s.data.regs.getXReg .X16) = s.data.regs.X16 from rfl, hI.x16]
        congr 2; omega,
       by
        show (s.data.regs.getXReg .X15).toBitVec =
          (cA m0 + BitVec.ofNat 64 (1024 * cb l)) + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        exact hI.x15,
       by
        show (s.data.regs.getXReg .X17).toBitVec =
          (oA m0 + BitVec.ofNat 64 (16 * (64 * l + z))) + BitVec.ofInt 64 8
        rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
          show (s.data.regs.getXReg .X17) = s.data.regs.X17 from rfl, hI.x17]
        congr 2; omega,
       trivial⟩ trivial ⟨and63_lt _, trivial⟩ trivial
  refine exec_at (b22_in_code.trans hp.1 (by simp [b22])) e22 hwf hpc hm fun s' hm' hpc' ↦ ?_
  -- the element
  have hx18 : ((envO m0 s.data l z).regs .X18).toNat = z + 1 := hI.x18
  have hel : NativeRustcVm.EWAt s'.data.dmem
      (oA m0 + BitVec.ofNat 64 (16 * (64 * l + z)) + BitVec.ofNat 64 0) (oF ws (64 * l + z)) := by
    have h := KeccakGkr.Match.ewAt_write2 hm' (pre := []) rfl rfl nofun (r := 3) rfl (by decide)
    have he0 := hI.mem.c (64 * ca l + z) (by omega)
    rw [← NativeRustcVm.addr_add_zero (cA m0 + _)] at he0
    have hx0 := load_ew (env := envO m0 s.data l z) (r := 0) he0
    have he1 := hI.mem.g (64 * l + z) (by omega)
    rw [← NativeRustcVm.addr_add_zero (gA m0 + _)] at he1
    have hx1 := load_ew (env := envO m0 s.data l z) (r := 1) he1
    have he2 := hI.mem.c (64 * cb l + (z + 1) % 64) (by omega)
    rw [show cA m0 + BitVec.ofNat 64 (16 * (64 * cb l + (z + 1) % 64)) =
        (cA m0 + BitVec.ofNat 64 (1024 * cb l)) + BitVec.ofNat 64 (16 * ((z + 1) % 64)) by
      rw [NativeRustcVm.addr_add_add]; congr 2; omega] at he2
    have hx2 := load_ew (env := envO m0 s.data l z) (r := 2) he2
    sym_simp at h
    rw [idx63_toNat', hx18] at h
    rw [Nat.zero_add] at hx0 hx1 h
    rw [Nat.add_comm 8, hx0.1, hx0.2, hx1.1, hx1.2, hx2.1, hx2.2, out_ew, ← oF_eq ws hz] at h
    exact h
  -- what the block wrote: the element, in the output
  have hso : SameOutside s.data.dmem s'.data.dmem
      (InRange (oA m0 + BitVec.ofNat 64 (16 * (64 * l + z))) 16) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun p h ↦
      Written.inRange (r := 3) rfl hnw3 (by decide) h
  have hbody : Body m0 s'.data :=
    hI.regs.ctx.body.write hS (by decide) slots_le (wsOff hpre) hm hm' hwf rfl free_ok (by decide)
      fun p h ↦ ⟨⟨oA m0, weightsBytes⟩, by simp [wsR],
        inRange_mono (Written.inRange (r := 3) rfl hnw3 (by decide) h)
          (by show 16 * (64 * l + z) + 16 ≤ 25600; omega)⟩
  have hregs := hI.regs.keep hbody (KeccakGkr.Match.regs_keep hm hm' _ (by decide))
  have hmem : OutMem m0 ws (64 * l + z + 1) s'.data := by
    refine ⟨elems_keep_apart hI.mem.g (by decide) hgo hgok.2 hook.2
        (by show 16 * (64 * l + z) + 16 ≤ 25600; omega) hso,
      elems_keep_apart hI.mem.c (by decide) hco hcok.2 hook.2
        (by show 16 * (64 * l + z) + 16 ≤ 25600; omega) hso, ?_⟩
    refine hI.mem.o.grow (k := 1) (NativeRustcVm.NoWrap.sub (o := 0)
        (by rw [NativeRustcVm.addr_add_zero] at *; exact hook.2)
        (by show 0 + 16 * (64 * l + z + 1) ≤ 25600; omega) |>.trans_eq'
        (by rw [NativeRustcVm.addr_add_zero])) (by rw [Nat.mul_one]; exact hso) fun j hj ↦ ?_
    obtain rfl : j = 0 := by omega
    rw [Nat.add_zero]
    rw [NativeRustcVm.addr_add_zero] at hel
    exact hel
  have h14 := hm'.regs .X14 _ rfl
  have h15 := hm'.regs .X15 _ rfl
  have h16 := hm'.regs .X16 _ rfl
  have h17 := hm'.regs .X17 _ rfl
  have h18 := hm'.regs .X18 _ rfl
  sym_simp at h14 h15 h16 h17 h18
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  have hx18' : (envO m0 s.data l z).regs .X18 + 1#64 = BitVec.ofNat 64 (z + 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat' (by rw [hx18]; omega), hx18, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  simp only [hx18'] at hpc'
  by_cases hlast : z = 63
  · subst hlast
    simp only [show (BitVec.ofNat 64 (63 + 2) == 65#64) = true from rfl, Bool.not_true,
      Bool.false_eq_true, ite_false, NativeRustcVmArm.Vm.LinearTranspose.b22_length, NativeRustcVmArm.Vm.LinearTranspose.b22Length] at hpc'
    exact .done _ (Or.inr ⟨hpc', hregs, hmem⟩)
  · have hc : (BitVec.ofNat 64 (z + 2) == 65#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h
      simp at this; omega
    simp only [hc, Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨hpc'.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b22Offset) NativeRustcVmArm.Vm.LinearTranspose.label_19_at), hregs,
      by rw [show 64 * l + (z + 1) = 64 * l + z + 1 by omega]; exact hmem, by omega, ?_, ?_, ?_, ?_,
      ?_⟩)
    · show (s'.data.regs.getXReg .X14).toBitVec = _
      rw [h14, show (envO m0 s.data l z).base 0 = cA m0 + BitVec.ofNat 64 (16 * (64 * ca l + z))
          from rfl, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add_add]
      congr 2; omega
    · show (s'.data.regs.getXReg .X15).toBitVec = _
      rw [h15, show (envO m0 s.data l z).base 2 = cA m0 + BitVec.ofNat 64 (1024 * cb l) from rfl,
        show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    · show (s'.data.regs.getXReg .X16).toBitVec = _
      rw [h16, show (envO m0 s.data l z).base 1 = gA m0 + BitVec.ofNat 64 (16 * (64 * l + z)) from rfl,
        show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add_add]
      congr 2; omega
    · show (s'.data.regs.getXReg .X17).toBitVec = _
      rw [h17, show (envO m0 s.data l z).base 3 = oA m0 + BitVec.ofNat 64 (16 * (64 * l + z)) from rfl,
        show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add_add]
      congr 2; omega
    · show (s'.data.regs.getXReg .X18).toBitVec.toNat = _
      rw [h18, hx18', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
