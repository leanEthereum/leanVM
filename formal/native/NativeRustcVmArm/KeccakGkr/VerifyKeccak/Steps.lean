module

public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Basic
public import NativeRustcVm.Tables.Same

/-!
# `verify_keccak`: the steps every part takes

- Addresses as numbers: the frame's (`loc_toNat`), a callee's stack (`sb_toNat`), a byte in a
  range (`inR_nat`); bytes a change misses stay (`same_num`).
- `callStep`: a block ending in a call, then the callee's contract, within the frame (`VFr`).
- `blockStep`: a block that writes nothing, within the frame.
- The exits: `exitFail` (`.LVerifyKeccak_31`, `None`), `exitAt` (the epilogue `b73`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)
open NativeRustcVm (Region)

public section

@[simp] theorem gx0 (m : MachineData) : m.regs.getXReg .X0 = m.regs.X0 := rfl
@[simp] theorem gx1 (m : MachineData) : m.regs.getXReg .X1 = m.regs.X1 := rfl
@[simp] theorem gx2 (m : MachineData) : m.regs.getXReg .X2 = m.regs.X2 := rfl
@[simp] theorem gx3 (m : MachineData) : m.regs.getXReg .X3 = m.regs.X3 := rfl
@[simp] theorem gx4 (m : MachineData) : m.regs.getXReg .X4 = m.regs.X4 := rfl
@[simp] theorem gx5 (m : MachineData) : m.regs.getXReg .X5 = m.regs.X5 := rfl
@[simp] theorem gx6 (m : MachineData) : m.regs.getXReg .X6 = m.regs.X6 := rfl
@[simp] theorem gx7 (m : MachineData) : m.regs.getXReg .X7 = m.regs.X7 := rfl

/-- A register a block set to `v`. -/
theorem reg_of [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    m.regs.getXReg r = w :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

theorem ult_ofNat (x : BitVec 64) {c : Nat} (hc : c < 2 ^ 64) :
    x.ult (BitVec.ofNat 64 c) = decide (x.toNat < c) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

/-- `x - c`, saturating. -/
theorem ite_sub (x : BitVec 64) (c : Nat) (hc : c < 2 ^ 64) :
    (if x.ult (BitVec.ofNat 64 c) = true then 0#64 else x - BitVec.ofNat 64 c).toNat =
      x.toNat - c := by
  rw [ult_ofNat x hc]
  by_cases h : x.toNat < c
  · simp only [h, decide_true, ite_true, BitVec.toNat_ofNat]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    have hle : BitVec.ofNat 64 c ≤ x := by
      rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]; omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

/-- `min x c`. -/
theorem ite_min (x : BitVec 64) (c : Nat) (hc : c < 2 ^ 64) :
    (if x.ult (BitVec.ofNat 64 c) = true then x else BitVec.ofNat 64 c).toNat = min x.toNat c := by
  rw [ult_ofNat x hc]
  by_cases h : x.toNat < c
  · simp only [h, decide_true, ite_true]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hc]; omega

/-- A register a block set to a frame address. -/
theorem reg_loc [Labels] {m0 m st : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S st) {r : XReg} {o : Nat}
    (h : S.reg r = some (.ptr 0 (o : Int))) : (st.regs.getXReg r).toBitVec = loc m0 o := by
  rw [hm.regs r _ h]
  simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some, BitVec.ofInt_natCast]

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 3360 := by decide

theorem slots_ge : ∀ p ∈ slots, 3264 ≤ p.1 := by decide

/-- The block's writes are in the frame below the slots. -/
theorem writeOk_low {m0 : MachineData} {env : Env} {S : SState}
    (hw : S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 3264)) = true) :
    ∀ w ∈ S.mem, WriteOk env 3360 slots (outs m0) w := by
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  intro w hw'
  exact .inl ⟨(hw w hw').1, by have := (hw w hw').2; omega,
    fun q hq ↦ .inl (by have := slots_ge q hq; have := (hw w hw').2; omega)⟩

/-- The block's writes are in the frame's ranges `L`, all below the slots. -/
theorem writeOk_ranges {m0 : MachineData} {env : Env} {S : SState} {L : List (Nat × Nat)}
    (hL : L.all (fun p ↦ decide (p.2 ≤ 3264)) = true)
    (hw : S.mem.all (fun w ↦ w.r == 0 &&
      L.any (fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2))) = true) :
    ∀ w ∈ S.mem, WriteOk env 3360 slots (outs m0) w := by
  simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw hL
  intro w hw'
  obtain ⟨hr, p, hp, h1, h2⟩ := hw w hw'
  have := hL p hp
  exact .inl ⟨hr, by omega, fun q hq ↦ .inl (by have := slots_ge q hq; omega)⟩

/-- The callee-saved registers. -/
@[expose] def csL : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

theorem mem_csL {r : XReg} (h : calleeSaved r = true) : r ∈ csL := by
  cases r <;> simp_all [calleeSaved, csL]

/-- **A block that keeps the callee-saved registers' symbolic values** keeps their values. -/
theorem cs_block [Labels] {env : Env} {S0 S : SState} {m m' : MachineData} (hm0 : Match env S0 m)
    (hm : Match env S m') (h : csL.all (fun r ↦ (S0.reg r).isSome && S.reg r == S0.reg r) = true) :
    ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r :=
  fun r hr ↦ Match.regs_keep hm0 hm csL h r (mem_csL hr)

/-! ## Addresses as numbers -/

section
variable {m0 : MachineData}

theorem fb_toNat (hN : 7008 ≤ m0.regs.SP.toNat) : (fb m0).toNat = m0.regs.SP.toNat - 3360 :=
  base_toNat (by omega)

theorem loc_toNat (hN : 7008 ≤ m0.regs.SP.toNat) {o : Nat} (ho : o ≤ 3360) :
    (loc m0 o).toNat = m0.regs.SP.toNat - 3360 + o := by
  have := m0.regs.SP.toNat_lt
  rw [NativeRustcVm.toNat_add_ofNat (by rw [fb_toNat hN]; omega), fb_toNat hN]

theorem sb_toNat (hN : 7008 ≤ m0.regs.SP.toNat) {st : MachineData} (hfr : VFr m0 st) {n : Nat}
    (hn : n ≤ 3648) : (stackBelow st n).toNat = m0.regs.SP.toNat - 3360 - n := by
  rw [stackBelow_eq hfr.sp (by omega), base_toNat (by omega)]
  omega

theorem inR_nat {x q : BitVec 64} {n : Nat} (hnw : x.toNat + n ≤ 2 ^ 64) (h : InRange x n q) :
    x.toNat ≤ q.toNat ∧ q.toNat < x.toNat + n :=
  (NativeRustcVm.inRange_iff hnw).mp h

/-- **Bytes a change misses** stay. -/
theorem same_num {d d' : DataMem} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    {A : BitVec 64} {k : Nat} (hA : A.toNat + k ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < A.toNat ∨ A.toNat + k ≤ q.toNat) :
    NativeRustcVm.Layout.Same d d' A k := by
  intro j hj
  apply hs
  intro hq
  have := hR _ hq
  rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
  omega

/-- The outputs' bytes as numbers. -/
theorem outs_nat [Labels] {a : DecArea} {inst : Array EW} (hn : Nums a inst m0) {q : BitVec 64}
    (h : outs m0 q) :
    ((tA m0).toNat ≤ q.toNat ∧ q.toNat < (tA m0).toNat + 760) ∨
      ((scA m0).toNat ≤ q.toNat ∧ q.toNat < (scA m0).toNat + 205824) ∨
      ((clA m0).toNat ≤ q.toNat ∧ q.toNat < (clA m0).toNat + 97288) ∨
      ((oA m0).toNat ≤ q.toNat ∧ q.toNat < (oA m0).toNat + 1608) := by
  rcases h with h | h | h | h
  · exact .inl (inR_nat hn.tW h)
  · exact .inr (.inl (inR_nat hn.sW h))
  · exact .inr (.inr (.inl (inR_nat hn.cW h)))
  · exact .inr (.inr (.inr (inR_nat hn.oW h)))

/-- The outputs are apart from the frame. -/
theorem outs_frame [Labels] {a : DecArea} {inst : Array EW} (hn : Nums a inst m0) :
    ∀ q, outs m0 q → ¬InRange (fb m0) 3360 q := by
  intro q hq hf
  have := m0.regs.SP.toNat_lt
  have h1 := inR_nat (by rw [fb_toNat hn.hN]; omega) hf
  rw [fb_toNat hn.hN] at h1
  have := hn.tS; have := hn.sS; have := hn.cS; have := hn.oS; have := hn.hN
  rcases outs_nat hn hq with _ | _ | _ | _ <;> omega

end

/-! ## Steps -/

section
variable [Host] {m0 : MachineData}

/-- **A block ending in a call**, then the callee's contract: the callee writes its stack, the
frame's `n` bytes from `lo` and the outputs. -/
theorem callStep {a : DecArea} {inst : Array EW} (hn : Nums a inst m0) {ds : List Directive}
    {i : Nat} {rs : List (BitVec 64 × Nat)} {S0 S' : SState} {l : Label}
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop} {N' lo n : Nat}
    {R : MachineState → Prop} {m : MachineData}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds S0 = some (S', .call l))
    (hfr : VFr m0 m) (hm : Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S0 m)
    (hwf : (Env.ofMachine m ((fb m0, 3360) :: rs)).WF) (hsp : S'.sp = S0.sp)
    (hW : ∀ w ∈ S'.mem, WriteOk (Env.ofMachine m ((fb m0, 3360) :: rs)) 3360 slots (outs m0) w)
    (hle : 3360 + N' ≤ 7008) (hlo : lo + n ≤ 3264)
    (hspec : Spec (Labels.label l) P Q)
    (hP : ∀ st : MachineData, Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S' st →
      VFr m0 st → P st)
    (hQ : ∀ st m', Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S' st → VFr m0 st →
      Q st m' → SameOutside st.dmem m'.dmem (fun q ↦
      InRange (stackBelow st N') N' q ∨ InRange (fb m0 + BitVec.ofNat 64 lo) n q ∨
        outs m0 q) ∧ Saved st m')
    (cont : ∀ st m2 : MachineData, Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S' st →
      VFr m0 st → Q st m2 → VFr m0 m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hN : verifyKeccakStack ≤ m0.regs.SP.toNat := by rw [stack_eq]; exact hn.hN
  refine exec_then hk hrun hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : VFr m0 st.data :=
    hfr.ofBlockW hm hm1 hwf rfl hsp (fun r hr ↦ by cases hr) rfl (by decide) hN slots_le hW
  refine Fr.leafIn hfr1 hN (N' := N') (lo := lo) (n := n) (by rw [stack_eq]; omega)
    (by omega) (fun r hr ↦ by cases hr)
    (fun p hp ↦ ⟨slots_le p hp, .inr (by have := slots_ge p hp; omega)⟩) (outs_frame hn) hspec
    hpc (hP st.data hm1 hfr1) (fun m' hq ↦ hQ st.data m' hm1 hfr1 hq)
        fun m2 hfr2 hq hcs ↦ cont st.data m2 hm1 hfr1 hq hfr2 hcs

omit [Host] in
theorem envM_wf [Labels] {a : DecArea} {inst : Array EW} (hn : Nums a inst m0) {m : MachineData}
    (hfr : VFr m0 m) : (envM m0 m).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (frame_mapped hn.stk (by decide) i hi),
    base_noWrap (by have := hn.hN; omega)⟩, trivial⟩ (List.pairwise_singleton _ _)

omit [Host] in
theorem matchM [Labels] {a : DecArea} {inst : Array EW} (hn : Nums a inst m0) {m : MachineData}
    (hfr : VFr m0 m) : Match (envM m0 m) midS m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hn.stk (by decide) (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial trivial

/-- **A block that writes nothing**, from `midS`. -/
theorem blockStep {a : DecArea} {inst : Array EW} (hn : Nums a inst m0) {ds : List Directive}
    {i : Nat} {S' : SState} {x : Exit} {R : MachineState → Prop} {m : MachineData}
    (hk : ds.IsInfixAt Host.prog i) (hrun : exec ds midS = some (S', x))
    (hfr : VFr m0 m) (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    (cont : ∀ st : MachineState, Match (envM m0 m) S' st.data → VFr m0 st.data →
      st.data.dmem = m.dmem → PcOk (envM m0 m) x (Host.addrOf (i + ds.length)) st →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := envM_wf hn hfr
  refine exec_then hk hrun hwf (matchM hn hfr) fun st hm1 hpc ↦ ?_
  have hd : st.data.dmem = m.dmem := hm1.dmem_eq hwf hmem
  exact cont st hm1 (hfr.ofBlock (matchM hn hfr) hm1 hwf rfl hmem (by rw [hsp]; rfl)
    (fun r hr ↦ by cases hr)) hd hpc

/-- **The epilogue** (`b73`): the entry's return address, callee-saved registers and SP; X0 and
memory as they were. -/
theorem exitAt {a : DecArea} {inst : Array EW} {k : Nat} (hp : Placed code k)
    (hn : Nums a inst m0) {m : MachineData} (hfr : VFr m0 m) {Q : MachineData → Prop}
    (hQ : ∀ m', retOf m' = retOf m0 → Saved m0 m' → m'.regs.X0 = m.regs.X0 →
      m'.dmem = m.dmem → Q m') :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ Q st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b73Offset)⟩ := by
  have hwf := envM_wf hn hfr
  refine exec_then (b73_in_code.trans hp.1 (by simp [b73])) run_b73 hwf (matchM hn hfr)
    fun st hm1 hpc ↦ .done _ ?_
  obtain ⟨hret, hsv⟩ := hfr.exit (rs := []) hm1 hwf (by decide)
  refine ⟨?_, hQ _ hret hsv (Match.reg_eq (matchM hn hfr) hm1 (r := .X0) rfl rfl)
    (hm1.dmem_eq hwf rfl)⟩
  simp only [PcOk] at hpc
  rw [hpc, hret]

/-- **The failure exit** (`.LVerifyKeccak_31`, `b72`): X0 `0`, then the epilogue. -/
theorem exitFail {a : DecArea} {inst : Array EW} {k : Nat} (hp : Placed code k)
    (hn : Nums a inst m0) {m : MachineData} (hfr : VFr m0 m) {Q : MachineData → Prop}
    (hQ : ∀ m', retOf m' = retOf m0 → Saved m0 m' → m'.regs.X0 = 0 →
      m'.dmem = m.dmem → Q m') :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ Q st.data)
      ⟨m, Labels.label NativeRustcVmArm.Vm.VerifyKeccak.label_31⟩ := by
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyKeccak.label_31 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b72Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyKeccak.b72Offset) NativeRustcVmArm.Vm.VerifyKeccak.label_31_at]
  refine blockStep hn (b72_in_code.trans hp.1 (by simp [b72])) run_b72 hfr rfl rfl
    fun st hm1 hfr1 hd hpc ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only [PcOk] at hpc
  subst hpc
  refine exitAt hp hn hfr1 fun m' hret hsv hx hd' ↦ hQ m' hret hsv ?_ (hd'.trans hd)
  rw [hx]
  exact UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)

end

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
