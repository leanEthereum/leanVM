module

public import NativeRustcVmX64.Wire.PhaseM.Sizes
public import NativeRustcVmX64.Code.Vm.InsD.Names

/-!
# `phase_m`: the distinct positions (x86-64)

`sort_run`: from the sort's head (`SortSt … 0`), each query inserted by `ins_d` into the positions
at the working area's byte 2048 (`b14`, `b15`), then the count's check (`b16`, at least one
position, at most 256), to the checks of the sizes (`Chk`, `b19`).
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write load_ofMachine
  stackOk_callee)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off Mapped.keeps)
open NativeRustcVmX64.Wire.Decode (eqv_eval ult_eval)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **After the sort** (`b16`): every query inserted. -/
structure At16 [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (height lw rw c5 : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b16Offset)
  bod : Bod m0 8 st.data
  model : phaseM B c = tail B qs height lw rw c5
  len : qs.length = count
  cnt0 : 0 < count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  hlt : height < 2 ^ 32
  lwlt : lw < 2 ^ 32
  rwlt : rw < 2 ^ 32
  f40 : FW m0 st.data.dmem 40 count.toUInt64
  f32 : FW m0 st.data.dmem 32 height.toUInt64
  f16 : FW m0 st.data.dmem 16 lw.toUInt64
  f24 : FW m0 st.data.dmem 24 rw.toUInt64
  rbp : (reg st.data .rbp).toNat = (sortD qs).length
  rdi : reg st.data .rdi = wa m0 2048
  rbx : reg st.data .rbx = wa m0 2048
  qsW : NativeRustcVm.WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  psW : NativeRustcVm.WordsAt st.data.dmem (wa m0 2048) ((sortD qs).map Nat.toUInt64)
  rd : ReaderAt st.data.dmem (RD m0) bp B c5

/-- **At the size checks** (`b19`): the distinct positions `ps` at the working area's byte 2048. -/
structure Chk [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (height lw rw c5 : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b19Offset)
  bod : Bod m0 8 st.data
  model : phaseM B c = tail B qs height lw rw c5
  len : qs.length = count
  cnt0 : 0 < count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  hlt : height < 2 ^ 32
  lwlt : lw < 2 ^ 32
  rwlt : rw < 2 ^ 32
  ps0 : 0 < (sortD qs).length
  ps256 : (sortD qs).length ≤ 256
  f40 : FW m0 st.data.dmem 40 count.toUInt64
  f32 : FW m0 st.data.dmem 32 height.toUInt64
  f16 : FW m0 st.data.dmem 16 lw.toUInt64
  f24 : FW m0 st.data.dmem 24 rw.toUInt64
  rbp : (reg st.data .rbp).toNat = (sortD qs).length
  rdi : reg st.data .rdi = wa m0 2048
  rbx : reg st.data .rbx = wa m0 2048
  r15 : (reg st.data .r15).toNat = rw
  qsW : NativeRustcVm.WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  psW : NativeRustcVm.WordsAt st.data.dmem (wa m0 2048) ((sortD qs).map Nat.toUInt64)
  rd : ReaderAt st.data.dmem (RD m0) bp B c5

end

public section

theorem sortD_ne {qs : List Nat} (h : qs ≠ []) : sortD qs ≠ [] := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil qs h
  intro he
  have := ((sortD_aux qs [] List.Pairwise.nil).2 q).2 (.inl hq)
  rw [show qs.foldl insD [] = sortD qs from rfl, he] at this
  simp at this

theorem length_sortD_take (qs : List Nat) (i : Nat) : (sortD (qs.take i)).length ≤ i := by
  have := length_sortD (qs.take i)
  simp only [List.length_take] at this
  omega

theorem sortD_lt {qs : List Nat} (h : ∀ q ∈ qs, q < 2 ^ 32) : ∀ y ∈ sortD qs, y < 2 ^ 32 :=
  fun y hy ↦ h y (mem_sortD hy)

/-- `b16`'s test, over its two constants: at least one position, at most 256. -/
theorem c16_gen (n a b : BitVec 64) (ha : a.toNat + 257 = 2 ^ 64) (hb : b.toNat + 256 = 2 ^ 64) :
    (!CmpOp.apply .ult .W64 (BinOp.apply .add .W64 n a) b) =
      decide (1 ≤ n.toNat ∧ n.toNat ≤ 256) := by
  rw [ult_eval]
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add]
  have hn := n.isLt
  generalize n.toNat = x at *
  generalize a.toNat = y at *
  generalize b.toNat = z at *
  generalize hP : (2 : Nat) ^ 64 = P at *
  have hmod : (x + y) % P = if x + y < P then x + y else x + y - P := by
    split
    · exact Nat.mod_eq_of_lt (by assumption)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  by_cases h : 1 ≤ x ∧ x ≤ 256
  · rw [decide_eq_true h, decide_eq_false (by split <;> omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by split <;> omega)]; rfl

/-- `b16`'s test: at least one position, at most 256. -/
theorem c16_eval (n : BitVec 64) :
    (!CmpOp.apply .ult .W64 (BinOp.apply .add .W64 n (BitVec.ofNat 64 18446744073709551359))
      (BitVec.ofNat 64 18446744073709551360)) = decide (1 ≤ n.toNat ∧ n.toNat ≤ 256) :=
  c16_gen n _ _ (by rw [BitVec.toNat_ofNat]; rfl) (by rw [BitVec.toNat_ofNat]; rfl)

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **A query inserted**: from the sort's head, `ins_d`; to the next head or past the loop. -/
theorem sort_step (hp : Placed code k) (G : Geo m0 bp B.length)
    (hins : Spec (Labels.label NativeRustcVmX64.Vm.InsD.entryLabel) InsDPre InsDPost) {count : Nat} {qs : List Nat}
    {height lw rw c5 i : Nat} {st : MachineState}
    (h : SortSt m0 bp B c k count qs height lw rw c5 i st) :
    Eventually (step1 Host.exe) (fun st' ↦ SortSt m0 bp B c k count qs height lw rw c5 (i + 1) st' ∨
      At16 m0 bp B c k count qs height lw rw c5 st') st := by
  have hS := h
  obtain ⟨hpc, hbod, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, hi, hf40, hf32, hf16, hf24, h13,
    h15, hbp, hdi, hqW, hpW, hrd⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsR := G.sR
  have hsB := G.sB
  have hsW := G.sW
  have hrW := G.rW
  have hbW := G.bW
  have hrn := G.rNw
  have hqi : i < qs.length := by omega
  have hps := length_sortD_take qs i
  -- `b14`: query `i`, `ins_d`.
  have h15' : reg st.data .r15 = BitVec.ofNat 64 (8 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [h15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm14 : Match (aEnv m0 st.data (8 * i) 8 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b14Offset + b14.length)).toBitVec) qS
      st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (reg st.data .r14) (reg st.data .r15) =
          wa m0 (8 * i) + BitVec.ofInt 64 0
        rw [NativeRustcVmX64.Transcript.ofInt_zero64, BitVec.add_zero, hbod.r14, h15']
        simp [BinOp.apply], trivial⟩
  obtain ⟨hmid14, hw14, hbx14, hdx14, hsi14, hdi14, hk14⟩ := ok_b14
  refine ablk hp G b14_in_code (by simp [b14]) exit_b14 (by omega) (by omega) hmid14
    (fun w hw ↦ .inl ⟨(hw14 w hw).1, by have := (hw14 w hw).2; omega,
      .inl (by have := (hw14 w hw).2; omega)⟩)
    (hk14 .r12 (by simp)) (hk14 .r14 (by simp)) hpc hbod hm14 fun s1 hb1 hs1 hkeep1 hsw1 hm1 hpc1 ↦ ?_
  have hq : (reg s1.data .rdx) = (qs[i].toUInt64).toBitVec := by
    rw [show reg s1.data .rdx = _ from hm1.regs .rdx _ hdx14]
    show (aEnv m0 st.data (8 * i) 8 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b14Offset + b14.length)).toBitVec).load 1 0 8 = _
    refine load_ofMachine (o := 0) (b := wa m0 (8 * i)) rfl ?_
    rw [off_zero]
    have := NativeRustcVm.WordsAt.getElem hqW (i := i) (by simp; omega)
    simpa [wa, off_off] using this
  have hdi1 : reg s1.data .rdi = wa m0 2048 := (hm1.regs .rdi _ hdi14).trans hdi
  have hsi1 : (reg s1.data .rsi).toNat = (sortD (qs.take i)).length := by
    rw [show reg s1.data .rsi = reg st.data .rbp from hm1.regs .rsi _ hsi14]; exact hbp
  have hsp1 : rspOf s1.data = stackBelow m0 160 := by rw [hb1.fr.sp, off_zero]
  obtain ⟨hcs1, -⟩ := callee_toNat (n := 0) hsp1 (by omega)
  have hw2048 := G.wa (o := 2048) (by omega)
  have hpre : InsDPre s1.data := by
    refine ⟨stackOk_callee G.st hb1.fr.kept hsp1 (by unfold insDStack; omega),
      by rw [hsi1]; omega, ?_, ?_⟩
    · rw [hdi1]
      have hwm : NativeRustcVm.Mapped m0.dmem (WK m0) 483584 := G.wOk.1
      exact ⟨NativeRustcVmX64.Transcript.mapped_off (o := 2048) (k := 2048)
        (Mapped.keeps hwm hb1.fr.kept) (by omega), show (wa m0 2048).toNat + 2048 ≤ 2 ^ 64 by omega⟩
    · rw [hdi1]
      refine List.pairwise_pair.mpr ?_
      show NativeRustcVm.Apart (stackBelow s1.data insDStack) (insDStack + 8) (wa m0 2048) 2048
      unfold NativeRustcVm.Apart insDStack
      rw [hcs1, hw2048]; omega
  simp only [PcOk] at hpc1
  refine call_then (env := aEnv m0 st.data (8 * i) 8 (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b14Offset + b14.length)).toBitVec)
    (l := NativeRustcVmX64.Vm.InsD.entryLabel) ⟨hpc1.1, hpc1.2⟩ hins hpre
    fun s2 hpc2 hrsp2 ⟨hres2, hso2, hsv2⟩ ↦ ?_
  rw [hdi1] at hres2 hso2
  have hso2' : NativeRustcVm.SameOutside s1.data.dmem s2.data.dmem
      (fun q ↦ (WK m0).toNat + 2048 ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 4096) :=
    hso2.mono fun q hq ↦ by
      have := iv_of_inRange (by rw [hw2048]; omega) hq
      rw [hw2048] at this; omega
  have hb2 : Bod m0 8 s2.data := Bod.call G hb1 hsv2 hrsp2 hso2' fun q hq ↦
    ⟨.inr (.inr (.inr (by omega))), by omega⟩
  have hpW1 : NativeRustcVm.WordsAt s1.data.dmem (wa m0 2048)
      ((sortD (qs.take i)).map Nat.toUInt64) := by
    refine wordsAt_keep hpW hs1 (by rw [List.length_map, hw2048]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw2048]
    rcases hq with hq | hq <;> omega
  have hres := hres2 (sortD (qs.take i)) hsi1.symm
    (fun y hy ↦ by have := sortD_lt (fun q hq ↦ hqlt q (List.mem_of_mem_take hq)) y hy; omega)
    hpW1
  rw [show (reg s1.data .rdx).toNat = qs[i] by
      rw [hq, UInt64.toNat_toBitVec, toNat_toUInt64 (by have := hqlt _ (List.getElem_mem hqi); omega)],
    ← sortD_take_succ qs hqi] at hres
  obtain ⟨hn2, hpW2⟩ := hres
  have rk2 : ∀ x ∈ [Reg64.rbp, .rbx, .r13, .r15], reg s2.data x = reg s1.data x := fun x hx ↦ by
    have hc : calleeSaved x = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> rfl
    exact hsv2.1 x hc
  -- What `b14` and `ins_d` changed.
  have hs1' : NativeRustcVm.SameOutside st.data.dmem s1.data.dmem (fun q ↦
      SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 152) := hsw1.mono fun q ⟨w, hw, h⟩ ↦ by
    have := hw14 w hw
    rcases h with ⟨-, h1, h2⟩ | ⟨h, -⟩
    · omega
    · omega
  have hs12 : NativeRustcVm.SameOutside st.data.dmem s2.data.dmem (fun q ↦
      (SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 152) ∨
      ((WK m0).toNat + 2048 ≤ q.toNat ∧ q.toNat < (WK m0).toNat + 4096)) := hs1'.trans hso2'
  have hkf : ∀ o v, 16 ≤ o → o + 8 ≤ 48 → FW m0 st.data.dmem o v → FW m0 s2.data.dmem o v :=
    fun o v h1 h2 hf ↦ hf.keep G (by omega) hs12 fun q hq ↦ by rcases hq with hq | hq <;> omega
  have hw0 := G.wa (o := 0) (by omega)
  have hqW2 : NativeRustcVm.WordsAt s2.data.dmem (wa m0 0) (qs.map Nat.toUInt64) := by
    refine wordsAt_keep hqW hs12 (by rw [List.length_map, hw0]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw0]
    rcases hq with hq | hq <;> omega
  have hR2 : ReaderAt s2.data.dmem (RD m0) bp B c5 :=
    reader_keep hrd hs12 (fun q hq ↦ by rcases hq with hq | hq <;> omega)
      (fun q hq ↦ by rcases hq with hq | hq <;> omega)
  have hbx2 : reg s2.data .rbx = wa m0 2048 := by
    rw [rk2 .rbx (by simp), show reg s1.data .rbx = _ from hm1.regs .rbx _ hbx14]; exact hdi
  -- `b15`: the count, the next query.
  obtain ⟨hok15, hdi15, hbp15, h15_15, hk15⟩ := ok_b15
  refine fblk hp G b15_in_code (by simp [b15]) exit_b15 nofun hok15 (hk15 .r12 (by simp))
    (hk15 .r14 (by simp)) (st := ⟨s2.data, _⟩) (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b14_next))
    hb2 fun s3 hb3 hd3 hm3 hpc3 ↦ ?_
  have hdi3 : reg s3.data .rdi = wa m0 2048 := by
    rw [show reg s3.data .rdi = reg s2.data .rbx from hm3.regs .rdi _ hdi15]; exact hbx2
  have hbp3 : (reg s3.data .rbp).toNat = (sortD (qs.take (i + 1))).length := by
    rw [show reg s3.data .rbp = reg s2.data .rax from hm3.regs .rbp _ hbp15]; exact hn2
  have h15_3 : (reg s3.data .r15).toNat = 8 * (i + 1) := by
    rw [show reg s3.data .r15 = BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg s2.data .r15) from
      hm3.regs .r15 _ h15_15, rk2 .r15 (by simp),
      show reg s1.data .r15 = reg st.data .r15 from hm1.regs .r15 _ (hk14 .r15 (by simp))]
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, h15]
    omega
  have h13_3 : (reg s3.data .r13).toNat = 8 * count := by
    rw [show reg s3.data .r13 = reg s2.data .r13 from hm3.regs .r13 _ (hk15 .r13 (by simp)),
      rk2 .r13 (by simp),
      show reg s1.data .r13 = reg st.data .r13 from hm1.regs .r13 _ (hk14 .r13 (by simp))]
    exact h13
  have hbx3 : reg s3.data .rbx = wa m0 2048 := by
    rw [show reg s3.data .rbx = reg s2.data .rbx from hm3.regs .rbx (.reg .rbx) (by decide +kernel)]
    exact hbx2
  simp only [PcOk] at hpc3
  have hc : (SBool.cmp .eq .W64 (.reg .r13) (.bin .add .W64 (.lit 8) (.reg .r15))).not.eval
      (frameEnv m0 s2.data 160 []) = !decide (count = i + 1) := by
    show (!CmpOp.apply .eq .W64 (reg s2.data .r13)
      (BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg s2.data .r15))) = _
    have a1 : (reg s2.data .r13).toNat = 8 * count := by
      rw [rk2 .r13 (by simp),
        show reg s1.data .r13 = reg st.data .r13 from hm1.regs .r13 _ (hk14 .r13 (by simp))]
      exact h13
    have a2 : (BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg s2.data .r15)).toNat = 8 * (i + 1) := by
      rw [rk2 .r15 (by simp),
        show reg s1.data .r15 = reg st.data .r15 from hm1.regs .r15 _ (hk14 .r15 (by simp))]
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, h15]
      omega
    rw [eqv_eval, a1, a2]
    by_cases hh : count = i + 1
    · simp [hh]
    · simp only [hh, decide_false]
      rw [decide_eq_false (by omega)]
  rw [hc] at hpc3
  rw [← hd3] at hpW2 hqW2 hR2
  have hf : ∀ o v, 16 ≤ o → o + 8 ≤ 48 → FW m0 st.data.dmem o v → FW m0 s3.data.dmem o v :=
    fun o v h1 h2 h ↦ by rw [hd3]; exact hkf o v h1 h2 h
  by_cases hlast : count = i + 1
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    have htk : qs.take (i + 1) = qs := List.take_of_length_le (by omega)
    rw [htk] at hbp3 hpW2
    exact .done _ (.inr ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b15_next), hb3, hmod, hql, hc0,
      hcnt, hqlt, hhl, hlwl, hrwl, hf 40 _ (by omega) (by omega) hf40,
      hf 32 _ (by omega) (by omega) hf32, hf 16 _ (by omega) (by omega) hf16,
      hf 24 _ (by omega) (by omega) hf24, hbp3, hdi3, hbx3, hqW2, hpW2, hR2⟩)
  simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc3
  exact .done _ (.inl ⟨hpc3.trans (hp.label NativeRustcVmX64.Vm.PhaseM.label_9_at), hb3, hmod, hql, hc0, hcnt, hqlt, hhl,
    hlwl, hrwl, by omega, hf 40 _ (by omega) (by omega) hf40, hf 32 _ (by omega) (by omega) hf32,
    hf 16 _ (by omega) (by omega) hf16, hf 24 _ (by omega) (by omega) hf24, h13_3, h15_3, hbp3,
    hdi3, hqW2, hpW2, hR2⟩)

/-- **The sort**, then the count's check (`b16`). -/
theorem sort_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hins : Spec (Labels.label NativeRustcVmX64.Vm.InsD.entryLabel) InsDPre InsDPost) {count : Nat} {qs : List Nat} {height lw rw c5 : Nat} {st : MachineState}
    (h : SortSt m0 bp B c k count qs height lw rw c5 0 st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      Chk m0 bp B c k count qs height lw rw c5 st') st := by
  refine Eventually.bind (Sym.loop (tr := step1 Host.exe)
    (Q := fun st ↦ At16 m0 bp B c k count qs height lw rw c5 st)
    (fun n st ↦ ∃ i, n = count - i ∧ SortSt m0 bp B c k count qs height lw rw c5 i st)
    (fun _ st ⟨i, hn, h⟩ ↦ Eventually.mono (sort_step hp G hins h) fun _ h' ↦ by
      rcases h' with h' | h'
      · exact .inr ⟨count - (i + 1), by have := h.ilt; omega, i + 1, rfl, h'⟩
      · exact .inl h')
    ⟨0, rfl, h⟩) fun s h16 ↦ ?_
  obtain ⟨hpc, hbod, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, hf40, hf32, hf16, hf24, hbp, hdi,
    hbx, hqW, hpW, hrd⟩ := h16
  obtain ⟨hok16, h15_16, hk16⟩ := ok_b16
  refine fblk hp G b16_in_code (by simp [b16]) exit_b16 nofun hok16 (hk16 .r12 (by simp))
    (hk16 .r14 (by simp)) hpc hbod fun s1 hb1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hps0 : 0 < (sortD qs).length :=
    List.length_pos_iff.mpr (sortD_ne (List.ne_nil_of_length_pos (by omega)))
  have hps256 : (sortD qs).length ≤ 256 := by have := length_sortD qs; omega
  have hc : (SBool.cmp .ult .W64 (.bin .add .W64 (.reg .rbp) (.lit 18446744073709551359))
      (.lit 18446744073709551360)).not.eval (frameEnv m0 s.data 160 []) = true := by
    show (!CmpOp.apply .ult .W64 (BinOp.apply .add .W64 (reg s.data .rbp)
      (BitVec.ofNat 64 18446744073709551359)) (BitVec.ofNat 64 18446744073709551360)) = true
    rw [c16_eval, hbp]
    exact decide_eq_true ⟨hps0, hps256⟩
  simp only [hc, ↓reduceIte] at hpc1
  have hl24 : ((frameEnv m0 s.data 160 []).load 0 24 8).toNat = rw := by
    rw [load_ofMachine (o := 24) rfl hf24, UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have rk : ∀ x ∈ [Reg64.rdi, .rbp], reg s1.data x = reg s.data x := fun x hx ↦
    hm1.regs x _ (hk16 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> simp))
  exact .done _ (.inr ⟨hpc1.trans (hp.label NativeRustcVmX64.Vm.PhaseM.label_11_at), hb1, hmod, hql, hc0, hcnt, hqlt, hhl,
    hlwl, hrwl, hps0, hps256, by rw [hd1]; exact hf40, by rw [hd1]; exact hf32,
    by rw [hd1]; exact hf16, by rw [hd1]; exact hf24, by rw [rk .rbp (by simp)]; exact hbp,
    by rw [rk .rdi (by simp)]; exact hdi,
    by rw [show reg s1.data .rbx = reg s.data .rbx from hm1.regs .rbx (.reg .rbx)
      (by decide +kernel)]; exact hbx,
    by rw [show reg s1.data .r15 = _ from hm1.regs .r15 _ h15_16]; exact hl24,
    by rw [hd1]; exact hqW, by rw [hd1]; exact hpW, by rw [hd1]; exact hrd⟩)

end

end NativeRustcVmX64.Wire.PhaseM
