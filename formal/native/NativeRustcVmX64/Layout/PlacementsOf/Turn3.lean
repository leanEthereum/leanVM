module

public import NativeRustcVmX64.Layout.PlacementsOf.Store

/-!
# `placements_of` on x86-64: a turn of the third loop (`b20` to `b28`)

At `.L16` (`I3 m0 c`) `b22` loads `kappas[c]` and the column's slot byte. A column with a slot
(`b23`, `b24`): the `q_keccak` offset plus `slot << kappa`, at most `158 · 2^36 + 63 · 2^36`, no
carry. Without a slot (`b27`): an output lane (`b28`) has no placement; a stacked column (`b20`)
its offset from `offsets`. Each then `b21` stores the placement (`store`, `turn3`).
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PlacementsOf NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

public section

theorem shl_eval (x y : BitVec 64) {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b) (hb : b < 64)
    (hlt : a * 2 ^ b < 2 ^ 64) : (BinOp.apply .shl .W64 x y).toNat = a * 2 ^ b := by
  simp only [BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask]
  have hs : (low .W8 y).toNat &&& 63 = b := by
    rw [toNat_low, Nat.mod_eq_of_lt (by simp [Width.bits]; omega), hy]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)
  rw [hs, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx]
  exact Nat.mod_eq_of_lt hlt

theorem addC_eval [Labels] (env : Env) (a b : Sym) :
    (SBool.cmp .addC .W64 a b).eval env =
      decide (2 ^ 64 ≤ (a.eval env).toNat + (b.eval env).toNat) := by
  simp only [SBool.eval, CmpOp.apply, low_W64, BitVec.unsigned]
  have ha := (a.eval env).isLt
  have hb := (b.eval env).isLt
  have h2 : (a.eval env + b.eval env).toNat = ((a.eval env).toNat + (b.eval env).toNat) % 2 ^ 64 :=
    BitVec.toNat_add _ _
  rw [h2, Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq]
  constructor
  · intro h; omega
  · intro h; omega

theorem m_ax (r : Reg64) (h : r ∈ Reg64.rax :: cs) : r ∈ Reg64.rax :: Reg64.rcx :: cs := by
  rcases List.mem_cons.mp h with rfl | h
  · simp
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem m_axd (r : Reg64) (h : r ∈ Reg64.rax :: cs) :
    r ∈ Reg64.rax :: Reg64.rcx :: Reg64.rdx :: cs := by
  rcases List.mem_cons.mp h with rfl | h
  · simp
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

variable [Host] {k : Nat} {m0 : MachineData}

/-- **A turn of the third loop**: column `c`'s placement written. -/
theorem turn3 (hp : Placed code k) (hF : Facts m0) {c : Nat} (hc : c < 158) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b22Offset)) (hI : I3 m0 c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (c + 1 < 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b22Offset) ∧
      I3 m0 (c + 1) s.data) ∨ (c + 1 = 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b32Offset) ∧ I3 m0 158 s.data))
      st := by
  have hκ := hF.κ_le hc
  have hsum := hF.sumF_le' (keyF (κ m0) 4)
  -- `b22a`: `kappas[c]`
  have hkr : NativeRustcVm.Mapped m0.dmem (kk m0 + BitVec.ofNat 64 (8 * c)) 8 :=
    mapped_off (N := 1264) hF.kr.1 (by omega)
  have hkn : (kk m0).toNat + 1264 ≤ 2 ^ 64 := hF.kr.2
  have hwfk := Env.wf_of (env := Env.ofMachine st.data [(kk m0 + BitVec.ofNat 64 (8 * c), 8)]
    (fun _ ↦ 0) 0) ⟨⟨Mapped.keeps hkr hI.b.fr.kept, by
      show (kk m0 + BitVec.ofNat 64 (8 * c)).toNat + 8 ≤ 2 ^ 64
      rw [toNat_off (by omega)]; omega⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hmk : Match (Env.ofMachine st.data [(kk m0 + BitVec.ofNat 64 (8 * c), 8)] (fun _ ↦ 0) 0)
      kapS st.data := by
    refine match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨?_, trivial⟩
    beta_reduce
    rw [idx_eval]
    show reg st.data .r14 + BitVec.ofNat 64 (8 * (reg st.data .rax).toNat) =
      kk m0 + BitVec.ofNat 64 (8 * c) + BitVec.ofInt 64 0
    rw [hI.r14, hI.rax, ofInt_zero64, BitVec.add_zero]
  have hk22a : b22a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PlacementsOf.b22Offset) :=
    ((infix_take b22 2).trans b22_in_code (by simp [b22])).trans hp.1 (by simp [b22])
  have hk22b : b22b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.PlacementsOf.b22Offset + b22a.length) :=
    ((infix_drop b22 2).trans b22_in_code (by simp [b22])).trans hp.1 (by simp [b22])
  obtain ⟨hok1, hmem1, hcx1, hK1⟩ := ok_b22a
  refine stepR hk22a exit_b22a nofun hpc hI.b hwfk hmk hok1 hmem1 fun st1 hm1 hpc1 hb1 hd1 ↦ ?_
  have hI1 : I3 m0 c st1.data := hI.of hb1 hd1 fun r hr ↦ kreg hm1 hK1 hr
  have hcx : (reg st1.data .rcx).toNat = κ m0 c := by
    show (st1.data.regs.get64 .rcx).toNat = _
    rw [hm1.regs .rcx _ hcx1]
    show ((Env.ofMachine st.data [(kk m0 + BitVec.ofNat 64 (8 * c), 8)] (fun _ ↦ 0) 0).load 0 0
      8).toNat = _
    rw [Arrays.load8_eq]
    show (wordOf st.data.dmem (kk m0 + BitVec.ofNat 64 (8 * c) + BitVec.ofNat 64 0)).toNat = _
    rw [NativeRustcVm.addr_add_zero, kap_same hF hI.b hc, κ_eq m0 hc]
  -- `b22b`: the slot byte
  obtain ⟨hwfs, hms, hvs⟩ := tab_run hF hb1 .keccakSlot length_slot hI1.rbp hc hI1.rax
  rw [slot_get hc] at hvs
  obtain ⟨hok2, hmem2, hdx2, hK2⟩ := ok_b22b
  simp only [PcOk] at hpc1
  refine stepR hk22b exit_b22b nofun (hpc1.trans rfl) hb1 hwfs hms hok2 hmem2
    fun st2 hm2 hpc2 hb2 hd2 ↦ ?_
  have hI2 : I3 m0 c st2.data := hI1.of hb2 hd2 fun r hr ↦ kreg hm2 hK2 (m_ax r hr)
  have hcx2 : (reg st2.data .rcx).toNat = κ m0 c := by rw [kreg hm2 hK2 (by simp)]; exact hcx
  have hdx : (reg st2.data .rdx).toNat = (NativeRustcVm.Data.slotByte (slotF c)).toNat := by
    show (st2.data.regs.get64 .rdx).toNat = _
    rw [hm2.regs .rdx _ hdx2]
    show (UnOp.apply (.zext .W8) .W32 _).toNat = _
    simp only [UnOp.apply, toNat_ext, BitVec.toNat_setWidth, toNat_low, Width.bits]
    rw [hvs]
    have := (NativeRustcVm.Data.slotByte (slotF c)).toNat_lt
    omega
  simp only [PcOk] at hpc2
  obtain ⟨hy2, hno2⟩ := pc_of (P := (NativeRustcVm.Data.slotByte (slotF c)).toNat = 255) hpc2 (by
    rw [eq_eval]
    have e : ((Sym.un (.zext .W8) .W32 (.loadx 0 0 (.reg .rax) 1)).eval
      (Env.ofMachine st1.data [(rodataAddr .keccakSlot, 158)] (fun _ ↦ 0) 0)).toNat =
        (NativeRustcVm.Data.slotByte (slotF c)).toNat := by
      rw [← hdx]; exact (congrArg BitVec.toNat (hm2.regs .rdx _ hdx2)).symm
    rw [e]; rfl)
  cases hs : slotF c with
  | some s =>
    -- `b23`, `b24`: the slot's index
    have hs64 := slotF_lt hs
    have hsb : (NativeRustcVm.Data.slotByte (slotF c)).toNat = s := slotByte_toNat hs
    obtain ⟨hok3, hmem3, hK3⟩ := ok_b23
    refine step0 hF (b23_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b23 nofun
      (hno2 (by omega)) hb2 hok3 hmem3 fun st3 hm3 hpc3 hb3 hd3 ↦ ?_
    simp only [PcOk] at hpc3
    obtain ⟨-, hno3⟩ := pc_of (P := ¬ κ m0 c < 64) hpc3 (by
      rw [SBool.eval, ult_eval, decide_not]
      have e : ((Sym.reg .rcx).eval (frameEnv m0 st2.data 5120 [] (fun _ ↦ 0) 0)).toNat =
        κ m0 c := hcx2
      rw [e]; rfl)
    have hK3' := fun r (hr : r ∈ Reg64.rax :: .rcx :: .rdx :: cs) ↦ kreg hm3 hK3 hr
    obtain ⟨hok4, hmem4, hdx4, hsx4, hK4⟩ := ok_b24
    refine step0 hF (b24_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b24 nofun
      ((hno3 (by omega)).trans rfl) hb3 hok4 hmem4 fun st4 hm4 hpc4 hb4 hd4 ↦ ?_
    have hpow : s * 2 ^ κ m0 c ≤ 63 * 2 ^ 36 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) hκ)
    have hshl : ((Sym.bin .shl .W64 (.reg .rdx) (.reg .rcx)).eval
        (frameEnv m0 st3.data 5120 [] (fun _ ↦ 0) 0)).toNat = s * 2 ^ κ m0 c :=
      shl_eval _ _ (by
        show (reg st3.data .rdx).toNat = _
        rw [hK3' .rdx (by simp), hdx, hsb]) (by
        show (reg st3.data .rcx).toNat = _
        rw [hK3' .rcx (by simp), hcx2]) (by omega) (by omega)
    have h15 : ((Sym.reg .r15).eval (frameEnv m0 st3.data 5120 [] (fun _ ↦ 0) 0)).toNat =
        sumF (κ m0) (keyF (κ m0) 4) := by
      show (reg st3.data .r15).toNat = _
      rw [hK3' .r15 (by simp [cs])]; exact hI2.r15
    simp only [PcOk] at hpc4
    obtain ⟨hy4, -⟩ := pc_of (P := ¬ 2 ^ 64 ≤ sumF (κ m0) (keyF (κ m0) 4) + s * 2 ^ κ m0 c) hpc4
      (by rw [SBool.eval, addC_eval, h15, hshl, decide_not])
    have hI4 : I3 m0 c st4.data := (hI2.of hb3 hd3 fun r hr ↦ hK3' r (m_axd r hr)).of hb4 hd4
      fun r hr ↦ kreg hm4 hK4 (m_ax r hr)
    refine store hp hF ((hy4 (by omega)).trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_15_at)) ⟨hI4, hc, ?_, ?_, ?_⟩
    · rw [plF_slot hs]
      show (st4.data.regs.get64 .rsi).toNat = _
      rw [hm4.regs .rsi _ hsx4]; rfl
    · intro p hp'
      rw [plF_slot hs] at hp'
      cases hp'
      rw [kreg hm4 hK4 (by simp), hK3' .rcx (by simp)]; exact hcx2
    · intro p hp'
      rw [plF_slot hs] at hp'
      cases hp'
      show (st4.data.regs.get64 .rdx).toNat = _
      rw [hm4.regs .rdx _ hdx4]
      show (BinOp.apply .add .W64 _ _).toNat = _
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add]
      rw [h15, hshl]
      omega
  | none =>
    -- `b27`: the output byte
    obtain ⟨hwfo, hmo, hvo⟩ := tab_run hF hb2 .keccakOutput length_out hI2.r12 hc hI2.rax
    rw [out_get hc] at hvo
    obtain ⟨hok5, hmem5, hK5⟩ := ok_b27
    refine stepR (b27_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b27 nofun
      ((hy2 (by rw [hs]; rfl)).trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_19_at)) hb2 hwfo hmo hok5 hmem5
      fun st3 hm3 hpc3 hb3 hd3 ↦ ?_
    have hK3' := fun r (hr : r ∈ Reg64.rax :: .rcx :: cs) ↦ kreg hm3 hK5 hr
    have hI3 : I3 m0 c st3.data := hI2.of hb3 hd3 fun r hr ↦ hK3' r (m_ax r hr)
    simp only [PcOk] at hpc3
    obtain ⟨hy3, hno3⟩ := pc_of (P := (if outF c then (1 : UInt8) else 0).toNat = 0) hpc3
      (by rw [eq8s _ hvo (UInt8.toNat_lt _)])
    by_cases ho : outF c = true
    · -- `b28`: no placement
      obtain ⟨hok6, hmem6, hsx6, hcx6, hdx6, hK6⟩ := ok_b28
      refine step0 hF (b28_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b28 nofun
        (hno3 (by simp [ho])) hb3 hok6 hmem6 fun st4 hm4 hpc4 hb4 hd4 ↦
          store hp hF (hpc4.trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_15_at))
            ⟨hI3.of hb4 hd4 fun r hr ↦ kreg hm4 hK6 hr, hc, ?_, ?_, ?_⟩
      · rw [plF_out hs ho]
        show (st4.data.regs.get64 .rsi).toNat = _
        rw [hm4.regs .rsi _ hsx6]; rfl
      · intro p hp'; rw [plF_out hs ho] at hp'; cases hp'
      · intro p hp'; rw [plF_out hs ho] at hp'; cases hp'
    · -- `b20`: a stacked column, its offset
      have ho' : outF c = false := by simpa using ho
      have hblk : c ∈ blockList := mem_blockList hc (by rw [hs]; rfl) ho'
      have p0 := hF.part (o := 16 + 8 * c) (l := 8) hb3 (by omega)
      have hwf0 := Env.wf_of (env := Env.ofMachine st3.data [(off (fb m0) (16 + 8 * c), 8)]
        (fun _ ↦ 0) 0) ⟨⟨p0.1, p0.2⟩, trivial⟩ (List.pairwise_singleton _ _)
      have hm0 : Match (Env.ofMachine st3.data [(off (fb m0) (16 + 8 * c), 8)] (fun _ ↦ 0) 0)
          (rdS (-8)) st3.data := by
        refine match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨?_, trivial⟩
        beta_reduce
        rw [idx_eval]
        show reg st3.data .rsp + BitVec.ofNat 64 (8 * (reg st3.data .rax).toNat) =
          off (fb m0) (16 + 8 * c) + BitVec.ofInt 64 (-8)
        rw [show reg st3.data .rsp = _ from hb3.fr.sp, hI3.rax, add_m8, off_sub _ (by omega)
          (by rw [hF.fb_toNat]; have := hF.rsp; omega), off_add,
          show 16 + 8 * c - 8 = 8 + 8 * c by omega]
      obtain ⟨hok7, hmem7, hdx7, hsx7, hK7⟩ := ok_b20
      refine stepR (b20_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b20 nofun
        ((hy3 (by simp [ho'])).trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_14_at)) hb3 hwf0 hm0 hok7 hmem7
        fun st4 hm4 hpc4 hb4 hd4 ↦ ?_
      have hld : (Sym.load 0 0 8).eval (Env.ofMachine st3.data [(off (fb m0) (16 + 8 * c), 8)]
          (fun _ ↦ 0) 0) = (sumF (κ m0) (keyF (κ m0) c)).toUInt64.toBitVec :=
        load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hI3.offs c hblk)
      have hsum' := hF.sumF_le' (keyF (κ m0) c)
      refine store hp hF (hpc4.trans rfl)
        ⟨hI3.of hb4 hd4 fun r hr ↦ kreg hm4 hK7 (m_ax r hr), hc, ?_, ?_, ?_⟩
      · rw [plF_block hs ho']
        show (st4.data.regs.get64 .rsi).toNat = _
        rw [hm4.regs .rsi _ hsx7]; rfl
      · intro p hp'
        rw [plF_block hs ho'] at hp'
        cases hp'
        rw [kreg hm4 hK7 (by simp), hK3' .rcx (by simp)]; exact hcx2
      · intro p hp'
        rw [plF_block hs ho'] at hp'
        cases hp'
        show (st4.data.regs.get64 .rdx).toNat = _
        rw [hm4.regs .rdx _ hdx7, hld, UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]

/-- **The third loop**, from `.L16` at column `c` to `.L24` with every placement written. -/
theorem loop3 (hp : Placed code k) (hF : Facts m0) {c : Nat} (hc : c < 158) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b22Offset)) (hI : I3 m0 c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b32Offset) ∧ I3 m0 158 s.data) st :=
  Sym.loop (fun n s ↦ ∃ c, c < 158 ∧ 158 - c = n ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b22Offset) ∧ I3 m0 c s.data)
    (fun n s ⟨c, hc, hn, hpc, hI⟩ ↦ Eventually.mono (turn3 hp hF hc hpc hI) fun s' h ↦ by
      rcases h with ⟨hlt, hpc', hI'⟩ | ⟨-, hpc', hI'⟩
      · exact Or.inr ⟨158 - (c + 1), by omega, c + 1, hlt, rfl, hpc', hI'⟩
      · exact Or.inl ⟨hpc', hI'⟩)
    ⟨c, hc, rfl, hpc, hI⟩

end

end NativeRustcVmX64.Layout.PlacementsOf
