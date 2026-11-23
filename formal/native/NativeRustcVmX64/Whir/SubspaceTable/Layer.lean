module

public import NativeRustcVmX64.Whir.SubspaceTable.Init

/-!
# `subspace_table`'s layer initialization (x86-64)

`vturn`: eight layer words set (`b7`); `tturn`: one word (`b10`); `tail`: from `b8` or `b9` with
the first `μ - μ % 8` words set, the rest, to `Init μ` at `b11`.
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add eval_cmp_eq eval_not eval_test apart_symm not_inRange_of_apart
  written_region0)

public section

theorem initL_patch (i n : Nat) (_hin : i + n ≤ 31) :
    ∀ k (hk : k < (initL i).length), (initL (i + n))[k]'(by rw [initL_length] at hk ⊢; exact hk) =
      if i ≤ k ∧ k < i + n then pow2 k else (initL i)[k] := by
  intro k hk
  rw [initL_getElem, initL_getElem]
  rcases Nat.lt_or_ge k i with h1 | h1
  · have h2 : k < i + n := by omega
    have h3 : ¬ i ≤ k := by omega
    simp only [h1, h2, h3, false_and, ↓reduceIte]
  · rcases Nat.lt_or_ge k (i + n) with h2 | h2
    · have h3 : ¬ k < i := by omega
      simp only [h1, h2, and_self, ↓reduceIte]
    · have h3 : ¬ k < i := by omega
      have h4 : ¬ k < i + n := by omega
      simp only [h3, h4, and_false, ↓reduceIte]

theorem mul8' (a : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

variable [Host] {k : Nat}

/-- **Eight layer words** (`b7`). -/
theorem vturn (hp : Placed code k) {m0 : MachineData} (hpre : SubspaceTablePre m0) {d : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b7Offset)) (hI : VInv m0 d st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b7Offset) ∧ VInv m0 (d + 8) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b8Offset) ∧ Init m0 (muOf m0 / 8 * 8) s.data ∧
        reg s.data .r15 = fbOf m0 + BitVec.ofNat 64 (552 + 8 * (muOf m0 / 8 * 8)) ∧
        reg s.data .rdx = BitVec.ofNat 64 (muOf m0 / 8 * 8) ∧
        reg s.data .rax = BitVec.ofNat 64 (muOf m0 % 8))) st := by
  obtain ⟨hS, hout, _⟩ := hpre
  obtain ⟨hF, -, -, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hsl := slots_ok
  have hfr := hI.init.fr
  have hmu := hI.init.hmu
  have hlt := hI.hlt
  have hd8 := hI.hd
  have hrd : Readable st.data (fbOf m0 + BitVec.ofNat 64 (552 + 8 * d)) 64 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr.kept
  have hwf : (Env.ofMachine st.data [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * d), 64)]).WF :=
    Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * d), 64)]) vecS
      st.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show reg st.data .r15 = _ + BitVec.ofInt 64 0 by
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; exact hI.r15, trivial⟩
      trivial trivial trivial
  refine exec_at (hb7 hp) run_b7 hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨⟨hk1, hw1⟩, hv1⟩ := after_eq run_b7 ▸ b7_write
  have hfr1 : Fr m0 st1.data := hfr.of_write hm hm1 hwf rfl hk1 (r := 0) rfl le_rfl hw1
    (fun p h ↦ .inr (inRange_stack_of hS hF (L := 800) (by decide) (by omega) h))
    (slot_not_in hS hF (by omega) (by omega) hsl)
  have hso := same_region_le hm1 hwf (r := 0) rfl le_rfl hw1
  have hlen : (initL d).length = 31 := initL_length d
  have hlayer : WordsAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 552) (initL (d + 8)) := by
    refine wordsAt_patch (c := d) (n := 8) (f := pow2) hI.init.layer
      (NativeRustcVm.NoWrap.sub hfnw (by rw [hlen]; omega)) ?_ (fun i hi ↦ ?_) (by omega)
      (by rw [initL_length, initL_length]) (initL_patch d 8 (by omega))
    · rw [addr_add]; exact hso
    · have := wordAt_of_write hm1 (r := 0) (o := 8 * i) rfl (by omega) (hv1 i hi)
      rw [show (Sym.bin .shl .W64 (.lit (2 ^ (i + 1))) (.un .trunc .W32 (.reg .rdx))).eval
          (Env.ofMachine st.data [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * d), 64)]) =
            (pow2 (d + (i + 1) - 1)).toBitVec from
          shl_pow2 (by omega) (by omega) _ (by
            show (reg st.data .rdx).toNat = d
            rw [hI.rdx, toNat_ofNat_lt (by omega)]),
        UInt64.ofBitVec_toBitVec, addr_add, show d + (i + 1) - 1 = d + i by omega] at this
      rw [show 552 + 8 * d + 8 * i = 552 + 8 * (d + i) by omega] at this
      rw [addr_add]
      exact this
  have e1 : ∀ R ∈ [Reg64.rax, .rsi, .r14], reg st1.data R = reg st.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have hout1 : OutAt m0 st1.data := NativeRustcVm.BytesAt.of_sameOutside hI.init.out hso
    fun j hj ↦ by
      rw [NativeRustcVm.length_wordBytes] at hj
      rw [addr_add]
      unfold fbOf
      rw [inRange_fb_iff hS hF (by omega) (by omega) (by omega)]
      omega
  have hinit : Init m0 (d + 8) st1.data :=
    ⟨hfr1, hout1, hlayer, (e1 .r14 (by simp)).trans hI.init.r14, hmu⟩
  have hr15 : reg st1.data .r15 = fbOf m0 + BitVec.ofNat 64 (552 + 8 * (d + 8)) := by
    refine (hm1.regs .r15 _ rfl).trans ?_
    show fbOf m0 + BitVec.ofNat 64 (552 + 8 * d) + BitVec.ofInt 64 64 = _
    rw [show BitVec.ofInt 64 64 = BitVec.ofNat 64 64 from rfl, addr_add,
      show 552 + 8 * d + 64 = 552 + 8 * (d + 8) by omega]
  have hrdx : reg st1.data .rdx = BitVec.ofNat 64 (d + 8) := by
    refine (hm1.regs .rdx _ rfl).trans ?_
    rw [eval_add, eval_lit, eval_reg, Env.ofMachine_regs,
      show st.data.regs.get64 .rdx = _ from hI.rdx, ← BitVec.ofNat_add]
    congr 1
    omega
  simp only [PcOk] at hpc1
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg, Env.ofMachine_regs,
    Env.ofMachine_regs, show st.data.regs.get64 .rsi = _ from hI.rsi,
    show st.data.regs.get64 .rdx = _ from hI.rdx, ← BitVec.ofNat_add,
    ofNat_beq (by omega) (by omega)] at hpc1
  obtain ⟨hT, hF1⟩ := Arrays.pc_cond hpc1
  by_cases hlast : muOf m0 / 8 * 8 = 8 + d
  · refine .done _ (.inr ⟨hF1 (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; omega), ?_,
      by rw [hr15, hlast, Nat.add_comm 8 d], by rw [hrdx, hlast, Nat.add_comm 8 d],
      (e1 .rax (by simp)).trans hI.rax⟩)
    rw [hlast, Nat.add_comm 8 d]
    exact hinit
  · refine .done _ (.inl ⟨(hT (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans
      (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_7_at), hinit, by omega, by omega, hr15, hrdx,
      (e1 .rsi (by simp)).trans hI.rsi, (e1 .rax (by simp)).trans hI.rax⟩)

/-- **One layer word** (`b10`). -/
theorem tturn (hp : Placed code k) {m0 : MachineData} (hpre : SubspaceTablePre m0) {s : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b10Offset)) (hI : TInv m0 s st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b10Offset) ∧ TInv m0 (s + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b11Offset) ∧ Init m0 (muOf m0) s'.data)) st := by
  obtain ⟨hS, hout, _⟩ := hpre
  obtain ⟨hF, -, -, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hsl := slots_ok
  have hfr := hI.init.fr
  have hmu := hI.init.hmu
  have hs := hI.hs
  have hdiv : muOf m0 / 8 * 8 + muOf m0 % 8 = muOf m0 := Nat.div_add_mod' _ _
  have hrd : Readable st.data (fbOf m0 + BitVec.ofNat 64 (552 + 8 * (muOf m0 / 8 * 8 + s))) 8 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr.kept
  have hwf : (Env.ofMachine st.data
      [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * (muOf m0 / 8 * 8 + s)), 8)]).WF :=
    Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data
      [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * (muOf m0 / 8 * 8 + s)), 8)]) tailS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      show BinOp.apply .add .W64 (reg st.data .r15)
        (BinOp.apply .mul .W64 (reg st.data .rsi) (BitVec.ofNat 64 8)) = _ + BitVec.ofInt 64 0
      rw [add64, mul64, hI.r15, hI.rsi, mul8', addr_add,
        show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      congr 2
      omega, trivial⟩
  refine exec_at (hb10 hp) run_b10 hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨⟨hk1, hw1⟩, hv1⟩ := after_eq run_b10 ▸ b10_write
  have hfr1 : Fr m0 st1.data := hfr.of_write hm hm1 hwf rfl hk1 (r := 0) rfl le_rfl hw1
    (fun p h ↦ .inr (inRange_stack_of hS hF (L := 800) (by decide) (by omega) h))
    (slot_not_in hS hF (by omega) (by omega) hsl)
  have hso := same_region_le hm1 hwf (r := 0) rfl le_rfl hw1
  have hlen : (initL (muOf m0 / 8 * 8 + s)).length = 31 := initL_length _
  have hlayer : WordsAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 552)
      (initL (muOf m0 / 8 * 8 + s + 1)) := by
    refine wordsAt_patch (c := muOf m0 / 8 * 8 + s) (n := 1) (f := pow2) hI.init.layer
      (NativeRustcVm.NoWrap.sub hfnw (by rw [hlen]; omega)) ?_ (fun i hi ↦ ?_) (by omega)
      (by rw [initL_length, initL_length]) (initL_patch _ 1 (by omega))
    · rw [addr_add]; exact hso
    · have := wordAt_of_write hm1 (r := 0) (o := 0) rfl (by omega) hv1
      rw [show (Sym.bin .shl .W64 (.lit 2) (.un .trunc .W32
          (.bin .add .W64 (.reg .rdx) (.reg .rsi)))).eval (Env.ofMachine st.data
            [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * (muOf m0 / 8 * 8 + s)), 8)]) =
            (pow2 (muOf m0 / 8 * 8 + s + 1 - 1)).toBitVec from
          shl_pow2 (m := 1) (by omega) (by omega) _ (by
            show (BinOp.apply .add .W64 (reg st.data .rdx) (reg st.data .rsi)).toNat = _
            rw [add64, hI.rdx, hI.rsi, ← BitVec.ofNat_add, toNat_ofNat_lt (by omega)]),
        UInt64.ofBitVec_toBitVec, NativeRustcVm.addr_add_zero, show muOf m0 / 8 * 8 + s + 1 - 1 =
          muOf m0 / 8 * 8 + s by omega] at this
      rw [show i = 0 by omega, Nat.add_zero, addr_add]
      exact this
  have e1 : ∀ R ∈ [Reg64.rax, .rdx, .r14, .r15], reg st1.data R = reg st.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have hout1 : OutAt m0 st1.data := NativeRustcVm.BytesAt.of_sameOutside hI.init.out hso
    fun j hj ↦ by
      rw [NativeRustcVm.length_wordBytes] at hj
      rw [addr_add]
      unfold fbOf
      rw [inRange_fb_iff hS hF (by omega) (by omega) (by omega)]
      omega
  have hinit : Init m0 (muOf m0 / 8 * 8 + (s + 1)) st1.data :=
    ⟨hfr1, hout1, hlayer, (e1 .r14 (by simp)).trans hI.init.r14, hmu⟩
  simp only [PcOk] at hpc1
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg, Env.ofMachine_regs,
    Env.ofMachine_regs, show st.data.regs.get64 .rax = _ from hI.rax,
    show st.data.regs.get64 .rsi = _ from hI.rsi, ← BitVec.ofNat_add,
    ofNat_beq (by omega) (by omega)] at hpc1
  obtain ⟨hT, hF1⟩ := Arrays.pc_cond hpc1
  by_cases hlast : muOf m0 % 8 = s + 1
  · refine .done _ (.inr ⟨(hF1 (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans
      rfl, ?_⟩)
    exact (show muOf m0 / 8 * 8 + (s + 1) = muOf m0 by omega) ▸ hinit
  · refine .done _ (.inl ⟨(hT (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans
      (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_10_at), hinit, by omega, (e1 .r15 (by simp)).trans hI.r15,
      (e1 .rdx (by simp)).trans hI.rdx, ?_, (e1 .rax (by simp)).trans hI.rax⟩)
    refine (hm1.regs .rsi _ rfl).trans ?_
    rw [eval_add, eval_lit, eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .rsi = _ from
      hI.rsi, ← BitVec.ofNat_add]

end

end NativeRustcVmX64.Whir.SubspaceTable
