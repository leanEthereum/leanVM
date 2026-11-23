module

public import NativeRustcVmX64.Layout.PlacementsOf.Loop1
public import NativeRustcVmX64.Arrays.Common

/-!
# `placements_of` on x86-64: a turn of the first loop (`b4` to `b8`)

From the head `.L2` (`I1 m0 c c`): `b5` tests the column's slot byte, `b6` its output byte (a
column with a slot or an output lane is skipped, `I1.skip`), `b7` room, `b8` appends the column
and its log-size (`append`); `.L1` (`b4`) moves on (`l1`). `loop1` runs the loop to `.L6`.
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PlacementsOf NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

public section

section
variable [Labels] {m0 : MachineData}

/-- A byte compared, as the executor states it. -/
theorem eq8s (env : Env) {a : Sym} {b v : Nat} (hx : (a.eval env).toNat = b) (hb : b < 256) :
    (SBool.cmp .eq .W8 a (.lit v)).eval env = decide (b = v % 256) := by
  show CmpOp.apply .eq .W8 (a.eval env) (BitVec.ofNat 64 v) = _
  exact eq8 hx hb

/-- **A byte of a read-only array** at RAX: the environment of `tabS r`. -/
theorem tab_run (hF : Facts m0) {d : MachineData} (hb : B m0 8 d) (t : NativeRustcVm.Data.Item)
    (hlen : t.bytes.length = 158) {r : Reg64} (hr : reg d r = rodataAddr t) {c : Nat}
    (hc : c < 158) (hrax : (reg d .rax).toNat = c) :
    (Env.ofMachine d [(rodataAddr t, 158)] (fun _ ↦ 0) 0).WF ∧
      Match (Env.ofMachine d [(rodataAddr t, 158)] (fun _ ↦ 0) 0) (tabS r) d ∧
      ((Sym.loadx 0 0 (.reg .rax) 1).eval (Env.ofMachine d [(rodataAddr t, 158)] (fun _ ↦ 0) 0)).toNat
        = (t.bytes[c]'(by omega)).toNat := by
  have hnw := hF.rod.noWrap t
  rw [hlen] at hnw
  refine ⟨Env.wf_of ⟨⟨fun i hi ↦ by
      show (d.dmem.get? (rodataAddr t + BitVec.ofNat 64 i)).isSome = true
      rw [rod_get hF hb t (by omega)]; rfl, hnw⟩, trivial⟩
    (List.pairwise_singleton _ _), match_ofMachine ⟨rfl, trivial⟩ trivial trivial
    ⟨by show (reg d .rax).toNat < 158; omega, trivial⟩
    ⟨by
      show reg d r = rodataAddr t + BitVec.ofInt 64 0
      rw [ofInt_zero64, BitVec.add_zero, hr], trivial⟩, ?_⟩
  show ((Env.ofMachine d [(rodataAddr t, 158)] (fun _ ↦ 0) 0).load 0 (0 + (reg d .rax).toNat) 1).toNat
    = _
  rw [hrax, Nat.zero_add]
  exact load_byte (rod_get hF hb t (by omega))

end

variable [Host] {k : Nat} {m0 : MachineData}

/-- **`b8`**: column `c` and its log-size appended. -/
theorem append (hp : Placed code k) (hF : Facts m0) {c : Nat} (hc : c < 158)
    (hblk : isBlockF c = true) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b8Offset))
    (hI : I1 m0 c c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b4Offset) ∧ I1 m0 (c + 1) c s.data)
      st := by
  have hb := hI.b
  have hrsp := hF.rsp
  set j := (below c).length with hj
  have hj94 : j ≤ 94 := below_length_le hI.le
  have hpt := hF.part (o := 1280 + 8 * j) (l := 1272) hb (by omega)
  have hkr : NativeRustcVm.Mapped m0.dmem (kk m0 + BitVec.ofNat 64 (8 * c)) 8 :=
    mapped_off (N := 1264) hF.kr.1 (by omega)
  have hkn : (kk m0).toNat + 1264 ≤ 2 ^ 64 := hF.kr.2
  have hknw : NativeRustcVm.NoWrap (kk m0 + BitVec.ofNat 64 (8 * c)) 8 := by
    unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega
  have hko : NativeRustcVm.Apart (off (fb m0) (1280 + 8 * j)) 1272
      (kk m0 + BitVec.ofNat 64 (8 * c)) 8 := by
    have := hF.part_apart_off (o := 1280 + 8 * j) (l := 1272) (by omega) hF.ko
    unfold NativeRustcVm.Apart at this ⊢
    rw [kappasBytes_eq, hF.off_toNat (by omega)] at this
    rw [hF.off_toNat (by omega), toNat_off (by omega)]
    omega
  let env := Env.ofMachine st.data [(off (fb m0) (1280 + 8 * j), 1272),
    (kk m0 + BitVec.ofNat 64 (8 * c), 8)] (fun _ ↦ 0) 0
  have hwf : env.WF := Env.wf_of ⟨⟨hpt.1, hpt.2⟩, ⟨Mapped.keeps hkr hb.fr.kept, hknw⟩, trivial⟩
    (List.pairwise_pair.mpr hko)
  have hm : Match env colS st.data := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩ trivial trivial trivial ⟨?_, ?_, trivial⟩
    · show (idx .rsp .r13).eval env = _
      rw [idx_eval]
      show reg st.data .rsp + BitVec.ofNat 64 (8 * (reg st.data .r13).toNat) =
        off (fb m0) (1280 + 8 * j) + BitVec.ofInt 64 (-1272)
      rw [show reg st.data .rsp = _ from hb.fr.sp, hI.r13, add_m1272, off_sub _ (by omega)
        (by rw [hF.fb_toNat]; omega), off_add, show 1280 + 8 * j - 1272 = 8 + 8 * j by omega]
    · show (idx .r14 .rax).eval env = _
      rw [idx_eval]
      show reg st.data .r14 + BitVec.ofNat 64 (8 * (reg st.data .rax).toNat) =
        kk m0 + BitVec.ofNat 64 (8 * c) + BitVec.ofInt 64 0
      rw [hI.r14, hI.rax, ofInt_zero64, BitVec.add_zero]
  refine exec_at (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b8 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hok, hw0, hwa, hwb, h13, hK⟩ := ok_b8
  have hok' := hok
  simp only [AOk, Bool.and_eq_true] at hok'
  have hw1 : ∀ q, Written env (after b8 colS) q →
      ∃ x, (x < 8 ∨ 1264 ≤ x ∧ x < 1272) ∧ q = off (off (fb m0) (1280 + 8 * j)) x :=
    fun q h ↦ by
      obtain ⟨w, hw, b, sz, hb', x, hx1, hx2, rfl⟩ := written_off hwf h
      obtain ⟨hr0, hwo⟩ := hw0 w hw
      rw [hr0] at hb'
      simp only [env, Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      exact ⟨x, by omega, rfl⟩
  have hb1 : B m0 8 st1.data := hb.of_written hF.stack (by decide) hwf hm1 hok (L := 5072)
    (by decide) slots_ge slots_le fun q h ↦ by
      obtain ⟨x, hx, rfl⟩ := hw1 q h
      have hx' : x < 1272 := by omega
      rw [off_off]
      exact Or.inr (hF.part_low (o := 1280 + 8 * j + x) (l := 1) (by omega)
        (inRange_off_self (b := off (fb m0) (1280 + 8 * j + x)) (N := 1) (j := 0) (by omega)
          (by omega) |> fun h ↦ by rwa [off_zero] at h))
  -- the new words
  have new1 : WordAt st1.data.dmem (off (fb m0) (1280 + 8 * j)) c.toUInt64 := by
    have := wordAt_write hm1 (r := 0) (o := 0) rfl (by omega) (fun t ht ↦ by simpa using hwa t ht)
    rwa [off_zero, u64_of (show ((Sym.reg .rax).eval env).toNat = c from hI.rax)] at this
  have new2 : WordAt st1.data.dmem (off (fb m0) (2544 + 8 * j)) (κ m0 c).toUInt64 := by
    have := wordAt_write hm1 (r := 0) (o := 1264) rfl (by omega) hwb
    rw [off_off, show 1280 + 8 * j + 1264 = 2544 + 8 * j by omega] at this
    convert this using 1
    show (κ m0 c).toUInt64 = UInt64.ofBitVec (env.load 1 0 8)
    rw [Arrays.load8_eq]
    show _ = UInt64.ofBitVec (wordOf st.data.dmem (kk m0 + BitVec.ofNat 64 (8 * c) +
      BitVec.ofNat 64 0)).toBitVec
    rw [NativeRustcVm.addr_add_zero, UInt64.ofBitVec_toBitVec, kap_same hF hb hc, κ_eq m0 hc,
      toUInt64_toNat']
  -- the old words, kept
  have keep : ∀ {o : Nat} {v : UInt64}, (o + 8 ≤ 1280 + 8 * j ∨
      (2544 ≤ o ∧ o + 8 ≤ 2544 + 8 * j)) → o < 5072 →
      WordAt st.data.dmem (off (fb m0) o) v → WordAt st1.data.dmem (off (fb m0) o) v := by
    intro o v ho ho' h
    refine bytesAt_congr h fun i hi ↦ ?_
    have hi8 : i < 8 := by simpa [NativeRustcVm.length_wordBytes] using hi
    rw [off_add]
    refine hm1.get?_mem0 hwf fun hw ↦ ?_
    obtain ⟨x, hx, he⟩ := hw1 _ hw
    rw [off_off] at he
    have := off_inj (b := fb m0) (N := 5128) hF.fnw (by omega) (by omega) he
    omega
  have hbl : below (c + 1) = below c ++ [c] := by rw [below_succ, hblk]; rfl
  have hK' := fun r (hr : r ∈ [Reg64.rax, .rbx, .rbp, .r12, .r14, .r15]) ↦ kreg hm1 hK hr
  simp only [PcOk] at hpc1
  refine .done _ ⟨hpc1.trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_1_at), hb1, by omega, by omega,
    by rw [hK' .rax (by simp)]; exact hI.rax, by rw [hK' .r15 (by simp)]; exact hI.r15, ?_,
    (hK' .rbp (by simp)).trans hI.rbp, (hK' .r12 (by simp)).trans hI.r12,
    (hK' .r14 (by simp)).trans hI.r14, (hK' .rbx (by simp)).trans hI.rbx,
    fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · show (st1.data.regs.get64 .r13).toNat = _
    rw [hm1.regs .r13 _ h13, hbl, List.length_append, ← hj]
    show (BinOp.apply .add .W64 (reg st.data .r13) (BitVec.ofNat 64 1)).toNat = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, hI.r13, BitVec.toNat_ofNat]
    simp only [List.length_singleton]
    omega
  · simp only [hbl, List.length_append, List.length_singleton] at hq
    rcases Nat.lt_or_ge q j with hq' | hq'
    · rw [show (below (c + 1))[q] = (below c)[q] by
        simp only [hbl]; exact List.getElem_append_left hq']
      exact keep (.inl (by omega)) (by omega) (hI.cols q hq')
    · obtain rfl : q = j := by omega
      rw [show (below (c + 1))[j] = c by
        simp only [hbl, hj]; exact List.getElem_concat_length rfl _]
      exact new1
  · simp only [hbl, List.length_append, List.length_singleton] at hq
    rcases Nat.lt_or_ge q j with hq' | hq'
    · rw [show (below (c + 1))[q] = (below c)[q] by
        simp only [hbl]; exact List.getElem_append_left hq']
      exact keep (.inr ⟨by omega, by omega⟩) (by omega) (hI.sizes q hq')
    · obtain rfl : q = j := by omega
      rw [show (below (c + 1))[j] = c by
        simp only [hbl, hj]; exact List.getElem_concat_length rfl _]
      exact new2

/-- **A turn** from `.L2`: column `c` tested, appended if stacked; at `.L1`. -/
theorem turn1 (hp : Placed code k) (hF : Facts m0) {c : Nat} (hc : c < 158) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b5Offset)) (hI : I1 m0 c c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b4Offset) ∧ I1 m0 (c + 1) c s.data)
      st := by
  -- `b5`: the slot byte
  obtain ⟨hwf5, hm5, hv5⟩ := tab_run hF hI.b .keccakSlot length_slot hI.rbp hc hI.rax
  obtain ⟨hok5, hmem5, hK5⟩ := ok_b5
  refine stepR (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b5 nofun hpc hI.b hwf5 hm5
    hok5 hmem5 fun st1 hm1 hpc1 hb1 hd1 ↦ ?_
  have hI1 : I1 m0 c c st1.data := hI.of hb1 hd1 fun r hr ↦ kreg hm1 hK5 hr
  rw [slot_get hc] at hv5
  simp only [PcOk] at hpc1
  obtain ⟨hy, hno⟩ := pc_of (P := ¬ (NativeRustcVm.Data.slotByte (slotF c)).toNat = 255) hpc1 (by
    rw [SBool.eval, eq8s _ hv5 (UInt8.toNat_lt _), decide_not])
  by_cases hs : slotF c = none
  swap
  · refine .done _ ⟨(hy (by rw [slotByte_255]; exact hs)).trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_1_at),
      hI1.skip hc ?_⟩
    rw [isBlockF_eq c hc]; simp [hs]
  -- `b6`: the output byte
  obtain ⟨hwf6, hm6, hv6⟩ := tab_run hF hb1 .keccakOutput length_out hI1.r12 hc hI1.rax
  obtain ⟨hok6, hmem6, hK6⟩ := ok_b6
  refine stepR (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b6 nofun
    (hno (by rw [slotByte_255]; exact not_not.mpr hs)) hb1 hwf6 hm6 hok6 hmem6
    fun st2 hm2 hpc2 hb2 hd2 ↦ ?_
  have hI2 : I1 m0 c c st2.data := hI1.of hb2 hd2 fun r hr ↦ kreg hm2 hK6 hr
  rw [out_get hc] at hv6
  have hvo : ((if outF c then (1 : UInt8) else 0)).toNat < 256 := UInt8.toNat_lt _
  simp only [PcOk] at hpc2
  obtain ⟨hy2, hno2⟩ := pc_of (P := (if outF c then (1 : UInt8) else 0).toNat = 1) hpc2
    (eq8s _ hv6 hvo)
  by_cases ho : outF c = true
  · refine .done _ ⟨(hy2 (by simp [ho])).trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_1_at), hI2.skip hc ?_⟩
    rw [isBlockF_eq c hc]; simp [ho]
  have hblk : isBlockF c = true := by rw [isBlockF_eq c hc]; simp [hs, ho]
  -- `b7`: room
  obtain ⟨hok7, hmem7, hK7⟩ := ok_b7
  refine step0 hF (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b7 nofun
    (hno2 (by simp [ho])) hb2 hok7 hmem7 fun st3 hm3 hpc3 hb3 hd3 ↦ ?_
  have hI3 : I1 m0 c c st3.data := hI2.of hb3 hd3 fun r hr ↦ kreg hm3 hK7 hr
  have hn := below_length_le hI2.le
  simp only [PcOk] at hpc3
  obtain ⟨-, hno3⟩ := pc_of (P := ¬ (below c).length < 158) hpc3 (by
    rw [SBool.eval, ult_eval, decide_not]
    have e : ((Sym.reg .r13).eval (frameEnv m0 st2.data 5120 [] (fun _ ↦ 0) 0)).toNat =
      (below c).length := hI2.r13
    rw [e]; rfl)
  exact append hp hF hc hblk (hno3 (by omega)) hI3

omit [Host] in
/-- `x - 8` as `x + (2 ^ 64 - 8)`. -/
theorem addM8_eval {x : BitVec 64} (h : 8 ≤ x.toNat) :
    (BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551608) x).toNat = x.toNat - 8 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add]
  rw [show (BitVec.ofNat 64 18446744073709551608).toNat = 18446744073709551608 from rfl]
  have := x.isLt
  omega

/-- **`.L1`** (`b4`): on to the next column, or out of the loop. -/
theorem l1 (hp : Placed code k) (hF : Facts m0) {c : Nat} (hc : c < 158) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b4Offset)) (hI : I1 m0 (c + 1) c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (c + 1 < 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b5Offset) ∧
      I1 m0 (c + 1) (c + 1) s.data) ∨ (c + 1 = 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b9Offset) ∧
      I1 m0 158 158 s.data)) st := by
  obtain ⟨hok, hmem, hax, h15, hK⟩ := ok_b4
  refine step0 hF (b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b4 nofun hpc hI.b hok hmem
    fun st1 hm1 hpc1 hb1 hd1 ↦ ?_
  have hK' := fun r (hr : r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14]) ↦ kreg hm1 hK hr
  have v15 : ((Sym.bin .add .W64 (.lit 18446744073709551608) (.reg .r15)).eval
      (frameEnv m0 st.data 5120 [] (fun _ ↦ 0) 0)).toNat = 1264 - 8 * (c + 1) := by
    show (BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551608) (reg st.data .r15)).toNat = _
    rw [addM8_eval (by rw [hI.r15]; omega), hI.r15]; omega
  have hI1 : I1 m0 (c + 1) (c + 1) st1.data :=
    ⟨hb1, hI.le, le_rfl, by
      show (st1.data.regs.get64 .rax).toNat = _
      rw [hm1.regs .rax _ hax]
      show (BinOp.apply .add .W64 (reg st.data .rax) (BitVec.ofNat 64 1)).toNat = _
      simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, hI.rax, BitVec.toNat_ofNat]
      omega, by
      show (st1.data.regs.get64 .r15).toNat = _
      rw [hm1.regs .r15 _ h15]; exact v15,
      by rw [hK' .r13 (by simp)]; exact hI.r13, (hK' .rbp (by simp)).trans hI.rbp,
      (hK' .r12 (by simp)).trans hI.r12, (hK' .r14 (by simp)).trans hI.r14,
      (hK' .rbx (by simp)).trans hI.rbx, by rw [hd1]; exact hI.cols, by rw [hd1]; exact hI.sizes⟩
  simp only [PcOk] at hpc1
  obtain ⟨hy, hno⟩ := pc_of (P := 1264 - 8 * (c + 1) = 0) hpc1 (by
    rw [eq_eval, v15]; rfl)
  by_cases hl : c + 1 = 158
  · refine .done _ (.inr ⟨hl, (hy (by omega)).trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_6_at), ?_⟩)
    rw [← hl]; exact hI1
  · exact .done _ (.inl ⟨by omega, hno (by omega), hI1⟩)

/-- **The first loop**, from `.L2` at column `c` to `.L6` with every column seen. -/
theorem loop1 (hp : Placed code k) (hF : Facts m0) {c : Nat} (hc : c < 158) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b5Offset)) (hI : I1 m0 c c st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b9Offset) ∧ I1 m0 158 158 s.data) st := by
  refine Sym.loop (fun n s ↦ ∃ c, c < 158 ∧ 158 - c = n ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b5Offset) ∧
      I1 m0 c c s.data) (fun n s ⟨c, hc, hn, hpc, hI⟩ ↦ ?_) ⟨c, hc, rfl, hpc, hI⟩
  refine Eventually.bind (turn1 hp hF hc hpc hI) fun s ⟨hpc', hI'⟩ ↦ ?_
  refine Eventually.mono (l1 hp hF hc hpc' hI') fun s' h ↦ ?_
  rcases h with ⟨hlt, hpc'', hI''⟩ | ⟨-, hpc'', hI''⟩
  · exact Or.inr ⟨158 - (c + 1), by omega, c + 1, hlt, rfl, hpc'', hI''⟩
  · exact Or.inl ⟨hpc'', hI''⟩

end

end NativeRustcVmX64.Layout.PlacementsOf
