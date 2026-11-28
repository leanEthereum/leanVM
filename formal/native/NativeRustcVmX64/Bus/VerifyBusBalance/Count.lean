module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Keep
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names

/-!
# `verify_bus_balance`'s count side (x86-64)

From `b50` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b50Offset`, RSP at the frame's offset `8` after the pull side's `accumulate_side`):
`b50` checks the pull side's tag; `b51` keeps its total in RBX, R15 and calls `accumulate_side`
on the count side (no fingerprints, the weights `&[ONE]`, `β = 0`); `b52` checks its tag; then
the tail (`count_spec`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section
variable [Labels]

/-- `&[ONE]` read as a slice. -/
theorem one_slice {m : MachineData}
    (h : NativeRustcVm.BytesAt m.dmem (rodataAddr .one) NativeRustcVm.Data.Item.one.bytes) :
    slice m (rodataAddr .one) 1#64 = #[1] := by
  have h' : NativeRustcVm.EWsAt m.dmem (rodataAddr .one) [⟨1, 0⟩] := h
  unfold slice
  have := NativeRustcVm.ewsOf_of_ewsAt h'
  rw [show (1#64 : BitVec 64).toNat = [(⟨1, 0⟩ : EW)].length from rfl, this]
  rfl

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The count side** (`b50`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b50Offset`). -/
theorem count_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {d : MachineData} {w pt tv mem : Array EW} {beta mf bf share : EW} {bp : Array EW}
    {s' : TState} (fr : St m0 8 d)
    (hrun : (verifyBusBalance L).run s0 = some (resultOf L w beta pt tv mem mf bf share bp, s'))
    (hopt : OptEWAt d.dmem (loc m0 192) (some (acc1 L w beta pt tv mem mf bf share).2))
    (hF : FormsAt d.dmem (reg m0 .r8) (acc1 L w beta pt tv mem mf bf share).1)
    (hfits : FitsUpTo (acc1 L w beta pt tv mem mf bf share).1 2)
    (hcount : BusLayoutWAt d.dmem (loc m0 4584) (countL L)) (tm : TailMem m0 pt d.dmem)
    (h312 : NativeRustcVm.WordAt d.dmem (loc m0 312) (tv.getD 2 0).c0)
    (h304 : NativeRustcVm.WordAt d.dmem (loc m0 304) (tv.getD 2 0).c1)
    (x14 : reg d .r14 = reg m0 .rsi)
    (x13 : reg d .r13 = (acc0 L w beta pt tv mem share).2.c0.toBitVec)
    (xbp : reg d .rbp = (acc0 L w beta pt tv mem share).2.c1.toBitVec)
    (hts : TStateAt d.dmem (reg m0 .rdi) a s')
    (hcl : ClaimsWAt d.dmem (reg m0 .r9) (claimsOf L pt mem mf bf)) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b50Offset)⟩ := by
  have hS := pre_stack h
  have hbus := pre_bus h
  have psz := tm.psz
  -- `b50`: the pull side's tag.
  have hwf0 := wf0 h fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_then (infix_of b50_in_code (by simp [b50]) hp) exit_b50 hwf0 nofun (match_fS fr)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hk1⟩ := ok_b50
  have fr1 := (fr.block0 hS N_ge hwf0 hm1 hmid1 slots_le (by simp [hmem1])).1
  have hd1 : st1.data.dmem = d.dmem := hm1.dmem_eq hwf0 hmem1
  simp only [PcOk, tag8_false hopt.1, Bool.false_eq_true, ↓reduceIte] at hpc1
  have k1 : ∀ r ∈ cs, reg st1.data r = reg d r := fun r hr ↦ hk1.reg hm1 hr
  -- `b51`: the count side's `accumulate_side`.
  have hwf2 := wf0 h fr1.frame.kept (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b51Offset + b51.length)).toBitVec)
  refine exec_at (infix_of b51_in_code (by simp [b51]) hp) exit_b51 hwf2 (fun _ _ ↦ rfl)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyBusBalance.b50_next)) (match_fS fr1) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hw2, wr2, hrdi, hrsi, hrdx, hrcx, hr8, hr9, hrbx, hr15, hk2⟩ := ok_b51
  have fr2 : St m0 0 st2.data := St.blk fr1 hS hwf2 hm2 hmid2 fun q hq ↦ wr0 hS hw2 (by omega) hq
  have hin2 := writesIn_of_mid hmid2
  have hs2 := blk_same hS hwf2 hm2 hw2 (by omega)
  have hsp2 : rspOf st2.data = loc m0 0 := fr2.frame.sp
  have hd : ∀ {j n : Nat} {x : UInt64}, 96 ≤ j → j + n ≤ 5520 → 8 ≤ n →
      NativeRustcVm.WordAt d.dmem (loc m0 j) x → NativeRustcVm.WordAt st2.data.dmem (loc m0 j) x :=
    fun h1 h2 h3 hw ↦ NativeRustcVm.Layout.WordAt.of_same (hd1 ▸ hw)
      (keepB hwf2 hm2 hin2 (j := _) (n := 8) (by omega) (miss0 hw2 (by omega))) le_rfl
  have ld : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt d.dmem (loc m0 o) x →
      (frameEnv m0 st1.data 5520 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b51Offset + b51.length)).toBitVec).load 0 o 8 = x.toBitVec :=
    fun hw ↦ load_loc (hd1 ▸ hw)
  have sa : ∀ {i : Nat} {v : Sym}, 8 + 8 * i + 8 ≤ 5520 →
      (∀ t < 8, findWrite 0 (8 + 8 * i + t) (after b51 (fS 104)).mem = some (v, t)) →
      stackArg st2.data i = v.eval (frameEnv m0 st1.data 5520 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b51Offset + b51.length)).toBitVec) := fun hle hw ↦
    (stackArg_loc hsp2 (wordAt_write hm2 (r := 0) rfl (by omega) hw)).trans rfl
  have e0 : stackArg st2.data 0 = loc m0 4584 :=
    (sa (i := 0) (by omega) (wr2.find (List.Mem.head _))).trans (eval_ptr0 4584)
  have e1 : stackArg st2.data 1 = 8#64 :=
    sa (i := 1) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.head _)))
  have e2 : stackArg st2.data 2 = 0#64 :=
    sa (i := 2) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have e3 : stackArg st2.data 3 = rodataAddr .one :=
    sa (i := 3) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.head _)))))
  have e4 : stackArg st2.data 4 = 1#64 :=
    sa (i := 4) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))))
  have e5 : stackArg st2.data 5 = 0#64 :=
    sa (i := 5) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
  have e6 : stackArg st2.data 6 = 0#64 :=
    sa (i := 6) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  have e7 : stackArg st2.data 7 = loc m0 1800 :=
    (sa (i := 7) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _)))))))))).trans (ld tm.w104)
  have e8 : stackArg st2.data 8 = pt.size.toUInt64.toBitVec :=
    (sa (i := 8) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.head _))))))))))).trans (ld tm.w120)
  have e9 : stackArg st2.data 9 = (tv.getD 2 0).c0.toBitVec :=
    (sa (i := 9) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))))))))).trans (ld h312)
  have e10 : stackArg st2.data 10 = (tv.getD 2 0).c1.toBitVec :=
    (sa (i := 10) (by omega) (wr2.find (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))).trans (ld h304)
  have hnsz : pt.size.toUInt64.toBitVec.toNat = pt.size := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hle : 5520 - 0 + accumulateSideStack ≤ NN := le_acc
  have hR := cal_ro h fr2 (by omega) hle
  have tm2 : TailMem m0 pt st2.data.dmem := tm.of_keep (hd1 ▸ keepIv_block hwf2 hm2 hin2
    (W0.reg0 hw2) (by decide) (by decide))
  have hptv : slice st2.data (stackArg st2.data 7) (stackArg st2.data 8) = pt := by
    rw [e7, e8]
    unfold slice
    rw [hnsz]
    have := NativeRustcVm.ewsOf_of_ewsAt tm2.hpt
    rw [Array.length_toList] at this
    rw [this]
  obtain ⟨rows, -, -, -, hbb⟩ := (pre_lay h).rows
  have hlen : (sideBlocks 2).length = 45 := by decide +kernel
  have hcount2 : BusLayoutWAt st2.data.dmem (loc m0 4584) (countL L) :=
    BusLayoutWAt.of_same hcount (hd1 ▸ keepB hwf2 hm2 hin2 (j := 4584) (n := 888) (by omega)
      (miss0 hw2 (by omega)))
  have hcs2 : (countL L).tables.size = (sideBlocks 2).length := by
    have e := sideOf_eq hbb 2
    rw [show sideOf L 2 = L.count from rfl] at e
    rw [busLayout_tables_size, ← e]
    simp
  have hbusF : ∀ {x : Mem 64}, NativeRustcVm.SameOutside d.dmem x (NativeRustcVm.InRange (fb m0) 5520) →
      Same d.dmem x (reg m0 .r8) formsBytes := fun hs ↦ Same.of_sameOutside hs fun j hj hq ↦ by
    have hfj : j < 106704 := hj
    have := bus_notLoc h (o := j) (n := 1) (j := 0) (l := 5520) (by omega) (by omega)
      (q := off (reg m0 .r8) j) (NativeRustcVm.inRange_self (by omega))
    rw [show loc m0 0 = fb m0 from off_zero _] at this
    exact this hq
  have hF2 : FormsAt st2.data.dmem (reg m0 .r8) (acc1 L w beta pt tv mem mf bf share).1 :=
    FormsAt.of_same hF (hbusF (hd1 ▸ hs2))
  have x0 : reg st2.data .rdi = loc m0 624 := (hm2.regs .rdi _ hrdi).trans (eval_ptr0 624)
  have x1 : reg st2.data .rsi = reg m0 .r8 := (hm2.regs .rsi _ hrsi).trans (ld tm.w112)
  have x5 : reg st2.data .r9 = reg m0 .rsi :=
    (hm2.regs .r9 _ hr9).trans ((k1 .r14 (by simp [cs])).trans x14)
  have hone := hR .one
  have hone16 : (NativeRustcVm.Data.Item.one).bytes.length = 16 := by decide
  rw [hone16] at hone
  have hbr := (pre_busR h) .one
  rw [hone16] at hbr
  have hw3 : SliceOk st2.data (stackArg st2.data 3) (stackArg st2.data 4) accumulateSideStack ∧
      NativeRustcVm.Apart (reg m0 .r8) formsBytes (stackArg st2.data 3)
        (16 * (stackArg st2.data 4).toNat) := by
    rw [e3, e4]
    have hfb : formsBytes ≤ busBytes := formsBytes_le
    exact ⟨⟨⟨hone.1.mapped, hone.2.1⟩, hone.2.2⟩,
      NativeRustcVm.Apart.mono hbr (Nat.le_refl _) (by omega) (Nat.le_refl _) (Nat.le_refl _)⟩
  simp only [PcOk] at hpc2
  refine accCall h hacc fr2 hpc2 (side := 2) (by omega) (it := .countBlocks) rfl (by simp)
    (o := 624) (ol := 4584) (by omega) (by omega) (by omega) (by omega) hcount2 hcs2 hF2 hfits
    x0 x1 (by rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hrdx]; rfl)
    (by rw [show reg st2.data .rcx = _ from hm2.regs .rcx _ hrcx]; rfl)
    (by rw [show reg st2.data .r8 = _ from hm2.regs .r8 _ hr8, hlen]; rfl) x5 e0
    (fun hn ↦ absurd hn (by rw [e2]; decide)) hw3
    e7 (by rw [e8, hnsz]; exact psz) (by rw [e2])
    ((congrArg₂ (slice st2.data) e3 e4).trans (one_slice hone.1)) (by rw [e5, e6]) hptv
    (by rw [e9, e10]) (by
      intro l hl
      constructor
      · intro hn
        rw [e2] at hn
        change 0 < 0 at hn
        omega
      · rw [e3, e4]
        have hg := ((pre_got h).1 l hl).2.2.2
          (rodataAddr .one, NativeRustcVm.Data.Item.one.bytes.length) (by simp)
        simpa only [hone16, BitVec.toNat_ofNat] using hg)
    fun m3 fr3 hopt3 hF3 hfits3 hs3 hk3 hcs3 ↦ ?_
  -- `b52`: the count side's tag.
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b51Offset + b51.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b52Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b51_next]]
  have hwf4 := wf0 h fr3.frame.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_then (infix_of b52_in_code (by simp [b52]) hp) exit_b52 hwf4 nofun (match_fS fr3)
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, hk4⟩ := ok_b52
  have fr4 := (fr3.block0 hS N_ge hwf4 hm4 hmid4 slots_le (by simp [hmem4])).1
  have hd4 : st4.data.dmem = m3.dmem := hm4.dmem_eq hwf4 hmem4
  simp only [PcOk, tag8_false hopt3.1, Bool.false_eq_true, ↓reduceIte] at hpc4
  have tm4 : TailMem m0 pt st4.data.dmem := by
    rw [hd4]
    refine tm2.of_keep (keepIv_call hS hsp2 (by omega) hle hs3 (by decide) (by decide) fun j hj hq ↦ ?_)
    obtain ⟨p, hp', h1, h2⟩ := hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hq with hq | hq
    · exact loc_notIn hS (j := j) (by rcases hp' with rfl | rfl <;> simp at h2 <;> omega) (by omega)
        (by rcases hp' with rfl | rfl <;> simp at h1 h2 <;> omega) hq
    · exact bus_notLoc h (o := 0) (n := formsBytes) (by decide) (j := j) (l := 1)
        (by rcases hp' with rfl | rfl <;> simp at h2 <;> omega) (by rw [off_zero]; exact hq)
        (loc_inR hS (by omega) (by omega) (by rcases hp' with rfl | rfl <;> simp at h2 <;> omega))
  have k4 : ∀ r ∈ cs, reg st4.data r = reg m3 r := fun r hr ↦ hk4.reg hm4 hr
  have r13 : reg st4.data .r13 = reg d .r13 :=
    (k4 .r13 (by simp [cs])).trans ((hcs3 .r13 rfl).trans ((hk2.reg hm2 (by simp)).trans
      (k1 .r13 (by simp [cs]))))
  have rbp : reg st4.data .rbp = reg d .rbp :=
    (k4 .rbp (by simp [cs])).trans ((hcs3 .rbp rfl).trans ((hk2.reg hm2 (by simp)).trans
      (k1 .rbp (by simp [cs]))))
  obtain ⟨-, ht1⟩ := hopt
  rw [ewAt_iff, off_off] at ht1
  have rbx : reg st4.data .rbx = (acc1 L w beta pt tv mem mf bf share).2.c0.toBitVec :=
    (k4 .rbx (by simp [cs])).trans ((hcs3 .rbx rfl).trans ((hm2.regs .rbx _ hrbx).trans
      (ld ht1.1)))
  have r15 : reg st4.data .r15 = (acc1 L w beta pt tv mem mf bf share).2.c1.toBitVec :=
    (k4 .r15 (by simp [cs])).trans ((hcs3 .r15 rfl).trans ((hm2.regs .r15 _ hr15).trans
      (ld (by rw [off_off] at ht1; exact ht1.2))))
  obtain ⟨-, ht2⟩ := hopt3
  rw [ewAt_iff, off_off] at ht2
  have hall : NativeRustcVm.SameOutside d.dmem st4.data.dmem (fun q ↦
      NativeRustcVm.InRange (fb m0) 5520 q ∨
        (NativeRustcVm.InRange (stackBelow st2.data accumulateSideStack) accumulateSideStack q ∨
          (NativeRustcVm.InRange (loc m0 624) 24 q ∨
            NativeRustcVm.InRange (reg m0 .r8) formsBytes q))) := by
    rw [hd4, ← hd1]
    exact hs2.trans hs3
  have hkept : Kept d.dmem st4.data.dmem := by
    rw [hd4, ← hd1]; exact kept_trans (hm2.kept hwf2) hk3
  have hX : ∀ q, (NativeRustcVm.InRange (fb m0) 5520 q ∨
      (NativeRustcVm.InRange (stackBelow st2.data accumulateSideStack) accumulateSideStack q ∨
        (NativeRustcVm.InRange (loc m0 624) 24 q ∨
          NativeRustcVm.InRange (reg m0 .r8) formsBytes q))) →
      NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨
        NativeRustcVm.InRange (reg m0 .r8) busBytes q := by
    rintro q (hq | hq | hq | hq)
    · exact .inl (frame_stack hS hq)
    · exact .inl (callee_stack hS hsp2 (by omega) hle hq)
    · exact .inl (loc_stack hS (by omega) hq)
    · exact .inr (inRange_mono hq formsBytes_le)
  obtain ⟨hts4, hcl4⟩ := tc_keep h hkept hall hX hts hcl
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b52Offset + b52.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b53Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b52_next]] at hpc4
  refine at_pc hpc4 (tail_spec hp h hext fr4 hrun rfl tm4.w112 tm4.w104 tm4.w120 psz tm4.hpt
    (r13.trans x13) (rbp.trans xbp) rbx r15 (by rw [hd4]; exact ht2.1)
    (by rw [hd4]; rw [off_off] at ht2; exact ht2.2) (hd4 ▸ hF3) hts4 hcl4)

end

end NativeRustcVmX64.Bus.VerifyBusBalance
