module

public import NativeRustcVmArm.Bus.GkrStep.Copy

/-!
# `gkr_step`'s end

`full_spec` (`.LGkrStep_21`, `b39`): every challenge copied, X0 = `1`, the epilogue. `rem_spec`
(`.LGkrStep_19`, `b37`, `b38`): the last challenge. `pairs_loop`: the pair loop. `copy_spec`
(`.LGkrStep_11`): the dispatch on `|xs|` (`b29`, `b30`, `b31`, `b34`, `b36`).
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- **Every challenge copied** (`b39`): X0 = `1`, the new state. -/
theorem full_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {xs y vs : Array EW}
    {s' : TState} {m : MachineData} (cp : AtCopy a s0 g0 m0 xs y vs s' m)
    (hall : NativeRustcVm.EWsAt m.dmem (pt m0 (56 + 16 * m0.regs.X1.toNat)) xs.toList) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b39Offset)⟩ := by
  have hS := pre_stack h
  refine Fr.runBlock hS N_ge rfl cp.fr (b39_in_code.trans hp.1 (by simp [b39])) run_b39 rfl rfl
    (by decide) (by decide) fun st hfr hd hm hpc ↦ ?_
  simp only [PcOk] at hpc
  refine at_pc (hpc.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b33Offset) NativeRustcVmArm.Vm.GkrStep.label_15_at)) (exit_spec hp h hfr ?_ fun g' s'' he ↦ ?_)
  · rw [cp.run]
    exact UInt64.toBitVec_inj.mp (reg_lit hm (r := .X0) (n := 1) rfl)
  · rw [cp.run, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [hd]
    have hsz := cp.size
    unfold busPointCap at hsz
    refine ⟨cp.ts, cp.vsize, cp.vals, ?_, ?_, ?_⟩
    · show (y ++ xs).toList.length ≤ busPointCap
      rw [Array.toList_append, List.length_append, Array.length_toList, Array.length_toList,
        cp.ysize]
      unfold busPointCap; omega
    · show NativeRustcVm.WordAt _ _ (y ++ xs).toList.length.toUInt64
      rw [Array.toList_append, List.length_append, Array.length_toList, Array.length_toList]
      exact cp.len
    · show NativeRustcVm.EWsAt _ (m0.regs.X3.toBitVec + BitVec.ofNat 64 48 + 8#64) _
      rw [Array.toList_append, NativeRustcVm.ewsAt_append,
        show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
        NativeRustcVm.addr_add_add, Array.length_toList, cp.ysize]
      exact ⟨cp.ys, hall⟩

/-- **The last challenge** (`b37`, `b38`), `c` copied, `|xs| = c + 1`. -/
theorem rem_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {xs y vs : Array EW}
    {s' : TState} {m : MachineData} {c : Nat} (cp : AtCopy a s0 g0 m0 xs y vs s' m)
    (hc : xs.size = c + 1) (h8 : (m.regs.getXReg .X8).toNat = c)
    (hpre : NativeRustcVm.EWsAt m.dmem (pt m0 (56 + 16 * m0.regs.X1.toNat)) (xs.toList.take c)) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b37Offset)⟩ := by
  have hS := pre_stack h
  have hsz := cp.size
  have hstep := pre_step h
  unfold busPointCap at hsz
  -- `b37`
  have hm := match_p h cp.fr cp.x19
  have hwf := wf_p h cp.fr
  refine exec_then (b37_in_code.trans hp.1 (by simp [b37])) run_b37 hwf hm fun st hm' hpc ↦ ?_
  have hfr := fr_p h cp.fr hm hm' rfl (by decide +kernel)
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf rfl
  have f19 : st.data.regs.getXReg .X19 = m0.regs.X3 :=
    UInt64.toBitVec_inj.mp ((hm'.regs .X19 _ rfl).trans (Transcript.eval_ptr rfl))
  have f20 : st.data.regs.getXReg .X20 = m0.regs.X1 := (reg_of hm' rfl).trans cp.x20
  have f23 : (st.data.regs.getXReg .X23).toNat = xs.size := by rw [reg_of hm' rfl]; exact cp.x23
  have f8 : (st.data.regs.getXReg .X8).toNat = 1 := by
    show (st.data.regs.getXReg .X8).toBitVec.toNat = 1
    rw [hm'.regs .X8 _ rfl]
    show (BinOp.apply .sub .W64 (m.regs.getXReg .X23).toBitVec (m.regs.getXReg .X8).toBitVec).toNat = 1
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub]
    rw [show (m.regs.getXReg .X23).toBitVec.toNat = (m.regs.getXReg .X23).toNat from rfl,
      show (m.regs.getXReg .X8).toBitVec.toNat = (m.regs.getXReg .X8).toNat from rfl, cp.x23, h8]
    omega
  have f9 : (st.data.regs.getXReg .X9).toBitVec = loc m0 (16 + 16 * c + 8) := by
    rw [hm'.regs .X9 _ rfl]
    show BinOp.apply .add .W64 (BinOp.apply .add .W64 (UnOp.apply (.ubfm 60 59) .W64
      (m.regs.getXReg .X8).toBitVec) ((envP m0 m).base 0 + BitVec.ofInt 64 16))
      (BitVec.ofNat 64 8) = _
    rw [Arrays.lsl4, Env.base_ofMachine m _ _ rfl,
      show (m.regs.getXReg .X8).toBitVec.toNat = (m.regs.getXReg .X8).toNat from rfl, h8]
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl]
    show _ = base m0 1392 + BitVec.ofNat 64 (16 + 16 * c + 8)
    rw [BitVec.ofNat_add (16 + 16 * c) 8, BitVec.ofNat_add 16 (16 * c)]
    ac_rfl
  have f10 : (st.data.regs.getXReg .X10).toBitVec =
      pt m0 (16 * c + 16 * m0.regs.X1.toNat + 64) := by
    rw [hm'.regs .X10 _ rfl]
    show BinOp.apply .add .W64 (BinOp.apply .add .W64 (BinOp.apply .add .W64
      (UnOp.apply (.ubfm 60 59) .W64 (m.regs.getXReg .X8).toBitVec)
      (UnOp.apply (.shift .LSL 4) .W64 (m.regs.getXReg .X20).toBitVec))
      ((envP m0 m).base 1 + BitVec.ofInt 64 0)) (BitVec.ofNat 64 64) = _
    rw [Arrays.lsl4, Env.base_ofMachine m _ _ rfl,
      show (m.regs.getXReg .X8).toBitVec.toNat = (m.regs.getXReg .X8).toNat from rfl, h8,
      cp.x20]
    simp only [UnOp.apply, BinOp.apply, low_W64, ext_W64, shiftW, Arrays.shl4]
    rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, BitVec.add_zero,
      show m0.regs.X1.toBitVec.toNat = m0.regs.X1.toNat from rfl]
    show _ = m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * c + 16 * m0.regs.X1.toNat + 64)
    rw [BitVec.ofNat_add (16 * c + 16 * m0.regs.X1.toNat) 64,
      BitVec.ofNat_add (16 * c) (16 * m0.regs.X1.toNat)]
    ac_rfl
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b37_length, NativeRustcVmArm.Vm.GkrStep.b37Length, show k + NativeRustcVmArm.Vm.GkrStep.b37Offset + 9 = k + NativeRustcVmArm.Vm.GkrStep.b38Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b37_length, NativeRustcVmArm.Vm.GkrStep.b37Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b37_next] at hpc
  -- `b38`
  have hwf2 := wf_cp h hfr (o := 16 + 16 * c) (o' := 56 + 16 * m0.regs.X1.toNat + 16 * c)
    (n := 16) (by omega) (by omega) (by omega)
  have hm2 : Match (Env.ofMachine st.data [(loc m0 (16 + 16 * c), 16),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 16 * c), 16)]) oneS st.data := by
    refine match_ofMachine (sregions := [(16, false), (16, false)])
      (regions := [(loc m0 (16 + 16 * c), 16), (pt m0 (56 + 16 * m0.regs.X1.toNat + 16 * c), 16)])
      ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl ⟨?_, ?_, trivial⟩ trivial trivial trivial
    · show _ = (Env.ofMachine st.data _).base 0 + BitVec.ofInt 64 8
      rw [Env.base_ofMachine st.data _ _ rfl, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
        f9, NativeRustcVm.addr_add_add]
    · show _ = (Env.ofMachine st.data _).base 1 + BitVec.ofInt 64 8
      rw [Env.base_ofMachine st.data _ _ rfl, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
        f10, pt_add, show 56 + 16 * m0.regs.X1.toNat + 16 * c + 8 =
          16 * c + 16 * m0.regs.X1.toNat + 64 by omega]
  refine exec_at (b38_in_code.trans hp.1 (by simp [b38])) run_b38 hwf2 hpc hm2
    fun st2 hm2' hpc2 ↦ ?_
  have hk : Kept st.data.dmem st2.data.dmem := hm2'.kept hwf2
  have hs : SameOutside st.data.dmem st2.data.dmem
      (InRange (pt m0 (56 + 16 * m0.regs.X1.toNat + 16 * c)) 16) :=
    NativeRustcVm.SameOutside.mono (hm2'.sameOutside hwf2) fun _ hq ↦
      Written.inRange (r := 1) rfl (hwf2.noWrap 1 _ _ rfl) (by decide +kernel) hq
  have hfr2 : Fr m0 1392 gkrStepStack slots keep (outs m0) st2.data :=
    fr_out h hfr (Match.sp_eq hm2 hm2' rfl) hk
      (NativeRustcVm.SameOutside.mono hs fun _ hq ↦ iv_sub h (by omega) (by omega) hq)
  have cp1 : AtCopy a s0 g0 m0 xs y vs s' st.data :=
    { cp with fr := hfr, x19 := f19, x20 := f20, x23 := f23
              hxs := by rw [hd]; exact cp.hxs
              vals := by rw [hd]; exact cp.vals
              len := by rw [hd]; exact cp.len
              ys := by rw [hd]; exact cp.ys
              ts := by rw [hd]; exact cp.ts }
  have hys := cp.ysize
  have cp2 := AtCopy.of_iv h cp1 hfr2 ((reg_of hm2' rfl).trans f19) ((reg_of hm2' rfl).trans f20)
    (by rw [reg_of hm2' rfl]; exact f23) hk hs (by omega) (by omega) (by omega)
  have hcl : c < xs.toList.length := by rw [Array.length_toList]; omega
  obtain ⟨a0, a8⟩ := ews_words (d := st.data.dmem) (b := base m0 1392) (o := 16)
    (by rw [hd]; exact cp.hxs) hcl
  have L0 : (Env.ofMachine st.data [(loc m0 (16 + 16 * c), 16),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 16 * c), 16)]).load 0 0 8 =
      (xs.toList[c]'hcl).c0.toBitVec :=
    Transcript.load_ofMachine (b := loc m0 (16 + 16 * c)) (n := 16) rfl (word_loc (by omega) a0)
  have L8 : (Env.ofMachine st.data [(loc m0 (16 + 16 * c), 16),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 16 * c), 16)]).load 0 8 8 =
      (xs.toList[c]'hcl).c1.toBitVec :=
    Transcript.load_ofMachine (b := loc m0 (16 + 16 * c)) (n := 16) rfl (word_loc (by omega) a8)
  have w0 := Transcript.wordAt_write hm2' (r := 1) (o := 0) rfl (by omega) (v := .load 0 0 8)
    (by decide +kernel)
  have w8 := Transcript.wordAt_write hm2' (r := 1) (o := 8) rfl (by omega) (v := .load 0 8 8)
    (by decide +kernel)
  simp only [Sym.eval] at w0 w8
  rw [L0] at w0
  rw [L8] at w8
  have N := ew_words (b := pt m0 (56 + 16 * m0.regs.X1.toNat + 16 * c)) (o := 0) w0 w8
  have old := keep_iv h hs (by omega) (by omega) (o' := 56 + 16 * m0.regs.X1.toNat)
    (bs := (xs.toList.take c).flatMap NativeRustcVm.ewBytes)
    (by rw [NativeRustcVm.length_ewsBytes, List.length_take]; omega)
    (.inl (by rw [NativeRustcVm.length_ewsBytes, List.length_take]; omega))
    (by rw [hd]; exact hpre)
  have hall : NativeRustcVm.EWsAt st2.data.dmem (pt m0 (56 + 16 * m0.regs.X1.toNat)) xs.toList := by
    have ht : xs.toList = xs.toList.take c ++ [xs.toList[c]'hcl] := by
      have e1 : xs.toList.take (c + 1) = xs.toList.take c ++ [xs.toList[c]'hcl] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hcl]; rfl
      rw [← e1, List.take_of_length_le (by rw [Array.length_toList]; omega)]
    rw [ht, NativeRustcVm.ewsAt_append, pt_add]
    refine ⟨old, ?_⟩
    rw [pt_add] at N
    rw [show 56 + 16 * m0.regs.X1.toNat + 16 * (xs.toList.take c).length =
      56 + 16 * m0.regs.X1.toNat + 16 * c + 0 by rw [List.length_take]; omega]
    exact N
  have hc2 : SBool.eval (Env.ofMachine st.data [(loc m0 (16 + 16 * c), 16),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 16 * c), 16)])
      (.not (.cmp .eq .W64 (.reg .X8) (.lit 1))) = false := by
    show (!CmpOp.eq.apply .W64 (st.data.regs.getXReg .X8).toBitVec (BitVec.ofNat 64 1)) = false
    rw [eq_lit64 _ _ (by decide)]
    rw [show (st.data.regs.getXReg .X8).toBitVec.toNat = (st.data.regs.getXReg .X8).toNat from rfl,
      f8]
    rfl
  simp only [PcOk, hc2, Bool.false_eq_true, ↓reduceIte, NativeRustcVmArm.Vm.GkrStep.b38_length, NativeRustcVmArm.Vm.GkrStep.b38Length,
    show k + NativeRustcVmArm.Vm.GkrStep.b38Offset + 7 = k + NativeRustcVmArm.Vm.GkrStep.b39Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b38_length, NativeRustcVmArm.Vm.GkrStep.b38Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b38_next] at hpc2
  exact at_pc hpc2 (full_spec hp h cp2 hall)

/-- **The pair loop**. -/
theorem pairs_loop (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {xs y vs : Array EW}
    {s' : TState}
    (hdone : ∀ m, PairsDone a s0 g0 m0 xs y vs s' m →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b36Offset)⟩) :
    ∀ n j m, xs.size / 2 * 2 - 2 * j = n → PairInv a s0 g0 m0 xs y vs s' j m →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b35Offset)⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro j m hn hi
  refine Eventually.bind (pair_step hp h hi) fun st hst ↦ ?_
  rcases hst with ⟨hpc, hi'⟩ | ⟨hpc, hd⟩
  · exact at_pc hpc (ih (n - 2) (by have := hi.lt; omega) (j + 1) st.data (by omega) hi')
  · exact at_pc hpc (hdone st.data hd)

omit [Host] in
/-- `x & 62` of a word below `64`: its even part. -/
theorem and62 (x : UInt64) (h : x.toNat < 64) :
    (BinOp.apply .and .W64 x.toBitVec (BitVec.ofNat 64 62)).toNat = x.toNat / 2 * 2 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_and, BitVec.toNat_ofNat]
  have key : ∀ n < 64, n &&& 62 = n / 2 * 2 := by decide
  rw [show (62 : Nat) % 2 ^ 64 = 62 from rfl]
  exact key _ h

/-- **After the pairs** (`b36`). -/
theorem done_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {xs y vs : Array EW}
    {s' : TState} {m : MachineData} (hd : PairsDone a s0 g0 m0 xs y vs s' m) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b36Offset)⟩ := by
  have cp := hd.cp
  refine Fr.runBlock (pre_stack h) N_ge rfl cp.fr (b36_in_code.trans hp.1 (by simp [b36]))
    run_b36 rfl rfl (by decide) (by decide) fun st hfr hd' hm hpc ↦ ?_
  have cp1 : AtCopy a s0 g0 m0 xs y vs s' st.data :=
    { cp with fr := hfr, x19 := (reg_of hm rfl).trans cp.x19, x20 := (reg_of hm rfl).trans cp.x20
              x23 := by rw [reg_of hm rfl]; exact cp.x23
              hxs := by rw [hd']; exact cp.hxs
              vals := by rw [hd']; exact cp.vals
              len := by rw [hd']; exact cp.len
              ys := by rw [hd']; exact cp.ys
              ts := by rw [hd']; exact cp.ts }
  have hc : SBool.eval (Env.ofMachine m [(base m0 1392, 1392)])
      (.cmp .eq .W64 (.reg .X23) (.reg .X8)) = decide (xs.size = xs.size / 2 * 2) := by
    show CmpOp.eq.apply .W64 (m.regs.getXReg .X23).toBitVec (m.regs.getXReg .X8).toBitVec = _
    rw [cmp_w64, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, cp.x23,
      hd.x8]
  simp only [PcOk, hc, NativeRustcVmArm.Vm.GkrStep.b36_length, NativeRustcVmArm.Vm.GkrStep.b36Length, show k + NativeRustcVmArm.Vm.GkrStep.b36Offset + 2 = k + NativeRustcVmArm.Vm.GkrStep.b37Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b36_length, NativeRustcVmArm.Vm.GkrStep.b36Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b36_next] at hpc
  by_cases he : xs.size = xs.size / 2 * 2
  · simp only [decide_eq_true he, ↓reduceIte] at hpc
    refine at_pc (hpc.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b39Offset) NativeRustcVmArm.Vm.GkrStep.label_21_at)) (full_spec hp h cp1 ?_)
    rw [hd']
    have := hd.pre
    rwa [← he, List.take_of_length_le (by rw [Array.length_toList])] at this
  · simp only [decide_eq_false he, Bool.false_eq_true, ↓reduceIte] at hpc
    exact at_pc hpc (rem_spec hp h cp1 (c := xs.size / 2 * 2) (by omega)
      (by rw [reg_of hm rfl]; exact hd.x8) (by rw [hd']; exact hd.pre))

/-- **The copy** (`.LGkrStep_11`): the dispatch on `|xs|`. -/
theorem copy_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {xs y vs : Array EW}
    {s' : TState} {m : MachineData} (cp : AtCopy a s0 g0 m0 xs y vs s' m) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b29Offset)⟩ := by
  have hS := pre_stack h
  have hsz := cp.size
  have hstep := pre_step h
  unfold busPointCap at hsz
  have hnil : NativeRustcVm.EWsAt m.dmem (pt m0 (56 + 16 * m0.regs.X1.toNat))
      (xs.toList.take 0) := NativeRustcVm.ewsAt_nil _ _
  -- `b29`
  refine Fr.runBlock hS N_ge rfl cp.fr (b29_in_code.trans hp.1 (by simp [b29])) run_b29 rfl rfl
    (by decide) (by decide) fun st hfr hd hm hpc ↦ ?_
  have cp1 : AtCopy a s0 g0 m0 xs y vs s' st.data :=
    { cp with fr := hfr, x19 := (reg_of hm rfl).trans cp.x19, x20 := (reg_of hm rfl).trans cp.x20
              x23 := by rw [reg_of hm rfl]; exact cp.x23
              hxs := by rw [hd]; exact cp.hxs
              vals := by rw [hd]; exact cp.vals
              len := by rw [hd]; exact cp.len
              ys := by rw [hd]; exact cp.ys
              ts := by rw [hd]; exact cp.ts }
  have hc : SBool.eval (Env.ofMachine m [(base m0 1392, 1392)])
      (.cmp .eq .W64 (.reg .X23) (.lit 0)) = decide (xs.size = 0) := by
    show CmpOp.eq.apply .W64 (m.regs.getXReg .X23).toBitVec (BitVec.ofNat 64 0) = _
    rw [eq_lit64 _ _ (by decide)]
    rw [show (m.regs.getXReg .X23).toBitVec.toNat = (m.regs.getXReg .X23).toNat from rfl, cp.x23]
  simp only [PcOk, hc, NativeRustcVmArm.Vm.GkrStep.b29_length, NativeRustcVmArm.Vm.GkrStep.b29Length, show k + NativeRustcVmArm.Vm.GkrStep.b29Offset + 2 = k + NativeRustcVmArm.Vm.GkrStep.b30Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b29_length, NativeRustcVmArm.Vm.GkrStep.b29Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b29_next] at hpc
  by_cases h0 : xs.size = 0
  · simp only [h0, decide_true, ↓reduceIte] at hpc
    refine at_pc (hpc.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b39Offset) NativeRustcVmArm.Vm.GkrStep.label_21_at)) (full_spec hp h cp1 ?_)
    rw [show xs.toList = [] from by rw [← Array.length_toList] at h0; exact List.eq_nil_of_length_eq_zero h0]
    exact NativeRustcVm.ewsAt_nil _ _
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc
  -- `b30`
  refine at_pc hpc (Fr.runBlock hS N_ge rfl hfr (b30_in_code.trans hp.1 (by simp [b30])) run_b30
    rfl rfl (by decide) (by decide) fun st2 hfr2 hd2 hm2 hpc2 ↦ ?_)
  have cp2 : AtCopy a s0 g0 m0 xs y vs s' st2.data :=
    { cp1 with fr := hfr2, x19 := (reg_of hm2 rfl).trans cp1.x19
               x20 := (reg_of hm2 rfl).trans cp1.x20
               x23 := by rw [reg_of hm2 rfl]; exact cp1.x23
               hxs := by rw [hd2]; exact cp1.hxs
               vals := by rw [hd2]; exact cp1.vals
               len := by rw [hd2]; exact cp1.len
               ys := by rw [hd2]; exact cp1.ys
               ts := by rw [hd2]; exact cp1.ts }
  have hc2 : SBool.eval (Env.ofMachine st.data [(base m0 1392, 1392)])
      (.not (.cmp .eq .W64 (.reg .X23) (.lit 1))) = !decide (xs.size = 1) := by
    show (!CmpOp.eq.apply .W64 (st.data.regs.getXReg .X23).toBitVec (BitVec.ofNat 64 1)) = _
    rw [eq_lit64 _ _ (by decide)]
    rw [show (st.data.regs.getXReg .X23).toBitVec.toNat = (st.data.regs.getXReg .X23).toNat
      from rfl, cp1.x23]
  simp only [PcOk, hc2, NativeRustcVmArm.Vm.GkrStep.b30_length, NativeRustcVmArm.Vm.GkrStep.b30Length, show k + NativeRustcVmArm.Vm.GkrStep.b30Offset + 2 = k + NativeRustcVmArm.Vm.GkrStep.b31Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b30_length, NativeRustcVmArm.Vm.GkrStep.b30Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b30_next] at hpc2
  by_cases h1 : xs.size = 1
  · simp only [h1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
    -- `b31`: none copied, to `.LGkrStep_19`.
    refine at_pc hpc2 (Fr.runBlock hS N_ge rfl hfr2 (b31_in_code.trans hp.1 (by simp [b31]))
      run_b31 rfl rfl (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_)
    simp only [PcOk] at hpc3
    refine at_pc (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b37Offset) NativeRustcVmArm.Vm.GkrStep.label_19_at)) (rem_spec hp h (c := 0)
      { cp2 with fr := hfr3, x19 := (reg_of hm3 rfl).trans cp2.x19
                 x20 := (reg_of hm3 rfl).trans cp2.x20
                 x23 := by rw [reg_of hm3 rfl]; exact cp2.x23
                 hxs := by rw [hd3]; exact cp2.hxs
                 vals := by rw [hd3]; exact cp2.vals
                 len := by rw [hd3]; exact cp2.len
                 ys := by rw [hd3]; exact cp2.ys
                 ts := by rw [hd3]; exact cp2.ts } h1
      (by rw [show (st3.data.regs.getXReg .X8).toNat = (st3.data.regs.getXReg .X8).toBitVec.toNat
            from rfl, reg_lit hm3 (r := .X8) (n := 0) rfl]; rfl)
      (NativeRustcVm.ewsAt_nil _ _))
  simp only [h1, decide_false, Bool.not_false, ↓reduceIte] at hpc2
  -- `b34`: the pair loop's start.
  have hm4 := match_p h hfr2 cp2.x19
  have hwf4 := wf_p h hfr2
  refine at_pc (hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b34Offset) NativeRustcVmArm.Vm.GkrStep.label_16_at)) (exec_then (b34_in_code.trans hp.1
    (by simp [b34])) run_b34 hwf4 hm4 fun st4 hm4' hpc4 ↦ ?_)
  have hd4 : st4.data.dmem = st2.data.dmem := hm4'.dmem_eq hwf4 rfl
  have hfr4 : Fr m0 1392 gkrStepStack slots keep (outs m0) st4.data :=
    Fr.ofBlock hfr2 hm4 hm4' hwf4 rfl rfl rfl (by decide)
  have cp4 : AtCopy a s0 g0 m0 xs y vs s' st4.data :=
    { cp2 with fr := hfr4
               x19 := UInt64.toBitVec_inj.mp ((hm4'.regs .X19 _ rfl).trans
                 (Transcript.eval_ptr rfl))
               x20 := (reg_of hm4' rfl).trans cp2.x20
               x23 := by rw [reg_of hm4' rfl]; exact cp2.x23
               hxs := by rw [hd4]; exact cp2.hxs
               vals := by rw [hd4]; exact cp2.vals
               len := by rw [hd4]; exact cp2.len
               ys := by rw [hd4]; exact cp2.ys
               ts := by rw [hd4]; exact cp2.ts }
  have hlt64 : (st2.data.regs.getXReg .X23).toNat < 64 := by rw [cp2.x23]; omega
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b34_length, NativeRustcVmArm.Vm.GkrStep.b34Length, show k + NativeRustcVmArm.Vm.GkrStep.b34Offset + 7 = k + NativeRustcVmArm.Vm.GkrStep.b35Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b34_length, NativeRustcVmArm.Vm.GkrStep.b34Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b34_next] at hpc4
  refine at_pc hpc4 (pairs_loop hp h (fun m hd ↦ done_spec hp h hd) _ 0 st4.data rfl
    { cp := cp4
      x8 := ?_
      x9 := ?_
      x10 := ?_
      x11 := ?_
      lt := by omega
      pre := by rw [hd4, hd2, hd]; exact hnil })
  · show (st4.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [hm4'.regs .X8 _ rfl]
    exact (and62 _ hlt64).trans (by rw [cp2.x23])
  · rw [hm4'.regs .X9 _ rfl]; rfl
  · rw [hm4'.regs .X10 _ rfl]
    show BinOp.apply .add .W64 (BinOp.apply .add .W64 ((envP m0 st2.data).base 1 +
      BitVec.ofInt 64 0) (UnOp.apply (.shift .LSL 4) .W64 (st2.data.regs.getXReg .X20).toBitVec))
      (BitVec.ofNat 64 80) = _
    rw [Env.base_ofMachine st2.data _ _ rfl, cp2.x20]
    simp only [UnOp.apply, BinOp.apply, low_W64, ext_W64, shiftW, Arrays.shl4]
    rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, BitVec.add_zero,
      show m0.regs.X1.toBitVec.toNat = m0.regs.X1.toNat from rfl]
    show _ = m0.regs.X3.toBitVec + BitVec.ofNat 64 (80 + 16 * m0.regs.X1.toNat + 32 * 0)
    rw [show 80 + 16 * m0.regs.X1.toNat + 32 * 0 = 16 * m0.regs.X1.toNat + 80 by omega,
      BitVec.ofNat_add]
    ac_rfl
  · show (st4.data.regs.getXReg .X11).toBitVec.toNat = _
    rw [hm4'.regs .X11 _ rfl]
    exact (and62 _ hlt64).trans (by rw [cp2.x23]; omega)

end

end NativeRustcVmArm.Bus.GkrStep
