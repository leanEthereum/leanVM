module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Whir.EachRowOfNextLevel.IterC

/-!
# `each_row` with `next_level`'s closure: the row's term, added

At `b17` `novel_eval`'s value `r` is at 1880, `What` `μ` (`w`) in X27, the folded row in X29,
X25: `b17` checks the `Some`, `b18`, `b19` scale `r` by `w` (`kmul`), `b20` reads query weight `j`
(`b5`) or `0` (`b21`), `b6` multiplies it by the folded row plus the scaled value (`EW::mul`), `b7`
adds the product to the batched value and counts the row: the next iteration, or the exit after
the last row (`iterD`). `Tail` is the iteration's state once X26 is reused.
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfNextLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

@[expose] public section

/-- **Iteration `j`'s state** once X26 is reused: `Mid` without the query. -/
structure Tail (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 m
  low : Low m0 m.dmem
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  bat : EWAt m.dmem (bOf m0) (parOf rows m0 j)
  x19 : m.regs.getXReg .X19 = rows.size.toUInt64
  x20 : (m.regs.getXReg .X20).toBitVec = bOf m0
  x21 : m.regs.getXReg .X21 = m0.regs.X3
  x22 : m.regs.getXReg .X22 = (8 * ((qsOf m0).size - j)).toUInt64
  x23 : (m.regs.getXReg .X23).toBitVec = (nextEnv m0 4).toBitVec + BitVec.ofNat 64 (8 + 16 * j)
  x24 : m.regs.getXReg .X24 = j.toUInt64

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

theorem Mid.tail {m : MachineData} (h : Mid rows m0 j m) : Tail rows m0 j m :=
  ⟨h.fr, h.low, h.hj, h.hjq, h.bat, h.x19, h.x20, h.x21, h.x22, h.x23, h.x24⟩

/-- **A call** changing memory in `HitN` only. -/
theorem Tail.call (hpre : EachRowNextPre rows op m0) {m m' : MachineData} (h : Tail rows m0 j m)
    (hs : SameOutside m.dmem m'.dmem (HitN m0)) (hsv : Saved m m') : Tail rows m0 j m' := by
  have hl := lay hpre
  have hr : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r := hsv.1
  exact ⟨EachRow.fr_hit hl h.fr hsv.2.1 hsv.2.2 hs slots_ok, h.low.keep hl hs, h.hj, h.hjq,
    bat_keep hpre h.bat hs fun q h ↦ hl.hit_stack h,
    (hr .X19 rfl).trans h.x19, (hr .X20 rfl) ▸ h.x20, (hr .X21 rfl).trans h.x21,
    (hr .X22 rfl).trans h.x22, (hr .X23 rfl) ▸ h.x23, (hr .X24 rfl).trans h.x24⟩

/-- A callee's change in its stack only, as a change in `HitN`. -/
theorem hit_of_stack (hpre : EachRowNextPre rows op m0) {m m' : MachineData} {N' : Nat}
    (hsp : m.regs.SP.toBitVec = fb m0) (hN' : 2000 + N' ≤ eachRowNextStack)
    (hs : SameOutside m.dmem m'.dmem (InRange (stackBelow m N') N')) :
    SameOutside m.dmem m'.dmem (HitN m0) :=
  EachRow.hit_of_call (lay hpre) hsp (o := 600) (n := 0) hN' le_rfl (by decide)
    fun q hq ↦ hs q fun h ↦ hq (.inr h)

/-- **The frame's bytes** are kept by a write of the batched value. -/
theorem frame_keep_out (hpre : EachRowNextPre rows op m0) {d d' : Mem 64}
    (hs : SameOutside d d' (InRange (bOf m0) 16)) {o : Nat} {bs : List UInt8}
    (hle : o + bs.length ≤ 2000) (hb : NativeRustcVm.BytesAt d (fb m0 + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d' (fb m0 + BitVec.ofNat 64 o) bs :=
  hb.of_sameOutside hs fun i hi hq ↦ by
    rw [NativeRustcVm.addr_add_add] at hq
    exact bat_not_frame hpre _ hq (NativeRustcVm.inRange_add (show o + i < 2000 by omega)
      (by decide))

theorem Low.keepOut (hpre : EachRowNextPre rows op m0) {d d' : Mem 64} (h : Low m0 d)
    (hs : SameOutside d d' (InRange (bOf m0) 16)) : Low m0 d' := by
  have kw : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 2000 → WordAt d (fb m0 + BitVec.ofNat 64 o) w →
      WordAt d' (fb m0 + BitVec.ofNat 64 o) w := fun ho hw ↦
    frame_keep_out hpre hs (by rw [NativeRustcVm.length_wordBytes]; omega) hw
  obtain ⟨hl', hw, hp⟩ := h.tab
  refine ⟨kw (by decide) h.w8, kw (by decide) h.w16, kw (by decide) h.w24, kw (by decide) h.w32,
    kw (by decide) h.w40, kw (by decide) h.w48, kw (by decide) h.w56, hl', kw (by decide) hw, ?_⟩
  have e : off (fb m0 + BitVec.ofNat 64 96) 8 = fb m0 + BitVec.ofNat 64 104 :=
    NativeRustcVm.addr_add_add _ _ _
  rw [e] at hp ⊢
  refine frame_keep_out hpre hs ?_ hp
  rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords]
  have : (tableOf m0).toList.length ≤ 31 := hl'
  omega

/-- Query weight `j`, below the weights' count. -/
theorem qw_get (hj : j < (nextEnv m0 5).toNat) :
    (qwOf m0).getD j 0 =
      NativeRustcVm.ewOf m0.dmem ((nextEnv m0 4).toBitVec + BitVec.ofNat 64 (16 * j)) := by
  unfold qwOf slice
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_eq_getElem (by rw [NativeRustcVm.length_ewsOf]; exact hj)]
  simp

/-- Past the weights' count, the weight `0`. -/
theorem qw_get_none (hj : (nextEnv m0 5).toNat ≤ j) : (qwOf m0).getD j 0 = 0 := by
  unfold qwOf slice
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_eq_none (by rw [NativeRustcVm.length_ewsOf]; exact hj)]
  rfl

theorem ew_add_comm (a b : EW) : a + b = b + a := by
  show (⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1⟩ : EW) = ⟨b.c0 ^^^ a.c0, b.c1 ^^^ a.c1⟩
  rw [UInt64.xor_comm a.c0, UInt64.xor_comm a.c1]

variable [Host] {k : Nat}

/-- **From `b17` to the next iteration or the exit.** -/
theorem iterD (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpre : EachRowNextPre rows op m0) {m : MachineData} (h : Mid rows m0 j m) {F r : EW}
    {w : UInt64} (hF : (⟨m.regs.getXReg .X29, m.regs.getXReg .X25⟩ : EW) = F)
    (h27 : m.regs.getXReg .X27 = w) (hr : OptEWAt m.dmem (fb m0 + BitVec.ofNat 64 1880) (some r))
    (hT : parOf rows m0 (j + 1) = parOf rows m0 j + (qwOf m0).getD j 0 * (F + EW.scale w r))
    (cont : ∀ m', Inv rows m0 (j + 1) m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b8Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b17Offset)⟩ := by
  have hl := lay hpre
  have hstk := hpre.1.1
  have hS : 3232 ≤ m0.regs.SP.toNat := hstk.2.1
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, hqw, hbin, -, -, -, -, -, -, -, -, apqw⟩ := hpre'
  have hbt : (fb m0).toNat = m0.regs.SP.toNat - 2000 := hl.base_F
  have hrs : rows.size ≤ 256 := hpre.1.2.1.2.1
  have hjr := h.hj
  have hjq := h.hjq
  -- `b17`, `b18`: `kmul(w, r.c0)`
  obtain ⟨hwf, hm⟩ := frame_env hpre h.fr
  let env := Env.ofMachine m [(fb m0, 2000)]
  have hrc := NativeRustcVm.ewAt_iff.mp hr.2
  have htag : env.load 0 1880 8 = (1 : UInt64).toBitVec := Ring.load_word hr.1
  have hr0 : env.load 0 1888 8 = r.c0.toBitVec := by
    refine Ring.load_word ?_
    have := hrc.1
    rwa [show off (fb m0 + BitVec.ofNat 64 1880) 8 = fb m0 + BitVec.ofNat 64 1888 from
      NativeRustcVm.addr_add_add _ _ _] at this
  have hr1 : env.load 0 1896 8 = r.c1.toBitVec := by
    refine Ring.load_word ?_
    have := hrc.2
    rwa [show off (fb m0 + BitVec.ofNat 64 1880) 8 + 8#64 = fb m0 + BitVec.ofNat 64 1896 by
        rw [NativeRustcVm.Transcript.off_add]; exact NativeRustcVm.addr_add_add _ _ _] at this
  have hk17 : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b17Offset) := b17_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk18 : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b18Offset) := b18_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk17 run_b17 hwf hm fun st17 hm17 hpc17 ↦ ?_
  have hpc17' : st17.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b18Offset) := by
    simp only [PcOk] at hpc17
    sym_simp at hpc17
    rw [htag] at hpc17
    exact hpc17
  refine exec_at hk18 (exec_after run_b17 run_b18) hwf hpc17' hm17 fun st18 hm18 hpc18 ↦ ?_
  have hmid18 : Mid rows m0 j st18.data := h.block hm hm18 hwf rfl rfl (by decide)
  have e18x0 : st18.data.regs.X0 = w := ((rv hm18 (r := .X0) rfl).trans rfl).trans h27
  have e18x1 : st18.data.regs.X1 = r.c0 :=
    (rv hm18 (r := .X1) rfl).trans (by show UInt64.ofBitVec (env.load 0 1888 8) = _; rw [hr0])
  have e18x28 : st18.data.regs.getXReg .X28 = r.c1 :=
    (rv hm18 (r := .X28) rfl).trans (by show UInt64.ofBitVec (env.load 0 1896 8) = _; rw [hr1])
  have e18x27 : st18.data.regs.getXReg .X27 = w := ((rv hm18 (r := .X27) rfl).trans rfl).trans h27
  have hF18 : (⟨st18.data.regs.getXReg .X29, st18.data.regs.getXReg .X25⟩ : EW) = F := by
    rw [(rv hm18 (r := .X29) rfl).trans rfl, (rv hm18 (r := .X25) rfl).trans rfl]; exact hF
  have hP18 : KmulPre st18.data := hmid18.fr.stackOk hstk (by decide) (by decide)
  refine call_then hpc18 hkmul hP18 fun ⟨d19, pc19⟩ hpc19 ⟨hv19, hs19, hsv19⟩ ↦ ?_
  simp only at hpc19
  subst hpc19
  have hmid19 := hmid18.call hpre (hit_of_stack hpre hmid18.fr.sp (by decide) hs19) hsv19
  rw [e18x0, e18x1] at hv19
  -- `b19`: `kmul(w, r.c1)`
  obtain ⟨hwf19, hm19⟩ := frame_env hpre hmid19.fr
  have hk19 : b19.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b19Offset) := b19_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk19 run_b19 hwf19 hm19 fun st20 hm20 hpc20 ↦ ?_
  have hd20 : st20.data.dmem = d19.dmem := hm20.dmem_eq hwf19 rfl
  have k20 : ∀ r, (after b19 frameS).reg r = some (.reg r) →
      st20.data.regs.getXReg r = d19.regs.getXReg r := fun r hr ↦
    (rv hm20 (by rw [← after_eq run_b19]; exact hr)).trans rfl
  have htail20 : Tail rows m0 j st20.data := by
    have t := hmid19.tail
    refine ⟨Ring.Fr.ofBlock t.fr hm19 hm20 hwf19 rfl rfl rfl (by simp), hd20 ▸ t.low, t.hj, t.hjq,
      hd20 ▸ t.bat, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k20 .X19 rfl, t.x19]
    · rw [k20 .X20 rfl, t.x20]
    · rw [k20 .X21 rfl, t.x21]
    · rw [k20 .X22 rfl, t.x22]
    · rw [k20 .X23 rfl, t.x23]
    · rw [k20 .X24 rfl, t.x24]
  have k19 : ∀ r, calleeSaved r = true → d19.regs.getXReg r = st18.data.regs.getXReg r :=
    hsv19.1
  have e20x0 : st20.data.regs.X0 = w :=
    ((rv hm20 (r := .X0) rfl).trans (k19 .X27 rfl)).trans e18x27
  have e20x1 : st20.data.regs.X1 = r.c1 :=
    ((rv hm20 (r := .X1) rfl).trans (k19 .X28 rfl)).trans e18x28
  have e20x26 : st20.data.regs.getXReg .X26 = kmul w r.c0 := (rv hm20 (r := .X26) rfl).trans hv19
  have hF20 : (⟨st20.data.regs.getXReg .X29, st20.data.regs.getXReg .X25⟩ : EW) = F := by
    rw [k20 .X29 rfl, k20 .X25 rfl, k19 .X29 rfl, k19 .X25 rfl]; exact hF18
  have hP20 : KmulPre st20.data := htail20.fr.stackOk hstk (by decide) (by decide)
  refine call_then hpc20 hkmul hP20 fun ⟨d21, pc21⟩ hpc21 ⟨hv21, hs21, hsv21⟩ ↦ ?_
  simp only at hpc21
  subst hpc21
  have htail21 := htail20.call hpre (hit_of_stack hpre htail20.fr.sp (by decide) hs21) hsv21
  rw [e20x0, e20x1] at hv21
  have k21 : ∀ r, calleeSaved r = true → d21.regs.getXReg r = st20.data.regs.getXReg r :=
    hsv21.1
  -- the scaled value: X26, X0
  have hsc0 : d21.regs.getXReg .X26 = (EW.scale w r).c0 := (k21 .X26 rfl).trans e20x26
  have hsc1 : d21.regs.X0 = (EW.scale w r).c1 := hv21
  have hF21 : (⟨d21.regs.getXReg .X29, d21.regs.getXReg .X25⟩ : EW) = F := by
    rw [k21 .X29 rfl, k21 .X25 rfl]; exact hF20
  -- `b20`: query weight `j`, or `0`
  obtain ⟨hwf21, hm21⟩ := frame_env hpre htail21.fr
  let env21 := Env.ofMachine d21 [(fb m0, 2000)]
  have hl8 : env21.load 0 8 8 = (nextEnv m0 5).toBitVec := Ring.load_word htail21.low.w8
  have hk20 : b20.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b20Offset) := b20_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk20 run_b20 hwf21 hm21 fun st22 hm22 hpc22 ↦ ?_
  have hd22 : st22.data.dmem = d21.dmem := hm22.dmem_eq hwf21 rfl
  have k22 : ∀ r, (after b20 frameS).reg r = some (.reg r) →
      st22.data.regs.getXReg r = d21.regs.getXReg r := fun r hr ↦
    (rv hm22 (by rw [← after_eq run_b20]; exact hr)).trans rfl
  have htail22 : Tail rows m0 j st22.data := by
    refine ⟨Ring.Fr.ofBlock htail21.fr hm21 hm22 hwf21 rfl rfl rfl (by simp), hd22 ▸ htail21.low,
      hjr, hjq, hd22 ▸ htail21.bat, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k22 .X19 rfl, htail21.x19]
    · rw [k22 .X20 rfl, htail21.x20]
    · rw [k22 .X21 rfl, htail21.x21]
    · rw [k22 .X22 rfl, htail21.x22]
    · rw [k22 .X23 rfl, htail21.x23]
    · rw [k22 .X24 rfl, htail21.x24]
  have hsc22 : (⟨st22.data.regs.getXReg .X26, st22.data.regs.X0⟩ : EW) = EW.scale w r := by
    rw [k22 .X26 rfl, show st22.data.regs.X0 = d21.regs.X0 from (k22 .X0 rfl), hsc0, hsc1]
  have hF22 : (⟨st22.data.regs.getXReg .X29, st22.data.regs.getXReg .X25⟩ : EW) = F := by
    rw [k22 .X29 rfl, k22 .X25 rfl]; exact hF21
  -- `b6`, `b7`, from `b5` or `b21`: the product, added
  have at6 : ∀ (d : MachineData), Tail rows m0 j d →
      (⟨d.regs.getXReg .X26, d.regs.X0⟩ : EW) = EW.scale w r →
      (⟨d.regs.getXReg .X29, d.regs.getXReg .X25⟩ : EW) = F →
      (⟨d.regs.getXReg .X8, d.regs.X1⟩ : EW) = (qwOf m0).getD j 0 →
      Eventually (step1 Host.exe) (Done rows m0) ⟨d, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b6Offset)⟩ := by
    intro d ht hsc hFd hq
    have hwf6 : (Env.ofMachine d [(fb m0, 2000), (bOf m0, 16)]).WF :=
      Env.wf_of ⟨⟨fun i hi ↦ ht.fr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
          Ring.base_noWrap (by omega)⟩, ⟨fun i hi ↦ ht.fr.kept _ (hbin.1.1 i hi), hbin.1.2⟩, trivial⟩
        (List.pairwise_pair.mpr (NativeRustcVm.Apart.symm
          (Ring.apart_frame (F := 2000) hstk.2.1 (by decide) hbin.2)))
    let env6 := Env.ofMachine d [(fb m0, 2000), (bOf m0, 16)]
    have hm6 : Match env6 batchS d :=
      match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
          fun h ↦ absurd h (by decide), trivial⟩
        (by rw [ht.fr.sp]; simp [Sym.eval])
        ⟨by show (d.regs.getXReg .X20).toBitVec = _; rw [ht.x20]; simp [Sym.eval], trivial⟩
        trivial trivial trivial
    have hbat := NativeRustcVm.ewAt_iff.mp ht.bat
    have hb0 : env6.load 1 0 8 = (parOf rows m0 j).c0.toBitVec := by
      refine Ring.load_word ?_
      show WordAt d.dmem (bOf m0 + BitVec.ofNat 64 0) _
      rw [NativeRustcVm.addr_add_zero]; exact hbat.1
    have hb8 : env6.load 1 8 8 = (parOf rows m0 j).c1.toBitVec := Ring.load_word hbat.2
    have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_then hk6 run_b6 hwf6 hm6 fun st6 hm6' hpc6 ↦ ?_
    have hd6 : st6.data.dmem = d.dmem := hm6'.dmem_eq hwf6 rfl
    have k6 : ∀ r, (after b6 batchS).reg r = some (.reg r) →
        st6.data.regs.getXReg r = d.regs.getXReg r := fun r hr ↦
      (rv hm6' (by rw [← after_eq run_b6]; exact hr)).trans rfl
    have hfr6 : FR m0 st6.data := Ring.Fr.ofBlock ht.fr hm6 hm6' hwf6 rfl rfl rfl (by simp)
    have e6x0 : st6.data.regs.X0 = d.regs.getXReg .X8 := (rv hm6' (r := .X0) rfl).trans rfl
    have e6x1 : st6.data.regs.X1 = d.regs.X1 := (rv hm6' (r := .X1) rfl).trans rfl
    have e6x2 : st6.data.regs.X2 = (F + EW.scale w r).c0 := by
      refine (rv hm6' (r := .X2) rfl).trans ?_
      sym_simp
      show UInt64.ofBitVec ((d.regs.getXReg .X26).toBitVec ^^^ (d.regs.getXReg .X29).toBitVec) = _
      rw [← hsc, ← hFd]
      exact UInt64.xor_comm _ _
    have e6x3 : st6.data.regs.X3 = (F + EW.scale w r).c1 := by
      refine (rv hm6' (r := .X3) rfl).trans ?_
      sym_simp
      show UInt64.ofBitVec (d.regs.X0.toBitVec ^^^ (d.regs.getXReg .X25).toBitVec) = _
      rw [← hsc, ← hFd]
      exact UInt64.xor_comm _ _
    have e6x27 : st6.data.regs.getXReg .X27 = (parOf rows m0 j).c0 :=
      (rv hm6' (r := .X27) rfl).trans (by show UInt64.ofBitVec (env6.load 1 0 8) = _; rw [hb0])
    have e6x28 : st6.data.regs.getXReg .X28 = (parOf rows m0 j).c1 :=
      (rv hm6' (r := .X28) rfl).trans (by show UInt64.ofBitVec (env6.load 1 8 8) = _; rw [hb8])
    have hj64 : j + 1 < 2 ^ 64 := by omega
    have e6x24 : st6.data.regs.getXReg .X24 = (j + 1).toUInt64 := by
      refine (rv hm6' (r := .X24) rfl).trans ?_
      sym_simp
      show UInt64.ofBitVec ((d.regs.getXReg .X24).toBitVec + BitVec.ofNat 64 1) = _
      rw [ht.x24]
      apply UInt64.toBitVec_inj.mp
      rw [UInt64.toBitVec_ofBitVec]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, UInt64.toNat_toBitVec, BitVec.toNat_ofNat,
        natCast_toUInt64_toNat (show j < 2 ^ 64 by omega), natCast_toUInt64_toNat hj64]
      omega
    have hP6 : EWMulPre st6.data := hfr6.stackOk hstk (by decide) (by decide)
    refine call_then hpc6 hmul hP6 fun ⟨d7, pc7⟩ hpc7 ⟨hv0, hv1, hs7, hsv7⟩ ↦ ?_
    simp only at hpc7
    subst hpc7
    have hs7' := hit_of_stack hpre hfr6.sp (by decide) hs7
    have hfr7 : FR m0 d7 := EachRow.fr_hit hl hfr6 hsv7.2.1 hsv7.2.2 hs7' slots_ok
    have k7 : ∀ r, calleeSaved r = true → d7.regs.getXReg r = st6.data.regs.getXReg r := hsv7.1
    have hq' : (⟨st6.data.regs.X0, st6.data.regs.X1⟩ : EW) = (qwOf m0).getD j 0 := by
      rw [e6x0, e6x1]; exact hq
    have hprod : (⟨d7.regs.X0, d7.regs.X1⟩ : EW) = (qwOf m0).getD j 0 * (F + EW.scale w r) := by
      rw [hv0, hv1, e6x2, e6x3, hq']
      rfl
    -- `b7`
    have hwf7 : (Env.ofMachine d7 [(fb m0, 2000), (bOf m0, 16)]).WF :=
      Env.wf_of ⟨⟨fun i hi ↦ hfr7.kept _ (Ring.frame_mapped hstk (by decide) i hi),
          Ring.base_noWrap (by omega)⟩, ⟨fun i hi ↦ hfr7.kept _ (hbin.1.1 i hi), hbin.1.2⟩, trivial⟩
        (List.pairwise_pair.mpr (NativeRustcVm.Apart.symm
          (Ring.apart_frame (F := 2000) hstk.2.1 (by decide) hbin.2)))
    let env7 := Env.ofMachine d7 [(fb m0, 2000), (bOf m0, 16)]
    have hm7 : Match env7 batchS d7 :=
      match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
          fun h ↦ absurd h (by decide), trivial⟩
        (by rw [hfr7.sp]; simp [Sym.eval])
        ⟨by
          show (d7.regs.getXReg .X20).toBitVec = _
          rw [k7 .X20 rfl, hm6'.regs .X20 _ rfl]
          rfl, trivial⟩
        trivial trivial trivial
    have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
    rw [show k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b6Offset + b6.length =
        k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b7Offset by
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.EachRowOfNextLevel.b6_next]]
    refine exec_then hk7 run_b7 hwf7 hm7 fun st8 hm8 hpc8 ↦ ?_
    have hfr8 : FR m0 st8.data :=
      Ring.Fr.ofBlockW hfr7 hm7 hm8 hwf7 rfl rfl (by simp) rfl (by decide) hS slots_le
        fun w hw ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl <;>
          · refine .inr ⟨by decide, fun b sz hb ↦ ?_⟩
            rw [show env7.regions = [(fb m0, 2000), (bOf m0, 16)] from rfl] at hb
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl⟩ := hb
            exact ⟨by decide, fun i hi ↦ NativeRustcVm.inRange_add hi (by decide)⟩
    have hs8 : SameOutside d7.dmem st8.data.dmem (InRange (bOf m0) 16) :=
      NativeRustcVm.SameOutside.mono (hm8.sameOutside hwf7) fun q hq ↦ by
        obtain ⟨w', hw', b', sz', hb', h1, h2⟩ := hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        have hnw := hbin.1.2
        unfold NoWrap at hnw
        rw [Sym.inRange_iff hnw]
        rcases hw' with rfl | rfl <;>
        · rw [show env7.regions = [(fb m0, 2000), (bOf m0, 16)] from rfl] at hb'
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq, Prod.mk.injEq] at hb'
          obtain ⟨rfl, rfl⟩ := hb'
          dsimp only at h1 h2
          have e : (bOf m0).toNat = (nextEnv m0 3).toBitVec.toNat := rfl
          omega
    -- the new batched value
    have hnew : EWAt st8.data.dmem (bOf m0) (parOf rows m0 (j + 1)) := by
      rw [hT, ew_add_comm, ← hprod]
      refine NativeRustcVm.ewAt_iff.mpr ⟨?_, ?_⟩
      · have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm8 (r := 1) (o := 0) rfl (by decide)
          (v := .bin .eor .W64 (.reg .X0) (.reg .X27)) (by decide)
        rw [NativeRustcVm.addr_add_zero] at this
        have e : UInt64.ofBitVec ((Sym.bin .eor .W64 (.reg .X0) (.reg .X27)).eval env7) =
            d7.regs.X0 ^^^ (parOf rows m0 j).c0 := by
          sym_simp
          show UInt64.ofBitVec (d7.regs.X0.toBitVec ^^^ (d7.regs.getXReg .X27).toBitVec) = _
          rw [k7 .X27 rfl, e6x27]
          rfl
        rw [e] at this
        exact this
      · have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm8 (r := 1) (o := 8) rfl (by decide)
          (v := .bin .eor .W64 (.reg .X1) (.reg .X28)) (by decide)
        have e : UInt64.ofBitVec ((Sym.bin .eor .W64 (.reg .X1) (.reg .X28)).eval env7) =
            d7.regs.X1 ^^^ (parOf rows m0 j).c1 := by
          sym_simp
          show UInt64.ofBitVec (d7.regs.X1.toBitVec ^^^ (d7.regs.getXReg .X28).toBitVec) = _
          rw [k7 .X28 rfl, e6x28]
          rfl
        rw [e] at this
        exact this
    have hlow8 : Low m0 st8.data.dmem :=
      Low.keepOut hpre ((ht.low.keep hl (fun q hq ↦ by rw [hd6])).keep hl hs7') hs8
    have hx19 : env7.regs .X19 = rows.size.toUInt64.toBitVec := by
      show (d7.regs.getXReg .X19).toBitVec = _
      rw [k7 .X19 rfl, k6 .X19 rfl, ht.x19]
    have hx24 : env7.regs .X24 = (j + 1).toUInt64.toBitVec := by
      show (d7.regs.getXReg .X24).toBitVec = _
      rw [k7 .X24 rfl, e6x24]
    simp only [PcOk] at hpc8
    sym_simp at hpc8
    rw [hx19, hx24] at hpc8
    by_cases hlast : rows.size = j + 1
    · -- the last row
      have hc : (rows.size.toUInt64.toBitVec == (j + 1).toUInt64.toBitVec) = true := by
        rw [hlast]; exact beq_self_eq_true _
      simp only [hc, ↓reduceIte] at hpc8
      rw [show Labels.label NativeRustcVmArm.Vm.EachRowOfNextLevel.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b23Offset) from hp.label (j := NativeRustcVmArm.Vm.EachRowOfNextLevel.b23Offset) NativeRustcVmArm.Vm.EachRowOfNextLevel.label_13_at]
        at hpc8
      obtain ⟨d8, pc8⟩ := st8
      simp only at hpc8
      subst hpc8
      refine exit_step hp hpre hfr8 ?_
      rw [EachRow.batchedOf_eq, show min (eachRowArgs m0).1.size rows.size = j + 1 by
        have : j < (eachRowArgs m0).1.size := hjq
        omega]
      exact hnew
    · have hc : (rows.size.toUInt64.toBitVec == (j + 1).toUInt64.toBitVec) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro he
        have := congrArg BitVec.toNat he
        rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, natCast_toUInt64_toNat (by omega),
          natCast_toUInt64_toNat hj64] at this
        exact hlast this
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc8
      rw [Nat.add_assoc, NativeRustcVmArm.Vm.EachRowOfNextLevel.b7_next] at hpc8
      obtain ⟨d8, pc8⟩ := st8
      simp only at hpc8
      subst hpc8
      have k8 : ∀ r, (after b7 batchS).reg r = some (.reg r) →
          d8.regs.getXReg r = d7.regs.getXReg r := fun r hr ↦
        (rv hm8 (by rw [← after_eq run_b7]; exact hr)).trans rfl
      have hnq : 8 * (qsOf m0).size < 2 ^ 64 := by
        have hq := hpre.1.2.2.2.2.1
        have h1 : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤ 2 ^ 64 := hq.1.2
        have h2 : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤
            (stackBelow m0 eachRowNextStack).toNat ∨
            (stackBelow m0 eachRowNextStack).toNat + eachRowNextStack ≤
              m0.regs.X1.toBitVec.toNat := hq.2
        have h3 : (stackBelow m0 eachRowNextStack).toNat < 2 ^ 64 := BitVec.isLt _
        have hsz : (qsOf m0).size = m0.regs.X2.toNat := EachRowOfFinalLevel.size_wordSlice _ _ _
        rw [hsz]
        rw [stack_eq] at h2
        omega
      refine cont d8 ⟨hfr8, hlow8, by omega, by omega, hnew, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [k8 .X19 rfl, k7 .X19 rfl, k6 .X19 rfl, ht.x19]
      · exact (hm8.regs .X20 _ rfl).trans (by simp [Sym.eval])
      · rw [k8 .X21 rfl, k7 .X21 rfl, k6 .X21 rfl, ht.x21]
      · refine (rv hm8 (r := .X22) rfl).trans ?_
        sym_simp
        show UInt64.ofBitVec ((d7.regs.getXReg .X22).toBitVec - BitVec.ofNat 64 8) = _
        rw [k7 .X22 rfl, k6 .X22 rfl, ht.x22]
        apply UInt64.toBitVec_inj.mp
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec,
          natCast_toUInt64_toNat (show 8 * ((qsOf m0).size - j) < 2 ^ 64 by omega),
          natCast_toUInt64_toNat (show 8 * ((qsOf m0).size - (j + 1)) < 2 ^ 64 by omega),
          BitVec.toNat_ofNat]
        omega
      · refine (hm8.regs .X23 _ rfl).trans ?_
        sym_simp
        show (d7.regs.getXReg .X23).toBitVec + BitVec.ofNat 64 16 = _
        rw [k7 .X23 rfl, k6 .X23 rfl, ht.x23, BitVec.add_assoc, ← BitVec.ofNat_add,
          show 8 + 16 * j + 16 = 8 + 16 * (j + 1) by omega]
      · rw [k8 .X24 rfl, k7 .X24 rfl, e6x24]
  -- the branch on the weights' count
  have hx24 : env21.regs .X24 = j.toUInt64.toBitVec := by
    show (d21.regs.getXReg .X24).toBitVec = _
    rw [htail21.x24]
  simp only [PcOk] at hpc22
  sym_simp at hpc22
  rw [hx24, hl8] at hpc22
  by_cases hjw : j < (nextEnv m0 5).toNat
  · -- `b5`: query weight `j`
    have hc : (j.toUInt64.toBitVec.ult (nextEnv m0 5).toBitVec) = true := by
      simp only [BitVec.ult, UInt64.toNat_toBitVec, natCast_toUInt64_toNat (show j < 2 ^ 64 by omega)]
      simpa using hjw
    simp only [hc, ↓reduceIte] at hpc22
    rw [show Labels.label NativeRustcVmArm.Vm.EachRowOfNextLevel.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b5Offset) from hp.label (j := NativeRustcVmArm.Vm.EachRowOfNextLevel.b5Offset) NativeRustcVmArm.Vm.EachRowOfNextLevel.label_3_at]
      at hpc22
    obtain ⟨d22, pc22⟩ := st22
    simp only at hpc22
    subst hpc22
    obtain ⟨qa, hqad⟩ : ∃ qa, qa = (nextEnv m0 4).toBitVec + BitVec.ofNat 64 (16 * j) :=
      ⟨_, rfl⟩
    have hqnw : (nextEnv m0 4).toBitVec.toNat + 16 * (nextEnv m0 5).toNat ≤ 2 ^ 64 := hqw.1.2
    have hqa : qa.toNat = (nextEnv m0 4).toBitVec.toNat + 16 * j := by
      rw [hqad]; exact NativeRustcVm.toNat_add_ofNat (by omega)
    have hfq : Apart (fb m0) 2000 qa 16 := by
      have := Ring.apart_frame (F := 2000) hstk.2.1 (by decide) hqw.2
      unfold Apart at this ⊢
      rw [hl.base_F] at this
      rw [hqa, hbt]
      omega
    let env5 := Env.ofMachine d22 [(fb m0, 2000), (qa, 16)]
    have hwf5 : env5.WF :=
      Env.wf_of ⟨⟨fun i hi ↦ htail22.fr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
          Ring.base_noWrap (by omega)⟩,
        ⟨fun i hi ↦ by
          rw [hqad, NativeRustcVm.addr_add_add]
          exact htail22.fr.kept _ (hqw.1.1 _ (by omega)), show qa.toNat + 16 ≤ 2 ^ 64 by omega⟩,
          trivial⟩
        (List.pairwise_pair.mpr hfq)
    have hx23a : (d22.regs.getXReg .X23).toBitVec = qa + BitVec.ofInt 64 8 := by
      rw [htail22.x23, hqad, BitVec.add_assoc,
        show BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 8 = BitVec.ofNat 64 (8 + 16 * j) by
          rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
            Nat.add_comm]]
    have hm5 : Match env5 weightS d22 :=
      match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
          fun h ↦ absurd h (by decide), trivial⟩
        (by rw [htail22.fr.sp]; simp [Sym.eval]) trivial trivial trivial
        ⟨hx23a, trivial⟩
    have hqv : NativeRustcVm.ewOf d22.dmem qa = (qwOf m0).getD j 0 := by
      rw [qw_get hjw, ← hqad]
      refine NativeRustcVm.ewOf_congr fun i hi ↦ ?_
      rw [hqad, NativeRustcVm.addr_add_add]
      exact input_same' hpre htail22.fr hqw apqw _ (by omega)
    have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b5Offset) := b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_then hk5 run_b5 hwf5 hm5 fun st5 hm5' hpc5 ↦ ?_
    have hd5 : st5.data.dmem = d22.dmem := hm5'.dmem_eq hwf5 rfl
    have k5 : ∀ r, (after b5 weightS).reg r = some (.reg r) →
        st5.data.regs.getXReg r = d22.regs.getXReg r := fun r hr ↦
      (rv hm5' (by rw [← after_eq run_b5]; exact hr)).trans rfl
    simp only [PcOk] at hpc5
    obtain ⟨d5, pc5⟩ := st5
    simp only at hpc5
    subst hpc5
    refine at6 d5 ⟨Ring.Fr.ofBlock htail22.fr hm5 hm5' hwf5 rfl rfl rfl (by simp),
      hd5 ▸ htail22.low, hjr, hjq, hd5 ▸ htail22.bat, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
    · rw [k5 .X19 rfl, htail22.x19]
    · rw [k5 .X20 rfl, htail22.x20]
    · rw [k5 .X21 rfl, htail22.x21]
    · rw [k5 .X22 rfl, htail22.x22]
    · rw [k5 .X23 rfl, htail22.x23]
    · rw [k5 .X24 rfl, htail22.x24]
    · rw [k5 .X26 rfl, show d5.regs.X0 = d22.regs.X0 from k5 .X0 rfl]; exact hsc22
    · rw [k5 .X29 rfl, k5 .X25 rfl]; exact hF22
    · rw [← hqv]
      have e8 : d5.regs.getXReg .X8 = UInt64.ofBitVec (env5.load 1 0 8) :=
        (rv hm5' (r := .X8) rfl).trans rfl
      have e1 : d5.regs.X1 = UInt64.ofBitVec (env5.load 1 8 8) :=
        (rv hm5' (r := .X1) rfl).trans rfl
      rw [e8, e1, Ring.load_eq_wordOf, Ring.load_eq_wordOf, UInt64.ofBitVec_toBitVec,
        UInt64.ofBitVec_toBitVec]
      show (⟨NativeRustcVm.wordOf d22.dmem (qa + BitVec.ofNat 64 0),
        NativeRustcVm.wordOf d22.dmem (qa + BitVec.ofNat 64 8)⟩ : EW) =
        ⟨NativeRustcVm.wordOf d22.dmem qa, NativeRustcVm.wordOf d22.dmem (qa + 8#64)⟩
      rw [NativeRustcVm.addr_add_zero]
  · -- `b21`: the weight `0`
    have hc : (j.toUInt64.toBitVec.ult (nextEnv m0 5).toBitVec) = false := by
      simp only [BitVec.ult, UInt64.toNat_toBitVec, natCast_toUInt64_toNat (show j < 2 ^ 64 by omega)]
      simpa using hjw
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc22
    obtain ⟨hwf22, hm22'⟩ := frame_env hpre htail22.fr
    have hk21 : b21.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b21Offset) := b21_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk21 run_b21 hwf22 hpc22 hm22' fun st5 hm5' hpc5 ↦ ?_
    have hd5 : st5.data.dmem = st22.data.dmem := hm5'.dmem_eq hwf22 rfl
    have k5 : ∀ r, (after b21 frameS).reg r = some (.reg r) →
        st5.data.regs.getXReg r = st22.data.regs.getXReg r := fun r hr ↦
      (rv hm5' (by rw [← after_eq run_b21]; exact hr)).trans rfl
    simp only [PcOk] at hpc5
    rw [show Labels.label NativeRustcVmArm.Vm.EachRowOfNextLevel.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b6Offset) from hp.label (j := NativeRustcVmArm.Vm.EachRowOfNextLevel.b6Offset) NativeRustcVmArm.Vm.EachRowOfNextLevel.label_4_at]
      at hpc5
    obtain ⟨d5, pc5⟩ := st5
    simp only at hpc5
    subst hpc5
    refine at6 d5 ⟨Ring.Fr.ofBlock htail22.fr hm22' hm5' hwf22 rfl rfl rfl (by simp),
      hd5 ▸ htail22.low, hjr, hjq, hd5 ▸ htail22.bat, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_
    · rw [k5 .X19 rfl, htail22.x19]
    · rw [k5 .X20 rfl, htail22.x20]
    · rw [k5 .X21 rfl, htail22.x21]
    · rw [k5 .X22 rfl, htail22.x22]
    · rw [k5 .X23 rfl, htail22.x23]
    · rw [k5 .X24 rfl, htail22.x24]
    · rw [k5 .X26 rfl, show d5.regs.X0 = st22.data.regs.X0 from k5 .X0 rfl]; exact hsc22
    · rw [k5 .X29 rfl, k5 .X25 rfl]; exact hF22
    · rw [qw_get_none (by omega), (rv hm5' (r := .X8) rfl).trans rfl,
        show d5.regs.X1 = 0 from (rv hm5' (r := .X1) rfl).trans rfl]
      rfl

end

end NativeRustcVmArm.Whir.EachRowOfNextLevel
