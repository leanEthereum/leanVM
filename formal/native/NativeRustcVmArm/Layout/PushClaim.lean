module

public import NativeRustcVmArm.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Layout.PushClaim.Regions

/-!
# `push_claim`

No room (`cs.size = 160`): `b0`, `b4` return `0`. Room: one environment of the entry state for
`b0`, `b1` (the frame, the count word, the next claim: `regions`), up to the call of
`Buf<EW, 36>::extend` on the point; one of the state it returns in for `b2` and `b3` (pushed,
`1`) or `b5` (the point too long, `0`). The frame's words, written by `b1`, are the entry's
callee-saved registers and return address when `b3`/`b5` restore them (`Frame`).
-/

namespace NativeRustcVmArm.Layout.PushClaim

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PushClaim
open NativeVm.Model NativeRustcVm.Layout
open NativeRustcVm.Transcript (off)

public section

theorem ofInt_neg8 : (BitVec.ofInt 64 (-8)).toNat = 2 ^ 64 - 8 := by
  rw [BitVec.toNat_ofInt]; omega

theorem toBitVec_toUInt64 (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

theorem ptr_zero_eval [Labels] (env : Env) (r : Nat) : (Sym.ptr r 0).eval env = env.base r := by
  simp [Sym.eval]

/-- The frame `b1` writes, at `sb`: the entry's X30, X22, X21, X20, X19. -/
structure Frame (d : Mem 64) (sb : BitVec 64) (m : MachineData) : Prop where
  x30 : NativeRustcVm.WordAt d (sb + BitVec.ofNat 64 0) m.regs.X30
  x22 : NativeRustcVm.WordAt d (sb + BitVec.ofNat 64 16) m.regs.X22
  x21 : NativeRustcVm.WordAt d (sb + BitVec.ofNat 64 24) m.regs.X21
  x20 : NativeRustcVm.WordAt d (sb + BitVec.ofNat 64 32) m.regs.X20
  x19 : NativeRustcVm.WordAt d (sb + BitVec.ofNat 64 40) m.regs.X19

theorem Frame.of_same {d d' : Mem 64} {sb : BitVec 64} {m : MachineData} (h : Frame d sb m)
    (hs : Same d d' sb 48) : Frame d' sb m :=
  ⟨WordAt.of_same h.x30 (hs.sub (by decide)) le_rfl, WordAt.of_same h.x22 (hs.sub (by decide)) le_rfl,
    WordAt.of_same h.x21 (hs.sub (by decide)) le_rfl, WordAt.of_same h.x20 (hs.sub (by decide)) le_rfl,
    WordAt.of_same h.x19 (hs.sub (by decide)) le_rfl⟩

theorem toUInt64_toNat (x : UInt64) : x.toNat.toUInt64 = x := by
  apply UInt64.toNat.inj; simp

/-- The count word in `b0`/`b1`: below `160` does not branch. -/
theorem room_cond {n : Nat} (hn : n < 160) :
    (!(BitVec.ofNat 64 n).ult (BitVec.ofNat 64 159) &&
      !(BitVec.ofNat 64 n == BitVec.ofNat 64 159)) = false := by
  rcases Nat.lt_or_ge n 159 with h | h
  · have : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 159) = true := by
      unfold BitVec.ult; simp only [BitVec.toNat_ofNat]; simp; omega
    simp [this]
  · obtain rfl : n = 159 := by omega
    decide

/-- `InRange` of nothing. -/
theorem not_inRange_zero {a p : BitVec 64} : ¬InRange a 0 p := by
  unfold InRange; omega

/-- The address `b1` computes, less `8`. -/
theorem alias_eq (c : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 n * BitVec.ofNat 64 608 + c =
      c + BitVec.ofNat 64 (8 + 608 * n) + BitVec.ofInt 64 (-8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_add, ofInt_neg8,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem alias_add (b : BitVec 64) (o : Nat) (ho : 8 ≤ o) (ho' : o < 2 ^ 64) :
    b + BitVec.ofInt 64 (-8) + BitVec.ofNat 64 o = b + BitVec.ofNat 64 (o - 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, ofInt_neg8, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

variable [Host] {k : Nat}

/-- **The epilogue**: from a block's start state whose region 0 is the frame at SP, a return that
loads X19 to X22 and X30 from it and pops it restores the entry's. -/
theorem restored {m st m' : MachineData} {sb : BitVec 64} {rs : List (BitVec 64 × Nat)}
    {S : SState} (hf : Frame st.dmem sb m)
    (hsp : m.regs.SP.toBitVec = sb + BitVec.ofInt 64 48)
    (hreg : ∀ r, calleeSaved r = true → r ≠ .X19 → r ≠ .X20 → r ≠ .X21 → r ≠ .X22 →
      st.regs.getXReg r = m.regs.getXReg r)
    (hk : Kept m.dmem st.dmem)
    (hm : Match (Env.ofMachine st ((sb, 48) :: rs)) S m')
    (hwf : (Env.ofMachine st ((sb, 48) :: rs)).WF)
    (h19 : S.reg .X19 = some (.load 0 40 8)) (h20 : S.reg .X20 = some (.load 0 32 8))
    (h21 : S.reg .X21 = some (.load 0 24 8)) (h22 : S.reg .X22 = some (.load 0 16 8))
    (h30 : S.reg .X30 = some (.load 0 0 8)) (hS : S.sp = .ptr 0 48)
    (hothers : ∀ r, calleeSaved r = true → r ≠ .X19 → r ≠ .X20 → r ≠ .X21 → r ≠ .X22 →
      S.reg r = some (.reg r)) :
    Saved m m' ∧ retOf m' = retOf m := by
  have ld : ∀ {o : Nat} {w : UInt64}, NativeRustcVm.WordAt st.dmem (sb + BitVec.ofNat 64 o) w →
      (Env.ofMachine st ((sb, 48) :: rs)).load 0 o 8 = w.toBitVec := fun h ↦ load_word h
  have hr : ∀ {r : XReg} {o : Nat} {w : UInt64}, S.reg r = some (.load 0 o 8) →
      NativeRustcVm.WordAt st.dmem (sb + BitVec.ofNat 64 o) w → m'.regs.getXReg r = w :=
    fun hs hw ↦ UInt64.toBitVec_inj.mp ((hm.regs _ _ hs).trans (ld hw))
  refine ⟨⟨fun r hr' ↦ ?_, ?_, fun p hp ↦ hm.kept hwf p (hk p hp)⟩, ?_⟩
  · by_cases e19 : r = .X19
    · subst e19; exact hr h19 hf.x19
    by_cases e20 : r = .X20
    · subst e20; exact hr h20 hf.x20
    by_cases e21 : r = .X21
    · subst e21; exact hr h21 hf.x21
    by_cases e22 : r = .X22
    · subst e22; exact hr h22 hf.x22
    have := hm.regs r _ (hothers r hr' e19 e20 e21 e22)
    exact (UInt64.toBitVec_inj.mp this).trans (hreg r hr' e19 e20 e21 e22)
  · apply UInt64.toBitVec_inj.mp
    rw [hm.sp, hS, hsp]
    simp [Sym.eval]
  · have := hr h30 hf.x30
    simp only [retOf]
    rw [show m'.regs.X30 = m.regs.X30 from this]

/-- **No room**: `b0` branches to `b4`, which returns `0`. -/
theorem full (hp : Placed code k) (cs : Array ColumnClaimW) (m : MachineData)
    (hC : ClaimsWAt m.dmem m.regs.X0.toBitVec cs)
    (hcm : Mapped m.dmem m.regs.X0.toBitVec claimsBytes)
    (hcn : NoWrap m.regs.X0.toBitVec claimsBytes) (hn : ¬cs.size < claimCap) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ PushClaimPost cs m st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.PushClaim.b0Offset)⟩ := by
  have hn160 : cs.size = 160 := by have := hC.len_le; unfold claimCap at *; omega
  let env := Env.ofMachine m [(m.regs.X0.toBitVec, 8)]
  have h8 : 8 ≤ claimsBytes := by decide
  have hwf : env.WF := Env.wf_of ⟨⟨NativeRustcVm.Mapped.mono hcm h8,
    NativeRustcVm.NoWrap.mono hcn h8⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env fullS m := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨show _ = (Sym.ptr 0 0).eval env by rw [ptr_zero_eval]; rfl, trivial⟩ trivial trivial trivial
  have hlen : env.load 0 0 8 = BitVec.ofNat 64 160 := by
    refine (load_word (v := (160 : Nat).toUInt64) ?_)
    rw [NativeRustcVm.addr_add_zero, ← hn160]
    exact hC.len
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_full hwf hm fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  sym_simp at hpc
  have hc : (!(BitVec.ofNat 64 160).ult (BitVec.ofNat 64 159) &&
      !(BitVec.ofNat 64 160 == BitVec.ofNat 64 159)) = true := by decide
  simp only [hlen, hc, ↓reduceIte] at hpc
  rw [hp.label (j := NativeRustcVmArm.Vm.PushClaim.b4Offset) NativeRustcVmArm.Vm.PushClaim.label_3_at] at hpc
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) (exec_after run_full run_b4) hwf hpc
    hm1 fun st2 hm2 hpc2 ↦ .done _ ⟨?_, ?_, ?_, ?_⟩
  · simp only [PcOk] at hpc2
    exact hpc2.trans (retOf_of_x30 hm2 rfl rfl)
  · simp only [hn, false_and, ↓reduceIte]
    exact UInt64.toBitVec_inj.mp (hm2.regs .X0 _ rfl)
  · exact NativeRustcVm.SameOutside.of_eq (hm2.dmem_eq hwf rfl) _
  · exact Match.saved hm hm2 hwf rfl (by decide)

/-- **Room**: `b0`, `b1`, the call, then `b2` and `b3` or `b5`. -/
theorem room (hp : Placed code k) (cs : Array ColumnClaimW)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    (m : MachineData) (hpre : PushClaimPre cs m) (hn : cs.size < claimCap) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ PushClaimPost cs m st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.PushClaim.b0Offset)⟩ := by
  obtain ⟨hS, hC, ⟨hcm, hcn⟩, hcs, ⟨⟨hpm, hpn⟩, hps⟩, hcp⟩ := hpre
  have hn' : cs.size < 160 := hn
  have hsbm := stack_mapped hS
  have hsbn := stack_noWrap hS
  have hslot := toNat_slot hcn hn'
  have hcn' := hcn
  unfold NoWrap claimsBytes columnClaimBytes claimCap at hcn'
  obtain ⟨hall, hpw⟩ := regions_wf hsbm hsbn hcm hcn hcs hn'
  have hcb : claimsBytes = 97288 := rfl
  have hcc : claimCap = 160 := rfl
  set c := m.regs.X0.toBitVec with hc
  set sb := stackBelow m pushClaimStack with hsbdef
  let env := Env.ofMachine m (regions sb c cs.size)
  have hwf : env.WF := Env.wf_of hall hpw
  have hb1 : env.base 1 = c := rfl
  have hb2 : env.base 2 = slot c cs.size := rfl
  have hlen : env.load 1 0 8 = BitVec.ofNat 64 cs.size :=
    load_word (v := cs.size.toUInt64) (by rw [hb1, NativeRustcVm.addr_add_zero]; exact hC.len)
  have halias : slotS.eval env = env.base 2 + BitVec.ofInt 64 (-8) := by
    show BinOp.apply .add .W64 (BinOp.apply .mul .W64 (env.load 1 0 8) (BitVec.ofNat 64 608))
      ((Sym.ptr 1 0).eval env) = _
    rw [hlen, ptr_zero_eval, hb1, hb2]
    simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
    exact alias_eq c cs.size
  have hm : Match env entryS m :=
    match_ofMachine ⟨rfl, fun _ ↦ stack_aligned hS rfl, rfl, nofun, rfl, nofun, trivial⟩
      sp_eq_stackBelow ⟨show _ = (Sym.ptr 1 0).eval env by rw [ptr_zero_eval]; rfl, trivial⟩
      trivial trivial ⟨halias, trivial⟩
  rw [show k + NativeRustcVmArm.Vm.PushClaim.b0Offset = k from rfl]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st0 hm0 hpc0 ↦ ?_
  simp only [PcOk] at hpc0
  sym_simp at hpc0
  simp only [hlen, room_cond hn', Bool.false_eq_true, ↓reduceIte] at hpc0
  rw [NativeRustcVmArm.Vm.PushClaim.b0_length, NativeRustcVmArm.Vm.PushClaim.b0Length] at hpc0
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf hpc0 hm0
    fun st hm1 hpc1 ↦ ?_
  -- At the call.
  have hk1 : Kept m.dmem st.data.dmem := hm1.kept hwf
  have hw1 : SameOutside m.dmem st.data.dmem (InRegions (regions sb c cs.size)) :=
    Layout.Match.sameOutside_regions hm1 hwf (by decide)
  have hX0 : st.data.regs.X0.toBitVec = slot c cs.size + BitVec.ofNat 64 8 := by
    have := hm1.regs .X0 _ rfl
    refine this.trans ?_
    show BinOp.apply .add .W64 (slotS.eval env) (BitVec.ofNat 64 16) = _
    rw [halias, hb2]
    simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
    exact alias_add _ 16 (by decide) (by decide)
  have hX1 : st.data.regs.X1 = m.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)
  have hX2 : st.data.regs.X2 = m.regs.X3 := UInt64.toBitVec_inj.mp (hm1.regs .X2 _ rfl)
  have hbuf0 : NativeRustcVm.WordAt st.data.dmem (slot c cs.size + BitVec.ofNat 64 8) 0 :=
    Layout.Match.wordAt_write hm1 (r := 2) (o := 8) (v := .lit 0) rfl (by decide) (by decide)
  have hsl8 : 8 + 608 * cs.size + 8 + 584 ≤ claimsBytes := by omega
  have hbm : Mapped m.dmem (slot c cs.size + BitVec.ofNat 64 8) 584 := by
    rw [NativeRustcVm.addr_add_add]; exact NativeRustcVm.Mapped.sub hcm hsl8
  have hbn : NoWrap (slot c cs.size + BitVec.ofNat 64 8) 584 := by
    rw [NativeRustcVm.addr_add_add]; exact NativeRustcVm.NoWrap.sub hcn hsl8
  have hbp : Apart (slot c cs.size + BitVec.ofNat 64 8) 584 m.regs.X2.toBitVec
      (16 * m.regs.X3.toNat) := by
    refine NativeRustcVm.Apart.mono hcp ?_ ?_ (Nat.le_refl _) (Nat.le_refl _) <;>
    · rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)]
      omega
  have hpre : BufEWExtendPre 36 st.data := by
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [hX0, NativeRustcVm.wordOf_of_wordAt hbuf0]; decide
    · rw [hX0]; exact fun i hi ↦ hk1 _ (hbm i hi)
    · rw [hX0]; exact hbn
    · rw [hX1, hX2]; exact fun i hi ↦ hk1 _ (hpm i hi)
    · rw [hX1, hX2]; exact hpn
    · rw [hX0, hX1, hX2]; exact hbp
  refine call_then hpc1 hext hpre fun st' hpc2 hpost ↦ ?_
  obtain ⟨hres, hch, hsv⟩ := hpost
  have hk2 : Kept st.data.dmem st'.data.dmem := hsv.2.2
  rw [hX0, hX2] at hres
  rw [hX0] at hch
  -- The point as `extend` read it is the entry's.
  have hslice : slice st.data st.data.regs.X1 m.regs.X3 = slice m m.regs.X2 m.regs.X3 := by
    rw [hX1]
    unfold slice
    exact congrArg List.toArray (NativeRustcVm.ewsOf_congr fun i hi ↦
      hw1 _ (not_inRegions hsbn hcn hn' hpn (NativeRustcVm.Apart.symm hcp) hps hi))
  have hbuf : NativeRustcVm.bufEWOf st.data.dmem (slot c cs.size + BitVec.ofNat 64 8) = [] := by
    unfold NativeRustcVm.bufEWOf
    rw [NativeRustcVm.wordOf_of_wordAt hbuf0]
    rfl
  rw [hbuf, hslice, List.nil_append] at hres
  -- After the call.
  have hsame2 : ∀ {a : BitVec 64} {len : Nat}, NoWrap a len →
      Apart a len (slot c cs.size + BitVec.ofNat 64 8) 584 → Same st.data.dmem st'.data.dmem a len :=
    fun ha hap ↦ Same.of_sameOutside hch fun j hj h ↦ h.elim
      (NativeRustcVm.Apart.not_inRange_add hap ha hbn hj) not_inRange_zero
  have hframe : Frame st'.data.dmem sb m := by
    refine Frame.of_same ⟨?_, ?_, ?_, ?_, ?_⟩ (hsame2 hsbn ?_)
    · exact Layout.Match.wordAt_write hm1 (r := 0) (o := 0) (v := .reg .X30) rfl (by decide)
        (by decide)
    · exact Layout.Match.wordAt_write hm1 (r := 0) (o := 16) (v := .reg .X22) rfl (by decide)
        (by decide)
    · exact Layout.Match.wordAt_write hm1 (r := 0) (o := 24) (v := .reg .X21) rfl (by decide)
        (by decide)
    · exact Layout.Match.wordAt_write hm1 (r := 0) (o := 32) (v := .reg .X20) rfl (by decide)
        (by decide)
    · exact Layout.Match.wordAt_write hm1 (r := 0) (o := 40) (v := .reg .X19) rfl (by decide)
        (by decide)
    · have h : c.toNat + 97288 ≤ sb.toNat ∨ sb.toNat + 48 ≤ c.toNat := hcs
      unfold Apart
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)]
      omega
  obtain ⟨hall', hpw'⟩ := regions_wf (fun i hi ↦ hk2 _ (hk1 _ (hsbm i hi))) hsbn
    (fun i hi ↦ hk2 _ (hk1 _ (hcm i hi))) hcn hcs hn'
  let envC := Env.ofMachine st'.data (regions sb c cs.size)
  have hwfC : envC.WF := Env.wf_of hall' hpw'
  have hspC : st'.data.regs.SP.toBitVec = sb := by
    rw [hsv.2.1, hm1.sp]; exact ptr_zero_eval env 0
  have hx20 : st'.data.regs.X20.toBitVec = c := by
    show (st'.data.regs.getXReg .X20).toBitVec = c
    rw [hsv.1 .X20 rfl]
    exact (hm1.regs .X20 _ rfl).trans (ptr_zero_eval env 1)
  have hx22 : st'.data.regs.X22.toBitVec = slot c cs.size := by
    show (st'.data.regs.getXReg .X22).toBitVec = _
    rw [hsv.1 .X22 rfl]
    refine (hm1.regs .X22 _ rfl).trans ?_
    show BinOp.apply .add .W64 (slotS.eval env) (BitVec.ofNat 64 8) = _
    rw [halias, hb2]
    simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
    exact (alias_add _ 8 (by decide) (by decide)).trans (NativeRustcVm.addr_add_zero _)
  have hmC : Match envC retS st'.data :=
    match_ofMachine ⟨rfl, fun _ ↦ stack_aligned hS rfl, rfl, nofun, rfl, nofun, trivial⟩
      (by rw [hspC]; exact (ptr_zero_eval envC 0).symm)
      ⟨show _ = (Sym.ptr 1 0).eval envC by rw [ptr_zero_eval]; exact hx20,
        show _ = (Sym.ptr 2 0).eval envC by rw [ptr_zero_eval]; exact hx22, trivial⟩
      trivial trivial trivial
  have hreg : ∀ r, calleeSaved r = true → r ≠ .X19 → r ≠ .X20 → r ≠ .X21 → r ≠ .X22 →
      st'.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr h19 h20 h21 h22
    rw [hsv.1 r hr]
    cases r <;> simp [calleeSaved] at hr h19 h20 h21 h22 ⊢ <;>
      exact Match.reg_eq hm hm1 rfl rfl
  have hk : Kept m.dmem st'.data.dmem := fun p h ↦ hk2 p (hk1 p h)
  have hpc2' : st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PushClaim.b2Offset) := hpc2
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwfC hpc2' hmC
    fun st2 hm2 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  -- Where memory changed: the regions and the point's buffer.
  have hout : ∀ p, InRegions (regions sb c cs.size) p → InRange c claimsBytes p ∨ InRange sb 48 p :=
    fun p h ↦ inRegions_out hcn hn' h
  have hbufin : ∀ p, InRange (slot c cs.size + BitVec.ofNat 64 8) 584 p → InRange c claimsBytes p :=
    fun p h ↦ by
      rw [NativeRustcVm.addr_add_add] at h
      exact NativeRustcVm.InRange.of_sub h hcn hsl8
  have hchanges : ∀ {m' : MachineData},
      SameOutside st'.data.dmem m'.dmem (InRegions (regions sb c cs.size)) →
      Changes m m' pushClaimStack c claimsBytes := by
    intro m' hd
    refine NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans
      (NativeRustcVm.SameOutside.trans hw1 hch) hd) fun p h ↦ ?_
    rcases h with (h | h | h) | h
    · exact hout p h
    · exact .inl (hbufin p h)
    · exact absurd h not_inRange_zero
    · exact hout p h
  by_cases hlenp : m.regs.X3.toNat ≤ 36
  · -- Pushed: `b3`.
    have hif : (NativeRustcVm.wordOf st.data.dmem (slot c cs.size + BitVec.ofNat 64 8)).toNat +
        m.regs.X3.toNat ≤ 36 := by rw [NativeRustcVm.wordOf_of_wordAt hbuf0]; simpa using hlenp
    simp only [hif, ↓reduceIte] at hres
    obtain ⟨hx0', hbufw⟩ := hres
    have hb0 : envC.regs .X0 = 1#64 := by show st'.data.regs.X0.toBitVec = _; rw [hx0']; rfl
    simp only [hb0] at hpc3
    rw [NativeRustcVmArm.Vm.PushClaim.b2_length, NativeRustcVmArm.Vm.PushClaim.b2Length] at hpc3
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) (exec_after run_b2 run_b3) hwfC hpc3
      hm2 fun st3 hm3 hpc4 ↦ ?_
    obtain ⟨hsaved, hret⟩ := restored hframe sp_eq_stackBelow hreg hk hm3 hwfC rfl rfl rfl rfl
      rfl rfl (fun r hr h19 h20 h21 h22 ↦ by
        cases r <;> first | rfl | simp [calleeSaved] at hr h19 h20 h21 h22)
    have hd3 : SameOutside st'.data.dmem st3.data.dmem (InRegions (regions sb c cs.size)) :=
      Layout.Match.sameOutside_regions hm3 hwfC (by decide)
    refine .done _ ⟨?_, ?_, hchanges hd3, hsaved⟩
    · simp only [PcOk] at hpc4; exact hpc4.trans hret
    · have hlenp' : m.regs.X3.toNat ≤ pointCap := hlenp
      simp only [hn, hlenp', and_self, ↓reduceIte]
      refine ⟨UInt64.toBitVec_inj.mp (hm3.regs .X0 _ rfl), ?_⟩
      have hs8 : (slot c cs.size + BitVec.ofNat 64 8).toNat = c.toNat + 16 + 608 * cs.size := by
        rw [NativeRustcVm.toNat_add_ofNat (by omega), hslot]; omega
      -- The count word, `cs.size` until `b3` adds one.
      have hc0 : NativeRustcVm.WordAt st'.data.dmem c cs.size.toUInt64 := by
        have h1 := Layout.Match.same_untouched hm1 (r := 1) (o := 0) (len := 8) rfl (by decide)
          (by decide)
        rw [NativeRustcVm.addr_add_zero] at h1
        refine WordAt.of_same (WordAt.of_same hC.len h1 le_rfl) (hsame2 ?_ ?_) le_rfl
        · exact NativeRustcVm.NoWrap.mono hcn (by decide)
        · unfold Apart; rw [hs8]; omega
      have hl0 : envC.load 1 0 8 = BitVec.ofNat 64 cs.size :=
        load_word (v := cs.size.toUInt64) (by rw [NativeRustcVm.addr_add_zero]; exact hc0)
      have hcnt : NativeRustcVm.WordAt st3.data.dmem c (cs.size + 1).toUInt64 := by
        have h := Layout.Match.wordAt_write hm3 (r := 1) (o := 0)
          (v := .bin .add .W64 (.load 1 0 8) (.lit 1)) rfl (by decide) (by decide)
        rw [NativeRustcVm.addr_add_zero] at h
        have e : UInt64.ofBitVec ((Sym.bin .add .W64 (.load 1 0 8) (.lit 1)).eval envC) =
            (cs.size + 1).toUInt64 := by
          apply UInt64.toBitVec_inj.mp
          show BinOp.apply .add .W64 (envC.load 1 0 8) (BitVec.ofNat 64 1) = BitVec.ofNat 64 (cs.size + 1)
          rw [hl0]
          simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show MemWidth.W64.bits = 64 from rfl]
          omega
        rw [e] at h
        exact h
      -- The earlier claims: apart from every write.
      have hold : ∀ i < cs.size, Same m.dmem st3.data.dmem (off c (8 + columnClaimBytes * i))
          columnClaimBytes := by
        intro i hi
        have hoff : (off c (8 + columnClaimBytes * i)).toNat = c.toNat + 8 + 608 * i := by
          rw [NativeRustcVm.toNat_add_ofNat (by unfold columnClaimBytes; omega)]
          unfold columnClaimBytes; omega
        have hni : ∀ j < columnClaimBytes, ¬InRegions (regions sb c cs.size)
            (off c (8 + columnClaimBytes * i) + BitVec.ofNat 64 j) :=
          fun j hj ↦ not_inRegions_old hsbn hcn hcs hn' hi hj
        refine ((Same.of_sameOutside hw1 hni).trans (hsame2 ?_ ?_)).trans
          (Same.of_sameOutside hd3 hni)
        · unfold NoWrap; rw [hoff]; unfold columnClaimBytes; omega
        · unfold Apart; rw [hoff, hs8]; unfold columnClaimBytes; omega
      -- The new claim: the column `b1` wrote, the point `extend` wrote, the value `b3` wrote.
      have hcol : NativeRustcVm.WordAt st3.data.dmem (slot c cs.size) m.regs.X1 := by
        have h1 := Layout.Match.wordAt_write hm1 (r := 2) (o := 0) (v := .reg .X1) rfl
          (by decide) (by decide)
        have h3 := Layout.Match.same_untouched hm3 (r := 2) (o := 0) (len := 8) rfl (by decide)
          (by decide)
        rw [NativeRustcVm.addr_add_zero] at h1 h3
        refine WordAt.of_same (WordAt.of_same h1 (hsame2 ?_ ?_) le_rfl) h3 le_rfl
        · unfold NoWrap; rw [hslot]; omega
        · unfold Apart; rw [hslot, hs8]; omega
      have hpt : NativeRustcVm.BufEWAt st3.data.dmem (slot c cs.size + BitVec.ofNat 64 8) 36
          (slice m m.regs.X2 m.regs.X3).toList :=
        NativeRustcVm.Layout.BufEWAt.of_same hbufw (Layout.Match.same_untouched hm3 (r := 2)
          (o := 8) (len := 584) rfl (by decide) (by decide)) (by decide)
      have h21 : UInt64.ofBitVec ((Sym.reg .X21).eval envC) = m.regs.X4 := by
        show st'.data.regs.getXReg .X21 = _
        rw [hsv.1 .X21 rfl]; exact UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
      have h19 : UInt64.ofBitVec ((Sym.reg .X19).eval envC) = m.regs.X5 := by
        show st'.data.regs.getXReg .X19 = _
        rw [hsv.1 .X19 rfl]; exact UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl)
      have hval : NativeRustcVm.EWAt st3.data.dmem (slot c cs.size + BitVec.ofNat 64 592)
          (ewArg m.regs.X4 m.regs.X5) := by
        have w0 := Layout.Match.wordAt_write hm3 (r := 2) (o := 592) (v := .reg .X21) rfl
          (by decide) (by decide)
        have w1 := Layout.Match.wordAt_write hm3 (r := 2) (o := 600) (v := .reg .X19) rfl
          (by decide) (by decide)
        rw [h21] at w0
        rw [h19] at w1
        have e : slot c cs.size + BitVec.ofNat 64 592 + BitVec.ofNat 64 8 =
            slot c cs.size + BitVec.ofNat 64 600 := NativeRustcVm.addr_add_add _ 592 8
        exact NativeRustcVm.ewAt_iff.mpr
          ⟨w0, (congrArg (fun a ↦ NativeRustcVm.WordAt st3.data.dmem a m.regs.X5) e).mpr w1⟩
      refine ClaimsWAt.push hC hn hcnt hold ⟨m.regs.X1.toBitVec.isLt, ?_, hpt, hval⟩
      show NativeRustcVm.WordAt _ _ m.regs.X1.toNat.toUInt64
      rw [toUInt64_toNat]
      exact hcol
  · -- Too long: `b5`.
    have hif : ¬(NativeRustcVm.wordOf st.data.dmem (slot c cs.size + BitVec.ofNat 64 8)).toNat +
        m.regs.X3.toNat ≤ 36 := by rw [NativeRustcVm.wordOf_of_wordAt hbuf0]; simpa using hlenp
    simp only [hif, ↓reduceIte] at hres
    have hb0 : envC.regs .X0 = 0#64 := by show st'.data.regs.X0.toBitVec = _; rw [hres]; rfl
    simp only [hb0] at hpc3
    rw [hp.label (j := NativeRustcVmArm.Vm.PushClaim.b5Offset) NativeRustcVmArm.Vm.PushClaim.label_4_at] at hpc3
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) (exec_after run_b2 run_b5) hwfC hpc3
      hm2 fun st3 hm3 hpc4 ↦ ?_
    obtain ⟨hsaved, hret⟩ := restored hframe sp_eq_stackBelow hreg hk hm3 hwfC rfl rfl rfl rfl
      rfl rfl (fun r hr h19 h20 h21 h22 ↦ by
        cases r <;> first | rfl | simp [calleeSaved] at hr h19 h20 h21 h22)
    refine .done _ ⟨?_, ?_, ?_, hsaved⟩
    · simp only [PcOk] at hpc4; exact hpc4.trans hret
    · have hlenp' : ¬m.regs.X3.toNat ≤ pointCap := hlenp
      simp only [hlenp', and_false, ↓reduceIte]
      exact UInt64.toBitVec_inj.mp (hm3.regs .X0 _ rfl)
    · exact hchanges (NativeRustcVm.SameOutside.of_eq (hm3.dmem_eq hwfC rfl) _)

/-- **`push_claim`'s contract.** -/
theorem pushClaim_spec (hp : Placed code k)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    (cs : Array ColumnClaimW) :
    Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs) := by
  intro m hpre
  rw [show Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.PushClaim.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.PushClaim.entryOffset) NativeRustcVmArm.Vm.PushClaim.entry_at]
  by_cases hn : cs.size < claimCap
  · exact room hp cs hext m hpre hn
  · obtain ⟨-, hC, ⟨hcm, hcn⟩, -⟩ := hpre
    exact full hp cs m hC hcm hcn hn

end

end NativeRustcVmArm.Layout.PushClaim
