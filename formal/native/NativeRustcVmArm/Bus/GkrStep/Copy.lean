module

public import NativeRustcVmArm.Bus.GkrStep.Values
public import NativeRustcVmArm.Arrays.Common

/-!
# `gkr_step`'s copy of the sumcheck's challenges

The challenges `xs` (the frame at `16`) go after `y` in the point (`pt m0 D`, `D = 56 + 16 step`):
two at a time (`b34`, the loop `b35`, `PairInv`), then the last one when `|xs|` is odd (`b37`,
`b38`); `b39` returns `1`.
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

/-- The `GkrStateW`'s byte `o`. -/
abbrev pt (m0 : MachineData) (o : Nat) : BitVec 64 := m0.regs.X3.toBitVec + BitVec.ofNat 64 o

variable [Labels] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}

/-- An interval of the `GkrStateW` is in it. -/
theorem iv_sub (h : GkrStepPre a s0 g0 m0) {o n : Nat} (hn : 0 < n) (hon : o + n ≤ 1064)
    {q : BitVec 64}
    (hq : InRange (pt m0 o) n q) : InRange m0.regs.X3.toBitVec gkrStateBytes q := by
  have hnw : m0.regs.X3.toBitVec.toNat + 1064 ≤ 2 ^ 64 := (pre_gk h).2.1
  have e : (pt m0 o).toNat = m0.regs.X3.toBitVec.toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  rw [Sym.inRange_iff (by rw [e]; omega), e] at hq
  rw [Sym.inRange_iff (by unfold gkrStateBytes pointBufBytes busPointCap; omega)]
  unfold gkrStateBytes pointBufBytes busPointCap
  omega

/-- Bytes of the `GkrStateW` kept outside an interval of it. -/
theorem keep_iv (h : GkrStepPre a s0 g0 m0) {d d' : DataMem} {o n : Nat}
    (hs : SameOutside d d' (InRange (pt m0 o) n)) (hn : 0 < n) (hon : o + n ≤ 1064) {o' : Nat}
    {bs : List UInt8} (hob : o' + bs.length ≤ 1064) (hd : o' + bs.length ≤ o ∨ o + n ≤ o')
    (hb : NativeRustcVm.BytesAt d (pt m0 o') bs) : NativeRustcVm.BytesAt d' (pt m0 o') bs :=
  NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ by
    have hnw : m0.regs.X3.toBitVec.toNat + 1064 ≤ 2 ^ 64 := (pre_gk h).2.1
    have e : (pt m0 o).toNat = m0.regs.X3.toBitVec.toNat + o :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    rw [NativeRustcVm.addr_add_add] at hq
    have e' : (pt m0 (o' + i)).toNat = m0.regs.X3.toBitVec.toNat + (o' + i) :=
      NativeRustcVm.toNat_add_ofNat (by omega)
    rw [Sym.inRange_iff (by rw [e]; omega), e, e'] at hq
    omega

/-- Bytes of the frame kept outside an interval of the `GkrStateW`. -/
theorem keep_iv_frame (h : GkrStepPre a s0 g0 m0) {d d' : DataMem} {o n : Nat}
    (hs : SameOutside d d' (InRange (pt m0 o) n)) (hn : 0 < n) (hon : o + n ≤ 1064) {o' : Nat}
    {bs : List UInt8} (hob : o' + bs.length ≤ 1392)
    (hb : NativeRustcVm.BytesAt d (loc m0 o') bs) : NativeRustcVm.BytesAt d' (loc m0 o') bs :=
  NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ by
    rw [NativeRustcVm.addr_add_add] at hq
    exact frame_not_p h (loc_in _ (by omega)) (iv_sub h hn hon hq)

/-- The `TState` kept outside an interval of the `GkrStateW`. -/
theorem ts_iv (h : GkrStepPre a s0 g0 m0) {d d' : DataMem} {o n : Nat} (hk : Kept d d')
    (hs : SameOutside d d' (InRange (pt m0 o) n)) (hn : 0 < n) (hon : o + n ≤ 1064) {s : TState}
    (ht : TStateAt d m0.regs.X0.toBitVec a s) : TStateAt d' m0.regs.X0.toBitVec a s :=
  ht.frame hk (fun _ hq ↦ p_apart h (iv_sub h hn hon hq)) hs

/-- The frame after a block writing in the `GkrStateW` only. -/
theorem fr_out (h : GkrStepPre a s0 g0 m0) {m m' : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) (hsp : m'.regs.SP = m.regs.SP)
    (hk : Kept m.dmem m'.dmem)
    (hs : SameOutside m.dmem m'.dmem (InRange m0.regs.X3.toBitVec gkrStateBytes)) :
    Fr m0 1392 gkrStepStack slots keep (outs m0) m' :=
  hfr.step hsp (fun _ hr ↦ absurd hr List.not_mem_nil) hk hs (fun _ hq ↦ .inr (.inr hq))
    fun p hp i hi hq ↦ by
      rw [NativeRustcVm.addr_add_add] at hq
      exact frame_not_p h (loc_in _ (by have := slots_le p hp; omega)) hq

/-- `AtCopy` across a change in the `GkrStateW` above the point's `y`. -/
theorem AtCopy.of_iv (h : GkrStepPre a s0 g0 m0) {xs y vs : Array EW} {s' : TState}
    {m m' : MachineData} (cp : AtCopy a s0 g0 m0 xs y vs s' m)
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m')
    (h19 : m'.regs.getXReg .X19 = m0.regs.X3) (h20 : m'.regs.getXReg .X20 = m0.regs.X1)
    (h23 : (m'.regs.getXReg .X23).toNat = xs.size) (hk : Kept m.dmem m'.dmem) {o n : Nat}
    (hs : SameOutside m.dmem m'.dmem (InRange (pt m0 o) n)) (ho : 56 + 16 * y.size ≤ o)
    (hn : 0 < n) (hon : o + n ≤ 1064) : AtCopy a s0 g0 m0 xs y vs s' m' where
  fr := hfr
  x19 := h19
  x20 := h20
  x23 := h23
  size := cp.size
  ysize := cp.ysize
  vsize := cp.vsize
  hxs := keep_iv_frame h hs hn hon (by rw [NativeRustcVm.length_ewsBytes]; have := xs_le cp.size; omega)
    cp.hxs
  vals := by
    have hv : NativeRustcVm.BytesAt m.dmem (pt m0 0) (vs.toList.flatMap NativeRustcVm.ewBytes) := by
      simp only [pt, NativeRustcVm.addr_add_zero]; exact cp.vals
    have := keep_iv h hs hn hon (o' := 0)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, cp.vsize]; omega)
      (.inl (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, cp.vsize]; omega)) hv
    simp only [pt, NativeRustcVm.addr_add_zero] at this
    exact this
  len := keep_iv h hs hn hon (o' := 48) (by rw [NativeRustcVm.length_wordBytes]; omega)
    (.inl (by rw [NativeRustcVm.length_wordBytes]; omega)) cp.len
  ys := keep_iv h hs hn hon (o' := 56)
    (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; have := cp.size
        unfold busPointCap at this; omega)
    (.inl (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; omega)) cp.ys
  ts := ts_iv h hk hs hn hon cp.ts
  run := cp.run

/-- **In the pair loop** (`.LGkrStep_17`), `j` pairs copied. -/
structure PairInv (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData)
    (xs y vs : Array EW) (s' : TState) (j : Nat) (m : MachineData) : Prop where
  cp : AtCopy a s0 g0 m0 xs y vs s' m
  x8 : (m.regs.getXReg .X8).toNat = xs.size / 2 * 2
  x9 : (m.regs.getXReg .X9).toBitVec = loc m0 (32 + 32 * j)
  x10 : (m.regs.getXReg .X10).toBitVec = pt m0 (80 + 16 * m0.regs.X1.toNat + 32 * j)
  x11 : (m.regs.getXReg .X11).toNat = xs.size / 2 * 2 - 2 * j
  lt : 2 * j < xs.size / 2 * 2
  pre : NativeRustcVm.EWsAt m.dmem (pt m0 (56 + 16 * m0.regs.X1.toNat)) (xs.toList.take (2 * j))

/-- **All pairs copied** (`b36`): `E = 2 ⌊|xs|/2⌋` challenges at the point's `D`. -/
structure PairsDone (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData)
    (xs y vs : Array EW) (s' : TState) (m : MachineData) : Prop where
  cp : AtCopy a s0 g0 m0 xs y vs s' m
  x8 : (m.regs.getXReg .X8).toNat = xs.size / 2 * 2
  pre : NativeRustcVm.EWsAt m.dmem (pt m0 (56 + 16 * m0.regs.X1.toNat))
    (xs.toList.take (xs.size / 2 * 2))

/-- The frame's `n` bytes at `o` and the `GkrStateW`'s at `o'`, as a block's regions. -/
theorem wf_cp (h : GkrStepPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) {o o' n : Nat} (hn : 0 < n)
    (ho : o + n ≤ 1392) (ho' : o' + n ≤ 1064) :
    (Env.ofMachine m [(loc m0 o, n), (pt m0 o', n)]).WF := by
  have cx := ctx h
  have hgk := pre_gk h
  have hnw : m0.regs.X3.toBitVec.toNat + 1064 ≤ 2 ^ 64 := hgk.2.1
  have hS := pre_stack h
  have hN := hS.2.1
  have := N_ge
  have hl := m0.regs.SP.toNat_lt
  have hb := base_toNat (m0 := m0) (F := 1392) (by omega)
  have e1 : (loc m0 o).toNat = (base m0 1392).toNat + o := NativeRustcVm.toNat_add_ofNat (by omega)
  have e2 : (pt m0 o').toNat = m0.regs.X3.toBitVec.toNat + o' :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hpa : NativeRustcVm.Apart m0.regs.X3.toBitVec gkrStateBytes (base m0 1392) 1392 :=
    apart_frame hN N_ge hgk.2.2.2.2.1
  refine Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (cx.mapped_frame0 (o := o) (n := n) ho i hi), ?_⟩,
    ⟨fun i hi ↦ hfr.kept _ ?_, ?_⟩, trivial⟩ ?_
  · show (loc m0 o).toNat + n ≤ 2 ^ 64
    rw [e1]; omega
  · rw [NativeRustcVm.addr_add_add]
    exact hgk.1 _ (by unfold gkrStateBytes pointBufBytes busPointCap; omega)
  · show (pt m0 o').toNat + n ≤ 2 ^ 64
    rw [e2]; omega
  · refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    simp only [List.mem_singleton, forall_eq]
    show (loc m0 o).toNat + n ≤ (pt m0 o').toNat ∨ (pt m0 o').toNat + n ≤ (loc m0 o).toNat
    unfold NativeRustcVm.Apart at hpa
    rw [e1, e2]
    have hgb : gkrStateBytes = 1064 := rfl
    omega

omit [Labels] in
/-- A word of the frame at a byte given by a sum. -/
theorem word_loc {d : DataMem} {o i o' : Nat} {w : UInt64} (he : o + i = o')
    (h : NativeRustcVm.WordAt d (base m0 1392 + BitVec.ofNat 64 o') w) :
    NativeRustcVm.WordAt d (off (loc m0 o) i) w := by
  show NativeRustcVm.WordAt d (base m0 1392 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) w
  rw [NativeRustcVm.addr_add_add, he]
  exact h

omit [Labels] in
/-- `x - v` of a word at least `v`. -/
theorem sub_lit (x : UInt64) (v : Nat) (h : v ≤ x.toNat) :
    (BinOp.apply .sub .W64 x.toBitVec (BitVec.ofNat 64 v)).toNat = x.toNat - v := by
  have hx := x.toBitVec.isLt
  have hx' : x.toBitVec.toNat = x.toNat := rfl
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [hx', Nat.mod_eq_of_lt (show v < 2 ^ 64 by rw [← hx'] at h; omega)]
  omega

omit [Labels] in
theorem pt_add (o i : Nat) : pt m0 o + BitVec.ofNat 64 i = pt m0 (o + i) :=
  NativeRustcVm.addr_add_add _ _ _

end

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- **A pair copied** (`b35`). -/
theorem pair_step (hp : Placed code k) (h : GkrStepPre a s0 g0 m0) {xs y vs : Array EW}
    {s' : TState} {j : Nat} {m : MachineData} (hi : PairInv a s0 g0 m0 xs y vs s' j m) :
    Eventually (step1 Host.exe) (fun st ↦
      (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b35Offset) ∧ PairInv a s0 g0 m0 xs y vs s' (j + 1) st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b36Offset) ∧ PairsDone a s0 g0 m0 xs y vs s' st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b35Offset)⟩ := by
  have hS := pre_stack h
  have cp := hi.cp
  have hsz := cp.size
  have hysz := cp.ysize
  have hstep := pre_step h
  have hlt := hi.lt
  unfold busPointCap at hsz
  have hE : xs.size / 2 * 2 ≤ xs.size := Nat.div_mul_le_self _ _
  have hwf := wf_cp h cp.fr (o := 16 + 32 * j) (o' := 56 + 16 * m0.regs.X1.toNat + 32 * j)
    (n := 32) (by omega) (by omega) (by omega)
  have hm : Match (Env.ofMachine m [(loc m0 (16 + 32 * j), 32),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 32 * j), 32)]) pairS m := by
    refine match_ofMachine (sregions := [(32, false), (32, false)])
      (regions := [(loc m0 (16 + 32 * j), 32), (pt m0 (56 + 16 * m0.regs.X1.toNat + 32 * j), 32)])
      ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl ⟨?_, ?_, trivial⟩ trivial trivial trivial
    · show _ = (Env.ofMachine m _).base 0 + BitVec.ofInt 64 16
      rw [Env.base_ofMachine m _ _ rfl, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl,
        hi.x9, NativeRustcVm.addr_add_add, show 16 + 32 * j + 16 = 32 + 32 * j by omega]
    · show _ = (Env.ofMachine m _).base 1 + BitVec.ofInt 64 24
      rw [Env.base_ofMachine m _ _ rfl, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl,
        hi.x10, pt_add, show 56 + 16 * m0.regs.X1.toNat + 32 * j + 24 =
          80 + 16 * m0.regs.X1.toNat + 32 * j by omega]
  refine exec_then (b35_in_code.trans hp.1 (by simp [b35])) run_b35 hwf hm fun st hm' hpc ↦ ?_
  have hk : Kept m.dmem st.data.dmem := hm'.kept hwf
  have hs : SameOutside m.dmem st.data.dmem (InRange (pt m0 (56 + 16 * m0.regs.X1.toNat + 32 * j)) 32) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun _ hq ↦
      Written.inRange (r := 1) rfl (hwf.noWrap 1 _ _ rfl) (by decide +kernel) hq
  have hfr' : Fr m0 1392 gkrStepStack slots keep (outs m0) st.data :=
    fr_out h cp.fr (Match.sp_eq hm hm' rfl) hk
      (NativeRustcVm.SameOutside.mono hs fun _ hq ↦ iv_sub h (by omega) (by omega) hq)
  have e19 : st.data.regs.getXReg .X19 = m0.regs.X3 := (reg_of hm' rfl).trans cp.x19
  have e20 : st.data.regs.getXReg .X20 = m0.regs.X1 := (reg_of hm' rfl).trans cp.x20
  have e23 : (st.data.regs.getXReg .X23).toNat = xs.size := by rw [reg_of hm' rfl]; exact cp.x23
  have e8 : (st.data.regs.getXReg .X8).toNat = xs.size / 2 * 2 := by
    rw [reg_of hm' rfl]; exact hi.x8
  have cp' := AtCopy.of_iv h cp hfr' e19 e20 e23 hk hs (by omega) (by omega) (by omega)
  -- the pair's words
  have h0 : 2 * j < xs.toList.length := by rw [Array.length_toList]; omega
  have h1 : 2 * j + 1 < xs.toList.length := by rw [Array.length_toList]; omega
  obtain ⟨a0, a8⟩ := ews_words (b := base m0 1392) (o := 16) cp.hxs h0
  obtain ⟨b0, b8⟩ := ews_words (b := base m0 1392) (o := 16) cp.hxs h1
  have L0 : (Env.ofMachine m [(loc m0 (16 + 32 * j), 32),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 32 * j), 32)]).load 0 0 8 =
      (xs.toList[2 * j]'h0).c0.toBitVec :=
    Transcript.load_ofMachine (b := loc m0 (16 + 32 * j)) (n := 32) rfl (word_loc (by omega) a0)
  have L8 : (Env.ofMachine m [(loc m0 (16 + 32 * j), 32),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 32 * j), 32)]).load 0 8 8 =
      (xs.toList[2 * j]'h0).c1.toBitVec :=
    Transcript.load_ofMachine (b := loc m0 (16 + 32 * j)) (n := 32) rfl (word_loc (by omega) a8)
  have L16 : (Env.ofMachine m [(loc m0 (16 + 32 * j), 32),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 32 * j), 32)]).load 0 16 8 =
      (xs.toList[2 * j + 1]'h1).c0.toBitVec :=
    Transcript.load_ofMachine (b := loc m0 (16 + 32 * j)) (n := 32) rfl (word_loc (by omega) b0)
  have L24 : (Env.ofMachine m [(loc m0 (16 + 32 * j), 32),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 32 * j), 32)]).load 0 24 8 =
      (xs.toList[2 * j + 1]'h1).c1.toBitVec :=
    Transcript.load_ofMachine (b := loc m0 (16 + 32 * j)) (n := 32) rfl (word_loc (by omega) b8)
  have w0 := Transcript.wordAt_write hm' (r := 1) (o := 0) rfl (by omega) (v := .load 0 0 8)
    (by decide +kernel)
  have w8 := Transcript.wordAt_write hm' (r := 1) (o := 8) rfl (by omega) (v := .load 0 8 8)
    (by decide +kernel)
  have w16 := Transcript.wordAt_write hm' (r := 1) (o := 16) rfl (by omega) (v := .load 0 16 8)
    (by decide +kernel)
  have w24 := Transcript.wordAt_write hm' (r := 1) (o := 24) rfl (by omega) (v := .load 0 24 8)
    (by decide +kernel)
  simp only [Sym.eval] at w0 w8 w16 w24
  rw [L0] at w0
  rw [L8] at w8
  rw [L16] at w16
  rw [L24] at w24
  have N := ews_cons (b := pt m0 (56 + 16 * m0.regs.X1.toNat + 32 * j)) (o := 0) (ew_words w0 w8)
    (ew_words (o := 16) w16 w24)
  have old := keep_iv h hs (by omega) (by omega) (o' := 56 + 16 * m0.regs.X1.toNat)
    (bs := (xs.toList.take (2 * j)).flatMap NativeRustcVm.ewBytes)
    (by rw [NativeRustcVm.length_ewsBytes, List.length_take]; omega)
    (.inl (by rw [NativeRustcVm.length_ewsBytes, List.length_take]; omega)) hi.pre
  have hpre : NativeRustcVm.EWsAt st.data.dmem (pt m0 (56 + 16 * m0.regs.X1.toNat))
      (xs.toList.take (2 * (j + 1))) := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, List.take_add_one, List.take_add_one,
      List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1, List.append_assoc]
    rw [NativeRustcVm.ewsAt_append, pt_add]
    refine ⟨old, ?_⟩
    rw [pt_add] at N
    rw [show 56 + 16 * m0.regs.X1.toNat + 16 * (xs.toList.take (2 * j)).length =
      56 + 16 * m0.regs.X1.toNat + 32 * j + 0 by rw [List.length_take]; omega]
    exact N
  have hc : SBool.eval (Env.ofMachine m [(loc m0 (16 + 32 * j), 32),
      (pt m0 (56 + 16 * m0.regs.X1.toNat + 32 * j), 32)])
      (.not (.cmp .eq .W64 (.reg .X11) (.lit 2))) = !decide (xs.size / 2 * 2 - 2 * j = 2) := by
    show (!CmpOp.eq.apply .W64 (m.regs.getXReg .X11).toBitVec (BitVec.ofNat 64 2)) = _
    rw [eq_lit64 _ _ (by decide)]
    rw [show (m.regs.getXReg .X11).toBitVec.toNat = (m.regs.getXReg .X11).toNat from rfl, hi.x11]
  simp only [PcOk, hc, NativeRustcVmArm.Vm.GkrStep.b35_length, NativeRustcVmArm.Vm.GkrStep.b35Length, show k + NativeRustcVmArm.Vm.GkrStep.b35Offset + 8 = k + NativeRustcVmArm.Vm.GkrStep.b36Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b35_length, NativeRustcVmArm.Vm.GkrStep.b35Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b35_next] at hpc
  by_cases hd : xs.size / 2 * 2 - 2 * j = 2
  · simp only [hd, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    refine .done _ (.inr ⟨hpc, cp', e8, ?_⟩)
    rw [show xs.size / 2 * 2 = 2 * (j + 1) by omega]
    exact hpre
  · simp only [hd, decide_false, Bool.not_false, ↓reduceIte] at hpc
    refine .done _ (.inl ⟨hpc.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b35Offset) NativeRustcVmArm.Vm.GkrStep.label_17_at), ⟨cp', e8, ?_, ?_, ?_, by omega, hpre⟩⟩)
    · rw [hm'.regs .X9 _ rfl]
      show (Env.ofMachine m _).base 0 + BitVec.ofInt 64 48 = _
      rw [Env.base_ofMachine m _ _ rfl, show BitVec.ofInt 64 48 = BitVec.ofNat 64 48 from rfl,
        NativeRustcVm.addr_add_add, show 16 + 32 * j + 48 = 32 + 32 * (j + 1) by omega]
    · rw [hm'.regs .X10 _ rfl]
      show (Env.ofMachine m _).base 1 + BitVec.ofInt 64 56 = _
      rw [Env.base_ofMachine m _ _ rfl, show BitVec.ofInt 64 56 = BitVec.ofNat 64 56 from rfl,
        pt_add, show 56 + 16 * m0.regs.X1.toNat + 32 * j + 56 =
          80 + 16 * m0.regs.X1.toNat + 32 * (j + 1) by omega]
    · show (st.data.regs.getXReg .X11).toBitVec.toNat = _
      rw [hm'.regs .X11 _ rfl]
      show (BinOp.apply .sub .W64 (m.regs.getXReg .X11).toBitVec (BitVec.ofNat 64 2)).toNat = _
      rw [sub_lit _ _ (by rw [hi.x11]; omega), hi.x11]
      omega

end

end NativeRustcVmArm.Bus.GkrStep
