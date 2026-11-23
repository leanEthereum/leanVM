module

public import NativeRustcVmX64.Bus.BusLayout.Common

/-!
# `bus_layout`'s sizes: the blocks' pairs (x86-64)

The loop head `NativeRustcVmX64.Vm.BusLayout.label_7` (`b9`, `SzInv i`): the sizes' first `nf + i` words written, `i`
even, RCX `i`, RSI two words past block `i`. A turn (`pair_step`): block `i`'s owner (`b9`), its
height written (`b10`'s first part), block `i + 1`'s owner (`b10`'s rest), its height (`b7`)
written (`b8`); out of the loop (to `NativeRustcVmX64.Vm.BusLayout.label_11`) once `i + 2` is the blocks' even count.
Each part runs in an environment of the regions it touches (the blocks' pair, the layout's
heights, the two sizes' words), which need not be apart from each other.
-/

namespace NativeRustcVmX64.Bus.BusLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmX64.Vm.BusLayout

public section

/-! ## Helpers -/

theorem beq_of_toNat {a c : BitVec 64} {x y : Nat} (ha : a.toNat = x) (hc : c.toNat = y) :
    (a == c) = decide (x = y) := by
  by_cases h : x = y
  · subst h
    have : a = c := BitVec.eq_of_toNat_eq (ha.trans hc.symm)
    simp [this]
  · have : a ≠ c := fun e ↦ h (by rw [← ha, ← hc, e])
    simp [this, h]

theorem ult_of_toNat {a c : BitVec 64} {x y : Nat} (ha : a.toNat = x) (hc : c.toNat = y) :
    a.ult c = decide (x < y) := by
  rw [BitVec.ult, ha, hc]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `ja` past `5`. -/
@[expose] def cJa (v : Sym) : SBool :=
  (SBool.cmp .ult .W64 v (.lit 5)).not.and (SBool.cmp .eq .W64 v (.lit 5)).not

/-- `jbe` to at most `5`. -/
@[expose] def cJbe (v : Sym) : SBool := (SBool.cmp .ult .W64 v (.lit 5)).or (SBool.cmp .eq .W64 v (.lit 5))

theorem eval_cJa [Labels] {env : Env} {v : Sym} {x : Nat} (hv : (v.eval env).toNat = x) :
    (cJa v).eval env = decide (5 < x) := by
  simp only [cJa, SBool.eval, CmpOp.apply, low_W64, Sym.eval]
  rw [ult_of_toNat hv (toNat_ofNat_lt (by decide)), beq_of_toNat hv (toNat_ofNat_lt (by decide))]
  by_cases h1 : x < 5 <;> by_cases h2 : x = 5 <;> simp [h1, h2] <;> omega

theorem eval_cJbe [Labels] {env : Env} {v : Sym} {x : Nat} (hv : (v.eval env).toNat = x) :
    (cJbe v).eval env = decide (x ≤ 5) := by
  simp only [cJbe, SBool.eval, CmpOp.apply, low_W64, Sym.eval]
  rw [ult_of_toNat hv (toNat_ofNat_lt (by decide)), beq_of_toNat hv (toNat_ofNat_lt (by decide))]
  by_cases h1 : x < 5 <;> by_cases h2 : x = 5 <;> simp [h1, h2] <;> omega

/-- A block writing only offsets `lo` to `hi` of region `r`, as a range. -/
theorem sameOutside_sub [Labels] {env : Env} {S : SState} {m : MachineData} (hwf : env.WF)
    (hm : Match env S m) {r : Nat} {b : BitVec 64} {sz lo hi : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hhi : hi ≤ sz)
    (hS : ∀ w ∈ S.mem, w.r = r ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) :
    NativeRustcVm.SameOutside env.mem0 m.dmem (NativeRustcVm.InRange (off b lo) (hi - lo)) := by
  intro q hq
  refine hm.get?_mem0 hwf fun hW ↦ hq ?_
  obtain ⟨w, hw, b', sz', hb', j, h1, h2, rfl⟩ := written_off hwf hW
  obtain ⟨hr, hlo, hhi'⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  have hnw := hwf.noWrap r b sz hb
  rw [inRange_off_iff (by omega) (by omega)]
  omega

/-- Every callee-saved register is pushed. -/
theorem regs_vac {P : Prop} : ∀ r, calleeSaved r = true → slots.any (·.2 == r) = false → P :=
  fun r h h' ↦ absurd h' (by rw [slots_all r h]; decide)

/-- **A block changing no byte**, RSP kept, keeps the body. -/
theorem Body.of_eq {m0 st st' : MachineData} {N o : Nat} (hst : StackOk m0 N) (hF : 1808 ≤ N)
    (hb : Body m0 1808 N slots o st) (hd : st'.dmem = st.dmem) (hsp : rspOf st' = rspOf st) :
    Body m0 1808 N slots o st' :=
  Body.of_sub (a := 896) (n := 0) hst hF hb (by omega) (fun p hp ↦ by have := slots_lo p hp; omega)
    (fun p hp ↦ slots_le p hp) (fun q _ ↦ by rw [hd]) hsp (by rw [hd]; exact fun _ h ↦ h)
    fun r h h' ↦ regs_vac r h h'

/-- The sizes kept where memory changed only from word `k` on. -/
theorem sizes_keep {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    {d d' : DataMem} {k a n : Nat} (hst : StackOk m0 busLayoutStack) (h : SizesAt d L bl m0 k)
    (ha : 896 + 8 * k ≤ a) (han : a + n ≤ 1808)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (off (fb m0) a) n)) :
    SizesAt d' L bl m0 k := by
  intro j hj
  have hrsp := hst.1
  have htop := hst.2.1
  have hN : 1808 ≤ busLayoutStack := by decide
  have hb : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  refine bytesAt_congr (h j hj) fun i hi ↦ ?_
  have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
  rw [off_add]
  refine hs _ fun hq ↦ ?_
  rw [inRange_off_iff (by omega) (by omega)] at hq
  omega

theorem sizes_snoc {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    {d : DataMem} {k : Nat} (h : SizesAt d L bl m0 k)
    (hw : NativeRustcVm.WordAt d (off (fb m0) (896 + 8 * k)) ((S L bl m0).getD k 0).toUInt64) :
    SizesAt d L bl m0 (k + 1) := fun j hj ↦ by
  rcases Nat.lt_or_ge j k with h' | h'
  · exact h j h'
  · obtain rfl : j = k := by omega
    exact hw

/-! ## The loop -/

/-- The registers the whole function keeps from `b0` on. -/
structure Rg (m0 st : MachineData) : Prop where
  rbx : reg st .rbx = reg m0 .rdi
  r12 : reg st .r12 = reg m0 .r9
  r13 : reg st .r13 = reg m0 .rcx
  r14 : reg st .r14 = reg m0 .rdx
  rbp : reg st .rbp = reg m0 .r8

theorem Rg.keep {m0 st st' : MachineData} (h : Rg m0 st)
    (hk : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .rbp], reg st' r = reg st r) : Rg m0 st' :=
  ⟨(hk .rbx (by simp)).trans h.rbx, (hk .r12 (by simp)).trans h.r12,
    (hk .r13 (by simp)).trans h.r13, (hk .r14 (by simp)).trans h.r14,
    (hk .rbp (by simp)).trans h.rbp⟩

/-- **The pairs' loop head** `NativeRustcVmX64.Vm.BusLayout.label_7`, the first `i` blocks' heights written. -/
structure SzInv (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) (i : Nat)
    (st : MachineData) : Prop where
  bd : Body m0 1808 busLayoutStack slots 8 st
  rg : Rg m0 st
  even : i % 2 = 0
  lt : i + 2 ≤ bl.length
  rax : reg st .rax = off (fb m0) (896 + 8 * nf m0)
  rcx : reg st .rcx = BitVec.ofNat 64 i
  rdx : reg st .rdx = BitVec.ofNat 64 (2 * (bl.length / 2))
  rsi : reg st .rsi = reg m0 .rcx + BitVec.ofNat 64 (16 + 16 * i)
  r15 : (reg st .r15).toNat = nf m0 + bl.length
  sizes : SizesAt st.dmem L bl m0 (nf m0 + i)

/-- The loop's exit `NativeRustcVmX64.Vm.BusLayout.label_11`: the first `2 ⌊nb / 2⌋` blocks' heights written. -/
structure SzEnd (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (st : MachineData) : Prop where
  bd : Body m0 1808 busLayoutStack slots 8 st
  rg : Rg m0 st
  rax : reg st .rax = off (fb m0) (896 + 8 * nf m0)
  rcx : reg st .rcx = BitVec.ofNat 64 (2 * (bl.length / 2))
  r15 : (reg st .r15).toNat = nf m0 + bl.length
  sizes : SizesAt st.dmem L bl m0 (nf m0 + 2 * (bl.length / 2))

variable [Host] {k : Nat}

/-- **A turn of the pairs' loop.** -/
theorem pair_step (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b9Offset)) (hI : SzInv L bl m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b15Offset) ∧ SzEnd L bl m0 st'.data)
      ∨ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b9Offset) ∧ SzInv L bl m0 (i + 2) st'.data)) st := by
  have hpre' := hpre
  obtain ⟨hst, hnf3, -, -, hbl2, hblmax, -, hown, -, hBok, -, hLok, -⟩ := hpre
  have hN : 1808 ≤ busLayoutStack := by decide
  have hrsp := hst.1
  have htop := hst.2.1
  have hlt := hI.lt
  have hev := hI.even
  have hmb : bl.length ≤ 51 := hblmax
  have hn54 := pre_n hpre'
  have hbase : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  have hnwF := frame_noWrap hst hN
  have hblk : (reg m0 .rcx).toNat + 16 * bl.length ≤ 2 ^ 64 := hBok.1.2
  have hlay : (reg m0 .r9).toNat + layoutBytes ≤ 2 ^ 64 := hLok.1.2
  have hlay72 : 72 ≤ layoutBytes := by decide
  -- The regions.
  have blkR : ∀ (j : Nat), j + 2 ≤ bl.length → ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (reg m0 .rcx + BitVec.ofNat 64 (16 * j)) 32 ∧
        NativeRustcVm.NoWrap (reg m0 .rcx + BitVec.ofNat 64 (16 * j)) 32 := fun j hj d hk ↦
    ⟨fun t ht ↦ by
      rw [NativeRustcVm.addr_add_add]; exact hk _ (hBok.1.1 _ (by omega)),
     by unfold NativeRustcVm.NoWrap; rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega⟩
  have layR : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (reg m0 .r9) 72 ∧ NativeRustcVm.NoWrap (reg m0 .r9) 72 :=
    fun d hk ↦ ⟨fun t ht ↦ hk _ (hLok.1.1 _ (by omega)), by unfold NativeRustcVm.NoWrap; omega⟩
  have hoff : ∀ o, o ≤ 1808 → (off (fb m0) o).toNat = (fb m0).toNat + o := fun o ho ↦
    toNat_off (by omega)
  have frR : ∀ (o : Nat), o + 16 ≤ 1760 → ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (off (fb m0) o) 16 ∧ NativeRustcVm.NoWrap (off (fb m0) o) 16 :=
    fun o ho d hk ↦ ⟨fun t ht ↦ by
      rw [off_add]; exact hk _ (frame_mapped hst hN (o + t) (by omega)),
     by unfold NativeRustcVm.NoWrap; rw [hoff o (by omega)]; omega⟩
  have frLay : ∀ (o : Nat), o + 16 ≤ 1760 →
      NativeRustcVm.Apart (off (fb m0) o) 16 (reg m0 .r9) 72 := fun o ho ↦ by
    have h' : NativeRustcVm.Apart (reg m0 .r9) layoutBytes (stackBelow m0 busLayoutStack)
      (busLayoutStack + 8) := hLok.2
    have hs := stackBelow_toNat (m := m0) (n := busLayoutStack) hrsp
    unfold NativeRustcVm.Apart at h' ⊢
    rw [hoff o (by omega)]
    omega
  set i0 := nf m0 + i with hi0
  have hi54 : i0 + 2 ≤ 54 := by omega
  have hrv : ∀ (st' st'' : MachineData), (∀ r, calleeSaved r = true →
      slots.any (·.2 == r) = false → reg st'' r = reg st' r) := fun _ _ r h h' ↦ regs_vac r h h'
  have hsl1 : ∀ a n, a + n ≤ 1760 → ∀ p ∈ slots, a + n ≤ p.1 := fun a n h p hp ↦ by
    have := slots_lo p hp; omega
  have hbi := hI.bd
  have hwk : ∀ j (hj : j < bl.length), bl[j].owner < 6 := fun j hj ↦ hown _ (List.getElem_mem hj)
  have htoN : ∀ {x : Nat}, x < 6 → (x.toUInt64.toBitVec).toNat = x := fun hx ↦ by
    rw [UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hvarN : ∀ {x : Nat}, x < 6 →
      (BinOp.mul.apply .W64 x.toUInt64.toBitVec (BitVec.ofNat 64 8)).toNat = 8 * x := fun hx ↦ by
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul]
    rw [htoN hx, toNat_ofNat_lt (by decide)]
    omega
  -- `b9`: block `i`'s owner.
  have hwf1 : (Env.ofMachine st.data [(reg m0 .rcx + BitVec.ofNat 64 (16 * i), 32)]
      (fun _ ↦ 0) 0).WF :=
    Env.wf_of ⟨blkR i hlt st.data hbi.fr.kept, trivial⟩ (List.pairwise_singleton _ _)
  have hrsi : reg st.data .rsi = (Sym.ptr 0 16).eval
      (Env.ofMachine st.data [(reg m0 .rcx + BitVec.ofNat 64 (16 * i), 32)] (fun _ ↦ 0) 0) := by
    show _ = (reg m0 .rcx + BitVec.ofNat 64 (16 * i)) + BitVec.ofInt 64 16
    rw [hI.rsi, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl,
      NativeRustcVm.addr_add_add, Nat.add_comm]
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf1 nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hrsi, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmem1, hdi1, hsi1, hk1⟩ := after_eq run_b9 ▸ ok_b9
  have hrsiA : reg st1.data .rsi = reg st.data .rsi := (hm1.regs .rsi _ hsi1).trans hrsi.symm
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf1 hmem1
  have bd1 := Body.of_eq hst hN hbi hd1 (hk1.reg' hm1 (by simp))
  have ho1 : reg st1.data .rdi = bl[i].owner.toUInt64.toBitVec := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hdi1]
    show (Env.ofMachine st.data _ (fun _ ↦ 0) 0).load 0 0 8 = _
    rw [NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st.data.dmem (reg m0 .rcx + BitVec.ofNat 64 (16 * i) +
      BitVec.ofNat 64 0)).toBitVec = _
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero,
      owner_word hpre' hbi.same (by omega)]
  simp only [PcOk] at hpc1
  change st1.pc = if (cJa (.load 0 0 8)).eval (Env.ofMachine st.data _ (fun _ ↦ 0) 0) then _
    else _ at hpc1
  rw [eval_cJa (x := bl[i].owner) ((congrArg BitVec.toNat ((hm1.regs .rdi _ hdi1).symm.trans ho1)).trans
    (htoN (hwk i (by omega))))] at hpc1
  rw [decide_eq_false (by have := hwk i (by omega); omega)] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b10`, first part: block `i`'s height written.
  have hwf2 : (Env.ofMachine st1.data [(off (fb m0) (896 + 8 * i0), 16), (reg m0 .r9, 72)]
      (fun _ ↦ reg st1.data .rdi) 0).WF :=
    Env.wf_of ⟨frR _ (by omega) st1.data bd1.fr.kept, layR st1.data bd1.fr.kept, trivial⟩
      (List.pairwise_pair.mpr (frLay _ (by omega)))
  have hrax1 : reg st1.data .rax = off (fb m0) (896 + 8 * nf m0) :=
    (hk1.reg' hm1 (by simp)).trans hI.rax
  have hrcx1 : reg st1.data .rcx = BitVec.ofNat 64 i := (hk1.reg' hm1 (by simp)).trans hI.rcx
  have hkey : ∀ (d : MachineData) (rs : List (BitVec 64 × Nat)) (vs : Nat → BitVec 64),
      reg d .rax = off (fb m0) (896 + 8 * nf m0) → reg d .rcx = BitVec.ofNat 64 i →
      rs[0]? = some (off (fb m0) (896 + 8 * i0), 16) →
      keyP.eval (Env.ofMachine d rs vs 0) = (Env.ofMachine d rs vs 0).base 0 +
        BitVec.ofInt 64 ((0 : Nat) : Int) := by
    intro d rs vs ha hc hr
    rw [Env.base_ofMachine d rs vs 0 hr]
    simp only [keyP, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show d.regs.get64 .rax = _ from ha, show d.regs.get64 .rcx = _ from hc,
      BitVec.ofNat_mul_ofNat, off_add, Nat.cast_zero, ofInt_zero64, BitVec.add_zero,
      show 896 + 8 * nf m0 + i * 8 = 896 + 8 * i0 by omega]
  have hb1 : (reg st1.data .rdi).toNat < 6 := by
    rw [ho1, htoN (hwk i (by omega))]; exact hwk i (by omega)
  have h12_1 : reg st1.data .r12 = reg m0 .r9 := (hk1.reg' hm1 (by simp)).trans hI.rg.r12
  refine exec_at (infix_of ((infix_take b10 2).trans b10_in_code (by simp [b10])) (by simp [b10])
    hp) run_b10a hwf2 nofun (hpc1.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b9_next)))
    (match_ofMachine (sregions := [16, 72]) ⟨rfl, rfl, trivial⟩
      ⟨h12_1.trans (eval_ptr rfl).symm, rfl, trivial⟩ trivial ⟨hb1, trivial⟩
      ⟨hkey _ _ _ hrax1 hrcx1 rfl, trivial⟩)
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hw2, hwr2, hdi2, h12_2, hk2⟩ := after_eq run_b10a ▸ ok_b10a
  have hs2 := sameOutside_sub hwf2 hm2 (r := 0) rfl (le_refl 16) (lo := 0)
    fun w hw ↦ ⟨(hw2 w hw).1, Nat.zero_le _, (hw2 w hw).2⟩
  rw [off_zero, Nat.sub_zero] at hs2
  have bd2 := Body.of_sub hst hN bd1 (a := 896 + 8 * i0) (n := 16) (by omega) (hsl1 _ _ (by omega))
    slots_le hs2 ((hk2.reg' hm2 (by simp))) (hm2.kept hwf2) (hrv _ _)
  have hh1 : (hX 1).eval (Env.ofMachine st1.data [(off (fb m0) (896 + 8 * i0), 16), (reg m0 .r9, 72)]
      (fun _ ↦ reg st1.data .rdi) 0) = ((S L bl m0).getD i0 0).toUInt64.toBitVec := by
    show (Env.ofMachine st1.data _ _ 0).load 1 (24 + (BinOp.mul.apply .W64 (reg st1.data .rdi)
      (BitVec.ofNat 64 8)).toNat) 8 = _
    rw [ho1, hvarN (hwk i (by omega)), NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st1.data.dmem (reg m0 .r9 +
      BitVec.ofNat 64 (24 + 8 * bl[i].owner))).toBitVec = _
    rw [height_word hpre' bd1.same (hwk i (by omega)), hi0, S_getD_bl (by omega)]
  have hW2 : NativeRustcVm.WordAt st2.data.dmem (off (fb m0) (896 + 8 * i0))
      ((S L bl m0).getD i0 0).toUInt64 := by
    have := wordAt_write_eq hm2 (b := off (fb m0) (896 + 8 * i0)) (o := 0) rfl (by decide) (hX 1)
      (hwr2.find (by simp)) hh1
    rwa [off_zero] at this
  have hsz2 : SizesAt st2.data.dmem L bl m0 (i0 + 1) :=
    sizes_snoc (sizes_keep hst (show SizesAt st1.data.dmem L bl m0 i0 by rw [hd1]; exact hI.sizes)
      (le_refl _) (by omega) hs2) hW2
  -- `b10`, second part: block `i + 1`'s owner.
  have hwf3 : (Env.ofMachine st2.data [(reg m0 .rcx + BitVec.ofNat 64 (16 * i), 32)]
      (fun _ ↦ 0) 0).WF :=
    Env.wf_of ⟨blkR i hlt st2.data bd2.fr.kept, trivial⟩ (List.pairwise_singleton _ _)
  have hrsi2 : reg st2.data .rsi = (Sym.ptr 0 16).eval
      (Env.ofMachine st2.data [(reg m0 .rcx + BitVec.ofNat 64 (16 * i), 32)] (fun _ ↦ 0) 0) :=
    ((hk2.reg' hm2 (by simp)).trans hrsiA).trans hrsi
  refine exec_at (infix_of ((infix_drop b10 2).trans b10_in_code (by simp [b10])) (by simp [b10])
    hp) run_b10b hwf3 nofun (hpc2.trans (congrArg Host.addrOf (by
      have : (b10.take 2).length = 2 := rfl; omega)))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hrsi2, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmem3, hdi3, hsi3, hk3⟩ := after_eq run_b10b ▸ ok_b10b
  have hrsiB : reg st3.data .rsi = reg st.data .rsi := (hm3.regs .rsi _ hsi3).trans hrsi.symm
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf3 hmem3
  have bd3 := Body.of_eq hst hN bd2 hd3 (hk3.reg' hm3 (by simp))
  have ho3 : reg st3.data .rdi = bl[i + 1].owner.toUInt64.toBitVec := by
    rw [show reg st3.data .rdi = _ from hm3.regs .rdi _ hdi3]
    show (Env.ofMachine st2.data _ (fun _ ↦ 0) 0).load 0 16 8 = _
    rw [NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st2.data.dmem (reg m0 .rcx + BitVec.ofNat 64 (16 * i) +
      BitVec.ofNat 64 16)).toBitVec = _
    rw [NativeRustcVm.addr_add_add, show 16 * i + 16 = 16 * (i + 1) by omega,
      owner_word hpre' bd2.same (by omega)]
  simp only [PcOk] at hpc3
  change st3.pc = if (cJbe (.load 0 16 8)).eval (Env.ofMachine st2.data _ (fun _ ↦ 0) 0) then _
    else _ at hpc3
  rw [eval_cJbe (x := bl[i + 1].owner) ((congrArg BitVec.toNat ((hm3.regs .rdi _ hdi3).symm.trans
    ho3)).trans (htoN (hwk (i + 1) (by omega))))] at hpc3
  rw [decide_eq_true (by have := hwk (i + 1) (by omega); omega)] at hpc3
  simp only [↓reduceIte] at hpc3
  -- `b7`: its height.
  have hwf4 : (Env.ofMachine st3.data [(reg m0 .r9, 72)] (fun _ ↦ reg st3.data .rdi) 0).WF :=
    Env.wf_of ⟨layR st3.data bd3.fr.kept, trivial⟩ (List.pairwise_singleton _ _)
  have h12_3 : reg st3.data .r12 = reg m0 .r9 :=
    (hk3.reg' hm3 (by simp)).trans ((hm2.regs .r12 _ h12_2).trans (eval_ptr rfl))
  have hb3 : (reg st3.data .rdi).toNat < 6 := by
    rw [ho3, htoN (hwk (i + 1) (by omega))]; exact hwk (i + 1) (by omega)
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf4 nofun
    (hpc3.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_5_at))
    (match_ofMachine (sregions := [72]) ⟨rfl, trivial⟩ ⟨h12_3.trans (eval_ptr rfl).symm, rfl, trivial⟩
      trivial ⟨hb3, trivial⟩ trivial)
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmem4, hdi4, h12_4, hk4⟩ := after_eq run_b7 ▸ ok_b7
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf4 hmem4
  have bd4 := Body.of_eq hst hN bd3 hd4 (hk4.reg' hm4 (by simp))
  have hh4 : reg st4.data .rdi = ((S L bl m0).getD (i0 + 1) 0).toUInt64.toBitVec := by
    rw [show reg st4.data .rdi = _ from hm4.regs .rdi _ hdi4]
    show (Env.ofMachine st3.data _ _ 0).load 0 (24 + (BinOp.mul.apply .W64 (reg st3.data .rdi)
      (BitVec.ofNat 64 8)).toNat) 8 = _
    rw [ho3, hvarN (hwk (i + 1) (by omega)), NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st3.data.dmem (reg m0 .r9 +
      BitVec.ofNat 64 (24 + 8 * bl[i + 1].owner))).toBitVec = _
    rw [height_word hpre' bd3.same (hwk (i + 1) (by omega)), hi0,
      show nf m0 + i + 1 = nf m0 + (i + 1) by omega, S_getD_bl (by omega)]
  -- `b8`: its height written; the next pair or out.
  have hwf5 : (Env.ofMachine st4.data [(off (fb m0) (896 + 8 * i0), 16)] (fun _ ↦ 0) 0).WF :=
    Env.wf_of ⟨frR _ (by omega) st4.data bd4.fr.kept, trivial⟩ (List.pairwise_singleton _ _)
  have K4 : ∀ r ∈ [Reg64.rax, .rcx, .rdx, .rbx, .rbp, .r13, .r14, .r15, .rsp],
      reg st4.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hk4.reg' hm4 (by simp)).trans ((hk3.reg' hm3 (by simp)).trans
        ((hk2.reg' hm2 (by simp)).trans (hk1.reg' hm1 (by simp))))
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf5 nofun
    (hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b7_next)))
    (match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial
      ⟨hkey _ _ _ ((K4 .rax (by simp)).trans hI.rax) ((K4 .rcx (by simp)).trans hI.rcx) rfl,
        trivial⟩)
    fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hw5, hwr5, hcx5, hsi5, hk5⟩ := after_eq run_b8 ▸ ok_b8
  have hs5 := sameOutside_sub hwf5 hm5 (r := 0) rfl (le_refl 16) (lo := 8) hw5
  rw [off_off] at hs5
  have bd5 := Body.of_sub hst hN bd4 (a := 896 + 8 * i0 + 8) (n := 16 - 8) (by omega)
    (hsl1 _ _ (by omega)) slots_le hs5 ((hk5.reg' hm5 (by simp))) (hm5.kept hwf5) (hrv _ _)
  have hW5 : NativeRustcVm.WordAt st5.data.dmem (off (fb m0) (896 + 8 * (i0 + 1)))
      ((S L bl m0).getD (i0 + 1) 0).toUInt64 := by
    have := wordAt_write_eq hm5 (b := off (fb m0) (896 + 8 * i0)) (o := 8) rfl (by decide) (.reg .rdi)
      (hwr5.find (by simp)) hh4
    rwa [off_off, show 896 + 8 * i0 + 8 = 896 + 8 * (i0 + 1) by omega] at this
  have hsz5 : SizesAt st5.data.dmem L bl m0 (i0 + 2) :=
    sizes_snoc (sizes_keep hst (show SizesAt st4.data.dmem L bl m0 (i0 + 1) by
      rw [hd4, hd3]; exact hsz2) (by omega) (by omega) hs5) hW5
  have hrcx5 : reg st5.data .rcx = BitVec.ofNat 64 (i + 2) := by
    rw [show reg st5.data .rcx = _ from hm5.regs .rcx _ hcx5]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st4.data.regs.get64 .rcx = _ from (K4 .rcx (by simp)).trans hI.rcx,
      ← BitVec.ofNat_add, Nat.add_comm 2 i]
  have hrsi5 : reg st5.data .rsi = reg m0 .rcx + BitVec.ofNat 64 (16 + 16 * (i + 2)) := by
    rw [show reg st5.data .rsi = _ from hm5.regs .rsi _ hsi5]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st4.data.regs.get64 .rsi = _ from
      ((hk4.reg' hm4 (by simp)).trans hrsiB).trans hI.rsi,
      BitVec.add_comm (BitVec.ofNat 64 32), NativeRustcVm.addr_add_add,
      show 16 + 16 * i + 32 = 16 + 16 * (i + 2) by omega]
  have K5 : ∀ r ∈ [Reg64.rax, .rdx, .rbx, .rbp, .r13, .r14, .r15, .rsp],
      reg st5.data r = reg st.data r := fun r hr ↦
    (hk5.reg' hm5 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h | h | h <;> simp [h])).trans (K4 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h | h | h | h <;> simp [h]))
  have rg5 : Rg m0 st5.data := by
    refine ⟨(K5 .rbx (by simp)).trans hI.rg.rbx, ?_, (K5 .r13 (by simp)).trans hI.rg.r13,
      (K5 .r14 (by simp)).trans hI.rg.r14, (K5 .rbp (by simp)).trans hI.rg.rbp⟩
    exact (hk5.reg' hm5 (by simp)).trans ((hm4.regs .r12 _ h12_4).trans (eval_ptr rfl))
  simp only [PcOk] at hpc5
  change st5.pc = if (SBool.cmp .eq .W64 (.reg .rdx) (.bin .add .W64 (.lit 2) (.reg .rcx))).eval
    (Env.ofMachine st4.data _ (fun _ ↦ 0) 0) then _ else _ at hpc5
  have hc5 : (SBool.cmp .eq .W64 (.reg .rdx) (.bin .add .W64 (.lit 2) (.reg .rcx))).eval
      (Env.ofMachine st4.data [(off (fb m0) (896 + 8 * i0), 16)] (fun _ ↦ 0) 0) =
      decide (2 * (bl.length / 2) = i + 2) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs]
    rw [show st4.data.regs.get64 .rdx = _ from (K4 .rdx (by simp)).trans hI.rdx,
      show st4.data.regs.get64 .rcx = _ from (K4 .rcx (by simp)).trans hI.rcx, ← BitVec.ofNat_add]
    exact beq_of_toNat (toNat_ofNat_lt (n := 2 * (bl.length / 2)) (by omega))
      (toNat_ofNat_lt (n := 2 + i) (by omega)) |>.trans (by rw [Nat.add_comm 2 i])
  rw [hc5] at hpc5
  have hr15 : (reg st5.data .r15).toNat = nf m0 + bl.length := by
    rw [K5 .r15 (by simp)]; exact hI.r15
  have hrax5 : reg st5.data .rax = off (fb m0) (896 + 8 * nf m0) := (K5 .rax (by simp)).trans hI.rax
  by_cases hend : 2 * (bl.length / 2) = i + 2
  · rw [decide_eq_true hend] at hpc5
    simp only [↓reduceIte] at hpc5
    rw [hp.label NativeRustcVmX64.Vm.BusLayout.label_11_at] at hpc5
    refine .done _ (Or.inl ⟨hpc5, bd5, rg5, hrax5, by rw [hrcx5, hend], hr15, ?_⟩)
    rw [hend, show nf m0 + (i + 2) = i0 + 2 by omega]
    exact hsz5
  · rw [decide_eq_false hend] at hpc5
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
    refine .done _ (Or.inr ⟨hpc5.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b8_next)), bd5, rg5, by omega, by omega, hrax5, hrcx5,
      (K5 .rdx (by simp)).trans hI.rdx, hrsi5, hr15, ?_⟩)
    rw [show nf m0 + (i + 2) = i0 + 2 by omega]
    exact hsz5

end

end NativeRustcVmX64.Bus.BusLayout
