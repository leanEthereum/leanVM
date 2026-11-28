module

public import NativeRustcVmX64.Bus.BusLayout.Place
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `bus_layout`: the layout copied out, the epilogue (x86-64)

From `NativeRustcVmX64.Vm.BusLayout.label_26` (`finish`): `b33` stores the framework's count at `16` (the layout at `8` is
then `busLayout`'s, `built`) and copies its 888 bytes out with `memcpy`
(`busLayoutWAt_transfer`); `b34` sets the tag `1`; `b35` returns.
-/

namespace NativeRustcVmX64.Bus.BusLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmX64.Vm.BusLayout
open LeanVM.Protocol.Verifier (Placement)

public section

/-! ## The layout moved -/

theorem wordAt_transfer {d d' : DataMem} {a b : BitVec 64} {n o : Nat} {w : UInt64}
    (htr : ∀ i < n, ∀ x, d.get? (off a i) = some x → d'.get? (off b i) = some x)
    (ho : o + 8 ≤ n) (h : NativeRustcVm.WordAt d (off a o) w) :
    NativeRustcVm.WordAt d' (off b o) w := fun i hi ↦ by
  have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
  rw [off_add]
  exact htr (o + i) (by omega) _ (by rw [← off_add]; exact h i hi)

theorem placementAt_transfer {d d' : DataMem} {a b : BitVec 64} {n o : Nat} {p : Placement}
    (htr : ∀ i < n, ∀ x, d.get? (off a i) = some x → d'.get? (off b i) = some x)
    (ho : o + 16 ≤ n) (h : PlacementAt d (off a o) p) : PlacementAt d' (off b o) p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, wordAt_transfer htr (by omega) h3, ?_⟩
  rw [off_off] at h4 ⊢
  exact wordAt_transfer htr (by omega) h4

/-- **A side's layout moved** with its 888 bytes. -/
theorem busLayoutWAt_transfer {d d' : DataMem} {a b : BitVec 64} {BL : BusLayoutW}
    (htr : ∀ i < 888, ∀ x, d.get? (off a i) = some x → d'.get? (off b i) = some x)
    (h : BusLayoutWAt d a BL) : BusLayoutWAt d' b BL := by
  obtain ⟨hdl, hd, ⟨hfs, hfl, hfi⟩, ⟨hts, htl, hti⟩⟩ := h
  refine ⟨hdl, ?_, ⟨hfs, wordAt_transfer htr (by omega) hfl, fun i hi ↦ ?_⟩,
    ⟨hts, wordAt_transfer htr (by omega) htl, fun i hi ↦ ?_⟩⟩
  · have := wordAt_transfer (o := 0) htr (by omega) (by rw [off_zero]; exact hd)
    rwa [off_zero] at this
  · have := hfi i hi
    rw [off_off] at this ⊢
    exact placementAt_transfer htr (by unfold NativeRustcVm.Bus.placementBytes; omega) this
  · have := hti i hi
    unfold maxBlocks at hts
    rw [off_off] at this ⊢
    exact placementAt_transfer htr (by unfold NativeRustcVm.Bus.placementBytes; omega) this

/-- **The layout built** at `8` in the frame: every placement pushed, the framework's count at
`16`. -/
theorem built [Labels] {d : DataMem} {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) (rows : Array Nat)
    (hp : Part d L bl m0 (nf m0 + bl.length))
    (h16 : NativeRustcVm.WordAt d (off (fb m0) 16) (nf m0).toUInt64) :
    BusLayoutWAt d (off (fb m0) 8)
      (busLayout (fws m0) (bl.map (blockW L.tableLogHeights rows)).toArray) := by
  have hnf : nf m0 ≤ 3 := hpre.2.1
  have hbl : bl.length ≤ 51 := hpre.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [busLayout_depth]; exact pre_depth_lt hpre
  · rw [busLayout_depth]; exact hp.depth
  · rw [busLayout_framework]
    refine ⟨by simp [fws_size, hnf], ?_, fun j hj ↦ ?_⟩
    · simp only [List.size_toArray, List.length_map, List.length_range, fws_size]
      rw [off_off]
      exact h16
    · have hj' : j < nf m0 := by simpa [fws_size] using hj
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      have := hp.fw j (by omega)
      rw [off_off, off_off, show 8 + (8 + (8 + NativeRustcVm.Bus.placementBytes * j)) =
        24 + 16 * j by unfold NativeRustcVm.Bus.placementBytes; omega]
      exact this
  · rw [busLayout_tables]
    refine ⟨by simp [hbl, maxBlocks], ?_, fun j hj ↦ ?_⟩
    · simp only [List.size_toArray, List.length_map, List.length_range]
      have := hp.tlen
      rw [Nat.add_sub_cancel_left] at this
      rw [off_off]
      exact this
    · have hj' : j < bl.length := by simpa using hj
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, fws_size]
      have := hp.tb j (by omega)
      rw [off_off, off_off, show 8 + (64 + (8 + NativeRustcVm.Bus.placementBytes * j)) =
        80 + 16 * j by unfold NativeRustcVm.Bus.placementBytes; omega]
      exact this

/-- Words of the frame kept where memory changed only at `[0, 8)` and `[16, 24)`. -/
theorem part_keep16 {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    {d d' : DataMem} {i : Nat} (hst : StackOk m0 busLayoutStack) (hnf : nf m0 ≤ 3)
    (hbl : bl.length ≤ 51) (hi : i ≤ nf m0 + bl.length) (h : Part d L bl m0 i)
    (hs : NativeRustcVm.SameOutside d d' (fun q ↦ NativeRustcVm.InRange (off (fb m0) 0) 8 q ∨
      NativeRustcVm.InRange (off (fb m0) 16) 8 q)) : Part d' L bl m0 i := by
  have hN : 1808 ≤ busLayoutStack := by decide
  have hrsp := hst.1
  have htop := hst.2.1
  have hb : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  have kw : ∀ {o : Nat} {w : UInt64}, 8 ≤ o ∧ o + 8 ≤ 16 ∨ 24 ≤ o ∧ o + 8 ≤ 1808 →
      NativeRustcVm.WordAt d (off (fb m0) o) w → NativeRustcVm.WordAt d' (off (fb m0) o) w :=
    fun {o} {w} ho h ↦ bytesAt_congr h fun t ht ↦ by
      have ht' : t < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using ht
      rw [off_add]
      refine hs _ fun hq ↦ ?_
      rcases hq with hq | hq <;> rw [inRange_off_iff (by omega) (by omega)] at hq <;> omega
  have kp : ∀ {o : Nat} {p : Placement}, 24 ≤ o → o + 16 ≤ 1808 →
      PlacementAt d (off (fb m0) o) p → PlacementAt d' (off (fb m0) o) p :=
    fun {o} {p} h1 h2 h ↦ ⟨h.1, h.2.1, kw (.inr ⟨h1, by omega⟩) h.2.2.1, by
      rw [off_off]
      exact kw (.inr ⟨by omega, by omega⟩) (by rw [← off_off]; exact h.2.2.2)⟩
  exact ⟨kw (.inl ⟨le_rfl, le_rfl⟩) h.depth, kw (.inr ⟨by omega, by omega⟩) h.tlen,
    fun j hj ↦ kp (by omega) (by
      have : j < nf m0 := lt_of_lt_of_le hj (Nat.min_le_right _ _); omega) (h.fw j hj),
    fun j hj ↦ kp (by omega) (by omega) (h.tb j hj)⟩

variable [Host] {k : Nat}

/-- **The epilogue**: from `NativeRustcVmX64.Vm.BusLayout.label_26`, every placement pushed, to the return. -/
theorem finish (hp : Placed code k)
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {L : LayoutW}
    {bl : List NativeRustcVm.Data.Block} {m0 : MachineData} (hpre : BusLayoutPre L bl m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b33Offset)) (hE : PEnd L bl m0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ BusLayoutPost L bl m0 st'.data) st := by
  have hst := hpre.1
  have hN : 1808 ≤ busLayoutStack := by decide
  have hnf3 : nf m0 ≤ 3 := hpre.2.1
  have hmb : bl.length ≤ 51 := hpre.2.2.2.2.2.1
  have hrsp := hst.1
  have htop := hst.2.1
  have hbase : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  have hO : InOk m0 (reg m0 .rdi) optBusLayoutBytes busLayoutStack :=
    hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hOB : optBusLayoutBytes = 896 := by decide
  rw [hOB] at hO
  have hOn : (reg m0 .rdi).toNat + 896 ≤ 2 ^ 64 := hO.1.2
  have hA : NativeRustcVm.Apart (reg m0 .rdi) 896 (fb m0) (1808 + 8) :=
    apart_frame hO.2 (by omega) hN
  unfold NativeRustcVm.Apart at hA
  have ho8 : (off (reg m0 .rdi) 8).toNat = (reg m0 .rdi).toNat + 8 := toNat_off (by omega)
  have hf8 : (off (fb m0) 8).toNat = (fb m0).toNat + 8 := toNat_off (by omega)
  have hbd := hE.bd
  -- `b33`: the framework's count; `memcpy` of the layout.
  have hwf0 := wf_got hpre hbd.fr.kept (l := "memcpy") (by simp) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b33Offset + b33.length)).toBitVec)
  refine exec_at (infix_of b33_in_code (by simp [b33]) hp) run_b33 hwf0 (fun _ _ ↦ rfl) hpc
    (match_got hpre hbd.same (by simp) hbd.fr.sp)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hw1, hwr1, hbd1, hdi1, hsi1, hdx1, hk1⟩ := after_eq run_b33 ▸ ok_b33
  have bd1 := Body.of_block hst hN hbd hwf0 hm1 hmid1 hw1 slots_le
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (fun q ↦ NativeRustcVm.InRange (off (fb m0) 0) 8 q ∨
        NativeRustcVm.InRange (off (fb m0) 16) 8 q) := fun q hq ↦ hm1.get?_mem0 hwf0 fun hW ↦
    hq (by
      obtain ⟨w, hw, b, sz, hb, j, h1, h2, rfl⟩ := written_off hwf0 hW
      rw [hw1 w hw] at hb
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      rcases hbd1 w hw with h | h
      · exact .inl ((inRange_off_iff (by omega) (by omega)).mpr ⟨by omega, by omega⟩)
      · exact .inr ((inRange_off_iff (by omega) (by omega)).mpr ⟨by omega, by omega⟩))
  have h16 : NativeRustcVm.WordAt st1.data.dmem (off (fb m0) 16) (nf m0).toUInt64 := by
    refine wordAt_write_eq hm1 (b := fb m0) (o := 16) rfl (by omega) (.reg .rdx)
      (hwr1.find (by simp)) ?_
    apply BitVec.eq_of_toNat_eq
    rw [toNat_toUInt64' (by omega)]
    show (reg st.data .rdx).toNat = _
    rw [hE.rdx]
    exact toNat_ofNat_lt (by omega)
  have hpart1 : Part st1.data.dmem L bl m0 (nf m0 + bl.length) :=
    part_keep16 hst hnf3 hmb le_rfl hE.part hs1
  have edi1 : reg st1.data .rdi = off (reg m0 .rdi) 8 := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hdi1]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .rbx = _ from hE.rbx]
  have esi1 : reg st1.data .rsi = off (fb m0) 8 := (hm1.regs .rsi _ hsi1).trans (eval_ptr0 8)
  have edx1 : (reg st1.data .rdx).toNat = 888 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hdx1]; rfl
  have hreg := frame_region hst bd1.fr.kept (o := 8) (n := 888) (by omega)
  have hpreM : MemcpyPre st1.data := by
    refine ⟨bd1.stackOk hst (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show NativeRustcVm.Mapped _ _ _
      rw [edi1, edx1]
      exact mapped_off (Mapped.keeps hO.1.1 bd1.fr.kept) (by omega)
    · show NativeRustcVm.Mapped _ _ _
      rw [esi1, edx1]; exact hreg.1
    · show NativeRustcVm.NoWrap _ _
      unfold NativeRustcVm.NoWrap; rw [edi1, edx1, ho8]; omega
    · show NativeRustcVm.NoWrap _ _
      rw [esi1, edx1]; exact hreg.2
    · show NativeRustcVm.Apart _ _ _ _
      unfold NativeRustcVm.Apart; rw [edi1, esi1, edx1, ho8, hf8]; omega
    · show NativeRustcVm.Apart _ _ _ _
      have hfb : (stackBelow m0 1808).toNat = (fb m0).toNat := rfl
      unfold NativeRustcVm.Apart
      rw [edi1, edx1, ho8, bd1.sp0, hfb]
      omega
  refine call_then hpc1 hmc hpreM fun st2 hpc2 hrsp2 ⟨_, hcp2, hso2, hsv2⟩ ↦ ?_
  rw [edi1, esi1, edx1] at hcp2
  rw [edi1, edx1] at hso2
  have hout : ∀ q, NativeRustcVm.InRange (off (reg m0 .rdi) 8) 888 q →
      NativeRustcVm.InRange (reg m0 .rdi) 896 q := fun q h ↦ inRange_of_off hOn (by omega) h
  have hnwF : NativeRustcVm.NoWrap (fb m0) (1808 + 8) := frame_noWrap hst hN
  have hOF : ∀ q, NativeRustcVm.InRange (reg m0 .rdi) 896 q →
      ¬NativeRustcVm.InRange (fb m0) (1808 + 8) q := fun q h1 h2 ↦ by
    rw [inRange_iff' (show NativeRustcVm.NoWrap _ _ from hOn)] at h1
    rw [inRange_iff' hnwF] at h2
    omega
  have hfr2 : Frame m0 1808 slots 8 st2.data :=
    Frame.call bd1.fr hsv2 hrsp2 hso2 (fun q hq ↦ hOF q (hout q hq)) hnwF slots_le
  have hBL2 : ∀ rows, BusLayoutWAt st2.data.dmem (off (reg m0 .rdi) 8)
      (busLayout (fws m0) (bl.map (blockW L.tableLogHeights rows)).toArray) := fun rows ↦
    busLayoutWAt_transfer (fun i hi x hx ↦ by
      have h := hcp2 i (by simp [NativeRustcX64.bytesOf, hi])
      simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range] at h
      rw [show (off (fb m0) 8 + BitVec.ofNat 64 i) = off (off (fb m0) 8) i from rfl, hx,
        Option.getD_some] at h
      exact h) (built hpre rows hpart1 h16)
  have hbx2 : reg st2.data .rbx = reg m0 .rdi := by
    refine (hsv2.1 .rbx rfl).trans ?_
    rw [← hE.rbx]
    exact hk1.reg' hm1 (by simp)
  -- `b34`: the tag; `b35`: the epilogue.
  have hOr : Readable m0 (reg m0 .rdi) 8 := ⟨fun t ht ↦ hO.1.1 t (by omega), by
    show NativeRustcVm.NoWrap _ _; unfold NativeRustcVm.NoWrap; omega⟩
  have hOs : NativeRustcVm.Apart (reg m0 .rdi) 8 (stackBelow m0 busLayoutStack)
      (busLayoutStack + 8) := by
    have := hO.2
    unfold OffStack NativeRustcX64.Apart at this
    unfold NativeRustcVm.Apart
    omega
  have hwf3 := wf1 (d := st2.data) hst hN hfr2.kept hOr hOs (vars := fun _ ↦ 0) (ret := 0)
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b34Offset) :=
    hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b33_next))
  refine exec_at (infix_of b34_in_code (by simp [b34]) hp) run_b34 hwf3 nofun hpc2'
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr2.rsp_eval, known_ptr rfl hbx2, trivial⟩
      trivial trivial trivial)
    fun st3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [← after_eq run_b34] at hm3
  refine exec_at (infix_of b35_in_code (by simp [b35]) hp) run_b35 hwf3 nofun hpc3 hm3
    fun st4 hm4 hpc4 ↦ ?_
  have ok := ok_end
  rw [show eT = _ from after_eq run_b35] at ok
  obtain ⟨hepi, hw4, hwr4⟩ := ok
  obtain ⟨hsv4, hrsp4⟩ := Frame.epilogue hfr2 hwf3 hm4 hepi
  have hso4 : NativeRustcVm.SameOutside st2.data.dmem st4.data.dmem
      (NativeRustcVm.InRange (reg m0 .rdi) 8) :=
    sameOutside_region hwf3 hm4 (r := 1) rfl fun w hw ↦ ⟨(hw4 w hw).1, Nat.zero_le _,
      (hw4 w hw).2⟩
  simp only [PcOk] at hpc4
  refine .done _ ⟨by rw [hpc4]; exact hfr2.load_ret hst hN, hrsp4, fun rows ↦ ⟨?_, ?_⟩, ?_, hsv4⟩
  · have := wordAt_write_eq hm4 (b := reg m0 .rdi) (o := 0) rfl (by omega) (.lit 1)
      (hwr4.find (by simp)) (w := 1) rfl
    rwa [off_zero] at this
  · refine busLayoutWAt_transfer (fun i hi x hx ↦ ?_) (hBL2 rows)
    rw [← hx]
    refine hso4 _ fun hq ↦ ?_
    have h0 := inRange_off_iff (b := reg m0 .rdi) (o := 0) (n := 8) (j := 8 + i) (by omega)
      (by omega)
    rw [off_zero] at h0
    rw [off_off, h0] at hq
    omega
  · intro q hq
    simp only [not_or] at hq
    have hq1 : ¬NativeRustcVm.InRange (reg m0 .rdi) 8 q := fun h ↦ hq.1 (by
      show NativeRustcVm.InRange _ _ _
      rw [hOB, inRange_iff' (show NativeRustcVm.NoWrap _ _ from hOn)]
      rw [inRange_iff' (show NativeRustcVm.NoWrap _ 8 by unfold NativeRustcVm.NoWrap; omega)] at h
      omega)
    have hq2 : ¬NativeRustcVm.InRange (off (reg m0 .rdi) 8) 888 q := fun h ↦ hq.1 (by
      show NativeRustcVm.InRange _ _ _
      rw [hOB]
      exact hout q h)
    exact (hso4 q hq1).trans ((hso2 q hq2).trans (bd1.same q hq.2))

end

end NativeRustcVmX64.Bus.BusLayout
