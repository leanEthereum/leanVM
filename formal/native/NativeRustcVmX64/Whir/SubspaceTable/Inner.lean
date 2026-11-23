module

public import NativeRustcVmX64.Whir.SubspaceTable.Entry
public import NativeRustcVmX64.Code.Vm.Kmul.Names

/-!
# `subspace_table`'s layer loop (x86-64)

`inner`: a turn of the layer loop of turn `t` (`IInv t j` at `b15a`): word `t + j` squared and
shifted by the last root (two `kmul`s, `b17` stores it); back at the head (`IInv t (j + 1)`) or,
the layer done, at `b18a` (`PInv t`).
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add eval_cmp_eq eval_not eval_xor apart_symm not_inRange_of_apart
  written_region0)

public section

theorem pairWords_len (ps : List (UInt64 × UInt64)) :
    ((pairWords ps).flatMap NativeRustcVm.wordBytes).length = 16 * ps.length := by
  rw [NativeRustcVm.length_wordsBytes, pairWords_length']; omega

theorem tableAt_len' {mu t : Nat} (h : t ≤ mu) : (tableAt mu t).length = t + 1 :=
  tableAt_length h

theorem set_patch {L : List UInt64} {c : Nat} {v : UInt64} (_hc : c < L.length) :
    ∀ k (hk : k < L.length), (L.set c v)[k]'(by rw [List.length_set]; exact hk) =
      if c ≤ k ∧ k < c + 1 then v else L[k] := by
  intro k hk
  rw [List.getElem_set]
  by_cases h : c = k
  · subst h; simp
  · have h2 : ¬(c ≤ k ∧ k < c + 1) := by omega
    simp only [h, h2, ↓reduceIte]

variable [Host] {k : Nat}

theorem hb15 (hp : Placed code k) : b15a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b15Offset) ∧
    b15b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b15Offset + b15a.length) := by
  have h := b15_in_code.trans hp.1 (by simp [b15])
  rw [← List.take_append_drop 2 b15] at h
  exact h.append
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b16Offset) :=
  b16_in_code.trans hp.1 (by simp [b16])
theorem hb17 (hp : Placed code k) : b17.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b17Offset) :=
  b17_in_code.trans hp.1 (by simp [b17])

omit [Host] in
/-- Frame words from `8` on kept by a block ending in a call and the call. -/
theorem keepc [Labels] {m0 : MachineData} (hS : StackOk m0 subspaceTableStack) {N : Nat}
    (hle : 848 + N ≤ subspaceTableStack) {env : Env} {Sy : SState} {d d1 d2 : MachineData}
    (hm : Match env Sy d1) (hwf : env.WF)
    (hr0 : env.regions[0]? = some (stackBelow m0 848, 848 + 8)) (hd : env.mem0 = d.dmem)
    (hw : ∀ w ∈ Sy.mem, w.r = 0 ∧ w.off + w.n ≤ 8) (hsp : rspOf d1 = stackBelow m0 848)
    (hso : SameOutside d1.dmem d2.dmem (InRange (stackBelow d1 N) N)) {o : Nat}
    {bs : List UInt8} (h8 : 8 ≤ o) (hlen : o + bs.length ≤ 856)
    (h : NativeRustcVm.BytesAt d.dmem (fbOf m0 + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt d2.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
  keep_call hm hwf hr0 hd hw hS hsp hle hso h8 hlen h

/-- **A turn of the layer loop.** -/
theorem inner (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) {t j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b15Offset)) (hI : IInv m0 t j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b15Offset) ∧ IInv m0 t (j + 1) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b18Offset) ∧ PInv m0 t s.data)) st := by
  have hpre' := hpre
  obtain ⟨hS, hout, _⟩ := hpre'
  obtain ⟨hF, -, hlek, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hsl := slots_ok
  have hfr := hI.tn.fr
  have hmu := hI.tn.hmu
  have ht := hI.ht
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have hll := layer_len m0 t
  have hil : (innerL (layerAt (muOf m0) t) t (t + j)).length = muOf m0 := by
    rw [innerL_length _ _ _ (by omega), hll]
  have hlb : ((innerL (layerAt (muOf m0) t) t (t + j)).flatMap NativeRustcVm.wordBytes).length =
      8 * muOf m0 := by rw [NativeRustcVm.length_wordsBytes, hil]
  have htl : t ≤ muOf m0 := by omega
  have hpl := pairWords_len (tableAt (muOf m0) t)
  rw [tableAt_len' htl] at hpl
  -- `b15a`: word `t + j`
  have hrd : Readable st.data (fbOf m0 + BitVec.ofNat 64 (552 + 8 * (t + j))) 8 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr.kept
  have hwf : (Env.ofMachine st.data [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * (t + j)), 8)]).WF :=
    Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * (t + j)), 8)])
      stS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      show BinOp.apply .add .W64 (reg st.data .rbx) (reg st.data .r14) = _ + BitVec.ofInt 64 0
      rw [add64, hI.rbx, hI.r14, addr_add, show BitVec.ofInt 64 0 = 0#64 from rfl,
        BitVec.add_zero]
      congr 2
      omega, trivial⟩
  refine exec_at (hb15 hp).1 run_b15a hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block hm hm1 hwf rfl (after_eq run_b15a ▸ b15a_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hv : (innerL (layerAt (muOf m0) t) t (t + j))[t + j]'(by omega) =
      (layerAt (muOf m0) t)[t + j]'(by omega) := innerL_getElem (by omega)
  have hval : reg st1.data .r12 = ((layerAt (muOf m0) t)[t + j]'(by omega)).toBitVec := by
    refine (hm1.regs .r12 _ rfl).trans ?_
    rw [eval_load, load8_eq, ← hv]
    have h := NativeRustcVm.WordsAt.getElem hI.layer (i := t + j) (by omega)
    rw [addr_add] at h
    show (wordOf st.data.dmem (fbOf m0 + BitVec.ofNat 64 (552 + 8 * (t + j)) + BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, NativeRustcVm.wordOf_of_wordAt h]
  have e1 : ∀ R ∈ [Reg64.rbx, .rbp, .r14, .r15], reg st1.data R = reg st.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  -- `b15b`: `kmul(v, v)`
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b15Offset + b15a.length) := hpc1
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b16Offset)).toBitVec) hS hF
  refine exec_at (hb15 hp).2 run_b15b hwf2 (fun _ _ ↦ rfl) hpc1' hfr1.mid_match fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hsp2, hw2⟩ := after_eq run_b15b ▸ b15b_call
  have hrsp2 := rsp_call hm2 hsp2
  refine Frame.call hkmul hfr1 hS hlek (L := 800) (by decide) hsl (out_one hout) hwf2
    hfr1.mid_match hm2 hpc2 hk2 hsp2 (fun w hw ↦ ⟨(hw2 w hw).1, by have := (hw2 w hw).2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm2.kept hwf2 p (hfr1.kept p h)) hrsp2 hlek)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st3 hpc3 hfr3 ⟨hax3, hso3, hsv3⟩ ↦ ?_
  have k3 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 856 →
      NativeRustcVm.BytesAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h8 hl h ↦ keepc hS hlek hm2 hwf2 rfl rfl hw2 hrsp2 hso3 h8 hl (hd1 ▸ h)
  have hsq : reg st3.data .rax =
      (kmul ((layerAt (muOf m0) t)[t + j]'(by omega)) ((layerAt (muOf m0) t)[t + j]'(by omega))).toBitVec := by
    rw [hax3, show reg st2.data .rdi = reg st1.data .r12 from hm2.regs .rdi _ rfl,
      show reg st2.data .rsi = reg st1.data .r12 from hm2.regs .rsi _ rfl, hval,
      UInt64.ofBitVec_toBitVec]
  have e3 : ∀ R ∈ [Reg64.rbx, .rbp, .r12, .r14, .r15], reg st3.data R = reg st1.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl <;>
      exact (hsv3.1 _ rfl).trans (Match.reg_eq hfr1.mid_match hm2 rfl rfl)
  -- `b16`: `kmul(last, v)`
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b16Offset) := hpc3
  have hwf4 := hfr3.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b17Offset)).toBitVec) hS hF
  refine exec_at (hb16 hp) run_b16 hwf4 (fun _ _ ↦ rfl) hpc3' hfr3.mid_match fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hk4, hsp4, hw4⟩ := after_eq run_b16 ▸ b16_call
  have hrsp4 := rsp_call hm4 hsp4
  refine Frame.call hkmul hfr3 hS hlek (L := 800) (by decide) hsl (out_one hout) hwf4
    hfr3.mid_match hm4 hpc4 hk4 hsp4 (fun w hw ↦ ⟨(hw4 w hw).1, by have := (hw4 w hw).2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm4.kept hwf4 p (hfr3.kept p h)) hrsp4 hlek)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st5 hpc5 hfr5 ⟨hax5, hso5, hsv5⟩ ↦ ?_
  have k5 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 856 →
      NativeRustcVm.BytesAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h8 hl h ↦ keepc hS hlek hm4 hwf4 rfl rfl hw4 hrsp4 hso5 h8 hl h
  have hlr : reg st5.data .rax = (kmul (lastAt (layerAt (muOf m0) t) t)
      ((layerAt (muOf m0) t)[t + j]'(by omega))).toBitVec := by
    rw [hax5, show reg st4.data .rdi = reg st3.data .r15 from hm4.regs .rdi _ rfl,
      show reg st4.data .rsi = reg st3.data .r12 from hm4.regs .rsi _ rfl,
      e3 .r15 (by simp), e3 .r12 (by simp), e1 .r15 (by simp), hI.r15, hval,
      UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
  have hr13 : reg st5.data .r13 = reg st3.data .rax :=
    (hsv5.1 .r13 rfl).trans (hm4.regs .r13 _ rfl)
  have e5 : ∀ R ∈ [Reg64.rbx, .rbp, .r14], reg st5.data R = reg st.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;>
      exact (hsv5.1 _ rfl).trans ((Match.reg_eq hfr3.mid_match hm4 rfl rfl).trans
        ((e3 _ (by simp)).trans (e1 _ (by simp))))
  -- `b17`: the word stored
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b17Offset) := hpc5
  have hrd6 : Readable st5.data (fbOf m0 + BitVec.ofNat 64 (552 + 8 * (t + j))) 8 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr5.kept
  have hwf6 : (Env.ofMachine st5.data [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * (t + j)), 8)]).WF :=
    Env.wf_of ⟨⟨hrd6.1, hrd6.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm6 : Match (Env.ofMachine st5.data [(fbOf m0 + BitVec.ofNat 64 (552 + 8 * (t + j)), 8)])
      stS st5.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨by
      show BinOp.apply .add .W64 (reg st5.data .rbx) (reg st5.data .r14) = _ + BitVec.ofInt 64 0
      rw [add64, e5 .rbx (by simp), e5 .r14 (by simp), hI.rbx, hI.r14, addr_add,
        show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      congr 2
      omega, trivial⟩
  refine exec_at (hb17 hp) run_b17 hwf6 (by intro l h; cases h) hpc5' hm6 fun st6 hm7 hpc6 ↦ ?_
  obtain ⟨⟨hk7, hw7⟩, hv7⟩ := after_eq run_b17 ▸ b17_write
  have hfr6 : Fr m0 st6.data := hfr5.of_write hm6 hm7 hwf6 rfl hk7 (r := 0) rfl le_rfl hw7
    (fun p h ↦ .inr (inRange_stack_of hS hF (L := 800) (by decide) (by omega) h))
    (slot_not_in hS hF (by omega) (by omega) hsl)
  have hso7 := same_region_le hm7 hwf6 (r := 0) rfl le_rfl hw7
  have k7 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 552 + 8 * (t + j) →
      NativeRustcVm.BytesAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun hl h ↦ NativeRustcVm.BytesAt.of_sameOutside h hso7 fun i hi ↦ by
      rw [addr_add]
      unfold fbOf
      rw [inRange_fb_iff hS hF (by omega) (by omega) (by omega)]
      omega
  have kk : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 552 →
      NativeRustcVm.BytesAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h8 hl h ↦ k7 (by omega) (k5 h8 (by omega) (k3 h8 (by omega) h))
  have hnew : WordAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 (552 + 8 * (t + j)))
      (sqStep (lastAt (layerAt (muOf m0) t) t) ((layerAt (muOf m0) t)[t + j]'(by omega))) := by
    have := wordAt_of_write hm7 (r := 0) (o := 0) rfl (by decide) hv7
    rw [NativeRustcVm.addr_add_zero, eval_xor, eval_reg, eval_reg, Env.ofMachine_regs,
      Env.ofMachine_regs, show st5.data.regs.get64 .rax = _ from hlr,
      show st5.data.regs.get64 .r13 = _ from hr13.trans hsq, ← UInt64.toBitVec_xor,
      UInt64.ofBitVec_toBitVec, UInt64.xor_comm] at this
    exact this
  have hlay6 : WordsAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 552)
      (innerL (layerAt (muOf m0) t) t (t + j + 1)) := by
    have hL5 : WordsAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 552)
        (innerL (layerAt (muOf m0) t) t (t + j)) := k5 (by omega) (by rw [hlb]; omega)
          (k3 (by omega) (by rw [hlb]; omega) hI.layer)
    rw [← innerL_set (show t ≤ t + j by omega) (by omega)]
    refine wordsAt_patch (c := t + j) (n := 1) (f := fun _ ↦ sqStep (lastAt (layerAt (muOf m0) t) t)
      ((layerAt (muOf m0) t)[t + j]'(by omega))) hL5
      (NativeRustcVm.NoWrap.sub hfnw (by rw [hil]; omega)) ?_ (fun i hi ↦ ?_) (by omega)
      (by rw [List.length_set]) (set_patch (by omega))
    · rw [addr_add]; exact hso7
    · rw [show i = 0 by omega, Nat.add_zero, addr_add]; exact hnew
  have hr14' : reg st6.data .r14 = BitVec.ofNat 64 (8 * (j + 1)) := by
    refine (hm7.regs .r14 _ rfl).trans ?_
    rw [eval_add, eval_lit, eval_reg, Env.ofMachine_regs, show st5.data.regs.get64 .r14 = _ from
      (e5 .r14 (by simp)).trans hI.r14, ← BitVec.ofNat_add]
    congr 1
    omega
  have hmu8 : 8 * (muOf m0 - t) < 2 ^ 64 := by omega
  simp only [PcOk] at hpc6
  rw [eval_not, eval_cmp_eq, eval_add, eval_lit, eval_reg, eval_reg, Env.ofMachine_regs,
    Env.ofMachine_regs, show st5.data.regs.get64 .rbp = _ from (e5 .rbp (by simp)).trans hI.rbp,
    show st5.data.regs.get64 .r14 = _ from (e5 .r14 (by simp)).trans hI.r14, ← BitVec.ofNat_add,
    ofNat_beq hmu8 (by omega)] at hpc6
  obtain ⟨hT, hF6⟩ := Arrays.pc_cond hpc6
  have htn : Turn m0 st6.data := ⟨hfr6, kk (by omega) (by rw [hlw]; omega) hI.tn.out,
    kk (by omega) (by rw [hlw]; omega) hI.tn.mu, kk (by omega) (by rw [hlw]; omega) hI.tn.mu8, hmu⟩
  have htt := kk (by omega) (by rw [hlw]; omega) hI.tt
  have htl6 := kk (by omega) (by rw [hlw]; omega) hI.tl
  have htab := kk (by omega) (by rw [hpl]; omega) hI.table
  have e6 : ∀ R ∈ [Reg64.rbx, .rbp, .r15], reg st6.data R = reg st.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact (Match.reg_eq hm6 hm7 rfl rfl).trans (e5 .rbx (by simp))
    · exact (Match.reg_eq hm6 hm7 rfl rfl).trans (e5 .rbp (by simp))
    · exact (Match.reg_eq hm6 hm7 rfl rfl).trans ((hsv5.1 .r15 rfl).trans
        ((Match.reg_eq hfr3.mid_match hm4 rfl rfl).trans ((e3 .r15 (by simp)).trans
          (e1 .r15 (by simp)))))
  by_cases hlast : t + j + 1 = muOf m0
  · refine .done _ (.inr ⟨(hF6 (by rw [Bool.not_eq_true', decide_eq_false_iff_not, not_not]; omega)),
      htn, by omega, htt, htl6, ?_, htab, (e6 .rbx (by simp)).trans hI.rbx⟩)
    rw [layerAt, ← innerL_end, hll]
    rw [← hlast] at hlay6 ⊢
    exact hlay6
  · have hlay6' : WordsAt st6.data.dmem (fbOf m0 + BitVec.ofNat 64 552)
        (innerL (layerAt (muOf m0) t) t (t + (j + 1))) := by
      rw [show t + (j + 1) = t + j + 1 by omega]; exact hlay6
    refine .done _ (.inl ⟨(hT (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; omega)).trans
      (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_14_at), htn, by omega, htt, htl6, hlay6', htab, (e6 .rbx (by simp)).trans hI.rbx,
      (e6 .rbp (by simp)).trans hI.rbp, hr14', (e6 .r15 (by simp)).trans hI.r15⟩)

end

end NativeRustcVmX64.Whir.SubspaceTable
