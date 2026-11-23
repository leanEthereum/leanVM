module

public import NativeRustcVmX64.Whir.SubspaceTable.Outer
public import NativeRustcVmX64.Code.Vm.Kinv.Names

/-!
# `subspace_table`: the end of a turn (x86-64)

`push`: after the layer loop of turn `t` (`PInv t`, `b18a`), `b18a` loads the turn and the new
root (layer word `t`), `b18b` calls `kinv` on it; turn `30` gives `None` (`b19`, `NoneAt` at
`b23`); else `b20` pushes the pair at the table's end: back at the turns' head (`OInv (t + 1)`)
or, the last turn, at the copy (`Done`, `b21`).
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add eval_cmp_eq eval_not eval_shl_lit apart_symm not_inRange_of_apart
  written_region0)

public section

/-- The new root's address in `b18a`. -/
theorem root_addr (b : BitVec 64) (t : Nat) :
    b + BitVec.ofNat 64 8 + BitVec.ofNat 64 t * BitVec.ofNat 64 8 + BitVec.ofNat 64 544 =
      b + BitVec.ofNat 64 (552 + 8 * t) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- The pushed pair's address in `b20`. -/
theorem pair_addr (b : BitVec 64) (n : Nat) :
    b + BitVec.ofNat 64 56 + BitVec.ofNat 64 n <<< 4 = b + BitVec.ofNat 64 (56 + 16 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem ofNat_succ (n : Nat) : BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) :=
  (BitVec.ofNat_add n 1).symm

variable [Host] {k : Nat}

theorem hb23 (hp : Placed code k) : b23.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b23Offset) :=
  b23_in_code.trans hp.1 (by simp [b23])

/-- **The end of turn `t`**: `kinv` of the new root; `None` at turn `30`, else the pair pushed. -/
theorem push (hp : Placed code k) (hkinv : Spec (Labels.label NativeRustcVmX64.Vm.Kinv.entryLabel) KinvPre KinvPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) {t : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b18Offset)) (hI : PInv m0 t st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b14Offset) ∧ OInv m0 (t + 1) s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b21Offset) ∧ Done m0 s.data) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b23Offset) ∧ NoneAt m0 s.data)) st := by
  have hpre' := hpre
  obtain ⟨hS, hout, _⟩ := hpre'
  obtain ⟨hF, hlek, -, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hsl := slots_ok
  have hfr := hI.tn.fr
  have hmu := hI.tn.hmu
  have ht := hI.ht
  have hmu64 : muOf m0 < 2 ^ 64 := (reg m0 .rsi).isLt
  have hmuv : reg m0 .rsi = BitVec.ofNat 64 (muOf m0) := reg_ofNat _
  have hlw : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  have hll := layer_len m0 (t + 1)
  have hlb : ((layerAt (muOf m0) (t + 1)).flatMap NativeRustcVm.wordBytes).length =
      8 * muOf m0 := by rw [NativeRustcVm.length_wordsBytes, hll]
  have hpl := pairWords_len (tableAt (muOf m0) t)
  rw [tableAt_len' (by omega)] at hpl
  have hlt : t < (layerAt (muOf m0) (t + 1)).length := by rw [hll]; exact ht
  have hroot : WordAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 (552 + 8 * t))
      ((layerAt (muOf m0) (t + 1))[t]'hlt) := by
    have h := NativeRustcVm.WordsAt.getElem hI.layer hlt
    rwa [addr_add] at h
  have hfb : ∀ {j : Nat}, j < 856 → (fbOf m0 + BitVec.ofNat 64 j).toNat = (rspOf m0).toNat - 848 + j :=
    fun hj ↦ fb_toNat hS hF hj
  -- `b18a`: the turn, the new root
  have hrd0 : Readable st.data (fbOf m0) 48 :=
    Readable.keep (Readable.mono (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr.kept
  have hrd1 : Readable st.data (fbOf m0 + BitVec.ofNat 64 (552 + 8 * t)) 8 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr.kept
  let env := Env.ofMachine st.data [(fbOf m0, 48), (fbOf m0 + BitVec.ofNat 64 (552 + 8 * t), 8)]
    (fun _ ↦ 0) 0
  have hwf : env.WF := Env.wf_of ⟨⟨hrd0.1, hrd0.2⟩, ⟨hrd1.1, hrd1.2⟩, trivial⟩
    (List.pairwise_pair.mpr (by
      show (fbOf m0).toNat + 48 ≤ (fbOf m0 + BitVec.ofNat 64 (552 + 8 * t)).toNat ∨ _
      rw [hfb (by omega)]
      unfold fbOf
      rw [hfe]
      omega))
  have hl40 : env.load 0 40 8 = BitVec.ofNat 64 t :=
    load_word (show WordAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 40) _ from hI.tt)
  have hm : Match env rootS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr.rsp, trivial⟩ trivial trivial ⟨by
      show BinOp.apply .add .W64 (BinOp.apply .add .W64 (fbOf m0 + BitVec.ofNat 64 8)
          (BinOp.apply .mul .W64 (env.load 0 40 8) (BitVec.ofNat 64 8))) (BitVec.ofNat 64 544) =
        fbOf m0 + BitVec.ofNat 64 (552 + 8 * t) + 0#64
      rw [hl40, add64, add64, mul64, BitVec.add_zero]
      exact root_addr _ _, trivial⟩
  refine exec_at (hb18 hp).1 run_b18a hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := hfr.of_block hm hm1 hwf rfl (after_eq run_b18a ▸ b18a_keeps)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hr13_1 : reg st1.data .r13 = BitVec.ofNat 64 t := (hm1.regs .r13 _ rfl).trans hl40
  have hr15_1 : reg st1.data .r15 = ((layerAt (muOf m0) (t + 1))[t]'hlt).toBitVec :=
    (hm1.regs .r15 _ rfl).trans (load_word (by rw [NativeRustcVm.addr_add_zero]; exact hroot))
  have hrbx_1 : reg st1.data .rbx = fbOf m0 + BitVec.ofNat 64 (552 + 8 * t) :=
    (Match.reg_eq (r := .rbx) hm hm1 rfl rfl).trans hI.rbx
  -- `b18b`: `kinv(root)`
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b18Offset + b18a.length) := hpc1
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b19Offset)).toBitVec) hS hF
  refine exec_at (hb18 hp).2 run_b18b hwf2 (fun _ _ ↦ rfl) hpc1' hfr1.mid_match
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hsp2, hw2⟩ := after_eq run_b18b ▸ b18b_call
  have hrsp2 := rsp_call hm2 hsp2
  refine Frame.call hkinv hfr1 hS hlek (L := 800) (by decide) hsl (out_one hout) hwf2
    hfr1.mid_match hm2 hpc2 hk2 hsp2 (fun w hw ↦ ⟨(hw2 w hw).1, by have := (hw2 w hw).2; omega⟩)
    (stackOk_callee hS (fun p h ↦ hm2.kept hwf2 p (hfr1.kept p h)) hrsp2 hlek)
    (fun m' ⟨_, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inr (.inr h))⟩)
    fun st3 hpc3 hfr3 ⟨hax3, hso3, hsv3⟩ ↦ ?_
  have k3 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 856 →
      NativeRustcVm.BytesAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h8 hl h ↦ keepc hS hlek hm2 hwf2 rfl rfl hw2 hrsp2 hso3 h8 hl (hd1 ▸ h)
  have hinv : reg st3.data .rax = (kinv ((layerAt (muOf m0) (t + 1))[t]'hlt)).toBitVec := by
    rw [hax3, show reg st2.data .rdi = reg st1.data .r15 from hm2.regs .rdi _ rfl, hr15_1,
      UInt64.ofBitVec_toBitVec]
  have e3 : ∀ R ∈ [Reg64.rbx, .r13, .r15], reg st3.data R = reg st1.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl <;>
      exact (hsv3.1 _ rfl).trans (Match.reg_eq hfr1.mid_match hm2 rfl rfl)
  -- `b19`: turn `30`
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b19Offset) := hpc3
  refine exec_at (hb19 hp) run_b19 (Env.wf_nil _) (by intro l h; cases h) hpc3' (match_nil _)
    fun st4 hm4 hpc4 ↦ ?_
  have hfr4 := hfr3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b19 ▸ b19_keeps)
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq (Env.wf_nil _) rfl
  have e4 : ∀ R ∈ [Reg64.rax, .rbx, .r13, .r15], reg st4.data R = reg st3.data R := by
    intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> exact Match.reg_eq (match_nil _) hm4 rfl rfl
  have hr13_3 : reg st3.data .r13 = BitVec.ofNat 64 t := (e3 .r13 (by simp)).trans hr13_1
  have k4 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 856 →
      NativeRustcVm.BytesAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h8 hl h ↦ hd4 ▸ k3 h8 hl h
  have hout4 : OutAt m0 st4.data := k4 (by omega) (by rw [hlw]; omega) hI.tn.out
  simp only [PcOk] at hpc4
  rw [eval_cmp_eq, eval_reg, eval_lit, Env.ofMachine_regs,
    show st3.data.regs.get64 .r13 = _ from hr13_3, ofNat_beq (by omega) (by decide)] at hpc4
  obtain ⟨hT4, hF4⟩ := Arrays.pc_cond hpc4
  by_cases h30 : t = 30
  · exact .done _ (.inr (.inr ⟨(hT4 (by rw [decide_eq_true_eq]; exact h30)).trans
      (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_16_at), hfr4, hout4, by omega⟩))
  -- `b20`: the pair pushed
  have ht29 : t ≤ 29 := by omega
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b20Offset) := hF4 (by rw [decide_eq_true_eq]; exact h30)
  have hrd5 : Readable st4.data (fbOf m0 + BitVec.ofNat 64 (56 + 16 * (t + 1))) 16 :=
    Readable.keep (Readable.sub (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr4.kept
  have hrd5' : Readable st4.data (fbOf m0) 48 :=
    Readable.keep (Readable.mono (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr4.kept
  let env6 := Env.ofMachine st4.data
    [(fbOf m0, 48), (fbOf m0 + BitVec.ofNat 64 (56 + 16 * (t + 1)), 16)] (fun _ ↦ 0) 0
  have hwf6 : env6.WF := Env.wf_of ⟨⟨hrd5'.1, hrd5'.2⟩, ⟨hrd5.1, hrd5.2⟩, trivial⟩
    (List.pairwise_pair.mpr (by
      show (fbOf m0).toNat + 48 ≤ (fbOf m0 + BitVec.ofNat 64 (56 + 16 * (t + 1))).toNat ∨ _
      rw [hfb (by omega)]
      unfold fbOf
      rw [hfe]
      omega))
  have hl32 : env6.load 0 32 8 = BitVec.ofNat 64 (t + 1) :=
    load_word (show WordAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 32) _ from
      k4 (by omega) (by rw [hlw]; omega) hI.tl)
  have hl16 : env6.load 0 16 8 = BitVec.ofNat 64 (muOf m0) :=
    (load_word (show WordAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 16) _ from
      k4 (by omega) (by rw [hlw]; omega) hI.tn.mu)).trans hmuv
  have hm6 : Match env6 pushS st4.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr4.rsp, trivial⟩ trivial trivial ⟨by
      show BinOp.apply .add .W64 (fbOf m0 + BitVec.ofNat 64 56)
          ((Sym.bin .shl .W64 (.load 0 32 8) (.lit 4)).eval env6) =
        fbOf m0 + BitVec.ofNat 64 (56 + 16 * (t + 1)) + 0#64
      rw [eval_shl_lit _ (by decide), eval_load, hl32, add64, BitVec.add_zero]
      exact pair_addr _ _, trivial⟩
  refine exec_at (hb20 hp) run_b20 hwf6 (by intro l h; cases h) hpc4' hm6 fun st5 hm7 hpc5 ↦ ?_
  obtain ⟨⟨hk7, hw7⟩, hv0, hv8⟩ := after_eq run_b20 ▸ b20_write
  have hfr5 : Fr m0 st5.data := hfr4.of_write hm6 hm7 hwf6 rfl hk7 (r := 1) rfl le_rfl hw7
    (fun p h ↦ .inr (inRange_stack_of hS hF (L := 800) (by decide) (by omega) h))
    (slot_not_in hS hF (by omega) (by omega) hsl)
  have hso7 := same_region_le hm7 hwf6 (r := 1) rfl le_rfl hw7
  have k7 : ∀ {o : Nat} {bs : List UInt8},
      (o + bs.length ≤ 56 + 16 * (t + 1) ∨ 56 + 16 * (t + 1) + 16 ≤ o) → o + bs.length ≤ 856 →
      NativeRustcVm.BytesAt st4.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun hap hl h ↦ NativeRustcVm.BytesAt.of_sameOutside h hso7 fun i hi ↦ by
      rw [addr_add]
      unfold fbOf
      rw [inRange_fb_iff hS hF (by omega) (by omega) (by omega)]
      omega
  have kk : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o →
      (o + bs.length ≤ 56 + 16 * (t + 1) ∨ 56 + 16 * (t + 1) + 16 ≤ o) → o + bs.length ≤ 856 →
      NativeRustcVm.BytesAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs →
      NativeRustcVm.BytesAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 o) bs :=
    fun h8 hap hl h ↦ k7 hap hl (k4 h8 hl h)
  have hw0 : WordAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 (56 + 16 * (t + 1)))
      ((layerAt (muOf m0) (t + 1))[t]'hlt) := by
    have := wordAt_of_write hm7 (r := 1) (o := 0) rfl (by decide) hv0
    rw [NativeRustcVm.addr_add_zero, eval_reg, Env.ofMachine_regs,
      show st4.data.regs.get64 .r15 = _ from (e4 .r15 (by simp)).trans
        ((e3 .r15 (by simp)).trans hr15_1), UInt64.ofBitVec_toBitVec] at this
    exact this
  have hw8 : WordAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 (56 + 16 * (t + 1)) + BitVec.ofNat 64 8)
      (kinv ((layerAt (muOf m0) (t + 1))[t]'hlt)) := by
    have := wordAt_of_write hm7 (r := 1) (o := 8) rfl (by decide) hv8
    rw [eval_reg, Env.ofMachine_regs, show st4.data.regs.get64 .rax = _ from
      (e4 .rax (by simp)).trans hinv, UInt64.ofBitVec_toBitVec] at this
    exact this
  have hpair : WordsAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 (56 + 16 * (t + 1)))
      [(layerAt (muOf m0) (t + 1))[t]'hlt, kinv ((layerAt (muOf m0) (t + 1))[t]'hlt)] :=
    NativeRustcVm.wordsAt_cons_iff.mpr ⟨hw0, NativeRustcVm.wordsAt_singleton_iff.mpr hw8⟩
  have htab : PairsAt st5.data.dmem (fbOf m0 + BitVec.ofNat 64 56) (tableAt (muOf m0) (t + 1)) := by
    unfold PairsAt
    rw [tableAt_succ ht, rootPair, pairWords_concat, NativeRustcVm.wordsAt_append_iff,
      pairWords_length', tableAt_length (by omega)]
    refine ⟨kk (by omega) (.inl (by rw [hpl])) (by rw [hpl]; omega) hI.table, ?_⟩
    rw [show fbOf m0 + BitVec.ofNat 64 56 + BitVec.ofNat 64 (8 * (2 * (t + 1))) =
        fbOf m0 + BitVec.ofNat 64 (56 + 16 * (t + 1)) by rw [addr_add]; congr 2; omega]
    dsimp only
    exact hpair
  have hr13_4 : reg st4.data .r13 = BitVec.ofNat 64 t := (e4 .r13 (by simp)).trans hr13_3
  have hr13 : reg st5.data .r13 = BitVec.ofNat 64 (t + 1) := by
    refine (hm7.regs .r13 _ rfl).trans ?_
    rw [eval_add, eval_reg, eval_lit, Env.ofMachine_regs, show st4.data.regs.get64 .r13 = _ from
      hr13_4, ofNat_succ]
  have hr12 : reg st5.data .r12 = BitVec.ofNat 64 (t + 1 + 1) := by
    refine (hm7.regs .r12 _ rfl).trans ?_
    rw [eval_add, eval_load, eval_lit, hl32, ofNat_succ]
  simp only [PcOk] at hpc5
  rw [eval_not, eval_cmp_eq, eval_add, eval_reg, eval_lit, eval_load, Env.ofMachine_regs,
    show st4.data.regs.get64 .r13 = _ from hr13_4, ofNat_succ, hl16,
    ofNat_beq (by omega) hmu64] at hpc5
  obtain ⟨hT5, hF5⟩ := Arrays.pc_cond hpc5
  have htn : Turn m0 st5.data := ⟨hfr5, kk (by omega) (.inl (by rw [hlw]; omega))
    (by rw [hlw]; omega) hI.tn.out, kk (by omega) (.inl (by rw [hlw]; omega)) (by rw [hlw]; omega)
    hI.tn.mu, kk (by omega) (.inl (by rw [hlw]; omega)) (by rw [hlw]; omega) hI.tn.mu8, hmu⟩
  by_cases hlast : t + 1 = muOf m0
  · have hc := hF5 (by
      rw [Bool.not_eq_true', decide_eq_false_iff_not, not_not]
      exact hlast)
    refine .done _ (.inr (.inl ⟨hc, hfr5, htn.out, by omega, ?_, ?_⟩))
    · have h := htab; rw [hlast] at h; exact h
    · rw [hr12, hlast]
  · refine .done _ (.inl ⟨(hT5 (by rw [Bool.not_eq_true', decide_eq_false_iff_not]; exact hlast)).trans
      (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_13_at), htn, by omega, ?_, htab, ?_, hr12, hr13, ?_, ?_⟩)
    · exact kk (by omega) (.inr (by omega)) (by rw [hlb]; omega) hI.layer
    · refine (hm7.regs .rbx _ rfl).trans ?_
      rw [eval_add, eval_reg, eval_lit, Env.ofMachine_regs, show st4.data.regs.get64 .rbx = _ from
        (e4 .rbx (by simp)).trans ((e3 .rbx (by simp)).trans hrbx_1), BitVec.add_comm, addr_add]
      congr 2
    · refine (hm7.regs .r14 _ rfl).trans ?_
      rw [eval_load, hl16, ← hmuv]
    · rw [lastAt_succ hlt]
      exact (Match.reg_eq (r := .r15) hm6 hm7 rfl rfl).trans
        ((e4 .r15 (by simp)).trans ((e3 .r15 (by simp)).trans hr15_1))

end

end NativeRustcVmX64.Whir.SubspaceTable
