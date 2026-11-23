module

public import NativeRustcVmX64.Top.Leanvm.Stage2
public import NativeRustcVmX64.Code.Vm.Verify.Names

/-!
# `leanvm_verify`: the verifier (x86-64)

`stage3`: from `AD` at `NativeRustcVmX64.Vm.LeanvmVerify.label_16` with the decoded proof in the area, `b16` stores the
`Decoded` (the area's address, word count, `L`) at the frame's bytes 40 to 63 and calls `verify`
with the bytecode (a dangling `8` when empty), the public input in the frame, the `Decoded` and
the working area; `b17` zero-extends its `bool`, `b13` returns: RAX is `Model.verify`'s verdict.
The read-only data stays at its labels (`rodataAt_keep`).
-/

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LeanvmVerify NativeRustcVmX64.Transcript
open NativeRustcVmX64.Top NativeVm NativeVm.Wire NativeRustcVm.Wire NativeRustcVm.Transcript
open NativeRustcVm.Top (workAreaBytes entryRegions ApartFrom Aligned)
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

/-- `movzbl %al, %eax`: RAX the `bool` in AL. -/
theorem zext_okAl {x : BitVec 64} {b : Bool} (h : x.toNat % 256 = (okWord b).toNat) :
    UnOp.apply (.zext .W8) .W32 x = (okWord b).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp only [UnOp.apply, ext, low, BitVec.toNat_setWidth]
  rw [show Width.W8.bits = 8 from rfl, show Width.W32.bits = 32 from rfl]
  simp only [UInt64.toNat_toBitVec]
  omega

variable [Host] {k : Nat}

/-- **The verifier.** -/
theorem stage3 (hp : Placed code k)
    (hver : ∀ a stream openings, Spec (Labels.label NativeRustcVmX64.Vm.Verify.entryLabel) (VerifyPre a stream openings)
      (VerifyPost stream openings))
    {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4}
    {m0 : MachineData} (hpre : LeanvmVerifyPre a bytes bytecode pub m0) {st : MachineState}
    {r : List E × List PhaseOut} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b16Offset))
    (hA : AD a bytes bytecode pub m0 st.data)
    (hD : DecodedAt st.data.dmem ⟨a.decoded.toBitVec, decodedWords bytes.length, bytes.length⟩
      (streamW r.1) (openingsW r.2)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧
      reg st'.data .rax = (okWord (Model.verify bytecode.toArray pub (streamW r.1)
        (openingsW r.2))).toBitVec ∧
      NativeRustcVm.SameOutside m0.dmem st'.data.dmem (Out m0 a bytes.length) ∧
      Saved m0 st'.data) st := by
  have g := geo_of hpre
  obtain ⟨hst, hrod, hin, -, -, hapR, hgot⟩ := hpre
  have hS := leanvmVerifyStack_eq
  have hR := g.R
  have h8 := g.e8
  have hBn := g.F
  have hn : leanvmVerifyStack ≤ (rspOf m0).toNat := hst.1
  have hfnw := frame_noWrap (F := 112) hst (by decide)
  have hwa := workAreaBytes_le bytecode.length
  have hdp := decodedWords_pos bytes.length
  have gdec := g.dec
  have gdecN := g.decN
  have gwork := g.work
  have gworkN := g.workN
  have gdw := g.decWork
  have hbs := hin.bcSmall
  have hoff : ∀ j, j < 120 → (off (stackBelow m0 112) j).toNat = lsb m0 + 18704 + j := fun j hj ↦ by
    rw [toNat_off (by omega), hBn]
  have hFm : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (stackBelow m0 112) (112 + 8) :=
    fun d hk ↦ Mapped.keeps (frame_mapped hst (by decide)) hk
  -- the areas apart from the read-only data
  have rodA : ∀ (x : UInt64) (sz : Nat),
      (⟨x.toBitVec, sz⟩ : NativeRustcVm.Region) ∈
        entryRegions (ctxOf m0) a bytes.length bytecode.length →
      0 < sz → ∀ t : NativeRustcVm.Data.Item,
        x.toNat + sz ≤ (rodataAddr t).toNat ∨ (rodataAddr t).toNat + t.bytes.length ≤ x.toNat :=
    fun x sz hr hp t ↦ by
      have h := hapR _ hr hp t
      unfold NativeRustcVm.Apart at h
      exact h
  have hwsz : 0 < 8 * NativeVm.Entry.workWords bytecode.length := by
    unfold workAreaBytes NativeRustcVm.Top.workAreaWords at hwa; omega
  have rodD := rodA a.decoded (8 * decodedWords bytes.length) (by simp [entryRegions]) (by omega)
  have rodW := rodA a.work (8 * NativeVm.Entry.workWords bytecode.length) (by simp [entryRegions]) hwsz
  have rodS : ∀ t : NativeRustcVm.Data.Item, (rodataAddr t).toNat + t.bytes.length ≤ lsb m0 ∨
      lsb m0 + 18824 ≤ (rodataAddr t).toNat := fun t ↦ by
    have h := hrod.apart t
    unfold NativeRustcVm.Apart at h
    rw [hS, lsb_eq] at h
    omega
  have notRod : ∀ p, Out m0 a bytes.length p → ∀ t : NativeRustcVm.Data.Item,
      ¬ NativeRustcVm.InRange (rodataAddr t) t.bytes.length p := by
    intro p hp t h
    have hnw := hrod.noWrap t
    rw [inR hnw] at h
    rcases hp with hp | hp | hp
    · rw [inR (by unfold NativeRustcVm.NoWrap; rw [lsb_eq]; omega), lsb_eq] at hp
      have := rodS t; omega
    · rw [inR (by unfold NativeRustcVm.NoWrap; simp; omega)] at hp
      simp only [UInt64.toNat_toBitVec] at hp
      have := rodD t; omega
    · rw [inR (by unfold NativeRustcVm.NoWrap; simp; omega)] at hp
      simp only [UInt64.toNat_toBitVec] at hp
      have := rodW t; omega
  -- `b16`: the `Decoded`, `call verify`.
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 112) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b16Offset + b16.length)).toBitVec) ⟨hFm _ hA.frame.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) run_b16 hwf (fun _ _ ↦ rfl) hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hA.frame.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hw1, h40, h48, h56, hrdi, hrsi, hrdx, hrcx, hr8⟩ := after_eq run_b16 ▸ ok_b16
  have hf1 : Frame m0 112 slots 0 st1.data := Frame.of_block hA.frame hwf hm1 hmid1 slots_le
  have hsp1 : rspOf st1.data = stackBelow m0 112 := by rw [hf1.sp, off_zero]
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (fun q ↦ Touch (stackBelow m0 112) 120 (fun j ↦ j < 8 ∨ 40 ≤ j ∧ j < 64) q) :=
    sameOutside_W hwf hm1 (r := 0) rfl fun w hw ↦ by
      obtain ⟨hr, hb⟩ := hw1 w hw
      exact ⟨hr, by omega, fun j h1 h2 ↦ by omega⟩
  have hs1' : ∀ q, Touch (stackBelow m0 112) 120 (fun j ↦ j < 8 ∨ 40 ≤ j ∧ j < 64) q →
      lsb m0 + 18704 ≤ q.toNat ∧ q.toNat < lsb m0 + 18768 := by
    rintro q ⟨j, hj, hW, rfl⟩
    rw [hoff j hj]
    omega
  have hsame1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0 a bytes.length) :=
    fun q hq ↦ by
      rw [hs1 q fun h ↦ hq (Or.inl (by
        have := hs1' q h
        rw [inR (by unfold NativeRustcVm.NoWrap; rw [lsb_eq]; omega), lsb_eq]
        omega))]
      exact hA.same q hq
  -- the registers
  set a' : DecArea := ⟨a.decoded.toBitVec, decodedWords bytes.length, bytes.length⟩ with ha'
  obtain ⟨bc, hbc⟩ : ∃ bc : BitVec 64, bc = if bytecode.length = 0 then 8#64 else a.bytecode.toBitVec :=
    ⟨_, rfl⟩
  have hbcE : 0 < bytecode.length → bc = a.bytecode.toBitVec := fun h0 ↦ by
    rw [hbc]; simp [show bytecode.length ≠ 0 by omega]
  have eRdi : reg st1.data .rdi = bc := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hrdi, hbc]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self,
      Env.ofMachine_regs]
    rw [show st.data.regs.get64 .r14 = _ from hA.r14, show st.data.regs.get64 .rbp = _ from hA.rbp]
    rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl]
    by_cases h0 : bytecode.length = 0
    · rw [h0]; simp
    · have : (BitVec.ofNat 64 bytecode.length == 0#64) = false := by
        rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
          ofNat_beq (X := bytecode.length) (k := 0) (by omega) (by decide)]
        simpa using h0
      simp [this, h0]
  have eRsi : (reg st1.data .rsi).toNat = bytecode.length := by
    rw [show reg st1.data .rsi = _ from (hm1.regs .rsi _ hrsi).trans hA.r14, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have eRdx : reg st1.data .rdx = off (stackBelow m0 112) 8 := (hm1.regs .rdx _ hrdx).trans (eval_ptr0 8)
  have eRcx : reg st1.data .rcx = off (stackBelow m0 112) 40 := (hm1.regs .rcx _ hrcx).trans (eval_ptr0 40)
  have eR8 : reg st1.data .r8 = a.work.toBitVec := (hm1.regs .r8 _ hr8).trans hA.r13
  -- the `Decoded`, the public input, the decoded proof, the bytecode
  have hdecF : DecFieldsAt st1.data.dmem (off (stackBelow m0 112) 40) a' := by
    have w : ∀ (o : Nat) (rg : Reg64) (v : UInt64), o + 8 ≤ 120 →
        (∀ j < 8, findWrite 0 (o + j) (after b16 bodyS).mem = some (.reg rg, j)) →
        reg st.data rg = v.toBitVec →
        NativeRustcVm.WordAt st1.data.dmem (off (stackBelow m0 112) o) v := fun o rg v ho hw hr ↦ by
      have := wordAt_write (r := 0) (b := stackBelow m0 112) (sz := 120) hm1 rfl ho hw
      rwa [show (Sym.reg rg).eval (frameEnv m0 st.data 112 [] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.LeanvmVerify.b16Offset + b16.length)).toBitVec) = reg st.data rg from rfl, hr,
        UInt64.ofBitVec_toBitVec] at this
    refine ⟨?_, ?_, ?_⟩
    · exact w 40 .r12 _ (by decide) (after_eq run_b16 ▸ h40) hA.r12
    · rw [off_off]; exact w 48 .r15 _ (by decide) (after_eq run_b16 ▸ h48) hA.r15
    · rw [off_off]; exact w 56 .rbx _ (by decide) (after_eq run_b16 ▸ h56) hA.rbx
  have hpub1 : NativeRustcVm.WordsAt st1.data.dmem (off (stackBelow m0 112) 8) pub.toList :=
    keep_off hA.pubw hs1 fun j h1 h2 ↦ by
      rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at h2
      exact not_touch (by unfold NativeRustcVm.NoWrap; omega) (by omega) (by omega)
  have notD : ∀ q, Touch (stackBelow m0 112) 120 (fun j ↦ j < 8 ∨ 40 ≤ j ∧ j < 64) q →
      ¬ NativeRustcVm.InRange a.decoded.toBitVec (8 * decodedWords bytes.length) q := fun q h h' ↦ by
    have := hs1' q h
    rw [inR (by unfold NativeRustcVm.NoWrap; simp; omega)] at h'
    simp only [UInt64.toNat_toBitVec] at h'
    omega
  have hD1 : DecodedAt st1.data.dmem a' (streamW r.1) (openingsW r.2) :=
    hD.agree (fun j hj _ ↦ hs1 _ fun h ↦ notD _ h (inRange_off_self hj (by simp; omega)))
  have hbcW : NativeRustcVm.WordsAt m0.dmem a.bytecode.toBitVec bytecode :=
    NativeRustcVm.wordsAt_of_wordView hin.bcWords
  have hbc1 : NativeRustcVm.WordsAt st1.data.dmem bc bytecode := by
    rcases Nat.eq_zero_or_pos bytecode.length with h0 | h0
    · rw [List.length_eq_zero_iff.mp h0]; exact NativeRustcVm.wordsAt_nil _ _
    · rw [hbcE h0]
      refine hbcW.of_sameOutside hsame1 fun i hi h ↦ ?_
      rw [NativeRustcVm.length_wordsBytes] at hi
      have gb := g.bc h0
      have gbd := g.bcDec
      have gbw := g.bcWork
      have gbN := g.bcN
      have hq : (a.bytecode.toBitVec + BitVec.ofNat 64 i).toNat = a.bytecode.toNat + i := by
        rw [NativeRustcVm.toNat_add_ofNat (by simp; omega)]; rfl
      rcases h with h | h | h
      · rw [inR (by unfold NativeRustcVm.NoWrap; rw [lsb_eq]; omega), lsb_eq, hq] at h; omega
      · rw [inR (by unfold NativeRustcVm.NoWrap; simp; omega), hq] at h
        simp only [UInt64.toNat_toBitVec] at h; omega
      · rw [inR (by unfold NativeRustcVm.NoWrap; simp; omega), hq] at h
        simp only [UInt64.toNat_toBitVec] at h; omega
  -- `verify`'s precondition
  have hvs : verifyStack = 18704 := rfl
  have hsbv : (stackBelow st1.data verifyStack).toNat = lsb m0 := by
    rw [hvs, stackBelow_callee hsp1 (by omega), lsb_eq]
  have hpre1 : VerifyPre a' (streamW r.1) (openingsW r.2) st1.data := by
    unfold VerifyPre
    simp only [eRdi, eRsi, eRdx, eRcx, eR8]
    have hstk1 : (stackBelow st1.data 18704).toNat = lsb m0 := by rw [← hvs]; exact hsbv
    have hP : (off (stackBelow m0 112) 8).toNat = lsb m0 + 18712 := by rw [hoff 8 (by decide)]
    have hDc : (off (stackBelow m0 112) 40).toNat = lsb m0 + 18744 := by rw [hoff 40 (by decide)]
    have hbcN : bc.toNat + 8 * bytecode.length ≤ 2 ^ 64 := by
      rw [hbc]; split
      · rename_i h0; rw [h0]; simp
      · simp only [UInt64.toNat_toBitVec]; exact g.bcN
    have stkRod : ∀ (p : BitVec 64) (sz : Nat), lsb m0 ≤ p.toNat → p.toNat + sz ≤ lsb m0 + 18824 →
        RodataApart p sz := fun p sz h1 h2 t ↦ by
      have := rodS t
      unfold NativeRustcVm.Apart
      omega
    refine ⟨stackOk_callee hst hf1.kept hsp1 (by omega), ?_, by omega, hdecF, hD1,
      ⟨hbc1.mapped, hbcN⟩, ⟨mapped_off (o := 8) (k := 32) (hFm _ hf1.kept) (by decide), by
        show (off (stackBelow m0 112) 8).toNat + 32 ≤ 2 ^ 64; omega⟩,
      ⟨mapped_off (o := 40) (k := 24) (hFm _ hf1.kept) (by decide), by
        show (off (stackBelow m0 112) 40).toNat + 24 ≤ 2 ^ 64; omega⟩,
      ⟨Mapped.keeps (NativeRustcVm.mapped_of_wordView hin.decSome) hf1.kept, by
        show a.decoded.toBitVec.toNat + 8 * decodedWords bytes.length ≤ 2 ^ 64; simp; omega⟩,
      ⟨Mapped.keeps (NativeRustcVm.Mapped.mono (NativeRustcVm.mapped_of_wordView hin.workSome)
        hwa) hf1.kept, by show a.work.toBitVec.toNat + workAreaBytes ≤ 2 ^ 64; simp; omega⟩,
      ?_, ?_, (fun h0 ↦ ⟨?_, ?_⟩), ?_⟩
    · refine rodataAt_keep hrod hsame1 notRod ?_ ?_ <;> rw [hvs, hstk1, hS, lsb_eq]
      omega
    · simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
        false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart,
        stackR, DecArea.region, hvs, hstk1, hP, hDc, ha', UInt64.toNat_toBitVec]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact stkRod _ _ (by dsimp only; omega) (by dsimp only; omega)
      · exact stkRod _ _ (by dsimp only; omega) (by dsimp only; omega)
      · exact hapR ⟨a.decoded.toBitVec, 8 * decodedWords bytes.length⟩ (by simp [entryRegions])
          (by show 0 < 8 * decodedWords bytes.length; omega)
      · intro t
        have := rodW t
        unfold NativeRustcVm.Apart
        dsimp only
        simp only [UInt64.toNat_toBitVec]
        omega
    · have gb := g.bc h0
      have gbd := g.bcDec
      have gbw := g.bcWork
      rw [hbcE h0]
      simp only [NativeRustcVm.disjoint_cons_iff, List.forall_mem_cons, List.mem_nil_iff,
        false_implies, implies_true, NativeRustcVm.disjoint_nil, and_true, NativeRustcVm.Apart,
        stackR, DecArea.region, hvs, hstk1, ha', UInt64.toNat_toBitVec]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega
    · rw [hbcE h0]
      exact hapR ⟨a.bytecode.toBitVec, 8 * bytecode.length⟩ (by simp [entryRegions])
        (by show 0 < 8 * bytecode.length; omega)
    · apply NativeRustcVmX64.GotAt.callee hgot
      · intro l hl i hi
        obtain ⟨_, hgn, hgs, hga⟩ := hgot.1 l hl
        apply hsame1
        rintro (h | h | h)
        · apply hgs.not_inRange hgn (noWrap_stackBelow hst) hi
          exact inRange_mono h (by omega)
        · exact NativeRustcX64.Apart.not_inRange
            (hga (a.decoded.toBitVec, 8 * decodedWords bytes.length) (by simp [entryRegions])) hgn
            (by show a.decoded.toBitVec.toNat + 8 * decodedWords bytes.length ≤ 2 ^ 64; exact gdecN) hi h
        · have hgwork := NativeRustcVm.Apart.mono_right
            (hga (a.work.toBitVec, 8 * NativeVm.Entry.workWords bytecode.length) (by simp [entryRegions]))
            (Nat.le_refl a.work.toBitVec.toNat)
            (show a.work.toBitVec.toNat + workAreaBytes ≤
              a.work.toBitVec.toNat + 8 * NativeVm.Entry.workWords bytecode.length by omega)
          exact NativeRustcX64.Apart.not_inRange hgwork hgn
            (by show a.work.toBitVec.toNat + workAreaBytes ≤ 2 ^ 64; exact gworkN) hi h
      · rw [hS, lsb_eq, hsbv]
      · rw [hS, lsb_eq, hsbv, hvs]
        omega
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · rcases List.mem_append.mp hp with hp | hp
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl
            · refine ⟨(stackBelow m0 leanvmVerifyStack, leanvmVerifyStack + 8), by simp, ?_, ?_⟩ <;>
                simp only [hS, lsb_eq, hP] <;> omega
            · refine ⟨(stackBelow m0 leanvmVerifyStack, leanvmVerifyStack + 8), by simp, ?_, ?_⟩ <;>
                simp only [hS, lsb_eq, hDc] <;> omega
            · exact ⟨(a.decoded.toBitVec, 8 * decodedWords bytes.length),
                by simp [entryRegions], Nat.le_refl _, Nat.le_refl _⟩
            · refine ⟨(a.work.toBitVec, 8 * NativeVm.Entry.workWords bytecode.length),
                by simp [entryRegions], Nat.le_refl _, ?_⟩
              dsimp only
              omega
          · exact ⟨p, by simp [hp], Nat.le_refl _, Nat.le_refl _⟩
        · split at hp
          · simp at hp
          · rename_i hn0
            simp only [List.mem_singleton] at hp
            subst p
            rw [hbcE (by omega)]
            exact ⟨(a.bytecode.toBitVec, 8 * bytecode.length), by simp [entryRegions],
              Nat.le_refl _, Nat.le_refl _⟩
  refine call_then hpc1 (hver a' _ _) hpre1 fun st2 hpc2 hrsp2 hpost2 ↦ ?_
  obtain ⟨hres2, hs2, hsv2⟩ := hpost2
  simp only [eRdi, eRsi, eRdx, eR8] at hres2 hs2
  have hok := hres2 bytecode rfl hbc1 pub hpub1
  have hR2 : ∀ q, NativeRustcVm.InAny [⟨a.work.toBitVec, workAreaBytes⟩,
      frameR st1.data verifyStack] q →
      (lsb m0 ≤ q.toNat ∧ q.toNat < lsb m0 + 18704) ∨
        NativeRustcVm.InRange a.work.toBitVec workAreaBytes q := by
    intro q h
    rcases inAny2 h with h | h
    · exact Or.inr h
    · left
      change NativeRustcVm.InRange (stackBelow st1.data verifyStack) verifyStack q at h
      rw [inR (by unfold NativeRustcVm.NoWrap; rw [hsbv, hvs]; omega), hsbv, hvs] at h
      exact h
  have hf2 : Frame m0 112 slots 8 st2.data := by
    refine Frame.call_low hf1 hsv2 hrsp2 hs2 (L := 8) (fun q h ↦ ?_) (fun p hp ↦ by
      have := slots_ge p hp; omega) (by decide) hfnw slots_le
    rw [hBn]
    rcases hR2 q h with h | h
    · left; omega
    · rw [inR (by unfold NativeRustcVm.NoWrap; simp; omega)] at h
      simp only [UInt64.toNat_toBitVec] at h
      omega
  -- `b17`: RAX the verdict; `b13`.
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 112) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨hFm _ hf2.kept, hfnw⟩ (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) run_b17 hwf2 nofun
    (hpc2.trans (by rw [show k + NativeRustcVmX64.Vm.LeanvmVerify.b16Offset + b16.length = k + NativeRustcVmX64.Vm.LeanvmVerify.b17Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.LeanvmVerify.b16_next]]))
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hf2.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hrax3⟩ := after_eq run_b17 ▸ ok_b17
  have hf3 : Frame m0 112 slots 8 st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  simp only [PcOk] at hpc3
  refine Eventually.mono (exit13 hp hst (hpc3.trans (lbl_18 hp)) hf3)
    fun s ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, ?_, fun q hq ↦ ?_, h5⟩
  · rw [h3, show reg st3.data .rax = _ from hm3.regs .rax _ hrax3]
    exact zext_okAl hok
  · have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
    rw [h4, hd3, hs2 q fun h ↦ by
      rcases hR2 q h with h | h
      · exact hq (Or.inl (by
          rw [inR (by unfold NativeRustcVm.NoWrap; rw [lsb_eq]; omega), lsb_eq]; omega))
      · exact hq (Or.inr (Or.inr h))]
    exact hsame1 q hq

end

end NativeRustcVmX64.Top.Leanvm
