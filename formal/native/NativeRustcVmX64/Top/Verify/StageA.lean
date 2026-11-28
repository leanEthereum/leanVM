module

public import NativeRustcVmX64.Top.Verify.Basic
public import NativeRustcVmX64.Code.Vm.Seed.Names

/-!
# `verify` up to `seed` (x86-64)

`stageA`: from the entry, the prologue (`b0`) and `seed` writing the seed's lanes at the `TState`:
the state `SA`.
-/

namespace NativeRustcVmX64.Top.Verify

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Verify NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Top NativeVm.Model

public section

variable [Host] {k : Nat}

/-- **`verify` up to `seed`.** -/
theorem stageA (hp : Placed code k) (hseed : Spec (Labels.label NativeRustcVmX64.Vm.Seed.entryLabel) SeedPre SeedPost)
    {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)} {m0 : MachineData}
    (hpre : VerifyPre a stream openings m0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b1Offset) ∧ SA m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b0Offset)⟩ := by
  have g := geo_of hpre
  obtain ⟨hst, hrod, -, -, -, ⟨hbcM, -⟩, ⟨hpubM, -⟩, -, -, -, -, -, -, hgot⟩ := hpre
  have hS := verifyStack_eq
  have hss : seedStack = 1008 := rfl
  have hn : verifyStack ≤ (rspOf m0).toNat := hst.1
  have hR := g.R
  have h8 := g.e8
  have hs : 18704 ≤ (rspOf m0).toNat := by omega
  have hfnw := frame_noWrap (F := 816) hst (by omega)
  have hBn := g.F
  have hoff : ∀ j, j < 824 → (off (fb m0) j).toNat = sb m0 + 17888 + j := fun j hj ↦ by
    rw [toNat_off (by omega), hBn]
  have hrc := hrod.rcAt
  have hrcN := hrc.2.1
  have hrcA := hrc.2.2
  unfold NativeRustcVm.Apart at hrcA
  unfold NativeRustcVm.NoWrap at hrcN
  rw [hS, sb_eq] at hrcA
  have hFm : ∀ d : MachineData, Kept m0.dmem d.dmem →
      NativeRustcVm.Mapped d.dmem (fb m0) (816 + 8) :=
    fun d hk ↦ Mapped.keeps (frame_mapped hst (by omega)) hk
  have hstk : ∀ q, sb m0 ≤ q.toNat → q.toNat < sb m0 + 18704 →
      NativeRustcVm.InRange (stackBelow m0 18704) 18704 q := by
    intro q h1 h2
    rw [inR (by unfold NativeRustcVm.NoWrap; rw [sb_eq]; omega), sb_eq]
    omega
  -- `b0`: the prologue, `call seed`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 816) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Verify.b0Offset + b0.length)).toBitVec) ⟨frame_mapped hst (by omega), hfnw⟩
    (by simp) (List.pairwise_singleton _ _)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw1, hrdi, hrsi, hrdx, hrcx, hrbx, hrbp, hr12, hr13, hr14, hr15⟩ :=
    after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 816 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (fb m0) 816) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hw1
  have hs1' : ∀ q, NativeRustcVm.InRange (fb m0) 816 q →
      sb m0 + 17888 ≤ q.toNat ∧ q.toNat < sb m0 + 18704 := fun q h ↦ by
    rw [inR (by unfold NativeRustcVm.NoWrap; omega), hBn] at h
    omega
  have hsp1 : rspOf st1.data = fb m0 := by rw [hf1.sp, off_zero]
  have eRdi : reg st1.data .rdi = tOf m0 := (hm1.regs .rdi _ hrdi).trans (eval_ptr0 8)
  have eRsi : reg st1.data .rsi = reg m0 .rdi := hm1.regs .rsi _ hrsi
  have eRdx : reg st1.data .rdx = reg m0 .rsi := hm1.regs .rdx _ hrdx
  have eRcx : reg st1.data .rcx = reg m0 .rdx := hm1.regs .rcx _ hrcx
  have hrc1 : ∀ i < 192, st1.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) :=
    rc_keep hs1 fun q hq h ↦ by
      have := hs1' q hq
      rw [inR (by unfold NativeRustcVm.NoWrap; omega)] at h
      omega
  have hbc1 : NativeRustcVm.WordsAt st1.data.dmem (reg m0 .rdi) (bcOf m0) := by
    rcases Nat.eq_zero_or_pos (reg m0 .rsi).toNat with h0 | h0
    · rw [List.length_eq_zero_iff.mp ((length_bcOf m0).trans h0)]
      exact NativeRustcVm.wordsAt_nil _ _
    · refine (wordsAt_bcOf hbcM).of_sameOutside hs1 fun i hi h ↦ ?_
      have hA := (g.bc h0).1
      have := g.bcN
      rw [NativeRustcVm.length_wordsBytes, length_bcOf] at hi
      have := hs1' _ h
      rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
      omega
  have hpub1 : NativeRustcVm.WordsAt st1.data.dmem (reg m0 .rdx) (pubOf m0).toList := by
    refine (wordsAt_pubOf hpubM).of_sameOutside hs1 fun i hi h ↦ ?_
    have := g.pub
    have := g.pubN
    rw [NativeRustcVm.length_wordsBytes, Vector.length_toList] at hi
    have := hs1' _ h
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at this
    omega
  have hsb1 : (stackBelow st1.data 1008).toNat = sb m0 + 16880 := by
    rw [stackBelow_callee hsp1 (by omega)]
    exact stackBelow_sb hs (by decide)
  have hT : (tOf m0).toNat = sb m0 + 17896 := by rw [hoff 8 (by decide)]
  have hpre1 : SeedPre st1.data := by
    unfold SeedPre
    simp only [eRdi, eRsi, eRdx, eRcx]
    refine ⟨stackOk_callee hst hf1.kept hsp1 (by omega), RcAt.callee hrc hrc1 hsp1 hn (by omega),
      g.n32, ⟨Mapped.keeps hbcM hf1.kept, g.bcN⟩, ⟨Mapped.keeps hpubM hf1.kept, g.pubN⟩,
      ⟨mapped_off (hFm _ hf1.kept) (by dsimp only; omega), ?_⟩,
      List.pairwise_pair.mpr ?_, List.pairwise_pair.mpr ?_, (fun h0 ↦ ?_), ?_⟩
    · show (tOf m0).toNat + 200 ≤ 2 ^ 64
      omega
    · show NativeRustcVm.Apart _ _ _ _
      unfold NativeRustcVm.Apart
      simp only [stackR, hss, hsb1]
      have := g.pub
      omega
    · show NativeRustcVm.Apart _ _ _ _
      unfold NativeRustcVm.Apart
      simp only [stackR, hss, hsb1, hT]
      omega
    · unfold NativeRustcVm.Apart
      rw [hss, hsb1]
      have := (g.bc h0).1
      omega
    · apply NativeRustcVmX64.GotAt.callee hgot
      · apply NativeRustcVmX64.GotAt.unchanged_stack hgot hst
        intro q hq
        exact hs1 q fun h => hq (by
          have hh := hs1' q h
          rw [hS]
          exact hstk q (by omega) (by omega))
      · rw [hS, sb_eq, hss, hsb1]
        omega
      · rw [hS, sb_eq, hss, hsb1]
        omega
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · refine ⟨(stackBelow m0 verifyStack, verifyStack + 8), by simp, ?_, ?_⟩
            · simp only [hS, sb_eq, hT]
              omega
            · simp only [hS, sb_eq, hT]
              omega
          · exact ⟨(reg m0 .rdx, 32), by simp, Nat.le_refl _, Nat.le_refl _⟩
          · exact ⟨(rcAddr, 192), by simp [rc_mem_rodataAreas], Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨p, by simp [hp], Nat.le_refl _, Nat.le_refl _⟩
  refine call_then hpc1 hseed hpre1 fun st2 hpc2 hrsp2 hpost2 ↦ ?_
  obtain ⟨hout2, hs2, hsv2⟩ := hpost2
  simp only [eRdi, eRsi, eRdx, eRcx] at hout2 hs2
  have hR2 : ∀ q, (NativeRustcVm.InRange (tOf m0) 200 q ∨
      NativeRustcVm.InRange (stackBelow st1.data seedStack) seedStack q) →
      sb m0 + 16880 ≤ q.toNat ∧ q.toNat < sb m0 + 17888 + 208 := by
    rintro q (h | h)
    · rw [inR (by unfold NativeRustcVm.NoWrap; omega), hT] at h
      omega
    · rw [hss, inR (by unfold NativeRustcVm.NoWrap; omega), hsb1] at h
      omega
  have hf2 : Frame m0 816 slots 8 st2.data :=
    Frame.call_low hf1 hsv2 hrsp2 hs2 (fun q h ↦ Or.inl (by
        have := hR2 q h
        rw [show (stackBelow m0 816).toNat = sb m0 + 17888 from hBn]
        omega)) (L := 208)
      (fun p hp ↦ by have := slots_ge p hp; omega) (by decide) hfnw slots_le
  refine .done _ ⟨hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Verify.b0_next),
    ⟨hf2, fun q hq ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hout2 _ (length_bcOf m0) hbc1 _ hpub1⟩⟩
  · have hq' : ¬ (sb m0 ≤ q.toNat ∧ q.toNat < sb m0 + 18704) :=
      fun h ↦ hq (hstk q h.1 h.2)
    have e2 : st2.data.dmem.get? q = st1.data.dmem.get? q := hs2 q fun h ↦ by
      have h' := hR2 q h
      exact hq' ⟨by omega, by omega⟩
    have e1 : st1.data.dmem.get? q = m0.dmem.get? q := hs1 q fun h ↦ by
      have h' := hs1' q h
      exact hq' ⟨by omega, by omega⟩
    exact e2.trans e1
  · exact (hsv2.1 .rbx rfl).trans (hm1.regs .rbx _ hrbx)
  · exact (hsv2.1 .r12 rfl).trans (hm1.regs .r12 _ hr12)
  · exact (hsv2.1 .r13 rfl).trans (hm1.regs .r13 _ hr13)
  · exact (hsv2.1 .r14 rfl).trans (hm1.regs .r14 _ hr14)
  · exact (hsv2.1 .r15 rfl).trans (hm1.regs .r15 _ hr15)
  · exact (hsv2.1 .rbp rfl).trans ((hm1.regs .rbp _ hrbp).trans (eval_ptr0 8))

end

end NativeRustcVmX64.Top.Verify
