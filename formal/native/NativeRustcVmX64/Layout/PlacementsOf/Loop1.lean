module

public import NativeRustcVmX64.Layout.PlacementsOf.Base
public import NativeRustcX64.Spec.Mem
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.PlacementsOf.Names

/-!
# `placements_of` on x86-64: the entry and the first loop (`b0` to `b8`)

The prologue `b0` and `b1` zero `block_cols` and `block_sizes` (`memset`), `b2` starts the loop at
column `0` (`entry`). At the head `.L2` (`I1 m0 c c`) the stacked columns below `c` and their
log-sizes are in `block_cols`, `block_sizes`; a turn (`turn1`) tests the column's slot byte
(`b5`), its output byte (`b6`), room (`b7`) and appends it (`b8`); `.L1` (`b4`) moves on to the
next column or out of the loop at `.L6` (`l1`, `loop1`).
-/

namespace NativeRustcVmX64.Layout.PlacementsOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PlacementsOf NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeRustcVmX64.Layout.BuildFrame
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf)

@[expose] public section

section
variable [Labels]

/-- **The first loop**: the stacked columns below `c` gathered, RAX `a`. -/
structure I1 (m0 : MachineData) (c a : Nat) (d : MachineData) : Prop where
  b : B m0 8 d
  le : c ≤ 158
  ac : a ≤ c
  rax : (reg d .rax).toNat = a
  r15 : (reg d .r15).toNat = 1264 - 8 * a
  r13 : (reg d .r13).toNat = (below c).length
  rbp : reg d .rbp = rodataAddr .keccakSlot
  r12 : reg d .r12 = rodataAddr .keccakOutput
  r14 : reg d .r14 = kk m0
  rbx : reg d .rbx = pp m0
  cols : ∀ q (h : q < (below c).length),
    WordAt d.dmem (off (fb m0) (1280 + 8 * q)) ((below c)[q]).toUInt64
  sizes : ∀ q (h : q < (below c).length),
    WordAt d.dmem (off (fb m0) (2544 + 8 * q)) (κ m0 (below c)[q]).toUInt64

end

end

public section

theorem toUInt64_toNat' {x : UInt64} : x.toNat.toUInt64 = x := by
  apply UInt64.toNat.inj; simp

section
variable [Labels] {m0 : MachineData}

theorem I1.of {c a : Nat} {d d' : MachineData} (h : I1 m0 c a d) (hb : B m0 8 d')
    (hd : d'.dmem = d.dmem) (he : ∀ r ∈ (Reg64.rax :: cs), reg d' r = reg d r) : I1 m0 c a d' where
  b := hb
  le := h.le
  ac := h.ac
  rax := by rw [he .rax (by simp)]; exact h.rax
  r15 := by rw [he .r15 (by simp [cs])]; exact h.r15
  r13 := by rw [he .r13 (by simp [cs])]; exact h.r13
  rbp := (he .rbp (by simp [cs])).trans h.rbp
  r12 := (he .r12 (by simp [cs])).trans h.r12
  r14 := (he .r14 (by simp [cs])).trans h.r14
  rbx := (he .rbx (by simp [cs])).trans h.rbx
  cols := by rw [hd]; exact h.cols
  sizes := by rw [hd]; exact h.sizes

/-- A column not stacked leaves the stacked columns. -/
theorem I1.skip {c : Nat} {d : MachineData} (h : I1 m0 c c d) (hc : c < 158)
    (hn : isBlockF c = false) : I1 m0 (c + 1) c d := by
  have e : below (c + 1) = below c := by rw [below_succ, hn]; simp
  exact ⟨h.b, by omega, by omega, h.rax, h.r15, e ▸ h.r13, h.rbp, h.r12, h.r14, h.rbx,
    e ▸ h.cols, e ▸ h.sizes⟩

/-- **`memset` on a part of the frame**: its precondition. -/
theorem memset_pre (hF : Facts m0) {d : MachineData} (hb : B m0 0 d) {o n : Nat}
    (hrdi : reg d .rdi = off (fb m0) o) (hrdx : (reg d .rdx).toNat = n) (h8 : 8 ≤ o)
    (hon : o + n ≤ 5072) : MemsetPre d := by
  have hsp := hb.rsp0
  have hp := hF.part (o := o) (l := n) hb (by omega)
  unfold MemsetPre
  rw [hrdi, hrdx]
  refine ⟨hb.stackOk hF.stack (by decide), hp.1, hp.2, ?_⟩
  show (off (fb m0) o).toNat + n ≤ (rspOf d).toNat ∨ (rspOf d).toNat + 8 ≤ (off (fb m0) o).toNat
  rw [hsp, hF.off_toNat (by omega), hF.fb_toNat]
  omega

/-- **`memset` on a part of the frame**: the body after it. -/
theorem memset_post (hF : Facts m0) {d d' : MachineData} (hb : B m0 0 d) {o n : Nat}
    (hrdi : reg d .rdi = off (fb m0) o) (hrdx : (reg d .rdx).toNat = n)
    (hon : o + n ≤ 5072) (hpost : MemsetPost d d') (hrsp : rspOf d' = rspOf d + 8#64) :
    B m0 8 d' := by
  obtain ⟨-, -, hso, hsv⟩ := hpost
  rw [show reg d .rdi = off (fb m0) o from hrdi, show (reg d .rdx).toNat = n from hrdx] at hso
  have hnot : ∀ j, 5072 ≤ j → j < 5128 → ¬ NativeRustcVm.InRange (off (fb m0) o) n
      (off (fb m0) j) := fun j h1 h2 h ↦ by
    rw [inRange_off_iff (by omega) (by omega)] at h; omega
  exact hb.call hsv hrsp hso
    (fun q h ↦ Or.inr (inRange_frame_stack hF.rsp.2 hF.rsp.1 (by decide)
      (inRange_mono (hF.part_low (by omega) h) (by omega))))
    (fun p hp i hi ↦ hnot _ (by have := slots_ge p hp; omega) (by have := slots_le p hp; omega))
    (fun j hj ↦ hnot _ (by omega) (by omega))

end

variable [Host] {k : Nat} {m0 : MachineData}

/-- **The entry**: the prologue, `block_cols` and `block_sizes` zeroed, the loop's head. -/
theorem entry (hp : Placed code k) (hms : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hF : Facts m0) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b5Offset) ∧ I1 m0 0 0 s.data)
      ⟨m0, Labels.label NativeRustcVmX64.Vm.PlacementsOf.entryLabel⟩ := by
  rw [show Labels.label NativeRustcVmX64.Vm.PlacementsOf.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b0Offset) from hp.label NativeRustcVmX64.Vm.PlacementsOf.entry_at]
  have hslot := hF.got.1 "memset" (by simp)
  have hwf0 : (frameEnv m0 m0 5120 [(gotAddr "memset", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b0Offset + b0.length)).toBitVec).WF :=
    frame_wf ⟨frame_mapped hF.stack (by decide), frame_noWrap hF.stack (by decide)⟩
      (by intro x hx; simp only [List.mem_singleton] at hx; subst x
          exact ⟨hF.got.mapped (by simp), hslot.2.1⟩)
      (List.pairwise_pair.mpr (apart_frame hslot.2.2.1 hF.stack.1 (by decide)).symm)
  have hm0 : Match (frameEnv m0 m0 5120 [(gotAddr "memset", 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b0Offset + b0.length)).toBitVec)
      entryS m0 := by
    apply Match.withKnownBytes
    · exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial
        ⟨by simp [Sym.eval, Env.base, gotAddr], trivial⟩
    · intro i hi
      simpa [Sym.eval, Env.base, frameEnv] using hF.got.byte (by simp : "memset" ∈ ["memset"]) hi
  refine exec_then (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b0 hwf0 (fun _ _ ↦ rfl)
    hm0 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, h7, h6, h2, h3, h14, h15⟩ := ok_b0
  have hb1 : B m0 0 st1.data := Bd.entry_frame hF.stack (by decide) hwf0 hm1 hpro slots_le slots_cs
    b0_mem
  have hrdi1 : reg st1.data .rdi = off (fb m0) 1280 := (hm1.regs .rdi _ h7).trans (eval_ptr0 1280)
  have hrdx1 : (reg st1.data .rdx).toNat = 1264 := by
    show (st1.data.regs.get64 .rdx).toNat = _; rw [hm1.regs .rdx _ h2]; rfl
  refine call_then hpc1 hms (memset_pre hF hb1 hrdi1 hrdx1 (by omega) (by omega))
    fun st2 hpc2 hrsp2 hpost2 ↦ ?_
  have hb2 := memset_post hF hb1 hrdi1 hrdx1 (by omega) hpost2 hrsp2
  have hsv2 := hpost2.2.2.2
  -- `b1`: `block_sizes` zeroed
  obtain ⟨hok1, h17, h16, h12, -, hK1⟩ := ok_b1
  have hwf1 := fr_wf0 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b1Offset + b1.length)).toBitVec)
    hb2 hF.stack (by decide)
  have hmCached : Match (frameEnv m0 st2.data 5120 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.PlacementsOf.b1Offset + b1.length)).toBitVec)
      cachedS st2.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨hb2.fr.rsp_eval, (hsv2.1 .r12 rfl).trans (hm1.regs .r12 _ b0_target), trivial⟩
      trivial trivial trivial
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b1 hwf1
    (fun _ _ ↦ rfl) (hpc2.trans rfl) hmCached fun st3 hm3 hpc3 ↦ ?_
  have hb3 := hb2.of_block0 hF.stack (by decide) hm3 hok1 slots_le
  have hrdi3 : reg st3.data .rdi = off (fb m0) 2544 := (hm3.regs .rdi _ h17).trans (eval_ptr0 2544)
  have hrdx3 : (reg st3.data .rdx).toNat = 1264 := by
    show (st3.data.regs.get64 .rdx).toNat = _; rw [hm3.regs .rdx _ h12]; rfl
  refine call_then hpc3 hms (memset_pre hF hb3 hrdi3 hrdx3 (by omega) (by omega))
    fun st4 hpc4 hrsp4 hpost4 ↦ ?_
  have hb4 := memset_post hF hb3 hrdi3 hrdx3 (by omega) hpost4 hrsp4
  have hsv4 := hpost4.2.2.2
  -- `b2`: the loop's registers
  obtain ⟨hok2, hmem2, hax, h13, hbp, h12', hK2⟩ := ok_b2
  refine step0 hF (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) exit_b2 nofun (hpc4.trans rfl)
    hb4 hok2 hmem2 fun st5 hm5 hpc5 hb5 hd5 ↦ .done _ ⟨hpc5.trans (hp.label NativeRustcVmX64.Vm.PlacementsOf.label_2_at), ?_⟩
  -- the callee-saved registers through the calls
  have hr : ∀ r, calleeSaved r = true → (after b1 cachedS).reg r = some (.reg r) →
      reg st4.data r = reg st1.data r := fun r hc h ↦
    (hsv4.1 r hc).trans ((hm3.regs r _ h).trans (hsv2.1 r hc))
  refine ⟨hb5, by omega, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq ↦ absurd hq (by simp [below]),
    fun q hq ↦ absurd hq (by simp [below])⟩
  · show (st5.data.regs.get64 .rax).toNat = _; rw [hm5.regs .rax _ hax]; rfl
  · rw [kreg hm5 hK2 (by simp), hr .r15 rfl (keeps_reg_some hK1 (by simp)),
      show reg st1.data .r15 = _ from hm1.regs .r15 _ h15]
    rfl
  · show (st5.data.regs.get64 .r13).toNat = _; rw [hm5.regs .r13 _ h13]; rfl
  · exact hm5.regs .rbp _ hbp
  · exact hm5.regs .r12 _ h12'
  · rw [kreg hm5 hK2 (by simp), hr .r14 rfl (keeps_reg_some hK1 (by simp))]
    exact hm1.regs .r14 _ h14
  · rw [kreg hm5 hK2 (by simp), hr .rbx rfl (keeps_reg_some hK1 (by simp))]
    exact hm1.regs .rbx _ h3

end

end NativeRustcVmX64.Layout.PlacementsOf
