module

public import NativeVm.Code.Phase6.Claim
public import NativeVm.Code.Phase6.OutCp
public import NativeVm.Code.Phase5.Setup

/-!
# Phase 6's results in their regions

`wclC so vo` appends the committed outputs' column claim on `q_keccak` to the column claims at
`claimsR` (`wcl_spec`): its point `KECCAK`'s point (`eInst`) then the slot point (at `so`), its
value the word at `vo`. `wkoC` writes `q_keccak`'s point (`low` at `eLow`, the claim's point up to
`packBits`, the slot point) and its `64` slices (`eSl`) at `keccakR` (`wko_spec`). Neither writes
the scratch, and each writes no word outside its region.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wdisp wdisp_toUInt64 Env cw ctxWork eval_cw wp_done wp_then
  wp_ite_true wp_ite_false rf_refl setMem_wd_ne
  setMem_wd_eq)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- The committed outputs' claim appended at `claimsR`: the count `n` read and raised, `r12` at
slot `n` (`76 n` words as three shifts), the column, the point's size `|inst| + 6`, `inst` and the
slot point by `cpLoop`, the value. -/
def wclC (so vo : Nat) : List Stmt := [
  I (.load .rsi (cw ctxWork)),
  I (.load .rax (at_ .rsi (wdisp claimsR.off))),
  I (.mov .rcx .rax), I (.shli .rcx 9), I (.mov .rbx .rax), I (.shli .rbx 6), I (.add .rcx .rbx),
  I (.mov .rbx .rax), I (.shli .rbx 5), I (.add .rcx .rbx),
  I (.lea .r12 (at_ .rsi (wdisp (claimsR.off + 1)))), I (.add .r12 .rcx),
  I (.addi .rax 1), I (.store (at_ .rsi (wdisp claimsR.off)) .rax),
  I (.storei (at_ .r12 (wdisp 0)) (Int64.ofNat qkeccak)),
  I (.load .rdx (at_ .rbp (wdisp (2 * eInstN)))),
  I (.mov .rax .rdx), I (.addi .rax 6), I (.store (at_ .r12 (wdisp 1)) .rax),
  I (.lea .rcx (at_ .r12 (wdisp 2))), I (.lea .r8 (at_ .rbp (wdisp (2 * eInst)))), cpLoop,
  I (.movi .rdx 6), I (.lea .r8 (at_ .rbp (wdisp (2 * so)))), cpLoop,
  I (.load .rax (at_ .rbp (wdisp (2 * vo)))),
  I (.store (at_ .r12 (wdisp (1 + vecWords pointCap))) .rax),
  I (.load .rax (at_ .rbp (wdisp (2 * vo + 1)))),
  I (.store (at_ .r12 (wdisp (2 + vecWords pointCap))) .rax)]

theorem wcl_spec (hin : Inputs env inp s0.mem) {so vo : Nat} (hso : so + 6 ≤ scrN) (hvo : vo < scrN)
    {acc : Array ColumnClaimW} {inst slot : Array EW} {word : EW} (h : StA env s0 g t s)
    (hcl : ClaimsAt s.mem (claimsR.at env.work) acc)
    (hacc : acc.size < claimCap) (hinst : inst.size ≤ 30)
    (hinstN : g eInstN = EW.ofK inst.size.toUInt64)
    (hinstG : ∀ i < inst.size, g (eInst + i) = inst.getD i 0)
    (hslot : slot.size = 6) (hslotG : ∀ i < 6, g (so + i) = slot.getD i 0)
    (hword : g vo = word) :
    WP (blk (wclC so vo)) s (fun s' ↦ StA env s0 g t s' ∧
      ClaimsAt s'.mem (claimsR.at env.work)
        (acc ++ #[⟨qkeccak, inst.extract 0 4 ++ inst.extract 4 inst.size ++ slot, word⟩]) ∧
      ∀ a, ¬ claimsR.In env.work a → s'.mem a = s.mem a) (fun _ ↦ False) := by
  have hcw := claimWords_val
  have hcs := claimsR_size
  have hO := claimsR_off
  have hvp := vecWords_pointCap
  have hpc := pointCap_val
  have hcc := claimCap_val
  have hq61 : claimsR.off + claimsR.size ≤ 2 ^ 61 := by
    have := region_lt (inp := inp) claimsR_mem (j := claimsR.size - 1) (by omega)
    have := workWords_lt hin
    omega
  have hcnt : s.mem (wd env.work claimsR.off) = some acc.size.toUInt64 := hcl.2.1.2
  have hrdi : s.reg .rdi = env.ctx := h.2.1.1.1
  have hrbp : s.reg .rbp = sb env := h.2.2.1
  have hS := h.2.2.2
  set n := acc.size with hn
  set m := inst.size with hm
  have hn160 : n < 160 := by omega
  unfold wclC
  refine wp_load_st (eval_cw hrdi _) h.1.layout.workPtr h (by decide) (by decide) fun h ↦ ?_
  refine wp_load_st (eval_work (w := env.work) (by reg_simp) _)
    (by simp only [QState.setReg_mem]; exact hcnt) h (by decide) (by decide) fun h ↦ ?_
  iterate 11 refine wp_reg_st rfl h (by decide) (by decide) fun h ↦ ?_
  refine StA.name h fun s1 h e1 ↦ ?_
  have r1si : s1.reg .rsi = env.work := by rw [e1]; reg_simp
  have h1rbp : s1.reg .rbp = sb env := h.2.2.1
  have r1ax : s1.reg .rax = (n + 1).toUInt64 := by
    rw [e1]; reg_simp; rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl,
      NativeVm.Transcript.toUInt64_add]
  have r112 : s1.reg .r12 = wd env.work (claimsR.off + (1 + 76 * n)) := by
    rw [e1]
    simp only [NativeVm.Transcript.eval_at]
    reg_simp
    rw [wdisp_toUInt64, slot_sum, UInt64.add_assoc, NativeVm.Transcript.toUInt64_add, hcw,
      NativeVm.Transcript.wd]
    congr 2
    omega
  have m1 : s1.mem = s.mem := by rw [e1]; rfl
  clear e1
  have hIo : eInst + 30 ≤ scrN := by rw [scrN_val]; unfold eInst; omega
  have hNo : eInstN < scrN := by rw [scrN_val]; unfold eInstN; omega
  -- the count, the column, the point's size; the copy's pointers
  refine wp_store_st hin h outR_claims (j := 0) (by omega)
    ((eval_work r1si _).trans (by rw [Nat.add_zero])) fun h ↦ ?_
  refine wp_storei_st hin h outR_claims (j := 1 + 76 * n + 0) (by omega)
    (eval_region (by reg_simp; exact r112) 0) fun h ↦ ?_
  refine wp_load_st (eval_el h.2.2.1 _) (h.2.2.2.word0 hNo) h (by decide) (by decide) fun h ↦ ?_
  iterate 2 refine wp_reg_st rfl h (by decide) (by decide) fun h ↦ ?_
  refine wp_store_st hin h outR_claims (j := 1 + 76 * n + 1) (by omega)
    (eval_region (by reg_simp; exact r112) 1) fun h ↦ ?_
  iterate 2 refine wp_reg_st rfl h (by decide) (by decide) fun h ↦ ?_
  refine StA.name h fun s2 h e2 ↦ ?_
  have hIN : (g eInstN).c0 = m.toUInt64 := by rw [hinstN]; rfl
  have r2cx : s2.reg .rcx = wd env.work (claimsR.off + (1 + 76 * n + 2)) := by
    rw [e2]; reg_simp; exact eval_region r112 2
  have r28 : s2.reg .r8 = wd (sb env) (2 * eInst) := by
    rw [e2]; reg_simp; exact eval_el (by reg_simp; exact h1rbp) _
  have r2dx : s2.reg .rdx = m.toUInt64 := by rw [e2]; reg_simp; exact hIN
  have r212 : s2.reg .r12 = wd env.work (claimsR.off + (1 + 76 * n)) := by
    rw [e2]; reg_simp; exact r112
  have m2c : s2.mem (wd env.work (claimsR.off + 0)) = some (n + 1).toUInt64 := by
    rw [e2]
    simp (disch := omega) only [QState.setReg_mem, setMem_wd_ne, setMem_wd_eq]
    rw [r1ax]
  have m2d : s2.mem (wd env.work (claimsR.off + (1 + 76 * n))) = some (4 : Nat).toUInt64 := by
    rw [e2]
    simp (disch := omega) only [QState.setReg_mem, setMem_wd_ne, setMem_wd_eq]
    rfl
  have m2e : s2.mem (wd env.work (claimsR.off + (1 + 76 * n + 1))) = some (m + 6).toUInt64 := by
    rw [e2]
    simp (disch := omega) only [QState.setReg_mem, setMem_wd_eq]
    reg_simp
    rw [hIN, show (6 : UInt64) = (6 : Nat).toUInt64 from rfl, NativeVm.Transcript.toUInt64_add]
  have m2a : ∀ x < claimsR.size, x ≠ 0 → x ≠ 1 + 76 * n → x ≠ 1 + 76 * n + 1 →
      s2.mem (wd env.work (claimsR.off + x)) = s.mem (wd env.work (claimsR.off + x)) := by
    intro x hx h0 h1 h2
    rw [e2, ← m1]
    simp (disch := omega) only [QState.setReg_mem, setMem_wd_ne]
  have m2o : ∀ a, ¬ claimsR.In env.work a → s2.mem a = s.mem a := by
    intro a ha
    rw [e2, ← m1]
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_out ha]
  clear e2
  -- the copies
  refine wp_then (cpLoop_spec hin outR_claims (j0 := 1 + 76 * n + 2) (n := m) (o := eInst)
    (by omega) (by omega) h r2cx r28 r2dx) fun s3 ⟨h, hf3, hx3, hz3, hk3⟩ ↦ ?_
  have h3rbp : s3.reg .rbp = sb env := h.2.2.1
  iterate 2 refine wp_reg_st rfl h (by decide) (by decide) fun h ↦ ?_
  refine wp_then (cpLoop_spec hin outR_claims (j0 := 1 + 76 * n + 2 + 2 * m) (n := 6) (o := so)
    (by omega) hso h (by reg_simp; exact hx3) (by reg_simp; exact eval_el h3rbp _)
    (by reg_simp; rfl))
    fun s4 ⟨h, hf4, _, hz4, hk4⟩ ↦ ?_
  have r412 : s4.reg .r12 = wd env.work (claimsR.off + (1 + 76 * n)) := by
    rw [hf4 .r12 (by decide)]; reg_simp; rw [hf3 .r12 (by decide), r212]
  -- the value
  refine wp_load_st (eval_el h.2.2.1 _) (h.2.2.2.word0 hvo) h (by decide) (by decide) fun h ↦ ?_
  refine wp_store_st hin h outR_claims (j := 1 + 76 * n + (1 + vecWords pointCap)) (by omega)
    (eval_region (by reg_simp; exact r412) _) fun h ↦ ?_
  refine wp_load_st (eval_el h.2.2.1 _) (h.2.2.2.word1 hvo) h (by decide) (by decide) fun h ↦ ?_
  refine wp_store_st hin h outR_claims (j := 1 + 76 * n + (2 + vecWords pointCap)) (by omega)
    (eval_region (by reg_simp; exact r412) _) fun h ↦ ?_
  refine StA.name h fun s5 h e5 ↦ wp_done ⟨h, ?_⟩
  have m5v : EWAt s5.mem (wd env.work (claimsR.off + (1 + 76 * n + 74))) word := by
    rw [e5, ← hword]
    simp only [EWAt, NativeVm.Code.wd_wd, hvp]
    simp (disch := omega) only [QState.setReg_mem, setMem_wd_ne, setMem_wd_eq]
    reg_simp
    exact ⟨trivial, trivial⟩
  have m5a : ∀ x < claimsR.size, x ≠ 1 + 76 * n + 74 → x ≠ 1 + 76 * n + 75 →
      s5.mem (wd env.work (claimsR.off + x)) = s4.mem (wd env.work (claimsR.off + x)) := by
    intro x hx h1 h2
    rw [e5]
    simp (disch := omega) only [QState.setReg_mem, setMem_wd_ne, hvp]
  have m5o : ∀ a, ¬ claimsR.In env.work a → s5.mem a = s4.mem a := by
    intro a ha
    rw [e5]
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_out ha]
  clear e5
  have W : ∀ x y, x = y → s5.mem (wd env.work x) = s5.mem (wd env.work y) := fun _ _ e ↦ by rw [e]
  have kp : ∀ x < claimsR.size, (x < 1 + 76 * n + 2 ∨ 1 + 76 * n + 2 + 2 * m + 12 ≤ x) →
      x ≠ 1 + 76 * n + 74 → x ≠ 1 + 76 * n + 75 →
      s5.mem (wd env.work (claimsR.off + x)) = s2.mem (wd env.work (claimsR.off + x)) := by
    intro x hx h1 h2 h3
    rw [m5a x hx h2 h3, frame_idx hk4 (by omega) (by omega) (by omega), QState.setReg_mem,
      QState.setReg_mem, frame_idx hk3 (by omega) (by omega) (by omega)]
  have k3 : ∀ x, 1 + 76 * n + 2 ≤ x → x < 1 + 76 * n + 2 + 2 * m →
      s5.mem (wd env.work (claimsR.off + x)) = s3.mem (wd env.work (claimsR.off + x)) := by
    intro x h1 h2
    rw [m5a x (by omega) (by omega) (by omega), frame_idx hk4 (by omega) (by omega) (by omega),
      QState.setReg_mem, QState.setReg_mem]
  have k4 : ∀ x, 1 + 76 * n + 2 + 2 * m ≤ x → x < 1 + 76 * n + 2 + 2 * m + 12 →
      s5.mem (wd env.work (claimsR.off + x)) = s4.mem (wd env.work (claimsR.off + x)) :=
    fun x _ h2 ↦ m5a x (by omega) (by omega) (by omega)
  have hpt : inst.extract 0 4 ++ inst.extract 4 m ++ slot = inst ++ slot := by
    rw [hm, Array.extract_append_extract, Nat.min_def, ite_eq_left_iff.mpr ?_,
      Array.extract_eq_self_of_le (Nat.le_max_right _ _)]
    omega
  have hsz : (inst ++ slot).size = m + 6 := by rw [Array.size_append, hslot]
  rw [hpt]
  refine ⟨ClaimsAt.push hcl (by omega) ?_ ?_ ?_, fun a ha ↦ ?_⟩
  · rw [Region.at, W _ (claimsR.off + 0) (by omega),
      kp 0 (by omega) (by omega) (by omega) (by omega), m2c]
  · intro k hk0 hk
    rw [hcw] at hk
    rw [Region.at, NativeVm.Code.wd_wd, kp k (by omega) (by omega) (by omega) (by omega),
      m2a k (by omega) (by omega) (by omega) (by omega)]
  · rw [Region.at, NativeVm.Code.wd_wd, hcw]
    refine ⟨⟨show qkeccak < 2 ^ 64 by decide, ?_⟩, ⟨show (inst ++ slot).size ≤ pointCap by omega,
      ⟨show (inst ++ slot).size < 2 ^ 64 by omega, ?_⟩, fun i hi ↦ ?_⟩, ?_⟩
    · rw [kp _ (by omega) (by omega) (by omega) (by omega), m2d]
      rfl
    · rw [NativeVm.Code.wd_wd, W _ (claimsR.off + (1 + 76 * n + 1)) (by omega),
        kp _ (by omega) (by omega) (by omega) (by omega), m2e, hsz]
    · have hi6 : i < m + 6 := by rw [← hsz]; exact hi
      rw [NativeVm.Code.wd_wd, NativeVm.Code.wd_wd, NativeVm.Code.wd_wd]
      by_cases hi' : i < m
      · rw [Array.getElem_append_left hi', Array.getElem_eq_getD 0, ← hinstG i hi']
        refine EWAt.idx (y := claimsR.off + (1 + 76 * n + 2 + 2 * i)) (by omega) ?_
        exact EWAt.keepI (hz3 i hi') fun z h1 h2 ↦ k3 z (by omega) (by omega)
      · rw [Array.getElem_append_right (by omega), Array.getElem_eq_getD 0, ← hm,
          ← hslotG (i - m) (by omega)]
        refine EWAt.idx (y := claimsR.off + (1 + 76 * n + 2 + 2 * m + 2 * (i - m))) (by omega) ?_
        exact EWAt.keepI (hz4 (i - m) (by omega)) fun z h1 h2 ↦ k4 z (by omega) (by omega)
    · rw [NativeVm.Code.wd_wd, hvp]
      exact EWAt.idx (by omega) m5v
  · rw [m5o a ha, frame_out hk4 ha (by omega), QState.setReg_mem, QState.setReg_mem,
      frame_out hk3 ha (by omega), m2o a ha]

/-- `rdx := min(rdx, rax)`, unsigned. -/
def minDx : Stmt := .ite (.cmp .ltu .rax (.reg .rdx)) (blk [I (.mov .rdx .rax)]) (blk [])

theorem minDx_spec {a b : Nat} (h : StA env s0 g t s) (hax : s.reg .rax = a.toUInt64)
    (hdx : s.reg .rdx = b.toUInt64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) {E : QState → Prop} :
    WP minDx s (fun s' ↦ StA env s0 g t s' ∧ s'.mem = s.mem ∧ RegsFrame [.rdx] s s' ∧
      s'.reg .rdx = (min b a).toUInt64) E := by
  unfold minDx
  by_cases hab : a < b
  · refine wp_ite_true (by rw [NativeVm.Transcript.cond_ltu, NativeVm.Transcript.rhs_reg, hax, hdx,
      decide_eq_true_iff]; exact (toUInt64_lt' ha hb).mpr hab) (WP.ins (by rfl) ?_)
    refine ⟨h.setReg (by decide) (by decide) _, rfl, by rf_tac, ?_⟩
    reg_simp
    rw [hax, Nat.min_eq_right (by omega)]
  · refine wp_ite_false (by rw [NativeVm.Transcript.cond_ltu, NativeVm.Transcript.rhs_reg, hax, hdx,
      decide_eq_false_iff_not]; exact fun e ↦ hab ((toUInt64_lt' ha hb).mp e)) (WP.skip ?_)
    exact ⟨h, rfl, rf_refl _ _, by rw [hdx, Nat.min_eq_left (by omega)]⟩

/-- The elements of `q_keccak`'s point `low ++ pt[..pb] ++ slot`. -/
theorem koPoint_get {low pt slot : Array EW} {pb i : Nat} (hlow : low.size = 4)
    (hi : i < (low ++ pt.extract 0 pb ++ slot).size) :
    (low ++ pt.extract 0 pb ++ slot)[i] = if i < 4 then low.getD i 0
      else if i < 4 + min pb pt.size then pt.getD (i - 4) 0
      else slot.getD (i - 4 - min pb pt.size) 0 := by
  simp only [Array.size_append, Array.size_extract, hlow] at hi
  by_cases h1 : i < 4
  · rw [Array.getElem_append_left (by simp [hlow]; omega), Array.getElem_append_left (by omega),
      Array.getElem_eq_getD 0]
    simp only [h1, ↓reduceIte]
  · by_cases h2 : i < 4 + min pb pt.size
    · rw [Array.getElem_append_left (by simp [hlow]; omega), Array.getElem_append_right (by omega),
        Array.getElem_extract, Array.getElem_eq_getD 0]
      simp [h1, h2, hlow]
    · rw [Array.getElem_append_right (by simp [hlow]; omega), Array.getElem_eq_getD 0]
      simp [h1, h2, hlow, Nat.sub_sub]

/-- `q_keccak`'s point and slices at `keccakR`: the point's size `4 + min(pb, |pt|) + 6`, then
`low`, `pt`'s first `min(pb, |pt|)` coordinates and the slot point, by `cpLoop`, and the slices. -/
def wkoC : List Stmt := [
  I (.load .rsi (cw ctxWork)),
  I (.load .rdx (at_ .rbp (wdisp (2 * ePB)))), I (.load .rax (at_ .rbp (wdisp (2 * ePtN)))), minDx,
  I (.mov .rbx .rdx), I (.mov .rax .rdx), I (.addi .rax 10),
  I (.store (at_ .rsi (wdisp keccakR.off)) .rax),
  I (.lea .rcx (at_ .rsi (wdisp (keccakR.off + 1)))), I (.lea .r8 (at_ .rbp (wdisp (2 * eLow)))),
  I (.movi .rdx 4), cpLoop,
  I (.mov .rdx .rbx), I (.lea .r8 (at_ .rbp (wdisp (2 * ePt)))), cpLoop,
  I (.movi .rdx 6), I (.lea .r8 (at_ .rbp (wdisp (2 * eSlot)))), cpLoop,
  I (.lea .rcx (at_ .rsi (wdisp (keccakR.off + vecWords pointCap)))),
  I (.lea .r8 (at_ .rbp (wdisp (2 * eSl)))), I (.movi .rdx 64), cpLoop]

theorem wko_spec (hin : Inputs env inp s0.mem) {low pt slot slices : Array EW} {pb : Nat}
    (h : StA env s0 g t s) (hlow : low.size = 4) (hlowG : ∀ i < 4, g (eLow + i) = low.getD i 0)
    (hpt : pt.size < 32) (hptN : g ePtN = EW.ofK pt.size.toUInt64)
    (hptG : ∀ i < pt.size, g (ePt + i) = pt.getD i 0)
    (hpb : g ePB = EW.ofK pb.toUInt64) (hpb26 : pb ≤ 26)
    (hslot : slot.size = 6) (hslotG : ∀ i < 6, g (eSlot + i) = slot.getD i 0)
    (hsl : slices.size = 64) (hslG : ∀ z < 64, g (eSl + z) = slices.getD z 0) :
    WP (blk wkoC) s (fun s' ↦ StA env s0 g t s' ∧
      KeccakOutAt s'.mem (keccakR.at env.work) (low ++ pt.extract 0 pb ++ slot) slices ∧
      ∀ a, ¬ keccakR.In env.work a → s'.mem a = s.mem a) (fun _ ↦ False) := by
  have hO : keccakR.off = 27730 := by decide
  have hKs : keccakR.size = 201 := by decide
  have hvp := vecWords_pointCap
  have hpc := pointCap_val
  have hq61 : keccakR.off + keccakR.size ≤ 2 ^ 61 := by
    have := region_lt (inp := inp) outR_keccak.reg (j := keccakR.size - 1) (by omega)
    have := workWords_lt hin
    omega
  have hN := scrN_val
  have hPBo : ePB < scrN := by unfold ePB; omega
  have hPNo : ePtN < scrN := by unfold ePtN; omega
  have hLo : eLow + 4 ≤ scrN := by unfold eLow; omega
  have hPo : ePt + 32 ≤ scrN := by unfold ePt; omega
  have hSo : eSlot + 6 ≤ scrN := by unfold eSlot; omega
  have hSlo : eSl + 64 ≤ scrN := by unfold eSl; omega
  set k := min pb pt.size with hk
  have hk32 : k < 32 := by omega
  unfold wkoC
  refine wp_load_st (eval_cw h.2.1.1.1 _) h.1.layout.workPtr h (by decide) (by decide) fun h ↦ ?_
  refine wp_load_st (eval_el h.2.2.1 _) (h.2.2.2.word0 hPBo) h (by decide) (by decide) fun h ↦ ?_
  refine wp_load_st (eval_el h.2.2.1 _) (h.2.2.2.word0 hPNo) h (by decide) (by decide) fun h ↦ ?_
  refine wp_then (minDx_spec (a := pt.size) (b := pb) h (by reg_simp; rw [hptN]; rfl)
    (by reg_simp; rw [hpb]; rfl) (by omega) (by omega)) fun s1 ⟨h, hm1, hf1, h1dx⟩ ↦ ?_
  have r1si : s1.reg .rsi = env.work := by rw [hf1 .rsi (by decide)]; reg_simp
  have h1rbp : s1.reg .rbp = sb env := h.2.2.1
  iterate 3 refine wp_reg_st rfl h (by decide) (by decide) fun h ↦ ?_
  refine wp_store_st hin h outR_keccak (j := 0) (by omega)
    ((eval_work (by reg_simp; exact r1si) _).trans (by rw [Nat.add_zero])) fun h ↦ ?_
  iterate 3 refine wp_reg_st rfl h (by decide) (by decide) fun h ↦ ?_
  refine StA.name h fun s2 h e2 ↦ ?_
  have r2si : s2.reg .rsi = env.work := by rw [e2]; reg_simp; exact r1si
  have r2bx : s2.reg .rbx = k.toUInt64 := by rw [e2]; reg_simp; exact h1dx
  have r2cx : s2.reg .rcx = wd env.work (keccakR.off + 1) := by
    rw [e2]; reg_simp; exact eval_work (by reg_simp; exact r1si) _
  have r28 : s2.reg .r8 = wd (sb env) (2 * eLow) := by
    rw [e2]; reg_simp; exact eval_el (by reg_simp; exact h1rbp) _
  have r2dx : s2.reg .rdx = (4 : Nat).toUInt64 := by rw [e2]; reg_simp; rfl
  have m2c : s2.mem (wd env.work (keccakR.off + 0)) = some (4 + k + 6).toUInt64 := by
    rw [e2]
    simp (disch := omega) only [QState.setReg_mem, setMem_wd_eq]
    reg_simp
    rw [h1dx, show (10 : UInt64) = (10 : Nat).toUInt64 from rfl, NativeVm.Transcript.toUInt64_add]
    congr 2
    omega
  have m2o : ∀ a, ¬ keccakR.In env.work a → s2.mem a = s.mem a := by
    intro a ha
    rw [e2]
    simp (disch := omega) only [QState.setReg_mem, mem_setMem_out ha]
    rw [hm1]
    rfl
  clear e2
  -- the point and the slices
  refine wp_then (cpLoop_spec hin outR_keccak (j0 := 1) (n := 4) (o := eLow) (by omega) hLo h r2cx
    r28 r2dx) fun s3 ⟨h, hf3, hx3, hz3, hk3⟩ ↦ ?_
  have h3rbp : s3.reg .rbp = sb env := h.2.2.1
  iterate 2 refine wp_reg_st rfl h (by decide) (by decide) fun h ↦ ?_
  refine wp_then (cpLoop_spec hin outR_keccak (j0 := 1 + 2 * 4) (n := k) (o := ePt) (by omega)
    (by omega) h (by reg_simp; exact hx3) (by reg_simp; exact eval_el h3rbp _)
    (by reg_simp; rw [hf3 .rbx (by decide), r2bx])) fun s4 ⟨h, hf4, hx4, hz4, hk4⟩ ↦ ?_
  have h4rbp : s4.reg .rbp = sb env := h.2.2.1
  iterate 2 refine wp_reg_st rfl h (by decide) (by decide) fun h ↦ ?_
  refine wp_then (cpLoop_spec hin outR_keccak (j0 := 1 + 2 * 4 + 2 * k) (n := 6) (o := eSlot)
    (by omega) hSo h (by reg_simp; exact hx4) (by reg_simp; exact eval_el h4rbp _)
    (by reg_simp; rfl)) fun s5 ⟨h, hf5, _, hz5, hk5⟩ ↦ ?_
  have h5rbp : s5.reg .rbp = sb env := h.2.2.1
  have r5si : s5.reg .rsi = env.work := by
    rw [hf5 .rsi (by decide)]; reg_simp; rw [hf4 .rsi (by decide)]; reg_simp
    rw [hf3 .rsi (by decide), r2si]
  iterate 3 refine wp_reg_st rfl h (by decide) (by decide) fun h ↦ ?_
  refine wp_then (cpLoop_spec hin outR_keccak (j0 := vecWords pointCap) (n := 64) (o := eSl)
    (by omega) hSlo h (by reg_simp; exact eval_work r5si _) (by reg_simp; exact eval_el h5rbp _)
    (by reg_simp; rfl)) fun s6 ⟨h, _, _, hz6, hk6⟩ ↦ wp_done ⟨h, ?_⟩
  simp only [QState.setReg_mem] at hk4 hk5 hk6
  have W : ∀ x y, x = y → s6.mem (wd env.work x) = s6.mem (wd env.work y) := fun _ _ e ↦ by rw [e]
  have k5 : ∀ x < vecWords pointCap,
      s6.mem (wd env.work (keccakR.off + x)) = s5.mem (wd env.work (keccakR.off + x)) :=
    fun x hx ↦ frame_idx hk6 (by omega) (by omega) (by omega)
  have k4 : ∀ x < 1 + 2 * 4 + 2 * k,
      s6.mem (wd env.work (keccakR.off + x)) = s4.mem (wd env.work (keccakR.off + x)) :=
    fun x hx ↦ by rw [k5 x (by omega), frame_idx hk5 (by omega) (by omega) (by omega)]
  have k3 : ∀ x < 1 + 2 * 4,
      s6.mem (wd env.work (keccakR.off + x)) = s3.mem (wd env.work (keccakR.off + x)) :=
    fun x hx ↦ by rw [k4 x (by omega), frame_idx hk4 (by omega) (by omega) (by omega)]
  have hsz : (low ++ pt.extract 0 pb ++ slot).size = 4 + k + 6 := by
    simp [hlow, hslot, hk]
    omega
  refine ⟨⟨⟨by rw [hsz]; omega, ⟨by rw [hsz]; omega, ?_⟩, fun i hi ↦ ?_⟩, by rw [hsl]; rfl,
    fun z hz ↦ ?_⟩, fun a ha ↦ ?_⟩
  · rw [Region.at, W _ (keccakR.off + 0) (by omega), k3 0 (by omega),
      frame_idx hk3 (by omega) (by omega) (by omega), m2c, hsz]
  · have hi' : i < 4 + k + 6 := by rw [← hsz]; exact hi
    rw [Region.at, NativeVm.Code.wd_wd, NativeVm.Code.wd_wd, koPoint_get hlow hi]
    split_ifs with h1 h2
    · rw [← hlowG i h1]
      refine EWAt.idx (y := keccakR.off + (1 + 2 * i)) (by omega) ?_
      exact EWAt.keepI (hz3 i h1) fun z _ _ ↦ k3 z (by omega)
    · rw [← hptG (i - 4) (by omega)]
      refine EWAt.idx (y := keccakR.off + (1 + 2 * 4 + 2 * (i - 4))) (by omega) ?_
      exact EWAt.keepI (hz4 (i - 4) (by omega)) fun z _ _ ↦ k4 z (by omega)
    · rw [← hslotG (i - 4 - k) (by omega)]
      refine EWAt.idx (y := keccakR.off + (1 + 2 * 4 + 2 * k + 2 * (i - 4 - k))) (by omega) ?_
      exact EWAt.keepI (hz5 (i - 4 - k) (by omega)) fun z _ _ ↦ k5 z (by omega)
  · rw [hsl] at hz
    rw [Region.at, NativeVm.Code.wd_wd, NativeVm.Code.wd_wd, Array.getElem_eq_getD 0, ← hslG z hz]
    exact EWAt.idx (by omega) (hz6 z hz)
  · rw [frame_out hk6 ha (by omega), frame_out hk5 ha (by omega), frame_out hk4 ha (by omega),
      frame_out hk3 ha (by omega), m2o a ha]

end NativeVm.Code.P6
