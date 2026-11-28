module

public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Steps
public import NativeRustcVm.Transcript.Update

/-!
# `verify_keccak`: what a change keeps

Changes as numbers: a callee's stack (`stk_nat`), the frame's bytes (`loc_nat`), a block's
writes (`written_nat`). What stays where a change misses it: the `TState` (`ts_keep`), the column
claims (`cls_keep`), elements (`ews_keep`), a word (`word_keep`), and the entry's read-only data
(`rc_at`, `proj_at`, `rho_at`, `ews_m0`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)
open NativeRustcVm (Region)
open NativeRustcVm.Layout (Same)

public section

variable {m0 : MachineData}

section
variable [Labels] {a : DecArea} {inst : Array EW}

/-- A callee's stack as numbers. -/
theorem stk_nat (hn : Nums a inst m0) {st : MachineData} (hfr : VFr m0 st) {N' : Nat}
    (hN' : N' ≤ 3648) {q : BitVec 64} (h : InRange (stackBelow st N') N' q) :
    m0.regs.SP.toNat - 3360 - N' ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 := by
  have := hn.hN
  have := m0.regs.SP.toNat_lt
  have h1 := inR_nat (by rw [sb_toNat hn.hN hfr hN']; omega) h
  rw [sb_toNat hn.hN hfr hN'] at h1
  omega

/-- Frame bytes as numbers. -/
theorem loc_nat (hn : Nums a inst m0) {o n : Nat} (ho : o + n ≤ 3360) {q : BitVec 64}
    (h : InRange (loc m0 o) n q) :
    m0.regs.SP.toNat - 3360 + o ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 + o + n := by
  have := hn.hN
  have := m0.regs.SP.toNat_lt
  have h1 := inR_nat (by rw [loc_toNat hn.hN (by omega)]; omega) h
  rw [loc_toNat hn.hN (by omega)] at h1
  exact h1

/-- **A block's writes**, all below the slots of the frame (region 0), as numbers. -/
theorem written_nat (hn : Nums a inst m0) {rs : List (BitVec 64 × Nat)} {m st : MachineData}
    {S : SState} (hm : Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S st)
    (hwf : (Env.ofMachine m ((fb m0, 3360) :: rs)).WF)
    {L : Nat} (hw : S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ L)) = true) :
    SameOutside m.dmem st.dmem (fun q ↦
      m0.regs.SP.toNat - 3360 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 + L) := by
  have hs := hm.sameOutside hwf
  refine NativeRustcVm.SameOutside.mono hs fun q ⟨w, hw', b, sz, hb, h1, h2⟩ ↦ ?_
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨hr, hle⟩ := hw w hw'
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have := fb_toNat hn.hN
  have := hn.hN
  omega

/-- **A transcript callee's change** as numbers: a frame output, the `TState`, its stack. -/
theorem tR_nat (hn : Nums a inst m0) {st : MachineData} (hfr : VFr m0 st) {o n N' : Nat}
    (ho : o + n ≤ 3360) (hN' : N' ≤ 3648) {q : BitVec 64}
    (h : InRange (loc m0 o) n q ∨ InRange (tA m0) tstateBytes q ∨
      InRange (stackBelow st N') N' q) :
    (m0.regs.SP.toNat - 3360 + o ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 + o + n) ∨
      ((tA m0).toNat ≤ q.toNat ∧ q.toNat < (tA m0).toNat + 760) ∨
      (m0.regs.SP.toNat - 3360 - N' ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360) := by
  rcases h with h | h | h
  · exact .inl (loc_nat hn ho h)
  · exact .inr (.inl (inR_nat (n := tstateBytes) hn.tW h))
  · exact .inr (.inr (stk_nat hn hfr hN' h))

/-- **A block's writes** in the frame's ranges `rs` (offsets), as numbers. -/
theorem written_in (hn : Nums a inst m0) {rs : List (BitVec 64 × Nat)} {m st : MachineData}
    {S : SState} (hm : Match (Env.ofMachine m ((fb m0, 3360) :: rs)) S st)
    (hwf : (Env.ofMachine m ((fb m0, 3360) :: rs)).WF) {L : List (Nat × Nat)}
    (hw : S.mem.all (fun w ↦ w.r == 0 &&
      L.any (fun p ↦ decide (p.1 ≤ w.off) && decide (w.off + w.n ≤ p.2))) = true) :
    SameOutside m.dmem st.dmem (fun q ↦ ∃ p ∈ L,
      m0.regs.SP.toNat - 3360 + p.1 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360 + p.2) := by
  have hs := hm.sameOutside hwf
  refine NativeRustcVm.SameOutside.mono hs fun q ⟨w, hw', b, sz, hb, h1, h2⟩ ↦ ?_
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
    decide_eq_true_eq] at hw
  obtain ⟨hr, p, hp, hlo, hhi⟩ := hw w hw'
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have := fb_toNat hn.hN
  exact ⟨p, hp, by omega, by omega⟩

/-- **The `TState`** stays where a change misses it and its decoded words. -/
theorem ts_keep (hn : Nums a inst m0) {d d' : Mem 64} {R : BitVec 64 → Prop} {s' : TState}
    (hts : TStateAt d (tA m0) a s') (hk : Kept d d') (hs : SameOutside d d' R)
    (hR : ∀ q, R q → (q.toNat < (tA m0).toNat ∨ (tA m0).toNat + 760 ≤ q.toNat) ∧
      (q.toNat < a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ q.toNat)) :
    TStateAt d' (tA m0) a s' :=
  have e : tstateBytes = 760 := rfl
  hts.frame hk (fun q hq ↦ ⟨fun ht ↦ by
      have := inR_nat (n := tstateBytes) hn.tW ht; have := hR q hq; omega,
    fun ht ↦ by have := inR_nat hn.wW ht; have := hR q hq; omega⟩) hs

/-- **The column claims** stay where a change misses them. -/
theorem cls_keep (hn : Nums a inst m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    {cs : Array ColumnClaimW} (hc : NativeRustcVm.Layout.ClaimsWAt d (clA m0) cs)
    (hs : SameOutside d d' R)
    (hR : ∀ q, R q → q.toNat < (clA m0).toNat ∨ (clA m0).toNat + 97288 ≤ q.toNat) :
    NativeRustcVm.Layout.ClaimsWAt d' (clA m0) cs :=
  NativeRustcVm.Tables.ClaimsWAt.of_same hc (same_num hs hn.cW hR)

end

/-- **Elements** stay where a change misses them. -/
theorem ews_keep {d d' : Mem 64} {R : BitVec 64 → Prop} {A : BitVec 64} {xs : List EW}
    (h : NativeRustcVm.EWsAt d A xs) (hs : SameOutside d d' R)
    (hA : A.toNat + 16 * xs.length ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < A.toNat ∨ A.toNat + 16 * xs.length ≤ q.toNat) :
    NativeRustcVm.EWsAt d' A xs :=
  NativeRustcVm.Tables.EWsAt.of_same h (same_num hs hA hR) le_rfl

/-- **A word** stays where a change misses it. -/
theorem word_keep {d d' : Mem 64} {R : BitVec 64 → Prop} {A : BitVec 64} {w : UInt64}
    (h : NativeRustcVm.WordAt d A w) (hs : SameOutside d d' R) (hA : A.toNat + 8 ≤ 2 ^ 64)
    (hR : ∀ q, R q → q.toNat < A.toNat ∨ A.toNat + 8 ≤ q.toNat) :
    NativeRustcVm.WordAt d' A w :=
  NativeRustcVm.Layout.WordAt.of_same h (same_num hs hA hR) le_rfl

/-! ## The entry's read-only data in the frame's states -/

section
variable [Labels] {a : DecArea} {inst : Array EW}

/-- Bytes the function only reads stay as at the entry. -/
theorem bytes_m0 (hn : Nums a inst m0) {m : MachineData} (hfr : VFr m0 m) {A : BitVec 64}
    {bs : List UInt8} (hb : NativeRustcVm.BytesAt m0.dmem A bs)
    (hA : A.toNat + bs.length ≤ 2 ^ 64)
    (hS : A.toNat + bs.length ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ A.toNat)
    (hO : ∀ q, outs m0 q → q.toNat < A.toNat ∨ A.toNat + bs.length ≤ q.toNat) :
    NativeRustcVm.BytesAt m.dmem A bs :=
  NativeRustcVm.Layout.BytesAt.of_same hb (same_num hfr.same hA fun q hq ↦ by
    rcases hq with hq | hq
    · have := hn.hN
      rw [stack_eq] at hq
      have h1 := inR_nat (by rw [base_toNat (by omega)]; have := m0.regs.SP.toNat_lt; omega) hq
      rw [base_toNat (by omega)] at h1
      omega
    · exact hO q hq) le_rfl

end

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
