module

public import NativeRustcVmX64.KeccakGkr.KeccakPhase.Model
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Frame

/-!
# `keccak_phase`: its frame and its regions as numbers

The 480 bytes below the entry's RSP and the return address are the frame (`Fn.Body`, the six
pushes at `432`); until `verify_keccak` the code writes only the frame (`W1`), in all the outputs
and the stack (`W2`, `Writes`'s). The regions of the precondition's `Areas` as numbers (`Nums`:
`B` the frame's base, `K` the stack's).
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVmX64.KeccakGkr.Fn
open NativeRustcVm (Region InAny)
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)

@[expose] public section

/-- The bytes of the frame below the entry's RSP. -/
abbrev W1 (m0 : MachineData) (q : BitVec 64) : Prop :=
  (stackBelow m0 480).toNat ≤ q.toNat ∧ q.toNat < (stackBelow m0 480).toNat + 480

/-- The regions `keccak_phase` writes. -/
abbrev wsOf (m0 : MachineData) : List Region :=
  [⟨reg m0 .rdi, tstateBytes⟩, ⟨reg m0 .rcx, scratchBytes⟩,
    ⟨reg m0 .r8, NativeRustcVm.Layout.claimsBytes⟩, ⟨reg m0 .r9, outBytes⟩]

/-- The bytes `keccak_phase` may change. -/
abbrev W2 (m0 : MachineData) : BitVec 64 → Prop :=
  InAny (⟨stackBelow m0 keccakPhaseStack, keccakPhaseStack⟩ :: wsOf m0)

/-- **The regions as numbers.** -/
structure Nums [Labels] (a : DecArea) (m0 : MachineData) : Prop where
  hB : (stackBelow m0 480).toNat + 480 = (rspOf m0).toNat
  hK : (stackBelow m0 keccakPhaseStack).toNat + 480 + verifyKeccakStack = (rspOf m0).toNat
  top : (rspOf m0).toNat + 8 ≤ 2 ^ 64
  tW : (reg m0 .rdi).toNat + 760 ≤ 2 ^ 64
  sW : (reg m0 .rcx).toNat + 205824 ≤ 2 ^ 64
  cW : (reg m0 .r8).toNat + 97288 ≤ 2 ^ 64
  oW : (reg m0 .r9).toNat + 1608 ≤ 2 ^ 64
  wW : a.words.toNat + 8 * a.len ≤ 2 ^ 64
  eW : (reg m0 .rdx).toNat + 11808 ≤ 2 ^ 64
  rcW : rcAddr.toNat + 192 ≤ 2 ^ 64
  pjW : projectAddr.toNat + 128 ≤ 2 ^ 64
  rhW : rhoAddr.toNat + 100 ≤ 2 ^ 64
  tS : Sep (reg m0 .rdi).toNat 760 (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)
  sS : Sep (reg m0 .rcx).toNat 205824 (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)
  cS : Sep (reg m0 .r8).toNat 97288 (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)
  oS : Sep (reg m0 .r9).toNat 1608 (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)
  wS : Sep a.words.toNat (8 * a.len) (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)
  eS : Sep (reg m0 .rdx).toNat 11808 (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)
  rcS : Sep rcAddr.toNat 192 (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)
  pjS : Sep projectAddr.toNat 128 (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)
  rhS : Sep rhoAddr.toNat 100 (stackBelow m0 keccakPhaseStack).toNat (keccakPhaseStack + 8)
  ts : Sep (reg m0 .rdi).toNat 760 (reg m0 .rcx).toNat 205824
  tc : Sep (reg m0 .rdi).toNat 760 (reg m0 .r8).toNat 97288
  tou : Sep (reg m0 .rdi).toNat 760 (reg m0 .r9).toNat 1608
  sc : Sep (reg m0 .rcx).toNat 205824 (reg m0 .r8).toNat 97288
  so : Sep (reg m0 .rcx).toNat 205824 (reg m0 .r9).toNat 1608
  co : Sep (reg m0 .r8).toNat 97288 (reg m0 .r9).toNat 1608
  tw : Sep (reg m0 .rdi).toNat 760 a.words.toNat (8 * a.len)
  te : Sep (reg m0 .rdi).toNat 760 (reg m0 .rdx).toNat 11808
  trc : Sep (reg m0 .rdi).toNat 760 rcAddr.toNat 192
  tpj : Sep (reg m0 .rdi).toNat 760 projectAddr.toNat 128
  trh : Sep (reg m0 .rdi).toNat 760 rhoAddr.toNat 100
  sw : Sep (reg m0 .rcx).toNat 205824 a.words.toNat (8 * a.len)
  se : Sep (reg m0 .rcx).toNat 205824 (reg m0 .rdx).toNat 11808
  src : Sep (reg m0 .rcx).toNat 205824 rcAddr.toNat 192
  spj : Sep (reg m0 .rcx).toNat 205824 projectAddr.toNat 128
  srh : Sep (reg m0 .rcx).toNat 205824 rhoAddr.toNat 100
  cw : Sep (reg m0 .r8).toNat 97288 a.words.toNat (8 * a.len)
  ce : Sep (reg m0 .r8).toNat 97288 (reg m0 .rdx).toNat 11808
  crc : Sep (reg m0 .r8).toNat 97288 rcAddr.toNat 192
  cpj : Sep (reg m0 .r8).toNat 97288 projectAddr.toNat 128
  crh : Sep (reg m0 .r8).toNat 97288 rhoAddr.toNat 100
  ow : Sep (reg m0 .r9).toNat 1608 a.words.toNat (8 * a.len)
  oe : Sep (reg m0 .r9).toNat 1608 (reg m0 .rdx).toNat 11808
  orc : Sep (reg m0 .r9).toNat 1608 rcAddr.toNat 192
  opj : Sep (reg m0 .r9).toNat 1608 projectAddr.toNat 128
  orh : Sep (reg m0 .r9).toNat 1608 rhoAddr.toNat 100

end

public section

theorem kps_eq : keccakPhaseStack = 480 + verifyKeccakStack := rfl

theorem tsz : tstateBytes = 760 := rfl
theorem ssz : scratchBytes = 205824 := rfl
theorem csz : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
theorem osz : outBytes = 1608 := rfl
theorem esz : NativeRustcVm.Tables.tableEvalsBytes = 11808 := rfl

theorem slots_le : ∀ p ∈ slots, 432 ≤ p.1 ∧ p.1 + 8 ≤ 480 := by decide

theorem slots_cs : ∀ r, calleeSaved r = true → ∃ p ∈ slots, p.2 = r := by
  intro r hr
  cases r <;> simp_all [calleeSaved, slots]

variable {m0 : MachineData}

/-- **The regions as numbers**, from the precondition's footprint. -/
theorem nums_of [Labels] {a : DecArea} (hS : StackOk m0 keccakPhaseStack)
    (hA : Areas m0 keccakPhaseStack (wsOf m0)
      [a.region, ⟨reg m0 .rdx, NativeRustcVm.Tables.tableEvalsBytes⟩, rcRegion, projectRegion,
        rhoRegion]) : Nums a m0 := by
  have h3 := hS.1
  have h4 := hS.2.1
  have hKV := kps_eq
  have hB : (stackBelow m0 480).toNat + 480 = (rspOf m0).toNat := by
    rw [stackBelow_toNat (by omega)]; omega
  have hK : (stackBelow m0 keccakPhaseStack).toNat + 480 + verifyKeccakStack =
      (rspOf m0).toNat := by
    rw [stackBelow_toNat h3]; omega
  obtain ⟨hNW, hwS, hrS, hww, hwr⟩ := Areas.nat hA
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.pairwise_cons, List.Pairwise.nil, and_true, DecArea.region, rcRegion,
    projectRegion, rhoRegion, or_assoc, wsOf, tsz, ssz, csz, osz, esz] at hNW hwS hrS hww hwr
  obtain ⟨tW, sW, cW, oW, wW, eW, rcW, pjW, rhW⟩ := hNW
  obtain ⟨tS, sS, cS, oS⟩ := hwS
  obtain ⟨wS, eS, rcS, pjS, rhS⟩ := hrS
  obtain ⟨⟨ts, tc, tou⟩, ⟨sc, so⟩, co, -⟩ := hww
  obtain ⟨⟨tw, te, trc, tpj, trh⟩, ⟨sw, se, src, spj, srh⟩, ⟨cw, ce, crc, cpj, crh⟩,
    ⟨ow, oe, orc, opj, orh⟩⟩ := hwr
  exact ⟨hB, hK, h4, tW, sW, cW, oW, wW, eW, rcW, pjW, rhW, tS, sS, cS, oS,
    wS, eS, rcS, pjS, rhS,
    ts, tc, tou, sc, so, co, tw, te, trc, tpj, trh, sw, se, src, spj, srh, cw, ce, crc, cpj, crh,
    ow, oe, orc, opj, orh⟩

theorem geo1 (hS : StackOk m0 keccakPhaseStack) : Geo m0 480 488 432 slots (W1 m0) where
  hF := by have := hS.1; rw [kps_eq] at this; omega
  hZ := by
    have := hS.1; have := hS.2.1; rw [kps_eq] at *
    omega
  FZ := by omega
  LF := by omega
  map := frame_mapped hS (by rw [kps_eq]; omega)
  sl := slots_le
  cs := slots_cs
  low j hj := by
    have := hS.1; have := hS.2.1; rw [kps_eq] at *
    have hb : (stackBelow m0 480).toNat = (rspOf m0).toNat - 480 := stackBelow_toNat (by omega)
    unfold W1
    rw [toNat_off (by rw [hb]; omega)]
    constructor <;> omega

theorem w12 [Labels] {a : DecArea} (hn : Nums a m0) : ∀ q, W1 m0 q → W2 m0 q := by
  intro q ⟨h1, h2⟩
  have := hn.hB; have := hn.hK; have := hn.top; have hKV := kps_eq
  refine ⟨_, List.mem_cons_self, ?_⟩
  show NativeRustcVm.InRange (stackBelow m0 keccakPhaseStack) keccakPhaseStack q
  rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; omega)]
  omega

theorem geo2 [Labels] {a : DecArea} (hS : StackOk m0 keccakPhaseStack) (hn : Nums a m0) :
    Geo m0 480 488 432 slots (W2 m0) :=
  (geo1 hS).weaken (w12 hn)

/-- A byte of `W2` as numbers. -/
theorem w2_nat [Labels] {a : DecArea} (hn : Nums a m0) {q : BitVec 64} (h : W2 m0 q) :
    ((stackBelow m0 keccakPhaseStack).toNat ≤ q.toNat ∧
        q.toNat < (stackBelow m0 keccakPhaseStack).toNat + keccakPhaseStack) ∨
      ((reg m0 .rdi).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rdi).toNat + 760) ∨
      ((reg m0 .rcx).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .rcx).toNat + 205824) ∨
      ((reg m0 .r8).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .r8).toNat + 97288) ∨
      ((reg m0 .r9).toNat ≤ q.toNat ∧ q.toNat < (reg m0 .r9).toNat + 1608) := by
  obtain ⟨r, hr, hq⟩ := h
  have := hn.hB; have := hn.hK; have := hn.top; have hKV := kps_eq
  simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact .inl (inR_nat (by omega) hq)
  · exact .inr (.inl (inR_nat hn.tW hq))
  · exact .inr (.inr (.inl (inR_nat hn.sW hq)))
  · exact .inr (.inr (.inr (.inl (inR_nat hn.cW hq))))
  · exact .inr (.inr (.inr (.inr (inR_nat hn.oW hq))))

end

end NativeRustcVmX64.KeccakGkr.KeccakPhase
