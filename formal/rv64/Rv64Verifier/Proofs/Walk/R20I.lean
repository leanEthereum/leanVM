import Rv64Verifier.Proofs.Walk.R20H
import Rv64Verifier.Proofs.Walk.AtR21

/-!
# `walk` R20: from `AtR20` to `ring_switch`'s call

`AtR21m.toAtR21`: the inputs are never empty, so their buffers lie below `NEXT`. `r20`: from
`AtR20` to `AtR21`, the `Err` return or a dead end.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus Rv64Verifier.Model.Gkr

section R20
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word}

/-- A nonempty `Vec<E>` allocated from `t` on lies below `NEXT`. -/
theorem old_of_newVecE {s t u : MachineState} {a : Word} {xs : List E} (h : NewVecE t u a xs)
    (hst : heapNext s ≤ heapNext t) (hn : 0 < xs.length) :
    Old s u (vecPtr u a) (24 * (vecLen u a).toNat) := by
  obtain ⟨Ia, Il, If⟩ := newVecE_facts h
  rw [Il] at If ⊢
  rcases If with h0 | ⟨q1, q2⟩
  · omega
  · exact ⟨Ia, q2, Or.inr (by omega)⟩

theorem AtR21m.toAtR21 {M : Nat} {cl : List ColumnClaim} {o : KeccakOpenings} {ks ke : Nat}
    (A : AtR21m OI s u₀ w t u layout rows lir bus evs P C M cl o ks ke) (hM : M < 2 ^ 64)
    (olen : 4 ≤ o.inputs.1.length ∧ o.inputs.2.length = Verifier.kBits) :
    AtR21 OI s u₀ w t u layout rows lir bus evs P C (BitVec.ofNat 64 M) cl o.inputs.1 o.inputs.2
      ks ke := by
  have e : (BitVec.ofNat 64 M).toNat = M := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM]
  have hst : heapNext s ≤ heapNext t := by
    have := A.core.smono; have := A.core.umono; omega
  have hk : 0 < Verifier.kBits := by decide
  exact {
    toCoreT := by rw [e]; exact A.core
    pc := A.pc
    x18 := A.x18
    x22 := A.x22
    x23 := A.x23
    x24 := A.x24
    x25 := A.x25
    point := NewVecE.widen' A.in1 hst
    pointOld := old_of_newVecE A.in1 hst (by omega)
    slices := by rw [A.x12, A.x13]; exact old_of_newVecE A.in2 hst (by omega)
    slicesVal := by rw [A.x12, A.x13]; exact A.in2.elems }

set_option maxRecDepth 8192 in
/-- **R20**: `verify_keccak` and its outputs' claim, from `AtR20` to `ring_switch`'s call. -/
theorem r20 (hVK : VerifyKeccakSpecE) (hG : GrowOneFreshSpec 0x8000c0a4 56 8)
    (hDN : DropNopSpec) (hDL : DropLayoutSpec) {pub : List ColumnClaim} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus)
    (A : AtR20 OI s u₀ w t u layout rows lir bus evs P C L pub) :
    ∃ v, Reaches Image.code u v ∧ ((∃ P' C' L' cl pt sl ks ke,
      AtR21 OI s u₀ w t v layout rows lir bus evs P' C' L' cl pt sl ks ke) ∨
      Done OI s v ∨ Dead Image.code v) := by
  obtain ⟨c, hr₁, K | hd⟩ := r20pre hpre h A
  swap
  · exact ⟨c, hr₁, Or.inr (Or.inr hd)⟩
  obtain ⟨v, hr₂, Kr | hd⟩ := r20call hVK hpre K
  swap
  · exact ⟨v, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  obtain ⟨x, hr₃, ⟨o, ks, ke, O⟩ | hd | hd⟩ := r20ret hDN hDL hpre h Kr
  rotate_left
  · exact ⟨x, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inl hd)⟩
  · exact ⟨x, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr hd)⟩
  have hr := hr₁.trans (hr₂.trans hr₃)
  rcases ho : o.outputs with _ | ⟨p, wd⟩
  · obtain ⟨y, hr₄, Y⟩ := r20none hpre O ho
    exact ⟨y, hr.trans hr₄, Or.inl ⟨_, _, _, _, _, _, _, _, Y.toAtR21 L.isLt O.olen⟩⟩
  · obtain ⟨y, hr₄, ⟨P', C', S⟩ | hd⟩ := r20some hG hpre O ho
    swap
    · exact ⟨y, hr.trans hr₄, Or.inr (Or.inr hd)⟩
    obtain ⟨y', hr₅, Y⟩ := r20store hpre S
    have hC := S.core.n_lt
    have room := S.room
    exact ⟨y', hr.trans (hr₄.trans hr₅), Or.inl ⟨_, _, _, _, _, _, _, _,
      Y.toAtR21 (by omega) O.olen⟩⟩

end R20

end Rv64Verifier.Proofs.Walk
