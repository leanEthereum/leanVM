module

public import NativeRustcVmArm.Whir.BasisWEval.Exec
public import NativeRustcVmArm.Whir.Block
public import NativeRustcVmArm.Whir.MathFrame
public import NativeRustcVmArm.Spec.Whir
public import NativeRustcVmArm.Spec.Layout
public import NativeRustcVm.Whir.BasisEval
public import NativeRustcVm.Tables.Same

/-!
# `BasisW::eval`: its frame, its inputs

`m0` is the entry's state. The prologue (`b0`) saves X19 to X30 in the 144-byte frame and the
point's length X3 at `sp + 16` (`slots0`); `b6` saves the output's address (X0) at `sp + 8`
(`slots`). Nothing outside the stack changes before `b24` stores the result (`Fr0`, `Fr1`: no
outputs), so every input reads as at the entry (`keep`).

`In m0 ba b v`: the precondition with the basis's data `v` (`Vals`) named. `ws v x j`: the weights
the code has met after `j` column claims (the ring-switched claim's, then those with a
placement).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr
open LeanVM.Protocol.Verifier (qkeccak)

@[expose] public section

/-- The prologue's slots: the callee-saved registers and X30, the point's length at `sp + 16`. -/
def slots0 : List (Nat × XReg) :=
  [(16, .X3), (48, .X29), (56, .X30), (64, .X28), (72, .X27), (80, .X26), (88, .X25), (96, .X24),
    (104, .X23), (112, .X22), (120, .X21), (128, .X20), (136, .X19)]

/-- From `b6` on: also the output's address at `sp + 8`. -/
def slots : List (Nat × XReg) := (8, .X0) :: slots0

/-- The frame before `b6`. -/
abbrev Fr0 (m0 st : MachineData) : Prop :=
  Fr m0 144 basisWEvalStack slots0 [] (fun _ ↦ False) st

/-- The frame from `b6` on. -/
abbrev Fr1 (m0 st : MachineData) : Prop :=
  Fr m0 144 basisWEvalStack slots [] (fun _ ↦ False) st

/-- The data a basis refers to. -/
structure Vals where
  L : LayoutW
  target : EW
  coeffs : Array EW
  kp : Array EW
  slices : Array EW
  cs : Array ColumnClaimW
  z : Array EW
  value : EW

/-- **The precondition**, the basis's data `v` named. -/
structure In (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) : Prop where
  pre : BasisWEvalPre ba b m0
  log : v.L.stackLog ≤ 30
  layout : LayoutWAt m0.dmem ba.layout v.L
  ring : RingWAt m0.dmem ba.ring v.target v.coeffs
  keccak : KeccakOutAt m0.dmem ba.keccak v.kp v.slices
  claims : ClaimsWAt m0.dmem ba.claims v.cs
  ood : EqClaimAt m0.dmem ba.ood v.z v.value
  eq : b.claims = stackClaims v.L v.target v.kp v.coeffs v.cs v.z v.value

/-- The point. -/
def xpt (m0 : MachineData) : Array EW := slice m0 m0.regs.X2 m0.regs.X3

/-- The ring-switched claim's weight at `x`. -/
def ringW (v : Vals) (x : Array EW) : EW :=
  StackWeight.eval (.ring (v.L.placement qkeccak) v.kp v.coeffs) x

/-- The weights met after `j` column claims. -/
def ws (v : Vals) (x : Array EW) (j : Nat) : Array EW :=
  (ringW v x :: colWs v.L x v.cs j).toArray

end

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

theorem in_of_pre (h : BasisWEvalPre ba b m0) : ∃ v, In m0 ba b v := by
  obtain ⟨L, target, coeffs, kp, slices, cs, z, value, hlog, hL, hR, hK, hC, hO, heq⟩ :=
    h.2.1.data.holds
  exact ⟨⟨L, target, coeffs, kp, slices, cs, z, value⟩, h, hlog, hL, hR, hK, hC, hO, heq⟩

theorem stack_le : 144 + ewMulStack ≤ basisWEvalStack ∧
    144 + ringClaimWeightStack ≤ basisWEvalStack ∧ 144 + columnWeightStack ≤ basisWEvalStack ∧
    144 + eqEvalStack ≤ basisWEvalStack ∧ 144 + layoutWPlacementStack ≤ basisWEvalStack ∧
    144 ≤ basisWEvalStack := by
  unfold basisWEvalStack layoutWPlacementStack; omega

theorem In.stackOk (h : In m0 ba b v) : StackOk m0 basisWEvalStack := h.pre.1

theorem In.hN (h : In m0 ba b v) : basisWEvalStack ≤ m0.regs.SP.toNat := h.pre.1.2.1

/-! ## Inputs -/

/-- The `BasisW`. -/
theorem In.basis (h : In m0 ba b v) : WhirIn m0 m0.regs.X1.toBitVec basisBytes basisWEvalStack :=
  h.pre.2.2.1.1

theorem In.area (h : In m0 ba b v) {r : NativeRustcVm.Region} (hr : r ∈ ba.regions) :
    WhirIn m0 r.addr r.size basisWEvalStack :=
  (h.pre.2.2.1.2.2 r hr).1

theorem In.scales (h : In m0 ba b v) : WhirIn m0 ba.scales (16 * ba.count) basisWEvalStack :=
  h.area (r := ⟨ba.scales, 16 * ba.count⟩) (by simp [BasisAddrs.regions])

theorem In.layoutIn (h : In m0 ba b v) : WhirIn m0 ba.layout layoutBytes basisWEvalStack :=
  h.area (r := ⟨ba.layout, layoutBytes⟩) (by unfold BasisAddrs.regions; exact .tail _ (.head _))

theorem In.ringIn (h : In m0 ba b v) : WhirIn m0 ba.ring ringWBytes basisWEvalStack :=
  h.area (r := ⟨ba.ring, ringWBytes⟩) (by
    unfold BasisAddrs.regions; exact .tail _ (.tail _ (.head _)))

theorem In.keccakIn (h : In m0 ba b v) : WhirIn m0 ba.keccak outBytes basisWEvalStack :=
  h.area (r := ⟨ba.keccak, outBytes⟩) (by
    unfold BasisAddrs.regions; exact .tail _ (.tail _ (.tail _ (.head _))))

theorem In.claimsIn (h : In m0 ba b v) : WhirIn m0 ba.claims claimsBytes basisWEvalStack :=
  h.area (r := ⟨ba.claims, claimsBytes⟩) (by
    unfold BasisAddrs.regions; exact .tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

theorem In.oodIn (h : In m0 ba b v) : WhirIn m0 ba.ood eqClaimBytes basisWEvalStack :=
  h.area (r := ⟨ba.ood, eqClaimBytes⟩) (by
    unfold BasisAddrs.regions; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))

theorem In.point (h : In m0 ba b v) : SliceOk m0 m0.regs.X2 m0.regs.X3 basisWEvalStack :=
  h.pre.2.2.2.2.1

theorem In.out (h : In m0 ba b v) : WhirIn m0 m0.regs.X0.toBitVec 24 basisWEvalStack :=
  h.pre.2.2.2.2.2.1

/-- The areas the blocks read together are apart. -/
theorem In.aparts (h : In m0 ba b v) :
    Apart m0.regs.X1.toBitVec basisBytes ba.keccak outBytes ∧
      Apart m0.regs.X1.toBitVec basisBytes ba.claims claimsBytes ∧
      Apart m0.regs.X1.toBitVec basisBytes ba.ood eqClaimBytes ∧
      Apart ba.layout layoutBytes ba.claims claimsBytes := by
  have hp := h.pre.2.2.2.2.2.2
  simp only [BasisApart, BasisAddrs.regions, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hp
  exact ⟨hp.1.2.2.2.1, hp.1.2.2.2.2.1, hp.1.2.2.2.2.2, hp.2.2.1.2.2.1⟩

/-! ## Reading through the frame -/

section
variable {F : Nat} {sl : List (Nat × XReg)} {st : MachineData}

/-- **An input reads as at the entry** in a state of the frame. -/
theorem same_of (hN : basisWEvalStack ≤ m0.regs.SP.toNat)
    (hf : Fr m0 F basisWEvalStack sl [] (fun _ ↦ False) st) {a : BitVec 64} {n : Nat}
    (h : WhirIn m0 a n basisWEvalStack) : Same m0.dmem st.dmem a n :=
  Same.of_sameOutside hf.same fun _ hj hq ↦ hq.elim
    (fun hq ↦ NativeRustcVm.Apart.not_inRange_add h.2 h.1.2 (base_noWrap hN) hj hq) id

theorem In.layoutAt (h : In m0 ba b v) (hf : Fr m0 F basisWEvalStack sl [] (fun _ ↦ False) st) :
    LayoutWAt st.dmem ba.layout v.L :=
  NativeRustcVm.Tables.LayoutWAt.of_same h.layout (same_of h.hN hf h.layoutIn)

theorem In.claimsAt (h : In m0 ba b v) (hf : Fr m0 F basisWEvalStack sl [] (fun _ ↦ False) st) :
    ClaimsWAt st.dmem ba.claims v.cs :=
  NativeRustcVm.Tables.ClaimsWAt.of_same h.claims (same_of h.hN hf h.claimsIn)

theorem In.wordsAt (h : In m0 ba b v) (hf : Fr m0 F basisWEvalStack sl [] (fun _ ↦ False) st) :
    NativeRustcVm.WordsAt st.dmem m0.regs.X1.toBitVec [UInt64.ofBitVec ba.scales,
      ba.count.toUInt64, UInt64.ofBitVec ba.layout, UInt64.ofBitVec ba.ring,
      UInt64.ofBitVec ba.keccak, UInt64.ofBitVec ba.claims, UInt64.ofBitVec ba.ood] :=
  NativeRustcVm.Tables.WordsAt.of_same h.pre.2.1.words (same_of h.hN hf h.basis)
    (by simp [basisBytes])

/-- An input is mapped in a state of the frame. -/
theorem mapped_of (hf : Fr m0 F basisWEvalStack sl [] (fun _ ↦ False) st) {a : BitVec 64}
    {n : Nat} (h : WhirIn m0 a n basisWEvalStack) :
    NativeRustcVm.Mapped st.dmem a n ∧ NoWrap a n :=
  ⟨fun i hi ↦ hf.kept _ (h.1.1 i hi), h.1.2⟩

/-- The frame is mapped in a state of the frame. -/
theorem frame_of (h : In m0 ba b v) (hf : Fr m0 F basisWEvalStack sl [] (fun _ ↦ False) st) :
    NativeRustcVm.Mapped st.dmem (base m0 144) 144 ∧ NoWrap (base m0 144) 144 :=
  ⟨fun i hi ↦ hf.kept _ (frame_mapped h.stackOk stack_le.2.2.2.2.2 i hi),
    base_noWrap (by have := h.hN; have := stack_le; omega)⟩

/-- An input is apart from the frame. -/
theorem frame_apart (h : In m0 ba b v) {a : BitVec 64} {n : Nat}
    (ha : WhirIn m0 a n basisWEvalStack) : Apart a n (base m0 144) 144 := by
  have hN := h.hN
  have hs := stack_le
  have e1 := base_toNat (m0 := m0) (F := 144) (by omega)
  have e2 := base_toNat (m0 := m0) (F := basisWEvalStack) hN
  have := ha.2
  unfold OffStack Apart at this
  unfold Apart
  rw [show stackBelow m0 basisWEvalStack = base m0 basisWEvalStack from rfl, e2] at this
  rw [e1]
  omega

end

/-! ## Sub-areas -/

/-- An area inside an input. -/
theorem WhirIn.sub' {m : MachineData} {a : BitVec 64} {N o n S : Nat} (h : WhirIn m a N S)
    (hle : o + n ≤ N) : WhirIn m (NativeRustcVm.Transcript.off a o) n S :=
  WhirIn.sub h hle

theorem off_toNat {a : BitVec 64} {N o : Nat} (h : NoWrap a N) (hle : o < N) :
    (NativeRustcVm.Transcript.off a o).toNat = a.toNat + o :=
  NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at h; omega)

/-- Areas inside apart areas are apart. -/
theorem apart_sub {a b : BitVec 64} {n m o n' o' m' : Nat} (h : Apart a n b m) (ha : NoWrap a n)
    (hb : NoWrap b m) (h1 : o + n' ≤ n) (h2 : o' + m' ≤ m) :
    Apart (NativeRustcVm.Transcript.off a o) n' (NativeRustcVm.Transcript.off b o') m' := by
  unfold NoWrap at ha hb
  unfold Apart at h ⊢
  have e1 := NativeRustcVm.toNat_add_ofNat_le (a := a) (i := o) (by omega)
  have e2 := NativeRustcVm.toNat_add_ofNat_le (a := b) (i := o') (by omega)
  simp only [NativeRustcVm.Transcript.off]
  omega

end

end NativeRustcVmArm.Whir.BasisWEval
