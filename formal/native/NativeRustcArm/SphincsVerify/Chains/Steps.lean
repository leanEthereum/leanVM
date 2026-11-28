module

public import NativeRustcArm.SphincsVerify.Chains.StepHead
public import NativeRustcArm.SphincsVerify.InlineTh.Model
public import NativeRustc.Sphincs.Digest

/-!
# A chain's steps

A step leaves `th` of the step's address and the chain's value (`step`, by `th_short`); the
steps from position `pos` to 3 leave the chain's end, `chain` from `pos` (`steps`), at `b142`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify
open NativeRustcArm.SphincsVerifyProof.InlineTh

public section

theorem length_th (seed adrs v : List UInt8) : (th seed adrs v).length = 16 := by
  rw [th, List.length_take, length_hashBytes]
  rfl

theorem length_chain (seed : List UInt8) (key : OtsKey) (i : Nat) :
    ∀ (s k : Nat) {v : List UInt8}, v.length = 16 → (chain seed key i s k v).length = 16
  | _, 0, _, hv => hv
  | s, k + 1, _, _ => length_chain seed key i (s + 1) k (length_th _ _ _)

/-- A chain's first step. -/
theorem chain_succ (r : Run) (l i s k : Nat) (v : List UInt8) :
    chain r.seed (r.key l) i s (k + 1) v =
      chain r.seed (r.key l) i (s + 1) k (th r.seed (chainAdrs r l i s) v) := by
  unfold chain
  rw [List.range'_succ, List.foldl_cons]
  rfl

theorem chain_zero (r : Run) (l i s : Nat) (v : List UInt8) :
    chain r.seed (r.key l) i s 0 v = v := rfl

variable [NativeRustcArm.Host] {r : Run}

/-- **A step**: the chain's value becomes `th` of the step's address and the value. -/
theorem step (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {pos i : Nat}
    (hpos : pos ≤ 2) (hi : i < 64) {v : List UInt8} (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : Keep r l x E m) (hR : Regs m pos i)
    (h22 : Run.RegIs m .X22 (r.off 21648)) (hcell : BytesAt m.dmem (r.off 15984) v)
    (cont : ∀ m', Keep r l x E m' → Regs m' (pos + 1) i → Run.RegIs m' .X22 (r.off 21648) →
      BytesAt m'.dmem (r.off 15984) (th r.seed (chainAdrs r l i pos) v) →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcArm.Sphincs.SphincsVerify.b142Offset else r.pc NativeRustcArm.Sphincs.SphincsVerify.b116Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b116Offset⟩ :=
  seg_b116 hp hc hpre hx hE hpos hi hv hK hR h22 hcell fun m' h1 h2 h3 h4 ↦ cont m' h1 h2 h3 (by
    rw [th_short (by simp [length_seed, length_chainAdrs, hv])]
    exact h4)

/-- **The steps from position `pos`**: `k + 1` steps to position 3 leave `chain` from `pos`; then
`b142`. -/
theorem steps (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i : Nat}
    (hi : i < 64) {R : MachineState → Prop} :
    ∀ (k pos : Nat) {v : List UInt8} {m : MachineData}, pos + (k + 1) = 3 → v.length = 16 →
      Keep r l x E m → Regs m pos i → Run.RegIs m .X22 (r.off 21648) →
      BytesAt m.dmem (r.off 15984) v →
      (∀ m', Keep r l x E m' → Regs m' 3 i →
        BytesAt m'.dmem (r.off 15984) (chain r.seed (r.key l) i pos (k + 1) v) →
        Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', r.pc NativeRustcArm.Sphincs.SphincsVerify.b142Offset⟩) →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b116Offset⟩
  | 0, pos, v, m, hk, hv, hK, hR, h22, hcell, cont =>
    step hp hc hpre hx hE (by omega) hi hv hK hR h22 hcell fun m' h1 h2 _ h4 ↦ by
      simp only [show pos + 1 = 3 by omega, ↓reduceIte] at h2 ⊢
      exact cont m' h1 h2 (by rw [chain_succ, chain_zero]; exact h4)
  | k + 1, pos, v, m, hk, hv, hK, hR, h22, hcell, cont =>
    step hp hc hpre hx hE (by omega) hi hv hK hR h22 hcell fun m' h1 h2 h3 h4 ↦ by
      simp only [show pos + 1 ≠ 3 by omega, ↓reduceIte]
      exact steps hp hc hpre hx hE hi k (pos + 1) (by omega) (length_th _ _ _) h1 h2 h3 h4
        fun m'' g1 g2 g3 ↦ cont m'' g1 g2 (by rw [chain_succ]; exact g3)

end

end NativeRustcArm.SphincsVerifyProof.Chains
