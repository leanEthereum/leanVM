module

public import NativeRustcArm.WotsLeaf.Chain.StepHead

/-!
# A chain's steps

A step leaves `th` of `P`, the step's address and the payload (`step`, by `th_short`); the steps
from position `pos` to 3 leave the chain's end, `chain` from `pos` (`steps`), at `b41`.
-/

namespace NativeRustcArm.WotsLeafProof.Chain

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf

public section

theorem chain_succ (pp : List UInt8) (layer : Nat) (e : UInt32) (i s k : Nat) (v : List UInt8) :
    chain pp layer e i s (k + 1) v = chain pp layer e i (s + 1) k
      (th pp ((tweak 1 (layerHi layer 0) e).withStep s) (v ++ u128Bytes i)) := by
  unfold chain
  rw [List.range'_succ, List.foldl_cons]

theorem chain_zero (pp : List UInt8) (layer : Nat) (e : UInt32) (i s : Nat) (v : List UInt8) :
    chain pp layer e i s 0 v = v := rfl

theorem length_chain (pp : List UInt8) (layer : Nat) (e : UInt32) (i : Nat) :
    ∀ (s k : Nat) {v : List UInt8}, v.length = 16 → (chain pp layer e i s k v).length = 16
  | _, 0, _, hv => hv
  | s, k + 1, v, _ => by
    rw [chain_succ]
    exact length_chain pp layer e i (s + 1) k (length_th _ _ _)

variable [NativeRustcArm.Host] {r : Run}

/-- **A step**: the chain's value becomes `th` of the step's address and the payload. -/
theorem step (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {pos i : Nat} (hpos : pos ≤ 2) {v : List UInt8} (hv : v.length = 16)
    {R : MachineState → Prop} {m : MachineData} (hK : r.CK x E m) (hR : r.SRegs m pos i)
    (hval : BytesAt m.dmem (r.off 1384) v)
    (cont : ∀ m', r.CK x E m' → r.SRegs m' (pos + 1) i →
      BytesAt m'.dmem (r.off 1384) (th r.pp ((tweak 1 r.hi r.e).withStep pos) (v ++ u128Bytes i)) →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcArm.Xmss.WotsLeaf.b41Offset else r.pc NativeRustcArm.Xmss.WotsLeaf.b15Offset⟩) :
    Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b15Offset⟩ :=
  seg_b15 hp hc hpre hpos hv hK hR hval fun m' h1 h2 h3 ↦ cont m' h1 h2 (by
    have hl : (r.pp ++ r.addr 1 pos ++ (v ++ u128Bytes i)).length < 136 := by
      simp only [List.length_append, length_pp, length_addr, hv, length_u128Bytes]
      decide
    rw [th_short hl]
    exact h3)

/-- **The steps from position `pos`**: `k + 1` steps to position 3 leave `chain` from `pos`; then
`b41`. -/
theorem steps (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    {x E : List UInt8} {i : Nat} {R : MachineState → Prop} :
    ∀ (k pos : Nat) {v : List UInt8} {m : MachineData}, pos + (k + 1) = 3 → v.length = 16 →
      r.CK x E m → r.SRegs m pos i → BytesAt m.dmem (r.off 1384) v →
      (∀ m', r.CK x E m' → r.SRegs m' 3 i →
        BytesAt m'.dmem (r.off 1384) (chain r.pp r.layer r.e i pos (k + 1) v) →
        Eventually (step1 NativeRustcArm.Host.exe) R ⟨m', r.pc NativeRustcArm.Xmss.WotsLeaf.b41Offset⟩) →
      Eventually (step1 NativeRustcArm.Host.exe) R ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b15Offset⟩
  | 0, pos, v, m, hk, hv, hK, hR, hval, cont =>
    step hp hc hpre (by omega) hv hK hR hval fun m' h1 h2 h3 ↦ by
      simp only [show pos + 1 = 3 by omega, ↓reduceIte] at h2 ⊢
      exact cont m' h1 h2 (by rw [chain_succ, chain_zero]; exact h3)
  | k + 1, pos, v, m, hk, hv, hK, hR, hval, cont =>
    step hp hc hpre (by omega) hv hK hR hval fun m' h1 h2 h3 ↦ by
      simp only [show pos + 1 ≠ 3 by omega, ↓reduceIte]
      exact steps hp hc hpre k (pos + 1) (by omega) (length_th _ _ _) h1 h2 h3
        fun m'' g1 g2 g3 ↦ cont m'' g1 g2 (by rw [chain_succ]; exact g3)

end

end NativeRustcArm.WotsLeafProof.Chain
