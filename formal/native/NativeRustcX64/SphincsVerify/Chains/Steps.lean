module

public import NativeRustcX64.SphincsVerify.Chains.StepHead
public import NativeRustcX64.SphincsVerify.InlineTh.Model
public import NativeRustc.Sphincs.Digest

/-!
# A chain's steps on x86-64

A step leaves `th` of the step's address and the chain's value (`step`, by `th_short`); the
steps from position `pos` to 3 leave the chain's end, `chain` from `pos` (`steps`), at `b141`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Chains

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym NativeRustcX64.Sphincs.SphincsVerify
open NativeRustcX64.SphincsVerifyProof.InlineTh

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

variable [Host] {r : Run}

/-- **A step**: the chain's value becomes `th` of the step's address and the value. -/
theorem step (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i pos : Nat}
    (hpos : pos ≤ 2) {v : List UInt8} (hv : v.length = 16) {R : MachineState → Prop}
    {m : MachineData} (hK : Keep r l x E i m) (hR : Regs r m pos)
    (hcell : BytesAt m.dmem (r.off 1592) v)
    (cont : ∀ m', Keep r l x E i m' → Regs r m' (pos + 1) →
      BytesAt m'.dmem (r.off 1592) (th r.seed (chainAdrs r l i pos) v) →
      Eventually (step1 Host.exe) R ⟨m', if pos + 1 = 3 then r.pc NativeRustcX64.Sphincs.SphincsVerify.b141Offset else r.pc NativeRustcX64.Sphincs.SphincsVerify.b110Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b110Offset⟩ :=
  seg_b110 hp hc hpre hx hE hpos hv hK hR hcell fun m' h1 h2 h3 ↦ cont m' h1 h2 (by
    rw [th_short (by simp [length_seed, length_chainAdrs, hv])]
    exact h3)

/-- **The steps from position `pos`**: `k + 1` steps to position 3 leave `chain` from `pos`; then
`b141`. -/
theorem steps (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {l : Nat} {x E : List UInt8} (hx : x.length = 64) (hE : E.length ≤ 1024) {i : Nat}
    {R : MachineState → Prop} :
    ∀ (k pos : Nat) {v : List UInt8} {m : MachineData}, pos + (k + 1) = 3 → v.length = 16 →
      Keep r l x E i m → Regs r m pos → BytesAt m.dmem (r.off 1592) v →
      (∀ m', Keep r l x E i m' → Regs r m' 3 →
        BytesAt m'.dmem (r.off 1592) (chain r.seed (r.key l) i pos (k + 1) v) →
        Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Sphincs.SphincsVerify.b141Offset⟩) →
      Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b110Offset⟩
  | 0, pos, v, m, hk, hv, hK, hR, hcell, cont =>
    step hp hc hpre hx hE (by omega) hv hK hR hcell fun m' h1 h2 h3 ↦ by
      simp only [show pos + 1 = 3 by omega, ↓reduceIte] at h2 ⊢
      exact cont m' h1 h2 (by rw [chain_succ, chain_zero]; exact h3)
  | k + 1, pos, v, m, hk, hv, hK, hR, hcell, cont =>
    step hp hc hpre hx hE (by omega) hv hK hR hcell fun m' h1 h2 h3 ↦ by
      simp only [show pos + 1 ≠ 3 by omega, ↓reduceIte]
      exact steps hp hc hpre hx hE k (pos + 1) (by omega) (length_th _ _ _) h1 h2 h3
        fun m'' g1 g2 g3 ↦ cont m'' g1 g2 (by rw [chain_succ]; exact g3)

end

end NativeRustcX64.SphincsVerifyProof.Chains
