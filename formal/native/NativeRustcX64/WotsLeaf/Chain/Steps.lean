module

public import NativeRustcX64.WotsLeaf.Chain.StepA
public import NativeRustc.Keccak.Buffer

/-!
# A chain's steps

A step leaves `th` of the step's tweak and the payload, the chain's value and `i` (`step`, by
`hashBytes_short`); the steps from position `p` to 3 leave the chain's end, `chain` from `p`
(`steps`), at `b48` (directive 515).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Chain

public section

theorem length_th (pp : List UInt8) (tw : Tweak) (x : List UInt8) : (th pp tw x).length = 16 := by
  rw [th, List.length_take, length_hashBytes]
  rfl

theorem length_chain (r : Run) (i : Nat) :
    ∀ (s k : Nat) {v : List UInt8}, v.length = 16 → (chain r.pp r.layer r.e i s k v).length = 16
  | _, 0, _, hv => hv
  | s, k + 1, v, _ => by
    unfold chain
    rw [List.range'_succ, List.foldl_cons]
    exact length_chain r i (s + 1) k (length_th _ _ _)

/-- A chain's first step. -/
theorem chain_succ (r : Run) (i s k : Nat) (v : List UInt8) :
    chain r.pp r.layer r.e i s (k + 1) v =
      chain r.pp r.layer r.e i (s + 1) k (th r.pp (r.tw s) (v ++ u128Bytes i)) := by
  unfold chain
  rw [List.range'_succ, List.foldl_cons]
  rfl

theorem length_tw (r : Run) (p : Nat) : (address (r.tw p)).length = 16 := length_addr r 1 p

/-- **A step's value is `th`**: the hash input is shorter than a block. -/
theorem stepOut_eq (r : Run) (i p : Nat) {cur : List UInt8} (hcur : cur.length = 16) :
    stepOut (r.pp ++ r.addr 1 p ++ (cur ++ u128Bytes i)) = th r.pp (r.tw p) (cur ++ u128Bytes i) := by
  rw [stepOut, th, Keccak.hashBytes_short (by
    simp only [List.length_append, length_pp, length_tw, hcur, length_u128Bytes]; omega),
    List.take_take, show min 16 32 = 16 from rfl]
  rfl

variable [Host] {r : Run}

/-- **A step**: the chain's value becomes `th` of the step's tweak and the payload. -/
theorem step (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {cur : List UInt8} (hcur : cur.length = 16) {R : MachineState → Prop}
    {m : MachineData} (hA : r.AtStep i p cur m)
    (cont : ∀ m', r.AtStep i (p + 1) (th r.pp (r.tw p) (cur ++ u128Bytes i)) m' →
      Eventually (step1 Host.exe) R ⟨m', if p + 1 = 3 then r.pc NativeRustcX64.Xmss.WotsLeaf.b48Offset else r.pc NativeRustcX64.Xmss.WotsLeaf.b17Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b17Offset⟩ :=
  seg_b17 hp hc hpre hp3 hcur hA fun m' h ↦ cont m' (by rw [← stepOut_eq r i p hcur]; exact h)

/-- **The steps from position `p`**: `k + 1` steps to position 3 leave `chain` from `p`; then
`b48`. -/
theorem steps (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i : Nat}
    {R : MachineState → Prop} :
    ∀ (k p : Nat) {v : List UInt8} {m : MachineData}, p + (k + 1) = 3 → v.length = 16 →
      r.AtStep i p v m →
      (∀ m', r.AtStep i 3 (chain r.pp r.layer r.e i p (k + 1) v) m' →
        Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Xmss.WotsLeaf.b48Offset⟩) →
      Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b17Offset⟩
  | 0, p, v, m, hk, hv, hA, cont =>
    step hp hc hpre (by omega) hv hA fun m' h ↦ by
      have h3 : p + 1 = 3 := by omega
      rw [ite_pos h3]
      rw [h3] at h
      exact cont m' (by rw [chain_succ]; exact h)
  | k + 1, p, v, m, hk, hv, hA, cont =>
    step hp hc hpre (by omega) hv hA fun m' h ↦ by
      rw [ite_neg (show ¬(p + 1 = 3) by omega)]
      exact steps hp hc hpre k (p + 1) (by omega) (length_th _ _ _) h
        fun m'' g ↦ cont m'' (by rw [chain_succ]; exact g)

end

end NativeRustcX64.WotsLeafProof
