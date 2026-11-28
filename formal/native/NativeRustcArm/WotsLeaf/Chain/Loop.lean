module

public import NativeRustcArm.WotsLeaf.Chain.Head

/-!
# Region 3: the 58 chains

From `AtChain x 0 []` at `b14` (directive 184), chain after chain (`chains_loop`, by induction on
the chains left), the machine reaches `b44` (directive 603) with the 58 chains' ends
(`Run.ends x 58`) at 440: **`chains_region`**.
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym Chain

@[expose] public section

/-- The ends of chains `0 .. i - 1` for the codeword `x`. -/
def Run.ends (r : Run) (x : List UInt8) (i : Nat) : List UInt8 :=
  ((List.range i).map (r.chainEnd x)).flatten

end

public section

theorem ends_succ (r : Run) (x : List UInt8) (i : Nat) :
    r.ends x (i + 1) = r.ends x i ++ r.chainEnd x i := by
  simp [Run.ends, List.range_succ]

variable [NativeRustcArm.Host]

/-- **The chains from chain `i`**: the ends of chains `i .. 57` after those before. -/
theorem chains_loop (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre)
    (x : List UInt8) : ∀ (n i : Nat) {m : MachineData}, i + n = 58 → 0 < n →
      r.AtChain x i (r.ends x i) m →
      Eventually (step1 NativeRustcArm.Host.exe)
        (fun st ↦ st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b44Offset ∧ r.AtChain x 58 (r.ends x 58) st.data) ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b14Offset⟩
  | 0, _, _, hn, h0, _ => absurd h0 (by decide)
  | n + 1, i, m, hn, _, hA => seg_b14 hp hc hpre (by omega) hA fun m' hA' ↦ by
    rw [← ends_succ] at hA'
    by_cases h : i + 1 = 58
    · simp only [h, ite_true]
      rw [h] at hA'
      exact .done _ ⟨rfl, hA'⟩
    · simp only [h, ite_false]
      exact chains_loop r hp hc hpre x n (i + 1) (by omega) (by omega) hA'

/-- **Region 3, the chains**: from `AtChain x 0 []` at `b14` to `AtChain x 58 (ends x 58)` at
`b44`. -/
theorem chains_region (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees)
    (hpre : r.Pre) (x : List UInt8) (m : MachineData) (hA : r.AtChain x 0 [] m) :
    Eventually (step1 NativeRustcArm.Host.exe)
      (fun st ↦ st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b44Offset ∧ r.AtChain x 58 (r.ends x 58) st.data) ⟨m, r.pc NativeRustcArm.Xmss.WotsLeaf.b14Offset⟩ :=
  chains_loop r hp hc hpre x 58 0 rfl (by decide) hA

end

end NativeRustcArm.WotsLeafProof
