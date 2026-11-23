module

public import NativeRustcVmX64.Transcript.Frame

/-!
# Decidable facts about a block's run (x86-64)

A block's `Exec` module states what its run did as decidable facts its proof reads back: the words
it wrote into a region (`Wrote`, read by `Wrote.find`), the registers it left alone (`Keeps`, read
by `Keeps.reg`).
-/

namespace NativeRustcVmX64.Bus

open NativeRustcX64 NativeRustcX64.Sym

@[expose] public section

/-- Words a block wrote into region `r`: at each offset its value. -/
def Wrote (r : Nat) (ws : List (Nat × Sym)) (S : SState) : Prop :=
  ∀ p ∈ ws, ∀ i < 8, findWrite r (p.1 + i) S.mem = some (p.2, i)

instance (r : Nat) (ws : List (Nat × Sym)) (S : SState) : Decidable (Wrote r ws S) := by
  unfold Wrote; infer_instance

/-- Registers a block left alone. -/
def Keeps (rs : List Reg64) (S : SState) : Prop := ∀ r ∈ rs, S.reg r = some (.reg r)

instance (rs : List Reg64) (S : SState) : Decidable (Keeps rs S) := by
  unfold Keeps; infer_instance

end

public section

theorem Wrote.find {r : Nat} {ws : List (Nat × Sym)} {S : SState} (h : Wrote r ws S) {o : Nat}
    {v : Sym} (hp : (o, v) ∈ ws) : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i) :=
  h _ hp

theorem Keeps.reg [Labels] {rs : List Reg64} {S : SState} (h : Keeps rs S) {env : Env}
    {m : MachineData} (hm : Match env S m) {r : Reg64} (hr : r ∈ rs) :
    m.regs.get64 r = env.regs r :=
  hm.regs r _ (h r hr)

theorem Keeps.reg' [Labels] {rs : List Reg64} {S : SState} (h : Keeps rs S) {d : MachineData}
    {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {m : MachineData} (hm : Match (Env.ofMachine d regions vars ret) S m) {r : Reg64}
    (hr : r ∈ rs) : NativeRustcX64.reg m r = NativeRustcX64.reg d r :=
  hm.regs r _ (h r hr)

end

end NativeRustcVmX64.Bus
