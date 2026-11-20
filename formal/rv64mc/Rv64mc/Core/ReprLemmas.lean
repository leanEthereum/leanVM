/-
  Rv64mc.Core.ReprLemmas

  Reading values through what a proof knows of memory, in the forms `rv_sym` computes addresses in:

  * an `E` slice in the heap through a frame without `out` (`EListAt.load`): element `j`'s limbs at `p + 16 j` and
    `p + 16 j + 8`;
  * a constant table of the static data (`DataRef.Words`): the words at a template's data reference, in every memory
    where `env.Static` holds, so a proof that reads a table takes its content as a hypothesis, as it takes a callee's
    contract, and depends on the content alone. The link step proves it from `env.data` (`DataRef.Words.of_data`).
-/

import Rv64mc.Core.Repr
import Rv64mc.Link.Basic
import Rv64mc.Tactic.Frame

namespace Rv64mc

open RiscvZkvm.Rv64

theorem EListAt.load {env : Env} {top : Word} {m M : MachineState} {p : Word} {es : List (Word × Word)} {j : Nat}
    (hf : env.Frame top Tactic.F m M) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (h : EListAt m p es)
    (hl : env.Live m p (Layouts.E.byteSize * es.length)) (hj : j < es.length) :
    M.getMem (p + BitVec.ofNat 64 (16 * j)) = es[j].1 ∧ M.getMem (p + BitVec.ofNat 64 (16 * j) + 8#64) = es[j].2 := by
  have h' := (h.keep (Env.Frame.keeps_live hf hnx hl fun _ _ h => h)).2 j hj
  simpa [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize] using h'

/-- **The data reference `d` holds the words `ws`** wherever the static data hold: word `k` at `d.hi + d.lo + 8 k`,
    the address the template's code computes. -/
def DataRef.Words (env : Env) (d : DataRef) (ws : List Word) : Prop :=
  ∀ m, env.Static m → ∀ k (h : k < ws.length), m.getMem (d.hi + d.lo + BitVec.ofNat 64 (8 * k)) = ws[k]

/-- The link step's proof of `DataRef.Words`: each word is one of `env.data`'s. -/
theorem DataRef.Words.of_data {env : Env} {d : DataRef} {ws : List Word}
    (h : ∀ k (hk : k < ws.length), (d.hi + d.lo + BitVec.ofNat 64 (8 * k), ws[k]) ∈ env.data) :
    DataRef.Words env d ws :=
  fun m hs k hk => env.static_data m hs _ (h k hk)

/-- Word `k` of a table, at the address `rv_sym` computes. -/
theorem DataRef.Words.get {env : Env} {d : DataRef} {ws : List Word} {m : MachineState} (hw : DataRef.Words env d ws)
    (hs : env.Static m) (k : Nat) (hk : k < ws.length) :
    m.getMem (d.hi + d.lo + BitVec.ofNat 64 (8 * k)) = ws[k] := hw m hs k hk

/-- Word `0` of a table, at the address `rv_sym` computes. -/
theorem DataRef.Words.get0 {env : Env} {d : DataRef} {ws : List Word} {m : MachineState} (hw : DataRef.Words env d ws)
    (hs : env.Static m) (hk : 0 < ws.length) : m.getMem (d.hi + d.lo) = ws[0] := by
  simpa using hw m hs 0 hk

end Rv64mc
