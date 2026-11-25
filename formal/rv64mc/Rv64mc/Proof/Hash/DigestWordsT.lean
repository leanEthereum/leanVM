/-
  Rv64mc.Proof.Hash.DigestWordsT

  `Digest::words` is total: `DigestWords.Post`'s words (`Spec.Hash.DigestWords`), over any program holding its
  template, from `compiler_builtins`' `memcpy`'s total contract (`MemcpySpecT`, a tail call through the C wrapper's
  index). The partial proof (`DigestWords.lean`) ported by `rv_autoT`, the bytes copied read from `CopyPostT`. The
  precondition (`PreT`) adds what `CopyPreT` asks: the slot in a window, the digest's bytes in a window, apart from
  the stack below the stack pointer.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Hash.DigestWords
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Hash.DigestWordsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Hash.DigestWords Rv64mc.Spec.Runtime
open Rv64mc.Proof.Hash.DigestWords
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Gen.Verifier.Hash.Digest.Words (Link tmpl)

/-- The total precondition: `Pre`, the slot in a window, the digest in a window apart from the stack below the
    stack pointer. -/
def PreT (env : Env) (d : List (BitVec 8)) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env d regs m ∧ InWin env (regs .x10) Layouts.Digest.byteSize ∧
    inWindow (regs .x11) Layouts.Digest.byteSize = true ∧ OffStack env (regs .x2) (regs .x11) Layouts.Digest.byteSize

/-- **The total contract of `Digest::words`**: `DigestWords.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ d, HoldsT env p i need (PreT env d) (Post d) Out

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : needM ≤ need) (hcp : MemcpySpecT env p L.memcpy.idx needM) : specT env p i need := by
  intro d
  rv_autoT hp with [hL] using [hcp]
  all_goals simp only [show (32#64 : Word).toNat = 32 from rfl, Layouts.Digest.byteSize] at *
  · have := hpre_6.2.1; simp only [hpre_6.1, Layouts.Digest.byteSize] at this; simpa using this
  · have := env.layout
    rw [hpre_2] at hpre_7 hpre_13
    exact .inr ⟨hpre_11, by unfold OffStack; omega, hpre_12, hpre_13⟩
  have hl : d.length = 32 := hpre_6.1
  have hb : BytesAt m1 (regs .x10) d := ⟨by rw [hl]; omega, fun k hk => by
    rw [hret1_17 k (by simpa [hl] using hk), hpre_6.2.2 k hk]⟩
  refine ⟨by simpa [Model.digestWordsRust] using hpre_8, fun k hk => ?_⟩
  have hk4 : k < 4 := by simpa [Model.digestWordsRust] using hk
  rw [getMem_of_bytes hb hpre_9 (by omega)]
  simp only [Model.digestWordsRust, List.getElem_map, List.getElem_range]
  exact (fromLeBytes_eq_packBytes (by simp [hl]; omega)).symm

end Rv64mc.Proof.Hash.DigestWordsT

/-- info: 'Rv64mc.Proof.Hash.DigestWordsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Hash.DigestWordsT.total
