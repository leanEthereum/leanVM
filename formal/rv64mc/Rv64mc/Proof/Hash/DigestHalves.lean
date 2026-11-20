/-
  Rv64mc.Proof.Hash.DigestHalves

  `Digest::halves` keeps its contract (`Spec.Hash.DigestHalves.spec`), over any program holding its template, from
  `Digest::words`'s: the words in an aligned slot of its own stack, then stored into `sret` in order.
-/

import Rv64mc.Spec.Hash.DigestHalves
import Rv64mc.Spec.Hash.DigestWords
import Rv64mc.Gen.Tmpl.Verifier.Hash.Digest.Halves
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Hash.DigestHalves

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Hash.DigestHalves
open Rv64mc.Gen.Verifier.Hash.Digest.Halves (Link tmpl)

/-- A slot of the stack below `top` is not the doubleword of a byte of a caller's object. -/
theorem slot_ne_align {env : Env} {m : MachineState} {top a s : Word} {n k : Nat} (hO : env.Owned m top a n)
    (hk : k < n) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat ≤ s.toNat)
    (hs : s.toNat < top.toNat) (hal : top.toNat % 8 = 0) : s ≠ alignToDword (a + BitVec.ofNat 64 k) := by
  intro he
  have e := congrArg BitVec.toNat he
  have := env.layout
  have h2 := hO.2
  rw [toNat_alignToDword, toNat_add_ofNat (by omega)] at e
  rcases hO.1 with h | h <;> omega

theorem slot_toNat {top : Word} {c : Nat} (hc : c ≤ top.toNat) (hc' : 0 < c) (hc2 : c < 2 ^ 64) :
    (top + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = top.toNat - c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := top.isLt; omega

set_option rv_sym.heap true in
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needW : Nat} (hnW : 48 + needW ≤ need) (hw : Spec.Hash.DigestWords.spec env p L.words.idx needW) :
    spec env p i need := by
  intro d
  rv_auto hp with [hL] using [hw d]
  · have hlim : env.stackLimit.toNat + 48 ≤ top.toNat := by omega
    have h8 := slot_toNat (top := top) (c := 8) (by omega) (by decide) (by decide)
    have h16 := slot_toNat (top := top) (c := 16) (by omega) (by decide) (by decide)
    simp only [show (2 : Nat) ^ 64 - 8 = 18446744073709551608 from rfl,
      show (2 : Nat) ^ 64 - 16 = 18446744073709551600 from rfl] at h8 h16
    refine ⟨hpre_6.1, hpre_6.2.1, fun k hk => ?_⟩
    have hk' : k < Layouts.Digest.byteSize := by rw [← hpre_6.1]; exact hk
    rw [getByte_setMem_ne (slot_ne_align ⟨hpre_7, hpre_8⟩ hk' hpre_5 (by rw [h16]; omega) (by rw [h16, hpre_2]; omega)
        (by rw [hpre_2]; omega)),
      getByte_setMem_ne (slot_ne_align ⟨hpre_7, hpre_8⟩ hk' hpre_5 (by rw [h8]; omega) (by rw [h8, hpre_2]; omega)
        (by rw [hpre_2]; omega)), hpre_6.2.2 k hk]
  all_goals
    have hl : (Model.digestWordsRust d).length = 4 := by simp [Model.digestWordsRust]
    have g : ∀ k (hk : k < 4), (Model.digestWordsRust d).getD k 0 =
        m1.getMem (top + 18446744073709551568#64 + BitVec.ofNat 64 (8 * k)) := fun k hk => by
      rw [List.getD_eq_getElem _ _ (by omega), hret1_16.2 k (by omega)]
    have g0 := g 0 (by decide); have g1 := g 1 (by decide); have g2 := g 2 (by decide); have g3 := g 3 (by decide)
    simp only [Nat.mul_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc,
      BitVec.reduceAdd] at g0 g1 g2 g3
    simp (config := { decide := true }) only [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize, Model.digestHalvesRust, g0, g1, g2, g3,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, MachineState.getMem_setMem_eq,
      MachineState.getMem_setMem_ne, ne_eq, BitVec.add_right_inj, Tactic.ne_add]

end Rv64mc.Proof.Hash.DigestHalves
