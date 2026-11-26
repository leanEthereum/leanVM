/-
  Rv64mc.Proof.Hash.DigestWords

  `Digest::words` keeps its contract (`Spec.Hash.DigestWords.spec`), over any program holding its template, from
  `memcpy`'s: a tail call copying the 32 bytes into the aligned slot, whose doublewords are then the bytes packed
  little-endian (`getMem_of_bytes`), `Model.fromLeBytes`'s.
-/

import Rv64mc.Spec.Hash.DigestWords
import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Core.ReprBytes
import Rv64mc.Model.Merkle
import Rv64mc.Gen.Tmpl.Verifier.Hash.Digest.Words
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Hash.DigestWords

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Hash.DigestWords Rv64mc.Spec.Runtime
open Rv64mc.Gen.Verifier.Hash.Digest.Words (Link tmpl)

/-- `u64::from_le_bytes` is riscv-zkvm's little-endian packing. -/
theorem fromLeBytes_eq_packBytes {l : List (BitVec 8)} (h : l.length = 8) : Model.fromLeBytes l = packBytes l := by
  have e : Model.toLeBytes (packBytes l) = l := by
    apply List.ext_getElem (by simp [Model.toLeBytes, h])
    intro k hk1 hk2
    have hk : k < 8 := by simpa [Model.toLeBytes] using hk1
    have := extractByte_packBytes l k hk hk2
    simp only [extractByte, BitVec.truncate_eq_setWidth] at this
    simp [Model.toLeBytes, ← this, Nat.mul_comm]
  conv_lhs => rw [← e]
  rw [Model.fromLeBytes_toLeBytes]

set_option rv_sym.heap true in
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : needM ≤ need) (hcp : MemcpySpec env p L.memcpy.idx needM) : spec env p i need := by
  intro d
  rv_auto hp with [hL] using [hcp]
  · have := hpre_6.2.1; simp only [hpre_6.1, Layouts.Digest.byteSize] at this; simpa using this
  have hl : d.length = 32 := hpre_6.1
  have hb : BytesAt m1 (regs .x10) d := ⟨by rw [hl]; simpa [Layouts.Digest.byteSize] using hpre_8, fun k hk => by
    rw [hret1_17 k (by simpa [hl] using hk), hpre_6.2.2 k hk]⟩
  refine ⟨by simpa [Model.digestWordsRust] using hpre_8, fun k hk => ?_⟩
  have hk4 : k < 4 := by simpa [Model.digestWordsRust] using hk
  rw [getMem_of_bytes hb hpre_9 (by omega)]
  simp only [Model.digestWordsRust, List.getElem_map, List.getElem_range]
  exact (fromLeBytes_eq_packBytes (by simp [hl]; omega)).symm

end Rv64mc.Proof.Hash.DigestWords
