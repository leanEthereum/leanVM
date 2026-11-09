module

public import XmssSecurity.Proof.IdealStatement
public import XmssSecurity.Proof.HashInputLemmas

@[expose] public section

namespace XmssSecurity

private theorem fin_of_ofNat32_eq {n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ 32)
    (h : BitVec.ofNat 32 a.val = BitVec.ofNat 32 b.val) : a = b := by
  apply Fin.ext
  have ha := a.isLt.trans_le hn
  have hb := b.isLt.trans_le hn
  have heq := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using heq

end XmssSecurity
