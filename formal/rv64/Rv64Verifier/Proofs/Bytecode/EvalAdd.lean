import Rv64Verifier.Proofs.Bytecode.EvalLoop

/-!
# `Bytecode::evaluate`: a word's sum into its eight buckets

`buckets[256 * byte + value] += sum` for each of the word's eight bytes: `0x80011150` computes
byte 0's bucket, and each of `0x80011158` .. `0x800112ec` adds the sum into one bucket and
computes the next one's, `0x8001132c` the last. `bucket_update` is one addition as the memory sees
it; `addToBuckets_unfold` the mirror's eight.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model

/-- One bucket of `addToBuckets`. -/
def addStep (word : BitVec 64) (sum : E) (k : Nat) (B : List E) : List E :=
  B.set (256 * k + ((toLeBytes word).getD k 0).toNat)
    (B.getD (256 * k + ((toLeBytes word).getD k 0).toNat) 0 + sum)

theorem addToBuckets_unfold (word : BitVec 64) (sum : E) (B : List E) :
    addToBuckets word sum B = addStep word sum 7 (addStep word sum 6 (addStep word sum 5
      (addStep word sum 4 (addStep word sum 3 (addStep word sum 2 (addStep word sum 1
        (addStep word sum 0 B))))))) := by
  rfl

/-- Adding into element `idx` of the buckets, as a block does it: each limb XORed with the sum's. -/
theorem bucket_update {e : Env} (he : EnvOk e) {u u' : MachineState} {idx : Word}
    (hidx : idx.toNat < 2048) {sum : E}
    (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum)
    (m2 : u'.getMem (e.bk + (idx * 16 + idx * 8)) = u.getMem (e.bk + (idx * 16 + idx * 8)) ^^^
      u.getReg .x16)
    (m1 : u'.getMem (e.bk + (idx * 16 + idx * 8) + 8) =
      u.getMem (e.bk + (idx * 16 + idx * 8) + 8) ^^^ u.getReg .x15)
    (m0 : u'.getMem (e.bk + (idx * 16 + idx * 8) + 16) =
      u.getMem (e.bk + (idx * 16 + idx * 8) + 16) ^^^ u.getReg .x14)
    (hfr : ∀ a, ¬ Within a (e.bk + (idx * 16 + idx * 8)) 24 → u'.getMem a = u.getMem a) :
    eListAt u' e.bk 2048 = (eListAt u e.bk 2048).set idx.toNat
      ((eListAt u e.bk 2048).getD idx.toNat 0 + sum) := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hb hh
  rw [mul24] at m0 m1 m2 hfr
  have hlen : idx.toNat < (eListAt u e.bk 2048).length := by rw [eListAt_length]; exact hidx
  refine eListAt_set hidx (by omega) ?_ hfr
  apply eAt_eq_of_limbs
  rw [List.getD_eq_getElem _ _ hlen, eListAt_getElem, limbs_add, limbs_eAt, ← hsum, m0, m1, m2]

end Rv64Verifier.Proofs.Bytecode.Eval
