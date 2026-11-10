/-
  LeanVM.Guest.B1.VerifySub.H.Sig

  An honest child's values as `verify_sub`'s valuation computes them: the root's sponge from the
  seed, the stacked opening's target as the batched claims' values, the pooled claims' values.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.KFacts
public import LeanVM.Guest.B1.VerifySub.H.Claims

/-!
# The honest values, as the valuation computes them

`ChildSegs.sR_eq`: the sponge the out-of-domain grind starts from is the seed's with the eight
announced words and the root's two absorbed. `ChildSegs.target_eq`: the stacked opening's target
is the powers of `λ` against the ring switch's target, the kept claims' values, the Keccak
reduction's value and the out-of-domain value (`137` claims). `ChildSegs.pool_vals`,
`ChildSegs.col_vals`, `ChildSegs.pi_vals`: the claims' values are the bus's four words, the
tables' evaluations (the stream past the table sumcheck) and the public input's two.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

theorem kept_columns : (Tables.claimColumns.filter fun x ↦ decide (x ∉ keccakOutputColumns)).length =
    134 := by decide +kernel

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **The out-of-domain grind's sponge**: the seed's, the announced words and the root absorbed. -/
theorem sR_eq : S.sR = (((seedFs seed (Node.statementDigest seed c.statement)).absorbAll
    (sizeWords S.logMem S.rowsN S.rate) dsObserve).absorb S.x0 dsObserve).absorb S.x1 dsObserve := by
  show (S.s1.absorb S.x0 dsObserve).absorb S.x1 dsObserve = _
  rw [S.s1_eq]

theorem kept_length (hbl : bytecode.length = 2 ^ 23) :
    (S.claims.filter fun c ↦ decide (c.column ∉ keccakOutputColumns)).length = 134 := by
  obtain ⟨hok, -⟩ := S.H_run hbl
  have hcol : S.claims.map (·.column) = Tables.claimColumns :=
    Tables.VtHonest.vtH_columns hok S.hrowsL
  rw [← kept_columns, ← hcol, List.filter_map, List.length_map]
  rfl

/-- **The stacked opening's target**, as the batched claims' values. -/
theorem target_eq (hbl : bytecode.length = 2 ^ 23) : S.target = dot (powers S.lam 137)
    (S.rs.1 :: (S.claims.filter fun c ↦ decide (c.column ∉ keccakOutputColumns)).map (·.value) ++
      [S.kOut.value, S.oodV]) := by
  obtain ⟨hk1, -, -⟩ := S.keccak_run hbl
  have hl := S.kept_length hbl
  show batchTarget (stackClaims S.layout S.kc.1 S.rs.1 S.rs.2 S.ood) S.lam = _
  rw [hk1, S.ood_inv.2.2.1]
  simp only [batchTarget, stackClaims, ringSwitchClaim, ColumnClaim.stackClaim, List.map_cons,
    List.map_append, List.map_map, List.length_cons, List.length_append, List.length_map,
    List.map_nil, List.length_nil, hl, List.append_assoc, List.cons_append, List.nil_append,
    Function.comp_def]

theorem claims_vals (hbl : bytecode.length = 2 ^ 23) :
    S.claims.map (·.value) = S.H.xs4 ++ S.H.evsT.flatten ++ S.H.pcW :=
  Tables.VtHonest.vtH_values (S.H_run hbl).1

theorem evs_eq (hbl : bytecode.length = 2 ^ 23) :
    S.H.evsT.flatten = S.xsT.drop (14 + 3 * S.nT) ∧ S.H.evsT.flatten.length = 153 := by
  obtain ⟨hok, hcur, -, hlen⟩ := S.H_run hbl
  have h4 := hok.hx4
  have h10 := hok.hbcW
  have hR := hok.hxR
  have e : S.xsT.drop (14 + 3 * S.nT) = S.H.evsT.flatten := by
    rw [hcur, Tables.VtHonest.curW, List.append_assoc, List.append_assoc,
      show 14 + 3 * S.nT = S.H.xs4.length + (S.H.bcW.length + S.H.xsR.length) by
        rw [h4, h10, hR]; show 14 + 3 * S.nT = 4 + (10 + 3 * S.nT); omega,
      ← List.drop_drop, List.drop_left, ← List.drop_drop, List.drop_left, List.drop_left]
  refine ⟨e.symm, ?_⟩
  rw [← e, List.length_drop, hlen]
  omega

theorem pool_vals (hbl : bytecode.length = 2 ^ 23) :
    (S.claims.take 4).map (·.value) = S.H.xs4 := by
  rw [List.map_take, S.claims_vals hbl, List.append_assoc,
    List.take_left' (S.H_run hbl).1.hx4]

theorem col_vals (hbl : bytecode.length = 2 ^ 23) :
    ((S.claims.drop 4).take 153).map (·.value) = S.H.evsT.flatten := by
  rw [List.map_take, List.map_drop, S.claims_vals hbl, List.append_assoc,
    List.drop_left' (S.H_run hbl).1.hx4, List.take_left' (S.evs_eq hbl).2]

theorem pi_vals (hbl : bytecode.length = 2 ^ 23) :
    (S.claims.drop 157).map (·.value) = S.H.pcW := by
  rw [List.map_drop, S.claims_vals hbl,
    show 157 = (S.H.xs4 ++ S.H.evsT.flatten).length by
      rw [List.length_append, (S.H_run hbl).1.hx4, (S.evs_eq hbl).2],
    List.drop_left]

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
