import SphincsSecurity.Proof.Seeded.FreshTable

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

variable (J R : Type) [Fintype J]

noncomputable def finTableEquiv : (Fin (Fintype.card J) → R) ≃ (J → R) where
  toFun values j := values (Fintype.equivFin J j)
  invFun values i := values ((Fintype.equivFin J).symm i)
  left_inv values := by funext i; simp
  right_inv values := by funext j; simp

variable {J R} {D : Type} [DecidableEq D]

noncomputable def cacheTable (cache : QueryCache (D →ₒ R)) (inputs : J → D) (outputs : J → R) :
    QueryCache (D →ₒ R) :=
  cacheFin cache (fun i => inputs ((Fintype.equivFin J).symm i))
    ((finTableEquiv J R).symm outputs)

theorem cacheTable_apply (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (hinj : Function.Injective inputs) (outputs : J → R) (j : J) :
    cacheTable cache inputs outputs (inputs j) = some (outputs j) := by
  have h := cacheFin_apply cache (fun i => inputs ((Fintype.equivFin J).symm i))
    (hinj.comp (Fintype.equivFin J).symm.injective) ((finTableEquiv J R).symm outputs)
    (Fintype.equivFin J j)
  rw [(Fintype.equivFin J).symm_apply_apply] at h
  simpa only [cacheTable, finTableEquiv, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply] using h

theorem cacheTable_apply_of_not_mem (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (outputs : J → R) (input : D) (hinput : ∀ j, input ≠ inputs j) :
    cacheTable cache inputs outputs input = cache input :=
  cacheFin_apply_of_not_mem _ _ _ _ (fun _ => hinput _)

noncomputable def queryTable (inputs : J → D) : OracleComp (D →ₒ R) (J → R) :=
  finTableEquiv J R <$> Concrete.sequenceFin fun i =>
    (liftM ((D →ₒ R).query (inputs ((Fintype.equivFin J).symm i))) : OracleComp (D →ₒ R) R)

variable [SampleableType R] [Fintype R] [SampleableType (J → R)]

theorem evalDist_queryTable_fresh (inputs : J → D) (hinj : Function.Injective inputs)
    (cache : QueryCache (D →ₒ R)) (hfresh : ∀ j, cache (inputs j) = none) :
    𝒟[(simulateQ randomOracle (queryTable inputs)).run cache] =
      𝒟[(fun outputs => (outputs, cacheTable cache inputs outputs)) <$> ($ᵗ (J → R))] := by
  classical
  rw [queryTable, simulateQ_map, StateT.run_map,
    run_sequenceFin_fresh (fun i => inputs ((Fintype.equivFin J).symm i))
      (fun _ _ h => (Fintype.equivFin J).symm.injective (hinj h)) cache (fun _ => hfresh _)]
  simp only [bind_pure_comp, Functor.map_map]
  rw [evalDist_map, evalDist_sequenceFin_uniform]
  have htable := evalDist_map_bijective_uniform_cross
    (α := Fin (Fintype.card J) → R) (β := J → R) (finTableEquiv J R) (finTableEquiv J R).bijective
  rw [evalDist_map, ← htable]
  simp only [evalDist_map, Functor.map_map]
  congr 1
  funext outputs
  simp only [cacheTable, Equiv.symm_apply_apply]

end SphincsSecurity.Seeded
