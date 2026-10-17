import Sphincs.BridgeInternalize
import Mathlib.Data.Set.Finite.List

/-! A computation whose hash queries are all short sees the lazy random oracle exactly as a
uniformly sampled table on the finite set of short inputs. Private draws stay private draws. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Eager

open Completeness Internalize Short

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

abbrev ShortIn := {input : HashInput // IsShort input}

instance : Finite ShortIn := (List.finite_length_le UInt8 bound).to_subtype

noncomputable instance : Fintype ShortIn := Fintype.ofFinite _

noncomputable instance : DecidableEq ShortIn := Classical.decEq _

abbrev Table := ShortIn → HashOutput

noncomputable instance : SampleableType Table := SampleableType.ofFintype Table

/-- Cached answers take priority; short inputs fall back to the sampled table. -/
noncomputable def extend (cache : QueryCache HashSpec) (table : Table) : HashInput → HashOutput :=
  fun input => (cache input).getD (if h : IsShort input then table ⟨input, h⟩ else 0)

/-- Private draws are forwarded; hash queries read a fixed answer function. -/
noncomputable def fixedRom (answers : HashInput → HashOutput) : QueryImpl OracleWorld ProbComp
  | .inl draw => liftM (unifSpec.query draw)
  | .inr input => pure (answers input)

theorem extend_cacheQuery (cache : QueryCache HashSpec) (table : Table) {input : HashInput}
    (h : IsShort input) (hnone : cache input = none) (answer : HashOutput) :
    extend (cache.cacheQuery input answer) table =
      extend cache (Function.update table ⟨input, h⟩ answer) := by
  funext query
  by_cases hq : query = input
  · subst query
    simp [extend, h, QueryCache.cacheQuery_self, hnone]
  · simp only [extend, QueryCache.cacheQuery_of_ne _ _ hq]
    split
    · rename_i hshort
      rw [Function.update_of_ne (fun heq => hq (congrArg Subtype.val heq))]
    · rfl

theorem evalDist_map_bind' {α β γ : Type} (x : ProbComp α) (f : α → β) (g : β → ProbComp γ) :
    𝒟[(f <$> x) >>= g] = 𝒟[x >>= fun a => g (f a)] := by
  rw [bind_map_left]

/-- Lazy sampling equals eager table sampling, from any cache. -/
theorem evalDist_romImpl_eq_table {α : Type} (oa : OracleComp OracleWorld α) (h : OnlyW oa)
    (cache : QueryCache HashSpec) :
    𝒟[(simulateQ romImpl oa).run' cache] =
      𝒟[do let table ← $ᵗ Table; simulateQ (fixedRom (extend cache table)) oa] := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      rw [DeferredSampling.evalDist_bind_const_neverFails _ (probFailure_uniformSample Table)]
  | query_bind input next ih =>
      rw [OnlyW, isQueryBoundP_query_bind_iff] at h
      have hnext : ∀ answer, OnlyW (next answer) := fun answer => by
        have := h.2 answer
        split at this <;> simpa [OnlyW] using this
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
      simp only [simulateQ_bind, simulateQ_spec_query]
      cases input with
      | inl draw =>
          refine (evalDist_map_bind' (liftM (unifSpec.query draw) : ProbComp _)
            (fun answer => (answer, cache)) _).trans ?_
          trans 𝒟[(liftM (unifSpec.query draw) : ProbComp _) >>= fun answer =>
            ($ᵗ Table) >>= fun table => simulateQ (fixedRom (extend cache table)) (next answer)]
          · refine evalDist_bind_congr' _ (fun answer => ?_)
            rw [← StateT.run'_eq]
            exact ih answer (hnext answer) cache
          · exact evalDist_bind_bind_swap _ _ _
      | inr bytes =>
          have hshort : IsShort bytes := by
            rcases h.1 with hnot | hzero
            · simpa [LongQuery] using hnot
            · omega
          change 𝒟[(randomOracle (spec := HashSpec) bytes).run cache >>= _] = _
          have hfixed : ∀ table : Table,
              (fixedRom (extend cache table) (.inr bytes) >>= fun answer =>
                simulateQ (fixedRom (extend cache table)) (next answer)) =
              simulateQ (fixedRom (extend cache table)) (next (extend cache table bytes)) := by
            intro table
            simp [fixedRom]
          simp_rw [hfixed]
          cases hc : cache bytes with
          | some answer =>
              rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
              have hext : ∀ table, extend cache table bytes = answer := fun table => by
                simp [extend, hc]
              simp_rw [hext]
              rw [← StateT.run'_eq]
              exact ih answer (hnext answer) cache
          | none =>
              rw [QueryImpl.withCaching_run_none _ hc]
              refine (evalDist_map_bind' (uniformSampleImpl (spec := HashSpec) bytes)
                (fun answer => (answer, cache.cacheQuery bytes answer)) _).trans ?_
              let ψ : Table → ProbComp α := fun table =>
                simulateQ (fixedRom (extend cache table)) (next (extend cache table bytes))
              have hupdate : ∀ (answer : HashOutput) (table : Table),
                  simulateQ (fixedRom (extend (cache.cacheQuery bytes answer) table)) (next answer) =
                    ψ (Function.update table ⟨bytes, hshort⟩ answer) := by
                intro answer table
                simp only [ψ, extend_cacheQuery cache table hshort hc answer]
                congr 2
                simp [extend, hc, hshort]
              trans 𝒟[(uniformSampleImpl (spec := HashSpec) bytes : ProbComp HashOutput) >>= fun answer =>
                ($ᵗ Table) >>= fun table => ψ (Function.update table ⟨bytes, hshort⟩ answer)]
              · refine evalDist_bind_congr' _ (fun answer => ?_)
                rw [← StateT.run'_eq, ih answer (hnext answer) (cache.cacheQuery bytes answer)]
                simp_rw [hupdate]
              · change 𝒟[($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
                  ($ᵗ Table) >>= fun table => ψ (Function.update table ⟨bytes, hshort⟩ answer)] =
                    𝒟[($ᵗ Table) >>= ψ]
                calc 𝒟[($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
                      ($ᵗ Table) >>= fun table => ψ (Function.update table ⟨bytes, hshort⟩ answer)]
                    = 𝒟[(($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer => ($ᵗ Table) >>=
                          fun table => pure (Function.update table ⟨bytes, hshort⟩ answer)) >>= ψ] := by
                      simp only [bind_assoc, pure_bind]
                  _ = 𝒟[($ᵗ Table) >>= ψ] := by
                      rw [evalDist_bind, evalDist_uniformSample_bind_update (D := ShortIn)
                        (R := HashOutput) ⟨bytes, hshort⟩, ← evalDist_bind]

end Sphincs.Security.Eager
