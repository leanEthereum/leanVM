module

public import NativeRustcVmX64.Whir.NextLevel.Glue
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmX64.Code.Vm.GlueLevel.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.NextLevel.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names
public import NativeRustcVmX64.Code.Vm.SampleQueries.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# `next_level` on x86-64

**`nextLevel_spec`**: AL becomes `nextLevelM`'s `Some`/`None`, the `TState` at RDI its next state,
the glued state at the stack argument `w` (its rounds kept), given its callees' contracts. The
prologue and `read_commitment` (`head1`), `read_scalars` (`head2`), `grind(t, 15)` (`head3`), the
out-of-domain sample, `read_scalar` and `grind(t, 17)` (`mid`), `sample_queries` and `squeeze`
(`qry`), the zeroing loop (`zero_loop`), `memcpy`, `powers` and `query_openings` (`ops`),
`each_row` (`rows`), `glue_level` and the epilogue (`glue`). Each `None` returns `0`.
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

public section

variable [Host] {k : Nat}

/-- **`next_level`'s contract.** -/
theorem nextLevel_spec (hp : Placed code k)
    (her : ∀ rows op, Spec (Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.entryLabel) (EachRowNextPre rows op)
      (EachRowNextPost rows))
    (hgl : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.GlueLevel.entryLabel) (GlueLevelPre s) (GlueLevelPost s))
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hpw : Spec (Labels.label NativeRustcVmX64.Vm.Powers.entryLabel) PowersPre PowersPost)
    (hsqz : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hqo : ∀ a s Q, Spec (Labels.label NativeRustcVmX64.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q)
      (QueryOpeningsPost a s Q))
    (hrc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s)
      (ReadCommitmentPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hsq : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SampleQueries.entryLabel) (SampleQueriesPre a s)
      (SampleQueriesPost a s)) :
    ∀ a s level w rounds, Spec (Labels.label NativeRustcVmX64.Vm.NextLevel.entryLabel) (NextLevelPre a s level w rounds)
      (NextLevelPost a s level w rounds) := by
  intro a s level w rounds m0 h
  have c := Ctx.of_pre h
  rw [show Labels.label NativeRustcVmX64.Vm.NextLevel.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b0Offset) from hp.label NativeRustcVmX64.Vm.NextLevel.entry_at]
  refine Eventually.bind (head1 hp c hrc) fun st1 h1 ↦ ?_
  rcases h1 with hg | ⟨hpc1, s1, hr1, hH1⟩
  · exact .done _ hg
  refine Eventually.bind (head2 hp c hrss hpc1 hH1 hr1) fun st2 h2 ↦ ?_
  rcases h2 with hg | ⟨hpc2, xs, s2, hr2, hH2⟩
  · exact .done _ hg
  refine Eventually.bind (head3 hp c hgr hpc2 hH2 hr2) fun st3 h3 ↦ ?_
  rcases h3 with hg | ⟨hpc3, s3, hr3, hH3⟩
  · exact .done _ hg
  refine Eventually.bind (mid hp c hsc hrs hgr hpc3 hH3 hr3) fun st4 h4 ↦ ?_
  rcases h4 with hg | ⟨hpc4, ood, v, s6, hr4, hH4⟩
  · exact .done _ hg
  refine Eventually.bind (qry hp c hsq hsqz hpc4 hH4 hr4) fun st5 h5 ↦ ?_
  rcases h5 with hg | ⟨hpc5, hrcx5, qs, lam, s8, hr5, hH5⟩
  · exact .done _ hg
  refine Eventually.bind (zero_loop hp c hpc5 hrcx5 hH5) fun st6 ⟨hpc6, hH6⟩ ↦ ?_
  refine Eventually.bind (ops hp c hmc hpw hqo hpc6 hH6 hr5) fun st7 h7 ↦ ?_
  rcases h7 with hg | ⟨hpc7, rws, op, s9, hr7, hH7⟩
  · exact .done _ hg
  refine Eventually.bind (rows hp c her hpc7 hH7) fun st8 h8 ↦ ?_
  rcases h8 with hg | ⟨hpc8, hH8⟩
  · exact .done _ hg
  exact glue hp c hgl hpc8 hH8 hr7

end

end NativeRustcVmX64.Whir.Levels.NL

/--
info: 'NativeRustcVmX64.Whir.Levels.NL.nextLevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.Levels.NL.nextLevel_spec
