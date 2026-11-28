/-
  LeanVM.Protocol.Relation.Doomed

  An accepted proof is doomed at the stack's root.
-/

module

public import LeanVM.Protocol.Relation.Whole
public import LeanVM.Protocol.Relation.Runs
public import LeanVM.Protocol.Relation.NoCommit
public import LeanVM.Protocol.Compile.Rom.Sound

/-!
# Doom on an accepted run

**`doomedRun_of_verify`**: on a proof the compiled verifier accepts, with any seeding, the prefix
of the extracted history up to the stack's root is a boundary at which the certificate's doom holds
(`leanVmSpec_D_commit`): the run announced its sizes, then committed a root of level 0's shape
(`OpeningIface.shape_commitStack`, its word well shaped). The random-oracle theorem charges the
run to the escape of that doom, unless the run is good.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Params LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **A doomed run**: some boundary prefix of the extracted history is doomed. -/
def DoomedRun {P : VerifierProgram Bool} {G : List Ev → Prop} (C : CertG P G) (σ : Seed)
    (π : Proof) (c : KeccakCalls.QueryCache) : Prop :=
  ∃ h₀, h₀ <+: extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) σ P π ∧
    Boundary h₀ ∧ C.D h₀

variable (O : OpeningIface) (LI : LinkIface) (KI : KeccakIface)

theorem leanVmVerifierProgram_eq (bytecode : List K) (input : PublicInput) :
    leanVmVerifierProgram bytecode (publicInputDigest input) =
      (readAnnouncedSizes bytecode).bind fun a ↦
        ((veBodyG a.1 a.2 input).bind fun _ ↦ VerifierProgram.ret ()).bind
          fun _ ↦ VerifierProgram.ret true := by
  simp only [leanVmVerifierProgram, verifyExecution_eq, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.pure_eq]


/-- **An accepted proof is doomed at the stack's root.** -/
theorem doomedRun_of_verify (bytecode : List K) (input : PublicInput)
    (hRF : RingFactsOf input bytecode) {σ : Seed} {c : KeccakCalls.QueryCache} {π : Proof}
    (hv : Rom.verify (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) σ
      (leanVmVerifierProgram bytecode (publicInputDigest input)) π = some true) :
    DoomedRun (leanVmCert O LI KI bytecode input hRF) σ π c := by
  set hist := extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) σ
    (leanVmVerifierProgram bytecode (publicInputDigest input)) π with hhist
  obtain ⟨hafter, hws⟩ := after_extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) hv
  rw [← hhist] at hafter hws
  rw [leanVmVerifierProgram_eq] at hafter
  obtain ⟨a, l₁, r, hsplit, hl₁, hbody⟩ := after_bind_ret hafter
  obtain ⟨u, m, m', hm, hve, -⟩ := after_bind_ret hbody
  obtain ⟨tr, n, n', hn, hvb, -⟩ := after_bind_ret hve
  rw [veBodyG_eq] at hvb
  obtain ⟨v, k, k', hk, hce, -⟩ := after_bind_ret hvb
  obtain ⟨level, rest, W', -, rfl⟩ := commitStack_after_ret hce
  set e := Ev.commit (levelShape a.1.stackLog level (2 ^ level.fold)).1
    (levelShape a.1.stackLog level (2 ^ level.fold)).2 W' with he
  have hce' : (commitStack a.1.stackLog a.2).after [e] = some (.ret ()) := by cases v; exact hce
  have hA : Announced bytecode a.1 a.2 := returns_of_after hl₁
  obtain ⟨⟨lm, rows, hb⟩, hadm⟩ := announced_built hA
  have hp : Placed a.1 := by
    obtain ⟨⟨p0, h0, -⟩, ⟨p1, h1, -⟩, ⟨qk, hqk, -⟩⟩ := global_placed hb
    exact ⟨qk, p0, p1, hqk, h0, h1⟩
  have hpre : l₁ ++ [e] <+: hist := by
    rw [hsplit, hm, hn, hk]
    exact ⟨k' ++ n' ++ m', by simp⟩
  have hcomm : commits (l₁ ++ [e]) = commits [e] := by
    rw [commits_append, NoCommit.commits_after (noCommit_readAnnouncedSizes bytecode) hl₁,
      List.nil_append]
  have hwell : ∀ ht w W, e = Ev.commit ht w W → WellShaped w W := by
    intro ht w W hw
    refine hws ht w W ?_
    rw [hsplit, hm, hn, hk, ← hw]
    simp
  have hshape : O.ShapeOK₀ a.1.stackLog a.2 (commits (l₁ ++ [e])) := by
    rw [hcomm]; exact O.shape_commitStack hadm hwell hce'
  have hD := leanVmSpec_D_commit O LI KI bytecode input hRF hl₁ hp hce' hshape
  refine ⟨l₁ ++ [e], hpre, by rw [he]; exact boundary_append_commit _ _ _ _, ?_⟩
  exact (leanVmCert_D O LI KI bytecode input hRF _).mpr hD

end

end LeanVM.Protocol.Relation
