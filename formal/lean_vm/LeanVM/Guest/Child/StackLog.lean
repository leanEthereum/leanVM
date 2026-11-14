/-
  LeanVM.Guest.Child.StackLog

  The honest proof announces the honest sizes: its stream starts with them, so the stack log a
  child's stream announces is the stack of the execution's committed size, at least `20` for the
  guest's `2^19` instructions.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.Child.Honest
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# The announced stack log of an honest proof

The honest script starts by sending `announce s ρ` (`honestRun`), and the verifier program starts
by reading eight scalars (`readAnnouncedSizes`), so the honest proof's stream starts with them
(`stream_prefix`). `readAnnouncedSizes` on them returns the verifier's layout at `s`
(`follows_readSizes`, run on a stream by `run_of_follows_sendList`), whose stack log is
`leanIsaμ prog s`, the ceiling of the stacked size's logarithm: at a child's witness the execution's
committed size (`announced_honest`, `muMin_le_announced`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol.KeccakHash
open Air.Flat (EnsembleWitness)

@[expose] public section

/-! ## The honest prover sends what its script sends first -/

/-- **The prover on a run of reads**: when the strategy sends `l` along the reads, the prover's
stream starts with `l`. -/
theorem proveFrom_readN {α : Type} (H : Bytes → Digest) (F : KeccakState → KeccakState) (S : Strategy)
    (fuel : ℕ) : ∀ (l : List E) (k : List E → VerifierProgram α) (sp : Sponge) (h : List Ev),
      (∀ i (hi : i < l.length), S.msg (h ++ (l.take i).map Ev.read) = l[i]) →
      ∃ sp', proveFrom H F S fuel ((VerifierProgram.readScalars l.length).bind k) sp h =
        (proveFrom H F S fuel (k l) sp' (h ++ l.map Ev.read)).map fun t ↦ (l ++ t.1, t.2)
  | [], k, sp, h, _ => ⟨sp, by simp [VerifierProgram.readScalars]⟩
  | x :: xs, k, sp, h, hS => by
    have h0 : S.msg h = x := by
      have := hS 0 (by simp)
      simpa only [List.take_zero, List.map_nil, List.append_nil, List.getElem_cons_zero] using this
    obtain ⟨sp', e⟩ := proveFrom_readN H F S fuel xs (fun ys ↦ k (x :: ys))
      (absorbI F sp x dsObserve) (h ++ [Ev.read x]) (fun i hi ↦ by
        have := hS (i + 1) (by simp; omega)
        simpa [List.take_succ_cons, List.append_assoc] using this)
    refine ⟨sp', ?_⟩
    have hb : (VerifierProgram.readScalars (x :: xs).length).bind k =
        VerifierProgram.read fun y ↦ (VerifierProgram.readScalars xs.length).bind fun ys ↦ k (y ::
            ys) := by
      simp only [List.length_cons, VerifierProgram.readScalars, VerifierProgram.readScalar,
          VerifierProgram.bind_eq, VerifierProgram.bind_assoc,
        VerifierProgram.pure_eq]
      rfl
    rw [hb, proveFrom, h0, e]
    simp only [Option.map_map, List.map_cons, List.cons_append, List.append_assoc]
    rfl

/-- The script sending `l` first sends `l[i]` after its first `i` sends. -/
theorem msgAt_sendList {α : Type} : ∀ (l : List E) (f : Unit → Script α) (i : ℕ)
    (hi : i < l.length), ((Script.sendList l).bind f).msgAt ((l.take i).map Ev.read) = l[i]
  | [], _, _, hi => by simp at hi
  | x :: xs, f, 0, _ => rfl
  | x :: xs, f, i + 1, hi => by
    have := msgAt_sendList xs f i (by simp at hi; omega)
    simpa [Script.msgAt, Script.walk, Script.step, Script.sendList, Script.bind] using this

/-- The verifier program reads eight scalars first. -/
theorem leanVmProgram_readN (bytecode : List K) (publicInput : Digest) :
    ∃ k, leanVmVerifierProgram bytecode publicInput = (VerifierProgram.readScalars 8).bind k :=
  ⟨_, by
    simp only [leanVmProgram_eq, verifyExecutionClaims, readAnnouncedSizes, VerifierProgram.bind_eq,
        VerifierProgram.bind_assoc]
    rfl⟩

theorem script_bind_assoc {α β γ : Type} (p : Script α) (f : α → Script β) (g : β → Script γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | send x k ih => simp only [Script.bind, ih]
  | sample k ih => simp only [Script.bind, ih]
  | grind k ih => simp only [Script.bind, ih]
  | commit w k ih => simp only [Script.bind, ih]
  | query k ih => simp only [Script.bind, ih]

/-- The honest script is the announcement, then the rest. -/
theorem honestProver_sendList (prog : LeanIsaProgram) (s : Sizes) (ρ : ℕ)
    (q : Column (leanIsaμ prog s)) (P : Phases) :
    ∃ f, honestProver prog s ρ q P = (Script.sendList (announce s ρ)).bind f :=
  ⟨_, by simp only [honestProver, honestRun, Script.bind_eq, script_bind_assoc]; rfl⟩

/-- **The honest proof's stream starts with the announcement.** -/
theorem stream_prefix (H : Bytes → Digest) (F : KeccakState → KeccakState) {prog : LeanIsaProgram} {s : Sizes}
    {ρ : ℕ} {q : Column (leanIsaμ prog s)} {input : PublicInput} {sd : KeccakState} {fuel : ℕ}
    {π : Proof}
    (h : prove H F (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      (leanVmProver prog s ρ q) sd fuel = some π) :
    ∃ rest, π.stream = announce s ρ ++ rest := by
  obtain ⟨k, hk⟩ := leanVmProgram_readN (bytecodeWords prog) (publicInputDigest input)
  have hl : (announce s ρ).length = 8 := by simp [announce]
  obtain ⟨f, hf⟩ := honestProver_sendList prog s ρ q (leanVmPhases prog s q)
  obtain ⟨sp', e⟩ := proveFrom_readN H F (leanVmProver prog s ρ q) fuel (announce s ρ) k
    ⟨sd, [], none⟩ [] (fun i hi ↦ by
      show (Strategy.ofScript _ 0).msg _ = _
      simp only [Strategy.ofScript, List.drop_zero, List.nil_append]
      rw [hf]
      exact msgAt_sendList _ f i hi)
  rw [hl] at e
  unfold prove at h
  rw [hk, e] at h
  simp only [Option.map_map] at h
  obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨t.1, rfl⟩

/-! ## The announcement read -/

/-- **A program met by sends runs on them**: if the script sending `l` follows `p`, then `p` run
on a stream starting with `l` returns a value the relation admits, the rest of the stream left. -/
theorem run_of_follows_sendList {β : Type} {R : Commits → Unit → β → Prop}
    (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState) :
    ∀ (l : List E) (p : VerifierProgram β) (cs : Commits), Follows R (Script.sendList l) p cs →
      ∀ (sp : Sponge), sp.ground = none → ∀ (rest : List E) (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)),
        ∃ b sp', Compile.runWithHash H F p ⟨sp, l ++ rest, os, roots⟩ = some (b, ⟨sp', rest, os, roots⟩) ∧
          R cs () b
  | [], p, cs, hf, sp, _, rest, os, roots => by
    cases p with
    | ret b => exact ⟨b, sp, rfl, hf⟩
    | _ => simp [Script.sendList, Follows] at hf
  | x :: xs, p, cs, hf, sp, hg, rest, os, roots => by
    cases p with
    | read k =>
      simp only [Script.sendList, Follows] at hf
      obtain ⟨b, sp', e, hR⟩ := run_of_follows_sendList H F xs (k x) cs hf
        (Id.run (Compile.absorb F sp x dsObserve)) ((absorbI_ground F sp x dsObserve).trans hg) rest
        os roots
      refine ⟨b, sp', ?_, hR⟩
      simp only [Compile.runWithHash, List.cons_append, hg]
      exact e
    | _ => simp [Script.sendList, Follows] at hf

/-- **The honest announcement is read as the verifier's layout.** -/
theorem announced_honest {prog : LeanIsaProgram} {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ}
    (hρ : validRate ρ) (rest : List E) :
    announcedLayoutAndRate (bytecodeWords prog) (announce s ρ ++ rest) = some (verifierLayout prog
        s, ρ) := by
  obtain ⟨b, sp', e, -, hb⟩ := run_of_follows_sendList (fun _ ↦ default)
    (fun _ ↦ default) (announce s ρ) _ [] (follows_readSizes prog hs hρ []) ⟨default, [], none⟩ rfl
    rest [] []
  unfold announcedLayoutAndRate
  rw [Compile.runPure_eq_withHash, e, hb]
  rfl

/-- **A child's honest proof announces a stack log of at least `20`**, for a program of at least
`2^19` instructions: its bytecode column alone commits `2^logSize` words, and the Keccak table
some more. -/
theorem muMin_le_announced {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {ρ : ℕ}
    {w : EnsembleWitness (leanIsaEnsemble prog t.logMemorySize)} {s : Sizes} (hc : ChildFor prog input t ρ w s)
    (hls : 19 ≤ prog.logSize) (rest : List E) :
    ∀ layout r, announcedLayoutAndRate (bytecodeWords prog) (announce s ρ ++ rest) = some
        (layout, r) →
      Coverage.minChildStackLog ≤ layout.stackLog := by
  intro layout r h
  obtain ⟨⟨hρ, -, -, hadm, -⟩, -⟩ := hc
  rw [announced_honest hadm hρ rest] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rw [stackLog_verifierLayout]
  refine le_trans ?_ (le_max_left _ _)
  have hb : 2 ^ 19 ≤ 2 ^ prog.logSize := Nat.pow_le_pow_right (by norm_num) hls
  have hk : 0 < 2 ^ s.τ 5 := Nat.two_pow_pos _
  have htot : 2 ^ 19 < (LeanIsa.blocks prog s).total := by
    rw [blocks_total_eq]
    have h4 : 2 ^ 19 < 2 ^ prog.logSize + 28 * 2 ^ s.τ 5 := by omega
    generalize 2 ^ s.logMem = a
    generalize 2 ^ (s.τ 5 + 6) = d
    omega
  exact (Nat.lt_clog_iff_pow_lt (by norm_num)).2 htot

end
end LeanVM.Guest.Child
