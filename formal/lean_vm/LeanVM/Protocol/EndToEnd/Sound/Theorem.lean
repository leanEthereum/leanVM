/-
  LeanVM.Protocol.EndToEnd.Sound.Theorem

  The end-to-end, random-oracle-model knowledge soundness of leanVM's deployed verifier, at
  `2^-128` per oracle query: the doom bound, the extractor, the knowledge statement, the
  execution it gives, and the numeric bound.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Assemble
public import LeanVM.Protocol.EndToEnd.Sound.Runs
public import LeanVM.Protocol.EndToEnd.Execution
public import LeanVM.Protocol.Verifier.Cost

/-!
# Knowledge soundness of the leanVM verifier in the random-oracle model

For one statement, `P = leanVmProgram (bytecodeWords prog) (publicDigest input)` the deployed
verifier program (leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`) and `σ = leanVmSeed …` its
Fiat-Shamir seed: the doom certificate's bound, the extractor, and the step from an accepted proof
without a witness to doom. The probability statements, for an adversary that chooses the
statement, are in `LeanVM.Protocol.EndToEnd.Sound.Statements`.

* `leanVmCert_bound`: every escape bound of `leanVmCert`, discounted by the proof of work before
  its group, is at most `2^-128`.
* `extractStack prog input c π`: **the extractor**. It reads the extracted history of `π` under
  the cache `c`, the announced sizes `(s, ρ)` (the value `readSizes` returned along it; a
  classical choice, unique by `announced_eq`) and the stack's committed word `W₀` (the first
  commitment), and returns a candidate of `W₀` at level 0's Johnson threshold satisfying
  `M3Holds (leanIsaInstance blake2sFlockSpec prog s) input`, if one exists (a classical choice;
  the extractor is a specification of what is extracted, not an algorithm).
* `doomed_of_not_extracted`: a proof accepted while the extractor finds no good candidate has a
  doomed boundary prefix: after the stack's root the certificate's doom is `CommitDoom`
  (`leanVmSpec_D_commit`), which is "no good candidate".

No statement takes a hypothesis beyond the adversary's query bound (and, for executions,
well-formed bytecode): the table sumcheck's fidelity is `tableFid_leanIsa`.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete (publicDigest)
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

variable (prog : Program) (input : PublicInput)

/-! ## The doom bound -/

/-- Doom never holds at the empty history: the announced sizes are not at stake. -/
theorem leanVmSpec_D_nil : ¬ (leanVmSpec prog input).D [] [] := by
  intro hD
  have hs : (verifyExecution .computed (bytecodeWords prog) (publicDigest input)).retSplit [] = none :=
    retSplit_eq_none_of_after rfl (verifyExecution_ne_ret _ _)
  have h1 : (veSpec prog input).D [] [] := (Spec.bindD_none hs).1 hD
  have hs' : (readSizes (bytecodeWords prog)).retSplit [] = none :=
    retSplit_eq_none_of_after rfl (readSizes_ne_ret _)
  exact (Spec.bindD_none hs').1 h1

/-- **The certificate's bound**: every escape bound of `leanVmCert`, discounted by the proof of
work before its group (`2^-min(b, 64)`), is at most `2^-128`. -/
theorem leanVmCert_bound (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (leanVmCert prog input).ε h ≤ εLean := by
  by_cases hr : (leanVmProgram (bytecodeWords prog) (publicDigest input)).Reachable h
  · rw [min_eq_left (grindBits_le_of_reachable _ _ hr)]
    exact Spec.toCert_bound _ (fun hD ↦ absurd hD (leanVmSpec_D_nil prog input)) h
  · simp only [leanVmCert, Spec.toCert_ε, hr, false_and, ↓reduceIte, mul_zero, zero_le]

/-! ## The doom after the stack's root -/

/-- The doom of `verify_execution` after the announced sizes, at good sizes, right after the
stack's root: the root's postcondition. -/
theorem realSpec_D {s : Sizes} {ρ : ℕ}
    (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) {l₁ : List Ev} {e : Ev}
    (hce : (commitStack (verifierLayout prog s).stackLog ρ).after [e] = some (.ret ()))
    (hpost : CommitPost prog input (verifierLayout prog s, ρ) () (l₁ ++ [e])) :
    (realSpec input hw hlb).D l₁ [e] := by
  refine (Spec.bindD_some (Prog.retSplit_self hce)).2 ⟨fun _ ↦ ?_, ?_⟩
  · obtain ⟨q₀, rest, hc, -⟩ := Whir.Complete.exists_ladder hw
    exact (commitSpec_D _ _ hc l₁ e).2 hpost
  · exact (restSpec input hw hlb).start_D _ hpost

/-- **After the stack's root, the certificate's doom is the root's postcondition**: along a
history where `readSizes` returned a good value `a` and the root was committed by `e`, the
doom holds if no candidate of the root satisfies the relation and the stack's is the only
commitment. -/
theorem leanVmSpec_D_commit {l₁ : List Ev} {a : Verifier.Layout × ℕ}
    (hl₁ : (readSizes (bytecodeWords prog)).after l₁ = some (.ret a)) {s : Sizes}
    (hg : Good prog a s) {e : Ev}
    (hce : (commitStack a.1.stackLog a.2).after [e] = some (.ret ()))
    (hpost : CommitPost prog input a () (l₁ ++ [e])) :
    (leanVmSpec prog input).D [] (l₁ ++ [e]) := by
  obtain ⟨lay, ρ⟩ := a
  have hve : (verifyExecution .computed (bytecodeWords prog) (publicDigest input)).after (l₁ ++ [e]) =
      some ((verifyBusBalance .computed lay).bind fun bus ↦ (tablePhase lay bus).bind fun cl ↦
        (Verifier.publicInputPhase lay (publicDigest input)).bind fun pc ↦
        (verifyFlock .computed (blake2sR1csLogSize + lay.tableLogHeights.getD opBlake2s 0)).bind fun x ↦
        (ringSwitch x.1 x.2).bind fun y ↦ verifyStackedOpening lay.stackLog ρ
          (ringSwitchClaim lay y.1 y.2 :: (cl ++ pc).map (·.onStack lay))) := by
    rw [verifyExecution_eq, Prog.after_bind_append _ hl₁]
    exact Prog.after_bind_append _ hce []
  have hs : (verifyExecution .computed (bytecodeWords prog) (publicDigest input)).retSplit (l₁ ++ [e]) =
      none := by
    refine retSplit_eq_none_of_after hve fun u h ↦ ?_
    obtain ⟨b, hb, -⟩ := bind_eq_ret_iff h
    exact verifyBusBalance_ne_ret _ _ hb
  refine (Spec.bindD_none hs).2 ?_
  refine (Spec.bindD_after (Prog.retSplit_of_after _ l₁ [e] hl₁) (List.cons_ne_nil _ _)).2 ?_
  have hex : ∃ s, Good prog (lay, ρ) s := ⟨s, hg⟩
  have hlay : lay = verifierLayout prog hex.choose := hex.choose_spec.1
  simp only [bodySpec, hex, ↓reduceDIte, Spec.congr_D]
  refine realSpec_D prog input _ _ (by rw [← hlay]; exact hce) ?_
  rw [← hlay]
  exact hpost

/-! ## The extractor -/

open Classical in
/-- The sizes and rate a history announced: the value `(verifierLayout prog s, ρ)` that
`readSizes` returned along a prefix of it (a classical choice; unique, `announced_eq`). -/
noncomputable def announced (hist : List Ev) : Option (Sizes × ℕ) :=
  if h : ∃ p : Sizes × ℕ, ∃ l₁, l₁ <+: hist ∧
      (readSizes (bytecodeWords prog)).after l₁ = some (.ret (verifierLayout prog p.1, p.2)) then
    some h.choose
  else none

/-- A program returns along at most one prefix of a history. -/
theorem ret_prefix_unique {α : Type} {p : Prog α} {l l' hist : List Ev} {a a' : α}
    (h1 : l <+: hist) (h2 : l' <+: hist) (ha : p.after l = some (.ret a))
    (ha' : p.after l' = some (.ret a')) : l = l' := by
  rcases le_total l.length l'.length with hlen | hlen
  · obtain ⟨t, rfl⟩ := List.prefix_of_prefix_length_le h1 h2 hlen
    have ht : t = [] := eq_of_after_ret ha (by rw [ha']; rfl)
    rw [ht, List.append_nil]
  · obtain ⟨t, rfl⟩ := List.prefix_of_prefix_length_le h2 h1 hlen
    have ht : t = [] := eq_of_after_ret ha' (by rw [ha]; rfl)
    rw [ht, List.append_nil]

/-- **The announced sizes are the sizes the run announced.** -/
theorem announced_eq {hist l₁ : List Ev} {a : Verifier.Layout × ℕ} {s : Sizes}
    (hpre : l₁ <+: hist) (hl₁ : (readSizes (bytecodeWords prog)).after l₁ = some (.ret a))
    (ha : a.1 = verifierLayout prog s) : announced prog hist = some (s, a.2) := by
  have hex : ∃ p : Sizes × ℕ, ∃ l₁, l₁ <+: hist ∧
      (readSizes (bytecodeWords prog)).after l₁ = some (.ret (verifierLayout prog p.1, p.2)) :=
    ⟨(s, a.2), l₁, hpre, by rw [hl₁, ← ha]⟩
  simp only [announced, hex, ↓reduceDIte, Option.some.injEq]
  obtain ⟨l', hl'pre, hl'⟩ := hex.choose_spec
  obtain rfl := ret_prefix_unique hl'pre hpre hl' hl₁
  rw [hl₁] at hl'
  simp only [Option.some.injEq, Prog.ret.injEq] at hl'
  have h1 : verifierLayout prog hex.choose.1 = verifierLayout prog s := by rw [← ha, hl']
  have h2 := verifierLayout_injective prog h1
  exact Prod.ext h2 (by rw [hl'])

open Classical in
/-- **The extractor.** From the cache `c` and the proof `π`: the extracted history of the
verifier's run, the sizes `s` and rate `ρ` it announced, and the stack's committed word `W₀`
(its first commitment); a candidate of `W₀` at level 0's Johnson threshold satisfying
`M3Holds (leanIsaInstance blake2sFlockSpec prog s) input`, if one exists. The candidate is a
classical choice: the extractor specifies what is extracted, with no claim of efficiency. -/
noncomputable def extractStack (c : HashSpec.QueryCache) (π : Proof) :
    Option (Σ s : Sizes, Column (leanIsaμ prog s)) :=
  let hist := extractedHistory (fun x ↦ c x) (leanVmSeed (bytecodeWords prog) (publicDigest input))
    (leanVmProgram (bytecodeWords prog) (publicDigest input)) π
  match announced prog hist, firstWord hist with
  | some (s, ρ), some W =>
    if hq : ∃ q ∈ Candidates (leanIsaμ prog s) ρ (thrOf (leanIsaμ prog s) ρ) W,
        M3Holds (leanIsaInstance F₀ prog s) input q then
      some ⟨s, hq.choose⟩
    else none
  | _, _ => none

/-- **The extractor succeeds**: it returns admissible sizes and a stack satisfying the leanISA
relation. -/
def Extracted (c : HashSpec.QueryCache) (π : Proof) : Prop :=
  ∃ (s : Sizes) (q : Column (leanIsaμ prog s)), extractStack prog input c π = some ⟨s, q⟩ ∧
    s.Admissible prog ∧
    M3Holds (leanIsaInstance F₀ prog s) input q

/-! ## Accepted without extraction is doomed -/

/-- The commitments of an announcement followed by one commitment. -/
theorem commits_reads_commit (xs : List E) (ht w : ℕ) (W : Word) :
    commits (xs.map Ev.read ++ [Ev.commit ht w W]) = [(ht, w, W)] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [commits] using ih

/-- **Accepted, and the extractor fails, is doomed**: the prefix of the extracted history up to
the stack's root is a boundary at which the certificate's doom holds. -/
theorem doomed_of_not_extracted {c : HashSpec.QueryCache} {π : Proof}
    (hv : Rom.verify (fun x ↦ c x) (leanVmSeed (bytecodeWords prog) (publicDigest input))
      (leanVmProgram (bytecodeWords prog) (publicDigest input)) π = some true)
    (hne : ¬ Extracted prog input c π) :
    DoomedRun (leanVmCert prog input) (leanVmSeed (bytecodeWords prog) (publicDigest input)) π
      c := by
  set hist := extractedHistory (fun x ↦ c x) (leanVmSeed (bytecodeWords prog) (publicDigest input))
    (leanVmProgram (bytecodeWords prog) (publicDigest input)) π with hhist
  obtain ⟨hafter, hws⟩ := after_extractedHistory (fun x ↦ c x) hv
  rw [← hhist] at hafter hws
  -- The run: the announced sizes, the root, the rest.
  obtain ⟨u, m, m', hm, hve, -⟩ := after_bind_ret hafter
  rw [verifyExecution_eq] at hve
  obtain ⟨a, l₁, r, rfl, hl₁, hbody⟩ := after_bind_ret hve
  obtain ⟨v, r₁, r₂, rfl, hce, -⟩ := after_bind_ret hbody
  obtain ⟨level, rest, W, hc, rfl⟩ := commitStack_after_ret hce
  set e := Ev.commit (levelShape a.1.stackLog level (2 ^ level.fold)).1
    (levelShape a.1.stackLog level (2 ^ level.fold)).2 W with he
  have hpre : l₁ ++ [e] <+: hist := by
    rw [hm]
    exact ⟨r₂ ++ m', by simp⟩
  obtain ⟨s, hg⟩ := good_of_readSizes prog hl₁
  obtain ⟨s', -, -, -, hreads⟩ := readSizes_ret_sizes prog hl₁
  -- The root's shape.
  have hcomm : commits (l₁ ++ [e]) = [((levelShape a.1.stackLog level (2 ^ level.fold)).1,
      (levelShape a.1.stackLog level (2 ^ level.fold)).2, W)] := by
    rw [hreads]; exact commits_reads_commit _ _ _ _
  obtain ⟨q₀, rest', hc', -⟩ := Whir.Complete.exists_ladder hg.2.2.1
  rw [hc] at hc'
  simp only [Option.some.injEq, List.cons.injEq] at hc'
  obtain ⟨rfl, rfl⟩ := hc'
  obtain ⟨-, -, hκ, hR, -⟩ := Whir.Params.deployed_spec_hyps hg.2.2.1 hc
  have hshape : StackShape a.1.stackLog a.2 (l₁ ++ [e]) := by
    have hmem : e ∈ hist := by rw [hm]; simp
    have hWs : WellShaped (2 ^ laneBits) W := by rw [he] at hmem; exact hws _ _ W hmem
    refine ⟨by rw [hcomm]; rfl, W, ?_, hWs⟩
    rw [hcomm]
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, levelShape, wdOf,
      ↓reduceIte, and_true]
    simp only [code₀, hκ, hR]
  -- The first word.
  have hfw : firstWord (l₁ ++ [e]) = some W := by
    simp [firstWord, hcomm]
  -- No good candidate.
  have hdoom : CommitDoom F₀ prog input thrOf a (l₁ ++ [e]) := by
    refine ⟨s, W, hg.1, hfw, fun q hq hM ↦ hne ?_⟩
    have hann : announced prog hist = some (s, a.2) :=
      announced_eq prog ((List.prefix_append l₁ [e]).trans hpre) hl₁ hg.1
    have hfw' : firstWord hist = some W := by
      rw [hm]
      have := firstWord_append hfw (r₂ ++ m')
      simpa [he] using this
    have hq' : ∃ q ∈ Candidates (leanIsaμ prog s) a.2 (thrOf (leanIsaμ prog s) a.2) W,
        M3Holds (leanIsaInstance F₀ prog s) input q := ⟨q, hq, hM⟩
    refine ⟨s, hq'.choose, ?_, hg.2.1, hq'.choose_spec.2⟩
    simp only [extractStack, ← hhist, hann, hfw', hq', ↓reduceDIte]
  exact ⟨l₁ ++ [e], hpre, by simp [Boundary, he], (leanVmSpec_D_commit prog input hl₁ hg
    (by cases v; exact hce) ⟨hdoom, hshape⟩)⟩

end
end LeanVM.Protocol.EndToEnd.Sound
