/-
  LeanVM.Protocol.EndToEnd.Sound.Theorem

  The end-to-end, random-oracle-model knowledge soundness of leanVM's verifier, at
  `2^-125` per oracle query: the certificate of a statement and its bound, the extractor, and the
  step from an accepted proof without a witness to doom.
-/

module

import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.EndToEnd.Sound.Front
import LeanVM.Protocol.EndToEnd.Sound.Runs
public import LeanVM.Protocol.EndToEnd.Front.LayoutSizes
import LeanVM.Protocol.Whir.Complete.Opening
import LeanVM.Protocol.EndToEnd.Execution
public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.WithHash

/-!
# Knowledge soundness of the leanVM verifier in the random-oracle model

For one statement, `P = leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)` the
verifier program and `σ = leanVmSeed …` its Fiat-Shamir seed: the doom certificate and its bound,
the extractor, and the step from an accepted proof without a witness to doom. The probability
statements, for an adversary that chooses the statement, are in
`LeanVM.Protocol.EndToEnd.Sound.Statements`. Everything is stated against the stacked opening's
interface `O : OpeningIface` (`Sound.Assemble`); the front phases' is built (`frontIface`).

* `stmtCert_bound`: every escape bound of `stmtCert O prog input` (`Assemble.leanVmCert` with the
  front phases of `frontIface`), discounted by the proof of work before its group, is at most
  `2^-125`.
* `extractStack O prog input c π`: **the extractor**. It reads the extracted history of `π` under
  the cache `c`, the announced sizes `(s, ρ)` (the value `readAnnouncedSizes` returned along it; a
  classical choice, unique by `announced_eq`) and the stack's committed word `W₀` (the first
  commitment), and returns a candidate of `W₀` at level 0's threshold `O.thr₀` satisfying
  `M3Holds (leanIsaInstance prog s) input`, if one exists (a classical choice; the extractor is a
  specification of what is extracted, not an algorithm).
* `doomed_of_not_extracted`: a proof accepted while the extractor finds no good candidate has a
  doomed boundary prefix: right after the stack's root the certificate's doom is `RootDoom`
  (`leanVmSpec_D_commit`), "level 0's shape and no good candidate"; the shape is the opening's
  (`OpeningIface.shape_commitStack`), on the run's well-shaped commitment.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

variable (O : OpeningIface) (prog : LeanIsaProgram) (input : PublicInput)

/-! ## The certificate of a statement -/

/-- **A statement's good runs**: `GoodRun` of its verifier program. -/
abbrev stmtG : List Ev → Prop :=
  GoodRun O (prog := prog) (input := input) (bytecodeWords prog) (publicInputDigest input)

/-- **The doom certificate of a statement's verifier program**: `leanVmCert` with the front
phases built, accepting from doom only good runs. -/
noncomputable abbrev stmtCert :
    CertG (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      (stmtG O prog input) :=
  leanVmCert O (frontIface prog input) (bytecodeWords prog)

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
group, is at most `2^-125`. -/
theorem stmtCert_bound (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (stmtCert O prog input).ε h ≤ εmsg :=
  leanVmCert_bound O (frontIface prog input) (bytecodeWords prog) h

/-- Some boundary prefix of the extracted history of the seeded verifier's run of `P` on `π`,
under the answers of the cache `c` to both oracles, is doomed. -/
def DoomedRun {P : VerifierProgram Bool} {G : List Ev → Prop} (C : CertG P G) (σ : Seed) (π : Proof)
    (c : KeccakCalls.QueryCache) : Prop :=
  ∃ h₀, h₀ <+: extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) σ P π ∧
    Boundary h₀ ∧ C.D h₀

/-! ## The announced sizes -/

/-- What the announced value is on a run: the verifier's layout at admissible sizes, and an
admissible WHIR shape. -/
def Good (a : Verifier.Layout × ℕ) (s : Sizes) : Prop :=
  a.1 = verifierLayout prog s ∧ s.Admissible prog ∧ Whir.Admissible a.1.stackLog a.2

variable {prog} in
/-- **The announced value of a run is good**, after reads only. -/
theorem good_of_readSizes {l : List Ev} {a : Verifier.Layout × ℕ}
    (h : (readAnnouncedSizes (bytecodeWords prog)).after l = some (.ret a)) :
    ∃ s, Good prog a s ∧ l = (announce s a.2).map Ev.read := by
  obtain ⟨s, hs, -, hl, hreads⟩ := readSizes_ret_sizes prog h
  obtain ⟨xs, -, -, -, hρ1, hρ2, -, -, hμ1, hμ2⟩ := readSizes_ret h
  exact ⟨s, ⟨hl, hs, ⟨hμ1, hμ2, hρ1, hρ2⟩⟩, hreads⟩

/-- The commitments of reads. -/
theorem commits_map_read (xs : List E) : commits (xs.map Ev.read) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [commits] using ih

/-! ## The doom after the stack's root -/

/-- The commitment's OOD sample starts with its grind: it does not return without an event. -/
theorem readOod_bind_ne_ret {β : Type} (μ : ℕ) (f : StackClaim → VerifierProgram β) (b : β) :
    (readOod μ).bind f ≠ .ret b := by
  intro h
  obtain ⟨c, hc, -⟩ := bind_eq_ret_iff h
  simp [readOod, VerifierProgram.grindProofOfWork, Whir.oodGrindingBits, VerifierProgram.bind] at hc

/-- The doom of `verify_execution` after the announced sizes, right after the stack's root: the
root's postcondition. -/
theorem realSpec_D {s : Sizes} {ρ : ℕ} (hs : s.Admissible prog)
    (hadm : Whir.Admissible (μs prog s) ρ) {h₀ : List Ev} {e : Ev}
    (hce : (commitStack (μs prog s) ρ).after [e] = some (.ret ()))
    (hpost : RootDoom O prog s ρ (commits (h₀ ++ [e]))) :
    (realSpec O (frontIface prog input) moves_computedBytecodeValue hs hadm).D h₀ [e] := by
  refine (Spec.bindD_some (VerifierProgram.retSplit_self hce)).2
    ⟨fun _ ↦ ?_, Spec.start_D _ _ hpost⟩
  obtain ⟨q₀, rest, hc, -⟩ := Whir.Complete.exists_ladder hadm
  exact (commitSpec_D _ _ hc h₀ e).2 hpost

/-- **After the stack's root, the certificate's doom is the root's**: along a history where
`readAnnouncedSizes` returned the layout of admissible sizes `s` and the root was committed by `e`,
the doom holds if the commitments have level 0's shape. -/
theorem leanVmSpec_D_commit {l₁ : List Ev} {s : Sizes} {ρ : ℕ}
    (hl₁ : (readAnnouncedSizes (bytecodeWords prog)).after l₁ =
      some (.ret (verifierLayout prog s, ρ)))
    (hg : Good prog (verifierLayout prog s, ρ) s) {e : Ev}
    (hce : (commitStack (μs prog s) ρ).after [e] = some (.ret ()))
    (hpost : RootDoom O prog s ρ (commits (l₁ ++ [e]))) :
    (leanVmSpec O (frontIface prog input) (bytecodeWords prog)).D [] (l₁ ++ [e]) := by
  -- After the root, the ghost body is at its OOD sample, which does not return at once.
  set pd := publicInputDigest input
  have hbody : ∀ {γ : Type} (g : Whir.Sound.WhirTrace → VerifierProgram γ),
      ∃ q, ((veBodyG computedBytecodeValue pd (verifierLayout prog s) ρ).bind g).after [e] =
        some q ∧ ∀ c, q ≠ .ret c := by
    intro γ g
    simp only [veBodyG, VerifierProgram.bind_eq, VerifierProgram.bind_assoc]
    rw [show [e] = [e] ++ [] from rfl, VerifierProgram.after_bind_append _ hce]
    exact ⟨_, rfl, fun c hc ↦ readOod_bind_ne_ret _ _ c hc⟩
  have hveG : ∀ {γ : Type} (g : (Verifier.Layout × ℕ) × Whir.Sound.WhirTrace → VerifierProgram γ),
      ∃ q, ((verifyExecutionClaimsG computedBytecodeValue (bytecodeWords prog) pd).bind g).after
        (l₁ ++ [e]) = some q ∧ ∀ c, q ≠ .ret c := by
    intro γ g
    obtain ⟨q, hq, hne⟩ := hbody (γ := γ) fun tr ↦ g ((verifierLayout prog s, ρ), tr)
    refine ⟨q, ?_, hne⟩
    simp only [verifyExecutionClaimsG, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
    rw [VerifierProgram.after_bind_append _ hl₁]
    exact hq
  obtain ⟨q₀, hq₀, hne₀⟩ := hveG (γ := Bool × (Verifier.Layout × ℕ) × Whir.Sound.WhirTrace)
    fun d ↦ VerifierProgram.ret (true, d)
  have hs₀ := retSplit_eq_none_of_after hq₀ hne₀
  obtain ⟨q₁, hq₁, hne₁⟩ := hveG (γ := (Verifier.Layout × ℕ) × Whir.Sound.WhirTrace)
    VerifierProgram.ret
  rw [VerifierProgram.bind_ret] at hq₁
  have hs₁ := retSplit_eq_none_of_after hq₁ hne₁
  obtain ⟨q₂, hq₂, hne₂⟩ := hbody (γ := Whir.Sound.WhirTrace) VerifierProgram.ret
  rw [VerifierProgram.bind_ret] at hq₂
  have hs₂ := retSplit_eq_none_of_after hq₂ hne₂
  rw [leanVmSpec]
  erw [Spec.congr_D]
  refine (Spec.bindD_none hs₀).2 ⟨?_, rfl⟩
  refine (Spec.bindD_none hs₁).2 ?_
  rw [veSpec]
  refine (Spec.bindD_after (VerifierProgram.retSplit_of_after _ l₁ [e] hl₁)
    (List.cons_ne_nil _ _)).2 ?_
  apply (Spec.bindD_none hs₂).2
  have hex : AdmAt prog (verifierLayout prog s, ρ) := ⟨s, rfl, hg.2.1, hg.2.2⟩
  have hs' : hex.choose = s := verifierLayout_injective prog hex.choose_spec.1.symm
  rw [bodySpec_D O (frontIface prog input) moves_computedBytecodeValue _ hex]
  refine realSpec_D O prog input _ _ ?_ ?_
  · rw [hs']; exact hce
  · rw [hs', List.nil_append]; exact hpost

/-! ## The extractor -/

open Classical in
/-- The sizes and rate a history announced: the value `(verifierLayout prog s, ρ)` that
`readAnnouncedSizes` returned along a prefix of it (a classical choice; unique, `announced_eq`). -/
noncomputable def announced (hist : List Ev) : Option (Sizes × ℕ) :=
  if h : ∃ p : Sizes × ℕ, ∃ l₁, l₁ <+: hist ∧
      (readAnnouncedSizes (bytecodeWords prog)).after l₁ = some (.ret (verifierLayout prog p.1,
          p.2)) then
    some h.choose
  else none

/-- A program returns along at most one prefix of a history. -/
theorem ret_prefix_unique {α : Type} {p : VerifierProgram α} {l l' hist : List Ev} {a a' : α}
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
    (hpre : l₁ <+: hist) (hl₁ : (readAnnouncedSizes (bytecodeWords prog)).after l₁ = some (.ret a))
    (ha : a.1 = verifierLayout prog s) : announced prog hist = some (s, a.2) := by
  have hex : ∃ p : Sizes × ℕ, ∃ l₁, l₁ <+: hist ∧
      (readAnnouncedSizes (bytecodeWords prog)).after l₁ = some (.ret (verifierLayout prog p.1,
          p.2)) :=
    ⟨(s, a.2), l₁, hpre, by rw [hl₁, ← ha]⟩
  simp only [announced, hex, ↓reduceDIte, Option.some.injEq]
  obtain ⟨l', hl'pre, hl'⟩ := hex.choose_spec
  obtain rfl := ret_prefix_unique hl'pre hpre hl' hl₁
  rw [hl₁] at hl'
  simp only [Option.some.injEq, VerifierProgram.ret.injEq] at hl'
  have h1 : verifierLayout prog hex.choose.1 = verifierLayout prog s := by rw [← ha, hl']
  have h2 := verifierLayout_injective prog h1
  exact Prod.ext h2 (by rw [hl'])

open Classical in
/-- **The extractor.** From the cache `c` and the proof `π`: the extracted history of the
verifier's run, the sizes `s` and rate `ρ` it announced, and the stack's committed word `W₀`
(its first commitment); a candidate of `W₀` at level 0's threshold satisfying
`M3Holds (leanIsaInstance prog s) input`, if one exists. The candidate is a classical choice:
the extractor specifies what is extracted, with no claim of efficiency. -/
noncomputable def extractStack (c : KeccakCalls.QueryCache) (π : Proof) :
    Option (Σ s : Sizes, Column (leanIsaμ prog s)) :=
  let hist := extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
    (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
    (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π
  match announced prog hist, firstWord hist with
  | some (s, ρ), some W =>
    if hq : ∃ q ∈ Candidates (leanIsaμ prog s) ρ (O.thr₀ (leanIsaμ prog s) ρ) W,
        M3Holds (leanIsaInstance prog s) input q then
      some ⟨s, hq.choose⟩
    else none
  | _, _ => none

/-- **The extractor succeeds**: it returns admissible sizes and a stack satisfying the leanISA
relation. -/
def Extracted (c : KeccakCalls.QueryCache) (π : Proof) : Prop :=
  ∃ (s : Sizes) (q : Column (leanIsaμ prog s)), extractStack O prog input c π = some ⟨s, q⟩ ∧
    s.Admissible prog ∧ M3Holds (leanIsaInstance prog s) input q

/-! ## Accepted without extraction is doomed -/

/-- A stack read on equal variables is a candidate exactly when it is one. -/
theorem mem_candidates_castColumn {a b : ℕ} (e : a = b) (R : ℕ) (A : ℕ → ℕ → ℕ) (W : Word)
    (q : Column a) : castColumn e q ∈ Candidates b R (A b R) W ↔ q ∈ Candidates a R (A a R) W := by
  subst e
  simp [castColumn]

/-- **A good run's announced sizes and good candidate**: on a history along which the verifier
accepts and which is a good run, the sizes announced are admissible and some candidate of the
stack's word at level 0's threshold satisfies the relation. -/
theorem goodRun_cand {hist : List Ev}
    (hafter : (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)).after hist =
      some (.ret true))
    (hG : stmtG O prog input hist) :
    ∃ s ρ W, s.Admissible prog ∧ announced prog hist = some (s, ρ) ∧ firstWord hist = some W ∧
      ∃ q ∈ Candidates (leanIsaμ prog s) ρ (O.thr₀ (leanIsaμ prog s) ρ) W,
        M3Holds (leanIsaInstance prog s) input q := by
  rw [← leanVmProgramG_eq] at hafter
  obtain ⟨r, m, m', rfl, hg, hret⟩ := after_bind_ret hafter
  obtain ⟨rfl, hr1⟩ := after_ret_eq hret
  rw [List.append_nil] at hG ⊢
  -- The ghost's data: the announced value and the trace.
  have hg' := hg
  unfold leanVmProgramG at hg'
  obtain ⟨d, m₁, m₂, rfl, hd, hretd⟩ := after_bind_ret hg'
  obtain ⟨rfl, hrd⟩ := after_ret_eq hretd
  rw [verifyExecutionClaimsG] at hd
  obtain ⟨a, l₁, l₂, rfl, hl₁, hbody⟩ := after_bind_ret hd
  obtain ⟨tr, l₃, l₄, rfl, -, hrt⟩ := after_bind_ret hbody
  obtain ⟨rfl, hdt⟩ := after_ret_eq hrt
  have hrt' : r = (true, (a, tr)) := by rw [← hrd, ← hdt]
  obtain ⟨hadm, hT⟩ := hG (a, tr) (by rw [← hrt']; exact hg)
  obtain ⟨hlay, hs, hwadm⟩ := hadm.choose_spec
  have hwadm' : Whir.Admissible (μs prog hadm.choose) a.2 := by rw [μs, ← hlay]; exact hwadm
  obtain ⟨W, hW, q, hq, hnb⟩ := O.traceGood_cands hwadm' _ tr _ hT
  refine ⟨hadm.choose, a.2, W, hs,
    announced_eq prog (by rw [List.append_assoc]; exact List.prefix_append _ _) hl₁ hlay, hW,
    toI prog hadm.choose q, ?_, not_not.mp hnb⟩
  exact (mem_candidates_castColumn (stackLog_verifierLayout prog hadm.choose) a.2 O.thr₀ W q).2 hq

/-- **A good run is extracted**: on an accepted proof whose extracted history is a good run, the
announced sizes are admissible and a candidate of the stack's word satisfies the relation. -/
theorem extracted_of_goodRun {c : KeccakCalls.QueryCache} {π : Proof}
    (hv : Rom.verify (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π = some true)
    (hG : stmtG O prog input (extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π)) :
    Extracted O prog input c π := by
  obtain ⟨hafter, -⟩ := after_extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) hv
  obtain ⟨s, ρ, W, hs, hann, hfw, hq'⟩ := goodRun_cand O prog input hafter hG
  refine ⟨s, hq'.choose, ?_, hs, hq'.choose_spec.2⟩
  simp only [extractStack, hann, hfw, hq', ↓reduceDIte]

/-- **An accepted proof is doomed at the stack's root**: the prefix of the extracted history up to
the stack's root is a boundary at which the certificate's doom holds. -/
theorem doomedRun_of_verify {c : KeccakCalls.QueryCache} {π : Proof}
    (hv : Rom.verify (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π = some true) :
    DoomedRun (stmtCert O prog input) (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      π c := by
  set hist := extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
    (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
    (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π with hhist
  obtain ⟨hafter, hws⟩ := after_extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s)) hv
  rw [← hhist] at hafter hws
  rw [leanVmProgram_eq] at hafter
  -- The run: the announced sizes, the root, the rest.
  obtain ⟨u, m, m', hm, hve, -⟩ := after_bind_ret hafter
  rw [verifyExecutionClaims_eq, VerifierProgram.bind_eq] at hve
  obtain ⟨a, l₁, r, rfl, hl₁, hbody⟩ := after_bind_ret hve
  obtain ⟨lay, ρ⟩ := a
  obtain ⟨s, hg, hreads⟩ := good_of_readSizes hl₁
  obtain ⟨hlay, hs, hadm⟩ := hg
  simp only at hlay hadm
  subst hlay
  simp only [veBody, VerifierProgram.bind_eq] at hbody
  obtain ⟨v, r₁, r₂, rfl, hce, -⟩ := after_bind_ret hbody
  obtain ⟨level, rest, W', -, rfl⟩ := commitStack_after_ret hce
  set e := Ev.commit (levelShape (verifierLayout prog s).stackLog level (2 ^ level.fold)).1
    (levelShape (verifierLayout prog s).stackLog level (2 ^ level.fold)).2 W' with he
  have hce' : (commitStack (μs prog s) ρ).after [e] = some (.ret ()) := by cases v; exact hce
  have hpre : l₁ ++ [e] <+: hist := by
    rw [hm]
    exact ⟨r₂ ++ m', by simp⟩
  -- The root's shape and word.
  have hcomm : commits (l₁ ++ [e]) = commits [e] := by
    rw [Compile.commits_append, hreads, commits_map_read, List.nil_append]
  have hwell : ∀ ht w W, e = Ev.commit ht w W → WellShaped w W := by
    intro ht w W hw
    refine hws ht w W ?_
    rw [hm, ← hw]
    simp
  have hshape : O.ShapeOK₀ (μs prog s) ρ (commits (l₁ ++ [e])) := by
    rw [hcomm]; exact O.shape_commitStack hadm hwell hce'
  have hdoom : RootDoom O prog s ρ (commits (l₁ ++ [e])) :=
    ⟨hshape, O.word₀ (commits (l₁ ++ [e])), O.shape_word hshape⟩
  exact ⟨l₁ ++ [e], hpre, by rw [he]; exact boundary_append_commit _ _ _ _,
    leanVmSpec_D_commit O prog input hl₁ ⟨rfl, hs, hadm⟩ hce' hdoom⟩


/-- **Accepted, and the extractor fails, is doomed and not a good run**: the prefix of the
extracted history up to the stack's root is a boundary at which the certificate's doom holds
(`doomedRun_of_verify`), and the extracted history is not a good run (`extracted_of_goodRun`). -/
theorem doomed_of_not_extracted {c : KeccakCalls.QueryCache} {π : Proof}
    (hv : Rom.verify (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π = some true)
    (hne : ¬ Extracted O prog input c π) :
    DoomedRun (stmtCert O prog input) (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      π c ∧
    ¬ stmtG O prog input (extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π) :=
  ⟨doomedRun_of_verify O prog input hv, fun hG ↦ hne (extracted_of_goodRun O prog input hv hG)⟩

end
end LeanVM.Protocol.EndToEnd.Sound
