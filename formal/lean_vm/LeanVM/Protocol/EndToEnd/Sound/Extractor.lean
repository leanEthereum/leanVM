/-
  LeanVM.Protocol.EndToEnd.Sound.Extractor

  The knowledge extractor (`LeanVM/Protocol/Extraction/Extractor.lean`) against the proof's:
  the commitment it reads is the extracted history's, its candidates contain the proof's, and its
  memory image is the witness's. (That it then returns a valid execution whenever the proof's
  extractor finds a stack satisfying the relation is `LeanVM.Protocol.Extraction.Sound`.)
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Theorem
public import LeanVM.Protocol.EndToEnd.Front.LayoutBridgeB
public import LeanVM.Protocol.LeanIsa.Read
public import LeanVM.Protocol.Rom.Statement
public import LeanVM.Protocol.Extraction.Params
public import LeanVM.Protocol.WithHash
public import LeanVM.Protocol.WithHashBridge

/-!
# The knowledge extractor against the proof's

`LeanVM.extractor` (`LeanVM/Protocol/Extraction/Extractor.lean`) reads the commitment off a run of the
verifier's first two steps and searches the candidates for one whose memory image runs validly.
The proof's extractor `extractStack` reads it off the extracted history of the whole run and picks
a candidate satisfying the leanISA relation. The bridges:

* `xrun_bind`, `run_id_of_xrun`, `xrun_rootsInv`: the extracted run of a sequence is the runs of
  its parts, an extracted run of reads and commitments is a run with any hash and permutation from
  any sponge, and the roots of a run are its history's commitments.
* `commitment_eq`: on an accepted proof, the verifier's first two steps announce the layout of
  the announced sizes, the announced rate and a root whose committed word is the first word of the
  extracted history.
* `thrOf_eq_johnsonThreshold`: the specification's threshold is level 0's, `thrOf` (through its
  real form, `Extraction.johnsonThreshold_eq_real`).
* `encode_eq`, `mem_candidates`: the specification's encoding is `enc` of the stack's blocks, so
  the proof's candidates are the specification's.
* `haltingRun_imageOf`: the specification's memory image is the witness's (`imageOf`).
* `committedWord_eq`: the word read from the Keccak-256 answers of a prefix of the log is the
  word extracted from the whole log, provided no entry past the prefix answers the root.
* `logged2`, `prEvent_logged2_root_le`: the experiment in two stages, the adversary's log then the
  verifier's, and the probability that a fresh hash answer of the verifier is the announced root,
  at most one `2^-256` per verifier query.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## Extracted runs -/

section XRun

variable (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)

/-- **The extracted run of a sequence** is the extracted run of its first part, then of the
second from where the first stopped. -/
theorem xrun_bind {α β : Type} (f : α → VerifierProgram β) :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev),
      xrun H F (p.bind f) s h = (xrun H F p s h).bind fun r ↦ xrun H F (f r.1) r.2.1 r.2.2
  | .ret a, s, h => rfl
  | .fail, s, h => rfl
  | .read k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rfl
    · rcases Compile.absorb (m := Option) F s.sponge _ _ with _ | sp
      · rfl
      · exact xrun_bind f _ _ _
  | .sample k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    rcases squeeze (m := Option) F s.sponge with _ | r
    · rfl
    · exact xrun_bind f _ _ _
  | .grind bits k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rfl
    · rcases Compile.absorb (m := Option) F s.sponge _ _ with _ | sp
      · rfl
      · simp only [Option.bind_some]
        rcases squeeze (m := Option) F sp with _ | r
        · rfl
        · simp only [Option.bind_some]
          split
          · exact xrun_bind f _ _ _
          · rfl
  | .commit height width k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · rcases Compile.absorb (m := Option) F s.sponge _ _ with _ | sp0
      · rfl
      · simp only [Option.bind_some]
        rcases Compile.absorb (m := Option) F sp0 _ _ with _ | sp1
        · rfl
        · simp only [Option.bind_some]
          split
          · exact xrun_bind f _ _ _
          · rfl
    · rfl
  | .query i ps k, s, h => by
    simp only [VerifierProgram.bind, xrun]
    split
    · split
      · exact xrun_bind f _ _ _
      · rfl
    · rfl

/-- The events of a history are reads and commitments. -/
def ReadsCommits (l : List Ev) : Prop :=
  ∀ e ∈ l, (∃ x, e = .read x) ∨ ∃ ht w W, e = .commit ht w W

/-- **A run of reads and commitments does not depend on the hash and the permutation**: an
extracted run whose events are reads and commitments is a run with any hash `H'` and permutation
`F'` from any sponge, reaching the same value and state up to the sponge. -/
theorem run_id_of_xrun (H' : Bytes → Digest) (F' : KeccakState → KeccakState) {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h l : List Ev) {a : α} {s' :
        VerifierProgramState},
      xrun H F p s h = some (a, s', h ++ l) → ReadsCommits l → ∀ sp : Sponge,
        ∃ sp', Id.run (Compile.runWithHash H' F' p { s with sponge := sp }) =
          some (a, { s' with sponge := sp' })
  | .ret a, s, h, l, _, _, hr, _, sp => by
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, -⟩ := hr
    exact ⟨sp, rfl⟩
  | .fail, s, h, l, _, _, hr, _, _ => by simp [xrun] at hr
  | .read k, s, h, l, _, _, hr, hrc, sp => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · rename_i x xs hs
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp0, -, hr⟩ := hr
      obtain ⟨l', hl'⟩ := xrun_prefix H F _ _ _ hr
      have hl : l = Ev.read x :: l' := by simpa using hl'.symm
      subst hl
      rw [← hl'] at hr
      obtain ⟨sp', hrun⟩ := run_id_of_xrun H' F' _ _ _ l' hr
        (fun e he ↦ hrc e (List.mem_cons_of_mem _ he))
        (Compile.absorb (m := Id) F' sp x dsObserve)
      refine ⟨sp', ?_⟩
      simp only [Compile.runWithHash, hs]
      exact hrun
  | .sample k, s, h, l, _, _, hr, hrc, _ => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨r, -, hr⟩ := hr
    obtain ⟨l', hl'⟩ := xrun_prefix H F _ _ _ hr
    have hl : l = Ev.sample r.1 :: l' := by simpa using hl'.symm
    subst hl
    rcases hrc _ List.mem_cons_self with ⟨x, hx⟩ | ⟨ht, w, W, hx⟩ <;> cases hx
  | .grind bits k, s, h, l, _, _, hr, hrc, _ => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp0, -, r, -, hr⟩ := hr
      split at hr
      · obtain ⟨l', hl'⟩ := xrun_prefix H F _ _ _ hr
        have hl : l = Ev.grind bits :: l' := by simpa using hl'.symm
        subst hl
        rcases hrc _ List.mem_cons_self with ⟨x, hx⟩ | ⟨ht, w, W, hx⟩ <;> cases hx
      · simp at hr
  | .commit height width k, s, h, l, _, _, hr, hrc, sp => by
    simp only [xrun] at hr
    split at hr
    · rename_i x0 x1 xs hs
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp0, -, sp1, -, hr⟩ := hr
      split at hr
      · rename_i root hroot
        obtain ⟨l', hl'⟩ := xrun_prefix H F _ _ _ hr
        have hl : l = Ev.commit height width (extract H root height width) :: l' := by
          simpa using hl'.symm
        subst hl
        rw [← hl'] at hr
        obtain ⟨sp', hrun⟩ := run_id_of_xrun H' F' _ _ _ l' hr
          (fun e he ↦ hrc e (List.mem_cons_of_mem _ he))
          (Compile.absorb (m := Id) F' (Compile.absorb (m := Id) F' sp x0 dsObserve) x1
            dsObserve)
        refine ⟨sp', ?_⟩
        simp only [Compile.runWithHash, hs, hroot]
        exact hrun
      · simp at hr
    · simp at hr
  | .query i ps k, s, h, l, _, _, hr, hrc, _ => by
    simp only [xrun] at hr
    split at hr
    · next root ht w phase rest hroot hphase =>
      split at hr
      · next rows ho =>
        obtain ⟨l', hl'⟩ := xrun_prefix H F _ _ _ hr
        have hl : l = Ev.query rows :: l' := by simpa using hl'.symm
        subst hl
        rcases hrc _ List.mem_cons_self with ⟨x, hx⟩ | ⟨ht, w, W, hx⟩ <;> cases hx
      · simp at hr
    · simp at hr

/-- **The roots of an extracted run are its history's commitments**, the words extracted under
the roots. -/
theorem xrun_rootsInv {α : Type} :
    ∀ (p : VerifierProgram α) (s : VerifierProgramState) (h : List Ev) {a : α} {s' :
        VerifierProgramState} {h' : List Ev},
      RootsInv H s h → xrun H F p s h = some (a, s', h') → RootsInv H s' h'
  | .ret a, s, h, _, _, _, hR, hr => by
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact hR
  | .fail, s, h, _, _, _, _, hr => by simp [xrun] at hr
  | .read k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · rename_i x xs hs
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp, -, hr⟩ := hr
      exact xrun_rootsInv _ _ _ (rootsInv_append_read hR x sp xs) hr
  | .sample k, s, h, _, _, _, hR, hr => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨r, -, hr⟩ := hr
    exact xrun_rootsInv _ _ _ (rootsInv_append_sample hR _ r.2) hr
  | .grind bits k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · rename_i n xs hs
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp, -, r, -, hr⟩ := hr
      split at hr
      · exact xrun_rootsInv _ _ _ (rootsInv_append_grind hR bits r.2 xs) hr
      · simp at hr
  | .commit height width k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · rename_i x0 x1 xs hs
      simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨sp0, -, sp1, -, hr⟩ := hr
      split at hr
      · rename_i root hroot
        exact xrun_rootsInv _ _ _ (rootsInv_append_commit hR root height width sp1 xs) hr
      · simp at hr
    · simp at hr
  | .query i ps k, s, h, _, _, _, hR, hr => by
    simp only [xrun] at hr
    split at hr
    · next root ht w phase rest hroot hphase =>
      split at hr
      · next rows ho =>
        exact xrun_rootsInv _ _ _ (rootsInv_append_query hR rows rest) hr
      · simp at hr
    · simp at hr

end XRun

/-! ## The commitment -/

/-- Reads commit nothing. -/
theorem commits_map_read (xs : List E) : commits (xs.map Ev.read) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [commits] using ih

variable {prog : LeanIsaProgram} {input : PublicInput}

/-- The root the proof announces for the stack: the first root the verifier's steps 1 and 2
read off it. -/
def announcedRoot (prog : LeanIsaProgram) (π : Proof) : Option Digest :=
  (Extraction.afterRoot (bytecodeWords prog) π).bind fun x ↦ x.2.roots.head?.map (·.1)

/-- **The specification's commitment is the extracted history's**: on an accepted proof, the
verifier's first two steps (`afterRoot`) announce the layout of the history's announced sizes and
its rate, and a root whose word under the hash answers is the history's first word. The sizes
are good and the ladder has a first level. -/
theorem commitment_eq {c : KeccakCalls.QueryCache} {π : Proof}
    (hv : Rom.verify (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π = some true)
    {s : Sizes} {ρ : ℕ} {W : Word}
    (hann : announced prog (extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π) = some (s, ρ))
    (hfw : firstWord (extractedHistory (fun x ↦ c (.inl x)) (fun s ↦ c (.inr s))
      (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π) = some W) :
    (∃ root ht w, announcedRoot prog π = some root ∧
      W = extract (fun x ↦ c (.inl x)) root ht w ∧
      ∃ st, Extraction.afterRoot (bytecodeWords prog) π = some ((verifierLayout prog s, ρ), st) ∧
        st.roots.head? = some (root, ht, w)) ∧
      Good prog (verifierLayout prog s, ρ) s ∧
      ∃ level rest, Whir.ladder (verifierLayout prog s).stackLog ρ = some (level :: rest) := by
  set H : Bytes → Option Digest := fun x ↦ c (.inl x)
  set F : KeccakState → Option KeccakState := fun s ↦ c (.inr s)
  set hist := extractedHistory H F (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
    (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) π with hhist
  obtain ⟨seed, sf, hseed, hx⟩ := xrun_of_verify hv
  rw [← hhist] at hx
  -- The run: the announced sizes, the root, the rest.
  have hP : leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input) =
      ((readAnnouncedSizes (bytecodeWords prog)).bind fun a ↦ veBody (publicInputDigest input) a.1
          a.2).bind
        fun _ ↦ .ret true := by
    rw [leanVmProgram_eq, verifyExecution_eq]
  rw [hP, xrun_bind, Option.bind_eq_some_iff] at hx
  obtain ⟨⟨u, s3, h3⟩, hx3, hfin⟩ := hx
  simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hfin
  obtain ⟨-, -, rfl⟩ := hfin
  rw [xrun_bind, Option.bind_eq_some_iff] at hx3
  obtain ⟨⟨a, s1, h1⟩, hx1, hx3⟩ := hx3
  obtain ⟨g, hg⟩ : ∃ g, veBody (publicInputDigest input) a.1 a.2 =
      (commitStack a.1.stackLog a.2).bind g := ⟨_, rfl⟩
  simp only at hx3
  rw [hg, xrun_bind, Option.bind_eq_some_iff] at hx3
  obtain ⟨⟨v, s2, h2⟩, hx2, hx4⟩ := hx3
  have hpre2 : h2 <+: hist := xrun_prefix H F _ _ _ hx4
  -- The histories of the two steps.
  obtain ⟨l₁, hl₁, ha, -⟩ := xrun_after H F _ _ _ hx1
  simp only [List.nil_append] at hl₁
  subst h1
  obtain ⟨l₂, rfl, hc, -⟩ := xrun_after H F _ _ _ hx2
  obtain ⟨level, rest, W', hcfg, rfl⟩ := commitStack_after_ret hc
  obtain ⟨s', hgood⟩ := good_of_readSizes prog ha
  obtain ⟨s'', -, -, -, hreads⟩ := readSizes_ret_sizes prog ha
  -- The roots.
  have hR0 : RootsInv H ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ [] := rfl
  have hR1 := xrun_rootsInv H F _ _ _ hR0 hx1
  have hR2 := xrun_rootsInv H F _ _ _ hR1 hx2
  have hc1 : commits l₁ = [] := by rw [hreads]; exact commits_map_read _
  rw [RootsInv, hc1] at hR1
  have hroots1 : s1.roots = [] := List.map_eq_nil_iff.mp hR1.symm
  rw [RootsInv, Compile.commits_append, hc1, List.nil_append] at hR2
  simp only [commits] at hR2
  obtain ⟨r, hr2⟩ : ∃ r, s2.roots = [r] := by
    rcases hs : s2.roots with _ | ⟨r, _ | ⟨r', rs⟩⟩
    · rw [hs] at hR2; simp at hR2
    · exact ⟨r, rfl⟩
    · rw [hs] at hR2; simp at hR2
  rw [hr2] at hR2
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hR2
  obtain ⟨hht, hw, hW'⟩ := hR2
  -- The announced sizes and the first word.
  have hann' := announced_eq prog ((List.prefix_append l₁ _).trans hpre2) ha hgood.1
  rw [hann, Option.some.injEq, Prod.mk.injEq] at hann'
  obtain ⟨rfl, rfl⟩ := hann'
  have hfw2 : firstWord (l₁ ++ [Ev.commit (levelShape a.1.stackLog level (2 ^ level.fold)).1
      (levelShape a.1.stackLog level (2 ^ level.fold)).2 W']) = some W' := by
    simp [firstWord, Compile.commits_append, hc1, commits]
  obtain ⟨m, hm⟩ := hpre2
  rw [← hm, firstWord_append hfw2 m, Option.some.injEq] at hfw
  subst hfw
  -- The specification's run of the two steps.
  have hxa : xrun H F (Extraction.announceSizesAndRoot (bytecodeWords prog))
      ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ [] = some (a, s2, [] ++ (l₁ ++ [Ev.commit
        (levelShape a.1.stackLog level (2 ^ level.fold)).1
        (levelShape a.1.stackLog level (2 ^ level.fold)).2 W'])) := by
    change xrun H F ((readAnnouncedSizes (bytecodeWords prog)).bind fun a ↦
      (commitStack a.1.stackLog a.2).bind fun _ ↦ .ret a) _ _ = _
    rw [xrun_bind, hx1, Option.bind_some]
    simp only
    rw [xrun_bind, hx2, Option.bind_some]
    rfl
  have hrc : ReadsCommits (l₁ ++ [Ev.commit (levelShape a.1.stackLog level (2 ^ level.fold)).1
      (levelShape a.1.stackLog level (2 ^ level.fold)).2 W']) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · rw [hreads] at he
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
      exact Or.inl ⟨x, rfl⟩
    · rw [List.mem_singleton] at he
      exact Or.inr ⟨_, _, _, he⟩
  obtain ⟨sp', hrun⟩ := run_id_of_xrun H F (fun _ ↦ default) (fun _ ↦ default) _ _ _ _ hxa hrc
    ⟨default, []⟩
  have haf : Extraction.afterRoot (bytecodeWords prog) π = some (a, { s2 with sponge := sp' }) := by
    rw [Extraction.afterRoot, Compile.runPure_eq_withHash]
    exact hrun
  refine ⟨⟨r.1, r.2.1, r.2.2, ?_, hW', { s2 with sponge := sp' }, ?_, ?_⟩,
    by rw [← hgood.1]; exact hgood, by rw [← hgood.1]; exact ⟨level, rest, hcfg⟩⟩
  · simp [announcedRoot, haf, hr2]
  · rw [haf, ← hgood.1]
  · show s2.roots.head? = _
    rw [hr2]
    rfl

/-! ## The threshold -/

/-- Level 0's certified slack is the specification's `johnsonSlack`, for every admissible
shape (kernel evaluation). -/
theorem certOf_e_eq : ∀ μ < 29, ∀ R < 5, Whir.Admissible μ R →
    (Whir.Params.certOf μ R 0).e =
      (Extraction.johnsonSlack.getD (R - 1) []).getD (μ - Whir.minLogStack) 0 := by
  decide +kernel

/-- **The specification's threshold is level 0's**, `thrOf`, at every admissible shape with a
ladder: through its real form (`Extraction.johnsonThreshold_eq_real`). -/
theorem thrOf_eq_johnsonThreshold {μ R : ℕ} (h : Whir.Admissible μ R) {level : Whir.Level}
    {rest : List Whir.Level} (hc : Whir.ladder μ R = some (level :: rest)) :
    thrOf μ R = Extraction.johnsonThreshold μ R := by
  rw [← Extraction.johnsonThreshold_eq_real]
  have hc' : Whir.ladder μ R = some (level :: rest) := hc
  have hμ : μ < 29 := by have := h.2.1; unfold Whir.maxLogStack at this; omega
  have hR : R < 5 := by have := h.2.2.2; omega
  have hok := Whir.Params.shapeOK_all μ hμ R hR h
  rw [Whir.Params.shapeOK, hc'] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hchk, hd⟩ := hok
  obtain ⟨hκ, hR', -, -⟩ := of_decide_eq_true hd
  have h0 := Whir.Params.chkLevels_head hchk
  have he := certOf_e_eq μ hμ R hR h
  rw [thrOf, Whir.Params.deployedCodes, Whir.Params.codesOf, Whir.Params.mkCode_eq h0]
  show ⌈ReedSolomon.HiddenDerivative.johnsonAgreement
      (2 ^ ((Whir.Params.certOf μ R 0).κ + (Whir.Params.certOf μ R 0).R))
      (2 ^ (Whir.Params.certOf μ R 0).κ - 1) (Whir.Params.certOf μ R 0).eta *
      ((2 ^ ((Whir.Params.certOf μ R 0).κ + (Whir.Params.certOf μ R 0).R) : ℕ) : ℝ)⌉₊ = _
  rw [hκ, hR', Whir.Params.Cert.eta, he]
  rfl

/-! ## The candidates -/

/-- **The specification's encoding is `enc` of the stack's blocks**, lifted to `E`. -/
theorem encode_eq {μ R : ℕ} (q : Column μ) (u : Fin (2 ^ laneBits))
    (v : Fin (2 ^ (μ - laneBits + R))) :
    enc (μ - laneBits) R (EndToEnd.blockOf q u) v =
      ofK (Extraction.encode (μ := μ) q.values u v) := by
  have hb : EndToEnd.blockOf q u =
      fun x ↦ ofK (q.values.getD (bitsToNat x + 2 ^ (μ - laneBits) * u) 0) := rfl
  rw [hb, enc_ofK]
  show ofK (encK _ R _ v) = _
  congr 1
  rw [encK, Extraction.encode, ← Fin.sum_univ_eq_sum_range (fun j ↦
    q.values.getD (j + 2 ^ (μ - Whir.initialFold) * u) 0 *
      Extraction.novelBasis j (K.ofBits v))]
  exact Fintype.sum_equiv (bitsEquiv _) _ _ (fun x ↦ by rw [bitsEquiv_val]; rfl)

/-- **The proof's candidates are the specification's**, at a lower threshold. -/
theorem mem_candidates {μ R A A' : ℕ} {W : Word} {q : Column μ}
    (hq : q ∈ Candidates μ R A W) (hA : A' ≤ A) :
    (q.values : Vector K (2 ^ μ)) ∈ Extraction.Candidates μ R A' W := by
  obtain ⟨S, hS, hag⟩ := hq
  refine hA.trans (hS.trans ?_)
  rw [← Finset.card_map Fin.valEmbedding]
  refine Finset.card_le_card fun v hv ↦ ?_
  obtain ⟨v, hvS, rfl⟩ := Finset.mem_map.mp hv
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr v.isLt, fun u ↦ ?_⟩
  have h : laneOf W u v = ofK (Extraction.encode (μ := μ) q.values u v) :=
    (hag v hvS u).trans (encode_eq q u v)
  exact ofK_injective h

/-- **The specification's candidates are the proof's**: a stack whose encoding agrees with the
word on at least `A` columns is a candidate of the proof's at `A`. -/
theorem candidates_of_values {μ R A : ℕ} {W : Word} {q : Vector K (2 ^ μ)}
    (hq : q ∈ Extraction.Candidates μ R A W) : (⟨q⟩ : Column μ) ∈ Candidates μ R A W := by
  let S : Finset (Fin (2 ^ (μ - laneBits + R))) :=
    Finset.univ.filter fun v ↦ (v : ℕ) ∈ Extraction.agreement R W q
  refine ⟨S, hq.trans ?_, fun v hv u ↦ ?_⟩
  · rw [← Finset.card_map Fin.valEmbedding]
    refine Finset.card_le_card fun v hv ↦ ?_
    have hlt : v < 2 ^ (μ - laneBits + R) :=
      Finset.mem_range.mp (Finset.mem_filter.mp hv).1
    exact Finset.mem_map.mpr ⟨⟨v, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  · have h := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).2).2 u
    refine Eq.trans ?_ (encode_eq (R := R) ⟨q⟩ u v).symm
    exact congrArg ofK h

/-- An admissible shape has a ladder. -/
theorem exists_ladder {μ R : ℕ} (h : Whir.Admissible μ R) :
    ∃ level rest, Whir.ladder μ R = some (level :: rest) := by
  have hμ : μ < 29 := by have := h.2.1; unfold Whir.maxLogStack at this; omega
  have hR : R < 5 := by have := h.2.2.2; omega
  have hok := Whir.Params.shapeOK_all μ hμ R hR h
  rw [Whir.Params.shapeOK] at hok
  rcases hc : Whir.ladder μ R with _ | config
  · rw [hc] at hok
    simp at hok
  · have hl := Whir.ladder_length h config hc
    match config, hl with
    | level :: rest, _ => exact ⟨level, rest, rfl⟩

/-- **The specification's candidates are at most `2^12`**: at every admissible shape, the
stacks whose encoding agrees with a word on at least the Johnson threshold of columns are among
the proof's candidates, at most level 0's list bound `listMax ≤ 2^12` (`candidates_ncard_le`,
`Whir.Params.deployed_spec_hyps`). -/
theorem spec_candidates_ncard_le {μ R : ℕ} (h : Whir.Admissible μ R) (W : Word) :
    (Extraction.Candidates μ R (Extraction.johnsonThreshold μ R) W).ncard ≤ 2 ^ 12 := by
  obtain ⟨level, rest, hc⟩ := exists_ladder h
  obtain ⟨-, hμ, hκ, hR, hL, -, -⟩ := Whir.Params.deployed_spec_hyps h hc
  have hthr : (Whir.Params.deployedCodes μ R 0).thr = Extraction.johnsonThreshold μ R :=
    thrOf_eq_johnsonThreshold h hc
  have hfin := candidates_finite (Whir.Params.deployedCodes μ R 0) hκ hR hμ W
  have hcard := candidates_ncard_le (Whir.Params.deployedCodes μ R 0) hκ hR hμ W
  rw [hthr] at hfin hcard
  have hsub : Extraction.Candidates μ R (Extraction.johnsonThreshold μ R) W ⊆
      (fun c : Column μ ↦ (c.values : Vector K (2 ^ μ))) ''
        Candidates μ R (Extraction.johnsonThreshold μ R) W :=
    fun q hq ↦ ⟨⟨q⟩, candidates_of_values hq, rfl⟩
  calc _ ≤ _ := Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ _ := Set.ncard_image_le hfin
    _ ≤ _ := hcard.trans hL

/-! ## The memory image -/

/-- Halting runs of equal images are equal. -/
theorem haltingRun_congr {κ κ' : ℕ} (L : MemoryImage κ) (L' : MemoryImage κ') (e : κ = κ')
    (hL : ∀ i : Fin (2 ^ κ), L i = L' (Fin.cast (congrArg (2 ^ ·) e) i)) :
    Extraction.haltingRun prog L = Extraction.haltingRun prog L' := by
  subst e
  have : L = L' := funext hL
  rw [this]

/-- An entry read with a default inside the vector. -/
theorem getD_eq {n : ℕ} (v : Vector K n) {i j : ℕ} (hij : i = j) (h : i < n) :
    v[i] = v.getD j 0 := by
  subst hij
  simp [Vector.getD, h]

/-- A cell of a memory column is the stack's cell at the column's placement. -/
theorem cell_memCol (s : Sizes) (q : Column (leanIsaμ prog s)) (j : Fin 4)
    (x : Fin (2 ^ s.logMem)) :
    cell prog s q (memCol j) x =
      q.values.getD (((verifierLayout prog s).placement j).index + x) 0 := by
  have hp := placement_committed prog s (memCol j) (not_isVirtual_memCol j)
  rw [refCol_memCol] at hp
  rw [hp]
  have h := column_committed prog s q (memCol j) (not_isVirtual_memCol j) x
  exact h.trans (getD_eq _ (Nat.add_comm _ _) _)

/-- **The specification's memory image is the witness's**: their halting runs agree. -/
theorem haltingRun_imageOf (s : Sizes) (hs : s.logMem ≤ maxLogMem)
    (q : Column (leanIsaμ prog s)) :
    Extraction.haltingRun prog (imageOf (witnessOf prog s q).data).2 =
      Extraction.haltingRun prog
        (Extraction.memoryImage (verifierLayout prog s) (q.values : Vector K (2 ^ _))) := by
  have hrows : memRows (witnessOf prog s q).data = LeanIsa.imageRows prog s q :=
    memRows_witnessOf prog s q (lt_of_le_of_lt hs (by decide))
  have hκ : (imageOf (witnessOf prog s q).data).1 = s.logMem := by
    simp only [imageOf, hrows, LeanIsa.imageRows, Array.size_ofFn,
      Nat.log_pow (by norm_num : 1 < 2)]
    exact min_eq_left hs
  refine haltingRun_congr _ _ hκ fun i ↦ ?_
  simp only [imageOf, hrows]
  have hi : (i : ℕ) < (LeanIsa.imageRows prog s q).size := by
    rw [LeanIsa.imageRows, Array.size_ofFn]; exact lt_of_lt_of_eq i.isLt (by rw [hκ])
  rw [Array.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
  simp only [LeanIsa.imageRows, Array.getElem_ofFn, Extraction.memoryImage]
  simp only [cell_memCol]
  rfl

/-- A witness representing a valid execution has its image's halting run, valid. -/
theorem haltingRun_valid {κw : ℕ} {w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog κw)}
    {t : Execution prog}
    (hrep : AssignmentRepresents w t) (hv : ValidExecution prog input t) :
    ∃ t', Extraction.haltingRun prog (imageOf w.data).2 = some t' ∧
      ValidExecution prog input t' := by
  obtain ⟨κ, image, steps⟩ := t
  obtain ⟨hκ, himage, -⟩ := hrep
  generalize imageOf w.data = p at hκ himage ⊢
  obtain ⟨κ', image'⟩ := p
  dsimp only at hκ himage ⊢
  subst hκ
  obtain rfl : image' = image := funext fun i ↦ himage i i.isLt
  have h : ∃ n, Semantics.run prog image' n Registers.initial = some (Registers.final prog) :=
    ⟨steps, hv.2⟩
  rcases hh : Extraction.haltingRun prog image' with _ | t'
  · simp [Extraction.haltingRun, h] at hh
  · simp only [Extraction.haltingRun, h, ↓reduceDIte, Option.some.injEq] at hh
    subst hh
    exact ⟨_, rfl, hv.1, by dsimp only; convert Nat.find_spec h using 3⟩

/-! ## The extractor -/

/-- **The word the specification reads from a prefix of the log is the word extracted from the
whole log**, without failure and when no hash entry past the prefix answers the root. -/
theorem committedWord_eq {X : Type} {σ : Seeds X} {ℓ : Log} {k : ℕ} {r : Digest}
    (hf : ¬ Fail σ ℓ) (hr : ∀ x, .inl (x, r) ∉ ℓ.drop k) (ht w : ℕ) :
    Extraction.committedWord (lookH (ℓ.take k)) r ht w = extract (lookH ℓ) r ht w := by
  have hbefore : HEntriesBefore ℓ r k := by
    intro i hi x hei
    by_contra hik
    refine hr x ?_
    rw [List.mem_iff_getElem]
    exact ⟨i - k, by simp; omega, by
      simp only [List.getElem_drop, Nat.add_sub_cancel' (by omega : k ≤ i)]; exact hei⟩
  rw [← extract_take_eq hf hbefore ht w]
  rfl

/-! ## The experiment in two stages -/

/-- The logged experiment in two stages: the adversary's run from the empty log, with the log it
leaves, then the verifier's run from that log. -/
noncomputable def logged2 {α : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) : ProbComp ((α × Log) × (Bool × Log)) :=
  (simulateQ loggedRO A).run [] >>= fun p ↦
    (fun r ↦ (p, r)) <$> (simulateQ loggedRO (V p.1)).run p.2

/-- The logged experiment forgets the adversary's log. -/
theorem logExperiment_eq_logged2 {α : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) :
    logExperiment A V = (fun w ↦ ((w.1.1, w.2.1), w.2.2)) <$> logged2 A V := by
  rw [logExperiment, Rom.run_simulateQ_bind, logged2, map_bind]
  refine bind_congr fun p ↦ ?_
  rw [simulateQ_map, StateT.run_map, Functor.map_map]

/-- The adversary's announced root answered by a hash entry past its log. -/
def RootAnswered {α : Type} (root : α → Option Digest) (a : α) (ℓ₀ ℓ : Log) : Prop :=
  ∃ r, root a = some r ∧ ∃ x, .inl (x, r) ∈ ℓ.drop ℓ₀.length

/-- **The verifier rarely answers the announced root afresh**: the probability that a fresh
hash answer of the verifier, past the adversary's log, is the root `root` of the adversary's
output is at most one `2^-256` per verifier query. Permutation answers are states, never roots. -/
theorem prEvent_logged2_root_le {α : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) (QV : ℕ) (hV : ∀ a, IsTotalQueryBound (V a) QV)
    (root : α → Option Digest) :
    Pr{let w ← logged2 A V}[¬ w.1.2 <+: w.2.2 ∨ RootAnswered root w.1.1 w.1.2 w.2.2] ≤
      QV * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  unfold logged2
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ ↦ ?_
  rw [prEvent_map]
  let Φ : Log → ℝ≥0∞ := fun ℓ ↦ ind (RootAnswered root p.1 p.2 ℓ)
  have hdrop : ∀ (ℓ : Log) (e : Entry), (ℓ ++ [e]).drop p.2.length ⊆ ℓ.drop p.2.length ++ [e] := by
    intro ℓ e x hx
    rw [List.drop_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_of_mem_drop hx)
  have hΦ : LogFreshStepBound Φ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ t _ ↦ ?_, fun ℓ t _ ↦ ?_⟩
    · have hstep : ∀ u, Φ (ℓ ++ [.inl (t, u)]) ≤ ind (root p.1 = some u) + Φ ℓ := fun u ↦ by
        refine (ind_mono ?_).trans ((ind_or_le _ _).trans (le_of_eq (add_comm _ _)))
        rintro ⟨r, hr, x, hx⟩
        rcases List.mem_append.mp (hdrop ℓ _ hx) with hx | hx
        · exact Or.inl ⟨r, hr, x, hx⟩
        · rw [List.mem_singleton] at hx
          cases hx
          exact Or.inr hr
      have hsum : ∑ u, ind (root p.1 = some u) ≤ 1 :=
        sum_ind_le_one fun u u' hu hu' ↦ Option.some.inj (hu.symm.trans hu')
      have h1 : (∑ u, Φ (ℓ ++ [.inl (t, u)])) / Fintype.card Digest ≤
          (∑ u, (ind (root p.1 = some u) + Φ ℓ)) / Fintype.card Digest :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hstep u) _
      rw [avg_add_const] at h1
      refine h1.trans ?_
      have h2 : (∑ u, ind (root p.1 = some u)) / Fintype.card Digest ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        have h3 : (∑ u, ind (root p.1 = some u)) / Fintype.card Digest ≤
            1 / Fintype.card Digest := ENNReal.div_le_div_right hsum _
        rw [card_digest, Nat.cast_pow, Nat.cast_ofNat, one_div] at h3
        rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
        exact h3
      rw [add_comm]
      exact add_le_add le_rfl h2
    · have hstep : ∀ u, Φ (ℓ ++ [.inr (t, u)]) ≤ Φ ℓ := fun u ↦ by
        refine ind_mono ?_
        rintro ⟨r, hr, x, hx⟩
        rcases List.mem_append.mp (hdrop ℓ _ hx) with hx | hx
        · exact ⟨r, hr, x, hx⟩
        · simp at hx
      exact (avg_le_of_le hstep).trans le_self_add
  dsimp only
  refine (prEvent_run_loggedRO_le_of_freshStepBound hΦ (V p.1) QV (hV p.1) p.2
    (fun _ ℓ ↦ ¬ p.2 <+: ℓ ∨ RootAnswered root p.1 p.2 ℓ) ?_).trans ?_
  · intro z hz hev
    have hpre := (simulateQ_look_of_mem_support _ p.2 z hz).1
    rcases hev with hn | hr
    · exact absurd hpre hn
    · exact (ind_of hr).ge
  · simp [Φ, RootAnswered, ind]

end
end LeanVM.Protocol.EndToEnd.Sound
