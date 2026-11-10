/-
  LeanVM.Protocol.EndToEnd.Sound.Moves

  The prover moves a verifier program allows: a structural predicate on programs of the verifier
  language (the bits of its proofs of work, whether it reads commitments, what it returns, and
  that a challenge follows each proof of work), its rules, and its instances on every phase of
  leanVM's verifier program.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Grind

/-!
# The prover moves of the leanVM verifier

`Moves g c Q G p` says that every proof of work `p` checks has its bits in `g` and is followed at
once by a challenge, inside `p` or, where `p` returns right after it a value satisfying `G`, by
the follower; that `p` reads a commitment only if `c` holds; and that every value `p` returns
satisfies `Q`. It is structural, with no arithmetic, and composes through `bind` (`Moves.seq`):
the follower of a return right after a proof of work must start with a challenge
(`VerifierProgram.StartsSample`). It survives along histories (`Moves.after`). Its uses:

* `Moves.grindThenSample`: a whole program whose returns need no follower (`G := False`) has
  `GrindThenSample`, the property the random-oracle theorem's grind step reads
  (`LeanVM.Protocol.Compile.Prog`): the challenge after a proof of work is drawn by the grind's own
  permutation;
* `Moves.reach_commits`: a sub-program that reads no commitment (`c := False`) adds none to a run,
  so the words its openings answer from are the ones committed before it;
* `Moves.grindBits_le`: on a program whose proofs of work have at most `B` bits, every reachable
  history ends with a proof of work of at most `B` bits.

The instances follow `leanVmVerifierProgram` (`Statement/LeanVmVerifier.lean`, leanVM `f128`)
phase by phase. Every grind is followed by a challenge: the sumcheck rounds' grinds by the round's
challenge, the bus's by the slot weights, a GKR step's by its combiner and its `y`, the table
phase's by `ξ`, the Keccak reduction's by its segment, `s` and `β`, ring switching's by its map,
WHIR's fold grinds by `θ` and `(γ, α, β)`, its query grinds by the first query sample (every
deployed level queries, `ladder_queries_pos`) and its batching grinds by `λ`, and the commitment's
OOD grind by its point, which has at least `minLogStack` coordinates (`readAnnouncedSizes`
checks it). Every grind has at most `64` bits (`grindingBits_le_sixtyFour`): the theorem
`grindBits_le_of_reachable` is the cap at which the random-oracle theorem discounts a group.

The instances hold at every bound `B ≥ 17` (`moves_*_le`), the bus's grind bounded at the layout
(`BusGrindLE`); the `G64` forms are those at `B = 64`. On a program's own bytecode the bus's grind
has at most `25` bits, and so has every grind (`Complete.moves_leanVm_twentyFive`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier VerifierProgram

@[expose] public section

variable {α β : Type}

/-! ## The predicate -/

/-- Every prover move of `p` is allowed, every proof of work followed by a challenge, and every
return satisfies `Q`: see the module docstring. -/
def Moves (g : ℕ → Prop) (c : Prop) (Q G : α → Prop) : VerifierProgram α → Prop
  | .ret a => Q a
  | .fail => True
  | .read k => ∀ x, Moves g c Q G (k x)
  | .sample k => ∀ x, Moves g c Q G (k x)
  | .grind b k => g b ∧ k.StartsSample G ∧ Moves g c Q G k
  | .commit _ _ k => c ∧ Moves g c Q G k
  | .query _ _ k => ∀ rows, Moves g c Q G (k rows)

/-- The moves of a phase that returns anything and may end on a proof of work. -/
abbrev MovesOK (g : ℕ → Prop) (c : Prop) (p : VerifierProgram α) : Prop :=
  Moves g c (fun _ ↦ True) (fun _ ↦ True) p

namespace Moves

variable {g : ℕ → Prop} {c : Prop} {Q G : α → Prop}

theorem startsSample_mono {R R' : α → Prop} (hR : ∀ a, R a → R' a) :
    ∀ {q : VerifierProgram α}, q.StartsSample R → q.StartsSample R'
  | .sample _, _ => trivial
  | .ret a, h => hR a h

/-- Monotonicity. -/
theorem mono {g' : ℕ → Prop} {c' : Prop} {Q' G' : α → Prop} (hg : ∀ b, g b → g' b)
    (hc : c → c') (hQ : ∀ a, Q a → Q' a) (hG : ∀ a, G a → G' a) :
    ∀ {p : VerifierProgram α}, Moves g c Q G p → Moves g' c' Q' G' p
  | .ret a, h => hQ a h
  | .fail, _ => trivial
  | .read _, h => fun x ↦ mono hg hc hQ hG (h x)
  | .sample _, h => fun x ↦ mono hg hc hQ hG (h x)
  | .grind b _, h => ⟨hg b h.1, startsSample_mono hG h.2.1, mono hg hc hQ hG h.2.2⟩
  | .commit _ _ _, h => ⟨hc h.1, mono hg hc hQ hG h.2⟩
  | .query _ _ _, h => fun rows ↦ mono hg hc hQ hG (h rows)

/-- **Sequencing**: the follower runs on every value `p` returns, and starts with a challenge
where `p` returns right after a proof of work. -/
theorem bind {Q' G' : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : Moves g c Q G p) (hf : ∀ a, Q a → Moves g c Q' G' (f a))
    (hs : ∀ a, Q a → G a → (f a).StartsSample G') : Moves g c Q' G' (p.bind f) := by
  induction p with
  | ret a => exact hf a hp
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih =>
    refine ⟨hp.1, ?_, ih hp.2.2⟩
    obtain ⟨-, hk, hm⟩ := hp
    cases k with
    | sample k' => trivial
    | ret a => exact hs a hm hk
    | _ => exact hk.elim
  | commit ht w k ih => exact ⟨hp.1, ih hp.2⟩
  | query i ps k ih => exact fun rows ↦ ih rows (hp rows)

/-- Sequencing in `do` notation. -/
theorem seq {Q' G' : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : Moves g c Q G p) (hf : ∀ a, Q a → Moves g c Q' G' (f a))
    (hs : ∀ a, Q a → G a → (f a).StartsSample G') : Moves g c Q' G' (p >>= f) :=
  bind hp hf hs

/-- Sequencing after a part that never returns right after a proof of work. -/
theorem seq' {Q' G' : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : Moves g c Q (fun _ ↦ False) p) (hf : ∀ a, Q a → Moves g c Q' G' (f a)) :
    Moves g c Q' G' (p >>= f) :=
  bind hp hf fun _ _ h ↦ h.elim

theorem fail : Moves g c Q G (VerifierProgram.fail : VerifierProgram α) := trivial

theorem pure {a : α} (h : Q a) : Moves g c Q G (Pure.pure a : VerifierProgram α) := h

theorem ret {a : α} (h : Q a) : Moves g c Q G (VerifierProgram.ret a) := h

theorem readE {G : E → Prop} : Moves g c (fun _ ↦ True) G readScalar := fun _ ↦ trivial

theorem sampleE {G : E → Prop} : Moves g c (fun _ ↦ True) G sampleChallenge := fun _ ↦ trivial

/-- `n` reads, `n` values. -/
theorem readN : ∀ n, Moves g c (fun xs ↦ xs.length = n) (fun _ ↦ False) (readScalars n)
  | 0 => rfl
  | n + 1 => seq' readE fun _ _ ↦ seq' (readN n) fun xs hxs ↦ by
      change (_ :: xs).length = n + 1
      rw [List.length_cons, hxs]

/-- `n` samples, `n` values. -/
theorem sampleN : ∀ n, Moves g c (fun xs ↦ xs.length = n) (fun _ ↦ False) (sampleChallenges n)
  | 0 => rfl
  | n + 1 => seq' sampleE fun _ _ ↦ seq' (sampleN n) fun xs hxs ↦ by
      change (_ :: xs).length = n + 1
      rw [List.length_cons, hxs]

/-- A check. -/
theorem require (q : Prop) [Decidable q] :
    Moves g c (fun _ ↦ q) (fun _ ↦ False) (VerifierProgram.require q) := by
  unfold VerifierProgram.require
  split
  · exact ‹q›
  · trivial

/-- A pure step that may fail returns the option's value. -/
theorem liftOption (o : Option α) : Moves g c (fun a ↦ o = some a) (fun _ ↦ False)
    (Verifier.liftOption o) := by
  cases o
  · trivial
  · rfl

/-- A proof of work. -/
theorem grindP {b : ℕ} (hb : b ≠ 0 → g b) :
    Moves g c (fun _ ↦ True) (fun _ ↦ True) (grindProofOfWork b) := by
  unfold grindProofOfWork
  split_ifs with h
  · trivial
  · exact ⟨hb h, trivial, trivial⟩

/-- A commitment. -/
theorem commitP (hc : c) (ht w : ℕ) :
    Moves g c (fun _ ↦ True) (fun _ ↦ False) (readCommitment ht w) := ⟨hc, trivial⟩

/-- An opening. -/
theorem queryP (i : ℕ) (ps : List ℕ) :
    Moves g c (fun _ ↦ True) (fun _ ↦ False) (queryOpenings i ps) := fun _ ↦ trivial

/-- A conditional. -/
theorem ite {q : Prop} [Decidable q] {p p' : VerifierProgram α} (hp : q → Moves g c Q G p)
    (hp' : ¬ q → Moves g c Q G p') : Moves g c Q G (if q then p else p') := by
  split
  · exact hp ‹_›
  · exact hp' ‹_›

/-! ## Challenges first -/

theorem startsSample_sampleChallenge {R : β → Prop} (k : E → VerifierProgram β) :
    (sampleChallenge >>= k).StartsSample R := trivial

theorem startsSample_sampleChallenges {R : β → Prop} {n : ℕ} (hn : n ≠ 0)
    (k : List E → VerifierProgram β) : (sampleChallenges n >>= k).StartsSample R := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  trivial

/-! ## Along histories -/

/-- The program after a history of an allowed program is allowed. -/
theorem after {p : VerifierProgram α} (hp : Moves g c Q G p) :
    ∀ {l : List Ev} {q : VerifierProgram α}, p.after l = some q → Moves g c Q G q := by
  induction p with
  | ret a | fail =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp [VerifierProgram.after] at h
  | read k ih | sample k ih | query i ps k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
      exact ih _ (hp _) h
  | grind b k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
      split at h
      · exact ih hp.2.2 h
      · cases h
  | commit ht w k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [VerifierProgram.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
      split at h
      · exact ih hp.2 h
      · cases h

/-- **A challenge follows every proof of work** of a program that never returns right after one. -/
theorem grindThenSample {P : VerifierProgram α} (hP : Moves g c Q (fun _ ↦ False) P) :
    GrindThenSample P := by
  intro l b k h
  have hs := (hP.after h).2.1
  cases k with
  | sample k' => exact ⟨k', rfl⟩
  | ret a => exact hs.elim
  | _ => exact hs.elim

/-- The commitments of a history extended by one event. -/
private theorem commits_snoc (l : List Ev) (e : Ev) :
    commits (l ++ [e]) = commits l ++ commits [e] := by
  induction l with
  | nil => rfl
  | cons e' l ih => cases e' <;> simp [commits, ih]

/-- A program without commitments commits nothing along a run. -/
theorem reach_commits {p : VerifierProgram α} (hp : Moves g False Q G p) {h₀ l : List Ev}
    (hl : p.Reach h₀ l) : commits l = [] := by
  induction hl with
  | nil => rfl
  | read x _ _ ih => simp [commits_snoc, ih, commits]
  | sample c _ _ ih => simp [commits_snoc, ih, commits]
  | grind _ _ ih => simp [commits_snoc, ih, commits]
  | commit word _ ha _ _ => exact ((hp.after ha).1).elim
  | query _ _ _ ih => simp [commits_snoc, ih, commits]

/-- Along a reachable history, the last proof of work's bits are at most `B`. -/
theorem grindBits_le {B : ℕ} {P : VerifierProgram α} (hP : Moves (· ≤ B) c Q G P) {h : List Ev}
    (hh : P.Reachable h) : grindBits h ≤ B := by
  cases hh with
  | nil => simp [grindBits]
  | read x _ _ => simp [grindBits]
  | sample x _ _ => simp [grindBits]
  | grind _ ha => simpa [grindBits] using (hP.after ha).1
  | commit word _ _ _ => simp [grindBits]
  | query _ _ _ => simp [grindBits]

end Moves

/-! ## The grinds' widths -/

/-- A grind of `grindingBits N` bits has at most `64` bits for `N ≤ 2^67`. -/
theorem grindingBits_le_sixtyFour {N : ℕ} (hN : N ≤ 2 ^ 67) : grindingBits N ≤ 64 := by
  unfold grindingBits
  split_ifs with h
  · omega
  · have : Nat.log2 (N - 1) < 67 := (Nat.log2_lt (by omega)).2 (by omega)
    simp only [securityBits]
    omega

/-- The proofs of work the leanVM verifier checks: at most `64` bits. -/
abbrev G64 : ℕ → Prop := (· ≤ 64)

/-- A grind of `grindingBits N` bits has at most `B` bits for `N ≤ 2^(B+3)`. -/
theorem grindingBits_le_of {N B : ℕ} (hN : N ≤ 2 ^ (B + 3)) : grindingBits N ≤ B := by
  unfold grindingBits
  split_ifs with h
  · omega
  · have : Nat.log2 (N - 1) < B + 3 := (Nat.log2_lt (by omega)).2 (by omega)
    simp only [securityBits]
    omega

theorem le_two_pow_of_le {n B : ℕ} (hB : 17 ≤ B) (hn : n ≤ 2 ^ 20) : n ≤ 2 ^ (B + 3) :=
  hn.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem le_of_le_seventeen {b B : ℕ} (hB : 17 ≤ B) (hb : b ≤ 17) : b ≤ B := hb.trans hB

/-- The bus's grind has at most `B` bits at `layout`, once its depth is checked. -/
def BusGrindLE (B : ℕ) (layout : Layout) : Prop :=
  (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth < 64 →
    busGrindingBits (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth ≤ B

theorem busGrindLE_sixtyFour (layout : Layout) : BusGrindLE 64 layout := fun _ ↦
  grindingBits_le_sixtyFour (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The phases that commit nothing, as moves of the whole program. -/
theorem Moves.liftTrue {g : ℕ → Prop} {p : VerifierProgram α} {Q : α → Prop}
    (h : Moves g False Q (fun _ ↦ False) p) : Moves g True Q (fun _ ↦ False) p :=
  h.mono (fun _ h ↦ h) False.elim (fun _ h ↦ h) (fun _ h ↦ h)

section Phases

/- The phases' programs are large closed terms; `Moves` is kept folded so that elaborating a
rule's conclusion does not unfold the program it is about. -/
attribute [local irreducible] Moves

/-!
## Every grind at most `B` bits, `17 ≤ B`

Every grind but the bus's has at most `17` bits; the bus's is bounded at the layout
(`BusGrindLE`). The forms at `G64` below are the instances at `B = 64`.
-/

variable {B : ℕ}

/-! ### Sumcheck and the bus -/

theorem moves_sumcheckRoundPoly_le {count : ℕ} (hc : count ≤ 2 ^ (B + 3)) (claim : E)
    (eq : Option E) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ True) (sumcheckRoundPoly count claim eq) := by
  have h1 : 1 ≤ 2 ^ (B + 3) := Nat.one_le_two_pow
  cases eq with
  | none =>
    exact Moves.seq' Moves.readE fun _ _ ↦ Moves.seq' (Moves.readN _) fun _ _ ↦
      Moves.seq (Moves.grindP fun _ ↦ grindingBits_le_of (by omega)) (fun _ _ ↦
        Moves.pure trivial) fun _ _ _ ↦ trivial
  | some r =>
    exact Moves.seq' (Moves.readN _) fun _ _ ↦
      Moves.seq (Moves.grindP fun _ ↦ grindingBits_le_of (by omega)) (fun _ _ ↦
        Moves.pure trivial) fun _ _ _ ↦ trivial

theorem moves_sumcheck_le {count : ℕ} (hc : count ≤ 2 ^ (B + 3)) :
    ∀ (claim : E) (eqs : List (Option E)),
      Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (sumcheck claim count eqs)
  | _, [] => Moves.pure trivial
  | claim, e :: es =>
    Moves.seq (moves_sumcheckRoundPoly_le hc claim e)
      (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦
        Moves.seq' (moves_sumcheck_le hc _ es) fun r _ ↦ by
          obtain ⟨point, final⟩ := r
          exact Moves.pure trivial)
      fun _ _ _ ↦ Moves.startsSample_sampleChallenge _

theorem moves_gkrStep_le (hB : 17 ≤ B) {step : ℕ} (h1 : 1 ≤ step) (h2 : step ≤ 2) (last : Bool)
    (s : GkrState) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (gkrStep step last s) := by
  have hpow : 2 ^ step + 1 ≤ 2 ^ (B + 3) := by
    have : 2 ^ step ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
    exact le_two_pow_of_le hB (by omega)
  refine Moves.seq (Moves.grindP fun _ ↦ grindingBits_le_of (le_two_pow_of_le hB (by decide)))
    (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦
      Moves.seq' (moves_sumcheck_le hpow _ _) fun r _ ↦ ?_)
    fun _ _ _ ↦ Moves.startsSample_sampleChallenge _
  obtain ⟨x, claim⟩ := r
  refine Moves.seq' (Moves.readN _) fun _ _ ↦ Moves.seq' (Moves.readN _) fun _ _ ↦
    Moves.seq' (Moves.readN _) fun _ _ ↦ Moves.seq' (Moves.require _) fun _ _ ↦
      Moves.seq (Moves.grindP fun _ ↦ grindingBits_le_of (le_two_pow_of_le hB ?_))
        (fun _ _ ↦ Moves.seq' (Moves.sampleN _) fun _ _ ↦ Moves.pure trivial)
        fun _ _ _ ↦ Moves.startsSample_sampleChallenges (by omega) _
  split <;> omega

theorem moves_gkrLayers_le (hB : 17 ≤ B) : ∀ (n : ℕ) (s : GkrState),
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (gkrLayers n s)
  | 0, _ => Moves.pure trivial
  | 1, s => Moves.seq' (moves_gkrStep_le hB le_rfl (by norm_num) true s) fun t _ ↦
      moves_gkrLayers_le hB 0 t
  | n + 2, s => by
    simp only [gkrLayers]
    split
    · exact Moves.seq' (moves_gkrStep_le hB le_rfl (by norm_num) false s) fun t _ ↦
        moves_gkrLayers_le hB (n + 1) t
    · exact Moves.seq' (moves_gkrStep_le hB (by norm_num) le_rfl (n = 0) s) fun t _ ↦
        moves_gkrLayers_le hB n t

theorem moves_verifyGkrGrandProducts_le (hB : 17 ≤ B) (depth : ℕ) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (verifyGkrGrandProducts depth) :=
  Moves.seq' Moves.readE fun _ _ ↦ Moves.seq' Moves.readE fun _ _ ↦
    Moves.seq' (moves_gkrLayers_le hB depth _) fun _ _ ↦ Moves.pure trivial

theorem moves_bytecodeShare_le (hB : 17 ≤ B) (weights bytecodeLow : List E) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (bytecodeShare weights bytecodeLow) := by
  refine Moves.seq' Moves.readE fun _ _ ↦
    Moves.seq' (moves_sumcheck_le (le_two_pow_of_le hB (by norm_num)) _ _) fun r _ ↦ ?_
  obtain ⟨slotPoint, claim⟩ := r
  exact Moves.seq' Moves.readE fun _ _ ↦ Moves.seq' (Moves.require _) fun _ _ ↦ Moves.pure trivial

/-- **The bus**, for a check of the fixed polynomial's value that makes no prover move, at a
layout whose bus grind has at most `B` bits. -/
theorem moves_verifyBusBalance_le (hB : 17 ≤ B)
    {bytecodeValue : List K → List E → E → VerifierProgram Unit}
    (hb : ∀ w p v, Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (bytecodeValue w p v))
    (layout : Layout) (hl : BusGrindLE B layout) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (verifyBusBalance bytecodeValue layout) := by
  refine Moves.seq' (Moves.require _) fun _ hd ↦
    Moves.seq (Moves.grindP fun _ ↦ hl hd)
      (fun _ _ ↦ Moves.seq' (Moves.sampleN _) fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦
        Moves.seq' (moves_verifyGkrGrandProducts_le hB _) fun r _ ↦ ?_)
      fun _ _ _ ↦ Moves.startsSample_sampleChallenges (by simp [busBits]) _
  obtain ⟨countRoot, point, treeValues⟩ := r
  refine Moves.seq' (Moves.require _) fun _ _ ↦ Moves.seq' (Moves.readN 2) fun _ _ ↦
    Moves.seq' Moves.readE fun _ _ ↦ Moves.seq' Moves.readE fun _ _ ↦
      Moves.seq' (moves_bytecodeShare_le hB _ _) fun r _ ↦ ?_
  obtain ⟨share, bytecodePoint, value⟩ := r
  exact Moves.seq' (hb _ _ _) fun _ _ ↦ Moves.pure trivial

/-! ### The sizes, the table sumcheck and the public input -/

/-- **The announced sizes**: reads; the stack has between `minLogStack` and `maxLogStack`
variables, and the layout is the one `buildLayout` gives at the sizes read. -/
theorem moves_readSizes_le {g : ℕ → Prop} (bytecode : List K) :
    Moves g False (fun a ↦ Whir.minLogStack ≤ a.1.stackLog ∧ a.1.stackLog ≤ Whir.maxLogStack ∧
      ∃ logMemory tableRows, buildLayout bytecode logMemory tableRows = some a.1) (fun _ ↦ False)
      (readAnnouncedSizes bytecode) :=
  Moves.seq' (Moves.readN _) fun _ _ ↦ Moves.seq' (Moves.require _) fun _ _ ↦
    Moves.seq' (Moves.require _) fun _ _ ↦ Moves.seq' (Moves.liftOption _) fun _ hl ↦
      Moves.seq' (Moves.require _) fun _ h ↦ Moves.pure ⟨h.1, h.2, _, _, hl⟩

theorem moves_tableTerms_le (constraintPowers formPowers point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E),
      Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False)
        (tableTerms constraintPowers formPowers point rows cursor final)
  | [], _, _ => Moves.pure trivial
  | (table, height, forms, weight) :: rest, cursor, final =>
    Moves.seq' (Moves.readN _) fun _ _ ↦
      Moves.seq' (moves_tableTerms_le constraintPowers formPowers point rest _ _) fun r _ ↦ by
        obtain ⟨final, rows⟩ := r
        exact Moves.pure trivial

theorem moves_tableSumcheck_le (hB : 17 ≤ B) (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False)
      (tableSumcheck heights busForms constraintPowers formPowers equalityPoint target) := by
  refine Moves.seq' (moves_sumcheck_le (le_two_pow_of_le hB (by norm_num)) _ _) fun r _ ↦ ?_
  obtain ⟨challenges, claim⟩ := r
  refine Moves.seq' (moves_tableTerms_le _ _ _ _ _ _) fun r _ ↦ ?_
  obtain ⟨final, evaluations⟩ := r
  exact Moves.seq' (Moves.require _) fun _ _ ↦ Moves.pure trivial

theorem moves_tablePhase_le (hB : 17 ≤ B) (layout : Layout) (bus : BusResult) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (tablePhase layout bus) :=
  Moves.seq (Moves.grindP fun _ ↦ grindingBits_le_of (le_two_pow_of_le hB (by decide)))
    (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦ moves_tableSumcheck_le hB _ _ _ _ _ _)
    fun _ _ _ ↦ Moves.startsSample_sampleChallenge _

theorem moves_publicInputPhase_le (layout : Layout) (publicInput : Digest) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (publicInputPhase layout publicInput) :=
  Moves.seq' Moves.sampleE fun _ _ ↦ Moves.pure trivial

/-! ### The Keccak reduction and ring switching -/

theorem moves_keccakPackRounds_le (hB : 17 ≤ B) : ∀ (rs : List E) (value scale : E),
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (keccakPackRounds rs value scale)
  | [], _, _ => Moves.pure trivial
  | r :: rs, value, scale =>
    Moves.seq (moves_sumcheckRoundPoly_le (le_two_pow_of_le hB (by norm_num)) _ _)
      (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦
        Moves.seq' (moves_keccakPackRounds_le hB rs _ _) fun r _ ↦ by
          obtain ⟨value, scale, point⟩ := r
          exact Moves.pure trivial)
      fun _ _ _ ↦ Moves.startsSample_sampleChallenge _

theorem moves_verifyKeccakLayer_le (hB : 17 ≤ B) (logSteps step : ℕ) (claim : KeccakClaim) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (verifyKeccakLayer logSteps step claim) := by
  refine Moves.seq' (Moves.readN _) fun _ _ ↦ Moves.seq' (Moves.require _) fun _ _ ↦
    Moves.seq (Moves.grindP fun _ ↦ grindingBits_le_of (le_two_pow_of_le hB (by decide)))
      (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦
        Moves.seq' (moves_keccakPackRounds_le hB _ _ _) fun r _ ↦ ?_)
      fun _ _ _ ↦ Moves.startsSample_sampleChallenge _
  obtain ⟨value, scale, point⟩ := r
  refine Moves.seq' (moves_sumcheck_le (le_two_pow_of_le hB (by norm_num)) _ _) fun r _ ↦ ?_
  obtain ⟨localPoint, value⟩ := r
  exact Moves.seq' (Moves.readN _) fun _ _ ↦ Moves.seq' (Moves.require _) fun _ _ ↦
    Moves.seq (Moves.grindP fun _ ↦ grindingBits_le_of (le_two_pow_of_le hB (by decide)))
      (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦ Moves.pure trivial)
      fun _ _ _ ↦ Moves.startsSample_sampleChallenge _

theorem moves_keccakLayers_le (hB : 17 ≤ B) (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : KeccakClaim),
      Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (keccakLayers logSteps steps claim)
  | [], _ => Moves.pure trivial
  | step :: steps, claim =>
    Moves.seq' (moves_verifyKeccakLayer_le hB logSteps step claim) fun c _ ↦
      moves_keccakLayers_le hB logSteps steps c

theorem moves_keccakOpen_le (hB : 17 ≤ B) (logSteps : ℕ) (claim : KeccakClaim)
    (first count : ℕ) (value : E) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False)
      (keccakOpen logSteps claim first count value) := by
  refine Moves.seq' (moves_sumcheck_le (le_two_pow_of_le hB (by norm_num)) _ _) fun r _ ↦ ?_
  obtain ⟨slot, value⟩ := r
  exact Moves.pure trivial

theorem moves_verifyKeccak_le (hB : 17 ≤ B) (logSteps : ℕ) (inst output : List E) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (verifyKeccak logSteps inst output) := by
  have hopen : ∀ (claim : KeccakClaim) (first count : ℕ) (value : E) (f : List E × List E × E →
      VerifierProgram (List ColumnClaim × List E × List E)),
      (∀ r, Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (f r)) →
      Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False)
        (keccakOpen logSteps claim first count value >>= f) :=
    fun _ _ _ _ _ hf ↦ Moves.seq' (moves_keccakOpen_le hB _ _ _ _ _) fun r _ ↦ hf r
  refine Moves.seq (Moves.grindP fun _ ↦ grindingBits_le_of (le_two_pow_of_le hB (by decide)))
    (fun _ _ ↦ ?_) fun _ _ _ ↦ Moves.startsSample_sampleChallenges (by decide) _
  refine Moves.seq' (Moves.sampleN _) fun segment _ ↦ Moves.seq' (Moves.sampleN _) fun lanePoint _ ↦ ?_
  -- `keccakSegments = 2`: the committed outputs are read.
  refine Moves.seq' Moves.readE fun committed _ ↦ ?_
  refine Moves.seq' (moves_keccakLayers_le hB _ _ _) fun claim _ ↦ ?_
  simp only [show (1 < keccakSegments) ↔ True from iff_true_intro (by decide), ↓reduceIte]
  refine hopen _ _ _ _ _ fun r ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  refine Moves.seq' Moves.readE fun _ _ ↦ Moves.seq' (Moves.require _) fun _ _ ↦
    Moves.seq' (Moves.pure (Q := fun _ ↦ True) trivial) fun outputs _ ↦ ?_
  refine Moves.seq' (moves_sumcheck_le (le_two_pow_of_le hB (by norm_num)) _ _) fun r _ ↦ ?_
  obtain ⟨low, value⟩ := r
  refine hopen _ _ _ _ _ fun r ↦ ?_
  obtain ⟨slot, weights, value⟩ := r
  exact Moves.seq' (Moves.readN _) fun _ _ ↦ Moves.seq' (Moves.require _) fun _ _ ↦
    Moves.pure trivial

theorem moves_keccakPhase_le (hB : 17 ≤ B) (layout : Layout)
    (evaluations : List (List E × List E)) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (keccakPhase layout evaluations) :=
  moves_verifyKeccak_le hB _ _ _

theorem moves_ringSwitch_le (hB : 17 ≤ B) (point s : List E) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (ringSwitch point s) :=
  Moves.seq (Moves.grindP fun _ ↦ le_of_le_seventeen hB (by decide))
    (fun _ _ ↦ Moves.seq' (Moves.sampleN _) fun _ _ ↦ Moves.pure trivial)
    fun _ _ _ ↦ Moves.startsSample_sampleChallenges (by decide) _

/-! ### The WHIR opening -/

theorem moves_foldRound_le (hB : 17 ≤ B) (s : WhirState) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (foldRound s) :=
  Moves.seq (Moves.grindP fun _ ↦ le_of_le_seventeen hB (by decide))
    (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦ Moves.seq' Moves.readE fun _ _ ↦
      Moves.seq' Moves.readE fun _ _ ↦ Moves.seq' Moves.readE fun _ _ ↦
        Moves.seq' Moves.readE fun _ _ ↦ Moves.seq' Moves.readE fun _ _ ↦
          Moves.seq (Moves.grindP fun _ ↦ le_of_le_seventeen hB (by decide))
            (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦
              Moves.seq' Moves.sampleE fun _ _ ↦ Moves.pure trivial)
            fun _ _ _ ↦ Moves.startsSample_sampleChallenge _)
    fun _ _ _ ↦ Moves.startsSample_sampleChallenge _

theorem moves_foldRounds_le (hB : 17 ≤ B) : ∀ (n : ℕ) (s : WhirState),
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (foldRounds n s)
  | 0, _ => Moves.pure trivial
  | n + 1, s => Moves.seq' (moves_foldRound_le hB s) fun r _ ↦ by
      obtain ⟨s, round⟩ := r
      exact Moves.seq' (moves_foldRounds_le hB n s) fun r _ ↦ by
        obtain ⟨s, rounds⟩ := r
        exact Moves.pure trivial

theorem moves_sampleOodPoints_le (mu : ℕ) : ∀ (count : ℕ),
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (sampleOodPoints mu count)
  | 0 => Moves.pure trivial
  | count + 1 => Moves.seq' (Moves.sampleN _) fun _ _ ↦
      Moves.seq' (moves_sampleOodPoints_le mu count) fun _ _ ↦ Moves.pure trivial

theorem moves_sampleQueriesAux_le (depth : ℕ) : ∀ (fuel remaining : ℕ),
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (sampleQueriesAux depth fuel remaining)
  | 0, _ => Moves.pure trivial
  | fuel + 1, _ =>
    Moves.ite (fun _ ↦ Moves.pure trivial) fun _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦
      Moves.seq' (moves_sampleQueriesAux_le depth fuel _) fun _ _ ↦ Moves.pure trivial

/-- The query positions of a level that queries start with a challenge. -/
theorem startsSample_sampleQueries {R : β → Prop} {depth count : ℕ} (hc : count ≠ 0)
    (k : List ℕ → VerifierProgram β) : (sampleQueries depth count >>= k).StartsSample R := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  unfold sampleQueries sampleQueriesAux
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  trivial

theorem moves_whirLevels_le (hB : 17 ≤ B) (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level), (∀ l ∈ levels, l.queries ≠ 0) → ∀ (s : WhirState),
      Moves (· ≤ B) True (fun _ ↦ True) (fun _ ↦ False)
        (whirLevels logN laneFolds evaluateBasis index levels s)
  | _, [], _, _ => Moves.fail
  | index, level :: rest, hq, s => by
    have hq0 : level.queries ≠ 0 := hq level List.mem_cons_self
    refine Moves.seq' (Moves.liftTrue (moves_foldRounds_le hB level.fold s)) fun r _ ↦ ?_
    obtain ⟨s', rounds⟩ := r
    cases rest with
    | nil =>
      exact Moves.seq' (Moves.readN _) fun _ _ ↦
        Moves.seq (Moves.grindP fun _ ↦ le_of_le_seventeen hB (by decide))
          (fun _ _ ↦ Moves.seq' (Moves.liftTrue (moves_sampleQueriesAux_le _ _ _)) fun _ _ ↦
            Moves.seq' (Moves.queryP _ _) fun _ _ ↦ Moves.seq' (Moves.require _) fun _ _ ↦
              Moves.seq' (Moves.liftTrue (moves_sumcheck_le (le_two_pow_of_le hB (by norm_num))
                _ _)) fun r _ ↦ by
                obtain ⟨tail, claim⟩ := r
                exact (Moves.require _).mono (fun _ h ↦ h) id (fun _ _ ↦ trivial) (fun _ h ↦ h))
          fun _ _ _ ↦ startsSample_sampleQueries hq0 _
    | cons next rest' =>
      exact Moves.seq' (Moves.commitP trivial _ _) fun _ _ ↦
        Moves.seq' (Moves.readN _) fun _ _ ↦
          Moves.seq' (Moves.liftTrue (moves_sampleOodPoints_le _ _)) fun _ _ ↦
          Moves.seq' (Moves.readN _) fun _ _ ↦
            Moves.seq (Moves.grindP fun _ ↦ le_of_le_seventeen hB (by decide))
              (fun _ _ ↦ Moves.seq' (Moves.liftTrue (moves_sampleQueriesAux_le _ _ _)) fun _ _ ↦
                Moves.seq (Moves.grindP fun _ ↦ le_of_le_seventeen hB (by decide))
                  (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦
                    Moves.seq' (Moves.queryP _ _) fun _ _ ↦
                      moves_whirLevels_le hB logN laneFolds evaluateBasis (index + 1)
                        (next :: rest')
                        (fun l hl ↦ hq l (List.mem_cons_of_mem _ hl)) _)
                  fun _ _ _ ↦ Moves.startsSample_sampleChallenge _)
              fun _ _ _ ↦ startsSample_sampleQueries hq0 _

/-- Every count of the query table is positive. -/
theorem queryTable_pos : ∀ row ∈ Whir.queryTable, ∀ r ∈ row, ∀ q ∈ r, q ≠ 0 := by
  decide

private theorem getD_mem_or {γ : Type} (l : List (List γ)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[i]? with _ | x
  · exact .inr rfl
  · exact .inl (List.mem_of_getElem? h)

/-- Every count the table gives a shape is positive. -/
theorem queryTable_getD_pos (i j : ℕ) : ∀ q ∈ (Whir.queryTable.getD i []).getD j [], q ≠ 0 := by
  intro q hq
  rcases getD_mem_or Whir.queryTable i with hrow | hrow
  · rcases getD_mem_or (Whir.queryTable.getD i []) j with hr | hr
    · exact queryTable_pos _ hrow _ hr q hq
    · rw [hr] at hq; simp at hq
  · rw [hrow] at hq; simp at hq

/-- **Every level of a deployed ladder queries.** -/
theorem ladder_queries_pos {μ R : ℕ} {config : List Whir.Level} (h : Whir.ladder μ R = some config) :
    ∀ l ∈ config, l.queries ≠ 0 := by
  unfold Whir.ladder at h
  dsimp only at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  subst h
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  simp only [List.getElem_zipWith]
  simp only [List.length_zipWith] at hi
  exact queryTable_getD_pos _ _ _ (List.getElem_mem (by omega))

theorem moves_verifyWhir_le (hB : 17 ≤ B) (logN logInvRate : ℕ) (target : E)
    (evaluateBasis : List E → E) :
    Moves (· ≤ B) True (fun _ ↦ True) (fun _ ↦ False)
      (verifyWhir logN logInvRate target evaluateBasis) :=
  Moves.seq' (Moves.liftOption _) fun _ h ↦
    moves_whirLevels_le hB _ _ _ _ _ (ladder_queries_pos h) _

theorem moves_commitStack_le (logN logInvRate : ℕ) :
    Moves (· ≤ B) True (fun _ ↦ True) (fun _ ↦ False) (commitStack logN logInvRate) := by
  refine Moves.seq' ((Moves.liftOption _).mono (fun _ h ↦ h) False.elim (fun _ _ ↦ trivial) (fun _ h ↦ h))
    fun config _ ↦ ?_
  cases config with
  | nil => exact Moves.fail
  | cons level rest => exact Moves.commitP trivial _ _

theorem moves_readOod_le (hB : 17 ≤ B) {stackLog : ℕ} (h : stackLog ≠ 0) :
    Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (readOod stackLog) :=
  Moves.seq (Moves.grindP fun _ ↦ le_of_le_seventeen hB (by decide))
    (fun _ _ ↦ Moves.seq' (Moves.sampleN _) fun _ _ ↦ Moves.seq' Moves.readE fun _ _ ↦
      Moves.pure trivial)
    fun _ _ _ ↦ Moves.startsSample_sampleChallenges h _

theorem moves_verifyStackedOpening_le (hB : 17 ≤ B) (stackLog logInvRate : ℕ)
    (claims : List StackClaim) :
    Moves (· ≤ B) True (fun _ ↦ True) (fun _ ↦ False)
      (verifyStackedOpening stackLog logInvRate claims) :=
  Moves.seq' ((Moves.require _).mono (fun _ h ↦ h) False.elim (fun _ _ ↦ trivial) (fun _ h ↦ h)) fun _ _ ↦
    Moves.seq' Moves.sampleE fun _ _ ↦ moves_verifyWhir_le hB _ _ _ _

/-! ### The whole program -/

/-- **`verify_execution`**, for a check of the fixed polynomial's value that makes no prover
move, where every layout the sizes can build has its bus grind at most `B` bits. -/
theorem moves_verifyExecution_le (hB : 17 ≤ B)
    {bytecodeValue : List K → List E → E → VerifierProgram Unit}
    (hb : ∀ w p v, Moves (· ≤ B) False (fun _ ↦ True) (fun _ ↦ False) (bytecodeValue w p v))
    (bytecode : List K) (publicInput : Digest)
    (hl : ∀ logMemory tableRows layout, buildLayout bytecode logMemory tableRows = some layout →
      layout.stackLog ≤ Whir.maxLogStack → BusGrindLE B layout) :
    Moves (· ≤ B) True (fun _ ↦ True) (fun _ ↦ False)
      (verifyExecution bytecodeValue bytecode publicInput) := by
  refine Moves.seq' (Moves.liftTrue (moves_readSizes_le bytecode)) fun p hp ↦ ?_
  obtain ⟨layout, logInverseRate⟩ := p
  obtain ⟨hmin, hmax, logMemory, tableRows, hbuild⟩ := hp
  have h0 : layout.stackLog ≠ 0 := by
    have : Whir.minLogStack ≤ layout.stackLog := hmin
    simp only [Whir.minLogStack] at this
    omega
  refine Moves.seq' (moves_commitStack_le _ _) fun _ _ ↦
    Moves.seq' (Moves.liftTrue (moves_readOod_le hB h0)) fun _ _ ↦
      Moves.seq' (Moves.liftTrue (moves_verifyBusBalance_le hB hb layout
        (hl _ _ _ hbuild hmax))) fun bus _ ↦
        Moves.seq' (Moves.liftTrue (moves_tablePhase_le hB layout bus)) fun _ _ ↦
          Moves.seq' (Moves.liftTrue (moves_publicInputPhase_le layout publicInput)) fun _ _ ↦
            Moves.seq' (Moves.liftTrue (moves_keccakPhase_le hB _ _)) fun r _ ↦ ?_
  obtain ⟨outputs, keccakPoint, keccakSlices⟩ := r
  refine Moves.seq' (Moves.liftTrue (moves_ringSwitch_le hB keccakPoint keccakSlices)) fun r _ ↦ ?_
  obtain ⟨ringTarget, ringWeight⟩ := r
  exact moves_verifyStackedOpening_le hB _ _ _

theorem moves_computedBytecodeValue_le {g : ℕ → Prop} (w : List K) (p : List E) (v : E) :
    Moves g False (fun _ ↦ True) (fun _ ↦ False) (computedBytecodeValue w p v) :=
  (Moves.require _).mono (fun _ h ↦ h) id (fun _ _ ↦ trivial) (fun _ h ↦ h)

theorem moves_claimedBytecodeValue_le {g : ℕ → Prop} (claim : BytecodeClaim) (w : List K)
    (p : List E) (v : E) :
    Moves g False (fun _ ↦ True) (fun _ ↦ False) (claimedBytecodeValue claim w p v) :=
  (Moves.require _).mono (fun _ h ↦ h) id (fun _ _ ↦ trivial) (fun _ h ↦ h)

/-- **The leanVM verifier program's moves**, every grind at most `B` bits where every layout the
sizes can build has its bus grind at most `B` bits. -/
theorem moves_leanVmProgram_le (hB : 17 ≤ B) (bytecode : List K) (publicInput : Digest)
    (hl : ∀ logMemory tableRows layout, buildLayout bytecode logMemory tableRows = some layout →
      layout.stackLog ≤ Whir.maxLogStack → BusGrindLE B layout) :
    Moves (· ≤ B) True (fun _ ↦ True) (fun _ ↦ False)
      (leanVmVerifierProgram bytecode publicInput) :=
  Moves.seq' (moves_verifyExecution_le hB moves_computedBytecodeValue_le bytecode publicInput hl)
    fun _ _ ↦ Moves.pure trivial

/-! ## At `64` bits -/

theorem moves_sumcheckRoundPoly {count : ℕ} (hc : count ≤ 2 ^ 67) (claim : E) (eq : Option E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ True) (sumcheckRoundPoly count claim eq) :=
  moves_sumcheckRoundPoly_le hc claim eq

theorem moves_sumcheck {count : ℕ} (hc : count ≤ 2 ^ 67) (claim : E) (eqs : List (Option E)) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (sumcheck claim count eqs) :=
  moves_sumcheck_le hc claim eqs

theorem moves_gkrStep {step : ℕ} (h1 : 1 ≤ step) (h2 : step ≤ 2) (last : Bool) (s : GkrState) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (gkrStep step last s) :=
  moves_gkrStep_le (by norm_num) h1 h2 last s

theorem moves_gkrLayers (n : ℕ) (s : GkrState) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (gkrLayers n s) :=
  moves_gkrLayers_le (by norm_num) n s

theorem moves_verifyGkrGrandProducts (depth : ℕ) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (verifyGkrGrandProducts depth) :=
  moves_verifyGkrGrandProducts_le (by norm_num) depth

theorem moves_bytecodeShare (weights bytecodeLow : List E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (bytecodeShare weights bytecodeLow) :=
  moves_bytecodeShare_le (by norm_num) weights bytecodeLow

/-- **The bus**, for a check of the fixed polynomial's value that makes no prover move. -/
theorem moves_verifyBusBalance {bytecodeValue : List K → List E → E → VerifierProgram Unit}
    (hb : ∀ w p v, Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (bytecodeValue w p v))
    (layout : Layout) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (verifyBusBalance bytecodeValue layout) :=
  moves_verifyBusBalance_le (by norm_num) hb layout (busGrindLE_sixtyFour layout)

/-- **The announced sizes**: reads; the stack has at least `minLogStack` variables. -/
theorem moves_readSizes (bytecode : List K) :
    Moves G64 False (fun a ↦ Whir.minLogStack ≤ a.1.stackLog) (fun _ ↦ False)
      (readAnnouncedSizes bytecode) :=
  (moves_readSizes_le bytecode).mono (fun _ h ↦ h) id (fun _ h ↦ h.1) (fun _ h ↦ h)

theorem moves_tableTerms (constraintPowers formPowers point : List E)
    (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False)
      (tableTerms constraintPowers formPowers point rows cursor final) :=
  moves_tableTerms_le constraintPowers formPowers point rows cursor final

theorem moves_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False)
      (tableSumcheck heights busForms constraintPowers formPowers equalityPoint target) :=
  moves_tableSumcheck_le (by norm_num) heights busForms constraintPowers formPowers equalityPoint
    target

/-- **The table phase**: its grind followed by `ξ`. -/
theorem moves_tablePhase (layout : Layout) (bus : BusResult) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (tablePhase layout bus) :=
  moves_tablePhase_le (by norm_num) layout bus

theorem moves_publicInputPhase (layout : Layout) (publicInput : Digest) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (publicInputPhase layout publicInput) :=
  moves_publicInputPhase_le layout publicInput

theorem moves_keccakPackRounds (rs : List E) (value scale : E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (keccakPackRounds rs value scale) :=
  moves_keccakPackRounds_le (by norm_num) rs value scale

theorem moves_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (verifyKeccakLayer logSteps step claim) :=
  moves_verifyKeccakLayer_le (by norm_num) logSteps step claim

theorem moves_keccakLayers (logSteps : ℕ) (steps : List ℕ) (claim : KeccakClaim) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (keccakLayers logSteps steps claim) :=
  moves_keccakLayers_le (by norm_num) logSteps steps claim

theorem moves_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False)
      (keccakOpen logSteps claim first count value) :=
  moves_keccakOpen_le (by norm_num) logSteps claim first count value

/-- **The Keccak reduction**: its first grind followed by the segment. -/
theorem moves_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (verifyKeccak logSteps inst output) :=
  moves_verifyKeccak_le (by norm_num) logSteps inst output

theorem moves_keccakPhase (layout : Layout) (evaluations : List (List E × List E)) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (keccakPhase layout evaluations) :=
  moves_keccakPhase_le (by norm_num) layout evaluations

/-- **Ring switching**: its grind followed by the map's sixteen challenges. -/
theorem moves_ringSwitch (point s : List E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (ringSwitch point s) :=
  moves_ringSwitch_le (by norm_num) point s

/-- The phases that commit nothing, as moves of the whole program. -/
theorem Moves.lift {p : VerifierProgram α} {Q : α → Prop}
    (h : Moves G64 False Q (fun _ ↦ False) p) : Moves G64 True Q (fun _ ↦ False) p :=
  h.liftTrue

theorem moves_foldRound (s : WhirState) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (foldRound s) :=
  moves_foldRound_le (by norm_num) s

theorem moves_foldRounds (n : ℕ) (s : WhirState) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (foldRounds n s) :=
  moves_foldRounds_le (by norm_num) n s

theorem moves_sampleOodPoints (mu count : ℕ) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (sampleOodPoints mu count) :=
  moves_sampleOodPoints_le mu count

theorem moves_sampleQueriesAux (depth fuel remaining : ℕ) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (sampleQueriesAux depth fuel remaining) :=
  moves_sampleQueriesAux_le depth fuel remaining

/-- **The WHIR levels**, every one of which queries. -/
theorem moves_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) (index : ℕ)
    (levels : List Whir.Level) (hq : ∀ l ∈ levels, l.queries ≠ 0) (s : WhirState) :
    Moves G64 True (fun _ ↦ True) (fun _ ↦ False)
      (whirLevels logN laneFolds evaluateBasis index levels s) :=
  moves_whirLevels_le (by norm_num) logN laneFolds evaluateBasis index levels hq s

theorem moves_verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) :
    Moves G64 True (fun _ ↦ True) (fun _ ↦ False)
      (verifyWhir logN logInvRate target evaluateBasis) :=
  moves_verifyWhir_le (by norm_num) logN logInvRate target evaluateBasis

/-- The stack's root: one commitment, no proof of work. -/
theorem moves_commitStack (logN logInvRate : ℕ) :
    Moves G64 True (fun _ ↦ True) (fun _ ↦ False) (commitStack logN logInvRate) :=
  moves_commitStack_le logN logInvRate

/-- **The commitment's OOD sample**: its grind followed by the point. -/
theorem moves_readOod {stackLog : ℕ} (h : stackLog ≠ 0) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (readOod stackLog) :=
  moves_readOod_le (by norm_num) h

theorem moves_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    Moves G64 True (fun _ ↦ True) (fun _ ↦ False)
      (verifyStackedOpening stackLog logInvRate claims) :=
  moves_verifyStackedOpening_le (by norm_num) stackLog logInvRate claims

/-- **`verify_execution`**, for a check of the fixed polynomial's value that makes no prover
move. -/
theorem moves_verifyExecution {bytecodeValue : List K → List E → E → VerifierProgram Unit}
    (hb : ∀ w p v, Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (bytecodeValue w p v))
    (bytecode : List K) (publicInput : Digest) :
    Moves G64 True (fun _ ↦ True) (fun _ ↦ False)
      (verifyExecution bytecodeValue bytecode publicInput) :=
  moves_verifyExecution_le (by norm_num) hb bytecode publicInput
    fun _ _ layout _ _ ↦ busGrindLE_sixtyFour layout

theorem moves_computedBytecodeValue (w : List K) (p : List E) (v : E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (computedBytecodeValue w p v) :=
  moves_computedBytecodeValue_le w p v

theorem moves_claimedBytecodeValue (claim : BytecodeClaim) (w : List K) (p : List E) (v : E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (claimedBytecodeValue claim w p v) :=
  moves_claimedBytecodeValue_le claim w p v

end Phases

/-- **The leanVM verifier program's moves.** -/
theorem moves_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    Moves G64 True (fun _ ↦ True) (fun _ ↦ False) (leanVmVerifierProgram bytecode publicInput) :=
  Moves.seq' (moves_verifyExecution moves_computedBytecodeValue bytecode publicInput) fun _ _ ↦
    Moves.pure trivial

/-- **The deferring verifier program's moves.** -/
theorem moves_deferringProgram (claim : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    Moves G64 True (fun _ ↦ True) (fun _ ↦ False)
      (deferringVerifierProgram claim bytecode publicInput) :=
  Moves.seq' (moves_verifyExecution (moves_claimedBytecodeValue claim) bytecode publicInput)
    fun _ _ ↦ Moves.pure trivial

/-- **A challenge follows every proof of work of the leanVM verifier.** -/
theorem grindThenSample_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    GrindThenSample (leanVmVerifierProgram bytecode publicInput) :=
  (moves_leanVmProgram bytecode publicInput).grindThenSample

/-- **A challenge follows every proof of work of the deferring verifier.** -/
theorem grindThenSample_deferringProgram (claim : BytecodeClaim) (bytecode : List K)
    (publicInput : Digest) : GrindThenSample (deferringVerifierProgram claim bytecode publicInput) :=
  (moves_deferringProgram claim bytecode publicInput).grindThenSample

/-- **Every reachable history of the leanVM verifier ends with a proof of work of at most 64
bits.** -/
theorem grindBits_le_of_reachable (bytecode : List K) (publicInput : Digest) {h : List Ev}
    (hh : (leanVmVerifierProgram bytecode publicInput).Reachable h) : grindBits h ≤ 64 :=
  (moves_leanVmProgram bytecode publicInput).grindBits_le hh

end
end LeanVM.Protocol.EndToEnd.Sound
