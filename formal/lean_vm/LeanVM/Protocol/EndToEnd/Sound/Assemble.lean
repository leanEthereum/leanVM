/-
  LeanVM.Protocol.EndToEnd.Sound.Assemble

  The specification of the whole leanVM verifier program, composed from the
  phase specifications, every verifier message held to `2^-125` after its grind, and the doom
  certificate it gives.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.EndToEnd.Sound.Frame
public import LeanVM.Protocol.EndToEnd.Sound.Moves
public import LeanVM.Protocol.EndToEnd.Sound.Runs
public import LeanVM.Protocol.EndToEnd.Front.CommitDoom
public import LeanVM.Protocol.EndToEnd.Front.RingFidelity
public import LeanVM.Protocol.EndToEnd.Front.RingMultilinear
public import LeanVM.Protocol.EndToEnd.Front.LayoutBridgeB
public import LeanVM.Protocol.Whir.Sound.Sumcheck
public import LeanVM.Protocol.Compile.SpecRules.Cert
public import LeanVM.Protocol.Extraction.Extractor

/-!
# The specification of the leanVM verifier

`veSpec` is a specification of `verifyExecutionClaims ev bytecode publicInput`
(`LeanVM.Protocol.Verifier.Claims`, the claim-list form of `Statement/LeanVmVerifier.lean`'s
`verifyExecution`, equal to it by `verifyExecution_claims`) from no doom, rejecting where it returns
in doom, every group of challenges at most `εmsg = 2^-125` after the grind before it. It composes:

1. the announced sizes (dead): no doom. Unless the announced value is the verifier's layout at
   admissible sizes `s` with an admissible WHIR shape (`Good`), the rest is dead;
2. the stack's root (`commitSpec`), creating `RootDoom`: the commitments have level 0's shape and no
   candidate of the root's word at level 0's threshold satisfies `M3Holds` of the leanISA instance;
3. the commitment's OOD sample (`commitOodSpec`): after its grind, the point separates the
   candidates except with probability `C(L₀, 2)·μ/|E|` (`OpeningIface.ood_row`), and then at most one
   candidate answers `y₀` (`oodCands`);
4. the front phases, the bus, the table sumcheck, the public input and the Keccak reduction
   (`FrontIface.frontSpec`, W3's), on that one candidate (`L₀ = 1`), ending in "it does not meet the
   column claims with true slices";
5. ring switching (`ringSpec`), its sixteen challenges and the opening's `λ` one group under the
   batching grind: `2/|E|` for the candidate and `(J − 1)·L₀/|E|` for `λ`, at most
   `(maxStackedClaims + 1)·L₀/|E|` (`OpeningIface.lambda_row`);
6. the stacked opening (`OpeningIface.stackedSpec`, W2's), from `StackedPreOf`: every member of the
   level-0 list violates one of `ring :: claims ++ [ood]`, the one left by the OOD sample a front
   claim or the ring claim, every other the OOD claim (`exists_violated_of_ood`).

The opening's and the front phases' specifications are taken at the boundary as the structures
`OpeningIface` and `FrontIface`, in the shapes W2 and W3 deliver; the assembly is proved against
them.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Sound (IsMultiaffine)
open scoped ENNReal

@[expose] public section

/-! ## The error arithmetic -/

/-- **A message of error `N/|E|`, `N ≤ 2^(b+3)`, ground by `b` bits, is at most `2^-125`.** -/
theorem discount_le (b N : ℕ) (hN : N ≤ 2 ^ (b + 3)) :
    (2 : ℝ≥0∞)⁻¹ ^ b * ((N : ℝ≥0∞) / Fintype.card E) ≤ εmsg := by
  have hN' : (N : ℝ≥0∞) ≤ 2 ^ (b + 3) := by exact_mod_cast hN
  rw [Protocol.card_E, εmsg, securityBits, Nat.cast_pow, Nat.cast_ofNat]
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ b * 2 ^ b = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  calc (2 : ℝ≥0∞)⁻¹ ^ b * ((N : ℝ≥0∞) / 2 ^ 128)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ b * (2 ^ (b + 3) / 2 ^ 128) := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ b * 2 ^ b * (2 ^ 3 / 2 ^ 128) := by
        rw [pow_add, mul_div_assoc, mul_assoc]
    _ = 2 ^ 3 / 2 ^ 128 := by rw [h2, one_mul]
    _ = (2 : ℝ≥0∞)⁻¹ ^ 125 := by
        rw [show (2 : ℝ≥0∞) ^ 128 = 2 ^ 3 * 2 ^ 125 by rw [← pow_add],
          ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp),
          mul_comm ((2 : ℝ≥0∞) ^ 3)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
          mul_one, ENNReal.inv_pow]

/-- An error `N/|E|` with `N ≤ 2^127` is below `1`. -/
theorem div_card_lt_one {N : ℕ} (hN : N ≤ 2 ^ 127) : (N : ℝ≥0∞) / Fintype.card E < 1 := by
  rw [Protocol.card_E, ENNReal.div_lt_iff (by simp) (by simp), one_mul]
  exact_mod_cast lt_of_le_of_lt hN (by norm_num)

/-! ## The opening's interface -/

/-- The opening's relation, in the shape W2's `Whir.Sound.StackedPre` has: the commitments have level
0's shape, and every candidate of the stack's word violates one of the claims. -/
def StackedPreOf (ShapeOK₀ : ℕ → ℕ → List (ℕ × ℕ × Word) → Prop) (thr₀ : ℕ → ℕ → ℕ)
    (word₀ : List (ℕ × ℕ × Word) → Word) (μ R : ℕ) (claims : List StackClaim)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  ShapeOK₀ μ R cs ∧
    ∀ q ∈ Candidates μ R (thr₀ μ R) (word₀ cs), ∃ c ∈ claims, ¬ StackClaim.Holds μ c q

/-- The batching challenge's error, `(J − 1)·L/|E|`. -/
noncomputable def eBatchOf (J L : ℕ) : ℝ≥0∞ := (((J - 1) * L : ℕ) : ℝ≥0∞) / Fintype.card E

/-- **What the assembly takes of the stacked opening** (W2's `Whir.Sound.stackedSpec` and the
level-0 parameters `Whir.Params.listMax₀`, `ood_row`, `lambda_row`, `card_candidates_le`). -/
structure OpeningIface : Type where
  /-- Level 0's agreement threshold `A₀`. -/
  thr₀ : ℕ → ℕ → ℕ
  /-- Level 0's list bound. -/
  listMax₀ : ℕ → ℕ → ℕ
  /-- The commitments are exactly the stack's, of level 0's shape. -/
  ShapeOK₀ : ℕ → ℕ → List (ℕ × ℕ × Word) → Prop
  /-- The stack's word (`wordOf cs 0`). -/
  word₀ : List (ℕ × ℕ × Word) → Word
  shape_word : ∀ {μ R cs}, ShapeOK₀ μ R cs → firstWordC cs = some (word₀ cs)
  /-- Level 0's threshold is the extractor's Johnson threshold. -/
  thr₀_eq : ∀ {μ R : ℕ}, Whir.Admissible μ R → thr₀ μ R = Extraction.johnsonThreshold μ R
  /-- The stack's root, as `commitStack` reads it, has level 0's shape: what the knowledge
  statement needs for the root's doom to hold on a run. -/
  shape_commitStack : ∀ {μ R : ℕ}, Whir.Admissible μ R → ∀ {e : Ev},
    (∀ ht w W, e = Ev.commit ht w W → WellShaped w W) →
    (commitStack μ R).after [e] = some (.ret ()) → ShapeOK₀ μ R (commits [e])
  candidates_finite : ∀ {μ R : ℕ} (W : Word), Whir.Admissible μ R →
    (Candidates μ R (thr₀ μ R) W).Finite
  card_candidates_le : ∀ {μ R : ℕ} (W : Word), Whir.Admissible μ R →
    (Candidates μ R (thr₀ μ R) W).ncard ≤ listMax₀ μ R
  /-- The OOD row: `C(L₀, 2)·μ ≤ 2^(g + 3)`, `g = Whir.oodGrindingBits` (`discount_le`). -/
  ood_row : ∀ {μ R : ℕ}, Whir.Admissible μ R →
    (listMax₀ μ R).choose 2 * μ ≤ 2 ^ (Whir.oodGrindingBits + 3)
  /-- The batching row with the ring's `2/|E|`: `(maxStackedClaims + 1)·L₀ ≤ 2^(g + 3)`,
  `g = Whir.batchGrindingBits`. -/
  lambda_row : ∀ {μ R : ℕ}, Whir.Admissible μ R →
    (maxStackedClaims + 1) * listMax₀ μ R ≤ 2 ^ (Whir.batchGrindingBits + 3)
  multiaffine_eqEval : ∀ z : List E, IsMultiaffine z.length (eqEval z)
  multiaffine_of_multilinear : ∀ {μ : ℕ} {w : List E → E}, IsMultilinearFn μ w → IsMultiaffine μ w
  /-- **The stacked opening**. -/
  stackedSpec : ∀ {μ R : ℕ}, Whir.Admissible μ R → ∀ (claims : List StackClaim),
    claims.length ≤ maxStackedClaims → (∀ c ∈ claims, IsMultiaffine μ c.1) → ∀ T : ℝ≥0∞,
    Spec (verifyStackedOpening μ R claims)
      (fun h ↦ StackedPreOf ShapeOK₀ thr₀ word₀ μ R claims (commits h)) (fun _ _ ↦ False) εmsg
      (eBatchOf claims.length (listMax₀ μ R)) T

/-! ## Multiaffine claims -/

/-- `zipWith` reads only as much of its right list as its left list is long. -/
theorem zipWith_take_right (f : E → E → E) :
    ∀ (z m : List E), List.zipWith f z m = List.zipWith f z (m.take z.length)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: z, b :: m => by simp [List.zipWith_cons_cons, zipWith_take_right f z m]

/-- `zipWith` reads only as much of its left list as its right list is long. -/
theorem zipWith_take_left (f : E → E → E) :
    ∀ (z m : List E), List.zipWith f z m = List.zipWith f (z.take m.length) m
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: z, b :: m => by simp [List.zipWith_cons_cons, zipWith_take_left f z m]

/-- `eq_eval(z, ·)` is multiaffine in any number of variables. -/
theorem isMultiaffine_eqEval_any (O : OpeningIface) (z : List E) (n : ℕ) :
    IsMultiaffine n (eqEval z) := by
  intro l hl k hk X
  rcases le_or_gt z.length n with hz | hz
  · have hcut : ∀ m : List E, eqEval z m = eqEval z (m.take z.length) := fun m ↦ by
      unfold eqEval; rw [zipWith_take_right]
    rw [hcut, hcut (l.set k 0), hcut (l.set k 1)]
    rcases lt_or_ge k z.length with hkz | hkz
    · simp only [List.take_set]
      exact O.multiaffine_eqEval z _ (by simp [hl, hz]) k hkz X
    · have hset : ∀ Y, (l.set k Y).take z.length = l.take z.length := fun Y ↦
        List.take_set_of_le hkz
      rw [hset, hset, hset]
      ring
  · have hcut : ∀ m : List E, m.length = n → eqEval z m = eqEval (z.take n) m := fun m hm ↦ by
      unfold eqEval; rw [zipWith_take_left, hm]
    rw [hcut _ (by simp [hl]), hcut _ (by simp [hl]), hcut _ (by simp [hl])]
    have := O.multiaffine_eqEval (z.take n)
    rw [List.length_take_of_le hz.le] at this
    exact this l hl k hk X

/-! ## The front phases' interface -/

/-- The front phases after the OOD sample: the bus, the table sumcheck, the public input and the
Keccak reduction, returning the column claims left, and the point and slices of `q_keccak`. -/
def frontProg (ev : List K → List E → E → VerifierProgram Unit) (layout : Verifier.Layout)
    (publicInput : Digest) : VerifierProgram (List Verifier.ColumnClaim × List E × List E) := do
  let bus ← verifyBusBalance ev layout
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase layout publicInput
  keccakPhaseClaims layout (claims ++ publicClaims)

section Sizes

variable (prog : LeanIsaProgram) (input : PublicInput) (s : Sizes)

/-- `q_keccak`'s offset on the verifier's layout. -/
abbrev qkOff : ℕ := (blocks prog s).offset (keccakBlock prog s)

/-- **After the front phases**: the point and slices have their lengths, the claims fit the
opening, and no candidate of `S` meets the column claims with true slices. -/
def FrontPost (S : Set (Column (verifierLayout prog s).stackLog))
    (r : List Verifier.ColumnClaim × List E × List E) (_ : List Ev) : Prop :=
  r.2.1.length = s.τ 5 + 6 ∧ r.2.2.length = 64 ∧ r.1.length ≤ maxStackedClaims - 2 ∧
    ∀ q ∈ S, ¬ (ColumnClaimsHold (verifierLayout prog s) r.1 q ∧
      ∀ i : Fin 64, sliceExt (s.τ 5) (qkAt (qkOff prog s) q) r.2.1 i = r.2.2.getD i 0)

end Sizes

/-- **What the assembly takes of the front phases** (W3's bus, table, public-input and Keccak
specifications composed): for admissible sizes and any finite candidate set of at most one stack,
from "a stack is committed and no candidate satisfies the relation" to `FrontPost`, lead at most
`εmsg` (the bus's fingerprint group, charged at the OOD answer's boundary when the bus does not
grind). -/
structure FrontIface (ev : List K → List E → E → VerifierProgram Unit) (prog : LeanIsaProgram)
    (input : PublicInput) (publicInput : Digest) : Type where
  frontSpec : ∀ (s : Sizes) (ρ : ℕ), s.Admissible prog →
    Whir.Admissible (verifierLayout prog s).stackLog ρ →
    ∀ (S : Set (Column (verifierLayout prog s).stackLog)), S.Finite → S.ncard ≤ 1 →
    ∀ T : ℝ≥0∞, T ≤ εmsg →
    Spec (frontProg ev (verifierLayout prog s) publicInput)
      (fun h ↦ (∃ W, firstWord h = some W) ∧
        ∀ q ∈ S, ¬ M3Holds (leanIsaInstance prog s) input (toI prog s q))
      (FrontPost prog s S) εmsg εmsg T


/-! ## The program after the announced sizes -/

/-- `verify_execution` after the announced sizes `(layout, ρ)`. -/
def veBody (ev : List K → List E → E → VerifierProgram Unit) (publicInput : Digest)
    (layout : Verifier.Layout) (ρ : ℕ) : VerifierProgram Unit := do
  commitStack layout.stackLog ρ
  let ood ← readOod layout.stackLog
  let (claims, keccakPoint, keccakSlices) ← frontProg ev layout publicInput
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpening layout.stackLog ρ
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout) ++ [ood])

/-- `verify_execution` is the announced sizes, then `veBody`. -/
theorem verifyExecutionClaims_eq (ev : List K → List E → E → VerifierProgram Unit)
    (bytecode : List K) (publicInput : Digest) :
    verifyExecutionClaims ev bytecode publicInput =
      readAnnouncedSizes bytecode >>= fun a ↦ match a with
        | (layout, ρ) => veBody ev publicInput layout ρ := by
  simp only [verifyExecutionClaims, veBody, frontProg, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc]

/-! ## Moves of the claim-list phases -/

/- The phases' programs are large closed terms; `Moves` is kept folded so that elaborating a
rule's conclusion does not unfold the program it is about. -/
attribute [local irreducible] Moves

theorem moves_tableTermsClaims (cP fP point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E) (claims : List Verifier.ColumnClaim),
      Moves G64 False (fun _ ↦ True) (fun _ ↦ False)
        (tableTermsClaims cP fP point rows cursor final claims)
  | [], _, _, _ => Moves.pure trivial
  | _ :: rest, _, _, _ =>
    Moves.seq' (Moves.readN _) fun _ _ ↦ moves_tableTermsClaims cP fP point rest _ _ _

theorem moves_tableSumcheckClaims (heights : List ℕ) (busForms : List (List Form))
    (cP fP equalityPoint : List E) (target : E) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False)
      (tableSumcheckClaims heights busForms cP fP equalityPoint target) := by
  unfold tableSumcheckClaims
  refine Moves.seq' (moves_sumcheck (by norm_num) _ _) fun r _ ↦ ?_
  obtain ⟨challenges, claim⟩ := r
  refine Moves.seq' (moves_tableTermsClaims _ _ _ _ _ _ _) fun r _ ↦ ?_
  obtain ⟨final, claims⟩ := r
  exact Moves.seq' (Moves.require _) fun _ _ ↦ Moves.pure trivial

theorem moves_tablePhaseClaims (layout : Verifier.Layout) (bus : BusResult) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (tablePhaseClaims layout bus) := by
  unfold tablePhaseClaims
  refine Moves.seq (Moves.grindP fun _ ↦ grindingBits_le_sixtyFour (by decide))
    (fun _ _ ↦ Moves.seq' Moves.sampleE fun _ _ ↦ ?_)
    fun _ _ _ ↦ Moves.startsSample_sampleChallenge _
  dsimp only
  exact Moves.seq' (Q := fun _ ↦ True) (moves_tableSumcheckClaims _ _ _ _ _ _) fun _ _ ↦
    Moves.pure trivial

theorem moves_keccakPhaseClaims (layout : Verifier.Layout) (claims : List Verifier.ColumnClaim) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (keccakPhaseClaims layout claims) := by
  unfold keccakPhaseClaims
  refine Moves.seq' (Moves.require _) fun _ _ ↦ ?_
  dsimp only
  refine Moves.seq' (moves_verifyKeccak _ _ _) fun r _ ↦ ?_
  obtain ⟨outputs, point, slices⟩ := r
  exact Moves.pure trivial

theorem moves_frontProg {ev : List K → List E → E → VerifierProgram Unit}
    (hb : ∀ w p v, Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (ev w p v)) (layout : Verifier.Layout)
    (publicInput : Digest) :
    Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (frontProg ev layout publicInput) :=
  Moves.seq' (moves_verifyBusBalance hb layout) fun _ _ ↦
    Moves.seq' (moves_tablePhaseClaims _ _) fun _ _ ↦
      Moves.seq' (moves_publicInputPhase _ _) fun _ _ ↦ moves_keccakPhaseClaims _ _

/-- A sub-program without commitments keeps any property of the commitments. -/
theorem keep_commits {α : Type} {p : VerifierProgram α} {Q G : α → Prop}
    (hp : Moves G64 False Q G p) (J : List (ℕ × ℕ × Word) → Prop) :
    ∀ h₀ l, p.Reach h₀ l → J (commits h₀) → J (commits (h₀ ++ l)) := by
  intro h₀ l hl hJ
  rwa [commits_append, hp.reach_commits hl, List.append_nil]

/-! ## The phases at sizes `s` and rate `ρ` -/

section Phases

variable (O : OpeningIface) {ev : List K → List E → E → VerifierProgram Unit}
  {prog : LeanIsaProgram} {input : PublicInput} {pd : Digest} (F : FrontIface ev prog input pd)
  {s : Sizes} {ρ : ℕ}

/-- The stack's variable count. -/
abbrev μs (prog : LeanIsaProgram) (s : Sizes) : ℕ := (verifierLayout prog s).stackLog

/-- The root's candidates at level 0's threshold. -/
abbrev cands₀ (prog : LeanIsaProgram) (s : Sizes) (ρ : ℕ) (W : Word) :
    Set (Column (μs prog s)) :=
  Candidates (μs prog s) ρ (O.thr₀ (μs prog s) ρ) W

/-- **The doom the stack's root creates**, on the commitments: level 0's shape, and no candidate of
the root's word satisfies the leanISA relation. -/
def RootDoom (prog : LeanIsaProgram) (input : PublicInput) (s : Sizes) (ρ : ℕ)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  O.ShapeOK₀ (μs prog s) ρ cs ∧ ∃ W, firstWordC cs = some W ∧
    ∀ q ∈ cands₀ O prog s ρ W, ¬ M3Holds (leanIsaInstance prog s) input (toI prog s q)

/-- The invariant the phases after the OOD sample carry: the stack's word and shape. -/
def WordShape (prog : LeanIsaProgram) (s : Sizes) (ρ : ℕ) (W : Word) (h : List Ev) : Prop :=
  firstWordC (commits h) = some W ∧ O.ShapeOK₀ (μs prog s) ρ (commits h)

/-- The candidate left by the OOD sample. -/
abbrev left (prog : LeanIsaProgram) (s : Sizes) (ρ : ℕ) (W : Word) (z : List E) (y : E) :
    Set (Column (μs prog s)) :=
  oodCands (cands₀ O prog s ρ W) z y

/-- The ring claim's reading on a candidate. -/
def ringRC (prog : LeanIsaProgram) (s : Sizes) (r : E × (List E → E)) (q : Column (μs prog s)) :
    Prop :=
  StackClaim.Holds (μs prog s) (ringSwitchClaim (verifierLayout prog s) r.1 r.2) q

/-- The opening's claims. -/
def openClaims (layout : Verifier.Layout) (cl : List Verifier.ColumnClaim) (y : E × (List E → E)) (ood : StackClaim) :
    List StackClaim :=
  ringSwitchClaim layout y.1 y.2 :: cl.map (·.stackClaim layout) ++ [ood]

theorem length_openClaims (layout : Verifier.Layout) (cl : List Verifier.ColumnClaim)
    (y : E × (List E → E)) (ood : StackClaim) :
    (openClaims layout cl y ood).length = cl.length + 2 := by
  simp only [openClaims, List.cons_append, List.length_cons, List.length_append, List.length_map,
    List.length_nil]

open Classical in
/-- **The stacked opening**, from ring switching's postcondition on the candidate left, the
separation of the candidates and the stack's word and shape. -/
noncomputable def openingPart (hadm : Whir.Admissible (μs prog s) ρ) (W : Word) (z : List E)
    (y : E) (hsep : OodSep (cands₀ O prog s ρ W) z) (cl : List Verifier.ColumnClaim)
    (hcl : cl.length ≤ maxStackedClaims - 2) (r : E × (List E → E)) :
    Spec (verifyStackedOpening (μs prog s) ρ
        (openClaims (verifierLayout prog s) cl r (oodClaim z y)))
      (fun h ↦ (RingPost (left O prog s ρ W z y)
          (fun q ↦ ColumnClaimsHold (verifierLayout prog s) cl q) (ringRC prog s) r h ∧
          IsMultilinearFn (μs prog s) (ringSwitchClaim (verifierLayout prog s) r.1 r.2).1) ∧
        WordShape O prog s ρ W h)
      (fun _ _ ↦ False) εmsg (eBatchOf (cl.length + 2) (O.listMax₀ (μs prog s) ρ)) 0 :=
  if hq : IsMultilinearFn (μs prog s) (ringSwitchClaim (verifierLayout prog s) r.1 r.2).1 then
    (O.stackedSpec hadm (openClaims (verifierLayout prog s) cl r (oodClaim z y))
      (by rw [length_openClaims]; simp only [maxStackedClaims] at hcl ⊢; omega)
      (by
        intro c hc
        simp only [openClaims, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | ⟨c', -, rfl⟩ | rfl
        · exact O.multiaffine_of_multilinear hq
        · exact isMultiaffine_eqEval_any O _ _
        · exact isMultiaffine_eqEval_any O _ _) 0).mono
      (fun h hp ↦ by
        obtain ⟨⟨hring, -⟩, hW, hshape⟩ := hp
        refine ⟨hshape, ?_⟩
        have hw : O.word₀ (commits h) = W := by
          have := O.shape_word hshape
          rw [hW] at this
          exact (Option.some.inj this).symm
        rw [hw]
        intro q hq'
        have hv := exists_violated_of_ood hsep
          (ringSwitchClaim (verifierLayout prog s) r.1 r.2 ::
            cl.map (·.stackClaim (verifierLayout prog s)))
          (fun q hq hall ↦ hring q hq
            ⟨fun c hc ↦ hall _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hc)),
              hall _ List.mem_cons_self⟩) q hq'
        simpa only [openClaims, List.cons_append] using hv)
      (fun _ _ h ↦ h) le_rfl
      (by rw [length_openClaims]) le_rfl
  else Spec.dead.mono (fun _ hp ↦ hq hp.1.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- The ring switch's returned claim is multilinear. -/
theorem ringSwitch_multilinear (layout : Verifier.Layout) (point sv : List E) :
    ∀ l y, (ringSwitch point sv).after l = some (.ret y) →
      IsMultilinearFn layout.stackLog (ringSwitchClaim layout y.1 y.2).1 := by
  have hm : Moves G64 False
      (fun y : E × (List E → E) ↦ ∃ cs, y.2 = fun r ↦ ringWeight point r cs)
      (fun _ ↦ False) (ringSwitch point sv) := by
    rw [Ring.ringSwitch_eq]
    exact Moves.bind (Moves.grindP fun _ ↦ by decide)
      (fun _ _ ↦ Moves.bind (Moves.sampleN 16) (fun _ _ ↦ Moves.ret ⟨_, rfl⟩) fun _ _ h ↦ h.elim)
      fun _ _ _ ↦ trivial
  intro l y hl
  obtain ⟨cs, hcs⟩ : ∃ cs, y.2 = fun r ↦ ringWeight point r cs := by
    have := hm.after hl
    unfold Moves at this
    exact this
  obtain ⟨t, w⟩ := y
  simp only at hcs
  subst hcs
  exact isMultilinearFn_ringSwitchClaim layout t point cs

/-- The ring's group error with the opening's `λ` is at most `2^-125` after the batch grind. -/
theorem ring_eps (hadm : Whir.Admissible (μs prog s) ρ) {J : ℕ} (hJ : J ≤ maxStackedClaims) :
    (2 : ℝ≥0∞)⁻¹ ^ Whir.batchGrindingBits *
        (((1 : ℕ) : ℝ≥0∞) * (2 / Fintype.card E) + eBatchOf J (O.listMax₀ (μs prog s) ρ)) ≤
      εmsg := by
  have hrow := O.lambda_row hadm
  have hsum : ((1 : ℕ) : ℝ≥0∞) * (2 / Fintype.card E) + eBatchOf J (O.listMax₀ (μs prog s) ρ) =
      ((2 + (J - 1) * O.listMax₀ (μs prog s) ρ : ℕ) : ℝ≥0∞) / Fintype.card E := by
    rw [eBatchOf, Nat.cast_one, one_mul, ENNReal.div_add_div_same, Nat.cast_add, Nat.cast_ofNat]
  rw [hsum]
  refine discount_le Whir.batchGrindingBits _ ?_
  have : (J - 1) * O.listMax₀ (μs prog s) ρ ≤ (maxStackedClaims - 1) * O.listMax₀ (μs prog s) ρ :=
    Nat.mul_le_mul_right _ (by omega)
  rcases Nat.eq_zero_or_pos (O.listMax₀ (μs prog s) ρ) with h0 | hpos
  · rw [h0, mul_zero, add_zero]
    exact Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : 1 ≤ Whir.batchGrindingBits + 3)
  · simp only [maxStackedClaims, Nat.reduceAdd, Nat.reduceSub] at hrow this
    omega

open Classical in
/-- **Ring switching, then the stacked opening**, for the front phases' result `r`. -/
noncomputable def ringPart (hadm : Whir.Admissible (μs prog s) ρ) (W : Word) (z : List E) (y : E)
    (hsep : OodSep (cands₀ O prog s ρ W) z) (r : List Verifier.ColumnClaim × List E × List E) :
    Spec ((ringSwitch r.2.1 r.2.2).bind fun y' ↦
        verifyStackedOpening (μs prog s) ρ (openClaims (verifierLayout prog s) r.1 y' (oodClaim z y)))
      (fun h ↦ FrontPost prog s (left O prog s ρ W z y) r h ∧ WordShape O prog s ρ W h)
      (fun _ _ ↦ False) εmsg 0 0 :=
  if hr : r.2.1.length = s.τ 5 + 6 ∧ r.2.2.length = 64 ∧ r.1.length ≤ maxStackedClaims - 2 then
    have hsv : List.ofFn (fun i : Fin 64 ↦ r.2.2.getD i 0) = r.2.2 := by
      apply List.ext_getElem (by simp [hr.2.1])
      intro i h1 h2
      rw [List.getElem_ofFn]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    have hS := (O.candidates_finite W hadm).subset (oodCands_subset _ z y)
    (Spec.frame (Spec.retInv
      ((ringSpec (left O prog s ρ W z y) (fun q ↦ ColumnClaimsHold (verifierLayout prog s) r.1 q)
        (fun q i ↦ sliceExt (s.τ 5) (qkAt (qkOff prog s) q) r.2.1 i) (fun i ↦ r.2.2.getD i 0)
        (ringRC prog s) (ringClaimBad_stack (ringLayoutHyp_verifierLayout prog s) hr.1 _) hS
        (oodCands_ncard_le _ z y) (by simpa using div_card_lt_one (N := 2) (by norm_num))
        (ring_eps O hadm (J := r.1.length + 2)
          (by have := hr.2.2; simp only [maxStackedClaims] at this ⊢; omega))).congr (by rw [hsv]))
      _ (ringSwitch_multilinear (verifierLayout prog s) r.2.1 r.2.2))
      (WordShape O prog s ρ W) (fun h₀ l hl hJ ↦
        ⟨keep_commits (moves_ringSwitch r.2.1 r.2.2) (fun cs ↦ firstWordC cs = some W) h₀ l hl hJ.1,
          keep_commits (moves_ringSwitch r.2.1 r.2.2) (O.ShapeOK₀ (μs prog s) ρ) h₀ l hl hJ.2⟩)
      ).mono (Pre' := fun h ↦ FrontPost prog s (left O prog s ρ W z y) r h ∧ WordShape O prog s ρ W h)
      (fun h hp ↦ ⟨fun q hq hG ↦ hp.1.2.2.2 q hq ⟨hG.1, fun i ↦ congrFun hG.2 i⟩, hp.2⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun y' ↦
      openingPart O hadm W z y hsep r.1 hr.2.2 y'
  else Spec.dead.mono (fun _ hp ↦ hr ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩) (fun _ _ h ↦ h) le_rfl
    le_rfl le_rfl

open Classical in
/-- **The front phases, ring switching and the opening**, for the candidate the OOD sample left. -/
noncomputable def afterOodPart (hev : ∀ w p v, Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (ev w p v))
    (hs : s.Admissible prog) (hadm : Whir.Admissible (μs prog s) ρ) (W : Word) (z : List E) (y : E)
    (hsep : OodSep (cands₀ O prog s ρ W) z) :
    Spec (frontProg ev (verifierLayout prog s) pd >>= fun r ↦ match r with
        | (claims, keccakPoint, keccakSlices) => ringSwitch keccakPoint keccakSlices >>= fun y' ↦
          match y' with
          | (ringTarget, ringWeight) => verifyStackedOpening (μs prog s) ρ
            (ringSwitchClaim (verifierLayout prog s) ringTarget ringWeight ::
              claims.map (·.stackClaim (verifierLayout prog s)) ++ [oodClaim z y]))
      (fun h ↦ (∀ q ∈ left O prog s ρ W z y, ¬ M3Holds (leanIsaInstance prog s) input (toI prog s q)) ∧
        WordShape O prog s ρ W h)
      (fun _ _ ↦ False) εmsg εmsg 0 :=
  (Spec.frame (F.frontSpec s ρ hs hadm (left O prog s ρ W z y)
      ((O.candidates_finite W hadm).subset (oodCands_subset _ z y)) (oodCands_ncard_le _ z y) 0
      zero_le)
    (WordShape O prog s ρ W) (fun h₀ l hl hJ ↦
      ⟨keep_commits (moves_frontProg hev _ pd) (fun cs ↦ firstWordC cs = some W) h₀ l hl hJ.1,
        keep_commits (moves_frontProg hev _ pd) (O.ShapeOK₀ (μs prog s) ρ) h₀ l hl hJ.2⟩)).mono
    (Pre' := fun h ↦ (∀ q ∈ left O prog s ρ W z y, ¬ M3Holds (leanIsaInstance prog s) input
      (toI prog s q)) ∧ WordShape O prog s ρ W h)
    (fun _ hp ↦ ⟨⟨⟨W, hp.2.1⟩, hp.1⟩, hp.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind'
    fun r ↦ by
      obtain ⟨claims, keccakPoint, keccakSlices⟩ := r
      exact (ringPart O hadm W z y hsep (claims, keccakPoint, keccakSlices)).congr
        (by congr 1)

open Classical in
/-- **After the OOD sample**: the claim it returned, the separation of the candidates at its point,
and the root's doom. -/
noncomputable def oodThen (hev : ∀ w p v, Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (ev w p v))
    (hs : s.Admissible prog) (hadm : Whir.Admissible (μs prog s) ρ) (ood : StackClaim) :
    Spec (frontProg ev (verifierLayout prog s) pd >>= fun r ↦ match r with
        | (claims, keccakPoint, keccakSlices) => ringSwitch keccakPoint keccakSlices >>= fun y' ↦
          match y' with
          | (ringTarget, ringWeight) => verifyStackedOpening (μs prog s) ρ
            (ringSwitchClaim (verifierLayout prog s) ringTarget ringWeight ::
              claims.map (·.stackClaim (verifierLayout prog s)) ++ [ood]))
      (OodPost (firstCands (μs prog s) ρ (O.thr₀ (μs prog s) ρ)) (RootDoom O prog input s ρ) ood)
      (fun _ _ ↦ False) εmsg εmsg 0 :=
  (Spec.exPre (ι := Word × List E × E) (Pre := fun i h ↦ ood = oodClaim i.2.1 i.2.2 ∧
      OodSep (cands₀ O prog s ρ i.1) i.2.1 ∧
      (∀ q ∈ left O prog s ρ i.1 i.2.1 i.2.2, ¬ M3Holds (leanIsaInstance prog s) input (toI prog s q)) ∧
      WordShape O prog s ρ i.1 h) fun i ↦
    if hc : ood = oodClaim i.2.1 i.2.2 ∧ OodSep (cands₀ O prog s ρ i.1) i.2.1 then
      (afterOodPart O F hev hs hadm i.1 i.2.1 i.2.2 hc.2).congr (by rw [hc.1]) |>.mono
        (fun _ hp ↦ hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hc ⟨hp.1, hp.2.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
    (fun h hp ↦ by
      obtain ⟨z, y, hood, -, ⟨hshape, W, hW, hdoom⟩, hsep⟩ := hp
      have hc : firstCands (μs prog s) ρ (O.thr₀ (μs prog s) ρ) (commits h) = cands₀ O prog s ρ W :=
        firstCands_eq hW
      rw [hc] at hsep
      exact ⟨(W, z, y), hood, hsep, fun q hq ↦ hdoom q (oodCands_subset _ z y hq), hW, hshape⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- The stack has at least one variable. -/
theorem μs_ne_zero (hadm : Whir.Admissible (μs prog s) ρ) : μs prog s ≠ 0 := by
  have := hadm.1
  simp only [Whir.minLogStack] at this
  omega

/-- **`verify_execution` after the announced sizes, at admissible sizes**: the stack's root, its OOD
sample, then `oodThen`. -/
noncomputable def realSpec (hev : ∀ w p v, Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (ev w p v))
    (hs : s.Admissible prog) (hadm : Whir.Admissible (μs prog s) ρ) :
    Spec (veBody ev pd (verifierLayout prog s) ρ) (fun _ ↦ False) (fun _ _ ↦ False) εmsg 0 0 :=
  (commitSpec (fun _ h ↦ RootDoom O prog input s ρ (commits h)) (μs prog s) ρ
      (zero_le (a := εmsg))).bind' fun _ ↦
    (commitOodSpec (A := O.thr₀) (μs_ne_zero hadm)
        (fun W ↦ ⟨O.candidates_finite W hadm, O.card_candidates_le W hadm⟩)
        (RootDoom O prog input s ρ)
        (by unfold oodError
            exact div_card_lt_one ((O.ood_row hadm).trans (Nat.pow_le_pow_right (by norm_num) (by decide))))
        (by rw [add_zero]; unfold oodError; exact discount_le Whir.oodGrindingBits _ (O.ood_row hadm))
        (le_refl εmsg)).bind' fun ood ↦
      oodThen O F hev hs hadm ood

end Phases

/-! ## The whole program -/

section Whole

variable (O : OpeningIface) {ev : List K → List E → E → VerifierProgram Unit}
  {prog : LeanIsaProgram} {input : PublicInput} {pd : Digest} (F : FrontIface ev prog input pd)
  (hev : ∀ w p v, Moves G64 False (fun _ ↦ True) (fun _ ↦ False) (ev w p v))

open Classical in
/-- `verify_execution` after the announced value `a`: `realSpec` at admissible sizes, dead
otherwise. -/
noncomputable def bodySpec (a : Verifier.Layout × ℕ) :
    Spec (veBody ev pd a.1 a.2) (fun _ ↦ False) (fun _ _ ↦ False) εmsg 0 0 :=
  if h : ∃ s, a.1 = verifierLayout prog s ∧ s.Admissible prog ∧ Whir.Admissible a.1.stackLog a.2 then
    (realSpec O F (s := h.choose) (ρ := a.2) hev h.choose_spec.2.1
      (by rw [μs, ← h.choose_spec.1]; exact h.choose_spec.2.2)).congr
      (congrArg (fun l ↦ veBody ev pd l a.2) h.choose_spec.1.symm)
  else Spec.dead

/-- **The specification of `verify_execution`**, on the claim-list form. -/
noncomputable def veSpec (bytecode : List K) :
    Spec (verifyExecutionClaims ev bytecode pd) (fun _ ↦ False) (fun _ _ ↦ False) εmsg 0 0 :=
  ((readSizesSpec bytecode (fun _ _ ↦ False)).bind' fun a ↦ by
    obtain ⟨layout, ρ⟩ := a
    exact bodySpec O F hev (layout, ρ)).congr (verifyExecutionClaims_eq ev bytecode pd).symm

end Whole



/-! ## The leanVM verifier and its certificate -/

section Program

variable (O : OpeningIface) {prog : LeanIsaProgram} {input : PublicInput} {pd : Digest}
  (F : FrontIface computedBytecodeValue prog input pd)

/-- **The specification of the leanVM verifier program**: from no doom, rejecting where it returns
in doom, every group at most `2^-125` after its grind, lead `0`. -/
@[irreducible] noncomputable def leanVmSpec (bytecode : List K) :
    Spec (leanVmVerifierProgram bytecode pd) (fun _ ↦ False) (fun b _ ↦ b = false) εmsg 0 0 :=
  ((veSpec O F moves_computedBytecodeValue bytecode).bind' fun _ ↦
    (Spec.ret (Post := fun b _ ↦ b = false) (T := 0) true).mono (fun _ h ↦ h.elim) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl).congr (leanVmProgram_eq _ _).symm

/-- Doom never holds at the empty history: the announced sizes are not at stake. -/
theorem leanVmSpec_D_nil (bytecode : List K) : ¬ (leanVmSpec O F bytecode).D [] [] := by
  intro hD
  rw [leanVmSpec, Spec.congr_D] at hD
  have hs : (verifyExecutionClaims computedBytecodeValue bytecode pd).retSplit [] = none :=
    retSplit_eq_none_of_after rfl (verifyExecution_ne_ret _ _)
  have h1 := (Spec.bindD_none hs).1 hD
  rw [veSpec, Spec.congr_D] at h1
  have hs' : (readAnnouncedSizes bytecode).retSplit [] = none :=
    retSplit_eq_none_of_after rfl (readSizes_ne_ret _)
  exact (Spec.bindD_none hs').1 h1

/-- **The doom certificate of the leanVM verifier.** -/
noncomputable def leanVmCert (bytecode : List K) : Cert (leanVmVerifierProgram bytecode pd) :=
  (leanVmSpec O F bytecode).toCert

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
group (`2^-min(b, 64)`), is at most `2^-125`, the random-oracle theorem's hypothesis. -/
theorem leanVmCert_bound (bytecode : List K) (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (leanVmCert O F bytecode).ε h ≤ εmsg := by
  by_cases hr : (leanVmVerifierProgram bytecode pd).Reachable h
  · rw [min_eq_left (grindBits_le_of_reachable _ _ hr)]
    exact Spec.toCert_bound _ (fun hD ↦ absurd hD (leanVmSpec_D_nil O F bytecode)) h
  · simp only [leanVmCert, Spec.toCert_ε, hr, false_and, ↓reduceIte, mul_zero, zero_le]

end Program

end
end LeanVM.Protocol.EndToEnd.Sound
