/-
Protocol 4.2 of the paper (DEEP-fold WHIR) with one batch of points per level, as a public-coin
transition system over a ladder of levels (`protocolD`), its state function, and the theorem that
it is round-by-round sound with the errors of Theorem 5.2.

The model. The prover's messages are the objects themselves (a committed word is a function on
the field, as in the interactive oracle model; Merkle commitments are outside), the verifier's
messages are uniform, and the verifier's final decision is a proposition. A position holds what
the messages so far determine and the rest of the protocol needs: the level's parameters, the
current folded word, the points, the carried values, the running claim, and two things that only
the analysis reads: the extraction predicate `G` and the proposition `tru`.

- `commit`: nothing has been sent. The prover commits the level-0 word, the verifier sends the
  level's points (Commit).
- `opening`: the prover answers the points and names `J` weighted claims, which may depend on
  the points (Commit, and the claims of Open); the verifier sends `λ` (Open).
- `fold`, `r + 1` rounds to come: the prover sends `(v_G, v_F, σ₀, σ₁, φ)`, the verifier the fold
  challenge (step 1).
- `fold`, no round to come, a next level: the prover commits the next word and sends the high
  part; the verifier sends the next level's points (step 2).
- `boundary`: the prover answers the new points; the verifier sends the queries and `λ` (step 2).
- `fold`, no round to come, no next level: the prover sends the final polynomial; the verifier
  checks the carried point claims on it and sends the queries (step 3).
- `tail`: a round of the tail sumcheck on the final claim (the prover sends a round polynomial of
  degree at most two, the verifier a scalar), and after the last round the terminal check.
- `done`: the protocol has ended.

What is abstract: the map `low` of a level (`U ↦ 𝒫_{g_U}`, any linear map), the high part `C`
(any polynomial on which the running weight vanishes and with `deg(low U + C) ≤ d` for the list
members of the next word), and the tables of the tail (`Terminal`: any two tables whose inner
product is the running claim's value on the final polynomial); the weights are arbitrary linear
functionals. The real encoder gives such data by the identities of Annex B of the leanVM
specification, which are not formalized.
With `Terminal.direct` there is no tail round and the verifier checks the running claim on the
final polynomial itself.
-/
import Soundness.RBR
import Soundness.State

open Polynomial
open Finset hiding dens
open scoped Classical

namespace Soundness

open DeepFold
open Protocol (Lane Word exL levelPot Good listW foldW dens)
open Rounds (Doomed InList NearT agr foldVal foldWeight foldClaim pull batchW batchC nextW nextC
  constL)

variable (K : Type) [Field K]

/-- The parameters of a level: the domain `D`, the degree bound `d`, the number `ℓ` of fold
rounds (lane variables), of points `s` and of queries `t`, the agreement thresholds `thr`
(`thr k = A^{(i,k)}` after `k` rounds; the queries are at `thr ℓ`), the list size `L` the
analysis assumes, and the map `low` from the tuples of this level to the polynomials of the
previous level's last round (`U ↦ 𝒫_{g_U}`; not used at level 0). -/
structure Level where
  /-- The evaluation domain. -/
  D : Finset K
  /-- The degree bound. -/
  d : ℕ
  /-- The number of fold rounds. -/
  ℓ : ℕ
  /-- The number of points. -/
  s : ℕ
  /-- The number of queries. -/
  t : ℕ
  /-- The agreement thresholds. -/
  thr : ℕ → ℕ
  /-- The list size the analysis assumes. -/
  L : ℕ
  /-- The polynomial of the previous level that a tuple of this level encodes. -/
  low : (Lane ℓ → K[X]) →ₗ[K] K[X]

variable {K}

/-- The standing assumptions on a level (Section 5.1 of the paper), for the analysis constant `M`:
at least one fold round, a nonempty domain with `C(n, 2) ≤ M` (S3), thresholds that grow by at
least one a round, and the hypothesis `ListBound`: every word of the level folded `k` times has
at most `L` list members at the agreement `thr k`. -/
structure Level.OK [Fintype K] (M : ℕ) (lv : Level K) : Prop where
  /-- `ℓ ≥ 1`. -/
  ell_pos : 1 ≤ lv.ℓ
  /-- The domain is not empty. -/
  nonempty : lv.D.Nonempty
  /-- (S3). -/
  choose_le : lv.D.card.choose 2 ≤ M
  /-- `A^{(i,k)} + 1 ≤ A^{(i,k+1)}`. -/
  thr_step : ∀ k, lv.thr k + 1 ≤ lv.thr (k + 1)
  /-- `ListBound`. -/
  listBound : ∀ k r, k + r = lv.ℓ → ∀ O' : Word K r, (listW lv.D O' lv.d (lv.thr k)).card ≤ lv.L

variable (K)

/-- The prover's message of the opening: the answers to the points and `J` weighted claims. -/
structure OpenMsg (lv : Level K) (J : ℕ) where
  /-- The answers `y_m`. -/
  y : Fin lv.s → K
  /-- The weights of the claims. -/
  Wk : Fin J → (Lane lv.ℓ → K[X]) →ₗ[K] K
  /-- The values of the claims. -/
  ck : Fin J → K

/-- The prover's message of a fold round: `(v_G, v_F, σ₀, σ₁)` and the values `φ_m`. -/
structure FoldAns (s : ℕ) where
  /-- `v_G`. -/
  vG : K
  /-- `v_F`. -/
  vF : K
  /-- `σ₀`. -/
  σ₀ : K
  /-- `σ₁`. -/
  σ₁ : K
  /-- `φ_m`. -/
  φ : Fin s → K

/-- The prover's message at the end of a level that is not the last: the next committed word `O'`
and the high part `C`, on which the running weight `W` vanishes, and with `deg(low U + C) ≤ d`
for every member `U` of the list of `O'`. -/
structure Handover (lv lv' : Level K) (W : (Lane 0 → K[X]) →ₗ[K] K) where
  /-- The word committed for the next level. -/
  O' : Word K lv'.ℓ
  /-- The high part. -/
  C : K[X]
  /-- The running weight ignores the high part. -/
  hW : W (fun _ => C) = 0
  /-- `P^*_U = low U + C` has degree at most `d`. -/
  hdeg : ∀ U : Lane lv'.ℓ → K[X], InList lv'.D O' lv'.d (lv'.thr 0) U →
    (lv'.low U + C).natDegree ≤ lv.d

/-- The tail: `ν` sumcheck rounds on two tables over `{0,1}^ν`. For the running weight `W` at the
end of the last level and the final polynomial `P`, `wtab W P` is the table of the terminal
weight and `ftab W P` the table of the low part of `P`; the final polynomial is one for which
their inner product is `⟨W, P⟩` (`FinalMsg`). In the protocol `wtab` is computed from the
transcript and `ftab` from `P`; here both may depend on both. -/
structure Terminal where
  /-- The number of tail rounds. -/
  ν : ℕ
  /-- The table of the terminal weight. -/
  wtab : ((Lane 0 → K[X]) →ₗ[K] K) → K[X] → Lane ν → K
  /-- The table of the final polynomial's low part. -/
  ftab : ((Lane 0 → K[X]) →ₗ[K] K) → K[X] → Lane ν → K

/-- No tail: one table entry, the value of the running claim on the final polynomial, so that the
terminal check is `⟨W, P⟩ = σ`. -/
noncomputable def Terminal.direct : Terminal K where
  ν := 0
  wtab := fun _ _ _ => 1
  ftab := fun W P _ => W (fun _ => P)

/-- The prover's last message of the opening: the final polynomial `P`, of degree at most `d`,
with `⟨W, P⟩` the inner product of the two tables of the tail. -/
structure FinalMsg (T : Terminal K) (lv : Level K) (W : (Lane 0 → K[X]) →ₗ[K] K) where
  /-- The final polynomial. -/
  P : K[X]
  /-- Its degree is at most `d` (it is sent by its coefficients). -/
  hdeg : P.natDegree ≤ lv.d
  /-- The running claim's value on `P` is the inner product of the tables. -/
  hspec : W (fun _ => P) = ∑ x, T.wtab W P x * T.ftab W P x

/-- The positions of the model. In `fold`, `k` rounds of the level have been played and `r` are
to come, `O` is the committed word folded `k` times, `z` the points, `v` the carried values,
`(W, σ)` the running claim, `G` the extraction predicate (which tuples of the current round
descend to a member of the level-0 list that matches the commit-phase answers and satisfies all
input claims) and `tru` the proposition that such a member exists. -/
inductive Pos : Type
  | commit (lv : Level K) (rest : List (Level K))
  | opening (lv : Level K) (rest : List (Level K)) (O : Word K lv.ℓ) (z : Fin lv.s → K × K)
  | fold (lv : Level K) (rest : List (Level K)) (k r : ℕ) (O : Word K r)
      (z : Fin lv.s → K × K) (v : Fin lv.s → K) (W : (Lane r → K[X]) →ₗ[K] K) (σ : K)
      (G : (Lane r → K[X]) → Prop) (tru : Prop)
  | boundary (lv : Level K) (k : ℕ) (O : Word K 0) (z : Fin lv.s → K × K) (v : Fin lv.s → K)
      (W : (Lane 0 → K[X]) →ₗ[K] K) (σ : K) (G : (Lane 0 → K[X]) → Prop) (tru : Prop)
      (lv' : Level K) (rest : List (Level K)) (h : Handover K lv lv' W)
      (z' : Fin lv'.s → K × K)
  | tail (r : ℕ) (Wt ft : Lane r → K) (σ : K) (ok ext tru : Prop)
  | done (acc ext tru : Prop)

variable (T : Terminal K)

/-- The prover's message at a `fold` position. -/
def FoldMsg (lv : Level K) : ∀ r : ℕ, ((Lane r → K[X]) →ₗ[K] K) → List (Level K) → Type
  | _ + 1, _, _ => FoldAns K lv.s
  | 0, W, [] => FinalMsg K T lv W
  | 0, W, lv' :: _ => Handover K lv lv' W

/-- The prover's message at a `tail` position: a round polynomial of degree at most two, and
nothing once no round is left. -/
def TailMsg : ℕ → Type
  | _ + 1 => {h : K[X] // h.natDegree ≤ 2}
  | 0 => PUnit

/-- The verifier's message at a `tail` position. -/
def TailChal : ℕ → Type
  | _ + 1 => K
  | 0 => PUnit

/-- The verifier's message at a `fold` position. -/
def FoldChal (lv : Level K) : ℕ → List (Level K) → Type
  | _ + 1, _ => K × K
  | 0, [] => Fin lv.t → lv.D
  | 0, lv' :: _ => Fin lv'.s → K × K

/-- The prover's messages. -/
def Msg (J : ℕ) : Pos K → Type
  | .commit lv _ => Word K lv.ℓ
  | .opening lv _ _ _ => OpenMsg K lv J
  | .fold lv rest _ r _ _ _ W _ _ _ => FoldMsg K T lv r W rest
  | .boundary _ _ _ _ _ _ _ _ _ lv' _ _ _ => Fin lv'.s → K
  | .tail r _ _ _ _ _ _ => TailMsg K r
  | .done _ _ _ => PUnit

/-- The verifier's messages. -/
def Chal : Pos K → Type
  | .commit lv _ => Fin lv.s → K × K
  | .opening _ _ _ _ => K
  | .fold lv rest _ r _ _ _ _ _ _ _ => FoldChal K lv r rest
  | .boundary lv _ _ _ _ _ _ _ _ _ _ _ _ => (Fin lv.t → lv.D) × K
  | .tail r _ _ _ _ _ _ => TailChal K r
  | .done _ _ _ => PUnit

variable {K}

/-- A table of the tail after its first variable is set to `c`: `(1 - c) T(0, ·) + c T(1, ·)`. -/
def tabFold (c : K) {r : ℕ} (t : Lane (r + 1) → K) : Lane r → K :=
  fun x => (1 - c) * t (Sum.inl x) + c * t (Sum.inr x)

/-- The extraction predicate at level 0: `U` is in the list of the committed word, matches the
commit-phase answers and satisfies every input claim. Its negation is the canonical predicate
`Bad` of Section 5.3 of the paper. -/
def claimsHold (lv : Level K) {J : ℕ} (O : Word K lv.ℓ) (z : Fin lv.s → K × K)
    (p : OpenMsg K lv J) : (Lane lv.ℓ → K[X]) → Prop :=
  fun U => InList lv.D O lv.d (lv.thr 0) U ∧ (∀ m, evL (exL 0 lv.ℓ) (z m) U = p.y m) ∧
    ∀ k, p.Wk k U = p.ck k

/-- One step of the descent (Section 5.5 of the paper): `P`, a tuple of the round after the
challenge `c`, descends through the fold if it agrees with the fold `O_c` on at least `A` columns
and some near tuple of the unfolded word `O` on its agreement set satisfies `G`. For `A ≥ d + 3` the
near tuple is unique (`descend_iff_unique`). -/
def descend (D : Finset K) (d A : ℕ) {r : ℕ} (O : Word K (r + 1)) (c : K × K)
    (G : (Lane (r + 1) → K[X]) → Prop) : (Lane r → K[X]) → Prop :=
  fun P => A ≤ (agr D (foldW O c) P).card ∧
    ∃ T : Lane (r + 1) → K[X], NearT D O d (agr D (foldW O c) P) T ∧ G T

/-- The negation of the descent is the pull-back of the negation (`Rounds.pull`): the predicate
of the relativised invariant after a fold round. -/
theorem pull_not_iff (D : Finset K) (d A : ℕ) {r : ℕ} (O : Word K (r + 1)) (c : K × K)
    (G : (Lane (r + 1) → K[X]) → Prop) (P : Lane r → K[X]) :
    pull D O d A c (fun U => ¬ G U) P ↔ ¬ descend D d A O c G P := by
  constructor
  · rintro h ⟨hA, T, hT, hG⟩
    exact h hA T hT hG
  · intro h hA T hT hG
    exact h ⟨hA, T, hT, hG⟩

variable (K)

/-- The position after a round played from a `fold` position. -/
noncomputable def foldNext (lv : Level K) (k : ℕ) :
    ∀ (r : ℕ) (_O : Word K r) (_z : Fin lv.s → K × K) (_v : Fin lv.s → K)
      (W : (Lane r → K[X]) →ₗ[K] K) (_σ : K) (_G : (Lane r → K[X]) → Prop) (_tru : Prop)
      (rest : List (Level K)), FoldMsg K T lv r W rest → FoldChal K lv r rest → Pos K
  | r + 1, O, z, v, W, σ, G, tru, rest, p, c =>
      .fold lv rest (k + 1) r (foldW O c) z (foldVal (2 ^ k) z v p.φ c) (foldWeight W c)
        (foldClaim σ p.vG p.vF p.σ₀ p.σ₁ c) (descend lv.D lv.d (lv.thr (k + 1)) O c G) tru
  | 0, O, z, v, W, σ, G, tru, [], p, x =>
      .tail T.ν (T.wtab W p.P) (T.ftab W p.P) σ
        ((∀ m, p.P.eval (z m).2 = v m) ∧ ∀ q, p.P.eval (x q : K) = O (x q) default)
        (G (fun _ => p.P)) tru
  | 0, O, z, v, W, σ, G, tru, lv' :: rest, h, z' => .boundary lv k O z v W σ G tru lv' rest h z'

/-- The position after a round played from a `tail` position: a sumcheck round (the verifier
checks `h(0) + h(1) = σ` and the claim becomes `h(c)` on the tables with their first variable set
to `c`), or the terminal check when no variable is left. -/
noncomputable def tailNext : ∀ (r : ℕ) (_Wt _ft : Lane r → K) (_σ : K) (_ok _ext _tru : Prop),
    TailMsg K r → TailChal K r → Pos K
  | r + 1, Wt, ft, σ, ok, ext, tru, h, c =>
      .tail r (tabFold (K := K) c Wt) (tabFold (K := K) c ft) (h.1.eval c)
        (ok ∧ h.1.eval 0 + h.1.eval 1 = σ) ext tru
  | 0, Wt, ft, σ, ok, ext, tru, _, _ => .done (ok ∧ Wt default * ft default = σ) ext tru

/-- The position after one round. -/
noncomputable def next (J : ℕ) : ∀ s : Pos K, Msg K T J s → Chal K s → Pos K
  | .commit lv rest, O, z => .opening lv rest O z
  | .opening lv rest O z, p, l =>
      .fold lv rest 0 lv.ℓ O z p.y (batchW p.Wk l) (batchC p.ck l) (claimsHold lv O z p)
        (∃ U, claimsHold lv O z p U)
  | .fold lv rest k r O z v W σ G tru, p, c => foldNext K T lv k r O z v W σ G tru rest p c
  | .boundary _ _ O z v W σ G tru lv' rest h z', y', xl =>
      .fold lv' rest 0 lv'.ℓ h.O' z' y'
        (nextW (W ∘ₗ constL (Lane 0)) lv'.low (fun m => (z m).2) (fun q => (xl.1 q : K)) xl.2)
        (nextC σ h.C (fun x => O x default) (fun m => (z m).2) v (fun q => (xl.1 q : K)) xl.2)
        (fun U => G (fun _ => lv'.low U + h.C)) tru
  | .tail r Wt ft σ ok ext tru, p, c => tailNext K r Wt ft σ ok ext tru p c
  | .done a e t, _, _ => .done a e t

variable [Fintype K]

noncomputable instance TailChal.instFintype : ∀ r : ℕ, Fintype (TailChal K r)
  | _ + 1 => inferInstanceAs (Fintype K)
  | 0 => inferInstanceAs (Fintype PUnit)

noncomputable instance FoldChal.instFintype (lv : Level K) :
    ∀ (r : ℕ) (rest : List (Level K)), Fintype (FoldChal K lv r rest)
  | _ + 1, _ => inferInstanceAs (Fintype (K × K))
  | 0, [] => inferInstanceAs (Fintype (Fin lv.t → lv.D))
  | 0, lv' :: _ => inferInstanceAs (Fintype (Fin lv'.s → K × K))

noncomputable instance Chal.instFintype : ∀ s : Pos K, Fintype (Chal K s)
  | .commit lv _ => inferInstanceAs (Fintype (Fin lv.s → K × K))
  | .opening _ _ _ _ => inferInstanceAs (Fintype K)
  | .fold lv rest _ r _ _ _ _ _ _ _ => FoldChal.instFintype K lv r rest
  | .boundary lv _ _ _ _ _ _ _ _ _ _ _ _ => inferInstanceAs (Fintype ((Fin lv.t → lv.D) × K))
  | .tail r _ _ _ _ _ _ => TailChal.instFintype K r
  | .done _ _ _ => inferInstanceAs (Fintype PUnit)

/-- **The model of Protocol 4.2 of the paper** with the tail `T` and `J` input claims, as a
public-coin transition system. A run starts at a position `commit lv rest`, where `lv :: rest` is
the ladder of levels. -/
noncomputable def protocolD (J : ℕ) : PublicCoin where
  Pos := Pos K
  Msg := Msg K T J
  Chal := Chal K
  chalFintype := Chal.instFintype K
  next := next K T J

variable {K T}

/-- The threshold `Θ` of the triple count of Definition 4.8 of the paper:
`K₀ (K₀ - 1) (K₀ - M)`. -/
abbrev tripleThr (K₀ M : ℕ) : ℕ := K₀ * (K₀ - 1) * (K₀ - M)

variable (τ : ℚ) (K₀ M : ℕ)

/-- **The state function** of Section 5.3 of the paper, for its canonical predicate.

- Before the points: nothing (the levels satisfy the standing assumptions).
- After the points of level 0: they are good for the committed word.
- At a `fold` position: the full state, `(I)` relativised to "does not descend to a tuple that
  satisfies the relation" and `(G)`, the potential of the level's points below one.
- At a `boundary`: `(I_{i,ℓ_i})` of the level that ended, and the new points are good for the new
  word.
- In the tail: a check has failed, or the sumcheck claim on the current tables is false, or the
  final polynomial descends (below).
- At the end: the verifier has rejected, or the final polynomial descends to a member of the
  level-0 list that matches the commit-phase answers and satisfies all input claims.

Each condition also records that the remaining levels satisfy the standing assumptions and that
a tuple that descends witnesses `tru`. -/
def doomed : Pos K → Prop
  | .commit lv rest => ∀ l ∈ lv :: rest, l.OK M
  | .opening lv rest O z => (∀ l ∈ lv :: rest, l.OK M) ∧
      Good τ lv.D lv.d lv.thr lv.s (tripleThr K₀ M) lv.ℓ O z
  | .fold lv rest k r O z v W σ G tru => (∀ l ∈ lv :: rest, l.OK M) ∧ (∀ P, G P → tru) ∧
      FullState τ lv.D lv.d lv.thr lv.s (tripleThr K₀ M) k r O z v W σ (fun U => ¬ G U)
  | .boundary lv k O z v W σ G tru lv' rest h z' => lv.OK M ∧ (∀ l ∈ lv' :: rest, l.OK M) ∧
      (∀ P, G P → tru) ∧ Doomed lv.D O lv.d (lv.thr k) (fun _ => 0) z v W σ (fun U => ¬ G U) ∧
      Good τ lv'.D lv'.d lv'.thr lv'.s (tripleThr K₀ M) lv'.ℓ h.O' z'
  | .tail _ Wt ft σ ok ext tru => (ext → tru) ∧ (ext ∨ ¬ ok ∨ ∑ x, Wt x * ft x ≠ σ)
  | .done acc ext tru => (ext → tru) ∧ ¬ (acc ∧ ¬ ext)

/-- The error of the point message of a level (row M0 of Theorem 5.2 of the paper, one batch). -/
noncomputable def errPoints (lv : Level K) : ℚ :=
  ((lv.L.choose 2 : ℚ) + (lv.L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 / (tripleThr K₀ M : ℕ) *
      ∑ j ∈ range lv.ℓ, τ⁻¹ ^ j) * (((lv.d + 2 ^ lv.ℓ - 1 : ℕ) : ℚ) / Fintype.card K) ^ lv.s

/-- The error of a fold challenge with `r` further rounds of the level to come (row M2):
`(K₀ - 1)/q^2 + τ`, and `(K₀ - 1)/q^2` in the last round. -/
noncomputable def errFold (K : Type) [Fintype K] (τ : ℚ) (K₀ r : ℕ) : ℚ :=
  ((K₀ : ℚ) - 1) / (Fintype.card K : ℚ) ^ 2 + if r = 0 then 0 else τ

/-- The query term `((A - 1)/n)^t` at the agreement `A = thr k` (rows M3 and M4). -/
noncomputable def errQuery (lv : Level K) (k : ℕ) : ℚ :=
  (((lv.thr k - 1 : ℕ) : ℚ) / (lv.D.card : ℚ)) ^ lv.t

/-- **The errors of Theorem 5.2 of the paper**, one for the verifier message sent from each
position. -/
noncomputable def err (J : ℕ) : Pos K → ℚ
  | .commit lv _ => errPoints τ K₀ M lv
  | .opening _ _ _ _ => ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ)
  | .fold lv rest k r _ _ _ _ _ _ _ =>
      match r, rest with
      | r + 1, _ => errFold K τ K₀ r
      | 0, [] => errQuery lv k
      | 0, lv' :: _ => errPoints τ K₀ M lv'
  | .boundary lv k _ _ _ _ _ _ _ _ _ _ _ =>
      errQuery lv k + ((lv.s + lv.t : ℕ) : ℚ) / (Fintype.card K : ℚ)
  | .tail r _ _ _ _ _ _ =>
      match r with
      | _ + 1 => 2 / (Fintype.card K : ℚ)
      | 0 => 0
  | .done _ _ _ => 0

/-- The run starts before the commitment, on a ladder that satisfies the standing assumptions. -/
def start : Pos K → Prop
  | .commit lv rest => ∀ l ∈ lv :: rest, l.OK M
  | _ => False

/-- **The winning condition**: the protocol has ended, the verifier has accepted, and it is not
the case that both the final polynomial descends to a member of the level-0 list that matches
the commit-phase answers and satisfies all input claims (`ext`), and such a member exists
(`tru`). -/
def win : Pos K → Prop
  | .done acc ext tru => acc ∧ ¬ (ext ∧ tru)
  | _ => False

/-- Plain soundness: the verifier has accepted although the input claims are false, that is, no
member of the level-0 list matches the commit-phase answers and satisfies all input claims. -/
def winPlain : Pos K → Prop
  | .done acc _ tru => acc ∧ ¬ tru
  | _ => False

/-- Knowledge soundness: the verifier has accepted and the descent from the final polynomial does
not reach a member of the level-0 list that matches the answers and satisfies all claims. -/
def winExtract : Pos K → Prop
  | .done acc ext _ => acc ∧ ¬ ext
  | _ => False

omit [Fintype K] in
theorem winPlain_le (s : Pos K) (h : winPlain s) : win s := by
  cases s <;> first | exact h | exact ⟨h.1, fun hc => h.2 hc.2⟩

omit [Fintype K] in
theorem winExtract_le (s : Pos K) (h : winExtract s) : win s := by
  cases s <;> first | exact h | exact ⟨h.1, fun hc => h.2 hc.1⟩

section Steps

variable {τ K₀ M}

/-- If `a` holds, "not (`a` and `p`)" is no more likely than "not `p`". -/
theorem dens_not_and_le {α : Type*} [Fintype α] {a : Prop} (ha : a) (p : α → Prop) :
    dens (fun c => ¬ (a ∧ p c)) ≤ dens (fun c => ¬ p c) :=
  Protocol.dens_mono fun _ h hp => h ⟨ha, hp⟩

/-- M0 at level 0: the points after the first commitment. -/
theorem step_commit (hτ : 0 < τ) (hΘ : 0 < tripleThr K₀ M) (lv : Level K)
    (rest : List (Level K)) (hOK : ∀ l ∈ lv :: rest, l.OK M) (O : Word K lv.ℓ) :
    dens (fun z : Fin lv.s → K × K => ¬ doomed τ K₀ M (.opening lv rest O z)) ≤
      errPoints τ K₀ M lv := by
  have h := hOK lv (List.mem_cons_self ..)
  exact (dens_not_and_le hOK _).trans
    (Protocol.dens_not_good_le hτ.le hΘ h.ell_pos h.listBound O)

/-- M1: the batching challenge. -/
theorem step_opening (lv : Level K) (rest : List (Level K)) (O : Word K lv.ℓ)
    (z : Fin lv.s → K × K) (hd : doomed τ K₀ M (.opening lv rest O z)) {J : ℕ}
    (p : OpenMsg K lv J) :
    dens (fun l : K => ¬ doomed τ K₀ M (.fold lv rest 0 lv.ℓ O z p.y (batchW p.Wk l)
        (batchC p.ck l) (claimsHold lv O z p) (∃ U, claimsHold lv O z p U))) ≤
      ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  obtain ⟨hOK, hgood⟩ := hd
  refine ((dens_not_and_le hOK _).trans (dens_not_and_le (fun P hP => ⟨P, hP⟩) _)).trans
    (batch_full O hgood p.y p.Wk p.ck (fun U => ¬ claimsHold lv O z p U) ?_)
  intro U hU hB hpt
  by_contra hcon
  exact hB ⟨hU, hpt, fun k => not_not.mp fun hk => hcon ⟨k, hk⟩⟩

/-- M2: a fold challenge. -/
theorem step_fold [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M) (lv : Level K)
    (rest : List (Level K)) (k r : ℕ) (O : Word K (r + 1)) (z : Fin lv.s → K × K)
    (v : Fin lv.s → K) (W : (Lane (r + 1) → K[X]) →ₗ[K] K) (σ : K)
    (G : (Lane (r + 1) → K[X]) → Prop) (tru : Prop)
    (hd : doomed τ K₀ M (.fold lv rest k (r + 1) O z v W σ G tru)) (p : FoldAns K lv.s) :
    dens (fun c : K × K => ¬ doomed τ K₀ M (.fold lv rest (k + 1) r (foldW O c) z
        (foldVal (2 ^ k) z v p.φ c) (foldWeight W c) (foldClaim σ p.vG p.vF p.σ₀ p.σ₁ c)
        (descend lv.D lv.d (lv.thr (k + 1)) O c G) tru)) ≤ errFold K τ K₀ r := by
  obtain ⟨hOK, hinv, hfull⟩ := hd
  have h := hOK lv (List.mem_cons_self ..)
  refine (Protocol.dens_mono ?_).trans
    (fold_full hτ hMq h.choose_le (h.thr_step k) O z v W σ (fun U => ¬ G U) hfull p.vG p.vF p.σ₀
      p.σ₁ p.φ)
  intro c hc hfs
  refine hc ⟨hOK, fun P hP => ?_, hfs.mono fun P hP => ?_⟩
  · obtain ⟨_, T, _, hT⟩ := hP
    exact hinv T hT
  · exact (pull_not_iff lv.D lv.d (lv.thr (k + 1)) O c G P).mpr hP

/-- M4: the queries of the last level. -/
theorem step_final (lv : Level K) (k : ℕ) (O : Word K 0) (z : Fin lv.s → K × K)
    (v : Fin lv.s → K) (W : (Lane 0 → K[X]) →ₗ[K] K) (σ : K) (G : (Lane 0 → K[X]) → Prop)
    (tru : Prop) (hd : doomed τ K₀ M (.fold lv [] k 0 O z v W σ G tru))
    (p : FinalMsg K T lv W) :
    dens (fun x : Fin lv.t → lv.D => ¬ doomed (K := K) τ K₀ M (.tail T.ν (T.wtab W p.P)
        (T.ftab W p.P) σ
        ((∀ m, p.P.eval (z m).2 = v m) ∧ ∀ q, p.P.eval (x q : K) = O (x q) default)
        (G (fun _ => p.P)) tru)) ≤ errQuery lv k := by
  obtain ⟨_, hinv, hfull⟩ := hd
  refine (Protocol.dens_mono ?_).trans
    (final_full lv.D lv.d (lv.thr k) O z v W σ (fun U => ¬ G U) hfull.1 p.P p.hdeg lv.t)
  intro x hx
  by_contra hcon
  refine hx ⟨hinv _, ?_⟩
  by_contra hcon2
  rcases not_or.mp hcon2 with ⟨hext, h2⟩
  rcases not_or.mp h2 with ⟨hok, hsum⟩
  have hok' := not_not.mp hok
  exact hcon ⟨hok'.1, hok'.2, p.hspec.trans (not_not.mp hsum), hext⟩

/-- M5: a round of the tail sumcheck. -/
theorem step_tail (r : ℕ) (Wt ft : Lane (r + 1) → K) (σ : K) (ok ext tru : Prop)
    (hd : doomed (K := K) τ K₀ M (.tail (r + 1) Wt ft σ ok ext tru)) (h : K[X])
    (hh : h.natDegree ≤ 2) :
    dens (fun c : K => ¬ doomed (K := K) τ K₀ M (.tail r (tabFold c Wt) (tabFold c ft) (h.eval c)
        (ok ∧ h.eval 0 + h.eval 1 = σ) ext tru)) ≤ 2 / (Fintype.card K : ℚ) := by
  obtain ⟨hinv, hst⟩ := hd
  have hsum : ∑ x : Lane (r + 1), Wt x * ft x = ∑ x : Lane r,
      (Wt (Sum.inl x) * ft (Sum.inl x) + Wt (Sum.inr x) * ft (Sum.inr x)) := by
    rw [Finset.sum_add_distrib]
    exact Fintype.sum_sum_type (fun x : Lane r ⊕ Lane r => Wt x * ft x)
  by_cases hfalse : ∑ x : Lane r,
      (Wt (Sum.inl x) * ft (Sum.inl x) + Wt (Sum.inr x) * ft (Sum.inr x)) ≠ σ
  · have hcount := Rounds.tail_round_transition_density (fun x : Lane r => Wt (Sum.inl x))
      (fun x => Wt (Sum.inr x)) (fun x => ft (Sum.inl x)) (fun x => ft (Sum.inr x)) σ hfalse h hh
    refine (Protocol.dens_mono (p' := fun c : K => h.eval 0 + h.eval 1 = σ ∧
      ∑ x : Lane r, ((1 - c) * Wt (Sum.inl x) + c * Wt (Sum.inr x)) *
        ((1 - c) * ft (Sum.inl x) + c * ft (Sum.inr x)) = h.eval c) ?_).trans ?_
    · intro c hc
      by_contra hcon
      refine hc ⟨hinv, ?_⟩
      by_contra hcon2
      rcases not_or.mp hcon2 with ⟨_, h2⟩
      rcases not_or.mp h2 with ⟨hok, hs⟩
      exact hcon ⟨(not_not.mp hok).2, not_not.mp hs⟩
    · rw [dens_eq_card_div]
      exact hcount
  · refine (dens_of_forall_not fun c hc => hc ⟨hinv, ?_⟩).le.trans (by positivity)
    rcases hst with he | hok | hs
    · exact Or.inl he
    · exact Or.inr (Or.inl fun hok' => hok hok'.1)
    · exact (hs (hsum.trans (not_not.mp hfalse))).elim

/-- The terminal check: the verifier evaluates the two tables, which have no variable left. -/
theorem step_terminal (Wt ft : Lane 0 → K) (σ : K) (ok ext tru : Prop)
    (hd : doomed (K := K) τ K₀ M (.tail 0 Wt ft σ ok ext tru)) :
    doomed (K := K) τ K₀ M (.done (ok ∧ Wt default * ft default = σ) ext tru) := by
  obtain ⟨hinv, hst⟩ := hd
  refine ⟨hinv, fun hacc => ?_⟩
  rcases hst with he | hok | hs
  · exact hacc.2 he
  · exact hok hacc.1.1
  · rw [Fintype.sum_unique] at hs
    exact hs hacc.1.2

/-- M0 at a later level: the points after the commitment of the next word. The condition of the
level that ended does not involve them. -/
theorem step_handover (hτ : 0 < τ) (hΘ : 0 < tripleThr K₀ M) (lv : Level K) (k : ℕ)
    (O : Word K 0) (z : Fin lv.s → K × K) (v : Fin lv.s → K) (W : (Lane 0 → K[X]) →ₗ[K] K)
    (σ : K) (G : (Lane 0 → K[X]) → Prop) (tru : Prop) (lv' : Level K) (rest : List (Level K))
    (hd : doomed τ K₀ M (.fold lv (lv' :: rest) k 0 O z v W σ G tru))
    (h : Handover K lv lv' W) :
    dens (fun z' : Fin lv'.s → K × K =>
        ¬ doomed τ K₀ M (.boundary lv k O z v W σ G tru lv' rest h z')) ≤
      errPoints τ K₀ M lv' := by
  obtain ⟨hOK, hinv, hfull⟩ := hd
  have h0 := hOK lv (List.mem_cons_self ..)
  have hOK' : ∀ l ∈ lv' :: rest, l.OK M := fun l hl => hOK l (List.mem_cons_of_mem _ hl)
  have h' := hOK' lv' (List.mem_cons_self ..)
  refine (Protocol.dens_mono ?_).trans
    (Protocol.dens_not_good_le hτ.le hΘ h'.ell_pos h'.listBound h.O')
  intro z' hz' hg
  exact hz' ⟨h0, hOK', hinv, hfull.1, hg⟩

/-- M3: the queries of a level that is not the last, with the batching challenge of the next. -/
theorem step_boundary [CharP K 2] (lv : Level K) (k : ℕ) (O : Word K 0) (z : Fin lv.s → K × K)
    (v : Fin lv.s → K) (W : (Lane 0 → K[X]) →ₗ[K] K) (σ : K) (G : (Lane 0 → K[X]) → Prop)
    (tru : Prop) (lv' : Level K) (rest : List (Level K)) (h : Handover K lv lv' W)
    (z' : Fin lv'.s → K × K)
    (hd : doomed τ K₀ M (.boundary lv k O z v W σ G tru lv' rest h z')) (y' : Fin lv'.s → K) :
    dens (fun xl : (Fin lv.t → lv.D) × K => ¬ doomed τ K₀ M (.fold lv' rest 0 lv'.ℓ h.O' z' y'
        (nextW (W ∘ₗ constL (Lane 0)) lv'.low (fun m => (z m).2) (fun q => (xl.1 q : K)) xl.2)
        (nextC σ h.C (fun x => O x default) (fun m => (z m).2) v (fun q => (xl.1 q : K)) xl.2)
        (fun U => G (fun _ => lv'.low U + h.C)) tru)) ≤
      errQuery lv k + ((lv.s + lv.t : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  obtain ⟨h0, hOK', hinv, hI, hgood⟩ := hd
  exact ((dens_not_and_le hOK' _).trans (dens_not_and_le (fun U hU => hinv _ hU) _)).trans
    (query_full lv.D h0.nonempty lv.d (lv.thr k) O z v W σ (fun U => ¬ G U) hI h.O' hgood y'
      lv'.low h.C h.hdeg h.hW lv.t)

end Steps

/-- Properties (ii) and (iii) of the state function: from a doomed position, whatever the prover
sends, the verifier's message leaves the doomed set with probability at most the error of that
message. -/
theorem doomed_step [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) (s : Pos K) (p : Msg K T J s) (hd : doomed τ K₀ M s) :
    dens (fun c : Chal K s => ¬ doomed τ K₀ M (next K T J s p c)) ≤ err τ K₀ M J s := by
  cases s with
  | commit lv rest => exact step_commit hτ hΘ lv rest hd p
  | opening lv rest O z => exact step_opening lv rest O z hd p
  | fold lv rest k r O z v W σ G tru =>
      cases r with
      | succ r => exact step_fold hτ hMq lv rest k r O z v W σ G tru hd p
      | zero =>
          cases rest with
          | nil => exact step_final lv k O z v W σ G tru hd p
          | cons lv' rest => exact step_handover hτ hΘ lv k O z v W σ G tru lv' rest hd p
  | boundary lv k O z v W σ G tru lv' rest h z' =>
      exact step_boundary lv k O z v W σ G tru lv' rest h z' hd p
  | tail r Wt ft σ ok ext tru =>
      cases r with
      | succ r => exact step_tail r Wt ft σ ok ext tru hd p.1 p.2
      | zero => exact (dens_of_forall_not fun c hc => hc (step_terminal Wt ft σ ok ext tru hd)).le
  | done a e t =>
      refine (dens_of_forall_not fun c hc => hc hd).le

/-- Property (iv): at a doomed position the prover has not won. -/
theorem doomed_not_win (s : Pos K) (hd : doomed τ K₀ M s) : ¬ win s := by
  cases s with
  | done a e t =>
      rintro ⟨hacc, hne⟩
      exact hd.2 ⟨hacc, fun he => hne ⟨he, hd.1 he⟩⟩
  | _ => exact fun h => h

/-- Property (i): a starting position is doomed. -/
theorem start_doomed (s : Pos K) (hs : start M s) : doomed τ K₀ M s := by
  cases s with
  | commit lv rest => exact hs
  | _ => exact hs.elim

/-- **The state function of the model** (Theorem 5.2 and Theorem 5.6 of the paper, properties (i)
to (iv) of Section 2.2). Over a finite field of characteristic two, for analysis constants
`τ > 0`, `M ≥ 2q` and `K₀` with `K₀ (K₀ - 1) (K₀ - M) > 0`, `doomed` is a round-by-round state
function of `protocolD` with the errors `err`. -/
theorem protocolD_stateFunction [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) :
    StateFunction (protocolD K T J) (start M) win (err τ K₀ M J) (doomed τ K₀ M)
      (fun s _ => doomed τ K₀ M s) :=
  StateFunction.of_positions (Γ := protocolD K T J) (start_doomed τ K₀ M)
    (fun s p hd => doomed_step τ K₀ M hτ hMq hΘ J s p hd) (doomed_not_win τ K₀ M)

/-- **The model of Protocol 4.2 is round-by-round sound with the errors of Theorem 5.2 of the
paper.** -/
theorem protocolD_rbr [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) :
    RBRSound (protocolD K T J) (start M) win (err τ K₀ M J) :=
  ⟨_, _, protocolD_stateFunction (T := T) τ K₀ M hτ hMq hΘ J⟩

end Soundness
