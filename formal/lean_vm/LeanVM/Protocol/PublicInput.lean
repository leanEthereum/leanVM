/-
  LeanVM.Protocol.PublicInput

  The public-input phase: the verifier draws a challenge, the prover sends the values it claims
  for the public columns on the line through their first two cells whose value is sent, and the
  verifier checks those values against the public statement and pools the claims. Both halves
  proved, at the slot and its error.
-/

module

public import LeanVM.Protocol.Spine.Errors
public import LeanVM.Protocol.Spine.Slots
import LeanVM.Protocol.ToCompPoly.Multilinear
import LeanVM.Protocol.ToVCVio.UniformSample
import Mathlib.Algebra.CharP.Two

/-!
# The public-input phase

Specification §8.2 (`doc/leanvm/body/08-end-to-end-protocol.tex:27-37`, and the paragraph
"Public input" of the unrolled protocol, `:84-89`, at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`): the public input is the first two memory cells,
both parties know them, and

1. the verifier samples `r ∈ E`;
2. the verifier computes `c_ℓ = (1 + r)·mem[g⁰]_ℓ + r·mem[g¹]_ℓ` for each memory limb `ℓ`, the
   line through the statement's two cells, and pools the `c_ℓ` as claims on the three memory
   limbs at `(r, 0, …, 0)`. The prover sends nothing.

Over an abstract instance the memory limbs are the instance's public lines, columns whose cells
0 and 1 the statement fixes; each line says whether its value is sent. The prover sends the
values of the lines that are, in order, as one message. The verifier rejects a message that
does not have one value per sent line, checks the rest against the lines' values, and pools one
claim per line: for a line whose value was sent, at the value *sent*, read off the message
(`pooledFrom`), and for the others at the value the verifier computes. Pooling the values sent
is what makes the check load-bearing: a verifier that pooled the values it computes would be
knowledge sound with no check at all. The length is not a check that can be dropped: a pool
exists only for a message of that length (`pooledFrom` takes the proof), so no weakened check
pools a value the prover did not send. When the check passes the verdict is the computed pool
(`verdict_pooledFrom_of_check`), and the proofs reason about that one, `pooled`. The verifier
reads the transcript and never the stack: it is a front verifier, `verifierWith` at the check
and the pool, a shape the tests reuse for the verifiers that omit or weaken the check.

The leanISA instance (`LeanVM.Protocol.LeanIsa`) sends no line, as the deployed verifiers do
(`python-verifier/verifier.py:1390-1396`, `crates/verifier/src/lib.rs:251-264`): its message is
empty, the check is that it is, and every pooled claim is a value the verifier computes. The
specification and the deployed verifiers coincide; an earlier deployed check of one equation on
the two public words, with the two low limbs sent, is gone upstream.

Perfect completeness: on a stack whose lines hold, every pooled claim is true, by the identity
`q̃(r, 0, …, 0) = (1 - r)·q(0) + r·q(1)` and `-1 = 1` in `E`. Knowledge soundness at `1/|E|`,
the slot's error: the extractor keeps the trivial witness, since the stack is the oracle; if the
pooled claims hold and some line's cells differ from the statement's, that line's claim is a
nonzero polynomial of degree one in `r`, true at one challenge at most, whatever the number of
lines.

Written from the specification.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

namespace PublicInput

/-! ## The line through cells 0 and 1 -/

/-- The point `(r, 0, …, 0)` of `E^n`, at which §8.2 evaluates the memory limbs. -/
def linePoint {n : ℕ} (hn : 0 < n) (r : E) : Vector E n :=
  Vector.cast (by omega : 1 + (n - 1) = n) (#v[r] ++ Vector.replicate (n - 1) (0 : E))

/-- The extension of a column on the line through its cells 0 and 1:
`q̃(r, 0, …, 0) = (1 - r)·q(0) + r·q(1)`. The zero coordinates select the first two cells, and
the first coordinate interpolates between them. -/
theorem eval₂Mle_linePoint {n : ℕ} (hn : 0 < n) (q : CMlPolynomialEval K n) (r : E) :
    CMlPolynomialEval.eval₂Mle q (algebraMap K E) (linePoint hn r) =
      (1 - r) * ofK (q.get ⟨0, Nat.two_pow_pos n⟩) +
        r * ofK (q.get ⟨1, Nat.one_lt_two_pow hn.ne'⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : 1 + m = m + 1 := Nat.add_comm 1 m
  -- The column as a table on `1 + m` variables, and the point as `(r)` followed by `m` zeros.
  have hq : CMlPolynomialEval.eval₂Mle q (algebraMap K E) (linePoint hn r) =
      CMlPolynomialEval.eval₂Mle
        (Vector.cast (congrArg (2 ^ ·) h) (Vector.cast (congrArg (2 ^ ·) h.symm) q))
        (algebraMap K E) (Vector.cast h (#v[r] ++ Vector.replicate m (0 : E))) := by
    simp only [linePoint, Nat.add_one_sub_one, Vector.cast_cast, Vector.cast_rfl]
  -- The zero coordinates select the slice at index zero; one variable is left.
  rw [hq, eval₂Mle_cast (algebraMap K E) h, CMlPolynomialEval.eval₂Mle, ← boolVec_zero,
    evalMle_append_boolVec, CMlPolynomialEval.evalMle_succ, CMlPolynomialEval.evalMle_zero,
    CMlPolynomialEval.evalMleLayer_get]
  simp only [Vector.head, Nat.reduceAdd, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, Nat.reducePow, slice, CMlPolynomialEval.map,
    Extension.Ext.algebraMap_eq_ofBase, cubeIndex, pow_one, mul_zero, add_zero, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_cast, Fin.zero_eta, Fin.isValue, Vector.get_eq_getElem,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, Vector.getElem_ofFn, zero_add, Fin.mk_one, Nat.mod_succ,
    Fin.mk_zero']

/-! ## Values, check and claims -/

variable (I : M3Instance)

/-- The value of a public line at the challenge `r`: the line through the statement's two
cells, `(1 + r)·cell0 + r·cell1`. -/
def lineValue (r : E) (l : PublicLine I.toShape) : E :=
  (1 + r) * ofK l.cell0 + r * ofK l.cell1

/-- The claim that a line's column takes the line's value at `(r, 0, …, 0)`. -/
def lineClaim (r : E) (l : PublicLine I.toShape) : ColumnClaim I :=
  ⟨l.col, linePoint l.pos r, lineValue I r l⟩

/-- What the verifier pools: the claims it received, then one claim per public line. -/
def pooled (s : I.Stmt × TableOut I) (r : E) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ (I.publicLines s.1).map (lineClaim I r)⟩)

/-- The values the verifier expects in the prover's message: the values at the challenge of the
lines whose value is sent, in order. -/
def expectedValues (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).toList.filter (·.sent)).map (lineValue I r)

/-- The verifier's check: the prover's message is the expected values. -/
def check (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs = expectedValues I s.1 r)

private theorem check_eq_true_iff (s : I.Stmt × TableOut I) (r : E) (cs : List E) :
    check I s r cs = true ↔ cs = expectedValues I s.1 r :=
  decide_eq_true_iff

/-- The number of lines whose value is sent: the length of the prover's message. -/
def sentCount {n : ℕ} (ls : Vector (PublicLine I.toShape) n) : ℕ :=
  (ls.toList.filter (·.sent)).length

/-- The expected values are one per sent line. -/
theorem expectedValues_length (input : I.Stmt) (r : E) :
    (expectedValues I input r).length = sentCount I (I.publicLines input) :=
  List.length_map ..

/-- The number of lines before line `i` whose value is sent: the position of line `i`'s value
in the message, when it is sent. -/
def sentBefore {n : ℕ} (ls : Vector (PublicLine I.toShape) n) (i : Fin n) : ℕ :=
  ((ls.toList.take i.val).filter (·.sent)).length

/-- In a filtered list, the element that comes from position `i` of the original sits at the
number of kept elements before `i`. -/
private theorem getElem?_filter_length_take {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length), p l[i] = true →
      (l.filter p)[((l.take i).filter p).length]? = some l[i]
  | [], i, hi, _ => absurd hi (Nat.not_lt_zero i)
  | a :: _, 0, _, h => by
    have ha : p a = true := by simpa using h
    simp [ha]
  | a :: l, i + 1, hi, h => by
    have ih := getElem?_filter_length_take p l i (Nat.lt_of_succ_lt_succ hi) (by simpa using h)
    by_cases hpa : p a = true
    · simp [hpa, ih]
    · simp [hpa, ih]

/-- A sent line's position is inside a message with one value per sent line. -/
theorem sentBefore_lt {n : ℕ} (ls : Vector (PublicLine I.toShape) n) (i : Fin n)
    (hs : ls[i].sent = true) : sentBefore I ls i < sentCount I ls :=
  (List.getElem?_eq_some_iff.mp (getElem?_filter_length_take
    (fun l : PublicLine I.toShape ↦ l.sent) ls.toList i.val (by simp) (by simpa using hs))).1

/-- The claims built from a message with one value per sent line, one per line, on the line's
column at `(r, 0, …, 0)`: a line whose value is sent takes it from the message, at its position
among the sent lines, and an unsent line takes `unsent` of it. -/
def claimsWith (r : E) (unsent : PublicLine I.toShape → E) {n : ℕ}
    (ls : Vector (PublicLine I.toShape) n) (cs : List E) (h : cs.length = sentCount I ls) :
    Vector (ColumnClaim I) n :=
  Vector.ofFn fun i ↦
    ⟨ls[i].col, linePoint ls[i].pos r,
      if hs : ls[i].sent then
        cs[sentBefore I ls i]'(lt_of_lt_of_eq (sentBefore_lt I ls i hs) h.symm)
      else unsent ls[i]⟩

/-- The claims from the message: an unsent line takes the value the verifier computes. -/
abbrev claimsFrom (r : E) {n : ℕ} (ls : Vector (PublicLine I.toShape) n) (cs : List E)
    (h : cs.length = sentCount I ls) : Vector (ColumnClaim I) n :=
  claimsWith I r (lineValue I r) ls cs h

/-- What the verifier pools from a message with one value per sent line: the claims it
received, then one claim per public line, from the values sent. No pool exists for another
message. -/
def pooledFrom (s : I.Stmt × TableOut I) (r : E) (cs : List E)
    (h : cs.length = sentCount I (I.publicLines s.1)) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ claimsFrom I r (I.publicLines s.1) cs h⟩)

/-- The claims from the expected values are the lines' claims: the value sent for a line is
its line value. -/
private theorem claimsFrom_expected (r : E) (input : I.Stmt)
    (h : (expectedValues I input r).length = sentCount I (I.publicLines input)) :
    claimsFrom I r (I.publicLines input) (expectedValues I input r) h =
      (I.publicLines input).map (lineClaim I r) := by
  apply Vector.ext
  intro i hi
  simp only [claimsFrom, claimsWith, Vector.getElem_ofFn, Vector.getElem_map, lineClaim,
    Fin.getElem_fin]
  split_ifs with hsent
  · congr 1
    simp only [expectedValues, sentBefore]
    rw [List.getElem_eq_iff, List.getElem?_map,
      getElem?_filter_length_take (fun l : PublicLine I.toShape ↦ l.sent)
        (I.publicLines input).toList i (by simpa using hi) (by simpa using hsent)]
    simp
  · rfl

/-- The pool from the expected values is the pool of the lines' claims. -/
theorem pooledFrom_expected (s : I.Stmt × TableOut I) (r : E)
    (h : (expectedValues I s.1 r).length = sentCount I (I.publicLines s.1)) :
    pooledFrom I s r (expectedValues I s.1 r) h = pooled I s r := by
  simp only [pooledFrom, pooled, claimsFrom_expected]

/-- A claim is in the pool exactly when it was received or is a line's claim. -/
private theorem mem_pooled (s : I.Stmt × TableOut I) (r : E) (c : ColumnClaim I) :
    c ∈ (pooled I s r).2.columns.toList ↔
      c ∈ s.2.columns.toList ∨ ∃ l ∈ (I.publicLines s.1).toList, lineClaim I r l = c := by
  simp only [pooled, Vector.toList_append, Vector.toList_map, List.mem_append, List.mem_map]

/-- A line's claim holds of the stack exactly when the line through the stack's two cells,
evaluated at `r`, is the line through the statement's. -/
private theorem lineClaim_holds_iff (q : Column I.μ) (r : E) (l : PublicLine I.toShape) :
    (lineClaim I r l).Holds q ↔
      (1 - r) * ofK ((I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩) +
          r * ofK ((I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩) =
        (1 + r) * ofK l.cell0 + r * ofK l.cell1 := by
  unfold ColumnClaim.Holds lineClaim
  rw [eval₂Mle_linePoint l.pos]
  exact Iff.rfl

/-- Two lines through cells in `K` that differ agree at one challenge at most: the difference is
a polynomial of degree one in `r` with a nonzero coefficient. -/
private theorem line_challenge_unique {a b c0 c1 : K} (hne : ¬ (a = c0 ∧ b = c1)) {r₁ r₂ : E}
    (h₁ : (1 - r₁) * ofK a + r₁ * ofK b = (1 + r₁) * ofK c0 + r₁ * ofK c1)
    (h₂ : (1 - r₂) * ofK a + r₂ * ofK b = (1 + r₂) * ofK c0 + r₂ * ofK c1) : r₁ = r₂ := by
  have e₁ : (ofK a - ofK c0) + r₁ * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
    linear_combination h₁
  have e₂ : (ofK a - ofK c0) + r₂ * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
    linear_combination h₂
  by_cases hβ : ofK b - ofK a - ofK c0 - ofK c1 = 0
  · exfalso
    apply hne
    have hα : ofK a = ofK c0 := by
      rw [hβ, mul_zero, add_zero, sub_eq_zero] at e₁
      exact e₁
    refine ⟨ofK_injective hα, ofK_injective ?_⟩
    have hb : ofK b = ofK c0 + ofK c0 + ofK c1 := by linear_combination hβ + hα
    rw [hb, CharTwo.add_self_eq_zero, zero_add]
  · have h : (r₁ - r₂) * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
      linear_combination e₁ - e₂
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hβ)

/-- On a stack in the table seam, the pool is in the public seam: the received claims still
hold, and each line's claim holds by the line identity. -/
private theorem pooled_mem_pub (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (h : ((s, o), ()) ∈ Seam.table I) (r : E) : ((pooled I s r, o), ()) ∈ Seam.pub I := by
  obtain ⟨hcols, hlines, haux⟩ := h
  refine ⟨fun c hc ↦ ?_, haux⟩
  rcases (mem_pooled I s r c).mp hc with hc | ⟨l, hl, rfl⟩
  · exact hcols c hc
  · obtain ⟨h0, h1⟩ := hlines l hl
    rw [lineClaim_holds_iff, h0, h1, CharTwo.sub_eq_add]

/-- A challenge is bad for a stack and statement outside the table seam when the pool at that
challenge is inside the public seam; two bad challenges are equal. -/
private theorem bad_challenge_unique (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (hin : ((s, o), ()) ∉ Seam.table I) {r₁ r₂ : E}
    (h₁ : ((pooled I s r₁, o), ()) ∈ Seam.pub I)
    (h₂ : ((pooled I s r₂, o), ()) ∈ Seam.pub I) : r₁ = r₂ := by
  obtain ⟨hcols₁, haux⟩ := h₁
  obtain ⟨hcols₂, -⟩ := h₂
  have hold : ∀ c ∈ s.2.columns.toList, c.Holds (theStack o) := fun c hc ↦
    hcols₁ c ((mem_pooled I s r₁ c).mpr (Or.inl hc))
  have hlines : ¬ I.PublicLinesHold s.1 (theStack o) := fun hl ↦ hin ⟨hold, hl, haux⟩
  simp only [M3Instance.PublicLinesHold, not_forall] at hlines
  obtain ⟨l, hl, hne⟩ := hlines
  have hc₁ := hcols₁ _ ((mem_pooled I s r₁ _).mpr (Or.inr ⟨l, hl, rfl⟩))
  have hc₂ := hcols₂ _ ((mem_pooled I s r₂ _).mpr (Or.inr ⟨l, hl, rfl⟩))
  rw [lineClaim_holds_iff] at hc₁ hc₂
  exact line_challenge_unique hne hc₁ hc₂

/-! ## The verifier's verdict -/

variable (accept : (I.Stmt × TableOut I) → E → List E → Bool)
  (pool : (s : I.Stmt × TableOut I) → E → (cs : List E) →
    cs.length = sentCount I (I.publicLines s.1) → I.Stmt × PubOut I)

/-- The check of a verifier of the phase's shape, as one Boolean: the message has one value
per sent line, and `accept` holds of it at the challenge. -/
def accepts (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs.length = sentCount I (I.publicLines s.1)) && accept s r cs

/-- The verdict of a verifier of the phase's shape: `pool` of a message with one value per
sent line. On any other message the verifier rejects, so the value here, the computed pool, is
never output. -/
def verdict (s : I.Stmt × TableOut I) (r : E) (cs : List E) : I.Stmt × PubOut I :=
  if h : cs.length = sentCount I (I.publicLines s.1) then pool s r cs h else pooled I s r

/-- The verifier's check holds exactly when the specification's check does: that check fixes
the length. -/
theorem accepts_check_iff (s : I.Stmt × TableOut I) (r : E) (cs : List E) :
    accepts I (check I) s r cs = true ↔ check I s r cs = true := by
  unfold accepts
  rw [Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨And.right, fun hc ↦
    ⟨by rw [(check_eq_true_iff I s r cs).mp hc, expectedValues_length], hc⟩⟩

/-- When the check passes, the verdict is the pool of the lines' claims. -/
theorem verdict_pooledFrom_of_check {s : I.Stmt × TableOut I} {r : E} {cs : List E}
    (hc : check I s r cs = true) : verdict I (pooledFrom I) s r cs = pooled I s r := by
  have hl : cs.length = sentCount I (I.publicLines s.1) := by
    rw [(check_eq_true_iff I s r cs).mp hc, expectedValues_length]
  rw [verdict, dite_eq_left hl]
  obtain rfl := (check_eq_true_iff I s r cs).mp hc
  exact pooledFrom_expected I s r hl

/-! ## The phase -/

/-- The verdict of a verifier of the phase's shape on a branch path: `pool` of the values sent,
if `accept` passes. -/
def verdictWith (s : I.Stmt × TableOut I) (p : pubTree.BranchPath) :
    Option (I.Stmt × PubOut I) :=
  if accepts I accept s p.1 p.2.1 then some (verdict I pool s p.1 p.2.1) else none

/-- A message that passes `accept` is pooled. -/
theorem verdictWith_of_accepts {s : I.Stmt × TableOut I} {r : E} {cs : List E}
    (h : accepts I accept s r cs = true) :
    verdictWith I accept pool s ⟨r, cs, PUnit.unit⟩ = some (verdict I pool s r cs) := by
  simp [verdictWith, h]

/-- A message that fails `accept` is rejected. -/
theorem verdictWith_of_reject {s : I.Stmt × TableOut I} {r : E} {cs : List E}
    (h : accepts I accept s r cs = false) : verdictWith I accept pool s ⟨r, cs, PUnit.unit⟩ = none := by
  simp [verdictWith, h]

/-- A component of the phase's shape: the honest prover, a verifier with `accept` and `pool`. -/
def phaseWith :
    Typed.Def (TheOracle I) (I.Stmt × TableOut I) Unit (I.Stmt × PubOut I) Unit pubSlot where
  verdict := verdictWith I accept pool
  prover := fun so w r ↦ pure (pure ⟨expectedValues I so.1.1 r, ((pooled I so.1 r, so.2), w)⟩)

/-- The verdict on a branch path: the pool from the values sent, if the check passes. -/
def verdictT (s : I.Stmt × TableOut I) (p : pubTree.BranchPath) : Option (I.Stmt × PubOut I) :=
  if accepts I (check I) s p.1 p.2.1 then some (verdict I (pooledFrom I) s p.1 p.2.1) else none

/-- The public-input phase as a typed component: the honest prover sends the expected values at
the challenge and outputs the pool. -/
def phase : Typed.Def (TheOracle I) (I.Stmt × TableOut I) Unit (I.Stmt × PubOut I) Unit pubSlot where
  verdict := verdictT I
  prover := fun so w r ↦ pure (pure ⟨expectedValues I so.1.1 r, ((pooled I so.1 r, so.2), w)⟩)

/-- **Completeness on the typed framework**: from the table seam, the prover's values pass the
check at every challenge and the pool lands in the public seam. -/
theorem complete : Typed.Complete (phase I) (Seam.table I) (Seam.pub I) := by
  rintro s o w hin ⟨r, cs, ⟨⟩⟩ a ⟨-, rest, hrest, rest', hrest', rfl⟩
  have hrest := (mem_support_pure_iff _ _).mp hrest
  subst hrest
  have hrest' := (mem_support_pure_iff _ _).mp hrest'
  obtain ⟨hcs, hrest'⟩ := Sigma.mk.inj_iff.mp hrest'
  change cs = expectedValues I s.1 r at hcs
  subst hcs
  obtain rfl := eq_of_heq hrest'
  have hc : check I s r (expectedValues I s.1 r) = true := decide_eq_true rfl
  refine ⟨?_, rfl, ?_⟩
  · change verdictT I s ⟨r, expectedValues I s.1 r, PUnit.unit⟩ = _
    simp only [verdictT, (accepts_check_iff I _ _ _).mpr hc, ite_true,
      verdict_pooledFrom_of_check I hc]
  · cases w
    exact pooled_mem_pub I s o hin r

/-- The backward witness maps: the table seam before the challenge; after it, the public seam of
the pool; after the values, that the check passes and the verdict is in the public seam. -/
def extractor (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i) :
    Interaction.Oracle.Security.RoundExtractor pubTree
      (Typed.inState (TheOracle I) (Seam.table I) s o) :=
  fun r ↦ ⟨⟨Unit, fun _ ↦ ((pooled I s r, o), ()) ∈ Seam.pub I⟩, id, fun cs ↦
    ⟨⟨Unit, fun _ ↦ accepts I (check I) s r cs = true ∧
      ((verdict I (pooledFrom I) s r cs, o), ()) ∈ Seam.pub I⟩, id, PUnit.unit⟩⟩

/-- **Round-by-round knowledge soundness on the typed framework**, at the slot's error `1/|E|`:
a bad transition is a bad challenge, and there is at most one; the values sent that pass the
check carry the public seam back to the pool. -/
def security : Typed.Security (phase I) (Seam.table I) (Seam.pub I) pubErrors where
  extractor := extractor I
  prover_preserving s o := ⟨fun _ h ↦ (nomatch h), fun r ↦ ⟨fun cs _ _ h ↦ by
    obtain ⟨hc, hp⟩ := h
    rw [verdict_pooledFrom_of_check I ((accepts_check_iff I _ _ _).mp hc)] at hp
    exact hp, fun _ ↦ trivial⟩⟩
  local_bound s o := by
    refine ⟨?_, fun _ ↦ fun _ ↦ trivial⟩
    rw [_root_.RoundByRound.GameFamily.isBounded_iff]
    intro _ _
    change Pr{let r ← $ᵗ E}[∃ w : Unit, ¬ ((s, o), w) ∈ Seam.table I ∧
      ((pooled I s r, o), ()) ∈ Seam.pub I] ≤ ((overE 1 : ℝ≥0) : ℝ≥0∞)
    rw [overE, Nat.cast_one]
    refine le_trans (prEvent_mono _ _ _ ?_) (prEvent_uniformSample_le_of_subsingleton (α := E)
      (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
      fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
    rintro r ⟨w, hin, hout⟩
    cases w
    exact ⟨hin, hout⟩
  terminal s o :=
    { witnessEquiv := fun _ ↦ Equiv.refl Unit
      knowledge_iff := fun path w ↦ by
        cases w
        change (accepts I (check I) s path.1 path.2.1 = true ∧
            ((verdict I (pooledFrom I) s path.1 path.2.1, o), ()) ∈ Seam.pub I) ↔
          ∃ t, verdictT I s ⟨path.1, path.2.1, PUnit.unit⟩ = some t ∧ ((t, o), ()) ∈ Seam.pub I
        simp only [verdictT]
        by_cases hc : accepts I (check I) s path.1 path.2.1 = true
        · simp [hc]
        · simp [hc] }

end PublicInput

end
end LeanVM.Protocol
