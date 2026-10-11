import Whir.WHIRCallerPrefix
import Whir.SamplingProbability

/-! PCS-only raw-message adapter for the chronological operations audited at
`8a7afbd01e592f2058f348852daa0f428d411e64`: stack/ring_switch initial
sampling and whir/verify.rs:461–469, whir/mod.rs:111–132. The existing
modeled wire compiler is reused, not asserted to be a universal Rust refinement.
The first message is gamma, six map draws, lambda; query messages retain every
full E squeeze before projection and the adjacent lambda. The book's raw
alphabet lower bound is 192, independently of the 256-bit Merkle/mode terms.
This is an IOP message adapter, not an application of the book's compiler theorem
or a whole-VM entropy/security theorem. -/
namespace Whir.PCSBCSRounds
open Concrete Protocol CausalGame CausalProbability WHIRHistory
open scoped BigOperators

noncomputable instance {c : Config} (q : Coordinate c) : Fintype (StackSample q) := by
  cases q <;> unfold StackSample Sample <;> infer_instance

/-- The actual dependent raw verifier alphabet, with the initial group replaced,
not followed by a second initial round. -/
abbrev Raw {c : Config} (q : Coordinate c) := StackSample q

def rawWidth {c : Config} (q : Coordinate c) : Nat := stackScalarCount q

/-- Exact number of book-style verifier messages, including the last tail draw. -/
def k (c : Config) : Nat := Fintype.card (Coordinate c)

/-- Exact maximal verifier message length in bits, before projection. -/
def rmax (c : Config) : Nat :=
  192 * ((schedule c).map rawWidth).foldl max 0

@[simp] theorem raw_card {c : Config} (q : Coordinate c) :
    Fintype.card (Raw q) = (2 ^ 192) ^ rawWidth q := by
  cases q <;> simp only [Raw, StackSample, Sample, rawWidth, stackScalarCount,
    scalarCount, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    FieldModel.card_E, pow_one]
  · norm_num
  · exact (pow_succ (2 ^ 192) _).symm

/-- Every production alphabet has at least 192 raw bits; zero-OOD levels
introduce no coordinate, and existing OOD coordinates have nonempty vectors. -/
theorem raw_entropy192 (p : ParameterBounds.Profile)
    (q : Coordinate (ParameterBounds.config p)) :
    2 ^ 192 ≤ Fintype.card (Raw q) := by
  rw [raw_card]
  have positive := (WHIRHistoryKey.production_sample_counts p q).2
  have bound : 1 ≤ rawWidth q := positive
  simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2 ^ 192) bound)

theorem depth_eq_k (c : Config) : depth c = k c := by
  classical
  have all : (schedule c).toFinset = Finset.univ := by
    ext q
    simp [coordinate_mem_schedule q]
  have card := congrArg Finset.card all
  simpa only [List.toFinset_card_of_nodup (schedule_nodup c), Finset.card_univ,
    depth, k] using card

/-- Canonical chronological enumeration: no duplicated initial stage or missing
final draw. Its inverse is the actual causal position. -/
def rounds (c : Config) : Fin (k c) ≃ Coordinate c where
  toFun n := (schedule c)[n.val]'(by change n.val < depth c; rw [depth_eq_k]; exact n.isLt)
  invFun q := ⟨position q, by simpa [depth_eq_k] using position_lt_depth q⟩
  left_inv n := by
    apply Fin.ext
    exact position_schedule_get c ⟨n.val, by rw [depth_eq_k]; exact n.isLt⟩
  right_inv q := by
    have h := schedule_get_position q
    rw [List.getElem?_eq_getElem (position_lt_depth q)] at h
    exact Option.some.inj h

/-- One and only one initial verifier message; its components retain source order. -/
theorem first_message {c : Config} (gamma lambda : E) (maps : Fin 6 → E) :
    stackSampleScalars (c := c) .initial ((gamma,maps),lambda) =
      [gamma] ++ List.ofFn maps ++ [lambda] := rfl

theorem query_message {c : Config} (i : Fin c.folds.size)
    (squeezes : Fin (queryChunks c i.val) → E) (lambda : E) :
    stackSampleScalars (.query i) (squeezes,lambda) =
      List.ofFn squeezes ++ [lambda] := rfl

/-- The source nonce is a prover string and a rejecting transition, not a
small verifier alphabet or an entropy contribution. All rows/intro replies
occur strictly after the complete query/lambda squeeze. -/
theorem query_operations {c : Config} (i : Fin c.folds.size) (bits : Nat)
    (nonce : E) : challengeEvents (.query i) bits nonce =
      [.nonce bits nonce, .squeeze (24 * (queryChunks c i.val + 1))] := rfl

theorem query_before_reply {c : Config} (i : Fin c.folds.size)
    (digests : Nat → FiatShamirGame.Digest32) (bits : Nat → Nat) (nonces : Nat → E)
    (rows : Oracle) (intro : Message E) (qs : List (Coordinate c)) (rs : List Reply) :
    visibleEvents digests bits nonces (.query i :: qs) (.query rows intro :: rs) =
      (visibleEvents digests bits nonces qs rs).map (fun rest =>
        [.nonce (bits i.val) (nonces i.val),
          .squeeze (24 * (queryChunks c i.val + 1)),
          .observe (messageScalars intro)] ++ rest) := by
  simp [visibleEvents, replyScalars, challengeEvents, scalarCount, coordinateLevel]
  cases visibleEvents digests bits nonces qs rs <;> rfl

/-- Projection to the stratified query law, retaining discarded high bits and
unused chunks in the actual raw domain. No iid-query or padding premise. -/
theorem projected_query_law (depth count : Nat) (positive : 0 < depth)
    (bounded : depth ≤ 64) (P : Fin count → Nat → Prop) :
    SamplingProbability.probability
      (fun t : Fin ((count + 192 / depth - 1) / (192 / depth)) → E =>
        ∃ qs, deriveQueries depth count (Array.ofFn t) = some qs ∧
          ∀ i : Fin count, P i qs[i.val]!) =
      ∏ i, SamplingProbability.probability (fun raw : Fin (2 ^ depth) =>
        P i (SamplingProbability.concretePlace count depth i.val raw.val)) :=
  SamplingProbability.deriveQueries_probability depth count positive bounded P

/-- Actual causal replies before the query message do not depend on any of
its full squeezes or its lambda, even on malformed/rejecting branches. -/
theorem query_causality {c : Config} (i : Fin c.folds.size) (t : Tape c)
    (x : Sample (.query i)) (strategy : Strategy) (input : Public) :
    (run strategy input [] (visibleBatches c (set (.query i) t x).1
      (challenges c (set (.query i) t x)))).take (position (.query i)) =
    (run strategy input [] (visibleBatches c t.1 (challenges c t))).take
      (position (.query i)) := response_prefix (.query i) t x strategy input

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All 56 profiles have actual nonempty folds/tails, bounded chunk depth, and
nonempty existing OOD messages; absent OOD points do not create empty rounds. -/
theorem production_edges : ∀ p : ParameterBounds.Profile,
    0 < (ParameterBounds.config p).logN - (ParameterBounds.config p).folds.toList.sum ∧
    ∀ i : Fin (ParameterBounds.config p).folds.size,
      0 < (ParameterBounds.config p).folds[i.val]! ∧
      0 < remaining (ParameterBounds.config p) i.val ∧
      0 < remaining (ParameterBounds.config p) i.val + (ParameterBounds.config p).rates[i.val]! ∧
      remaining (ParameterBounds.config p) i.val + (ParameterBounds.config p).rates[i.val]! ≤ 64 := by
  decide +kernel

#print axioms raw_entropy192
#print axioms depth_eq_k
#print axioms projected_query_law
end Whir.PCSBCSRounds
