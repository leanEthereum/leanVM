import Whir.PCSBCSRounds

/-! Adjacent source squeezes form one book-style verifier message without an
intervening prover string. This proves the actual modeled full-history/byte-cursor
operation and the executable byte loop, rather than assuming seed stretching.
Nonce checking is a prover-message rejection and carries no verifier entropy. -/
namespace Whir.PCSBCSRounds
open Concrete Protocol CausalGame CausalProbability WHIRHistory DuplexRefinement
open scoped BigOperators

/-- Exact canonical-history and byte-cursor grouping, including empty squeezes. -/
theorem model_squeeze_add (m : Model) (a b : Nat) :
    modelSqueeze (modelSqueeze m a) b = modelSqueeze m (a+b) := by
  by_cases ha : a = 0
  · subst a; simp [modelSqueeze]
  by_cases hb : b = 0
  · subst b; simp [modelSqueeze]
  have hab : a+b ≠ 0 := by omega
  have closed : closeRun {closeRun m with consumed := m.consumed+a} =
      {closeRun m with consumed := m.consumed+a} := by
    have empty : ({closeRun m with consumed := m.consumed+a} : Model).run = [] :=
      closeRun_empty m
    rw [closeRun, ite_eq_left empty]
  simp only [modelSqueeze, ha, hb, hab, ↓reduceIte, closed]
  simp only [Nat.add_assoc]

/-- Gamma (24 bytes), six maps (144), lambda (24) share one maximal squeeze.
No prover absorb, transcript reset, or second initial IOP round is inserted. -/
theorem initial_byte_group (m : Model) :
    modelSqueeze (modelSqueeze (modelSqueeze m 24) 144) 24 = modelSqueeze m 192 := by
  rw [model_squeeze_add, model_squeeze_add]

/-- Actual query raw squeezes then lambda, before authentication/intro.
Zero queries still carry the genuine independently sampled lambda. -/
theorem query_byte_group (m : Model) (chunks : Nat) :
    modelSqueeze (modelSqueeze m (24*chunks)) 24 =
      modelSqueeze m (24*(chunks+1)) := by
  rw [model_squeeze_add]
  congr 1

/-- Executable underlying byte-loop state and output concatenation agree exactly.
Flush/limit and reachability checks remain the explicit source preconditions of
the existing squeeze implementation; there is no claimed universal Rust bridge. -/
theorem executable_byte_group (compress : Compression) (s : State) (a b : Nat) :
    squeezeLoop compress (a+b) s =
      let first := squeezeLoop compress a s
      let second := squeezeLoop compress b first.1
      (second.1,first.2 ++ second.2) := squeezeLoop_append compress a b s

/-- Every actual full chunk lies within the 192-bit field representation. A
cross-limb chunk may read the next limb, but never limb three. -/
theorem query_chunk_no_wrap (depth : Nat) (positive : 0 < depth)
    (bounded : depth ≤ 64) (j : Fin (192 / depth)) :
    j.val * depth + depth ≤ 192 ∧ j.val * depth / 64 < 3 ∧
      (64 < j.val * depth % 64 + depth → j.val * depth / 64 + 1 < 3) := by
  have full : (j.val+1)*depth ≤ 192 :=
    (Nat.le_div_iff_mul_le positive).mp (by omega)
  rw [Nat.add_mul, one_mul] at full
  have split := Nat.mod_add_div (j.val*depth) 64
  omega

/-- Discarded high bits are a counted factor of the real raw alphabet, not
manufactured padding to meet the book's entropy condition. -/
theorem unused_query_bits (depth : Nat) (chunks : Fin (192 / depth) → Fin (2^depth)) :
    Fintype.card {a : E // (SamplingProbability.chunkEquiv depth a).2 = chunks} =
      2 ^ (192 % depth) := SamplingProbability.chunk_fiber depth chunks

private theorem product_probability {A B : Type*} [Fintype A] [Fintype B]
    (P : A → Prop) (Q : B → Prop) :
    SamplingProbability.probability (fun x : A × B => P x.1 ∧ Q x.2) =
      SamplingProbability.probability P * SamplingProbability.probability Q := by
  classical
  let e : {x : A × B // P x.1 ∧ Q x.2} ≃ {a : A // P a} × {b : B // Q b} :=
    { toFun := fun x => (⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2⟩)
      invFun := fun x => ⟨(x.1.val,x.2.val),x.1.property,x.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold SamplingProbability.probability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact joint query/lambda law on the unsplit raw verifier message. The
stratified query projection has the proved coset law, independently of lambda. -/
theorem query_lambda_joint_law (depth count : Nat) (positive : 0 < depth)
    (bounded : depth ≤ 64) (P : Fin count → Nat → Prop) (L : E → Prop) :
    SamplingProbability.probability
      (fun x : (Fin ((count+192/depth-1)/(192/depth)) → E) × E =>
        (∃ qs, deriveQueries depth count (Array.ofFn x.1) = some qs ∧
          ∀ i : Fin count, P i qs[i.val]!) ∧ L x.2) =
      (∏ i, SamplingProbability.probability (fun raw : Fin (2^depth) =>
        P i (SamplingProbability.concretePlace count depth i.val raw.val))) *
          SamplingProbability.probability L := by
  rw [product_probability
    (fun t : Fin ((count+192/depth-1)/(192/depth)) → E =>
      ∃ qs, deriveQueries depth count (Array.ofFn t) = some qs ∧
        ∀ i : Fin count, P i qs[i.val]!) L,
    projected_query_law depth count positive bounded P]

/-- A failing source nonce check rejects rather than resampling the PCS coins. -/
theorem nonce_rejected (compress : Compression)
    (powOK : FiatShamirGame.Digest32 → FiatShamirGame.Scalar24 → Nat → Bool)
    (s t : State) (bits : Nat) (nonce : E)
    (failed : verifyNonce compress powOK s (ByteCodec.encodeE nonce) bits = .ok (t,false)) :
    executeEvent compress powOK s (.nonce bits nonce) = none := by
  simp [executeEvent,failed]

/-- Every parsed visible PCS reply absorbs at least its two polynomial
coefficients; OOD additionally absorbs its value. No empty reply creates a
cross-round continuation of the preceding output cache. -/
theorem reply_boundary_nonempty {c : Config} (q : Coordinate c)
    (digest : FiatShamirGame.Digest32) (reply : Reply) (xs : List E)
    (parsed : replyScalars q digest reply = some xs) : xs ≠ [] := by
  cases q <;> cases reply <;> simp only [replyScalars] at parsed <;> try contradiction
  all_goals
    cases Option.some.inj parsed
    simp [messageScalars]

theorem reply_boundary_bytes_nonempty {c : Config} (q : Coordinate c)
    (digest : FiatShamirGame.Digest32) (reply : Reply) (xs : List E)
    (parsed : replyScalars q digest reply = some xs) : scalarBytes xs ≠ [] := by
  intro empty
  have size := congrArg List.length empty
  rw [scalarBytes_length, List.length_nil] at size
  have nonempty := reply_boundary_nonempty q digest reply xs parsed
  have positive : 0 < xs.length := List.length_pos_iff.mpr nonempty
  omega

private theorem absorbByte_cursor_reset (compress : Compression) (s : State)
    (byte : FiatShamirGame.Byte) : (absorbByte compress s byte).consumed = 0 := by
  simp only [absorbByte]
  split <;> split <;> simp_all

private theorem absorb_cursor_zero (compress : Compression) (s : State)
    (bytes : List FiatShamirGame.Byte) (zero : s.consumed = 0) :
    (absorb compress s bytes).consumed = 0 := by
  induction bytes generalizing s with
  | nil => exact zero
  | cons byte bytes ih =>
    exact ih (absorbByte compress s byte) (absorbByte_cursor_reset compress s byte)

/-- The executable absorb resets the cursor on any nonempty reply. Cached
bytes may remain stored, but are unreachable at the next positive squeeze. -/
theorem nonempty_absorb_cursor_reset (compress : Compression) (s : State)
    (bytes : List FiatShamirGame.Byte) (nonempty : bytes ≠ []) :
    (absorb compress s bytes).consumed = 0 := by
  cases bytes with
  | nil => contradiction
  | cons byte bytes =>
    exact absorb_cursor_zero compress (absorbByte compress s byte) bytes
      (absorbByte_cursor_reset compress s byte)

theorem parsed_reply_cursor_reset {c : Config} (compress : Compression) (s : State)
    (q : Coordinate c) (digest : FiatShamirGame.Digest32) (reply : Reply) (xs : List E)
    (parsed : replyScalars q digest reply = some xs) :
    (absorb compress s (scalarBytes xs)).consumed = 0 :=
  nonempty_absorb_cursor_reset compress s _ (reply_boundary_bytes_nonempty q digest reply xs parsed)

/-- Special nonce binding resets at every difficulty, including canonical
bits=0. No claim that the nonce contributes verifier entropy is made. -/
theorem nonce_cursor_reset (compress : Compression) (s : State)
    (nonce : FiatShamirGame.Scalar24) (bits : Nat) :
    (bindNonce compress s nonce bits).consumed = 0 := rfl

/-- At a zero cursor the first byte comes from outputBlock(0), not stored
unused bytes from the preceding public compression output. -/
theorem squeezeByte_old_cache_irrelevant (compress : Compression) (s : State)
    (zero : s.consumed = 0) (left right : FiatShamirGame.Digest32) :
    squeezeByte compress {s with output := left} =
      squeezeByte compress {s with output := right} := by
  simp [squeezeByte, zero]

theorem positive_squeezeLoop_old_cache_irrelevant (compress : Compression)
    (s : State) (zero : s.consumed = 0) (left right : FiatShamirGame.Digest32) (n : Nat) :
    squeezeLoop compress (n+1) {s with output := left} =
      squeezeLoop compress (n+1) {s with output := right} := by
  simp only [squeezeLoop]
  rw [squeezeByte_old_cache_irrelevant compress s zero left right]

private theorem finish_setOutput (compress : Compression) (s : State)
    (output : FiatShamirGame.Digest32) :
    finish compress {s with output := output} = {finish compress s with output := output} := by
  simp only [finish]
  split <;> rfl

/-- The actual guarded squeeze, including pending-input finalization and limit
rejection, cannot use the old cache after a round boundary cursor reset. -/
theorem positive_squeeze_old_cache_irrelevant (compress : Compression)
    (s : State) (zero : s.consumed = 0) (left right : FiatShamirGame.Digest32) (n : Nat) :
    squeeze compress {s with output := left} (n+1) =
      squeeze compress {s with output := right} (n+1) := by
  simp only [squeeze, Nat.add_one_ne_zero, ↓reduceIte]
  by_cases limit : s.consumed + (n+1) ≤ maxCursor
  · simp only [limit, ↓reduceIte, finish_setOutput]
    exact congrArg Except.ok (positive_squeezeLoop_old_cache_irrelevant compress
      (finish compress s) ((finish_consumed compress s).trans zero) left right n)
  · simp only [limit, ↓reduceIte]

/-- This is the modeled cursor boundary of every admitted book message,
including malformed values and nonce rejection branches. Initial caller-entry
normalization/physical representation is a separate explicit precondition. -/
theorem scheduled_round_cursor_zero (p : ParameterBounds.Profile)
    (entry : FiatShamirGame.FramedHistory) (messages : List Pending)
    (nonempty : messages ≠ [])
    (admitted : scheduledAdmissible (ParameterBounds.config p) messages = true) :
    (WHIRCallerPrefix.beforeModelFrom (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
      entry messages).consumed = 0 :=
  WHIRCallerPrefix.beforeModelFrom_consumed _ (WHIRHistoryKey.stackWidth_positive p)
    entry (WHIRHistoryKey.scheduled_normal _ _ nonempty admitted)

/-- Operative no-cross-round unused-cache bridge for the actual executable
state representing an admitted canonical source byte history. Representation
is explicit; independence of fresh compression outputs is NOT inferred here. -/
theorem physical_round_old_cache_irrelevant (compress : Compression)
    (iv : FiatShamirGame.Digest32) (p : ParameterBounds.Profile)
    (entry : FiatShamirGame.FramedHistory) (messages : List Pending)
    (nonempty : messages ≠ [])
    (admitted : scheduledAdmissible (ParameterBounds.config p) messages = true)
    (s : State)
    (represents : Represents compress iv
      (WHIRCallerPrefix.beforeModelFrom (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
        entry messages) s)
    (left right : FiatShamirGame.Digest32) (n : Nat) :
    squeeze compress {s with output := left} (n+1) =
      squeeze compress {s with output := right} (n+1) := by
  apply positive_squeeze_old_cache_irrelevant
  have cursor := materialize_consumed compress iv
    (WHIRCallerPrefix.beforeModelFrom (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
      entry messages) s.output represents.1
  rw [← represents.2.1] at cursor
  exact cursor.trans (scheduled_round_cursor_zero p entry messages nonempty admitted)

#print axioms initial_byte_group
#print axioms query_byte_group
#print axioms executable_byte_group
#print axioms nonce_rejected
#print axioms physical_round_old_cache_irrelevant
#print axioms parsed_reply_cursor_reset
end Whir.PCSBCSRounds
