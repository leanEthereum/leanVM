import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.Wots
import XmssSecurity.Proof.EncodingLemmas

namespace XmssSecurity.Wots

@[simp]
theorem walk_zero {α : Type} (step : Nat → α → α) (position : Nat) (value : α) :
    walk step position 0 value = value := rfl

theorem walk_add {α : Type} (step : Nat → α → α) (position first second : Nat)
    (value : α) :
    walk step position (first + second) value =
      walk step (position + first) second (walk step position first value) := by
  induction second with
  | zero => simp
  | succ second ih =>
      simp only [walk]
      exact congrArg₂ step (Nat.add_assoc position first second).symm ih

theorem walk_split {α : Type} (step : Nat → α → α) (start split finish : Nat)
    (value : α) (hstart : start ≤ split) (hfinish : split ≤ finish) :
    walk step start (finish - start) value =
      walk step split (finish - split) (walk step start (split - start) value) := by
  rw [show finish - start = (split - start) + (finish - split) by omega, walk_add]
  congr 2
  omega

def HasStepCollision {α : Type} (step : Nat → α → α) (position steps : Nat)
    (left right : α) : Prop :=
  ∃ offset, offset < steps ∧
    walk step position offset left ≠ walk step position offset right ∧
    step (position + offset) (walk step position offset left) =
      step (position + offset) (walk step position offset right)

/-- Equal chain endpoints come from equal starts or from a collision at one chain step. -/
theorem eq_or_hasStepCollision {α : Type} (step : Nat → α → α) (position steps : Nat)
    (left right : α) (hend : walk step position steps left = walk step position steps right) :
    left = right ∨ HasStepCollision step position steps left right := by
  induction steps with
  | zero =>
      left
      simpa using hend
  | succ steps ih =>
      rcases Classical.em
        (walk step position steps left = walk step position steps right) with hmid | hmid
      · rcases ih hmid with hstart | hcollision
        · exact Or.inl hstart
        · exact Or.inr <| by
            obtain ⟨offset, hoffset, hne, heq⟩ := hcollision
            exact ⟨offset, Nat.lt_succ_of_lt hoffset, hne, heq⟩
      · right
        exact ⟨steps, Nat.lt_succ_self steps, hmid, by simpa only [walk] using hend⟩

/-- A value forged earlier in a chain either recovers the signed value or creates a chain collision. -/
theorem backward_value_or_hasStepCollision {α : Type} (step : Nat → α → α)
    (forgedPosition signedPosition finish : Nat) (forgedValue signedValue : α)
    (hforged : forgedPosition ≤ signedPosition) (hsigned : signedPosition ≤ finish)
    (hend : walk step forgedPosition (finish - forgedPosition) forgedValue =
      walk step signedPosition (finish - signedPosition) signedValue) :
    walk step forgedPosition (signedPosition - forgedPosition) forgedValue = signedValue ∨
      HasStepCollision step signedPosition (finish - signedPosition)
        (walk step forgedPosition (signedPosition - forgedPosition) forgedValue) signedValue := by
  apply eq_or_hasStepCollision
  rw [← walk_split step forgedPosition signedPosition finish forgedValue hforged hsigned]
  exact hend

def signChain {α : Type} (step : Nat → α → α) (digit : Digit) (secret : α) : α :=
  walk step 0 digit.val secret

def recoverChain {α : Type} (step : Nat → α → α) (digit : Digit) (value : α) : α :=
  walk step digit.val (chainLength - 1 - digit.val) value

def publicChain {α : Type} (step : Nat → α → α) (secret : α) : α :=
  walk step 0 (chainLength - 1) secret

/-- Continuing an honestly generated chain value reaches its public endpoint. -/
theorem recover_signChain_eq_publicChain {α : Type} (step : Nat → α → α)
    (digit : Digit) (secret : α) :
    recoverChain step digit (signChain step digit secret) = publicChain step secret := by
  calc
    recoverChain step digit (signChain step digit secret) =
        walk step 0 (digit.val + (chainLength - 1 - digit.val)) secret := by
      simpa [recoverChain, signChain] using
        (walk_add step 0 digit.val (chainLength - 1 - digit.val) secret).symm
    _ = publicChain step secret := by
      unfold publicChain
      congr 2
      omega

/-- A distinct valid WOTS encoding with the same recovered endpoints yields a backward preimage or a chain collision. -/
theorem extract_of_distinct_valid_encodings {α : Type}
    (step : ChainIndex → Nat → α → α)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → α)
    (hsigned : TargetSum.Valid signedEncoding) (hforged : TargetSum.Valid forgedEncoding)
    (hne : signedEncoding ≠ forgedEncoding)
    (hendpoints : ∀ i,
      recoverChain (step i) (forgedEncoding i) (forgedValue i) =
        recoverChain (step i) (signedEncoding i) (signedValue i)) :
    ∃ i, forgedEncoding i < signedEncoding i ∧
      (walk (step i) (forgedEncoding i).val
          ((signedEncoding i).val - (forgedEncoding i).val) (forgedValue i) = signedValue i ∨
        HasStepCollision (step i) (signedEncoding i).val
          (chainLength - 1 - (signedEncoding i).val)
          (walk (step i) (forgedEncoding i).val
            ((signedEncoding i).val - (forgedEncoding i).val) (forgedValue i))
          (signedValue i)) := by
  obtain ⟨i, hi⟩ := TargetSum.exists_forged_lt_signed hsigned hforged hne
  refine ⟨i, hi, ?_⟩
  apply backward_value_or_hasStepCollision
  · exact hi.le
  · exact Nat.le_pred_of_lt (signedEncoding i).isLt
  · simpa only [recoverChain] using hendpoints i

def IsBackwardWitnessAt {α : Type} (step : ChainIndex → Nat → α → α)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → α) (i : ChainIndex) : Prop :=
  forgedEncoding i < signedEncoding i ∧
  walk (step i) (forgedEncoding i).val
    ((signedEncoding i).val - (forgedEncoding i).val) (forgedValue i) = signedValue i

def HasBackwardWitness {α : Type} (step : ChainIndex → Nat → α → α)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → α) : Prop :=
  ∃ i, IsBackwardWitnessAt step signedEncoding forgedEncoding signedValue forgedValue i

theorem walk_signChain_to_later {α : Type} (step : Nat → α → α)
    (earlier later : Nat) (secret : α) (hle : earlier ≤ later) :
    walk step earlier (later - earlier) (walk step 0 earlier secret) =
      walk step 0 later secret := by
  simpa using (walk_split step 0 earlier later secret (Nat.zero_le earlier) hle).symm

theorem backwardWitness_eq_honest_or_hasStepCollision {α : Type}
    (step : ChainIndex → Nat → α → α)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue secret : ChainIndex → α) (i : ChainIndex)
    (hsigned : signedValue i = signChain (step i) (signedEncoding i) (secret i))
    (hwitness : IsBackwardWitnessAt step signedEncoding forgedEncoding signedValue forgedValue i) :
    forgedValue i = signChain (step i) (forgedEncoding i) (secret i) ∨
      HasStepCollision (step i) (forgedEncoding i).val
        ((signedEncoding i).val - (forgedEncoding i).val)
        (forgedValue i) (signChain (step i) (forgedEncoding i) (secret i)) := by
  apply eq_or_hasStepCollision
  calc
    walk (step i) (forgedEncoding i).val
        ((signedEncoding i).val - (forgedEncoding i).val) (forgedValue i) =
      signedValue i := hwitness.2
    _ = signChain (step i) (signedEncoding i) (secret i) := hsigned
    _ = walk (step i) (forgedEncoding i).val
        ((signedEncoding i).val - (forgedEncoding i).val)
        (signChain (step i) (forgedEncoding i) (secret i)) := by
      symm
      exact walk_signChain_to_later (step i) (forgedEncoding i).val
        (signedEncoding i).val (secret i) hwitness.1.le

def IsSuffixCollisionAt {α : Type} (step : ChainIndex → Nat → α → α)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → α)
    (position : TargetSum.SuffixPosition signedEncoding) : Prop :=
  let i := position.1
  let offset := position.2.val
  let forgedAtSigned := walk (step i) (forgedEncoding i).val
    ((signedEncoding i).val - (forgedEncoding i).val) (forgedValue i)
  forgedEncoding i ≤ signedEncoding i ∧
    walk (step i) (signedEncoding i).val offset forgedAtSigned ≠
      walk (step i) (signedEncoding i).val offset (signedValue i) ∧
    step i ((signedEncoding i).val + offset)
        (walk (step i) (signedEncoding i).val offset forgedAtSigned) =
      step i ((signedEncoding i).val + offset)
        (walk (step i) (signedEncoding i).val offset (signedValue i))

def HasSuffixCollisionWitness {α : Type} (step : ChainIndex → Nat → α → α)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → α) : Prop :=
  ∃ position, IsSuffixCollisionAt step signedEncoding forgedEncoding signedValue forgedValue position

/-- The WOTS extraction alternatives are indexed by 42 chains and exactly 99 valid suffix positions. -/
theorem classify_distinct_valid_encodings {α : Type}
    (step : ChainIndex → Nat → α → α)
    (signedEncoding forgedEncoding : Encoding)
    (signedValue forgedValue : ChainIndex → α)
    (hsigned : TargetSum.Valid signedEncoding) (hforged : TargetSum.Valid forgedEncoding)
    (hne : signedEncoding ≠ forgedEncoding)
    (hendpoints : ∀ i,
      recoverChain (step i) (forgedEncoding i) (forgedValue i) =
        recoverChain (step i) (signedEncoding i) (signedValue i)) :
    HasBackwardWitness step signedEncoding forgedEncoding signedValue forgedValue ∨
      HasSuffixCollisionWitness step signedEncoding forgedEncoding signedValue forgedValue := by
  obtain ⟨i, hi, hbackward | hcollision⟩ :=
    extract_of_distinct_valid_encodings step signedEncoding forgedEncoding signedValue forgedValue
      hsigned hforged hne hendpoints
  · exact Or.inl ⟨i, hi, hbackward⟩
  · right
    obtain ⟨offset, hoffset, hne, heq⟩ := hcollision
    exact ⟨⟨i, ⟨offset, hoffset⟩⟩, hi.le, hne, heq⟩

/-- With the same encoding, different chain values recovering the same endpoints expose a suffix collision. -/
theorem suffixCollision_of_sameEncoding_of_values_ne {α : Type}
    (step : ChainIndex → Nat → α → α) (encoding : Encoding)
    (signedValue forgedValue : ChainIndex → α)
    (hne : signedValue ≠ forgedValue)
    (hendpoints : ∀ i,
      recoverChain (step i) (encoding i) (forgedValue i) =
        recoverChain (step i) (encoding i) (signedValue i)) :
    HasSuffixCollisionWitness step encoding encoding signedValue forgedValue := by
  have hcoordinate : ∃ i, forgedValue i ≠ signedValue i := by
    by_contra h
    push Not at h
    apply hne
    funext i
    exact (h i).symm
  obtain ⟨i, hi⟩ := hcoordinate
  have hcollision := eq_or_hasStepCollision (step i) (encoding i).val
    (chainLength - 1 - (encoding i).val) (forgedValue i) (signedValue i)
    (by simpa only [recoverChain] using hendpoints i)
  rcases hcollision with heq | ⟨offset, hoffset, hstepNe, hstepEq⟩
  · exact (hi heq).elim
  · exact ⟨⟨i, ⟨offset, hoffset⟩⟩, le_rfl, by simpa using hstepNe,
      by simpa using hstepEq⟩

def IsFreshChainValueAt {α : Type} (step : ChainIndex → Nat → α → α)
    (encoding : Encoding) (forgedValue secret : ChainIndex → α) (i : ChainIndex) : Prop :=
  forgedValue i = signChain (step i) (encoding i) (secret i)

def HasFreshChainValue {α : Type} (step : ChainIndex → Nat → α → α)
    (encoding : Encoding) (forgedValue secret : ChainIndex → α) : Prop :=
  ∃ i, IsFreshChainValueAt step encoding forgedValue secret i

/-- A fresh-epoch WOTS opening either reveals an honest hidden chain value or creates a suffix collision. -/
theorem freshChainValue_or_suffixCollision {α : Type}
    (step : ChainIndex → Nat → α → α) (encoding : Encoding)
    (forgedValue secret : ChainIndex → α)
    (hendpoints : ∀ i,
      recoverChain (step i) (encoding i) (forgedValue i) = publicChain (step i) (secret i)) :
    HasFreshChainValue step encoding forgedValue secret ∨
      HasSuffixCollisionWitness step encoding encoding
        (fun i => signChain (step i) (encoding i) (secret i)) forgedValue := by
  classical
  rcases Classical.em
    (∀ i, forgedValue i = signChain (step i) (encoding i) (secret i)) with hall | hall
  · left
    exact ⟨⟨0, by decide⟩, hall _⟩
  · right
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hcollision := eq_or_hasStepCollision (step i) (encoding i).val
      (chainLength - 1 - (encoding i).val) (forgedValue i)
      (signChain (step i) (encoding i) (secret i)) (by
        change recoverChain (step i) (encoding i) (forgedValue i) =
          recoverChain (step i) (encoding i) (signChain (step i) (encoding i) (secret i))
        rw [recover_signChain_eq_publicChain]
        exact hendpoints i)
    rcases hcollision with heq | ⟨offset, hoffset, hstepNe, hstepEq⟩
    · exact (hi heq).elim
    · exact ⟨⟨i, ⟨offset, hoffset⟩⟩, le_rfl, by simpa using hstepNe,
        by simpa using hstepEq⟩

def HasLeafCollision {α β : Type} (leafHash : (ChainIndex → α) → β)
    (left right : ChainIndex → α) : Prop :=
  left ≠ right ∧ leafHash left = leafHash right

/-- Equal WOTS leaves come from equal recovered endpoint vectors or one leaf-hash collision. -/
theorem eq_or_hasLeafCollision {α β : Type} (leafHash : (ChainIndex → α) → β)
    (left right : ChainIndex → α) (hleaf : leafHash left = leafHash right) :
    left = right ∨ HasLeafCollision leafHash left right := by
  rcases Classical.em (left = right) with heq | heq
  · exact Or.inl heq
  · exact Or.inr ⟨heq, hleaf⟩

end XmssSecurity.Wots
