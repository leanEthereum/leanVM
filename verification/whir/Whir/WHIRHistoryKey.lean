import Whir.WHIRHistory
import Whir.DuplexEncoding

/-! Recovery of scheduled cache prefixes from the actual #552 framed history.
Every noninitial PCS reply has at least two absorbed scalars. The initial
request has no new absorption. Nonces are separate frame constructors, not
ordinary bytes. Parsing these real delimiters recovers the whole pending
prefix; no root, compression, or semantic serialization injectivity is assumed. -/
namespace Whir.WHIRHistoryKey
open Concrete Protocol CausalProbability FiatShamirGame WHIRHistory DuplexRefinement

 def initialPending : Pending := ⟨[], none⟩

inductive Normal : List Pending → Prop where
  | initial : Normal [initialPending]
  | cons {ps : List Pending} (prior : Normal ps) (m : Pending)
      (nonempty : m.scalars ≠ []) : Normal (m :: ps)

 theorem Normal.nonempty {ps : List Pending} (h : Normal ps) : ps ≠ [] := by
  cases h <;> simp

/-- An executable syntax test, including rejecting branches. -/
def normal? : List Pending → Bool
  | [] => false
  | [m] => decide (m = initialPending)
  | m :: n :: ps => !m.scalars.isEmpty && normal? (n :: ps)

 theorem normal?_correct (ps : List Pending) : normal? ps = true ↔ Normal ps := by
  induction ps with
  | nil => simp [normal?]; intro h; cases h
  | cons m ps ih =>
    cases ps with
    | nil =>
      simp only [normal?, decide_eq_true_eq]
      constructor
      · rintro rfl; exact .initial
      · intro h; cases h with
        | initial => rfl
        | cons prior _ _ => exact False.elim (prior.nonempty rfl)
    | cons n ps =>
      simp only [normal?, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, ih]
      constructor
      · rintro ⟨hn,hp⟩; exact .cons hp m hn
      · intro h; cases h with | cons hp _ hn => exact ⟨hn,hp⟩

 def stepFrames (previous : Nat) (m : Pending) : List Frame :=
  [.absorb previous (scalarBytes m.scalars)] ++
    (m.nonce.toList.map (fun p => Frame.nonce 0 p.1 (ByteCodec.encodeE p.2)))

 def parseSteps : List Frame → Option (List Pending)
  | [] => some []
  | .absorb _ bytes :: .nonce _ bits nonce :: rest => do
    let xs ← parseExact (bytes.length / 24) bytes
    let ms ← parseSteps rest
    pure (⟨xs, some (bits,ByteCodec.decodeE nonce)⟩ :: ms)
  | .absorb _ bytes :: rest => do
    let xs ← parseExact (bytes.length / 24) bytes
    let ms ← parseSteps rest
    pure (⟨xs, none⟩ :: ms)
  | _ => none

 def encodeSteps (steps : List (Nat × Pending)) : List Frame :=
  steps.flatMap (fun p => stepFrames p.1 p.2)

 theorem steps_roundtrip (steps : List (Nat × Pending)) :
    parseSteps (encodeSteps steps) = some (steps.map Prod.snd) := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
    rcases step with ⟨previous,⟨xs,nonce⟩⟩
    cases nonce with
    | none =>
      cases steps with
      | nil => simp [encodeSteps, stepFrames, parseSteps, scalarBytes_length, parseExact_roundtrip]
      | cons next rest =>
        rcases next with ⟨n,⟨ys,nonce⟩⟩
        cases nonce <;>
          simp [encodeSteps, stepFrames, parseSteps, scalarBytes_length, parseExact_roundtrip,
            ByteCodec.decodeE_encodeE] at ih ⊢ <;>
          rw [ih] <;> rfl
    | some nonce =>
      rcases nonce with ⟨bits,value⟩
      simp [encodeSteps, stepFrames] at ih
      simp [encodeSteps, stepFrames, parseSteps, scalarBytes_length, parseExact_roundtrip,
        ByteCodec.decodeE_encodeE]
      rw [ih]
      rfl

 def annotated (width : Nat → Nat) : List Pending → List (Nat × Pending)
  | [] => []
  | m :: ps => if ps = [] then [] else (width (ps.length-1),m) :: annotated width ps

 def canonicalFrames (width : Nat → Nat) (ps : List Pending) : List Frame :=
  encodeSteps (annotated width ps).reverse

 theorem annotated_erases (width : Nat → Nat) (ps : List Pending) :
    (annotated width ps).map Prod.snd = ps.dropLast := by
  induction ps with
  | nil => rfl
  | cons m ps ih =>
    cases ps with
    | nil => simp [annotated]
    | cons n ps =>
      simp only [annotated, List.cons_ne_nil, ↓reduceIte, List.map_cons, List.dropLast_cons_cons]
      exact congrArg (List.cons m) ih

 theorem Normal.restore {ps : List Pending} (h : Normal ps) :
    ps.dropLast ++ [initialPending] = ps := by
  induction h with
  | initial => rfl
  | @cons ps hp m hn ih =>
    simpa only [List.dropLast_cons_of_ne_nil hp.nonempty, List.cons_append] using congrArg (List.cons m) ih

 theorem canonicalFrames_injective (width width' : Nat → Nat) {ps qs : List Pending}
    (hp : Normal ps) (hq : Normal qs)
    (he : canonicalFrames width ps = canonicalFrames width' qs) : ps = qs := by
  have parsed := congrArg parseSteps he
  simp only [canonicalFrames, steps_roundtrip, Option.some.injEq,
    List.map_reverse, annotated_erases] at parsed
  have erased : ps.dropLast = qs.dropLast := List.reverse_injective parsed
  rw [← hp.restore, ← hq.restore, erased]

/-- Generic recurrence used by both standalone WHIR and stack_open. `width n`
is the fixed whole-vector byte count at position n, including initial 192
bytes for stack_open and the invisible final 24 bytes. -/
def completedModel (width : Nat → Nat) (domain statement : Digest32) : List Pending → Model
  | [] => ⟨⟨domain,statement,[]⟩,[],0,0⟩
  | m :: ps => modelSqueeze (pendingModel (completedModel width domain statement ps) m) (width ps.length)

 def beforeModel (width : Nat → Nat) (domain statement : Digest32) : List Pending → Model
  | [] => completedModel width domain statement []
  | m :: ps => pendingModel (completedModel width domain statement ps) m

 theorem completed_normal (width : Nat → Nat) (positive : ∀ n, 0 < width n)
    (domain statement : Digest32) {ps : List Pending} (h : Normal ps) :
    completedModel width domain statement ps =
      ⟨⟨domain,statement,canonicalFrames width ps⟩,[],0,width (ps.length-1)⟩ := by
  induction h with
  | initial =>
    simp [completedModel, initialPending, pendingModel, modelAbsorb, scalarBytes,
      modelSqueeze, closeRun, canonicalFrames, annotated, encodeSteps, Nat.ne_of_gt (positive 0)]
  | @cons ps hp m hn ih =>
    have hb : scalarBytes m.scalars ≠ [] := fun h => hn ((scalarBytes_empty _).mp h)
    have hw : width ps.length ≠ 0 := Nat.ne_of_gt (positive ps.length)
    rw [completedModel, ih]
    rcases m with ⟨xs,nonce⟩
    cases nonce with
    | none =>
      simp only [pendingModel, modelAbsorb, hb, ↓reduceIte, List.nil_append,
        modelSqueeze, hw, closeRun]
      simp [canonicalFrames, annotated, hp.nonempty, encodeSteps, stepFrames,
        Nat.ne_of_gt (positive (ps.length-1))]
    | some nonce =>
      rcases nonce with ⟨bits,value⟩
      simp only [pendingModel, modelAbsorb, hb, ↓reduceIte, List.nil_append,
        modelNonce, modelSqueeze, hw, closeRun]
      simp [canonicalFrames, annotated, hp.nonempty, encodeSteps, stepFrames,
        Nat.ne_of_gt (positive (ps.length-1))]

 theorem before_history (width : Nat → Nat) (positive : ∀ n, 0 < width n)
    (domain statement : Digest32) {ps : List Pending} (h : Normal ps) :
    (closeRun (beforeModel width domain statement ps)).history =
      ⟨domain,statement,canonicalFrames width ps⟩ := by
  have hc := congrArg Model.history (completed_normal width positive domain statement h)
  cases ps with
  | nil => exact False.elim (h.nonempty rfl)
  | cons m ps =>
    simpa only [completedModel, beforeModel, modelSqueeze,
      Nat.ne_of_gt (positive ps.length), ↓reduceIte] using hc

/-- This is actual framed-history-to-cache-prefix injection. Counts need only
be positive; the parser reads the real absorb/nonce constructors and bytes.
There is no injectivity premise for a digest or compression function. -/
theorem before_history_injective (width width' : Nat → Nat)
    (positive : ∀ n, 0 < width n) (positive' : ∀ n, 0 < width' n)
    (domain statement domain' statement' : Digest32) {ps qs : List Pending}
    (hp : Normal ps) (hq : Normal qs)
    (same : (closeRun (beforeModel width domain statement ps)).history =
      (closeRun (beforeModel width' domain' statement' qs)).history) :
    domain = domain' ∧ statement = statement' ∧ ps = qs := by
  rw [before_history width positive domain statement hp,
    before_history width' positive' domain' statement' hq] at same
  exact ⟨congrArg FramedHistory.domain same, congrArg FramedHistory.statement same,
    canonicalFrames_injective width width' hp hq (congrArg FramedHistory.frames same)⟩

theorem replyScalarCount_positive {c : Config} (q : Coordinate c) : 0 < replyScalarCount q := by
  cases q <;> simp only [replyScalarCount] <;> omega

private theorem normal_reverse (rest : List Pending)
    (hn : ∀ m ∈ rest, m.scalars ≠ []) : Normal (rest.reverse ++ [initialPending]) := by
  induction rest using List.reverseRecOn with
  | nil => exact .initial
  | append_singleton rest m ih =>
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    exact .cons (ih (fun a ha => hn a (by simp [ha]))) m (hn m (by simp))

/-- The regular fixed-position recognizer already implies the delimiter syntax
needed above: every postinitial reply contributes at least two scalars. -/
theorem scheduled_normal (c : Config) (ps : List Pending) (nonempty : ps ≠ [])
    (admitted : scheduledAdmissible c ps = true) : Normal ps := by
  have checks := admitted
  simp only [scheduledAdmissible, Bool.and_eq_true, List.all_eq_true,
    List.forall_mem_zipIdx'] at checks
  have hc := checks.2
  cases hr : ps.reverse with
  | nil =>
    have : ps = [] := by simpa only [List.reverse_eq_nil_iff] using hr
    exact False.elim (nonempty this)
  | cons m rest =>
    rw [hr] at hc
    have first := hc 0 (by simp)
    simp [schedule, visibleCoordinates] at first
    have hm : m = initialPending := by
      rcases m with ⟨xs,nonce⟩
      simp only at first
      rcases first with ⟨hx,hn⟩
      have hnonce : nonce = none := by simpa using hn
      subst xs
      subst nonce
      rfl
    subst m
    have hn : ∀ m ∈ rest, m.scalars ≠ [] := by
      intro m hm
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
      have step := hc (i+1) (by simp; omega)
      simp only [List.getElem_cons_succ, Nat.add_one_ne_zero, ↓reduceIte,
        decide_eq_true_eq] at step
      have hp := replyScalarCount_positive (((schedule c)[i+1-1]?).getD .initial)
      intro empty
      have len : m.scalars.length = 0 := by rw [empty]; rfl
      have hs := step.1
      rw [he] at hs
      omega
    have recovered := normal_reverse rest hn
    have eq : rest.reverse ++ [initialPending] = ps := by
      have := congrArg List.reverse hr
      simpa only [List.reverse_reverse, List.reverse_cons] using this.symm
    exact eq ▸ recovered

/-- Ancestor answers are completed through the same global dependent oracle.
They are not placed in the byte stream, and an arbitrary future table is not
part of the adversary's message syntax. -/
def fullInput (c : Config) {A : CausalProbability.Coordinate c → Type*}
    (oracle : TypedFiatShamirGame.Oracle (A := A) (queryFor c))
    (statement : Digest32) (ps : List Pending) :
    TypedFiatShamirGame.FullInput Digest32 Pending (CausalProbability.Coordinate c) A :=
  ⟨statement, ps, TypedFiatShamirGame.complete (queryFor c) oracle statement ps.tail⟩

/-- Equal actual canonical mode histories yield equal completed typed inputs.
The sole width premise is arithmetic positivity; the schedule recognizer and
history parser are executable definitions with checked inverse theorems. -/
theorem framed_fullInput_injective (c : Config) {A : CausalProbability.Coordinate c → Type*}
    (oracle : TypedFiatShamirGame.Oracle (A := A) (queryFor c))
    (width width' : Nat → Nat)
    (positive : ∀ n, 0 < width n) (positive' : ∀ n, 0 < width' n)
    (domain statement domain' statement' : Digest32) (ps qs : List Pending)
    (hp : ps ≠ []) (hq : qs ≠ [])
    (ap : scheduledAdmissible c ps = true) (aq : scheduledAdmissible c qs = true)
    (same : (closeRun (beforeModel width domain statement ps)).history =
      (closeRun (beforeModel width' domain' statement' qs)).history) :
    fullInput c oracle statement ps = fullInput c oracle statement' qs := by
  obtain ⟨_,hs,hps⟩ := before_history_injective width width' positive positive'
    domain statement domain' statement' (scheduled_normal c ps hp ap)
    (scheduled_normal c qs hq aq) same
  subst statement'
  subst qs
  rfl

def standaloneWidth (c : Config) (n : Nat) : Nat :=
  24 * scalarCount (((schedule c)[n]?).getD .initial)

def stackWidth (c : Config) (n : Nat) : Nat :=
  24 * stackScalarCount (((schedule c)[n]?).getD .initial)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem production_sample_counts :
    ∀ p : ParameterBounds.Profile,
      ∀ q : CausalProbability.Coordinate (ParameterBounds.config p),
        0 < scalarCount q ∧ 0 < stackScalarCount q := by
  have residual : ∀ p : ParameterBounds.Profile,
      0 < (ParameterBounds.config p).logN - (ParameterBounds.config p).folds.toList.sum := by
    decide +kernel
  intro p q
  cases q <;> simp only [scalarCount, stackScalarCount] <;> try omega
  rename_i i j
  have hr := residual p
  have hs := List.sum_take_add_sum_drop (ParameterBounds.config p).folds.toList (i.val+1)
  unfold CausalGame.remaining
  omega

theorem standaloneWidth_positive (p : ParameterBounds.Profile) (n : Nat) :
    0 < standaloneWidth (ParameterBounds.config p) n :=
  Nat.mul_pos (by decide) (production_sample_counts p _).1

theorem stackWidth_positive (p : ParameterBounds.Profile) (n : Nat) :
    0 < stackWidth (ParameterBounds.config p) n :=
  Nat.mul_pos (by decide) (production_sample_counts p _).2

def outputKey (width : Nat → Nat) (domain statement : Digest32)
    (ps : List Pending) (block : Nat) : FiatShamirGame.Coordinate :=
  ⟨(closeRun (beforeModel width domain statement ps)).history, .output block⟩

/-- Distinct scheduled statement/prefix/block keys cannot alias a physical
framed output coordinate. Repeated prefixes therefore reuse the same key;
there is no new allocation for a clone or an overlapping output slice. -/
theorem outputKey_injective (c : Config) (width width' : Nat → Nat)
    (positive : ∀ n, 0 < width n) (positive' : ∀ n, 0 < width' n)
    (domain statement domain' statement' : Digest32) (ps qs : List Pending)
    (block block' : Nat) (hp : ps ≠ []) (hq : qs ≠ [])
    (ap : scheduledAdmissible c ps = true) (aq : scheduledAdmissible c qs = true)
    (same : outputKey width domain statement ps block =
      outputKey width' domain' statement' qs block') :
    domain = domain' ∧ statement = statement' ∧ ps = qs ∧ block = block' := by
  have hh := congrArg FiatShamirGame.Coordinate.history same
  have ht := congrArg FiatShamirGame.Coordinate.terminal same
  obtain ⟨hd,hs,hps⟩ := before_history_injective width width' positive positive'
    domain statement domain' statement' (scheduled_normal c ps hp ap)
    (scheduled_normal c qs hq aq) hh
  exact ⟨hd,hs,hps,Terminal.output.inj ht⟩

theorem scheduled_nonce_bits (c : Config) (ps : List Pending)
    (admitted : scheduledAdmissible c ps = true) :
    ∀ m ∈ ps, ∀ bits value, m.nonce = some (bits,value) → bits ≤ 63 := by
  simp only [scheduledAdmissible, Bool.and_eq_true, List.all_eq_true,
    List.forall_mem_zipIdx'] at admitted
  intro m hm bits value hn
  have hr : m ∈ ps.reverse := List.mem_reverse.mpr hm
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hr
  have hc := (admitted.2 i hi).2
  rw [he] at hc
  cases hq : ((schedule c)[i]?).getD .initial <;> simp [hq, hn] at hc
  exact hc

theorem canonicalFrames_cons (width : Nat → Nat) (m : Pending) (ps : List Pending)
    (hp : ps ≠ []) : canonicalFrames width (m :: ps) =
      canonicalFrames width ps ++ stepFrames (width (ps.length-1)) m := by
  simp [canonicalFrames, annotated, hp, encodeSteps]

theorem canonicalFrames_valid (width : Nat → Nat) (bounded : ∀ n, width n < 2^49)
    {ps : List Pending} (h : Normal ps)
    (nonces : ∀ m ∈ ps, ∀ bits value, m.nonce = some (bits,value) → bits ≤ 63) :
    ∀ f ∈ canonicalFrames width ps, DuplexEncoding.FrameValid f := by
  revert nonces
  induction h with
  | initial => simp [canonicalFrames, annotated, encodeSteps]
  | @cons ps hp m hn ih =>
    intro nonces f hf
    rw [canonicalFrames_cons width m ps hp.nonempty] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact ih (fun a ha => nonces a (by simp [ha])) f hf
    · simp only [stepFrames, List.mem_append, List.mem_singleton, List.mem_map] at hf
      rcases hf with rfl | ⟨p,hp,rfl⟩
      · exact ⟨bounded _, fun he => hn ((scalarBytes_empty _).mp he)⟩
      · rcases p with ⟨bits,value⟩
        have he : m.nonce = some (bits,value) := by simpa using hp
        exact ⟨by decide, nonces m (by simp) bits value he⟩

theorem outputKey_admissible (c : Config) (width : Nat → Nat)
    (positive : ∀ n, 0 < width n) (bounded : ∀ n, width n < 2^49)
    (domain statement : Digest32) (ps : List Pending) (block : Nat)
    (nonempty : ps ≠ []) (admitted : scheduledAdmissible c ps = true)
    (blockBound : block < (width (ps.length-1) + 31) / 32) :
    DuplexEncoding.Admissible (outputKey width domain statement ps block) := by
  have hn := scheduled_normal c ps nonempty admitted
  have hf := canonicalFrames_valid width bounded hn (scheduled_nonce_bits c ps admitted)
  constructor
  · simpa only [outputKey, before_history width positive domain statement hn] using hf
  · change block < 2^44
    have hw := bounded (ps.length-1)
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem production_sample_upper :
    ∀ p : ParameterBounds.Profile,
      ∀ q : CausalProbability.Coordinate (ParameterBounds.config p),
        scalarCount q < 2^40 ∧ stackScalarCount q < 2^40 := by
  decide +kernel

theorem standaloneWidth_bounded (p : ParameterBounds.Profile) (n : Nat) :
    standaloneWidth (ParameterBounds.config p) n < 2^49 := by
  have h := (production_sample_upper p (((schedule (ParameterBounds.config p))[n]?).getD .initial)).1
  unfold standaloneWidth
  omega

theorem stackWidth_bounded (p : ParameterBounds.Profile) (n : Nat) :
    stackWidth (ParameterBounds.config p) n < 2^49 := by
  have h := (production_sample_upper p (((schedule (ParameterBounds.config p))[n]?).getD .initial)).2
  unfold stackWidth
  omega

theorem production_outputKey_admissible (p : ParameterBounds.Profile)
    (domain statement : Digest32) (ps : List Pending) (block : Nat)
    (nonempty : ps ≠ []) (admitted : scheduledAdmissible (ParameterBounds.config p) ps = true)
    (blockBound : block < (standaloneWidth (ParameterBounds.config p) (ps.length-1) + 31) / 32) :
    DuplexEncoding.Admissible
      (outputKey (standaloneWidth (ParameterBounds.config p)) domain statement ps block) :=
  outputKey_admissible (ParameterBounds.config p) _ (standaloneWidth_positive p)
    (standaloneWidth_bounded p) domain statement ps block nonempty admitted blockBound

theorem production_stackOutputKey_admissible (p : ParameterBounds.Profile)
    (domain statement : Digest32) (ps : List Pending) (block : Nat)
    (nonempty : ps ≠ []) (admitted : scheduledAdmissible (ParameterBounds.config p) ps = true)
    (blockBound : block < (stackWidth (ParameterBounds.config p) (ps.length-1) + 31) / 32) :
    DuplexEncoding.Admissible
      (outputKey (stackWidth (ParameterBounds.config p)) domain statement ps block) :=
  outputKey_admissible (ParameterBounds.config p) _ (stackWidth_positive p)
    (stackWidth_bounded p) domain statement ps block nonempty admitted blockBound

end Whir.WHIRHistoryKey
