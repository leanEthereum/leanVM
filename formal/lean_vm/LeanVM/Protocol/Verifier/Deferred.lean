/-
  LeanVM.Protocol.Verifier.Deferred

  The deferring verifier, its claims true, is the deployed verifier: a proof the deferring
  verifier accepts under the deployed IV, with true claims on the fixed polynomials, the deployed
  verifier accepts.
-/

module

public import LeanVM.Facts.Verifier
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Protocol.WithHash
public import LeanVM.Protocol.WithHashBridge

/-!
# The deferring verifier, its claims true

The deferring verifier (`verifyDeferred`) differs from the deployed one (`verify`) in two
places: its IV is given rather than hashed from the bytecode, and it takes the fixed polynomials'
values from claims (`claimedBytecodeValue c`) instead of computing them (`computedBytecodeValue`).
Under the deployed IV the seeds agree, and where the claims are true (`BytecodeClaim.Holds`) each
claimed value is either refused (the verifier asks at another point) or the computed one. So the
deferring program refines the deployed one (`VerifierProgram.Le`: it does what the deployed one
does, or fails), and an accepted run of it is an accepted run of the deployed verifier
(`verify_of_verifyDeferred`).

The refinement is proved through the verifier's text: `verifyExecution` reads the fixed
polynomials only through `ev` (`verifyBusBalance`), and every other
program it runs is the same on both sides.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

@[expose] public section

namespace VerifierProgram

variable {α β : Type}

/-- **`p` refines `q`**: `p` makes the same moves as `q` and returns what `q` returns, or fails
earlier. -/
inductive Le : VerifierProgram α → VerifierProgram α → Prop where
  /-- Failing refines anything. -/
  | fail (q : VerifierProgram α) : Le fail q
  /-- A return refines itself. -/
  | ret (a : α) : Le (ret a) (ret a)
  /-- Reading a scalar. -/
  | read {k k' : E → VerifierProgram α} : (∀ x, Le (k x) (k' x)) → Le (read k) (read k')
  /-- Sampling a challenge. -/
  | sample {k k' : E → VerifierProgram α} : (∀ x, Le (k x) (k' x)) → Le (sample k) (sample k')
  /-- A proof of work. -/
  | grind (bits : ℕ) {k k' : VerifierProgram α} : Le k k' → Le (grind bits k) (grind bits k')
  /-- A commitment. -/
  | commit (height width : ℕ) {k k' : VerifierProgram α} : Le k k' → Le (commit height width k) (commit height width k')
  /-- An opening. -/
  | query (i : ℕ) (positions : List ℕ) {k k' : List (List K) → VerifierProgram α} :
      (∀ rows, Le (k rows) (k' rows)) → Le (query i positions k) (query i positions k')

/-- **`p` may return `a`**, along some run. -/
inductive Returns : VerifierProgram α → α → Prop where
  /-- A return. -/
  | ret (a : α) : Returns (ret a) a
  /-- After reading a scalar. -/
  | read {k : E → VerifierProgram α} {a : α} (x : E) : Returns (k x) a → Returns (read k) a
  /-- After sampling a challenge. -/
  | sample {k : E → VerifierProgram α} {a : α} (x : E) : Returns (k x) a → Returns (sample k) a
  /-- After a proof of work. -/
  | grind (bits : ℕ) {k : VerifierProgram α} {a : α} : Returns k a → Returns (grind bits k) a
  /-- After a commitment. -/
  | commit (height width : ℕ) {k : VerifierProgram α} {a : α} : Returns k a → Returns (commit height
      width k) a
  /-- After an opening. -/
  | query (i : ℕ) (positions : List ℕ) {k : List (List K) → VerifierProgram α} {a : α} (rows : List
      (List K)) :
      Returns (k rows) a → Returns (query i positions k) a

theorem Le.refl : ∀ p : VerifierProgram α, Le p p
  | .ret a => .ret a
  | .fail => .fail _
  | .read k => .read fun x ↦ Le.refl (k x)
  | .sample k => .sample fun x ↦ Le.refl (k x)
  | .grind b k => .grind b (Le.refl k)
  | .commit h w k => .commit h w (Le.refl k)
  | .query i ps k => .query i ps fun r ↦ Le.refl (k r)

/-- Sequencing refines, the continuation at every value the first program may return. -/
theorem Le.bind_of {p p' : VerifierProgram α} {f g : α → VerifierProgram β} (hp : Le p p')
    (hf : ∀ a, Returns p a → Le (f a) (g a)) : Le (p >>= f) (p' >>= g) := by
  induction hp with
  | fail q => exact .fail _
  | ret a => exact hf a (.ret a)
  | read _ ih => exact .read fun x ↦ ih x fun a h ↦ hf a (.read x h)
  | sample _ ih => exact .sample fun x ↦ ih x fun a h ↦ hf a (.sample x h)
  | grind b _ ih => exact .grind b (ih fun a h ↦ hf a (.grind b h))
  | commit h w _ ih => exact .commit h w (ih fun a h' ↦ hf a (.commit h w h'))
  | query i ps _ ih => exact .query i ps fun r ↦ ih r fun a h ↦ hf a (.query i ps r h)

theorem Le.bind {p p' : VerifierProgram α} {f g : α → VerifierProgram β} (hp : Le p p') (hf : ∀ a,
    Le (f a) (g a)) :
    Le (p >>= f) (p' >>= g) :=
  hp.bind_of fun a _ ↦ hf a

theorem returns_bind {p : VerifierProgram α} {f : α → VerifierProgram β} {b : β} (h : Returns (p >>=
    f) b) :
    ∃ a, Returns p a ∧ Returns (f a) b := by
  induction p with
  | ret a => exact ⟨a, .ret a, h⟩
  | fail => cases h
  | read k ih =>
    cases h with
    | read x h => obtain ⟨a, ha, hb⟩ := ih x h; exact ⟨a, .read x ha, hb⟩
  | sample k ih =>
    cases h with
    | sample x h => obtain ⟨a, ha, hb⟩ := ih x h; exact ⟨a, .sample x ha, hb⟩
  | grind b k ih =>
    cases h with
    | grind _ h => obtain ⟨a, ha, hb⟩ := ih h; exact ⟨a, .grind _ ha, hb⟩
  | commit hh w k ih =>
    cases h with
    | commit _ _ h => obtain ⟨a, ha, hb⟩ := ih h; exact ⟨a, .commit _ _ ha, hb⟩
  | query i ps k ih =>
    cases h with
    | query _ _ r h => obtain ⟨a, ha, hb⟩ := ih r h; exact ⟨a, .query _ _ r ha, hb⟩

theorem returns_ret {a b : α} (h : Returns (ret a : VerifierProgram α) b) : b = a := by
  cases h; rfl

end VerifierProgram

section Run

variable (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)

/-- A refining program's successful run is the refined program's. -/
theorem run_of_le {α : Type} {p q : VerifierProgram α} (hpq : VerifierProgram.Le p q) :
    ∀ {s : VerifierProgramState} {r : α × VerifierProgramState}, runWithHash H F p s = some r → runWithHash H F q s = some r := by
  induction hpq with
  | fail q => intro s r h; simp [runWithHash] at h
  | ret a => intro s r h; exact h
  | read _ ih =>
    intro s r h
    simp only [runWithHash] at h ⊢
    split at h
    · simp at h
    · next x xs hs => exact ih x h
  | sample _ ih => intro s r h; simp only [runWithHash] at h ⊢; exact ih _ h
  | grind bits _ ih =>
    intro s r h
    simp only [runWithHash] at h ⊢
    split at h
    · simp at h
    · next n xs hs =>
      change (if _ then _ else _) = _ at h
      change (if _ then _ else _) = _
      split at h
      · next hpow => simp only [hpow, ↓reduceIte]; exact ih h
      · simp at h
  | commit height width _ ih =>
    intro s r h
    simp only [runWithHash] at h ⊢
    split at h
    · next x0 x1 xs hs =>
      change (match digestFromHalves (x0, x1) with | some root => _ | none => _) = _ at h
      change (match digestFromHalves (x0, x1) with | some root => _ | none => _) = _
      split at h
      · next root hroot => exact ih h
      · simp at h
    · simp at h
  | query i ps _ ih =>
    intro s r h
    obtain ⟨root, height, width, phase, rest, rows, hr, ho, hp, h⟩ :=
      (runWithHash_query_eq_some_iff H F i ps _ s r).mp h
    exact (runWithHash_query_eq_some_iff H F i ps _ s r).mpr
      ⟨root, height, width, phase, rest, rows, hr, ho, hp, ih rows h⟩

/-- A refining program's accepted proof is the refined program's. -/
theorem runProof_of_le {P Q : VerifierProgram Bool} (hPQ : VerifierProgram.Le P Q) {seed :
    KeccakState} {π : Proof}
    (h : runProofWithHash H F P seed π = true) : runProofWithHash H F Q seed π = true := by
  unfold runProofWithHash at h ⊢
  revert h
  match hr : runWithHash H F P ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ with
  | some (true, s) => rw [run_of_le H F hPQ hr]; exact id
  | some (false, _) => intro h; simp at h
  | none => intro h; simp at h

end Run

end
end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **`ev` refines `ev'` on the bytecode `bytecode`**: at every point, `ev`'s value is `ev'`'s or
refused. -/
def Evaluations.Le (bytecode : List K) (ev ev' : (List K → List E → VerifierProgram E)) : Prop :=
  ∀ point, VerifierProgram.Le (ev bytecode point) (ev' bytecode point)

/-- True claims refine the computed values. -/
theorem claimed_le_computed {bytecode : List K} {c : BytecodeClaim} (hc : c.Holds bytecode) :
    Evaluations.Le bytecode (claimedBytecodeValue c) computedBytecodeValue := by
  intro point
  simp only [claimedBytecodeValue, computedBytecodeValue, VerifierProgram.require]
  split
  · next h => rw [h, ← hc]; exact .ret _
  · exact .fail _

/-- The layout `readAnnouncedSizes` returns carries the bytecode it read. -/
theorem readSizes_bytecode {bytecode : List K} {x : Layout × ℕ}
    (h : VerifierProgram.Returns (readAnnouncedSizes bytecode) x) : x.1.bytecode = bytecode := by
  unfold readAnnouncedSizes at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨layout, hl, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  unfold liftOption at hl
  split at hl
  · cases hl
  · next o ho =>
    rw [VerifierProgram.returns_ret hl]
    unfold buildLayout at ho
    split at ho
    · simp at ho
    · split at ho
      · simp only [Option.some.injEq] at ho; rw [← ho]
      · simp at ho

theorem verifyBusBalance_le {ev ev' : (List K → List E → VerifierProgram E)} {layout : Layout}
    (hev : Evaluations.Le layout.bytecode ev ev') :
    VerifierProgram.Le (verifyBusBalance ev layout) (verifyBusBalance ev' layout) := by
  unfold verifyBusBalance
  refine .bind (.refl _) fun _ ↦ .bind (.refl _) fun _ ↦ .bind (.refl _) fun x ↦ ?_
  obtain ⟨_, _, _⟩ := x
  refine .bind (.refl _) fun _ ↦ .bind (.refl _) fun _ ↦ .bind (.refl _) fun _ ↦
    .bind (.refl _) fun _ ↦ .bind (hev _) fun _ ↦ .refl _

/-- **The verifier's run refines with its evaluations.** -/
theorem verifyExecution_le {ev ev' : (List K → List E → VerifierProgram E)} {bytecode : List K}
    (hev : Evaluations.Le bytecode ev ev') (publicInput : Digest) :
    VerifierProgram.Le (verifyExecutionClaims ev bytecode publicInput) (verifyExecutionClaims ev' bytecode publicInput) := by
  unfold verifyExecutionClaims
  refine (VerifierProgram.Le.refl _).bind_of fun x hx ↦ ?_
  obtain ⟨layout, r⟩ := x
  have hb : layout.bytecode = bytecode := readSizes_bytecode hx
  exact .bind (.refl _) fun _ ↦ .bind (verifyBusBalance_le (hb ▸ hev)) fun _ ↦ .refl _

/-- **The deferring verifier, its claims true, is the deployed verifier**: a proof the deferring
verifier accepts under the deployed IV, with a true claim of the bytecode,
the deployed verifier accepts. -/
theorem verify_of_verifyDeferred {bytecode : List K} {publicInput : Digest} {c : BytecodeClaim}
    {π : Proof} (hc : c.Holds bytecode)
    (h : verifyDeferred bytecode (fiatShamirIv bytecode) publicInput c π = true) :
    verify bytecode publicInput π = true := by
  have hle : VerifierProgram.Le (deferringVerifierProgram c bytecode publicInput) (leanVmVerifierProgram bytecode publicInput) := by
    rw [deferredProgram_eq, leanVmProgram_eq]
    exact .bind (verifyExecution_le (claimed_le_computed hc) publicInput) fun _ ↦ .refl _
  rw [verifyDeferred_eq_withHash] at h
  exact runProof_of_le keccak256 keccakF1600 hle h

end
end LeanVM.Protocol.Verifier
