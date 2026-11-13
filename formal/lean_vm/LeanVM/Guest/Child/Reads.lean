/-
  LeanVM.Guest.Child.Reads

  The scalars a run of the leanVM verifier program reads off the stream: at most `childReads`,
  over every announced size the verifier accepts, so a proof the deferring verifier accepts has a
  stream of at most `8192` scalars (`LeanVM.Guest.Hints.childStreamCap`).
-/

module

public import LeanVM.Protocol.Verifier.Cost
public import Statement.LeanVmGuest
public import LeanVM.Protocol.WithHash
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Guest.AcceptableChild

/-!
# The stream an accepted proof carries

`Reads p n Q` is `VerifierProgram.Costs`' calculus with other weights: a scalar read costs `1`, a
proof of work `1` (its nonce), a commitment `2` (its root's two scalars), and a challenge or an
opening `0`. A run of a program of `n` reads consumes at most `n` scalars of the stream
(`run_reads`), and an accepted run consumes the whole stream (`runProofWithHash`), so its proof's
stream has at most `n` scalars. The verifier's phases are read as `Verifier/Cost.lean` costs them,
with the same crude bounds (the bus's GKR walk over at most `36` levels, at most `30` table
rounds, the Keccak reduction at a point of at most `27` coordinates, the WHIR levels over the 60
admissible ladders, every proof of work charged a nonce). In total `childReads ≤ 8192`
(`childReads_le`), for every check of the fixed polynomial's value that reads nothing (the deployed
and the claimed ones), so every proof the deferring verifier accepts has a stream of at most
`8192` scalars (`stream_le_of_verifyDeferred`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

variable {α β : Type}

/-! ## The calculus -/

/-- **The reads of a program**: every run of `p` reads at most `n` scalars of the stream (a read
`1`, a proof of work `1`, a commitment `2`), and every value it returns satisfies `Q`. -/
def Reads : VerifierProgram α → ℕ → (α → Prop) → Prop
  | .ret a, _, Q => Q a
  | .fail, _, _ => True
  | .read k, n, Q => 1 ≤ n ∧ ∀ x, Reads (k x) (n - 1) Q
  | .sample k, n, Q => 0 ≤ n ∧ ∀ c, Reads (k c) n Q
  | .grind _ k, n, Q => 1 ≤ n ∧ Reads k (n - 1) Q
  | .commit _ _ k, n, Q => 2 ≤ n ∧ Reads k (n - 2) Q
  | .query _ _ k, n, Q => 0 ≤ n ∧ ∀ rows, Reads (k rows) n Q

namespace Reads

theorem mono {p : VerifierProgram α} {n m : ℕ} {Q R : α → Prop} (h : Reads p n Q) (hnm : n ≤ m)
    (hQR : ∀ a, Q a → R a) : Reads p m R := by
  induction p generalizing n m with
  | ret a => exact hQR a h
  | fail => trivial
  | read k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | sample k ih => exact ⟨Nat.zero_le _, fun x ↦ ih x (h.2 x) hnm⟩
  | grind b k ih => exact ⟨by have := h.1; omega, ih h.2 (by omega)⟩
  | commit ht w k ih => exact ⟨by have := h.1; omega, ih h.2 (by omega)⟩
  | query i ps k ih => exact ⟨Nat.zero_le _, fun r ↦ ih r (h.2 r) hnm⟩

theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {n m : ℕ} {Q : α → Prop} {R : β
    → Prop}
    (hp : Reads p n Q) (hf : ∀ a, Q a → Reads (f a) m R) : Reads (p.bind f) (n + m) R := by
  induction p generalizing n with
  | ret a => exact (hf a hp).mono (by omega) fun _ h ↦ h
  | fail => trivial
  | read k ih =>
    refine ⟨by have := hp.1; omega, fun x ↦ ?_⟩
    have := ih x (hp.2 x)
    rwa [show n - 1 + m = n + m - 1 by have := hp.1; omega] at this
  | sample k ih => exact ⟨Nat.zero_le _, fun x ↦ ih x (hp.2 x)⟩
  | grind b k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2
    rwa [show n - 1 + m = n + m - 1 by have := hp.1; omega] at this
  | commit ht w k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2
    rwa [show n - 2 + m = n + m - 2 by have := hp.1; omega] at this
  | query i ps k ih => exact ⟨Nat.zero_le _, fun r ↦ ih r (hp.2 r)⟩

theorem seq {p : VerifierProgram α} {f : α → VerifierProgram β} {a n : ℕ} {Q : α → Prop} {R : β
    → Prop}
    (hp : Reads p a Q) (hf : ∀ x, Q x → Reads (f x) (n - a) R) (ha : a ≤ n) :
    Reads (p >>= f) n R :=
  (bind hp hf).mono (by omega) fun _ h ↦ h

theorem ite {c : Prop} [Decidable c] {p q : VerifierProgram α} {n : ℕ} {Q : α → Prop}
    (hp : c → Reads p n Q) (hq : ¬ c → Reads q n Q) : Reads (if c then p else q) n Q := by
  split
  · exact hp ‹_›
  · exact hq ‹_›

theorem pure0 (a : α) : Reads (pure a : VerifierProgram α) 0 fun _ ↦ True := trivial

theorem readE : Reads VerifierProgram.readScalar 1 fun _ ↦ True := ⟨le_rfl, fun _ ↦ trivial⟩

theorem sampleE : Reads VerifierProgram.sampleChallenge 0 fun _ ↦ True :=
  ⟨le_rfl, fun _ ↦ trivial⟩

theorem readN : ∀ n, Reads (VerifierProgram.readScalars n) n fun xs ↦ xs.length = n
  | 0 => rfl
  | n + 1 => by
    have h := bind readE fun x (_ : True) ↦
      bind (m := 0) (readN n) fun xs (hxs : xs.length = n) ↦
        (show Reads (VerifierProgram.ret (x :: xs)) 0 fun ys ↦ ys.length = n + 1 by
          show (x :: xs).length = n + 1
          simp [hxs])
    exact h.mono (by omega) fun _ h ↦ h

theorem sampleN : ∀ n, Reads (VerifierProgram.sampleChallenges n) 0 fun xs ↦ xs.length = n
  | 0 => rfl
  | n + 1 => by
    have h := bind sampleE fun x (_ : True) ↦
      bind (m := 0) (sampleN n) fun xs (hxs : xs.length = n) ↦
        (show Reads (VerifierProgram.ret (x :: xs)) 0 fun ys ↦ ys.length = n + 1 by
          show (x :: xs).length = n + 1
          simp [hxs])
    exact h.mono (by omega) fun _ h ↦ h

theorem grindP (bits : ℕ) : Reads (VerifierProgram.grindProofOfWork bits) 1 fun _ ↦ True := by
  unfold VerifierProgram.grindProofOfWork
  split
  · trivial
  · exact ⟨le_rfl, trivial⟩

theorem commitP (ht w : ℕ) : Reads (VerifierProgram.readCommitment ht w) 2 fun _ ↦ True := ⟨le_rfl,
    trivial⟩

theorem queryP (i : ℕ) (ps : List ℕ) : Reads (VerifierProgram.queryOpenings i ps) 0 fun _ ↦ True :=
  ⟨le_rfl, fun _ ↦ trivial⟩

theorem require (c : Prop) [Decidable c] {n : ℕ} : Reads (VerifierProgram.require c) n fun _ ↦
    c := by
  unfold VerifierProgram.require
  split
  · exact ‹c›
  · trivial

theorem liftOption (o : Option α) (n : ℕ) : Reads (liftOption o) n fun a ↦ o = some a := by
  cases o
  · trivial
  · rfl

end Reads

/-! ## A run reads at most its reads -/

/-- **A run of a program of `n` reads consumes at most `n` scalars of the stream.** -/
theorem run_reads (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState) :
    ∀ {p : VerifierProgram α} {n : ℕ} {Q : α → Prop}, Reads p n Q → ∀ {s : VerifierProgramState} {r
        : α × VerifierProgramState},
      Compile.runWithHash H F p s = some r → ∃ xs, s.stream = xs ++ r.2.stream ∧ xs.length ≤ n := by
  intro p
  induction p with
  | ret a =>
    intro n Q _ s r h
    simp only [Compile.runWithHash] at h
    cases h
    exact ⟨[], rfl, Nat.zero_le _⟩
  | fail => intro n Q _ s r h; simp [Compile.runWithHash] at h
  | read k ih =>
    intro n Q hp s r h
    simp only [Compile.runWithHash] at h
    split at h
    · next x xs hs _ =>
      obtain ⟨ys, hys, hl⟩ := ih x (hp.2 x) h
      refine ⟨x :: ys, ?_, ?_⟩
      · rw [hs]; simp only at hys; rw [hys]; rfl
      · simp only [List.length_cons]; have := hp.1; omega
    · simp at h
  | sample k ih =>
    intro n Q hp s r h
    simp only [Compile.runWithHash] at h
    obtain ⟨ys, hys, hl⟩ := ih (Id.run (squeeze F s.sponge)).1 (hp.2 _)
      (s := { s with sponge := (Id.run (squeeze F s.sponge)).2 }) h
    exact ⟨ys, hys, hl⟩
  | grind b k ih =>
    intro n Q hp s r h
    simp only [Compile.runWithHash] at h
    split at h
    · next x xs hs _ =>
      change (if _ then _ else _) = _ at h
      split at h
      · obtain ⟨ys, hys, hl⟩ := ih hp.2 h
        refine ⟨x :: ys, ?_, ?_⟩
        · rw [hs]; simp only at hys; rw [hys]; rfl
        · simp only [List.length_cons]; have := hp.1; omega
      · simp at h
    · simp at h
  | commit ht w k ih =>
    intro n Q hp s r h
    simp only [Compile.runWithHash] at h
    split at h
    · next x0 x1 xs hs _ =>
      obtain ⟨ys, hys, hl⟩ := ih hp.2 h
      refine ⟨x0 :: x1 :: ys, ?_, ?_⟩
      · rw [hs]; simp only at hys; rw [hys]; rfl
      · simp only [List.length_cons]; have := hp.1; omega
    · simp at h
  | query i ps k ih =>
    intro n Q hp s r h
    obtain ⟨_, _, _, _, _, rows, _, _, _, h'⟩ :=
      (Compile.runWithHash_query_eq_some_iff H F i ps k s r).mp h
    obtain ⟨ys, hys, hl⟩ := ih rows (hp.2 rows) h'
    exact ⟨ys, hys, hl⟩

/-- **An accepted proof's stream has at most the program's reads.** -/
theorem stream_le_of_runProof (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState) {P : VerifierProgram Bool}
    {n : ℕ} {Q : Bool → Prop} (hP : Reads P n Q) {seed : KeccakState} {π : Proof}
    (h : runProofWithHash H F P seed π = true) : π.stream.length ≤ n := by
  unfold runProofWithHash at h
  revert h
  match hr : Compile.runWithHash H F P ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ with
  | some (true, s) =>
    intro h
    obtain ⟨xs, hxs, hl⟩ := run_reads H F hP hr
    have he : s.stream = [] := by
      have h' : (s.stream.isEmpty && s.openings.isEmpty) = true := h
      simp only [Bool.and_eq_true, List.isEmpty_iff] at h'
      exact h'.1
    rw [he, List.append_nil] at hxs
    have e : π.stream = xs := hxs
    rw [e]
    exact hl
  | some (false, _) => intro h; simp at h
  | none => intro h; simp at h

/-! ## The reads of the verifier's phases -/

/-- One sumcheck round of `count` coefficients: the polynomial's reads (at least one) and its proof
of work. -/
def roundReads (count : ℕ) : ℕ := max count 2 - 1 + 1

/-- One GKR step of `step` levels at a point of `L` coordinates. -/
def gkrStepReads (step L : ℕ) : ℕ := 1 + L * roundReads (2 ^ step + 1) + 3 * 2 ^ step + 1

/-- The GKR walk over `n` remaining levels from a point of `L` coordinates, as `gkrCost`. -/
def gkrReads : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, L => gkrStepReads 1 L + gkrReads 0 (1 + L)
  | n + 2, L =>
    if n % 2 = 1 then gkrStepReads 1 L + gkrReads (n + 1) (1 + L)
    else gkrStepReads 2 L + gkrReads n (2 + L)

/-- The GKR walk over at most `36` levels. -/
def gkrReadsBound : ℕ := gkrReads 36 0

/-- The GKR walk over at most `36` levels reads at most `gkrReadsBound`. -/
theorem gkrReads_le : ∀ D ≤ 36, gkrReads D 0 ≤ gkrReadsBound := by decide

/-- The bus phase. -/
def busReads : ℕ := 1 + 0 + 0 + (2 + gkrReadsBound) + 4 + (1 + busBits * roundReads 3 + 1)

/-- The table phase. -/
def tableReads : ℕ := 1 + 0 + (30 * roundReads 4 + tableWidthSum)

/-- One fold round: four reads and a proof of work. -/
def foldRoundReads : ℕ := 4 + 1 + 0

/-- The WHIR levels from a message of `μ` variables, as `whirCost`. -/
def whirReads : ℕ → List Whir.Level → ℕ
  | _, [] => 0
  | μ, [level] =>
    foldRoundReads * level.fold + (2 ^ (μ - level.fold) + level.fold) + 1 +
      (μ - level.fold) * roundReads 3
  | μ, level :: next :: rest =>
    foldRoundReads * level.fold + 2 + level.fold + 1 + 1 + 1 +
      whirReads (μ - level.fold) (next :: rest)

/-- The bound on the WHIR levels' reads over every admissible ladder (`ladder_reads`). -/
def whirReadsBound : ℕ := 249

/-- One layer of the Keccak reduction at a point of `L` coordinates. -/
def keccakLayerReads (L : ℕ) : ℕ :=
  productBits + 1 + 0 + L * roundReads 3 + keccakLocalBits * roundReads 4 + 3 + 1 + 0

/-- The Keccak reduction at a point of `L` coordinates. -/
def keccakReads (L : ℕ) : ℕ :=
  1 + 0 + 0 + 1 + keccakDepth * keccakLayerReads L + (qkeccakSlotBits * roundReads 3 + 1) +
    4 * roundReads 3 + qkeccakSlotBits * roundReads 3 + kBits

/-- The stack's out-of-domain sample: a proof of work and a read. -/
def oodReads : ℕ := 1 + 0 + 1

/-- Ring switching: a proof of work. -/
def ringReads : ℕ := 1 + 0

/-- **The reads of the leanVM verifier program**, phase by phase. -/
def childReads : ℕ :=
  8 + 2 + oodReads + busReads + tableReads + 0 + keccakReads 27 + ringReads + (0 + whirReadsBound)

section Phases

theorem reads_liftOption {α : Type} (o : Option α) (n : ℕ) :
    Reads (liftOption o) n fun a ↦ o = some a := by
  cases o
  · trivial
  · rfl

/-- A round polynomial of `count` coefficients reads `count - 1` of them (at least one), then
grinds. -/
theorem reads_sumcheckRoundPoly (count : ℕ) (claim : E) (eq : Option E) :
    Reads (sumcheckRoundPoly count claim eq) (max count 2 - 1 + 1)
      fun _ ↦ True := by
  cases eq with
  | none =>
    refine Reads.seq Reads.readE (fun _ _ ↦
        Reads.seq (Reads.readN _)
      (fun _ _ ↦ Reads.seq (Reads.grindP _)
        (fun _ _ ↦ trivial) ?_) ?_) ?_ <;> omega
  | some r =>
    exact Reads.seq (Reads.readN _) (fun _ _ ↦
      Reads.seq (Reads.grindP _) (fun _ _ ↦ trivial) (by omega))
      (by omega)

/-- A sumcheck of `k` rounds costs `k · roundReads count`, and returns `k` challenges. -/
theorem reads_sumcheck (count : ℕ) : ∀ (claim : E) (eqs : List (Option E)),
    Reads (sumcheck claim count eqs) (eqs.length * roundReads count)
      fun r ↦ r.1.length = eqs.length
  | _, [] => rfl
  | claim, e :: es => by
    refine Reads.seq (reads_sumcheckRoundPoly count claim e) (fun msg _ ↦
      Reads.seq Reads.sampleE (fun c _ ↦
        Reads.seq (reads_sumcheck count _ es) (fun r hr ↦ ?_) ?_) ?_) ?_
    · obtain ⟨point, final⟩ := r
      show (c :: point).length = (e :: es).length
      simpa using hr
    all_goals simp only [List.length_cons, Nat.succ_mul, roundReads]; omega

/-! ## The bus -/

theorem reads_gkrStep (step : ℕ) (last : Bool) (s : GkrState) :
    Reads (gkrStep step last s) (gkrStepReads step s.point.length)
      fun t ↦ t.point.length = step + s.point.length := by
  refine Reads.seq (Reads.grindP _) (fun _ _ ↦
    Reads.seq Reads.sampleE (fun _ _ ↦
    Reads.seq (reads_sumcheck _ _ (s.point.map some)) (fun r hr ↦ ?_) ?_) ?_) ?_
  · obtain ⟨x, claim⟩ := r
    refine Reads.seq (Reads.readN _) (fun c0 _ ↦
        Reads.seq (Reads.readN _)
      (fun c1 _ ↦ Reads.seq (Reads.readN _) (fun c2 _ ↦
        Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
          Reads.seq (Reads.grindP _) (fun _ _ ↦
          Reads.seq (Reads.sampleN step) (fun y hy ↦ ?_) ?_) ?_)
            ?_) ?_) ?_) ?_
    · show (y ++ x).length = step + s.point.length
      simp only [List.length_map] at hr
      simp [hy, hr]
    all_goals simp only [gkrStepReads, List.length_map]; omega
  all_goals simp only [gkrStepReads, List.length_map]; omega

/-- The GKR walk costs `gkrReads`. -/
theorem reads_gkrLayers : ∀ (n : ℕ) (s : GkrState),
    Reads (gkrLayers n s) (gkrReads n s.point.length) fun _ ↦ True
  | 0, _ => trivial
  | 1, s => by
    refine Reads.seq (reads_gkrStep 1 true s) (fun t ht ↦
      (reads_gkrLayers 0 t).mono (by simp [gkrReads]) fun _ h ↦ h) ?_
    simp only [gkrReads]; omega
  | n + 2, s => by
    simp only [gkrLayers, gkrReads]
    split
    · refine Reads.seq (reads_gkrStep 1 false s) (fun t ht ↦
        (reads_gkrLayers (n + 1) t).mono (by rw [ht]; omega) fun _ h ↦ h) (by omega)
    · refine Reads.seq (reads_gkrStep 2 _ s) (fun t ht ↦
        (reads_gkrLayers n t).mono (by rw [ht]; omega) fun _ h ↦ h) (by omega)

/-- The GKR grand products: the two roots and the walk. -/
theorem reads_verifyGkrGrandProducts (depth : ℕ) :
    Reads (verifyGkrGrandProducts depth) (2 + gkrReads depth 0) fun _ ↦
        True := by
  refine Reads.seq Reads.readE (fun _ _ ↦ Reads.seq
      Reads.readE
    (fun _ _ ↦ Reads.seq (reads_gkrLayers depth _) (fun _ _ ↦ trivial) ?_)
        ?_) ?_ <;>
    (try simp only [List.length_nil]) <;> omega

/-- The bytecode's share: a read, a sumcheck over the tuple slot, a read. -/
theorem reads_bytecodeShare (weights bytecodeLow : List E) :
    Reads (bytecodeShare weights bytecodeLow)
      (1 + busBits * roundReads 3 + 1) fun _ ↦ True := by
  refine Reads.seq Reads.readE (fun _ _ ↦
    Reads.seq (reads_sumcheck 3 _ _) (fun r _ ↦ ?_) ?_) ?_
  · obtain ⟨slotPoint, claim⟩ := r
    exact Reads.seq Reads.readE (fun _ _ ↦
      Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦ trivial)
        (Nat.zero_le _)) (by rw [List.length_replicate]; omega)
  all_goals (try simp only [List.length_replicate]); omega

theorem reads_verifyBusBalance (ev : List K → List E → E → VerifierProgram Unit)
    (hev : ∀ w p v, Reads (ev w p v) 0 fun _ ↦ True) (layout : Layout)
    (hm : layout.logMemory ≤ 30) (hb : layout.logBytecode ≤ 30) :
    Reads (verifyBusBalance ev layout)
      (1 + 0 + 0 + (2 + gkrReads (busLayout [0, layout.logMemory, layout.logBytecode]
        layout.push).depth 0) + 4 + (1 + busBits * roundReads 3 + 1))
      fun r ↦ ClaimsShort r.claims := by
  refine Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
    Reads.seq (Reads.grindP _) (fun _ _ ↦
    Reads.seq (Reads.sampleN _) (fun _ _ ↦
      Reads.seq Reads.sampleE
    (fun _ _ ↦ Reads.seq (reads_verifyGkrGrandProducts _) (fun r _ ↦ ?_) ?_) ?_)
      ?_) ?_) (Nat.zero_le _)
  · obtain ⟨countRoot, point, treeValues⟩ := r
    refine Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
        Reads.seq (Reads.readN 2)
      (fun memory hmem ↦ Reads.seq Reads.readE (fun _ _ ↦
          Reads.seq Reads.readE (fun _ _ ↦
            Reads.seq (reads_bytecodeShare _ _) (fun r _ ↦ ?_) ?_) ?_) ?_) ?_)
        (Nat.zero_le _)
    · obtain ⟨share, bytecodePoint, value⟩ := r
      refine Reads.seq (hev _ _ _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      intro c hc _
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
        simp only [List.getElem_zipWith, List.length_take]
        omega
      · simp only [List.length_take]; omega
      · simp only [List.length_take]; omega
    all_goals omega
  all_goals omega


theorem reads_readSizes (bytecode : List K) :
    Reads (readAnnouncedSizes bytecode) 8 SizesOK := by
  rw [readAnnouncedSizes_eq]
  refine Reads.seq (Reads.readN _) (fun _ _ ↦ (Reads.liftOption _ _).mono le_rfl fun x hx ↦ ?_)
    (by simp [tables])
  have s := sizesOf_spec hx
  exact ⟨layoutBounds_of_buildLayout s.layout, s.rate_ge, s.rate_le, s.stack_ge, s.stack_le⟩

/-- The push side of a built layout has depth at most `36`. -/

theorem reads_verifyBusBalance_le (ev : List K → List E → E → VerifierProgram Unit)
    (hev : ∀ w p v, Reads (ev w p v) 0 fun _ ↦ True) {layout : Layout}
    (h : LayoutBounds layout) :
    Reads (verifyBusBalance ev layout) busReads
      fun r ↦ ClaimsShort r.claims :=
  (reads_verifyBusBalance ev hev layout h.logMemory_le h.logBytecode_le).mono
    (by have := gkrReads_le _ (pushDepth_le h); unfold busReads; omega) fun _ h ↦ h


theorem reads_tableTerms (constraintPowers formPowers point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), ClaimsShort claims → (∀ r ∈ rows, r.2.1 ≤ 30) →
      Reads
        (tableTermsClaims constraintPowers formPowers point rows cursor final claims)
        (rows.map (·.1.width)).sum fun r ↦ ClaimsShort r.2
  | [], _, _, claims, hc, _ => hc
  | (table, h, forms, weight) :: rest, cursor, final, claims, hc, hh => by
    have h0 : h ≤ 30 := hh _ List.mem_cons_self
    refine Reads.seq (Reads.readN _) (fun evals _ ↦
      (reads_tableTerms constraintPowers formPowers point rest _ _ _ ?_
        fun r hr ↦ hh r (List.mem_cons_of_mem _ hr)).mono ?_ fun _ h ↦ h) ?_
    · intro c hc' hcol
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact hc c hc' hcol
      · obtain ⟨⟨v, col⟩, -, rfl⟩ := List.mem_map.mp hc'
        simp only [List.length_take]
        omega
    · simp only [List.map_cons, List.sum_cons]; omega
    · simp only [List.map_cons, List.sum_cons]; omega

private theorem foldl_max_le (M : ℕ) : ∀ (l : List ℕ) (acc : ℕ), acc ≤ M → (∀ x ∈ l, x ≤ M) →
    l.foldl max acc ≤ M
  | [], _, h, _ => h
  | x :: xs, acc, h, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le M xs _ (max_le h (hl x List.mem_cons_self))
      fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)

/-- The widths of the first components of a zip are at most the widths of the list. -/

theorem reads_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E)
    (hh : ∀ h ∈ heights, h ≤ 30) :
    Reads
      (tableSumcheckClaims heights busForms constraintPowers formPowers equalityPoint target)
      (30 * roundReads 4 + tableWidthSum) fun cl ↦ ClaimsShort cl := by
  have hmax := foldl_max_le 30 heights 0 (Nat.zero_le _) hh
  have hr4 : roundReads 4 = 4 := rfl
  refine Reads.seq (reads_sumcheck _ _ _) (fun r _ ↦ ?_) ?_
  · obtain ⟨challenges, claim⟩ := r
    have hrows : ∀ r ∈ List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint challenges.reverse))), r.2.1 ≤ 30 := by
      intro r hr
      exact hh _ (List.of_mem_zip (List.of_mem_zip hr).2).1
    refine Reads.seq (reads_tableTerms _ _ _ _ 0 0 [] (fun _ h ↦
        by simp at h) hrows)
      (fun r hr ↦ ?_) ?_
    · obtain ⟨final, claims⟩ := r
      exact Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦ hr)
          (Nat.zero_le _)
    · simp only [List.length_replicate, hr4]
      have := sum_width_zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint challenges.reverse)))
      unfold tableWidthSum
      omega
  · simp only [List.length_replicate, hr4]
    omega

/-- **The table phase** on a built layout. -/
theorem reads_tablePhase {layout : Layout} (hl : LayoutBounds layout) (bus : BusResult)
    (hbus : ClaimsShort bus.claims) :
    Reads (tablePhaseClaims layout bus) tableReads
      fun cl ↦ ClaimsShort cl :=
  Reads.seq (Reads.grindP _) (fun _ _ ↦
  Reads.seq Reads.sampleE (fun _ _ ↦ Reads.seq
    (reads_tableSumcheck _ _ _ _ _ _ hl.heights_le) (fun cl hcl ↦ by
      intro c hc hcol
      rcases List.mem_append.mp hc with hc | hc
      · exact hbus c hc hcol
      · exact hcl c hc hcol) (by unfold tableReads; omega)) (by unfold tableReads; omega))
    (by unfold tableReads; omega)

/-- **The public-input phase**: one challenge; its claims are on the memory's columns. -/
theorem reads_publicInputPhase (layout : Layout) (publicInput : Digest) :
    Reads (publicInputPhase layout publicInput) 0 fun cl ↦ ClaimsShort
        cl := by
  rw [publicInputPhase_eq]
  refine Reads.seq Reads.sampleE (fun _ _ ↦ (Reads.liftOption _ _).mono le_rfl fun cl hcl ↦ ?_) (by omega)
  rw [publicClaimsOf_spec hcl]
  simp only [publicClaims]
  intro c hc hcol
  exfalso
  have hbase : ∀ x ∈ keccakOutputColumns, 5 ≤ x := by
    intro x hx
    simp only [keccakOutputColumns, List.mem_map] at hx
    obtain ⟨_, -, rfl⟩ := hx
    have : 5 ≤ globalColumnBases.getD opKeccak 0 := by decide
    omega
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  simp only [List.getElem_zipWith] at hcol
  have hi' : i < 2 := by simp at hi; omega
  have hle : [memory0, memory1][i] < 2 := by
    interval_cases i <;> simp [memory0, memory1]
  have := hbase _ hcol
  omega


theorem reads_keccakPackRounds : ∀ (point : List E) (value scale : E),
    Reads (keccakPackRounds point value scale) (point.length * roundReads 3)
      fun r ↦ r.2.2.length = point.length
  | [], _, _ => rfl
  | r :: rs, value, scale => by
    refine Reads.seq (reads_sumcheckRoundPoly 3 _ _) (fun _ _ ↦
        Reads.seq
      Reads.sampleE (fun c _ ↦ Reads.seq (reads_keccakPackRounds
          rs _ _)
        (fun t ht ↦ ?_) ?_) ?_) ?_
    · obtain ⟨v, s, p⟩ := t
      show (c :: p).length = (r :: rs).length
      simpa using ht
    all_goals simp only [List.length_cons, Nat.succ_mul, roundReads]; omega

/-- One layer of the Keccak reduction keeps the claim's point length. -/
theorem reads_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    Reads (verifyKeccakLayer logSteps step claim)
      (keccakLayerReads claim.point.length) fun c ↦ c.point.length = claim.point.length := by
  have hr4 : roundReads 4 = 4 := rfl
  have hr3 : roundReads 3 = 3 := rfl
  refine Reads.seq (Reads.readN _) (fun _ _ ↦
      Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
    Reads.seq (Reads.grindP _) (fun _ _ ↦
      Reads.seq Reads.sampleE (fun _ _ ↦
      Reads.seq (reads_keccakPackRounds _ _ _) (fun r hr ↦ ?_) ?_) ?_) ?_) ?_) ?_
  · obtain ⟨value, scale, point⟩ := r
    refine Reads.seq (reads_sumcheck 4 _ _) (fun r _ ↦ ?_) ?_
    · obtain ⟨localPoint, value⟩ := r
      refine Reads.seq (Reads.readN 3) (fun _ _ ↦
          Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
            Reads.seq (Reads.grindP _) (fun _ _ ↦
            Reads.seq Reads.sampleE (fun _ _ ↦ hr) ?_) ?_) ?_) ?_
      all_goals simp only [keccakLayerReads, List.length_replicate, hr4, hr3]
      all_goals omega
    · simp only [keccakLayerReads, List.length_replicate, hr4, hr3]
      omega
  all_goals simp only [keccakLayerReads, hr4, hr3]; omega

/-- The Keccak layers keep the claim's point length. -/
theorem reads_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    Reads (keccakLayers logSteps steps claim)
      (steps.length * keccakLayerReads claim.point.length)
      fun c ↦ c.point.length = claim.point.length
  | [], _ => rfl
  | s :: ss, claim => by
    refine Reads.seq (reads_verifyKeccakLayer logSteps s claim) (fun c hc ↦
      (reads_keccakLayers logSteps ss c).mono (by
        rw [hc]; simp only [List.length_cons, Nat.succ_mul]; omega) fun _ h ↦ h.trans hc) ?_
    simp only [List.length_cons, Nat.succ_mul]; omega

/-- Opening `q_keccak`: a sumcheck over the slot. -/
theorem reads_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    Reads (keccakOpen logSteps claim first count value)
      (qkeccakSlotBits * roundReads 3) fun _ ↦ True :=
  Reads.seq (reads_sumcheck 3 _ _) (fun _ _ ↦ trivial)
    (by simp only [List.length_replicate]; omega)

/-- **The Keccak reduction** at an instance point of at most `30` coordinates. -/
theorem reads_verifyKeccak (logSteps : ℕ) (inst output : List E) (hi : inst.length ≤ 30) :
    Reads (verifyKeccak logSteps inst output) (keccakReads 27) fun _ ↦
        True := by
  have hL : (inst.drop 4).length + keccakSegmentBits ≤ 27 := by
    simp only [List.length_drop, keccakSegmentBits]
    have : log2Ceil keccakSegments = 1 := by decide
    omega
  have h1 : 1 < keccakSegments := by decide
  have hr3 : roundReads 3 = 3 := rfl
  unfold verifyKeccak
  simp only [h1, ↓reduceIte]
  refine Reads.seq (Reads.grindP _) (fun _ _ ↦
    Reads.seq (Reads.sampleN _) (fun segment hseg ↦
      Reads.seq
    (Reads.sampleN _) (fun _ _ ↦ Reads.seq
        Reads.readE (fun committed _ ↦ ?_) ?_)
    ?_) ?_) ?_
  · have hpl : (inst.drop 4 ++ segment).length ≤ 27 := by
      rw [List.length_append, hseg]; exact hL
    have hlay : keccakDepth * keccakLayerReads (inst.drop 4 ++ segment).length ≤
        keccakDepth * keccakLayerReads 27 := by
      refine Nat.mul_le_mul_left _ ?_
      unfold keccakLayerReads
      have := Nat.mul_le_mul_right (roundReads 3) hpl
      omega
    refine Reads.seq (reads_keccakLayers logSteps (List.range keccakDepth) _)
      (fun claim _ ↦ Reads.seq (reads_keccakOpen logSteps _ 1 _ _) (fun r _ ↦
        Reads.seq Reads.readE (fun word _ ↦
            Reads.seq
          (Reads.require (n := 0) _) (fun _ _ ↦ Reads.seq
              (Reads.pure0 _)
            (fun outputs _ ↦ Reads.seq (reads_sumcheck 3 _ _) (fun r2 _ ↦
              Reads.seq (reads_keccakOpen logSteps _ 0 _ _) (fun r3 _ ↦
                Reads.seq (Reads.readN kBits) (fun slices _ ↦
                  Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
                      trivial)
                    (Nat.zero_le _)) ?_) ?_) ?_) (Nat.zero_le _)) (Nat.zero_le _)) ?_) ?_) ?_
    all_goals simp only [keccakReads, keccakFirstClaim, List.length_range, List.length_replicate,
      hr3] at hlay ⊢
    all_goals omega
  all_goals simp only [keccakReads, hr3]; omega

/-- The first claim on a `KECCAK` output lane is at a point of at most `30` coordinates. -/

theorem reads_keccakPhase (layout : Layout) (claims : List ColumnClaim)
    (hc : ClaimsShort claims) :
    Reads (keccakPhaseClaims layout claims) (keccakReads 27) fun _ ↦
        True := by
  exact Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
      Reads.seq
    (reads_verifyKeccak _ _ _ (headD_filter_short claims hc)) (fun _ _ ↦ trivial) le_rfl)
    (Nat.zero_le _)

/-- **Ring switching**: a proof of work and sixteen challenges. -/
theorem reads_ringSwitch (point s : List E) :
    Reads (ringSwitch point s) ringReads fun _ ↦ True := by
  rw [ringSwitch_eq]
  exact Reads.seq (Reads.grindP _) (fun _ _ ↦
    Reads.seq (Reads.sampleN _) (fun _ _ ↦ (Reads.liftOption _ _).mono le_rfl fun _ _ ↦ trivial)
      (by simp [ringReads])) (by simp [ringReads])

/-- **The stack's out-of-domain sample**, on a stack of at most `28` variables. -/
theorem reads_readOod (stackLog : ℕ) :
    Reads (readOod stackLog) oodReads fun _ ↦ True := by
  rw [readOod_eq]
  exact Reads.seq (Reads.grindP _) (fun _ _ ↦
    Reads.seq (Reads.sampleN _) (fun _ _ ↦
      Reads.seq Reads.readE (fun _ _ ↦ (Reads.liftOption _ _).mono le_rfl fun _ _ ↦ trivial) (by
        unfold oodReads; omega)) (by unfold oodReads; omega)) (by unfold oodReads; omega)


theorem reads_foldRound (s : WhirState) :
    Reads (foldRound s) foldRoundReads
      fun r ↦ r.1.alphas.length = s.alphas.length + 1 := by
  refine Reads.seq Reads.readE (fun _ _ ↦
    Reads.seq Reads.readE (fun _ _ ↦
    Reads.seq Reads.readE (fun _ _ ↦
    Reads.seq Reads.readE (fun _ _ ↦
    Reads.seq (Reads.grindP _) (fun _ _ ↦
    Reads.seq Reads.sampleE (fun _ _ ↦
    Reads.seq Reads.sampleE (fun _ _ ↦ ?_)
      ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · show (s.alphas ++ [_]).length = s.alphas.length + 1
    simp
  all_goals simp only [foldRoundReads]; omega

/-- A level's fold rounds; they append one `α` each. -/
theorem reads_foldRounds : ∀ (n : ℕ) (s : WhirState),
    Reads (foldRounds n s) (foldRoundReads * n)
      fun r ↦ r.1.alphas.length = s.alphas.length + n
  | 0, _ => rfl
  | n + 1, s => by
    refine Reads.seq (reads_foldRound s) (fun r hr ↦ ?_) ?_
    · obtain ⟨s', round⟩ := r
      refine Reads.seq (reads_foldRounds n s') (fun r' hr' ↦ ?_) ?_
      · obtain ⟨s'', rounds⟩ := r'
        show s''.alphas.length = s.alphas.length + (n + 1)
        simp only at hr hr'
        omega
      · rw [Nat.mul_succ]; omega
    · rw [Nat.mul_succ]; omega

theorem reads_sampleQueriesAux (depth : ℕ) :
    ∀ (fuel remaining : ℕ), Reads (sampleQueriesAux depth fuel remaining) 0 fun _ ↦ True
  | 0, _ => trivial
  | fuel + 1, remaining => by
    refine Reads.ite (fun _ ↦ trivial) fun _ ↦ Reads.seq Reads.sampleE
      (fun c _ ↦ Reads.seq (reads_sampleQueriesAux depth fuel _) (fun qs _ ↦ trivial) le_rfl)
      le_rfl

/-- **The WHIR levels** from a message of `μ` variables read `whirReads μ levels`. -/
theorem reads_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (μ : ℕ),
      logN - s.alphas.length = μ →
      Reads (whirLevels logN laneFolds evaluateBasis index levels s)
        (whirReads μ levels) fun _ ↦ True
  | [], _, _, _, _ => trivial
  | [level], index, s, μ, hμ => by
    have hr3 : roundReads 3 = 3 := rfl
    simp only [whirReads]
    generalize hP : 2 ^ (μ - level.fold) = P
    refine Reads.seq (reads_foldRounds level.fold s) (fun r hr ↦ ?_) (by omega)
    obtain ⟨s', rounds⟩ := r
    simp only at hr
    have hm : logN - s'.alphas.length = μ - level.fold := by rw [hr]; omega
    refine Reads.seq (Reads.readN _) (fun _ _ ↦
      Reads.seq (Reads.grindP _) (fun _ _ ↦ Reads.seq
        (reads_sampleQueriesAux _ level.queries level.queries) (fun queries _ ↦ ?_)
          ?_) ?_) ?_
    · refine Reads.seq (Reads.queryP index queries) (fun words _ ↦
        Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
          Reads.seq (reads_sumcheck 3 _ _) (fun r _ ↦ ?_) ?_) (Nat.zero_le _)) ?_
      · obtain ⟨tail, claim⟩ := r
        exact (Reads.require (n := 0) _).mono (Nat.zero_le _) fun _ _ ↦ trivial
      all_goals (try simp only [hm, hP, hr3, List.length_replicate])
      all_goals omega
    all_goals (try simp only [hm, hP, hr3])
    all_goals omega
  | level :: next :: rest, index, s, μ, hμ => by
    simp only [whirReads]
    refine Reads.seq (reads_foldRounds level.fold s) (fun r hr ↦ ?_) (by omega)
    obtain ⟨s', rounds⟩ := r
    simp only at hr
    have hm : logN - s'.alphas.length = μ - level.fold := by rw [hr]; omega
    refine Reads.seq (Reads.commitP _ _) (fun _ _ ↦
      Reads.seq (Reads.readN _) (fun _ _ ↦
      Reads.seq (Reads.grindP _) (fun _ _ ↦
      Reads.seq (Reads.sampleN _) (fun _ _ ↦
      Reads.seq Reads.readE (fun _ _ ↦
      Reads.seq (Reads.grindP _) (fun _ _ ↦
      Reads.seq (reads_sampleQueriesAux _ level.queries level.queries) (fun queries _ ↦ ?_)
          ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · refine Reads.seq Reads.sampleE (fun lam _ ↦
        Reads.seq (Reads.queryP index queries) (fun words _ ↦
          (reads_whirLevels logN laneFolds evaluateBasis (next :: rest) (index + 1) _
            (μ - level.fold) (by rw [glueLevel_alphas]; exact hm)).mono ?_
            fun _ h ↦ h) ?_) ?_
      all_goals omega
    all_goals omega

/-- **WHIR** on a stack whose every ladder reads at most `W`. -/
theorem reads_verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E)
    (W : ℕ) (hW : ∀ levels, Whir.ladder logN logInvRate = some levels → whirReads logN levels ≤ W) :
    Reads (verifyWhir logN logInvRate target evaluateBasis) W fun _ ↦ True :=
  Reads.seq (Reads.liftOption _ 0) (fun config hc ↦
    (reads_whirLevels logN _ evaluateBasis config 0 _ logN rfl).mono
      (by have := hW config hc; omega) fun _ h ↦ h)
    (Nat.zero_le _)

/-- **The stack's commitment.** -/
theorem reads_commitStack (logN logInvRate : ℕ) :
    Reads (commitStack logN logInvRate) 2 fun _ ↦ True := by
  rw [commitStack_eq]
  exact Reads.seq (Reads.liftOption _ 0) (fun _ _ ↦ Reads.commitP _ _) (Nat.zero_le _)

/-- **The stacked opening**: the batching challenge and WHIR. -/
theorem reads_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (W : ℕ) (hW : ∀ levels, Whir.ladder stackLog logInvRate = some levels →
      whirReads stackLog levels ≤ W) :
    Reads (verifyStackedOpening stackLog logInvRate claims) W fun _ ↦ True := by
  rw [verifyStackedOpening_nf]
  exact Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
    Reads.seq Reads.sampleE (fun _ _ ↦
      (reads_verifyWhir _ _ _ _ W hW).mono (by omega) fun _ h ↦ h) (by omega)) (Nat.zero_le _)


/-! ## Every admissible ladder -/

/-- Over every admissible ladder the WHIR levels read at most `whirReadsBound` scalars;
decided over the 56 admissible pairs. -/
theorem ladder_reads (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) : whirReads μ levels ≤ whirReadsBound := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels → whirReads μ levels ≤ whirReadsBound := by
      decide +kernel
    exact key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2)
      hadm levels h
  · simp [Whir.ladder, hadm] at h

/-! ## The whole program -/

/-- **The reads of `verify_execution`**, for a check of the fixed polynomial's value that reads
nothing. -/
theorem reads_verifyExecution (ev : List K → List E → E → VerifierProgram Unit)
    (hev : ∀ w p v, Reads (ev w p v) 0 fun _ ↦ True)
    (bytecode : List K) (publicInput : Digest) :
    Reads (verifyExecutionClaims ev bytecode publicInput) childReads
      fun _ ↦ True := by
  unfold childReads
  refine Reads.seq (reads_readSizes bytecode) (fun p hp ↦ ?_) (by omega)
  obtain ⟨layout, logInverseRate⟩ := p
  obtain ⟨hl, -, -, -, -⟩ := hp
  refine Reads.seq (reads_commitStack _ _) (fun _ _ ↦ Reads.seq (reads_readOod _) (fun ood _ ↦
    Reads.seq (reads_verifyBusBalance_le ev hev hl) (fun bus hbus ↦
        Reads.seq
      (reads_tablePhase hl bus hbus) (fun claims hcl ↦ Reads.seq
        (reads_publicInputPhase layout publicInput) (fun publicClaims hpc ↦
          Reads.seq (reads_keccakPhase layout _ ?_) (fun r _ ↦ ?_) ?_) ?_)
              ?_) ?_) ?_) ?_
  · intro c hc hcol
    rcases List.mem_append.mp hc with hc | hc
    · exact hcl c hc hcol
    · exact hpc c hc hcol
  · obtain ⟨claims', keccakPoint, keccakSlices⟩ := r
    refine Reads.seq (reads_ringSwitch keccakPoint keccakSlices) (fun r _ ↦ ?_) ?_
    · obtain ⟨ringTarget, ringWeight⟩ := r
      exact reads_verifyStackedOpening _ _ _ whirReadsBound fun levels h ↦
        ladder_reads _ _ levels h
    · omega
  all_goals omega

/-- The deployed check of the fixed polynomial's value reads nothing. -/
theorem reads_computedBytecodeValue (w : List K) (p : List E) (v : E) :
    Reads (computedBytecodeValue w p v) 0 fun _ ↦ True :=
  (Reads.require (n := 0) _).mono le_rfl fun _ _ ↦ trivial

/-- The deferring check of the fixed polynomial's value reads nothing. -/
theorem reads_claimedBytecodeValue (claim : BytecodeClaim) (w : List K) (p : List E) (v : E) :
    Reads (claimedBytecodeValue claim w p v) 0 fun _ ↦ True :=
  (Reads.require (n := 0) _).mono le_rfl fun _ _ ↦ trivial

end Phases

/-- The reads, evaluated: at most `8192`. -/
theorem childReads_le : childReads ≤ LeanVM.Guest.Coverage.childStreamCap := by decide

/-- **A proof the deferring verifier accepts has a stream of at most `8192` scalars.** -/
theorem stream_le_of_verifyDeferred {bytecode : List K} {iv publicInput : Digest}
    {c : BytecodeClaim} {π : Proof} (h : verifyDeferred bytecode iv publicInput c π = true) :
    π.stream.length ≤ LeanVM.Guest.Coverage.childStreamCap := by
  have hP : Reads (deferringVerifierProgram c bytecode publicInput) childReads fun _ ↦ True := by
    rw [deferredProgram_eq]
    exact Reads.seq (reads_verifyExecution _ (reads_claimedBytecodeValue c) bytecode publicInput)
      (fun _ _ ↦ trivial) le_rfl
  rw [verifyDeferred_eq_withHash] at h
  exact (stream_le_of_runProof keccak256 keccakF1600 hP h).trans childReads_le

end
end LeanVM.Guest.Child
