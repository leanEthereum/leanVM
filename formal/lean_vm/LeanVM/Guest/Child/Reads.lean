/-
  LeanVM.Guest.Child.Reads

  The scalars a run of the leanVM verifier program reads off the stream: at most `childReads`,
  over every announced size the verifier accepts, so a proof the deferring verifier accepts has a
  stream of at most `8192` scalars (`LeanVM.Guest.Hints.childStreamCap`).
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.Verifier.Cost
public import Statement.LeanVmGuest
public import LeanVM.Protocol.WithHash
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Guest.AcceptableChild

/-!
# The stream an accepted proof carries

`Reads p n Q` is `VerifierProgram.Costs`' calculus with other weights: a scalar read costs `1`, a
proof of work `1` (its nonce), a commitment `2` (its root's two scalars), and a challenge or an
opening
`0`. A run of a program of `n` reads consumes at most `n` scalars of the stream (`run_reads`),
and an accepted run consumes the whole stream (`runProof`), so its proof's stream has at most
`n` scalars. The verifier's phases are costed as in `Verifier/Cost.lean`, each bound crude: the
bus's GKR walk over at most `36` levels, at most `30` table rounds, the Keccak reduction at a point
of at most `27` coordinates, and the WHIR levels over the 60 admissible ladders. In total
`childReads ≤ 8192` (`childReads_le`), for every evaluation of the fixed polynomial that reads
nothing (the deployed and the claimed ones), so every proof the deferring verifier accepts has a
stream of at most `8192` scalars (`stream_le_of_verifyDeferred`).
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
  | .sample k, n, Q => ∀ c, Reads (k c) n Q
  | .grind _ k, n, Q => 1 ≤ n ∧ Reads k (n - 1) Q
  | .commit _ _ k, n, Q => 2 ≤ n ∧ Reads k (n - 2) Q
  | .query _ _ k, n, Q => ∀ rows, Reads (k rows) n Q

namespace Reads

theorem mono {p : VerifierProgram α} {n m : ℕ} {Q R : α → Prop} (h : Reads p n Q) (hnm : n ≤ m)
    (hQR : ∀ a, Q a → R a) : Reads p m R := by
  induction p generalizing n m with
  | ret a => exact hQR a h
  | fail => trivial
  | read k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | sample k ih => exact fun x ↦ ih x (h x) hnm
  | grind b k ih => exact ⟨by have := h.1; omega, ih h.2 (by omega)⟩
  | commit ht w k ih => exact ⟨by have := h.1; omega, ih h.2 (by omega)⟩
  | query i ps k ih => exact fun r ↦ ih r (h r) hnm

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
  | sample k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2
    rwa [show n - 1 + m = n + m - 1 by have := hp.1; omega] at this
  | commit ht w k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2
    rwa [show n - 2 + m = n + m - 2 by have := hp.1; omega] at this
  | query i ps k ih => exact fun r ↦ ih r (hp r)

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

theorem sampleE : Reads VerifierProgram.sampleChallenge 0 fun _ ↦ True := fun _ ↦ trivial

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
  fun _ ↦ trivial

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
    · simp at h
    · next x xs hs =>
      obtain ⟨ys, hys, hl⟩ := ih x (hp.2 x) h
      refine ⟨x :: ys, ?_, ?_⟩
      · rw [hs]; simp only at hys; rw [hys]; rfl
      · simp only [List.length_cons]; have := hp.1; omega
  | sample k ih =>
    intro n Q hp s r h
    simp only [Compile.runWithHash] at h
    obtain ⟨ys, hys, hl⟩ := ih (Id.run (squeeze F s.sponge)).1 (hp _)
      (s := { s with sponge := (Id.run (squeeze F s.sponge)).2 }) h
    exact ⟨ys, hys, hl⟩
  | grind b k ih =>
    intro n Q hp s r h
    simp only [Compile.runWithHash] at h
    split at h
    · simp at h
    · next x xs hs =>
      change (if _ then _ else _) = _ at h
      split at h
      · obtain ⟨ys, hys, hl⟩ := ih hp.2 h
        refine ⟨x :: ys, ?_, ?_⟩
        · rw [hs]; simp only at hys; rw [hys]; rfl
        · simp only [List.length_cons]; have := hp.1; omega
      · simp at h
  | commit ht w k ih =>
    intro n Q hp s r h
    simp only [Compile.runWithHash] at h
    split at h
    · next x0 x1 xs hs =>
      change (match digestFromHalves (x0, x1) with | some root => _ | none => _) = _ at h
      split at h
      · obtain ⟨ys, hys, hl⟩ := ih hp.2 h
        refine ⟨x0 :: x1 :: ys, ?_, ?_⟩
        · rw [hs]; simp only at hys; rw [hys]; rfl
        · simp only [List.length_cons]; have := hp.1; omega
      · simp at h
    · simp at h
  | query i ps k ih =>
    intro n Q hp s r h
    obtain ⟨_, _, _, _, _, rows, _, _, _, h'⟩ :=
      (Compile.runWithHash_query_eq_some_iff H F i ps k s r).mp h
    obtain ⟨ys, hys, hl⟩ := ih rows (hp rows) h'
    exact ⟨ys, hys, hl⟩

/-- **An accepted proof's stream has at most the program's reads.** -/
theorem stream_le_of_runProof (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState) {P : VerifierProgram Bool}
    {n : ℕ} {Q : Bool → Prop} (hP : Reads P n Q) {seed : KeccakState} {π : Proof}
    (h : runProofWithHash H F P seed π = true) : π.stream.length ≤ n := by
  unfold runProofWithHash at h
  revert h
  match hr : Compile.runWithHash H F P ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ with
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

/-- The reads of one GKR step of `step` levels at a point of `L` coordinates: the sumcheck's `L`
rounds and the three trees' children. -/
def gkrStepReads (step L : ℕ) : ℕ := L * (max (2 ^ step + 1) 2 - 1) + 3 * 2 ^ step

/-- The reads of the GKR walk over `n` remaining levels from a point of `L` coordinates. -/
def gkrReads : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, L => gkrStepReads 1 L + gkrReads 0 (1 + L)
  | n + 2, L =>
    if n % 2 = 1 then gkrStepReads 1 L + gkrReads (n + 1) (1 + L)
    else gkrStepReads 2 L + gkrReads n (2 + L)

/-- The reads of one layer of the Keccak reduction at a point of `L` coordinates. -/
def keccakLayerReads (L : ℕ) : ℕ := productBits + L * 2 + keccakLocalBits * 3 + 3

/-- The reads of `verifyKeccak` at a point of `L` coordinates after the instances. -/
def keccakReads (L : ℕ) : ℕ :=
  1 + keccakDepth * keccakLayerReads L + (2 * qkeccakSlotBits + 1) + 2 * 4 +
    2 * qkeccakSlotBits + kBits

/-- The reads of the WHIR levels from a message of `μ` variables. -/
def whirReads : ℕ → List Whir.Level → ℕ
  | _, [] => 0
  | μ, [level] => 2 * level.fold + 2 ^ (μ - level.fold) + 1 + 2 + 2 * (μ - level.fold)
  | μ, level :: next :: rest =>
    2 * level.fold + (2 + 1 + 2) + 1 + 2 + whirReads (μ - level.fold) (next :: rest)

/-- The bound on the WHIR levels' reads over every admissible ladder. -/
def whirReadsBound : ℕ := 300

/-- **The reads of the leanVM verifier program**, phase by phase. -/
def childReads : ℕ :=
  8 + 2 + (2 + gkrReads 36 0 + 5) + (30 * 3 + tableWidthSum) + keccakReads 27 +
    (2 + whirReadsBound)

section Phases

theorem reads_sumcheckRoundPoly (count : ℕ) (claim : E) (eq : Option E) :
    Reads (sumcheckRoundPoly count claim eq) (max count 2 - 1) fun _ ↦ True := by
  cases eq with
  | none =>
    refine Reads.seq Reads.readE (fun _ _ ↦ Reads.seq (Reads.readN _)
      (fun _ _ ↦ trivial) ?_) ?_ <;> omega
  | some r =>
    exact Reads.seq (Reads.readN _) (fun _ _ ↦ trivial) (by omega)

theorem reads_sumcheck (count : ℕ) : ∀ (claim : E) (eqs : List (Option E)),
    Reads (sumcheck claim count eqs) (eqs.length * (max count 2 - 1))
      fun r ↦ r.1.length = eqs.length
  | _, [] => rfl
  | claim, e :: es => by
    refine Reads.seq (reads_sumcheckRoundPoly count claim e) (fun msg _ ↦
      Reads.seq Reads.sampleE (fun c _ ↦
        Reads.seq (reads_sumcheck count _ es) (fun r hr ↦ ?_) ?_) ?_) ?_
    · obtain ⟨point, final⟩ := r
      show (c :: point).length = (e :: es).length
      simpa using hr
    all_goals simp only [List.length_cons, Nat.succ_mul]; omega

theorem reads_gkrStep (step : ℕ) (s : GkrState) :
    Reads (gkrStep step s) (gkrStepReads step s.point.length)
      fun t ↦ t.point.length = step + s.point.length := by
  refine Reads.seq Reads.sampleE (fun _ _ ↦
    Reads.seq (reads_sumcheck _ _ (s.point.map some)) (fun r hr ↦ ?_) ?_) ?_
  · obtain ⟨x, claim⟩ := r
    refine Reads.seq (Reads.readN _) (fun c0 _ ↦ Reads.seq (Reads.readN _)
      (fun c1 _ ↦ Reads.seq (Reads.readN _) (fun c2 _ ↦
        Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦
          Reads.seq (Reads.sampleN step) (fun y hy ↦ ?_) ?_) ?_) ?_) ?_) ?_
    · show (y ++ x).length = step + s.point.length
      simp only [List.length_map] at hr
      simp [hy, hr]
    all_goals simp only [gkrStepReads, List.length_map]; omega
  all_goals simp only [gkrStepReads, List.length_map]; omega

theorem reads_gkrLayers : ∀ (n : ℕ) (s : GkrState),
    Reads (gkrLayers n s) (gkrReads n s.point.length) fun _ ↦ True
  | 0, _ => trivial
  | 1, s => by
    refine Reads.seq (reads_gkrStep 1 s) (fun t ht ↦
      (reads_gkrLayers 0 t).mono (by simp [gkrReads]) fun _ h ↦ h) ?_
    simp only [gkrReads]; omega
  | n + 2, s => by
    simp only [gkrLayers, gkrReads]
    split
    · refine Reads.seq (reads_gkrStep 1 s) (fun t ht ↦
        (reads_gkrLayers (n + 1) t).mono (by rw [ht]; omega) fun _ h ↦ h) (by omega)
    · refine Reads.seq (reads_gkrStep 2 s) (fun t ht ↦
        (reads_gkrLayers n t).mono (by rw [ht]; omega) fun _ h ↦ h) (by omega)

theorem reads_verifyGkrGrandProducts (depth : ℕ) :
    Reads (verifyGkrGrandProducts depth) (2 + gkrReads depth 0) fun _ ↦ True := by
  refine Reads.seq Reads.readE (fun _ _ ↦ Reads.seq Reads.readE
    (fun _ _ ↦ Reads.seq (reads_gkrLayers depth _) (fun _ _ ↦ trivial) ?_) ?_) ?_ <;>
    (try simp only [List.length_nil]) <;> omega

/-- An evaluation of the fixed polynomial that reads nothing: the deployed one and the claimed
ones. -/
def ReadsNothing (ev : (List K → List E → VerifierProgram E)) : Prop :=
  ∀ words point, Reads (ev words point) 0 fun _ ↦ True

theorem readsNothing_claimed (c : BytecodeClaim) : ReadsNothing (claimedBytecodeValue c) :=
    fun _ _ ↦
  Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦ trivial) le_rfl

theorem reads_verifyBusBalance {ev : (List K → List E → VerifierProgram E)} (hev : ReadsNothing ev) (layout : Layout)
    (hm : layout.logMemory ≤ 30) (hb : layout.logBytecode ≤ 30) :
    Reads (verifyBusBalance ev layout)
      (2 + gkrReads (busLayout [0, layout.logMemory, layout.logBytecode]
        layout.push).depth 0 + 5) fun r ↦ ClaimsShort r.claims := by
  refine Reads.seq (Reads.sampleN _) (fun _ _ ↦ Reads.seq Reads.sampleE
    (fun _ _ ↦ Reads.seq (reads_verifyGkrGrandProducts _) (fun r _ ↦ ?_) ?_) ?_) ?_
  · obtain ⟨countRoot, point, treeValues⟩ := r
    refine Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦ Reads.seq
      (Reads.readN 3)
      (fun memory hmem ↦ Reads.seq Reads.readE (fun _ _ ↦ Reads.seq
        Reads.readE (fun _ _ ↦ Reads.seq (hev _ _) (fun _ _ ↦ ?_) ?_) ?_) ?_) ?_) ?_
    · intro c hc _
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
        simp only [List.getElem_zipWith, List.length_take]
        omega
      · simp only [List.length_take]; omega
      · simp only [List.length_take]; omega
    all_goals omega
  all_goals omega

theorem gkrReads_le : ∀ D ≤ 36, gkrReads D 0 ≤ gkrReads 36 0 := by decide

theorem reads_verifyBusBalance_le {ev : (List K → List E → VerifierProgram E)} (hev : ReadsNothing ev) {layout : Layout}
    (h : LayoutBounds layout) :
    Reads (verifyBusBalance ev layout) (2 + gkrReads 36 0 + 5) fun r ↦ ClaimsShort r.claims :=
  (reads_verifyBusBalance hev layout h.logMemory_le h.logBytecode_le).mono
    (by have := gkrReads_le _ (pushDepth_le h); omega) fun _ h ↦ h

theorem reads_tableTerms (constraintPowers formPowers point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), ClaimsShort claims → (∀ r ∈ rows, r.2.1 ≤ 30) →
      Reads (tableTermsClaims constraintPowers formPowers point rows cursor final claims)
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

private theorem foldl_max_le' (M : ℕ) : ∀ (l : List ℕ) (acc : ℕ), acc ≤ M → (∀ x ∈ l, x ≤ M) →
    l.foldl max acc ≤ M
  | [], _, h, _ => h
  | x :: xs, acc, h, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le' M xs _ (max_le h (hl x List.mem_cons_self))
      fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)

theorem reads_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E)
    (hh : ∀ h ∈ heights, h ≤ 30) :
    Reads (tableSumcheckClaims heights busForms constraintPowers formPowers equalityPoint target)
      (30 * 3 + tableWidthSum) fun cl ↦ ClaimsShort cl := by
  have hmax := foldl_max_le' 30 heights 0 (Nat.zero_le _) hh
  refine Reads.seq (reads_sumcheck _ _ _) (fun r _ ↦ ?_) ?_
  · obtain ⟨challenges, claim⟩ := r
    have hrows : ∀ r ∈ List.zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint challenges.reverse))), r.2.1 ≤ 30 := by
      intro r hr
      exact hh _ (List.of_mem_zip (List.of_mem_zip hr).2).1
    refine Reads.seq (reads_tableTerms _ _ _ _ 0 0 [] (fun _ h ↦ by simp at h) hrows)
      (fun r hr ↦ ?_) ?_
    · obtain ⟨final, claims⟩ := r
      exact Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦ hr) (Nat.zero_le _)
    · simp only [List.length_replicate, show max 4 2 - 1 = 3 from rfl]
      have := sum_width_zip tables (List.zip heights (List.zip busForms
        (tableWeights heights equalityPoint challenges.reverse)))
      unfold tableWidthSum
      omega
  · simp only [List.length_replicate, show max 4 2 - 1 = 3 from rfl]
    omega

theorem reads_tablePhase {layout : Layout} (hl : LayoutBounds layout) (bus : BusResult)
    (hbus : ClaimsShort bus.claims) :
    Reads (tablePhaseClaims layout bus) (30 * 3 + tableWidthSum) fun cl ↦ ClaimsShort cl :=
  Reads.seq Reads.sampleE (fun _ _ ↦ Reads.seq
    (reads_tableSumcheck _ _ _ _ _ _ hl.heights_le) (fun cl hcl ↦ by
      intro c hc hcol
      rcases List.mem_append.mp hc with hc | hc
      · exact hbus c hc hcol
      · exact hcl c hc hcol) (by omega)) (by omega)

theorem reads_publicInputPhase (layout : Layout) (publicInput : Digest) :
    Reads (publicInputPhase layout publicInput) 0 fun cl ↦ ClaimsShort cl := by
  refine Reads.seq Reads.sampleE (fun _ _ ↦ ?_) (by omega)
  intro c hc hcol
  exfalso
  have hbase : ∀ x ∈ keccakOutputColumns, 6 ≤ x := by
    intro x hx
    simp only [keccakOutputColumns, List.mem_map] at hx
    obtain ⟨_, -, rfl⟩ := hx
    have : 6 ≤ globalColumnBases.getD opKeccak 0 := by decide
    omega
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  simp only [List.getElem_zipWith] at hcol
  have hi' : i < 3 := by simp at hi; omega
  have hle : [memory0, memory1, memory2][i] < 3 := by
    interval_cases i <;> simp [memory0, memory1, memory2]
  have := hbase _ hcol
  omega

theorem reads_keccakPackRounds : ∀ (point : List E) (value scale : E),
    Reads (keccakPackRounds point value scale) (point.length * 2)
      fun r ↦ r.2.2.length = point.length
  | [], _, _ => rfl
  | r :: rs, value, scale => by
    refine Reads.seq (reads_sumcheckRoundPoly 3 _ _) (fun _ _ ↦ Reads.seq
      Reads.sampleE (fun c _ ↦ Reads.seq (reads_keccakPackRounds rs _ _)
        (fun t ht ↦ ?_) ?_) ?_) ?_
    · obtain ⟨v, s, p⟩ := t
      show (c :: p).length = (r :: rs).length
      simpa using ht
    all_goals simp only [List.length_cons, Nat.succ_mul, show max 3 2 - 1 = 2 from rfl]; omega

theorem reads_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    Reads (verifyKeccakLayer logSteps step claim)
      (keccakLayerReads claim.point.length) fun c ↦ c.point.length = claim.point.length := by
  refine Reads.seq (Reads.readN _) (fun _ _ ↦ Reads.seq
    (Reads.require (n := 0) _) (fun _ _ ↦ Reads.seq Reads.sampleE (fun _ _ ↦
      Reads.seq (reads_keccakPackRounds _ _ _) (fun r hr ↦ ?_) ?_) ?_) ?_) ?_
  · obtain ⟨value, scale, point⟩ := r
    refine Reads.seq (reads_sumcheck 4 _ _) (fun r _ ↦ ?_) ?_
    · obtain ⟨localPoint, value⟩ := r
      refine Reads.seq (Reads.readN 3) (fun _ _ ↦ Reads.seq
        (Reads.require (n := 0) _) (fun _ _ ↦ Reads.seq Reads.sampleE
          (fun _ _ ↦ hr) ?_) ?_) ?_
      all_goals simp only [keccakLayerReads, List.length_replicate,
        show max 4 2 - 1 = 3 from rfl]
      all_goals omega
    · simp only [keccakLayerReads, List.length_replicate, show max 4 2 - 1 = 3 from rfl]
      omega
  all_goals simp only [keccakLayerReads]; omega

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

theorem reads_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    Reads (keccakOpen logSteps claim first count value) (2 * qkeccakSlotBits) fun _ ↦ True :=
  Reads.seq (reads_sumcheck 3 _ _) (fun _ _ ↦ trivial)
    (by simp only [List.length_replicate, show max 3 2 - 1 = 2 from rfl]; omega)

theorem reads_verifyKeccak (logSteps : ℕ) (inst output : List E) (hi : inst.length ≤ 30) :
    Reads (verifyKeccak logSteps inst output) (keccakReads 27) fun _ ↦ True := by
  have hL : (inst.drop 4).length + keccakSegmentBits ≤ 27 := by
    simp only [List.length_drop, keccakSegmentBits]
    have : log2Ceil keccakSegments = 1 := by decide
    omega
  have h1 : 1 < keccakSegments := by decide
  unfold verifyKeccak
  simp only [h1, ↓reduceIte]
  refine Reads.seq (Reads.sampleN _) (fun segment hseg ↦ Reads.seq
    (Reads.sampleN _) (fun _ _ ↦ Reads.seq Reads.readE (fun committed _ ↦ ?_) ?_)
    ?_) ?_
  · have hpl : (inst.drop 4 ++ segment).length ≤ 27 := by
      rw [List.length_append, hseg]; exact hL
    have hlay : keccakDepth * keccakLayerReads (inst.drop 4 ++ segment).length ≤
        keccakDepth * keccakLayerReads 27 := by
      refine Nat.mul_le_mul_left _ ?_
      unfold keccakLayerReads
      omega
    refine Reads.seq (reads_keccakLayers logSteps (List.range keccakDepth) _)
      (fun claim _ ↦ Reads.seq (reads_keccakOpen logSteps _ 1 _ _) (fun r _ ↦
        Reads.seq Reads.readE (fun word _ ↦ Reads.seq
          (Reads.require (n := 0) _) (fun _ _ ↦ Reads.seq (Reads.pure0 _)
            (fun outputs _ ↦ Reads.seq (reads_sumcheck 3 _ _) (fun r2 _ ↦
              Reads.seq (reads_keccakOpen logSteps _ 0 _ _) (fun r3 _ ↦
                Reads.seq (Reads.readN kBits) (fun slices _ ↦
                  Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦ trivial)
                    (Nat.zero_le _)) ?_) ?_) ?_) (Nat.zero_le _)) (Nat.zero_le _)) ?_) ?_) ?_
    all_goals simp only [keccakReads, keccakFirstClaim, List.length_range, List.length_replicate,
      show max 3 2 - 1 = 2 from rfl] at hlay ⊢
    all_goals omega
  all_goals simp only [keccakReads]; omega

theorem reads_keccakPhase (layout : Layout) (claims : List ColumnClaim)
    (hc : ClaimsShort claims) :
    Reads (keccakPhaseClaims layout claims) (keccakReads 27) fun _ ↦ True := by
  exact Reads.seq (Reads.require (n := 0) _) (fun _ _ ↦ Reads.seq
    (reads_verifyKeccak _ _ _ (headD_filter_short claims hc)) (fun _ _ ↦ trivial) le_rfl)
    (Nat.zero_le _)

theorem reads_ringSwitch (point s : List E) : Reads (ringSwitch point s) 0 fun _ ↦ True :=
  Reads.seq (Reads.sampleN _) (fun _ _ ↦ trivial) le_rfl

end Phases

/-! ## WHIR -/

section Whir

theorem reads_foldRounds : ∀ (n : ℕ) (s : WhirStateT) (levelFolds : List E),
    Reads (foldRoundsT n s levelFolds) (2 * n) fun r ↦ r.1.folds.length = s.folds.length + n
  | 0, _, _ => rfl
  | n + 1, s, levelFolds => by
    refine Reads.seq Reads.sampleE (fun c _ ↦
      Reads.seq (reads_sumcheckRoundPoly 3 _ none) (fun _ _ ↦
        (reads_foldRounds n _ _).mono ?_ fun r hr ↦ ?_) ?_) ?_
    · simp only [show max 3 2 - 1 = 2 from rfl]; omega
    · rw [hr, List.length_append, List.length_singleton]; omega
    · simp only [show max 3 2 - 1 = 2 from rfl]; omega
    · omega

theorem reads_tailRounds : ∀ (n : ℕ) (target : E) (quad : List E),
    Reads (tailRoundsT n target quad) (2 * n) fun _ ↦ True
  | 0, _, _ => trivial
  | n + 1, _, quad => by
    refine Reads.seq Reads.sampleE (fun c _ ↦ Reads.ite (fun _ ↦ trivial)
      fun _ ↦ Reads.seq (reads_sumcheckRoundPoly 3 _ none) (fun _ _ ↦
        Reads.seq (reads_tailRounds n _ _) (fun r _ ↦ ?_) ?_) ?_) ?_
    · obtain ⟨rest, target⟩ := r
      trivial
    all_goals (try simp only [show max 3 2 - 1 = 2 from rfl])
    all_goals omega

theorem reads_sampleQueriesAux (depth : ℕ) :
    ∀ (fuel remaining : ℕ), Reads (sampleQueriesAux depth fuel remaining) 0 fun _ ↦ True
  | 0, _ => trivial
  | fuel + 1, remaining => by
    refine Reads.ite (fun _ ↦ trivial) fun _ ↦ Reads.seq Reads.sampleE
      (fun c _ ↦ Reads.seq (reads_sampleQueriesAux depth fuel _) (fun qs _ ↦ trivial) le_rfl)
      le_rfl

theorem reads_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirStateT) (μ : ℕ),
      logN - s.folds.length = μ →
      Reads (whirLevelsT logN laneFolds evaluateBasis index levels s)
        (whirReads μ levels) fun _ ↦ True
  | [], _, _, _, _ => trivial
  | [level], index, s, μ, hμ => by
    simp only [whirReads]
    generalize hP : 2 ^ (μ - level.fold) = P
    refine Reads.seq (reads_foldRounds level.fold s []) (fun r hr ↦ ?_) (by omega)
    obtain ⟨s', levelFolds⟩ := r
    simp only at hr
    have hm : logN - s'.folds.length = μ - level.fold := by rw [hr]; omega
    refine Reads.seq (Reads.readN _) (fun _ _ ↦ Reads.seq (Reads.pure0 _)
      (fun _ _ ↦ Reads.seq (Reads.grindP _) (fun _ _ ↦ Reads.seq
        (reads_sampleQueriesAux _ level.queries level.queries) (fun queries hq ↦ ?_)
          ?_) ?_) ?_) ?_
    · refine Reads.seq Reads.sampleE (fun lam _ ↦ Reads.seq
        (Reads.queryP index queries) (fun words _ ↦ Reads.seq
          (reads_sumcheckRoundPoly 3 _ none) (fun intro _ ↦ Reads.seq
            (reads_tailRounds _ _ _) (fun r _ ↦ ?_) ?_) ?_) ?_) ?_
      · obtain ⟨tailFolds, target⟩ := r
        exact (Reads.require (n := 0) _).mono (Nat.zero_le _) fun _ _ ↦ trivial
      all_goals (try simp only [hm, hP, show max 3 2 - 1 = 2 from rfl])
      all_goals omega
    all_goals (try simp only [hm, hP])
    all_goals omega
  | level :: next :: rest, index, s, μ, hμ => by
    simp only [whirReads]
    refine Reads.seq (reads_foldRounds level.fold s []) (fun r hr ↦ ?_) (by omega)
    obtain ⟨s', levelFolds⟩ := r
    simp only at hr
    have hm : logN - s'.folds.length = μ - level.fold := by rw [hr]; omega
    refine Reads.seq (Reads.commitP _ _) (fun _ _ ↦
      Reads.seq (Reads.sampleN _) (fun _ _ ↦ Reads.seq Reads.readE
        (fun _ _ ↦ Reads.seq (reads_sumcheckRoundPoly 3 _ none) (fun _ _ ↦
          Reads.seq (Reads.pure0 _) (fun _ _ ↦
          Reads.seq (Reads.grindP _) (fun _ _ ↦ Reads.seq
            (reads_sampleQueriesAux _ level.queries level.queries)
              (fun queries hq ↦ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · refine Reads.seq Reads.sampleE (fun lam _ ↦ Reads.seq
        (Reads.queryP index queries) (fun words _ ↦ Reads.seq
          (reads_sumcheckRoundPoly 3 _ none) (fun intro _ ↦
            (reads_whirLevels logN laneFolds evaluateBasis (next :: rest) (index + 1) _
              (μ - level.fold) (by rw [glue_folds]; exact hm)).mono ?_
              fun _ h ↦ h) ?_) ?_) ?_
      all_goals (try simp only [show max 3 2 - 1 = 2 from rfl])
      all_goals omega
    all_goals (try simp only [show max 3 2 - 1 = 2 from rfl])
    all_goals omega

theorem reads_verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E)
    (W : ℕ) (hW : ∀ levels, Whir.ladder logN logInvRate = some levels → whirReads logN levels ≤ W) :
    Reads (verifyWhirT logN logInvRate target evaluateBasis) (2 + W) fun _ ↦ True := by
  refine Reads.seq (Reads.liftOption _ 0) (fun config hc ↦ Reads.seq
    (reads_sumcheckRoundPoly 3 _ none) (fun quad _ ↦
      ((reads_whirLevels logN _ evaluateBasis config 0 _ logN rfl).mono
        ((hW config hc).trans (by omega)) fun _ h ↦ h)) ?_)
    (Nat.zero_le _)
  simp only [show max 3 2 - 1 = 2 from rfl]; omega

theorem reads_commitStack (logN logInvRate : ℕ) :
    Reads (commitStack logN logInvRate) 2 fun _ ↦ True := by
  refine Reads.seq (Reads.liftOption _ 0) (fun config hc ↦ ?_) (Nat.zero_le _)
  cases config with
  | nil => trivial
  | cons level rest => exact Reads.commitP _ _

theorem reads_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (W : ℕ) (hW : ∀ levels, Whir.ladder stackLog logInvRate = some levels →
      whirReads stackLog levels ≤ W) :
    Reads (verifyStackedOpening stackLog logInvRate claims) (2 + W) fun _ ↦ True := by
  rw [verifyStackedOpening_eq_target]
  exact Reads.seq Reads.sampleE (fun _ _ ↦
    (reads_verifyWhir _ _ _ _ W hW).mono (by omega) fun _ h ↦ h) (by omega)

/-- Over every admissible ladder the WHIR levels read at most `whirReadsBound` scalars. -/
theorem ladder_reads (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) : whirReads μ levels ≤ whirReadsBound := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels → whirReads μ levels ≤ whirReadsBound := by
      decide +kernel
    exact key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2)
      hadm levels h
  · simp [Whir.ladder, hadm] at h

end Whir

/-! ## The whole program -/

theorem reads_readSizes (bytecode : List K) : Reads (readAnnouncedSizes bytecode) 8 SizesOK := by
  refine Reads.seq (Reads.readN _) (fun announced _ ↦ Reads.seq
    (Reads.require (n := 0) _) (fun _ _ ↦ Reads.seq (Reads.require (n := 0) _)
      (fun _ hr ↦ Reads.seq (Reads.liftOption _ 0) (fun layout hl ↦ Reads.seq
        (Reads.require (n := 0) _) (fun _ hs ↦ ?_) ?_) ?_) ?_) ?_) ?_
  · exact ⟨layoutBounds_of_buildLayout hl, hr.1, hr.2, hs.1, hs.2⟩
  all_goals simp [tables]

/-- **The reads of `verify_execution`**, for an evaluation of the fixed polynomial that reads
nothing. -/
theorem reads_verifyExecution {ev : (List K → List E → VerifierProgram E)} (hev : ReadsNothing ev) (bytecode : List K)
    (publicInput : Digest) :
    Reads (verifyExecutionClaims ev bytecode publicInput) childReads fun _ ↦ True := by
  unfold childReads
  refine Reads.seq (reads_readSizes bytecode) (fun p hp ↦ ?_) (by omega)
  obtain ⟨layout, logInverseRate⟩ := p
  obtain ⟨hl, -, -, -, -⟩ := hp
  refine Reads.seq (reads_commitStack _ _)
    (fun _ _ ↦ Reads.seq (reads_verifyBusBalance_le hev hl) (fun bus hbus ↦ Reads.seq
      (reads_tablePhase hl bus hbus) (fun claims hcl ↦ Reads.seq
        (reads_publicInputPhase layout publicInput) (fun publicClaims hpc ↦
          Reads.seq (reads_keccakPhase layout _ ?_) (fun r _ ↦ ?_) ?_) ?_) ?_) ?_) ?_
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

/-- The reads, evaluated: at most `8192`. -/
theorem childReads_le : childReads ≤ LeanVM.Guest.Coverage.childStreamCap := by decide

/-- **A proof the deferring verifier accepts has a stream of at most `8192` scalars.** -/
theorem stream_le_of_verifyDeferred {bytecode : List K} {iv publicInput : Digest}
    {c : BytecodeClaim} {π : Proof} (h : verifyDeferred bytecode iv publicInput c π = true) :
    π.stream.length ≤ LeanVM.Guest.Coverage.childStreamCap := by
  have hP : Reads (deferringVerifierProgram c bytecode publicInput) childReads fun _ ↦ True := by
    rw [deferredProgram_eq]
    exact Reads.seq (reads_verifyExecution (readsNothing_claimed c) bytecode publicInput)
      (fun _ _ ↦ trivial) le_rfl
  rw [verifyDeferred_eq_withHash] at h
  exact (stream_le_of_runProof keccak256 keccakF1600 hP h).trans childReads_le

end
end LeanVM.Guest.Child
