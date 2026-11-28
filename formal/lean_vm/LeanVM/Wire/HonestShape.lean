/-
  LeanVM.Wire.HonestShape

  Every opening phase of the leanVM verifier program is within the wire decoding's bounds, and its
  stream is short: at most `wireMaxPhases` phases, each of `1` to `wireMaxQueries` positions below
  `2^height` of a commitment of height at most `wireMaxHeight`, and at most `leanVmStream` stream
  elements.
-/

module

public import LeanVM.Wire.HonestRun
public import LeanVM.Wire.HonestCost

/-!
# The verifier program's openings and stream are within the wire bounds

The leanVM verifier program is `Wired` from no commitment with `wireMaxPhases` openings and
`leanVmStream` stream elements (`wired_leanVmProgram`). It is `verify_execution` split at the link's
call of the program's split (`verifyExecution_split`): the prefix (`execPre`: the sizes, the stack's
commitment, its out-of-domain sample, the link up to the split), the computed split, and the
suffix (`execSuf`: the rest of the link, the public input, `KECCAK`'s reduction, ring switching,
the memory term and the stacked opening). Its only commitments are the stack's and the WHIR
levels', its only openings the WHIR levels', one per level; every other phase commits and opens
nothing and reads the stream `LeanVM.Wire.HonestCost` bounds. The WHIR bounds are decided over the
`60` admissible ladders (`ladder_wire`): at most `wireMaxPhases` levels, `1` to `wireMaxQueries`
queries per level, query depths (the commitments' heights) `1` to `wireMaxHeight`, and at most
`whirStreamBound` stream elements.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Verifier.Defers

variable {α β : Type}

/-! ## The calculus -/

namespace Wired

theorem mono {p : VerifierProgram α} {hs : List ℕ} {n c d : ℕ}
    {Q R : α → List ℕ → ℕ → Prop} (h : Wired p hs n c Q)
    (hQR : ∀ a hs' n', Q a hs' n' → R a hs' n') (hcd : c ≤ d) : Wired p hs n d R := by
  induction p generalizing hs n c d with
  | ret a => exact hQR a hs n h
  | fail => trivial
  | read k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | sample k ih => exact fun x ↦ ih x (h x) hcd
  | readPacked m k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | samplePacked m k ih => exact fun x ↦ ih x (h x) hcd
  | grind b k ih => exact ⟨by have := h.1; omega, ih h.2 (by omega)⟩
  | commit ht w k ih => exact ⟨by have := h.1; omega, ih h.2 (by omega)⟩
  | query i ps k ih => exact ⟨h.1, h.2.1, fun r ↦ ih r (h.2.2 r) hcd⟩

theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {hs : List ℕ} {n a b : ℕ}
    {Q : α → List ℕ → ℕ → Prop} {R : β → List ℕ → ℕ → Prop}
    (hp : Wired p hs n a Q) (hf : ∀ x hs' n', Q x hs' n' → Wired (f x) hs' n' b R) :
    Wired (p.bind f) hs n (a + b) R := by
  induction p generalizing hs n a with
  | ret x => exact (hf x hs n hp).mono (fun _ _ _ h ↦ h) (by omega)
  | fail => trivial
  | read k ih =>
    refine ⟨by have := hp.1; omega, fun x ↦ ?_⟩
    have := ih x (hp.2 x)
    rwa [show a - 1 + b = a + b - 1 by have := hp.1; omega] at this
  | sample k ih => exact fun x ↦ ih x (hp x)
  | readPacked m k ih =>
    refine ⟨by have := hp.1; omega, fun x ↦ ?_⟩
    have := ih x (hp.2 x)
    rwa [show a - m + b = a + b - m by have := hp.1; omega] at this
  | samplePacked m k ih => exact fun x ↦ ih x (hp x)
  | grind bits k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2
    rwa [show a - 1 + b = a + b - 1 by have := hp.1; omega] at this
  | commit ht w k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2
    rwa [show a - 2 + b = a + b - 2 by have := hp.1; omega] at this
  | query i ps k ih => exact ⟨hp.1, hp.2.1, fun r ↦ ih r (hp.2.2 r)⟩

theorem seq {p : VerifierProgram α} {f : α → VerifierProgram β} {hs : List ℕ} {n a c : ℕ}
    {Q : α → List ℕ → ℕ → Prop} {R : β → List ℕ → ℕ → Prop}
    (hp : Wired p hs n a Q) (hf : ∀ x hs' n', Q x hs' n' → Wired (f x) hs' n' (c - a) R)
    (ha : a ≤ c) : Wired (p >>= f) hs n c R :=
  (bind hp hf).mono (fun _ _ _ h ↦ h) (by omega)

/-- A program that commits and opens nothing keeps the heights and the openings left. -/
theorem of_cost : ∀ {p : VerifierProgram α} {hs : List ℕ} {n a : ℕ}, CostLE p a →
    Wired p hs n a fun x hs' n' ↦ hs' = hs ∧ n' = n ∧ VerifierProgram.ReturnsAny p x := by
  intro p
  induction p with
  | ret x => intro _ _ _ _; exact ⟨rfl, rfl, .ret x⟩
  | fail => intro _ _ _ _; trivial
  | read k ih =>
    intro hs n a h
    exact ⟨h.1, fun x ↦ (ih x (h.2 x)).mono (fun y _ _ hr ↦ ⟨hr.1, hr.2.1, .read x hr.2.2⟩)
      le_rfl⟩
  | sample k ih =>
    intro hs n a h x
    exact (ih x (h x)).mono (fun y _ _ hr ↦ ⟨hr.1, hr.2.1, .sample x hr.2.2⟩) le_rfl
  | readPacked m k ih =>
    intro hs n a h
    exact ⟨h.1, fun xs ↦ (ih xs (h.2 xs)).mono
      (fun y _ _ hr ↦ ⟨hr.1, hr.2.1, .readPacked m xs hr.2.2⟩) le_rfl⟩
  | samplePacked m k ih =>
    intro hs n a h xs
    exact (ih xs (h xs)).mono (fun y _ _ hr ↦ ⟨hr.1, hr.2.1, .samplePacked m xs hr.2.2⟩) le_rfl
  | grind b k ih =>
    intro hs n a h
    exact ⟨h.1, (ih h.2).mono (fun y _ _ hr ↦ ⟨hr.1, hr.2.1, .grind b hr.2.2⟩) le_rfl⟩
  | commit _ _ _ _ => intro _ _ _ h; exact h.elim
  | query _ _ _ _ => intro _ _ _ h; exact h.elim

/-- A program that commits and opens nothing, then a wired one. -/
theorem cost_seq {p : VerifierProgram α} {f : α → VerifierProgram β} {hs : List ℕ} {n a c : ℕ}
    {R : β → List ℕ → ℕ → Prop} (hp : CostLE p a)
    (hf : ∀ x, VerifierProgram.ReturnsAny p x → Wired (f x) hs n (c - a) R) (ha : a ≤ c) :
    Wired (p >>= f) hs n c R :=
  seq (of_cost hp) (fun x _ _ h ↦ h.1 ▸ h.2.1 ▸ hf x h.2.2) ha

end Wired

/-! ## The WHIR ladders -/

/-- The levels from a message of `μ` variables are within the wire bounds: each queries `1` to
`wireMaxQueries` positions at a depth (its commitment's height) of `1` to `wireMaxHeight` bits. -/
def levelsWired : ℕ → List Whir.Level → Bool
  | _, [] => true
  | μ, level :: rest =>
    decide (1 ≤ level.queries ∧ level.queries ≤ wireMaxQueries ∧
        1 ≤ μ - level.fold + level.logInvRate ∧ μ - level.fold + level.logInvRate ≤ wireMaxHeight) &&
      levelsWired (μ - level.fold) rest

/-- The stream the WHIR levels from a message of `μ` variables read: per level its fold rounds
(four scalars and a nonce each), then on the final level the folded lane, a nonce and the tail's
rounds, on another the next commitment's root, the high part and three nonces and scalars. -/
def whirStream : ℕ → List Whir.Level → ℕ
  | _, [] => 0
  | μ, [level] =>
    level.fold * 5 + (2 ^ (μ - level.fold) + level.fold) + 1 + (μ - level.fold) * 5
  | μ, level :: next :: rest =>
    level.fold * 5 + 2 + level.fold + 1 + 1 + 1 + whirStream (μ - level.fold) (next :: rest)

/-- The stream the WHIR levels read, at most. -/
def whirStreamBound : ℕ := 256

/-- **Every admissible ladder is within the wire bounds**: at most `wireMaxPhases` levels, each
within the bounds, at most `whirStreamBound` stream elements; decided over the `60` admissible
pairs. -/
theorem ladder_wire (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) :
    levels.length ≤ wireMaxPhases ∧ levelsWired μ levels = true ∧
      whirStream μ levels ≤ whirStreamBound := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels →
          (decide (levels.length ≤ wireMaxPhases) && levelsWired μ levels &&
            decide (whirStream μ levels ≤ whirStreamBound)) = true := by
      decide +kernel
    have hk := key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2)
      hadm levels h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    exact ⟨hk.1.1, hk.1.2, hk.2⟩
  · simp [Whir.ladder, hadm] at h

/-! ## The WHIR levels -/

theorem foldRoundP (s : WhirState) : CostLE (foldRound s) 5 := by
  unfold foldRound
  exact CostLE.seq CostLE.readE (fun _ _ ↦ CostLE.seq CostLE.readE (fun _ _ ↦
    CostLE.seq CostLE.readE (fun _ _ ↦ CostLE.seq CostLE.readE (fun _ _ ↦
      CostLE.seq (CostLE.grindP _) (fun _ _ ↦ CostLE.seq CostLE.sampleE (fun _ _ ↦
        CostLE.seq CostLE.sampleE (fun _ _ ↦ trivial) (Nat.zero_le _)) (Nat.zero_le _))
        (by omega)) (by omega)) (by omega)) (by omega)) (by omega)

theorem foldRound_returns (s : WhirState) {r : WhirState × FoldRound}
    (h : VerifierProgram.ReturnsAny (foldRound s) r) : r.1.alphas.length = s.alphas.length + 1 := by
  unfold foldRound at h
  repeat obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  rw [VerifierProgram.returnsAny_ret h]
  simp

theorem foldRoundsP : ∀ (n : ℕ) (s : WhirState), CostLE (foldRounds n s) (n * 5)
  | 0, _ => trivial
  | n + 1, s => by
    unfold foldRounds
    refine CostLE.seq (foldRoundP s) (fun x _ ↦ ?_) (by omega)
    obtain ⟨s', round⟩ := x
    exact CostLE.seq (foldRoundsP n _) (fun y _ ↦ by obtain ⟨_, _⟩ := y; trivial) (by
      rw [Nat.succ_mul]; omega)

theorem foldRounds_returns : ∀ (n : ℕ) (s : WhirState) {r : WhirState × List FoldRound},
    VerifierProgram.ReturnsAny (foldRounds n s) r → r.1.alphas.length = s.alphas.length + n
  | 0, s, r, h => by
    have := VerifierProgram.returnsAny_ret h
    subst this
    rfl
  | n + 1, s, r, h => by
    unfold foldRounds at h
    obtain ⟨c, hc, h⟩ := VerifierProgram.returnsAny_bind h
    obtain ⟨d, hd, h⟩ := VerifierProgram.returnsAny_bind h
    have h1 := foldRound_returns s hc
    have h2 := foldRounds_returns n _ hd
    rw [VerifierProgram.returnsAny_ret h]
    simp only at h2 ⊢
    omega

theorem sampleQueriesAuxP (depth : ℕ) : ∀ (fuel remaining : ℕ),
    CostLE (sampleQueriesAux depth fuel remaining) 0
  | 0, _ => trivial
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    split
    · trivial
    · exact CostLE.seq CostLE.sampleE (fun _ _ ↦ CostLE.seq (sampleQueriesAuxP depth fuel _)
        (fun _ _ ↦ trivial) le_rfl) le_rfl

/-- The positions `sampleQueriesAux` returns: at most `remaining`, below `2^depth`, and at least
one when `1 ≤ remaining`, `1 ≤ depth ≤ 128` and there is fuel. -/
theorem sampleQueriesAux_returns (depth : ℕ) : ∀ (fuel remaining : ℕ) {qs : List ℕ},
    VerifierProgram.ReturnsAny (sampleQueriesAux depth fuel remaining) qs →
      qs.length ≤ remaining ∧ (∀ q ∈ qs, q < 2 ^ depth) ∧
        (1 ≤ fuel → 1 ≤ remaining → 1 ≤ depth → depth ≤ 128 → qs ≠ [])
  | 0, _, qs, h => by
    have := VerifierProgram.returnsAny_ret h
    subst this
    simp
  | fuel + 1, remaining, qs, h => by
    unfold sampleQueriesAux at h
    split at h
    · have := VerifierProgram.returnsAny_ret h
      subst this
      simp only [List.length_nil, Nat.zero_le, List.not_mem_nil, false_implies,
        implies_true, true_and]
      intro _ hr
      omega
    · obtain ⟨c, -, h⟩ := VerifierProgram.returnsAny_bind h
      obtain ⟨rest, hrest, h⟩ := VerifierProgram.returnsAny_bind h
      have := VerifierProgram.returnsAny_ret h
      subst this
      obtain ⟨hl, hlt, -⟩ := sampleQueriesAux_returns depth fuel _ hrest
      refine ⟨?_, fun q hq ↦ ?_, fun _ _ hd1 hd2 ↦ ?_⟩
      · simp only [List.length_append, List.length_map, List.length_range]
        omega
      · rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hq
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        · exact hlt q hq
      · have h128 : 1 ≤ 128 / depth := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
        have hn : 1 ≤ min (128 / depth) remaining := by omega
        intro he
        have := congrArg List.length he
        simp only [List.length_append, List.length_map, List.length_range, List.length_nil] at this
        omega

theorem glueLevel_alphas (s : WhirState) (lam : E) (mu : ℕ) (oodPoint : List E) (oodValue : E)
    (queries : List ℕ) (queryWeights : List E) (batched : E) :
    (glueLevel s lam mu oodPoint oodValue queries queryWeights batched).alphas = s.alphas := rfl

/-- **The WHIR levels are wired**: at level `index`, the heights so far end with the current
level's commitment, of height `logN − |α| − fold + rate`, and as many openings are left as
levels. -/
theorem wired_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (hs : List ℕ) (n : ℕ),
      hs.length = index + 1 → levels.length ≤ n →
      levelsWired (logN - s.alphas.length) levels = true →
      (∀ level ∈ levels.head?,
        hs.getD index 0 = logN - s.alphas.length - level.fold + level.logInvRate) →
      Wired (whirLevels logN laneFolds evaluateBasis index levels s) hs n
        (whirStream (logN - s.alphas.length) levels) fun _ _ _ ↦ True
  | [], _, _, _, _, _, _, _, _ => trivial
  | level :: rest, index, s, hs, n, hl, hn, hw, hh => by
    have hh1 := hh level rfl
    simp only [levelsWired, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨hq1, hq2, hd1, hd2⟩, hrest⟩ := hw
    have hd2' : logN - s.alphas.length - level.fold + level.logInvRate ≤ 32 := hd2
    have hn1 : 0 < n := by simp only [List.length_cons] at hn; omega
    unfold whirLevels
    cases rest with
    | nil =>
      simp only [whirStream]
      generalize hP : 2 ^ (logN - s.alphas.length - level.fold) = P
      refine Wired.cost_seq (foldRoundsP _ _) (fun r hr ↦ ?_) (by omega)
      obtain ⟨s', rounds⟩ := r
      have hf := foldRounds_returns _ _ hr
      simp only at hf
      have hdepth : logN - s'.alphas.length + level.logInvRate = hs.getD index 0 := by
        rw [hh1, hf]; omega
      have hmu : logN - s'.alphas.length = logN - s.alphas.length - level.fold := by omega
      refine Wired.cost_seq (CostLE.readN _) (fun _ _ ↦ ?_) (by rw [hmu, hP]; omega)
      refine Wired.cost_seq (CostLE.grindP _) (fun _ _ ↦ ?_) (by rw [hmu, hP]; omega)
      refine Wired.cost_seq (sampleQueriesAuxP _ _ _) (fun queries hqs ↦ ?_) (Nat.zero_le _)
      obtain ⟨hlen, hlt, hne⟩ := sampleQueriesAux_returns _ _ _ hqs
      rw [hdepth] at hlt hne
      have hne' : queries ≠ [] := hne hq1 hq1 (by rw [hh1]; omega) (by rw [hh1]; omega)
      refine ⟨hn1, ⟨hne', hlen.trans hq2, by rw [hh1]; exact hd2, hlt⟩, fun words ↦ ?_⟩
      refine Wired.cost_seq (CostLE.ret' words 0) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine Wired.cost_seq (CostLE.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine Wired.cost_seq (CostLE.sumcheckP 3 _ _) (fun r _ ↦ ?_) ?_
      · exact (Wired.of_cost (CostLE.require _)).mono (fun _ _ _ _ ↦ trivial) (Nat.zero_le _)
      · rw [List.length_replicate, hmu]; omega
    | cons next rest' =>
      refine Wired.cost_seq (foldRoundsP _ _) (fun r hr ↦ ?_) (by simp only [whirStream]; omega)
      obtain ⟨s', rounds⟩ := r
      have hf := foldRounds_returns _ _ hr
      simp only at hf
      have hdepth : logN - s'.alphas.length + level.logInvRate = hs.getD index 0 := by
        rw [hh1, hf]; omega
      have hmu : logN - s'.alphas.length = logN - s.alphas.length - level.fold := by omega
      simp only [levelShape, whirStream]
      have hc : Wired (VerifierProgram.readCommitment (logN - s'.alphas.length - next.fold +
          next.logInvRate) (2 * 2 ^ next.fold)) hs n 2
          (fun _ hs' n' ↦ hs' = hs ++ [logN - s'.alphas.length - next.fold +
            next.logInvRate] ∧ n' = n) :=
        ⟨le_rfl, rfl, rfl⟩
      refine Wired.seq hc (fun _ _ n' e ↦ ?_) (by omega)
      obtain ⟨rfl, hn'⟩ := e
      rw [hn']
      have hgi : (hs ++ [logN - s'.alphas.length - next.fold + next.logInvRate]).getD index 0 =
          hs.getD index 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      refine Wired.cost_seq (CostLE.readN _) (fun _ _ ↦ ?_) (by omega)
      refine Wired.cost_seq (CostLE.grindP _) (fun _ _ ↦ ?_) (by omega)
      refine Wired.cost_seq (CostLE.sampleN _) (fun _ _ ↦ ?_) (Nat.zero_le _)
      refine Wired.cost_seq CostLE.readE (fun _ _ ↦ ?_) (by omega)
      refine Wired.cost_seq (CostLE.grindP _) (fun _ _ ↦ ?_) (by omega)
      refine Wired.cost_seq (sampleQueriesAuxP _ _ _) (fun queries hqs ↦ ?_) (Nat.zero_le _)
      refine Wired.cost_seq CostLE.sampleE (fun lam _ ↦ ?_) (Nat.zero_le _)
      obtain ⟨hlen, hlt, hne⟩ := sampleQueriesAux_returns _ _ _ hqs
      rw [hdepth] at hlt hne
      have hne' : queries ≠ [] := hne hq1 hq1 (by rw [hh1]; omega) (by rw [hh1]; omega)
      refine ⟨hn1, ?_, fun words ↦ ?_⟩
      · rw [hgi]
        exact ⟨hne', hlen.trans hq2, by rw [hh1]; exact hd2, hlt⟩
      · refine (wired_whirLevels logN laneFolds evaluateBasis (next :: rest') (index + 1) _ _
          (n - 1) ?_ ?_ ?_ ?_).mono (fun _ _ _ h ↦ h) ?_
        · simp [hl]
        · simp only [List.length_cons] at hn ⊢; omega
        · rw [glueLevel_alphas, hmu]
          exact hrest
        · intro lv hlv
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
          subst hlv
          rw [glueLevel_alphas]
          simp [List.getD_eq_getElem?_getD, hl]
        · rw [glueLevel_alphas, hmu]
          omega

/-- The stack's commitment: the height of the ladder's first level. -/
theorem wired_commitStack (μ r : ℕ) (hs : List ℕ) (n : ℕ) :
    Wired (commitStack μ r) hs n 2 fun _ hs' n' ↦ n' = n ∧ ∃ level rest,
      Whir.ladder μ r = some (level :: rest) ∧
        hs' = hs ++ [μ - level.fold + level.logInvRate] := by
  unfold commitStack
  refine Wired.cost_seq (CostLE.liftOptionP _) (fun config hc ↦ ?_) (Nat.zero_le _)
  have hc := returnsAny_liftOption hc
  cases config with
  | nil => trivial
  | cons level rest => exact ⟨le_rfl, rfl, level, rest, hc, rfl⟩

/-- **The stacked opening is wired**, from the stack's commitment. -/
theorem wired_verifyStackedOpening (μ r : ℕ) (claims : List StackClaim) (batching : E)
    (hs : List ℕ) (n : ℕ) (level : Whir.Level) (rest : List Whir.Level)
    (hl : Whir.ladder μ r = some (level :: rest)) (hlen : hs.length = 1)
    (hh : hs.getD 0 0 = μ - level.fold + level.logInvRate) (hn : wireMaxPhases ≤ n) :
    Wired (verifyStackedOpening μ r claims batching) hs n whirStreamBound fun _ _ _ ↦ True := by
  obtain ⟨hlen', hlw, hst⟩ := ladder_wire _ _ _ hl
  unfold verifyStackedOpening
  refine Wired.cost_seq (CostLE.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  unfold verifyWhir
  refine Wired.cost_seq (CostLE.liftOptionP _) (fun config hc ↦ ?_) (Nat.zero_le _)
  have hc := returnsAny_liftOption hc
  rw [hl] at hc
  cases hc
  refine (wired_whirLevels _ _ _ _ 0 _ _ _ hlen (by omega) (by simpa using hlw) ?_).mono
    (fun _ _ _ h ↦ h) (by simpa using hst)
  intro lv hlv
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
  subst hlv
  simpa using hh

/-! ## The whole program -/

/-- The stream the leanVM verifier program reads, at most: the sizes, the stack's root, its
out-of-domain sample, the link, `KECCAK`'s reduction, ring switching and the WHIR levels. -/
def leanVmStream : ℕ := 8 + 2 + 2 + 122 + linkSufCost + keccakStream + 1 + whirStreamBound

theorem leanVmStream_lt : leanVmStream < 2 ^ 32 := by
  unfold leanVmStream linkSufCost keccakStream keccakStreamOf keccakLayerStream whirStreamBound
  decide

/-- **The prefix is wired**: the stack's commitment, of the ladder's first level's height, the
sizes the verifier accepts, `Chunks::new`'s chunks. -/
theorem wired_execPre (bytecode : List K) :
    Wired (execPre bytecode) [] wireMaxPhases (8 + 2 + 2 + 122) fun z hs n ↦
      n = wireMaxPhases ∧ SizesOK z.layout ∧ (∃ w, Chunks.new w = some z.link.chunks) ∧
        ∃ level rest, Whir.ladder z.layout.stackLog z.rate = some (level :: rest) ∧
          hs = [z.layout.stackLog - level.fold + level.logInvRate] := by
  unfold execPre
  refine Wired.cost_seq (readSizesP bytecode) (fun sizes hsz ↦ ?_) (by omega)
  have hok := (readSizes_ok hsz).1
  refine Wired.seq (wired_commitStack _ _ [] _) (fun _ hs' n' hc ↦ ?_) (by omega)
  obtain ⟨rfl, level, rest, hl, rfl⟩ := hc
  refine Wired.cost_seq (readOodP _) (fun _ _ ↦ ?_) (by omega)
  refine Wired.cost_seq (linkPreP _) (fun y hy ↦ ?_) (by omega)
  exact ⟨rfl, hok, linkPre_chunks hy, level, rest, hl, rfl⟩

theorem computedSplitP (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ)) :
    CostLE (computedSplit bytecode point pc) 0 := by
  unfold computedSplit
  exact CostLE.seq (CostLE.require _) (fun _ _ ↦ trivial) le_rfl

/-- **The suffix is wired**, from the stack's commitment. -/
theorem wired_execSuf (publicInput : Digest) (z : ExecPre) (split : Split) (hsz : SizesOK z.layout)
    {w : ℕ} (hc : Chunks.new w = some z.link.chunks) (level : Whir.Level)
    (rest : List Whir.Level) (hl : Whir.ladder z.layout.stackLog z.rate = some (level :: rest)) :
    Wired (execSuf publicInput z split) [z.layout.stackLog - level.fold + level.logInvRate]
      wireMaxPhases (linkSufCost + keccakStream + 1 + whirStreamBound) fun _ _ _ ↦ True := by
  unfold execSuf linkSuf
  refine Wired.cost_seq (linkSufOfP hsz hc _) (fun link _ ↦ ?_) (by omega)
  refine Wired.cost_seq (bindPublicInputP _ _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine Wired.cost_seq (keccakValidityP hsz _) (fun x _ ↦ ?_) (by omega)
  obtain ⟨outputs, keccakPoint, keccakSlices⟩ := x
  refine Wired.cost_seq (CostLE.liftOptionP _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine Wired.cost_seq (ringSwitchP _) (fun x _ ↦ ?_) (by omega)
  obtain ⟨ring, batching⟩ := x
  refine Wired.cost_seq (memoryTermClaimP _ _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  exact (wired_verifyStackedOpening _ _ _ _ _ _ level rest hl rfl rfl le_rfl).mono
    (fun _ _ _ h ↦ h) (by omega)

/-- **The verifier program's openings and stream are within the wire bounds**, from no commitment,
with `wireMaxPhases` openings and `leanVmStream` stream elements. -/
theorem wired_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    Wired (leanVmVerifierProgram bytecode publicInput) [] wireMaxPhases leanVmStream
      fun _ _ _ ↦ True := by
  rw [leanVmVerifierProgram_eq, verifyExecution_split]
  refine (Wired.bind (f := fun _ ↦ VerifierProgram.ret true) (a := leanVmStream) (b := 0)
    (Q := fun _ _ _ ↦ True) (R := fun _ _ _ ↦ True) ?_ fun _ _ _ _ ↦ trivial).mono
    (fun _ _ _ h ↦ h) le_rfl
  refine Wired.seq (wired_execPre bytecode) (fun z hs n hz ↦ ?_) (by unfold leanVmStream; omega)
  obtain ⟨rfl, hsz, ⟨w, hc⟩, level, rest, hl, rfl⟩ := hz
  refine Wired.cost_seq (computedSplitP _ _ _) (fun split _ ↦ ?_) (Nat.zero_le _)
  exact (wired_execSuf publicInput z split hsz hc level rest hl).mono (fun _ _ _ h ↦ h)
    (by unfold leanVmStream; omega)

end LeanVM.Wire

end
