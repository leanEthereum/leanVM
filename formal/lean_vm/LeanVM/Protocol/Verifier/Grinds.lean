/-
  LeanVM.Protocol.Verifier.Grinds

  The leanVM verifier's proofs of work have at most `64` bits: every reachable history ends with
  a proof of work of at most `64` bits, the discount the random-oracle theorem's `εmax` reads.
-/

module

public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.Compile.Moves

/-!
# The verifier's proofs of work are at most `64` bits

`GrindsLE B Q p`: every proof of work of `p` has at most `B` bits, and every value `p` returns
satisfies `Q`. It composes through `bind` with the postcondition (`GrindsLE.seq`), so a proof of
work whose bits depend on the announced sizes (the link's, `grindingBits` of the tables' heights
and the pointer width) is bounded on the sizes `buildLayout` admits (`LayoutBounds`,
`chunks_bounds`). Along a reachable history of such a program the last proof of work has at most
`B` bits (`GrindsLE.grindBits_le`).

`grindBits_le_of_reachable`: on every reachable history of the leanVM verifier program,
`grindBits h ≤ 64`; `grindBits_le_of_reachable_deferring` for the deferring program.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Protocol.Verifier VerifierProgram

@[expose] public section

variable {α β : Type}

/-- **Every proof of work of `p` has at most `B` bits, and every value it returns satisfies
`Q`.** -/
def GrindsLE (B : ℕ) (Q : α → Prop) : VerifierProgram α → Prop
  | .ret a => Q a
  | .fail => True
  | .read k => ∀ x, GrindsLE B Q (k x)
  | .sample k => ∀ x, GrindsLE B Q (k x)
  | .readPacked _ k => ∀ xs, GrindsLE B Q (k xs)
  | .samplePacked _ k => ∀ xs, GrindsLE B Q (k xs)
  | .grind b k => b ≤ B ∧ GrindsLE B Q k
  | .commit _ _ k => GrindsLE B Q k
  | .query _ _ k => ∀ rows, GrindsLE B Q (k rows)

namespace GrindsLE

variable {B : ℕ}

theorem mono {Q R : α → Prop} (hQR : ∀ a, Q a → R a) {p : VerifierProgram α}
    (h : GrindsLE B Q p) : GrindsLE B R p := by
  induction p with
  | ret a => exact hQR a h
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (h x)
  | sample k ih => exact fun x ↦ ih x (h x)
  | readPacked n k ih => exact fun x ↦ ih x (h x)
  | samplePacked n k ih => exact fun x ↦ ih x (h x)
  | grind b k ih => exact ⟨h.1, ih h.2⟩
  | commit ht w k ih => exact ih h
  | query i ps k ih => exact fun x ↦ ih x (h x)

/-- **Sequencing**: the follower bounded on the values the first part returns. -/
theorem bind {Q : α → Prop} {R : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : GrindsLE B Q p) (hf : ∀ a, Q a → GrindsLE B R (f a)) : GrindsLE B R (p.bind f) := by
  induction p with
  | ret a => exact hf a hp
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | readPacked n k ih => exact fun x ↦ ih x (hp x)
  | samplePacked n k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih => exact ⟨hp.1, ih hp.2⟩
  | commit h w k ih => exact ih hp
  | query i ps k ih => exact fun x ↦ ih x (hp x)

/-- Sequencing in `do` notation. -/
theorem seq {Q : α → Prop} {R : β → Prop} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : GrindsLE B Q p) (hf : ∀ a, Q a → GrindsLE B R (f a)) : GrindsLE B R (p >>= f) :=
  bind hp hf

/-- Along a history, the node reached is bounded too (its returns unconstrained). -/
theorem after {Q : α → Prop} : ∀ {p : VerifierProgram α} {l : List Ev} {q : VerifierProgram α},
    GrindsLE B Q p → p.after l = some q → GrindsLE B (fun _ ↦ True) q
  | p, [], q, hp, h => by
    simp only [VerifierProgram.after, Option.some.injEq] at h
    subst h
    exact hp.mono fun _ _ ↦ trivial
  | .ret _, _ :: _, _, _, h => by simp [VerifierProgram.after] at h
  | .fail, _ :: _, _, _, h => by simp [VerifierProgram.after] at h
  | .read k, e :: es, _, hp, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    exact after (hp _) h
  | .sample k, e :: es, _, hp, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    exact after (hp _) h
  | .readPacked n k, e :: es, _, hp, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    exact after (hp _) h
  | .samplePacked n k, e :: es, _, hp, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    exact after (hp _) h
  | .grind b k, e :: es, _, hp, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    exact after hp.2 h
  | .commit ht w k, e :: es, _, hp, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    split_ifs at h
    exact after (p := k) hp h
  | .query i ps k, e :: es, _, hp, h => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    exact after (hp _) h

/-- **Along a reachable history, the last proof of work has at most `B` bits.** -/
theorem grindBits_le {Q : α → Prop} {P : VerifierProgram α} (hP : GrindsLE B Q P) {h : List Ev}
    (hh : P.Reachable h) : grindBits h ≤ B := by
  cases hh with
  | nil => simp [grindBits]
  | grind _ ha => simpa [grindBits] using (hP.after ha).1
  | read _ _ _ => simp [grindBits]
  | sample _ _ _ => simp [grindBits]
  | commit _ _ _ _ => simp [grindBits]
  | query _ _ _ => simp [grindBits]
  | readPacked _ _ _ _ => simp [grindBits]
  | samplePacked _ _ _ _ => simp [grindBits]

/-! ## Leaves -/

theorem ret' {Q : α → Prop} {a : α} (h : Q a) : GrindsLE B Q (ret a) := h

theorem pure' (a : α) : GrindsLE B (fun _ ↦ True) (pure a : VerifierProgram α) := trivial

theorem fail' {Q : α → Prop} : GrindsLE B Q (fail : VerifierProgram α) := trivial

theorem readE : GrindsLE B (fun _ ↦ True) readScalar := fun _ ↦ trivial

theorem sampleE : GrindsLE B (fun _ ↦ True) sampleChallenge := fun _ ↦ trivial

theorem readN : ∀ n, GrindsLE B (fun _ ↦ True) (readScalars n)
  | 0 => trivial
  | n + 1 => fun _ ↦ (readN n).bind fun _ _ ↦ trivial

theorem sampleN : ∀ n, GrindsLE B (fun xs ↦ xs.length = n) (sampleChallenges n)
  | 0 => rfl
  | n + 1 => fun _ ↦ (sampleN n).bind fun xs hxs ↦ by
      show (_ :: xs).length = n + 1
      simp [hxs]

theorem readPackedE (n : ℕ) : GrindsLE B (fun _ ↦ True) (readScalarsPacked n) := fun _ ↦ trivial

theorem samplePackedE (n : ℕ) : GrindsLE B (fun _ ↦ True) (sampleChallengesPacked n) :=
  fun _ ↦ trivial

theorem requireI {c : Prop} {inst : Decidable c} : GrindsLE B (fun _ ↦ c) (@require c inst) := by
  unfold require; split
  · exact ‹c›
  · trivial

theorem liftOption' (o : Option α) : GrindsLE B (fun a ↦ o = some a) (liftOption o) := by
  cases o
  · trivial
  · rfl

theorem grindP {b : ℕ} (hb : b ≤ B) : GrindsLE B (fun _ ↦ True) (grindProofOfWork b) := by
  unfold grindProofOfWork; split
  · trivial
  · exact ⟨hb, trivial⟩

theorem commitP (ht w : ℕ) : GrindsLE B (fun _ ↦ True) (readCommitment ht w) := trivial

theorem queryP (i : ℕ) (ps : List ℕ) : GrindsLE B (fun _ ↦ True) (queryOpenings i ps) :=
  fun _ ↦ trivial

end GrindsLE

/-! ## The verifier's pieces -/

theorem grindsLE_sumcheckRoundPoly {count : ℕ} (hc : count ≤ 2 ^ 66) (claim : E) (e : Option E) :
    GrindsLE 64 (fun _ ↦ True) (sumcheckRoundPoly count claim e) := by
  cases e with
  | none =>
    unfold sumcheckRoundPoly
    exact GrindsLE.readE.seq fun _ _ ↦ (GrindsLE.readN _).seq fun _ _ ↦
      (GrindsLE.grindP (grindingBits_le_sixtyFour (by omega))).seq fun _ _ ↦ GrindsLE.pure' _
  | some f =>
    unfold sumcheckRoundPoly
    exact (GrindsLE.readN _).seq fun _ _ ↦
      (GrindsLE.grindP (grindingBits_le_sixtyFour (by omega))).seq fun _ _ ↦ GrindsLE.pure' _

theorem grindsLE_sumcheck {count : ℕ} (hc : count ≤ 2 ^ 66) :
    ∀ (eqs : List (Option E)) (claim : E), GrindsLE 64 (fun _ ↦ True) (sumcheck claim count eqs)
  | [], _ => by unfold sumcheck; exact GrindsLE.pure' _
  | e :: es, claim => by
    unfold sumcheck
    exact (grindsLE_sumcheckRoundPoly hc _ _).seq fun _ _ ↦ GrindsLE.sampleE.seq fun _ _ ↦
      (grindsLE_sumcheck hc es _).seq fun _ _ ↦ GrindsLE.pure' _

theorem grindsLE_sampleQueriesAux (depth : ℕ) :
    ∀ (fuel remaining : ℕ), GrindsLE 64 (fun _ ↦ True) (sampleQueriesAux depth fuel remaining)
  | 0, _ => by unfold sampleQueriesAux; exact GrindsLE.pure' _
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    split
    · exact GrindsLE.pure' _
    · exact GrindsLE.sampleE.seq fun _ _ ↦
        (grindsLE_sampleQueriesAux depth fuel _).seq fun _ _ ↦ GrindsLE.pure' _

theorem grindsLE_foldRounds : ∀ (n : ℕ) (s : WhirState),
    GrindsLE 64 (fun _ ↦ True) (foldRounds n s)
  | 0, _ => by unfold foldRounds; exact GrindsLE.pure' _
  | n + 1, s => by
    unfold foldRounds
    refine GrindsLE.seq (Q := fun _ ↦ True) ?_ fun _ _ ↦ ?_
    · unfold foldRound
      exact GrindsLE.readE.seq fun _ _ ↦ GrindsLE.readE.seq fun _ _ ↦
        GrindsLE.readE.seq fun _ _ ↦ GrindsLE.readE.seq fun _ _ ↦
        (GrindsLE.grindP (by decide)).seq fun _ _ ↦ GrindsLE.sampleE.seq fun _ _ ↦
        GrindsLE.sampleE.seq fun _ _ ↦ GrindsLE.pure' _
    · exact (grindsLE_foldRounds n _).seq fun _ _ ↦ GrindsLE.pure' _

theorem grindsLE_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      GrindsLE 64 (fun _ ↦ True) (whirLevels logN laneFolds evaluateBasis index levels s)
  | _, [], _ => by unfold whirLevels; exact GrindsLE.fail'
  | index, level :: rest, s => by
    unfold whirLevels
    refine (grindsLE_foldRounds _ _).seq fun r _ ↦ ?_
    obtain ⟨s', rounds⟩ := r
    dsimp only
    split
    · refine (GrindsLE.readN _).seq fun _ _ ↦ ?_
      refine (GrindsLE.grindP (by decide)).seq fun _ _ ↦ ?_
      refine (grindsLE_sampleQueriesAux _ _ _).seq fun _ _ ↦ ?_
      refine (GrindsLE.queryP _ _).seq fun _ _ ↦ ?_
      refine GrindsLE.requireI.seq fun _ _ ↦ ?_
      refine (grindsLE_sumcheck (by norm_num) _ _).seq fun r _ ↦ ?_
      exact GrindsLE.requireI.mono fun _ _ ↦ trivial
    · refine (GrindsLE.commitP _ _).seq fun _ _ ↦ ?_
      refine (GrindsLE.readN _).seq fun _ _ ↦ ?_
      refine (GrindsLE.grindP (by decide)).seq fun _ _ ↦ ?_
      refine (GrindsLE.sampleN _).seq fun _ _ ↦ ?_
      refine GrindsLE.readE.seq fun _ _ ↦ ?_
      refine (GrindsLE.grindP (by decide)).seq fun _ _ ↦ ?_
      refine (grindsLE_sampleQueriesAux _ _ _).seq fun _ _ ↦ ?_
      refine GrindsLE.sampleE.seq fun _ _ ↦ ?_
      refine (GrindsLE.queryP _ _).seq fun _ _ ↦ ?_
      exact grindsLE_whirLevels logN laneFolds evaluateBasis _ _ _

theorem grindsLE_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (batching : E) :
    GrindsLE 64 (fun _ ↦ True) (verifyStackedOpening stackLog logInvRate claims batching) := by
  unfold verifyStackedOpening verifyWhir
  exact GrindsLE.requireI.seq fun _ _ ↦ (GrindsLE.liftOption' _).seq fun _ _ ↦
    grindsLE_whirLevels _ _ _ _ _ _

theorem grindsLE_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    GrindsLE 64 (fun _ ↦ True) (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  dsimp only
  with_reducible refine GrindsLE.seq (GrindsLE.readN _) fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq GrindsLE.requireI fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq (GrindsLE.grindP (by decide)) fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq GrindsLE.sampleE fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq (grindsLE_sumcheck (by norm_num) _ _) ?_
  rintro ⟨_, _⟩ _
  dsimp only
  with_reducible refine GrindsLE.seq (grindsLE_sumcheck (by norm_num) _ _) ?_
  rintro ⟨_, _⟩ _
  dsimp only
  with_reducible refine GrindsLE.seq (GrindsLE.readN _) fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq GrindsLE.requireI fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq (GrindsLE.grindP (by decide)) fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq GrindsLE.sampleE fun _ _ ↦ ?_
  exact GrindsLE.pure' _

theorem grindsLE_keccakLayers (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : KeccakClaim),
      GrindsLE 64 (fun _ ↦ True) (keccakLayers logSteps steps claim)
  | [], _ => by unfold keccakLayers; exact GrindsLE.pure' _
  | step :: steps, claim => by
    unfold keccakLayers
    with_reducible exact (grindsLE_verifyKeccakLayer _ _ _).seq fun _ _ ↦
      grindsLE_keccakLayers logSteps steps _

theorem grindsLE_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    GrindsLE 64 (fun _ ↦ True) (keccakOpen logSteps claim first count value) := by
  unfold keccakOpen
  with_reducible refine GrindsLE.seq (grindsLE_sumcheck (by norm_num) _ _) ?_
  rintro ⟨_, _⟩ _
  exact GrindsLE.pure' _

theorem grindsLE_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    GrindsLE 64 (fun _ ↦ True) (verifyKeccak logSteps inst output) := by
  unfold verifyKeccak
  dsimp only
  with_reducible refine GrindsLE.seq GrindsLE.requireI fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq (GrindsLE.grindP (by decide)) fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq (GrindsLE.sampleN _) fun _ _ ↦ ?_
  with_reducible refine GrindsLE.seq (GrindsLE.sampleN _) fun _ _ ↦ ?_
  repeat' (first
    | split
    | with_reducible exact GrindsLE.pure' _
    | with_reducible refine GrindsLE.seq (grindsLE_keccakLayers _ _ _) fun _ _ ↦ ?_
    | with_reducible refine GrindsLE.seq (grindsLE_sumcheck (by norm_num) _ _) fun _ _ ↦ ?_
    | with_reducible refine GrindsLE.seq GrindsLE.readE fun _ _ ↦ ?_
    | with_reducible refine GrindsLE.seq (GrindsLE.readN _) fun _ _ ↦ ?_
    | with_reducible refine GrindsLE.seq GrindsLE.requireI fun _ _ ↦ ?_
    | with_reducible refine GrindsLE.seq (GrindsLE.pure' _) fun _ _ ↦ ?_
    | with_reducible refine GrindsLE.seq (grindsLE_keccakOpen _ _ _ _ _) fun _ _ ↦ ?_)

theorem grindsLE_keccakValidity (layout : Layout) (link : LinkEnd) :
    GrindsLE 64 (fun _ ↦ True) (keccakValidity layout link) := by
  unfold keccakValidity
  split
  with_reducible exact (GrindsLE.liftOption' _).seq fun _ _ ↦ grindsLE_verifyKeccak _ _ _

theorem grindsLE_ringSwitch (claims : List RingClaim) :
    GrindsLE 64 (fun _ ↦ True) (ringSwitch claims) := by
  unfold ringSwitch
  exact (GrindsLE.grindP (by decide)).seq fun _ _ ↦ (GrindsLE.samplePackedE _).seq fun _ _ ↦
    GrindsLE.pure' _

/-- **The link's proofs of work**, on a built layout: its challenges' grind is
`grindingBits` of the tables' heights and the pointer width, its sum-checks' of their degrees. -/
theorem grindsLE_verifyLink
    {bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split}
    (hsplit : ∀ b p pc, GrindsLE 64 (fun _ ↦ True) (bytecodeSplit b p pc))
    {layout : Layout} (hl : LayoutBounds layout) :
    GrindsLE 64 (fun _ ↦ True) (verifyLink bytecodeSplit layout) := by
  unfold verifyLink
  refine (GrindsLE.liftOption' _).seq fun chunks hch ↦ ?_
  obtain ⟨hw, hd⟩ := chunks_bounds hch
  have hrows : layout.tableLogHeights.foldl max 0 ≤ 30 := foldl_max_le hl.heights_le
  have hslot : bytecodeSlotBits = 4 := rfl
  dsimp only
  refine (GrindsLE.grindP (grindingBits_le_sixtyFour (by omega))).seq fun _ _ ↦ ?_
  refine GrindsLE.sampleE.seq fun _ _ ↦ ?_
  refine (GrindsLE.samplePackedE _).seq fun _ _ ↦ ?_
  refine (grindsLE_sumcheck (by norm_num) _ _).seq fun r _ ↦ ?_
  obtain ⟨r, claim⟩ := r
  refine GrindsLE.readE.seq fun _ _ ↦ ?_
  refine (GrindsLE.samplePackedE 5).seq fun _ _ ↦ ?_
  refine (hsplit _ _ _).seq fun _ _ ↦ ?_
  have hrc : (roundCoefficients chunks.d).1 ≤ 2 ^ 66 := by simp only [roundCoefficients]; omega
  have hcc : (roundCoefficients chunks.d).2 ≤ 2 ^ 66 := by simp only [roundCoefficients]; omega
  refine (grindsLE_sumcheck hrc _ _).seq fun _ _ ↦ ?_
  refine (grindsLE_sumcheck hcc _ _).seq fun _ _ ↦ ?_
  refine (GrindsLE.readPackedE _).seq fun _ _ ↦ ?_
  exact GrindsLE.requireI.seq fun _ _ ↦ GrindsLE.pure' _

/-- The phases before the link, and the announced sizes' bounds. -/
theorem grindsLE_readAnnouncedSizes (bytecode : List K) :
    GrindsLE 64 SizesOK (readAnnouncedSizes bytecode) := by
  unfold readAnnouncedSizes
  refine (GrindsLE.readN _).seq fun _ _ ↦ ?_
  refine GrindsLE.requireI.seq fun _ _ ↦ ?_
  refine GrindsLE.requireI.seq fun _ hr ↦ ?_
  refine (GrindsLE.liftOption' _).seq fun layout hl ↦ ?_
  refine GrindsLE.requireI.seq fun _ hs ↦ ?_
  exact (show SizesOK _ from ⟨layoutBounds_of_buildLayout hl, hr.1, hr.2, hs.1, hs.2⟩)

/-- **The verifier's proofs of work**, for a split without one. -/
theorem grindsLE_verifyExecution
    {bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split}
    (hsplit : ∀ b p pc, GrindsLE 64 (fun _ ↦ True) (bytecodeSplit b p pc))
    (bytecode : List K) (pd : Digest) :
    GrindsLE 64 (fun _ ↦ True) (verifyExecution bytecodeSplit bytecode pd) := by
  unfold verifyExecution
  refine (grindsLE_readAnnouncedSizes bytecode).seq fun p hp ↦ ?_
  obtain ⟨layout, logInverseRate⟩ := p
  obtain ⟨hl, -⟩ := hp
  refine GrindsLE.seq (Q := fun _ ↦ True) ?_ fun _ _ ↦ ?_
  · unfold commitStack
    refine (GrindsLE.liftOption' _).seq fun config _ ↦ ?_
    rcases config with _ | ⟨level, rest⟩
    · exact GrindsLE.fail'
    · exact GrindsLE.commitP _ _
  refine GrindsLE.seq (Q := fun _ ↦ True) ?_ fun _ _ ↦ ?_
  · unfold readOod
    exact (GrindsLE.grindP (by decide)).seq fun _ _ ↦ (GrindsLE.sampleN _).seq fun _ _ ↦
      GrindsLE.readE.seq fun _ _ ↦ GrindsLE.pure' _
  refine (grindsLE_verifyLink hsplit hl).seq fun link _ ↦ ?_
  refine GrindsLE.seq (Q := fun _ ↦ True) ?_ fun _ _ ↦ ?_
  · unfold bindPublicInput
    exact GrindsLE.sampleE.seq fun _ _ ↦ (GrindsLE.liftOption' _).seq fun _ _ ↦ GrindsLE.pure' _
  refine (grindsLE_keccakValidity _ link).seq fun r _ ↦ ?_
  obtain ⟨outputs, keccakPoint, keccakSlices⟩ := r
  refine (GrindsLE.liftOption' _).seq fun _ _ ↦ ?_
  refine (grindsLE_ringSwitch _).seq fun r _ ↦ ?_
  obtain ⟨ring, batching⟩ := r
  refine GrindsLE.seq (Q := fun _ ↦ True) ?_ fun _ _ ↦ ?_
  · unfold memoryTermClaim
    exact (GrindsLE.liftOption' _).seq fun _ _ ↦ (GrindsLE.liftOption' _).seq fun _ _ ↦
      GrindsLE.pure' _
  exact grindsLE_verifyStackedOpening _ _ _ _

theorem grindsLE_computedSplit (b : List K) (p : List E) (pc : List (ℕ × ℕ)) :
    GrindsLE 64 (fun _ ↦ True) (computedSplit b p pc) := by
  unfold computedSplit
  exact GrindsLE.requireI.seq fun _ _ ↦ GrindsLE.pure' _

theorem grindsLE_freshSplit (fresh : FreshClaim) (b : List K) (p : List E) (pc : List (ℕ × ℕ)) :
    GrindsLE 64 (fun _ ↦ True) (freshSplit fresh b p pc) := by
  unfold freshSplit
  exact GrindsLE.requireI.seq fun _ _ ↦ GrindsLE.pure' _

/-- **Every proof of work of the leanVM verifier program has at most `64` bits.** -/
theorem grindsLE_leanVmVerifierProgram (bytecode : List K) (pd : Digest) :
    GrindsLE 64 (fun _ ↦ True) (leanVmVerifierProgram bytecode pd) := by
  unfold leanVmVerifierProgram
  exact (grindsLE_verifyExecution grindsLE_computedSplit _ _).seq fun _ _ ↦ GrindsLE.pure' _

/-- **On every reachable history of the leanVM verifier program, the last proof of work has at
most `64` bits.** -/
theorem grindBits_le_of_reachable (bytecode : List K) (pd : Digest) {h : List Ev}
    (hh : (leanVmVerifierProgram bytecode pd).Reachable h) : grindBits h ≤ 64 :=
  (grindsLE_leanVmVerifierProgram bytecode pd).grindBits_le hh

/-- The same for the deferring verifier program. -/
theorem grindBits_le_of_reachable_deferring (fresh : FreshClaim) (bytecode : List K) (pd : Digest)
    {h : List Ev} (hh : (deferringVerifierProgram fresh bytecode pd).Reachable h) :
    grindBits h ≤ 64 := by
  have hP : GrindsLE 64 (fun _ ↦ True) (deferringVerifierProgram fresh bytecode pd) := by
    unfold deferringVerifierProgram
    exact (grindsLE_verifyExecution (grindsLE_freshSplit fresh) _ _).seq fun _ _ ↦
      GrindsLE.pure' _
  exact hP.grindBits_le hh

end

end LeanVM.Protocol.Compile
