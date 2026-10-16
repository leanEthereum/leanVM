module

public import LeanVMCircuits.Rec.Run

@[expose] public section

/-!
The round theorems' premises can all hold.

`sumcheck_test_sound` and `odd_test_sound` quantify over the prover's answers to every challenge vector. As first
stated, the answers had to compress at every hash row, the squeezes included, and to agree on what is absorbed before
each challenge whenever the challenges before it agree; the challenge, a compression of what is absorbed, then agreed
too, so no answers existed once `E` has two elements and both theorems were vacuous. They now ask for answers in the
random-oracle view (`RomAnswers`: squeezes relaxed, each challenge a seed one step after the block it reads), and
these lemmas exhibit answers meeting every premise but the circuit's acceptance, on a circuit whose challenges are
squeezes of its transcript's blocks. `top_test_sound` and `whir_test_sound` take answers in the same view.

The circuit (`state`): four `HASH` rows tagged at the duplex's output role, the first and third read as absorb blocks
(`transcript`), the second and fourth as the squeezes drawing `λ` (wire 16, from block 0) and the next challenge (wire
22, from block 1). The sumcheck (`sumcheck`) has one round reading the first block's words, and `sumcheckH` is it with
its input claim a hint; the odd layer (`odd`) and the top layer (`top`, whose last challenge is wire 23) have one value;
the WHIR sumcheck (`whir`) has a batch round at `λ`, whose squeeze's fourth word is squeezed with it, then a fold round.
`sumcheck_answers_exist`, `sumcheck_hinted_answers_exist`, `odd_answers_exist`, `top_answers_exist` and
`whir_answers_exist` give answers whose challenges are any vector, which the first statement could not;
`pow_answers_exist` gives proof-of-work answers whose trial words are uniform. `run_exists` gives a prover's run in
the random-oracle model (`Run`) whose two challenges read three words each of their squeezes, drawn in order, meeting
every premise of `Run.sumcheckAnswers` and the other answer theorems but acceptance.
-/

namespace LeanVMCircuits.Rec.Bind.RomExample

open LeanVMCircuits.Rec Model Sumcheck Polynomial Finset

/-- The duplex's output role, as a counter word. -/
def outTag : ℕ := 6 * 2 ^ 56

/-- A `HASH` row reading chaining value `h` and writing `o`, its counter wire 1, its message wires 8 to 15. -/
def row (h o : ℕ) : List ℕ := [h, 1, 2, 3, 4, 5, o, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def state : State where
  next := 24
  hash := #[row 0 6, row 6 16, row 6 21, row 21 22]
  pub := #[(1, .const [outTag, 0, 0, 0])]

def transcript : Transcript where
  blocks := [0, 2]
  firings := #[]
  squeezes := [1, 3]

def round : RoundCert where
  coeffs := [8, 9]
  weight := none
  tailZero := 0
  tailAt := []
  fixedAt := 0
  chal := 16
  hornerZero := 0
  hornerAt := []
  chalAt := 0
  words := []
  time := 1

def sumcheck : SumcheckCert where
  claim0 := 17
  rounds := [round]
  deg := 1
  test := 0
  final := 18
  transcript := 0

/-- The same sumcheck with its input claim a hint (wire 17), which no transcript binds. -/
def sumcheckH : SumcheckCert := { sumcheck with hints := [17] }

def odd : OddCert where
  values := [17]
  lam := ⟨16, 0, [], 1⟩
  claimZero := 0
  claimAt := []
  lefts := []
  rights := []
  prodAt := []
  expZero := 0
  expAt := []
  test := 0
  next := ⟨22, 0, [], 2⟩
  sumAt := []
  outAt := []
  transcript := 0

def top : TopCert where
  values := [17]
  lam := ⟨16, 0, [], 1⟩
  claimZero := 0
  claimAt := []
  kids := []
  prodAt := []
  expZero := 0
  expAt := []
  test := 0
  low := ⟨22, 0, [], 2⟩
  high := ⟨23, 0, [], 2⟩
  lineAt := []
  transcript := 0

/-- A batch round at `λ` (wire 16, drawn after block 0; its own words the squeeze's first three), then a fold round
at the next challenge (wire 22, after block 1). -/
def batchRound : WhirRound := .batch ⟨16, 0, [], 1⟩ (.atom 17) [64, 65, 66] #[]

def whirRound : WhirRound := .fold (.recv 17 8 9 0 0 0) ⟨22, 0, [], 2⟩ 0 0

def whir : WhirCert where
  claim0 := 17
  rounds := [batchRound, whirRound]
  test := 0
  final := 18
  transcript := 0

def powCert : PowCert where
  compressAt := 0
  dkAt := 0
  splitAt := 0
  bits := 0
  testAt := []

def cert : Cert where
  rules := {}
  nodes := 0
  isTest := #[]
  claims := #[]
  transcripts := [transcript]
  calls := #[]
  relax := #[]
  pools := #[]
  prods := #[]
  points := #[]
  covers := #[]
  sumchecks := #[sumcheck, sumcheckH]
  pows := #[powCert]
  odds := #[odd]
  tops := #[top]
  whirs := #[whir]

/-- Limbs of an element of `E`. -/
noncomputable def limbsE (e : E) : Fin 4 → K := fun i =>
  match i with
  | 0 => (toE_surjective e).choose
  | 1 => (toE_surjective e).choose_spec.choose
  | 2 => (toE_surjective e).choose_spec.choose_spec.choose
  | 3 => 0

theorem ev_limbsE (val : Val) (w : ℕ) (e : E) (h : val w = limbsE e) : Model.ev val w = e := by
  rw [Model.ev, h]
  exact (toE_surjective e).choose_spec.choose_spec.choose_spec

/-- The answer to challenges `a` (`λ`) and `b` (the next): the counter its constant, the challenges theirs, the value
and the input claim one, every other wire zero. -/
noncomputable def answer (a b : E) : Val := fun w =>
  if w = 1 then limbsOf [outTag, 0, 0, 0] else if w = 16 then limbsE a else if w = 22 then limbsE b
  else if w = 17 then limbsE 1 else fun _ => 0

/-- The answer to challenges `a`, `b` and `d`, the third at wire 23. -/
noncomputable def answer3 (a b d : E) : Val := fun w => if w = 23 then limbsE d else answer a b w

/-- The transcript's random-oracle view drops every row: its two absorb blocks and its two squeezes. -/
theorem dropped_rows : ∀ r ∈ state.hash, dropOf state (cert.transcripts.getD 0 default) r = true := by
  intro r hr
  simp only [state, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

theorem rom {ι : Type} (st : ι → ℕ → Fin 4 → K) (val : ι → Val) (hpub : ∀ r, val r 1 = limbsOf [outTag, 0, 0, 0]) :
    RomAnswers cert state 0 st val where
  holds r := {
    unions := fun p hp => by simp [keepP, keep, state] at hp
    emul := fun _ hp => by simp [keepP, keep, state] at hp
    exk := fun _ hp => by simp [keepP, keep, state] at hp
    hash := fun x hx => by
      simp only [keepP] at hx
      obtain ⟨hm, hs⟩ := Array.mem_filter.mp hx
      rw [dropped_rows x hm] at hs
      exact absurd hs (by decide)
    split := fun _ hp => by simp [keepP, keep, state] at hp
    cast := fun _ hp => by simp [keepP, keep, state] at hp
    pub := fun w src hp => by
      simp only [keepP, keep, state, List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact hpub r }
  facts _ := fun j hj => absurd hj (by simp [cert])
  unions _ _ := fun uc hu => by simp [cert] at hu

/-- Every row is a squeeze, so any two assignments are collision-free on the rows any seeds bind. -/
theorem pairCR (X : List ℕ) (val val' : Val) : PairCR cert state 0 X val val' :=
  ⟨fun x hx _ _ hs => absurd (dropped_rows x hx) (by rw [hs]; decide),
    fun x hx _ _ hs => absurd (dropped_rows x hx) (by rw [hs]; decide)⟩

/-- What the simp sets need to compute a seed list. -/
theorem chalSeeds_eq : chalSeeds state transcript = [(2, 64), (2, 65), (2, 66), (2, 67), (3, 88), (3, 89), (3, 90), (3, 91)] := by
  simp [chalSeeds, transcript, state, row, isSqueezeRow, outTag, readsBlock, hashOut, colNode, hashSrc, limb,
    List.findIdx?_cons, List.range_succ]

theorem seeds_one : seedsBefore state transcript 1 = [32, 36, 40, 44, 48, 52, 56, 60] := by
  rw [seedsBefore, chalSeeds_eq]
  simp [absorbed, wordsOf, transcript, state, row, limb, List.range_succ]

theorem seeds_two : seedsBefore state transcript 2 =
    [32, 36, 40, 44, 48, 52, 56, 60, 32, 36, 40, 44, 48, 52, 56, 60, 64, 65, 66, 67] := by
  rw [seedsBefore, chalSeeds_eq]
  simp [absorbed, wordsOf, transcript, state, row, limb, List.range_succ]

/-- The words squeezed with `λ` but its own three: its squeeze's fourth. -/
theorem sibs_one : sibSeeds state transcript 1 [64, 65, 66] = [67] := by
  rw [sibSeeds, chalSeeds_eq]
  rfl

/-- The honest instance of one round: the zero polynomial, ending at zero. -/
noncomputable def inst : Inst E 1 := .node none 0 fun _ => .leaf 0

/-- The honest instance of two rounds, the first with eq weight zero (a batch round): zero polynomials, ending at
zero. -/
noncomputable def inst2 : Inst E 2 := .node (some 0) 0 fun _ => .node none 0 fun _ => .leaf 0

/-- Answers meeting every premise of `sumcheck_test_sound` but acceptance, at every challenge vector, all `good`. -/
theorem sumcheck_answers_exist :
    ∃ (c : Cert) (s : State) (sc : SumcheckCert) (I : Inst E sc.rounds.length) (T : ℕ → E)
      (st : (Fin sc.rounds.length → E) → ℕ → Fin 4 → K) (val : (Fin sc.rounds.length → E) → Val),
      sc ∈ c.sumchecks ∧ 0 < sc.rounds.length ∧ I.ok sc.deg ∧ SumcheckAnswers c s sc I T (fun _ => True) st val := by
  have h0 : ∀ i : Fin sumcheck.rounds.length, i = ⟨0, by decide⟩ := fun i =>
    Fin.ext (by have := i.isLt; simp [sumcheck] at this; omega)
  refine ⟨cert, state, sumcheck, inst, fun _ => 0, fun _ _ _ => 0, fun r => answer (r ⟨0, by decide⟩) 0,
    by simp [cert], by decide, ⟨by simp, fun r => ⟨by simp [Inst.sum], trivial⟩⟩, ?_⟩
  refine ⟨rom _ _ fun r => by simp [answer], fun r r' i _ m hm => ?_, fun _ _ _ _ _ _ => pairCR _ _ _, fun r i => ?_,
    fun r i => ?_, fun r _ _ => ?_⟩
  · obtain rfl := h0 i
    rw [show (sumcheck.rounds.getD 0 default).time = 1 from rfl,
      show cert.transcripts.getD sumcheck.transcript default = transcript from rfl, seeds_one] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nu, answer]
  · obtain rfl := h0 i
    exact ev_limbsE _ 16 _ (by simp [answer, sumcheck, round])
  · obtain rfl := h0 i
    rfl
  · rw [show sumcheck.claim0 = 17 from rfl, ev_limbsE _ 17 1 (by simp [answer])]
    simp [inst, Inst.sum, lin]

/-- Answers meeting every premise of `sumcheck_test_sound` but acceptance, at every challenge vector, for a sumcheck
whose input claim is a hint the prover picks after the challenge (its value is the challenge), true at one. -/
theorem sumcheck_hinted_answers_exist :
    ∃ (c : Cert) (s : State) (sc : SumcheckCert) (I : Inst E sc.rounds.length) (T : ℕ → E)
      (st : (Fin sc.rounds.length → E) → ℕ → Fin 4 → K) (val : (Fin sc.rounds.length → E) → Val),
      sc ∈ c.sumchecks ∧ sc.hints = [sc.claim0] ∧ 0 < sc.rounds.length ∧ I.ok sc.deg ∧
        SumcheckAnswers c s sc I T (fun _ => True) st val ∧ ∀ r i, Model.ev (val r) sc.claim0 = r i := by
  have h0 : ∀ i : Fin sumcheckH.rounds.length, i = ⟨0, by decide⟩ := fun i =>
    Fin.ext (by have := i.isLt; simp [sumcheckH, sumcheck] at this; omega)
  let ans : E → Val := fun a w => if w = 17 then limbsE a else answer a 0 w
  refine ⟨cert, state, sumcheckH, inst, fun _ => 1, fun _ _ _ => 0, fun r => ans (r ⟨0, by decide⟩), by simp [cert],
    rfl, by decide, ⟨by simp, fun r => ⟨by simp [Inst.sum], trivial⟩⟩,
    ⟨rom _ _ fun r => by simp [ans, answer], fun r r' i _ m hm => ?_, fun _ _ _ _ _ _ => pairCR _ _ _, fun r i => ?_,
      fun r i => ?_, fun r _ hT => ?_⟩,
    fun r i => by rw [h0 i]; exact ev_limbsE _ 17 _ (by simp [ans, sumcheckH, sumcheck])⟩
  · obtain rfl := h0 i
    rw [show (sumcheckH.rounds.getD 0 default).time = 1 from rfl,
      show cert.transcripts.getD sumcheckH.transcript default = transcript from rfl, seeds_one] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nu, ans, answer]
  · obtain rfl := h0 i
    exact ev_limbsE _ 16 _ (by simp [ans, answer, sumcheckH, sumcheck, round])
  · obtain rfl := h0 i
    rfl
  · rw [show sumcheckH.claim0 = 17 from rfl, hT 17 (by simp [sumcheckH])]
    simp [inst, Inst.sum, lin]

/-- Answers meeting every premise of `odd_test_sound` but acceptance, at every challenge pair, all `good`, with true
children zero. -/
theorem odd_answers_exist :
    ∃ (c : Cert) (s : State) (oc : OddCert) (L R : ℕ → E) (st : (Fin 2 → E) → ℕ → Fin 4 → K)
      (val : (Fin 2 → E) → Val), oc ∈ c.odds ∧ OddAnswers c s oc L R (fun _ => True) st val := by
  refine ⟨cert, state, odd, fun _ => 0, fun _ => 0, fun _ _ _ => 0, fun r => answer (r 0) (r 1), by simp [cert], ?_⟩
  refine ⟨rom _ _ fun r => by simp [answer], fun r r' m hm => ?_, fun r r' h0 m hm => ?_,
    fun _ _ _ _ => pairCR _ _ _, fun _ _ _ _ _ => pairCR _ _ _, fun r => ⟨?_, ?_⟩,
    fun r _ => ⟨0, by simp [OddCert.m, odd], ?_⟩⟩
  · rw [show odd.lam.time = 1 from rfl, show cert.transcripts.getD odd.transcript default = transcript from rfl,
      seeds_one] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nu, answer]
  · rw [show odd.next.time = 2 from rfl, show cert.transcripts.getD odd.transcript default = transcript from rfl,
      seeds_two] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp [nu, answer, h0]
  · exact ev_limbsE _ 16 _ (by simp [answer])
  · exact ev_limbsE _ 22 _ (by simp [answer])
  · rw [show odd.values.getD 0 0 = 17 from rfl, ev_limbsE _ 17 1 (by simp [answer])]
    simp

/-- Answers meeting every premise of `top_test_sound` but acceptance, at every challenge triple, all `good`, with true
children zero. -/
theorem top_answers_exist :
    ∃ (c : Cert) (s : State) (tc : TopCert) (T : ℕ → ℕ → E) (st : (Fin 3 → E) → ℕ → Fin 4 → K)
      (val : (Fin 3 → E) → Val), tc ∈ c.tops ∧ TopAnswers c s tc T (fun _ => True) st val := by
  refine ⟨cert, state, top, fun _ _ => 0, fun _ _ _ => 0, fun r => answer3 (r 0) (r 1) (r 2), by simp [cert], ?_⟩
  refine ⟨rom _ _ fun r => by simp [answer3, answer], fun r r' m hm => ?_, fun r r' h0 m hm => ?_,
    fun _ _ _ _ => pairCR _ _ _, fun _ _ _ _ _ => pairCR _ _ _, fun r => ⟨?_, ?_, ?_⟩,
    fun r _ => ⟨0, by simp [TopCert.m, top], ?_⟩⟩
  · rw [show top.lam.time = 1 from rfl, show cert.transcripts.getD top.transcript default = transcript from rfl,
      seeds_one] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nu, answer3, answer]
  · rw [show top.low.time = 2 from rfl, show cert.transcripts.getD top.transcript default = transcript from rfl,
      seeds_two] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp [nu, answer3, answer, h0]
  · exact ev_limbsE _ 16 _ (by simp [answer3, answer])
  · exact ev_limbsE _ 22 _ (by simp [answer3, answer])
  · exact ev_limbsE _ 23 _ (by simp [answer3])
  · rw [show top.values.getD 0 0 = 17 from rfl, ev_limbsE _ 17 1 (by simp [answer3, answer])]
    simp

/-- Answers meeting every premise of `whir_test_sound` but acceptance, at every challenge vector, all `good`, for a
batch round (`λ` wire 16, whose squeeze's fourth word is squeezed with it) and a fold round. -/
theorem whir_answers_exist :
    ∃ (c : Cert) (s : State) (wc : WhirCert) (I : Inst E wc.rounds.length)
      (st : (Fin wc.rounds.length → E) → ℕ → Fin 4 → K) (val : (Fin wc.rounds.length → E) → Val),
      wc ∈ c.whirs ∧ 0 < wc.rounds.length ∧ I.ok wc.deg ∧ WhirAnswers c s wc I (fun _ => True) st val ∧
        sibSeeds s (c.transcripts.getD wc.transcript default) 1 [64, 65, 66] = [67] := by
  refine ⟨cert, state, whir, inst2, fun _ _ _ => 0, fun r => answer (r ⟨0, by decide⟩) (r ⟨1, by decide⟩),
    by simp [cert], by decide,
    ⟨by simp, fun _ => ⟨by simp [Inst.sum, lin], by simp, fun _ => ⟨by simp [Inst.sum], trivial⟩⟩⟩, ?_, sibs_one⟩
  refine ⟨rom _ _ fun r => by simp [answer], fun r r' i hj m hm => ?_, fun _ _ _ _ _ _ => pairCR _ _ _, fun r i => ?_,
    fun r i => ?_, fun r _ => ?_⟩
  · match i with
    | ⟨0, _⟩ =>
      rw [show (whir.rounds.getD 0 default).seeds state (cert.transcripts.getD whir.transcript default) =
        seedsBefore state transcript 1 ++ sibSeeds state transcript 1 [64, 65, 66] from rfl, seeds_one,
        sibs_one] at hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;> simp [nu, answer, limbsE]
    | ⟨1, _⟩ =>
      have h0 : r ⟨0, by decide⟩ = r' ⟨0, by decide⟩ := hj ⟨0, by decide⟩ (by simp [Fin.lt_def])
      rw [show (whir.rounds.getD 1 default).seeds state (cert.transcripts.getD whir.transcript default) =
        seedsBefore state transcript 2 from rfl, seeds_two] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp [nu, answer, h0]
  · match i with
    | ⟨0, _⟩ => exact ev_limbsE _ 16 _ (by simp [answer, whir, batchRound])
    | ⟨1, _⟩ => exact ev_limbsE _ 22 _ (by simp [answer, whir, whirRound])
  · match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  · rw [show whir.claim0 = 17 from rfl, ev_limbsE _ 17 1 (by simp [answer])]
    simp [inst2, Inst.sum, lin]

/-- Proof-of-work answers meeting every premise of `pow_test_sound` but acceptance: one trial, whose word is each
outcome. -/
theorem pow_answers_exist :
    ∃ (c : Cert) (pc : PowCert) (wd : ℕ → Fin (2 ^ 64) → Fin (2 ^ 64)) (qOf : Fin (2 ^ 64) → ℕ)
      (st : Fin (2 ^ 64) → ℕ → Fin 4 → K) (val : Fin (2 ^ 64) → Val), pc ∈ c.pows ∧
      (∀ q < 1, ∀ v : Fin (2 ^ 64), 2 ^ 64 * #{ω | wd q ω = v} = Fintype.card (Fin (2 ^ 64))) ∧
      (∀ ω, qOf ω < 1) ∧ (∀ ω, FactsBut c.calls c.relax c.outs pc.compressAt (st ω) (val ω)) ∧
      ∀ ω, toWord (val ω (PowCert.trial c.outs pc) 0) = (wd (qOf ω) ω).val := by
  refine ⟨cert, powCert, fun _ ω => ω, fun _ => 0, fun _ _ _ => 0, fun ω _ _ => ofWord ω.val, by simp [cert],
    fun q _ v => ?_, fun _ => by norm_num, fun _ j hj _ => absurd hj (by simp [cert]), fun ω => toWord_ofWord _ ω.isLt⟩
  rw [show ({ω | ω = v} : Finset (Fin (2 ^ 64))) = {v} by ext; simp, card_singleton, Fintype.card_fin]
  ring

/-- A run on `state`: at oracle `ρ`, the squeezes' outputs (wires 16 and 22) are `ρ`'s answers at their words, the
counter its constant, the input claim one, every other wire zero. -/
noncomputable def runVal (ρ : ℕ → K) : Val := fun w =>
  if w = 1 then limbsOf [outTag, 0, 0, 0] else if w = 16 then fun i => ρ (64 + i) else if w = 22 then fun i => ρ (88 + i)
  else if w = 17 then limbsE 1 else fun _ => 0

/-- The run's challenges: `λ` (wire 16) reads its squeeze's first three words, drawn after block 0; the next (wire 22)
its squeeze's, after block 1. -/
def runOwn : Fin 2 → Fin 3 → ℕ := ![![64, 65, 66], ![88, 89, 90]]

def runTime : Fin 2 → ℕ := ![1, 2]

def runChal : Fin 2 → ℕ := ![16, 22]

theorem run_ans (ρ : ℕ → K) : ∀ p ∈ chalSeeds state transcript, nu (runVal ρ) p.2 = ρ p.2 := by
  rw [chalSeeds_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [nu, runVal]

theorem run_causal (ρ ρ' : ℕ → K) (k : ℕ) (h : ∀ p ∈ chalSeeds state transcript, p.1 ≤ k → ρ p.2 = ρ' p.2) :
    ∀ m ∈ seedsBefore state transcript k, nu (runVal ρ) m = nu (runVal ρ') m := by
  intro m hm
  simp only [seedsBefore, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hm
  rcases hm with (hm | ⟨p, ⟨hp, hk⟩, rfl⟩) | hm
  · have hsub : m ∈ absorbed state transcript.blocks := by
      simp only [absorbed, List.mem_flatMap] at hm ⊢
      obtain ⟨b, hb, hm⟩ := hm
      exact ⟨b, List.mem_of_mem_take hb, hm⟩
    have hl : absorbed state transcript.blocks =
        [32, 36, 40, 44, 48, 52, 56, 60, 32, 36, 40, 44, 48, 52, 56, 60] := by
      simp [absorbed, wordsOf, transcript, state, row, limb, List.range_succ]
    rw [hl] at hsub
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
    rcases hsub with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [nu, runVal]
  · rw [run_ans ρ p hp, run_ans ρ' p hp, h p hp hk]
  · split at hm
    · simp [statementNodes, state] at hm
    · simp at hm

/-- A prover's run meeting every premise of the answer theorems (`Run.sumcheckAnswers`, ...) but acceptance: a `Run`
with no collision event (every row a squeeze) whose two challenges each read three words of their squeeze as an
element of `E`, drawn at increasing times, each word a challenge seed only one step after its challenge's time, no
word shared; and its input claim false. -/
theorem run_exists :
    ∃ (c : Cert) (s : State) (st : (ℕ → K) → ℕ → Fin 4 → K) (val : (ℕ → K) → Val) (own : Fin 2 → Fin 3 → ℕ)
      (time : Fin 2 → ℕ) (chal : Fin 2 → ℕ), Run c s 0 (fun _ => False) st val ∧
      OwnAt s (c.transcripts.getD 0 default) own time ∧
      OwnInj own ∧ (∀ i j, i < j → time i < time j) ∧
      (∀ ρ i, Model.ev (val ρ) (chal i) =
        toE (nu (val ρ) (own i 0)) (nu (val ρ) (own i 1)) (nu (val ρ) (own i 2))) ∧
      ∀ ρ, Model.ev (val ρ) sumcheck.claim0 ≠ inst.sum := by
  refine ⟨cert, state, fun _ _ _ => 0, runVal, runOwn, runTime, runChal,
    ⟨rom _ _ fun ρ => by simp [runVal], run_ans, run_causal, fun _ _ _ _ _ _ _ _ => pairCR _ _ _⟩, fun i k => ?_, ?_,
    fun i j hij => ?_, fun ρ i => ?_, fun ρ => ?_⟩
  · show (_, _) ∈ chalSeeds state transcript ∧ ∀ p ∈ chalSeeds state transcript, _
    rw [chalSeeds_eq]
    fin_cases i <;> fin_cases k <;> simp [runOwn, runTime]
  · rintro ⟨i, k⟩ ⟨j, l⟩ h
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;> simp_all [runOwn]
  · fin_cases i <;> fin_cases j <;> simp_all [runTime]
  · fin_cases i <;> simp [Model.ev, runVal, runChal, runOwn, nu]
  · rw [show sumcheck.claim0 = 17 from rfl, ev_limbsE _ 17 1 (by simp [runVal])]
    simp [inst, Inst.sum, lin]

/-- A replay whose call 0 outputs `λ`'s squeeze wire 16 and call 1 the next challenge's wire 22. -/
def chalOs : Array (List ℕ) := #[[16], [22]]

/-- `λ` reading wire 16's first three words, drawn after block 0; the next challenge wire 22's, after block 1. -/
def lamCC : ChalCert := ⟨16, 0, [(0, 0, 0), (0, 1, 0), (0, 2, 0)], 1⟩

def nextCC : ChalCert := ⟨22, 0, [(1, 0, 1), (1, 1, 1), (1, 2, 1)], 2⟩

/-- The verdict's `chalsOk` on `state`'s transcript: `λ` then the next challenge pass, strictly; the same challenge
twice (a shared word), `λ` drawn a block later than its squeeze (its words not seeds one step after its time), the
two out of order, and a word at a fifth place of its digest each fail. -/
theorem chalsOk_mutations :
    chalsOk state chalOs transcript true [lamCC, nextCC] = true ∧
      chalsOk state chalOs transcript false [lamCC, lamCC] = false ∧
      chalsOk state chalOs transcript false [{ lamCC with time := 2 }] = false ∧
      chalsOk state chalOs transcript false [nextCC, lamCC] = false ∧
      chalsOk state chalOs transcript false [{ lamCC with words := [(0, 0, 0), (0, 1, 0), (0, 4, 0)] }] = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := { decide := true }) [chalsOk, ChalCert.ownOk, ChalCert.own, chalSeeds_eq, lamCC, nextCC, chalOs,
      outAt, limb]

end LeanVMCircuits.Rec.Bind.RomExample
