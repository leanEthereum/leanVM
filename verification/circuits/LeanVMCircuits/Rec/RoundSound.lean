module

public import LeanVMCircuits.Rec.UnionCover
public import LeanVMCircuits.Rec.Rounds

@[expose] public section

/-!
Sumcheck's soundness on the circuit's tests.

An accepted certificate names sumchecks (`Cert.sumchecksOk`): each round's calls (`RoundCert.ok`), the test of its last
claim, each round's challenge drawn by a squeeze of its transcript after its first `time` blocks (`RoundCert.chalOk`),
and what the round's prover sends, its eq weight and the input claim bound by those blocks (`SumcheckCert.boundOk`).

`sumcheck_test_sound` applies `Sumcheck.sumcheck_sound` to such a test. The honest instance is an explicit interface
(`Sumcheck.Inst`, the committed witness's truths: its round polynomials, each round's eq weight, the final value at
each challenge vector). The prover answers each challenge vector `r` of `S^n` with an assignment holding every
constraint but the tests, whose challenges are `r`, and whose transcript's blocks before round `i`'s challenge read
only the challenges before it (the random oracle's view of a prover that may adapt to every challenge so far). If the
input claim is not the instance's sum, the challenge vectors at which the test holds with the test's other side the
instance's final value are at most `n · d · |S|^(n-1)`. Where the other side is not the final value, the claims the
reduction outputs (the next layer's values, or an opening) are false, which the next reduction's test is for.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Sumcheck Polynomial

/-- Answers indexed by `ι` in the random-oracle view of transcript `T`: each holds every constraint and every
replayed call but the tests and `T`'s own compressions (`HoldsP` dropping `dropOf`, `Facts` dropping every squeeze),
whose outputs are the oracle's answers; and each union product is a function of its inputs. Collision resistance is
asked separately, of two answers sharing the transcript's prefix before a time (`PairCR`). -/
structure RomAnswers (c : Cert) (s : State) (T : ℕ) {ι : Type} (st : ι → ℕ → Fin 4 → K) (val : ι → Val) :
    Prop where
  holds : ∀ r, HoldsP (st r) s c.test (dropOf s (c.transcripts.getD T default)) (val r)
  facts : ∀ r, Facts c.calls c.relax c.outs (st r) (val r)
  unions : ∀ r r', UnionsValid c.claims (val r) (val r')

/-- Assignments of an accepted circuit holding every constraint but the tests, the squeezes' compressions included,
pairwise free of collisions, are such answers for every transcript. -/
theorem RomAnswers.of_holds {c : Cert} {s : State} (h : c.accepts s = true) (T : ℕ) {ι : Type}
    {st : ι → ℕ → Fin 4 → K} {val : ι → Val} (hv : ∀ r, Holds (st r) s c.test (val r))
    (hcr : ∀ r r', HashCR s (val r) (val r')) : RomAnswers c s T st val :=
  have hun := (Cert.accepts_parts h).2.2.1
  ⟨fun r => (hv r).toP _, fun r => (facts_of_holds hun (hv r)).1,
    fun r r' => unionsValid c s hun (hv r) (hv r') (hcr r r')⟩

/-- The hint nodes of transcript `T`'s sumchecks: claims no transcript binds (`SumcheckCert.hints`), seeds where they
are their true values. -/
def Cert.hintNodes (c : Cert) (T : ℕ) : List ℕ :=
  (c.sumchecks.toList.filter fun sc => sc.transcript == T).flatMap fun sc => sc.hints.flatMap limbs3

/-- The nodes transcript `T`'s random-oracle rules bind from seeds `X`: the closure of `X` and its sumchecks'
hints. -/
def Cert.liveOn (c : Cert) (T : ℕ) (X : List ℕ) (n : ℕ) : Prop :=
  Closure (c.transcripts.getD T default).rulesRO (X ++ c.hintNodes T) n

/-- Collision resistance between two answers on the rows transcript `T` binds from seeds `X` (`Cert.liveOn`): what the
rules firing from `X` need. A prover's queries before the squeezes `X` reads decide those rows, so two answers sharing
that prefix ask it of the prefix's queries (`Bind.Run.cr_of_extract`). -/
structure PairCR (c : Cert) (s : State) (T : ℕ) (X : List ℕ) (val val' : Val) : Prop where
  cr : HashCRP s (dropOf s (c.transcripts.getD T default)) (c.liveOn T X) val val'
  win : WindowCRP s (dropOf s (c.transcripts.getD T default)) (c.liveOn T X) val val'

/-- `PairCR` on the seeds before time `k`. -/
abbrev PairCRAt (c : Cert) (s : State) (T k : ℕ) (val val' : Val) : Prop :=
  PairCR c s T (seedsBefore s (c.transcripts.getD T default) k) val val'

/-- Assignments with no collision at all give `PairCR` on every seeds. -/
theorem PairCR.of_full {c : Cert} {s : State} {T : ℕ} {X : List ℕ} {val val' : Val} (hcr : HashCR s val val')
    (hw : WindowCR s val val') : PairCR c s T X val val' :=
  ⟨hcr.toP _ _, hw.toP _ _⟩

/-- `PairCR` on fewer live nodes. -/
theorem PairCR.anti {c : Cert} {s : State} {T : ℕ} {X Y : List ℕ} {val val' : Val}
    (hsub : ∀ n, c.liveOn T X n → c.liveOn T Y n) (h : PairCR c s T Y val val') : PairCR c s T X val val' := by
  have hl : ∀ row, RowLive (c.liveOn T X) row → RowLive (c.liveOn T Y) row :=
    fun row ⟨n, hn, hx⟩ => ⟨n, hn, hsub n hx⟩
  exact ⟨fun row hr row' hr' hd hd' hl1 hl2 => h.cr row hr row' hr' hd hd' (hl row hl1) (hl row' hl2),
    fun ra ha rb hb hda hdb hl1 hl2 => h.win ra ha rb hb hda hdb (hl ra hl1) (hl rb hl2)⟩

/-- Fewer seeds bind fewer nodes. -/
theorem Cert.liveOn_mono (c : Cert) (T : ℕ) {X Y : List ℕ} (h : ∀ m ∈ X, m ∈ Y) (n : ℕ) :
    c.liveOn T X n → c.liveOn T Y n :=
  fun hn => hn.mono fun m hm => by
    rw [List.mem_append] at hm ⊢
    exact hm.imp (h m) id

theorem Cert.marksRO_getD (c : Cert) (s : State) {k : ℕ} (hk : k < (c.marksRO s).length) :
    (c.marksRO s).getD k default = (c.transcripts.getD k default, c.timesRO s (c.transcripts.getD k default)) := by
  have hk' : k < c.transcripts.length := by simpa [Cert.marksRO] using hk
  simp [Cert.marksRO, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

/-- A wire in the closure of `seeds` under a transcript's random-oracle rules is a function of those seeds, between
two answers collision-free on the rows bound from seeds `X` binding at least as much. -/
theorem ro_agree {c : Cert} {s : State} (h : c.accepts s = true) {T : ℕ} (hT : T < (c.marksRO s).length)
    {ι : Type} {st : ι → ℕ → Fin 4 → K} {val : ι → Val} (ha : RomAnswers c s T st val) (r r' : ι) {seeds X : List ℕ}
    {w : ℕ} (hcr : PairCR c s T X (val r) (val r'))
    (hk : ∀ n, Closure (c.transcripts.getD T default).rulesRO seeds n → c.liveOn T X n)
    (hb : ∀ n ∈ limbs3 w, Closure (c.transcripts.getD T default).rulesRO seeds n)
    (hs : ∀ m ∈ seeds, nu (val r) m = nu (val r') m) :
    Model.ev (val r) w = Model.ev (val r') w := by
  have hall := (Cert.accepts_rounds h).2.2.2.1
  have hT' : T < c.transcripts.length := by simpa [Cert.marksRO] using hT
  have hr : rulesOk s c.test c.claims (dropOf s (c.transcripts.getD T default))
      (c.transcripts.getD T default).rulesRO = true := by
    rw [List.all_eq_true] at hall
    exact hall _ (by rw [List.getD_eq_getElem _ _ hT']; exact List.getElem_mem hT')
  exact ev_eq_of_limbs3 fun n hn => closure_agree_on (fun i hi hp => rules_valid hr (ha.holds r) (ha.holds r')
    hcr.cr hcr.win (ha.unions r r') i hi fun q hq => hk q (hp q hq)) hs (hb n hn)

/-- A wire whose limbs a transcript binds by `time` in the random-oracle view is a function of what its first `time`
blocks absorb and the challenges drawn before `time`, between two answers collision-free on the rows bound by
`time`. -/
theorem bound_agree {c : Cert} {s : State} (h : c.accepts s = true) {T : ℕ} (hT : T < (c.marksRO s).length)
    {ι : Type} {st : ι → ℕ → Fin 4 → K} {val : ι → Val} (ha : RomAnswers c s T st val) (r r' : ι) {time w : ℕ}
    (hcr : PairCRAt c s T time (val r) (val r'))
    (hb : ∀ n ∈ limbs3 w, ∃ k, ((c.marksRO s).getD T default).2.getD n none = some k ∧ k ≤ time)
    (hs : ∀ m ∈ seedsBefore s (c.transcripts.getD T default) time, nu (val r) m = nu (val r') m) :
    Model.ev (val r) w = Model.ev (val r') w := by
  refine ro_agree h hT ha r r' hcr (fun n hn => hn.mono fun m hm => List.mem_append_left _ hm) (fun n hn => ?_) hs
  obtain ⟨k, hk, hle⟩ := hb n hn
  rw [Cert.marksRO_getD c s hT] at hk
  exact (Cert.timesRO_sound c s _ hk).mono (seedsBefore_mono hle)

theorem boundBy_wires {m : Array (Option ℕ)} {ws : List ℕ} {time : ℕ} (h : boundBy m ws time = true) :
    ∀ w ∈ ws, ∀ n ∈ limbs3 w, ∃ k, m.getD n none = some k ∧ k ≤ time := by
  intro w hw n hn
  simp only [boundBy, List.all_eq_true, List.mem_flatMap] at h
  have := h n ⟨w, hw, hn⟩
  split at this
  · rename_i k hk
    exact ⟨k, hk, of_decide_eq_true this⟩
  · simp at this

theorem boundOk_wires {m : Array (Option ℕ)} {sc : SumcheckCert} {i : ℕ} (h : sc.boundOk m i = true) :
    ∀ w ∈ (sc.rounds.getD i default).sent ++ (sc.rounds.getD i default).weight.toList ++
        (if i = 0 ∧ sc.hints = [] then [sc.claim0] else []),
      ∀ n ∈ limbs3 w, ∃ k, m.getD n none = some k ∧ k ≤ (sc.rounds.getD i default).time := by
  intro w hw n hn
  simp only [SumcheckCert.boundOk, List.all_eq_true, List.mem_flatMap] at h
  have := h n ⟨w, hw, hn⟩
  split at this
  · rename_i k hk
    exact ⟨k, hk, of_decide_eq_true this⟩
  · simp at this

/-- A coefficient is one the prover sends or the fixed one. -/
theorem mem_coeffs {rc : RoundCert} {w : ℕ} (hw : w ∈ rc.coeffs) (hlen : rc.fixed < rc.coeffs.length) :
    w ∈ rc.sent ∨ w = rc.coeffs.getD rc.fixed 0 := by
  rw [← List.take_append_drop rc.fixed rc.coeffs, List.drop_eq_getElem_cons hlen] at hw
  simp only [List.mem_append, List.mem_cons] at hw
  rw [RoundCert.sent, List.eraseIdx_eq_take_drop_succ]
  rcases hw with hw | hw | hw
  · exact Or.inl (List.mem_append_left _ hw)
  · right
    rw [hw, List.getD_eq_getElem _ _ hlen]
  · exact Or.inl (List.mem_append_right _ hw)

theorem mem_tail {rc : RoundCert} {w : ℕ} (hw : w ∈ rc.coeffs.drop (rc.fixed + 1)) : w ∈ rc.sent := by
  rw [RoundCert.sent, List.eraseIdx_eq_take_drop_succ]
  exact List.mem_append_right _ hw

/-- Two assignments where every replayed call holds, agreeing on a round's claim, weight and what its prover sends,
agree on its coefficients. -/
theorem coeffs_agree {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st st' : ℕ → Fin 4 → K}
    {val val' : Val} (hF : Facts cs rl os st val) (hF' : Facts cs rl os st' val') {rc : RoundCert} {d claim : ℕ}
    (hok : rc.ok os cs rl d claim = true) (hcl : Model.ev val claim = Model.ev val' claim)
    (hw : ∀ e ∈ rc.weight.toList, Model.ev val e = Model.ev val' e)
    (hs : ∀ w ∈ rc.sent, Model.ev val w = Model.ev val' w) :
    rc.coeffs.map (Model.ev val) = rc.coeffs.map (Model.ev val') := by
  simp only [RoundCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hlen, hge⟩, htl⟩, hhl⟩, hfx⟩, hcalls⟩ := hok
  simp only [RoundCert.calls, callsOk_append, Bool.and_eq_true] at hcalls
  obtain ⟨⟨hhead, hfold⟩, -⟩ := hcalls
  obtain ⟨hz, hrest⟩ := callsOk_cons hhead
  obtain ⟨-, hfc⟩ := callsOk_cons hrest
  have hfix : rc.fixed < rc.coeffs.length := by
    unfold RoundCert.fixed; split <;> omega
  -- The tail is a sum of sent coefficients, from a zero.
  have htail : Model.ev val (rc.tail os) = Model.ev val' (rc.tail os) := by
    have hz' : ∀ {st : ℕ → Fin 4 → K} {val : Val}, Facts cs rl os st val → Model.ev val (o os rc.tailZero) = 0 :=
      fun hF => holds_of_mem hF hz (List.mem_singleton_self _)
    rw [RoundCert.tail, fold_sem hF _ _ _ (by simp; omega) hfold, fold_sem hF' _ _ _ (by simp; omega) hfold,
      hz' hF, hz' hF', List.map_congr_left fun w hw => hs w (mem_tail hw)]
  have hfixed : Model.ev val (rc.coeffs.getD rc.fixed 0) = Model.ev val' (rc.coeffs.getD rc.fixed 0) := by
    have h1 : (rc.fixedCall os claim).Holds st val (os.getD rc.fixedAt []) :=
      holds_of_mem hF hfc (List.mem_singleton_self _)
    have h2 : (rc.fixedCall os claim).Holds st' val' (os.getD rc.fixedAt []) :=
      holds_of_mem hF' hfc (List.mem_singleton_self _)
    rw [← hfx]
    unfold RoundCert.fixedCall at h1 h2
    split at h1 <;> rename_i e he <;> simp only [he, Call.Holds, getD_o] at h1 h2
    · rw [h1, h2, htail, hcl, hw e (by simp [he])]
    · rw [h1, h2, htail, hcl]
  exact List.map_congr_left fun w hw => (mem_coeffs hw hfix).elim (hs w) fun he => he ▸ hfixed

/-- What `sumcheck_test_sound` asks of the prover's answers to a certified sumcheck `sc`'s challenge vectors `r`:
they are answers in the random-oracle view of its transcript (`RomAnswers`); two answers whose challenges before round
`i` agree agree on the seeds before round `i`'s time (what the blocks before its challenge absorb and the challenges
drawn before them, not round `i`'s own) and, both `good` (off their executions' collision events), are
collision-free on the rows bound by that time (`PairCR`); round `i`'s challenge is `r i`; the eq weights are the
honest instance's; and where the hints the input claim reads (`SumcheckCert.hints`: hinted fixed-column evaluations,
claims deferred to the reduction, which no transcript binds) are their true values `T`, the input claim is not the
instance's sum. `sumcheck_answers_exist` exhibits such answers. -/
structure SumcheckAnswers (c : Cert) (s : State) (sc : SumcheckCert) (I : Inst E sc.rounds.length) (T : ℕ → E)
    (good : (Fin sc.rounds.length → E) → Prop) (st : (Fin sc.rounds.length → E) → ℕ → Fin 4 → K)
    (val : (Fin sc.rounds.length → E) → Val) : Prop where
  rom : RomAnswers c s sc.transcript st val
  seed : ∀ r r' (i : Fin sc.rounds.length), (∀ j < i, r j = r' j) →
    ∀ m ∈ seedsBefore s (c.transcripts.getD sc.transcript default) (sc.rounds.getD i default).time,
      nu (val r) m = nu (val r') m
  cr : ∀ r r' (i : Fin sc.rounds.length), good r → good r' → (∀ j < i, r j = r' j) →
    PairCRAt c s sc.transcript (sc.rounds.getD i default).time (val r) (val r')
  chal : ∀ r (i : Fin sc.rounds.length), Model.ev (val r) (sc.rounds.getD i default).chal = r i
  weight : ∀ r (i : Fin sc.rounds.length), (sc.rounds.getD i default).weight.map (Model.ev (val r)) = I.weight r i
  false_claim : ∀ r, good r → (∀ w ∈ sc.hints, Model.ev (val r) w = T w) → Model.ev (val r) sc.claim0 ≠ I.sum

theorem mem_hintNodes {c : Cert} {sc : SumcheckCert} (hsc : sc ∈ c.sumchecks) {m : ℕ}
    (hm : m ∈ sc.hints.flatMap limbs3) : m ∈ c.hintNodes sc.transcript :=
  List.mem_flatMap.mpr ⟨sc, List.mem_filter.mpr ⟨by simpa using hsc, by simp⟩, hm⟩

/-- A certified sumcheck's input claim is bound before its first challenge, with its hints as seeds: two answers in
the random-oracle view agreeing on the seeds before the first challenge, collision-free on the rows bound by then,
whose hints are their true values `T`, agree on it. -/
theorem sumcheck_claim_agree (c : Cert) (s : State) (h : c.accepts s = true) {sc : SumcheckCert}
    (hsc : sc ∈ c.sumchecks) {ι : Type} {st : ι → ℕ → Fin 4 → K} {val : ι → Val}
    (hrom : RomAnswers c s sc.transcript st val) (T : ℕ → E) (r r' : ι)
    (hcr : PairCRAt c s sc.transcript (sc.rounds.getD 0 default).time (val r) (val r'))
    (hs : ∀ m ∈ seedsBefore s (c.transcripts.getD sc.transcript default) (sc.rounds.getD 0 default).time,
      nu (val r) m = nu (val r') m)
    (hr : ∀ w ∈ sc.hints, Model.ev (val r) w = T w) (hr' : ∀ w ∈ sc.hints, Model.ev (val r') w = T w) :
    Model.ev (val r) sc.claim0 = Model.ev (val r') sc.claim0 := by
  have hall := (Cert.accepts_rounds h).1
  simp only [Cert.sumchecksOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hall
  obtain ⟨⟨⟨⟨⟨htr, hok⟩, -⟩, -⟩, hrounds⟩, hhint⟩ := hall sc hsc
  simp only [SumcheckCert.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  have hpos := hok.1.1
  by_cases hh : sc.hints = []
  · exact bound_agree h htr hrom r r' hcr (boundOk_wires (hrounds 0 hpos).2 _ (by simp [hh])) hs
  · have hb : boundBy (c.timesX s (c.transcripts.getD sc.transcript default) sc.hintSeeds sc.hintFirings)
        [sc.claim0] (sc.rounds.getD 0 default).time = true := by
      rcases hhint with hh' | hb
      · exact absurd (List.isEmpty_iff.mp hh') hh
      · rwa [Cert.marksRO_getD c s htr] at hb
    refine ro_agree h htr hrom r r' hcr
      (seeds := seedsBefore s (c.transcripts.getD sc.transcript default) (sc.rounds.getD 0 default).time ++
        sc.hints.flatMap limbs3) (fun n hn => hn.mono fun m hm => ?_) (fun n hn => ?_) fun m hm => ?_
    · rw [List.mem_append] at hm ⊢
      exact hm.imp id (mem_hintNodes hsc)
    · obtain ⟨k, hk, hle⟩ := boundBy_wires hb _ (List.mem_singleton_self _) n hn
      refine (Cert.timesX_sound c s _ _ _ hk).mono fun m hm => ?_
      rw [List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl (seedsBefore_mono hle m hm)
      · simp only [SumcheckCert.hintSeeds, seedsBy, List.mem_map, List.mem_filter] at hm
        obtain ⟨p, ⟨⟨x, hx, rfl⟩, -⟩, rfl⟩ := hm
        exact Or.inr hx
    · rw [List.mem_append] at hm
      rcases hm with hm | hm
      · exact hs m hm
      · obtain ⟨w, hw, hmw⟩ := List.mem_flatMap.mp hm
        exact limbs3_of_ev ((hr w hw).trans (hr' w hw).symm) m hmw

open Classical Finset in
/-- Sumcheck's soundness on a certified test. Take an accepted circuit and a sumcheck it names (`sc`, `n` rounds of
degree `d`), the honest instance `I` of degree `d`, the true values `T` of the hints its input claim reads, and the
prover's answers to the challenge vectors (`SumcheckAnswers`: in the random-oracle view, each round's challenge `r i`,
what is absorbed before it reading only the challenges before it, from an input claim false where the hints are
true). The challenge vectors of `S^n` at which the answer is `good`, the hints are their true values, the test holds
and its other side, plus the residual's terms when the test is of a residual, is the instance's final value are at
most `n · d · |S|^(n-1)`. Where a hint is not its true value, the claim the reduction takes on it is false. -/
theorem sumcheck_test_sound (c : Cert) (s : State) (h : c.accepts s = true) {sc : SumcheckCert}
    (hsc : sc ∈ c.sumchecks) (S : Finset E) (I : Inst E sc.rounds.length) (hI : I.ok sc.deg) (T : ℕ → E)
    (good : (Fin sc.rounds.length → E) → Prop)
    (st : (Fin sc.rounds.length → E) → ℕ → Fin 4 → K) (val : (Fin sc.rounds.length → E) → Val)
    (ha : SumcheckAnswers c s sc I T good st val) :
    #{r ∈ Fintype.piFinset (fun _ : Fin sc.rounds.length => S) | good r ∧
        (∀ w ∈ sc.hints, Model.ev (val r) w = T w) ∧ (∀ a b, s.unions[sc.test]? = some (a, b) → val r a = val r b) ∧
          Model.ev (val r) sc.final + (sc.resid.map fun t => Model.ev (val r) t.1 * Model.ev (val r) t.2.1).sum =
            I.final r} ≤
      sc.rounds.length * sc.deg * #S ^ (sc.rounds.length - 1) := by
  have hall := (Cert.accepts_rounds h).1
  simp only [Cert.sumchecksOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hall
  obtain ⟨⟨⟨⟨⟨htr, hok⟩, -⟩, hpair⟩, hrounds⟩, hhint⟩ := hall sc hsc
  simp only [SumcheckCert.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨hpos, hok⟩, hres⟩ := hok
  have hF := ha.rom.facts
  have hseed := ha.seed
  have hchal := ha.chal
  have hw := ha.weight
  have hbound : ∀ i < sc.rounds.length, sc.boundOk ((c.marksRO s).getD sc.transcript default).2 i = true :=
    fun i hi => (hrounds i hi).2
  -- Round `i`'s polynomial and claims along `r`.
  set g : (Fin sc.rounds.length → E) → Fin sc.rounds.length → E[X] := fun r i => polyOf ((sc.rounds.getD i default).coeffs.map (Model.ev (val r)))
  set cl : (Fin sc.rounds.length → E) → Fin (sc.rounds.length + 1) → E := fun r k => Model.ev (val r) (sc.claimAt c.outs k)
  have hsem : ∀ r (i : Fin sc.rounds.length), (g r i).natDegree ≤ sc.deg ∧
      lin (I.weight r i) (g r i) = cl r i.castSucc ∧ cl r i.succ = (g r i).eval (r i) := by
    intro r i
    obtain ⟨h1, h2, h3⟩ := sumRound_sem (hF r) (hok i i.isLt)
    refine ⟨h1, by rw [← hw r i]; exact h2, ?_⟩
    simp only [cl, Fin.val_succ, SumcheckCert.claimAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [h3, hchal r i]
  -- The good challenge vectors at which the hints are their true values.
  set A : Set (Fin sc.rounds.length → E) := {r | good r ∧ ∀ w ∈ sc.hints, Model.ev (val r) w = T w}
  -- The input claim is one value among them: bound by the transcript, or with the hints as seeds.
  have hin : ∀ r ∈ A, ∀ r' ∈ A, cl r ⟨0, by omega⟩ = cl r' ⟨0, by omega⟩ := by
    intro r hr r' hr'
    simp only [cl, SumcheckCert.claimAt, if_true]
    exact sumcheck_claim_agree c s h hsc ha.rom T r r'
      (ha.cr r r' ⟨0, hpos⟩ hr.1 hr'.1 fun j hj => absurd hj (by simp [Fin.lt_def]))
      (hseed r r' ⟨0, hpos⟩ fun j hj => absurd hj (by simp [Fin.lt_def])) hr.2 hr'.2
  -- What a round's prover sends, its weight and its claim agree between such answers agreeing on the challenges
  -- before it.
  have hagree : ∀ i, (hi : i < sc.rounds.length) → ∀ r ∈ A, ∀ r' ∈ A,
      (∀ j : Fin sc.rounds.length, j.val < i → r j = r' j) →
      cl r ⟨i, by omega⟩ = cl r' ⟨i, by omega⟩ ∧ g r ⟨i, hi⟩ = g r' ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi r hr r' hr' _
      have hs := hseed r r' ⟨0, hi⟩ fun j hj => absurd hj (by simp [Fin.lt_def])
      have hc := ha.cr r r' ⟨0, hi⟩ hr.1 hr'.1 fun j hj => absurd hj (by simp [Fin.lt_def])
      have hb := boundOk_wires (hbound 0 hi)
      have h0 := hin r hr r' hr'
      refine ⟨h0, congrArg polyOf (coeffs_agree (hF r) (hF r') (hok 0 hi) h0 (fun e he => ?_) fun w hw => ?_)⟩
      · exact bound_agree h htr ha.rom r r' hc (hb _ (List.mem_append_left _ (List.mem_append_right _ he))) hs
      · exact bound_agree h htr ha.rom r r' hc (hb _ (List.mem_append_left _ (List.mem_append_left _ hw))) hs
    | succ i ih =>
      intro hi r hr r' hr' hrr
      have hs := hseed r r' ⟨i + 1, hi⟩ fun j hj => hrr j hj
      have hc := ha.cr r r' ⟨i + 1, hi⟩ hr.1 hr'.1 fun j hj => hrr j hj
      have hb := boundOk_wires (hbound (i + 1) hi)
      obtain ⟨-, hg⟩ := ih (by omega) r hr r' hr' fun j hj => hrr j (by omega)
      have hcl : cl r ⟨i + 1, by omega⟩ = cl r' ⟨i + 1, by omega⟩ := by
        have e1 := (hsem r ⟨i, by omega⟩).2.2
        have e2 := (hsem r' ⟨i, by omega⟩).2.2
        simp only [Fin.succ_mk] at e1 e2
        rw [e1, e2, hg, hrr ⟨i, by omega⟩ (by simp)]
      refine ⟨hcl, congrArg polyOf (coeffs_agree (hF r) (hF r') (hok (i + 1) hi) hcl (fun e he => ?_)
        fun w hw => ?_)⟩
      · exact bound_agree h htr ha.rom r r' hc (hb _ (List.mem_append_left _ (List.mem_append_right _ he))) hs
      · exact bound_agree h htr ha.rom r r' hc (hb _ (List.mem_append_left _ (List.mem_append_left _ hw))) hs
  have hpre : PrefixDepOn A g := fun r hr r' hr' i hrr => (hagree i i.isLt r hr r' hr' fun j hj => hrr j hj).2
  by_cases hex : ∃ r₀, r₀ ∈ A
  swap
  · simp only [not_exists] at hex
    exact le_trans (le_of_eq (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun r _ hr => hex r ⟨hr.1, hr.2.1⟩)))
      (Nat.zero_le _)
  obtain ⟨r₀, hr₀⟩ := hex
  refine le_trans (card_le_card fun r hr => ?_)
    (sumcheck_sound_on S sc.deg I hI A g hpre (fun r i => (hsem r i).1) cl (cl r₀ 0)
      (ha.false_claim r₀ hr₀.1 hr₀.2))
  simp only [mem_filter] at hr ⊢
  obtain ⟨hS, hg, hA, htest, hfin⟩ := hr
  refine ⟨hS, ⟨hg, hA⟩, hin r ⟨hg, hA⟩ r₀ hr₀, fun i => (hsem r i).2.1, fun i => (hsem r i).2.2, ?_⟩
  have hlast : cl r (Fin.last sc.rounds.length) = Model.ev (val r) sc.final +
      (sc.resid.map fun t => Model.ev (val r) t.1 * Model.ev (val r) t.2.1).sum := by
    have hside : Model.ev (val r) (sc.side c.outs) = Model.ev (val r) sc.final := by
      rcases hpair with hp | hp
      · simp only [Model.ev, htest _ _ hp]
      · simp only [Model.ev, ← htest _ _ hp]
    rw [SumcheckCert.side, resid_sem (hF r) _ _ hres] at hside
    simp only [cl, Fin.val_last]
    linear_combination hside - (sc.resid.map fun t => Model.ev (val r) t.1 * Model.ev (val r) t.2.1).sum * two_E
  rw [hlast, hfin]

/-! Proof of work. -/

open Classical Finset in
/-- The words below `2^m`, `m ≤ 64`, are `2^m`. -/
theorem card_low_words {m : ℕ} (hm : m ≤ 64) : #{v : Fin (2 ^ 64) | v.val < 2 ^ m} = 2 ^ m := by
  have hlt : ∀ x < 2 ^ m, x < 2 ^ 64 := fun x hx => lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hm)
  have he : ({v : Fin (2 ^ 64) | v.val < 2 ^ m} : Finset (Fin (2 ^ 64))).map Fin.valEmbedding = range (2 ^ m) := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, hlt x hx⟩, hx, rfl⟩
  rw [← card_map, he, card_range]

open Classical Finset in
/-- Proof of work's grinding bound. A prover makes `Q` trials, trial `q`'s first output word `wd q` uniform on 64-bit
words over the outcomes `Ω`, and picks one, `qOf ω`. The outcomes at which the picked trial's word has its top `b` bits
zero are at most a `Q / 2^b` fraction: each passing proof costs about `2^b` compressions. -/
theorem grinding_bound (b : ℕ) (hb : b ≤ 64) (Q : ℕ) {Ω : Type} [Fintype Ω] (wd : ℕ → Ω → Fin (2 ^ 64))
    (hwd : ∀ q < Q, ∀ v : Fin (2 ^ 64), 2 ^ 64 * #{ω | wd q ω = v} = Fintype.card Ω) (qOf : Ω → ℕ)
    (hq : ∀ ω, qOf ω < Q) :
    (#{ω | (wd (qOf ω) ω).val < 2 ^ (64 - b)} : ℚ≥0) / Fintype.card Ω ≤ Q / 2 ^ b := by
  set B : ℕ → Finset Ω := fun q => {ω | (wd q ω).val < 2 ^ (64 - b)}
  -- One trial passes at a `1 / 2^b` fraction of the outcomes.
  have hone : ∀ q < Q, 2 ^ b * #(B q) = Fintype.card Ω := by
    intro q hqQ
    have hsplit : B q = ({v : Fin (2 ^ 64) | v.val < 2 ^ (64 - b)} : Finset (Fin (2 ^ 64))).biUnion
        fun v => {ω | wd q ω = v} := by
      ext ω
      simp [B]
    have hdisj : (({v : Fin (2 ^ 64) | v.val < 2 ^ (64 - b)} : Finset (Fin (2 ^ 64))) : Set (Fin (2 ^ 64))).PairwiseDisjoint
        fun v => ({ω | wd q ω = v} : Finset Ω) := by
      intro v _ v' _ hvv'
      simp only [Function.onFun]
      rw [disjoint_left]
      intro ω h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      exact hvv' (h1.symm.trans h2)
    have hsum : 2 ^ 64 * #(B q) = 2 ^ (64 - b) * Fintype.card Ω := by
      rw [hsplit, card_biUnion hdisj, mul_sum, sum_congr rfl fun v _ => hwd q hqQ v, sum_const, smul_eq_mul,
        card_low_words (by omega)]
    have h64 : (2 : ℕ) ^ 64 = 2 ^ (64 - b) * 2 ^ b := by rw [← pow_add]; congr 1; omega
    rw [h64, mul_assoc] at hsum
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hsum
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
  · rw [h0]; simp
  have hsub : ({ω | (wd (qOf ω) ω).val < 2 ^ (64 - b)} : Finset Ω) ⊆ (range Q).biUnion B := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    exact mem_biUnion.mpr ⟨qOf ω, mem_range.mpr (hq ω), by simp [B, hω]⟩
  have hc : (Fintype.card Ω : ℚ≥0) ≠ 0 := by exact_mod_cast h0.ne'
  calc (#{ω | (wd (qOf ω) ω).val < 2 ^ (64 - b)} : ℚ≥0) / Fintype.card Ω
      ≤ (∑ q ∈ range Q, (#(B q) : ℚ≥0)) / Fintype.card Ω := by
        gcongr
        exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ = ∑ _q ∈ range Q, (1 / 2 ^ b : ℚ≥0) := by
        rw [sum_div]
        refine sum_congr rfl fun q hqQ => ?_
        have := hone q (mem_range.mp hqQ)
        rw [div_eq_div_iff hc (by positivity), one_mul]
        exact_mod_cast (by rw [mul_comm]; exact this.symm : (Fintype.card Ω : ℕ) = #(B q) * 2 ^ b).symm
    _ = Q / 2 ^ b := by rw [sum_const, card_range, nsmul_eq_mul, mul_one_div]

open Classical Finset in
/-- Proof of work on the circuit. Take an accepted circuit and a proof-of-work check it names (`pc`, difficulty
`b`). For each outcome the prover answers with an assignment holding every replayed call but the tests, the
squeezes and the trial's compression (`FactsBut`), whose trial digest's first word is the word of the trial it picked
among `Q`, each uniform (the ideal compression's answer to the trial). Then the outcomes at which the check's tests hold (the word's top `b` bits zero) are at
most a `Q / 2^b` fraction. `pow_answers_exist` exhibits such answers. -/
theorem pow_test_sound (c : Cert) (s : State) (h : c.accepts s = true) {pc : PowCert} (hpc : pc ∈ c.pows) (Q : ℕ)
    {Ω : Type} [Fintype Ω] (wd : ℕ → Ω → Fin (2 ^ 64))
    (hwd : ∀ q < Q, ∀ v : Fin (2 ^ 64), 2 ^ 64 * #{ω | wd q ω = v} = Fintype.card Ω) (qOf : Ω → ℕ)
    (hq : ∀ ω, qOf ω < Q) (st : Ω → ℕ → Fin 4 → K) (val : Ω → Val)
    (hF : ∀ ω, FactsBut c.calls c.relax c.outs pc.compressAt (st ω) (val ω))
    (htrial : ∀ ω, toWord (val ω (PowCert.trial c.outs pc) 0) = (wd (qOf ω) ω).val) :
    (#{ω | ∀ k < pc.bits, val ω (pc.bit c.outs (64 - pc.bits + k)) 0 = 0} : ℚ≥0) / Fintype.card Ω ≤
      Q / 2 ^ pc.bits := by
  have hok : pc.ok c.outs c.calls c.relax = true := by
    have := (Cert.accepts_rounds h).2.1
    simp only [Array.all_eq_true'] at this
    exact this pc hpc
  have hb : pc.bits ≤ 64 := by
    simp only [PowCert.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1
  refine le_trans (div_le_div_of_nonneg_right ?_ (by positivity)) (grinding_bound pc.bits hb Q wd hwd qOf hq)
  refine Nat.cast_le.mpr (card_le_card fun ω hω => ?_)
  simp only [mem_filter, mem_univ, true_and] at hω ⊢
  rw [← htrial ω]
  exact pow_sem (hF ω) hok hω

/-! GKR's odd layer. -/

theorem map_eq_range {α β : Type} (f : α → β) (d : α) (l : List α) :
    l.map f = (List.range l.length).map fun k => f (l.getD k d) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem?_eq_getElem (show i < l.length by simpa using h1)]

/-- What `odd_test_sound` asks of the prover's answers to an odd layer's challenge pairs `r` (`λ`, then the next):
answers in the random-oracle view (`RomAnswers`) that agree on the seeds before `λ`'s time, and when their `λ` agree on
the seeds before the next challenge's time, both `good` collision-free on the rows bound by
those times (`PairCR`); whose challenges are `r`; and in which some input value is not its true children's product.
`odd_answers_exist` exhibits such answers. -/
structure OddAnswers (c : Cert) (s : State) (oc : OddCert) (L R : ℕ → E) (good : (Fin 2 → E) → Prop)
    (st : (Fin 2 → E) → ℕ → Fin 4 → K) (val : (Fin 2 → E) → Val) : Prop where
  rom : RomAnswers c s oc.transcript st val
  seed0 : ∀ r r', ∀ n ∈ seedsBefore s (c.transcripts.getD oc.transcript default) oc.lam.time,
    nu (val r) n = nu (val r') n
  seed1 : ∀ r r', r 0 = r' 0 →
    ∀ n ∈ seedsBefore s (c.transcripts.getD oc.transcript default) oc.next.time, nu (val r) n = nu (val r') n
  cr0 : ∀ r r', good r → good r' → PairCRAt c s oc.transcript oc.lam.time (val r) (val r')
  cr1 : ∀ r r', good r → good r' → r 0 = r' 0 → PairCRAt c s oc.transcript oc.next.time (val r) (val r')
  chal : ∀ r, Model.ev (val r) oc.lam.chal = r 0 ∧ Model.ev (val r) oc.next.chal = r 1
  false_value : ∀ r, good r → ∃ k < oc.m, Model.ev (val r) (oc.values.getD k 0) ≠ L k * R k

open Classical Finset in
/-- GKR's odd layer on the circuit. Take an accepted circuit, an odd layer it names (`oc`, `m` values), the layer's
true children `L k`, `R k`, and the prover's answers to the challenge pairs (`OddAnswers`). The pairs of `S^2` at which
the answer is `good`, the test holds and every next claim is its value's true line at the next challenge are at most
`m · |S|`: an `m / |S|` fraction. -/
theorem odd_test_sound (c : Cert) (s : State) (h : c.accepts s = true) {oc : OddCert} (hoc : oc ∈ c.odds)
    (S : Finset E) (L R : ℕ → E) (good : (Fin 2 → E) → Prop) (st : (Fin 2 → E) → ℕ → Fin 4 → K)
    (val : (Fin 2 → E) → Val) (ha : OddAnswers c s oc L R good st val) :
    #{r ∈ Fintype.piFinset (fun _ : Fin 2 => S) | good r ∧
        (∀ a b, s.unions[oc.test]? = some (a, b) → val r a = val r b) ∧
        ∀ k < oc.m, Model.ev (val r) (oc.out c.outs k) = L k + r 1 * (L k + R k)} ≤ oc.m * #S := by
  have hall := (Cert.accepts_rounds h).2.2.1
  simp only [Cert.oddsOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hall
  obtain ⟨⟨⟨⟨⟨⟨⟨htr, hok⟩, -⟩, hpair⟩, -⟩, -⟩, hb0⟩, hb1⟩ := hall oc hoc
  have hm : 0 < oc.m := by
    simp only [OddCert.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1
  have hF := ha.rom.facts
  have hseed0 := ha.seed0
  have hseed1 := ha.seed1
  have hchal := ha.chal
  have hne := ha.false_value
  have agree := fun r r' {time w : ℕ} hc hb hs => bound_agree h htr ha.rom r r' (time := time) (w := w) hc hb hs
  -- The values are bound before `λ`, the children before the next challenge.
  have hval : ∀ r r', good r → good r' → ∀ k < oc.m,
      Model.ev (val r) (oc.values.getD k 0) = Model.ev (val r') (oc.values.getD k 0) :=
    fun r r' hg hg' k hk => agree r r' (ha.cr0 r r' hg hg')
      (boundBy_wires hb0 _ (getD_mem_of_lt (by simpa [OddCert.m] using hk))) (hseed0 r r')
  have hch : ∀ r r', good r → good r' → r 0 = r' 0 → ∀ k < oc.m,
      Model.ev (val r) (oc.left k) = Model.ev (val r') (oc.left k) ∧
      Model.ev (val r) (oc.right k) = Model.ev (val r') (oc.right k) := by
    intro r r' hg hg' h0 k hk
    have hmem : oc.left k ∈ (List.range oc.m).flatMap (fun k => [oc.left k, oc.right k]) ∧
        oc.right k ∈ (List.range oc.m).flatMap (fun k => [oc.left k, oc.right k]) :=
      ⟨List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, by simp⟩,
        List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, by simp⟩⟩
    exact ⟨agree r r' (ha.cr1 r r' hg hg' h0) (boundBy_wires hb1 _ hmem.1) (hseed1 r r' h0),
      agree r r' (ha.cr1 r r' hg hg' h0) (boundBy_wires hb1 _ hmem.2) (hseed1 r r' h0)⟩
  -- The values' differences from the children's products, a nonzero polynomial in `λ`.
  by_cases hex : ∃ r₀ : Fin 2 → E, good r₀
  swap
  · simp only [not_exists] at hex
    exact le_trans (le_of_eq (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun r _ hr => hex r hr.1))) (Nat.zero_le _)
  obtain ⟨r₀, hg₀⟩ := hex
  set vs : ℕ → E := fun k => Model.ev (val r₀) (oc.values.getD k 0)
  set D : E[X] := polyOf ((List.range oc.m).map fun k => vs k - L k * R k)
  have hD0 : D ≠ 0 := by
    obtain ⟨k, hk, hk'⟩ := hne r₀ hg₀
    intro hD
    have := congrArg (fun p => Polynomial.coeff p k) hD
    simp only [D, coeff_polyOf, coeff_zero, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some] at this
    exact hk' (sub_eq_zero.mp this)
  have hDdeg : D.natDegree ≤ oc.m - 1 := (natDegree_polyOf _).trans (by simp)
  set Q : (Fin 2 → E) → Prop := fun r => good r ∧ (∀ a b, s.unions[oc.test]? = some (a, b) → val r a = val r b) ∧
    ∀ k < oc.m, Model.ev (val r) (oc.out c.outs k) = L k + r 1 * (L k + R k)
  set A := ({r ∈ Fintype.piFinset (fun _ : Fin 2 => S) | Q r} : Finset (Fin 2 → E))
  have hext : ∀ r r' : Fin 2 → E, r 0 = r' 0 → r 1 = r' 1 → r = r' := by
    intro r r' h0 h1
    funext i
    fin_cases i
    exacts [h0, h1]
  -- At a `λ` that is no root, two answers passing the test agree on the next challenge.
  have hgood : ∀ a, D.eval a ≠ 0 → #{r ∈ A | r 0 = a} ≤ 1 := by
    intro a ha
    refine card_le_one.mpr fun r1 h1 r2 h2 => ?_
    simp only [A, mem_filter] at h1 h2
    obtain ⟨⟨-, hg1, htest, hout1⟩, h10⟩ := h1
    obtain ⟨⟨-, hg2, -, hout2⟩, h20⟩ := h2
    obtain ⟨hc1, he1, ho1⟩ := odd_sem (hF r1) hok
    obtain ⟨-, -, ho2⟩ := odd_sem (hF r2) hok
    -- The test: the values' and the products' polynomials agree at `a`.
    have htv : Model.ev (val r1) (oc.claim c.outs) = Model.ev (val r1) (oc.expected c.outs) := by
      rcases hpair with hp | hp
      · simp only [Model.ev, htest _ _ hp]
      · simp only [Model.ev, ← htest _ _ hp]
    rw [hc1, he1, (hchal r1).1, h10, map_eq_range _ 0 oc.values] at htv
    have hvs : (List.range oc.values.length).map (fun k => Model.ev (val r1) (oc.values.getD k 0)) =
        (List.range oc.m).map vs := List.map_congr_left fun k hk => hval r1 r₀ hg1 hg₀ k (List.mem_range.mp hk)
    rw [hvs] at htv
    obtain ⟨k, hk, hkne⟩ : ∃ k < oc.m, Model.ev (val r1) (oc.left k) * Model.ev (val r1) (oc.right k) ≠ L k * R k := by
      by_contra hn
      simp only [not_exists, not_and, not_not] at hn
      apply ha
      have hl : (List.range oc.m).map (fun k => Model.ev (val r1) (oc.left k) * Model.ev (val r1) (oc.right k)) =
          (List.range oc.m).map (fun k => L k * R k) :=
        List.map_congr_left fun k hk => hn k (List.mem_range.mp hk)
      rw [hl] at htv
      have hD : D.eval a = (polyOf ((List.range oc.m).map vs)).eval a -
          (polyOf ((List.range oc.m).map fun k => L k * R k)).eval a := by
        rw [← Polynomial.eval_sub, ← polyOf_map_sub]
      rw [hD, htv, sub_self]
    obtain ⟨hl2, hr2⟩ := hch r2 r1 hg2 hg1 (h20.trans h10.symm) k hk
    have e1 := (ho1 k hk).symm.trans (hout1 k hk)
    have e2 := (ho2 k hk).symm.trans (hout2 k hk)
    rw [(hchal r1).2] at e1
    rw [(hchal r2).2, hl2, hr2] at e2
    refine hext r1 r2 (h10.trans h20.symm) ?_
    by_contra hx
    have hsub : (r1 1 - r2 1) * ((Model.ev (val r1) (oc.left k) + Model.ev (val r1) (oc.right k)) - (L k + R k)) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp hsub with h0 | h0
    · exact hx (sub_eq_zero.mp h0)
    · have hs : Model.ev (val r1) (oc.left k) + Model.ev (val r1) (oc.right k) = L k + R k := sub_eq_zero.mp h0
      have hl : Model.ev (val r1) (oc.left k) = L k := by linear_combination e1 - r1 1 * h0
      have hr : Model.ev (val r1) (oc.right k) = R k := by linear_combination hs - hl
      exact hkne (by rw [hl, hr])
  -- At a root, the answers are at most one per next challenge.
  have hbad : ∀ a, #{r ∈ A | r 0 = a} ≤ #S := by
    intro a
    refine card_le_card_of_injOn (fun r => r 1) (fun r hr => ?_) (fun r hr r' hr' he => ?_)
    · simp only [Finset.mem_coe, A, mem_filter, Fintype.mem_piFinset] at hr ⊢
      exact hr.1.1 1
    · simp only [Finset.mem_coe, A, mem_filter] at hr hr'
      exact hext r r' (hr.2.trans hr'.2.symm) he
  have hfib := card_eq_sum_card_fiberwise (s := A) (t := S) (f := fun r => r 0) fun r hr => by
    exact Fintype.mem_piFinset.mp (mem_filter.mp hr).1 0
  calc #A = ∑ a ∈ S, #{r ∈ A | r 0 = a} := hfib
    _ ≤ ∑ a ∈ S, if D.eval a = 0 then #S else 1 := sum_le_sum fun a _ => by
        split
        · exact hbad a
        · exact hgood a (by assumption)
    _ = #{a ∈ S | D.eval a = 0} * #S + #{a ∈ S | ¬ D.eval a = 0} := by
        rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul, mul_one]
    _ ≤ (oc.m - 1) * #S + #S :=
        add_le_add (Nat.mul_le_mul_right _ (card_roots_le S hD0 hDdeg)) (card_le_card (filter_subset _ _))
    _ = oc.m * #S := by
        obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
        rw [hm', Nat.succ_sub_one, Nat.succ_mul]

end LeanVMCircuits.Rec.Bind
