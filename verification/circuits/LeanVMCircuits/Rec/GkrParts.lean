module

public import LeanVMCircuits.Rec.GkrInst
public import LeanVMCircuits.Rec.RecParts
public import LeanVMCircuits.Rec.LateSound

@[expose] public section

/-!
A radix-four GKR layer past the top as a check of `RecParts`.

`Bind.layer_part`: where the parent's circuit holds a linked layer's calls and its sumcheck's test (`LayerCert.layer_sem`), the layer's next claims true (each tree's level below at `[low, high] ++ r`, `AirLink.next_claim`) make its values, the previous layer's next claims, true (each tree's level at the previous point), off three events: its sumcheck's against the honest instance `AirLink.layerInst` (`sumcheckFalse`, which `sumcheck_run_sound_at` bounds), the line event `LineBad` (children not the true ones, yet every next claim the true children's, at most `2|S|` of the pairs `(low, high)` of `S × S`, `lineBad_card`) and the `λ` event `LamBad` (values not the true ones, yet one claim at `λ`, at most one `λ`, `lamBad_card`). So a chain of layers meets `RecParts.Ok.test` with those events, each layer's inputs its values and its outputs its next claims.

`checkbind` now asks each layer to draw its challenges as a top layer's (`LayerCert.chalOk`, `GkrCert.layersOk`): `λ`, `low` and `high` in order from its transcript, its children bound by `low`'s time (`LayerCert.boundOk`) and its values by `λ`'s time with the words squeezed with `λ` but its own as seeds (`LayerCert.lamOk`, the sibling-word argument of WHIR's batch rounds: the values read the previous layer's `high`, squeezed from the chaining value `λ` is squeezed from), each with mutation tests. `layer_run_sound_at` bounds the two events together over a run by `3 / |E|` of the oracles off the run's collision event, the true values and children fixed before the layer's challenges: the values are fixed across `λ` (`Run.sib_agree`), so at most one `λ` per `(low, high)`, and the children across `(low, high)`, so at most `2|E|` pairs per `λ`. `LayerCert.chal_eval` makes the challenge wires `layer_part` reads the oracle's challenges.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Sumcheck Finset

/-- A radix-four layer's `λ` event: its values (the previous layer's next claims) are not the true ones, yet both
combine at `λ` to one claim. -/
def LamBad (o T : Fin 2 → E) (lam : E) : Prop := o ≠ T ∧ o 0 + lam * o 1 = T 0 + lam * T 1

/-- A radix-four layer's line event: its children are not the true ones, yet every next claim, the line at `high`
through their lines at `low`, is the true children's. -/
def LineBad (kid T : Fin 2 → Fin 4 → E) (low high : E) : Prop :=
  kid ≠ T ∧ ∀ t, lineE (lineE (kid t 0) (kid t 1) low) (lineE (kid t 2) (kid t 3) low) high =
    lineE (lineE (T t 0) (T t 1) low) (lineE (T t 2) (T t 3) low) high

open Classical in
/-- The `λ` event is at most one draw: the two combinations differ by a nonzero line in `λ`. -/
theorem lamBad_card (S : Finset E) {o T : Fin 2 → E} (h : o ≠ T) : #{lam ∈ S | LamBad o T lam} ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  have ha' := ((Finset.mem_filter.mp ha).2).2
  have hb' := ((Finset.mem_filter.mp hb).2).2
  by_cases h1 : o 1 = T 1
  · exfalso
    have h0 : o 0 = T 0 := by rw [h1] at ha'; exact add_right_cancel ha'
    exact h (funext fun i => by fin_cases i <;> simp [h0, h1])
  · have hd : o 1 - T 1 ≠ 0 := sub_ne_zero.mpr h1
    have e : (a - b) * (o 1 - T 1) = 0 := by linear_combination ha' - hb'
    rcases mul_eq_zero.mp e with e | e
    · exact sub_eq_zero.mp e
    · exact absurd e hd

theorem lineE_sub (x y x' y' t : E) : lineE x y t - lineE x' y' t = lineE (x - x') (y - y') t := by
  simp only [lineE]
  ring

open Classical in
/-- The line event is at most `2|S|` of the pairs `(low, high)`: some value's children differ, and the difference of
its two lines through them is `card_plane_zero`'s plane. -/
theorem lineBad_card (S : Finset E) {kid T : Fin 2 → Fin 4 → E} (h : kid ≠ T) :
    #{p ∈ S ×ˢ S | LineBad kid T p.1 p.2} ≤ 2 * #S := by
  obtain ⟨t, ht⟩ : ∃ t, kid t ≠ T t := by
    by_contra hall
    push Not at hall
    exact h (funext hall)
  have hd : kid t 0 - T t 0 ≠ 0 ∨ kid t 1 - T t 1 ≠ 0 ∨ kid t 2 - T t 2 ≠ 0 ∨ kid t 3 - T t 3 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ht (funext fun c => by fin_cases c <;> simp [sub_eq_zero.mp hall.1, sub_eq_zero.mp hall.2.1,
      sub_eq_zero.mp hall.2.2.1, sub_eq_zero.mp hall.2.2.2])
  refine (card_le_card fun p hp => ?_).trans (card_plane_zero S hd)
  obtain ⟨hpS, -, hpl⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨hpS, ?_⟩
  rw [← lineE_sub, ← lineE_sub, ← lineE_sub, hpl t, sub_self]

/-- A radix-four GKR layer past the top is a check of `RecParts`: where the parent's circuit holds its sumcheck's test
and its calls (`LayerCert.layer_sem`), its next claims true (each tree's level below, `W t`, at `[low, high] ++ r`)
make its values true (each tree's level, the products of `W t`'s fours, at the previous point `p`), off its sumcheck's
event against the honest instance `AirLink.layerInst` (`sumcheckFalse`), the line event (`LineBad`, at most `2|E|` of
the pairs `(low, high)`, `lineBad_card`) and the `λ` event (`LamBad`, at most one `λ`, `lamBad_card`). -/
theorem layer_part {c : Cert} {s : State} {lc : LayerCert} {sc : SumcheckCert} {cs : Array Call} {rl : Array Bool}
    {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : (ℕ → K) → Val} {outs pt : List ℕ} {T' : ℕ → E} (ρ : ℕ → K)
    (hF : Facts cs rl os st (val ρ)) (hlink : lc.linkOk sc os outs pt = true) (hok : lc.layer.ok os cs rl = true)
    (hm : lc.layer.m = 2) (p : Fin sc.rounds.length → E) (W : Fin 2 → ℕ → E)
    (htest : ∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b)
    (hhint : ∀ w ∈ sc.hints, Model.ev (val ρ) w = T' w)
    (hout : ∀ t : Fin 2, Model.ev (val ρ) (lc.layer.out os t) =
      AirLink.mleAt (sc.rounds.length + 2) (Fin.cons (Model.ev (val ρ) lc.layer.low.chal)
        (Fin.cons (Model.ev (val ρ) lc.layer.high.chal) (readR (chalWords c.outs sc.chals) ρ))) (W t))
    (hnot : ¬ sumcheckFalse c s sc (AirLink.layerInst _ p (Model.ev (val ρ) lc.layer.lam.chal) W) T' val ρ)
    (hlam : ¬ LamBad (fun t => Model.ev (val ρ) (outs.getD t 0))
      (fun t => AirLink.mleAt _ p fun z => ∏ c ∈ range 4, W t (4 * z + c)) (Model.ev (val ρ) lc.layer.lam.chal))
    (hline : ¬ LineBad (fun t i => Model.ev (val ρ) (lc.layer.kid t i))
      (fun t i => MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ) (AirLink.childMle _ (W t) i))
      (Model.ev (val ρ) lc.layer.low.chal) (Model.ev (val ρ) lc.layer.high.chal)) :
    ∀ t : Fin 2, Model.ev (val ρ) (outs.getD t 0) = AirLink.mleAt _ p fun z => ∏ c ∈ range 4, W t (4 * z + c) := by
  obtain ⟨hres, -, hclaim, hfinal, hlines⟩ := LayerCert.layer_sem hF hlink hok
  have hvals : lc.layer.values = outs := (LayerCert.link_sem hlink).2.1
  have hlen : outs.length = 2 := by rw [← hvals]; exact hm
  have hkid : (fun (t : Fin 2) (i : Fin 4) => Model.ev (val ρ) (lc.layer.kid t i)) =
      fun (t : Fin 2) (i : Fin 4) => MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ)
        (AirLink.childMle _ (W t) i) := by
    by_contra hne
    exact hline ⟨hne, fun t => (hlines t (by rw [hm]; exact t.isLt)).symm.trans
      ((hout t).trans (AirLink.next_claim _ _ _ _ _))⟩
  have hk : ∀ (t : Fin 2) (i : Fin 4), Model.ev (val ρ) (lc.layer.kid t i) =
      MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ) (AirLink.childMle _ (W t) i) :=
    fun t i => congrFun (congrFun hkid t) i
  have hfin : Model.ev (val ρ) sc.final =
      (AirLink.layerInst _ p (Model.ev (val ρ) lc.layer.lam.chal) W).final (readR (chalWords c.outs sc.chals) ρ) := by
    rw [hfinal, AirLink.layerInst_final, hm]
    have ek : ∀ (t : Fin 2) (i : ℕ), i < 4 → Model.ev (val ρ) (lc.layer.kid t i) =
        MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ) (AirLink.childMle _ (W t) i) :=
      fun t i hi => hk t ⟨i, hi⟩
    simp only [eval_polyOf, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil, List.foldr_cons, List.foldr_nil, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      one_mul, Finset.prod_range_succ, Finset.prod_range_zero, zero_mul, zero_add]
    have e0 := ek 0 0 (by norm_num); have e1 := ek 0 1 (by norm_num)
    have e2 := ek 0 2 (by norm_num); have e3 := ek 0 3 (by norm_num)
    have f0 := ek 1 0 (by norm_num); have f1 := ek 1 1 (by norm_num)
    have f2 := ek 1 2 (by norm_num); have f3 := ek 1 3 (by norm_num)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one] at e0 e1 e2 e3 f0 f1 f2 f3
    rw [e0, e1, e2, e3, f0, f1, f2, f3]
    ring
  have hsum : Model.ev (val ρ) sc.claim0 = (AirLink.layerInst _ p (Model.ev (val ρ) lc.layer.lam.chal) W).sum := by
    by_contra hne
    exact hnot ⟨⟨hhint, htest, by rw [hres, hfin]; simp⟩, hne⟩
  rw [hclaim, AirLink.layerInst_sum] at hsum
  obtain ⟨o0, o1, rfl⟩ : ∃ a b, outs = [a, b] := by
    match outs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have hall : (fun t : Fin 2 => Model.ev (val ρ) ([o0, o1].getD t 0)) =
      fun t => AirLink.mleAt _ p fun z => ∏ c ∈ range 4, W t (4 * z + c) := by
    by_contra hne
    refine hlam ⟨hne, ?_⟩
    simp only [eval_polyOf, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Fin.sum_univ_two,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, zero_mul, zero_add] at hsum
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, List.getD_cons_zero, List.getD_cons_succ]
    linear_combination hsum
  exact fun t => congrFun hall t

/-- Non-vacuity of the events: values `(0, 1)` against true `(1, 0)` combine to one claim at `λ = 1`, and children
off by one in a single slot give every next claim the true one at `low = 0` (the line through the first two) and
`high = 0`. -/
example : LamBad ![0, 1] ![1, 0] 1 ∧ LineBad (fun _ => ![0, 0, 1, 0]) (fun _ => ![0, 0, 0, 0]) 0 0 := by
  refine ⟨⟨fun h => by simpa using congrFun h 0, by simp⟩, fun h => by simpa using congrFun (congrFun h 0) 2,
    fun t => by simp [lineE]⟩

/-! A layer's `λ` and line events over a run. -/

/-- A layer's `λ` event at the oracle's `λ`, against true values `TV`. -/
def lamBadAt (c : Cert) (lc : LayerCert) (TV : Fin 2 → E) (val : (ℕ → K) → Val) (ρ : ℕ → K) : Prop :=
  LamBad (fun t => Model.ev (val ρ) (lc.layer.values.getD t 0)) TV (readR (chalWords c.outs lc.layer.chals) ρ 0)

/-- A layer's line event at the oracle's `low` and `high`, against true children `TK`. -/
def lineBadAt (c : Cert) (lc : LayerCert) (TK : Fin 2 → Fin 4 → E) (val : (ℕ → K) → Val) (ρ : ℕ → K) : Prop :=
  LineBad (fun t i => Model.ev (val ρ) (lc.layer.kid t i)) TK (readR (chalWords c.outs lc.layer.chals) ρ 1)
    (readR (chalWords c.outs lc.layer.chals) ρ 2)

/-- A layer's `λ` or line event. -/
def layerBad (c : Cert) (lc : LayerCert) (TV : Fin 2 → E) (TK : Fin 2 → Fin 4 → E) (val : (ℕ → K) → Val)
    (ρ : ℕ → K) : Prop :=
  lamBadAt c lc TV val ρ ∨ lineBadAt c lc TK val ρ

/-- What `LayerCert.chalOk` gives: the layer's challenges drawn in order from its transcript, each where it says, its
children bound by `low`'s time and its values by `λ`'s with the words squeezed with `λ`. -/
theorem LayerCert.chal_sem {c : Cert} {s : State} {lc : LayerCert} (hlc : lc.chalOk c s c.outs = true) :
    lc.layer.transcript < (c.marksRO s).length ∧
    chalsOk s c.outs (c.transcripts.getD lc.layer.transcript default) false (List.ofFn lc.layer.chals) = true ∧
    (∀ i, (lc.layer.chals i).ok s c.outs c.calls (c.transcripts.getD lc.layer.transcript default).blocks = true) ∧
    lc.boundOk ((c.marksRO s).getD lc.layer.transcript default).2 = true ∧
    lc.lamOk c s c.outs (c.transcripts.getD lc.layer.transcript default) = true := by
  simp only [LayerCert.chalOk, Bool.and_eq_true, decide_eq_true_eq] at hlc
  obtain ⟨⟨⟨⟨⟨⟨htr, hch⟩, hlam⟩, hlow⟩, hhigh⟩, hb⟩, hl⟩ := hlc
  rw [Cert.marksRO_getD c s htr] at hlam hlow hhigh hl
  refine ⟨htr, by simpa [TopCert.chals, List.ofFn_succ] using hch, fun i => ?_, hb, hl⟩
  fin_cases i
  · exact hlam
  · exact hlow
  · exact hhigh

/-- A layer's values are in the closure of the seeds before `λ`'s time and the words squeezed with `λ` but its own,
when `LayerCert.lamOk` passes (`whirBound_closure`'s batch round). -/
theorem LayerCert.lam_closure {c : Cert} {s : State} {T : Transcript} {lc : LayerCert}
    (h : lc.lamOk c s c.outs T = true) :
    ∀ w ∈ lc.layer.values, ∀ n ∈ limbs3 w, Closure T.rulesRO
      (seedsBefore s T lc.layer.lam.time ++ sibSeeds s T lc.layer.lam.time (lc.layer.lam.own c.outs)) n := by
  intro w hw n hn
  simp only [LayerCert.lamOk] at h
  obtain ⟨k, hk, hle⟩ := boundBy_wires h w hw n hn
  refine (Cert.timesX_sound c s T _ lc.fs hk).mono fun m hm => ?_
  simp only [List.mem_append] at hm ⊢
  rcases hm with hm | hm
  · exact Or.inl (seedsBefore_mono hle m hm)
  · simp only [seedsBy, List.mem_map, List.mem_filter, decide_eq_true_eq] at hm
    obtain ⟨p, ⟨⟨x, hx, rfl⟩, -⟩, rfl⟩ := hm
    exact Or.inr hx

/-- Two vectors differing only at challenges whose words are all in `ownL` give assignments agreeing on the words
squeezed at any time but `ownL`: each such word is the oracle's answer, and no differing challenge's. -/
theorem Run.sib_agree {n : ℕ} {c : Cert} {s : State} {T : ℕ} {C : (ℕ → K) → Prop} {st : (ℕ → K) → ℕ → Fin 4 → K}
    {val : (ℕ → K) → Val} (hR : Run c s T C st val) {own : Fin n → Fin 3 → ℕ} (hinj : OwnInj own) (ρ : ℕ → K)
    (k : ℕ) (ownL : List ℕ) (r r' : Fin n → E) (hr : ∀ j, r j ≠ r' j → ∀ l, own j l ∈ ownL) :
    ∀ m ∈ sibSeeds s (c.transcripts.getD T default) k ownL,
      nu (val (oracleAt own ρ r)) m = nu (val (oracleAt own ρ r')) m := by
  intro m hm
  simp only [sibSeeds, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hm
  obtain ⟨p, ⟨hp, -, hnot⟩, rfl⟩ := hm
  rw [hR.ans _ p hp, hR.ans _ p hp]
  by_cases h : ∃ q : Fin n × Fin 3, own q.1 q.2 = p.2
  · obtain ⟨⟨j, l⟩, hj⟩ := h
    have hrj : r j = r' j := by
      by_contra hne
      have hm : ownL.contains p.2 = true := List.contains_iff_mem.mpr (hj ▸ hr j hne l)
      rw [hm] at hnot
      exact Bool.noConfusion hnot
    rw [← hj, oracleAt_own hinj, oracleAt_own hinj, hrj]
  · push Not at h
    rw [oracleAt_off _ _ fun i k => h (i, k), oracleAt_off _ _ fun i k => h (i, k)]

open Classical in
/-- A layer's `λ` and line events over a uniform oracle, at each oracle, off the run's collision event `C`: at most a
`3 / |E|` fraction of the oracles. The values are bound by `λ`'s time with the words squeezed with `λ` but its own
(`LayerCert.lamOk`), so fixed across `λ` off `C` at each `(low, high)`, and at most one `λ` gives false values the
true claim (`lamBad_card`); the children are bound before `low`, so fixed across `(low, high)` off `C` at each `λ`, and
at most `2|E|` pairs give false children the true next claims (`lineBad_card`). The true values `TV ρ` and children
`TK ρ` are the oracle's, fixed before the layer's challenges (`hTV`, `hTK`). -/
theorem layer_run_sound_at {c : Cert} {s : State} {C : (ℕ → K) → Prop} {st : (ℕ → K) → ℕ → Fin 4 → K}
    {val : (ℕ → K) → Val} (h : c.accepts s = true) {lc : LayerCert} (hlc : lc.chalOk c s c.outs = true)
    (hm : lc.layer.m = 2) (TV : (ℕ → K) → Fin 2 → E) (TK : (ℕ → K) → Fin 2 → Fin 4 → E)
    (hTV : ∀ ρ r, TV (oracleAt (chalWords c.outs lc.layer.chals) ρ r) = TV ρ)
    (hTK : ∀ ρ r, TK (oracleAt (chalWords c.outs lc.layer.chals) ρ r) = TK ρ)
    (hR : Run c s lc.layer.transcript C st val) (U : Finset ℕ)
    (hU : oracleWords s (c.transcripts.getD lc.layer.transcript default) ⊆ U) :
    (#{ρ : U → K | offC (fun ρ => layerBad c lc (TV ρ) (TK ρ) val ρ) C (extU _ ρ)} : ℚ≥0) /
      Fintype.card (U → K) ≤ (3 : ℕ) / Fintype.card E := by
  obtain ⟨htr, hc, hok, hbk, hlk⟩ := LayerCert.chal_sem hlc
  obtain ⟨hown, hinj, hmono, -⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i)
  simp only [LayerCert.boundOk] at hbk
  refine run_frac hinj (fun i k => hU (own_mem_oracleWords hown i k))
    (offC (fun ρ => layerBad c lc (TV ρ) (TK ρ) val ρ) C) 3 fun ρ => ?_
  set ow := chalWords c.outs lc.layer.chals with how
  have hkids : ∀ r r' : Fin 3 → E, ¬ C (oracleAt ow ρ r) → ¬ C (oracleAt ow ρ r') → r 0 = r' 0 →
      (fun (t : Fin 2) (i : Fin 4) => Model.ev (val (oracleAt ow ρ r)) (lc.layer.kid t i)) =
        fun (t : Fin 2) (i : Fin 4) => Model.ev (val (oracleAt ow ρ r')) (lc.layer.kid t i) := by
    intro r r' hg hg' h0
    have hp : ∀ j, r j ≠ r' j → (lc.layer.chals 1).time ≤ (lc.layer.chals j).time := fun j hj => by
      fin_cases j
      · exact absurd h0 hj
      · exact le_rfl
      · exact hmono 1 2 (by decide)
    funext t i
    exact bound_agree h htr (hR.rom.comp fun r => oracleAt ow ρ r) r r' (hR.crAt hown hinj ρ _ r r' hp hg hg')
      (boundBy_wires hbk _ (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (by rw [hm]; exact t.isLt),
        List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩⟩))
      (hR.seed_at hown hinj ρ _ r r' hp)
  have h3w : lc.layer.lam.words.length = 3 := ChalCert.ok_words (hok 0)
  have hL : ∀ l : Fin 3, ow 0 l ∈ lc.layer.lam.own c.outs := fun l => by
    have h3 : (lc.layer.lam.own c.outs).length = 3 := by simp [ChalCert.own, h3w]
    show (lc.layer.lam.own c.outs).getD l 0 ∈ _
    rw [List.getD_eq_getElem _ _ (by rw [h3]; exact l.isLt)]
    exact List.getElem_mem _
  have hvals : ∀ r r' : Fin 3 → E, ¬ C (oracleAt ow ρ r) → ¬ C (oracleAt ow ρ r') → r 1 = r' 1 → r 2 = r' 2 →
      (fun t : Fin 2 => Model.ev (val (oracleAt ow ρ r)) (lc.layer.values.getD t 0)) =
        fun t : Fin 2 => Model.ev (val (oracleAt ow ρ r')) (lc.layer.values.getD t 0) := by
    intro r r' hg hg' h1 h2
    have hr : ∀ j, r j ≠ r' j → lc.layer.lam.time ≤ (lc.layer.chals j).time ∧
        ((lc.layer.chals j).time = lc.layer.lam.time → ∀ l, ow j l ∈ lc.layer.lam.own c.outs) := fun j hj => by
      fin_cases j
      · exact ⟨le_rfl, fun _ => hL⟩
      · exact absurd h1 hj
      · exact absurd h2 hj
    have hsib : ∀ j, r j ≠ r' j → ∀ l, ow j l ∈ lc.layer.lam.own c.outs := fun j hj => by
      fin_cases j
      · exact hL
      · exact absurd h1 hj
      · exact absurd h2 hj
    funext t
    have hlen : lc.layer.values.length = 2 := hm
    exact ro_agree h htr (hR.rom.comp fun r => oracleAt ow ρ r) r r'
      (hR.cr_at hown hinj ρ lc.layer.lam.time (lc.layer.lam.own c.outs) r r' hr hg hg')
      (fun n hn => hn.mono fun m hm => List.mem_append_left _ hm)
      (LayerCert.lam_closure hlk _ (by
        rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact t.isLt)]
        exact List.getElem_mem _))
      fun m hm => by
        rcases List.mem_append.mp hm with hm | hm
        · exact hR.seed_at hown hinj ρ _ r r' (fun j hj => (hr j hj).1) m hm
        · exact Run.sib_agree hR hinj ρ _ _ r r' hsib m hm
  have hsub : ({r : Fin 3 → E | offC (fun ρ => layerBad c lc (TV ρ) (TK ρ) val ρ) C (oracleAt ow ρ r)} : Finset _) ⊆
      ({r | ¬ C (oracleAt ow ρ r) ∧ LamBad (fun t : Fin 2 => Model.ev (val (oracleAt ow ρ r))
        (lc.layer.values.getD t 0)) (TV ρ) (r 0)} : Finset _) ∪
      ({r | ¬ C (oracleAt ow ρ r) ∧ LineBad (fun (t : Fin 2) (i : Fin 4) => Model.ev (val (oracleAt ow ρ r))
        (lc.layer.kid t i)) (TK ρ) (r 1) (r 2)} : Finset _) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, offC, layerBad, lamBadAt, lineBadAt,
      ← how, readR_oracleAt hinj, hTV ρ, hTK ρ] at hr ⊢
    rcases hr.1 with h1 | h1
    · exact Or.inl ⟨hr.2, h1⟩
    · exact Or.inr ⟨hr.2, h1⟩
  have h1 : #{r : Fin 3 → E | ¬ C (oracleAt ow ρ r) ∧ LamBad (fun t : Fin 2 =>
      Model.ev (val (oracleAt ow ρ r)) (lc.layer.values.getD t 0)) (TV ρ) (r 0)} ≤ Fintype.card E ^ 2 := by
    rw [card_eq_sum_card_fiberwise (f := fun r => (r 1, r 2)) (t := univ) (fun _ _ => mem_univ _)]
    calc _ ≤ ∑ _a : E × E, 1 := sum_le_sum fun a _ => ?_
      _ = Fintype.card E ^ 2 := by rw [sum_const, card_univ, Fintype.card_prod, smul_eq_mul]; ring
    rcases Finset.eq_empty_or_nonempty ({r ∈ ({r : Fin 3 → E | ¬ C (oracleAt ow ρ r) ∧ LamBad (fun t : Fin 2 =>
        Model.ev (val (oracleAt ow ρ r)) (lc.layer.values.getD t 0)) (TV ρ) (r 0)} : Finset _) |
        (r 1, r 2) = a} : Finset _) with he | ⟨r₀, hr₀⟩
    · rw [he, card_empty]
      exact Nat.zero_le _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₀
    calc _ ≤ #{lam ∈ (univ : Finset E) | LamBad (fun t : Fin 2 =>
          Model.ev (val (oracleAt ow ρ r₀)) (lc.layer.values.getD t 0)) (TV ρ) lam} :=
          card_le_card_of_injOn (fun r => r 0) (fun r hr => by
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hr
            refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
            have e := hr.2.trans hr₀.2.symm
            rw [hvals r₀ r hr₀.1.1 hr.1.1 (congrArg Prod.fst e).symm (congrArg Prod.snd e).symm]
            exact hr.1.2) fun r hr r' hr' he => by
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hr hr'
            have e := hr.2.trans hr'.2.symm
            funext j
            fin_cases j
            · exact he
            · exact congrArg Prod.fst e
            · exact congrArg Prod.snd e
      _ ≤ 1 := lamBad_card univ hr₀.1.2.1
  have h2 : #{r : Fin 3 → E | ¬ C (oracleAt ow ρ r) ∧ LineBad (fun (t : Fin 2) (i : Fin 4) =>
      Model.ev (val (oracleAt ow ρ r)) (lc.layer.kid t i)) (TK ρ) (r 1) (r 2)} ≤ 2 * Fintype.card E ^ 2 := by
    rw [card_eq_sum_card_fiberwise (f := fun r => r 0) (t := univ) (fun _ _ => mem_univ _)]
    calc _ ≤ ∑ _a : E, 2 * Fintype.card E := sum_le_sum fun a _ => ?_
      _ = 2 * Fintype.card E ^ 2 := by rw [sum_const, card_univ, smul_eq_mul]; ring
    rcases Finset.eq_empty_or_nonempty ({r ∈ ({r : Fin 3 → E | ¬ C (oracleAt ow ρ r) ∧ LineBad (fun (t : Fin 2)
        (i : Fin 4) => Model.ev (val (oracleAt ow ρ r)) (lc.layer.kid t i)) (TK ρ) (r 1) (r 2)} : Finset _) |
        r 0 = a} : Finset _) with he | ⟨r₀, hr₀⟩
    · rw [he, card_empty]
      exact Nat.zero_le _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr₀
    calc _ ≤ #{p ∈ (univ : Finset E) ×ˢ univ | LineBad (fun (t : Fin 2) (i : Fin 4) =>
          Model.ev (val (oracleAt ow ρ r₀)) (lc.layer.kid t i)) (TK ρ) p.1 p.2} :=
          card_le_card_of_injOn (fun r => (r 1, r 2)) (fun r hr => by
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hr
            refine Finset.mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩
            rw [hkids r₀ r hr₀.1.1 hr.1.1 (hr₀.2.trans hr.2.symm)]
            exact hr.1.2) fun r hr r' hr' he => by
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hr hr'
            funext j
            fin_cases j
            · exact hr.2.trans hr'.2.symm
            · exact congrArg Prod.fst he
            · exact congrArg Prod.snd he
      _ ≤ 2 * #(univ : Finset E) := lineBad_card univ hr₀.1.2.1
      _ = 2 * Fintype.card E := by rw [card_univ]
  calc #{r : Fin 3 → E | offC (fun ρ => layerBad c lc (TV ρ) (TK ρ) val ρ) C (oracleAt ow ρ r)} * Fintype.card E
      ≤ (Fintype.card E ^ 2 + 2 * Fintype.card E ^ 2) * Fintype.card E :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add h1 h2)))
    _ = 3 * Fintype.card E ^ 3 := by ring

/-- A layer's challenge wire is the oracle's challenge where the replayed calls hold: `ChalCert.read` of its own words,
the run's answers there. So `layer_part`'s `λ`, `low` and `high` are `layer_run_sound_at`'s. -/
theorem LayerCert.chal_eval {c : Cert} {s : State} {lc : LayerCert} {C : (ℕ → K) → Prop}
    {st : (ℕ → K) → ℕ → Fin 4 → K} {val : (ℕ → K) → Val} {rl : Array Bool} (hlc : lc.chalOk c s c.outs = true)
    (hR : Run c s lc.layer.transcript C st val) (ρ : ℕ → K) (hF : Facts c.calls rl c.outs (st ρ) (val ρ))
    (i : Fin 3) : Model.ev (val ρ) (lc.layer.chals i).chal = readR (chalWords c.outs lc.layer.chals) ρ i := by
  obtain ⟨-, hc, hok, -, -⟩ := LayerCert.chal_sem hlc
  obtain ⟨hown, -, -, -, hp⟩ := chalsOk_sem hc fun i => ChalCert.ok_words (hok i)
  rw [ChalCert.read (hok i) (hp i) hF]
  simp only [readR, chalWords]
  have e : ∀ k : Fin 3, nu (val ρ) (((lc.layer.chals i).own c.outs).getD k 0) =
      ρ (((lc.layer.chals i).own c.outs).getD k 0) := fun k => hR.ans ρ _ (hown i k).1
  exact congrArg₂ (fun a b => toE a b _) (e 0) (e 1) ▸ congrArg (toE _ _) (e 2)

/-- Mutation tests of `LayerCert.boundOk`: a layer whose children (wire 1) are bound by `low`'s time passes; its
children bound after `low`, or unbound, fail. -/
example : LayerCert.boundOk #[some 1, some 1, some 1, none, some 2, some 2, some 2]
    { sc := 0, layer := { (default : TopCert) with
        values := [0], kids := [[1, 1, 1, 1]], lam := ⟨0, 0, [], 1⟩, low := ⟨0, 0, [], 2⟩ } } = true := by
  decide

example : LayerCert.boundOk #[some 1, some 1, some 1, none, some 3, some 3, some 3]
    { sc := 0, layer := { (default : TopCert) with
        values := [0], kids := [[1, 1, 1, 1]], lam := ⟨0, 0, [], 1⟩, low := ⟨0, 0, [], 2⟩ } } = false := by
  decide

example : LayerCert.boundOk #[some 1, some 1, some 1]
    { sc := 0, layer := { (default : TopCert) with
        values := [0], kids := [[1, 1, 1, 1]], lam := ⟨0, 0, [], 1⟩, low := ⟨0, 0, [], 2⟩ } } = false := by
  decide

namespace LamOkExample

/-- A `HASH` row reading chaining value `h` and writing `o`, its counter wire 1 (the duplex's output role). -/
def row (h o : ℕ) : List ℕ := [h, 1, 2, 3, 4, 5, o, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- One absorb block (row 0) and two squeezes of its output (rows 1 and 2, writing wires 16 and 20), both drawn after
block 0: the second's words are the first's siblings. -/
def state : State where
  next := 24
  hash := #[row 0 6, row 6 16, row 6 20]
  pub := #[(1, .const [6 * 2 ^ 56, 0, 0, 0])]

def transcript : Transcript where
  blocks := [0]
  firings := #[]
  squeezes := [1, 2]

def cert : Cert where
  rules := {}
  nodes := 96
  isTest := #[]
  claims := #[]
  transcripts := [transcript]
  calls := #[]
  relax := #[]
  pools := #[]
  prods := #[]
  points := #[]
  covers := #[]

/-- A layer with values `vs` and `λ` reading wire `w`'s first three limbs (call 0's output, `os = #[[w]]`), drawn after
block 0. -/
def layer (vs : List ℕ) : LayerCert :=
  { sc := 0, layer := { (default : TopCert) with values := vs, lam := ⟨0, 0, [(0, 0, 0), (0, 1, 0), (0, 2, 0)], 1⟩ } }

end LamOkExample

open LamOkExample in
/-- Mutation tests of `LayerCert.lamOk`: values squeezed with `λ` (wire 20, beside `λ` at wire 16) pass; values that
are `λ`'s own words (wire 16 at `λ` wire 16, or wire 20 at `λ` wire 20), or a wire only one of whose limbs the block
absorbs (wire 8), fail. -/
example : (layer [20]).lamOk cert state #[[16]] transcript = true := by decide +kernel

open LamOkExample in
example : (layer [16]).lamOk cert state #[[16]] transcript = false := by decide +kernel

open LamOkExample in
example : (layer [20]).lamOk cert state #[[20]] transcript = false := by decide +kernel

open LamOkExample in
example : (layer [8]).lamOk cert state #[[16]] transcript = false := by decide +kernel

end LeanVMCircuits.Rec.Bind
