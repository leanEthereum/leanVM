module

public import LeanVMCircuits.Rec.BusDecompose
public import LeanVMCircuits.Rec.TableResid
public import LeanVMCircuits.Rec.AirRun
public import LeanVMCircuits.Rec.GkrParts
public import LeanVMCircuits.Rec.Named

@[expose] public section

/-!
The bus's balance and the table sumcheck as checks of `RecParts`.

`bus::verify_balance` takes the bus GKR's leaf claims `v_s` at the point `ζ` and derives the totals `tot_s = fw_s + v_s`, `fw_s` the side's framework part; `TableArgument::verify` draws `ξ` and runs the table sumcheck of the claim `tot_0 + ξ tot_1`. Two checks of `RecParts` sit between the GKR's last layer and the opening.

The balance (`AirLink.balance_part`): its inputs are the leaf claims, its output the table sumcheck's input claim, `tot_0 + ξ tot_1` being the batch's honest sum `tableSum` at the forms' honest sums. Where the framework parts are `framework` and the forms `sideForm` over the bus's blocks, and the GKR's leaf layer is those blocks (`totals_eq_formSums`), a true output makes the leaf claims true off the balance's event `balDraws`: the bus parts (the forms' sums less the totals) are nonzero, yet the batch claim holds. `Bind.balance_named` states it on the named certificates (`TableCert`, `GkrCert`): the GKR's two last next claims are the true leaf claims. As a polynomial in `ξ` with a nonzero constant or linear coefficient the batch claim has at most `66 + 1` roots (`xi_roots_low`), so the event is at most `(66 + 1) / |E|` of the draws (`balDraws_card`), of the outcomes when the draw is uniform after the totals (`balBad_frac`, the batch's lens) and of a run's oracles (`balRun_frac`).

The table sumcheck (`Bind.table_part`): its input claim is its honest instance `tableInst`'s sum, its outputs the hints and the column claims, openings of the committed witness at `chi r`. Where its residual is certified term by term (`ResidCert.final_eq`) and its last side tested against zero, true outputs make the input true off its event `sumcheckFalse`, which `sumcheck_run_sound_at` bounds.

`Edges.tableParts` lays a child's checks from the bus GKR's root to the opening in a line: the GKR's layers from the root (each one's outputs the next one's values, the last one's the leaf claims), the balance, the table sumcheck and flock's reduction (outputs openings). `Edges.tableParts_ok`: they meet `RecParts.Ok` where each check's test holds off its event and the openings off `pcsBad`; `Edges.checksGiveTable_of_parts`: their named inputs give `AirLink.ChecksGiveTable` (`checksGiveTable_of_named`).
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model Finset

/-- A nonzero constant or linear coefficient leaves at most `m + 1` roots. -/
theorem xi_roots_low {m : ℕ} (c : Fin m → E) (a : Fin 2 → E) (ha : a ≠ 0) :
    #({ξ | a 0 + ξ * a 1 + ∑ j : Fin m, ξ ^ (2 + (j : ℕ)) * c j = 0} : Finset E) ≤ m + 1 := by
  have hp : xiPoly c a ≠ 0 := by
    intro h0
    have e0 := coeff_xiPoly c a 0
    have e1 := coeff_xiPoly c a 1
    rw [h0, Polynomial.coeff_zero, if_pos rfl, if_neg (by norm_num),
      Finset.sum_eq_zero fun j _ => if_neg (by omega)] at e0
    rw [h0, Polynomial.coeff_zero, if_neg (by norm_num), if_pos rfl,
      Finset.sum_eq_zero fun j _ => if_neg (by omega)] at e1
    refine ha (funext fun i => ?_)
    fin_cases i
    · simpa using e0.symm
    · simpa using e1.symm
  have hdeg : (xiPoly c a).natDegree ≤ m + 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_xiPoly, if_neg (by omega), if_neg (by omega), zero_add, zero_add]
    exact Finset.sum_eq_zero fun j _ => if_neg (by omega)
  calc #({ξ | a 0 + ξ * a 1 + ∑ j : Fin m, ξ ^ (2 + (j : ℕ)) * c j = 0} : Finset E)
      ≤ (xiPoly c a).roots.toFinset.card := by
        refine card_le_card fun ξ hξ => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot, eval_xiPoly]
        exact hξ
    _ ≤ Multiset.card (xiPoly c a).roots := Multiset.toFinset_card_le _
    _ ≤ (xiPoly c a).natDegree := Polynomial.card_roots' _
    _ ≤ m + 1 := hdeg

open Classical in
/-- The balance's draw event for a committed witness and bus parts depending on `ζ`: the parts are nonzero at `ζ`, yet
the batch claim holds at `(ζ, ξ)`. -/
noncomputable def balDraws {n : ℕ} (w : Witness) (a : (Fin n → E) → Fin 2 → E) : Finset ((Fin n → E) × E) :=
  {x | a x.1 ≠ 0 ∧ BatchClaim w x.1 (a x.1) x.2}

/-- Off the draw event, the batch claim makes the bus parts zero. -/
theorem parts_zero {n : ℕ} {w : Witness} {a : (Fin n → E) → Fin 2 → E} {x : (Fin n → E) × E}
    (hx : x ∉ balDraws w a) (h : BatchClaim w x.1 (a x.1) x.2) : a x.1 = 0 := by
  by_contra hne
  exact hx (by simp only [balDraws, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hne, h⟩)

open Classical in
/-- The balance's draw event is at most a `(66 + 1)/|E|` fraction of the draws `E^n × E`: at most `66 + 1` values of
`ξ` per `ζ`, whatever the witness and the bus parts. -/
theorem balDraws_card {n : ℕ} (w : Witness) (a : (Fin n → E) → Fin 2 → E) :
    #(balDraws w a) * Fintype.card E ≤ (allIds.length + 1) * Fintype.card E ^ (n + 1) := by
  have hfib : ∀ ζ : Fin n → E, #({ξ | (ζ, ξ) ∈ balDraws w a} : Finset E) ≤ allIds.length + 1 := by
    intro ζ
    by_cases ha : a ζ = 0
    · have : ({ξ | (ζ, ξ) ∈ balDraws w a} : Finset E) = ∅ := by
        ext ξ
        simp [balDraws, ha]
      rw [this]
      exact Nat.zero_le _
    · refine le_trans (card_le_card fun ξ hξ => ?_)
        (xi_roots_low (fun j : Fin allIds.length => coef w ζ allIds[j]) (a ζ) ha)
      exact Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp (Finset.mem_filter.mp hξ).2).2.2⟩
  have hsum : #(balDraws w a) ≤ Fintype.card E ^ n * (allIds.length + 1) := by
    calc #(balDraws w a) = ∑ ζ : Fin n → E, #({ξ | (ζ, ξ) ∈ balDraws w a} : Finset E) := by
          have := card_pairs (fun x : (Fin n → E) × E => x ∈ balDraws w a)
          rw [← this]
          congr 1
          ext x
          simp
      _ ≤ ∑ _ζ : Fin n → E, (allIds.length + 1) := sum_le_sum fun ζ _ => hfib ζ
      _ = _ := by rw [sum_const, card_univ, card_draws, smul_eq_mul]
  calc #(balDraws w a) * Fintype.card E ≤ Fintype.card E ^ n * (allIds.length + 1) * Fintype.card E :=
        Nat.mul_le_mul_right _ hsum
    _ = (allIds.length + 1) * Fintype.card E ^ (n + 1) := by ring

open Classical in
/-- The balance's event: the outcomes whose draw is in the draw event. -/
noncomputable def balBad {Ω : Type} [Fintype Ω] {n : ℕ} (wit : Ω → Witness) (aOf : Ω → (Fin n → E) → Fin 2 → E)
    (bdraw : Ω → (Fin n → E) × E) : Finset Ω :=
  {ω | bdraw ω ∈ balDraws (wit ω) (aOf ω)}

/-- The balance's event is at most a `(66 + 1)/|E|` fraction of the outcomes when the draw `(ζ, ξ)` is uniform and
made after the commitment and the totals, the bus parts fixed but for `ζ`: the lens of `batchBad_frac`. -/
theorem balBad_frac {Ω : Type} [Fintype Ω] {n : ℕ} (wit : Ω → Witness) (aOf : Ω → (Fin n → E) → Fin 2 → E)
    (bdraw : Ω → (Fin n → E) × E) (put : Ω → (Fin n → E) × E → Ω) (hgp : ∀ ω x, bdraw (put ω x) = x)
    (hpg : ∀ ω, put ω (bdraw ω) = ω) (hpp : ∀ ω x y, put (put ω x) y = put ω y)
    (hwit : ∀ ω x, wit (put ω x) = wit ω) (haOf : ∀ ω x, aOf (put ω x) = aOf ω) :
    (#(balBad wit aOf bdraw) : ℚ≥0) / Fintype.card Ω ≤ ((allIds.length + 1 : ℕ) : ℚ≥0) / Fintype.card E := by
  have hpos : 0 < Fintype.card E := Fintype.card_pos
  set B := allIds.length + 1
  have hterm : ∀ ω, #(balDraws (wit ω) (aOf ω)) ≤ B * Fintype.card E ^ n := by
    intro ω
    have hc := balDraws_card (wit ω) (aOf ω)
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc #(balDraws (wit ω) (aOf ω)) * Fintype.card E ≤ B * Fintype.card E ^ (n + 1) := hc
      _ = B * Fintype.card E ^ n * Fintype.card E := by ring
  have hlens := Bind.card_lens put bdraw hgp hpg hpp fun ω => bdraw ω ∈ balDraws (wit ω) (aOf ω)
  have hA : #(balBad wit aOf bdraw) * Fintype.card ((Fin n → E) × E) ≤
      Fintype.card Ω * (B * Fintype.card E ^ n) := by
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) (hlens.trans ?_)
    · intro ω hω
      simp only [balBad, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hω
    · calc _ ≤ ∑ _ω : Ω, B * Fintype.card E ^ n :=
            sum_le_sum fun ω _ => (card_le_card fun x hx => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
              rwa [hgp, hwit, haOf] at hx).trans (hterm ω)
        _ = _ := by rw [sum_const, card_univ, smul_eq_mul]
  rw [Fintype.card_prod, card_draws] at hA
  refine Bind.frac_of_card n ?_
  calc #(balBad wit aOf bdraw) * Fintype.card E * Fintype.card E ^ n =
        #(balBad wit aOf bdraw) * (Fintype.card E ^ n * Fintype.card E) := by ring
    _ ≤ Fintype.card Ω * (B * Fintype.card E ^ n) := hA
    _ = Fintype.card Ω * B * Fintype.card E ^ n := by ring

open Classical in
/-- The balance's draw `(ζ, ξ)` as a run's `n + 1` challenges `own`, drawn after time `k` (the batch's draw,
`batchRun_frac`): where the committed witness and the bus parts' dependence on `ζ` are fixed before `k`, the oracles
at which the draw is in the balance's draw event are at most `(66 + 1)/|E|` of them. -/
theorem balRun_frac {c : Bind.Cert} {s : State} {T : ℕ} {C : (ℕ → K) → Prop} {st : (ℕ → K) → ℕ → Fin 4 → K}
    {val : (ℕ → K) → Val} (hR : Bind.Run c s T C st val) {n : ℕ} {own : Fin (n + 1) → Fin 3 → ℕ}
    {time : Fin (n + 1) → ℕ} (hown : Bind.OwnAt s (c.transcripts.getD T default) own time) (hinj : Bind.OwnInj own)
    {k : ℕ} (hk : ∀ i, k ≤ time i) (wit : (ℕ → K) → Witness) (aOf : (ℕ → K) → (Fin n → E) → Fin 2 → E)
    (hwit : Bind.CommittedBefore s (c.transcripts.getD T default) val k wit)
    (haOf : Bind.CommittedBefore s (c.transcripts.getD T default) val k aOf)
    (U : Finset ℕ) (hU : Bind.oracleWords s (c.transcripts.getD T default) ⊆ U) :
    (#{ρ : U → K | batchOf (Bind.readR own (Bind.extU U ρ)) ∈ balDraws (wit (Bind.extU U ρ)) (aOf (Bind.extU U ρ))} :
      ℚ≥0) / Fintype.card (U → K) ≤ ((allIds.length + 1 : ℕ) : ℚ≥0) / Fintype.card E := by
  have key := Bind.run_frac hinj (fun i j => hU (Bind.own_mem_oracleWords hown i j))
    (fun ρ => batchOf (Bind.readR own ρ) ∈ balDraws (wit ρ) (aOf ρ)) (allIds.length + 1) fun ρ => by
      refine le_trans (Nat.mul_le_mul_right _ (card_le_card
        (t := ({r : Fin (n + 1) → E | batchOf r ∈ balDraws (wit ρ) (aOf ρ)} : Finset _)) fun r hr => ?_)) ?_
      · simp only [mem_filter, mem_univ, true_and, Bind.readR_oracleAt hinj, hR.committed_at hown hinj hk hwit ρ,
          hR.committed_at hown hinj hk haOf ρ] at hr ⊢
        exact hr
      · rw [batchOf_card]
        exact balDraws_card (wit ρ) (aOf ρ)
  convert key

open Classical in
/-- Non-vacuity of the event: nonzero bus parts `(ξ_0, 1)` meet the batch claim of a witness breaking no identity
at `ξ = ξ_0`, so for each `ζ` exactly one draw is in the event. -/
example {n : ℕ} (w : Witness) (hv : ¬ Viol w) (ζ : Fin n → E) (ξ : E) :
    (ζ, ξ) ∈ balDraws w fun _ => ![ξ, 1] := by
  have hc : ∀ p ∈ allIds, coef w ζ p = 0 := fun p hp => Finset.sum_eq_zero fun z hz => by
    have : p.2.eval (w.cols p.1 z) = 0 := by
      by_contra hne
      exact hv ⟨p, hp, z, Finset.mem_range.mp hz, hne⟩
    rw [this, emb_zero, mul_zero]
  refine Finset.mem_filter.mpr ⟨mem_univ _, fun h => by simpa using congrFun h 1, ?_⟩
  simp only [BatchClaim]
  rw [Finset.sum_eq_zero fun j _ => by rw [hc allIds[j] (List.getElem_mem j.isLt), mul_zero]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, add_zero]
  rw [← two_mul, two_E, zero_mul]

/-- The balance as a check of `RecParts`: where the totals are the framework parts plus the leaf claims `v` and the
framework parts plus the true leaf claims `V` are the forms' sums (`totals_eq_formSums`, at the bus's blocks), the
table sumcheck's input claim `tot_0 + ξ tot_1` being the batch's honest sum at the forms' sums makes each leaf claim
true, off the draw event at the bus parts the forms' sums less the totals. -/
theorem balance_part {n : ℕ} {w : Witness} {ζ : Fin n → E} {ξ : E} {forms : Fin 2 → Table → Quad}
    {a : (Fin n → E) → Fin 2 → E} {tot fw v V : Fin 2 → E}
    (ha : a ζ = fun i => formSums w ζ forms i - tot i) (htot : ∀ i, tot i = fw i + v i)
    (hdec : ∀ i, fw i + V i = formSums w ζ forms i)
    (hsum : tot 0 + ξ * tot 1 = tableSum w ζ (formSums w ζ forms) ξ) (hx : (ζ, ξ) ∉ balDraws w a) :
    ∀ i, v i = V i := by
  have h0 := parts_zero (x := (ζ, ξ)) hx (by rw [ha]; exact batchClaim_of_sum hsum)
  intro i
  have hi := congrFun h0 i
  rw [ha] at hi
  simp only [Pi.zero_apply] at hi
  linear_combination -hi - htot i - hdec i

/-- The balance from the table sumcheck's input: its input claim `tot_0 + ξ tot_1` being its honest instance's sum,
every owned table's `τ` at most its rounds (`tableInst_sum`), makes each leaf claim true off the draw event. -/
theorem balance_of_inst {n : ℕ} {w : Witness} {ζ : Fin n → E} {ξ : E} {forms : Fin 2 → Table → Quad}
    {a : (Fin n → E) → Fin 2 → E} {tot fw v V : Fin 2 → E} (htau : ∀ T ∈ owned, tauOf w T ≤ n)
    (ha : a ζ = fun i => formSums w ζ forms i - tot i) (htot : ∀ i, tot i = fw i + v i)
    (hdec : ∀ i, fw i + V i = formSums w ζ forms i)
    (hsum : tot 0 + ξ * tot 1 = (tableInst n w ζ forms ξ).sum) (hx : (ζ, ξ) ∉ balDraws w a) :
    ∀ i, v i = V i :=
  balance_part ha htot hdec (by rw [hsum, tableInst_sum w ζ forms ξ htau]) hx

end LeanVMCircuits.Rec.AirLink

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model AirLink Finset

/-- The table sumcheck as a check of `RecParts`: where its residual is certified term by term (`ResidCert.okIn`) at the
named point `ζ`, heights and forms, its last side tested against a zero, its hints true and its column claims the
committed columns' extensions at `chi r` (openings), its input claim is its honest instance `tableInst`'s sum off its
event `sumcheckFalse`. -/
theorem table_part {c : Cert} {s : State} {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)}
    {st : ℕ → Fin 4 → K} {val : (ℕ → K) → Val} {rc : ResidCert} {sc : SumcheckCert} {T' : ℕ → E} (ρ : ℕ → K)
    (hF : Facts cs rl os st (val ρ)) (h : rc.okIn os c.sumchecks cs rl = true) (hsc : c.sumchecks[rc.sc]? = some sc)
    (w : Witness) (ζ : Fin sc.rounds.length → E) (forms : Fin 2 → Table → Quad)
    (hζ : ∀ m : Fin sc.rounds.length, Model.ev (val ρ) (rc.zeta.getD m 0) = ζ m)
    (hτ : ∀ T ∈ owned, (rc.termOf T).tau = tauOf w T) (hforms : ∀ T ∈ owned, ∀ i, rc.formsV (val ρ) i T = forms i T)
    (hchal : ∀ j : Fin sc.rounds.length,
      Model.ev (val ρ) (sc.rounds.getD j default).chal = readR (chalWords c.outs sc.chals) ρ j)
    (htest : ∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b)
    (hzero : Model.ev (val ρ) sc.final = 0) (hhint : ∀ w ∈ sc.hints, Model.ev (val ρ) w = T' w)
    (hcol : ∀ T ∈ owned, ∀ c < nCols T, rc.colV (val ρ) T c =
      MvPolynomial.eval (chi fun j => Model.ev (val ρ) (sc.rounds.getD j default).chal) (mle sc.rounds.length w T c))
    (hnot : ¬ sumcheckFalse c s sc (tableInst sc.rounds.length w ζ forms (Model.ev (val ρ) rc.xi)) T' val ρ) :
    Model.ev (val ρ) sc.claim0 = (tableInst sc.rounds.length w ζ forms (Model.ev (val ρ) rc.xi)).sum := by
  refine sumcheck_part ρ htest ⟨hhint, ?_⟩ hnot
  rw [hzero, zero_add, ResidCert.final_eq hF h hsc w ζ forms hζ hτ hforms hcol]
  congr 1
  funext j
  exact hchal j

/-- The balance on the named certificates: where the calls hold and the table sumcheck `tc` and its bus GKR `g` pass,
the table sumcheck's input claim being its honest instance's sum makes the GKR's two last next claims the true leaf
claims `V`, off the balance's draw event at the bus parts the forms' sums less the named totals, where the named
framework shares plus `V` are the forms' sums (`totals_eq_formSums` with the framework shares `AirLink.framework`). -/
theorem balance_named {tc : TableCert} {g : GkrCert} {scs : Array SumcheckCert} {tops : Array TopCert}
    {odds : Array OddCert} {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    (hF : Facts cs rl os st val) (htc : tc.okIn scs tops odds cs rl os = true)
    (hg : g.okIn tc scs tops odds cs rl os = true) {sc : SumcheckCert} (hsc : scs[tc.sc]? = some sc) {n : ℕ}
    {w : Witness} {ζ : Fin n → E} {forms : Fin 2 → Table → Quad} {a : (Fin n → E) → Fin 2 → E} {V : Fin 2 → E}
    (htau : ∀ T ∈ owned, tauOf w T ≤ n)
    (ha : a ζ = fun i => formSums w ζ forms i - Model.ev val (if i = 0 then tc.tot0 else tc.tot1))
    (hdec : ∀ i, Model.ev val (if i = 0 then g.fw.1 else g.fw.2) + V i = formSums w ζ forms i)
    (hin : Model.ev val sc.claim0 = (tableInst n w ζ forms (Model.ev val tc.xi)).sum)
    (hx : (ζ, Model.ev val tc.xi) ∉ balDraws w a) :
    ∃ v0 v1, LayerCert.chain scs cs rl os g.layers (g.start tops odds os).2.1 (g.start tops odds os).2.2 =
      some [v0, v1] ∧ Model.ev val v0 = V 0 ∧ Model.ev val v1 = V 1 := by
  obtain ⟨-, v0, v1, hch, e0, e1⟩ := GkrCert.sem hF hg
  have hsum := (TableCert.claim_iff hF htc hsc _).mp hin
  have hv := balance_of_inst (tot := fun i => Model.ev val (if i = 0 then tc.tot0 else tc.tot1))
    (fw := fun i => Model.ev val (if i = 0 then g.fw.1 else g.fw.2))
    (v := fun i => Model.ev val (if i = 0 then v0 else v1)) htau ha
    (fun i => by fin_cases i <;> simp [e0, e1]) hdec (by simpa using hsum) hx
  exact ⟨v0, v1, hch, by simpa using hv 0, by simpa using hv 1⟩

end LeanVMCircuits.Rec.Bind

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model Finset

variable {ι Ω : Type}

/-- A child's checks from its bus GKR's root to the opening. Checks `0` to `g v - 1` are the GKR's layers from the
root, check `k`'s inputs its values `vals v k ω` being the true ones `tvals v k ω` and its outputs the next layer's
values, so `vals v (g v)` are the leaf claims; check `g v` is the balance, its inputs the leaf claims true and its
output the table sumcheck's input `tin`; check `g v + 1` is the table sumcheck, its outputs openings `opened`; check
`g v + 2` is flock's reduction, its input `fl` and its outputs openings. -/
def tableParts (g : ι → ℕ) (vals tvals : ι → ℕ → Ω → Fin 2 → E) (tin fl opened : ι → Ω → Prop)
    (layerBad : ι → ℕ → Finset Ω) (balBad tabBad flBad pcsBad crBad : ι → Finset Ω) : RecParts ι Ω where
  J v := g v + 3
  inOk v j ω := if j ≤ g v then vals v j ω = tvals v j ω else if j = g v + 1 then tin v ω else fl v ω
  outOk v j ω := if j < g v then vals v (j + 1) ω = tvals v (j + 1) ω else if j = g v then tin v ω else opened v ω
  testBad v j := if j < g v then layerBad v j else if j = g v then balBad v else if j = g v + 1 then tabBad v
    else flBad v
  pcsBad := pcsBad
  crBad := crBad

/-- The checks from the GKR's root to the opening meet `RecParts.Ok` where each check's test holds off its event:
each layer's (`Bind.layer_part`, off its sumcheck's, line and `λ` events), the balance's (`AirLink.balance_part`, off
`balDraws`), the table sumcheck's (`Bind.table_part`, off `sumcheckFalse`) and flock's reduction's; and the openings
are true off `pcsBad`. -/
theorem tableParts_ok (g : ι → ℕ) (vals tvals : ι → ℕ → Ω → Fin 2 → E) (tin fl opened : ι → Ω → Prop)
    (layerBad : ι → ℕ → Finset Ω) (balBad tabBad flBad pcsBad crBad : ι → Finset Ω) (held : ι → Ω → Prop)
    (hlayer : ∀ v j ω, j < g v → held v ω → ω ∉ crBad v → ω ∉ layerBad v j →
      vals v (j + 1) ω = tvals v (j + 1) ω → vals v j ω = tvals v j ω)
    (hbal : ∀ v ω, held v ω → ω ∉ crBad v → ω ∉ balBad v → tin v ω → vals v (g v) ω = tvals v (g v) ω)
    (htab : ∀ v ω, held v ω → ω ∉ crBad v → ω ∉ tabBad v → opened v ω → tin v ω)
    (hfl : ∀ v ω, held v ω → ω ∉ crBad v → ω ∉ flBad v → opened v ω → fl v ω)
    (hopen : ∀ v ω, ω ∉ pcsBad v → opened v ω) :
    (tableParts g vals tvals tin fl opened layerBad balBad tabBad flBad pcsBad crBad).Ok held where
  test v j ω hj hh hc hb ho := by
    simp only [tableParts] at hj hb ho ⊢
    by_cases h1 : j < g v
    · rw [if_pos h1] at hb ho
      rw [if_pos h1.le]
      exact hlayer v j ω h1 hh hc hb ho
    rw [if_neg h1] at hb ho
    by_cases h2 : j = g v
    · subst h2
      rw [if_pos rfl] at hb ho
      rw [if_pos le_rfl]
      exact hbal v _ hh hc hb ho
    rw [if_neg h2] at hb ho
    rw [if_neg (by omega)]
    by_cases h3 : j = g v + 1
    · rw [if_pos h3] at hb
      rw [if_pos h3]
      exact htab v ω hh hc hb ho
    rw [if_neg h3] at hb
    rw [if_neg h3]
    exact hfl v ω hh hc hb ho
  flow v j ω hj hp hin := by
    simp only [tableParts] at hj hin ⊢
    by_cases h1 : j < g v
    · rw [if_pos h1]
      have := hin (j + 1) (by omega) (by omega)
      rwa [if_pos (by omega : j + 1 ≤ g v)] at this
    rw [if_neg h1]
    by_cases h2 : j = g v
    · rw [if_pos h2]
      have := hin (g v + 1) (by omega) (by omega)
      rwa [if_neg (by omega), if_pos rfl] at this
    rw [if_neg h2]
    exact hopen v ω hp

/-- `ChecksGiveTable` from the checks from the GKR's root to the opening: child `v`'s parent accepts its certificate
and names the table sumcheck `tc v`; the GKR's root check's inputs (the root values true) are the named root being both
trees' honest roots, the table sumcheck's input is its input claim being its honest instance's sum on the committed
witness, flock's input is `Flocked`; the root's premise may use the parent's calls holding (`Bind.Facts`). The certificates are checked on the parent's states `tb`, whose satisfaction `t`'s gives (`hsat`). -/
theorem checksGiveTable_of_parts [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (g : ι → ℕ) (vals tvals : ι → ℕ → Ω → Fin 2 → E) (tin fl opened : ι → Ω → Prop)
    (layerBad : ι → ℕ → Finset Ω) (balBad tabBad flBad pcsBad crBad : ι → Finset Ω)
    (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → AirLink.Quad) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K) (bc : ι → Bind.Cert) (tc : ι → Bind.TableCert)
    (tb : ι → State) (hsat : ∀ v st val', Sat st (t v) val' → Sat st (tb v) val')
    (hnamed : ∀ v ∈ T.nodes, v ≠ T.root → (bc (T.parent v)).accepts (tb (T.parent v)) = true ∧
      (tc v).ok (bc (T.parent v)) (bc (T.parent v)).outs = true)
    (hxi : ∀ v ω, (bdraw v ω).2 = Model.ev (val (T.parent v) ω) (tc v).xi)
    (hT : ∀ v ω sc, (bc (T.parent v)).sumchecks[(tc v).sc]? = some sc → tin v ω →
      Model.ev (val (T.parent v) ω) sc.claim0 =
        (AirLink.tableInst (n v) (AirLink.witAt T cert t slot stRoot val taus cols v ω) (bdraw v ω).1
          (qforms v ω (bdraw v ω).1) (bdraw v ω).2).sum)
    (hG : ∀ v ω, Bind.Facts (bc (T.parent v)).calls (bc (T.parent v)).relax (bc (T.parent v)).outs
        (treeStmt T cert slot stRoot val (T.parent v) ω) (val (T.parent v) ω) → vals v 0 ω = tvals v 0 ω →
      Model.ev (val (T.parent v) ω) (tc v).root =
        AirLink.pullRoot (t v) (AirLink.witAt T cert t slot stRoot val taus cols v ω) (draw v ω) ∧
      Model.ev (val (T.parent v) ω) (tc v).root =
        AirLink.pushRoot (t v) (AirLink.witAt T cert t slot stRoot val taus cols v ω) (draw v ω))
    (hF : ∀ v ω, fl v ω → AirLink.Flocked (t v) (AirLink.witAt T cert t slot stRoot val taus cols v ω)) :
    AirLink.ChecksGiveTable T cert t os L slot stRoot val
      (tableParts g vals tvals tin fl opened layerBad balBad tabBad flBad pcsBad crBad) n bdraw qforms
      (fun v ω _ i => Model.ev (val (T.parent v) ω) (if i = 0 then (tc v).tot0 else (tc v).tot1))
      (fun v ω _ => Model.ev (val (T.parent v) ω) (tc v).root) draw taus cols :=
  AirLink.checksGiveTable_of_named T cert t os L slot stRoot val _ n bdraw qforms draw taus cols bc tc
    (fun v => g v + 1) (fun _ => 0) (fun v => g v + 2) tb hsat
    (fun v hv hne => ⟨(hnamed v hv hne).1, (hnamed v hv hne).2, by simp [tableParts], by simp [tableParts],
      by simp [tableParts]⟩)
    hxi
    (fun v ω sc hsc h => hT v ω sc hsc (by simpa [tableParts] using h))
    (fun v ω hf h => hG v ω hf (by simpa [tableParts] using h))
    (fun v ω h => hF v ω (by simpa [tableParts] using h))

end LeanVMCircuits.Rec.Edges
