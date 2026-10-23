import Sphincs.BridgePotentialA4

/-! One step of the cost-level comparison against the linear potential: every input class of a
fresh answer, guesses at parsed inputs, canonical continuations, reveals, draws and ticks. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

theorem msg_ne_chain {x : HashInput} (hx : ForestSigner.IsMsgInput x) {p : PublicParameter} {l : Index}
    {i : ChainIndex} {st : ChainStep} {v : Digest} : x ≠ chainInput p l i st v := by
  obtain ⟨p', call, payload, rfl⟩ := hx
  intro h
  have hd := (domain_eq_of_input h trivial trivial).1
  cases hd

theorem msg_ne_enc {x : HashInput} (hx : ForestSigner.IsMsgInput x) {p : PublicParameter} {l : LeafIndex}
    {m : Digest} {c : Counter} : x ≠ Wots.encodingInput p topLayer rootTree l m c := by
  obtain ⟨p', call, payload, rfl⟩ := hx
  intro h
  have hd := (domain_eq_of_input h trivial trivial).1
  cases hd

theorem msg_ne_fchain {x : HashInput} (hx : ForestSigner.IsMsgInput x) {p : PublicParameter} {f : FIn} :
    x ≠ f.input p := by
  obtain ⟨p', call, payload, rfl⟩ := hx
  intro h
  have hd := (domain_eq_of_input h trivial trivial).1
  cases hd

theorem input_chain (p : PublicParameter) (l : Index) (i : ChainIndex) (st : ChainStep) (v : Digest) :
    HiddenGraph.input p (Address.chain topLayer rootTree l i st, v) = chainInput p l i st v := rfl

theorem input_fchain (p : PublicParameter) (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx)
    (i : FChain) (t : FStep) (v : Digest) :
    HiddenGraph.input p (Address.fchain index c sp j a i t, v) = (FIn.mk index c sp j a i t v).input p := rfl

/-- A forest step is determined by the coordinate it reads and its payload. -/
theorem fin_eq_of_inC {f : FIn} {index : Index} {c : Coord} {sp : SuperIdx} {j : SubIdx} {a : ChildIdx}
    {i : FChain} {t : FStep} {v : Digest}
    (h : ((Address.fchain index c sp j a i t).inputCoordinate, v) = (f.inC, f.v)) :
    f = FIn.mk index c sp j a i t v := by
  obtain ⟨index', c', sp', j', a', i', t', v'⟩ := f
  simp only [Address.inputCoordinate, FIn.inC, Prod.mk.injEq, Coordinate.fchain.injEq, Fin.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ht⟩, rfl⟩ := h
  have : t' = t := Fin.ext ht.symm
  subst this
  rfl

namespace Ctx

variable (K : Ctx)

theorem kindUnit_le_one (x : HashInput) : K.kindUnit x ≤ 1 := by
  unfold kindUnit
  split_ifs <;> simp

theorem kindUnit_none {x : HashInput} (h : K.tg.kind x = .none) : K.kindUnit x = 0 := by
  unfold kindUnit
  rw [ite_eq_left h]

section Fresh

variable {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) {y' : ℕ} (hY : (y' : ℝ≥0∞) * ν ≤ ENNReal.ofReal xr)
  (hsec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none)

include hN hxr hY hsec in
/-- **A fresh answer without a guess.** -/
theorem fresh_zero {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) :
    ∑' r, Pr{let y ← readOutside x s}[y = r] * K.pot y' r.2 ≤ K.pot (y' + 1) s := by
  by_cases hA : ∃ l i, Landed K.p l ∧ K.IsA l i x
  · obtain ⟨l, i, hl, hA⟩ := hA
    simpa using K.fresh_A hN hinv hx hl hA (hsec x (K.secondOrder_of_isA hA)) (g := 0) bot_le
  by_cases hB : ∃ l i v, Landed K.p l ∧ K.IsB l i v x
  · obtain ⟨l, i, v, hl, hB⟩ := hB
    simpa using K.fresh_B hN hxr hY hinv hx hl hB (hsec x (K.secondOrder_of_isB hB)) (g := 0) bot_le
  by_cases hE : ∃ l msg ctr, Landed K.p l ∧ x = Wots.encodingInput K.p topLayer rootTree l msg ctr
  · obtain ⟨l, msg, ctr, hl, hxE⟩ := hE
    simpa using K.fresh_enc hN hxr hY hinv hx hl hxE (g := 0) (by rw [zero_add]; exact K.kindUnit_le_one x)
  by_cases hF : ∃ f : FIn, x = f.input K.p
  · obtain ⟨f, hxF⟩ := hF
    simpa using K.fresh_fchain hN hxr hY hinv hx hxF
      (hsec x (Or.inr ⟨f.index, f.c, f.s, f.j, f.a, f.i, f.t, f.v, hxF⟩)) (g := 0) bot_le (Or.inl rfl)
  have h := K.fresh_other hN (y' := y') hinv hx
    (fun l hl => ⟨fun i h => hA ⟨l, i, hl, h⟩, fun i v h => hB ⟨l, i, v, hl, h⟩⟩)
    (fun l msg ctr hl h => hE ⟨l, msg, ctr, hl, h⟩) (fun f h => hF ⟨f, h⟩) (w := 0)
    (by rw [zero_add]; exact (K.kindUnit_le_one x).trans (one_le_ofReal (by linarith [hN.low])))
  simpa using h

include hN in
/-- **A fresh message-digest query** pays the baseline from the rate. -/
theorem fresh_digest (hmsg : ∀ x, ForestSigner.IsMsgInput x → K.tg.kind x = .none) {s : St} (hinv : K.Inv s)
    {x : HashInput} (hx : s.cache x = none) (hd : ForestSigner.IsMsgInput x) :
    ∑' r, Pr{let y ← readOutside x s}[y = r] * K.pot y' r.2 + ν * ENNReal.ofReal K.ρ ≤ K.pot (y' + 1) s := by
  refine K.fresh_other hN hinv hx (fun l _ => ⟨fun i h => ?_, fun i v h => ?_⟩)
    (fun l msg ctr _ h => msg_ne_enc hd h) (fun f h => msg_ne_fchain hd h)
    (by rw [K.kindUnit_none (hmsg x hd), add_zero])
  · obtain ⟨st, pay, -, h⟩ := h
    exact msg_ne_chain hd h
  · obtain ⟨st, -, h⟩ := h
    exact msg_ne_chain hd h

include hN hxr hY hsec in
/-- **A guess at a fresh parsed input.** The guess pays one unit, the answer its class. -/
theorem guess_fresh {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) (q : Address × Digest)
    (hp : HiddenGraph.parse K.p (candidateActive K.p) x = some q) (hk : s.known q.1.inputCoordinate = none) :
    ∑' r, Pr{let y ← readOutside x (s.record (q.1.inputCoordinate, q.2))}[y = r] * K.pot y' r.2 ≤
      K.pot (y' + 1) s := by
  obtain ⟨rfl, hact⟩ := (parse_some_iff _ _ x q).1 hp
  obtain ⟨addr, v⟩ := q
  have hinv₁ := hinv.record (addr.inputCoordinate, v)
  have hx₁ : (s.record (addr.inputCoordinate, v)).cache (HiddenGraph.input K.p (addr, v)) = none := hx
  suffices main : ∑' r, Pr{let x ← (readOutside (HiddenGraph.input K.p (addr, v))
        (s.record (addr.inputCoordinate, v)))}[x = r] * K.pot y' r.2 + ν * 1 ≤
        K.pot (y' + 1) (s.record (addr.inputCoordinate, v)) ∧
      (∀ f : FIn, (addr.inputCoordinate, v) = (f.inC, f.v) → K.FE s f → (addr.inputCoordinate, v) ∈ s.guesses) by
    have hrec := K.pot_record (y' + 1) s (addr.inputCoordinate, v) hk main.2
    rw [mul_one] at main
    exact (ENNReal.add_le_add_iff_right ν_ne_top).1 (main.1.trans hrec)
  cases addr with
  | chain lay tree leaf chain step =>
      have hl : Landed K.p leaf := hact
      have hKF : ∀ f : FIn, ((Address.chain lay tree leaf chain step).inputCoordinate, v) = (f.inC, f.v) →
          K.FE s f → ((Address.chain lay tree leaf chain step).inputCoordinate, v) ∈ s.guesses :=
        fun f hg _ => by
          have := congrArg Prod.fst hg
          cases this
      refine ⟨?_, hKF⟩
      by_cases htop : lay = topLayer ∧ tree = rootTree
      · obtain ⟨rfl, rfl⟩ := htop
        have hnot : ¬(K.w leaf chain).val ≤ step.val := by
          intro hle
          have hanc : K.Anchor (Address.chain topLayer rootTree leaf chain step).inputCoordinate :=
            Or.inl ⟨rfl, rfl, hl, hle⟩
          rw [hinv.anchored _ hanc] at hk
          cases hk
        have hsecx : SecondOrderInput K.p K.R (chainInput K.p leaf chain step v) :=
          Or.inl ⟨topLayer, rootTree, leaf, chain, step, v, rfl, fun h => hnot h.2.2.2⟩
        have hkind := hsec _ hsecx
        rw [input_chain] at hx₁ ⊢
        by_cases h1 : step.val + 1 = (K.w leaf chain).val
        · exact K.fresh_B hN hxr hY hinv₁ hx₁ hl ⟨step, h1, rfl⟩ hkind le_rfl
        by_cases h2 : step.val + 2 = (K.w leaf chain).val
        · exact K.fresh_A hN hinv₁ hx₁ hl ⟨step, v, h2, rfl⟩ hkind le_rfl
        refine K.fresh_other hN hinv₁ hx₁ (fun l' _ => ⟨fun i' hA => ?_, fun i' v' hB => ?_⟩)
          (fun l' msg ctr _ => chainInput_ne_enc) (fun _ => chainInput_ne_fchain)
          (by rw [K.kindUnit_none hkind, add_zero]; exact one_le_ofReal (by linarith [hN.low]))
        · obtain ⟨st', pay', hst', heq⟩ := hA
          obtain ⟨rfl, rfl, rfl, -⟩ := chainInput_inj heq
          exact h2 hst'
        · obtain ⟨st', hst', heq⟩ := hB
          obtain ⟨rfl, rfl, rfl, -⟩ := chainInput_inj heq
          exact h1 hst'
      · have hsecx : SecondOrderInput K.p K.R (HiddenGraph.input K.p (Address.chain lay tree leaf chain step, v)) :=
          Or.inl ⟨lay, tree, leaf, chain, step, v, rfl, fun h => htop ⟨h.1, h.2.1⟩⟩
        have hkind := hsec _ hsecx
        have hdom : ∀ (l' : Index) (i' : ChainIndex) (st' : ChainStep) (v' : Digest),
            HiddenGraph.input K.p (Address.chain lay tree leaf chain step, v) ≠ chainInput K.p l' i' st' v' := by
          intro l' i' st' v' heq
          have hd : HashDomain.chain lay tree leaf chain step = HashDomain.chain topLayer rootTree l' i' st' :=
            (domain_eq_of_input heq trivial trivial).1
          simp only [HashDomain.chain.injEq] at hd
          exact htop ⟨hd.1, hd.2.1⟩
        refine K.fresh_other hN hinv₁ hx₁ (fun l' _ => ⟨fun i' hA => ?_, fun i' v' hB => ?_⟩)
          (fun l' msg ctr _ heq => ?_) (fun _ heq => ?_)
          (by rw [K.kindUnit_none hkind, add_zero]; exact one_le_ofReal (by linarith [hN.low]))
        · obtain ⟨st', pay', -, heq⟩ := hA
          exact hdom _ _ _ _ heq
        · obtain ⟨st', -, heq⟩ := hB
          exact hdom _ _ _ _ heq
        · have hd := (domain_eq_of_input heq trivial trivial).1
          cases hd
        · have hd := (domain_eq_of_input heq trivial trivial).1
          cases hd
  | fchain index c sp j a i t =>
      have hKF : ∀ f : FIn, ((Address.fchain index c sp j a i t).inputCoordinate, v) = (f.inC, f.v) →
          K.FE s f → ((Address.fchain index c sp j a i t).inputCoordinate, v) ∈ s.guesses := by
        intro f hg hfe
        exfalso
        obtain ⟨w, hfr⟩ := hfe
        rw [fin_eq_of_inC hg] at hfr
        have h1 := hfr.1
        change s.cache (HiddenGraph.input K.p (Address.fchain _ _ _ _ _ _ _, _)) = some w at h1
        rw [hx] at h1
        cases h1
      refine ⟨?_, hKF⟩
      have hkind := hsec _ (Or.inr ⟨index, c, sp, j, a, i, t, v, rfl⟩)
      rw [input_fchain] at hx₁ ⊢
      exact K.fresh_fchain hN hxr hY hinv₁ hx₁ rfl hkind le_rfl (Or.inr List.mem_cons_self)

end Fresh

/-- **A guess at a cached parsed input** records a guess that is already pending. -/
theorem guess_cached {xr : ℝ} (hN : Numeric K.ρ xr) (y' : ℕ) {s : St} (hinv : K.Inv s) {x : HashInput}
    {u : HashOutput} (hc : s.cache x = some u) (q : Address × Digest)
    (hp : HiddenGraph.parse K.p (candidateActive K.p) x = some q) (hk : s.known q.1.inputCoordinate = none) :
    K.pot y' (s.record (q.1.inputCoordinate, q.2)) ≤ K.pot (y' + 1) s := by
  obtain ⟨rfl, -⟩ := (parse_some_iff _ _ x q).1 hp
  have hKF : ∀ f : FIn, (q.1.inputCoordinate, q.2) = (f.inC, f.v) → K.FE s f →
      (q.1.inputCoordinate, q.2) ∈ s.guesses := by
    intro f hg hfe
    obtain ⟨addr, v⟩ := q
    cases addr with
    | chain lay tree' leaf' chain step =>
        have := congrArg Prod.fst hg
        cases this
    | fchain index c sp j a i t =>
        obtain ⟨w, hfr⟩ := hfe
        rw [fin_eq_of_inC hg] at hfr
        exact hinv.guessed _ w _ hfr hp hk
  calc K.pot y' (s.record (q.1.inputCoordinate, q.2)) ≤ K.pot y' s + ν := K.pot_record y' s _ hk hKF
    _ ≤ K.pot y' s + ν * K.rate s := add_le_add le_rfl (by
        calc ν = ν * 1 := (mul_one ν).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (K.one_le_rate hN s) bot_le)
    _ = _ := (K.pot_succ y' s).symm

end Ctx

end Sphincs.Security.PotentialA
