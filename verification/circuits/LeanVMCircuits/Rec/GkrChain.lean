module

public import LeanVMCircuits.Rec.SideCert

@[expose] public section

/-!
The bus GKR's layers from the root to the leaves on the named certificates (`GkrCert`), stage by stage.

Stage `0` of a table sumcheck's bus GKR is its first layer's values (the root, read as both trees' value), stage `1` the first layer's next claims and stage `k + 2` layer `k`'s next claims (`GkrCert.outsAt`). Stage `k`'s point is where its values are claimed (`GkrCert.ptAt`, its wires; `GkrCert.ptR`, the oracle's challenges): none at the root, the first layer's `low` and `high` (a top layer) or its next challenge (an odd layer), then each layer's `low`, `high` and its sumcheck's rounds'. `LayerCert.chain_at`: a passing chain links layer `k` to stage `k + 1`'s wires, and its result is the last stage. `GkrCert.ptAt_ev`: where the calls hold and the transcripts' squeezes answer the oracle, the stages' point wires are the oracle's challenges (`chal_readR`).

The steps, each a check of `RecParts` on a product tree with leaves `leaf t` over `μ` variables: `top_step` and `odd_step` (the first layer, `top_part`, `odd_part`) and `layer_step` (`layer_part`) make stage `k`'s values the tree's level at stage `k`'s point (`mleL`) from stage `k + 1`'s, off each layer's event. At the leaves the level at the last point is the sides' leaf claim (`mleL_rowEq`).
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Finset Sumcheck

/-- A level's value at a point given as a list: its multilinear extension at the list's coordinates. -/
noncomputable def mleL (l : List E) (W : ℕ → E) : E := mleAt l.length (fun j => l.getD j 0) W

theorem mleL_eq (l : List E) {n : ℕ} (h : l.length = n) (W : ℕ → E) :
    mleL l W = mleAt n (fun j : Fin n => l.getD j 0) W := by
  subst h
  rfl

theorem mleL_nil (W : ℕ → E) : mleL [] W = W 0 := mleAt_zero _ W

theorem mleL_one (a : E) (W : ℕ → E) : mleL [a] W = Bind.lineE (W 0) (W 1) a := by
  rw [mleL_eq [a] rfl, ← odd_next]
  congr 1
  funext j
  fin_cases j
  rfl

theorem mleL_two (a b : E) (W : ℕ → E) :
    mleL [a, b] W = Bind.lineE (Bind.lineE (W 0) (W 1) a) (Bind.lineE (W 2) (W 3) a) b := by
  have e : ∀ c, MvPolynomial.eval (Fin.elim0 : Fin 0 → E) (childMle 0 W c) = W c := fun c => by
    rw [eval_childMle_eq, mleAt_zero]
    simp
  rw [mleL_eq [a, b] (n := 2) rfl, show (fun j : Fin 2 => [a, b].getD j 0) = Fin.cons a (Fin.cons b Fin.elim0) by
    funext j; fin_cases j <;> rfl, next_claim 0 W a b Fin.elim0, e, e, e, e]

theorem mleL_cons2 (a b : E) {n : ℕ} (r : Fin n → E) (W : ℕ → E) :
    mleL ([a, b] ++ List.ofFn r) W = mleAt (n + 2) (Fin.cons a (Fin.cons b r)) W := by
  rw [mleL_eq _ (n := n + 2) (by simp)]
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j
  · rfl
  · rfl
  · simp [List.getD_eq_getElem?_getD, Fin.cons_succ]

/-- In characteristic two `eq` of a point and a row's bits is `rowEq`. -/
theorem eqv_bitPoint {n : ℕ} (p : Fin n → E) (x : ℕ) : eqv p (bitPoint n x) = rowEq p n x := by
  simp only [eqv, rowEq]
  refine prod_congr rfl fun j _ => ?_
  by_cases hb : x.testBit j = true <;> simp [j.isLt, hb, bitPoint, one_sub_eq_one_add]

/-- The level at the leaves at a point is the leaves' `rowEq`-weighted sum: the sides' leaf claim's form. -/
theorem mleL_rowEq (l : List E) {n : ℕ} (h : l.length = n) (ζ : Fin n → E) (hζ : ∀ j : Fin n, ζ j = l.getD j 0)
    (W : ℕ → E) : mleL l W = ∑ x ∈ range (2 ^ n), rowEq ζ n x * W x := by
  rw [mleL_eq l h, mleAt]
  refine sum_congr rfl fun x _ => ?_
  rw [show (fun j : Fin n => l.getD j 0) = ζ from funext fun j => (hζ j).symm, eqv_bitPoint]

end LeanVMCircuits.Rec.AirLink

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Finset AirLink

/-- A challenge family drawn in order from a transcript reads the oracle: where the calls hold and the transcript's squeezes answer the oracle, each challenge's wire is the oracle's challenge (`ChalCert.read` of its own words). -/
theorem chal_readR {s : State} {t : Transcript} {os : Array (List ℕ)} {cs : Array Call} {rl : Array Bool}
    {st : ℕ → Fin 4 → K} {val : Val} {ρ : ℕ → K} {strict : Bool} {n : ℕ} {cc : Fin n → ChalCert}
    (hch : chalsOk s os t strict (List.ofFn cc) = true) (hok : ∀ i, (cc i).ok s os cs t.blocks = true)
    (hF : Facts cs rl os st val) (hans : ∀ p ∈ chalSeeds s t, nu val p.2 = ρ p.2) (i : Fin n) :
    Model.ev val (cc i).chal = readR (chalWords os cc) ρ i := by
  obtain ⟨hown, -, -, -, hp⟩ := chalsOk_sem hch fun i => ChalCert.ok_words (hok i)
  rw [ChalCert.read (hok i) (hp i) hF]
  simp only [readR, chalWords]
  have e : ∀ k : Fin 3, nu val (((cc i).own os).getD k 0) = ρ (((cc i).own os).getD k 0) :=
    fun k => hans _ (hown i k).1
  exact congrArg₂ (fun a b => toE a b _) (e 0) (e 1) ▸ congrArg (toE _ _) (e 2)

/-! The stages of a chain of layers. -/

/-- Stage `k` of a chain of layers from next claims `outs`: `outs`, then layer `k - 1`'s next claims. -/
def LayerCert.outsN (os : Array (List ℕ)) (layers : List LayerCert) (outs : List ℕ) : ℕ → List ℕ
  | 0 => outs
  | k + 1 => (List.range 2).map ((layers.getD k default).layer.out os)

/-- Stage `k`'s point wires: `pt`, then layer `k - 1`'s `low`, `high` and its sumcheck's rounds' challenges. -/
def LayerCert.ptN (scs : Array SumcheckCert) (layers : List LayerCert) (pt : List ℕ) : ℕ → List ℕ
  | 0 => pt
  | k + 1 => [(layers.getD k default).layer.low.chal, (layers.getD k default).layer.high.chal] ++
      (scs.getD (layers.getD k default).sc default).rounds.map (·.chal)

/-- A passing chain links each layer to its stage: layer `k` to stage `k`'s next claims and point, and its result is the last stage. -/
theorem LayerCert.chain_at {scs : Array SumcheckCert} {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} :
    ∀ (layers : List LayerCert) (outs pt last : List ℕ), LayerCert.chain scs cs rl os layers outs pt = some last →
      (∀ k < layers.length, ∃ sc, scs[(layers.getD k default).sc]? = some sc ∧
        (layers.getD k default).linkOk sc os (LayerCert.outsN os layers outs k) (LayerCert.ptN scs layers pt k) = true ∧
        (layers.getD k default).layer.ok os cs rl = true ∧ (layers.getD k default).layer.m = 2) ∧
      last = LayerCert.outsN os layers outs layers.length
  | [], outs, pt, last, h => by
    simp only [LayerCert.chain, Option.some.injEq] at h
    exact ⟨fun k hk => absurd hk (Nat.not_lt_zero k), h.symm⟩
  | lc :: rest, outs, pt, last, h => by
    obtain ⟨sc, hsc, hlink, hok, hm, hrest⟩ := LayerCert.chain_cons h
    obtain ⟨ih, hlast⟩ := LayerCert.chain_at rest _ _ last hrest
    have ho : ∀ k, LayerCert.outsN os (lc :: rest) outs (k + 1) =
        LayerCert.outsN os rest ((List.range 2).map (lc.layer.out os)) k := fun k => by
      cases k <;> rfl
    have hp : ∀ k, LayerCert.ptN scs (lc :: rest) pt (k + 1) =
        LayerCert.ptN scs rest ([lc.layer.low.chal, lc.layer.high.chal] ++ sc.rounds.map (·.chal)) k := fun k => by
      cases k
      · simp [LayerCert.ptN, Array.getD_eq_getD_getElem?, hsc]
      · rfl
    refine ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero => exact ⟨sc, hsc, hlink, hok, hm⟩
      | succ k =>
        simp only [List.getD_cons_succ]
        rw [ho, hp]
        exact ih k (by simp at hk; omega)
    · rw [hlast, List.length_cons, ho]

/-- The first layer's point, the oracle's challenges: an odd layer's next challenge, a top layer's `low` and `high`. -/
noncomputable def GkrCert.firstPt (g : GkrCert) (c : Cert) (ρ : ℕ → K) : List E :=
  if g.odd then [readR (chalWords c.outs (c.odds.getD g.first default).chals) ρ 1]
  else [readR (chalWords c.outs (c.tops.getD g.first default).chals) ρ 1,
    readR (chalWords c.outs (c.tops.getD g.first default).chals) ρ 2]

/-- A layer's next point, the oracle's challenges: its `low` and `high`, then its sumcheck's rounds'. -/
noncomputable def LayerCert.nextPt (lc : LayerCert) (c : Cert) (ρ : ℕ → K) : List E :=
  [readR (chalWords c.outs lc.layer.chals) ρ 1, readR (chalWords c.outs lc.layer.chals) ρ 2] ++
    List.ofFn (readR (chalWords c.outs (c.sumchecks.getD lc.sc default).chals) ρ)

/-- Stage `k`'s values' wires: the first layer's values, its next claims, then layer `k - 2`'s next claims. -/
def GkrCert.outsAt (g : GkrCert) (c : Cert) : ℕ → List ℕ
  | 0 => (g.start c.tops c.odds c.outs).1
  | k + 1 => LayerCert.outsN c.outs g.layers (g.start c.tops c.odds c.outs).2.1 k

/-- Stage `k`'s point's wires. -/
def GkrCert.ptAt (g : GkrCert) (c : Cert) : ℕ → List ℕ
  | 0 => []
  | k + 1 => LayerCert.ptN c.sumchecks g.layers (g.start c.tops c.odds c.outs).2.2 k

/-- Stage `k`'s point as the oracle's challenges. -/
noncomputable def GkrCert.ptR (g : GkrCert) (c : Cert) (ρ : ℕ → K) : ℕ → List E
  | 0 => []
  | 1 => g.firstPt c ρ
  | k + 2 => (g.layers.getD k default).nextPt c ρ

theorem GkrCert.ptR_length (g : GkrCert) (c : Cert) (ρ : ℕ → K) (k : ℕ) :
    (g.ptR c ρ k).length = (g.ptAt c k).length := by
  match k with
  | 0 => rfl
  | 1 =>
    simp only [GkrCert.ptR, GkrCert.ptAt, LayerCert.ptN, GkrCert.firstPt, GkrCert.start]
    cases g.odd <;> simp
  | k + 2 => simp [GkrCert.ptR, GkrCert.ptAt, LayerCert.ptN, LayerCert.nextPt]

/-- Along a passing chain each stage's point is two coordinates longer than the one before. -/
theorem GkrCert.ptAt_length {g : GkrCert} {c : Cert} {last : List ℕ}
    (h : LayerCert.chain c.sumchecks c.calls c.relax c.outs g.layers (g.start c.tops c.odds c.outs).2.1
      (g.start c.tops c.odds c.outs).2.2 = some last) :
    ∀ k ≤ g.layers.length, (g.ptAt c (k + 1)).length = (g.ptAt c 1).length + 2 * k := by
  obtain ⟨hl, -⟩ := LayerCert.chain_at _ _ _ _ h
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨sc, hsc, hlink, -, -⟩ := hl k (by omega)
    have hw := congrArg List.length (LayerCert.link_sem hlink).2.2.2.2.1
    simp only [List.length_map] at hw
    have hgd : c.sumchecks.getD (g.layers.getD k default).sc default = sc := by
      rw [Array.getD_eq_getD_getElem?, hsc, Option.getD_some]
    have ih' := ih (by omega)
    simp only [GkrCert.ptAt, LayerCert.ptN, hgd, List.length_append, List.length_cons, List.length_nil,
      List.length_map] at ih' hw ⊢
    omega

/-- The last stage's point is the bus GKR's last point (`GkrCert.point`, the sides' point). -/
theorem GkrCert.point_eq {g : GkrCert} {c : Cert} {last : List ℕ}
    (h : LayerCert.chain c.sumchecks c.calls c.relax c.outs g.layers (g.start c.tops c.odds c.outs).2.1
      (g.start c.tops c.odds c.outs).2.2 = some last) :
    g.point c.sumchecks c.tops c.odds c.outs = g.ptAt c (g.layers.length + 1) := by
  obtain ⟨hl, -⟩ := LayerCert.chain_at _ _ _ _ h
  unfold GkrCert.point
  rcases hL : g.layers.length with _ | k
  · rw [List.length_eq_zero_iff] at hL
    simp [hL, GkrCert.ptAt, LayerCert.ptN]
  · obtain ⟨sc, hsc, -⟩ := hl k (by omega)
    have hlast : g.layers.getLast? = some (g.layers.getD k default) := by
      rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, hL]
      simp [List.getElem?_eq_getElem (show k < g.layers.length by omega)]
    have hgd : c.sumchecks.getD (g.layers.getD k default).sc default = sc := by
      rw [Array.getD_eq_getD_getElem?, hsc, Option.getD_some]
    rw [hlast]
    simp only [GkrCert.ptAt, LayerCert.ptN, hsc, hgd, Option.map_some, Option.getD_some]

/-- Where the calls hold, each transcript's squeezes answer the oracle and each certified sumcheck reads its rounds' challenges from it, a passing bus GKR's stages' point wires are the oracle's challenges. -/
theorem GkrCert.ptAt_ev {g : GkrCert} {tc : TableCert} {c : Cert} {s : State} {st : ℕ → Fin 4 → K} {val : Val}
    {ρ : ℕ → K} (hacc : c.accepts s = true) (hF : Facts c.calls c.relax c.outs st val)
    (hans : ∀ T, ∀ p ∈ chalSeeds s (c.transcripts.getD T default), nu val p.2 = ρ p.2)
    (hsc : ∀ sc ∈ c.sumchecks, ∀ j : Fin sc.rounds.length,
      Model.ev val (sc.rounds.getD j default).chal = readR (chalWords c.outs sc.chals) ρ j)
    (hg : g.okIn tc c.sumchecks c.tops c.odds c.calls c.relax c.outs = true) (hlay : g.layersOk c s c.outs = true) :
    ∀ k ≤ g.layers.length, (g.ptAt c (k + 1)).map (Model.ev val) = g.ptR c ρ (k + 1) := by
  obtain ⟨-, v0, v1, hch, -⟩ := GkrCert.sem hF hg
  obtain ⟨hl, -⟩ := LayerCert.chain_at _ _ _ _ hch
  have hfirst : g.first < if g.odd then c.odds.size else c.tops.size := by
    unfold GkrCert.okIn at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg.1.1
  intro k hk
  match k with
  | 0 =>
    simp only [GkrCert.ptAt, LayerCert.ptN, GkrCert.ptR, GkrCert.firstPt, GkrCert.start]
    cases hodd : g.odd
    · rw [hodd] at hfirst
      simp only [Bool.false_eq_true, ↓reduceIte] at hfirst ⊢
      have hm : c.tops.getD g.first default ∈ c.tops := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hfirst, Option.getD_some]
        exact Array.getElem_mem hfirst
      obtain ⟨hc, hok⟩ := Cert.top_chals hacc hm
      have e := chal_readR hc hok hF (hans _)
      simp only [List.map_cons, List.map_nil]
      rw [show (c.tops.getD g.first default).low = (c.tops.getD g.first default).chals 1 from rfl,
        show (c.tops.getD g.first default).high = (c.tops.getD g.first default).chals 2 from rfl, e, e]
    · rw [hodd] at hfirst
      simp only [↓reduceIte] at hfirst ⊢
      have hm : c.odds.getD g.first default ∈ c.odds := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hfirst, Option.getD_some]
        exact Array.getElem_mem hfirst
      obtain ⟨hc, hok⟩ := Cert.odd_chals hacc hm
      have e := chal_readR hc hok hF (hans _)
      simp only [List.map_cons, List.map_nil]
      rw [show (c.odds.getD g.first default).next = (c.odds.getD g.first default).chals 1 from rfl, e]
  | k + 1 =>
    obtain ⟨sc, hsc', -⟩ := hl k (by omega)
    have hmem : g.layers.getD k default ∈ g.layers := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < g.layers.length by omega),
        Option.getD_some]
      exact List.getElem_mem _
    have hlc : (g.layers.getD k default).chalOk c s c.outs = true := by
      simp only [GkrCert.layersOk, List.all_eq_true] at hlay
      exact hlay _ hmem
    obtain ⟨-, hc, hok, -, -⟩ := LayerCert.chal_sem hlc
    have e := chal_readR hc hok hF (hans _)
    have hgd : c.sumchecks.getD (g.layers.getD k default).sc default = sc := by
      rw [Array.getD_eq_getD_getElem?, hsc', Option.getD_some]
    have hscm : sc ∈ c.sumchecks := Array.mem_of_getElem? hsc'
    subst hgd
    simp only [GkrCert.ptAt, LayerCert.ptN, GkrCert.ptR, LayerCert.nextPt, List.map_append, List.map_cons,
      List.map_nil, List.map_map]
    rw [show (g.layers.getD k default).layer.low = (g.layers.getD k default).layer.chals 1 from rfl,
      show (g.layers.getD k default).layer.high = (g.layers.getD k default).layer.chals 2 from rfl, e, e]
    congr 1
    rw [← ofFn_getD_map]
    exact congrArg List.ofFn (funext fun j => hsc _ hscm j)

/-! The steps. -/

/-- A top first layer as a check: where its test holds and its next claims are each tree's level two below the root at `[low, high]`, its values are the roots, off `topFalse` at the true children. -/
theorem top_step {c : Cert} {s : State} {tc : TopCert} {val : (ℕ → K) → Val} (ρ : ℕ → K) (leaf : ℕ → ℕ → E)
    {μ : ℕ} (hμ : 2 ≤ μ) (hm : tc.m = 2) (htest : ∀ a b, s.unions[tc.test]? = some (a, b) → val ρ a = val ρ b)
    (hnext : ∀ t < 2, Model.ev (val ρ) (tc.out c.outs t) = mleL [readR (chalWords c.outs tc.chals) ρ 1,
      readR (chalWords c.outs tc.chals) ρ 2] (level (leaf t) (μ - 2)))
    (hnot : ¬ topFalse c s tc (fun t i => level (leaf t) (μ - 2) i) val ρ) :
    ∀ t < 2, Model.ev (val ρ) (tc.values.getD t 0) = mleL [] (level (leaf t) μ) := by
  intro t ht
  have := top_part ρ htest (fun k hk => by rw [hnext k (hm ▸ hk), mleL_two]) hnot t (hm ▸ ht)
  rw [this, mleL_nil, show μ = μ - 2 + 2 by omega, level_four]
  simp [Finset.prod_range_succ, mul_assoc]

/-- An odd first layer as a check: where its test holds and its next claims are each tree's level one below the root at `[r]`, its values are the roots, off `oddFalse` at the true children. -/
theorem odd_step {c : Cert} {s : State} {oc : OddCert} {val : (ℕ → K) → Val} (ρ : ℕ → K) (leaf : ℕ → ℕ → E)
    {μ : ℕ} (hμ : 1 ≤ μ) (hm : oc.m = 2) (htest : ∀ a b, s.unions[oc.test]? = some (a, b) → val ρ a = val ρ b)
    (hnext : ∀ t < 2, Model.ev (val ρ) (oc.out c.outs t) =
      mleL [readR (chalWords c.outs oc.chals) ρ 1] (level (leaf t) (μ - 1)))
    (hnot : ¬ oddFalse c s oc (fun t => level (leaf t) (μ - 1) 0) (fun t => level (leaf t) (μ - 1) 1) val ρ) :
    ∀ t < 2, Model.ev (val ρ) (oc.values.getD t 0) = mleL [] (level (leaf t) μ) := by
  intro t ht
  have := odd_part ρ htest (fun k hk => by rw [hnext k (hm ▸ hk), mleL_one]; rfl) hnot t (hm ▸ ht)
  rw [this, mleL_nil, show μ = μ - 1 + 1 by omega, level_two]
  simp

/-- A radix-four layer as a check: where the calls hold, the layer is linked to stage `outs` at point wires `pt`, its test holds, its challenges read the oracle and its next claims are each tree's level below at its next point, its values are each tree's level at `p` (the previous point's challenges), off its sumcheck's event against `layerInst` and its `λ` and line events (`Bind.layerBad`). Its sumcheck reads no hints (`LayerCert.linkOk`). -/
theorem layer_step {c : Cert} {s : State} {lc : LayerCert} {sc : SumcheckCert} {st : ℕ → Fin 4 → K}
    {val : (ℕ → K) → Val} {outs pt : List ℕ} (ρ : ℕ → K) (hF : Facts c.calls c.relax c.outs st (val ρ))
    (hlink : lc.linkOk sc c.outs outs pt = true) (hok : lc.layer.ok c.outs c.calls c.relax = true)
    (hm : lc.layer.m = 2) (leaf : ℕ → ℕ → E) {μ : ℕ} (p : List E)
    (hp : p.length = sc.rounds.length) (hμ : sc.rounds.length + 2 ≤ μ)
    (htest : ∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b)
    (hchal : ∀ i, Model.ev (val ρ) (lc.layer.chals i).chal = readR (chalWords c.outs lc.layer.chals) ρ i)
    (hnext : ∀ t < 2, Model.ev (val ρ) (lc.layer.out c.outs t) =
      mleL ([readR (chalWords c.outs lc.layer.chals) ρ 1, readR (chalWords c.outs lc.layer.chals) ρ 2] ++
        List.ofFn (readR (chalWords c.outs sc.chals) ρ)) (level (leaf t) (μ - (sc.rounds.length + 2))))
    (hnot : ¬ (sumcheckFalse c s sc (layerInst sc.rounds.length (fun j => p.getD j 0)
        (readR (chalWords c.outs lc.layer.chals) ρ 0) fun t => level (leaf t) (μ - (sc.rounds.length + 2)))
          (fun _ => 0) val ρ ∨
      layerBad c lc (fun t => mleAt sc.rounds.length (fun j => p.getD j 0) fun z =>
          ∏ c ∈ range 4, level (leaf t) (μ - (sc.rounds.length + 2)) (4 * z + c))
        (fun t i => MvPolynomial.eval (readR (chalWords c.outs sc.chals) ρ)
          (childMle sc.rounds.length (level (leaf t) (μ - (sc.rounds.length + 2))) i)) val ρ)) :
    ∀ t < 2, Model.ev (val ρ) (outs.getD t 0) = mleL p (level (leaf t) (μ - p.length)) := by
  have hlam0 : Model.ev (val ρ) lc.layer.lam.chal = readR (chalWords c.outs lc.layer.chals) ρ 0 := hchal 0
  have hlo : Model.ev (val ρ) lc.layer.low.chal = readR (chalWords c.outs lc.layer.chals) ρ 1 := hchal 1
  have hhi : Model.ev (val ρ) lc.layer.high.chal = readR (chalWords c.outs lc.layer.chals) ρ 2 := hchal 2
  have hvals : lc.layer.values = outs := (LayerCert.link_sem hlink).2.1
  have hhint : sc.hints = [] := (LayerCert.link_sem hlink).2.2.2.2.2
  rw [not_or] at hnot
  obtain ⟨hnS, hnL⟩ := hnot
  simp only [layerBad, not_or, lamBadAt, lineBadAt] at hnL
  obtain ⟨hnlam, hnl⟩ := hnL
  have := layer_part (T' := fun _ => 0) ρ hF hlink hok hm (fun j => p.getD j 0)
    (fun t => level (leaf t) (μ - (sc.rounds.length + 2))) htest (by simp [hhint])
    (fun t => by rw [hnext t t.isLt, hlo, hhi, mleL_cons2])
    (by rw [hlam0]; exact hnS) (by rw [hlam0, ← hvals]; exact hnlam)
    (by rw [hlo, hhi]; exact hnl)
  intro t ht
  rw [show outs.getD t 0 = outs.getD (⟨t, ht⟩ : Fin 2) 0 from rfl, this ⟨t, ht⟩, mleL_eq p hp]
  congr 1
  funext z
  rw [← level_four, hp]
  congr 1
  omega

/-! The sides' leaves. -/

/-- A side's stacked leaves (`SideCert.leafClaim`'s): each owned block's leaves over its table's committed rows, the framework blocks' over their public columns, padding elsewhere. -/
noncomputable def SideCert.stack (sc : SideCert) (val : Val) (pubF : Bool → ℕ → ℕ → E) (w : Witness) : ℕ → E :=
  stackLeaf (fun b => sc.blocks[b].kappa) (fun b => sc.blocks[b].q) fun b z =>
    if sc.blocks[b].owner = none then sc.leafOf val pubF b z
    else blockLeaf (Model.ev val sc.beta) (sc.tsOf val pubF b) (fun c => emb (w.cols (sc.blocks[b].owner.getD .emul) z c)) z

/-- A side's leaf claim is its stacked leaves' level at the leaves, at a point whose coordinates are the side's named point's values. -/
theorem SideCert.leafClaim_mleL (sc : SideCert) (val : Val) (pubF : Bool → ℕ → ℕ → E) (w : Witness) (l : List E)
    (hl : l.length = sc.mu) (hz : ∀ j : Fin sc.mu, Model.ev val (sc.zeta.getD j 0) = l.getD j 0) :
    sc.leafClaim val pubF w = mleL l (sc.stack val pubF w) := by
  rw [mleL_rowEq l hl (sc.zetaV val) hz]
  rfl

end LeanVMCircuits.Rec.Bind
