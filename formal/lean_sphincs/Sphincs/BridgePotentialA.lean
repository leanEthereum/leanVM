import Sphincs.BridgeImplicationA
import Sphincs.BridgeLinear
import Sphincs.BridgeTargeting

/-! A linear potential on the interpreted comparison for small budgets. Guesses and first-order
hits pay one unit per query. The WOTS second-order events (two edges into the frontier, a
contact with an encoding marker, two contacts at one leaf) and the forest contact events (a contact
without guess record, two contacts at different chains of one index) are paid by an armed rate, a
contact count, credits for two-edge pairs and a pair term. A forest step whose written coordinate
is still unexposed is latent: it becomes a contact with chance `2^-128` when that coordinate is
exposed, and the potential carries it at that weight. This file holds the definitions and how one
step of the lazy comparison changes them. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-- Comparison states of the candidate. -/
abbrev St := DebtState HashInput HashOutput Coordinate

/-- One digest's share of the space. -/
noncomputable def ν : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 128)⁻¹

/-- The fixed data of the potential: the truncated public parameter, the prepared search
results, the prepared cache, the values of the always-known coordinates, the targeting deciding
first-order hits (comparing truncated answers), and the plain rate. -/
structure Ctx where
  p : PublicParameter
  R : Index → Option (Counter × Encoding)
  initial : QueryCache HashSpec
  F : Coordinate → Digest
  tg : Targeting HashInput HashOutput Coordinate
  ρ : ℝ
  trunc_eq : tg.trunc = truncateHash

/-! ### Means over a uniform digest -/

/-- The mean of a function of a uniform digest. -/
noncomputable def meanD (G : Digest → ℝ≥0∞) : ℝ≥0∞ := ν * ∑ t, G t

theorem card_digest_ennreal : (Fintype.card Digest : ℝ≥0∞) = 2 ^ 128 := by
  rw [HiddenDebt.card_digest]
  norm_num

theorem ν_mul_space : ν * (2 ^ 128 : ℝ≥0∞) = 1 :=
  ENNReal.inv_mul_cancel (by simp) (by simp)

theorem ν_ne_top : ν ≠ ⊤ := by
  unfold ν
  simp

theorem probOutput_digest (t : Digest) : Pr{let x ← ($ᵗ Digest : ProbComp Digest)}[x = t] = ν := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, card_digest_ennreal]
  rfl

/-- The truncated answer of a uniform output is a uniform digest. -/
theorem mean_trunc (G : Digest → ℝ≥0∞) :
    ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] * G (truncateHash u) = meanD G := by
  rw [← OracleComp.tsum_prEvent_map_mul]
  have h : ∀ t, Pr{let x ← truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)}[x = t] = ν := by
    intro t
    rw [evalDist_truncateHash_uniform.prEvent_eq, probOutput_digest]
  simp only [h]
  rw [tsum_fintype, meanD, Finset.mul_sum]

theorem meanD_const (a : ℝ≥0∞) : meanD (fun _ => a) = a := by
  rw [meanD, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    show (Fintype.card Digest : ℝ≥0∞) = 2 ^ 128 from card_digest_ennreal, ν_mul_space, one_mul]

theorem meanD_add (G H : Digest → ℝ≥0∞) : meanD (fun t => G t + H t) = meanD G + meanD H := by
  simp only [meanD, Finset.sum_add_distrib, mul_add]

theorem meanD_mono {G H : Digest → ℝ≥0∞} (h : ∀ t, G t ≤ H t) : meanD G ≤ meanD H := by
  unfold meanD
  gcongr with t
  exact h t

theorem meanD_ite (P : Digest → Prop) [DecidablePred P] (a : ℝ≥0∞) :
    meanD (fun t => if P t then a else 0) = ν * (({t | P t}.encard : ℝ≥0∞) * a) := by
  have hS : {t | P t} = ((Finset.univ.filter P : Finset Digest) : Set Digest) := by
    ext t
    simp
  rw [meanD, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hS, Set.encard_coe_eq_coe_finsetCard,
    ENat.toENNReal_coe]

theorem meanD_ite_eq (v : Digest) (P : Digest → Prop) [DecidablePred P] (hP : ∀ t, P t ↔ t = v)
    (a : ℝ≥0∞) : meanD (fun t => if P t then a else 0) = ν * a := by
  rw [meanD_ite]
  have h : {t | P t} = {v} := by
    ext t
    simp [hP]
  rw [h, Set.encard_singleton, ENat.toENNReal_one, one_mul]

theorem meanD_ite_le (P : Digest → Prop) [DecidablePred P] (S : Finset Digest) (hP : ∀ t, P t → t ∈ S)
    (a : ℝ≥0∞) : meanD (fun t => if P t then a else 0) ≤ ν * ((S.card : ℝ≥0∞) * a) := by
  rw [meanD_ite]
  gcongr
  rw [← ENat.toENNReal_coe, ENat.toENNReal_le, ← Set.encard_coe_eq_coe_finsetCard]
  exact Set.encard_le_encard fun t ht => hP t ht

theorem encard_insert_le_ennreal {α : Type} (S : Set α) (a : α) :
    ((insert a S).encard : ℝ≥0∞) ≤ (S.encard : ℝ≥0∞) + 1 :=
  calc ((insert a S).encard : ℝ≥0∞) ≤ ((S.encard + 1 : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.2 (Set.encard_insert_le S a)
    _ = _ := by rw [ENat.toENNReal_add, ENat.toENNReal_one]

/-! ### Distinct input shapes -/

theorem domain_eq_of_input {p p' : PublicParameter} {d d' : HashDomain} {m m' : HashInput}
    (h : tweakableHashInput p d m = tweakableHashInput p' d' m') (hd : d.InRange) (hd' : d'.InRange) :
    d = d' ∧ m = m' :=
  ⟨hashFields_injective hd hd' (tweakableInput_injective h).1, (tweakableInput_injective h).2.2⟩

theorem chainInput_inj {p : PublicParameter} {l l' : Index} {i i' : ChainIndex} {st st' : ChainStep}
    {v v' : Digest} (h : chainInput p l i st v = chainInput p l' i' st' v') :
    l = l' ∧ i = i' ∧ st = st' ∧ v = v' := by
  obtain ⟨hd, hm⟩ := domain_eq_of_input h trivial trivial
  simp only [HashDomain.chain.injEq] at hd
  obtain ⟨-, -, rfl, rfl, rfl⟩ := hd
  exact ⟨rfl, rfl, rfl, bytesLE_injective hm⟩

theorem chainInput_ne_enc {p p' : PublicParameter} {l : Index} {i : ChainIndex} {st : ChainStep} {v : Digest}
    {lay : Layer} {tree : TreeIndex} {l' : LeafIndex} {m : Digest} {c : Counter} :
    chainInput p l i st v ≠ Wots.encodingInput p' lay tree l' m c := by
  intro h
  have hd := (domain_eq_of_input h trivial trivial).1
  cases hd

/-- A forest chain step query: the chain, the step and the payload. -/
structure FIn where
  index : Index
  c : Coord
  s : SuperIdx
  j : SubIdx
  a : ChildIdx
  i : FChain
  t : FStep
  v : Digest
  deriving DecidableEq

instance FIn.instFintype : Fintype FIn :=
  Fintype.ofEquiv (Index × Coord × SuperIdx × SubIdx × ChildIdx × FChain × FStep × Digest)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
        x.2.2.2.2.2.2.2⟩
      invFun := fun f => (f.index, f.c, f.s, f.j, f.a, f.i, f.t, f.v)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

attribute [irreducible] FIn.instFintype

namespace FIn

/-- The hash input of a forest chain step query. -/
def input (p : PublicParameter) (f : FIn) : HashInput := fchainInput p f.index f.c f.s f.j f.a f.i f.t f.v

/-- The coordinate read by the step. -/
def inC (f : FIn) : Coordinate := .fchain f.index f.c f.s f.j f.a f.i ⟨f.t.val, by omega⟩

/-- The coordinate written by the step. -/
def outC (f : FIn) : Coordinate := .fchain f.index f.c f.s f.j f.a f.i ⟨f.t.val + 1, by omega⟩

/-- Two steps at different chains (tree, subtree, chain) of one index. -/
def Rel (f g : FIn) : Prop := f.index = g.index ∧ (f.c, f.j, f.i) ≠ (g.c, g.j, g.i)

theorem rel_symm {f g : FIn} (h : f.Rel g) : g.Rel f := ⟨h.1.symm, fun e => h.2 e.symm⟩

/-- Related steps write different coordinates. -/
theorem outC_ne_of_rel {f g : FIn} (h : f.Rel g) : f.outC ≠ g.outC := by
  intro e
  simp only [outC, Coordinate.fchain.injEq] at e
  obtain ⟨-, hc, -, hj, -, hi, -⟩ := e
  exact h.2 (by rw [hc, hj, hi])

end FIn

theorem chainInput_ne_fchain {p p' : PublicParameter} {l : Index} {i : ChainIndex} {st : ChainStep} {v : Digest}
    {f : FIn} : chainInput p l i st v ≠ f.input p' := by
  intro h
  have hd := (domain_eq_of_input h trivial trivial).1
  cases hd

theorem enc_ne_fchain {p p' : PublicParameter} {lay : Layer} {tree : TreeIndex} {l : LeafIndex} {m : Digest}
    {c : Counter} {f : FIn} : Wots.encodingInput p lay tree l m c ≠ f.input p' := by
  intro h
  have hd := (domain_eq_of_input h trivial trivial).1
  cases hd

theorem enc_inj {p : PublicParameter} {l l' : LeafIndex} {m m' : Digest} {c c' : Counter}
    (h : Wots.encodingInput p topLayer rootTree l m c = Wots.encodingInput p topLayer rootTree l' m' c') :
    l = l' ∧ m = m' ∧ c = c' := by
  have hd := (domain_eq_of_input h trivial trivial).1
  simp only [HashDomain.encoding.injEq] at hd
  obtain ⟨-, -, rfl⟩ := hd
  exact ⟨rfl, Wots.encodingInput_injective p topLayer rootTree l h⟩

theorem fchain_inj {p : PublicParameter} {f g : FIn} (h : f.input p = g.input p) : f = g := by
  obtain ⟨hd, hm⟩ := domain_eq_of_input h trivial trivial
  simp only [HashDomain.fchain.injEq] at hd
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hd
  have hv := bytesLE_injective hm
  cases f; cases g
  simp_all

variable [Params]

namespace Ctx

variable (K : Ctx)

/-- The prepared word of a leaf. -/
noncomputable def w (l : Index) : Encoding := preparedWord K.R l

/-- A cache entry made during the run. -/
def Fr (s : St) (x : HashInput) (u : HashOutput) : Prop := s.cache x = some u ∧ K.initial x = none

/-- The frontier value of a chain: the value at the prepared word. -/
noncomputable def front (l : Index) (i : ChainIndex) : Digest :=
  K.F (.chain topLayer rootTree l i (K.w l i))

/-- A chain input two steps below the word. -/
def IsA (l : Index) (i : ChainIndex) (x : HashInput) : Prop :=
  ∃ (st : ChainStep) (payload : Digest), st.val + 2 = (K.w l i).val ∧ x = chainInput K.p l i st payload

/-- A chain input one step below the word, with its payload. -/
def IsB (l : Index) (i : ChainIndex) (v : Digest) (x : HashInput) : Prop :=
  ∃ st : ChainStep, st.val + 1 = (K.w l i).val ∧ x = chainInput K.p l i st v

/-- Truncated answers of fresh inputs two steps below the word. -/
def AAns (s : St) (l : Index) (i : ChainIndex) : Set Digest :=
  {t | ∃ x u, K.IsA l i x ∧ K.Fr s x u ∧ truncateHash u = t}

/-- Payloads of fresh inputs one step below the word. -/
def BPay (s : St) (l : Index) (i : ChainIndex) : Set Digest :=
  {v | ∃ x u, K.IsB l i v x ∧ K.Fr s x u}

/-- Payloads of fresh inputs one step below the word whose answer is the frontier. -/
def ContactB (s : St) (l : Index) (i : ChainIndex) : Set Digest :=
  {v | ∃ x u, K.IsB l i v x ∧ K.Fr s x u ∧ truncateHash u = K.front l i}

/-- Digests decoding to a unit neighbour of the prepared word lowering one chain. -/
noncomputable def markSet (l : Index) (i : ChainIndex) : Finset Digest :=
  decodingDigests (unitNeighbors (K.w l) i)

/-- Digests decoding to a unit neighbour of the prepared word. -/
noncomputable def markAll (l : Index) : Finset Digest := decodingDigests (allUnitNeighbors (K.w l))

/-- A fresh encoding answer of the leaf decodes to a unit neighbour lowering the chain. -/
def Marker (s : St) (l : Index) (i : ChainIndex) : Prop :=
  ∃ msg ctr u, K.Fr s (Wots.encodingInput K.p topLayer rootTree l msg ctr) u ∧ truncateHash u ∈ K.markSet l i

/-- The WOTS events of a leaf: an observed contact, a contact at a marked chain, or contacts at
two chains. -/
def BadLeaf (s : St) (l : Index) : Prop :=
  (∃ i, (K.ContactB s l i ∩ K.AAns s l i).Nonempty) ∨
  (∃ i, (K.ContactB s l i).Nonempty ∧ K.Marker s l i) ∨
  (∃ i i', i ≠ i' ∧ (K.ContactB s l i).Nonempty ∧ (K.ContactB s l i').Nonempty)

def WotsBad (s : St) : Prop := ∃ l, Landed K.p l ∧ K.BadLeaf s l

/-- A fresh entry of a forest chain step. -/
def FE (s : St) (f : FIn) : Prop := ∃ u, K.Fr s (f.input K.p) u

/-- A decided forest contact: a fresh step answer equal to the exposed value it writes. -/
def FC (s : St) (f : FIn) : Prop :=
  ∃ u w, K.Fr s (f.input K.p) u ∧ s.known f.outC = some w ∧ truncateHash u = w

/-- A latent forest step: a fresh step whose written coordinate is not exposed yet. -/
def Lat (s : St) (f : FIn) : Prop := K.FE s f ∧ s.known f.outC = none

/-- The step carries a guess record: its read coordinate was unexposed when it was asked. -/
def Recd (s : St) (f : FIn) : Prop := (f.inC, f.v) ∈ s.guesses

/-- The decided bad event. -/
def Bad (s : St) : Prop := Realized K.tg K.initial s ∨ K.WotsBad s

/-- Some landed leaf without a WOTS event has a marker or a contact. -/
def Armed (s : St) : Prop :=
  ∃ l, Landed K.p l ∧ ¬K.BadLeaf s l ∧ ((∃ i, K.Marker s l i) ∨ ∃ i, (K.ContactB s l i).Nonempty)

/-- Contacts at a leaf without a WOTS event. -/
noncomputable def leafCount (s : St) (l : Index) : ℝ≥0∞ :=
  if K.BadLeaf s l then 0 else ∑ i, ((K.ContactB s l i).encard : ℝ≥0∞)

noncomputable def contactCount (s : St) : ℝ≥0∞ := ∑ l, if Landed K.p l then K.leafCount s l else 0

/-- Inputs two steps below the word whose answer is no payload one step below. -/
def UAset (s : St) : Set HashInput :=
  {x | ∃ l i u, Landed K.p l ∧ K.IsA l i x ∧ K.Fr s x u ∧ truncateHash u ∉ K.BPay s l i}

/-- The contact weight of a forest step: one for a decided contact, `2^-128` for a latent step,
zero otherwise. -/
noncomputable def cw (s : St) (f : FIn) : ℝ≥0∞ := if K.FC s f then 1 else if K.Lat s f then ν else 0

/-- Weighted contacts without a guess record. -/
noncomputable def ng (s : St) : ℝ≥0∞ := ∑ f, if Recd s f then 0 else K.cw s f

/-- Weighted contacts with a guess record. -/
noncomputable def kf (s : St) : ℝ≥0∞ := ∑ f, if Recd s f then K.cw s f else 0

/-- Weighted ordered pairs of recorded contacts at different chains of one index. -/
noncomputable def pp (s : St) : ℝ≥0∞ :=
  ∑ f, ∑ g, if Recd s f ∧ Recd s g ∧ f.Rel g then K.cw s f * K.cw s g else 0

/-- Pending debts at unexposed coordinates. -/
noncomputable def pend (s : St) : ℝ≥0∞ :=
  ∑ c : Coordinate, if s.known c = none then ((debts K.tg K.initial s c).encard : ℝ≥0∞) * ν else 0

/-- The forest part: weighted contacts without record and half the weighted pairs. -/
noncomputable def latent (s : St) : ℝ≥0∞ := K.ng s + K.pp s / 2

/-- The armed rate. -/
noncomputable def vrate (s : St) : ℝ≥0∞ := if K.Armed s then 2 else ENNReal.ofReal K.ρ

/-- The rate per remaining unit of budget. -/
noncomputable def rate (s : St) : ℝ≥0∞ := K.vrate s + 64 * K.contactCount s + K.kf s

noncomputable def done (s : St) : ℝ≥0∞ := if K.Bad s then 1 else 0

/-- **The potential.** The decided bad event, the pending debts, the weighted forest contacts
without guess record and pairs of recorded ones, half a unit per input two steps below the word
whose answer is no payload one step below, and the remaining budget at the rate: 2 when armed and
`ρ` otherwise, 64 per contact at a leaf without a WOTS event, and the weighted recorded forest
contacts. -/
noncomputable def pot (y : ℕ) (s : St) : ℝ≥0∞ :=
  K.done s + K.pend s + K.latent s + ν / 2 * ((K.UAset s).encard : ℝ≥0∞) + ((y : ℝ≥0∞) * ν) * K.rate s

/-- The potential, infinite above the total budget. -/
noncomputable def potCap (total y : ℕ) (s : St) : ℝ≥0∞ := if y ≤ total then K.pot y s else ⊤

/-- A forest contact against a completed table. -/
def FCT (T : Coordinate → Digest) (s : St) (f : FIn) : Prop :=
  ∃ u, K.Fr s (f.input K.p) u ∧ truncateHash u = T f.outC

/-- The final payoff: a hit of the targeting, a WOTS event, or a forest contact without guess record
or two related forest contacts against the completed table. -/
noncomputable def payoff (T : Coordinate → Digest) (s : St) : ℝ≥0∞ :=
  if Hit K.tg K.initial T s ∨ K.WotsBad s ∨ (∃ f, K.FCT T s f ∧ ¬Recd s f) ∨
    (∃ f g, f.Rel g ∧ K.FCT T s f ∧ K.FCT T s g) then 1 else 0

/-! ### Shapes of the WOTS inputs -/

variable {K}

theorem isA_unique {l l' : Index} {i i' : ChainIndex} {x : HashInput} (h : K.IsA l i x) (h' : K.IsA l' i' x) :
    l = l' ∧ i = i' := by
  obtain ⟨st, pay, -, rfl⟩ := h
  obtain ⟨st', pay', -, heq⟩ := h'
  obtain ⟨hl, hi, -, -⟩ := chainInput_inj heq
  exact ⟨hl, hi⟩

theorem isB_unique {l l' : Index} {i i' : ChainIndex} {v v' : Digest} {x : HashInput} (h : K.IsB l i v x)
    (h' : K.IsB l' i' v' x) : l = l' ∧ i = i' ∧ v = v' := by
  obtain ⟨st, -, rfl⟩ := h
  obtain ⟨st', -, heq⟩ := h'
  obtain ⟨hl, hi, -, hv⟩ := chainInput_inj heq
  exact ⟨hl, hi, hv⟩

theorem isB_input {l : Index} {i : ChainIndex} {v : Digest} {x y : HashInput} (h : K.IsB l i v x)
    (h' : K.IsB l i v y) : x = y := by
  obtain ⟨st, hst, rfl⟩ := h
  obtain ⟨st', hst', rfl⟩ := h'
  have : st = st' := Fin.ext (by omega)
  rw [this]

theorem isA_not_isB {l l' : Index} {i i' : ChainIndex} {v : Digest} {x : HashInput} (h : K.IsA l i x)
    (h' : K.IsB l' i' v x) : False := by
  obtain ⟨st, pay, hst, rfl⟩ := h
  obtain ⟨st', hst', heq⟩ := h'
  obtain ⟨rfl, rfl, rfl, -⟩ := chainInput_inj heq
  omega

theorem isA_ne_enc {l : Index} {i : ChainIndex} {x : HashInput} (h : K.IsA l i x) (l' : LeafIndex) (msg : Digest)
    (ctr : Counter) : x ≠ Wots.encodingInput K.p topLayer rootTree l' msg ctr := by
  obtain ⟨st, pay, -, rfl⟩ := h
  exact chainInput_ne_enc

theorem isB_ne_enc {l : Index} {i : ChainIndex} {v : Digest} {x : HashInput} (h : K.IsB l i v x) (l' : LeafIndex)
    (msg : Digest) (ctr : Counter) : x ≠ Wots.encodingInput K.p topLayer rootTree l' msg ctr := by
  obtain ⟨st, -, rfl⟩ := h
  exact chainInput_ne_enc

theorem isA_ne_fchain {l : Index} {i : ChainIndex} {x : HashInput} (h : K.IsA l i x) (f : FIn) :
    x ≠ f.input K.p := by
  obtain ⟨st, pay, -, rfl⟩ := h
  exact chainInput_ne_fchain

theorem isB_ne_fchain {l : Index} {i : ChainIndex} {v : Digest} {x : HashInput} (h : K.IsB l i v x) (f : FIn) :
    x ≠ f.input K.p := by
  obtain ⟨st, -, rfl⟩ := h
  exact chainInput_ne_fchain

/-! ### Fresh entries after a store -/

section Store

variable {s : St} {x : HashInput} (u : HashOutput)

theorem fr_store (hx : s.cache x = none) (hi : K.initial x = none) {y : HashInput} {v : HashOutput} :
    K.Fr (s.store x u) y v ↔ K.Fr s y v ∨ (y = x ∧ v = u) := by
  unfold Fr
  by_cases hy : y = x
  · subst hy
    have hself : (s.store y u).cache y = some u := by simp [DebtState.store]
    rw [hself, hx]
    constructor
    · rintro ⟨h, -⟩
      exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
    · rintro (⟨h, -⟩ | ⟨-, rfl⟩)
      · cases h
      · exact ⟨rfl, hi⟩
  · rw [HiddenDebt.store_cache_ne s x y hy u]
    simp [hy]

theorem fr_store_of (hx : s.cache x = none) (hi : K.initial x = none) {y : HashInput} {v : HashOutput}
    (h : K.Fr s y v) : K.Fr (s.store x u) y v :=
  (fr_store u hx hi).2 (Or.inl h)

theorem aAns_store (hx : s.cache x = none) (hi : K.initial x = none) (l : Index) (i : ChainIndex) :
    K.AAns (s.store x u) l i =
      if K.IsA l i x then insert (truncateHash u) (K.AAns s l i) else K.AAns s l i := by
  ext t
  simp only [AAns, Set.mem_ofPred_eq, fr_store u hx hi]
  split_ifs with hA
  · simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, v, hy, (hfr | ⟨rfl, rfl⟩), ht⟩
      · exact Or.inr ⟨y, v, hy, hfr, ht⟩
      · exact Or.inl ht.symm
    · rintro (rfl | ⟨y, v, hy, hfr, ht⟩)
      · exact ⟨x, u, hA, Or.inr ⟨rfl, rfl⟩, rfl⟩
      · exact ⟨y, v, hy, Or.inl hfr, ht⟩
  · constructor
    · rintro ⟨y, v, hy, (hfr | ⟨rfl, rfl⟩), ht⟩
      · exact ⟨y, v, hy, hfr, ht⟩
      · exact absurd hy hA
    · rintro ⟨y, v, hy, hfr, ht⟩
      exact ⟨y, v, hy, Or.inl hfr, ht⟩

theorem bPay_store (hx : s.cache x = none) (hi : K.initial x = none) (l : Index) (i : ChainIndex) :
    K.BPay (s.store x u) l i = K.BPay s l i ∪ {v | K.IsB l i v x} := by
  ext v
  simp only [BPay, Set.mem_union, Set.mem_ofPred_eq, fr_store u hx hi]
  constructor
  · rintro ⟨y, w, hy, (hfr | ⟨rfl, rfl⟩)⟩
    · exact Or.inl ⟨y, w, hy, hfr⟩
    · exact Or.inr hy
  · rintro (⟨y, w, hy, hfr⟩ | hv)
    · exact ⟨y, w, hy, Or.inl hfr⟩
    · exact ⟨x, u, hv, Or.inr ⟨rfl, rfl⟩⟩

theorem contactB_store (hx : s.cache x = none) (hi : K.initial x = none) (l : Index) (i : ChainIndex) :
    K.ContactB (s.store x u) l i =
      K.ContactB s l i ∪ {v | K.IsB l i v x ∧ truncateHash u = K.front l i} := by
  ext v
  simp only [ContactB, Set.mem_union, Set.mem_ofPred_eq, fr_store u hx hi]
  constructor
  · rintro ⟨y, w, hy, (hfr | ⟨rfl, rfl⟩), ht⟩
    · exact Or.inl ⟨y, w, hy, hfr, ht⟩
    · exact Or.inr ⟨hy, ht⟩
  · rintro (⟨y, w, hy, hfr, ht⟩ | ⟨hv, ht⟩)
    · exact ⟨y, w, hy, Or.inl hfr, ht⟩
    · exact ⟨x, u, hv, Or.inr ⟨rfl, rfl⟩, ht⟩

theorem marker_store (hx : s.cache x = none) (hi : K.initial x = none) (l : Index) (i : ChainIndex) :
    K.Marker (s.store x u) l i ↔ K.Marker s l i ∨
      ((∃ msg ctr, x = Wots.encodingInput K.p topLayer rootTree l msg ctr) ∧ truncateHash u ∈ K.markSet l i) := by
  simp only [Marker, fr_store u hx hi]
  constructor
  · rintro ⟨msg, ctr, w, (hfr | ⟨hxe, rfl⟩), hm⟩
    · exact Or.inl ⟨msg, ctr, w, hfr, hm⟩
    · exact Or.inr ⟨⟨msg, ctr, hxe.symm⟩, hm⟩
  · rintro (⟨msg, ctr, w, hfr, hm⟩ | ⟨⟨msg, ctr, rfl⟩, hm⟩)
    · exact ⟨msg, ctr, w, Or.inl hfr, hm⟩
    · exact ⟨msg, ctr, u, Or.inr ⟨rfl, rfl⟩, hm⟩

theorem fe_store (hx : s.cache x = none) (hi : K.initial x = none) (f : FIn) :
    K.FE (s.store x u) f ↔ K.FE s f ∨ x = f.input K.p := by
  simp only [FE, fr_store u hx hi]
  constructor
  · rintro ⟨w, (hfr | ⟨hxe, rfl⟩)⟩
    · exact Or.inl ⟨w, hfr⟩
    · exact Or.inr hxe.symm
  · rintro (⟨w, hfr⟩ | rfl)
    · exact ⟨w, Or.inl hfr⟩
    · exact ⟨u, Or.inr ⟨rfl, rfl⟩⟩

theorem fc_store (hx : s.cache x = none) (hi : K.initial x = none) (f : FIn) :
    K.FC (s.store x u) f ↔ K.FC s f ∨
      (x = f.input K.p ∧ ∃ w, s.known f.outC = some w ∧ truncateHash u = w) := by
  have hk : (s.store x u).known = s.known := rfl
  simp only [FC, fr_store u hx hi, hk]
  constructor
  · rintro ⟨w, w', (hfr | ⟨hxe, rfl⟩), hkn, ht⟩
    · exact Or.inl ⟨w, w', hfr, hkn, ht⟩
    · exact Or.inr ⟨hxe.symm, w', hkn, ht⟩
  · rintro (⟨w, w', hfr, hkn, ht⟩ | ⟨rfl, w', hkn, ht⟩)
    · exact ⟨w, w', Or.inl hfr, hkn, ht⟩
    · exact ⟨u, w', Or.inr ⟨rfl, rfl⟩, hkn, ht⟩

theorem lat_store (hx : s.cache x = none) (hi : K.initial x = none) (f : FIn) :
    K.Lat (s.store x u) f ↔ K.Lat s f ∨ (x = f.input K.p ∧ s.known f.outC = none) := by
  have hk : (s.store x u).known = s.known := rfl
  simp only [Lat, fe_store u hx hi, hk]
  tauto

theorem bPay_mono (hx : s.cache x = none) (hi : K.initial x = none) (l : Index) (i : ChainIndex) :
    K.BPay s l i ⊆ K.BPay (s.store x u) l i := by
  rw [bPay_store u hx hi]
  exact Set.subset_union_left

theorem uaSet_store (hx : s.cache x = none) (hi : K.initial x = none) :
    K.UAset (s.store x u) ⊆ insert x (K.UAset s) := by
  rintro y ⟨l, i, w, hl, hA, hfr, hnot⟩
  rcases (fr_store u hx hi).1 hfr with hfr | ⟨rfl, rfl⟩
  · exact Or.inr ⟨l, i, w, hl, hA, hfr, fun h => hnot (bPay_mono u hx hi l i h)⟩
  · exact Or.inl rfl

theorem uaSet_store_of_not (hx : s.cache x = none) (hi : K.initial x = none)
    (hA : ∀ l i, Landed K.p l → ¬K.IsA l i x) : K.UAset (s.store x u) ⊆ K.UAset s := by
  intro y hy
  rcases uaSet_store u hx hi hy with rfl | h
  · obtain ⟨l, i, w, hl, hA', -⟩ := hy
    exact absurd hA' (hA l i hl)
  · exact h

/-- A fresh input one step below the word has a fresh payload. -/
theorem not_mem_bPay (hx : s.cache x = none) {l : Index} {i : ChainIndex} {v : Digest} (hB : K.IsB l i v x) :
    v ∉ K.BPay s l i := by
  rintro ⟨y, w, hy, hfr, -⟩
  rw [← isB_input hB hy, hx] at hfr
  cases hfr

theorem contactB_subset_bPay (l : Index) (i : ChainIndex) : K.ContactB s l i ⊆ K.BPay s l i := by
  rintro v ⟨y, w, hy, hfr, -⟩
  exact ⟨y, w, hy, hfr⟩

end Store

/-! ### Leaf-local data -/

/-- A leaf without a WOTS event that has a marker or a contact. -/
def ArmedAt (s : St) (l : Index) : Prop :=
  ¬K.BadLeaf s l ∧ ((∃ i, K.Marker s l i) ∨ ∃ i, (K.ContactB s l i).Nonempty)

/-- Two states agree at a leaf. -/
def SameLeaf (s s' : St) (l : Index) : Prop :=
  (∀ i, K.ContactB s' l i = K.ContactB s l i) ∧ (∀ i, K.AAns s' l i = K.AAns s l i) ∧
    (∀ i, K.Marker s' l i ↔ K.Marker s l i)

theorem badLeaf_congr {s s' : St} {l : Index} (h : K.SameLeaf s s' l) : K.BadLeaf s' l ↔ K.BadLeaf s l := by
  obtain ⟨hc, ha, hm⟩ := h
  simp only [BadLeaf, hc, ha, hm]

theorem armedAt_congr {s s' : St} {l : Index} (h : K.SameLeaf s s' l) : K.ArmedAt s' l ↔ K.ArmedAt s l := by
  have hb := badLeaf_congr h
  obtain ⟨hc, -, hm⟩ := h
  simp only [ArmedAt, hb, hc, hm]

theorem leafCount_congr {s s' : St} {l : Index} (h : K.SameLeaf s s' l) : K.leafCount s' l = K.leafCount s l := by
  have hb := badLeaf_congr h
  obtain ⟨hc, -, -⟩ := h
  simp only [leafCount, hb, hc]

/-- Away from one leaf, the WOTS aggregates follow that leaf. -/
theorem wotsBad_of_same {s s' : St} (l₀ : Index) (h : ∀ l, Landed K.p l → l ≠ l₀ → K.SameLeaf s s' l)
    (hw : K.WotsBad s') : K.WotsBad s ∨ (Landed K.p l₀ ∧ K.BadLeaf s' l₀) := by
  obtain ⟨l, hl, hb⟩ := hw
  by_cases hll : l = l₀
  · subst hll
    exact Or.inr ⟨hl, hb⟩
  · exact Or.inl ⟨l, hl, (badLeaf_congr (h l hl hll)).1 hb⟩

theorem armed_of_same {s s' : St} (l₀ : Index) (h : ∀ l, Landed K.p l → l ≠ l₀ → K.SameLeaf s s' l)
    (ha : K.Armed s') : K.Armed s ∨ (Landed K.p l₀ ∧ K.ArmedAt s' l₀) := by
  obtain ⟨l, hl, hb⟩ := ha
  by_cases hll : l = l₀
  · subst hll
    exact Or.inr ⟨hl, hb⟩
  · exact Or.inl ⟨l, hl, (armedAt_congr (h l hl hll)).1 hb⟩

theorem contactCount_of_same {s s' : St} (l₀ : Index) (h : ∀ l, Landed K.p l → l ≠ l₀ → K.SameLeaf s s' l)
    (d : ℝ≥0∞) (hd : Landed K.p l₀ → K.leafCount s' l₀ ≤ K.leafCount s l₀ + d) :
    K.contactCount s' ≤ K.contactCount s + d := by
  unfold contactCount
  calc ∑ l, (if Landed K.p l then K.leafCount s' l else 0)
      ≤ ∑ l, ((if Landed K.p l then K.leafCount s l else 0) + if l = l₀ then d else 0) := by
        refine Finset.sum_le_sum fun l _ => ?_
        by_cases hl : Landed K.p l
        · rw [ite_eq_left hl, ite_eq_left hl]
          by_cases hll : l = l₀
          · subst hll
            rw [ite_eq_left rfl]
            exact hd hl
          · rw [ite_eq_right hll, add_zero, leafCount_congr (h l hl hll)]
        · rw [ite_eq_right hl, ite_eq_right hl, zero_add]
          exact bot_le
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ l₀, ite_eq_left (Finset.mem_univ _)]

/-- With every landed leaf unchanged, the WOTS aggregates are unchanged. -/
theorem wots_of_allSame {s s' : St} (h : ∀ l, Landed K.p l → K.SameLeaf s s' l) :
    (K.WotsBad s' ↔ K.WotsBad s) ∧ (K.Armed s' ↔ K.Armed s) ∧ K.contactCount s' = K.contactCount s := by
  refine ⟨⟨fun ⟨l, hl, hb⟩ => ⟨l, hl, (badLeaf_congr (h l hl)).1 hb⟩,
    fun ⟨l, hl, hb⟩ => ⟨l, hl, (badLeaf_congr (h l hl)).2 hb⟩⟩,
    ⟨fun ⟨l, hl, hb⟩ => ⟨l, hl, (armedAt_congr (h l hl)).1 hb⟩,
      fun ⟨l, hl, hb⟩ => ⟨l, hl, (armedAt_congr (h l hl)).2 hb⟩⟩, ?_⟩
  unfold contactCount
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : Landed K.p l
  · rw [ite_eq_left hl, ite_eq_left hl, leafCount_congr (h l hl)]
  · rw [ite_eq_right hl, ite_eq_right hl]

/-- Under a store, a leaf is unchanged when the input is not of its WOTS shapes. -/
theorem sameLeaf_store {s : St} {x : HashInput} (u : HashOutput) (hx : s.cache x = none)
    (hi : K.initial x = none) (l : Index) (hA : ∀ i, ¬K.IsA l i x) (hB : ∀ i v, ¬K.IsB l i v x)
    (hE : ∀ msg ctr, x ≠ Wots.encodingInput K.p topLayer rootTree l msg ctr) :
    K.SameLeaf s (s.store x u) l := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [contactB_store u hx hi]
    refine Set.union_eq_left.2 fun v hv => absurd hv.1 (hB i v)
  · rw [aAns_store u hx hi, ite_eq_right (hA i)]
  · rw [marker_store u hx hi]
    exact ⟨fun h => h.resolve_right fun ⟨⟨msg, ctr, he⟩, _⟩ => hE msg ctr he, Or.inl⟩

/-- Monotonicity of a leaf's WOTS event under a store. -/
theorem badLeaf_store_of {s : St} {x : HashInput} (u : HashOutput) (hx : s.cache x = none)
    (hi : K.initial x = none) {l : Index} (h : K.BadLeaf s l) : K.BadLeaf (s.store x u) l := by
  have hc : ∀ i, K.ContactB s l i ⊆ K.ContactB (s.store x u) l i := fun i => by
    rw [contactB_store u hx hi]
    exact Set.subset_union_left
  have ha : ∀ i, K.AAns s l i ⊆ K.AAns (s.store x u) l i := fun i => by
    rw [aAns_store u hx hi]
    split_ifs
    · exact Set.subset_insert _ _
    · exact le_rfl
  have hm : ∀ i, K.Marker s l i → K.Marker (s.store x u) l i := fun i h => (marker_store u hx hi l i).2 (Or.inl h)
  rcases h with ⟨i, hne⟩ | ⟨i, hne, hmk⟩ | ⟨i, i', hii, hne, hne'⟩
  · exact Or.inl ⟨i, hne.mono (Set.inter_subset_inter (hc i) (ha i))⟩
  · exact Or.inr (Or.inl ⟨i, hne.mono (hc i), hm i hmk⟩)
  · exact Or.inr (Or.inr ⟨i, i', hii, hne.mono (hc i), hne'.mono (hc i')⟩)

/-! ### The components of the potential -/

theorem done_le {s s' : St} (E : Prop) [Decidable E] (h : K.Bad s' → K.Bad s ∨ E) :
    K.done s' ≤ K.done s + (if ¬K.Bad s ∧ E then 1 else 0) := by
  unfold done
  by_cases hb' : K.Bad s'
  · rw [ite_eq_left hb']
    by_cases hb : K.Bad s
    · rw [ite_eq_left hb]
      exact le_self_add
    · rw [ite_eq_right hb, zero_add, ite_eq_left ⟨hb, (h hb').resolve_left hb⟩]
  · rw [ite_eq_right hb']
    exact bot_le

/-- Pending debts after a fresh answer: at most one more at the input's hidden target. -/
theorem pend_store {s : St} {x : HashInput} (u : HashOutput) (hx : s.cache x = none) (hi : K.initial x = none) :
    K.pend (s.store x u) ≤
      K.pend s + ∑ c : Coordinate, if K.tg.kind x = .hidden c ∧ s.known c = none then ν else 0 := by
  unfold pend
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have hknown : (s.store x u).known = s.known := rfl
  rw [hknown, debts_store K.tg K.initial s x u hx hi]
  by_cases hc : s.known c = none
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases hk : K.tg.kind x = .hidden c
    · rw [ite_eq_left hk, ite_eq_left ⟨hk, hc⟩]
      calc ((insert (K.tg.trunc u) (debts K.tg K.initial s c)).encard : ℝ≥0∞) * ν
          ≤ (((debts K.tg K.initial s c).encard : ℝ≥0∞) + 1) * ν :=
            mul_le_mul_of_nonneg_right (encard_insert_le_ennreal _ _) bot_le
        _ = _ := by rw [add_mul, one_mul]
    · have hk' : ¬(K.tg.kind x = .hidden c ∧ s.known c = none) := fun h => hk h.1
      rw [ite_eq_right hk, ite_eq_right hk', add_zero]
  · rw [ite_eq_right hc, ite_eq_right hc, zero_add]
    exact bot_le

theorem pend_store_none {s : St} {x : HashInput} (u : HashOutput) (hx : s.cache x = none)
    (hi : K.initial x = none) (hk : K.tg.kind x = .none) : K.pend (s.store x u) = K.pend s := by
  unfold pend
  refine Finset.sum_congr rfl fun c _ => ?_
  have hknown : (s.store x u).known = s.known := rfl
  have hk' : ¬K.tg.kind x = .hidden c := by rw [hk]; exact fun h => by cases h
  rw [hknown, debts_store K.tg K.initial s x u hx hi, ite_eq_right hk']

theorem pend_record (s : St) (g : Coordinate × Digest) : K.pend (s.record g) ≤ K.pend s + ν := by
  unfold pend
  have hknown : (s.record g).known = s.known := rfl
  calc ∑ c : Coordinate, (if (s.record g).known c = none then
          ((debts K.tg K.initial (s.record g) c).encard : ℝ≥0∞) * ν else 0)
      ≤ ∑ c : Coordinate, ((if s.known c = none then ((debts K.tg K.initial s c).encard : ℝ≥0∞) * ν else 0) +
          if c = g.1 then ν else 0) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [hknown, debts_record]
        by_cases hc : s.known c = none
        · rw [ite_eq_left hc, ite_eq_left hc]
          by_cases hcg : c = g.1
          · rw [ite_eq_left hcg, ite_eq_left hcg]
            calc ((insert g.2 (debts K.tg K.initial s c)).encard : ℝ≥0∞) * ν
                ≤ (((debts K.tg K.initial s c).encard : ℝ≥0∞) + 1) * ν :=
                  mul_le_mul_of_nonneg_right (encard_insert_le_ennreal _ _) bot_le
              _ = _ := by rw [add_mul, one_mul]
          · rw [ite_eq_right hcg, ite_eq_right hcg, add_zero]
        · rw [ite_eq_right hc, ite_eq_right hc, zero_add]
          exact bot_le
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ g.1, ite_eq_left (Finset.mem_univ _)]

/-- Exposing an unexposed coordinate settles exactly its debts. -/
theorem pend_expose (s : St) (c : Coordinate) (v : Digest) (hc : s.known c = none) :
    K.pend s = K.pend (s.expose c v) + ((debts K.tg K.initial s c).encard : ℝ≥0∞) * ν := by
  unfold pend
  have hpoint : ∀ c' : Coordinate,
      (if s.known c' = none then ((debts K.tg K.initial s c').encard : ℝ≥0∞) * ν else 0) =
        (if (s.expose c v).known c' = none then
          ((debts K.tg K.initial (s.expose c v) c').encard : ℝ≥0∞) * ν else 0) +
        if c' = c then ((debts K.tg K.initial s c).encard : ℝ≥0∞) * ν else 0 := by
    intro c'
    by_cases hcc : c' = c
    · subst hcc
      have hself : (s.expose c' v).known c' = some v := by simp [DebtState.expose]
      rw [ite_eq_left hc, hself, ite_eq_right (by simp), zero_add, ite_eq_left rfl]
    · have hk : (s.expose c v).known c' = s.known c' := by simp [DebtState.expose, hcc]
      rw [hk, ite_eq_right hcc, add_zero]
      rfl
  rw [Finset.sum_congr rfl fun c' _ => hpoint c', Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ c,
    ite_eq_left (Finset.mem_univ _)]

/-- The first-order cost of a fresh answer: a fatal value, or a new debt at an unexposed target. -/
noncomputable def kindUnit (x : HashInput) : ℝ≥0∞ := if K.tg.kind x = .none then 0 else 1

theorem fo_mean (s : St) (x : HashInput) :
    meanD (fun t => if Fatal (K.tg.kind x) s.known t then 1 else 0) +
      (∑ c : Coordinate, if K.tg.kind x = .hidden c ∧ s.known c = none then ν else 0) ≤ ν * K.kindUnit x := by
  unfold kindUnit
  cases hk : K.tg.kind x with
  | none =>
      have h1 : (fun t : Digest => if Fatal (TargetKind.none : TargetKind Coordinate) s.known t then (1 : ℝ≥0∞)
          else 0) = fun _ => 0 := funext fun t => ite_eq_right (fun h => h)
      have h2 : ∀ c : Coordinate, ¬((TargetKind.none : TargetKind Coordinate) = .hidden c ∧ s.known c = none) :=
        fun c h => by cases h.1
      simp only [h1, h2, ite_false, Finset.sum_const_zero, add_zero, ite_true, meanD_const, mul_zero, le_refl]
  | fixed value =>
      simp only [ite_false, reduceCtorEq, mul_one]
      rw [meanD_ite_eq value (fun t => Fatal (TargetKind.fixed value) s.known t) (fun t => Iff.rfl), mul_one]
      simp
  | hidden target =>
      simp only [reduceCtorEq, ite_false, mul_one]
      have hsum : (∑ c : Coordinate, if TargetKind.hidden target = TargetKind.hidden c ∧ s.known c = none
          then ν else 0) = if s.known target = none then ν else 0 := by
        rw [Finset.sum_eq_single target]
        · simp
        · intro c _ hc
          rw [ite_eq_right]
          rintro ⟨h, -⟩
          exact hc (TargetKind.hidden.inj h).symm
        · simp
      rw [hsum]
      cases hc : s.known target with
      | none =>
          have h1 : (fun t : Digest => if Fatal (TargetKind.hidden target) s.known t then (1 : ℝ≥0∞) else 0) =
              fun _ => 0 := funext fun t => ite_eq_right (by simp [Fatal, hc])
          rw [h1, meanD_const, zero_add, ite_eq_left rfl]
      | some value =>
          rw [ite_eq_right (by simp), add_zero, meanD_ite_eq value (fun t => Fatal (TargetKind.hidden target) s.known t)
            (fun t => by simp [Fatal, hc, eq_comm]), mul_one]

/-! ### Combining the components -/

theorem ua_le_of_subset {s s' : St} (h : K.UAset s' ⊆ K.UAset s) :
    ν / 2 * ((K.UAset s').encard : ℝ≥0∞) ≤ ν / 2 * ((K.UAset s).encard : ℝ≥0∞) :=
  mul_le_mul_of_nonneg_left (ENat.toENNReal_le.2 (Set.encard_le_encard h)) bot_le

theorem ua_le_insert {s s' : St} (x : HashInput) (h : K.UAset s' ⊆ insert x (K.UAset s)) :
    ν / 2 * ((K.UAset s').encard : ℝ≥0∞) ≤ ν / 2 * ((K.UAset s).encard : ℝ≥0∞) + ν / 2 := by
  calc ν / 2 * ((K.UAset s').encard : ℝ≥0∞) ≤ ν / 2 * (((K.UAset s).encard : ℝ≥0∞) + 1) :=
        mul_le_mul_of_nonneg_left ((ENat.toENNReal_le.2 (Set.encard_le_encard h)).trans
          (encard_insert_le_ennreal _ _)) bot_le
    _ = _ := by rw [mul_add, mul_one]

theorem ua_strict {s s' : St} {y : HashInput} (h : K.UAset s' ⊆ K.UAset s) (hy : y ∈ K.UAset s)
    (hy' : y ∉ K.UAset s') :
    ν / 2 * ((K.UAset s').encard : ℝ≥0∞) + ν / 2 ≤ ν / 2 * ((K.UAset s).encard : ℝ≥0∞) := by
  have hsub : K.UAset s' ⊆ K.UAset s \ {y} := fun z hz => ⟨h hz, fun hzy => hy' (hzy ▸ hz)⟩
  have hcard : ((K.UAset s').encard : ℝ≥0∞) + 1 ≤ ((K.UAset s).encard : ℝ≥0∞) := by
    rw [← Set.encard_sdiff_singleton_add_one hy, ENat.toENNReal_add, ENat.toENNReal_one]
    gcongr
  calc ν / 2 * ((K.UAset s').encard : ℝ≥0∞) + ν / 2 = ν / 2 * (((K.UAset s').encard : ℝ≥0∞) + 1) := by
        rw [mul_add, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard bot_le

theorem pot_le {s s' : St} (y : ℕ) {cr dD dP dL dU dR : ℝ≥0∞}
    (hD : K.done s' ≤ K.done s + dD) (hP : K.pend s' ≤ K.pend s + dP) (hL : K.latent s' ≤ K.latent s + dL)
    (hU : ν / 2 * ((K.UAset s').encard : ℝ≥0∞) + cr ≤ ν / 2 * ((K.UAset s).encard : ℝ≥0∞) + dU)
    (hR : K.rate s' ≤ K.rate s + dR) :
    K.pot y s' + cr ≤ K.pot y s + (dD + dP + dL + dU + ((y : ℝ≥0∞) * ν) * dR) := by
  unfold pot
  calc _ = K.done s' + K.pend s' + K.latent s' + (ν / 2 * ((K.UAset s').encard : ℝ≥0∞) + cr) +
        ((y : ℝ≥0∞) * ν) * K.rate s' := by ring
    _ ≤ (K.done s + dD) + (K.pend s + dP) + (K.latent s + dL) + (ν / 2 * ((K.UAset s).encard : ℝ≥0∞) + dU) +
        ((y : ℝ≥0∞) * ν) * (K.rate s + dR) :=
        add_le_add (add_le_add (add_le_add (add_le_add hD hP) hL) hU) (mul_le_mul_of_nonneg_left hR bot_le)
    _ = _ := by ring

/-- A fresh read: the mean potential after a pointwise bound through the truncated answer. -/
theorem mean_store (y : ℕ) {s : St} {x : HashInput} (hx : s.cache x = none) (cr : ℝ≥0∞)
    (G : Digest → ℝ≥0∞) (h : ∀ u, K.pot y (s.store x u) + cr ≤ K.pot y s + G (truncateHash u)) :
    ∑' r, Pr{let y ← readOutside x s}[y = r] * K.pot y r.2 + cr ≤ K.pot y s + meanD G := by
  rw [readOutside_fresh x s hx, OracleComp.tsum_prEvent_map_mul]
  calc ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] * K.pot y (s.store x u) + cr
      = ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] * (K.pot y (s.store x u) + cr) := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, tsum_uniform_const]
    _ ≤ ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] * (K.pot y s + G (truncateHash u)) :=
        ENNReal.tsum_le_tsum fun u => mul_le_mul_of_nonneg_left (h u) bot_le
    _ = K.pot y s + meanD G := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, tsum_uniform_const, mean_trunc]

theorem vrate_le (hρ : K.ρ ≤ 2) {s s' : St} (E : Prop) [Decidable E] (h : K.Armed s' → K.Armed s ∨ E) :
    K.vrate s' ≤ K.vrate s + (if ¬K.Armed s ∧ E then ENNReal.ofReal (2 - K.ρ) else 0) := by
  have h2 : ENNReal.ofReal K.ρ ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hρ
  unfold vrate
  by_cases ha' : K.Armed s'
  · rw [ite_eq_left ha']
    by_cases ha : K.Armed s
    · rw [ite_eq_left ha]
      exact le_self_add
    · rw [ite_eq_right ha, ite_eq_left ⟨ha, (h ha').resolve_left ha⟩]
      calc (2 : ℝ≥0∞) = ENNReal.ofReal (K.ρ + (2 - K.ρ)) := by simp
        _ ≤ _ := ENNReal.ofReal_add_le
  · rw [ite_eq_right ha']
    by_cases ha : K.Armed s
    · rw [ite_eq_left ha]
      exact h2.trans le_self_add
    · rw [ite_eq_right ha]
      exact le_self_add

theorem rate_le {s s' : St} {dV dC dK : ℝ≥0∞} (hV : K.vrate s' ≤ K.vrate s + dV)
    (hC : K.contactCount s' ≤ K.contactCount s + dC) (hK : K.kf s' ≤ K.kf s + dK) :
    K.rate s' ≤ K.rate s + (dV + 64 * dC + dK) := by
  unfold rate
  calc K.vrate s' + 64 * K.contactCount s' + K.kf s'
      ≤ (K.vrate s + dV) + 64 * (K.contactCount s + dC) + (K.kf s + dK) :=
        add_le_add (add_le_add hV (mul_le_mul_of_nonneg_left hC bot_le)) hK
    _ = _ := by ring

theorem cw_congr {s s' : St} (hfr : ∀ (f : FIn) u, K.Fr s' (f.input K.p) u ↔ K.Fr s (f.input K.p) u)
    (hk : ∀ f : FIn, s'.known f.outC = s.known f.outC) (f : FIn) : K.cw s' f = K.cw s f := by
  have hFC : K.FC s' f ↔ K.FC s f := by simp only [FC, hfr, hk]
  have hLat : K.Lat s' f ↔ K.Lat s f := by simp only [Lat, FE, hfr, hk]
  simp only [cw, hFC, hLat]

/-- The forest aggregates follow the contact weights and the guess records. -/
theorem forest_same {s s' : St} (hcw : ∀ f, K.cw s' f = K.cw s f) (hg : s'.guesses = s.guesses) :
    K.ng s' = K.ng s ∧ K.kf s' = K.kf s ∧ K.pp s' = K.pp s ∧ K.latent s' = K.latent s := by
  have hR : ∀ f, Recd s' f ↔ Recd s f := fun f => by simp only [Recd, hg]
  have h1 : K.ng s' = K.ng s := by simp only [ng, hcw, hR]
  have h3 : K.pp s' = K.pp s := by simp only [pp, hcw, hR]
  exact ⟨h1, by simp only [kf, hcw, hR], h3, by simp only [latent, h1, h3]⟩

end Ctx

end Sphincs.Security.PotentialA
