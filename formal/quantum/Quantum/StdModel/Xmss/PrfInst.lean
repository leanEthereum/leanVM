module

public import Quantum.StdModel.Xmss.Gen
public import Quantum.StdModel.Props.Prf
public import Quantum.Qrom.Xmss.Slots

@[expose] public section

/-!
# leanXMSS's KIM-PRF instance (design D1) and the law of the ideal secret

leanXMSS derives every secret from `S = H("leanXMSS" ‖ S_0)` (X1) with the key in the middle of
three formats (`PrfDom`): the public parameter (X2, `inl ()`), the starts of a pair of chains
(X3, `(P, l, e, j)`) and the randomizer base of a layer's message (X4, `(P, e, M)`). The chain
pairs keep all 256 bits; the other formats keep the first 16 bytes, zero-extended (`prfTrunc`).

* `prfFmt`, `prfKey`, `prfSeedBytes`, `prfTrunc`: the instance; `prfInput_param`,
  `prfInput_chainPair`, `prfInput_rnd`: the keyed inputs are the scheme's inputs.
* `prfFmt_injective`, `prfFmt_lengthLe`, `length_prfSeedInput`: the obligations (b) and (a).
* `xmssPrfAdv`: the derived-key KIM-PRF advantage of this instance.
* `prfView f`: the ideal secret (`IdealKey`) read off a function `f` on the formats: the
  parameter, the chain starts at that parameter and the randomizer bases at that parameter. It
  depends on `f` only through the ideal answers `prfTrunc x (f x)` (`prfView_prfTrunc`).
* `sum_prfView` (**law of the view**): the view of a uniform function is a uniform ideal secret.
  The proof is over abstract finite types (`unifAvg_view`): a uniform function on a sum is a
  triple of independent uniform functions, the parameter is a uniform half of a uniform output,
  and the slices of the other two functions at it are uniform, independent of it.
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal
open Quantum.Xmss (addressBytes_injective length_littleEndianBytes layerOf_layerHi lowOf_layerHi
  keyOf_ofNat)
open Quantum.Qrom.Xmss (littleEndianBytes_inj length_thInput_eq length_seedInput)

namespace Quantum.StdModel.Xmss

/-! ## Uniform averages over finite types -/

section Uniform

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]

/-- The uniform average of `F` over a finite type. -/
noncomputable def unifAvg (F : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * F a

theorem unifAvg_congr {F G : α → ℝ≥0∞} (h : ∀ a, F a = G a) : unifAvg F = unifAvg G :=
  congrArg unifAvg (funext h)

/-- A bijection pushes the uniform law to the uniform law. -/
theorem unifAvg_equiv (e : α ≃ β) (F : β → ℝ≥0∞) : unifAvg (fun a ↦ F (e a)) = unifAvg F := by
  unfold unifAvg
  rw [Fintype.card_congr e]
  exact Equiv.sum_comp e fun b ↦ (Fintype.card β : ℝ≥0∞)⁻¹ * F b

/-- A uniform pair is a pair of independent uniform components. -/
theorem unifAvg_prod (F : α × β → ℝ≥0∞) :
    unifAvg F = unifAvg fun a ↦ unifAvg fun b ↦ F (a, b) := by
  unfold unifAvg
  rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _)), Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, mul_assoc]

theorem unifAvg_const [Nonempty α] (c : ℝ≥0∞) : unifAvg (fun _ : α ↦ c) = c := by
  unfold unifAvg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

/-- The first component of a bijection onto a product is uniform. -/
theorem unifAvg_fst [Nonempty γ] (e : α ≃ β × γ) (F : β → ℝ≥0∞) :
    unifAvg (fun a ↦ F (e a).1) = unifAvg F :=
  ((unifAvg_equiv e fun p ↦ F p.1).trans (unifAvg_prod _)).trans
    (unifAvg_congr fun b ↦ unifAvg_const (F b))

/-- A uniform function evaluated at a fixed point is uniform. -/
theorem unifAvg_eval [DecidableEq α] [Nonempty β] (a : α) (F : β → ℝ≥0∞) :
    unifAvg (fun h : α → β ↦ F (h a)) = unifAvg F :=
  unifAvg_fst (Equiv.piSplitAt a fun _ ↦ β) F

/-- **The law of a view, abstractly**: for a uniform function `f` on `Unit ⊕ K × R ⊕ K × B`,
the key `k = p (f (inl ()))` and the images under `cv` and `gv` of the slices of `f` at `k` are
independent and uniform, when `p` and `gv` push the uniform law to the uniform law and `cv` is a
bijection. -/
theorem unifAvg_view {U K R B C G : Type} [Fintype U] [Nonempty U] [Fintype K] [DecidableEq K]
    [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B] [Fintype C] [Fintype G]
    (p : U → K) (hp : ∀ F : K → ℝ≥0∞, unifAvg (fun u ↦ F (p u)) = unifAvg F)
    (cv : (R → U) ≃ C) (gv : (B → U) → G)
    (hg : ∀ F : G → ℝ≥0∞, unifAvg (fun x ↦ F (gv x)) = unifAvg F) (Φ : K × C × G → ℝ≥0∞) :
    unifAvg (fun f : Unit ⊕ (K × R) ⊕ (K × B) → U ↦
      Φ (p (f (.inl ())), cv (fun r ↦ f (.inr (.inl (p (f (.inl ())), r)))),
        gv fun b ↦ f (.inr (.inr (p (f (.inl ())), b))))) = unifAvg Φ := by
  let E : (Unit ⊕ (K × R) ⊕ (K × B) → U) ≃ U × (K → R → U) × (K → B → U) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr (Equiv.funUnique Unit U)
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        (Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.curry _ _ _))))
  refine (unifAvg_equiv E fun q ↦ Φ (p q.1, cv (q.2.1 (p q.1)), gv (q.2.2 (p q.1)))).trans
    ((unifAvg_prod _).trans (Eq.trans ?_ (unifAvg_prod Φ).symm))
  refine (unifAvg_congr fun u ↦ ?_).trans (hp fun k ↦ unifAvg fun cg : C × G ↦ Φ (k, cg))
  refine (unifAvg_prod _).trans (Eq.trans ?_ (unifAvg_prod _).symm)
  have h2 : ∀ h1 : K → R → U,
      (unifAvg fun h2 : K → B → U ↦ Φ (p u, cv (h1 (p u)), gv (h2 (p u)))) =
        unifAvg fun g ↦ Φ (p u, cv (h1 (p u)), g) := fun h1 ↦
    (unifAvg_eval (p u) fun x ↦ Φ (p u, cv (h1 (p u)), gv x)).trans
      (hg fun g ↦ Φ (p u, cv (h1 (p u)), g))
  exact (unifAvg_congr h2).trans ((unifAvg_eval (p u) fun x ↦
    unifAvg fun g ↦ Φ (p u, cv x, g)).trans (unifAvg_equiv cv fun c ↦
      unifAvg fun g ↦ Φ (p u, c, g)))

end Uniform

/-! ## The halves of a hash output -/

/-- The hash output with first half `lo` and second half `hi`. -/
def hashJoin (lo hi : Digest) : HashOutput :=
  hi ++ lo

theorem getLsbD_hashJoin (lo hi : Digest) (j : ℕ) :
    (hashJoin lo hi).getLsbD j = if j < 128 then lo.getLsbD j else hi.getLsbD (j - 128) :=
  BitVec.getLsbD_append (x := hi) (y := lo) (i := j)

theorem truncateHash_hashJoin (lo hi : Digest) : truncateHash (hashJoin lo hi) = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj : j < 128 := hj
  simp only [truncateHash, digestBits, BitVec.getLsbD_extractLsb', getLsbD_hashJoin]
  simp [hj]

theorem upperHalfOfHash_hashJoin (lo hi : Digest) : upperHalfOfHash (hashJoin lo hi) = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj : j < 128 := hj
  simp only [upperHalfOfHash, digestBits, BitVec.getLsbD_extractLsb', getLsbD_hashJoin]
  simp [hj]

theorem hashJoin_halves (y : HashOutput) : hashJoin (truncateHash y) (upperHalfOfHash y) = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj : j < 256 := hj
  rw [getLsbD_hashJoin]
  by_cases h : j < 128
  · simp only [h, ↓reduceIte, truncateHash, digestBits, BitVec.getLsbD_extractLsb']
    simp
  · simp only [h, ↓reduceIte, upperHalfOfHash, digestBits, BitVec.getLsbD_extractLsb']
    rw [show 128 + (j - 128) = j by omega]
    simp [show j - 128 < 128 by omega]

/-- A hash output as its two halves. -/
def hashSplit : HashOutput ≃ Digest × Digest where
  toFun o := (truncateHash o, upperHalfOfHash o)
  invFun d := hashJoin d.1 d.2
  left_inv := hashJoin_halves
  right_inv _ := Prod.ext (truncateHash_hashJoin _ _) (upperHalfOfHash_hashJoin _ _)

/-- A function to hash outputs as the functions to their two halves. -/
def arrowHashSplit (B : Type) : (B → HashOutput) ≃ (B → Digest) × (B → Digest) :=
  (Equiv.arrowCongr (Equiv.refl B) hashSplit).trans (Equiv.arrowProdEquivProdArrow _ _ _)

/-! ## The chain starts from the pairs -/

/-- The first chain `2 j` of the pair `j`. -/
def evenChain (j : ChainPairIndex) : ChainIndex :=
  ⟨2 * j.val, by have := j.isLt; omega⟩

/-- The second chain `2 j + 1` of the pair `j`. -/
def oddChain (j : ChainPairIndex) : ChainIndex :=
  ⟨2 * j.val + 1, by have := j.isLt; omega⟩

theorem chainPair_evenChain (j : ChainPairIndex) : chainPair (evenChain j) = j :=
  Fin.ext (show 2 * j.val / 2 = j.val by omega)

theorem chainPair_oddChain (j : ChainPairIndex) : chainPair (oddChain j) = j :=
  Fin.ext (show (2 * j.val + 1) / 2 = j.val by omega)

theorem hashHalfForChain_evenChain (j : ChainPairIndex) (o : HashOutput) :
    hashHalfForChain (evenChain j).val o = truncateHash o :=
  ite_eq_left (show 2 * j.val % 2 = 0 by omega)

theorem hashHalfForChain_oddChain (j : ChainPairIndex) (o : HashOutput) :
    hashHalfForChain (oddChain j).val o = upperHalfOfHash o :=
  ite_eq_right (show ¬(2 * j.val + 1) % 2 = 0 by omega)

/-- **The chain starts of the pair outputs**: chain `i` of key `(l, e)` starts at the half
`hashHalfForChain i` of the output of its pair; a bijection. -/
def chainStartsEquiv :
    (Layer × KeyIndex × ChainPairIndex → HashOutput) ≃ (Layer → KeyIndex → ChainIndex → Digest)
    where
  toFun x l e i := hashHalfForChain i.val (x (l, e, chainPair i))
  invFun c t := hashJoin (c t.1 t.2.1 (evenChain t.2.2)) (c t.1 t.2.1 (oddChain t.2.2))
  left_inv x := funext fun ⟨l, e, j⟩ ↦ by
    show hashJoin (hashHalfForChain (evenChain j).val (x (l, e, chainPair (evenChain j))))
      (hashHalfForChain (oddChain j).val (x (l, e, chainPair (oddChain j)))) = x (l, e, j)
    rw [chainPair_evenChain, chainPair_oddChain, hashHalfForChain_evenChain,
      hashHalfForChain_oddChain, hashJoin_halves]
  right_inv c := funext fun l ↦ funext fun e ↦ funext fun i ↦ by
    show hashHalfForChain i.val
      (hashJoin (c l e (evenChain (chainPair i))) (c l e (oddChain (chainPair i)))) = c l e i
    by_cases h : i.val % 2 = 0
    · rw [hashHalfForChain, ite_eq_left h, truncateHash_hashJoin]
      exact congrArg (c l e) (Fin.ext (show 2 * (i.val / 2) = i.val by omega))
    · rw [hashHalfForChain, ite_eq_right h, upperHalfOfHash_hashJoin]
      exact congrArg (c l e) (Fin.ext (show 2 * (i.val / 2) + 1 = i.val by omega))

/-! ## The formats -/

/-- **The KIM-PRF formats of leanXMSS**: the public parameter (X2), the starts of the chain pair
`j` of key `(l, e)` under `P` (X3), the randomizer base of key `e` for the message `M` under `P`
(X4). -/
abbrev PrfDom :=
  Unit ⊕ (PublicParameter × Layer × KeyIndex × ChainPairIndex) ⊕
    (PublicParameter × KeyIndex × LayerMsg)

/-- The prefix and the address fields of a format. -/
def prfFields : PrfDom → PublicParameter × TweakFields
  | .inl _ => (0, keygenDomainFields .parameter)
  | .inr (.inl (P, l, e, j)) => (P, keygenDomainFields (.oneTimeChainPair l e j))
  | .inr (.inr (P, e, M)) => (P, tweakFields 7 0 (layerHi M.layer 0) e)

/-- The bytes after the key: the message of a randomizer base, else none. -/
def prfSuffix : PrfDom → HashInput
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr (_, _, M)) => M.bytes

/-- **The formats' bytes** around the key: the prefix and address, and the suffix. -/
def prfFmt (x : PrfDom) : HashInput × HashInput :=
  (littleEndianBytes 16 (prfFields x).1 ++ addressBytes (prfFields x).2, prfSuffix x)

/-- The bytes of the derived key `S`. -/
def prfKey (S : HashOutput) : HashInput :=
  littleEndianBytes 32 S

/-- The bytes of the key's seed `S_0`. -/
def prfSeedBytes (S0 : MasterSeed) : HashInput :=
  littleEndianBytes 32 S0

/-- **The truncations**: a chain pair keeps all 256 bits, the other formats the first 16 bytes,
zero-extended. -/
def prfTrunc : PrfDom → HashOutput → HashOutput
  | .inl _ => fun o ↦ (truncateHash o).setWidth 256
  | .inr (.inl _) => id
  | .inr (.inr _) => fun o ↦ (truncateHash o).setWidth 256

theorem prfInput_eq (x : PrfDom) (S : HashOutput) :
    (prfFmt x).1 ++ prfKey S ++ (prfFmt x).2 =
      thInput (prfFields x).1 (prfFields x).2 (prfKey S ++ prfSuffix x) := by
  simp only [prfFmt, thInput, hasherInput, List.append_assoc]

/-- X2: the keyed input of the parameter format is the parameter's derivation. -/
theorem prfInput_param (S : HashOutput) :
    (prfFmt (.inl ())).1 ++ prfKey S ++ (prfFmt (.inl ())).2 =
      thInput 0 (keygenDomainFields .parameter) (littleEndianBytes 32 S) := by
  rw [prfInput_eq]
  exact congrArg (thInput 0 (keygenDomainFields .parameter)) (List.append_nil _)

/-- X3: the keyed input of a chain-pair format is the pair's derivation. -/
theorem prfInput_chainPair (P : PublicParameter) (l : Layer) (e : KeyIndex) (j : ChainPairIndex)
    (S : HashOutput) :
    (prfFmt (.inr (.inl (P, l, e, j)))).1 ++ prfKey S ++ (prfFmt (.inr (.inl (P, l, e, j)))).2 =
      thInput P (keygenDomainFields (.oneTimeChainPair l e j)) (littleEndianBytes 32 S) := by
  rw [prfInput_eq]
  exact congrArg (thInput P (keygenDomainFields (.oneTimeChainPair l e j))) (List.append_nil _)

/-- X4: the keyed input of a randomizer format is the randomizer base's input. -/
theorem prfInput_rnd (P : PublicParameter) (e : KeyIndex) (M : LayerMsg) (S : HashOutput) :
    (prfFmt (.inr (.inr (P, e, M)))).1 ++ prfKey S ++ (prfFmt (.inr (.inr (P, e, M)))).2 =
      thInput P (tweakFields 7 0 (layerHi M.layer 0) e) (littleEndianBytes 32 S ++ M.bytes) :=
  prfInput_eq _ S

/-! ## The obligations -/

theorem prfHead_inj {P P' : PublicParameter} {f f' : TweakFields}
    (h : littleEndianBytes 16 P ++ addressBytes f = littleEndianBytes 16 P' ++ addressBytes f') :
    P = P' ∧ f = f' := by
  obtain ⟨h1, h2⟩ := List.append_inj h
    (by rw [length_littleEndianBytes, length_littleEndianBytes])
  exact ⟨littleEndianBytes_inj h1, addressBytes_injective h2⟩

/-- A layer's message is determined by its layer and bytes. -/
theorem layerMsg_eq_of_layer_bytes :
    ∀ {M M' : LayerMsg}, M.layer = M'.layer → M.bytes = M'.bytes → M = M'
  | .inl _, .inl _, _, h => congrArg Sum.inl (littleEndianBytes_inj h)
  | .inr _, .inr _, _, h => congrArg Sum.inr (littleEndianBytes_inj h)
  | .inl _, .inr _, h, _ => absurd (show bottomLayer = topLayer from h) (by decide)
  | .inr _, .inl _, h, _ => absurd (show topLayer = bottomLayer from h) (by decide)

theorem chainPairIndex_lt (j : ChainPairIndex) : j.val < 2 ^ 23 :=
  lt_of_lt_of_le j.isLt (by decide)

theorem prfFields_inj :
    ∀ {x y : PrfDom}, prfFields x = prfFields y → prfSuffix x = prfSuffix y → x = y
  | .inl (), .inl (), _, _ => rfl
  | .inl _, .inr (.inl _), h, _ =>
    absurd (show BitVec.ofNat 5 5 = BitVec.ofNat 5 0 from congrArg (·.2.tag) h) (by decide)
  | .inl _, .inr (.inr _), h, _ =>
    absurd (show BitVec.ofNat 5 5 = BitVec.ofNat 5 7 from congrArg (·.2.tag) h) (by decide)
  | .inr (.inl _), .inl _, h, _ =>
    absurd (show BitVec.ofNat 5 0 = BitVec.ofNat 5 5 from congrArg (·.2.tag) h) (by decide)
  | .inr (.inl _), .inr (.inr _), h, _ =>
    absurd (show BitVec.ofNat 5 0 = BitVec.ofNat 5 7 from congrArg (·.2.tag) h) (by decide)
  | .inr (.inr _), .inl _, h, _ =>
    absurd (show BitVec.ofNat 5 7 = BitVec.ofNat 5 5 from congrArg (·.2.tag) h) (by decide)
  | .inr (.inr _), .inr (.inl _), h, _ =>
    absurd (show BitVec.ofNat 5 7 = BitVec.ofNat 5 0 from congrArg (·.2.tag) h) (by decide)
  | .inr (.inl (P, l, e, j)), .inr (.inl (P', l', e', j')), h, _ => by
    have hP : P = P' := congrArg (·.1) h
    have hhi : BitVec.ofNat 24 (layerHi l j) = BitVec.ofNat 24 (layerHi l' j') :=
      congrArg (·.2.hi) h
    have hlo : BitVec.ofNat 32 e.val = BitVec.ofNat 32 e'.val := congrArg (·.2.lo) h
    have hl : l = l' := by
      rw [← layerOf_layerHi l j (chainPairIndex_lt j), hhi,
        layerOf_layerHi l' j' (chainPairIndex_lt j')]
    have hj : j = j' := Fin.ext (by
      rw [← lowOf_layerHi l j (chainPairIndex_lt j), hhi,
        lowOf_layerHi l' j' (chainPairIndex_lt j')])
    have he : e = e' := by rw [← keyOf_ofNat e, hlo, keyOf_ofNat]
    rw [hP, hl, he, hj]
  | .inr (.inr (P, e, M)), .inr (.inr (P', e', M')), h, hs => by
    have hP : P = P' := congrArg (·.1) h
    have hhi : BitVec.ofNat 24 (layerHi M.layer 0) = BitVec.ofNat 24 (layerHi M'.layer 0) :=
      congrArg (·.2.hi) h
    have hlo : BitVec.ofNat 32 e.val = BitVec.ofNat 32 e'.val := congrArg (·.2.lo) h
    have hl : M.layer = M'.layer := by
      rw [← layerOf_layerHi M.layer 0 (by norm_num), hhi, layerOf_layerHi M'.layer 0 (by norm_num)]
    have he : e = e' := by rw [← keyOf_ofNat e, hlo, keyOf_ofNat]
    rw [hP, he, layerMsg_eq_of_layer_bytes hl hs]

/-- **Obligation (b)**: distinct formats have distinct bytes. -/
theorem prfFmt_injective : Props.KimFmtInjective prfFmt prfTrunc := by
  intro x y h
  have hf := congrArg (·.1) h
  obtain ⟨hP, hT⟩ := prfHead_inj (congrArg (·.1) hf)
  exact prfFields_inj (Prod.ext hP hT) (congrArg (·.2) hf)

theorem length_prfSuffix : ∀ x : PrfDom, (prfSuffix x).length ≤ 32
  | .inl _ => Nat.zero_le _
  | .inr (.inl _) => Nat.zero_le _
  | .inr (.inr (_, _, .inl m)) => (length_littleEndianBytes 32 m).le
  | .inr (.inr (_, _, .inr r)) => (length_littleEndianBytes 16 r).trans_le (by norm_num)

/-- **Obligation (a)**: every keyed input has at most `Qrom.maxLen` bytes. -/
theorem prfFmt_lengthLe : Props.KimLengthLe prfFmt prfKey Qrom.maxLen := by
  intro x S
  rw [prfInput_eq, length_thInput_eq, List.length_append, prfKey, length_littleEndianBytes]
  have := length_prfSuffix x
  simp only [Qrom.maxLen]
  omega

/-- Obligation (a) for the derived key's input `"leanXMSS" ‖ S_0`. -/
theorem length_prfSeedInput (S0 : MasterSeed) :
    (seedTag ++ prfSeedBytes S0).length ≤ Qrom.maxLen :=
  length_seedInput S0

/-- **The derived-key KIM-PRF advantage of leanXMSS** at the table `tab`: the seed `S_0`
uniform, the key `S = H("leanXMSS" ‖ S_0)`. -/
noncomputable abbrev xmssPrfAdv (W : OracleWorld) (tab : W.Tab)
    (B : Props.Adversary W (PrfDom →ₒ HashOutput) Unit Bool) : ℝ :=
  Props.derivedKimPrfAdv W seedTag prfSeedBytes prfKey prfFmt prfTrunc tab B

/-! ## The view of an ideal function -/

theorem truncateHash_setWidth (o : HashOutput) :
    truncateHash ((truncateHash o).setWidth 256) = truncateHash o := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj : j < 128 := hj
  have hj' : j < 256 := by omega
  simp only [truncateHash, digestBits, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  simp [hj, hj']

/-- The truncations keep the first 16 bytes. -/
theorem truncateHash_prfTrunc : ∀ (x : PrfDom) (o : HashOutput),
    truncateHash (prfTrunc x o) = truncateHash o
  | .inl _, o => truncateHash_setWidth o
  | .inr (.inl _), _ => rfl
  | .inr (.inr _), o => truncateHash_setWidth o

theorem prfTrunc_chainPair (t : PublicParameter × Layer × KeyIndex × ChainPairIndex)
    (o : HashOutput) : prfTrunc (.inr (.inl t)) o = o :=
  rfl

/-- **The view of a function on the formats**: the parameter `P` (the first half of the
parameter format's value), the chain starts at `P` (the halves of the chain pairs' values) and
the randomizer bases at `P` (the first halves of the randomizer formats' values). -/
def prfView (f : PrfDom → HashOutput) : IdealKey :=
  let P : PublicParameter := truncateHash (f (.inl ()))
  (P, fun l e i ↦ hashHalfForChain i.val (f (.inr (.inl (P, l, e, chainPair i)))),
    fun eM ↦ truncateHash (f (.inr (.inr (P, eM)))))

/-- The view depends only on the ideal answers `prfTrunc x (f x)` (`Props.prfIdeal` with
`post = prfTrunc`). -/
theorem prfView_prfTrunc (f : PrfDom → HashOutput) :
    prfView (fun x ↦ prfTrunc x (f x)) = prfView f := by
  simp only [prfView, truncateHash_prfTrunc, prfTrunc_chainPair]

/-- **The law of the view**: the view of a uniform function on the formats is a uniform ideal
secret. -/
theorem sum_prfView (G : IdealKey → ℝ≥0∞) :
    ∑ f : PrfDom → HashOutput, (Fintype.card (PrfDom → HashOutput) : ℝ≥0∞)⁻¹ * G (prfView f) =
      ∑ k : IdealKey, (Fintype.card IdealKey : ℝ≥0∞)⁻¹ * G k := by
  have h := unifAvg_view (fun o : HashOutput ↦ (truncateHash o : PublicParameter))
    (fun F ↦ unifAvg_fst hashSplit F) chainStartsEquiv
    (fun (x : KeyIndex × LayerMsg → HashOutput) b ↦ (truncateHash (x b) : Randomizer))
    (fun F ↦ unifAvg_fst (arrowHashSplit _) F) G
  exact h

end Quantum.StdModel.Xmss

end
