module

public import Quantum.StdModel.Props.Basic

@[expose] public section

/-!
# Pseudorandomness with classical queries: KIM-PRF and PRF_msg (design D1, D2)

The adversary is quantum, with superposition access to the world's hash ports, and gets
classical access to either a keyed function `F K` under a uniform key `K` (`prfReal`) or a uniform
random function on the same finite domain (`prfIdeal`); it outputs a bit. The advantage `prfAdv` is
the signed difference of the two probabilities of outputting `true`, so that it averages linearly
over tables.

This is the post-quantum PRF notion with classical queries (Zhandry, FOCS 2012, "standard
security" against quantum adversaries), relativized to an oracle world: the keyed function is
computed through the world's Keccak-256, to which the adversary also has quantum access. Only the
challenger evaluates `F`, so no quantum-query (QPRF) security is asked for.

* `kimFn` (KIM-PRF, D1): `F_K(x) = trunc x (H (a x ‖ K ‖ b x))` on a finite set of formats, the
  truncation per format; the ideal side answers the same truncations of a uniform function to
  256-bit digests (`prfIdeal` with `post = trunc`). With
  `a x` empty this is the outer-keyed (prefix-keyed) sponge of the keyed-sponge literature
  (Bertoni, Daemen, Peeters, Van Assche, SKEW 2011; Andreeva, Daemen, Mennink, Van Assche,
  FSE 2015; Gazi, Pietrzak, Tessaro, CRYPTO 2015; Mennink, Reyhanitabar, Vizar, ASIACRYPT 2015;
  quantum: Hosoyamada, ASIACRYPT 2025). The difference: the key follows a public prefix `a x`
  that the format fixes (for one-block inputs, key and prefix lie in the first rate block).
* `derivedKimFn` (D1, leanXMSS): the composite `F'_{S0}(x) = F_{H(pre ‖ S0)}(x)`; the derived
  key is never output, so the assumption is about the composite.
* `prefixFn` (PRF_msg, D2): `F_K(x) = trunc (H (K ‖ b x))`, the prefix-keyed sponge.

Instance obligations (`Props.Basic`): `KimFmtInjective fmt trunc` (otherwise two formats with
equal bytes and truncation distinguish real from ideal), and `KimLengthLe fmt keyBytes maxLen`
(every keyed input within the QROM domain cap; the same for the derived-key input of
`derivedKimFn`).
-/

open OracleComp OracleSpec

namespace Quantum.StdModel.Props

open HashSig

variable (W : OracleWorld) {Key Dom Rng : Type}

/-- **The real PRF challenger**: a uniform key `K`; the classical query `x` is answered by
`F K x`; the adversary's bit is the decision. -/
noncomputable def prfReal [SampleableType Key] (F : Key → Dom → OracleComp W.Oracles Rng) :
    Experiment W (Dom →ₒ Rng) Unit Bool where
  State := Key
  setup := sample W Key
  pub _ := ()
  answer K x := F K x
  judge _ _ b := pure b

/-- **The ideal PRF challenger**: a uniform function `f : Dom → U`; the classical query `x` is
answered by `post x (f x)` (`post` truncates per format; the identity for a plain random
function). -/
noncomputable def prfIdeal {U : Type} [Fintype Dom] [SampleableType U] (post : Dom → U → Rng) :
    Experiment W (Dom →ₒ Rng) Unit Bool where
  State := Dom → U
  setup := sample W (Dom → U)
  pub _ := ()
  answer f x := pure (post x (f x))
  judge _ _ b := pure b

/-- **PRF advantage with classical queries** at the table `tab` (signed):
`Pr[A → 1 | F_K] - Pr[A → 1 | post ∘ f]`. -/
noncomputable def prfAdv {U : Type} [SampleableType Key] [Fintype Dom] [SampleableType U]
    (F : Key → Dom → OracleComp W.Oracles Rng) (post : Dom → U → Rng) (tab : W.Tab)
    (A : Adversary W (Dom →ₒ Rng) Unit Bool) : ℝ :=
  ((prfReal W F).succAt tab A).toReal - ((prfIdeal W post).succAt tab A).toReal

/-- **The key-in-the-middle function** (D1): on the format `x` with prefix `(fmt x).1` and suffix
`(fmt x).2`, `F_K(x) = trunc x (H ((fmt x).1 ‖ K ‖ (fmt x).2))`, the truncation per format. -/
noncomputable def kimFn (fmt : Dom → HashInput × HashInput) (keyBytes : Key → HashInput)
    (trunc : Dom → HashOutput → Rng) (K : Key) (x : Dom) : OracleComp W.Oracles Rng :=
  trunc x <$> W.hash ((fmt x).1 ++ keyBytes K ++ (fmt x).2)

/-- **Obligation (b)**: distinct formats differ in their bytes or in their truncation. -/
def KimFmtInjective (fmt : Dom → HashInput × HashInput) (trunc : Dom → HashOutput → Rng) :
    Prop :=
  Function.Injective fun x ↦ (fmt x, trunc x)

/-- **Obligation (a) for KIM-PRF**: every keyed input has at most `n` bytes. -/
def KimLengthLe (fmt : Dom → HashInput × HashInput) (keyBytes : Key → HashInput) (n : ℕ) :
    Prop :=
  ∀ x K, ((fmt x).1 ++ keyBytes K ++ (fmt x).2).length ≤ n

/-- **The derived-key function** (D1, leanXMSS): the key is `S = H(pre ‖ S0)`, never output, and
`F'_{S0}(x) = F_S(x)` with the key-in-the-middle function `kimFn`. -/
noncomputable def derivedKimFn {Seed : Type} (pre : HashInput) (seedBytes : Seed → HashInput)
    (keyBytes : HashOutput → HashInput) (fmt : Dom → HashInput × HashInput)
    (trunc : Dom → HashOutput → Rng) (S0 : Seed) (x : Dom) : OracleComp W.Oracles Rng := do
  let S ← W.hash (pre ++ seedBytes S0)
  kimFn W fmt keyBytes trunc S x

/-- **The prefix-keyed function** (D2, PRF_msg): `F_K(x) = trunc (H (K ‖ b x))`, the
key-in-the-middle function with empty prefixes. -/
noncomputable def prefixFn (bytes : Dom → HashInput) (keyBytes : Key → HashInput)
    (trunc : HashOutput → Rng) : Key → Dom → OracleComp W.Oracles Rng :=
  kimFn W (fun x ↦ ([], bytes x)) keyBytes fun _ ↦ trunc

/-- **KIM-PRF advantage** (D1) at `tab`: against the same truncations of a uniform function to
256-bit digests. -/
noncomputable abbrev kimPrfAdv [SampleableType Key] [Fintype Dom]
    (fmt : Dom → HashInput × HashInput) (keyBytes : Key → HashInput)
    (trunc : Dom → HashOutput → Rng) (tab : W.Tab) (A : Adversary W (Dom →ₒ Rng) Unit Bool) :
    ℝ :=
  prfAdv W (kimFn W fmt keyBytes trunc) trunc tab A

/-- **Derived-key KIM-PRF advantage** (D1, leanXMSS) at `tab`: the seed `S0` uniform. -/
noncomputable abbrev derivedKimPrfAdv {Seed : Type} [SampleableType Seed] [Fintype Dom]
    (pre : HashInput) (seedBytes : Seed → HashInput) (keyBytes : HashOutput → HashInput)
    (fmt : Dom → HashInput × HashInput) (trunc : Dom → HashOutput → Rng) (tab : W.Tab)
    (A : Adversary W (Dom →ₒ Rng) Unit Bool) : ℝ :=
  prfAdv W (derivedKimFn W pre seedBytes keyBytes fmt trunc) trunc tab A

/-- **PRF_msg advantage** (D2) at `tab`. -/
noncomputable abbrev prfMsgAdv [SampleableType Key] [Fintype Dom]
    (bytes : Dom → HashInput) (keyBytes : Key → HashInput) (trunc : HashOutput → Rng)
    (tab : W.Tab) (A : Adversary W (Dom →ₒ Rng) Unit Bool) : ℝ :=
  prfAdv W (prefixFn W bytes keyBytes trunc) (fun _ ↦ trunc) tab A

end Quantum.StdModel.Props

end
