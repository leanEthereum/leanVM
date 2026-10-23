/-
  LeanVM.Protocol.Flock

  The Flock phase of the leanVM protocol: the Flock argument at leanVM's sizes and constants, on
  the instance's Flock region, at the spine's slot, with its completeness and the bound on its
  error.
-/

module

public import LeanVM.Parameters.Generator
public import LeanVM.Protocol.Spine.Errors
public import LeanVM.Protocol.Spine.Slots
public import LeanVM.Protocol.FlockFields
public import LeanVM.Protocol.ToArkLib.Flock.Reduction
public import LeanVM.Protocol.ToArkLib.Flock.Security

/-!
# The Flock phase

The fourth phase after the commitment (Annex C and Annex A, at leanVM pin
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`). The instance's Flock region is a column of
`2 ^ (8 + kBatch)` cells of `K`, each packing 64 bits of the BLAKE2s witness, and the phase
proves of it the predicate `FlockRegion.Holds`: every block of `2 ^ 14` bits satisfies the
region's R1CS and holds `1` at position `512`. It is the generic Flock argument
(`Flock.flock`) at `s = 6` skipped and packed coordinates, `m = 8` within-block coordinates,
`κ = kBatch` batch coordinates, the skip nodes `φ_8(0), …, φ_8(127)`, the seven fixed
coordinates of `LeanVM.Parameters.Flock`, and six ring-switching coefficients with shifts
`32, 16, 8, 4, 2, 1`. Its verifier reads no pooled claim: it hands the column claims on and adds
one weighted claim, `⟨W, q⟩ = T` with `T = Σ_{i < 64} x^i · Φ(s_i)` and `W` the combination of
the equality kernels at the Frobenius powers of the lincheck's point, lifted into the stack by
the instance's layout (`crates/verifier/src/lib.rs:271-281`, `crates/verifier/src/flock.rs:376-390`,
`verifier.py:1297-1342`; the prover's strided claim on the region is
`crates/leanvm_core/src/cpu/mod.rs:718-724`).
With no region, the phase hands the claims on.

* `flockPhase`: the phase, a typed front component at the slot `flockPhaseSlot`.
* `flockComplete`: its completeness from `Seam.pub` to `Seam.flock`.
* `flockSecurity`: its round-by-round knowledge soundness from `Seam.pub` to `Seam.flock`, at the
  slot's errors (`flockErrors`, summing to `(4·kBatch + 302 + 2^31 + 2^15) / |E|` along every path,
  `flockErrorsOf_bounded`), which dominate the proved ones challenge by challenge
  (`flockErrorsT_le_flockErrorsOf`).

The phase rests on two facts about leanVM's constants and fields: the 128 skip nodes are
distinct (`flockNodes_injective`, from the `F_2`-linearity of `φ_8` and a kernel check of its
127 nonzero images), and a cell of `K` is its bits packed by the powers of `x`
(`ofK_eq_sum_cellBit`, through CompPoly's bridge to `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`).
Its knowledge soundness rests on two more, from `LeanVM.Protocol.FlockFields`: the weights of
the fixed coordinates are `F_2`-independent, and ring switching is injective.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec

@[expose] public section

/-! ## Packing bits into `K` -/

/-- A cell of `K` is its bits packed by the powers of `x`: `a = Σ_{i < 64} a_i · x^i`. -/
theorem K.eq_sum_bits (a : K) :
    a = ∑ i : Fin 64, if a.toBitVec.getLsbD i then g ^ (i : ℕ) else 0 := by
  apply BF64.toQuot_injective
  have hg : BF64.toQuot g = AdjoinRoot.root BF64.basePoly := by
    rw [BF64.toQuot, BF64.toPolyBF64, g, K.ofBits, BF64.toBitVec_ofBitVec,
      show BitVec.ofNat 64 2 = (1 <<< 1 : BitVec 64) by decide,
      BinaryField.toPoly_one_shiftLeft 1 (by norm_num), pow_one, AdjoinRoot.mk_X]
  have hsum : ∀ (s : Finset (Fin 64)) (f : Fin 64 → K),
      BF64.toQuot (∑ i ∈ s, f i) = ∑ i ∈ s, BF64.toQuot (f i) := fun s f ↦ by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BF64.toQuot_add, ih]
  rw [hsum]
  conv_lhs => rw [BF64.toQuot, BF64.toPolyBF64, BinaryField.toPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [BitVec.getLsb, BitVec.getLsbD]
  split
  · rw [map_pow, AdjoinRoot.mk_X, BF64.toQuot_npow, hg]
  · rw [map_zero, BF64.toQuot_zero]

/-- The embedding of a cell in `E` is its bits packed by the powers of `x`. -/
theorem ofK_eq_sum_cellBit (a : K) :
    ofK a = ∑ i : Fin (2 ^ Flock.kSkip), ofK (g ^ i.val) * cellBit a i := by
  conv_lhs => rw [K.eq_sum_bits a]
  change algebraMap K E _ = _
  rw [map_sum (algebraMap K E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [cellBit]
  split <;> simp_all

/-- Entry `u` of the table of bit `i` is bit `i` of cell `u`. -/
theorem bitTable_getElem {n : ℕ} (c : Column n) (i : Fin (2 ^ Flock.kSkip)) (u : Fin (2 ^ n)) :
    (bitTable c i)[u] = cellBit c.values[u] i := by
  simp [bitTable, Vector.get_eq_getElem]

/-- A column of `K` is its bit tables packed by the powers of `x`, entry by entry. -/
theorem ofK_eq_sum_bitTable {n : ℕ} (c : Column n) (u : Fin (2 ^ n)) :
    ofK c.values[u] = ∑ i : Fin (2 ^ Flock.kSkip), ofK (g ^ i.val) * (bitTable c i)[u] := by
  simp only [bitTable_getElem]
  exact ofK_eq_sum_cellBit _

/-- The bits of a cell are `0` or `1`. -/
theorem cellBit_isBool (a : K) (i : ℕ) : cellBit a i = 0 ∨ cellBit a i = 1 := by
  unfold cellBit
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The bit tables hold `0`s and `1`s. -/
theorem bitTable_isBool {n : ℕ} (c : Column n) (i : Fin (2 ^ Flock.kSkip)) (u : Fin (2 ^ n)) :
    (bitTable c i)[u] = 0 ∨ (bitTable c i)[u] = 1 := by
  rw [bitTable_getElem]
  exact cellBit_isBool _ _

/-! ## The skip nodes -/

/-- `φ_8` is additive in its byte: it sums the basis images of the set bits. -/
theorem phi8_xor (a b : ℕ) : Flock.phi8 (a ^^^ b) = Flock.phi8 a + Flock.phi8 b := by
  simp only [Flock.phi8, ← Finset.sum_add_distrib, Nat.testBit_xor]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases a.testBit i <;> cases b.testBit i <;> simp [← two_mul, CharTwo.two_eq_zero]

/-- The nonzero bytes below `128` have nonzero images: a kernel check. -/
theorem phi8_ne_zero : ∀ b : Fin 128, b ≠ 0 → Flock.phi8 b ≠ 0 := by decide +kernel

/-- `φ_8` is injective on the bytes below `128`. -/
theorem phi8_injOn {a b : ℕ} (ha : a < 128) (hb : b < 128) (h : Flock.phi8 a = Flock.phi8 b) :
    a = b := by
  have hx : a ^^^ b < 128 := Nat.xor_lt_two_pow (n := 7) ha hb
  by_contra hne
  have hz : Flock.phi8 (a ^^^ b) = 0 := by
    rw [phi8_xor, h, CharTwo.add_self_eq_zero]
  refine phi8_ne_zero ⟨a ^^^ b, hx⟩ (fun h0 ↦ hne ?_) hz
  have h0' : a ^^^ b = 0 := congrArg Fin.val h0
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  have := congrArg (·.testBit i) h0'
  simpa [Nat.testBit_xor] using this

/-- The skip nodes `φ_8(0), …, φ_8(127)`: the skip domain, then its coset. -/
def flockNodes : Vector E (2 ^ Flock.kSkip + 2 ^ Flock.kSkip) :=
  Vector.ofFn fun i ↦ Flock.skipNode ⟨i.val, i.isLt⟩

/-- The skip nodes are distinct. -/
theorem flockNodes_injective :
    Function.Injective fun j : Fin (2 ^ Flock.kSkip + 2 ^ Flock.kSkip) ↦ flockNodes[j] := by
  intro a b h
  simp only [flockNodes, Fin.getElem_fin, Vector.getElem_ofFn, Flock.skipNode] at h
  exact Fin.ext (phi8_injOn a.isLt b.isLt (ofK_injective h))

/-! ## The argument at leanVM's sizes -/

/-- The skip domain: the nodes with their inverse Lagrange denominators, computed once. -/
def flockSkipDomain : Flock.SkipDomain E Flock.kSkip := Flock.SkipDomain.ofPts flockNodes

/-- leanVM's Flock parameters for `2 ^ k` compressions. -/
def flockParams (k : ℕ) : Flock.Params E where
  s := Flock.kSkip
  m := Flock.kIn
  κ := k
  nodes := flockSkipDomain
  nFix := 7
  nRand := k + 1
  fixed := Flock.fixedPoint
  hpoint := by simp only [Flock.kIn]; omega
  cpos := Flock.constPos

namespace FlockPhase

variable {I : M3Instance} (r : FlockRegion I.toShape)

/-- The region's 64 Boolean tables, read off the stack. -/
def bits (o : ∀ i, TheOracle I i) : Fin (2 ^ Flock.kSkip) → CMlPolynomialEval E (8 + r.kBatch) :=
  bitTable (I.flockColumn r (theStack o))

/-- The pooled column claims hold of the stack: what the phase carries along. -/
def side (s : I.Stmt × PubOut I) (o : ∀ i, TheOracle I i) : Prop :=
  ∀ c ∈ s.2.columns.toList, c.Holds (theStack o)

/-- A point of the region, lifted to the stack by the instance's layout. -/
def lift (p : Vector E (8 + r.kBatch)) : Vector E I.μ :=
  I.layout.extend r.col (Vector.cast r.height.symm p)

theorem flockClaims_eq_one (h : I.flock = some r) : I.flockClaims = 1 := by
  simp [M3Instance.flockClaims, h]

/-- The phase's output: the column claims, and the switched weighted claim. -/
def finish (h : I.flock = some r) (s : I.Stmt × PubOut I) (W : Weight E I.μ) (T : E) :
    I.Stmt × FlockOut I :=
  (s.1, ⟨s.2.columns, Vector.cast (flockClaims_eq_one r h).symm #v[⟨W, T⟩]⟩)

/-- The region's column of the stack is read through the lift. -/
theorem eval₂Mle_flockColumn (q : Column I.μ) (p : Vector E (8 + r.kBatch)) :
    eval₂Mle (I.flockColumn r q).values (algebraMap K E) p =
      eval₂Mle q.values (algebraMap K E) (lift r p) := by
  have h := eval₂Mle_cast (algebraMap K E) r.height (I.column q r.col).values
    (Vector.cast r.height.symm p)
  simp only [Vector.cast_cast, Vector.cast_rfl] at h
  rw [M3Instance.flockColumn, h, M3Instance.column, Layout.read_eval]
  rfl

end FlockPhase

variable (I : M3Instance)

/-! ## Errors and the switched claim -/

/-- `N / |E|`, counted by `Nat.card`, is `overE N`. -/
theorem overF_eq_overE (N : ℕ) : Flock.overF E N = overE N := by
  rw [Flock.overF, overE, Nat.card_eq_fintype_card]

/-- The switched claim is among the claims the phase hands on. -/
theorem FlockPhase.mem_weighted_finish {I : M3Instance} (r : FlockRegion I.toShape)
    (h : I.flock = some r) (s : I.Stmt × PubOut I) (W : Weight E I.μ) (T : E) :
    (⟨W, T⟩ : WeightedClaim I) ∈ (FlockPhase.finish r h s W T).2.weighted.toList := by
  simp only [FlockPhase.finish, Vector.toList_cast, Vector.toList_mk, List.mem_singleton]

/-! ## The phase -/

/-- The Flock phase on a region, typed. -/
def flockPhaseSome (r : FlockRegion I.toShape) (h : I.flock = some r) :
    Typed.Def (TheOracle I) (I.Stmt × PubOut I) Unit (I.Stmt × FlockOut I) Unit
      (flockSlotOf r.kBatch) :=
  Flock.flock (flockParams r.kBatch) r.r1cs (FlockPhase.bits r) FlockPhase.side 5
    (algebraMap K E) g (FlockPhase.lift r) (FlockPhase.finish r h)

/-- The Flock phase on the slot of a region or of none, typed. -/
def flockPhaseOpt : (o : Option (FlockRegion I.toShape)) → I.flock = o →
    Typed.Def (TheOracle I) (I.Stmt × PubOut I) Unit (I.Stmt × FlockOut I) Unit (flockSlotOpt I o)
  | none, h => Typed.passThrough _ fun s ↦
      (s.1, ⟨s.2.columns, Vector.cast (by simp [M3Instance.flockClaims, h]) #v[]⟩)
  | some r, h => flockPhaseSome I r h

/-- **The Flock phase on the typed framework**, at its slot `flockPhaseSlot I`. -/
def flockPhase : Typed.Def (TheOracle I) (I.Stmt × PubOut I) Unit (I.Stmt × FlockOut I) Unit
    (flockPhaseSlot I) :=
  flockPhaseOpt I I.flock rfl

/-- Typed completeness of the Flock phase on a slot. -/
theorem flockCompleteOpt : (o : Option (FlockRegion I.toShape)) → (h : I.flock = o) →
    Typed.Complete (flockPhaseOpt I o h) (Seam.pub I) (Seam.flock I)
  | none, h => Typed.passThroughComplete fun s o w hin ↦ by
      cases w
      exact ⟨hin.1, by simp⟩
  | some r, h =>
    Flock.flockComplete (flockParams r.kBatch) r.r1cs (FlockPhase.bits r) FlockPhase.side 5
      (algebraMap K E) g (FlockPhase.lift r) (FlockPhase.finish r h)
      (fun o ↦ (I.flockColumn r (theStack o)).values) (fun o ↦ (theStack o).values)
      flockNodes_injective (Seam.pub I) (Seam.flock I)
      (fun s o _ hin ↦ ⟨hin.1, hin.2 r (by rw [h]; rfl)⟩)
      (fun s o _ W T hside hpair ↦ ⟨hside, by
        simp only [FlockPhase.finish, Vector.toList_cast]
        intro c hc
        simp only [Vector.toList_mk, List.mem_singleton] at hc
        subst hc
        exact hpair⟩)
      (fun o u ↦ ofK_eq_sum_bitTable (I.flockColumn r (theStack o)) u)
      (fun o i u ↦ bitTable_isBool (I.flockColumn r (theStack o)) i u)
      (fun o p ↦ FlockPhase.eval₂Mle_flockColumn r (theStack o) p)

/-- **Completeness of the Flock phase on the typed framework.** -/
theorem flockComplete : Typed.Complete (flockPhase I) (Seam.pub I) (Seam.flock I) :=
  flockCompleteOpt I I.flock rfl

/-- The generic argument's typed errors are within the slot's on every challenge. -/
theorem flockErrorsT_le_flockErrorsOf (k : ℕ) :
    Typed.Errors.Le (flockSlotOf k).tree (flockSlotOf k).roles
      (Flock.flockErrorsT (flockParams k) 5) (flockErrorsOf k) := by
  have h1 : Flock.overF E 1 ≤ overE 1 := (overF_eq_overE 1).le
  have h2 : Flock.overF E 2 ≤ overE 2 := (overF_eq_overE 2).le
  refine Typed.Errors.Le.append _ _ (Typed.Errors.Le.append _ _ (Typed.Errors.Le.append _ _
    (Typed.Errors.Le.append _ _ (Typed.Errors.Le.append _ _ (Typed.Errors.Le.append _ _
    (Typed.Errors.Le.append _ _ (Typed.Errors.Le.append _ _ (Typed.Errors.Le.append _ _
    (Typed.drawsErrors_le E h1 _) (Typed.Errors.Le.refl _ _ _)) ?_)
    (Typed.roundsErrors_le E 2 h2 _))
    (Typed.roundsErrors_le E 2 (h2.trans (overE_mono (by norm_num))) _))
    (Typed.Errors.Le.refl _ _ _)) ?_)
    (Typed.roundsErrors_le E 2 h2 _)) (Typed.Errors.Le.refl _ _ _))
    (Typed.drawsErrors_le_of E 6 fun p _ ↦ h1.trans (overE_mono Nat.one_le_two_pow))
  · refine ⟨?_, fun _ ↦ trivial⟩
    rw [overF_eq_overE]
    exact overE_mono (by norm_num [flockParams, Flock.kSkip])
  · exact ⟨(overF_eq_overE 3).le, fun _ ↦ trivial⟩

/-- Typed knowledge soundness of the Flock phase on a slot. -/
def flockSecurityOpt : (o : Option (FlockRegion I.toShape)) → (h : I.flock = o) →
    Typed.Security (flockPhaseOpt I o h) (Seam.pub I) (Seam.flock I) (flockErrorsOpt I o)
  | none, h => Typed.passThroughSecurityOfIff fun s o ↦
      ⟨fun hout ↦ ⟨hout.1, fun r hr ↦ by simp [h] at hr⟩, fun hin ↦ ⟨hin.1, by simp⟩⟩
  | some r, h =>
    (Flock.flockSecurity (flockParams r.kBatch) r.r1cs (FlockPhase.bits r) FlockPhase.side 5
        (algebraMap K E) g (FlockPhase.lift r) (fun o ↦ (I.flockColumn r (theStack o)).values)
        (fun o ↦ (theStack o).values) (FlockPhase.finish r h) flockNodes_injective
        fixedWeights_independent (fun δ hδ ↦ ringSwitch_injective δ fun k hk ↦ hδ k hk)
        (Seam.pub I) (Seam.flock I)
        (fun s o ↦ ⟨fun hin ↦ ⟨hin.1, hin.2 r (by rw [h]; rfl)⟩,
          fun hin ↦ ⟨hin.1, fun r' hr' ↦ by
            rw [h] at hr'
            cases hr'
            exact hin.2⟩⟩)
        (fun s o W T hout ↦ by
          have h1 : FlockPhase.side s o := hout.1
          have h2 : WeightedClaim.Holds (theStack o) ⟨W, T⟩ :=
            hout.2 _ (FlockPhase.mem_weighted_finish r h s W T)
          exact ⟨h1, h2⟩)
        (fun o u ↦ ofK_eq_sum_bitTable (I.flockColumn r (theStack o)) u)
        (fun o i u ↦ bitTable_isBool (I.flockColumn r (theStack o)) i u)
        (fun o p ↦ FlockPhase.eval₂Mle_flockColumn r (theStack o) p)).mono
      (flockErrorsT_le_flockErrorsOf r.kBatch)

/-- **Knowledge soundness of the Flock phase on the typed framework**, at the slot's errors. -/
def flockSecurity : Typed.Security (flockPhase I) (Seam.pub I) (Seam.flock I) (flockErrors I) :=
  flockSecurityOpt I I.flock rfl

end
end LeanVM.Protocol
