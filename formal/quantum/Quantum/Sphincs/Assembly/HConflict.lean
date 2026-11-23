module

public import Quantum.Sphincs.Assembly.PrefixFacts
public import Quantum.Sphincs.Assembly.GameR
public import Quantum.Sphincs.Assembly.GameTCalls
public import Quantum.Sig.Sampled
public import Quantum.Sponge.Oracle.Hardwired.Mixed

@[expose] public section

/-!
# The mass of the `H_msg` conflict event

PrefixFacts' exception event `HConflict pub v` (two distinct held `H_msg` calls at their
messages' randomizers share their `h`-cell) is bounded here, averaged over the hidden values, at
the end of the canonical game `gameR strPol A pub v` (`hConflictMassP`, SP-ER's `hConflictMass`
with the same body).

The event depends only on the hardwired cells (`compressReg` is the identity there, so its
decompressed projector is diagonal: `decProj_eq_diagonal`), and the hardwired values are the
public keys': the only fresh data is the randomizer `R(M)`, hidden until `M` is first signed.

* **The realized runs** (`querySupportedOn_run_hmsgRev`, `progsQ_gameT`): on `HmsgSep`, a
  hardwired `H_msg` `k`-cell names a message whose randomizer and the root are in the memory label
  (`HmsgRev`). With `HSelfSep` (the two calls of one message never meet), the conflict is the
  store event `StoreConf` of the label's values (`storeConf_of_hConflict`,
  `trace_hConflict_le_embM`).
* **Lazy sampling** (`Quantum.Sig.Sampled`, `branch_run_sampled`): the average over `v` of the
  store event's weight is its weight at the end of the run of the template against the sampled
  runtime.
* **The sampled run** (`tsum_potential_run_le_charge`, a linear potential bound with a grade
  `hcGrade` and a charge `hcCharge`): the store event changes only at a reveal of a randomizer,
  which samples it fresh; with `n` randomizers stored, the new calls meet one of the `2n` stored
  `h`-cells for at most `12 n` of the randomizers (`card_fiber_storeConf_le`, `HZLoad pub`: at most
  three randomizers per `h`-cell). A game with at most `N` signing requests reveals at most `N`
  randomizers (`chgH_gameT`): `eventWeight_sampled_le`.
* **Result** (`uavg_hConflictMassP_le`): for each `pub` with `HZLoad pub`, the averaged conflict
  mass is at most `hConflictCap N = N · 12 N / 2^128 ≤ 2^-64` (`hConflictCap_le`) plus the fraction
  of the `v` without `HmsgSep pub v ∧ HSelfSep pub v`.
* **Key fractions** (`hZLoad_frac_le`, `hSelfSep_frac_le`, from `card_quad_le`, `card_pair_le`:
  resampling `k'` at distinct `k'`-cells, equal `k'`-cells forcing distinct `h`-cells): for every
  `PK.seed`, `π`, `h` (and `v`), the keys `(k, k')` violating `HZLoad` are at most
  `2^897 / |Z|^3 = 2^-639` of all, those violating `HSelfSep` at most `2^384 / |Z| = 2^-128`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w w₁

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message Randomizer PublicParameter)
open Quantum.Xmss (X Z blocks blocks_injective)
open Quantum.Xmss.Hybrid (LazyProg restrictTo ReadKeeps KeepsLab uavg querySupportedOn_queryStep
  progUpdate readKeeps_liftRead)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec readLift readLens realizeT revealThen progThen
  RevealVals memLab liftRead runtimeR Disc cmdNeed cmdGain rnK rnZ rnK_zero)

/-! ## A linear potential bound with a grade and a charge -/

namespace Quantum.Sponge

section potential

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {Ω : QReg → Type w} {Zk : Type} [Fintype Zk] (K : Matrix Zk R.D ℂ)
  (g : R.D → ℕ) (κ : spec.Port → ℕ) (N : ℕ) (δ : ℝ≥0∞)

/-- **A linear potential bound.** Let every step raise the grade `g` of the support by at most the
port's charge `κ i`, and every port raise the potential by at most `κ i · δ · tr σ` on inputs of
grade `t` with `t + κ i ≤ N`. From a state of grade `t`, a program within the charge budget `n`,
`t + n ≤ N`, ends with summed potential at most the initial one plus `n δ tr ρ`. -/
theorem tsum_potential_run_le_charge
    (hg : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + κ i))
          ((R.step i).branch r σ))
    (hd : ∀ i t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ), σ.PosSemidef →
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ → t + κ i ≤ N →
        ∑' r, potential K ((R.step i).branch r σ) ≤
          potential K σ + (κ i : ℝ≥0∞) * δ * ENNReal.ofReal σ.trace.re)
    {A : QReg} (x : QuantumComp L spec Ω A) (n t : ℕ)
    (hx : IFreeM.IsChargeBound x (portCharge κ) n) (htn : t + n ≤ N)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hρg : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    ∑' p, potential K ((R.run I x).branch p ρ) ≤
      potential K ρ + (n : ℝ≥0∞) * δ * ENNReal.ofReal ρ.trace.re := by
  classical
  induction x using QuantumComp.inductionOn generalizing n t with
  | pure B y =>
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, Ω u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply]
        simp [potential],
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
    exact le_self_add
  | primBind B o k ih =>
    have hρb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    have hL : ∀ p, potential K ((R.run I (QuantumComp.primBind o k)).branch p ρ) =
        ∑' b, potential K ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)) :=
      fun p ↦ by
        rw [run_primBind, DSubInstrument.branch_bind_apply]
        exact potential_tsum K ((((I o).frame R.D).isCPTNIFamily.comp_eval
          (fun b ↦ (R.run I (k b)).isCPTNIFamily) p).summable_apply ρ)
          fun b ↦ (R.run I (k b)).posSemidef_branch_apply p (hρb b)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_primBind_iff] at hx
    calc ∑' b, ∑' p, potential K ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ))
        ≤ ∑' b, (potential K (((I o).frame R.D).branch b ρ) + (n : ℝ≥0∞) * δ *
            ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re) :=
          ENNReal.tsum_le_tsum fun b ↦ ih b n t (hx b) htn (hρb b) (hρg.amplify_snd _)
      _ ≤ potential K ρ + (n : ℝ≥0∞) * δ * ENNReal.ofReal ρ.trace.re := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
          gcongr
          · exact tsum_potential_frame_le K (I o) hρ
          · exact ((I o).frame R.D).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
  | queryBind B i E ℓ k ih =>
    have hρr := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
    have hL : ∀ p, potential K ((R.run I (QuantumComp.queryBind i E ℓ k)).branch p ρ) =
        ∑' r, potential K ((R.run I (k r)).branch p ((R.queryStep i E ℓ).branch r ρ)) :=
      fun p ↦ by
        rw [run_queryBind, DSubInstrument.branch_bind_apply]
        exact potential_tsum K (((R.queryStep i E ℓ).isCPTNIFamily.comp_eval
          (fun r ↦ (R.run I (k r)).isCPTNIFamily) p).summable_apply ρ)
          fun r ↦ (R.run I (k r)).posSemidef_branch_apply p (hρr r)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_queryBind_iff] at hx
    obtain ⟨hκ, hk⟩ := hx
    have hσ := posSemidef_callInput ℓ hρ
    have hσg : QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t)
        (callInput ℓ R.D ρ) := hρg.callInput ℓ
    have hρrg : ∀ r, QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ g m.2)
        (Set.Iic (t + κ i)) ((R.queryStep i E ℓ).branch r ρ) := fun r ↦
      querySupportedOn_queryStep R g i r (fun σ hσ' ↦ hg i r t σ hσ') E ℓ hρg
    have hpot : ∑' r, potential K ((R.queryStep i E ℓ).branch r ρ) =
        ∑' r, potential K ((R.step i).branch r (callInput ℓ R.D ρ)) :=
      tsum_congr fun r ↦ potential_queryStep R K i E ℓ r ρ
    have htr : ∑' r, ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re ≤
        ENNReal.ofReal ρ.trace.re := (R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    have hd0 := hd i t _ hσ hσg (by omega)
    rw [potential_callInput, trace_callInput, ← hpot] at hd0
    calc ∑' r, ∑' p, potential K ((R.run I (k r)).branch p ((R.queryStep i E ℓ).branch r ρ))
        ≤ ∑' r, (potential K ((R.queryStep i E ℓ).branch r ρ) + ((n - κ i : ℕ) : ℝ≥0∞) * δ *
            ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re) :=
          ENNReal.tsum_le_tsum fun r ↦ ih r (n - κ i) (t + κ i) (hk r) (by omega) (hρr r) (hρrg r)
      _ ≤ (potential K ρ + (κ i : ℝ≥0∞) * δ * ENNReal.ofReal ρ.trace.re) +
            ((n - κ i : ℕ) : ℝ≥0∞) * δ * ENNReal.ofReal ρ.trace.re := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
          gcongr
      _ = potential K ρ + (n : ℝ≥0∞) * δ * ENNReal.ofReal ρ.trace.re := by
          rw [add_assoc, ← add_mul, ← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hκ]

end potential

end Quantum.Sponge

namespace Quantum.Sphincs.Assembly

/-! ## Diagonal projectors -/

section diag

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [Fintype β] in
theorem hc_one_kronecker_diagonal (f : β → ℂ) :
    (1 : Matrix α α ℂ) ⊗ₖ diagonal f = diagonal fun x : α × β ↦ f x.2 := by
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  simp only [one_mul]

/-- The trace of a state conjugated by a diagonal `0`/`1` projector. -/
theorem hc_trace_conj_diagonal_ind (P : β → Prop) [DecidablePred P] (ρ : Matrix β β ℂ) :
    (MatrixMap.conj (diagonal fun b ↦ if P b then (1 : ℂ) else 0) ρ).trace =
      ∑ b, if P b then ρ b b else 0 := by
  rw [MatrixMap.conj_apply, Matrix.trace_mul_cycle, diagonal_conjTranspose, diagonal_mul_diagonal,
    Matrix.trace]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [diag_apply, diagonal_mul, Pi.star_apply]
  split_ifs <;> simp

theorem hc_re_diag_nonneg {γ : Type} [Fintype γ] {ρ : Matrix γ γ ℂ} (hρ : ρ.PosSemidef) (x : γ) :
    0 ≤ (ρ x x).re :=
  (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := x))).1

/-- **Comparing diagonal events on the support**: if on the support `S` of the register every
state of `E` is in `E'`, the weight of `E` is at most that of `E'`. -/
theorem hc_trace_conj_diag_le {E E' : β → Prop} [hE : DecidablePred E] [hE' : DecidablePred E']
    {S : Set β}
    {ρ : Matrix (α × β) (α × β) ℂ} (hρ : ρ.PosSemidef)
    (hS : QuerySupportedOn (fun m : α × β ↦ m.2) S ρ) (h : ∀ b ∈ S, E b → E' b) :
    (MatrixMap.conj ((1 : Matrix α α ℂ) ⊗ₖ diagonal fun b ↦ if E b then (1 : ℂ) else 0)
        ρ).trace.re ≤
      (MatrixMap.conj ((1 : Matrix α α ℂ) ⊗ₖ diagonal fun b ↦ if E' b then (1 : ℂ) else 0)
        ρ).trace.re := by
  have h1 := hc_trace_conj_diagonal_ind (fun x : α × β ↦ E x.2) ρ
  have h2 := hc_trace_conj_diagonal_ind (fun x : α × β ↦ E' x.2) ρ
  rw [hc_one_kronecker_diagonal, hc_one_kronecker_diagonal, h1, h2, Complex.re_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  by_cases hx : ρ x x = 0
  · simp [hx]
  · have hxS := (hS x x hx).1
    by_cases hE : E x.2
    · simp [hE, h _ hxS hE]
    · simp only [hE, ↓reduceIte, Complex.zero_re]
      split_ifs
      · exact hc_re_diag_nonneg hρ x
      · exact le_rfl

theorem hc_conj_psd {α β : Type} [Fintype α] [Fintype β] (K : Matrix β α ℂ)
    {ρ : Matrix α α ℂ} (hρ : ρ.PosSemidef) : (MatrixMap.conj K ρ).PosSemidef := by
  rw [MatrixMap.conj_apply]
  exact hρ.mul_mul_conjTranspose_same K

theorem hc_trace_conj_re_nonneg {α β : Type} [Fintype α] [Fintype β] (K : Matrix β α ℂ)
    {ρ : Matrix α α ℂ} (hρ : ρ.PosSemidef) : 0 ≤ (MatrixMap.conj K ρ).trace.re :=
  (Complex.nonneg_iff.mp (hc_conj_psd K hρ).trace_nonneg).1

end diag

/-! ## The decompressed projector of an event of the hardwired cells -/

section decomp

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **The decompressed projector of an event of the hardwired cells and memory** is its diagonal
projector: `compressReg` acts on the databases only. -/
theorem decProj_eq_diagonal (E : Set (HwReg X Z M)) [hdec : DecidablePred (· ∈ E)]
    (hE : ∀ s s' : HwReg X Z M, s.2 = s'.2 → (s ∈ E ↔ s' ∈ E)) :
    compressReg X Z M * diagonal (fun s ↦ if s ∈ E then (1 : ℂ) else 0) * compressReg X Z M =
      diagonal fun s ↦ if s ∈ E then (1 : ℂ) else 0 := by
  classical
  let f : Hw X Z × M → ℂ := fun b ↦ if ((Database.empty, Database.empty, Database.empty), b) ∈ E
    then 1 else 0
  have hd : (diagonal fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0) =
      (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ) ⊗ₖ diagonal f := by
    rw [hc_one_kronecker_diagonal]
    congr 1
    funext s
    simp only [f]
    have he := hE s ((Database.empty, Database.empty, Database.empty), s.2) rfl
    by_cases hs : s ∈ E
    · simp [hs, he.mp hs]
    · simp [hs, mt he.mpr hs]
  rw [hd, compressReg, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
    compressDbs_mul_self, Matrix.one_mul, Matrix.mul_one]

end decomp

/-! ## The `H_msg` cells at a randomizer -/

section cells

variable (pub : Pub)

/-- The `h`-cell of `H_msg` call `i` on `M` at the randomizer `R`, at the values `f` (only the root
matters, `hZf_congr`). -/
def hZf (f : ValPos → Digest) (M : Message) (i : DigestCall) (R : Randomizer) : Z :=
  rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (slotBlk pub.seed (.hmsg R M i) f) 0

theorem hZ_eq_hZf (v : (s : HPos) → XD s) (M : Message) (i : DigestCall) :
    hZ pub v M i = hZf pub (valsOf v) M i (v (.rnd M)) :=
  rfl

theorem slotBlk_hmsg_congr {f g : ValPos → Digest} (h : f rootPos = g rootPos) (R : Randomizer)
    (M : Message) (i : DigestCall) :
    slotBlk pub.seed (.hmsg R M i) f = slotBlk pub.seed (.hmsg R M i) g := by
  funext j
  unfold slotBlk
  rw [slotInput_congr pub.seed (g := g) fun p hp ↦ by
    simp only [slotNeed, Finset.mem_singleton] at hp
    subst hp
    exact h]

theorem hZf_congr {f g : ValPos → Digest} (h : f rootPos = g rootPos) (M : Message)
    (i : DigestCall) (R : Randomizer) : hZf pub f M i R = hZf pub g M i R := by
  unfold hZf
  rw [slotBlk_hmsg_congr pub h]

/-- **Good public data: every `H_msg` `h`-cell is hit by at most three randomizers**, for every
root, message and call (`hZLoad_frac_le`). -/
def HZLoad : Prop :=
  ∀ (f : ValPos → Digest) (M : Message) (i : DigestCall) (z : Z),
    (Finset.univ.filter fun R : Randomizer ↦ hZf pub f M i R = z).card ≤ 3

/-- **Good data: the two `H_msg` calls on a message at any randomizer have distinct `h`-cells**, at
the root of `v` (`hSelfSep_frac_le`). -/
def HSelfSep (v : (s : HPos) → XD s) : Prop :=
  ∀ (M : Message) (R : Randomizer), hZf pub (valsOf v) M 0 R ≠ hZf pub (valsOf v) M 1 R

variable {pub}

/-- **An `H_msg` block names its message.** -/
theorem hmsg_blk_inj (v : (s : HPos) → XD s) {R R' : Randomizer} {M M' : Message}
    {i i' : DigestCall}
    (h : slotBlk pub.seed (.hmsg R M i) (valsOf v) 0 =
      slotBlk pub.seed (.hmsg R' M' i') (valsOf v) 0) :
    M = M' := by
  have ht : (evData pub v).honTail (.hmsg R M i) = (evData pub v).honTail (.hmsg R' M' i') := by
    rw [honTail_hmsg, honTail_hmsg, rnK_zero, rnK_zero, h]
  exact (absorbTail_blocks_messageDigestInput_injective _ ht).2.2.2.1

end cells

/-! ## The realized runs: a held `H_msg` call is revealed -/

section rev

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **A hardwired `H_msg` `k`-cell names a revealed message**: its randomizer and the root are in
the memory label. -/
def HmsgRev {M : Type} (d : HwReg X Z (Finset HPos × M)) : Prop :=
  ∀ msg i, d.2.1.2.1 (hBlk pub v msg i 0) ≠ none →
    HPos.rnd msg ∈ d.2.2.1 ∧ HPos.val rootPos ∈ d.2.2.1

/-- A template program port whose realized cell is an `H_msg` `k`-cell needs the message's
randomizer and the root. -/
def PortRev (p : LazyProg X Z HPos XD) : Prop :=
  ∀ msg i, progPt (p.realize v) = .k (hBlk pub v msg i 0) →
    HPos.rnd msg ∈ p.need ∧ HPos.val rootPos ∈ p.need

end rev

/-! ## Templates whose program ports satisfy a condition -/

section progsQ

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  (Q : LazyProg X Z HPos XD → Prop)

/-- The condition on a command: a program port satisfies `Q`. -/
def CmdQ {A : QReg} : QuantumComp.Cmd L (SSpec M) A → Prop
  | .query (.inl (.inr p)) _ _ => Q p.1
  | _ => True

/-- **A template whose program ports all satisfy `Q`.** -/
def ProgsQ : {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A → Prop
  | _, .pure _ => True
  | _, .liftBind c next => CmdQ Q c ∧ ∀ b, ProgsQ (next b)

omit [Fintype M] [DecidableEq M] in
theorem progsQ_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A) :
    ProgsQ Q (e ▸ y) ↔ ProgsQ Q y := by
  subst e
  rfl

omit [Fintype M] [DecidableEq M] in
theorem progsQ_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Y u)
    (hx : ProgsQ Q x) (hg : ∀ u a, ProgsQ Q (g u a)) : ProgsQ Q (x.bind g) := by
  induction x using IFreeM.inductionOn with
  | pure _ a => exact hg _ a
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

omit [Fintype M] [DecidableEq M] in
theorem progsQ₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (SSpec M) A B α) (g : α → QuantumComp₂ L (SSpec M) B B' β)
    (hx : ProgsQ Q x) (hg : ∀ a, ProgsQ Q (g a)) : ProgsQ Q (x.bind g) := by
  refine progsQ_bind Q x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

omit [Fintype M] [DecidableEq M] in
theorem progsQ_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (SSpec M)))
    (hσ : ∀ A c, ProgsQ Q (σ A c)) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) : ProgsQ Q (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact progsQ_bind Q _ _ (hσ s c) fun u ans ↦ (progsQ_cast Q ans.2 _).mpr (ih ans.1)

omit [Fintype M] [DecidableEq M] in
theorem progsQ_readLift {A : QReg} (y : QuantumComp L (hwReadSpec X Z M) Ω A) :
    ProgsQ Q (readLift goodAll y) := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind _ c next ih =>
    show ProgsQ Q (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _⟩
    · exact ⟨trivial, fun b ↦ ih _⟩
    · exact ⟨trivial, fun b ↦ ih _⟩

omit [Fintype M] [DecidableEq M] in
theorem progsQ_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    ProgsQ Q (QComp.act (spec := SSpec M) p) :=
  ⟨trivial, fun _ ↦ trivial⟩

omit [Fintype M] [DecidableEq M] in
theorem progsQ_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α)
    (hk : ∀ r, ProgsQ Q (k r)) : ProgsQ Q (revealThen goodAll T k) :=
  ⟨trivial, fun r ↦ progsQ₂_bind Q _ _ (progsQ_act Q _) fun _ ↦ hk r.down⟩

omit [Fintype M] [DecidableEq M] in
theorem progsQ_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) (hpQ : Q p) (hk : ProgsQ Q k) :
    ProgsQ Q (progThen p hp k) :=
  ⟨hpQ, fun _ ↦ progsQ₂_bind Q _ _ (progsQ_act Q _) fun _ ↦ hk⟩

omit [Fintype M] [DecidableEq M] in
theorem progsQ_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) (h : ∀ p ∈ ps, Q p) :
    ProgsQ Q (progPorts M B ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact progsQ_progThen Q p trivial _ (h p List.mem_cons_self)
      (ih fun p' hp' ↦ h p' (List.mem_cons_of_mem _ hp'))

omit [Fintype M] [DecidableEq M] in
theorem progsQ_progSlots (pub : Pub) (B : QReg) (ss : List Slot)
    (h : ∀ s ∈ ss, ∀ p ∈ slotPorts pub s, Q p) : ProgsQ Q (progSlots M pub B ss) := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    exact progsQ₂_bind Q _ _ (progsQ_progPorts Q B _ (h s List.mem_cons_self)) fun _ ↦
      ih fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')

end progsQ

/-! ## The game's program ports need what they hardwire -/

section portRev

/- Membership in the concrete FORS opening's sets is otherwise decided by evaluating them. -/
attribute [local irreducible] forsNeed forsSlots

variable {pub : Pub} {v : (s : HPos) → XD s}

/-- **An in-table slot's port** never programs an `H_msg` `k`-cell (on `HmsgSep`). -/
theorem portRev_slotPorts (hsep : HmsgSep pub v) {s : Slot} (hs : InTable s)
    {p : LazyProg X Z HPos XD} (hp : p ∈ slotPorts pub s) : PortRev pub v p := by
  intro msg i h
  exfalso
  obtain ⟨s', hs', hpt, -⟩ := slotPorts_pt (pub := pub) (ss := [s]) v
    (fun s₁ h₁ ↦ by rw [List.mem_singleton.mp h₁]; exact hs) (c := p.realize v)
    (List.mem_map.2 ⟨p, List.mem_flatMap.2 ⟨s, List.mem_singleton_self _, hp⟩, rfl⟩)
  rw [List.mem_singleton.mp hs'] at hpt
  rw [h] at hpt
  obtain ⟨j, hj, hq | hq | hq⟩ := hpt
  · exact hsep (v (.rnd msg)) msg i s hs j hj (SpongeQuery.k.inj hq).symm
  · cases hq
  · cases hq

/-- **An `H_msg` port** needs the randomizer of the message whose `k`-cell it programs. -/
theorem portRev_digestPorts {pol : DigestPolicy} {T : Finset HPos} {msg : Message}
    {p : LazyProg X Z HPos XD} (hp : p ∈ digestPorts pub pol T msg) : PortRev pub v p := by
  intro M i h
  obtain ⟨i', hpt, -⟩ := digestPorts_pt v (c := p.realize v) (List.mem_map.2 ⟨p, hp, rfl⟩)
  rw [h] at hpt
  obtain ⟨j, hj, hq | hq | hq⟩ := hpt
  · obtain rfl : j = 0 := by omega
    have hq' : slotBlk pub.seed (.hmsg (v (.rnd M)) M i) (valsOf v) 0 =
        slotBlk pub.seed (.hmsg (v (.rnd msg)) msg i') (valsOf v) 0 := by
      have := SpongeQuery.k.inj hq
      rw [show (cellK pub (hBlk pub v msg i') 0).1 = hBlk pub v msg i' 0 from rnK_zero _ _ _ _ _]
        at this
      exact this
    obtain rfl := hmsg_blk_inj v hq'
    have hneed : p.need = hmsgNeed pol T M 0 ∨ p.need = hmsgNeed pol T M 1 := by
      rcases List.mem_append.mp hp with hp | hp
      · exact Or.inl (need_of_mem_hmsgPorts pub hp)
      · exact Or.inr (need_of_mem_hmsgPorts pub hp)
    rcases hneed with hn | hn <;> rw [hn] <;> simp [hmsgNeed]
  · cases hq
  · cases hq

variable (hsep : HmsgSep pub v)
include hsep

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M) (pol : DigestPolicy)

omit [Fintype M] [DecidableEq M] in
theorem progsQ_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    ProgsQ (PortRev pub v) (forsOpenT M pub B idx lv) :=
  progsQ_revealThen _ _ _ fun _ ↦ progsQ₂_bind _ _ _ (progsQ_progSlots _ pub B _
    fun _ hs _ hp ↦ portRev_slotPorts hsep (inTable_of_mem_forsSlots hs) hp) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem progsQ_signLayerT (B : QReg) (K : Key) (hK : KeyIn K) :
    ProgsQ (PortRev pub v) (signLayerT M upd pub B K) := by
  refine progsQ_revealThen _ _ _ fun _ ↦ progsQ₂_bind _ _ _ (progsQ_readLift _ _) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · trivial
  · exact progsQ_revealThen _ _ _ fun _ ↦ progsQ₂_bind _ _ _ (progsQ_progSlots _ pub B _
      fun _ hs _ hp ↦ portRev_slotPorts hsep (inTable_of_mem_layerSlots hK hs) hp) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem progsQ_signT (B : QReg) (msg : Message) :
    ProgsQ (PortRev pub v) (signT M upd pol pub B msg) := by
  refine progsQ_revealThen _ _ _ fun r₁ ↦ progsQ_revealThen _ _ _ fun r₂ ↦ ?_
  refine progsQ₂_bind _ _ _ (progsQ_progPorts _ B _ fun _ hp ↦ portRev_digestPorts hp) fun _ ↦ ?_
  refine progsQ₂_bind _ _ _ (progsQ_forsOpenT hsep B _ _) fun _ ↦ ?_
  refine progsQ₂_bind _ _ _ (progsQ_signLayerT hsep upd B _ (keyIn_keyOf _ _)) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · trivial
  · refine progsQ₂_bind _ _ _ (progsQ_signLayerT hsep upd B _ (keyIn_keyOf _ _)) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · trivial
    · refine progsQ₂_bind _ _ _ (progsQ_signLayerT hsep upd B _ (keyIn_keyOf _ _)) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> trivial

omit [Fintype M] [DecidableEq M] in
theorem progsQ_challengeT (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    ProgsQ (PortRev pub v) (challengeT M upd pol pub A c) := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact progsQ_readLift _ _
  · exact progsQ_readLift _ _
  · exact progsQ_bind _ _ _ (progsQ₂_bind _ _ _ (progsQ_act _ _) fun _ ↦
      progsQ_signT hsep upd pol _ msg) fun _ _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The game's program ports need what they hardwire** (on `HmsgSep`). -/
theorem progsQ_gameT (A : SAdversary) : ProgsQ (PortRev pub v) (gameT M upd pol pub A) :=
  progsQ_revealThen _ _ _ fun _ ↦ progsQ₂_bind _ _ _
    (progsQ_substitute _ _ (progsQ_challengeT hsep upd pol) _) fun _ ↦
      progsQ₂_bind _ _ _ (progsQ_readLift _ _) fun _ ↦ trivial

end portRev

/-! ## The realized runs keep `HmsgRev` -/

section supp

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  (pub : Pub) (v : (s : HPos) → XD s)

omit [Fintype M] [DecidableEq M] in
theorem labKeep_of_readKeeps (c : HwRead X Z (Finset HPos × M)) (h : ReadKeeps c) : LabKeep c := by
  cases c <;> exact h

/-- **Support of a composite's branch** from the supports of the continuation's branches. -/
theorem hc_querySupportedOn_branch_bind {A' : Type*} [Fintype A'] {ι κ : Type*} {B : ι → Type*}
    [∀ i, Fintype (B i)] {C : κ → Type*} [∀ c, Fintype (C c)] (d : DSubInstrument A' ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) (c : κ) (ρ : Matrix A' A' ℂ) {Y : Type*}
    {q : C c → Y} {S' : Set Y} (h : ∀ i, QuerySupportedOn q S' ((k i).branch c (d.branch i ρ))) :
    QuerySupportedOn q S' ((d.bind k).branch c ρ) := by
  rw [DSubInstrument.branch_bind_apply]
  exact QuerySupportedOn.tsum h

/-- **Along a realized template** that reveals before it programs, whose reads keep the label and
whose program ports need what they hardwire (`PortRev`), every branch is supported on
`HmsgRev`. -/
theorem querySupportedOn_run_hmsgRev (m₀ : Finset HPos × M) (I : L.Interp) {A : QReg}
    (y : QuantumComp L (SSpec M) Ω A) :
    ∀ T, Disc y T → ProgsQ (PortRev pub v) y → KeepsLab y →
      ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2)
        {s | HmsgRev pub v s ∧ T ⊆ s.2.2.1} ρ →
      ∀ p : Σ u, Ω u, QuerySupportedOn (fun m : p.1 × (runtimeR m₀).D ↦ m.2)
        {s | HmsgRev pub v s} (((runtimeR m₀).run I (realizeT v y)).branch p ρ) := by
  classical
  induction y using QuantumComp.inductionOn with
  | pure _ y =>
    intro T _ _ _ ρ hρ p
    show QuerySupportedOn _ _
      ((DSubInstrument.ret (fun p : Σ u, Ω u ↦ p.1 × (runtimeR m₀).D) ⟨_, y⟩).branch p ρ)
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.mono fun _ h ↦ h.1
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    intro T hd hq hk ρ hρ p
    show QuerySupportedOn _ _
      ((((I o).frame _).bind fun b ↦ (runtimeR m₀).run I (realizeT v (k b))).branch p ρ)
    refine hc_querySupportedOn_branch_bind ((I o).frame _)
      (fun b ↦ (runtimeR m₀).run I (realizeT v (k b))) p ρ fun b ↦ ?_
    have hd' : Disc (k b) (T ∪ ∅) := hd.2 (ULift.up b)
    rw [Finset.union_empty] at hd'
    exact ih b T hd' (hq.2 (ULift.up b)) (hk.2 (ULift.up b)) _
      (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _) p
  | queryBind _ i E ℓ k ih =>
    intro T hd hq hk ρ hρ p
    rcases i with ((i | ⟨c, hcm⟩) | ⟨p', hp'⟩) | T₀
    · have hs : StepR m₀ (.inl (.inl (.inl i)))
          (fun s ↦ HmsgRev pub v s ∧ T ⊆ s.2.2.1) (fun s ↦ HmsgRev pub v s ∧ T ⊆ s.2.2.1) :=
        stepR_sponge m₀ i fun r₀ r₁ he h ↦ by
          refine ⟨fun msg i' hm ↦ ?_, ?_⟩
          · rw [he] at hm ⊢
            exact h.1 msg i' hm
          · rw [he]
            exact h.2
      refine hc_querySupportedOn_branch_bind ((runtimeR m₀).queryStep (.inl (.inl (.inl i))) E ℓ)
        (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
      have hd' : Disc (k r) (T ∪ ∅) := hd.2 (ULift.up r)
      rw [Finset.union_empty] at hd'
      exact ih r T hd' (hq.2 (ULift.up r)) (hk.2 (ULift.up r)) _
        (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) (.inl (.inl (.inl i))) r
          (hs r) E ℓ hρ) p
    · have hs : StepR m₀ (.inl (.inl (.inr c)))
          (fun s ↦ HmsgRev pub v s ∧ T ⊆ s.2.2.1) (fun s ↦ HmsgRev pub v s ∧ T ⊆ s.2.2.1) :=
        stepR_readKeep m₀ ⟨c, hcm⟩ (labKeep_of_readKeeps c hk.1) fun r₀ r₁ h1 h2 h ↦ by
          refine ⟨fun msg i' hm ↦ ?_, ?_⟩
          · rw [h1] at hm
            rw [h2]
            exact h.1 msg i' hm
          · rw [h2]
            exact h.2
      refine hc_querySupportedOn_branch_bind
        ((runtimeR m₀).queryStep (.inl (.inl (.inr c))) E ℓ)
        (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
      have hd' : Disc (k r) (T ∪ ∅) := hd.2 (ULift.up r)
      rw [Finset.union_empty] at hd'
      exact ih r T hd' (hq.2 (ULift.up r)) (hk.2 (ULift.up r)) _
        (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) (.inl (.inl (.inr c))) r
          (hs r) E ℓ hρ) p
    · have hneed : p'.need ⊆ T := hd.1
      have hpq : PortRev pub v p' := hq.1
      have hd' : ∀ r, Disc (k r) T := fun r ↦ by
        have h' : Disc (k r) (T ∪ ∅) := hd.2 (ULift.up r)
        rwa [Finset.union_empty] at h'
      have hstep : StepR m₀ (.inl (.inr (p'.realize v)))
          (fun s ↦ HmsgRev pub v s ∧ T ⊆ s.2.2.1) (fun s ↦ HmsgRev pub v s ∧ T ⊆ s.2.2.1) :=
        stepR_prog m₀ (p'.realize v) fun r₀ r₁ he h ↦ by
          have hlab : r₁.2.2.1 = r₀.2.2.1 := by rw [he]
          refine ⟨fun msg i' hm ↦ ?_, hlab ▸ h.2⟩
          rw [hlab]
          by_cases hc : ∃ a, p'.realize v = .programK (hBlk pub v msg i' 0) a
          · obtain ⟨a, ha⟩ := hc
            have hr := hpq msg i' (by rw [ha]; rfl)
            exact ⟨h.2 (hneed hr.1), h.2 (hneed hr.2)⟩
          · refine h.1 msg i' ?_
            rw [he] at hm
            rwa [progUpdate_k_of_ne (fun a he' ↦ hc ⟨a, he'⟩)] at hm
      cases p' with
      | programH T₁ c₁ =>
        refine hc_querySupportedOn_branch_bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programH T₁ c₁).realize v))) E ℓ)
          (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
        exact ih r T (hd' r) (hq.2 (ULift.up r)) (hk.2 (ULift.up r)) _
          (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) _ r (hstep r) E ℓ hρ) p
      | programK T₁ c₁ =>
        refine hc_querySupportedOn_branch_bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programK T₁ c₁).realize v))) E ℓ)
          (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
        exact ih r T (hd' r) (hq.2 (ULift.up r)) (hk.2 (ULift.up r)) _
          (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) _ r (hstep r) E ℓ hρ) p
      | programK' T₁ c₁ =>
        refine hc_querySupportedOn_branch_bind ((runtimeR m₀).queryStep
          (.inl (.inr ((LazyProg.programK' T₁ c₁).realize v))) E ℓ)
          (fun r ↦ (runtimeR m₀).run I (realizeT v (k r))) p ρ fun r ↦ ?_
        exact ih r T (hd' r) (hq.2 (ULift.up r)) (hk.2 (ULift.up r)) _
          (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) _ r (hstep r) E ℓ hρ) p
    · have hs : StepR m₀ (.inr T₀)
          (fun s ↦ HmsgRev pub v s ∧ T ⊆ s.2.2.1)
          (fun s ↦ HmsgRev pub v s ∧ T ∪ T₀ ⊆ s.2.2.1) :=
        stepR_rec m₀ T₀ fun r₀ r₁ he h ↦ by
          have hlab : r₁.2.2.1 = r₀.2.2.1 ∪ T₀ := by rw [he]
          refine ⟨fun msg i' hm ↦ ?_, ?_⟩
          · rw [he] at hm
            obtain ⟨h1, h2⟩ := h.1 msg i' hm
            rw [hlab]
            exact ⟨Finset.mem_union_left _ h1, Finset.mem_union_left _ h2⟩
          · rw [hlab]
            exact Finset.union_subset_union h.2 subset_rfl
      refine hc_querySupportedOn_branch_bind ((runtimeR m₀).queryStep (.inr T₀) E ℓ)
        (fun m ↦ (runtimeR m₀).run I (realizeT v (k (restrictTo T₀ v, m)))) p ρ fun m ↦ ?_
      exact ih (restrictTo T₀ v, m) (T ∪ T₀) (hd.2 (ULift.up (restrictTo T₀ v, m)))
        (hq.2 (ULift.up (restrictTo T₀ v, m))) (hk.2 (ULift.up (restrictTo T₀ v, m))) _
        (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) (.inr T₀) m (hs m) E ℓ hρ) p

end supp

/-! ## The sampled register: the store event, the grade and the charge -/

section store

open Quantum.Sig (Store fill swapIn swapOpt)

variable (pub : Pub)

/-- **The store event**: two distinct `H_msg` calls on messages whose randomizers are stored share
their `h`-cell, at the stored values. -/
def StoreConf (σ : Store XD) : Prop :=
  ∃ (msg : Message) (i : DigestCall) (msg' : Message) (i' : DigestCall), msg ≠ msg' ∧
    ∃ R R' : Randomizer, σ (.rnd msg) = some R ∧ σ (.rnd msg') = some R' ∧
      hZf pub (valsOf (fill σ)) msg i R = hZf pub (valsOf (fill σ)) msg' i' R'

/-- The messages whose randomizer is in `T`. -/
@[irreducible] def rndMsgs (T : Finset HPos) : Finset Message :=
  Finset.univ.filter fun msg : Message ↦ HPos.rnd msg ∈ T

theorem mem_rndMsgs {T : Finset HPos} {msg : Message} : msg ∈ rndMsgs T ↔ HPos.rnd msg ∈ T := by
  unfold rndMsgs
  simp

/-- The number of messages whose randomizer is in `T`. -/
def rndCount (T : Finset HPos) : ℕ :=
  (rndMsgs T).card

/-- No randomizer coordinate. -/
def RndFree (T : Finset HPos) : Prop :=
  ∀ msg, HPos.rnd msg ∉ T

/-- The root and exactly one randomizer coordinate. -/
def RndOne (T : Finset HPos) : Prop :=
  HPos.val rootPos ∈ T ∧ ∃ msg, HPos.rnd msg ∈ T ∧ ∀ msg', HPos.rnd msg' ∈ T → msg' = msg

variable {pub}

theorem storeConf_congr {σ σ' : Store XD} (hr : ∀ msg, σ' (.rnd msg) = σ (.rnd msg))
    (h0 : σ' (.val rootPos) = σ (.val rootPos)) : StoreConf pub σ' ↔ StoreConf pub σ := by
  have hf : valsOf (fill σ') rootPos = valsOf (fill σ) rootPos := by
    show (σ' (.val rootPos)).getD _ = (σ (.val rootPos)).getD _
    rw [h0]
  constructor
  · rintro ⟨msg, i, msg', i', hne, R, R', h1, h2, he⟩
    refine ⟨msg, i, msg', i', hne, R, R', (hr msg).symm.trans h1, (hr msg').symm.trans h2, ?_⟩
    rwa [hZf_congr pub hf, hZf_congr pub hf] at he
  · rintro ⟨msg, i, msg', i', hne, R, R', h1, h2, he⟩
    refine ⟨msg, i, msg', i', hne, R, R', (hr msg).trans h1, (hr msg').trans h2, ?_⟩
    rwa [hZf_congr pub hf.symm, hZf_congr pub hf.symm] at he

theorem not_storeConf_of {σ : Store XD} (h : ∀ msg, σ (.rnd msg) = none) : ¬StoreConf pub σ := by
  rintro ⟨msg, -, -, -, -, R, -, h1, -, -⟩
  rw [h msg] at h1
  cases h1

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **The store holds exactly the label's coordinates**, and the label holds the root once it holds
a randomizer. -/
def StoreOK (x : Quantum.Sig.SReg X Z HPos XD M) : Prop :=
  (∀ s, x.2 s ≠ none ↔ s ∈ x.1.2.2.1) ∧
    ((∃ msg, HPos.rnd msg ∈ x.1.2.2.1) → HPos.val rootPos ∈ x.1.2.2.1)

open Classical in
/-- **The grade of the sampled register**: the number of revealed randomizers, or `N + 1` off
`StoreOK` or past `N`. -/
noncomputable def hcGrade (N : ℕ) (x : Quantum.Sig.SReg X Z HPos XD M) : ℕ :=
  if StoreOK x ∧ rndCount x.1.2.2.1 ≤ N then rndCount x.1.2.2.1 else N + 1

omit [Fintype M] [DecidableEq M] in
theorem hcGrade_le (N : ℕ) (x : Quantum.Sig.SReg X Z HPos XD M) : hcGrade N x ≤ N + 1 := by
  unfold hcGrade
  split_ifs with h
  · exact h.2.trans (Nat.le_succ N)
  · exact le_rfl

omit [Fintype M] [DecidableEq M] in
theorem hcGrade_le_of {N m : ℕ} {x : Quantum.Sig.SReg X Z HPos XD M} (h : StoreOK x)
    (hc : rndCount x.1.2.2.1 ≤ m) : hcGrade N x ≤ m := by
  unfold hcGrade
  split_ifs with h'
  · exact hc
  · have : ¬rndCount x.1.2.2.1 ≤ N := fun h'' ↦ h' ⟨h, h''⟩
    omega

omit [Fintype M] [DecidableEq M] in
theorem of_hcGrade_le {N t : ℕ} {x : Quantum.Sig.SReg X Z HPos XD M} (h : hcGrade N x ≤ t)
    (ht : t ≤ N) : StoreOK x ∧ rndCount x.1.2.2.1 ≤ t := by
  unfold hcGrade at h
  split_ifs at h with h'
  · exact ⟨h'.1, h⟩
  · omega

omit [Fintype M] [DecidableEq M] in
theorem hcGrade_congr (N : ℕ) {x x' : Quantum.Sig.SReg X Z HPos XD M}
    (h1 : x'.1.2.2.1 = x.1.2.2.1) (h2 : x'.2 = x.2) : hcGrade N x' = hcGrade N x := by
  unfold hcGrade StoreOK
  rw [h1, h2]

open Classical in
/-- **The charge of the sampled run**: one per reveal of the root with exactly one randomizer,
none for a reveal of no randomizer and for the other ports, and more than the budget for the
other reveals and for reads changing the label. -/
noncomputable def hcCharge (N : ℕ) : (SSpec M).Port → ℕ
  | .inl (.inl (.inl _)) => 0
  | .inl (.inl (.inr c)) => if ReadKeeps c.1 then 0 else N + 1
  | .inl (.inr _) => 0
  | .inr T => if RndFree T then 0 else if RndOne T then 1 else N + 1

end store

/-! ## The game's charge -/

section charge

open Quantum.Xmss.Assembly (rdCharge chg_act)

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  (N : ℕ)

omit [Fintype M] [DecidableEq M] in
theorem chg_rdCharge_zero {A : QReg} (y : QuantumComp L (hwReadSpec X Z M) Ω A) :
    IFreeM.IsChargeBound y (portCharge (rdCharge M 0 0)) 0 := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact IFreeM.isChargeBound_pure _ _
  | liftBind _ c next ih =>
    rcases c with o | ⟨i | c, E, ℓ⟩ <;> exact ⟨le_rfl, fun b ↦ ih b⟩

omit [Fintype M] [DecidableEq M] in
theorem chgH_readLift {A : QReg} (y : QuantumComp L (hwReadSpec X Z M) Ω A) :
    IFreeM.IsChargeBound (readLift goodAll y) (portCharge (hcCharge (M := M) N)) 0 := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodAll) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (hcCharge (M := M) N) s
      ((readLens goodAll).toFunA s cmd)) = portCharge (rdCharge M 0 0) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩
    · rfl
    · rfl
    · simp [readLens, portCharge, hcCharge, rdCharge, readKeeps_liftRead]
  rw [he]
  exact chg_rdCharge_zero y

omit [Fintype M] [DecidableEq M] in
theorem chgH_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (hcCharge N)) n) :
    IFreeM.IsChargeBound (revealThen goodAll T k) (portCharge (hcCharge N))
      (hcCharge (M := M) N (.inr T) + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right _ n,
    fun r ↦ ?_⟩
  rw [Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk r) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chgH_revealThen_free {B B' : QReg} {α : Type} (T : Finset HPos) (hT : RndFree T)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (hcCharge N)) n) :
    IFreeM.IsChargeBound (revealThen goodAll T k) (portCharge (hcCharge N)) n := by
  have h := chgH_revealThen N T k hk
  have h0 : hcCharge (M := M) N (.inr T) = 0 := by
    simp only [hcCharge, hT, ↓reduceIte]
  rwa [h0, Nat.zero_add] at h

omit [Fintype M] [DecidableEq M] in
theorem chgH_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) {n : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (hcCharge N)) n) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (hcCharge N)) n := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.zero_le _, fun r ↦ ?_⟩
  simp only [hcCharge, Nat.sub_zero]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chgH_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    IFreeM.IsChargeBound (progPorts M B ps) (portCharge (hcCharge N)) 0 := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact chgH_progThen N p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem chgH_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    IFreeM.IsChargeBound (progSlots M pub B ss) (portCharge (hcCharge N)) 0 := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgH_progPorts N B _) fun _ ↦ ih

theorem rndFree_valSet (T : Finset ValPos) : RndFree (valSet T) := fun msg h ↦ by
  rw [valSet, Finset.mem_map] at h
  obtain ⟨_, -, he⟩ := h
  cases he

theorem rndFree_singleton_val (q : ValPos) : RndFree {HPos.val q} := fun msg h ↦ by
  rw [Finset.mem_singleton] at h
  cases h

theorem rndFree_strPol_need (T : Finset HPos) (msg : Message) : RndFree (strPol.need T msg) := by
  intro M h
  unfold DigestPolicy.need strPol at h
  cases hs : streamIdx T msg <;> simp [hs] at h

theorem rndOne_root_rnd (msg : Message) : RndOne {HPos.val rootPos, HPos.rnd msg} := by
  refine ⟨by simp, msg, by simp, fun msg' h ↦ ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or] at h
  exact HPos.rnd.inj h

omit [Fintype M] [DecidableEq M] in
theorem hcCharge_root_rnd (msg : Message) :
    hcCharge (M := M) N (.inr {HPos.val rootPos, HPos.rnd msg}) = 1 := by
  have hnf : ¬RndFree {HPos.val rootPos, HPos.rnd msg} := fun h ↦ h msg (by simp)
  simp only [hcCharge, hnf, rndOne_root_rnd msg, ↓reduceIte]

variable (pub : Pub) (upd : TrialUpd M)

attribute [local irreducible] forsNeed forsSlots in
omit [Fintype M] [DecidableEq M] in
theorem chgH_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    IFreeM.IsChargeBound (forsOpenT M pub B idx lv) (portCharge (hcCharge N)) 0 :=
  chgH_revealThen_free N _ (rndFree_valSet _) _ fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgH_progSlots N pub B _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem chgH_signLayerT (B : QReg) (K : Key) :
    IFreeM.IsChargeBound (signLayerT M upd pub B K) (portCharge (hcCharge N)) 0 := by
  refine chgH_revealThen_free N _ (rndFree_singleton_val _) _ fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgH_readLift N _) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · trivial
  · exact chgH_revealThen_free N _ (rndFree_valSet _) _ fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgH_progSlots N pub B _) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **A signature reveals one randomizer** (with the root). -/
theorem chgH_signT (B : QReg) (msg : Message) :
    IFreeM.IsChargeBound (signT M upd strPol pub B msg) (portCharge (hcCharge N)) 1 := by
  unfold signT
  refine IFreeM.IsChargeBound.mono (chgH_revealThen N _ _ (n := 0) fun r₁ ↦ ?_)
    (le_of_eq (by rw [hcCharge_root_rnd]))
  refine chgH_revealThen_free N _ (rndFree_strPol_need _ _) _ fun r₂ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgH_progPorts N B _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgH_forsOpenT N pub B _ _)
    fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgH_signLayerT N pub upd B _)
    fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · trivial
  · refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgH_signLayerT N pub upd B _)
      fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · trivial
    · refine FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
        (chgH_signLayerT N pub upd B _) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> trivial

omit [Fintype M] [DecidableEq M] in
theorem chgH_challengeT (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    IFreeM.IsChargeBound (challengeT M upd strPol pub A c) (portCharge (hcCharge N))
      (cmdCharge signCharge A c) := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact IFreeM.IsChargeBound.mono (chgH_readLift N _) (Nat.zero_le _)
  · exact IFreeM.IsChargeBound.mono (chgH_readLift N _) (Nat.zero_le _)
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (FreeM₂.isChargeBound_bind
      (n₁ := 0) (chg_act _ _ 0) fun _ ↦ chgH_signT N pub upd _ msg) fun _ _ ↦
        IFreeM.isChargeBound_pure _ 0) ?_
    simp [cmdCharge, signCharge]

omit [Fintype M] [DecidableEq M] in
/-- **The game reveals at most `N` randomizers**, for an adversary with at most `N` signing
requests. -/
theorem chgH_gameT (A : SAdversary)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) N) :
    IFreeM.IsChargeBound (gameT M upd strPol pub A) (portCharge (hcCharge N)) N := by
  refine chgH_revealThen_free N _ (rndFree_singleton_val _) _ fun r₀ ↦ ?_
  have hx := isChargeBound_withSignLog (hsign (pkOf pub r₀.1))
  have hh : ∀ s (cmd : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A s),
      IFreeM.IsChargeBound (challengeT M upd strPol pub s cmd) (portCharge (hcCharge N))
        (cmdCharge signCharge s cmd) := chgH_challengeT N pub upd
  have hc := IFreeM.IsChargeBound.substitute (challengeT M upd strPol pub) hh hx
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0) hc fun run ↦ ?_)
    (Nat.add_zero N).le
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chgH_readLift N _) fun _ ↦ trivial

end charge

/-! ## Counting -/

section count

/-- **Double counting over one coordinate**: if `A` ignores coordinate `i₀` and, at every other
coordinates, `B` holds for at most `c` values of coordinate `i₀`, then
`#(A ∩ B) · |β i₀| ≤ c · #A`. -/
theorem hc_card_filter_and_mul_le {ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type}
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] (i₀ : ι) (A B : ((i : ι) → β i) → Prop)
    [DecidablePred A] [DecidablePred B] (c : ℕ)
    (hA : ∀ w a, A (Function.update w i₀ a) ↔ A w)
    (hB : ∀ w, (Finset.univ.filter fun a ↦ B (Function.update w i₀ a)).card ≤ c) :
    (Finset.univ.filter fun w ↦ A w ∧ B w).card * Fintype.card (β i₀) ≤
      c * (Finset.univ.filter A).card := by
  let e : ((i : ι) → β i) × β i₀ ≃ ((i : ι) → β i) × β i₀ :=
    { toFun := fun p ↦ (Function.update p.1 i₀ p.2, p.1 i₀)
      invFun := fun p ↦ (Function.update p.1 i₀ p.2, p.1 i₀)
      left_inv := fun p ↦ by simp
      right_inv := fun p ↦ by simp }
  have h1 : (Finset.univ.filter fun w ↦ A w ∧ B w).card * Fintype.card (β i₀) =
      ∑ p : ((i : ι) → β i) × β i₀, if A p.1 ∧ B p.1 then 1 else 0 := by
    rw [Fintype.sum_prod_type, Finset.card_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    by_cases h : A w ∧ B w <;> simp [h]
  have h2 : ∑ p : ((i : ι) → β i) × β i₀, (if A p.1 ∧ B p.1 then 1 else 0) =
      ∑ p : ((i : ι) → β i) × β i₀, if A (e p).1 ∧ B (e p).1 then 1 else 0 :=
    (e.sum_comp fun p ↦ if A p.1 ∧ B p.1 then 1 else 0).symm
  rw [h1, h2, Fintype.sum_prod_type, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  simp only [e, Equiv.coe_fn_mk, hA]
  by_cases hw : A w
  · simp only [hw, true_and, ↓reduceIte, mul_one]
    rw [← Finset.card_filter]
    exact hB w
  · simp [hw]

/-- Filters of implied predicates are smaller, whatever the decidability instances. -/
theorem hc_card_filter_le_of_imp {α : Type} [Fintype α] (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ a, P a → Q a) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter Q).card :=
  Finset.card_le_card fun a ha ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ a,
    h a (Finset.mem_filter.mp ha).2⟩

end count

/-! ## Controlled Kraus operators -/

section ctrl

open Quantum.Sig (Store ctrlK)

variable {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
  [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [DecidableEq S]
  [∀ s, Fintype (D s)] [Fintype M] [DecidableEq M] [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] in
theorem ctrlK_ne_zero
    (K : Store D → Matrix (β × HwReg X₁ Z₁ (Finset S × M)) (α × HwReg X₁ Z₁ (Finset S × M)) ℂ)
    {x : β × Quantum.Sig.SReg X₁ Z₁ S D M} {y : α × Quantum.Sig.SReg X₁ Z₁ S D M}
    (h : ctrlK K x y ≠ 0) : x.2.2 = y.2.2 ∧ K y.2.2 (x.1, x.2.1) (y.1, y.2.1) ≠ 0 := by
  simp only [ctrlK, of_apply] at h
  split_ifs at h with he
  · exact ⟨he, h⟩
  · exact absurd rfl h

theorem one_kron_diag_mul_ctrlK (q : Store D → ℂ)
    (K : Store D → Matrix (β × HwReg X₁ Z₁ (Finset S × M)) (α × HwReg X₁ Z₁ (Finset S × M)) ℂ) :
    ((1 : Matrix β β ℂ) ⊗ₖ diagonal fun x : Quantum.Sig.SReg X₁ Z₁ S D M ↦ q x.2) * ctrlK K =
      ctrlK K * ((1 : Matrix α α ℂ) ⊗ₖ diagonal fun x : Quantum.Sig.SReg X₁ Z₁ S D M ↦ q x.2) := by
  rw [hc_one_kronecker_diagonal, hc_one_kronecker_diagonal]
  ext x y
  rw [diagonal_mul, mul_diagonal]
  simp only [ctrlK, of_apply]
  split_ifs with h
  · rw [h, mul_comm]
  · simp

section reveal

open Quantum.Sig (swapIn swapOpt swapIn_swapIn revKS revAmp cAmp Agrees recU fill)
open Quantum.Xmss.Assembly (RevealVals)

variable [∀ s, Nonempty (D s)]

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype S] [∀ s, Fintype (D s)]
  [Fintype M] [DecidableEq M] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [∀ s, Nonempty (D s)] in
theorem swapIn_of_not {T L : Finset S} {w : RevealVals D T} {σ : Store D} {s : S}
    (h : ¬(s ∈ T ∧ s ∉ L)) : swapIn T L w σ s = σ s := by
  unfold swapIn
  exact dite_eq_right h

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype S] [∀ s, Fintype (D s)]
  [Fintype M] [DecidableEq M] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [∀ s, Nonempty (D s)] in
theorem swapIn_of_mem {T L : Finset S} {w : RevealVals D T} {σ : Store D} {s : S} (hT : s ∈ T)
    (hL : s ∉ L) (hn : σ s = none) : swapIn T L w σ s = some (w ⟨s, hT⟩) := by
  unfold swapIn
  rw [dite_eq_left ⟨hT, hL⟩, hn]
  rfl

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype S] [∀ s, Fintype (D s)]
  [Fintype M] [DecidableEq M] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [∀ s, Nonempty (D s)] in
theorem swapIn_update_of_ne {T L : Finset S} (w : RevealVals D T) (i₀ : {s // s ∈ T})
    (a : D i₀.1) (σ : Store D) {s : S} (hs : s ≠ i₀.1) :
    swapIn T L (Function.update w i₀ a) σ s = swapIn T L w σ s := by
  unfold swapIn
  split_ifs with h
  · rw [Function.update_of_ne fun he ↦ hs (congrArg Subtype.val he)]
  · rfl

omit [Fintype M] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem revKS_ne_zero {T : Finset S} {r : RevealVals D T × (Finset S × M)}
    {x y : Unit × Quantum.Sig.SReg X₁ Z₁ S D M} (h : revKS T r x y ≠ 0) :
    y.2.1.2.2 = r.2 ∧ x = ((), (recU T r.2 y.2.1, swapIn T r.2.1 r.1 y.2.2)) := by
  simp only [revKS, of_apply] at h
  split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

omit [Fintype M] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem revKS_rowInj (T : Finset S) (r : RevealVals D T × (Finset S × M))
    (x y y' : Unit × Quantum.Sig.SReg X₁ Z₁ S D M) (h : revKS T r x y ≠ 0)
    (h' : revKS T r x y' ≠ 0) : y = y' := by
  obtain ⟨hm, hx⟩ := revKS_ne_zero h
  obtain ⟨hm', hx'⟩ := revKS_ne_zero h'
  have e := hx.symm.trans hx'
  obtain ⟨u₁, d₁, σ₁⟩ := y
  obtain ⟨u₂, d₂, σ₂⟩ := y'
  simp only [Prod.mk.injEq, recU, true_and] at e hm hm'
  obtain ⟨⟨he₁, he₂, -⟩, he₃⟩ := e
  have hσ : σ₁ = σ₂ := by
    rw [← swapIn_swapIn T r.2.1 r.1 σ₁, he₃, swapIn_swapIn]
  have hd : d₁ = d₂ := Prod.ext he₁ (Prod.ext he₂ (hm.trans hm'.symm))
  rw [hσ, hd, Subsingleton.elim u₁ u₂]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- **The reveal's weight on a store event** from one input state: the average over the fresh
values of the event at the new store. -/
theorem sum_revKS_normSq (T : Finset S) (F : Store D → Prop) [DecidablePred F]
    (y : Unit × Quantum.Sig.SReg X₁ Z₁ S D M) :
    ∑ r, ∑ x, (if F x.2.2 then (1 : ℝ) else 0) * Complex.normSq (revKS T r x y) =
      ∑ w, (if F (swapIn T y.2.1.2.2.1 w y.2.2) then (1 : ℝ) else 0) *
        Complex.normSq (revAmp T y.2.1.2.2.1 y.2.2 w) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.sum_eq_single y.2.1.2.2]
  · rw [Finset.sum_eq_single ((), (recU T y.2.1.2.2 y.2.1, swapIn T y.2.1.2.2.1 w y.2.2))]
    · simp [revKS]
    · intro x _ hx
      simp [revKS, hx]
    · simp
  · intro m _ hm
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp [revKS, Ne.symm hm]
  · simp

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype S] [Fintype M]
  [DecidableEq M] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem normSq_revAmp (T L : Finset S) (σ : Store D) (w : RevealVals D T) :
    Complex.normSq (revAmp T L σ w) =
      if Agrees T L (fill σ) w then ((Fintype.card (RevealVals D (T \ L)) : ℝ))⁻¹ else 0 := by
  unfold revAmp
  split_ifs
  · rw [cAmp, Complex.normSq_ofReal, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
  · simp

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype S] [Fintype M]
  [DecidableEq M] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem sum_ind_normSq_revAmp (T L : Finset S) (σ : Store D) (F : RevealVals D T → Prop)
    [DecidablePred F] :
    ∑ w, (if F w then (1 : ℝ) else 0) * Complex.normSq (revAmp T L σ w) =
      ((Finset.univ.filter fun w ↦ Agrees T L (fill σ) w ∧ F w).card : ℝ) /
        Fintype.card (RevealVals D (T \ L)) := by
  simp only [normSq_revAmp]
  rw [div_eq_mul_inv, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  by_cases h1 : F w <;> by_cases h2 : Agrees T L (fill σ) w <;> simp [h1, h2]

end reveal

end ctrl

/-! ## The steps of the sampled runtime -/

section sampled

open Quantum.Sig (Store fill swapIn swapOpt revKS revAmp cAmp Agrees recU ctrlK sampStep
  sampledRuntime card_agrees star_cAmp_mul_self)
open Quantum.Xmss.Hybrid (kraus2 hwProgKraus_ne_zero_snd)

variable {M : Type} [Fintype M] [DecidableEq M]

open Classical in
/-- **The store event's projector** on the sampled register. -/
noncomputable def confProj (pub : Pub) :
    Matrix (Quantum.Sig.SReg X Z HPos XD M) (Quantum.Sig.SReg X Z HPos XD M) ℂ :=
  diagonal fun x ↦ if StoreConf pub x.2 then 1 else 0

/-- The per-reveal fraction: `12 N / |R|`. -/
noncomputable def hcDelta (N : ℕ) : ℝ :=
  (12 * N : ℝ) / Fintype.card Randomizer

/-- **A step whose branches commute with `1 ⊗ Q` does not raise the potential.** -/
theorem tsum_potential_le_of_commute {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
    (i : spec.Port) (Q : Matrix R.D R.D ℂ)
    (Kr : spec.Result i → Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ)
    (hb : ∀ r, (R.step i).branch r = MatrixMap.conj (Kr r))
    (hc : ∀ r, ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Q) * Kr r =
      Kr r * ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Q))
    {σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, potential Q ((R.step i).branch r σ) ≤ potential Q σ := by
  have hσ' := hσ.mul_mul_conjTranspose_same ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Q)
  calc ∑' r, potential Q ((R.step i).branch r σ)
      = ∑' r, ENNReal.ofReal ((R.step i).branch r
          (MatrixMap.conj ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Q) σ)).trace.re := by
        refine tsum_congr fun r ↦ ?_
        rw [potential, MatrixMap.amplifyLeft_conj, hb, MatrixMap.conj_apply, MatrixMap.conj_apply,
          MatrixMap.conj_apply, MatrixMap.conj_apply]
        have h2 : (Kr r)ᴴ * ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ Q)ᴴ =
            ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Q)ᴴ * (Kr r)ᴴ := by
          rw [← conjTranspose_mul, hc r, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        rw [h2, ← Matrix.mul_assoc _ (Kr r), hc r]
        simp only [Matrix.mul_assoc]
    _ ≤ ENNReal.ofReal (MatrixMap.conj ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ Q) σ).trace.re :=
        (R.step i).isCPTNIFamily.tsum_ofReal_trace_re_le (by rw [MatrixMap.conj_apply]; exact hσ')
    _ = potential Q σ := by rw [potential, MatrixMap.amplifyLeft_conj]

/-- The diagonal entry of a conjugation by an operator with at most one nonzero entry per row. -/
theorem hc_conj_apply_diag {α β : Type} [Fintype α] [Fintype β] (K : Matrix α β ℂ)
    (σ : Matrix β β ℂ) (x : α) (h : ∀ y y', K x y ≠ 0 → K x y' ≠ 0 → y = y') :
    (MatrixMap.conj K σ) x x = ∑ y, K x y * σ y y * star (K x y) := by
  rw [MatrixMap.conj_apply, mul_apply]
  simp only [mul_apply, conjTranspose_apply]
  by_cases h0 : ∃ y₀, K x y₀ ≠ 0
  · obtain ⟨y₀, hy₀⟩ := h0
    have hz : ∀ y, y ≠ y₀ → K x y = 0 := fun y hy ↦ by
      by_contra hne
      exact hy (h y y₀ hne hy₀)
    rw [Finset.sum_eq_single y₀ (fun y _ hy ↦ by simp [hz y hy]) (by simp),
      Finset.sum_eq_single y₀ (fun y _ hy ↦ by simp [hz y hy]) (by simp),
      Finset.sum_eq_single y₀ (fun y _ hy ↦ by simp [hz y hy]) (by simp)]
  · simp only [ne_eq, not_exists, not_not] at h0
    simp [h0]

/-- **The event weight after a family of operators with one nonzero entry per row**, as a sum over
the input's diagonal. -/
theorem hc_sum_trace_conj_rowInj {ι α β : Type} [Fintype ι] [Fintype α] [DecidableEq α]
    [Fintype β] (K : ι → Matrix α β ℂ)
    (hinj : ∀ r x y y', K r x y ≠ 0 → K r x y' ≠ 0 → y = y') (F : α → Prop) [DecidablePred F]
    (σ : Matrix β β ℂ) :
    ∑ r, (MatrixMap.conj (diagonal fun x ↦ if F x then (1 : ℂ) else 0)
        (MatrixMap.conj (K r) σ)).trace.re =
      ∑ y, (σ y y).re * ∑ r, ∑ x, (if F x then (1 : ℝ) else 0) * Complex.normSq (K r x y) := by
  have hx : ∀ r x, ((MatrixMap.conj (K r) σ) x x).re =
      ∑ y, Complex.normSq (K r x y) * (σ y y).re := fun r x ↦ by
    rw [hc_conj_apply_diag (K r) σ x (hinj r x), Complex.re_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hk : K r x y * star (K r x y) = (Complex.normSq (K r x y) : ℂ) := Complex.mul_conj _
    rw [mul_comm (K r x y), mul_assoc, hk, mul_comm, Complex.re_ofReal_mul]
  simp only [hc_trace_conj_diagonal_ind, Complex.re_sum]
  have he : ∀ r x, (if F x then (MatrixMap.conj (K r) σ) x x else 0).re =
      (if F x then (1 : ℝ) else 0) * ((MatrixMap.conj (K r) σ) x x).re := fun r x ↦ by
    split_ifs <;> simp
  simp only [he, hx, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun r _ ↦ Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun r _ ↦
    Finset.sum_congr rfl fun x _ ↦ ?_
  ring

end sampled

/-! ### The reveals -/

section revealSph

open Quantum.Sig (Store fill swapIn revKS revAmp Agrees recU card_agrees sampledRuntime ctrlK)

variable {pub : Pub}

theorem storeConf_swapIn_iff {T L : Finset HPos} (w : RevealVals XD T) {σ : Store XD}
    (hcons : ∀ s, σ s ≠ none ↔ s ∈ L)
    (hroot : (∃ msg, HPos.rnd msg ∈ L) → HPos.val rootPos ∈ L)
    (hT : ∀ msg, HPos.rnd msg ∈ T → HPos.rnd msg ∈ L) :
    StoreConf pub (swapIn T L w σ) ↔ StoreConf pub σ := by
  have hr : ∀ msg, swapIn T L w σ (.rnd msg) = σ (.rnd msg) := fun msg ↦
    swapIn_of_not fun h ↦ h.2 (hT msg h.1)
  by_cases h0 : HPos.val rootPos ∈ L
  · exact storeConf_congr hr (swapIn_of_not fun h ↦ h.2 h0)
  · have hn : ∀ msg, σ (.rnd msg) = none := fun msg ↦ by
      by_contra hne
      exact h0 (hroot ⟨msg, (hcons _).mp hne⟩)
    exact iff_of_false (not_storeConf_of fun msg ↦ (hr msg).trans (hn msg)) (not_storeConf_of hn)

/-- **The cases of a conflict after storing a fresh randomizer** `a` for `M₀`: the two calls on
`M₀` meet, or a call on `M₀` meets a call on a message stored before. -/
theorem storeConf_fresh_cases {σ σ' : Store XD} {M₀ : Message} {a : Randomizer}
    {f : ValPos → Digest} (ha0 : σ' (.rnd M₀) = some a)
    (hoth : ∀ msg, msg ≠ M₀ → σ' (.rnd msg) = σ (.rnd msg))
    (hf : valsOf (fill σ') rootPos = f rootPos)
    (hold : (∃ msg, σ (.rnd msg) ≠ none) → f rootPos = valsOf (fill σ) rootPos)
    (hF : ¬StoreConf pub σ) (hconf : StoreConf pub σ') :
    ∃ M'', σ (.rnd M'') ≠ none ∧ ∃ ii : DigestCall × DigestCall,
      hZf pub f M₀ ii.1 a = hZf pub f M'' ii.2 (fill σ (.rnd M'')) := by
  obtain ⟨M, i, M', i', hne, R, R', h1, h2, he⟩ := hconf
  rw [hZf_congr pub hf, hZf_congr pub hf] at he
  have hfill : ∀ msg (R₀ : Randomizer), σ (.rnd msg) = some R₀ → fill σ (.rnd msg) = R₀ :=
    fun msg R₀ h ↦ by
      show Option.getD _ _ = _
      rw [h]
      rfl
  by_cases hM : M = M₀ <;> by_cases hM' : M' = M₀
  · exact absurd (hM.trans hM'.symm) hne
  · rw [hM, ha0] at h1
    obtain rfl := Option.some.inj h1
    rw [hoth M' hM'] at h2
    rw [hM] at he
    refine ⟨M', Option.ne_none_iff_exists.mpr ⟨R', h2.symm⟩, (i, i'), ?_⟩
    rw [hfill M' R' h2]
    exact he
  · rw [hM', ha0] at h2
    obtain rfl := Option.some.inj h2
    rw [hoth M hM] at h1
    rw [hM'] at he
    refine ⟨M, Option.ne_none_iff_exists.mpr ⟨R, h1.symm⟩, (i', i), ?_⟩
    rw [hfill M R h1]
    exact he.symm
  · exfalso
    rw [hoth M hM] at h1
    rw [hoth M' hM'] at h2
    have hfσ := hold ⟨M, Option.ne_none_iff_exists.mpr ⟨R, h1.symm⟩⟩
    rw [hZf_congr pub hfσ, hZf_congr pub hfσ] at he
    exact hF ⟨M, i, M', i', hne, R, R', h1, h2, he⟩

/-- The randomizers for which call `i` on `M₀` shares its `h`-cell with call `j` on `M''` at
`R''`. -/
def crossF (pub : Pub) (f : ValPos → Digest) (M₀ M'' : Message) (R'' : Randomizer)
    (i j : DigestCall) : Finset Randomizer :=
  Finset.univ.filter fun a ↦ hZf pub f M₀ i a = hZf pub f M'' j R''

/-- The randomizers for which a call on `M₀` shares its `h`-cell with a call on `M''` at `R''`. -/
@[irreducible] def crossBad (pub : Pub) (f : ValPos → Digest) (M₀ M'' : Message)
    (R'' : Randomizer) : Finset Randomizer :=
  crossF pub f M₀ M'' R'' 0 0 ∪ crossF pub f M₀ M'' R'' 0 1 ∪ crossF pub f M₀ M'' R'' 1 0 ∪
    crossF pub f M₀ M'' R'' 1 1

theorem mem_crossBad {f : ValPos → Digest} {M₀ M'' : Message} {R'' a : Randomizer} :
    a ∈ crossBad pub f M₀ M'' R'' ↔
      ∃ ii : DigestCall × DigestCall, hZf pub f M₀ ii.1 a = hZf pub f M'' ii.2 R'' := by
  have h01 : ∀ j : DigestCall, j = 0 ∨ j = 1 := by decide
  unfold crossBad
  simp only [Finset.mem_union, crossF, Finset.mem_filter]
  constructor
  · rintro (((⟨-, h⟩ | ⟨-, h⟩) | ⟨-, h⟩) | ⟨-, h⟩)
    · exact ⟨(0, 0), h⟩
    · exact ⟨(0, 1), h⟩
    · exact ⟨(1, 0), h⟩
    · exact ⟨(1, 1), h⟩
  · rintro ⟨⟨i, j⟩, h⟩
    rcases h01 i with rfl | rfl <;> rcases h01 j with rfl | rfl <;> simp [h]

theorem card_crossBad_le (hload : HZLoad pub) (f : ValPos → Digest) (M₀ M'' : Message)
    (R'' : Randomizer) : (crossBad pub f M₀ M'' R'').card ≤ 12 := by
  unfold crossBad
  have hc : ∀ i j, (crossF pub f M₀ M'' R'' i j).card ≤ 3 := fun i j ↦ hload f M₀ i _
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((Finset.card_union_le _ _).trans (Nat.add_le_add_right
    (Finset.card_union_le _ _) _)) _).trans ?_
  have := hc 0 0
  have := hc 0 1
  have := hc 1 0
  have := hc 1 1
  omega

open Classical in
/-- **The fresh randomizer of a reveal**: off the event, at most `12 n` of its values create
a conflict, `n` the number of revealed randomizers (`HZLoad`). -/
theorem card_fiber_storeConf_le (hload : HZLoad pub) {T L : Finset HPos} {σ : Store XD}
    (hcons : ∀ s, σ s ≠ none ↔ s ∈ L)
    (hroot : (∃ msg, HPos.rnd msg ∈ L) → HPos.val rootPos ∈ L) {M₀ : Message}
    (hM₀T : HPos.rnd M₀ ∈ T) (hM₀L : HPos.rnd M₀ ∉ L)
    (huniq : ∀ msg, HPos.rnd msg ∈ T → msg = M₀) (hF : ¬StoreConf pub σ) (w : RevealVals XD T) :
    (Finset.univ.filter fun a : Randomizer ↦
      StoreConf pub (swapIn T L (Function.update w ⟨HPos.rnd M₀, hM₀T⟩ a) σ)).card ≤
      12 * rndCount L := by
  have hσ0 : σ (.rnd M₀) = none := by
    by_contra h
    exact hM₀L ((hcons _).mp h)
  have hold : (∃ msg, σ (.rnd msg) ≠ none) →
      valsOf (fill (swapIn T L w σ)) rootPos = valsOf (fill σ) rootPos := fun ⟨msg, hm⟩ ↦ by
    have hr : HPos.val rootPos ∈ L := hroot ⟨msg, (hcons _).mp hm⟩
    show Option.getD _ _ = Option.getD _ _
    rw [swapIn_of_not fun h ↦ h.2 hr]
  have hsub : (Finset.univ.filter fun a : Randomizer ↦
      StoreConf pub (swapIn T L (Function.update w ⟨HPos.rnd M₀, hM₀T⟩ a) σ)) ⊆
      (rndMsgs L).biUnion fun M'' ↦
        crossBad pub (valsOf (fill (swapIn T L w σ))) M₀ M'' (fill σ (.rnd M'')) := by
    intro a ha
    have hconf : StoreConf pub (swapIn T L (Function.update w ⟨HPos.rnd M₀, hM₀T⟩ a) σ) := by
      simp only [Finset.mem_filter] at ha
      exact ha.2
    have ha0 : swapIn T L (Function.update w ⟨HPos.rnd M₀, hM₀T⟩ a) σ (.rnd M₀) = some a := by
      rw [swapIn_of_mem hM₀T hM₀L hσ0]
      exact congrArg some (Function.update_self _ _ _)
    have hoth : ∀ msg, msg ≠ M₀ →
        swapIn T L (Function.update w ⟨HPos.rnd M₀, hM₀T⟩ a) σ (.rnd msg) = σ (.rnd msg) :=
      fun msg hm ↦ swapIn_of_not fun h ↦ hm (huniq msg h.1)
    have hf : valsOf (fill (swapIn T L (Function.update w ⟨HPos.rnd M₀, hM₀T⟩ a) σ)) rootPos =
        valsOf (fill (swapIn T L w σ)) rootPos := by
      show Option.getD _ _ = Option.getD _ _
      rw [swapIn_update_of_ne w ⟨HPos.rnd M₀, hM₀T⟩ a σ (by simp)]
    have key := storeConf_fresh_cases (pub := pub) (σ := σ)
      (σ' := swapIn T L (Function.update w ⟨HPos.rnd M₀, hM₀T⟩ a) σ) (M₀ := M₀) (a := a)
      (f := valsOf (fill (swapIn T L w σ))) ha0 hoth hf hold hF hconf
    obtain ⟨M'', hM'', ii, hii⟩ := key
    exact Finset.mem_biUnion.mpr ⟨M'', mem_rndMsgs.mpr ((hcons _).mp hM''),
      mem_crossBad.mpr ⟨ii, hii⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ rndCount L * 12 :=
        Finset.card_biUnion_le_card_mul _ _ 12 fun M'' _ ↦ card_crossBad_le hload _ M₀ M'' _
    _ = 12 * rndCount L := by ring

variable {M : Type}

open Classical in
/-- **A reveal's conflict fraction**: the fresh values creating the event are at most a fraction
`κ · δ` of the values agreeing with the store, `κ` the reveal's charge. -/
theorem card_agrees_storeConf_le (hload : HZLoad pub) {N t : ℕ} {T L : Finset HPos}
    {σ : Store XD} (hcons : ∀ s, σ s ≠ none ↔ s ∈ L)
    (hroot : (∃ msg, HPos.rnd msg ∈ L) → HPos.val rootPos ∈ L) (hcount : rndCount L ≤ t)
    (ht : t + hcCharge (M := M) N (.inr T) ≤ N) :
    ((Finset.univ.filter fun w ↦ Agrees T L (fill σ) w ∧ StoreConf pub (swapIn T L w σ)).card :
        ℝ) ≤
      ((if StoreConf pub σ then 1 else 0) + hcCharge (M := M) N (.inr T) * hcDelta N) *
        Fintype.card (RevealVals XD (T \ L)) := by
  have hA : ((Finset.univ.filter fun w ↦ Agrees T L (fill σ) w).card : ℝ) =
      Fintype.card (RevealVals XD (T \ L)) := by
    rw [← Fintype.card_subtype, card_agrees]
  have hle : ((Finset.univ.filter fun w ↦ Agrees T L (fill σ) w ∧
      StoreConf pub (swapIn T L w σ)).card : ℝ) ≤ Fintype.card (RevealVals XD (T \ L)) := by
    rw [← hA]
    refine Nat.cast_le.mpr (Finset.card_le_card fun w hw ↦ ?_)
    simp only [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, hw.2.1⟩
  have hδ : 0 ≤ hcDelta N := by unfold hcDelta; positivity
  have hcard : (0 : ℝ) ≤ Fintype.card (RevealVals XD (T \ L)) := Nat.cast_nonneg _
  have hsame : (∀ w : RevealVals XD T, StoreConf pub (swapIn T L w σ) ↔ StoreConf pub σ) →
      ((Finset.univ.filter fun w ↦ Agrees T L (fill σ) w ∧
        StoreConf pub (swapIn T L w σ)).card : ℝ) ≤
      ((if StoreConf pub σ then 1 else 0) + hcCharge (M := M) N (.inr T) * hcDelta N) *
        Fintype.card (RevealVals XD (T \ L)) := fun hw ↦ by
    by_cases hF : StoreConf pub σ
    · refine hle.trans ?_
      simp only [hF, ↓reduceIte]
      exact le_mul_of_one_le_left hcard (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ))
    · have h0 : (Finset.univ.filter fun w ↦ Agrees T L (fill σ) w ∧
          StoreConf pub (swapIn T L w σ)) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun w _ h ↦ hF ((hw w).mp h.2)
      rw [h0, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (by positivity) hcard
  by_cases hfree : RndFree T
  · exact hsame fun w ↦ storeConf_swapIn_iff w hcons hroot fun msg h ↦ absurd h (hfree msg)
  · by_cases hone : RndOne T
    · have hκ : hcCharge (M := M) N (.inr T) = 1 := by
        simp only [hcCharge, hfree, hone, ↓reduceIte]
      obtain ⟨-, M₀, hM₀T, huniq⟩ := hone
      by_cases hM₀L : HPos.rnd M₀ ∈ L
      · exact hsame fun w ↦ storeConf_swapIn_iff w hcons hroot fun msg h ↦
          (huniq msg h) ▸ hM₀L
      · by_cases hF : StoreConf pub σ
        · refine hle.trans ?_
          simp only [hF, ↓reduceIte]
          exact le_mul_of_one_le_left hcard
            (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ))
        · have hAupd : ∀ (w : RevealVals XD T) (a : XD (⟨HPos.rnd M₀, hM₀T⟩ : {s // s ∈ T}).1),
              Agrees T L (fill σ) (Function.update w ⟨HPos.rnd M₀, hM₀T⟩ a) ↔
                Agrees T L (fill σ) w := fun w a ↦
            forall_congr' fun s ↦ imp_congr_right fun hs ↦ by
              rw [Function.update_of_ne]
              rintro rfl
              exact hM₀L hs
          have hm := hc_card_filter_and_mul_le (β := fun s : {s // s ∈ T} ↦ XD s.1)
            ⟨HPos.rnd M₀, hM₀T⟩ (fun w ↦ Agrees T L (fill σ) w)
            (fun w ↦ StoreConf pub (swapIn T L w σ)) (12 * rndCount L) hAupd
            (fun w ↦ card_fiber_storeConf_le hload hcons hroot hM₀T hM₀L huniq hF w)
          have hR : Fintype.card (XD (⟨HPos.rnd M₀, hM₀T⟩ : {s // s ∈ T}).1) =
              Fintype.card Randomizer := rfl
          rw [hR] at hm
          have ht1 : rndCount L ≤ N := by
            rw [hκ] at ht
            omega
          have hm' : ((Finset.univ.filter fun w ↦ Agrees T L (fill σ) w ∧
              StoreConf pub (swapIn T L w σ)).card : ℝ) * Fintype.card Randomizer ≤
              (12 * N) * Fintype.card (RevealVals XD (T \ L)) := by
            rw [← hA]
            have h2 : (12 * rndCount L) * (Finset.univ.filter fun w ↦
                Agrees T L (fill σ) w).card ≤ (12 * N) * (Finset.univ.filter fun w ↦
                Agrees T L (fill σ) w).card := Nat.mul_le_mul_right _ (by omega)
            exact_mod_cast hm.trans h2
          simp only [hF, ↓reduceIte]
          rw [hκ, zero_add, Nat.cast_one, one_mul, hcDelta, div_mul_eq_mul_div,
            le_div_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)]
          exact hm'
    · have hκ : hcCharge (M := M) N (.inr T) = N + 1 := by
        simp only [hcCharge, hfree, hone, ↓reduceIte]
      omega

end revealSph

/-! ### The grade and the potential along the sampled runtime -/

section stepsSph

open Quantum.Sig (Store fill swapIn revKS Agrees recU sampledRuntime ctrlK)
open Quantum.Xmss.Hybrid (kraus2 hwProgKraus_ne_zero_snd)

theorem rndCount_union_le (L T : Finset HPos) : rndCount (L ∪ T) ≤ rndCount L + rndCount T := by
  unfold rndCount
  refine (Finset.card_le_card fun msg h ↦ ?_).trans (Finset.card_union_le _ _)
  rw [mem_rndMsgs, Finset.mem_union] at h
  rw [Finset.mem_union, mem_rndMsgs, mem_rndMsgs]
  exact h

theorem rndCount_free_le {T : Finset HPos} (h : RndFree T) : rndCount T ≤ 0 := by
  unfold rndCount
  refine (Finset.card_le_card (t := ∅) fun msg hm ↦ absurd (mem_rndMsgs.mp hm) (h msg)).trans ?_
  simp

theorem rndCount_one_le {T : Finset HPos} (h : RndOne T) : rndCount T ≤ 1 := by
  obtain ⟨-, m₀, -, hu⟩ := h
  unfold rndCount
  refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
  rw [hu a (mem_rndMsgs.mp ha), hu b (mem_rndMsgs.mp hb)]

theorem storeOK_reveal {T L : Finset HPos} (w : RevealVals XD T) {σ : Store XD}
    (hcons : ∀ s, σ s ≠ none ↔ s ∈ L) (s : HPos) : swapIn T L w σ s ≠ none ↔ s ∈ L ∪ T := by
  by_cases h : s ∈ T ∧ s ∉ L
  · have hn : σ s = none := by
      by_contra hn
      exact h.2 ((hcons s).mp hn)
    rw [swapIn_of_mem h.1 h.2 hn]
    exact ⟨fun _ ↦ Finset.mem_union_right _ h.1, fun _ ↦ Option.some_ne_none _⟩
  · rw [swapIn_of_not h, hcons, Finset.mem_union]
    refine ⟨Or.inl, fun h₁ ↦ h₁.elim id fun h₂ ↦ ?_⟩
    by_contra h₃
    exact h ⟨h₂, h₃⟩

variable {M : Type} [Fintype M] [DecidableEq M]

omit [Fintype M] [DecidableEq M] in
theorem hcGrade_reveal_of {N t k : ℕ} {T L : Finset HPos} (w : RevealVals XD T) {σ : Store XD}
    {x : Quantum.Sig.SReg X Z HPos XD M} (hx1 : x.1.2.2.1 = L ∪ T) (hx2 : x.2 = swapIn T L w σ)
    (hcons : ∀ s, σ s ≠ none ↔ s ∈ L)
    (hroot : (∃ msg, HPos.rnd msg ∈ L) → HPos.val rootPos ∈ L) (hc : rndCount L ≤ t)
    (hrootT : ∀ msg, HPos.rnd msg ∈ T → HPos.val rootPos ∈ T) (hcT : rndCount T ≤ k) :
    hcGrade N x ≤ t + k := by
  have hok : StoreOK x := by
    unfold StoreOK
    refine ⟨fun s ↦ ?_, fun ⟨msg, hmsg⟩ ↦ ?_⟩
    · rw [hx2, hx1]
      exact storeOK_reveal w hcons s
    · rw [hx1] at hmsg ⊢
      rcases Finset.mem_union.mp hmsg with h₁ | h₁
      · exact Finset.mem_union_left _ (hroot ⟨msg, h₁⟩)
      · exact Finset.mem_union_right _ (hrootT msg h₁)
  refine hcGrade_le_of hok ?_
  rw [hx1]
  exact (rndCount_union_le L T).trans (by omega)

omit [Fintype M] in
/-- **A reveal raises the grade by at most its charge.** -/
theorem hcGrade_reveal {N t : ℕ} {T : Finset HPos} {r : RevealVals XD T × (Finset HPos × M)}
    {x y : Unit × Quantum.Sig.SReg X Z HPos XD M} (hK : revKS T r x y ≠ 0)
    (hy : hcGrade N y.2 ≤ t) : hcGrade N x.2 ≤ t + hcCharge (M := M) N (.inr T) := by
  obtain ⟨hm, rfl⟩ := revKS_ne_zero hK
  by_cases ht : t ≤ N
  · obtain ⟨hok, hc⟩ := of_hcGrade_le hy ht
    unfold StoreOK at hok
    obtain ⟨hcons, hroot⟩ := hok
    have hL : y.2.1.2.2.1 = r.2.1 := congrArg Prod.fst hm
    rw [hL] at hcons hroot hc
    by_cases hfree : RndFree T
    · have hκ : hcCharge (M := M) N (.inr T) = 0 := by
        simp only [hcCharge, hfree, ↓reduceIte]
      rw [hκ]
      exact hcGrade_reveal_of r.1 rfl rfl hcons hroot hc (fun msg h ↦ absurd h (hfree msg))
        (rndCount_free_le hfree)
    · by_cases hone : RndOne T
      · have hκ : hcCharge (M := M) N (.inr T) = 1 := by
          simp only [hcCharge, hfree, hone, ↓reduceIte]
        rw [hκ]
        exact hcGrade_reveal_of r.1 rfl rfl hcons hroot hc (fun _ _ ↦ hone.1)
          (rndCount_one_le hone)
      · have hκ : hcCharge (M := M) N (.inr T) = N + 1 := by
          simp only [hcCharge, hfree, hone, ↓reduceIte]
        rw [hκ]
        exact (hcGrade_le N _).trans (by omega)
  · exact (hcGrade_le N _).trans (by omega)

omit [DecidableEq M] in
theorem hcGrade_ctrlK {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (N t : ℕ)
    (K : Store XD → Matrix (β × HwReg X Z (Finset HPos × M)) (α × HwReg X Z (Finset HPos × M)) ℂ)
    (hK : ∀ σ' a b, K σ' a b ≠ 0 → a.2.2.2.1 = b.2.2.2.1)
    {σ : Matrix (α × Quantum.Sig.SReg X Z HPos XD M) (α × Quantum.Sig.SReg X Z HPos XD M) ℂ}
    (hσ : QuerySupportedOn (fun q : α × Quantum.Sig.SReg X Z HPos XD M ↦ hcGrade N q.2)
      (Set.Iic t) σ) :
    QuerySupportedOn (fun q : β × Quantum.Sig.SReg X Z HPos XD M ↦ hcGrade N q.2) (Set.Iic t)
      (MatrixMap.conj (ctrlK K) σ) :=
  QuerySupportedOn.conj hσ fun q' q hKq hq ↦ by
    obtain ⟨hs, hk⟩ := ctrlK_ne_zero K hKq
    have hl := hK _ _ _ hk
    show hcGrade N q'.2 ≤ t
    rw [hcGrade_congr N (x := q.2) (x' := q'.2) hl hs]
    exact hq

theorem kraus2_prog_ne_zero (m₀ : Finset HPos × M) (c : HwProg X Z) (r : c.Result)
    {a b : Unit × HwReg X Z (Finset HPos × M)} (h : kraus2 X Z m₀ (.inr c) r a b ≠ 0) :
    a.2.2.2 = b.2.2.2 := by
  obtain ⟨u', s'⟩ := a
  obtain ⟨u, s⟩ := b
  show s'.2.2 = s.2.2
  rw [hwProgKraus_ne_zero_snd c r h]

/-- **Every step of the sampled runtime raises the grade by at most its charge.** -/
theorem hg_sampled (N : ℕ) (m : M) (i : (SSpec M).Port) (r : (SSpec M).Result i) (t : ℕ)
    (σ : Matrix ((SSpec M).In i × (sampledRuntime goodAll m).D)
      ((SSpec M).In i × (sampledRuntime goodAll m).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (SSpec M).In i × (sampledRuntime goodAll m).D ↦
      hcGrade N q.2) (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (SSpec M).Out i × (sampledRuntime goodAll m).D ↦ hcGrade N q.2)
      (Set.Iic (t + hcCharge N i)) (((sampledRuntime goodAll m).step i).branch r σ) := by
  have hmono : Set.Iic t ⊆ Set.Iic (t + hcCharge N i) :=
    Set.Iic_subset_Iic.mpr (Nat.le_add_right _ _)
  rcases i with ((i | ⟨c, hcm⟩) | ⟨p, hp⟩) | T
  · exact (hcGrade_ctrlK N t (fun _ ↦ kraus2 X Z ((∅ : Finset HPos), m) (.inl (.inl i)) r)
      (fun _ a b h ↦ congrArg (fun z ↦ z.2.1)
        (snd_eq_of_spongeHardwired_U_ne_zero _ _ i b.1 a.1 b.2 a.2 h)) hσ).mono hmono
  · cases c with
    | readH z upd =>
      by_cases hk : ReadKeeps (HwRead.readH z upd)
      · exact (hcGrade_ctrlK N t
          (fun _ ↦ kraus2 X Z ((∅ : Finset HPos), m) (.inl (.inr (.readH z upd))) r)
          (fun _ a b h ↦ (hwReadKraus_ne_zero_keep (labKeep_of_readKeeps _ hk) r h).2) hσ).mono
          hmono
      · exact QuerySupportedOn.conj hσ fun q' _ _ _ ↦ by
          simp only [Set.mem_Iic, hcCharge, hk, ↓reduceIte]
          exact (hcGrade_le N _).trans (by omega)
    | readK x upd =>
      by_cases hk : ReadKeeps (HwRead.readK x upd)
      · exact (hcGrade_ctrlK N t
          (fun _ ↦ kraus2 X Z ((∅ : Finset HPos), m) (.inl (.inr (.readK x upd))) r)
          (fun _ a b h ↦ (hwReadKraus_ne_zero_keep (labKeep_of_readKeeps _ hk) r h).2) hσ).mono
          hmono
      · exact QuerySupportedOn.conj hσ fun q' _ _ _ ↦ by
          simp only [Set.mem_Iic, hcCharge, hk, ↓reduceIte]
          exact (hcGrade_le N _).trans (by omega)
    | readK' x upd =>
      by_cases hk : ReadKeeps (HwRead.readK' x upd)
      · exact (hcGrade_ctrlK N t
          (fun _ ↦ kraus2 X Z ((∅ : Finset HPos), m) (.inl (.inr (.readK' x upd))) r)
          (fun _ a b h ↦ (hwReadKraus_ne_zero_keep (labKeep_of_readKeeps _ hk) r h).2) hσ).mono
          hmono
      · exact QuerySupportedOn.conj hσ fun q' _ _ _ ↦ by
          simp only [Set.mem_Iic, hcCharge, hk, ↓reduceIte]
          exact (hcGrade_le N _).trans (by omega)
  · cases p with
    | programH T₀ c₀ =>
      exact (hcGrade_ctrlK N t (fun σ' ↦ kraus2 X Z ((∅ : Finset HPos), m)
        (.inr ((LazyProg.programH T₀ c₀).realize (fill σ'))) r)
        (fun _ _ _ h ↦ congrArg Prod.fst (kraus2_prog_ne_zero _ _ _ h)) hσ).mono hmono
    | programK T₀ c₀ =>
      exact (hcGrade_ctrlK N t (fun σ' ↦ kraus2 X Z ((∅ : Finset HPos), m)
        (.inr ((LazyProg.programK T₀ c₀).realize (fill σ'))) r)
        (fun _ _ _ h ↦ congrArg Prod.fst (kraus2_prog_ne_zero _ _ _ h)) hσ).mono hmono
    | programK' T₀ c₀ =>
      exact (hcGrade_ctrlK N t (fun σ' ↦ kraus2 X Z ((∅ : Finset HPos), m)
        (.inr ((LazyProg.programK' T₀ c₀).realize (fill σ'))) r)
        (fun _ _ _ h ↦ congrArg Prod.fst (kraus2_prog_ne_zero _ _ _ h)) hσ).mono hmono
  · exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ hcGrade_reveal hK hq

end stepsSph

/-! ### The potential of the store event along the sampled runtime -/

section potSph

open Quantum.Sig (Store fill swapIn revKS revAmp Agrees recU sampledRuntime ctrlK)
open Quantum.Xmss.Hybrid (kraus2)

variable {pub : Pub} {M : Type} [Fintype M] [DecidableEq M]

open Classical in
/-- **A reveal raises the store event's weight by at most its charge times `hcDelta`**, on
states of grade `t` with `t` plus the charge at most `N`. -/
theorem sum_trace_revKS_le (hload : HZLoad pub) (N t : ℕ) (T : Finset HPos)
    {σ : Matrix (Unit × Quantum.Sig.SReg X Z HPos XD M) (Unit × Quantum.Sig.SReg X Z HPos XD M) ℂ}
    (hσ : σ.PosSemidef)
    (hsupp : QuerySupportedOn (fun q : Unit × Quantum.Sig.SReg X Z HPos XD M ↦ hcGrade N q.2)
      (Set.Iic t) σ) (ht : t + hcCharge (M := M) N (.inr T) ≤ N) :
    ∑ r, (MatrixMap.conj (diagonal fun x : Unit × Quantum.Sig.SReg X Z HPos XD M ↦
        if StoreConf pub x.2.2 then (1 : ℂ) else 0) (MatrixMap.conj (revKS T r) σ)).trace.re ≤
      (MatrixMap.conj (diagonal fun x : Unit × Quantum.Sig.SReg X Z HPos XD M ↦
        if StoreConf pub x.2.2 then (1 : ℂ) else 0) σ).trace.re +
        hcCharge (M := M) N (.inr T) * hcDelta N * σ.trace.re := by
  rw [hc_sum_trace_conj_rowInj (fun r ↦ revKS T r) (revKS_rowInj T)
    (fun x : Unit × Quantum.Sig.SReg X Z HPos XD M ↦ StoreConf pub x.2.2) σ,
    hc_trace_conj_diagonal_ind, Complex.re_sum, Matrix.trace, Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  rw [sum_revKS_normSq T (fun σ' ↦ StoreConf pub σ') y, sum_ind_normSq_revAmp]
  by_cases hy : σ y y = 0
  · simp [hy]
  have hgy := (hsupp y y hy).1
  obtain ⟨hok, hc⟩ := of_hcGrade_le hgy (by omega)
  have hb := card_agrees_storeConf_le (M := M) hload hok.1 hok.2 hc ht (T := T)
  have hcard : (0 : ℝ) < Fintype.card (RevealVals XD (T \ y.2.1.2.2.1)) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hratio : ((Finset.univ.filter fun w ↦ Agrees T y.2.1.2.2.1 (fill y.2.2) w ∧
      StoreConf pub (swapIn T y.2.1.2.2.1 w y.2.2)).card : ℝ) /
        Fintype.card (RevealVals XD (T \ y.2.1.2.2.1)) ≤
      (if StoreConf pub y.2.2 then 1 else 0) + hcCharge (M := M) N (.inr T) * hcDelta N :=
    (div_le_iff₀ hcard).mpr hb
  have h0 := hc_re_diag_nonneg hσ y
  calc (σ y y).re * (((Finset.univ.filter fun w ↦ Agrees T y.2.1.2.2.1 (fill y.2.2) w ∧
        StoreConf pub (swapIn T y.2.1.2.2.1 w y.2.2)).card : ℝ) /
          Fintype.card (RevealVals XD (T \ y.2.1.2.2.1)))
      ≤ (σ y y).re * ((if StoreConf pub y.2.2 then 1 else 0) +
          hcCharge (M := M) N (.inr T) * hcDelta N) := mul_le_mul_of_nonneg_left hratio h0
    _ = (if StoreConf pub y.2.2 then σ y y else 0).re +
          hcCharge (M := M) N (.inr T) * hcDelta N * (σ y y).re := by
        split_ifs <;> simp <;> ring

end potSph

/-! ### The sampled run -/

section sampledRun

open Quantum.Sig (Store fill swapIn revKS sampledRuntime ctrlK)
open Quantum.Xmss.Hybrid (kraus2)

variable {pub : Pub} {M : Type} [Fintype M] [DecidableEq M]

theorem hc_supp_basis {A B Y : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (a : A) (b : B) (f : B → Y) (S : Set Y) (h : f b ∈ S) :
    QuerySupportedOn (fun m : A × B ↦ f m.2) S
      ((SubState.basis a).matrix ⊗ₖ (SubState.basis b).matrix) := by
  intro m m' hm
  simp only [SubState.matrix_basis, kroneckerMap_apply] at hm
  have h' := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show f m.2 ∈ S ∧ f m'.2 ∈ S
    rw [← he.1, ← he.2]
    exact ⟨h, h⟩
  · exact absurd rfl h'

open Classical in
theorem hd_reveal (hload : HZLoad pub) (N t : ℕ) (T : Finset HPos)
    {σ : Matrix (Unit × Quantum.Sig.SReg X Z HPos XD M) (Unit × Quantum.Sig.SReg X Z HPos XD M) ℂ}
    (hσ : σ.PosSemidef)
    (hsupp : QuerySupportedOn (fun q : Unit × Quantum.Sig.SReg X Z HPos XD M ↦ hcGrade N q.2)
      (Set.Iic t) σ) (ht : t + hcCharge (M := M) N (.inr T) ≤ N) :
    ∑' r : RevealVals XD T × (Finset HPos × M),
        potential (confProj pub) (MatrixMap.conj (revKS T r) σ) ≤
      potential (confProj pub) σ + (hcCharge (M := M) N (.inr T) : ℝ≥0∞) *
        ENNReal.ofReal (hcDelta N) * ENNReal.ofReal σ.trace.re := by
  have hkey := sum_trace_revKS_le (M := M) hload N t T hσ hsupp ht
  have hP : ∀ (ρ : Matrix (Unit × Quantum.Sig.SReg X Z HPos XD M)
      (Unit × Quantum.Sig.SReg X Z HPos XD M) ℂ),
      potential (confProj pub) ρ = ENNReal.ofReal (MatrixMap.conj
        (diagonal fun x : Unit × Quantum.Sig.SReg X Z HPos XD M ↦
          if StoreConf pub x.2.2 then (1 : ℂ) else 0) ρ).trace.re := fun ρ ↦ by
    rw [potential, MatrixMap.amplifyLeft_conj, confProj, hc_one_kronecker_diagonal]
  have hnn : ∀ r, 0 ≤ (MatrixMap.conj (diagonal fun x : Unit × Quantum.Sig.SReg X Z HPos XD M ↦
      if StoreConf pub x.2.2 then (1 : ℂ) else 0) (MatrixMap.conj (revKS T r) σ)).trace.re :=
    fun r ↦ hc_trace_conj_re_nonneg _ (hc_conj_psd _ hσ)
  simp only [hP]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hnn r]
  refine (ENNReal.ofReal_le_ofReal hkey).trans ?_
  have hδ : 0 ≤ hcDelta N := by unfold hcDelta; positivity
  refine ENNReal.ofReal_add_le.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hδ),
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

open Classical in
/-- **Every port of the sampled runtime raises the store event's weight by at most its charge
times `hcDelta N`.** -/
theorem hd_sampled (hload : HZLoad pub) (N : ℕ) (m : M) (i : (SSpec M).Port) (t : ℕ)
    (σ : Matrix ((SSpec M).In i × (sampledRuntime goodAll m).D)
      ((SSpec M).In i × (sampledRuntime goodAll m).D) ℂ) (hσ : σ.PosSemidef)
    (hsupp : QuerySupportedOn (fun q : (SSpec M).In i × (sampledRuntime goodAll m).D ↦
      hcGrade N q.2) (Set.Iic t) σ) (ht : t + hcCharge N i ≤ N) :
    ∑' r, potential (confProj pub) (((sampledRuntime goodAll m).step i).branch r σ) ≤
      potential (confProj pub) σ + (hcCharge N i : ℝ≥0∞) * ENNReal.ofReal (hcDelta N) *
        ENNReal.ofReal σ.trace.re := by
  have hcomm : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (K : Store XD → Matrix (β × HwReg X Z (Finset HPos × M)) (α × HwReg X Z (Finset HPos × M)) ℂ),
      ((1 : Matrix β β ℂ) ⊗ₖ confProj pub) * ctrlK K =
        ctrlK K * ((1 : Matrix α α ℂ) ⊗ₖ confProj pub) :=
    fun K ↦ by
      unfold confProj
      exact one_kron_diag_mul_ctrlK (fun σ' ↦ if StoreConf pub σ' then (1 : ℂ) else 0) K
  rcases i with ((i | ⟨c, hcm⟩) | ⟨p, hp⟩) | T
  · exact (tsum_potential_le_of_commute (sampledRuntime goodAll m) (.inl (.inl (.inl i)))
      (confProj pub) (fun r ↦ ctrlK fun _ ↦ kraus2 X Z ((∅ : Finset HPos), m) (.inl (.inl i)) r)
      (fun _ ↦ rfl) (fun _ ↦ hcomm _) hσ).trans le_self_add
  · exact (tsum_potential_le_of_commute (sampledRuntime goodAll m) (.inl (.inl (.inr ⟨c, hcm⟩)))
      (confProj pub) (fun r ↦ ctrlK fun _ ↦ kraus2 X Z ((∅ : Finset HPos), m) (.inl (.inr c)) r)
      (fun _ ↦ by cases c <;> rfl) (fun _ ↦ hcomm _) hσ).trans le_self_add
  · cases p with
    | programH T₀ c₀ =>
      exact (tsum_potential_le_of_commute (sampledRuntime goodAll m)
        (.inl (.inr ⟨LazyProg.programH T₀ c₀, hp⟩)) (confProj pub)
        (fun r ↦ ctrlK fun σ' ↦ kraus2 X Z ((∅ : Finset HPos), m)
          (.inr ((LazyProg.programH T₀ c₀).realize (fill σ'))) r)
        (fun _ ↦ rfl) (fun _ ↦ hcomm _) hσ).trans le_self_add
    | programK T₀ c₀ =>
      exact (tsum_potential_le_of_commute (sampledRuntime goodAll m)
        (.inl (.inr ⟨LazyProg.programK T₀ c₀, hp⟩)) (confProj pub)
        (fun r ↦ ctrlK fun σ' ↦ kraus2 X Z ((∅ : Finset HPos), m)
          (.inr ((LazyProg.programK T₀ c₀).realize (fill σ'))) r)
        (fun _ ↦ rfl) (fun _ ↦ hcomm _) hσ).trans le_self_add
    | programK' T₀ c₀ =>
      exact (tsum_potential_le_of_commute (sampledRuntime goodAll m)
        (.inl (.inr ⟨LazyProg.programK' T₀ c₀, hp⟩)) (confProj pub)
        (fun r ↦ ctrlK fun σ' ↦ kraus2 X Z ((∅ : Finset HPos), m)
          (.inr ((LazyProg.programK' T₀ c₀).realize (fill σ'))) r)
        (fun _ ↦ rfl) (fun _ ↦ hcomm _) hσ).trans le_self_add
  · change ∑' r : RevealVals XD T × (Finset HPos × M),
        potential (confProj pub) (MatrixMap.conj (revKS T r) σ) ≤ _
    exact hd_reveal hload N t T hσ hsupp ht

end sampledRun

/-! ### The sampled game -/

section sampledGame

open Quantum.Sig (Store sampledRuntime)

variable {pub : Pub} {M : Type} [Fintype M] [DecidableEq M]

/-- The initial register of the sampled runtime. -/
def sInit (m : M) : Quantum.Sig.SReg X Z HPos XD M :=
  (((Database.empty, Database.empty, Database.empty), hwEmpty X Z, ((∅ : Finset HPos), m)),
    fun _ ↦ none)

omit [Fintype M] [DecidableEq M] in
theorem hcGrade_sInit (N : ℕ) (m : M) : hcGrade N (sInit m) ≤ 0 := by
  refine hcGrade_le_of ⟨fun s ↦ ?_, fun ⟨msg, h⟩ ↦ ?_⟩ (rndCount_free_le fun msg h ↦ ?_)
  · show (none : Option (XD s)) ≠ none ↔ s ∈ (∅ : Finset HPos)
    simp
  · exact absurd h (Finset.notMem_empty _)
  · exact absurd h (Finset.notMem_empty _)

open Classical in
theorem potential_init_eq_zero (m : M) :
    potential (confProj pub) ((SubState.basis ()).matrix ⊗ₖ
      (SubState.basis (sInit m)).matrix) = 0 := by
  rw [potential, MatrixMap.amplifyLeft_conj, confProj]
  have hS := hc_supp_basis () (sInit m) id
    {b : Quantum.Sig.SReg X Z HPos XD M | ¬StoreConf pub b.2} (not_storeConf_of fun _ ↦ rfl)
  have hρ : ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (sInit m)).matrix).PosSemidef :=
    ((SubState.basis ()).prod (SubState.basis (sInit m))).posSemidef
  have h := hc_trace_conj_diag_le (E := fun b : Quantum.Sig.SReg X Z HPos XD M ↦ StoreConf pub b.2)
    (E' := fun _ ↦ False) hρ hS fun _ hb he ↦ hb he
  have h0 : (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
      diagonal fun _ : Quantum.Sig.SReg X Z HPos XD M ↦ if False then (1 : ℂ) else 0)
      ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (sInit m)).matrix)) = 0 := by
    simp
  rw [h0, Matrix.trace_zero, Complex.zero_re] at h
  exact ENNReal.ofReal_eq_zero.mpr h

open Classical in
/-- **The store event at the end of the sampled game**: at most `N · hcDelta N`, for an adversary
with at most `N` signing requests. -/
theorem eventWeight_sampled_le (hload : HZLoad pub) (N : ℕ) (m : M) (upd : TrialUpd M)
    (A : SAdversary) (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) N) :
    (sampledRuntime goodAll m).eventWeight .instruments (confProj pub)
        (gameT M upd strPol pub A)
        ((SubState.basis ()).matrix ⊗ₖ (sampledRuntime (X := X) (Z := Z) goodAll m).init.matrix) ≤
      N * ENNReal.ofReal (hcDelta N) := by
  refine (eventWeight_eq_tsum_potential (sampledRuntime goodAll m) .instruments (confProj pub)
    (gameT M upd strPol pub A) _).trans_le ?_
  have hρ : ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (sInit m)).matrix).PosSemidef :=
    ((SubState.basis ()).prod (SubState.basis (sInit m))).posSemidef
  have hρg := hc_supp_basis () (sInit m) (hcGrade N) (Set.Iic 0)
    (hcGrade_sInit N m)
  refine (tsum_potential_run_le_charge (sampledRuntime goodAll m) .instruments (confProj pub)
    (hcGrade N) (hcCharge N) N (ENNReal.ofReal (hcDelta N))
    (fun i r t σ hσ ↦ hg_sampled N m i r t σ hσ)
    (fun i t σ hσ hs ht ↦ hd_sampled hload N m i t σ hσ hs ht) (gameT M upd strPol pub A) N 0
    (chgH_gameT N pub upd A hsign) (by omega) hρ hρg).trans ?_
  have htr : ENNReal.ofReal ((SubState.basis ()).matrix ⊗ₖ
      (SubState.basis (sInit m)).matrix).trace.re ≤ 1 :=
    ENNReal.ofReal_le_one.mpr ((SubState.basis ()).prod (SubState.basis (sInit m))).trace_re_le_one
  have h0 : potential (confProj pub) ((SubState.basis ()).matrix ⊗ₖ
      (SubState.basis (sInit m)).matrix) = 0 := potential_init_eq_zero m
  rw [h0, zero_add]
  calc (N : ℝ≥0∞) * ENNReal.ofReal (hcDelta N) * ENNReal.ofReal ((SubState.basis ()).matrix ⊗ₖ
        (SubState.basis (sInit m)).matrix).trace.re
      ≤ N * ENNReal.ofReal (hcDelta N) * 1 := by gcongr
    _ = N * ENNReal.ofReal (hcDelta N) := mul_one _

end sampledGame

/-! ## From the realized games to the sampled game -/

section bridge

open Quantum.Sig (Store storeOn embV embK embM embM_eq_conj trace_embM sampledRuntime
  branch_run_sampled)

variable {pub : Pub} {M : Type} [Fintype M] [DecidableEq M]

/-- A held `H_msg` conflict on registers whose held calls are revealed is the store event of the
label's values. -/
theorem storeConf_of_hConflict {v : (s : HPos) → XD s} (hself : HSelfSep pub v) {s : SReg}
    (hr : HmsgRev pub v s) (h : s ∈ HConflict pub v) : StoreConf pub (storeOn s.2.2.1 v) := by
  obtain ⟨M, i, M', i', hne', ⟨h1, -⟩, ⟨h3, -⟩, hz⟩ := h
  have hne : M ≠ M' := by
    rintro rfl
    have hii : i ≠ i' := fun h ↦ hne' (by rw [h])
    have h01 : ∀ j : DigestCall, j = 0 ∨ j = 1 := by decide
    rcases h01 i with rfl | rfl <;> rcases h01 i' with rfl | rfl
    · exact hii rfl
    · exact hself M _ hz
    · exact hself M _ hz.symm
    · exact hii rfl
  have hk : ∀ msg c, (cellK pub (hBlk pub v msg c) 0).1 = hBlk pub v msg c 0 :=
    fun _ _ ↦ rnK_zero _ _ _ _ _
  rw [hk] at h1 h3
  obtain ⟨hM, hroot⟩ := hr M i h1
  obtain ⟨hM', -⟩ := hr M' i' h3
  have hf : valsOf (Quantum.Sig.fill (storeOn s.2.2.1 v)) rootPos = valsOf v rootPos :=
    Quantum.Sig.fill_storeOn_of_mem hroot
  refine ⟨M, i, M', i', hne, v (.rnd M), v (.rnd M'), ite_eq_left hM, ite_eq_left hM', ?_⟩
  exact (hZf_congr pub hf M i _).trans (hz.trans (hZf_congr pub hf M' i' _).symm)

open Classical in
theorem confProj_mul_embK (v : (s : HPos) → XD s) :
    confProj (M := M) pub * embK (X := X) (Z := Z) v =
      embK v * diagonal fun d : HwReg X Z (Finset HPos × M) ↦
        if StoreConf pub (storeOn d.2.2.1 v) then (1 : ℂ) else 0 := by
  ext x d
  rw [confProj, diagonal_mul, mul_diagonal]
  simp only [embK, of_apply]
  by_cases h2 : x = embV v d
  · subst h2
    have he : StoreConf pub (embV (X := X) (Z := Z) v d).2 ↔ StoreConf pub (storeOn d.2.2.1 v) :=
      Iff.rfl
    by_cases h1 : StoreConf pub (storeOn d.2.2.1 v)
    · simp [h1, he.mpr h1]
    · simp [h1, mt he.mp h1]
  · simp [h2]

theorem hc_embM_psd {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
    {S : Type} [Fintype S] [DecidableEq S] {D : S → Type} [∀ s, Fintype (D s)]
    [∀ s, DecidableEq (D s)] {M : Type} [Fintype M] [DecidableEq M] {α : Type} [Fintype α]
    [DecidableEq α] (v : (s : S) → D s)
    {ρ : Matrix (α × HwReg X₁ Z₁ (Finset S × M)) (α × HwReg X₁ Z₁ (Finset S × M)) ℂ}
    (hρ : ρ.PosSemidef) : (Quantum.Sig.embM α v ρ).PosSemidef := by
  rw [Quantum.Sig.embM_eq_conj]
  exact hc_conj_psd _ hρ

/-- `HConflict` depends only on the hardwired cells. -/
theorem hConflict_congr (v : (s : HPos) → XD s) (s s' : SReg) (h : s.2 = s'.2) :
    s ∈ HConflict pub v ↔ s' ∈ HConflict pub v := by
  obtain ⟨d, b⟩ := s
  obtain ⟨d', b'⟩ := s'
  simp only at h
  subst h
  exact Iff.rfl

open Classical in
/-- **The conflict's decompressed weight is at most the store event's**, for a state supported on
`HmsgRev` (the realized runs on `HmsgSep`), embedded at the hidden values. -/
theorem trace_hConflict_le_embM (v : (s : HPos) → XD s) (hself : HSelfSep pub v) {α : Type}
    [Fintype α] [DecidableEq α] {Y : Matrix (α × SReg) (α × SReg) ℂ} (hY : Y.PosSemidef)
    (hS : QuerySupportedOn (fun m : α × SReg ↦ m.2) {s | HmsgRev pub v s} Y) :
    (MatrixMap.conj ((1 : Matrix α α ℂ) ⊗ₖ (compressReg X Z (Finset HPos × Selections) *
      diagonal (fun s ↦ @ite ℂ (s ∈ HConflict pub v) (Classical.decPred (· ∈ HConflict pub v) s)
        1 0) * compressReg X Z (Finset HPos × Selections))) Y).trace.re ≤
      (MatrixMap.conj ((1 : Matrix α α ℂ) ⊗ₖ confProj pub) (embM α v Y)).trace.re := by
  rw [decProj_eq_diagonal (HConflict pub v) (hdec := Classical.decPred _) (hConflict_congr v)]
  have e1 : MatrixMap.conj ((1 : Matrix α α ℂ) ⊗ₖ confProj pub) (embM α v Y) =
      embM α v (MatrixMap.conj ((1 : Matrix α α ℂ) ⊗ₖ diagonal fun d : SReg ↦
        if StoreConf pub (storeOn d.2.2.1 v) then (1 : ℂ) else 0) Y) := by
    rw [embM_eq_conj]
    show (MatrixMap.conj _ ∘ₗ MatrixMap.conj _) Y = (MatrixMap.conj _ ∘ₗ MatrixMap.conj _) Y
    rw [← MatrixMap.conj_mul, ← MatrixMap.conj_mul, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.one_mul, confProj_mul_embK]
  rw [e1, trace_embM]
  exact hc_trace_conj_diag_le (hE := Classical.decPred _)
    (E' := fun d : SReg ↦ StoreConf pub (storeOn d.2.2.1 v)) hY hS
    fun b hb he ↦ storeConf_of_hConflict hself hb he

open Classical in
/-- The conflict's decompressed weight is at most the trace. -/
theorem trace_hConflict_le_trace (v : (s : HPos) → XD s) {α : Type} [Fintype α]
    [DecidableEq α] {Y : Matrix (α × SReg) (α × SReg) ℂ} (hY : Y.PosSemidef) :
    (MatrixMap.conj ((1 : Matrix α α ℂ) ⊗ₖ (compressReg X Z (Finset HPos × Selections) *
      diagonal (fun s ↦ @ite ℂ (s ∈ HConflict pub v) (Classical.decPred (· ∈ HConflict pub v) s)
        1 0) * compressReg X Z (Finset HPos × Selections))) Y).trace.re ≤ Y.trace.re := by
  rw [decProj_eq_diagonal (HConflict pub v) (hdec := Classical.decPred _) (hConflict_congr v)]
  refine (hc_trace_conj_diag_le (hE := Classical.decPred _) (E' := fun _ : SReg ↦ True) hY
    (querySupportedOn_univ _ Y) fun _ _ _ ↦ trivial).trans (le_of_eq ?_)
  simp

end bridge

/-! ## The averaged conflict mass -/

section final

open Quantum.Sig (embM trace_embM sampledRuntime branch_run_sampled)

variable {pub : Pub}

open Classical in
/-- **The conflict mass** (SP-ER's `hConflictMass`, the same body): the decompressed weight of
`HConflict pub v` at the end of the canonical game `gameR strPol A pub v`. -/
noncomputable def hConflictMassP (m₀ : Finset HPos × Selections) (A : SAdversary) (pub : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m₀).eventWeight .instruments
    (compressReg X Z (Finset HPos × Selections) *
      diagonal (fun s ↦ @ite ℂ (s ∈ HConflict pub v) (Classical.decPred (· ∈ HConflict pub v) s)
        1 0) * compressReg X Z (Finset HPos × Selections))
    (gameR strPol A pub v)
    ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)

/-- **The conflict cap**: `N · 12 N / |R|`. -/
noncomputable def hConflictCap (N : ℕ) : ℝ :=
  N * hcDelta N

theorem card_randomizer : Fintype.card Randomizer = 2 ^ 128 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  rfl

theorem hConflictCap_eq (N : ℕ) : hConflictCap N = N * (12 * N) / 2 ^ 128 := by
  rw [hConflictCap, hcDelta, card_randomizer, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- **At leanSPHINCS's signature limit the cap is below `2^-64`.** -/
theorem hConflictCap_le : hConflictCap signatureLimit ≤ 1 / 2 ^ 64 := by
  rw [hConflictCap_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  norm_num [signatureLimit]

open Classical in
/-- **The averaged conflict mass.** For public data with `HZLoad pub` and an adversary with at
most `signatureLimit` signing requests, the conflict mass at the end of the canonical game, from
an empty label, averaged over the hidden values, is at most `hConflictCap signatureLimit` plus the
fraction of the hidden values violating `HmsgSep`. -/
theorem uavg_hConflictMassP_le (hload : HZLoad pub) (m : Selections) (A : SAdversary)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit) :
    uavg (fun v ↦ hConflictMassP ((∅ : Finset HPos), m) A pub v) ≤
      ENNReal.ofReal (hConflictCap signatureLimit) +
        uavg (fun v : (s : HPos) → XD s ↦
          @ite ℝ≥0∞ (HmsgSep pub v ∧ HSelfSep pub v) (Classical.propDecidable _) 0 1) := by
  set N := signatureLimit
  set y := gameT Selections cwUpd strPol pub A
  set ρ₀ : Matrix (Unit × HwReg X Z (Finset HPos × Selections))
      (Unit × HwReg X Z (Finset HPos × Selections)) ℂ :=
    (SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) ((∅ : Finset HPos), m)).init.matrix
  have hρ₀ : ρ₀.PosSemidef :=
    ((SubState.basis ()).prod (runtimeR (X := X) (Z := Z) ((∅ : Finset HPos), m)).init).posSemidef
  have hρ₀1 : ENNReal.ofReal ρ₀.trace.re ≤ 1 := ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := X) (Z := Z) ((∅ : Finset HPos), m)).init).trace_re_le_one
  set Yv := fun (v : (s : HPos) → XD s) (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) ↦
    ((runtimeR ((∅ : Finset HPos), m)).run .instruments (realizeT v y)).branch p ρ₀
  have hY : ∀ v p, (Yv v p).PosSemidef := fun v p ↦
    ((runtimeR ((∅ : Finset HPos), m)).run .instruments
      (realizeT v y)).posSemidef_branch_apply p hρ₀
  have hsupp : ∀ v, HmsgSep pub v → ∀ p,
      QuerySupportedOn (fun q : p.1 × SReg ↦ q.2) {s | HmsgRev pub v s} (Yv v p) := fun v hsep p ↦
    querySupportedOn_run_hmsgRev pub v ((∅ : Finset HPos), m) .instruments y ∅
      (disc_gameT Selections cwUpd strPol pub A ∅) (progsQ_gameT hsep cwUpd strPol A)
      (keepsLab_gameT Selections cwUpd strPol pub A) ρ₀
      (hc_supp_basis () _ (fun s ↦ s) {s | HmsgRev pub v s ∧ ∅ ⊆ s.2.2.1}
        ⟨fun _ _ h ↦ absurd rfl h, Finset.empty_subset _⟩) p
  -- the sampled game
  set ρs := (SubState.basis ()).matrix ⊗ₖ
    (sampledRuntime (X := X) (Z := Z) goodAll (M := Selections) m).init.matrix
  set sp := fun p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u ↦
    (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ confProj (M := Selections) pub)
      (((sampledRuntime goodAll m).run .instruments y).branch p ρs)).trace.re
  have hsum : ∀ p, ∑ v, (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ confProj pub)
      (embM p.1 v (Yv v p))).trace.re = Fintype.card ((s : HPos) → XD s) * sp p := fun p ↦ by
    have hb := branch_run_sampled (good := goodAll) .instruments m y
      (disc_gameT Selections cwUpd strPol pub A ∅) (keepsLab_gameT Selections cwUpd strPol pub A)
      (SubState.basis ()).matrix p
    have hc : (Fintype.card ((s : HPos) → XD s) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [sp, ρs]
    rw [hb, map_smul, map_sum, trace_smul, trace_sum, smul_eq_mul, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum, ← mul_assoc, mul_inv_cancel₀ hc,
      one_mul]
    rfl
  have hE : ∑' p, ENNReal.ofReal (sp p) ≤ N * ENNReal.ofReal (hcDelta N) :=
    eventWeight_sampled_le hload N m cwUpd A hsign
  have hcard0 : (Fintype.card ((s : HPos) → XD s) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcardT : (Fintype.card ((s : HPos) → XD s) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hbnn : ∀ v p, 0 ≤ (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ confProj pub)
      (embM p.1 v (Yv v p))).trace.re := fun v p ↦
    hc_trace_conj_re_nonneg _ (hc_embM_psd v (hY v p))
  -- per hidden values
  have hv : ∀ v, hConflictMassP ((∅ : Finset HPos), m) A pub v ≤
      ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ confProj pub)
        (embM p.1 v (Yv v p))).trace.re +
        @ite ℝ≥0∞ (HmsgSep pub v ∧ HSelfSep pub v) (Classical.propDecidable _) 0 1 := fun v ↦ by
    have hdef : hConflictMassP ((∅ : Finset HPos), m) A pub v = ∑' p, ENNReal.ofReal
        (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ (compressReg X Z (Finset HPos × Selections) *
          diagonal (fun s ↦ @ite ℂ (s ∈ HConflict pub v)
            (Classical.decPred (· ∈ HConflict pub v) s) 1 0) *
          compressReg X Z (Finset HPos × Selections))) (Yv v p)).trace.re := rfl
    rw [hdef]
    by_cases hsep : HmsgSep pub v ∧ HSelfSep pub v
    · exact (ENNReal.tsum_le_tsum fun p ↦ ENNReal.ofReal_le_ofReal
        (trace_hConflict_le_embM v hsep.2 (hY v p) (hsupp v hsep.1 p))).trans le_self_add
    · refine (ENNReal.tsum_le_tsum fun p ↦ ENNReal.ofReal_le_ofReal
        (trace_hConflict_le_trace v (hY v p))).trans (le_trans ?_ le_add_self)
      rw [ite_eq_right hsep]
      exact ((runtimeR ((∅ : Finset HPos), m)).run .instruments
        (realizeT v y)).isCPTNIFamily.tsum_ofReal_trace_re_le hρ₀ |>.trans hρ₀1
  have hmain : ∑ v, hConflictMassP ((∅ : Finset HPos), m) A pub v ≤
      Fintype.card ((s : HPos) → XD s) * (N * ENNReal.ofReal (hcDelta N)) +
        ∑ v : (s : HPos) → XD s,
          @ite ℝ≥0∞ (HmsgSep pub v ∧ HSelfSep pub v) (Classical.propDecidable _) 0 1 := by
    refine (Finset.sum_le_sum fun v _ ↦ hv v).trans ?_
    rw [Finset.sum_add_distrib, ← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
    gcongr
    calc ∑' p, ∑ v, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ confProj pub)
          (embM p.1 v (Yv v p))).trace.re
        = ∑' p, Fintype.card ((s : HPos) → XD s) * ENNReal.ofReal (sp p) := by
          refine tsum_congr fun p ↦ ?_
          rw [← ENNReal.ofReal_sum_of_nonneg fun v _ ↦ hbnn v p, hsum p,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ _ := by
          rw [ENNReal.tsum_mul_left]
          gcongr
  unfold uavg
  calc (Fintype.card ((s : HPos) → XD s) : ℝ≥0∞)⁻¹ *
        ∑ v, hConflictMassP ((∅ : Finset HPos), m) A pub v
      ≤ (Fintype.card ((s : HPos) → XD s) : ℝ≥0∞)⁻¹ *
          (Fintype.card ((s : HPos) → XD s) * (N * ENNReal.ofReal (hcDelta N)) +
            ∑ v : (s : HPos) → XD s,
              @ite ℝ≥0∞ (HmsgSep pub v ∧ HSelfSep pub v) (Classical.propDecidable _) 0 1) :=
        by gcongr
    _ = N * ENNReal.ofReal (hcDelta N) + (Fintype.card ((s : HPos) → XD s) : ℝ≥0∞)⁻¹ *
          ∑ v : (s : HPos) → XD s,
            @ite ℝ≥0∞ (HmsgSep pub v ∧ HSelfSep pub v) (Classical.propDecidable _) 0 1 := by
        rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hcard0 hcardT, one_mul]
    _ = _ := by
        congr 1
        rw [hConflictCap, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end final

/-! ## The fractions of the bad keys -/

section fracGen

variable {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [AddCommGroup Z₁]

/-- The `h`-cell of a one-block absorption of `b` under `π`, `k`, `k'`. -/
def z0 (π : Equiv.Perm (X₁ × Z₁)) (k k' : X₁ → Z₁) (b : X₁) : Z₁ :=
  (π (b, k b)).2 + k' (π (b, k b)).1

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] in
theorem rnZ_zero_eq_z0 [AddCommGroup X₁] (π : Equiv.Perm (X₁ × Z₁)) (h : Z₁ → X₁)
    (k k' : X₁ → Z₁) (b : ℕ → X₁) :
    rnZ π h k k' b 0 = z0 π k k' (b 0) := by
  simp only [rnZ, Quantum.Xmss.Assembly.rnMid, Quantum.Xmss.Assembly.rnR, rnK,
    Quantum.Xmss.Assembly.rnSt, zero_add, z0]

omit [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁] in
/-- **Two one-block absorptions meet only at distinct `k'`-cells**: at equal `k'`-cells the
capacities after `π` differ. -/
theorem r_ne_of_z0_eq {π : Equiv.Perm (X₁ × Z₁)} {k k' : X₁ → Z₁} {b b' : X₁} (hb : b ≠ b')
    (h : z0 π k k' b = z0 π k k' b') : (π (b, k b)).1 ≠ (π (b', k b')).1 := by
  intro hr
  apply hb
  have hc : (π (b, k b)).2 = (π (b', k b')).2 := by
    unfold z0 at h
    rw [hr] at h
    exact add_right_cancel h
  exact congrArg Prod.fst (π.injective (Prod.ext hr hc))

omit [Fintype X₁] [Fintype Z₁] [DecidableEq Z₁] in
theorem z0_update_of_ne {π : Equiv.Perm (X₁ × Z₁)} {k f : X₁ → Z₁} {b r : X₁} (a : Z₁)
    (h : (π (b, k b)).1 ≠ r) : z0 π k (Function.update f r a) b = z0 π k f b := by
  unfold z0
  rw [Function.update_of_ne h]

omit [Fintype X₁] [Fintype Z₁] [DecidableEq Z₁] in
theorem z0_update_self {π : Equiv.Perm (X₁ × Z₁)} {k f : X₁ → Z₁} {b : X₁} (a : Z₁) :
    z0 π k (Function.update f (π (b, k b)).1 a) b = (π (b, k b)).2 + a := by
  unfold z0
  rw [Function.update_self]

/-- **Resampling one value at the `k'`-cell of `b`**: `b`'s `h`-cell equals `g f` for at most a
`1 / |Z|` fraction of `A`, when `A` and `g` are blind to that cell. -/
theorem card_move_le (π : Equiv.Perm (X₁ × Z₁)) (k : X₁ → Z₁) (b : X₁)
    (A : (X₁ → Z₁) → Prop) [DecidablePred A] (g : (X₁ → Z₁) → Z₁)
    (hA : ∀ f a, A (Function.update f (π (b, k b)).1 a) ↔ A f)
    (hg : ∀ f a, g (Function.update f (π (b, k b)).1 a) = g f) :
    (Finset.univ.filter fun f ↦ A f ∧ z0 π k f b = g f).card * Fintype.card Z₁ ≤
      (Finset.univ.filter A).card := by
  have h := hc_card_filter_and_mul_le (β := fun _ : X₁ ↦ Z₁) (π (b, k b)).1 A
    (fun f ↦ z0 π k f b = g f) 1 hA fun f ↦ by
      refine Finset.card_le_one.mpr fun a ha a' ha' ↦ ?_
      simp only [Finset.mem_filter, z0_update_self, hg] at ha ha'
      exact add_left_cancel (ha.2.trans ha'.2.symm)
  rwa [one_mul] at h

/-- `card_move_le` from no condition. -/
theorem card_move_le₁ (π : Equiv.Perm (X₁ × Z₁)) (k : X₁ → Z₁) (b : X₁)
    (g : (X₁ → Z₁) → Z₁) (hg : ∀ f a, g (Function.update f (π (b, k b)).1 a) = g f) :
    (Finset.univ.filter fun f ↦ z0 π k f b = g f).card * Fintype.card Z₁ ≤
      Fintype.card (X₁ → Z₁) := by
  have h := card_move_le π k b (fun _ ↦ True) g (fun _ _ ↦ Iff.rfl) hg
  refine le_trans (Nat.mul_le_mul_right _ (hc_card_filter_le_of_imp _ _ fun _ h' ↦ ⟨trivial, h'⟩))
    (h.trans ((Finset.card_le_univ _).trans_eq Finset.card_univ))

/-- **Four one-block absorptions at distinct blocks share their `h`-cell** for at most a
`1 / |Z|^3` fraction of `k'`. -/
theorem card_quad_le (π : Equiv.Perm (X₁ × Z₁)) (k : X₁ → Z₁) {b₁ b₂ b₃ b₄ : X₁}
    (h₁₂ : b₁ ≠ b₂) (h₁₃ : b₁ ≠ b₃) (h₁₄ : b₁ ≠ b₄) (h₂₃ : b₂ ≠ b₃) (h₂₄ : b₂ ≠ b₄)
    (h₃₄ : b₃ ≠ b₄) :
    (Finset.univ.filter fun k' : X₁ → Z₁ ↦ (z0 π k k' b₂ = z0 π k k' b₁ ∧
      z0 π k k' b₃ = z0 π k k' b₁) ∧ z0 π k k' b₄ = z0 π k k' b₁).card *
        Fintype.card Z₁ ^ 3 ≤ Fintype.card (X₁ → Z₁) := by
  by_cases hr : (π (b₁, k b₁)).1 ≠ (π (b₂, k b₂)).1 ∧ (π (b₁, k b₁)).1 ≠ (π (b₃, k b₃)).1 ∧
      (π (b₁, k b₁)).1 ≠ (π (b₄, k b₄)).1 ∧ (π (b₂, k b₂)).1 ≠ (π (b₃, k b₃)).1 ∧
      (π (b₂, k b₂)).1 ≠ (π (b₄, k b₄)).1 ∧ (π (b₃, k b₃)).1 ≠ (π (b₄, k b₄)).1
  · obtain ⟨r₁₂, r₁₃, r₁₄, r₂₃, r₂₄, r₃₄⟩ := hr
    have s3 := card_move_le π k b₄
      (fun f ↦ z0 π k f b₂ = z0 π k f b₁ ∧ z0 π k f b₃ = z0 π k f b₁) (fun f ↦ z0 π k f b₁)
      (fun f a ↦ by
        simp only [z0_update_of_ne a r₂₄, z0_update_of_ne a r₁₄, z0_update_of_ne a r₃₄])
      (fun f a ↦ z0_update_of_ne a r₁₄)
    have s2 := card_move_le π k b₃ (fun f ↦ z0 π k f b₂ = z0 π k f b₁) (fun f ↦ z0 π k f b₁)
      (fun f a ↦ by simp only [z0_update_of_ne a r₂₃, z0_update_of_ne a r₁₃])
      (fun f a ↦ z0_update_of_ne a r₁₃)
    have s1 := card_move_le₁ π k b₂ (fun f ↦ z0 π k f b₁) (fun f a ↦ z0_update_of_ne a r₁₂)
    rw [pow_succ, pow_succ, pow_one, ← mul_assoc, ← mul_assoc]
    refine le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (hc_card_filter_le_of_imp _ _ fun _ h ↦ h)))) ?_
    refine le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ s3)) ?_
    refine le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (hc_card_filter_le_of_imp _ _ fun _ h ↦ h))) ?_
    refine le_trans (Nat.mul_le_mul_right _ s2) ?_
    exact le_trans (Nat.mul_le_mul_right _ (hc_card_filter_le_of_imp _ _ fun _ h ↦ h)) s1
  · have h0 : (Finset.univ.filter fun k' : X₁ → Z₁ ↦ (z0 π k k' b₂ = z0 π k k' b₁ ∧
        z0 π k k' b₃ = z0 π k k' b₁) ∧ z0 π k k' b₄ = z0 π k k' b₁) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun k' _ ⟨⟨e₂, e₃⟩, e₄⟩ ↦ hr ?_
      exact ⟨r_ne_of_z0_eq h₁₂ e₂.symm, r_ne_of_z0_eq h₁₃ e₃.symm, r_ne_of_z0_eq h₁₄ e₄.symm,
        r_ne_of_z0_eq h₂₃ (e₂.trans e₃.symm), r_ne_of_z0_eq h₂₄ (e₂.trans e₄.symm),
        r_ne_of_z0_eq h₃₄ (e₃.trans e₄.symm)⟩
    rw [h0, Finset.card_empty, zero_mul]
    exact Nat.zero_le _

/-- **Two one-block absorptions at distinct blocks share their `h`-cell** for at most a `1 / |Z|`
fraction of `k'`. -/
theorem card_pair_le (π : Equiv.Perm (X₁ × Z₁)) (k : X₁ → Z₁) {b₁ b₂ : X₁} (h₁₂ : b₁ ≠ b₂) :
    (Finset.univ.filter fun k' : X₁ → Z₁ ↦ z0 π k k' b₂ = z0 π k k' b₁).card *
      Fintype.card Z₁ ≤ Fintype.card (X₁ → Z₁) := by
  by_cases r₁₂ : (π (b₁, k b₁)).1 ≠ (π (b₂, k b₂)).1
  · exact card_move_le₁ π k b₂ (fun f ↦ z0 π k f b₁) (fun f a ↦ z0_update_of_ne a r₁₂)
  · have h0 : (Finset.univ.filter fun k' : X₁ → Z₁ ↦ z0 π k k' b₂ = z0 π k k' b₁) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun k' _ e ↦ r₁₂ (r_ne_of_z0_eq h₁₂ e.symm)
    rw [h0, Finset.card_empty, zero_mul]
    exact Nat.zero_le _

end fracGen

section fracGen2

variable {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [AddCommGroup Z₁]

/-- **The union bound for four-fold `h`-cell meets**: if every bad key pair has, for some label,
four distinct indices whose blocks' `h`-cells meet, the bad pairs are at most
`|Λ| |ι|^4 / |Z|^3` of all. -/
theorem card_bad_quad_le {Λ ι : Type} [Fintype Λ] [Fintype ι] [DecidableEq ι]
    (π : Equiv.Perm (X₁ × Z₁)) (blk : Λ → ι → X₁) (hinj : ∀ l, Function.Injective (blk l))
    (Bad : (X₁ → Z₁) → (X₁ → Z₁) → Prop) [∀ k, DecidablePred (Bad k)]
    (hbad : ∀ k k', Bad k k' → ∃ (l : Λ) (R₁ R₂ R₃ R₄ : ι), R₁ ≠ R₂ ∧ R₁ ≠ R₃ ∧ R₁ ≠ R₄ ∧
      R₂ ≠ R₃ ∧ R₂ ≠ R₄ ∧ R₃ ≠ R₄ ∧ (z0 π k k' (blk l R₂) = z0 π k k' (blk l R₁) ∧
        z0 π k k' (blk l R₃) = z0 π k k' (blk l R₁)) ∧
          z0 π k k' (blk l R₄) = z0 π k k' (blk l R₁)) :
    Fintype.card Z₁ ^ 3 * ∑ k, (Finset.univ.filter (Bad k)).card ≤
      Fintype.card (Λ × ι × ι × ι × ι) * (Fintype.card (X₁ → Z₁) * Fintype.card (X₁ → Z₁)) := by
  classical
  have hk : ∀ k, (Finset.univ.filter (Bad k)).card * Fintype.card Z₁ ^ 3 ≤
      Fintype.card (Λ × ι × ι × ι × ι) * Fintype.card (X₁ → Z₁) := fun k ↦ by
    let S : (Λ × ι × ι × ι × ι) → Finset (X₁ → Z₁) := fun t ↦
      if t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2.1 ∧ t.2.1 ≠ t.2.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2.1 ∧
        t.2.2.1 ≠ t.2.2.2.2 ∧ t.2.2.2.1 ≠ t.2.2.2.2 then
        Finset.univ.filter fun k' ↦ (z0 π k k' (blk t.1 t.2.2.1) = z0 π k k' (blk t.1 t.2.1) ∧
          z0 π k k' (blk t.1 t.2.2.2.1) = z0 π k k' (blk t.1 t.2.1)) ∧
            z0 π k k' (blk t.1 t.2.2.2.2) = z0 π k k' (blk t.1 t.2.1)
      else ∅
    have hsub : Finset.univ.filter (Bad k) ⊆ Finset.univ.biUnion S := fun k' hk' ↦ by
      obtain ⟨l, R₁, R₂, R₃, R₄, d₁₂, d₁₃, d₁₄, d₂₃, d₂₄, d₃₄, he⟩ :=
        hbad k k' (Finset.mem_filter.mp hk').2
      refine Finset.mem_biUnion.mpr ⟨(l, R₁, R₂, R₃, R₄), Finset.mem_univ _, ?_⟩
      simp only [S, ne_eq, d₁₂, d₁₃, d₁₄, d₂₃, d₂₄, d₃₄, not_false_eq_true, and_self,
        ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
      exact he
    have hS : ∀ t, (S t).card * Fintype.card Z₁ ^ 3 ≤ Fintype.card (X₁ → Z₁) := fun t ↦ by
      by_cases hd : t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2.1 ∧ t.2.1 ≠ t.2.2.2.2 ∧
          t.2.2.1 ≠ t.2.2.2.1 ∧ t.2.2.1 ≠ t.2.2.2.2 ∧ t.2.2.2.1 ≠ t.2.2.2.2
      · simp only [S, hd, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        obtain ⟨d₁₂, d₁₃, d₁₄, d₂₃, d₂₄, d₃₄⟩ := hd
        exact le_trans (Nat.mul_le_mul_right _ (hc_card_filter_le_of_imp _ _ fun _ h ↦ h))
          (card_quad_le π k ((hinj t.1).ne d₁₂) ((hinj t.1).ne d₁₃) ((hinj t.1).ne d₁₄)
            ((hinj t.1).ne d₂₃) ((hinj t.1).ne d₂₄) ((hinj t.1).ne d₃₄))
      · simp only [S, hd, ↓reduceIte, Finset.card_empty, zero_mul, Nat.zero_le]
    calc (Finset.univ.filter (Bad k)).card * Fintype.card Z₁ ^ 3
        ≤ (∑ t, (S t).card) * Fintype.card Z₁ ^ 3 :=
          Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
      _ = ∑ t, (S t).card * Fintype.card Z₁ ^ 3 := Finset.sum_mul _ _ _
      _ ≤ ∑ _t : Λ × ι × ι × ι × ι, Fintype.card (X₁ → Z₁) := Finset.sum_le_sum fun t _ ↦ hS t
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc Fintype.card Z₁ ^ 3 * ∑ k, (Finset.univ.filter (Bad k)).card
      = ∑ k, (Finset.univ.filter (Bad k)).card * Fintype.card Z₁ ^ 3 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    _ ≤ ∑ _k : X₁ → Z₁, Fintype.card (Λ × ι × ι × ι × ι) * Fintype.card (X₁ → Z₁) :=
        Finset.sum_le_sum fun k _ ↦ hk k
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

/-- **The union bound for two-call `h`-cell meets**: if every bad key pair has a label whose two
distinct blocks' `h`-cells meet, the bad pairs are at most `|Λ| / |Z|` of all. -/
theorem card_bad_pair_le {Λ : Type} [Fintype Λ] (π : Equiv.Perm (X₁ × Z₁)) (b₁ b₂ : Λ → X₁)
    (hne : ∀ l, b₁ l ≠ b₂ l) (Bad : (X₁ → Z₁) → (X₁ → Z₁) → Prop) [∀ k, DecidablePred (Bad k)]
    (hbad : ∀ k k', Bad k k' → ∃ l, z0 π k k' (b₂ l) = z0 π k k' (b₁ l)) :
    Fintype.card Z₁ * ∑ k, (Finset.univ.filter (Bad k)).card ≤
      Fintype.card Λ * (Fintype.card (X₁ → Z₁) * Fintype.card (X₁ → Z₁)) := by
  have hk : ∀ k, (Finset.univ.filter (Bad k)).card * Fintype.card Z₁ ≤
      Fintype.card Λ * Fintype.card (X₁ → Z₁) := fun k ↦ by
    have hsub : Finset.univ.filter (Bad k) ⊆ Finset.univ.biUnion fun l ↦
        Finset.univ.filter fun k' ↦ z0 π k k' (b₂ l) = z0 π k k' (b₁ l) := fun k' hk' ↦ by
      obtain ⟨l, he⟩ := hbad k k' (Finset.mem_filter.mp hk').2
      exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
    calc (Finset.univ.filter (Bad k)).card * Fintype.card Z₁
        ≤ (∑ l, (Finset.univ.filter fun k' ↦ z0 π k k' (b₂ l) = z0 π k k' (b₁ l)).card) *
            Fintype.card Z₁ :=
          Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
      _ = ∑ l, (Finset.univ.filter fun k' ↦ z0 π k k' (b₂ l) = z0 π k k' (b₁ l)).card *
            Fintype.card Z₁ := Finset.sum_mul _ _ _
      _ ≤ ∑ _l : Λ, Fintype.card (X₁ → Z₁) :=
          Finset.sum_le_sum fun l _ ↦ card_pair_le π k (hne l)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc Fintype.card Z₁ * ∑ k, (Finset.univ.filter (Bad k)).card
      = ∑ k, (Finset.univ.filter (Bad k)).card * Fintype.card Z₁ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
    _ ≤ ∑ _k : X₁ → Z₁, Fintype.card Λ * Fintype.card (X₁ → Z₁) :=
        Finset.sum_le_sum fun k _ ↦ hk k
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring

end fracGen2

/-! ### leanSPHINCS's key fractions -/

section fracSph

/-- **An `H_msg` block names its randomizer, message and call.** -/
theorem hmsg_blk_inj' (P : PublicParameter) {f g : ValPos → Digest} {R R' : Randomizer}
    {M M' : Message} {i i' : DigestCall}
    (h : slotBlk P (.hmsg R M i) f 0 = slotBlk P (.hmsg R' M' i') g 0) :
    R = R' ∧ M = M' ∧ i = i' := by
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 (length_blocks_hmsg P R M i f)
  obtain ⟨b', hb'⟩ := List.length_eq_one_iff.1 (length_blocks_hmsg P R' M' i' g)
  have e1 : slotBlk P (.hmsg R M i) f 0 = b := by
    unfold slotBlk
    rw [hb]
    rfl
  have e2 : slotBlk P (.hmsg R' M' i') g 0 = b' := by
    unfold slotBlk
    rw [hb']
    rfl
  have hbl : blocks (slotInput P (.hmsg R M i) f) = blocks (slotInput P (.hmsg R' M' i') g) := by
    rw [hb, hb', ← e1, ← e2, h]
  have hin : messageDigestInput R P (f rootPos) M i = messageDigestInput R' P (g rootPos) M' i' :=
    blocks_injective hbl
  obtain ⟨h1, -, -, h4, h5⟩ := messageDigestInput_injective hin
  exact ⟨h1, h4, h5⟩

theorem hZf_eq_z0 (pub : Pub) (f : ValPos → Digest) (M : Message) (i : DigestCall)
    (R : Randomizer) :
    hZf pub f M i R = z0 pub.perm pub.keys.2.1 pub.keys.2.2
      (slotBlk pub.seed (.hmsg R M i) (fun _ ↦ f rootPos) 0) := by
  rw [hZf, rnZ_zero_eq_z0, slotBlk_hmsg_congr pub (g := fun _ ↦ f rootPos) rfl]

open Classical in
/-- **`HZLoad` fails for at most `2^-639` of the keys `(k, k')`**, for every `PK.seed`, `π` and
`h`: four randomizers of one root, message and call meeting at one `h`-cell, `2^897` choices at
`|Z|^-3` each (`card_quad_le`). -/
theorem hZLoad_frac_le (P : PublicParameter) (π : Equiv.Perm (X × Z)) (h : Z → X) :
    Fintype.card Z ^ 3 * ∑ k : X → Z, (Finset.univ.filter fun k' : X → Z ↦
      ¬HZLoad ⟨P, π, (h, k, k')⟩).card ≤
      Fintype.card ((Digest × Message × DigestCall) × Randomizer × Randomizer × Randomizer ×
        Randomizer) * (Fintype.card (X → Z) * Fintype.card (X → Z)) :=
  card_bad_quad_le π (Λ := Digest × Message × DigestCall) (ι := Randomizer)
    (fun l R ↦ slotBlk P (.hmsg R l.2.1 l.2.2) (fun _ ↦ l.1) 0)
    (fun l _ _ he ↦ (hmsg_blk_inj' P he).1)
    (fun k k' ↦ ¬HZLoad ⟨P, π, (h, k, k')⟩) fun k k' hb ↦ by
      simp only [HZLoad, not_forall, not_le] at hb
      obtain ⟨f, M, i, z, hc⟩ := hb
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le 3) hc)
      have h2 : 2 < ((Finset.univ.filter fun R : Randomizer ↦
          hZf ⟨P, π, (h, k, k')⟩ f M i R = z).erase a).card := by
        rw [Finset.card_erase_of_mem ha]
        omega
      obtain ⟨b, c, d, hb, hc', hd, hbc, hbd, hcd⟩ := Finset.two_lt_card_iff.mp h2
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc' hd
      refine ⟨(f rootPos, M, i), a, b, c, d, Ne.symm hb.1, Ne.symm hc'.1, Ne.symm hd.1, hbc, hbd,
        hcd, ⟨?_, ?_⟩, ?_⟩
      · rw [← hZf_eq_z0 ⟨P, π, (h, k, k')⟩ f, ← hZf_eq_z0 ⟨P, π, (h, k, k')⟩ f, hb.2, ha]
      · rw [← hZf_eq_z0 ⟨P, π, (h, k, k')⟩ f, ← hZf_eq_z0 ⟨P, π, (h, k, k')⟩ f, hc'.2, ha]
      · rw [← hZf_eq_z0 ⟨P, π, (h, k, k')⟩ f, ← hZf_eq_z0 ⟨P, π, (h, k, k')⟩ f, hd.2, ha]

open Classical in
/-- **`HSelfSep` fails for at most `2^-128` of the keys `(k, k')`**, for every `PK.seed`, `π`, `h`
and hidden values: the two calls of one message and randomizer meeting, `2^384` choices at
`|Z|^-1` each (`card_pair_le`). -/
theorem hSelfSep_frac_le (P : PublicParameter) (π : Equiv.Perm (X × Z)) (h : Z → X)
    (v : (s : HPos) → XD s) :
    Fintype.card Z * ∑ k : X → Z, (Finset.univ.filter fun k' : X → Z ↦
      ¬HSelfSep ⟨P, π, (h, k, k')⟩ v).card ≤
      Fintype.card (Message × Randomizer) * (Fintype.card (X → Z) * Fintype.card (X → Z)) :=
  card_bad_pair_le π (Λ := Message × Randomizer)
    (fun l ↦ slotBlk P (.hmsg l.2 l.1 0) (fun _ ↦ valsOf v rootPos) 0)
    (fun l ↦ slotBlk P (.hmsg l.2 l.1 1) (fun _ ↦ valsOf v rootPos) 0)
    (fun l he ↦ absurd (hmsg_blk_inj' P he).2.2 (by decide))
    (fun k k' ↦ ¬HSelfSep ⟨P, π, (h, k, k')⟩ v) fun k k' hb ↦ by
      simp only [HSelfSep, not_forall, not_not] at hb
      obtain ⟨M, R, he⟩ := hb
      refine ⟨(M, R), ?_⟩
      have e0 := hZf_eq_z0 ⟨P, π, (h, k, k')⟩ (valsOf v) M 0 R
      have e1 := hZf_eq_z0 ⟨P, π, (h, k, k')⟩ (valsOf v) M 1 R
      exact e1.symm.trans (he.symm.trans e0)

end fracSph

end Quantum.Sphincs.Assembly

end
