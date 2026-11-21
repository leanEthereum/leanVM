module

public import Quantum.Sphincs.Assembly.GameTCalls
public import Quantum.Xmss.Assembly.Costs
public import Common.SphincsCost

@[expose] public section

/-!
# leanSPHINCS's honest costs and the cap on the hardwired cells

**Honest costs** in permutation calls of the statement's scheme over `π`
(`Sphincs.RandomPermutationModel.sufCmaScheme`), the costs `kc`, `sc`, `vc` of
`Quantum.SufCma.isTotalQueryBound_game` (`isTotalQueryBound_game_concrete`):

* `kc`, `sc`: key generation and one signature, **crude**: `Common.SphincsCost`'s `keygenCost` and
  `signCost`, which charge `8` calls to every addressed hash (the signer's `2^32` counter trials
  per layer included);
* `vc = verifyBlocks = 903`: the verification, one call per Keccak-f block
  (`Quantum.Sphincs.Assembly.verify_hashBlocks`).

Downstream statements use the names `kc`, `sc`, `vc`, never their values, so that sharper bounds
replace only these definitions' bodies.

**The cap.** Only the program ports change the hardwired cells, each by one cell, so after `K`
program calls every reachable state has `dbGrade W ≤ dbGrade W₀ + K` (leanXMSS's
`Quantum.Sponge.dbGrade_le_of_programs`). The template game makes at most
`progCap = progCalls = 2700 · signatureLimit` program calls (`hN_prog`), so from `W₀ = ∅` every
reachable state of runtime 2 with record ports (which keep the hardwired cells) has
`dbGrade W ≤ progCap` (`dbGrade_le_progCap`).
-/

open OracleComp OracleSpec Matrix IPFunctor
open scoped Kronecker

universe w uL vL

open Quantum.SufCma

open Quantum Sphincs Common Common.SufCma
open HashSig (MasterSeed Message)

namespace Quantum.Sphincs.Assembly

/-! ## The honest costs -/

/-- **`kc`**, crude: the key generation's permutation calls, `8` per addressed hash
(`Common.SphincsCost.KeyGenerationAndSigning.keygenCost`). -/
def kc : ℕ :=
  Common.SphincsCost.KeyGenerationAndSigning.keygenCost

/-- **`sc`**, crude: one signature's permutation calls, `8` per addressed hash, the counter search
at its cap of `2^32` trials per layer (`Common.SphincsCost.KeyGenerationAndSigning.signCost`). -/
def sc : ℕ :=
  Common.SphincsCost.KeyGenerationAndSigning.signCost

/-- **`vc`**: the verification's permutation calls, one per Keccak-f block (`verifyBlocks`,
`903`). -/
def vc : ℕ :=
  verifyBlocks

theorem vc_eq : vc = 903 :=
  verifyBlocks_eq

/-- The statement's key generation makes at most `kc` permutation calls. -/
theorem generateKeys_cost_kc (S0 : MasterSeed) :
    QueryCostAtMost (RandomPermutationModel.sufCmaScheme.generateKeys S0) permutationCallCost kc :=
  Common.SphincsCost.sufCmaScheme_generateKeys_cost S0

/-- The statement's signer makes at most `sc` permutation calls per message. -/
theorem sign_cost_sc (sk : SecretKey) (msg : Message) :
    QueryCostAtMost (RandomPermutationModel.sufCmaScheme.sign sk msg) permutationCallCost sc :=
  Common.SphincsCost.sufCmaScheme_sign_cost sk msg

/-- The statement's verifier makes at most `vc` permutation calls: the hash-query verifier's
blocks, one call each over `π`. -/
theorem verify_cost_vc (pk : PublicKey) (f : Forgery) :
    QueryCostAtMost (RandomPermutationModel.sufCmaScheme.verify pk f) permutationCallCost vc := by
  rw [← simulateQ_schemeHash_verify]
  exact isWeightBound_simulateQ _ _ _ Quantum.Xmss.schemeHashOverPermutation_cost
    (verify_hashBlocks pk f)

/-- **The game's calls**: key generation's `kc`, the adversary's `q`, at most `sc` per signing
request, and verification's `vc`. -/
theorem isTotalQueryBound_game_concrete {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (e : LeanVM.Semantics.KeccakState ≃ S) (S0 : MasterSeed)
    {A : Adversary PublicKey Message (Option Signature) Forgery S} {q n : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsignq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) n) :
    (game RandomPermutationModel.sufCmaScheme e S0 A).IsTotalQueryBound
      (kc + (q + sc * n) + vc) :=
  isTotalQueryBound_game RandomPermutationModel.sufCmaScheme e S0 (generateKeys_cost_kc S0)
    sign_cost_sc verify_cost_vc hperm hsignq

/-! ## The cap on the hardwired cells -/

/-- **The cap `N` of the event**: the game's program calls (`progCalls`, `hN_prog`), `2700` per
signing request. -/
def progCap : ℕ :=
  progCalls

theorem progCap_eq : progCap = 2700 * signatureLimit :=
  progCalls_eq

section extend

variable {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  {M : Type} [Fintype M] [DecidableEq M]
  [AddCommGroup X₁] [AddCommGroup Z₁] [Nonempty X₁] [Nonempty Z₁]
  {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg}

/-- **The cap on reachable states for runtime 2 extended by ports keeping the hardwired cells**
(such as record ports): a program making at most `K ≤ progCap` program calls on every path ends,
on every branch, supported on `dbGrade W ≤ progCap`. -/
theorem dbGrade_le_progCap {t : QuantumOracleSpec.{0, 0}} (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × (Xmss.Hybrid.runtime2 X₁ Z₁ m₀).D)
      (t.Out j × (Xmss.Hybrid.runtime2 X₁ Z₁ m₀).D) (t.Result j))
    (hstep' : ∀ j r n (σ : Matrix (t.In j × (Xmss.Hybrid.runtime2 X₁ Z₁ m₀).D)
        (t.In j × (Xmss.Hybrid.runtime2 X₁ Z₁ m₀).D) ℂ),
      QuerySupportedOn (fun q : t.In j × (Xmss.Hybrid.runtime2 X₁ Z₁ m₀).D ↦
          Sponge.dbGrade q.2.2.1) (Set.Iic n) σ →
      QuerySupportedOn (fun q : t.Out j × (Xmss.Hybrid.runtime2 X₁ Z₁ m₀).D ↦
          Sponge.dbGrade q.2.2.1) (Set.Iic n) ((step' j).branch r σ))
    (I : L.Interp) {x : QuantumComp L ((Sponge.hwSpec X₁ Z₁ M).sum t) W A} {K : ℕ}
    (hx : IFreeM.IsChargeBound x (Sponge.portCharge (Xmss.extProgCharge X₁ Z₁ M t)) K)
    (hK : K ≤ progCap) (ρ : SubState A) (p : Σ u, W u) :
    QuerySupportedOn (fun s : p.1 × Sponge.HwReg X₁ Z₁ M ↦ Sponge.dbGrade s.2.2.1)
      (Set.Iic progCap)
      ((((Xmss.Hybrid.runtime2 X₁ Z₁ m₀).extend step').run I x).branch p
        (ρ.matrix ⊗ₖ (Xmss.Hybrid.runtime2 X₁ Z₁ m₀).init.matrix)) := by
  have hgrade : QuerySupportedOn (fun m : A × Sponge.HwReg X₁ Z₁ M ↦ Sponge.dbGrade m.2.2.1)
      (Set.Iic 0) (ρ.matrix ⊗ₖ (Xmss.Hybrid.runtime2 X₁ Z₁ m₀).init.matrix) := by
    intro m m' hm
    change (ρ.matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
      Sponge.hwEmpty X₁ Z₁, m₀) : Sponge.HwReg X₁ Z₁ M)).matrix) m m' ≠ 0 at hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · constructor <;> simp [← he.1, ← he.2, Sponge.hwEmpty, Sponge.dbGrade, Database.size_empty]
    · exact False.elim (h rfl)
  refine (QuerySupportedOn.run_of_charge_step ((Xmss.Hybrid.runtime2 X₁ Z₁ m₀).extend step')
    (fun s : Sponge.HwReg X₁ Z₁ M ↦ Sponge.dbGrade s.2.1) (Xmss.extProgCharge X₁ Z₁ M t)
    (fun i r n σ hσ ↦ ?_) I hx hgrade p).mono (Set.Iic_subset_Iic.2 (by omega))
  rcases i with i | j
  · exact Sponge.querySupportedOn_hw_step (Sponge.hwEmpty X₁ Z₁) m₀ i r n σ hσ
  · exact hstep' j r n σ hσ

end extend

end Quantum.Sphincs.Assembly

end
