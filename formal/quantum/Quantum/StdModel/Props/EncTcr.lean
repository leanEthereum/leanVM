module

public import Quantum.StdModel.Props.Basic

@[expose] public section

/-!
# Encoding target-collision resistance with grinding: EncTCR$ and EncTCR+C (design D5a, D5b)

The WOTS+C encoding hashes a message with a salt or counter until the digest is a codeword
(`isCode`), giving up after `limit` trials. Both games are multi-target target-collision games on
the selected digest, with distinct tweaks, won by any different input pair (strong
unforgeability needs the pair, not only the message, to differ).

* `encTcrSalt` (EncTCR$, leanXMSS): `P` is public. A target `(T, M)` gets a fresh uniform salt base
  `R_0` and the first `ρ_c = shift R_0 c` (`c < limit`) whose digest `Th(P, T, (M, ρ_c))` is a
  codeword, with that digest, or `none`. A forgery `(T, M', ρ')` wins against the target at `T`
  answered `(ρ, D)` when `(M', ρ') ≠ (M, ρ)` and `Th(P, T, (M', ρ')) = D`. This extends the
  cnM-eTCR of Bos, Hulsing, Renes, van Vredendaal (TCHES 2021, Section 4: a uniform salt and a
  grinding counter per target), the index being the tweak. Differences: salt and counter are
  merged additively (`ρ = R_0 + c`); the pair inequality instead of `M' ≠ M` (SUF); `P` uniform
  rather than chosen by the adversary. The published quantum bound of cnM-eTCR (BHRvV21,
  Theorem 3) is vacuous at `2^32` targets, `2^32` trials and 128-bit digests, so the generic
  plausibility of EncTCR$ rests on its own QROM bound (design, SM6) and on cryptanalysis.
* `encTcrCtr` (EncTCR+C, leanSPHINCS): the S-TCR(+C) of Hulsing, Kudinov, Ronen, Yogev (SPHINCS+C,
  S&P 2023, App. C): `P` hidden in phase 1, targets `(T, M)` in phase 1 answered with the least
  counter `c < limit` whose digest `Th(P, T, (M, c))` is a codeword and that digest (or `none`),
  evaluations of a collection at non-target tweaks, and `reveal`. A forgery `(T, M', c')` with
  `c' < limit` wins against the target at `T` answered `(c, D)` when `(M', c') ≠ (M, c)` and
  `Th(P, T, (M', c')) = D`. HKRY23 require `M' ≠ M`; the pair inequality is the strong
  (SUF) variant. HKRY23 assume a counter always exists; here the answer `none` is kept.

Both games give the adversary superposition access to the world's hash. Instance obligation for
EncTCR+C (see `Props.Basic`): the evaluation restriction compares tweaks, so no function of the
evaluation collection may produce the bytes of a target's digest input under another tweak.
-/

open OracleComp OracleSpec

namespace Quantum.StdModel.Props

open HashSig

/-! ## EncTCR$ -/

/-- **A salted encoding with grinding**: the digest `Th(P, T, (M, ρ))`, the codeword test, the
trial limit, and the salt of trial `c` from the base `R_0`. -/
structure SaltEnc (Par Tw Msg Salt Dig : Type) where
  /-- The encoding digest. -/
  hash : TwHash Par Tw (Msg × Salt) Dig
  /-- Whether a digest is a codeword. -/
  isCode : Dig → Bool
  /-- The number of trials. -/
  limit : ℕ
  /-- The salt of trial `c`: `R_0 + c`. -/
  shift : Salt → ℕ → Salt

variable {Par Tw Msg Salt Dig : Type} (W : OracleWorld)

/-- Grinding from trial `c` with `n` trials left: the first salt whose digest is a codeword, with
the digest. -/
noncomputable def SaltEnc.grind (e : SaltEnc Par Tw Msg Salt Dig) (P : Par) (t : Tw) (m : Msg)
    (r0 : Salt) : ℕ → ℕ → OracleComp W.Oracles (Option (Salt × Dig))
  | _, 0 => pure none
  | c, n + 1 => do
    let d ← e.hash.eval W () P t (m, e.shift r0 c)
    if e.isCode d then pure (some (e.shift r0 c, d)) else e.grind P t m r0 (c + 1) n

/-- **The rule of the EncTCR$ transcript**: pairwise distinct target tweaks. -/
def EncSaltValid (log : QueryLog (Tw × Msg →ₒ Option (Salt × Dig))) : Prop :=
  (log.map fun e ↦ e.1.1).Nodup

/-- **The EncTCR$ challenger**: a uniform public `P`; the target `(T, M)` is answered by grinding
from a fresh uniform base; the forgery `(T, M', ρ')` wins against the target at `T` answered
`(ρ, D)` when `(M', ρ') ≠ (M, ρ)` and its digest is `D`, on a valid transcript. -/
noncomputable def encTcrSalt [SampleableType Par] [SampleableType Salt]
    (e : SaltEnc Par Tw Msg Salt Dig) :
    Experiment W (Tw × Msg →ₒ Option (Salt × Dig)) Par (Tw × Msg × Salt) where
  State := Par
  setup := sample W Par
  pub P := P
  answer P q := do
    let r0 ← sample W Salt
    e.grind W P q.1 q.2 r0 0 e.limit
  judge P log out := do
    let d ← e.hash.eval W () P out.1 (out.2.1, out.2.2)
    pure (holds (EncSaltValid log ∧ ∃ x ∈ log, ∃ ρ, x.2 = some (ρ, d) ∧
      x.1.1 = out.1 ∧ (x.1.2, ρ) ≠ out.2))

/-- **EncTCR$ success probability** at the table `tab`. -/
noncomputable abbrev encTcrSaltSucc [SampleableType Par] [SampleableType Salt]
    (e : SaltEnc Par Tw Msg Salt Dig) (tab : W.Tab)
    (A : Adversary W (Tw × Msg →ₒ Option (Salt × Dig)) Par (Tw × Msg × Salt)) : ENNReal :=
  (encTcrSalt W e).succAt tab A

/-! ## EncTCR+C -/

/-- **A counter encoding with grinding**: the digest `Th(P, T, (M, c))`, the codeword test and
the counter limit. -/
structure CtrEnc (Par Tw Msg Dig : Type) where
  /-- The encoding digest. -/
  hash : TwHash Par Tw (Msg × ℕ) Dig
  /-- Whether a digest is a codeword. -/
  isCode : Dig → Bool
  /-- The number of counters. -/
  limit : ℕ

/-- Grinding from counter `c` with `n` counters left: the least counter whose digest is a
codeword, with the digest. -/
noncomputable def CtrEnc.grind (e : CtrEnc Par Tw Msg Dig) (P : Par) (t : Tw) (m : Msg) :
    ℕ → ℕ → OracleComp W.Oracles (Option (ℕ × Dig))
  | _, 0 => pure none
  | c, n + 1 => do
    let d ← e.hash.eval W () P t (m, c)
    if e.isCode d then pure (some (c, d)) else e.grind P t m (c + 1) n

/-- The classical queries of the EncTCR+C game. -/
inductive CtrQuery (Tw Msg Fn : Type) (CMsg : Fn → Type) where
  /-- A target `(T, M)`, phase 1 only, at a fresh tweak. -/
  | target (t : Tw) (m : Msg)
  /-- An evaluation `Th_l(P, T, M)` of the collection at a tweak no target uses. -/
  | eval (l : Fn) (t : Tw) (m : CMsg l)
  /-- The public parameter. -/
  | reveal

namespace CtrQuery

variable {Fn : Type} {CMsg : Fn → Type}

/-- The answer types: the counter and digest (or `none`), a digest of the collection, the
parameter. -/
def Resp (Par Dig Out : Type) : CtrQuery Tw Msg Fn CMsg → Type
  | .target .. => Option (ℕ × Dig)
  | .eval .. => Out
  | .reveal => Par

/-- Whether a query is `reveal`. -/
def isReveal : CtrQuery Tw Msg Fn CMsg → Bool
  | .reveal => true
  | _ => false

/-- Whether a query is a target. -/
def isTarget : CtrQuery Tw Msg Fn CMsg → Bool
  | .target .. => true
  | _ => false

variable {Out : Type}

/-- A transcript entry as a target: its tweak, message and answer. -/
def asTarget : ((q : CtrQuery Tw Msg Fn CMsg) × Resp Par Dig Out q) →
    Option ((Tw × Msg) × Option (ℕ × Dig))
  | ⟨.target t m, a⟩ => some ((t, m), a)
  | _ => none

/-- A transcript entry as an evaluation: its tweak. -/
def evalTweak : ((q : CtrQuery Tw Msg Fn CMsg) × Resp Par Dig Out q) → Option Tw
  | ⟨.eval _ t _, _⟩ => some t
  | _ => none

end CtrQuery

open CtrQuery

/-- The oracle specification of the EncTCR+C ports. -/
abbrev CtrSpec (Par Tw Msg Dig Fn : Type) (CMsg : Fn → Type) (Out : Type) :
    OracleSpec (CtrQuery Tw Msg Fn CMsg) :=
  OracleSpec.ofFn (Resp Par Dig Out)

variable {Fn Out : Type} {CMsg : Fn → Type}

/-- The targets of a transcript, in order. -/
def ctrTargets (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)) :
    List ((Tw × Msg) × Option (ℕ × Dig)) :=
  log.filterMap asTarget

/-- **The rules of the EncTCR+C transcript**: pairwise distinct target tweaks, every target before
the first reveal, and no evaluation at a target tweak. -/
def EncCtrValid (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)) : Prop :=
  ((ctrTargets log).map fun e ↦ e.1.1).Nodup ∧
    (∀ e ∈ phaseTwo (fun q ↦ q.isReveal) log, e.1.isTarget = false) ∧
    ∀ t ∈ log.filterMap evalTweak, t ∉ (ctrTargets log).map fun e ↦ e.1.1

/-- **The EncTCR+C challenger** for the encoding `e`, with the collection `C` behind the
evaluation port: a uniform hidden `P`; a target is answered by the least codeword counter; the
forgery `(T, M', c')` with `c' < limit` wins against the target at `T` answered `(c, D)` when
`(M', c') ≠ (M, c)` and its digest is `D`, on a valid transcript. -/
noncomputable def encTcrCtr [SampleableType Par] (e : CtrEnc Par Tw Msg Dig)
    (C : TwColl Par Tw Fn CMsg Out) :
    Experiment W (CtrSpec Par Tw Msg Dig Fn CMsg Out) Unit (Tw × Msg × ℕ) where
  State := Par
  setup := sample W Par
  pub _ := ()
  answer P
    | .target t m => e.grind W P t m 0 e.limit
    | .eval l t m => C.eval W l P t m
    | .reveal => pure P
  judge P log out := do
    let d ← e.hash.eval W () P out.1 (out.2.1, out.2.2)
    pure (holds (EncCtrValid log ∧ out.2.2 < e.limit ∧ ∃ x ∈ ctrTargets log, ∃ c,
      x.2 = some (c, d) ∧ x.1.1 = out.1 ∧ (x.1.2, c) ≠ out.2))

/-- **EncTCR+C success probability** at the table `tab`. -/
noncomputable abbrev encTcrCtrSucc [SampleableType Par] (e : CtrEnc Par Tw Msg Dig)
    (C : TwColl Par Tw Fn CMsg Out) (tab : W.Tab)
    (A : Adversary W (CtrSpec Par Tw Msg Dig Fn CMsg Out) Unit (Tw × Msg × ℕ)) : ENNReal :=
  (encTcrCtr W e C).succAt tab A

end Quantum.StdModel.Props

end
