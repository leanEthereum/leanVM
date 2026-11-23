module

public import Quantum.Qrom.Xmss.GameT
public import Quantum.Qrom.Xmss.Multi.Memo
public import Quantum.Qrom.Xmss.Multi.Table

@[expose] public section

/-!
# leanXMSS's multi-user game with honest read ports and a selection memo, in the QROM

The `n`-user analog of `Quantum.Qrom.Xmss.GameReads`, with the top-layer memo of the design
(section 3.5) moved to the adversary's side: `memoFrom T x` runs the adversary `x` and attaches
to each signing request of user `i` the top selection memoized for the request's top key
(`SelMemo`), reading the selection from the answer. The signing ports of `memoSpec n` take the
request with the memoized selection and return the signature with the top selection. A signer
receiving a memoized selection computes no top-layer search.

* `memoSpec n`, `SelMemo n`, `memoFrom T x`: the ports with the memo, the memo, the transformed
  adversary.
* `signWithN`, `topWithN`: two layers' searches and publications, the top search replaced by the
  memoized selection when there is one.
* `challengeWithN M sgn`, `gameReadsWithN M sgn pks valid A`: the multi-user game after key
  generation with a read signer `sgn`, against `memoFrom` from the empty memo.

## Main statements

* `intertwines_muChallenged_memoFrom`: against a function consistent with every user's table,
  the challenged adversary and its memo transform with a read signer returning the users'
  signatures and top selections intertwine, from every memo that agrees with the function.
* `evalDistMap_muGame_eq_readsN`: the multi-user game has the law of `gameReadsWithN` against the
  classical reads.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open LeanXmss HashSig
open Quantum.Sponge (Hw hwReadSpec hwReadCmdSpec spongeFnReadRuntime overwrite ReadsTo hwAt
  hwCol hwAt_basis conjTranspose_hwCol_mul_self intertwines_run_pure intertwines_run₂_pure
  intertwines_run₂_bind intertwines_run₂_act_bind intertwines_run_of_run₂ intertwines_run₂_of_run
  intertwines_run_bind run₂_bind_of_classicalOn_pure evalDistMap_eq_of_intertwines)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muChallenge muChallenged muGame generateAll
  withMuSignLog MuSignLog)

variable {n : ℕ}

/-! ## The signing ports with the memo -/

/-- **A top-layer selection**: the result of a top key's randomizer search. -/
abbrev TopSel : Type :=
  Option (Randomizer × Encoding)

/-- **The adversary's ports with the memo**: a signing request carries the top selection memoized
for its top key, if any; the answer is the signature and the top selection. -/
abbrev memoSpec (n : ℕ) : QuantumOracleSpec.{0, 0} :=
  muAdvSpec n (SigningRequest × Option TopSel) (Option Signature × TopSel)

-- The adversary's commands, as indexed polynomial functors.
set_option quotPrecheck false in
local notation "MuP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n SigningRequest (Option Signature))

set_option quotPrecheck false in
local notation "MemoP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpec n)

/-- **The selection memo**: per user and top key, the top selection once computed. -/
abbrev SelMemo (n : ℕ) : Type :=
  Fin n → KeyIndex → Option TopSel

/-- Memoize the top selection `s` of user `i` at the top key `t`. -/
def SelMemo.put (T : SelMemo n) (i : Fin n) (t : KeyIndex) (s : TopSel) : SelMemo n :=
  Function.update T i (Function.update (T i) t (some s))

theorem SelMemo.put_self (T : SelMemo n) (i : Fin n) (t : KeyIndex) (s : TopSel) :
    T.put i t s i t = some s := by
  simp [SelMemo.put]

theorem SelMemo.put_of_ne (T : SelMemo n) {i j : Fin n} {t u : KeyIndex} (s : TopSel)
    (h : ¬(j = i ∧ u = t)) : T.put i t s j u = T j u := by
  simp only [SelMemo.put]
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Function.update_of_ne fun hu ↦ h ⟨rfl, hu⟩]
  · rw [Function.update_of_ne hj]

/-- **The memo transform**: the adversary's program with each signing request of user `i`
carrying the selection memoized at the request's top key, and the answer's selection memoized. -/
def memoFrom {Y : QReg → Type} : {A : QReg} → SelMemo n → IFreeM (MuP n) Y A →
    IFreeM (MemoP n) Y A
  | _, _, .pure y => .pure y
  | _, T, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ memoFrom T (next b)
  | _, T, .liftBind (.query .hash E ℓ) next =>
      .liftBind (.query .hash E ℓ) fun b ↦ memoFrom T (next b)
  | _, T, .liftBind (.query (.sign i r) E ℓ) next =>
      .liftBind (.query (.sign i (r, T i (topKeyOf r))) E ℓ) fun b ↦
        memoFrom (T.put i (topKeyOf r) (b.down : Option Signature × TopSel).2)
          (next (ULift.up (b.down : Option Signature × TopSel).1))

/-! ## Read signers -/

/-- The signature of a request from its two layers' searches, publishing both layers when both
succeed. -/
noncomputable def pubBothN {spec : QuantumOracleSpec.{0, 0}} {B : QReg}
    (pub : Layer → KeyIndex → Randomizer → Encoding → QComp spec B B LayerSignature)
    (r : SigningRequest) : TopSel → TopSel → QComp spec B B (Option Signature)
  | some (ρb, xb), some (ρt, xt) =>
    (pub bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) ρb xb).bind fun bottom ↦
      (pub topLayer (keyIndexOnLayer r.leafIndex topLayer) ρt xt).bind fun top ↦
        QuantumComp₂.pure
          (some ⟨r.leafIndex, fun lay ↦ if lay = bottomLayer then bottom else top⟩)
  | _, _ => QuantumComp₂.pure none

/-- **The top layer's search or its memo**: the memoized selection if any, otherwise the search
on the bottom root `root`. -/
noncomputable def topWithN {spec : QuantumOracleSpec.{0, 0}} {B : QReg}
    (sel : Layer → KeyIndex → MsgBytes → Pos → QComp spec B B TopSel) (root : Digest)
    (r : SigningRequest) : Option TopSel → QComp spec B B TopSel
  | some o => QuantumComp₂.pure o
  | none => sel topLayer (keyIndexOnLayer r.leafIndex topLayer) (rootBytes root)
      (.rndTop (keyIndexOnLayer r.leafIndex topLayer) root)

/-- **A signature with the memo**: the bottom layer's search, the top layer's search `top` (or its
memo), the layers published when both succeed; the answer and the top selection. -/
noncomputable def signWithN {spec : QuantumOracleSpec.{0, 0}} (B : QReg)
    (sel : Layer → KeyIndex → MsgBytes → Pos → QComp spec B B TopSel)
    (pub : Layer → KeyIndex → Randomizer → Encoding → QComp spec B B LayerSignature)
    (top : QComp spec B B TopSel) (r : SigningRequest) :
    QComp spec B B (Option Signature × TopSel) :=
  (sel bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) (messageBytes r.message)
    (.rndBottom (keyIndexOnLayer r.leafIndex bottomLayer) r.message)).bind fun gb ↦
    top.bind fun gt ↦ (pubBothN pub r gb gt).map fun s ↦ (s, gt)

/-- A read signer: for user `i`, request `r` and memoized selection `h`, a program beside `B`. -/
abbrev SignerN (M : Type) [Fintype M] [DecidableEq M] (n : ℕ) : Type 1 :=
  Fin n → SigningRequest → Option TopSel → (B : QReg) →
    QComp (hwReadSpec HashOutput HashDomain M) B B (Option Signature × TopSel)

/-- The answer to a signing request with the adversary's register held, from a program (the
register named as in `answerTree`). -/
noncomputable def signAtN {spec : QuantumOracleSpec.{0, 0}} (i : Fin n) (q : SigningRequest ×
    Option TopSel) (E : QReg) {A : QReg} (ℓ : A ≃ (memoSpec n).In (.sign i q) × E)
    (sgn : (B : QReg) → QComp spec B B (Option Signature × TopSel)) :
    QComp spec A (QReg.of ((memoSpec n).Out (.sign i q) × E)) (Option Signature × TopSel) :=
  (QComp.act (spec := spec)
    (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign q.1) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ sgn _

/-- The secret keys carrying nothing. -/
def noKeys : Fin n → SecretKey :=
  fun _ ↦ noKey

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The multi-user challenger with honest reads, from a read signer**: local operations and hash
calls as `muChallenge`, lifted to port `h`; a signing request answered by `sgn`. -/
noncomputable def challengeWithN (sgn : SignerN M n) :
    IPFunctor.CommandSubstitution (MemoP n)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec HashOutput HashDomain M))
  | A, .prim o => (liftH (muChallenge xmssRom (noKeys (n := n)) A (.prim o))).liftOrdinary
  | A, .query .hash E ℓ =>
      (liftH (muChallenge xmssRom (noKeys (n := n)) A (.query .hash E ℓ))).liftOrdinary
  | _, .query (.sign i q) E ℓ =>
      QuantumComp.bind (signAtN i q E ℓ (sgn i q.1 q.2)) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The multi-user game with honest reads after key generation**: the adversary's memo transform
against `challengeWithN M sgn` from the empty memo, with all users' transcript, the verification
through read ports under the forged user's key `pks`, and the winning condition. -/
noncomputable def gameReadsWithN (sgn : SignerN M n) (pks : Fin n → PublicKey)
    (valid : SignLog → Bool) (A : MuAdversary n) :
    QComp (hwReadSpec HashOutput HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IPFunctor.IFreeM.substitute (challengeWithN M sgn)
    (memoFrom (fun _ _ ↦ none) (withMuSignLog (A pks)))) fun run ↦
    ((readsProgram M _ (xmssRom.verify (pks run.1.1) run.1.2)).map Prod.fst).bind fun verified ↦
      QuantumComp₂.pure (xmssRom.winningCondition (run.2.user run.1.1) run.1.2 &&
        run.2.allValid valid && verified)

variable {M}

/-! ## The memo transform and its substitution at a signing request -/

/-- The substituted memo transform at a signing request: the signer's answer program, then the
transform of the continuation with the answer's selection memoized. -/
theorem substitute_memoFrom_liftBind_sign (sgn : SignerN M n) {C : QReg} {α : Type} {A : QReg}
    (T : SelMemo n) (i : Fin n) (r : SigningRequest) (E : QReg)
    (ℓ : A ≃ (muAdvSpec n SigningRequest (Option Signature)).In (.sign i r) × E)
    (next : (b : (MuP n).B A (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ)) →
      IFreeM (MuP n) (QuantumComp₂.Leaf C α)
        ((MuP n).src A (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) b)) :
    (memoFrom T (IFreeM.liftBind (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) next)).substitute
        (challengeWithN M sgn) =
      QuantumComp₂.bind (signAtN i (r, T i (topKeyOf r)) E ℓ (sgn i r (T i (topKeyOf r))))
        fun w ↦ (memoFrom (T.put i (topKeyOf r) w.2) (next (ULift.up w.1))).substitute
          (challengeWithN M sgn) := by
  refine (IFreeM.bind_assoc _ _ _).trans
    (congrArg (IFreeM.bind _) (funext fun u ↦ funext fun l ↦ ?_))
  obtain ⟨rfl, a⟩ := l
  rfl

/-! ## Intertwining with the game -/

section intertwine

attribute [local irreducible] xmssRom QTable.select QTable.signature

variable {t : (HashDomain → HashOutput) × (HashOutput → HashDomain) × (HashOutput → HashDomain)}
  {W : Hw HashOutput HashDomain} {m : M}

/-- **A deterministic step on each side, then intertwining continuations**: an honest
computation returning `a₀` with certainty and a read program returning `b₀` with certainty on the
block, continued by programs that intertwine at `a₀` and `b₀`. -/
theorem intertwines_bind_classicalOn_readsTo {B C : QReg} {α β γ : Type}
    {x₁ : QComp romSpec B B α} {a₀ : α}
    (h₁ : ClassicalOn (additiveOracleRuntime (overwrite W t).1) x₁ (pure a₀) LinearMap.id)
    {x₂ : QComp (hwReadSpec HashOutput HashDomain M) B B β} {b₀ : β} (h₂ : ReadsTo t W m x₂ b₀)
    {k₁ : α → QComp romSpec B C γ} {k₂ : β → QComp (hwReadSpec HashOutput HashDomain M) B C γ}
    (hk : DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments (k₁ a₀))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments (k₂ b₀))) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments (x₁.bind k₁))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments (x₂.bind k₂)) := by
  rw [run₂_bind_of_classicalOn_pure h₁]
  intro c
  have key : ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments
      (x₂.bind k₂)).branch c ∘ₗ (hwAt W m).amplifyLeft B =
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments (k₂ b₀)).branch c ∘ₗ
        (hwAt W m).amplifyLeft B := by
    refine LinearMap.ext fun ρ ↦ ?_
    have h₀ : ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments x₂).branch b₀
        ((hwAt W m).amplifyLeft B ρ) = (hwAt W m).amplifyLeft B ρ :=
      LinearMap.congr_fun h₂.1 ρ
    have h₃ : ∀ b ≠ b₀, ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments
        x₂).branch b ((hwAt W m).amplifyLeft B ρ) = 0 := fun b hb ↦
      LinearMap.congr_fun (h₂.2 b hb) ρ
    change ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments (x₂.bind k₂)).branch
        c ((hwAt W m).amplifyLeft B ρ) =
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments (k₂ b₀)).branch c
        ((hwAt W m).amplifyLeft B ρ)
    rw [QuantumRuntime.run₂_bind]
    erw [DSubInstrument.branch_bind_apply]
    rw [tsum_eq_single b₀ fun b hb ↦ by erw [h₃ b hb, map_zero]]
    erw [h₀]
  exact key.trans (hk c)

/-- **A local operation, a deterministic step on each side, then intertwining continuations.** -/
theorem intertwines_act_bind_bind {A B C : QReg} {α β γ : Type} (p : SubInstrument A B Unit)
    {x₁ : QComp romSpec B B α} {a₀ : α}
    (h₁ : ClassicalOn (additiveOracleRuntime (overwrite W t).1) x₁ (pure a₀) LinearMap.id)
    {x₂ : QComp (hwReadSpec HashOutput HashDomain M) B B β} {b₀ : β} (h₂ : ReadsTo t W m x₂ b₀)
    {k₁ : α → QComp romSpec B C γ} {k₂ : β → QComp (hwReadSpec HashOutput HashDomain M) B C γ}
    (hk : DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments (k₁ a₀))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments (k₂ b₀))) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments
        (((QComp.act p).bind fun _ ↦ x₁).bind k₁))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments
        (((QComp.act p).bind fun _ ↦ x₂).bind k₂)) := by
  rw [QuantumComp₂.bind_assoc, QuantumComp₂.bind_assoc]
  exact intertwines_run₂_act_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m) p
    fun _ ↦ intertwines_bind_classicalOn_readsTo h₁ h₂ hk

variable (t W m)

/-- The top selection of key `t` of the top layer of a table against `H`: the search on the root
of the bottom tree below `t`. -/
def topSelOf (u : QTable) (H : HashDomain → HashOutput) (t : KeyIndex) : TopSel :=
  u.select H topLayer t (rootBytes (u.treeValue bottomLayer layerHeight t.val))
    (truncateHash (u (.rndTop t (u.treeValue bottomLayer layerHeight t.val))))

/-- **The memo agrees with `H`**: every memoized selection of user `i` is the top selection of
`w`'s user `i` against `H`. -/
def SelMemoOK (w : QTableN n) (H : HashDomain → HashOutput) (T : SelMemo n) : Prop :=
  ∀ i u o, T i u = some o → o = topSelOf (w.user i) H u

theorem selMemoOK_empty (w : QTableN n) (H : HashDomain → HashOutput) :
    SelMemoOK w H fun _ _ ↦ none :=
  fun _ _ _ h ↦ by simp at h

theorem SelMemoOK.put {w : QTableN n} {H : HashDomain → HashOutput} {T : SelMemo n}
    (hT : SelMemoOK w H T) (i : Fin n) (u : KeyIndex) :
    SelMemoOK w H (T.put i u (topSelOf (w.user i) H u)) := by
  intro j u' o h
  by_cases hji : j = i ∧ u' = u
  · obtain ⟨rfl, rfl⟩ := hji
    rw [SelMemo.put_self] at h
    exact (Option.some.inj h).symm
  · rw [SelMemo.put_of_ne _ _ hji] at h
    exact hT j u' o h

/-- **A read signer returning the users' signatures and top selections**: from a memoized
selection that agrees with the function, the signer of user `i` returns `w`'s signature and the
top selection with certainty on the block. -/
def SignsN (w : QTableN n) (sgn : SignerN M n) : Prop :=
  ∀ i r h B, (∀ o, h = some o → o = topSelOf (w.user i) (overwrite W t).1 (topKeyOf r)) →
    ReadsTo t W m (sgn i r h B)
      ((w.user i).signature (overwrite W t).1 r,
        topSelOf (w.user i) (overwrite W t).1 (topKeyOf r))

/-- **The challenged adversary and its memo transform intertwine**: against `(overwrite W t).1`,
consistent with every user's table, the adversary against the challenger with the users' keys
and its memo transform against `challengeWithN M sgn` with a signer satisfying `SignsN`, from
every memo that agrees with the function. -/
theorem intertwines_muChallenged_memoFrom {S0 : Fin n → MasterSeed} {w : QTableN n}
    (hv : ∀ i, Consistent (S0 i) (w.user i) (overwrite W t).1) {sgn : SignerN M n}
    (hsgn : SignsN t W m w sgn) {C : QReg} {α : Type} {A : QReg}
    (x : IFreeM (MuP n) (QuantumComp₂.Leaf C α) A) (T : SelMemo n)
    (hT : SelMemoOK w (overwrite W t).1 T) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments
        (muChallenged xmssRom (fun i ↦ (w.user i).secretKey (S0 i)) x))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments
        ((memoFrom T x).substitute (challengeWithN M sgn))) := by
  induction x using IFreeM.inductionOn generalizing T with
  | pure _ y =>
    exact intertwines_run₂_of_run (R₁ := additiveOracleRuntime (overwrite W t).1)
      (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
      (intertwines_run_pure y)
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · refine intertwines_run₂_of_run (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
        (intertwines_run_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
          (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
          (Quantum.Qrom.Xmss.intertwines_liftH t W m
            (muChallenge xmssRom (fun i ↦ (w.user i).secretKey (S0 i)) A (.prim o))) fun p ↦ ?_)
      obtain ⟨u, b, hb⟩ := p
      subst hb
      exact intertwines_run_of_run₂ (ih b T hT)
    · refine intertwines_run₂_of_run (R₁ := additiveOracleRuntime (overwrite W t).1)
        (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
        (intertwines_run_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
          (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
          (Quantum.Qrom.Xmss.intertwines_liftH t W m
            (muChallenge xmssRom (fun i ↦ (w.user i).secretKey (S0 i)) A (.query .hash E ℓ)))
          fun p ↦ ?_)
      obtain ⟨u, b, hb⟩ := p
      subst hb
      exact intertwines_run_of_run₂ (ih b T hT)
    · rw [muChallenged_liftBind_sign, substitute_memoFrom_liftBind_sign, answerTree, signAtN]
      have hc := (Quantum.Qrom.Xmss.classicalOn_toQuantumAt_romImpl_pure
        (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
        QTable.not_signRead_inl _ (QTable.signReads_sign (hv i) r)).congr
        (congrArg pure (QTable.eval_sign (hv i) r)) rfl
      refine intertwines_act_bind_bind (A := A)
        (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
        (C := C) (b₀ := ((w.user i).signature (overwrite W t).1 r,
          topSelOf (w.user i) (overwrite W t).1 (topKeyOf r))) (SubInstrument.relabel ℓ) hc ?_ ?_
      · exact hsgn i r (T i (topKeyOf r)) _ fun o ho ↦ hT i _ o ho
      · exact ih _ _ (hT.put i (topKeyOf r))

/-- **The game and its reads intertwine**: against `(overwrite W t).1`, consistent with every
user's table, the multi-user game runs as `gameReadsWithN` from the users' public keys with a
signer satisfying `SignsN`. -/
theorem intertwines_muGame_readsN {S0 : Fin n → MasterSeed} {w : QTableN n}
    (hv : ∀ i, Consistent (S0 i) (w.user i) (overwrite W t).1) {sgn : SignerN M n}
    (hsgn : SignsN t W m w sgn) (valid : SignLog → Bool) (A : MuAdversary n) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt W m).amplifyLeft (QReg.of Unit))
      ((additiveOracleRuntime (overwrite W t).1).run₂ .instruments (muGame xmssRom valid S0 A))
      ((spongeFnReadRuntime HashOutput HashDomain t W m).run₂ .instruments
        (gameReadsWithN M sgn (fun i ↦ (w.user i).publicKey) valid A)) := by
  rw [muGame, run₂_bind_of_classicalOn_pure
    ((Quantum.Qrom.Xmss.classicalOn_toQuantumAt_romImpl (overwrite W t).1 _ _).congr
      (simulateQ_generateAll (fun _ ↦ rfl) n S0 w hv) rfl)]
  dsimp only
  refine intertwines_run₂_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
    (intertwines_muChallenged_memoFrom t W m hv hsgn _ _ (selMemoOK_empty w _)) fun run ↦ ?_
  exact intertwines_run₂_bind (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (V := hwAt W m)
    (Quantum.Qrom.Xmss.intertwines_readsProgram not_isHash_inl _ (isHash_verify _ _))
    fun _ ↦ intertwines_run₂_pure _

/-- **The game is its reads at a fixed function** consistent with every user's table. -/
theorem evalDistMap_muGame_eq_readsN {S0 : Fin n → MasterSeed} {w : QTableN n}
    (hv : ∀ i, Consistent (S0 i) (w.user i) (overwrite W t).1) {sgn : SignerN M n}
    (hsgn : SignsN t W m w sgn) (valid : SignLog → Bool) (A : MuAdversary n)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (additiveOracleRuntime (overwrite W t).1).evalDistMap .instruments
        (muGame xmssRom valid S0 A) ρ f =
      (spongeFnReadRuntime HashOutput HashDomain t W m).evalDistMap .instruments
        (gameReadsWithN M sgn (fun i ↦ (w.user i).publicKey) valid A) ρ f :=
  evalDistMap_eq_of_intertwines (R₁ := additiveOracleRuntime (overwrite W t).1)
    (R₂ := spongeFnReadRuntime HashOutput HashDomain t W m) (K := hwCol W m)
    (conjTranspose_hwCol_mul_self W m) (hwAt_basis W m)
    (intertwines_run_of_run₂ (intertwines_muGame_readsN t W m hv hsgn valid A)) ρ f

end intertwine

end Quantum.Qrom.Xmss.Multi

end
