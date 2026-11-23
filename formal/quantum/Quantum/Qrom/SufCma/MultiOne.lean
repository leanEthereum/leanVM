module

public import Quantum.Qrom.SufCma.MultiGame

@[expose] public section

/-!
# One user: the multi-user game is the single-user game

For `n = 1` and a transcript validity implied by the winning condition, the multi-user SUF-CMA game
is the single-user one: the port `.sign 0 r` is the port `.sign r`, the keys of the only user are
the single-user keys, the forged user is user `0`, and user `0`'s transcript is the whole
transcript.

* `toOneUser f x`, `ofOneUser f x`: relabel the ports of a program between the single-user
  signature and the multi-user signature of one user, mapping the leaves by `f`.
* `muOfSingle A`, `singleOfMu A`: the adversaries so relabelled; `singleOfMu (muOfSingle A) = A`.

## Main statements

* `muGame_one`: the multi-user game of an adversary against one user is the single-user game of
  `singleOfMu A`.
* `muWinProb_one`: so are the winning probabilities.
* `muQuantumStronglyUnforgeable_one_iff`: multi-user SUF-CMA with one user, per-user and total
  limits `limit`, is single-user SUF-CMA with the limit `limit`.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

namespace Quantum.Qrom.SufCma.Multi

open Common HashSig

variable {PK Req Resp F : Type}

/-! ## Relabelling the ports -/

/-- **A single-user program as a program against one user**: the same commands, the port
`.sign r` as `.sign 0 r`, the leaves mapped by `f`. -/
def toOneUser {X Y : QReg → Type} (f : ∀ u, X u → Y u) :
    {A : QReg} →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SufCma.advSpec Req Resp)) X A →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (muAdvSpec 1 Req Resp)) Y A
  | _, .pure x => .pure (f _ x)
  | _, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ toOneUser f (next b)
  | _, .liftBind (.query .hash E ℓ) next =>
      .liftBind (.query .hash E ℓ) fun b ↦ toOneUser f (next b)
  | _, .liftBind (.query (.sign r) E ℓ) next =>
      .liftBind (.query (.sign 0 r) E ℓ) fun b ↦ toOneUser f (next b)

/-- **A program against one user as a single-user program**: the same commands, the port
`.sign i r` as `.sign r`, the leaves mapped by `f`. -/
def ofOneUser {X Y : QReg → Type} (f : ∀ u, X u → Y u) :
    {A : QReg} →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (muAdvSpec 1 Req Resp)) X A →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SufCma.advSpec Req Resp)) Y A
  | _, .pure x => .pure (f _ x)
  | _, .liftBind (.prim o) next => .liftBind (.prim o) fun b ↦ ofOneUser f (next b)
  | _, .liftBind (.query .hash E ℓ) next =>
      .liftBind (.query .hash E ℓ) fun b ↦ ofOneUser f (next b)
  | _, .liftBind (.query (.sign _ r) E ℓ) next =>
      .liftBind (.query (.sign r) E ℓ) fun b ↦ ofOneUser f (next b)

/-- Relabelling there and back, with leaf maps that cancel, is the identity. -/
theorem ofOneUser_toOneUser {X Y : QReg → Type} {f : ∀ u, X u → Y u} {g : ∀ u, Y u → X u}
    (hfg : ∀ u x, g u (f u x) = x) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SufCma.advSpec Req Resp))
      X A) :
    ofOneUser g (toOneUser f x) = x := by
  induction x using IFreeM.inductionOn with
  | pure _ v => exact congrArg IFreeM.pure (hfg _ v)
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | r, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind _) (funext ih)
    · exact congrArg (IFreeM.liftBind _) (funext ih)
    · exact congrArg (IFreeM.liftBind _) (funext ih)

/-- Relabelling to one user keeps a charge bound when the charges of the ports agree. -/
theorem isChargeBound_toOneUser {X Y : QReg → Type} (f : ∀ u, X u → Y u)
    {c : SufCma.AdvPort Req → ℕ} {c' : MuPort 1 Req → ℕ} (hh : c' .hash = c .hash)
    (hs : ∀ r, c' (.sign 0 r) = c (.sign r)) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SufCma.advSpec Req Resp))
      X A) {m : ℕ} (h : IFreeM.IsChargeBound x (SufCma.cmdCharge c) m) :
    IFreeM.IsChargeBound (toOneUser f x) (cmdCharge c') m := by
  induction x using IFreeM.inductionOn generalizing m with
  | pure _ _ => trivial
  | liftBind A c₀ next ih =>
    rcases c₀ with o | ⟨_ | r, E, ℓ⟩
    · exact ⟨h.1, fun b ↦ ih b (h.2 b)⟩
    · refine ⟨?_, fun b ↦ ?_⟩
      · show c' .hash ≤ m
        rw [hh]
        exact h.1
      · show IFreeM.IsChargeBound _ _ (m - c' .hash)
        rw [hh]
        exact ih b (h.2 b)
    · refine ⟨?_, fun b ↦ ?_⟩
      · show c' (.sign 0 r) ≤ m
        rw [hs]
        exact h.1
      · show IFreeM.IsChargeBound _ _ (m - c' (.sign 0 r))
        rw [hs]
        exact ih b (h.2 b)

/-- Relabelling to a single user keeps a charge bound when the charges of the ports agree. -/
theorem isChargeBound_ofOneUser {X Y : QReg → Type} (f : ∀ u, X u → Y u)
    {c : SufCma.AdvPort Req → ℕ} {c' : MuPort 1 Req → ℕ} (hh : c .hash = c' .hash)
    (hs : ∀ i r, c (.sign r) = c' (.sign i r)) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (muAdvSpec 1 Req Resp)) X A)
    {m : ℕ} (h : IFreeM.IsChargeBound x (cmdCharge c') m) :
    IFreeM.IsChargeBound (ofOneUser f x) (SufCma.cmdCharge c) m := by
  induction x using IFreeM.inductionOn generalizing m with
  | pure _ _ => trivial
  | liftBind A c₀ next ih =>
    rcases c₀ with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · exact ⟨h.1, fun b ↦ ih b (h.2 b)⟩
    · refine ⟨?_, fun b ↦ ?_⟩
      · show c .hash ≤ m
        rw [hh]
        exact h.1
      · show IFreeM.IsChargeBound _ _ (m - c .hash)
        rw [hh]
        exact ih b (h.2 b)
    · refine ⟨?_, fun b ↦ ?_⟩
      · show c (.sign r) ≤ m
        rw [hs i]
        exact h.1
      · show IFreeM.IsChargeBound _ _ (m - c (.sign r))
        rw [hs i]
        exact ih b (h.2 b)

/-- A single-user adversary as an adversary against one user, forging for user `0`. -/
def muOfSingle (A : SufCma.Adversary PK Req Resp F) : MuAdversary 1 PK Req Resp F :=
  fun pks ↦ toOneUser (fun _ l ↦ ⟨l.1, ((0 : Fin 1), l.2)⟩) (A (pks 0))

/-- An adversary against one user as a single-user adversary. -/
def singleOfMu (A : MuAdversary 1 PK Req Resp F) : SufCma.Adversary PK Req Resp F :=
  fun pk ↦ ofOneUser (fun _ l ↦ ⟨l.1, l.2.2⟩) (A fun _ ↦ pk)

theorem singleOfMu_muOfSingle (A : SufCma.Adversary PK Req Resp F) :
    singleOfMu (muOfSingle A) = A :=
  funext fun pk ↦ ofOneUser_toOneUser (fun _ _ ↦ rfl) (A pk)

/-! ## The challenged programs -/

variable {Seed SK : Type} (sch : SchemeOver RomOracles Seed PK SK Req Resp F)
  (valid : SignLog Req Resp → Bool)

/-- **The challenged program against one user is the single-user one**: with continuations that
agree on user `0`'s transcript and on the values mapped by `f`, the programs with their
transcripts, challenged and continued, are equal. -/
theorem muChallenged_muLogSigns_bind (sk : SK) {B C : QReg} {α α' β : Type} (f : α → α')
    (k : α × MuSignLog 1 Req Resp → QComp romSpec B C β)
    (k' : α' × SignLog Req Resp → QComp romSpec B C β)
    (hk : ∀ a log, k (a, log) = k' (f a, log.user 0)) {A : QReg}
    (x : QComp (muAdvSpec 1 Req Resp) A B α) (log : MuSignLog 1 Req Resp) :
    (muChallenged sch (fun _ ↦ sk) (muLogSigns (X := QuantumComp₂.Leaf B α)
        (Y := QuantumComp₂.Leaf B (α × MuSignLog 1 Req Resp))
        (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x log)).bind k =
      (SufCma.challenged sch sk (SufCma.logSigns (X := QuantumComp₂.Leaf B α')
        (Y := QuantumComp₂.Leaf B (α' × SignLog Req Resp)) (fun _ l log ↦ ⟨l.1, (l.2, log)⟩)
        (ofOneUser (X := QuantumComp₂.Leaf B α) (Y := QuantumComp₂.Leaf B α')
          (fun _ l ↦ ⟨l.1, f l.2⟩) x) (log.user 0))).bind k' := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure _ v =>
    obtain ⟨rfl, a⟩ := v
    exact hk a log
  | liftBind A c next ih =>
    simp only [muChallenged, SufCma.challenged, QuantumComp₂.bind, FreeM₂.bind] at ih ⊢
    rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · simp only [muLogSigns, SufCma.logSigns, ofOneUser]
      refine (IFreeM.bind_assoc _ _ _).trans (Eq.trans ?_ (IFreeM.bind_assoc _ _ _).symm)
      refine congrArg (IFreeM.bind _) (funext fun u ↦ funext fun ans ↦ ?_)
      obtain ⟨b, h⟩ := ans
      subst h
      exact ih b log
    · simp only [muLogSigns, SufCma.logSigns, ofOneUser]
      refine (IFreeM.bind_assoc _ _ _).trans (Eq.trans ?_ (IFreeM.bind_assoc _ _ _).symm)
      refine congrArg (IFreeM.bind _) (funext fun u ↦ funext fun ans ↦ ?_)
      obtain ⟨b, h⟩ := ans
      subst h
      exact ih b log
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      simp only [muLogSigns, SufCma.logSigns, ofOneUser]
      refine (IFreeM.bind_assoc _ _ _).trans (Eq.trans ?_ (IFreeM.bind_assoc _ _ _).symm)
      refine congrArg (IFreeM.bind _) (funext fun u ↦ funext fun ans ↦ ?_)
      obtain ⟨b, h⟩ := ans
      subst h
      have hu : MuSignLog.user (log ++ [⟨(0, r), b.down⟩]) 0 = log.user 0 ++ [⟨r, b.down⟩] := by
        rw [MuSignLog.user_append_singleton, ite_eq_left rfl]
      have hb := ih b (log ++ [⟨(0, r), b.down⟩])
      rw [hu] at hb
      exact hb

/-! ## The game and the winning probability -/

/-- Key generation of one user is the single-user key generation. -/
theorem generateAll_one (S0 : Fin 1 → Seed) :
    generateAll sch 1 S0 =
      (fun k ↦ (Fin.cons k Fin.elim0 : Fin 1 → PK × SK)) <$> sch.generateKeys (S0 0) := by
  simp only [generateAll, pure_bind, map_eq_bind_pure_comp, Function.comp_def]

/-- The only user's keys. -/
theorem cons_elim0_apply (k : PK × SK) (i : Fin 1) :
    (Fin.cons k Fin.elim0 : Fin 1 → PK × SK) i = k := by
  rw [Fin.fin_one_eq_zero i]
  rfl

/-- **One user: the multi-user game is the single-user game** of the relabelled adversary, for a
validity implied by the winning condition. -/
theorem muGame_one (hvalid : ∀ log f, sch.winningCondition log f = true → valid log = true)
    (S0 : Fin 1 → Seed) (A : MuAdversary 1 PK Req Resp F) :
    muGame sch valid S0 A = SufCma.game sch (S0 0) (singleOfMu A) := by
  unfold muGame SufCma.game
  rw [generateAll_one, map_eq_bind_pure_comp, toQuantumAt_romImpl_bind, QuantumComp₂.bind_assoc]
  refine congrArg (QuantumComp₂.bind _) (funext fun keys ↦ ?_)
  simp only [Function.comp_apply, toQuantumAt_pure, QuantumComp₂.pure_bind, cons_elim0_apply]
  refine muChallenged_muLogSigns_bind sch keys.2 Prod.snd _ _ (fun a log ↦ ?_) _ []
  dsimp only
  refine congrArg (QuantumComp₂.bind _) (funext fun verified ↦ ?_)
  have h0 : a.1 = 0 := Subsingleton.elim _ _
  rw [h0]
  congr 1
  cases hw : sch.winningCondition (log.user 0) a.2
  · rfl
  · have hv : log.allValid valid = true := by
      refine decide_eq_true fun j ↦ ?_
      rw [Fin.fin_one_eq_zero j]
      exact hvalid _ _ hw
    rw [hv]
    rfl

/-- **One user: the multi-user winning probability is the single-user one** of the relabelled
adversary. -/
theorem muWinProb_one [Fintype Seed]
    (hvalid : ∀ log f, sch.winningCondition log f = true → valid log = true)
    (A : MuAdversary 1 PK Req Resp F) :
    muWinProb sch valid 1 A = SufCma.winProb sch (singleOfMu A) := by
  unfold muWinProb SufCma.winProb
  simp only [Fintype.prod_unique, Fin.default_eq_zero, muGame_one sch valid hvalid]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) Seed) _ _ fun _ ↦ rfl

/-- **Multi-user SUF-CMA with one user is single-user SUF-CMA**, for per-user and total limits
`limit` and a validity implied by the winning condition. -/
theorem muQuantumStronglyUnforgeable_one_iff [Fintype Seed]
    (hvalid : ∀ log f, sch.winningCondition log f = true → valid log = true)
    {limit : ℕ} {bound : ℕ → ℝ≥0∞} :
    MuQuantumStronglyUnforgeable sch valid 1 limit limit bound ↔
      SufCma.QuantumStronglyUnforgeable sch limit bound := by
  constructor
  · intro h q A hhash hsign
    rw [← singleOfMu_muOfSingle A, ← muWinProb_one sch valid hvalid]
    refine h q _ (fun pks ↦ ?_) (fun pks i ↦ ?_) (fun pks ↦ ?_)
    · exact isChargeBound_toOneUser _ rfl (fun _ ↦ rfl) _ (hhash _)
    · refine isChargeBound_toOneUser _ rfl (fun _ ↦ ?_) _ (hsign _)
      rw [Fin.fin_one_eq_zero i]
      rfl
    · exact isChargeBound_toOneUser _ rfl (fun _ ↦ rfl) _ (hsign _)
  · intro h q A hhash hsign _
    rw [muWinProb_one sch valid hvalid]
    refine h q _ (fun pk ↦ ?_) (fun pk ↦ ?_)
    · exact isChargeBound_ofOneUser _ rfl (fun _ _ ↦ rfl) _ (hhash _)
    · refine isChargeBound_ofOneUser _ rfl (fun i _ ↦ ?_) _ (hsign _ 0)
      rw [Fin.fin_one_eq_zero i]
      rfl

end Quantum.Qrom.SufCma.Multi

end
