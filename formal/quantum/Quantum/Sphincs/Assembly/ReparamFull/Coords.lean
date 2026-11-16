module

public import Quantum.Sphincs.Assembly.ReparamFull.HiFix
public import Quantum.Sphincs.Assembly.Reparam
public import Quantum.Sphincs.Hybrid.DigestStage
public import Quantum.Sphincs.Hybrid.SeedStage

@[expose] public section

/-!
# The composed reparametrization of leanSPHINCS's tables: the coordinates

The padded tables `FT` (an honest table with SchemeSplit's slots, the randomizer and digest stages'
coin slots, SeedStage's slots, Reparam's pad and the stream pad) are moved by a chain of
bijections (`stagesE`) and split into Reparam's table and the rest (`phiE`); Reparam's `fwd` and a
final bijection `psiE` give the public data `PP`, the hidden values `(s : HPos) → XD s` and the
never-revealed part `K` (`fullE`).

* **The stages**: DigestStage's `dSplit` (SchemeSplit's staged swap, the randomizer stage, the
  digest stage), then three fix-ups (`dHiE`, `rHiE`, `sHiE`: HiFix's `hiStageOn` at the digest
  stage's first labels, the randomizer stage's first labels and the `SK.seed`-keyed cells, which
  give back the bits of `h` from `256` on), the undoing of the digest stage's `k`- and
  `k'`-stages (`dUndo`: the template programs the `H_msg` paths with the public keys), SeedStage's
  `seedKStages` (`seedE`) and the exchange of the secrets' low bits with Reparam's pad at the
  secret positions (`secXE`).
* **The coordinates**: Reparam's table `((h, u), (PK.seed, π, k, k'))`; the public data `PP` is
  `fwd`'s `(h'', w)` with SchemeSplit's public slot bits; the hidden values (`hidOf`) are `fwd`'s
  at `.val`, the first `128` bits of the randomizer slots at `.rnd`, the first `256` bits of the
  digest slots at the root `.val rootPos` at `.dig`, the stream pad at `.str`; the never-revealed
  part `K` is `(SK.seed, SK.prf)`, SeedStage's slots, the coin slots' `k`- and `k'`-parts, the
  slots' other bits and the digest slots at the other roots (indexed by the offset from the root,
  `NZ`).
* `fullE_injOn`: `fullE` is injective where Reparam's table is good; `card_fullE`: the
  coordinates are as many as the padded tables.
-/

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer MasterSeed truncateHash)
open Quantum.Xmss (X Z out256 trunc128)
open Quantum.Xmss.Hybrid (CoinSlots IsFirst isFirst_inj capOf rateOf r0SlotEquiv r0SlotEquiv_fst)
open Quantum.Xmss.Assembly (fwd injOn_fwd XW)
open Quantum.Sphincs.Hybrid (DSt DTab DF PubSlots Secret SeedKS SkIdx seedKStages dSplit dCellP
  dLabCell dLabMsg dLabOrd DLab rCell rOrd pStageK pStageK' skCell)

namespace Quantum.Sphincs.Assembly

/-! ## The stages after the digest stage -/

section stages

/-- The digest stage's coordinates. -/
abbrev DS : Type := DSt Message DLab

/-- The digest stage's first blocks in the path-stage form. -/
abbrev dcP : PubSlots → DF Message → DLab → X :=
  dCellP dLabCell dLabMsg

/-- The data the digest fix keeps: `k`, `k'`, `π`, the public slots, the digest stage's `k`- and
`k'`-coins, the randomizer stage's slots and the secret. -/
abbrev DW : Type :=
  (X → Z) × (X → Z) × Equiv.Perm (X × Z) × PubSlots × (DLab → Z) × (DLab → Z) × DF Message

/-- The digest fix's view: `h` with the digest slots, and the rest. -/
def dView : DS ≃ ((Z → X) × (DLab → X)) × DW where
  toFun y := ((y.1.1.1.1.1, y.1.2.2.2),
    (y.1.1.1.1.2.1, y.1.1.1.1.2.2, y.1.1.1.2, y.1.1.2, y.1.2.1, y.1.2.2.1, y.2))
  invFun p := (((((p.1.1, p.2.1, p.2.2.1), p.2.2.2.1), p.2.2.2.2.1),
    (p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.1.2)), p.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The digest labels' first blocks from the kept data. -/
def dcW (w : DW) (a : DLab) : X :=
  dcP w.2.2.2.1 w.2.2.2.2.2.2 a

/-- The digest labels' capacities from the kept data (the path stages' `pCellH`). -/
def dPosW (w : DW) (_ : DLab → HashOutput) (a : DLab) : Z :=
  (w.2.2.1 (dcW w a, w.2.2.2.2.1 a)).2 + w.2.2.2.2.2.1 a

/-- The digest labels' rates from the kept data. -/
def dShW (w : DW) (_ : DLab → HashOutput) (a : DLab) : X :=
  (w.2.2.1 (dcW w a, w.2.2.2.2.1 a)).1

/-- The digest stage's first labels. -/
def dFW (w : DW) (lo : DLab → HashOutput) (a : DLab) : Prop :=
  IsFirst dLabOrd (dPosW w lo) a

theorem dFW_inj (w : DW) (lo : DLab → HashOutput) (a b : DLab) (ha : dFW w lo a)
    (hb : dFW w lo b) (h : dPosW w lo a = dPosW w lo b) : a = b :=
  isFirst_inj dLabOrd (dPosW w lo) a b ha hb h

/-- **The digest fix**: at the digest stage's first labels, the bits of `h` from `256` on are given
back (HiFix's `hiStageOn`). -/
noncomputable def dHiE : DS ≃ DS :=
  dView.trans ((hiStageOn dFW dPosW dShW dFW_inj).trans dView.symm)

/-- **The undoing of the digest stage's `k`- and `k'`-stages.** -/
noncomputable def dUndo : DS ≃ DS :=
  ((pStageK dcP).trans (pStageK' dcP)).symm

/-- The data the randomizer fix keeps: `k`, `k'`, `π`, the public slots, the digest stage's coin
slots, the randomizer stage's `k`- and `k'`-coins and the secret. -/
abbrev RW : Type :=
  (X → Z) × (X → Z) × Equiv.Perm (X × Z) × PubSlots × CoinSlots DLab × (Message → Z) ×
    (Message → Z) × Secret

/-- The randomizer fix's view: `h` with the randomizer slots, and the rest. -/
def rView : DS ≃ ((Z → X) × (Message → X)) × RW where
  toFun y := ((y.1.1.1.1.1, y.2.1.2.2),
    (y.1.1.1.1.2.1, y.1.1.1.1.2.2, y.1.1.1.2, y.1.1.2, y.1.2, y.2.1.1, y.2.1.2.1, y.2.2))
  invFun p := (((((p.1.1, p.2.1, p.2.2.1), p.2.2.2.1), p.2.2.2.2.1), p.2.2.2.2.2.1),
    ((p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.1.2), p.2.2.2.2.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The randomizer labels' first blocks from the kept data. -/
def rcW (w : RW) (M : Message) : X :=
  rCell M (trunc128 w.2.2.2.1.2.1) w.2.2.2.2.2.2.2.2

/-- The randomizer labels' capacities from the kept data (DigestStage's `dRCap`). -/
def rPosW (w : RW) (_ : Message → HashOutput) (M : Message) : Z :=
  (w.2.2.1 (rcW w M, w.2.2.2.2.2.1 M)).2 + w.2.2.2.2.2.2.1 M

/-- The randomizer labels' rates from the kept data. -/
def rShW (w : RW) (_ : Message → HashOutput) (M : Message) : X :=
  (w.2.2.1 (rcW w M, w.2.2.2.2.2.1 M)).1

/-- The randomizer stage's first labels. -/
def rFW (w : RW) (lo : Message → HashOutput) (M : Message) : Prop :=
  IsFirst rOrd (rPosW w lo) M

theorem rFW_inj (w : RW) (lo : Message → HashOutput) (a b : Message) (ha : rFW w lo a)
    (hb : rFW w lo b) (h : rPosW w lo a = rPosW w lo b) : a = b :=
  isFirst_inj rOrd (rPosW w lo) a b ha hb h

/-- **The randomizer fix**: at the randomizer stage's first labels, the bits of `h` from `256` on
are given back. -/
noncomputable def rHiE : DS ≃ DS :=
  rView.trans ((hiStageOn rFW rPosW rShW rFW_inj).trans rView.symm)

/-- The data the scheme fix keeps: `k`, `k'`, `π`, the coin slots and `SK.seed`. -/
abbrev SW : Type :=
  (X → Z) × (X → Z) × Equiv.Perm (X × Z) × CoinSlots DLab × CoinSlots Message × MasterSeed

/-- SchemeSplit's slots by index: slot `0` (`SK.prf` with its public bits), slot `1`, the secrets'
slots. -/
def skSlots (y : DS) : SkIdx → X
  | none => outSplit.symm (y.2.2.2, y.1.1.2.1)
  | some none => y.1.1.2.2.1
  | some (some d) => y.1.1.2.2.2 d

/-- The scheme fix's view: `h` with SchemeSplit's slots, and the rest. -/
def sView : DS ≃ ((Z → X) × (SkIdx → X)) × SW where
  toFun y := ((y.1.1.1.1.1, skSlots y),
    (y.1.1.1.1.2.1, y.1.1.1.1.2.2, y.1.1.1.2, y.1.2, y.2.1, y.2.2.1))
  invFun p := (((((p.1.1, p.2.1, p.2.2.1), p.2.2.2.1),
      ((outSplit (p.1.2 none)).2, p.1.2 (some none), fun d ↦ p.1.2 (some (some d)))),
      p.2.2.2.2.1), (p.2.2.2.2.2.1, (p.2.2.2.2.2.2, (outSplit (p.1.2 none)).1)))
  left_inv y := by
    obtain ⟨⟨⟨⟨t, π⟩, r, u₁, u₂⟩, dc⟩, rc, S, prf⟩ := y
    simp only [skSlots, Equiv.apply_symm_apply]
  right_inv p := by
    obtain ⟨⟨h, sl⟩, k, k', π, dc, rc, S⟩ := p
    refine Prod.ext (Prod.ext rfl (funext fun a ↦ ?_)) rfl
    rcases a with _ | _ | d
    · exact Equiv.symm_apply_apply outSplit (sl none)
    · rfl
    · rfl

/-- `PK.seed` from the slots' low parts. -/
def sParW (lo : SkIdx → HashOutput) : PublicParameter :=
  truncateHash (lo (some none))

/-- The `SK.seed`-keyed capacities (SchemeSplit's `posOf`). -/
def sPosW (w : SW) (lo : SkIdx → HashOutput) (a : SkIdx) : Z :=
  capOf w.1 w.2.1 w.2.2.1 (skCell (sParW lo) w.2.2.2.2.2 a)

/-- The `SK.seed`-keyed rates. -/
def sShW (w : SW) (lo : SkIdx → HashOutput) (a : SkIdx) : X :=
  rateOf w.1 w.2.2.1 (skCell (sParW lo) w.2.2.2.2.2 a)

/-- The scheme fix acts when the capacities are distinct. -/
def sFW (w : SW) (lo : SkIdx → HashOutput) (_ : SkIdx) : Prop :=
  Function.Injective (sPosW w lo)

theorem sFW_inj (w : SW) (lo : SkIdx → HashOutput) (a b : SkIdx) (ha : sFW w lo a)
    (_ : sFW w lo b) (h : sPosW w lo a = sPosW w lo b) : a = b :=
  ha h

/-- **The scheme fix**: at the `SK.seed`-keyed capacities, the bits of `h` from `256` on are given
back. -/
noncomputable def sHiE : DS ≃ DS :=
  sView.trans ((hiStageOn sFW sPosW sShW sFW_inj).trans sView.symm)

/-- **The table through the stages after the digest stage**: the digest fix, the undoing of the
digest stage's `k`- and `k'`-stages, the randomizer fix, the scheme fix. -/
noncomputable def dFull : DTab Message DLab ≃ DS :=
  (dSplit rCell rOrd dLabCell dLabMsg dLabOrd).trans (dHiE.trans (dUndo.trans (rHiE.trans sHiE)))

/-- SeedStage's view of the digest stage's coordinates with the seed slots. -/
def seedView : DS × SeedKS ≃ ((Hybrid.Pub × Secret) × SeedKS) × (CoinSlots DLab × CoinSlots Message)
    where
  toFun x := (((x.1.1.1, x.1.2.2), x.2), (x.1.1.2, x.1.2.1))
  invFun p := (((p.1.1.1, p.2.1), (p.2.2, p.1.1.2)), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **SeedStage's `k`- and `k'`-stages** on the digest stage's coordinates. -/
noncomputable def seedE : DS × SeedKS ≃ DS × SeedKS :=
  seedView.trans ((seedKStages.prodCongr (Equiv.refl _)).trans seedView.symm)

end stages

/-! ## The secrets' exchange with the pad -/

section secrets

/-- The position of a secret. -/
def secPos : KeygenDomain → ValPos
  | .oneTimeChain l τ e i => .chain l τ e i ⟨0, by decide⟩
  | .forsSecret idx κ s => .forsSecret idx κ s

/-- The secret at a position, if any. -/
def secOf : ValPos → Option KeygenDomain
  | .chain l τ e i j => if j.val = 0 then some (.oneTimeChain l τ e i) else none
  | .forsSecret idx κ s => some (.forsSecret idx κ s)
  | _ => none

theorem secOf_secPos (d : KeygenDomain) : secOf (secPos d) = some d := by
  cases d <;> rfl

theorem secPos_of_secOf {q : ValPos} {d : KeygenDomain} (h : secOf q = some d) : secPos d = q := by
  cases q with
  | chain l τ e i j =>
    by_cases hj : j.val = 0
    · have hd : some (KeygenDomain.oneTimeChain l τ e i) = some d := by
        rw [← h]
        exact (ite_eq_left hj).symm
      obtain rfl := Option.some_injective _ hd
      exact congrArg (ValPos.chain l τ e i) (Fin.ext hj.symm)
    · have hn : secOf (.chain l τ e i j) = none := ite_eq_right hj
      rw [hn] at h
      exact absurd h (by simp)
  | forsSecret idx κ s =>
    obtain rfl := Option.some_injective _ h
    rfl
  | tree => exact absurd h (by simp [secOf])
  | forsTree => exact absurd h (by simp [secOf])
  | forsKey => exact absurd h (by simp [secOf])

/-- A secret position is the position of a secret. -/
theorem secOf_of_secretPos {q : ValPos} (hq : SecretPos q) : ∃ d, secOf q = some d := by
  cases q with
  | chain l τ e i j => exact ⟨.oneTimeChain l τ e i, ite_eq_left hq.1⟩
  | forsSecret idx κ s => exact ⟨.forsSecret idx κ s, rfl⟩
  | tree => exact hq.elim
  | forsTree => exact hq.elim
  | forsKey => exact hq.elim

/-- The pad after the exchange: the secrets' slots' first `128` bits at the secret positions. -/
def secU (sl : KeygenDomain → X) (u : ValPos → Digest) (q : ValPos) : Digest :=
  match secOf q with
  | some d => trunc128 (sl d)
  | none => u q

theorem secU_of_some {sl : KeygenDomain → X} {u : ValPos → Digest} {q : ValPos}
    {d : KeygenDomain} (h : secOf q = some d) : secU sl u q = trunc128 (sl d) := by
  unfold secU
  rw [h]

theorem secU_of_none {sl : KeygenDomain → X} {u : ValPos → Digest} {q : ValPos}
    (h : secOf q = none) : secU sl u q = u q := by
  unfold secU
  rw [h]

theorem secU_secPos (sl : KeygenDomain → X) (u : ValPos → Digest) (d : KeygenDomain) :
    secU sl u (secPos d) = trunc128 (sl d) :=
  secU_of_some (secOf_secPos d)

/-- The exchange: the secrets' slots take the pad at the secret positions in their first `128`
bits, the pad takes the slots' first `128` bits there. -/
def secXF (p : (KeygenDomain → X) × (ValPos → Digest)) :
    (KeygenDomain → X) × (ValPos → Digest) :=
  (fun d ↦ r0SlotEquiv.symm (p.2 (secPos d), (r0SlotEquiv (p.1 d)).2), secU p.1 p.2)

theorem secXF_secXF (p : (KeygenDomain → X) × (ValPos → Digest)) : secXF (secXF p) = p := by
  obtain ⟨sl, u⟩ := p
  refine Prod.ext (funext fun d ↦ ?_) (funext fun q ↦ ?_)
  · show r0SlotEquiv.symm (secU sl u (secPos d),
      (r0SlotEquiv (r0SlotEquiv.symm (u (secPos d), (r0SlotEquiv (sl d)).2))).2) = sl d
    rw [secU_secPos, Equiv.apply_symm_apply, ← r0SlotEquiv_fst, Prod.mk.eta,
      Equiv.symm_apply_apply]
  · show secU (fun d ↦ r0SlotEquiv.symm (u (secPos d), (r0SlotEquiv (sl d)).2)) (secU sl u) q = u q
    cases hq : secOf q with
    | none => rw [secU_of_none hq, secU_of_none hq]
    | some d =>
      rw [secU_of_some hq, ← r0SlotEquiv_fst, Equiv.apply_symm_apply]
      exact congrArg u (secPos_of_secOf hq)

/-- **The secrets' exchange**, an involution. -/
def secX : (KeygenDomain → X) × (ValPos → Digest) ≃ (KeygenDomain → X) × (ValPos → Digest) where
  toFun := secXF
  invFun := secXF
  left_inv := secXF_secXF
  right_inv := secXF_secXF

/-- The rest beside the secrets' slots and the pad. -/
abbrev SXR : Type :=
  ((((SpongeKeys X Z × Equiv.Perm (X × Z)) × ((Fin 832 → ZMod 2) × X)) × CoinSlots DLab) ×
    DF Message) × SeedKS

/-- The view of the secrets' slots and the pad. -/
def secView : (DS × SeedKS) × (ValPos → Digest) ≃
    ((KeygenDomain → X) × (ValPos → Digest)) × SXR where
  toFun x := ((x.1.1.1.1.2.2.2, x.2),
    ((((x.1.1.1.1.1, (x.1.1.1.1.2.1, x.1.1.1.1.2.2.1)), x.1.1.1.2), x.1.1.2), x.1.2))
  invFun p := (((((p.2.1.1.1.1, (p.2.1.1.1.2.1, p.2.1.1.1.2.2, p.1.1)), p.2.1.1.2), p.2.1.2),
    p.2.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The secrets' exchange** on the coordinates with the pad. -/
def secXE : (DS × SeedKS) × (ValPos → Digest) ≃ (DS × SeedKS) × (ValPos → Digest) :=
  secView.trans ((secX.prodCongr (Equiv.refl _)).trans secView.symm)

end secrets

/-! ## The padded tables and their coordinates -/

section coords

/-- The stream pad. -/
abbrev StrPad : Type := Fin signatureLimit → DigestCall → HashOutput

/-- **The padded tables**: the digest stage's tables with SeedStage's slots, Reparam's pad and the
stream pad. -/
abbrev FT : Type := ((DTab Message DLab × SeedKS) × (ValPos → Digest)) × StrPad

/-- **The stages**: `dFull`, SeedStage's stages, the secrets' exchange. -/
noncomputable def stagesE : FT ≃ ((DS × SeedKS) × (ValPos → Digest)) × StrPad :=
  ((((dFull.prodCongr (Equiv.refl SeedKS)).trans seedE).prodCongr (Equiv.refl _)).trans
    secXE).prodCongr (Equiv.refl _)

/-- Reparam's tables. -/
abbrev RTabS : Type := ((Z → X) × (ValPos → Digest)) × XW

/-- SchemeSplit's public slot bits: those of slot `0` beyond `SK.prf`, those of slot `1` beyond
`PK.seed`, the secrets' slots. -/
abbrev PubR : Type := (Fin 832 → ZMod 2) × (Fin 960 → ZMod 2) × (KeygenDomain → X)

/-- **The rest** beside Reparam's table: the public slot bits, the coin slots, the secret,
SeedStage's slots and the stream pad. -/
abbrev RestF : Type :=
  PubR × CoinSlots DLab × CoinSlots Message × Secret × SeedKS × StrPad

/-- The coordinates after the stages as Reparam's table and the rest. -/
def tabR : ((DS × SeedKS) × (ValPos → Digest)) × StrPad ≃ RTabS × RestF where
  toFun z := (((z.1.1.1.1.1.1.1.1, z.1.2),
      ((r0SlotEquiv z.1.1.1.1.1.2.2.1).1, z.1.1.1.1.1.1.2, z.1.1.1.1.1.1.1.2.1,
        z.1.1.1.1.1.1.1.2.2)),
    ((z.1.1.1.1.1.2.1, (r0SlotEquiv z.1.1.1.1.1.2.2.1).2, z.1.1.1.1.1.2.2.2), z.1.1.1.1.2,
      z.1.1.1.2.1, z.1.1.1.2.2, z.1.1.2, z.2))
  invFun x := ((((((((x.1.1.1, x.1.2.2.2.1, x.1.2.2.2.2), x.1.2.2.1),
      (x.2.1.1, r0SlotEquiv.symm (x.1.2.1, x.2.1.2.1), x.2.1.2.2)), x.2.2.1),
      (x.2.2.2.1, x.2.2.2.2.1)), x.2.2.2.2.2.1), x.1.1.2), x.2.2.2.2.2.2)
  left_inv z := by
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h, k, k'⟩, π⟩, r, u₁, u₂⟩, dc⟩, rc, s⟩, sk⟩, u⟩, sp⟩ := z
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv x := by
    obtain ⟨⟨⟨h, u⟩, P, π, k, k'⟩, ⟨r, ρ, u₂⟩, dc, rc, s, sk, sp⟩ := x
    simp only [Equiv.apply_symm_apply]

/-- **The padded tables as Reparam's table and the rest.** -/
noncomputable def phiE : FT ≃ RTabS × RestF :=
  stagesE.trans tabR

/-- The digest offsets other than `0`. -/
abbrev NZ : Type := {δ : Digest // δ ≠ 0}

/-- **The public data**: Reparam's public coordinates `(h'', w)` and SchemeSplit's public slot
bits. -/
abbrev PP : Type := ((Z → X) × XW) × PubR

/-- **The never-revealed part**: `(SK.seed, SK.prf)`, SeedStage's slots, the randomizer coin
slots' `k`- and `k'`-parts and the bits of its slots beyond `128`, the digest coin slots' `k`- and
`k'`-parts, the bits of its slots beyond `256`, and its slots' first `256` bits at the roots other
than the hidden root (by their offset). -/
abbrev KK : Type :=
  Secret × SeedKS × (Message → Z) × (Message → Z) × (Message → Fin 960 → ZMod 2) ×
    (DLab → Z) × (DLab → Z) × (DLab → Fin 832 → ZMod 2) × (NZ → Message × DigestCall → HashOutput)

/-- The hidden values: Reparam's at the positions, the randomizer slots' first `128` bits, the
digest slots' first `256` bits at the root (the value at `rootPos`), the stream pad. -/
def hidOf (vals : ValPos → Digest) (rhc : Message → X) (dhc : DLab → X) (sp : StrPad) :
    (s : HPos) → XD s
  | .val q => vals q
  | .rnd M => trunc128 (rhc M)
  | .dig M i => out256 (dhc (vals rootPos, M, i))
  | .str j i => sp j i
  | .asg _ _ => ()

/-- The root among the hidden values. -/
def rootV (v : (s : HPos) → XD s) : Digest :=
  v (.val rootPos)

/-- The digest slots from the root, the hidden values at `.dig` and the never-revealed part. -/
def dhcOf (root : Digest) (dig : Message × DigestCall → HashOutput)
    (low : NZ → Message × DigestCall → HashOutput) (hi : DLab → Fin 832 → ZMod 2) (a : DLab) : X :=
  outSplit.symm ((if h : a.1 ^^^ root = 0 then dig (a.2.1, a.2.2) else low ⟨a.1 ^^^ root, h⟩
    (a.2.1, a.2.2)), hi a)

theorem xor_xor_cancel (a b : Digest) : a ^^^ b ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem eq_of_xor_eq_zero {a b : Digest} (h : a ^^^ b = 0) : a = b := by
  have := congrArg (· ^^^ b) h
  simpa [xor_xor_cancel] using this

theorem dhcOf_out256 (root : Digest) (dhc : DLab → X) :
    dhcOf root (fun c ↦ out256 (dhc (root, c.1, c.2)))
      (fun δ c ↦ out256 (dhc (δ.1 ^^^ root, c.1, c.2))) (fun a ↦ (outSplit (dhc a)).2) = dhc := by
  funext a
  obtain ⟨r, M, i⟩ := a
  unfold dhcOf
  split_ifs with h
  · obtain rfl := eq_of_xor_eq_zero h
    show outSplit.symm (out256 (dhc (r, M, i)), (outSplit (dhc (r, M, i))).2) = _
    rw [← outSplit_fst, Prod.mk.eta, Equiv.symm_apply_apply]
  · show outSplit.symm (out256 (dhc (r ^^^ root ^^^ root, M, i)), _) = _
    rw [xor_xor_cancel, ← outSplit_fst, Prod.mk.eta, Equiv.symm_apply_apply]

/-- **The final coordinates** from Reparam's public coordinates, its hidden values and the rest. -/
def psiF (x : (((Z → X) × XW) × (ValPos → Digest)) × RestF) : PP × (((s : HPos) → XD s) × KK) :=
  ((x.1.1, x.2.1),
    (hidOf x.1.2 x.2.2.2.1.2.2 x.2.2.1.2.2 x.2.2.2.2.2.2,
      (x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.1.1, x.2.2.2.1.2.1,
        fun M ↦ (r0SlotEquiv (x.2.2.2.1.2.2 M)).2, x.2.2.1.1, x.2.2.1.2.1,
        fun a ↦ (outSplit (x.2.2.1.2.2 a)).2,
        fun δ c ↦ out256 (x.2.2.1.2.2 (δ.1 ^^^ x.1.2 rootPos, c.1, c.2)))))

/-- The inverse of `psiF`. -/
def psiB (y : PP × (((s : HPos) → XD s) × KK)) : (((Z → X) × XW) × (ValPos → Digest)) × RestF :=
  ((y.1.1, fun q ↦ y.2.1 (.val q)),
    (y.1.2, (y.2.2.2.2.2.2.2.1, y.2.2.2.2.2.2.2.2.1,
        dhcOf (y.2.1 (.val rootPos)) (fun c ↦ y.2.1 (.dig c.1 c.2)) y.2.2.2.2.2.2.2.2.2.2
          y.2.2.2.2.2.2.2.2.2.1),
      (y.2.2.2.2.1, y.2.2.2.2.2.1, fun M ↦ r0SlotEquiv.symm (y.2.1 (.rnd M), y.2.2.2.2.2.2.1 M)),
      y.2.2.1, y.2.2.2.1, fun j i ↦ y.2.1 (.str j i)))

theorem psiB_psiF (x : (((Z → X) × XW) × (ValPos → Digest)) × RestF) : psiB (psiF x) = x := by
  obtain ⟨⟨hw, vals⟩, pr, ⟨dk, dk', dhc⟩, ⟨rk, rk', rhc⟩, s, sk, sp⟩ := x
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext (Prod.ext rfl (Prod.ext rfl ?_))
    (Prod.ext (Prod.ext rfl (Prod.ext rfl ?_)) rfl)))
  · exact dhcOf_out256 (vals rootPos) dhc
  · funext M
    show r0SlotEquiv.symm (trunc128 (rhc M), (r0SlotEquiv (rhc M)).2) = rhc M
    rw [← r0SlotEquiv_fst, Prod.mk.eta, Equiv.symm_apply_apply]

theorem psiF_psiB (y : PP × (((s : HPos) → XD s) × KK)) : psiF (psiB y) = y := by
  obtain ⟨p, v, s, sk, rk, rk', rhi, dk, dk', dhi, low⟩ := y
  have hd : ∀ a, outSplit (dhcOf (v (.val rootPos)) (fun c ↦ v (.dig c.1 c.2)) low dhi a) =
      ((if h : a.1 ^^^ rootV v = 0 then v (.dig a.2.1 a.2.2)
        else low ⟨a.1 ^^^ rootV v, h⟩ (a.2.1, a.2.2)), dhi a) := fun a ↦
    Equiv.apply_symm_apply _ _

  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext s'
    cases s' with
    | val q => rfl
    | rnd M =>
      show trunc128 (r0SlotEquiv.symm (v (.rnd M), rhi M)) = v (.rnd M)
      rw [← r0SlotEquiv_fst, Equiv.apply_symm_apply]
    | dig M i =>
      show out256 (dhcOf (v (.val rootPos)) (fun c ↦ v (.dig c.1 c.2)) low dhi
        (v (.val rootPos), M, i)) = v (.dig M i)
      rw [← outSplit_fst, hd]
      exact dite_eq_left (BitVec.xor_self (x := rootV v))
    | str j i => rfl
    | asg M j => rfl
  · refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl
      (Prod.ext rfl (Prod.ext ?_ ?_)))))))
    · funext M
      show (r0SlotEquiv (r0SlotEquiv.symm (v (.rnd M), rhi M))).2 = rhi M
      rw [Equiv.apply_symm_apply]
    · funext a
      show (outSplit (dhcOf (v (.val rootPos)) (fun c ↦ v (.dig c.1 c.2)) low dhi a)).2 = dhi a
      rw [hd]
    · funext δ c
      show out256 (dhcOf (v (.val rootPos)) (fun c ↦ v (.dig c.1 c.2)) low dhi
        (δ.1 ^^^ rootV v, c.1, c.2)) = low δ c
      rw [← outSplit_fst, hd]
      have hne : δ.1 ^^^ rootV v ^^^ rootV v ≠ 0 := by
        rw [xor_xor_cancel]
        exact δ.2
      dsimp only
      have e : (⟨δ.1 ^^^ rootV v ^^^ rootV v, hne⟩ : NZ) = δ :=
        Subtype.ext (xor_xor_cancel δ.1 (rootV v))
      refine (dite_eq_right hne).trans ?_
      rw [e]

/-- **The final coordinates** as a bijection. -/
def psiE : (((Z → X) × XW) × (ValPos → Digest)) × RestF ≃ PP × (((s : HPos) → XD s) × KK) where
  toFun := psiF
  invFun := psiB
  left_inv := psiB_psiF
  right_inv := psiF_psiB

/-- **The composed reparametrization**: the stages, Reparam's `fwd` on Reparam's table, the final
coordinates. -/
noncomputable def fullE (t : FT) : PP × (((s : HPos) → XD s) × KK) :=
  psiE ((fwd sphFix sO (phiE t).1, (phiE t).2))

/-- The template's public data of the public coordinates. -/
def pubP (p : PP) : Pub :=
  sPub p.1.2 p.1.1

/-- **The reparametrization is injective where Reparam's table is good.** -/
theorem fullE_injOn : Set.InjOn fullE {t | XGood (phiE t).1} := by
  intro t₁ h₁ t₂ h₂ he
  have h := psiE.injective he
  have hθ := injOn_fwd sO_consistent (good_of_xGood h₁) (good_of_xGood h₂) (Prod.mk.inj h).1
  exact phiE.injective (Prod.ext hθ (Prod.mk.inj h).2)

/-- Reparam's public coordinates and hidden values as Reparam's tables. -/
def rtabS : ((Z → X) × XW) × (ValPos → Digest) ≃ RTabS where
  toFun y := ((y.1.1, y.2), y.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The coordinates are the padded tables, up to a bijection.** -/
noncomputable def coordEquiv : PP × (((s : HPos) → XD s) × KK) ≃ FT :=
  psiE.symm.trans ((rtabS.prodCongr (Equiv.refl RestF)).trans phiE.symm)

end coords

end Quantum.Sphincs.Assembly

end
