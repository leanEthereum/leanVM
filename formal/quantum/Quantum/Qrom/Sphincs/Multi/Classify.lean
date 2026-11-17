module

public import Quantum.Qrom.Sphincs.Multi.Events
public import Quantum.Qrom.Sphincs.Classify

@[expose] public section

/-!
# leanSPHINCS for `n` users in the random-oracle model: a win is in the event

`win_imp_badQP` strengthens the single-user `win_imp_badQ`: the event `BadQP pk hon S` is `BadQ`
with the Cov target restricted to the cells carrying `pk`'s `PK.seed` (`covTgtP`), and the
hardwired call-0 `H_msg` cells constrained by `HwDigestsP` are those carrying the table's
`PK.seed` (other users' digest cells may be hardwired too). The walks meet the honest table
through the single-user meet lemmas at `S = ⊥` (no Cov target), since
`BadQ pk hon ⊥ ⊆ BadQP pk hon S` (`badQ_bot_subset_badQP`); the forged call-0 `H_msg` cell is
hashed under `pk`, so the final Cov hit is prefixed.

`mem_badQN_of_badQP`: a hit of user `i`'s prefixed event on the projection `projU i s` (the
register with `i`'s memory; same union view, `unionH_projU`) is a hit of `BadQN` when the
`PK.seed`s are distinct and the honest cells sit at `PK.seed`-carrying slots (`PrefixedSlot`):
the witness is owned by `i` (`ownerS_of_slotOf`, `ownerS_eq_some`). `win_imp_badQN` assembles
both at the users' honest tables (`honCellN`).
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (layerSignatures)
open Quantum.Sphincs (Slot Key Disclosures Covered)
open Quantum.Qrom.Xmss (honestEval)
open Common.SufCma (SignerReturnedForgery)

namespace Quantum.Qrom.Sphincs.Multi

open Quantum Quantum.Sponge

attribute [local irreducible] sphincsRom

/-! ## The single-user event with prefixed Cov targets -/

/-- **The Cov targets of the cells carrying `pk`'s `PK.seed`.** -/
def covTgtP (pk : PublicKey) (S : Disclosures) (W : Hw PairOut Qrom.HashDomain) (m : SelMem)
    (x : Qrom.HashDomain) : Set PairOut :=
  {ω | ω ∈ covTgt S W m x ∧ prefixS x = some pk.publicSeed}

/-- **The leanSPHINCS targets with prefixed Cov targets.** -/
def sphTgtQP (pk : PublicKey) (hon : HonestCells) (S : Disclosures)
    (W : Hw PairOut Qrom.HashDomain) (m : SelMem) (x : Qrom.HashDomain) : Set PairOut :=
  {ω | ω ∈ structTgtQ pk hon W m x ∨ ω ∈ covTgtP pk S W m x}

/-- **The single-user event with prefixed Cov targets.** -/
abbrev BadQP (pk : PublicKey) (hon : HonestCells) (S : Disclosures) :
    Set (RomReg Qrom.HashDomain PairOut SelMem) :=
  CellTargetBad (sphTgtQP pk hon S)

section Prefixed

variable {pk : PublicKey} {hon : HonestCells} {S : Disclosures}
  {s : RomReg Qrom.HashDomain PairOut SelMem}

theorem mem_covTgtP {W : Hw PairOut Qrom.HashDomain} {m : SelMem} {x : Qrom.HashDomain}
    {ω : PairOut} :
    ω ∈ covTgtP pk S W m x ↔ ω ∈ covTgt S W m x ∧ prefixS x = some pk.publicSeed :=
  Iff.rfl

theorem mem_badQP_iff :
    s ∈ BadQP pk hon S ↔ ∃ x ω, unionH s x = some ω ∧
      (tgtDigest pk hon s.2.1.1 s.2.2 x = some (pairDigest ω) ∨
        (ω ∈ covTgt S s.2.1 s.2.2 x ∧ prefixS x = some pk.publicSeed)) :=
  Iff.rfl

/-- **Without Cov targets, the event is in the prefixed one.** -/
theorem badQ_bot_subset_badQP : BadQ pk hon ⊥ ⊆ BadQP pk hon S := by
  rintro s ⟨x, ω, hx, hω | ⟨-, -, hc⟩⟩
  · exact ⟨x, ω, hx, .inl hω⟩
  · exact absurd (hc ⟨0, by decide⟩) (Finset.notMem_empty _)

/-- **A prefixed Cov hit**: a recorded call-0 `H_msg` cell carrying `pk`'s `PK.seed`, not
hardwired, whose pair is covered. -/
theorem mem_badQP_of_cov {x : Qrom.HashDomain} {ω : PairOut} (hx : unionH s x = some ω)
    (h0 : hmsgCall x = some 0) (hw : s.2.1.1 x = none) (hc : Covered S (pairView ω))
    (hpre : prefixS x = some pk.publicSeed) : s ∈ BadQP pk hon S :=
  ⟨x, ω, hx, .inr ⟨⟨h0, hw, hc⟩, hpre⟩⟩

/-- **A target is at a `PK.seed`-carrying slot** when the honest cells are. -/
theorem prefixS_of_tgtDigest (hhon : ∀ sl, (hon sl).isSome → PrefixedSlot sl)
    {W : Database Qrom.HashDomain PairOut} {m : SelMem} {x : Qrom.HashDomain} {d : Digest}
    (h : tgtDigest pk hon W m x = some d) : prefixS x = some pk.publicSeed := by
  cases hsl : slotOf pk x with
  | none => rw [tgtDigest_of_slotOf_none W m hsl] at h; cases h
  | some sl =>
    refine prefixS_of_slotOf hsl ?_
    by_cases henc : ∀ l τ e, sl ≠ .enc l τ e
    · apply hhon
      rw [tgtDigest, hsl, Option.bind_some, slotDigest_of_ne_enc _ _ _ henc, structDigest] at h
      cases hs : hon sl with
      | none => rw [hs] at h; cases h
      | some _ => rfl
    · push Not at henc
      obtain ⟨l, τ, e, rfl⟩ := henc
      exact prefixedSlot_enc l τ e

end Prefixed

/-- **The honest cells of a table sit at `PK.seed`-carrying slots.** -/
theorem prefixedSlot_of_honCell (S0 : MasterSeed) (v : QTable) :
    ∀ sl, (QTable.honCell S0 v sl).isSome → PrefixedSlot sl := by
  intro sl h
  cases sl with
  | prfMsg _ => exact Bool.false_ne_true h
  | expand _ => exact Bool.false_ne_true h
  | _ => trivial

/-- **The hardwired call-0 `H_msg` cells carrying the table's `PK.seed` are signed digests**:
each is the digest cell of a signed message and holds its honest pair. -/
def HwDigestsP (S0 : MasterSeed) (v : QTable) (s : RomReg Qrom.HashDomain PairOut SelMem)
    (msgs : List Message) : Prop :=
  ∀ x ω, hmsgCall x = some 0 → prefixS x = some v.publicSeed → s.2.1.1 x = some ω →
    ∃ M ∈ msgs, x = cellOf S0 (digPos M) v ∧ ω = v (digPos M)

/-! ## The classification -/

/-- **A win is in the prefixed event**: `win_imp_badQ` with the Cov target and the hardwired
digest cells restricted to the cells carrying the table's `PK.seed`. -/
theorem win_imp_badQP (S0 : MasterSeed) (v : QTable) (H : Qrom.HashDomain → HashOutput)
    (S : Disclosures) (s : RomReg Qrom.HashDomain PairOut SelMem)
    (log : QueryLog SigningOracleSpec) (forgery : Forgery)
    (hlog : ∀ r ∈ log, r.2 = v.signature H r.1) (hM : ∀ r ∈ log, Records v H s.2.2 r.1)
    (hEx : HwKnown S0 v H s (log.map Sigma.fst)) (hD : HwDigestsP S0 v s (log.map Sigma.fst))
    (hcov : ∀ r ∈ log, Covered S (pairView (v (digPos r.1))))
    (hfresh : ¬SignerReturnedForgery id log forgery.message forgery.signature)
    (hverify : (honestEval (regroup hmsgRoute (viewP (unionH s)))
      (sphincsRom.verify v.publicKey forgery)).1 = true)
    (hreads : ∀ c ∈ (honestEval (regroup hmsgRoute (viewP (unionH s)))
      (sphincsRom.verify v.publicKey forgery)).2, (unionH s (hmsgRoute (c, false)).1).isSome) :
    s ∈ BadQP v.publicKey (QTable.honCell S0 v) S := by
  by_contra hnbP
  have hnb : s ∉ BadQ v.publicKey (QTable.honCell S0 v) ⊥ :=
    fun h ↦ hnbP (badQ_bot_subset_badQP h)
  have hM' : ∀ M ∈ log.map Sigma.fst, Records v H s.2.2 M := fun M hM0 ↦ by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM0
    exact hM r hr
  obtain ⟨o, ho, fk, hfk, hlay⟩ := Quantum.Sphincs.verify_spec (verify_optHash hverify hreads)
  set σ := forgery.signature
  set M := forgery.message
  -- The two digest calls read the pair of the call-0 cell.
  have hc0 := encodeInput_digestCell v.publicKey.publicSeed v.publicKey.root σ.randomizer M 0
  have hc1 := encodeInput_digestCell v.publicKey.publicSeed v.publicKey.root σ.randomizer M 1
  set x0 := digestCell v.publicKey.publicSeed v.publicKey.root σ.randomizer M 0
  have hx0 : hmsgCall x0 = some 0 := by
    rw [hmsgCall_of_encodeInput_eq_some hc0, hmsgCallOf_messageDigestInput]
  have hpre : prefixS x0 = some v.publicSeed :=
    prefixS_of_slotOf (slotOf_cell (s := .hmsg σ.randomizer M 0) ⟨0, 0, v.publicKey.publicSeed⟩
      v.publicKey.root trivial ()) (prefixedSlot_hmsg _ _ _)
  obtain ⟨ω, hω, hω0⟩ := optHash_of_ne_one hc0 (by rw [hx0]; exact fun h ↦ by cases h) (ho 0)
  have hω1 : ω.2 = o 1 := by
    have h1 := ho 1
    rw [optHash_of_encodeInput hc1, hmsgRoute_messageDigestInput _ _ _ _ hc0 hc1, hω,
      Option.map_some] at h1
    exact Option.some.inj h1
  have hop : o = pairCalls ω := funext fun c ↦ by
    rcases Quantum.Sphincs.digestCall_cases c with rfl | rfl
    · rw [pairCalls_zero, hω0]
    · rw [pairCalls_one, hω1]
  rw [hop] at hfk hlay
  set idx := (Quantum.Sphincs.digestView (pairCalls ω)).1
  set lv := (Quantum.Sphincs.digestView (pairCalls ω)).2
  obtain ⟨r0, r1, h0, h1, h2⟩ := Quantum.Sphincs.verifyLayers_spec hlay
  -- The layers, from the top.
  have ht : treeOfIndex 2 idx = 0 := Quantum.Sphincs.treeOfIndex_topLayer idx
  obtain ⟨hm2, hs2⟩ := layer_meet hnb hM' hEx h2 (by rw [ht]; rfl)
  obtain ⟨hm1, hs1⟩ := layer_meet hnb hM' hEx h1 hm2
  obtain ⟨hm0, hs0⟩ := layer_meet hnb hM' hEx h0 hm1
  -- FORS: the roots and the openings are honest, the opened leaf cells hardwired.
  obtain ⟨roots, hroots, hpk⟩ := Quantum.Sphincs.forsRecover_spec hfk
  rw [hm0] at hpk
  have hr := forsRoots_meet hnb hpk
  have hfors : ∀ κ, (σ.forsOpening κ).secret = v.forsSecret idx κ (lv κ) ∧
      (∀ z : Fin forsTreeHeight, (σ.forsOpening κ).path z =
        v.forsValue idx κ z.val (((lv κ).val >>> z.val) ^^^ 1)) ∧
      (s.2.1.1 (cellOf S0 ⟨.forsLeaf idx κ (lv κ), trivial⟩ v)).isSome := fun κ ↦ by
    obtain ⟨lf, hlf, hfold⟩ := hroots κ
    rw [hr] at hfold
    exact forsTree_meet hnb hlf hfold
  cases hw0 : s.2.1.1 x0 with
  | some y =>
    -- A signed digest cell: the forgery is that message's signature.
    obtain ⟨M', hM'm, hxM, hyM⟩ := hD x0 y hx0 hpre hw0
    have hωy : ω = y := by
      have h := hω
      change (s.2.1.1 x0).or (s.1.1 x0) = some ω at h
      rw [hw0, Option.some_or] at h
      exact (Option.some.inj h).symm
    obtain ⟨r, hrl, rfl⟩ := List.mem_map.1 hM'm
    have hsl := cell_injective (v.expandedKey S0) v.root (s := .hmsg σ.randomizer M 0)
      (s' := .hmsg (v.randomizer r.1) r.1 0) trivial trivial (p := ()) (p' := ()) hxM
    obtain ⟨hR, hMr, -⟩ := Slot.hmsg.inj (congrArg Sigma.fst hsl)
    have hview := pairView_digPos v r.1
    rw [← hyM, ← hωy] at hview
    have hidx : idx = v.index r.1 := congrArg Prod.fst hview
    have hlv : lv = v.leaves r.1 := congrArg Prod.snd hview
    apply hfresh
    refine ⟨r, hrl, hMr.symm, ?_⟩
    rw [hlog r hrl]
    unfold QTable.signature
    rw [← hidx, hs0, hs1, hs2]
    change some ⟨v.randomizer r.1, v.forsOpening idx (v.leaves r.1),
      layerSignatures (σ.layers 0) (σ.layers 1) (σ.layers 2)⟩ = some σ
    rw [← hlv, Quantum.Sphincs.layerSignatures_layers, ← hR]
    have hop : v.forsOpening idx lv = σ.forsOpening := funext fun κ ↦
      Quantum.Sphincs.forsTreeOpening_ext (hfors κ).1.symm (funext fun z ↦ ((hfors κ).2.1 z).symm)
    rw [hop]
  | none =>
    -- Otherwise the opened leaves are disclosed, hence covered: a prefixed Cov hit.
    apply hnbP
    refine mem_badQP_of_cov hω hx0 hw0 (fun κ ↦ ?_) hpre
    have hk := Quantum.Sphincs.known_forsSecret (hEx.2 idx κ (lv κ) (hfors κ).2.2)
    obtain ⟨M', hM'm, hi, hl⟩ := forsSecret_mem_disclosures hk
    obtain ⟨r, hrl, rfl⟩ := List.mem_map.1 hM'm
    have hc := hcov r hrl κ
    rw [pairView_digPos] at hc
    change lv κ ∈ S idx κ
    rw [← hi, ← hl]
    exact hc

/-! ## `n` users -/

variable {n : ℕ}

/-- **User `i`'s view of the register**: the database and hardwired cells, and `i`'s memory. -/
def projU (i : Fin n) (s : RomReg Qrom.HashDomain PairOut (SelMemN n)) :
    RomReg Qrom.HashDomain PairOut SelMem :=
  (s.1, s.2.1, s.2.2 i)

theorem unionH_projU (i : Fin n) (s : RomReg Qrom.HashDomain PairOut (SelMemN n)) :
    unionH (projU i s) = unionH s :=
  rfl

/-- **The users' honest cells.** -/
def honCellN (S0 : Fin n → MasterSeed) (w : QTableN n) : Fin n → HonestCells :=
  fun i ↦ QTable.honCell (S0 i) (w.user i)

/-- **A hit of user `i`'s prefixed event is a hit for `n` users**, with distinct `PK.seed`s and
honest cells at `PK.seed`-carrying slots: the witness is owned by `i`, whose single-user targets
are the targets of `BadQN`. -/
theorem mem_badQN_of_badQP {pk : Fin n → PublicKey} {hon : Fin n → HonestCells}
    {S : Fin n → Disclosures} (hP : Function.Injective fun j ↦ (pk j).publicSeed)
    (hhon : ∀ j sl, (hon j sl).isSome → PrefixedSlot sl)
    {s : RomReg Qrom.HashDomain PairOut (SelMemN n)} {i : Fin n}
    (h : projU i s ∈ BadQP (pk i) (hon i) (S i)) : s ∈ BadQN pk hon S := by
  obtain ⟨x, ω, hx, hω | ⟨⟨h0, hw, hc⟩, hpre⟩⟩ := h
  · have ho := ownerS_eq_some hP (prefixS_of_tgtDigest (hhon i) hω)
    exact mem_badQN_iff.2 ⟨x, ω, hx, .inl ((tgtDigestN_of_owner _ _ ho).trans hω)⟩
  · exact mem_badQN_of_cov hx h0 hw (ownerS_eq_some hP hpre) hc

/-- **A win for `n` users is in the event**: a forgery for user `i` that verifies against `i`'s
public key with every hashed cell recorded or hardwired, against a transcript of `i`'s honest
signatures and not returned by `i`'s signer, puts the state in `BadQN`, when the `PK.seed`s are
distinct, every hardwired honest chain step and FORS leaf of `i` has a known input, `i`'s memory
records `i`'s selections, every hardwired call-0 `H_msg` cell carrying `i`'s `PK.seed` is a
signed digest cell of `i` with its honest pair, and `S i` covers the view of every signed
message. -/
theorem win_imp_badQN (S0 : Fin n → MasterSeed) (w : QTableN n) (hP : PDistinct w)
    (H : Qrom.HashDomain → HashOutput) (S : Fin n → Disclosures)
    (s : RomReg Qrom.HashDomain PairOut (SelMemN n)) (i : Fin n)
    (log : QueryLog SigningOracleSpec) (forgery : Forgery)
    (hlog : ∀ r ∈ log, r.2 = (w.user i).signature H r.1)
    (hM : ∀ r ∈ log, Records (w.user i) H (s.2.2 i) r.1)
    (hEx : HwKnown (S0 i) (w.user i) H (projU i s) (log.map Sigma.fst))
    (hD : HwDigestsP (S0 i) (w.user i) (projU i s) (log.map Sigma.fst))
    (hcov : ∀ r ∈ log, Covered (S i) (pairView ((w.user i) (digPos r.1))))
    (hfresh : ¬SignerReturnedForgery id log forgery.message forgery.signature)
    (hverify : (honestEval (regroup hmsgRoute (viewP (unionH s)))
      (sphincsRom.verify (w.user i).publicKey forgery)).1 = true)
    (hreads : ∀ c ∈ (honestEval (regroup hmsgRoute (viewP (unionH s)))
      (sphincsRom.verify (w.user i).publicKey forgery)).2,
        (unionH s (hmsgRoute (c, false)).1).isSome) :
    s ∈ BadQN w.pks (honCellN S0 w) S :=
  mem_badQN_of_badQP (pk := w.pks) hP (fun j ↦ prefixedSlot_of_honCell (S0 j) (w.user j))
    (win_imp_badQP (S0 i) (w.user i) H (S i) (projU i s) log forgery hlog hM hEx hD hcov hfresh
      hverify hreads)

end Quantum.Qrom.Sphincs.Multi

end
