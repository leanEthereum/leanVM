module

public import Quantum.StdModel.Sphincs.Prf
public import Quantum.StdModel.Sphincs.ItsrHop
public import Quantum.StdModel.Sphincs.Build
public import Quantum.StdModel.Sphincs.Trace

@[expose] public section

/-!
# leanSPHINCS at a fixed table: the SM-TCR hop (B6)

The ideal hybrid read through the SM-TCR decision (`ideal W tab A (tcrDec h)`) is at most the
success of a straight-line reduction `tcrRed W A` (B6) against the SM-TCR challenger of the
target collection `tcrColl` with the evaluation collection `slotColl` (`Props.smTcr`), at every
table of a world with fair coins.

* `tcrRed W A`: samples the secret digests `s` and the randomizers `r`; while `PK.seed` is hidden,
  builds the key's digest table position by position (`buildDig` with `tcrAsk`): a secret is its
  own digest, a target position (WOTS leaf, hypertree node, FORS node, FORS key) is a `target`
  query at its slot with its payload, every other position (chain steps, FORS leaves) an `eval`
  query of `slotColl` at its slot; then `reveal`s `PK.seed`, computes the public key by the
  routed key generation and answers signing requests with the routed signer; finally it records
  the forgery's verification (`recVerify`), hashes the recorded inputs and outputs a target
  position's slot with a different payload whose recorded hash has the target's digest
  (`tcrPick`).
* At a fixed table the setup's transcript is `tcrLog` (`run_tcrRest`): one target per target
  position, at pairwise distinct slots, all before the reveal, and evaluations only at the other
  slots (`tcrValid_tcrLog`); the kernel is the signer of the routed table (`hKernel_tcr`), and
  the SM-TCR event of the forgery's trace makes the challenger's decision true
  (`tcrJudgeDec_true`).
* `ideal_tcr_le`: `ideal W tab A (tcrDec h) ≤ Props.smTcrSucc W tcrColl slotColl tab (tcrRed W A)`.
* `isChargeBound_tcrRed`: `A`'s hash calls plus the honest work of the reduction;
  `isChargeBound_tcrRed_call`: one challenger query per key position and the reveal, none per
  signing request.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Slot)
open Quantum.Qrom.Sphincs (QTable RawPos Pos posPayload posSlot slotInput SlotPayload
  SlotInRange slotInRange_posSlot posSlot_injective)

namespace Quantum.StdModel.Sphincs

open Props (TcrSpec TcrQuery tcrTargets TcrValid)

/-! ## Target messages at the key's slots -/

/-- A payload of a key position's slot as a message of its target function (`0` for the
positions that are no target). -/
def tcrKeyMsg : (p : RawPos) → SlotPayload (keySlot p) → TcrMsg (tcrFnOf p)
  | .leaf .., d => d
  | .node .., d => d
  | .forsNode .., d => d
  | .forsRoots _, d => d
  | .prfKey, _ => fun _ ↦ 0
  | .publicSeed, _ => fun _ ↦ 0
  | .chainStart .., _ => fun _ ↦ 0
  | .chain .., _ => fun _ ↦ 0
  | .forsSecret .., _ => fun _ ↦ 0
  | .forsLeaf .., _ => fun _ ↦ 0
  | .prfMsg _, _ => fun _ ↦ 0
  | .hmsg _, _ => fun _ ↦ 0

theorem tcrKeyMsg_injective {p : RawPos} (hp : IsTarget p) : Function.Injective (tcrKeyMsg p) := by
  cases p with
  | leaf | node | forsNode | forsRoots => exact fun _ _ h ↦ h
  | _ => exact False.elim hp

/-- **A target position as a target input**: its slot and a payload of the slot give the slot's
honest input. -/
theorem tcrColl_layout_key (P : PublicParameter) (p : Pos) (hp : IsTarget p.1)
    (d : SlotPayload (keySlot p.1)) :
    tcrColl.layout (tcrFnOf p.1) P (keySlot p.1) (tcrKeyMsg p.1 d) =
      slotInput (pubKey P) 0 (keySlot p.1) d := by
  obtain ⟨p, hin⟩ := p
  have hr := slotInRange_posSlot (fun _ ↦ 0) ⟨p, hin⟩
  cases p with
  | leaf => rfl
  | node => exact ite_eq_left hr
  | forsNode => exact ite_eq_left hr
  | forsRoots => rfl
  | _ => exact False.elim hp

/-! ## Classification of the key's positions -/

/-- The secret digest of a position, if it is a secret of the key. -/
def tcrSecOf : RawPos → Option KeygenDomain
  | .chainStart l τ e i => some (.oneTimeChain l τ e i)
  | .forsSecret idx κ j => some (.forsSecret idx κ j)
  | _ => none

/-- Whether a position is a target. -/
def tcrIsTgt : RawPos → Bool
  | .leaf .. | .node .. | .forsNode .. | .forsRoots _ => true
  | _ => false

theorem tcrIsTgt_iff {p : RawPos} : tcrIsTgt p = true ↔ IsTarget p := by
  cases p <;> simp [tcrIsTgt, IsTarget]

theorem tcr_keyPart_of_isTarget {p : RawPos} (hp : IsTarget p) : KeyPart p := by
  cases p <;> trivial

theorem tcr_not_secret_of_isTarget {p : RawPos} (hp : IsTarget p) : ¬IsSecret p := by
  cases p <;> first | exact id | exact False.elim hp

theorem tcr_not_secret {p : RawPos} (hk : KeyPart p) (hs : tcrSecOf p = none) : ¬IsSecret p := by
  cases p <;> simp_all [tcrSecOf, KeyPart, IsSecret]

theorem tcr_ne_hmsg {p : RawPos} (hk : KeyPart p) (M : Message) : p ≠ .hmsg M := by
  rintro rfl
  exact hk

/-- Distinct key positions have distinct slots (DIST). -/
theorem tcr_keySlot_inj {p q : RawPos} (hp : KeyPart p) (hq : KeyPart q)
    (h : keySlot p = keySlot q) : p = q :=
  posSlot_injective (fun _ ↦ 0) ((posSlot_eq_keySlot _ (tcr_ne_hmsg hp)).trans
    (h.trans (posSlot_eq_keySlot _ (tcr_ne_hmsg hq)).symm))

theorem tcr_dig_secret (h : HashInput → HashOutput) (P : PublicParameter)
    (s : KeygenDomain → Digest) (r : Message → Digest) (p : Pos) {k : KeygenDomain}
    (hk : tcrSecOf p.1 = some k) : (digTable h P s r).dig p.1 = s k := by
  obtain ⟨p, hin⟩ := p
  cases p with
  | chainStart l τ e i =>
    obtain rfl := Option.some.inj hk
    exact dig_chainStart_digTable h P s r hin
  | forsSecret idx κ j =>
    obtain rfl := Option.some.inj hk
    exact dig_forsSecret_digTable h P s r idx κ j
  | _ => simp [tcrSecOf] at hk

theorem tcr_nodup_keyOrder : keyOrder.Nodup := by
  unfold keyOrder
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

/-! ## The reduction -/

/-- The SM-TCR ports of leanSPHINCS. -/
abbrev TcrPorts : OracleSpec (TcrQuery Slot TcrFn TcrMsg Slot SlotPayload) :=
  TcrSpec PublicParameter Slot TcrFn TcrMsg Digest Slot SlotPayload Digest

/-- A query of the SM-TCR ports. -/
abbrev TcrQ : Type := TcrQuery Slot TcrFn TcrMsg Slot SlotPayload

/-- An entry of the SM-TCR transcript. -/
abbrev TcrEnt : Type := (q : TcrQ) × TcrPorts.Range q

/-- An output of the SM-TCR game: a target function, a tweak and a message. -/
abbrev TcrOut : Type := Σ l : TcrFn, Slot × TcrMsg l

/-- The output at a key position's slot with the payload `d`. -/
def tcrOutOf (p : RawPos) (d : SlotPayload (keySlot p)) : TcrOut :=
  ⟨tcrFnOf p, keySlot p, tcrKeyMsg p d⟩

/-- The output when no witness exists. -/
def tcrDefault : TcrOut :=
  ⟨.node, .expand 0, (0, 0)⟩

/-- **A witness of the reduction**: a target position and a payload of its slot other than the
one read from the digests `t`, whose input `H` answers with the position's digest. -/
def TcrWit (P : PublicParameter) (t : RawPos → Digest) (H : HashInput → Option HashOutput)
    (p : Pos) (d : SlotPayload (keySlot p.1)) : Prop :=
  IsTarget p.1 ∧ d ≠ keyPayload p.1 t ∧
    ∃ o, H (slotInput (pubKey P) 0 (keySlot p.1) d) = some o ∧ truncateHash o = t p.1

/-- **The reduction's output**: a witness, chosen classically, else `tcrDefault`. -/
noncomputable def tcrPick (P : PublicParameter) (t : RawPos → Digest)
    (H : HashInput → Option HashOutput) : TcrOut :=
  @dite _ (∃ w : Σ p : Pos, SlotPayload (keySlot p.1), TcrWit P t H w.1 w.2)
    (Classical.propDecidable _) (fun hw ↦ tcrOutOf hw.choose.1.1 hw.choose.2)
    fun _ ↦ tcrDefault

theorem tcrPick_spec {P : PublicParameter} {t : RawPos → Digest}
    {H : HashInput → Option HashOutput}
    (h : ∃ (p : Pos) (d : SlotPayload (keySlot p.1)), TcrWit P t H p d) :
    ∃ (p : Pos) (d : SlotPayload (keySlot p.1)), TcrWit P t H p d ∧
      tcrPick P t H = tcrOutOf p.1 d := by
  have hw : ∃ w : Σ p : Pos, SlotPayload (keySlot p.1), TcrWit P t H w.1 w.2 := by
    obtain ⟨p, d, hpd⟩ := h
    exact ⟨⟨p, d⟩, hpd⟩
  exact ⟨hw.choose.1, hw.choose.2, hw.choose_spec, dite_eq_left hw⟩

/-- The answer recorded for an input in a list of hashed inputs. -/
def tcrLook : List (HashInput × HashOutput) → HashInput → Option HashOutput
  | [], _ => none
  | y :: ps, x => if x = y.1 then some y.2 else tcrLook ps x

/-- The reduction's data after its setup. -/
structure TcrData where
  /-- `PK.seed`, revealed by the challenger. -/
  P : PublicParameter
  /-- The secret digests. -/
  s : KeygenDomain → Digest
  /-- The randomizers. -/
  r : Message → Digest
  /-- The built digest table. -/
  t : RawPos → Digest
  /-- The public key. -/
  pk : PublicKey

/-- The handler state: the data and the signing transcript. -/
abbrev TcrSt : Type := TcrData × SignLog

variable (W : OracleWorld)

/-- The world's Keccak-256 as a classical call of the reduction. -/
noncomputable def tcrHash (l : HashInput) : OracleComp (W.Oracles + TcrPorts) HashOutput :=
  liftW TcrPorts (W.hash l)

/-- **The reduction's ask at a key position**: a target query at a target position, the own
digest at a secret, an evaluation of `slotColl` at the other positions. -/
noncomputable def tcrAsk (s : KeygenDomain → Digest) (p : RawPos) (t : RawPos → Digest) :
    OracleComp (W.Oracles + TcrPorts) Digest :=
  if tcrIsTgt p then
    portQ W TcrPorts (.target (tcrFnOf p) (keySlot p) (tcrKeyMsg p (keyPayload p t)))
  else
    match tcrSecOf p with
    | some k => pure (s k)
    | none => portQ W TcrPorts (.eval (keySlot p) (keySlot p) (keyPayload p t))

/-- The setup after the sampling: the build while `PK.seed` is hidden, the reveal, the routed
key generation. -/
noncomputable def tcrRest (s : KeygenDomain → Digest) (r : Message → Digest) :
    OracleComp (W.Oracles + TcrPorts) TcrData := do
  let t ← buildDig (tcrAsk W s)
  let P ← portQ W TcrPorts .reveal
  let keys ← Qrom.Sphincs.LeanSphincsOver.keygenFromSeed
    (routeHash P (fun d ↦ pure (s d)) (fun M ↦ pure (r M)) (tcrHash W)) 0
  pure ⟨P, s, r, t, keys.1⟩

/-- **The setup of B6**: uniform secret digests and randomizers, then `tcrRest`. -/
noncomputable def tcrPre : OracleComp (W.Oracles + TcrPorts) TcrData := do
  let s ← liftW TcrPorts (Props.sample W (KeygenDomain → Digest))
  let r ← liftW TcrPorts (Props.sample W (Message → Digest))
  tcrRest W s r

/-- **The handler of B6**: the routed signer, logged. -/
noncomputable def tcrSigner : HHandler W SignSpec TcrPorts TcrSt := fun st M ↦ do
  let sig ← Qrom.Sphincs.LeanSphincsOver.sign
    (routeHash st.1.P (fun d ↦ pure (st.1.s d)) (fun M ↦ pure (st.1.r M)) (tcrHash W)) 0 M
  pure (sig, (st.1, st.2 ++ [⟨M, sig⟩]))

/-- Each input with its hash. -/
noncomputable def tcrHashAll :
    List HashInput → OracleComp (W.Oracles + TcrPorts) (List (HashInput × HashOutput))
  | [] => pure []
  | x :: xs => do
    let o ← tcrHash W x
    let ps ← tcrHashAll xs
    pure ((x, o) :: ps)

/-- **The output of B6**: the forgery's recorded verification, the recorded inputs hashed, and
a witness among them. -/
noncomputable def tcrPost (a : TcrData) (forg : Forgery) (_ : TcrSt) :
    OracleComp (W.Oracles + TcrPorts) TcrOut := do
  let rv ← recVerify (tcrHash W) a.pk forg.message forg.signature
  let ps ← tcrHashAll W rv.2
  pure (tcrPick a.P a.t (tcrLook ps))

/-- **B6, the SM-TCR reduction**: the setup `tcrPre`, `A` on the public key with its requests
answered by `tcrSigner`, the output `tcrPost`. -/
noncomputable def tcrRed (A : SAdv W) : Props.Adversary W TcrPorts Unit TcrOut := fun _ ↦
  slRed W (tcrPre W) (fun a ↦ A a.pk) (fun a ↦ (a, [])) (tcrSigner W) (tcrPost W)

/-! ## A straight-line reduction against a deterministic decision -/

section Normal

variable (tab : W.Tab) {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
  {R' : OracleSpec.{0, 0} Q'}

/-- **A straight-line reduction whose output and decision are deterministic**: the success
probability is the average over the challenger's setup and the reduction's logged setup of the
canonical run against the reduction's kernel, read through the decision `D`. -/
theorem tcr_succAt_slRed {Out : Type} (E : Props.Experiment W R' Unit Out) {S0 St F : Type}
    (pre : OracleComp (W.Oracles + R') S0)
    (adv : S0 → QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) F) (st0 : S0 → St)
    (σ : HHandler W R R' St) (post : S0 → F → St → OracleComp (W.Oracles + R') Out)
    (D : E.State → S0 → F × (St × QueryLog R') → Bool)
    (hpost : ∀ s a f st log,
      ((simulateQ (logImpl tab (E.answer s)) (post a f st)).run log >>= fun r ↦
        simulateQ (W.eager tab) (E.judge s r.2 r.1)) = pure (D s a (f, (st, log)))) :
    E.succAt tab (fun _ ↦ slRed W pre adv st0 σ post) =
      ∑' s, Pr{let z ← simulateQ (W.eager tab) E.setup}[z = s] *
        ∑' p, Pr{let z ← (simulateQ (logImpl tab (E.answer s)) pre).run []}[z = p] *
          W.probAt tab ((kRunQ W (hKernel tab (E.answer s) σ) (adv p.1) (st0 p.1, p.2)).map
            (D s p.1)) := by
  refine (probAt_eq_of_run₂ W tab (run₂_game_slRed tab E (fun _ ↦ pre) (fun _ ↦ adv)
    (fun _ ↦ st0) (fun _ ↦ σ) (fun _ ↦ post))).trans
    ((probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt (W.runtime tab) _)
      _).trans (tsum_congr fun s ↦ congrArg _ ?_))
  rw [slNormal, QuantumComp₂.bind_assoc]
  refine (probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt (W.runtime tab) _)
    _).trans ?_
  refine tsum_congr fun p ↦ congrArg _ (probAt_eq_of_run₂ W tab ?_)
  rw [QuantumComp₂.bind_assoc]
  have htail : ∀ r : (F × St) × QueryLog R', (W.runtime tab).run₂ .instruments
      (QuantumComp₂.bind (((simulateQ (logImpl tab (E.answer s)) (post p.1 r.1.1 r.1.2)).run
        r.2).toQuantumAt (QComp.coinImpl W.spec (QReg.of Unit))) fun r' ↦
        (simulateQ (W.eager tab) (E.judge s r'.2 r'.1)).toQuantumAt
          (QComp.coinImpl W.spec (QReg.of Unit))) =
      (W.runtime tab).run₂ .instruments
        (QuantumComp₂.pure (D s p.1 (r.1.1, (r.1.2, r.2)))) := fun r ↦
    run₂_eq_of_classicalOn (((classicalOn_coinImpl_toQuantumAt _ _).bind_id fun r' ↦
      classicalOn_coinImpl_toQuantumAt _ _).congr (hpost s p.1 r.1.1 r.1.2 r.2) rfl)
      (classicalOn_pure _)
  refine (run₂_bind_congr rfl htail).trans ?_
  rw [← QuantumComp₂.map_eq_bind_pure, kRunL_eq_map, map_map_qcomp]
  rfl

end Normal

/-! ## Transcript -/

/-- The transcript entry of a key position, its payload and answer read from the digests `u`. -/
def tcrEnt (u : RawPos → Digest) (p : RawPos) : Option TcrEnt :=
  if tcrIsTgt p then
    some ⟨.target (tcrFnOf p) (keySlot p) (tcrKeyMsg p (keyPayload p u)), u p⟩
  else
    match tcrSecOf p with
    | some _ => none
    | none => some ⟨.eval (keySlot p) (keySlot p) (keyPayload p u), u p⟩

/-- **The setup's transcript** at the digests `u` and `PK.seed = P`. -/
noncomputable def tcrLog (u : RawPos → Digest) (P : PublicParameter) : QueryLog TcrPorts :=
  keyOrder.filterMap (fun p ↦ tcrEnt u p.1) ++ [⟨.reveal, P⟩]

theorem tcrTargets_tcrLog (u : RawPos → Digest) (P : PublicParameter) :
    tcrTargets (tcrLog u P) = keyOrder.filterMap fun p ↦ if tcrIsTgt p.1 then
      some (((⟨tcrFnOf p.1, keySlot p.1, tcrKeyMsg p.1 (keyPayload p.1 u)⟩ : TcrOut)), u p.1)
    else none := by
  unfold tcrTargets tcrLog
  rw [List.filterMap_append, List.filterMap_filterMap]
  refine (congrArg₂ (· ++ ·) (congrArg (List.filterMap · keyOrder) (funext fun p ↦ ?_))
    (rfl : _ = [])).trans (List.append_nil _)
  unfold tcrEnt
  split_ifs
  · rfl
  · split <;> rfl

theorem tcrTweaks_tcrLog (u : RawPos → Digest) (P : PublicParameter) :
    (tcrTargets (tcrLog u P)).map (fun e ↦ e.1.2.1) =
      keyOrder.filterMap fun p ↦ if tcrIsTgt p.1 then some (keySlot p.1) else none := by
  rw [tcrTargets_tcrLog, List.map_filterMap]
  refine congrArg (List.filterMap · keyOrder) (funext fun p ↦ ?_)
  split_ifs <;> rfl

theorem mem_tcrTargets_tcrLog (u : RawPos → Digest) (P : PublicParameter) (p : Pos)
    (hp : IsTarget p.1) :
    (((⟨tcrFnOf p.1, keySlot p.1, tcrKeyMsg p.1 (keyPayload p.1 u)⟩ : TcrOut)), u p.1) ∈
      tcrTargets (tcrLog u P) := by
  rw [tcrTargets_tcrLog]
  exact List.mem_filterMap.mpr ⟨p, (mem_keyOrder p).mpr (tcr_keyPart_of_isTarget hp),
    ite_eq_left (tcrIsTgt_iff.mpr hp)⟩

theorem tcrEnt_isReveal {u : RawPos → Digest} {p : RawPos} {e : TcrEnt}
    (h : tcrEnt u p = some e) : e.1.isReveal = false := by
  unfold tcrEnt at h
  split_ifs at h
  · obtain rfl := Option.some.inj h
    rfl
  · split at h
    · simp at h
    · obtain rfl := Option.some.inj h
      rfl

theorem tcrEnt_evalTweak {u : RawPos → Digest} {p : RawPos} {tw : Slot}
    (h : (tcrEnt u p).bind Props.TcrQuery.evalTweak = some tw) :
    tcrIsTgt p = false ∧ keySlot p = tw := by
  unfold tcrEnt at h
  split_ifs at h with hg
  · simp [Props.TcrQuery.evalTweak] at h
  · refine ⟨by simpa using hg, ?_⟩
    split at h
    · simp at h
    · exact Option.some.inj h

theorem tcr_phaseTwo (L : QueryLog TcrPorts) (hL : ∀ e ∈ L, e.1.isReveal = false) (x : TcrEnt)
    (hx : x.1.isReveal = true) :
    Props.phaseTwo (fun q : TcrQ ↦ q.isReveal) (L ++ [x]) = [x] := by
  induction L with
  | nil => simp [Props.phaseTwo, hx]
  | cons a L ih =>
    have ha := hL a List.mem_cons_self
    have ih' := ih fun e he ↦ hL e (List.mem_cons_of_mem a he)
    unfold Props.phaseTwo at ih' ⊢
    rw [List.cons_append, List.dropWhile_cons]
    simpa [ha] using ih'

/-- **The setup's transcript is valid**: one target per target position at pairwise distinct
slots, every target before the reveal, evaluations only at the slots of no target. -/
theorem tcrValid_tcrLog (u : RawPos → Digest) (P : PublicParameter) :
    TcrValid (tcrLog u P) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tcrTweaks_tcrLog]
    refine List.Nodup.filterMap (fun p q b hb hb' ↦ ?_) tcr_nodup_keyOrder
    split_ifs at hb hb' with h1 h2
    · exact Subtype.ext (tcr_keySlot_inj
        (tcr_keyPart_of_isTarget (tcrIsTgt_iff.mp h1)) (tcr_keyPart_of_isTarget
          (tcrIsTgt_iff.mp h2)) ((Option.mem_some_iff.mp hb).trans
            (Option.mem_some_iff.mp hb').symm))
    all_goals simp at hb hb'
  · intro e he
    rw [tcrLog, tcr_phaseTwo _ (fun e he ↦ ?_) _ rfl] at he
    · rw [List.mem_singleton.mp he]
      rfl
    · obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp he
      exact tcrEnt_isReveal hp
  · intro tw htw htg
    rw [tcrTweaks_tcrLog] at htg
    obtain ⟨q, hq, hqtw⟩ := List.mem_filterMap.mp htg
    unfold tcrLog at htw
    rw [List.filterMap_append, List.mem_append, List.filterMap_filterMap] at htw
    rcases htw with htw | htw
    · obtain ⟨p, hp, hptw⟩ := List.mem_filterMap.mp htw
      obtain ⟨hpg, hpk⟩ := tcrEnt_evalTweak hptw
      split_ifs at hqtw with hqg
      · have hpq : p.1 = q.1 := tcr_keySlot_inj ((mem_keyOrder p).mp hp)
          ((mem_keyOrder q).mp hq) (hpk.trans (Option.some.inj hqtw).symm)
        rw [hpq, hqg] at hpg
        exact Bool.noConfusion hpg
    · exact List.not_mem_nil htw

/-! ## The logged build -/

/-- **The logged build**: when each ask, given the target digests `T` at the lower positions,
returns `T` and appends its entry, the build returns `T` on the key's positions and appends the
entries in `keyOrder`. -/
theorem tcr_foldlM_log {n : Type → Type} [Monad n] [LawfulMonad n] {E : Type}
    (ask : RawPos → (RawPos → Digest) → StateT (List E) n Digest) (T : RawPos → Digest)
    (ent : RawPos → Option E)
    (hask : ∀ p : Pos, KeyPart p.1 → ∀ t : RawPos → Digest,
      (∀ q : Pos, KeyPart q.1 → q.1.rank < p.1.rank → t q.1 = T q.1) →
        ∀ L, (ask p.1 t).run L = pure (T p.1, L ++ (ent p.1).toList)) :
    ∀ Ps : List Pos, Ps.Pairwise (fun a b : Pos ↦ a.1.rank ≤ b.1.rank) →
      (∀ p ∈ Ps, KeyPart p.1) → ∀ t : RawPos → Digest,
        (∀ q : Pos, KeyPart q.1 → q ∉ Ps → t q.1 = T q.1) → ∀ L,
          ∃ tf, (Ps.foldlM (buildStep ask) t).run L =
              pure (tf, L ++ Ps.filterMap fun p ↦ ent p.1) ∧
            ∀ q : Pos, KeyPart q.1 → tf q.1 = T q.1
  | [], _, _, t, hinv, L => ⟨t, by simp, fun q hk ↦ hinv q hk fun h ↦ by cases h⟩
  | p :: Ps, hL, hK, t, hinv, L => by
    rw [List.pairwise_cons] at hL
    have hkp := hK p List.mem_cons_self
    have hlow : ∀ q : Pos, KeyPart q.1 → q.1.rank < p.1.rank → t q.1 = T q.1 :=
      fun q hk hr ↦ hinv q hk fun hmem ↦ by
        rcases List.mem_cons.1 hmem with rfl | hmem
        · exact lt_irrefl _ hr
        · exact absurd (hL.1 q hmem) (Nat.not_le.2 hr)
    obtain ⟨tf, h1, h2⟩ := tcr_foldlM_log ask T ent hask Ps hL.2
      (fun q hq ↦ hK q (List.mem_cons_of_mem p hq)) (Function.update t p.1 (T p.1))
      (fun q hk hq ↦ by
        by_cases hqp : q = p
        · subst hqp
          rw [Function.update_self]
        · rw [Function.update_of_ne fun e ↦ hqp (Subtype.ext e)]
          exact hinv q hk fun hmem ↦ (List.mem_cons.1 hmem).elim hqp hq)
      (L ++ (ent p.1).toList)
    refine ⟨tf, ?_, h2⟩
    simp only [List.foldlM_cons, buildStep, StateT.run_bind, hask p hkp t hlow L, pure_bind,
      StateT.run_pure, h1]
    rcases he : ent p.1 with _ | e <;> simp [he]

theorem tcr_buildDig_log {n : Type → Type} [Monad n] [LawfulMonad n] {E : Type}
    (ask : RawPos → (RawPos → Digest) → StateT (List E) n Digest) (T : RawPos → Digest)
    (ent : RawPos → Option E)
    (hask : ∀ p : Pos, KeyPart p.1 → ∀ t : RawPos → Digest,
      (∀ q : Pos, KeyPart q.1 → q.1.rank < p.1.rank → t q.1 = T q.1) →
        ∀ L, (ask p.1 t).run L = pure (T p.1, L ++ (ent p.1).toList)) (L : List E) :
    ∃ tf, (buildDig ask).run L = pure (tf, L ++ keyOrder.filterMap fun p ↦ ent p.1) ∧
      ∀ q : Pos, KeyPart q.1 → tf q.1 = T q.1 :=
  tcr_foldlM_log ask T ent hask keyOrder pairwise_keyOrder (fun p hp ↦ (mem_keyOrder p).1 hp) _
    (fun q hk hq ↦ (hq ((mem_keyOrder q).2 hk)).elim) L

/-! ## The reduction at a fixed table -/

section Table

variable (tab : W.Tab)

theorem simulateQ_logImpl_tcrHash (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q))
    (l : HashInput) :
    simulateQ (logImpl tab ans) (tcrHash W l) =
      (pure (W.hashOf tab l) : StateT (QueryLog TcrPorts) ProbComp HashOutput) := by
  refine StateT.ext fun log ↦ ?_
  rw [tcrHash, run_simulateQ_logImpl_liftW, W.simulateQ_hash, map_pure, StateT.run_pure]

theorem run_logImpl_tcrPortQ (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q))
    (q : TcrQ) (L : QueryLog TcrPorts) :
    (simulateQ (logImpl tab ans) (portQ W TcrPorts q)).run L =
      (fun a ↦ (a, L ++ [⟨q, a⟩])) <$> simulateQ (W.eager tab) (ans q) := by
  rw [portQ, simulateQ_spec_query]
  rfl

theorem run_logImpl_tcrTarget (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q))
    (l : TcrFn) (tw : Slot) (m : TcrMsg l) (L : QueryLog TcrPorts) :
    (simulateQ (α := Digest) (logImpl tab ans) (portQ W TcrPorts (.target l tw m))).run L =
      (fun a : Digest ↦ (a, L ++ [⟨.target l tw m, a⟩])) <$> simulateQ (α := Digest)
        (W.eager tab) (ans (.target l tw m)) :=
  run_logImpl_tcrPortQ W tab ans _ L

theorem run_logImpl_tcrEval (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q))
    (l : Slot) (tw : Slot) (m : SlotPayload l) (L : QueryLog TcrPorts) :
    (simulateQ (α := Digest) (logImpl tab ans) (portQ W TcrPorts (.eval l tw m))).run L =
      (fun a : Digest ↦ (a, L ++ [⟨.eval l tw m, a⟩])) <$> simulateQ (α := Digest)
        (W.eager tab) (ans (.eval l tw m)) :=
  run_logImpl_tcrPortQ W tab ans _ L

theorem simulateQ_logImpl_tcrSign
    (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q)) (P : PublicParameter)
    (s : KeygenDomain → Digest) (r : Message → Digest) (M : Message) :
    simulateQ (logImpl tab ans) (Qrom.Sphincs.LeanSphincsOver.sign
      (routeHash P (fun d ↦ pure (s d)) (fun M ↦ pure (r M)) (tcrHash W)) 0 M) =
      (pure ((digTable (W.hashOf tab) P s r).signature (cellHash (W.hashOf tab)) M) :
        StateT (QueryLog TcrPorts) ProbComp (Option Signature)) := by
  rw [Over.simulateQ_sign]
  simp only [simulateQ_routeHash, simulateQ_pure, simulateQ_logImpl_tcrHash]
  exact sign_routeHash (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) M

theorem simulateQ_logImpl_tcrKeygen
    (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q)) (P : PublicParameter)
    (s : KeygenDomain → Digest) (r : Message → Digest) :
    simulateQ (logImpl tab ans) (Qrom.Sphincs.LeanSphincsOver.keygenFromSeed
      (routeHash P (fun d ↦ pure (s d)) (fun M ↦ pure (r M)) (tcrHash W)) 0) =
      (pure ((digTable (W.hashOf tab) P s r).publicKey, 0) :
        StateT (QueryLog TcrPorts) ProbComp (PublicKey × SecretKey)) := by
  rw [Over.simulateQ_keygenFromSeed]
  simp only [simulateQ_routeHash, simulateQ_pure, simulateQ_logImpl_tcrHash]
  exact keygenFromSeed_routeHash (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

theorem simulateQ_tcrHashAll (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q)) :
    ∀ xs : List HashInput, simulateQ (logImpl tab ans) (tcrHashAll W xs) =
      (pure (xs.map fun y ↦ (y, W.hashOf tab y)) :
        StateT (QueryLog TcrPorts) ProbComp (List (HashInput × HashOutput)))
  | [] => simulateQ_pure _ _
  | x :: xs => by
    simp only [tcrHashAll, simulateQ_bind, simulateQ_logImpl_tcrHash, pure_bind,
      simulateQ_tcrHashAll ans xs, simulateQ_pure, List.map_cons]

theorem tcrLook_map (h : HashInput → HashOutput) (xs : List HashInput) :
    tcrLook (xs.map fun y ↦ (y, h y)) = traceOf xs h := by
  funext x
  induction xs with
  | nil => simp [tcrLook, traceOf]
  | cons y xs ih =>
    simp only [List.map_cons, tcrLook]
    by_cases hxy : x = y
    · subst hxy
      simp [traceOf]
    · rw [ite_eq_right hxy, ih]
      simp [traceOf, hxy]

/-- The challenger of SM-TCR. -/
noncomputable abbrev tcrGame : Props.Experiment W TcrPorts Unit TcrOut :=
  Props.smTcr W tcrColl slotColl

theorem simulateQ_tcrAnswer_target (P : PublicParameter) (p : Pos) (hp : IsTarget p.1)
    (d : SlotPayload (keySlot p.1)) :
    simulateQ (α := Digest) (W.eager tab) ((tcrGame W).answer P
      (.target (tcrFnOf p.1) (keySlot p.1) (tcrKeyMsg p.1 d))) =
      pure (thSlot (W.hashOf tab) P (keySlot p.1) d) := by
  change simulateQ (W.eager tab) (tcrColl.eval W (tcrFnOf p.1) P (keySlot p.1)
    (tcrKeyMsg p.1 d)) = _
  rw [simulateQ_eval, tcrColl_layout_key P p hp d]
  rfl

theorem simulateQ_tcrAnswer_eval (P : PublicParameter) (p : Pos) (hk : KeyPart p.1)
    (d : SlotPayload (keySlot p.1)) :
    simulateQ (α := Digest) (W.eager tab)
      ((tcrGame W).answer P (.eval (keySlot p.1) (keySlot p.1) d)) =
      pure (thSlot (W.hashOf tab) P (keySlot p.1) d) :=
  simulateQ_slotColl_eval W tab P (slotInRange_keySlot p (tcr_ne_hmsg hk)) d

/-- **An ask at a fixed table** returns the routed table's digest and logs its entry. -/
theorem run_tcrAsk (P : PublicParameter) (s : KeygenDomain → Digest) (r : Message → Digest)
    (p : Pos) (hk : KeyPart p.1) (t : RawPos → Digest)
    (ht : ∀ q : Pos, KeyPart q.1 → q.1.rank < p.1.rank →
      t q.1 = (digTable (W.hashOf tab) P s r).dig q.1)
    (L : QueryLog TcrPorts) :
    (simulateQ (logImpl tab ((tcrGame W).answer P)) (tcrAsk W s p.1 t)).run L =
      pure ((digTable (W.hashOf tab) P s r).dig p.1,
        L ++ (tcrEnt (digTable (W.hashOf tab) P s r).dig p.1).toList) := by
  have hpay : keyPayload p.1 t = keyPayload p.1 (digTable (W.hashOf tab) P s r).dig :=
    keyPayload_congr p.1 ht
  unfold tcrAsk tcrEnt
  by_cases hg : tcrIsTgt p.1 = true
  · have hp := tcrIsTgt_iff.mp hg
    simp only [hg, ↓reduceIte]
    rw [hpay, run_logImpl_tcrTarget, simulateQ_tcrAnswer_target W tab P p hp,
      ← dig_digTable_eq_thSlot _ P s r p hk (tcr_not_secret_of_isTarget hp)]
    rfl
  · have hg' : tcrIsTgt p.1 = false := by simpa using hg
    simp only [hg', Bool.false_eq_true, ↓reduceIte]
    rcases hs : tcrSecOf p.1 with _ | k <;> dsimp only
    · rw [hpay, run_logImpl_tcrEval, simulateQ_tcrAnswer_eval W tab P p hk,
        ← dig_digTable_eq_thSlot _ P s r p hk (tcr_not_secret hk hs)]
      rfl
    · rw [simulateQ_pure, StateT.run_pure, tcr_dig_secret _ P s r p hs]
      simp

/-- **The setup after the sampling at a fixed table**: the routed table's digests and public
key, with the transcript `tcrLog`. -/
theorem run_tcrRest (P : PublicParameter) (s : KeygenDomain → Digest) (r : Message → Digest) :
    ∃ tf : RawPos → Digest,
      (∀ q : Pos, KeyPart q.1 → tf q.1 = (digTable (W.hashOf tab) P s r).dig q.1) ∧
      (simulateQ (logImpl tab ((tcrGame W).answer P)) (tcrRest W s r)).run [] =
        pure (⟨P, s, r, tf, (digTable (W.hashOf tab) P s r).publicKey⟩,
          tcrLog (digTable (W.hashOf tab) P s r).dig P) := by
  obtain ⟨tf, hrun, htf⟩ := tcr_buildDig_log
    (fun p t ↦ simulateQ (logImpl tab ((tcrGame W).answer P)) (tcrAsk W s p t))
    (digTable (W.hashOf tab) P s r).dig (tcrEnt (digTable (W.hashOf tab) P s r).dig)
    (fun p hk t ht L ↦ run_tcrAsk W tab P s r p hk t ht L) []
  refine ⟨tf, htf, ?_⟩
  have hrev : ∀ L, (simulateQ (logImpl tab ((tcrGame W).answer P))
      (portQ W TcrPorts .reveal)).run L = (pure (P, L ++ [⟨.reveal, P⟩]) :
        ProbComp (TcrPorts.Range .reveal × QueryLog TcrPorts)) := fun L ↦ by
    rw [run_logImpl_tcrPortQ]
    rfl
  simp only [tcrRest, simulateQ_bind, StateT.run_bind, simulateQ_buildDig, hrun, pure_bind,
    hrev, simulateQ_logImpl_tcrKeygen, StateT.run_pure, simulateQ_pure, List.nil_append]
  rfl

theorem run_tcrPre (hW : W.CoinsFair)
    (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q)) :
    (simulateQ (logImpl tab ans) (tcrPre W)).run [] =
      ($ᵗ (KeygenDomain → Digest)) >>= fun s ↦ ($ᵗ (Message → Digest)) >>= fun r ↦
        (simulateQ (logImpl tab ans) (tcrRest W s r)).run [] := by
  simp only [tcrPre, simulateQ_bind, StateT.run_bind, run_simulateQ_logImpl_liftW,
    W.simulateQ_sample hW tab, bind_map_left]

/-- The reduction's kernel answers as the signer of the routed table, keeping its transcript. -/
theorem hKernel_tcr (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q)) (a : TcrData)
    (slog : SignLog) (L : QueryLog TcrPorts) (M : Message) :
    hKernel tab ans (tcrSigner W) ((a, slog), L) M =
      pure ((digTable (W.hashOf tab) a.P a.s a.r).signature (cellHash (W.hashOf tab)) M,
        ((a, slog ++ [⟨M, (digTable (W.hashOf tab) a.P a.s a.r).signature
          (cellHash (W.hashOf tab)) M⟩]), L)) := by
  simp only [hKernel, tcrSigner, simulateQ_bind, simulateQ_logImpl_tcrSign,
    StateT.run_pure, pure_bind, simulateQ_pure, map_pure]

/-- **The challenger's decision on the reduction's run**: the transcript's validity and a
target colliding with the output. -/
noncomputable def tcrJudgeDec (P : PublicParameter) (a : TcrData)
    (x : Forgery × (TcrSt × QueryLog TcrPorts)) : Bool :=
  Props.holds (TcrValid x.2.2 ∧ ∃ e ∈ tcrTargets x.2.2,
    e.1.1 = (tcrPick a.P a.t (traceOf (Extract.verifyQueries (W.hashOf tab) a.pk x.1.message
      x.1.signature) (W.hashOf tab))).1 ∧
    e.1.2.1 = (tcrPick a.P a.t (traceOf (Extract.verifyQueries (W.hashOf tab) a.pk x.1.message
      x.1.signature) (W.hashOf tab))).2.1 ∧
    e.1 ≠ tcrPick a.P a.t (traceOf (Extract.verifyQueries (W.hashOf tab) a.pk x.1.message
      x.1.signature) (W.hashOf tab)) ∧
    e.2 = tcrColl.trunc (W.hashOf tab (tcrColl.layout
      (tcrPick a.P a.t (traceOf (Extract.verifyQueries (W.hashOf tab) a.pk x.1.message
        x.1.signature) (W.hashOf tab))).1 P
      (tcrPick a.P a.t (traceOf (Extract.verifyQueries (W.hashOf tab) a.pk x.1.message
        x.1.signature) (W.hashOf tab))).2.1
      (tcrPick a.P a.t (traceOf (Extract.verifyQueries (W.hashOf tab) a.pk x.1.message
        x.1.signature) (W.hashOf tab))).2.2)))

/-- The output and the challenger's decision at a fixed table. -/
theorem tcrPost_judge (P : PublicParameter) (a : TcrData) (f : Forgery) (st : TcrSt)
    (log : QueryLog TcrPorts) :
    ((simulateQ (logImpl tab ((tcrGame W).answer P)) (tcrPost W a f st)).run log >>= fun r ↦
      simulateQ (W.eager tab) ((tcrGame W).judge P r.2 r.1)) =
      pure (tcrJudgeDec W tab P a (f, (st, log))) := by
  simp only [tcrPost, simulateQ_bind,
    simulateQ_recVerify (logImpl tab ((tcrGame W).answer P)) (tcrHash W) (W.hashOf tab)
      (simulateQ_logImpl_tcrHash W tab _),
    simulateQ_tcrHashAll, StateT.run_pure, pure_bind, simulateQ_pure, tcrLook_map]
  simp only [tcrGame, Props.smTcr, simulateQ_bind, simulateQ_eval, pure_bind, simulateQ_pure]
  rfl

/-! ## The SM-TCR event makes the decision true -/

/-- **The SM-TCR event gives a witness** of the reduction at digests `t` agreeing with the table
on the key's positions. -/
theorem tcrWit_of_evTcrT {h : HashInput → HashOutput} {v : QTable} {t : RawPos → Digest}
    (ht : ∀ q : Pos, KeyPart q.1 → t q.1 = v.dig q.1) {H : HashInput → Option HashOutput}
    (hT : EvTcrT h v H) :
    ∃ (p : Pos) (d : SlotPayload (keySlot p.1)), TcrWit v.publicSeed t H p d := by
  have hd : ∀ q : RawPos, KeyPart q → (ofDig t).dig q = v.dig q := fun q hq ↦
    (dig_ofDig_congr fun hp hk ↦ ht ⟨q, hp⟩ hk).trans (dig_ofDig_dig v hq)
  have hcv : (ofDig t).chainValue = v.chainValue := by
    funext l τ e i j
    exact chainValue_congr_key fun q hq _ ↦ hd q hq
  have htv : (ofDig t).treeValue = v.treeValue := by
    funext l τ level index
    exact treeValue_congr_key fun q hq _ ↦ hd q hq
  have hfv : (ofDig t).forsValue = v.forsValue := by
    funext idx κ height node
    exact forsValue_congr_key fun q hq _ ↦ hd q hq
  obtain ⟨⟨p, hin⟩, hp, d, hne, o, ho, hdig⟩ := hT
  have hdt : truncateHash o = t p := hdig.trans (ht ⟨p, hin⟩ (tcr_keyPart_of_isTarget hp)).symm
  cases p with
  | leaf l τ e =>
    refine ⟨⟨.leaf l τ e, hin⟩, d, hp, fun h ↦ hne (h.trans ?_), o, ho, hdt⟩
    exact funext fun i ↦ congrArg (fun f ↦ f l τ e i (chainLength - 1)) hcv
  | node l τ level index =>
    refine ⟨⟨.node l τ level index, hin⟩, d, hp, fun h ↦ hne (h.trans ?_), o, ho, hdt⟩
    exact congrArg (fun f ↦ (f l τ level.val (2 * index.val), f l τ level.val
      (2 * index.val + 1))) htv
  | forsNode idx κ level node =>
    refine ⟨⟨.forsNode idx κ level node, hin⟩, d, hp, fun h ↦ hne (h.trans ?_), o, ho, hdt⟩
    exact congrArg (fun f ↦ (f idx κ level.val (2 * node.val), f idx κ level.val
      (2 * node.val + 1))) hfv
  | forsRoots idx =>
    refine ⟨⟨.forsRoots idx, hin⟩, d, hp, fun h ↦ hne (h.trans ?_), o, ho, hdt⟩
    exact funext fun κ ↦ congrArg (fun f ↦ f idx κ forsTreeHeight 0) hfv
  | _ => exact False.elim hp

/-- **The decision is true on the SM-TCR event**: at the routed table, a forgery whose trace
has an SM-TCR win makes the challenger accept the reduction's output against its transcript. -/
theorem tcrJudgeDec_true (P : PublicParameter) (s : KeygenDomain → Digest)
    (r : Message → Digest) (t : RawPos → Digest)
    (htf : ∀ q : Pos, KeyPart q.1 → t q.1 = (digTable (W.hashOf tab) P s r).dig q.1)
    (f : Forgery) (st : TcrSt) (slog : SignLog)
    (hdec : tcrDec (W.hashOf tab) (digTable (W.hashOf tab) P s r) (f, slog) = true) :
    tcrJudgeDec W tab P ⟨P, s, r, t, (digTable (W.hashOf tab) P s r).publicKey⟩
      (f, (st, tcrLog (digTable (W.hashOf tab) P s r).dig P)) = true := by
  have hE := Props.holds_eq_true.mp hdec
  have hW := tcrWit_of_evTcrT htf hE
  rw [publicSeed_digTable] at hW
  obtain ⟨p, d, ⟨hp, hne, o, ho, hot⟩, hpick⟩ := tcrPick_spec hW
  have hpick' : tcrPick P t (traceOf (Extract.verifyQueries (W.hashOf tab)
      (digTable (W.hashOf tab) P s r).publicKey f.message f.signature) (W.hashOf tab)) =
      tcrOutOf p.1 d := hpick
  have hoh : o = W.hashOf tab (slotInput (pubKey P) 0 (keySlot p.1) d) := by
    unfold forgTrace Extract.traceH at ho
    split_ifs at ho
    exact (Option.some.inj ho).symm
  have hkp : keyPayload p.1 t = keyPayload p.1 (digTable (W.hashOf tab) P s r).dig :=
    keyPayload_congr p.1 fun q hq _ ↦ htf q hq
  refine Props.holds_eq_true.mpr ⟨tcrValid_tcrLog _ _, _,
    mem_tcrTargets_tcrLog (digTable (W.hashOf tab) P s r).dig P p hp, ?_, ?_, ?_, ?_⟩
  · rw [hpick']
    rfl
  · rw [hpick']
    rfl
  · rw [hpick']
    intro he
    have h2 := eq_of_heq (Sigma.mk.inj_iff.mp he).2
    exact hne ((tcrKeyMsg_injective hp (congrArg Prod.snd h2)).symm.trans hkp.symm)
  · rw [hpick']
    change (digTable (W.hashOf tab) P s r).dig p.1 = truncateHash (W.hashOf tab
      (tcrColl.layout (tcrFnOf p.1) P (keySlot p.1) (tcrKeyMsg p.1 d)))
    rw [tcrColl_layout_key P p hp d, ← hoh, hot, htf p (tcr_keyPart_of_isTarget hp)]

/-- The invariant of the reduction's run: its data and its transcript stay those of the
setup. -/
def tcrInv (a0 : TcrData) (L0 : QueryLog TcrPorts) (st : TcrSt × QueryLog TcrPorts) : Prop :=
  st.1.1 = a0 ∧ st.2 = L0

/-- The reduction's kernel simulates the signer of the routed table. -/
theorem tcr_hK (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q)) (a0 : TcrData)
    (L0 : QueryLog TcrPorts) (st : TcrSt × QueryLog TcrPorts) (hst : tcrInv a0 L0 st)
    (M : Message) :
    Prod.map id (fun st : TcrSt × QueryLog TcrPorts ↦ st.1.2) <$>
        hKernel tab ans (tcrSigner W) st M =
      detKernel (W.hashOf tab) (digTable (W.hashOf tab) a0.P a0.s a0.r) st.1.2 M := by
  obtain ⟨⟨a, slog⟩, L⟩ := st
  obtain ⟨h1, -⟩ := hst
  dsimp only at h1
  subst h1
  rw [hKernel_tcr, map_pure]
  simp only [detKernel, Prod.map_apply, id_eq]

/-- The reduction's kernel keeps the invariant. -/
theorem tcr_hInv (ans : (q : TcrQ) → OracleComp W.Oracles (TcrPorts.Range q)) (a0 : TcrData)
    (L0 : QueryLog TcrPorts) (st : TcrSt × QueryLog TcrPorts) (hst : tcrInv a0 L0 st)
    (M : Message) :
    ∀ p ∈ support (hKernel tab ans (tcrSigner W) st M), tcrInv a0 L0 p.2 := by
  obtain ⟨⟨a, slog⟩, L⟩ := st
  obtain ⟨h1, h2⟩ := hst
  intro p hp
  rw [hKernel_tcr, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact ⟨h1, h2⟩

/-- **The ideal game at the routed table is at most the reduction's run** read through the
challenger's decision. -/
theorem tcr_game_le (A : SAdv W) (P : PublicParameter) (s : KeygenDomain → Digest)
    (r : Message → Digest) (t : RawPos → Digest)
    (htf : ∀ q : Pos, KeyPart q.1 → t q.1 = (digTable (W.hashOf tab) P s r).dig q.1) :
    gameAt W tab A (digTable (W.hashOf tab) P s r)
        (tcrDec (W.hashOf tab) (digTable (W.hashOf tab) P s r)) ≤
      W.probAt tab ((kRunQ W (hKernel tab ((tcrGame W).answer P) (tcrSigner W))
        (A (digTable (W.hashOf tab) P s r).publicKey)
        ((⟨P, s, r, t, (digTable (W.hashOf tab) P s r).publicKey⟩, []),
          tcrLog (digTable (W.hashOf tab) P s r).dig P)).map
        (tcrJudgeDec W tab P ⟨P, s, r, t, (digTable (W.hashOf tab) P s r).publicKey⟩)) := by
  have hsim := run₂_map_kRunQ_sim (W.runtime tab)
    (detKernel (W.hashOf tab) (digTable (W.hashOf tab) P s r))
    (hKernel tab ((tcrGame W).answer P) (tcrSigner W))
    (tcrInv ⟨P, s, r, t, (digTable (W.hashOf tab) P s r).publicKey⟩
      (tcrLog (digTable (W.hashOf tab) P s r).dig P)) (fun st ↦ st.1.2)
    (fun st hst M ↦ tcr_hK W tab _ _ _ st hst M) (fun st hst M ↦ tcr_hInv W tab _ _ _ st hst M)
    (A (digTable (W.hashOf tab) P s r).publicKey)
    ((⟨P, s, r, t, (digTable (W.hashOf tab) P s r).publicKey⟩, []),
      tcrLog (digTable (W.hashOf tab) P s r).dig P) ⟨rfl, rfl⟩
    (tcrDec (W.hashOf tab) (digTable (W.hashOf tab) P s r))
    (fun x ↦ tcrDec (W.hashOf tab) (digTable (W.hashOf tab) P s r) (x.1, x.2.1.2) &&
      Props.holds (tcrInv ⟨P, s, r, t, (digTable (W.hashOf tab) P s r).publicKey⟩
        (tcrLog (digTable (W.hashOf tab) P s r).dig P) x.2))
    (fun f st hst ↦ by simp only [Props.holds_eq_true.mpr hst, Bool.and_true])
  refine (le_of_eq (probAt_eq_of_run₂ W tab hsim).symm).trans
    ((probAt_map_le_sum W tab _ _ (Finset.univ : Finset Unit)
      (fun _ ↦ tcrJudgeDec W tab P ⟨P, s, r, t, (digTable (W.hashOf tab) P s r).publicKey⟩)
      fun x hx ↦ ⟨(), Finset.mem_univ _, ?_⟩).trans (le_of_eq (by simp)))
  obtain ⟨f, ⟨⟨a, slog⟩, L⟩⟩ := x
  simp only [Bool.and_eq_true, Props.holds_eq_true, tcrInv] at hx
  obtain ⟨hdec, ha, hL⟩ := hx
  subst ha hL
  exact tcrJudgeDec_true W tab P s r t htf f _ slog hdec

end Table

/-! ## The SM-TCR hop -/

/-- The uniform average is monotone. -/
theorem tcr_unifAvg_le {X : Type} [Fintype X] {Φ Ψ : X → ℝ≥0∞} (h : ∀ x, Φ x ≤ Ψ x) :
    unifAvg X Φ ≤ unifAvg X Ψ :=
  mul_le_mul' le_rfl (Finset.sum_le_sum fun x _ ↦ h x)

variable (tab : W.Tab) (A : SAdv W)

/-- **The SM-TCR hop of Theorem 2**: at every table of a world with fair coins, the ideal game
read through the SM-TCR decision is at most the SM-TCR success of `tcrRed W A`. -/
theorem ideal_tcr_le (hW : W.CoinsFair) :
    ideal W tab A (tcrDec (W.hashOf tab)) ≤
      Props.smTcrSucc W tcrColl slotColl tab (tcrRed W A) := by
  have e1 := tcr_succAt_slRed W tab (tcrGame W) (tcrPre W) (fun a ↦ A a.pk) (fun a ↦ (a, []))
    (tcrSigner W) (tcrPost W) (fun P a ↦ tcrJudgeDec W tab P a)
    (fun P a f st log ↦ tcrPost_judge W tab P a f st log)
  change ideal W tab A (tcrDec (W.hashOf tab)) ≤
    (tcrGame W).succAt tab (fun _ ↦ slRed W (tcrPre W) (fun a ↦ A a.pk) (fun a ↦ (a, []))
      (tcrSigner W) (tcrPost W))
  rw [e1]
  refine le_of_le_of_eq ?_ (tsum_sample_mul W tab hW (α := PublicParameter) _).symm
  unfold ideal
  refine tcr_unifAvg_le fun P ↦ ?_
  rw [run_tcrPre W tab hW, tsum_prEvent_bind_mul, tsum_prEvent_uniformSample]
  refine tcr_unifAvg_le fun s ↦ ?_
  rw [tsum_prEvent_bind_mul, tsum_prEvent_uniformSample]
  refine tcr_unifAvg_le fun r ↦ ?_
  obtain ⟨tf, htf, hrun⟩ := run_tcrRest W tab P s r
  rw [hrun, tsum_prEvent_pure_mul]
  exact tcr_game_le W tab A P s r tf htf

/-! ## Charges -/

/-- **B6's hash calls**: `A`'s hash calls plus the honest work of the setup (`c₀`), of each
signing request (`k`) and of the output (`c₁`). -/
theorem isChargeBound_tcrRed {c₀ c₁ k n m : ℕ}
    (hpre : Common.QueryCostAtMost (tcrPre W) (hcallCost W (R' := TcrPorts)) c₀)
    (hσ : ∀ st M, Common.QueryCostAtMost (tcrSigner W st M) (hcallCost W (R' := TcrPorts)) k)
    (hpost : ∀ a f st,
      Common.QueryCostAtMost (tcrPost W a f st) (hcallCost W (R' := TcrPorts)) c₁)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (tcrRed W A u) (cmdCharge hashCharge) (c₀ + ((n + k * m) + c₁)) :=
  isChargeBound_slRed_hash W _ _ _ _ _ hpre hσ hpost (fun a ↦ hn a.pk) fun a ↦ hm a.pk

/-- A world program makes no challenger query. -/
theorem tcr_queryCostAtMost_liftW {α : Type} (oa : OracleComp W.Oracles α) (b : ℕ) :
    Common.QueryCostAtMost (liftW TcrPorts oa) (portCost W (R' := TcrPorts)) b := by
  unfold liftW
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [simulateQ_pure]
    trivial
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (OracleComp.isQueryBound_query_bind_iff _ _ _ _ _).mpr ⟨Nat.zero_le _, ih⟩

theorem tcr_queryCostAtMost_portQ (q : TcrQ) :
    Common.QueryCostAtMost (portQ W TcrPorts q) (portCost W (R' := TcrPorts)) 1 :=
  (OracleComp.isQueryBound_query_iff _ _ _ _).mpr le_rfl

/-- An ask makes at most one challenger query. -/
theorem tcr_queryCostAtMost_tcrAsk (s : KeygenDomain → Digest) (p : RawPos)
    (t : RawPos → Digest) :
    Common.QueryCostAtMost (tcrAsk W s p t) (portCost W (R' := TcrPorts)) 1 := by
  unfold tcrAsk
  by_cases hg : tcrIsTgt p = true
  · simp only [hg, ↓reduceIte]
    exact tcr_queryCostAtMost_portQ W _
  · have hg' : tcrIsTgt p = false := by simpa using hg
    simp only [hg', Bool.false_eq_true, ↓reduceIte]
    rcases tcrSecOf p with _ | k <;> dsimp only
    · exact tcr_queryCostAtMost_portQ W _
    · trivial

omit W in
/-- A build of asks of cost at most one costs at most the number of positions. -/
theorem tcr_queryCostAtMost_foldlM {ι : Type} {O : OracleSpec.{0, 0} ι} (w : ι → ℕ)
    (ask : RawPos → (RawPos → Digest) → OracleComp O Digest)
    (hask : ∀ p t, Common.QueryCostAtMost (ask p t) w 1) :
    ∀ (L : List Pos) (t : RawPos → Digest),
      Common.QueryCostAtMost (L.foldlM (buildStep ask) t) w L.length
  | [], _ => trivial
  | p :: L, t => by
    rw [List.foldlM_cons, List.length_cons, Nat.add_comm]
    refine Common.QueryCostAtMost.bind ?_ fun t' ↦ tcr_queryCostAtMost_foldlM w ask hask L t'
    show Common.QueryCostAtMost (buildStep ask t p) w 1
    unfold buildStep
    exact Common.QueryCostAtMost.bind (a := 1) (b := 0) (hask p.1 t) fun _ ↦ trivial

omit W in
/-- A recorded computation over a hash without queries of cost makes none. -/
theorem tcr_queryCostAtMost_recImpl {ι : Type} {O : OracleSpec.{0, 0} ι} (w : ι → ℕ)
    (hash : HashInput → OracleComp O HashOutput)
    (hh : ∀ y, Common.QueryCostAtMost (hash y) w 0) {α : Type}
    (x : OracleComp Common.SufCma.SchemeHashSpec α) (l : List HashInput) :
    Common.QueryCostAtMost ((simulateQ (recImpl hash) x).run l) w 0 := by
  induction x using OracleComp.inductionOn generalizing l with
  | pure a =>
    rw [simulateQ_pure, StateT.run_pure]
    trivial
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hq : (recImpl hash t).run l = (fun o ↦ (o, l ++ [t])) <$> hash t := by
      simp [recImpl, StateT.run_bind, StateT.run_monadLift, StateT.run_modify]
    rw [hq]
    exact Common.QueryCostAtMost.bind (a := 0) (b := 0)
      ((OracleComp.isQueryBound_map_iff _ _ _ _ _).mpr (hh t))
      fun (p : HashOutput × List HashInput) ↦ ih p.1 p.2

theorem tcr_keygen_liftW (P : PublicParameter) (s : KeygenDomain → Digest)
    (r : Message → Digest) :
    Qrom.Sphincs.LeanSphincsOver.keygenFromSeed
        (routeHash P (fun d ↦ pure (s d)) (fun M ↦ pure (r M)) (tcrHash W)) 0 =
      liftW TcrPorts (Qrom.Sphincs.LeanSphincsOver.keygenFromSeed
        (routeHash P (fun d ↦ pure (s d)) (fun M ↦ pure (r M)) W.hash) 0) := by
  simp only [liftW, Over.simulateQ_keygenFromSeed, simulateQ_routeHash, simulateQ_pure]
  rfl

theorem tcr_sign_liftW (P : PublicParameter) (s : KeygenDomain → Digest) (r : Message → Digest)
    (M : Message) :
    Qrom.Sphincs.LeanSphincsOver.sign
        (routeHash P (fun d ↦ pure (s d)) (fun M ↦ pure (r M)) (tcrHash W)) 0 M =
      liftW TcrPorts (Qrom.Sphincs.LeanSphincsOver.sign
        (routeHash P (fun d ↦ pure (s d)) (fun M ↦ pure (r M)) W.hash) 0 M) := by
  simp only [liftW, Over.simulateQ_sign, simulateQ_routeHash, simulateQ_pure]
  rfl

theorem tcr_queryCostAtMost_keygen (P : PublicParameter) (s : KeygenDomain → Digest)
    (r : Message → Digest) :
    Common.QueryCostAtMost (Qrom.Sphincs.LeanSphincsOver.keygenFromSeed
      (routeHash P (fun d ↦ pure (s d)) (fun M ↦ pure (r M)) (tcrHash W)) 0)
      (portCost W (R' := TcrPorts)) 0 := by
  rw [tcr_keygen_liftW]
  exact tcr_queryCostAtMost_liftW W _ 0

/-- **B6's setup queries**: one per key position and the reveal. -/
theorem queryCostAtMost_tcrPre :
    Common.QueryCostAtMost (tcrPre W) (portCost W (R' := TcrPorts)) (keyOrder.length + 1) := by
  have hrest : ∀ s r, Common.QueryCostAtMost (tcrRest W s r) (portCost W (R' := TcrPorts))
      (keyOrder.length + (1 + (0 + 0))) := by
    intro s r
    unfold tcrRest
    refine Common.QueryCostAtMost.bind (a := keyOrder.length)
      (tcr_queryCostAtMost_foldlM _ _ (tcr_queryCostAtMost_tcrAsk W s) keyOrder _) fun t ↦ ?_
    refine Common.QueryCostAtMost.bind (a := 1) (tcr_queryCostAtMost_portQ W _) fun P ↦ ?_
    exact Common.QueryCostAtMost.bind (a := 0) (b := 0) (tcr_queryCostAtMost_keygen W P s r)
      fun _ ↦ trivial
  exact (Common.QueryCostAtMost.bind (a := 0) (tcr_queryCostAtMost_liftW W _ 0) fun s ↦
    Common.QueryCostAtMost.bind (a := 0) (tcr_queryCostAtMost_liftW W _ 0) fun r ↦
      hrest s r).mono (by omega)

/-- B6's signer makes no challenger query. -/
theorem queryCostAtMost_tcrSigner (st : TcrSt) (M : Message) :
    Common.QueryCostAtMost (tcrSigner W st M) (portCost W (R' := TcrPorts)) 0 := by
  unfold tcrSigner
  rw [tcr_sign_liftW]
  exact Common.QueryCostAtMost.bind (a := 0) (b := 0) (tcr_queryCostAtMost_liftW W _ 0)
    fun _ ↦ trivial

theorem queryCostAtMost_tcrHashAll :
    ∀ xs : List HashInput,
      Common.QueryCostAtMost (tcrHashAll W xs) (portCost W (R' := TcrPorts)) 0
  | [] => trivial
  | _ :: xs => Common.QueryCostAtMost.bind (a := 0) (b := 0) (tcr_queryCostAtMost_liftW W _ 0)
      fun _ ↦ Common.QueryCostAtMost.bind (a := 0) (b := 0) (queryCostAtMost_tcrHashAll xs)
        fun _ ↦ trivial

/-- B6's output makes no challenger query. -/
theorem queryCostAtMost_tcrPost (a : TcrData) (forg : Forgery) (st : TcrSt) :
    Common.QueryCostAtMost (tcrPost W a forg st) (portCost W (R' := TcrPorts)) 0 :=
  Common.QueryCostAtMost.bind (a := 0) (b := 0) (tcr_queryCostAtMost_recImpl _ (tcrHash W)
    (fun _ ↦ tcr_queryCostAtMost_liftW W _ 0) _ []) fun rv ↦
    Common.QueryCostAtMost.bind (a := 0) (b := 0) (queryCostAtMost_tcrHashAll W rv.2)
      fun _ ↦ trivial

/-- **B6's challenger queries**: one per key position and the reveal in the setup, none per
signing request of `A` and none in the output. -/
theorem isChargeBound_tcrRed_call {m : ℕ}
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (tcrRed W A u) (cmdCharge callCharge)
      ((keyOrder.length + 1) + (0 * m + 0)) :=
  isChargeBound_slRed_call W _ _ _ _ _ (queryCostAtMost_tcrPre W)
    (fun st M ↦ queryCostAtMost_tcrSigner W st M) (fun a f st ↦ queryCostAtMost_tcrPost W a f st)
    fun a ↦ hm a.pk

end Quantum.StdModel.Sphincs

end
