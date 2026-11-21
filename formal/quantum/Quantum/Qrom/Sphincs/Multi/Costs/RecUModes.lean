module

public import Quantum.Qrom.Sphincs.Multi.GameTSel
public import Quantum.Qrom.Sphincs.Multi.GameTFactsPre
public import Quantum.Qrom.Sphincs.Costs.RecUMove

@[expose] public section

/-!
# The counter searches of the `n`-user challenge prefix, as moded programs

The `n`-user analog of `Quantum.Qrom.Sphincs.Costs.RecUModes`. The modes: between searches
(`rest`), or in the search of user `i`'s key `K` on the value `m` before trial `j` (`grd`); both
carry the users' keys whose search was started or memoized. A reveal of the single coordinate
`(i, vcoord (msgPos K))` of user `i`'s key starts its search from the revealed value; a trial read
whose digest is a codeword ends it, otherwise the next trial follows; the other calls (sponge
calls, programs off every encoding slot, reveals without a key's coordinate outside the started
keys) happen only between searches. A memo hit makes no call; its key was started by the earlier
request that memoized it.

* `keyOfTSN`, `RevOkSN`, `ModeSN`, `ModeSN.Rest`, `revNxSN`.
* The allowed calls and the mode after a call on runtime 1's ports (`srchOkRSN`, `srchNxRSN`), the
  template's (`srchOkTSN`, `srchNxTSN`) and runtime 2's with record ports (`srchOkZSN`,
  `srchNxZSN`).
* **`modedP_prefixQSN`**: the realized challenge prefix `prefixQSN pols A θ` is moded from `rest ∅`,
  user `i`'s trials under user `i`'s `PK.seed` (`parQSN θ i`), ending between searches.
* `ReRevQSN`, `reRevQWSN`: the repeated reveals of a key's coordinate with the key unselected.
-/

open Matrix IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

universe u v w

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Xmss.Hybrid (restrictTo LazyProg diagMass)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals liftRead tmplLens readLens ModedP modedP_bind modedP₂_bind modedP_map
  modeCmdOk modeCmdNx realizeT_bind realizeT_bind₂ realizeT_substitute)
open Quantum.Qrom.SufCma.Multi (muAdvSpec)

attribute [local irreducible] sphincsRom Fin.fintype

/- Instance search for the register's memory exceeds the default size. -/
set_option synthInstance.maxSize 2000

variable {n : ℕ}

-- The adversary's commands, as indexed polynomial functors.
set_option quotPrecheck false in
local notation "MuPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n Message (Option Signature))

/-- **User `i`'s `PK.seed`** at the hidden values `θ`. -/
def parQSN (θ : TValsN n) : Fin n → PublicParameter :=
  fun i ↦ (tabOf (userOf θ i)).publicSeed

/-! ## The key of a reveal -/

/-- **User `i`'s key of a reveal** of the single coordinate `(i, vcoord (msgPos K))` a key of the
signatures signs (decided classically). -/
noncomputable def keyOfTSN (T : Finset (TPosN n)) : Option (Fin n × Key) :=
  @dite _ (∃ k : Fin n × Key, InRangeU k.2 ∧ T = atU k.1 {vcoord (msgPos k.2)})
    (Classical.propDecidable _) (fun h ↦ some h.choose) fun _ ↦ none

theorem keyOfTSN_spec {T : Finset (TPosN n)} {i : Fin n} {K : Key}
    (h : keyOfTSN T = some (i, K)) : InRangeU K ∧ T = atU i {vcoord (msgPos K)} := by
  unfold keyOfTSN at h
  split_ifs at h with h'
  obtain ⟨h1, h2⟩ := h'.choose_spec
  have e := Option.some.inj h
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

theorem keyOfTSN_atU {K : Key} (hK : InRangeU K) (i : Fin n) :
    keyOfTSN (atU i {vcoord (msgPos K)}) = some (i, K) := by
  have hs : ∀ (j : Fin n) (s : TPos), atU j {s} = {(j, s)} :=
    fun _ _ ↦ Finset.singleton_product_singleton
  unfold keyOfTSN
  split_ifs with h'
  · obtain ⟨hK', he⟩ := h'.choose_spec
    have e' : (i, vcoord (msgPos K)) = (h'.choose.1, vcoord (msgPos h'.choose.2)) :=
      Finset.singleton_injective ((hs _ _).symm.trans (he.trans (hs _ _)))
    exact congrArg some (Prod.ext (congrArg Prod.fst e').symm
      (vcoord_msgPos_injU hK' hK (congrArg Prod.snd e').symm))
  · exact absurd ⟨(i, K), hK, rfl⟩ h'

theorem keyOfTSN_eq_none {T : Finset (TPosN n)} {s : TPosN n} (hs : s ∈ T) (hn : NotMcU s.2) :
    keyOfTSN T = none := by
  rcases h : keyOfTSN T with _ | ⟨i, K⟩
  · rfl
  · obtain ⟨hK, rfl⟩ := keyOfTSN_spec h
    exact absurd (Finset.mem_singleton.1 (mem_atU_iff.1 hs).2) (hn K hK)

theorem keyOfTSN_eq_none_of {T : Finset (TPosN n)} (h : ∀ s ∈ T, NotMcU s.2) :
    keyOfTSN T = none := by
  rcases hk : keyOfTSN T with _ | ⟨i, K⟩
  · rfl
  · obtain ⟨hK, rfl⟩ := keyOfTSN_spec hk
    exact absurd rfl (h _ (mk_mem_atU i (Finset.mem_singleton_self _)) K hK)

/-- **A reveal the searches allow between searches**, with the started keys `ks`: the coordinates
of users' keys of the signatures it reveals are of started keys. -/
def RevOkSN (ks : Finset (Fin n × Key)) (T : Finset (TPosN n)) : Prop :=
  ∀ i K, InRangeU K → (i, vcoord (msgPos K)) ∈ T → (i, K) ∈ ks

theorem revOkSN_of_notMc {ks : Finset (Fin n × Key)} {T : Finset (TPosN n)}
    (h : ∀ s ∈ T, NotMcU s.2) : RevOkSN ks T :=
  fun _ K hK hm ↦ absurd rfl (h _ hm K hK)

/-! ## The modes -/

/-- **The modes of the counter searches**: between searches; in the search of user `i`'s key `K`
on the value `m` before trial `j`. Both carry the users' keys whose search was started. -/
inductive ModeSN (n : ℕ)
  | rest (ks : Finset (Fin n × Key))
  | grd (ks : Finset (Fin n × Key)) (i : Fin n) (K : Key) (m : Digest) (j : ℕ)

/-- The users' keys whose search was started. -/
def ModeSN.ks : ModeSN n → Finset (Fin n × Key)
  | .rest ks => ks
  | .grd ks _ _ _ _ => ks

/-- A mode between searches: `rest`, or after the last trial. -/
def ModeSN.Rest : ModeSN n → Prop
  | .rest _ => True
  | .grd _ _ _ _ j => j = encodingAttemptLimit

/-- **The mode after a reveal of `T`**, the values given by `val`: the search of its user's key
from its value, between searches otherwise. -/
noncomputable def revNxSN (μ : ModeSN n) (T : Finset (TPosN n)) (val : Fin n → Key → Digest) :
    ModeSN n :=
  match keyOfTSN T with
  | some (i, K) => .grd (insert (i, K) μ.ks) i K (val i K) 0
  | none => .rest μ.ks

theorem revNxSN_congr (μ : ModeSN n) {T : Finset (TPosN n)} {val val' : Fin n → Key → Digest}
    (h : ∀ i K, keyOfTSN T = some (i, K) → val i K = val' i K) :
    revNxSN μ T val = revNxSN μ T val' := by
  unfold revNxSN
  rcases hT : keyOfTSN T with _ | ⟨i, K⟩
  · rfl
  · exact congrArg (fun m ↦ ModeSN.grd (insert (i, K) μ.ks) i K m 0) (h i K hT)

theorem revNxSN_atU (μ : ModeSN n) {K : Key} (hK : InRangeU K) (i : Fin n)
    (val : Fin n → Key → Digest) :
    revNxSN μ (atU i {vcoord (msgPos K)}) val = .grd (insert (i, K) μ.ks) i K (val i K) 0 := by
  unfold revNxSN
  rw [keyOfTSN_atU hK i]

theorem revNxSN_none (μ : ModeSN n) {T : Finset (TPosN n)} (h : keyOfTSN T = none)
    (val : Fin n → Key → Digest) : revNxSN μ T val = .rest μ.ks := by
  unfold revNxSN
  rw [h]

/-- The mode after a trial with the decoded digest `d`: between searches after a codeword, the
next trial otherwise. -/
def decNxSN (ks : Finset (Fin n × Key)) (i : Fin n) (K : Key) (m : Digest) (j : ℕ) :
    Option Encoding → ModeSN n
  | some _ => .rest ks
  | none => .grd ks i K m (j + 1)

variable (P : Fin n → PublicParameter)

/-- **The trial read a mode allows**: in the search of user `i`'s `K` on `m` before trial
`j < 2^32`, the trial read of trial `j`'s encoding cell under user `i`'s `PK.seed`. -/
def srchRdOkSN : ModeSN n → HwRead PairOut HashDomain (Finset (TPosN n) × SelMemN n) → Prop
  | .grd _ i K m j, c => j < encodingAttemptLimit ∧ c = trialReadSN (trialCell (P i) K m j) (i, K)
  | .rest _, _ => False

/-- **The mode after a read**: the decoded digest decides (`decNxSN`). -/
def srchRdNxSN {M' : Type} : ModeSN n → (c : HwRead PairOut HashDomain M') → c.Result → ModeSN n
  | .grd ks i K m j, .readH _ _, r =>
      decNxSN ks i K m j (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1))
  | μ, _, _ => .rest μ.ks

/-- **A program the searches allow**: an `h`-cell off the encoding slots under every key. -/
def ProgOkSN (c : HwProg PairOut HashDomain) : Prop :=
  ∃ z a, c = .programH z a ∧
    ∀ (pk : PublicKey) (K : Key), slotOf pk z ≠ some (.enc K.1 K.2.1 K.2.2)

/-- The calls the modes allow, on runtime 1's ports. -/
def srchOkRSN : ModeSN n → (hwReadSpec PairOut HashDomain (SelMemN n)).Port → Prop
  | μ, .inl _ => μ.Rest
  | μ, .inr c => srchRdOkSN P μ (liftRead (S := TPosN n) c)

/-- The mode after a call of runtime 1. -/
def srchNxRSN : ModeSN n → (i : (hwReadSpec PairOut HashDomain (SelMemN n)).Port) →
    (hwReadSpec PairOut HashDomain (SelMemN n)).Result i → ModeSN n
  | μ, .inr c, r => srchRdNxSN μ c r
  | μ, .inl _, _ => .rest μ.ks

/-- The calls the modes allow, on the template's ports. -/
def srchOkTSN : ModeSN n → (XSpecSN (SelMemN n) n).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => srchRdOkSN P μ c.1
  | μ, .inl (.inr p) => μ.Rest ∧ ∀ θ, ProgOkSN (p.1.realize θ)
  | μ, .inr T => μ.Rest ∧ (keyOfTSN T = none → RevOkSN μ.ks T)

/-- The mode after a call of the template: a reveal of a user's key's coordinate starts its
search. -/
noncomputable def srchNxTSN : ModeSN n → (i : (XSpecSN (SelMemN n) n).Port) →
    (XSpecSN (SelMemN n) n).Result i → ModeSN n
  | μ, .inl (.inl (.inr c)), r => srchRdNxSN μ c.1 r
  | μ, .inr T, r => revNxSN μ T fun i K ↦ (tabRN r.1 i).valuePos (msgPos K)
  | μ, _, _ => .rest μ.ks

/-- **The calls the modes allow**, on runtime 2's ports with record ports: user `i`'s trials
under `P i`. -/
def srchOkZSN : ModeSN n → (RSpecSN n (SelMemN n)).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => srchRdOkSN P μ c
  | μ, .inl (.inr c) => μ.Rest ∧ ProgOkSN c
  | μ, .inr T => μ.Rest ∧ (keyOfTSN T = none → RevOkSN μ.ks T)

/-- **The mode after a call** of runtime 2 with record ports, at the hidden values `θ`. -/
noncomputable def srchNxZSN (θ : TValsN n) : ModeSN n → (i : (RSpecSN n (SelMemN n)).Port) →
    (RSpecSN n (SelMemN n)).Result i → ModeSN n
  | μ, .inl (.inl (.inr c)), r => srchRdNxSN μ c r
  | μ, .inr T, _ => revNxSN μ T fun i K ↦ (tabOf (userOf θ i)).valuePos (msgPos K)
  | μ, _, _ => .rest μ.ks

/-! ## Moded programs -/

/-- Sequencing two parts that keep the started keys between searches. -/
theorem modedP_bind_keepSN {spec : QuantumOracleSpec.{0, 0}} {ok : ModeSN n → spec.Port → Prop}
    {nx : ModeSN n → (i : spec.Port) → spec.Result i → ModeSN n} {A B B' : QReg} {α β : Type}
    (x : QuantumComp₂ LocalSig.instruments spec A B α)
    (g : α → QuantumComp₂ LocalSig.instruments spec B B' β) {μ : ModeSN n}
    (hx : ModedP ok nx (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ x)
    (hg : ∀ a μ', μ'.Rest → μ.ks ⊆ μ'.ks →
      ModedP ok nx (fun _ μ'' ↦ μ''.Rest ∧ μ'.ks ⊆ μ''.ks) μ' (g a)) :
    ModedP ok nx (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ (x.bind g) :=
  modedP₂_bind (F := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks)
    (F' := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) x g hx fun a μ' h ↦
      modedP_monoU (fun _ _ h' ↦ ⟨h'.1, h.2.trans h'.2⟩) _ _ (hg a μ' h.1 h.2)

variable {P}

/-! ### Runtime 1's searches -/

/-- **User `i`'s counter search** of `K` on `m`, from trial `j` to the last, ends between
searches with the started keys kept. -/
theorem modedP_grindTSN (B : QReg) (ks : Finset (Fin n × Key)) (i : Fin n) (K : Key)
    (m : Digest) : ∀ k j, j + k = encodingAttemptLimit →
      ModedP (L := LocalSig.instruments) (srchOkRSN P) srchNxRSN
        (fun _ (μ : ModeSN n) ↦ μ.Rest ∧ μ.ks = ks) (.grd ks i K m j)
        (grindT (SelMemN n) (cwUpdN i) (P i) B K m k j)
  | 0, j, hk => ⟨(Nat.add_zero j).symm.trans hk, rfl⟩
  | k + 1, j, hk => by
    have hj : j < encodingAttemptLimit := by omega
    have ih := modedP_grindTSN B ks i K m k (j + 1) (by omega)
    rw [grindT]
    generalize hz : trialCell (P i) K m j = z
    have hr : srchRdOkSN P (.grd ks i K m j)
        (liftRead (S := TPosN n) (.readH z (cwUpdN i K z))) :=
      ⟨hj, by rw [← hz]; rfl⟩
    refine ⟨hr, fun b ↦ ⟨trivial, fun _ ↦ ?_⟩⟩
    show ModedP _ _ _
      (decNxSN ks i K m j (TargetSum.decodeDigest (truncateHash (b.down.1.getD 0).1)))
      (match TargetSum.decodeDigest (truncateHash (b.down.1.getD 0).1) with
        | some x => QuantumComp₂.pure (some (BitVec.ofNat counterBits j, x))
        | none => grindT (SelMemN n) (cwUpdN i) (P i) B K m k (j + 1))
    generalize TargetSum.decodeDigest (truncateHash (b.down.1.getD 0).1) = dd
    cases dd with
    | none => exact ih
    | some x => exact ⟨trivial, rfl⟩

/-- **Lifting runtime 1's moded programs to templates.** -/
theorem modedP_readLiftSN {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → ModeSN n → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec PairOut HashDomain (SelMemN n)) Ω A)
    {μ : ModeSN n} (hy : ModedP (srchOkRSN P) srchNxRSN fin μ y) :
    ModedP (srchOkTSN P) srchNxTSN fin μ (readLift goodQN y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodQN) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with ks | ⟨ks, i, K, m, j⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- A sponge program of runtime 1 runs between searches, the started keys kept. -/
theorem modedP_liftOrdinarySN {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec PairOut HashDomain) Ω A) :
    ∀ μ : ModeSN n, μ.Rest →
      ModedP (srchOkRSN P) srchNxRSN (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ
        (y.liftOrdinary (t := hwReadCmdSpec PairOut HashDomain (SelMemN n))) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun _ h ↦ ⟨h, subset_rfl⟩
  | liftBind _ c next ih =>
    intro μ hμ
    show ModedP _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ μ hμ⟩
    · exact ⟨hμ, fun b ↦ ih _ (.rest μ.ks) trivial⟩

/-! ### Realizing -/

theorem srchNxZSN_rec_eq (θ : TValsN n) (μ : ModeSN n) (T : Finset (TPosN n))
    (m : Finset (TPosN n) × SelMemN n) :
    srchNxZSN θ μ (.inr T) m = srchNxTSN μ (.inr T) (restrictTo T θ, m) :=
  revNxSN_congr μ fun i K hK ↦ by
    have hm : (i, vcoord (msgPos K)) ∈ T := by
      rw [(keyOfTSN_spec hK).2]
      exact mk_mem_atU i (Finset.mem_singleton_self _)
    exact (valuePos_tabOf_congr (msgPos K) (pairRN_restrictTo hm θ)).symm

/-- **Realizing keeps the modes.** -/
theorem modedP_realizeTSN (θ : TValsN n) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → ModeSN n → Prop} (y : QuantumComp L (XSpecSN (SelMemN n) n) Ω A)
    {μ : ModeSN n} (hy : ModedP (srchOkTSN P) srchNxTSN fin μ y) :
    ModedP (srchOkZSN P) (srchNxZSN θ) fin μ (realizeT θ y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (tmplLens θ) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨⟨hy.1.1, hy.1.2 θ⟩, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      have h := ih _ (hy.2 (ULift.up (restrictTo T θ, b.down)))
      exact (congrArg (fun μ' ↦ ModedP (srchOkZSN P) (srchNxZSN θ) fin μ' _)
        (srchNxZSN_rec_eq θ μ T b.down)).mpr h

/-- **A realized reveal**: the record port, then the continuation at the values of `θ`. -/
theorem modedP_realizeT_revealThenSN (θ : TValsN n) {B B' : QReg} {α : Type}
    {T : Finset (TPosN n)}
    {k : RevealVals (TValN n) T × (Finset (TPosN n) × SelMemN n) →
      QComp (XSpecSN (SelMemN n) n) B B' α} {F : α → ModeSN n → Prop}
    {μ : ModeSN n} (hok : srchOkZSN P μ (.inr T))
    (hk : ∀ mem, ModedP (srchOkZSN P) (srchNxZSN θ) (fun p μ ↦ F p.2.2 μ)
      (srchNxZSN θ μ (.inr T) mem) (realizeT θ (k (restrictTo T θ, mem)))) :
    ModedP (srchOkZSN P) (srchNxZSN θ) (fun p μ ↦ F p.2.2 μ) μ
      (realizeT θ (revealThen goodQN T k)) := by
  have e : realizeT θ (revealThen goodQN T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments) (spec := RSpecSN n (SelMemN n))
        (.inr T) B (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((RSpecSN n (SelMemN n)).Out (.inr T) × B)) (B := B)
            (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  rw [e]
  refine ⟨hok, fun b ↦ modedP₂_bind (F := fun _ μ' ↦ μ' = srchNxZSN θ μ (.inr T) b.down) _ _
    ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ ?_⟩
  subst h
  exact hk b.down

/-- A realized reveal of no key's coordinate, between searches. -/
theorem modedP_realizeT_revealThen_noneSN (θ : TValsN n) {B B' : QReg} {α : Type}
    {T : Finset (TPosN n)} (hT : keyOfTSN T = none)
    {k : RevealVals (TValN n) T × (Finset (TPosN n) × SelMemN n) →
      QComp (XSpecSN (SelMemN n) n) B B' α} {F : α → ModeSN n → Prop}
    {μ : ModeSN n} (hμ : μ.Rest) (hR : RevOkSN μ.ks T)
    (hk : ∀ mem, ModedP (srchOkZSN P) (srchNxZSN θ) (fun p μ ↦ F p.2.2 μ) (.rest μ.ks)
      (realizeT θ (k (restrictTo T θ, mem)))) :
    ModedP (srchOkZSN P) (srchNxZSN θ) (fun p μ ↦ F p.2.2 μ) μ
      (realizeT θ (revealThen goodQN T k)) :=
  modedP_realizeT_revealThenSN θ ⟨hμ, fun _ ↦ hR⟩ fun mem ↦ by
    rw [show srchNxZSN θ μ (.inr T) mem = .rest μ.ks from revNxSN_none μ hT _]
    exact hk mem

theorem modedP_realizeT_bindSN (θ : TValsN n) {Ω Ω' : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments (XSpecSN (SelMemN n) n) Ω A)
    (g : ∀ u, Ω u → QuantumComp LocalSig.instruments (XSpecSN (SelMemN n) n) Ω' u)
    {fin : (Σ u, Ω u) → ModeSN n → Prop} {fin' : (Σ u, Ω' u) → ModeSN n → Prop}
    {μ : ModeSN n} (hx : ModedP (srchOkZSN P) (srchNxZSN θ) fin μ (realizeT θ x))
    (hg : ∀ u a μ', fin ⟨u, a⟩ μ' → ModedP (srchOkZSN P) (srchNxZSN θ) fin' μ'
      (realizeT θ (g u a))) :
    ModedP (srchOkZSN P) (srchNxZSN θ) fin' μ (realizeT θ (x.bind g)) := by
  rw [realizeT_bind]
  exact modedP_bind _ _ hx hg

theorem modedP_realizeT_bind₂SN (θ : TValsN n) {A B C : QReg} {α β : Type}
    (x : QComp (XSpecSN (SelMemN n) n) A B α) (k : α → QComp (XSpecSN (SelMemN n) n) B C β)
    {F : α → ModeSN n → Prop} {F' : β → ModeSN n → Prop} {μ : ModeSN n}
    (hx : ModedP (srchOkZSN P) (srchNxZSN θ) (fun p μ ↦ F p.2.2 μ) μ (realizeT θ x))
    (hk : ∀ a μ', F a μ' → ModedP (srchOkZSN P) (srchNxZSN θ) (fun p μ ↦ F' p.2.2 μ) μ'
      (realizeT θ (k a))) :
    ModedP (srchOkZSN P) (srchNxZSN θ) (fun p μ ↦ F' p.2.2 μ) μ (realizeT θ (x.bind k)) := by
  rw [realizeT_bind₂]
  exact modedP₂_bind _ _ hx hk

/-! ### The template's parts -/

variable (P) in
/-- **A template moded between searches**: from every mode between searches it ends between
searches, the started keys kept. -/
def SRestSN {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (XSpecSN (SelMemN n) n) Ω A) : Prop :=
  ∀ μ : ModeSN n, μ.Rest → ModedP (srchOkTSN P) srchNxTSN (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ y

theorem sRestSN_bind {A B B' : QReg} {α β : Type} (x : QComp (XSpecSN (SelMemN n) n) A B α)
    (g : α → QComp (XSpecSN (SelMemN n) n) B B' β) (hx : SRestSN P x)
    (hg : ∀ a, SRestSN P (g a)) : SRestSN P (x.bind g) :=
  fun μ hμ ↦ modedP_bind_keepSN x g (hx μ hμ) fun a μ' h _ ↦ hg a μ' h

theorem sRestSN_pure {A : QReg} {α : Type} (a : α) :
    SRestSN P (QuantumComp₂.pure (L := LocalSig.instruments) (spec := XSpecSN (SelMemN n) n)
      (A := A) a) :=
  fun _ h ↦ ⟨h, subset_rfl⟩

/-- A template reveal: the reveal port, then the continuation. -/
theorem modedP_revealThenSN {B B' : QReg} {α : Type} {T : Finset (TPosN n)}
    {F : α → ModeSN n → Prop}
    {k : RevealVals (TValN n) T × (Finset (TPosN n) × SelMemN n) →
      QComp (XSpecSN (SelMemN n) n) B B' α} {μ : ModeSN n}
    (hok : srchOkTSN P μ (.inr T))
    (hk : ∀ r, ModedP (srchOkTSN P) srchNxTSN (fun p μ ↦ F p.2.2 μ) (srchNxTSN μ (.inr T) r)
      (k r)) :
    ModedP (srchOkTSN P) srchNxTSN (fun p μ ↦ F p.2.2 μ) μ (revealThen goodQN T k) := by
  refine ⟨hok, fun b ↦ modedP₂_bind (F := fun _ μ' ↦ μ' = srchNxTSN μ (.inr T) b.down) _ _
    ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ ?_⟩
  subst h
  exact hk b.down

/-- A template reveal of no key's coordinate, between searches. -/
theorem modedP_revealThen_noneSN {B B' : QReg} {α : Type} {T : Finset (TPosN n)}
    (hT : keyOfTSN T = none) {F : α → ModeSN n → Prop}
    {k : RevealVals (TValN n) T × (Finset (TPosN n) × SelMemN n) →
      QComp (XSpecSN (SelMemN n) n) B B' α} {μ : ModeSN n} (hμ : μ.Rest)
    (hR : RevOkSN μ.ks T)
    (hk : ∀ r, ModedP (srchOkTSN P) srchNxTSN (fun p μ ↦ F p.2.2 μ) (.rest μ.ks) (k r)) :
    ModedP (srchOkTSN P) srchNxTSN (fun p μ ↦ F p.2.2 μ) μ (revealThen goodQN T k) :=
  modedP_revealThenSN ⟨hμ, fun _ ↦ hR⟩ fun r ↦ by
    rw [show srchNxTSN μ (.inr T) r = .rest μ.ks from revNxSN_none μ hT _]
    exact hk r

/-- A template program port off the encoding slots, between searches. -/
theorem modedP_progThenSN {B B' : QReg} {α : Type}
    (p : LazyProg PairOut HashDomain (TPosN n) (TValN n)) (hp : ∀ θ, ProgOkSN (p.realize θ))
    {F : α → ModeSN n → Prop} (k : QComp (XSpecSN (SelMemN n) n) B B' α) {μ : ModeSN n}
    (hμ : μ.Rest)
    (hk : ModedP (srchOkTSN P) srchNxTSN (fun p μ ↦ F p.2.2 μ) (.rest μ.ks) k) :
    ModedP (srchOkTSN P) srchNxTSN (fun p μ ↦ F p.2.2 μ) μ (progThen p trivial k) := by
  refine ⟨⟨hμ, hp⟩, fun _ ↦ ?_⟩
  refine modedP₂_bind (F := fun _ (μ' : ModeSN n) ↦ μ' = ModeSN.rest μ.ks) (F' := F) _ _
    ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ ?_
  subst h
  exact hk

/-- **A cell of a table is programmed off the encoding slots**, under every key. -/
theorem progOkSN_cellOf (S0 : MasterSeed) (p : Pos) (v : QTable) (a : PairOut) :
    ProgOkSN (.programH (cellOf S0 p v) a) := by
  refine ⟨_, _, rfl, fun pk K h ↦ ?_⟩
  have h' : slotF (cellOf S0 p v) = some (.enc K.1 K.2.1 K.2.2) :=
    slotOfInput_pkOfInput (input := decodeInput (cellOf S0 p v)) h
  rw [slotF_cellOf] at h'
  exact posSlot_ne_enc v p.1 K.1 K.2.1 K.2.2 (Option.some.inj h')

theorem progOkSN_progTN {p : Pos} (hp : p.1.IsStruct) (i : Fin n) (θ : TValsN n) :
    ProgOkSN ((progTN i p).realize θ) := by
  rw [realize_progTN hp i θ]
  exact progOkSN_cellOf _ p _ _

theorem progOkSN_digPortN (pol : DigestPolicy) (i : Fin n) (L : Finset (TPosN n))
    (msg : Message) (θ : TValsN n) : ProgOkSN ((digPortN pol i L msg).realize θ) := by
  rw [realize_digPortN, ← cellOf_digPos (seedsOf θ i)]
  exact progOkSN_cellOf _ _ _ _

theorem sRestSN_progPosN (i : Fin n) (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.1.IsStruct) → SRestSN P (progPosN (SelMemN n) i B ps)
  | [], _ => sRestSN_pure _
  | p :: ps, h => fun μ hμ ↦ modedP_progThenSN (F := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) _
      (progOkSN_progTN (h p List.mem_cons_self) i) _ hμ
      (sRestSN_progPosN i B ps (fun q hq ↦ h q (List.mem_cons_of_mem _ hq)) (.rest μ.ks) trivial)

/-- **User `i`'s counter search** reveals its coordinate, starts the key, and searches from the
revealed value under `P i`. -/
theorem modedP_selectTSN (B : QReg) (i : Fin n) {K : Key} (hK : InRangeU K) (μ : ModeSN n)
    (hμ : μ.Rest) :
    ModedP (srchOkTSN P) srchNxTSN (fun _ μ' ↦ μ'.Rest ∧ insert (i, K) μ.ks ⊆ μ'.ks) μ
      (selectTN (SelMemN n) cwUpdN i (P i) B K) := by
  unfold selectTN
  refine modedP_revealThenSN (F := fun _ μ' ↦ μ'.Rest ∧ insert (i, K) μ.ks ⊆ μ'.ks)
    ⟨hμ, fun h ↦ by rw [keyOfTSN_atU hK] at h; cases h⟩ fun r ↦ ?_
  rw [show srchNxTSN μ (.inr (atU i {vcoord (msgPos K)})) r =
    .grd (insert (i, K) μ.ks) i K ((tabRN r.1 i).valuePos (msgPos K)) 0 from
      revNxSN_atU μ hK i _]
  exact modedP_monoU (fun _ μ' h ↦ ⟨h.1, by rw [h.2]⟩) _ _
    (modedP_readLiftSN _ (modedP_grindTSN B _ i K _ _ 0 (Nat.zero_add _)))

/-- User `i`'s selection of `K` or its memo: a memo hit makes no call, its key started. -/
theorem modedP_selOrMemoTSN (B : QReg) (i : Fin n) {K : Key} (hK : InRangeU K)
    (o : Option SelS) (μ : ModeSN n) (hμ : μ.Rest) (ho : ∀ g, o = some g → (i, K) ∈ μ.ks) :
    ModedP (srchOkTSN P) srchNxTSN (fun _ μ' ↦ μ'.Rest ∧ insert (i, K) μ.ks ⊆ μ'.ks) μ
      (selOrMemoTN (SelMemN n) cwUpdN i (P i) B K o) := by
  rcases o with _ | g
  · exact modedP_selectTSN B i hK μ hμ
  · exact ⟨hμ, Finset.insert_subset (ho g rfl) subset_rfl⟩

/-- User `i`'s layer publication of an index whose keys were started. -/
theorem modedP_publishTSN (B : QReg) (i : Fin n) (l : Layer) (idx : Index)
    (c : EncodingCounter) (x : Encoding) (μ : ModeSN n) (hμ : μ.Rest)
    (hks : ∀ l', (i, keyOf l' idx) ∈ μ.ks) :
    ModedP (srchOkTSN P) srchNxTSN (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ
      (publishTN (SelMemN n) i B (keyOf l idx) c x) := by
  have hT : keyOfTSN (atU i (layerReveal (keyOf l idx) x)) = none :=
    keyOfTSN_eq_none (mk_mem_atU i (chainC_mem_layerRevealU _ x ⟨0, by decide⟩))
      (notMcU_chainC _ _ _ _ _)
  unfold publishTN
  refine modedP_revealThen_noneSN (F := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) hT hμ
    (fun i' K hK hm ↦ ?_) fun r ↦ ?_
  · obtain ⟨rfl, hm'⟩ := mem_atU.1 hm
    rcases key_of_mem_layerRevealU hK hm' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hks _
  · exact sRestSN_bind _ _ (sRestSN_progPosN i B _ fun _ hp ↦ isStruct_of_mem_layerPos hp)
      (fun _ ↦ sRestSN_pure _) (.rest μ.ks) trivial

/-- User `i`'s FORS opening of an index whose keys were started. -/
theorem modedP_forsOpenTSN (B : QReg) (i : Fin n) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (μ : ModeSN n) (hμ : μ.Rest)
    (hks : ∀ l', (i, keyOf l' idx) ∈ μ.ks) :
    ModedP (srchOkTSN P) srchNxTSN (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ
      (forsOpenTN (SelMemN n) i B idx lv) := by
  have hT : keyOfTSN (atU i (forsReveal idx lv)) = none :=
    keyOfTSN_eq_none (mk_mem_atU i (seedC_mem_forsRevealU idx lv)) notMcU_seedC
  unfold forsOpenTN
  refine modedP_revealThen_noneSN (F := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) hT hμ
    (fun i' K hK hm ↦ ?_) fun r ↦ ?_
  · obtain ⟨rfl, hm'⟩ := mem_atU.1 hm
    rw [key_of_mem_forsRevealU hK hm']
    exact hks _
  · exact sRestSN_bind _ _ (sRestSN_progPosN i B _ fun _ hp ↦ isStruct_of_mem_forsPos hp)
      (fun _ ↦ sRestSN_pure _) (.rest μ.ks) trivial

/-- **User `i`'s publication** of an index whose keys were started. -/
theorem modedP_publishAllTSN (B : QReg) (i : Fin n) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (g₀ g₁ g₂ : SelS) (μ : ModeSN n)
    (hμ : μ.Rest) (hks : ∀ l', (i, keyOf l' idx) ∈ μ.ks) :
    ModedP (srchOkTSN P) srchNxTSN (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ
      (publishAllTN (SelMemN n) i B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact ⟨hμ, subset_rfl⟩
  simp only [publishAllTN]
  refine modedP_bind_keepSN _ _ (modedP_forsOpenTSN B i idx lv μ hμ hks) fun _ μ₁ h₁ s₁ ↦ ?_
  refine modedP_bind_keepSN _ _ (modedP_publishTSN B i 0 idx c₀ x₀ μ₁ h₁ fun l' ↦ s₁ (hks l'))
    fun _ μ₂ h₂ s₂ ↦ ?_
  refine modedP_bind_keepSN _ _
    (modedP_publishTSN B i 1 idx c₁ x₁ μ₂ h₂ fun l' ↦ s₂ (s₁ (hks l'))) fun _ μ₃ h₃ s₃ ↦ ?_
  refine modedP_bind_keepSN _ _
    (modedP_publishTSN B i 2 idx c₂ x₂ μ₃ h₃ fun l' ↦ s₃ (s₂ (s₁ (hks l')))) fun _ μ₄ h₄ _ ↦ ?_
  exact ⟨h₄, subset_rfl⟩

/-- **The three selections and the publication** of user `i`'s request with memo `h`, under the
seed `sd = P i`: the request's three keys started at the end. -/
theorem modedP_selsPubTSN (B : QReg) (i : Fin n) {sd : PublicParameter} (hsd : sd = P i)
    (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) (R : Randomizer) (h : KeyMemo)
    (μ : ModeSN n) (hμ : μ.Rest) (hh : ∀ K g, h K = some g → (i, K) ∈ μ.ks) :
    ModedP (srchOkTSN P) srchNxTSN (fun p μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧
      ∀ l, (i, keyOf l (p.2.2 : Option Signature × MemoAns).2.1) ∈ μ'.ks) μ
      ((selOrMemoTN (SelMemN n) cwUpdN i sd B (keyOf 0 idx) (h (keyOf 0 idx))).bind fun g₀ ↦
        (selOrMemoTN (SelMemN n) cwUpdN i sd B (keyOf 1 idx) (h (keyOf 1 idx))).bind
          fun g₁ ↦
        (selOrMemoTN (SelMemN n) cwUpdN i sd B (keyOf 2 idx) (h (keyOf 2 idx))).bind
          fun g₂ ↦
        (publishAllTN (SelMemN n) i B idx lv R g₀ g₁ g₂).map fun s ↦
          (s, (idx, layerSels g₀ g₁ g₂))) := by
  subst hsd
  refine modedP₂_bind
    (F := fun _ (μ' : ModeSN n) ↦ μ'.Rest ∧ insert (i, keyOf 0 idx) μ.ks ⊆ μ'.ks)
    (F' := fun (a : Option Signature × MemoAns) (μ' : ModeSN n) ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧
      ∀ l, (i, keyOf l a.2.1) ∈ μ'.ks) _ _
    (modedP_selOrMemoTSN B i ⟨0, idx, rfl⟩ _ μ hμ (hh _)) fun g₀ μ₁ h₁ ↦ ?_
  refine modedP₂_bind
    (F := fun _ (μ' : ModeSN n) ↦ μ'.Rest ∧ insert (i, keyOf 1 idx) μ₁.ks ⊆ μ'.ks)
    (F' := fun (a : Option Signature × MemoAns) (μ' : ModeSN n) ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧
      ∀ l, (i, keyOf l a.2.1) ∈ μ'.ks) _ _
    (modedP_selOrMemoTSN B i ⟨1, idx, rfl⟩ _ μ₁ h₁.1 fun g hg ↦
      h₁.2 (Finset.mem_insert_of_mem (hh _ g hg))) fun g₁ μ₂ h₂ ↦ ?_
  refine modedP₂_bind
    (F := fun _ (μ' : ModeSN n) ↦ μ'.Rest ∧ insert (i, keyOf 2 idx) μ₂.ks ⊆ μ'.ks)
    (F' := fun (a : Option Signature × MemoAns) (μ' : ModeSN n) ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧
      ∀ l, (i, keyOf l a.2.1) ∈ μ'.ks) _ _
    (modedP_selOrMemoTSN B i ⟨2, idx, rfl⟩ _ μ₂ h₂.1 fun g hg ↦
      h₂.2 (Finset.mem_insert_of_mem (h₁.2 (Finset.mem_insert_of_mem (hh _ g hg)))))
    fun g₂ μ₃ h₃ ↦ ?_
  have hs : μ.ks ⊆ μ₃.ks := ((Finset.subset_insert _ _).trans h₁.2).trans
    (((Finset.subset_insert _ _).trans h₂.2).trans ((Finset.subset_insert _ _).trans h₃.2))
  have hks : ∀ l', (i, keyOf l' idx) ∈ μ₃.ks := by
    intro l'
    rcases layer_casesU l' with rfl | rfl | rfl
    · exact h₃.2 (Finset.mem_insert_of_mem (h₂.2 (Finset.mem_insert_of_mem
        (h₁.2 (Finset.mem_insert_self _ _)))))
    · exact h₃.2 (Finset.mem_insert_of_mem (h₂.2 (Finset.mem_insert_self _ _)))
    · exact h₃.2 (Finset.mem_insert_self _ _)
  refine modedP_map _ (F := fun (a : Option Signature × MemoAns) (μ' : ModeSN n) ↦
    μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧ ∀ l, (i, keyOf l a.2.1) ∈ μ'.ks) ?_
  exact modedP_monoU (fun _ _ h ↦ ⟨h.1, hs.trans h.2, fun l ↦ h.2 (hks l)⟩) _ _
    (modedP_publishAllTSN B i _ lv R g₀ g₁ g₂ μ₃ h₃.1 hks)

/-! ### The realized challenge prefix -/

/-- **User `i`'s realized signature with memo `h`** is moded between searches, its trials under
user `i`'s `PK.seed`; it ends with the request's three keys started. -/
theorem modedP_signTSN {pols : Fin n → DigestPolicy} (i : Fin n) (hpol : (pols i).NoVal)
    (θ : TValsN n) (B : QReg) (msg : Message) (h : KeyMemo) (μ : ModeSN n) (hμ : μ.Rest)
    (hh : ∀ K g, h K = some g → (i, K) ∈ μ.ks) :
    ModedP (srchOkZSN (parQSN θ)) (srchNxZSN θ) (fun p μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧
      ∀ l, (i, keyOf l (p.2.2 : Option Signature × MemoAns).2.1) ∈ μ'.ks) μ
      (realizeT θ (signTN (SelMemN n) cwUpdN pols i B msg h)) := by
  rw [signTN]
  refine modedP_realizeT_revealThen_noneSN (F := fun (a : Option Signature × MemoAns) μ' ↦
      μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧ ∀ l, (i, keyOf l a.2.1) ∈ μ'.ks) θ
    (keyOfTSN_eq_none (mk_mem_atU i (Finset.mem_insert_self _ _)) notMcU_seedC) hμ
    (revOkSN_of_notMc fun s hs ↦ notMcU_sigReveal msg _ (mem_atU_iff.1 hs).2) fun mem ↦ ?_
  have hs₀ : (tabRN (restrictTo (atU i {seedC, rootC, rndC msg}) θ) i).publicSeed =
      parQSN θ i :=
    publicSeed_tabOf_congr (tabRN_restrictTo_congr (atU_restrict _) θ _ (by simp))
  refine modedP_realizeTSN θ _ ?_
  refine modedP_revealThen_noneSN (F := fun (a : Option Signature × MemoAns) μ' ↦
      μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧ ∀ l, (i, keyOf l a.2.1) ∈ μ'.ks)
    (keyOfTSN_eq_none (mk_mem_atU i ((pols i).out_mem _ _))
      (notMcU_of_noVal hpol ((pols i).out_mem _ _))) trivial
    (revOkSN_of_notMc fun s hs ↦ notMcU_of_noVal hpol (mem_atU_iff.1 hs).2) fun r₂ ↦ ?_
  refine modedP_progThenSN (F := fun (a : Option Signature × MemoAns) μ' ↦
      μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧ ∀ l, (i, keyOf l a.2.1) ∈ μ'.ks) _
    (progOkSN_digPortN _ i _ msg) _ trivial ?_
  exact modedP_selsPubTSN B i hs₀ _ _ _ h (.rest μ.ks) trivial hh

/-- **The realized challenger at user `i`'s signing request with memo `q.2`**: it ends with the
answered request's three keys started. -/
theorem modedP_challengeTSN_sign {pols : Fin n → DigestPolicy} (hpols : ∀ i, (pols i).NoVal)
    (θ : TValsN n) {A : QReg} (i : Fin n) (q : Message × KeyMemo) (E : QReg)
    (ℓ : A ≃ (memoSpecS n).In (.sign i q) × E) (μ : ModeSN n) (hμ : μ.Rest)
    (hh : ∀ K g, q.2 K = some g → (i, K) ∈ μ.ks) :
    ModedP (srchOkZSN (parQSN θ)) (srchNxZSN θ) (fun p μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧
      ∀ l, (i, keyOf l (ULift.down p.2.1 : Option Signature × MemoAns).2.1) ∈ μ'.ks) μ
      (realizeT θ (challengeTN (SelMemN n) cwUpdN pols A (.query (.sign i q) E ℓ))) := by
  have hx : ModedP (srchOkZSN (parQSN θ)) (srchNxZSN θ) (fun p μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧
      ∀ l, (i, keyOf l (p.2.2 : Option Signature × MemoAns).2.1) ∈ μ'.ks) μ
      (realizeT θ (signAtSN (spec := XSpecSN (SelMemN n) n) i q E ℓ fun B ↦
        signTN (SelMemN n) cwUpdN pols i B q.1 q.2)) := by
    unfold signAtSN
    refine modedP_realizeT_bind₂SN θ _ _ (F := fun _ (μ' : ModeSN n) ↦ μ' = μ)
      (F' := fun (a : Option Signature × MemoAns) μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks ∧
        ∀ l, (i, keyOf l a.2.1) ∈ μ'.ks) ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ ?_
    subst h
    exact modedP_signTSN i (hpols i) θ _ q.1 q.2 μ' hμ hh
  dsimp only [challengeTN]
  exact modedP_realizeT_bindSN θ _ _ hx fun _ _ _ h ↦ h

/-- **The memo transform against the realized challenger** is moded between searches, from a mode
whose started keys hold the memoized ones. -/
theorem modedP_memoFromSN {pols : Fin n → DigestPolicy} (hpols : ∀ i, (pols i).NoVal)
    (θ : TValsN n) {Y : QReg → Type} {A : QReg} (y : IFreeM (MuPS n) Y A) :
    ∀ (T : SelMemoS n) (μ : ModeSN n), μ.Rest → (∀ j K g, T j K = some g → (j, K) ∈ μ.ks) →
      ModedP (srchOkZSN (parQSN θ)) (srchNxZSN θ) (fun _ (μ : ModeSN n) ↦ μ.Rest) μ
        ((memoFromS T y).substitute fun A c ↦
          realizeT θ (challengeTN (SelMemN n) cwUpdN pols A c)) := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact fun _ _ h _ ↦ h
  | liftBind A c next ih =>
    intro T μ hμ hT
    rcases c with o | ⟨_ | ⟨i, msg⟩, E, ℓ⟩
    · refine modedP_bind _ _ (modedP_realizeTSN θ _ (modedP_readLiftSN _
        (modedP_liftOrdinarySN _ μ hμ))) fun u ans μ' h ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b T μ' h.1 fun j K g hg ↦ h.2 (hT j K g hg)
    · refine modedP_bind _ _ (modedP_realizeTSN θ _ (modedP_readLiftSN _
        (modedP_liftOrdinarySN _ μ hμ))) fun u ans μ' h ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b T μ' h.1 fun j K g hg ↦ h.2 (hT j K g hg)
    · refine modedP_bind _ _ (modedP_challengeTSN_sign hpols θ i (msg, T i) E ℓ μ hμ
        fun K g hg ↦ hT i K g hg) fun u ans μ' h ↦ ?_
      obtain ⟨b, hb⟩ := ans
      subst hb
      refine ih _ _ μ' h.1 fun j K g hg ↦ ?_
      by_cases hj : j = i ∧ K = keyOf K.1 (ULift.down b : Option Signature × MemoAns).2.1
      · obtain ⟨rfl, hK⟩ := hj
        rw [hK]
        exact h.2.2 K.1
      · rw [SelMemoS.put_of_ne T hj] at hg
        exact h.2.1 (hT j K g hg)

/-- **The realized challenge prefix is moded** from `rest ∅`, user `i`'s trials under user `i`'s
`PK.seed`, ending between searches. -/
theorem modedP_prefixQSN {pols : Fin n → DigestPolicy} (hpols : ∀ i, (pols i).NoVal)
    (A : MuAdversaryS n) (θ : TValsN n) :
    ModedP (srchOkZSN (parQSN θ)) (srchNxZSN θ) (fun _ (μ : ModeSN n) ↦ μ.Rest) (.rest ∅)
      (prefixQSN pols A θ) := by
  have hn : ∀ s ∈ (pkRevealN : Finset (TPosN n)), NotMcU s.2 :=
    fun s hs ↦ notMcU_pkReveal _ (Finset.mem_product.1 hs).2
  unfold prefixQSN prefixTN
  refine modedP_realizeT_revealThen_noneSN (F := fun _ μ' ↦ μ'.Rest) θ
    (keyOfTSN_eq_none_of hn) trivial (revOkSN_of_notMc hn) fun mem ↦ ?_
  dsimp only
  rw [realizeT_bind₂]
  refine modedP₂_bind (F := fun _ (μ' : ModeSN n) ↦ μ'.Rest)
    (F' := fun _ (μ' : ModeSN n) ↦ μ'.Rest) _ _ ?_ fun _ _ h ↦ h
  unfold challengedTN
  rw [realizeT_substitute]
  exact modedP_memoFromSN hpols θ _ _ _ trivial fun _ _ _ h ↦ by cases h

/-! ## The repeated-reveal charges -/

/-- **A repeated reveal of user `i`'s `K` with `K` unselected**: `(i, vcoord (msgPos K))` already
revealed, user `i`'s `K` unselected. -/
def ReRevQSN (i : Fin n) (K : Key) (s : RRegSN n (SelMemN n)) : Prop :=
  (i, vcoord (msgPos K)) ∈ s.2.2.1 ∧ s.2.2.2 i K = none

open scoped Classical in
/-- **The repeated-reveal charges**: at a reveal of user `i`'s key coordinate, `2^32` times the
mass of `ReRevQSN i K`; nothing elsewhere. -/
noncomputable def reRevQWSN : ∀ x : (RSpecSN n (SelMemN n)).Port,
    Matrix ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n))
      ((RSpecSN n (SelMemN n)).In x × RRegSN n (SelMemN n)) ℂ → ℝ≥0∞
  | .inr T, σ =>
    match keyOfTSN T with
    | some (i, K) => (encodingAttemptLimit : ℝ≥0∞) *
        diagMass {q : Unit × RRegSN n (SelMemN n) | ReRevQSN i K q.2} σ
    | none => 0
  | _, _ => 0

end Quantum.Qrom.Sphincs.Multi

end
