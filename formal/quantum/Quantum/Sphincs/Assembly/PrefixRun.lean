module

public import Quantum.Xmss.Assembly.PrefixRun
public import Quantum.Sphincs.Assembly.Template

@[expose] public section

/-!
# leanSPHINCS's realized template in the decompressed basis

leanSPHINCS's instance of the support semantics of `Quantum.Xmss.Assembly.PrefixRun` (the Hoare
predicates `HT`, `HT₂`, the ports in the decompressed basis, `Det`), on the register `SReg` of
runtime 2 with record ports at leanSPHINCS's memory (`Finset HPos × Selections`).

* `ht₂_progPorts`, `ht₂_progSlots`: program ports move the register along their realized calls.
* **The counter search as a function of the view**: `encIn` (Classify's `encInput` at the value
  `m`), `encDigest` (a trial's digest against the functions `t`), `grindKV` (the search against
  `t`), `grindMemK` (the memory after it: the found trial's block and digest, if the key was
  unselected); `det_grindK`: the realized `grindK` answers `grindKV` of the register's functions
  and updates the memory by `grindMemK`.
* `ht_challengeT_perm`, `ht_logSigns`, `ht₂_prefixT`: the challenge prefix with the signing log,
  for every digest policy.
-/

open Matrix
open scoped Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput HashInput Message PublicParameter littleEndianBytes truncateHash)
open Quantum.Xmss (X Z blocks trunc128 out256 length_blocks)
open Quantum.Xmss.Hybrid (LazyProg restrictTo)
open Quantum.Xmss.Assembly (PRegOf HT HT₂ ht₂_pure ht_pure ht₂_act ht_of_ht₂ ht₂_of_ht
  ht_realizeT_bind ht₂_realizeT_bind ht₂_revealThen ht₂_progThen ht_sponge ProgsRel progsRel_append
  Det det_pure det_hashTrial trialMid trialRate trialMem hwView_h_of_noBot regFns realizeT
  realizeT_bind₂ realizeT_substitute revealThen tmplSpec recHwSpec RevealVals hashTrial)

namespace Quantum.Sphincs.Assembly

/- Instance search for the run families over the register `SReg` exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-- The register of runtime 2 with record ports at leanSPHINCS's memory. -/
abbrev SReg : Type := PRegOf HPos Selections

/-! ## Program ports -/

section ports

variable (m₀ : Finset HPos × Selections) (v : (s : HPos) → XD s)

/-- **Program ports** move the register along their realized calls. -/
theorem ht₂_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) (P : Set SReg) :
    HT₂ m₀ (realizeT v (progPorts Selections B ps)) P
      fun _ ↦ {s' | ∃ s ∈ P, ProgsRel (ps.map (·.realize v)) s s'} := by
  induction ps generalizing P with
  | nil => exact ht₂_pure () fun s hs ↦ ⟨s, hs, rfl⟩
  | cons p ps ih =>
    refine ht₂_progThen m₀ v p trivial _ P _ ((ih _).mono subset_rfl fun _ ↦ ?_)
    rintro s'' ⟨s', ⟨s, hs, h₁⟩, h₂⟩
    exact ⟨s, hs, s', h₁, h₂⟩

/-- **Programming the honest paths of slots**: the register moves along their program calls. -/
theorem ht₂_progSlots (pub : Pub) (B : QReg) (ss : List Slot) (P : Set SReg) :
    HT₂ m₀ (realizeT v (progSlots Selections pub B ss)) P
      (fun _ ↦ {s' | ∃ s ∈ P, ProgsRel ((ss.flatMap (slotPorts pub)).map (·.realize v)) s s'}) := by
  induction ss generalizing P with
  | nil => exact ht₂_pure () fun s hs ↦ ⟨s, hs, rfl⟩
  | cons s ss ih =>
    rw [progSlots, realizeT_bind₂]
    refine HT₂.bind (ht₂_progPorts m₀ v B (slotPorts pub s) P) fun _ ↦
      (ih _).mono subset_rfl fun _ ↦ ?_
    rintro s'' ⟨s', ⟨s₀, hs₀, h₁⟩, h₂⟩
    refine ⟨s₀, hs₀, ?_⟩
    rw [List.flatMap_cons, List.map_append]
    exact progsRel_append h₁ h₂

end ports

/-! ## The counter search as a function of the view -/

section grind

variable (pub : Pub)

/-- The input of key `K`'s trial at counter `c` on the value `m`:
`PK.seed ‖ ADRS_enc(K) ‖ m ‖ BE32(c)` (Classify's `encInput` at `m`). -/
def encIn (K : Key) (m : Digest) (c : EncodingCounter) : HashInput :=
  addressedHashInput pub.seed (hashDomainFields (.encoding K.1 K.2.1 K.2.2))
    (littleEndianBytes 16 m ++ bigEndianBytes 4 c)

theorem trialInput_eq (K : Key) (m : Digest) (c : ℕ) :
    trialInput pub K m c = encIn pub K m (BitVec.ofNat counterBits c) :=
  rfl

theorem length_encIn (K : Key) (m : Digest) (c : EncodingCounter) :
    (encIn pub K m c).length = 68 := by
  rw [encIn, length_addressedHashInput]
  simp [littleEndianBytes, bigEndianBytes]

/-- A trial input is one block. -/
theorem blocks_encIn (K : Key) (m : Digest) (c : EncodingCounter) :
    blocks (encIn pub K m c) = [(blocks (encIn pub K m c)).headD 0] := by
  have hl : (blocks (encIn pub K m c)).length = 1 := by
    rw [length_blocks, length_encIn]
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hl
  rw [hb]
  rfl

/-- The digest of key `K`'s trial at counter `c` on `m` against the functions `t`. -/
def encDigest (t : SpongeKeys X Z) (K : Key) (m : Digest) (c : EncodingCounter) : Digest :=
  trunc128 ((blocks (encIn pub K m c)).foldl (absorbStep (spongePerm t pub.perm)) (0, 0)).1

theorem encDigest_eq {t : SpongeKeys X Z} {K : Key} {m : Digest} {c : EncodingCounter} {b : X}
    (hb : blocks (encIn pub K m c) = [b]) :
    encDigest pub t K m c = trunc128 (trialRate t pub.perm b) := by
  unfold encDigest
  rw [hb]
  rfl

/-- **The counter search against the functions `t`**: trials `c, c + 1, …` on the value `m` until
a codeword. -/
def grindKV (t : SpongeKeys X Z) (K : Key) (m : Digest) :
    ℕ → ℕ → Option (EncodingCounter × Encoding)
  | 0, _ => none
  | n + 1, c =>
    match TargetSum.decodeDigest (encDigest pub t K m (BitVec.ofNat counterBits c)) with
    | some x => some (BitVec.ofNat counterBits c, x)
    | none => grindKV t K m n (c + 1)

/-- **The memory after the counter search**: the found trial's block and digest, if the key was
unselected. -/
noncomputable def grindMemK (t : SpongeKeys X Z) (K : Key) (m : Digest) (n c : ℕ)
    (sel : Selections) : Selections :=
  match sel K, grindKV pub t K m n c with
  | none, some (cc, _) =>
    sel.select K ((blocks (encIn pub K m cc)).headD 0) (encDigest pub t K m cc)
  | _, _ => sel

theorem grindMemK_zero (t : SpongeKeys X Z) (K : Key) (m : Digest) (c : ℕ) (sel : Selections) :
    grindMemK pub t K m 0 c sel = sel := by
  unfold grindMemK
  rcases sel K with _ | _ <;> rfl

theorem grindMemK_succ (t : SpongeKeys X Z) (K : Key) (m : Digest) (n c : ℕ) (sel : Selections)
    {b : X} (hb : blocks (encIn pub K m (BitVec.ofNat counterBits c)) = [b]) :
    grindMemK pub t K m (n + 1) c sel =
      match TargetSum.decodeDigest (encDigest pub t K m (BitVec.ofNat counterBits c)) with
      | some _ => cwUpd K b (trialMid t pub.perm b).1 sel
          (some (t.1 ((trialMid t pub.perm b).2 + t.2.2 (trialMid t pub.perm b).1)))
      | none => grindMemK pub t K m n (c + 1) (cwUpd K b (trialMid t pub.perm b).1 sel
          (some (t.1 ((trialMid t pub.perm b).2 + t.2.2 (trialMid t pub.perm b).1)))) := by
  have hD := encDigest_eq pub (t := t) hb
  rcases hd : TargetSum.decodeDigest (encDigest pub t K m (BitVec.ofNat counterBits c))
    with _ | x
  · have hv : ¬ Codeword.Valid (trunc128 (trialRate t pub.perm b)) := by
      rw [← hD]
      exact Codeword.decode_eq_none_iff.1 hd
    have hcw : cwUpd K b (trialMid t pub.perm b).1 sel
        (some (t.1 ((trialMid t pub.perm b).2 + t.2.2 (trialMid t pub.perm b).1))) = sel := by
      show (if sel K = none then cwSel sel K b (trialMid t pub.perm b).1
        (t.1 ((trialMid t pub.perm b).2 + t.2.2 (trialMid t pub.perm b).1)) else sel) = sel
      split_ifs
      · exact ite_eq_right hv
      · rfl
    rw [hcw]
    simp only [grindMemK, grindKV, hd]
  · have hv : Codeword.Valid (trunc128 (trialRate t pub.perm b)) := by
      rw [← hD]
      exact Codeword.valid_of_decode hd
    simp only [grindMemK, grindKV, hd]
    rcases hm : sel K with _ | y
    · show sel.select K ((blocks (encIn pub K m (BitVec.ofNat counterBits c))).headD 0)
        (encDigest pub t K m (BitVec.ofNat counterBits c)) = _
      rw [hb, cwUpd_some_of_none K b _ hm, cwSel, ite_eq_left (show Codeword.Valid
        (trunc128 ((trialMid t pub.perm b).1 +
          t.1 ((trialMid t pub.perm b).2 + t.2.2 (trialMid t pub.perm b).1))) from hv), hD]
      rfl
    · show sel = if sel K = none then _ else sel
      rw [hm, ite_eq_right (Option.some_ne_none y)]

variable {m₀ : Finset HPos × Selections} {v : (s : HPos) → XD s}

/-- **The counter search answers as a function of the view**: its result is `grindKV` of the
register's functions, and it updates the memory by `grindMemK`. -/
theorem det_grindK (B : QReg) (K : Key) (m : Digest) (n c : ℕ) :
    Det m₀ v goodAll (grindK Selections cwUpd pub B K m n c)
      (fun s ↦ grindKV pub (regFns s) K m n c)
      (fun s ↦ (s.1, s.2.1, (s.2.2.1, grindMemK pub (regFns s) K m n c s.2.2.2))) := by
  induction n generalizing c with
  | zero =>
    refine (det_pure none).congr fun s _ ↦ ⟨rfl, ?_⟩
    rw [grindMemK_zero]
  | succ n ih =>
    obtain ⟨b, hb⟩ : ∃ b, blocks (encIn pub K m (BitVec.ofNat counterBits c)) = [b] :=
      ⟨_, blocks_encIn pub K m _⟩
    rw [grindK]
    have hb₀ : blocks (trialInput pub K m c) = [b] := hb
    refine Det.congr (Det.bind (det_hashTrial (cwUpd K) pub.perm B hb₀)
      (out' := fun o s ↦ Option.elim (TargetSum.decodeDigest (truncateHash o))
        (grindKV pub (regFns s) K m n (c + 1)) fun x ↦ some (BitVec.ofNat counterBits c, x))
      (fin' := fun o s ↦ Option.elim (TargetSum.decodeDigest (truncateHash o))
        (s.1, s.2.1, (s.2.2.1, grindMemK pub (regFns s) K m n (c + 1) s.2.2.2)) fun _ ↦ s)
      fun o ↦ ?_) fun s hs ↦ ⟨?_, ?_⟩
    · cases TargetSum.decodeDigest (truncateHash o) with
      | none => exact ih (c + 1)
      | some x => exact det_pure _
    · show Option.elim (TargetSum.decodeDigest (trunc128 (trialRate (regFns s) pub.perm b)))
        (grindKV pub (regFns s) K m n (c + 1)) (fun x ↦ some (BitVec.ofNat counterBits c, x)) = _
      rw [grindKV, encDigest_eq pub hb]
      cases TargetSum.decodeDigest (trunc128 (trialRate (regFns s) pub.perm b)) <;> rfl
    · show Option.elim (TargetSum.decodeDigest (trunc128 (trialRate (regFns s) pub.perm b)))
        (s.1, s.2.1, (s.2.2.1, grindMemK pub (regFns s) K m n (c + 1)
          (trialMem (cwUpd K) pub.perm b s)))
        (fun _ ↦ (s.1, s.2.1, (s.2.2.1, trialMem (cwUpd K) pub.perm b s))) = _
      rw [grindMemK_succ pub _ _ _ _ _ _ hb, encDigest_eq pub hb]
      have hw : trialMem (cwUpd K) pub.perm b s =
          cwUpd K b (trialMid (regFns s) pub.perm b).1 s.2.2.2 (some ((regFns s).1
            ((trialMid (regFns s) pub.perm b).2 +
              (regFns s).2.2 (trialMid (regFns s) pub.perm b).1))) := by
        rw [trialMem, hwView_h_of_noBot hs]
      rw [hw]
      cases TargetSum.decodeDigest (trunc128 (trialRate (regFns s) pub.perm b)) <;> rfl

end grind

/-! ## The challenge prefix -/

section prefixRun

variable (m₀ : Finset HPos × Selections) (v : (s : HPos) → XD s) (pol : DigestPolicy) (pub : Pub)

/-- **The challenger's local operations and permutation calls keep every register set.** -/
theorem ht_challengeT_perm (A : QReg) (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A)
    (hc : (∃ o, c = .prim o) ∨ ∃ p E ℓ, c = .query (.perm p) E ℓ) (P : Set SReg) :
    HT m₀ (realizeT v (challengeT Selections cwUpd pol pub A c)) P fun _ ↦ P := by
  rcases hc with ⟨o, rfl⟩ | ⟨p, E, ℓ, rfl⟩
  · exact ht_sponge m₀ v _ P
  · exact ht_sponge m₀ v _ P

/-- **The substituted adversary with its signing log**: along the adversary's program, sponge-only
steps keep the invariant `Inv log`, and a signing request moves it to the extended log. -/
theorem ht_logSigns (Inv : SignLog Message (Option Signature) → Set SReg)
    (hsign : ∀ (B : QReg) (msg : Message) (log : SignLog Message (Option Signature)),
      HT₂ m₀ (realizeT v (signT Selections cwUpd pol pub B msg)) (Inv log)
        (fun sig ↦ Inv (log ++ [⟨msg, sig⟩])))
    {Ω Y : QReg → Type} (leaf : ∀ u, Ω u → SignLog Message (Option Signature) → Y u)
    (Q : (Σ u, Y u) → Set SReg) (hleaf : ∀ u y log, Inv log ⊆ Q ⟨u, leaf u y log⟩) {A : QReg}
    (x : IPFunctor.IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec) Ω A)
    (log : SignLog Message (Option Signature)) :
    HT m₀ ((logSigns (S := X × Z) leaf x log).substitute fun A c ↦
      realizeT v (challengeT Selections cwUpd pol pub A c)) (Inv log) Q := by
  induction x using IPFunctor.IFreeM.inductionOn generalizing log with
  | pure u y => exact ht_pure (leaf u y log) (hleaf u y log)
  | liftBind s c next ih =>
    refine HT.bind (x := realizeT v (challengeT Selections cwUpd pol pub s c))
      (Q := fun p ↦ Inv (logAfter c p.2.1 log)) ?_ fun u ans ↦ ?_
    · rcases c with o | ⟨p | r, E, ℓ⟩
      · exact ht_challengeT_perm m₀ v pol pub s _ (.inl ⟨o, rfl⟩) (Inv log)
      · exact ht_challengeT_perm m₀ v pol pub s _ (.inr ⟨p, E, ℓ, rfl⟩) (Inv log)
      · have hs : HT₂ m₀ (realizeT v (signAt Selections cwUpd pol pub r E ℓ)) (Inv log)
            fun sig ↦ Inv (log ++ [⟨r, sig⟩]) :=
          ht₂_realizeT_bind m₀ v (ht₂_act _ _) fun _ ↦ hsign _ r log
        exact ht_realizeT_bind m₀ v (ht_of_ht₂ hs) fun _ l ↦ ht_pure _ subset_rfl
    · obtain ⟨b, hb⟩ := ans
      subst hb
      exact ih b (logAfter c b log)

/-- **The challenge prefix**: the root revealed (label grown by the root's position), then the
adversary against the challenger with its signing log, moving the invariant `Inv log` along the
log; it returns the public key of the revealed root. -/
theorem ht₂_prefixT (A : SAdversary) (Inv : SignLog Message (Option Signature) → Set SReg)
    (hsign : ∀ (B : QReg) (msg : Message) (log : SignLog Message (Option Signature)),
      HT₂ m₀ (realizeT v (signT Selections cwUpd pol pub B msg)) (Inv log)
        (fun sig ↦ Inv (log ++ [⟨msg, sig⟩])))
    (P₀ : Set SReg) (hroot : ∀ s ∈ P₀, (s.1, s.2.1, (s.2.2.1 ∪ {.val rootPos}, s.2.2.2)) ∈ Inv []) :
    HT₂ m₀ (realizeT v (prefixT Selections cwUpd pol pub A)) P₀
      (fun pre ↦ {s | s ∈ Inv pre.2.2 ∧ pre.1 = pkOf pub (restrictTo {.val rootPos} v)}) := by
  unfold prefixT
  refine ht₂_revealThen m₀ v _ _ P₀ _ fun mem ↦ ?_
  refine ht₂_realizeT_bind m₀ v (Q := fun run ↦ Inv run.2) ?_ fun run ↦
    ht₂_pure _ fun s hs ↦ ⟨hs, rfl⟩
  refine ht₂_of_ht (HT.mono (P := Inv []) ?_ ?_ fun _ ↦ subset_rfl)
  · have e := realizeT_substitute (good := goodAll) (M := Selections) v
      (challengeT Selections cwUpd pol pub)
      (withSignLog (A (pkOf pub (restrictTo {.val rootPos} v, mem).1)))
    refine (congrArg (fun y ↦ HT m₀ y (Inv []) fun p ↦ Inv p.2.2.2) e).mpr ?_
    exact ht_logSigns m₀ v pol pub Inv hsign _
      (fun q : (Σ u, QuantumComp₂.Leaf (QReg.of Unit)
        (Forgery × SignLog Message (Option Signature)) u) ↦ Inv q.2.2.2)
      (fun _ _ _ ↦ subset_rfl) _ []
  · rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hroot s₀ hs₀

end prefixRun

end Quantum.Sphincs.Assembly

end
