module

public import Qrom.Sphincs.Bound.Terms
public import Qrom.Deferral

@[expose] public section

/-!
# Deferring the signed digests

The data splits into its digests `Dg : Message → DigestCall → HashOutput` and the rest
(`Qrom.Sphincs.withDig`). The hidden game reads the digest of a message only once the message is
logged (`Qrom.Sphincs.dig_mem_sig`), so it is the game `Qrom.Sphincs.gB` that gives the `i`-th
distinct logged message the digest `δ i`, on corresponding digests (`Qrom.OvGame.deferral_le`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- The outputs of a message's digest calls. -/
abbrev DigV := DigestCall → HashOutput

/-- The data `r` with the digests `Dg`. -/
def withDig (r : Data) (Dg : Message → DigV) : Data
  | some (.dig m c) => Dg m c
  | q => r q

/-- The digests of the data. -/
def digOf (d : Data) : Message → DigV := fun m c ↦ d (some (.dig m c))

theorem withDig_dig (r : Data) (Dg : Message → DigV) (m : Message) (c : DigestCall) :
    withDig r Dg (some (.dig m c)) = Dg m c := rfl

theorem withDig_of_ne (r : Data) (Dg : Message → DigV) (q : Option Key)
    (hq : ∀ m c, q ≠ some (.dig m c)) : withDig r Dg q = r q := by
  rcases q with _ | k
  · rfl
  · cases k with
    | dig m c => exact absurd rfl (hq m c)
    | _ => rfl

theorem withDig_digOf (r : Data) (Dg : Message → DigV) :
    withDig (withDig r Dg) (digOf r) = r := by
  funext q
  by_cases hq : ∃ m c, q = some (.dig m c)
  · obtain ⟨m, c, rfl⟩ := hq
    rfl
  · push Not at hq
    rw [withDig_of_ne _ _ q hq, withDig_of_ne _ _ q hq]

theorem digOf_withDig (r : Data) (Dg : Message → DigV) : digOf (withDig r Dg) = Dg := rfl

/-- Averaging over the data is averaging over the rest and the digests. -/
theorem sum_withDig {β : Type} [AddCommMonoid β] (f : Data → β) :
    ∑ r, ∑ Dg, f (withDig r Dg) = Fintype.card (Message → DigV) • ∑ d, f d := by
  let Φ : Data × (Message → DigV) → Data × (Message → DigV) := fun x ↦ (withDig x.1 x.2, digOf x.1)
  have hΦ : Function.Involutive Φ := fun x ↦ by
    simp only [Φ, withDig_digOf, digOf_withDig]
  calc ∑ r, ∑ Dg, f (withDig r Dg) = ∑ x : Data × (Message → DigV), f (Φ x).1 :=
        (Fintype.sum_prod_type' (fun r Dg ↦ f (withDig r Dg))).symm
    _ = ∑ x : Data × (Message → DigV), f x.1 := Equiv.sum_comp hΦ.toPerm (fun x ↦ f x.1)
    _ = Fintype.card (Message → DigV) • ∑ d, f d := by
      refine (Fintype.sum_prod_type' (fun (d : Data) (_ : Message → DigV) ↦ f d)).trans ?_
      simp [Finset.smul_sum]

/-! ## The distinct logged messages -/

/-- Append a message unless it is already there. -/
def sigStep (acc : List Message) (m : Message) : List Message := if m ∈ acc then acc else acc ++ [m]

/-- The distinct messages of a list of entries, in order of first occurrence. -/
def sigFrom (acc : List Message) (l : List (Message × Option Signature)) : List Message :=
  l.foldl (fun a e ↦ sigStep a e.1) acc

/-- The distinct logged messages, in order. -/
def sig (s : Log) : List Message := sigFrom [] s.1

theorem prefix_sigStep (acc : List Message) (m : Message) : acc <+: sigStep acc m := by
  unfold sigStep; split_ifs
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

theorem mem_sigStep {acc : List Message} {m m' : Message} : m' ∈ sigStep acc m ↔ m' ∈ acc ∨ m' = m := by
  unfold sigStep; split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h' | rfl)
      · exact h'
      · exact h
  · simp

theorem nodup_sigStep {acc : List Message} (h : acc.Nodup) (m : Message) : (sigStep acc m).Nodup := by
  unfold sigStep; split_ifs with hm
  · exact h
  · refine List.nodup_append.mpr ⟨h, List.nodup_singleton m, fun a ha b hb ↦ ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    rintro rfl
    exact hm ha

theorem length_sigStep (acc : List Message) (m : Message) : (sigStep acc m).length ≤ acc.length + 1 := by
  unfold sigStep; split_ifs <;> simp

theorem sigFrom_props : ∀ (l : List (Message × Option Signature)) (acc : List Message),
    acc <+: sigFrom acc l ∧ (∀ m, m ∈ sigFrom acc l ↔ m ∈ acc ∨ ∃ e ∈ l, e.1 = m) ∧
      (acc.Nodup → (sigFrom acc l).Nodup) ∧ (sigFrom acc l).length ≤ acc.length + l.length
  | [], acc => ⟨List.prefix_refl _, fun m ↦ by simp [sigFrom], id, by simp [sigFrom]⟩
  | e :: l, acc => by
    obtain ⟨h1, h2, h3, h4⟩ := sigFrom_props l (sigStep acc e.1)
    refine ⟨(prefix_sigStep acc e.1).trans h1, fun m ↦ ?_, fun h ↦ h3 (nodup_sigStep h _), ?_⟩
    · change m ∈ sigFrom (sigStep acc e.1) l ↔ _
      rw [h2, mem_sigStep]
      constructor
      · rintro ((h | rfl) | ⟨e', he', rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e, List.mem_cons_self, rfl⟩
        · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', rfl⟩
      · rintro (h | ⟨e', he', rfl⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp he' with rfl | he'
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨e', he', rfl⟩
    · change (sigFrom (sigStep acc e.1) l).length ≤ _
      have := length_sigStep acc e.1
      simp only [List.length_cons]
      omega

theorem mem_sig {s : Log} {m : Message} : m ∈ sig s ↔ ∃ e ∈ s.1, e.1 = m := by
  rw [sig, (sigFrom_props s.1 []).2.1]
  simp

theorem nodup_sig (s : Log) : (sig s).Nodup := (sigFrom_props s.1 []).2.2.1 List.nodup_nil

theorem length_sig_le (s : Log) : (sig s).length ≤ signatureLimit :=
  (sigFrom_props s.1 []).2.2.2.trans (by simpa using s.2)

/-- The distinct logged messages after a port. -/
def sigNext (j : Port) (s : Log) : List Message :=
  match j with
  | .pk => sig s
  | .sign m => if s.1.length < signatureLimit then sigStep (sig s) m else sig s

theorem sig_portTrans (pk : PublicKey) (sign : Message → Option Signature) (j : Port) (s : Log) :
    sig (portTrans pk sign j s).2 = sigNext j s := by
  cases j with
  | pk => rfl
  | sign m =>
    simp only [portTrans, sigNext]
    split_ifs
    · simp only [sig, sigFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]
    · rfl

theorem prefix_sigNext (j : Port) (s : Log) : sig s <+: sigNext j s := by
  cases j with
  | pk => exact List.prefix_refl _
  | sign m =>
    simp only [sigNext]
    split_ifs
    · exact prefix_sigStep _ _
    · exact List.prefix_refl _

theorem hidGame_trans (d : Data) (j : Port) (s : Log) :
    (hidGame d).trans j s = portTrans (keysH (d none) (hOf d)).1 (signH (d none) (hOf d)) j s := rfl

/-! ## The hidden game reads only logged digests -/

theorem chainKeys_ne_dig (h : Key → HashOutput) (m' : Message) {q : Option Key} (hq : q ∈ chainKeys h m')
    (m : Message) (c : DigestCall) : q ≠ some (.dig m c) := by
  unfold chainKeys at hq
  split at hq
  · simp at hq
  · simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq
    obtain ⟨x, rfl⟩ := hq
    rcases chainKey_cases x.1 _ _ x.2 _ with h' | ⟨j, h'⟩ <;> rw [h'] <;> simp

theorem dig_mem_sig {d : Data} {s : Log} {m : Message} {c : DigestCall}
    (h : some (.dig m c) ∈ rev d s) : m ∈ sig s := by
  rw [mem_sig]
  rcases mem_rev.mp h with hb | hd
  · simp only [baseKeys, pubKeys, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_biUnion, List.mem_toFinset] at hb
    rcases hb with (hb | hb) | ⟨e, he, hk⟩
    · cases hb
    · cases hb
    · refine ⟨e, he, ?_⟩
      classical
      simp only [keysRead, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and] at hk
      rcases hk with hk | ((((⟨call, hk⟩ | ⟨x, hk⟩) | ⟨κ, hk⟩) | ⟨⟨p, hp⟩, hk⟩) | hk)
      · cases hk
      · cases hk; rfl
      · cases hk
      · cases hk
      · cases hk
      · exact absurd rfl (chainKeys_ne_dig _ _ hk m c)
  · have hq : some (Key.rnd m) ∈ deps (.dig m c) := by simp [deps]
    exact inv_of_mem_rev d s _ (mem_rev.mpr (hd _ hq))

/-! ## The deferred game -/

/-- The digests of the messages of `l`, the `i`-th getting `δ i`. -/
def dgOf (δ : Fin signatureLimit → DigV) (l : List Message) : Message → DigV := fun m ↦
  if h : l.idxOf m < signatureLimit then δ ⟨_, h⟩ else 0

theorem dgOf_corr {l : List Message} (hl : l.length ≤ signatureLimit) {Dg : Message → DigV}
    {δ : Fin signatureLimit → DigV} (hc : OvGame.Corr l Dg δ) {m : Message} (hm : m ∈ l) :
    Dg m = dgOf δ l m := by
  have hi : l.idxOf m < l.length := List.idxOf_lt_length_iff.mpr hm
  have hq : l.idxOf m < signatureLimit := lt_of_lt_of_le hi hl
  have := hc _ hi hq
  rw [List.get_eq_getElem, List.getElem_idxOf hi] at this
  rw [this, dgOf, dite_eq_left hq]

/-- The game that answers the `i`-th distinct logged message with the digests `δ i`. -/
def gB (r : Data) (δ : Fin signatureLimit → DigV) : OvGame Input HashOutput Log Port Res where
  init := Log.empty
  ov := fun s ↦ (hidGame (withDig r (dgOf δ (sig s)))).ov s
  trans := fun j s ↦ (hidGame (withDig r (dgOf δ (sigNext j s)))).trans j s

theorem agree_of_corr (r : Data) {Dg : Message → DigV} {δ : Fin signatureLimit → DigV}
    {l : List Message} (hl : l.length ≤ signatureLimit) (hc : OvGame.Corr l Dg δ) (s : Log)
    (hsub : ∀ m c, some (.dig m c) ∈ rev (withDig r Dg) s → m ∈ l) :
    ∀ q ∈ rev (withDig r Dg) s, withDig r Dg q = withDig r (dgOf δ l) q := by
  intro q hq
  by_cases hd : ∃ m c, q = some (.dig m c)
  · obtain ⟨m, c, rfl⟩ := hd
    rw [withDig_dig, withDig_dig, dgOf_corr hl hc (hsub m c hq)]
  · push Not at hd
    rw [withDig_of_ne _ _ q hd, withDig_of_ne _ _ q hd]

theorem sig_trans_hid (d : Data) (j : Port) (s : Log) : sig ((hidGame d).trans j s).2 = sigNext j s := by
  rw [hidGame_trans, sig_portTrans]

theorem sig_trans_gB (r : Data) (δ : Fin signatureLimit → DigV) (j : Port) (s : Log) :
    sig ((gB r δ).trans j s).2 = sigNext j s := by
  change sig ((hidGame (withDig r (dgOf δ (sigNext j s)))).trans j s).2 = _
  exact sig_trans_hid _ j s

/-- **The deferral of the signed digests.** -/
theorem deferral_dig (r : Data) (eA : (Message → DigV) → (Σ u, QuantumComp₂.Leaf (QReg.of Unit)
      (PublicKey × Forgery) u) → Log → Bool)
    (eB : (Fin signatureLimit → DigV) → (Σ u, QuantumComp₂.Leaf (QReg.of Unit)
      (PublicKey × Forgery) u) → Log → Bool)
    (hev : ∀ Dg δ p s, OvGame.Corr (sig s) Dg δ → eA Dg p s = true → eB δ p s = true)
    (G : Input → HashOutput) {A : QReg} (adv : Adversary A) (ρ : SubState A) :
    (Fintype.card (Message → DigV) : ℝ≥0∞)⁻¹ *
        ∑ Dg, OvGame.sideW (hidGame (withDig r Dg)) G .instruments (withKey adv) ρ (eA Dg) ≤
      (Fintype.card (Fin signatureLimit → DigV) : ℝ≥0∞)⁻¹ *
        ∑ δ, OvGame.sideW (gB r δ) G .instruments (withKey adv) ρ (eB δ) := by
  have hmA : ∀ Dg j s, sig s <+: sig ((hidGame (withDig r Dg)).trans j s).2 := fun Dg j s ↦ by
    rw [sig_trans_hid]; exact prefix_sigNext j s
  have hmB : ∀ δ j s, sig s <+: sig ((gB r δ).trans j s).2 := fun δ j s ↦ by
    rw [sig_trans_gB]; exact prefix_sigNext j s
  have hcorr : ∀ Dg δ s, OvGame.Corr (sig s) Dg δ →
      (hidGame (withDig r Dg)).ov s = (gB r δ).ov s := by
    intro Dg δ s hc
    change _ = (hidGame (withDig r (dgOf δ (sig s)))).ov s
    exact hidGame_local (withDig r Dg) (withDig r (dgOf δ (sig s))) s
      (agree_of_corr r (length_sig_le s) hc s fun m c h ↦ dig_mem_sig h)
  have hcorrTr : ∀ Dg δ j s, OvGame.Corr (sig ((hidGame (withDig r Dg)).trans j s).2) Dg δ ∨
      OvGame.Corr (sig ((gB r δ).trans j s).2) Dg δ →
      (hidGame (withDig r Dg)).trans j s = (gB r δ).trans j s := by
    intro Dg δ j s hc
    have hc' : OvGame.Corr (sigNext j s) Dg δ := by
      rcases hc with hc | hc
      · rwa [sig_trans_hid] at hc
      · rwa [sig_trans_gB] at hc
    have hl : (sigNext j s).length ≤ signatureLimit := by
      rw [← sig_trans_hid (withDig r Dg) j s]; exact length_sig_le _
    change _ = (hidGame (withDig r (dgOf δ (sigNext j s)))).trans j s
    refine hidGame_localTr (withDig r Dg) (withDig r (dgOf δ (sigNext j s))) j s
      (agree_of_corr r hl hc' _ fun m c h ↦ ?_)
    rw [← sig_trans_hid (withDig r Dg) j s]
    exact dig_mem_sig h
  exact OvGame.deferral_le (M := Message) (V := DigV) (q := signatureLimit)
    (fun Dg ↦ hidGame (withDig r Dg)) (gB r) sig nodup_sig length_sig_le
    hmA hmB hcorr hcorrTr (fun _ _ ↦ rfl) eA eB hev .instruments G (withKey adv) ρ

end Qrom.Sphincs
