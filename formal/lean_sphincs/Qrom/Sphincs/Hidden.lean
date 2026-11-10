module

public import Qrom.Sphincs.Signer
public import Qrom.Sphincs.Count

@[expose] public section

/-!
# The hidden game

In side state `s` the data `d` reveals the public key, the keys every logged signature reads, and,
closing up, every position whose input reads revealed keys only (`Qrom.Sphincs.rev`). The hidden
game answers from the data the honest inputs that read revealed keys only, and the rest with `G`
(`Qrom.Sphincs.hidGame`); it differs from the presampled game only on the protected inputs, the
honest inputs that read a key not revealed (`Qrom.Sphincs.Prot`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- The public key's keys: `PK.seed` and the top root. -/
def pubKeys : Finset (Option Key) := {some .pkSeed, some (.pos topRootPos)}

/-- The keys the public key and the logged signatures read. -/
def baseKeys (d : Data) (s : Log) : Finset (Option Key) :=
  pubKeys ∪ s.1.toFinset.biUnion fun e ↦ keysRead (hOf d) e.1

/-- The keys revealed from `B`: those of `B`, and every position whose input reads revealed keys
only. -/
inductive Revealed (B : Finset (Option Key)) : Option Key → Prop where
  | base {q : Option Key} (hq : q ∈ B) : Revealed B q
  | derive {k : Key} : (∀ q ∈ deps k, Revealed B q) → Revealed B (some k)

theorem Revealed.mono {B B' : Finset (Option Key)} (hB : B ⊆ B') {q : Option Key}
    (h : Revealed B q) : Revealed B' q := by
  induction h with
  | base hq => exact .base (hB hq)
  | derive _ ih => exact .derive ih

open Classical in
/-- The keys the data `d` reveals in side state `s`. -/
def rev (d : Data) (s : Log) : Finset (Option Key) := Finset.univ.filter (Revealed (baseKeys d s))

theorem mem_rev {d : Data} {s : Log} {q : Option Key} : q ∈ rev d s ↔ Revealed (baseKeys d s) q := by
  simp [rev]

theorem base_sub_rev (d : Data) (s : Log) : baseKeys d s ⊆ rev d s := fun _ hq ↦
  mem_rev.mpr (.base hq)

theorem derive_mem_rev {d : Data} {s : Log} {k : Key} (h : deps k ⊆ rev d s) : some k ∈ rev d s :=
  mem_rev.mpr (.derive fun _ hq ↦ mem_rev.mp (h hq))

/-- The revealed keys are read on themselves. -/
theorem rev_self (d d' : Data) (s : Log) (H : ∀ q ∈ rev d s, d q = d' q) : rev d' s = rev d s := by
  have hk : ∀ e ∈ s.1.toFinset, keysRead (hOf d') e.1 = keysRead (hOf d) e.1 := fun e he ↦
    (signExpl_local fun k hk ↦ H _ (base_sub_rev d s
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, hk⟩)))).2
  have hb : baseKeys d' s = baseKeys d s := by
    unfold baseKeys
    rw [Finset.biUnion_congr rfl hk]
  ext q
  rw [mem_rev, mem_rev, hb]

/-! ## The hidden game -/

/-- The honest inputs that read a key the data does not reveal in `s`. -/
def Prot (d : Data) (s : Log) (x : Input) : Prop :=
  ∃ k, ¬ deps k ⊆ rev d s ∧ pt (hOf d) (d none) k = x

/-- The hidden game: the honest inputs reading revealed keys only answered from the data. -/
def hidGame (d : Data) : OvGame Input HashOutput Log Port Res where
  init := Log.empty
  ov := fun s x ↦ if hx : ∃ k, deps k ⊆ rev d s ∧ pt (hOf d) (d none) k = x then
    some (d (some (Classical.choose hx))) else none
  trans := (presGame d).trans

theorem pt_inj (d : Data) {k k' : Key} (h : pt (hOf d) (d none) k = pt (hOf d) (d none) k') : k = k' :=
  input_cross_injective (congrArg Subtype.val h)

theorem dite_congr_choose {α β : Type} {P P' : α → Prop} {_ : Decidable (∃ a, P a)}
    {_ : Decidable (∃ a, P' a)} (hPP : ∀ a, P a ↔ P' a) (f f' : α → β)
    (hff : ∀ a, P a → f a = f' a) (huniq : ∀ a b, P a → P b → a = b) :
    (if h : ∃ a, P a then some (f (Classical.choose h)) else none) =
      (if h : ∃ a, P' a then some (f' (Classical.choose h)) else none) := by
  by_cases h : ∃ a, P a
  · have h' : ∃ a, P' a := h.imp fun a ha ↦ (hPP a).mp ha
    rw [dite_eq_left h, dite_eq_left h']
    have e := huniq _ _ (Classical.choose_spec h) ((hPP _).mpr (Classical.choose_spec h'))
    rw [hff _ (Classical.choose_spec h), e]
  · have h' : ¬ ∃ a, P' a := fun ⟨a, ha⟩ ↦ h ⟨a, (hPP a).mpr ha⟩
    rw [dite_eq_right h, dite_eq_right h']

theorem presGame_ov (d : Data) (s : Log) (x : Input) :
    (presGame d).ov s x = if hx : ∃ k, pt (hOf d) (d none) k = x then
      some (d (some (Classical.choose hx))) else none := rfl

/-- Off the protected inputs, the hidden game answers as the presampled game. -/
theorem hidGame_ov (d : Data) (s : Log) (x : Input) (hx : ¬ Prot d s x) :
    (presGame d).ov s x = (hidGame d).ov s x := by
  rw [presGame_ov]
  simp only [hidGame]
  refine dite_congr_choose (P := fun k ↦ pt (hOf d) (d none) k = x)
    (P' := fun k ↦ deps k ⊆ rev d s ∧ pt (hOf d) (d none) k = x) ?_ (fun k ↦ d (some k))
    (fun k ↦ d (some k)) ?_ ?_
  · intro k
    refine ⟨fun hk ↦ ⟨?_, hk⟩, fun hk ↦ hk.2⟩
    by_contra hn
    exact hx ⟨k, hn, hk⟩
  · intro _ _
    rfl
  · intro a b ha hb
    exact pt_inj d (ha.trans hb.symm)

/-- The hidden game's answers in `s` read the revealed keys only. -/
theorem hidGame_local (d d' : Data) (s : Log) (H : ∀ q ∈ rev d s, d q = d' q) :
    (hidGame d).ov s = (hidGame d').ov s := by
  have hrev := rev_self d d' s H
  have hpt : ∀ k, deps k ⊆ rev d s → pt (hOf d) (d none) k = pt (hOf d') (d' none) k :=
    fun k hk ↦ Subtype.ext (input_dep k fun q hq ↦ H q (hk hq))
  funext x
  simp only [hidGame]
  refine dite_congr_choose (P := fun k ↦ deps k ⊆ rev d s ∧ pt (hOf d) (d none) k = x)
    (P' := fun k ↦ deps k ⊆ rev d' s ∧ pt (hOf d') (d' none) k = x) ?_ (fun k ↦ d (some k))
    (fun k ↦ d' (some k)) ?_ ?_
  · intro k
    rw [hrev]
    exact ⟨fun hk ↦ ⟨hk.1, (hpt k hk.1).symm.trans hk.2⟩, fun hk ↦ ⟨hk.1, (hpt k hk.1).trans hk.2⟩⟩
  · intro k hk
    exact H _ (derive_mem_rev hk.1)
  · intro a b ha hb
    exact pt_inj d (ha.2.trans hb.2.symm)

theorem pubKeys_sub_rev (d : Data) (s : Log) : pubKeys ⊆ rev d s :=
  fun _ hq ↦ base_sub_rev d s (Finset.mem_union_left _ hq)

theorem keysRead_sub_rev (d : Data) (s : Log) (e : Message × Option Signature) (he : e ∈ s.1) :
    keysRead (hOf d) e.1 ⊆ rev d s := fun _ hq ↦
  base_sub_rev d s (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, List.mem_toFinset.mpr he, hq⟩))

theorem signH_local (d d' : Data) (m : Message) (H : ∀ q ∈ keysRead (hOf d) m, d q = d' q) :
    signH (d' none) (hOf d') m = signH (d none) (hOf d) m := by
  exact (signH_eq _ _ m).trans ((signExpl_local fun k hk ↦ H _ hk).1.trans (signH_eq _ _ m).symm)

/-- A transition reads the keys revealed in the side state it leads to. -/
theorem hidGame_localTr (d d' : Data) (j : Port) (s : Log)
    (H : ∀ q ∈ rev d ((hidGame d).trans j s).2, d q = d' q) :
    (hidGame d).trans j s = (hidGame d').trans j s := by
  cases j with
  | pk =>
    have h0 := H (some .pkSeed) (pubKeys_sub_rev d _ (by simp [pubKeys]))
    have h1 := H (some (.pos topRootPos)) (pubKeys_sub_rev d _ (by simp [pubKeys]))
    show ((keysH (d none) (hOf d)).1, s) = ((keysH (d' none) (hOf d')).1, s)
    simp only [keysH, dataOf_root, param, hOf]
    rw [h0, h1]
  | sign m =>
    simp only [hidGame, presGame, portTrans] at H ⊢
    split_ifs at H ⊢ with hlen
    · have hs := signH_local d d' m fun q hq ↦ H q (keysRead_sub_rev d _ (m, _)
        (List.mem_append_right _ (List.mem_singleton_self _)) hq)
      simp only [hs]
    · rfl

/-- The revealed keys only grow. -/
theorem rev_mono (d : Data) (j : Port) (s : Log) : rev d s ⊆ rev d ((hidGame d).trans j s).2 := by
  have hb : ∀ s' : Log, s.1 ⊆ s'.1 → rev d s ⊆ rev d s' := by
    intro s' hs q hq
    refine mem_rev.mpr (Revealed.mono (fun r hr ↦ ?_) (mem_rev.mp hq))
    simp only [baseKeys, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset] at hr ⊢
    rcases hr with hr | ⟨e, he, hr⟩
    · exact Or.inl hr
    · exact Or.inr ⟨e, hs he, hr⟩
  cases j with
  | pk => exact hb _ (List.Subset.refl _)
  | sign m =>
    simp only [hidGame, presGame, portTrans]
    split_ifs
    · exact hb _ (List.subset_append_left _ _)
    · exact hb _ (List.Subset.refl _)

open Classical in
/-- **At most a fraction `2^-128` of the hidden values protect an input.** -/
theorem card_prot_le (d : Data) (s : Log) (x : Input) :
    ((Finset.univ.filter fun b ↦ Prot (merge (rev d s) d b) s x).card : ℝ) ≤
      (2 : ℝ)⁻¹ ^ 128 * Fintype.card ({q // q ∉ rev d s} → HashOutput) := by
  set R := rev d s
  by_cases hex : ∃ b₀, Prot (merge R d b₀) s x
  · obtain ⟨b₀, k₀, hk₀, hpt₀⟩ := hex
    have hR₀ : rev (merge R d b₀) s = R :=
      rev_self d _ s fun q hq ↦ (merge_agree R d b₀ q hq).symm
    rw [hR₀] at hk₀
    obtain ⟨q₀, hq₀deps, hq₀R⟩ := Finset.not_subset.mp hk₀
    refine card_trunc_at_le (⟨q₀, hq₀R⟩ : {q // q ∉ R}) (truncateHash (b₀ ⟨q₀, hq₀R⟩)) _ ?_
    rintro b ⟨k, -, hpt⟩
    have hval : inputD (merge R d b) k = inputD (merge R d b₀) k₀ :=
      congrArg Subtype.val (hpt.trans hpt₀.symm)
    have hkk : k = k₀ := input_cross_injective hval
    subst hkk
    have := input_embed hval q₀ hq₀deps
    simpa [merge, hq₀R] using this
  · have : (Finset.univ.filter fun b ↦ Prot (merge R d b) s x) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun b _ hb ↦ hex ⟨b, hb⟩
    rw [this, Finset.card_empty, Nat.cast_zero]
    positivity

end Qrom.Sphincs
