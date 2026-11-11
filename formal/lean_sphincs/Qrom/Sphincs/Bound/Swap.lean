module

public import Qrom.Sphincs.Bound.Terms

@[expose] public section

/-!
# Hits and encoding collisions

The verifier may read an input that is no honest input at which `G` hits the honest value of its
address, or an encoding input of a counter other than the one the signer finds, whose value in the
data carries the key's word (`Qrom.Sphincs.HitE`). Such a counter is above the found one, and the
honest computation never reads the data there: the inputs read no encoding values, and the signer
reads the counters up to the one it finds (`Qrom.Sphincs.encH_congr_found`,
`Qrom.Sphincs.signExpl_same`). Exchanging the data above the
found counters with `G` at their inputs is then an involution of the pairs `(d, G)`
(`Qrom.Sphincs.swapE`) that carries the hidden game to one answering those inputs by `G` once
revealed (`Qrom.Sphincs.answer_swap`), where both events are hits of `G`. Averaged over the data and
`G`, they weigh at most `2^-128 (√(2 + 4 · 2^-128) (n + 1 + verifyQueries) + 2 verifyQueries)² tr ρ`
(`Qrom.Sphincs.avg_hit_le`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- `encH` reads only the counters it tries. -/
theorem encH_congr_below {h h' : Key → HashOutput} (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    ∀ n c₀, (∀ j, c₀ ≤ j → j < c₀ + n → h (.enc lay tree leaf (BitVec.ofNat counterBits j)) =
      h' (.enc lay tree leaf (BitVec.ofNat counterBits j))) →
      encH h lay tree leaf n c₀ = encH h' lay tree leaf n c₀ := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro c₀ H
    simp only [encH]
    rw [H c₀ le_rfl (by omega), ih (c₀ + 1) fun j h1 h2 ↦ H j (by omega) (by omega)]

/-- What `encH` finds: the first counter whose value decodes, found by any search that reaches it. -/
theorem encH_spec (h : Key → HashOutput) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    ∀ n c₀ cw, encH h lay tree leaf n c₀ = some cw → ∃ j, c₀ ≤ j ∧ j < c₀ + n ∧
      cw.1 = BitVec.ofNat counterBits j ∧
      TargetSum.decodeDigest (truncateHash (h (.enc lay tree leaf (BitVec.ofNat counterBits j)))) =
        some cw.2 ∧
      (∀ j', c₀ ≤ j' → j' < j →
        TargetSum.decodeDigest (truncateHash (h (.enc lay tree leaf (BitVec.ofNat counterBits j')))) =
          none) ∧
      ∀ m, j < c₀ + m → encH h lay tree leaf m c₀ = some cw := by
  intro n
  induction n with
  | zero => intro _ _ h0; simp [encH] at h0
  | succ n ih =>
    intro c₀ cw hn
    simp only [encH] at hn
    split at hn
    · rename_i w hw
      cases hn
      refine ⟨c₀, le_rfl, by omega, rfl, hw, fun j' h1 h2 ↦ by omega, fun m hm ↦ ?_⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [encH, hw]
    · rename_i hw
      obtain ⟨j, h1, h2, h3, h4, h5, h6⟩ := ih (c₀ + 1) cw hn
      refine ⟨j, by omega, by omega, h3, h4, fun j' h1' h2' ↦ ?_, fun m hm ↦ ?_⟩
      · rcases Nat.eq_or_lt_of_le h1' with rfl | hlt
        · exact hw
        · exact h5 j' (by omega) h2'
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [encH, hw]
        exact h6 m' (by omega)

theorem decodeDigest_valid {x : Digest} {w : Encoding} (h : TargetSum.decodeDigest x = some w) :
    TargetSum.Valid w := by
  unfold TargetSum.decodeDigest at h
  split at h
  · cases h; assumption
  · cases h

/-! ## The counters above the found ones -/

/-- `k` is a counter of an encoding key above the one the signer finds. -/
def Above (d : Data) (k : Key) : Prop :=
  ∃ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : Counter) (cw : Counter × Encoding),
    k = .enc lay tree leaf c ∧ encH (hOf d) lay tree leaf encodingAttemptLimit 0 = some cw ∧
    cw.1.toNat < c.toNat

/-- An encoding key. -/
def IsEnc : Key → Prop
  | .enc .. => True
  | _ => False

theorem not_isEnc_of_above {d : Data} {k : Key} (h : ¬ IsEnc k) : ¬ Above d k := by
  rintro ⟨_, _, _, _, _, rfl, -⟩
  exact h trivial

theorem rank_le (k : Key) : rank k ≤ 3 + maxDepth := by
  cases k
  case pos p => have := depth_le p; simp only [rank]; omega
  all_goals simp only [rank]; omega

theorem not_isEnc_of_rank_lt {k k' : Key} (h : rank k' < rank k) : ¬ IsEnc k' := by
  have := rank_le k
  cases k' with
  | enc => exact absurd (lt_of_lt_of_le h (rank_le k)) (by simp [rank])
  | _ => exact id

/-- Data that agree off the encoding keys and find the same encodings. -/
structure Same (d d' : Data) : Prop where
  seed : d none = d' none
  off : ∀ k, ¬ IsEnc k → d (some k) = d' (some k)
  enc : ∀ lay tree leaf, encH (hOf d) lay tree leaf encodingAttemptLimit 0 =
    encH (hOf d') lay tree leaf encodingAttemptLimit 0

theorem same_pt {d d' : Data} (h : Same d d') (k : Key) :
    pt (hOf d) (d none) k = pt (hOf d') (d' none) k := by
  apply Subtype.ext
  show input (hOf d) (d none) k = input (hOf d') (d' none) k
  rw [h.seed]
  exact input_congr (d' none) k fun k' hk' ↦ h.off k' (not_isEnc_of_rank_lt hk')

theorem same_above {d d' : Data} (h : Same d d') (k : Key) : Above d k ↔ Above d' k := by
  simp only [Above, h.enc]

/-- The signature reads no encoding value but through the encodings it finds. -/
theorem signExpl_same {h h' : Key → HashOutput} {m : Message} (H : ∀ k, ¬ IsEnc k → h k = h' k)
    (henc : ∀ lay tree leaf, encH h lay tree leaf encodingAttemptLimit 0 =
      encH h' lay tree leaf encodingAttemptLimit 0) :
    signExpl h' m = signExpl h m ∧ keysRead h' m = keysRead h m := by
  have hdig : digestH h' m = digestH h m := by
    unfold digestH
    congr 1
    funext call
    exact (H _ id).symm
  have hrnd : rndOf h' m = rndOf h m := congrArg truncateHash (H _ id).symm
  set index := digestIndex (digestH h m) with hindex
  set leaves := digestLeaves (digestH h m) with hleaves
  have hall : Completeness.allSome (fun lay ↦ encH h' lay (treeIndexAt index lay)
      (leafIndexAt index lay) encodingAttemptLimit 0) = Completeness.allSome (fun lay ↦ encH h lay
      (treeIndexAt index lay) (leafIndexAt index lay) encodingAttemptLimit 0) := by
    simp only [henc]
  have hfors : assembledFors (dataOf h') (tableOf h') index leaves =
      assembledFors (dataOf h) (tableOf h) index leaves := by
    funext κ
    simp only [assembledFors]
    rw [forsPath_congr index (fun p _ ↦ (H _ id).symm)]
    congr 1
    exact congrArg truncateHash (H _ id).symm
  constructor
  · unfold signExpl
    rw [hdig, ← hindex, ← hleaves, hall, hrnd, hfors]
    cases hres : Completeness.allSome (fun lay ↦ encH h lay (treeIndexAt index lay)
        (leafIndexAt index lay) encodingAttemptLimit 0) with
    | none => rfl
    | some found =>
      simp only [Option.map_some, Option.some.injEq, Signature.mk.injEq, true_and]
      funext lay
      simp only [layerSignatures]
      rw [treePath_congr index (fun p _ ↦ (H _ id).symm)]
      congr 1
      funext chain
      simp only [assembledValues, tableOf, HiddenGraph.coordinates]
      split_ifs
      · exact congrArg truncateHash (H _ id).symm
      · exact congrArg truncateHash (H _ id).symm
  · unfold keysRead chainKeys
    rw [hdig, ← hindex, ← hleaves, hall]

theorem same_signH {d d' : Data} (h : Same d d') :
    signH (d none) (hOf d) = signH (d' none) (hOf d') := by
  funext m
  exact (signH_eq _ _ m).trans (((signExpl_same h.off h.enc).1.symm).trans (signH_eq _ _ m).symm)

theorem same_keysRead {d d' : Data} (h : Same d d') (m : Message) :
    keysRead (hOf d) m = keysRead (hOf d') m :=
  (signExpl_same h.off h.enc).2.symm

theorem same_keysH {d d' : Data} (h : Same d d') : keysH (d none) (hOf d) = keysH (d' none) (hOf d') := by
  have hl : labelsOf (hOf d) = labelsOf (hOf d') := funext fun q ↦ h.off (.pos q) id
  have hp : param (hOf d) = param (hOf d') := congrArg truncateHash (h.off .pkSeed id)
  have hf : hOf d .prf = hOf d' .prf := h.off .prf id
  unfold keysH dataOf
  rw [hl, hp, hf, h.seed]

theorem same_rev {d d' : Data} (h : Same d d') (s : Log) : rev d s = rev d' s := by
  unfold rev baseKeys
  rw [show (fun e : Message × Option Signature ↦ keysRead (hOf d) e.1) =
    fun e ↦ keysRead (hOf d') e.1 from funext fun e ↦ same_keysRead h e.1]

theorem same_trans {d d' : Data} (h : Same d d') : (hidGame d).trans = (hidGame d').trans := by
  show portTrans (keysH (d none) (hOf d)).1 (signH (d none) (hOf d)) =
    portTrans (keysH (d' none) (hOf d')).1 (signH (d' none) (hOf d'))
  rw [same_keysH h, same_signH h]

/-! ## The exchange -/

open Classical in
/-- The data with the values above the found counters taken from `G` at their inputs. -/
def swapD (d : Data) (G : Input → HashOutput) : Data
  | none => d none
  | some k => if Above d k then G (pt (hOf d) (d none) k) else d (some k)

open Classical in
/-- `G` with the values at the inputs above the found counters taken from the data. -/
def swapG (d : Data) (G : Input → HashOutput) (x : Input) : HashOutput :=
  if hx : ∃ k, Above d k ∧ pt (hOf d) (d none) k = x then d (some (Classical.choose hx)) else G x

theorem swapD_of_not {d : Data} {G : Input → HashOutput} {k : Key} (h : ¬ Above d k) :
    swapD d G (some k) = d (some k) := by
  simp only [swapD]
  exact ite_eq_right h

theorem swapD_of_above {d : Data} {G : Input → HashOutput} {k : Key} (h : Above d k) :
    swapD d G (some k) = G (pt (hOf d) (d none) k) := by
  simp only [swapD]
  exact ite_eq_left h

theorem swapG_pt {d : Data} {G : Input → HashOutput} {k : Key} (h : Above d k) :
    swapG d G (pt (hOf d) (d none) k) = d (some k) := by
  have hx : ∃ k', Above d k' ∧ pt (hOf d) (d none) k' = pt (hOf d) (d none) k := ⟨k, h, rfl⟩
  rw [swapG, dite_eq_left hx, pt_inj d (Classical.choose_spec hx).2]

theorem swapG_of_not {d : Data} {G : Input → HashOutput} {x : Input}
    (h : ¬ ∃ k, Above d k ∧ pt (hOf d) (d none) k = x) : swapG d G x = G x := by
  rw [swapG, dite_eq_right h]

/-- `encH` stops at the counter it finds. -/
theorem encH_congr_found {h h' : Key → HashOutput} {lay : Layer} {tree : TreeIndex} {leaf : LeafIndex}
    {cw : Counter × Encoding} (hf : encH h lay tree leaf encodingAttemptLimit 0 = some cw)
    (H : ∀ c : Counter, c.toNat ≤ cw.1.toNat → h (.enc lay tree leaf c) = h' (.enc lay tree leaf c)) :
    encH h' lay tree leaf encodingAttemptLimit 0 = some cw := by
  have hlim : encodingAttemptLimit = 2 ^ counterBits := rfl
  obtain ⟨j, -, hj, hcw, -, -, hstop⟩ := encH_spec h lay tree leaf _ 0 cw hf
  have hjt : cw.1.toNat = j := by
    rw [hcw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hlim] at hj; omega)]
  have h1 : encH h' lay tree leaf (j + 1) 0 = some cw := by
    rw [← hstop (j + 1) (by omega)]
    refine (encH_congr_below lay tree leaf (j + 1) 0 fun j' _ hj' ↦ ?_).symm
    refine H _ ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hlim] at hj; omega)]
    omega
  obtain ⟨j', -, hj', -, -, -, hstop'⟩ := encH_spec h' lay tree leaf _ 0 cw h1
  exact hstop' _ (by omega)

theorem same_swap (d : Data) (G : Input → HashOutput) : Same d (swapD d G) where
  seed := rfl
  off k hk := (swapD_of_not (not_isEnc_of_above hk)).symm
  enc lay tree leaf := by
    cases hE : encH (hOf d) lay tree leaf encodingAttemptLimit 0 with
    | none =>
      rw [← hE]
      refine encH_congr lay tree leaf (fun c ↦ ?_) _ _
      refine (swapD_of_not ?_).symm
      rintro ⟨lay', tree', leaf', c', cw, hk, hf, -⟩
      simp only [Key.enc.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
      rw [hE] at hf
      cases hf
    | some cw =>
      refine (encH_congr_found hE fun c hc ↦ (swapD_of_not ?_).symm).symm
      rintro ⟨lay', tree', leaf', c', cw', hk, hf, hlt⟩
      simp only [Key.enc.injEq] at hk
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
      rw [hE] at hf
      cases hf
      omega

theorem swapD_swap (d : Data) (G : Input → HashOutput) :
    swapD (swapD d G) (swapG d G) = d := by
  have hS := same_swap d G
  funext q
  cases q with
  | none => rfl
  | some k =>
    by_cases ha : Above d k
    · rw [swapD_of_above ((same_above hS k).mp ha), ← same_pt hS k, swapG_pt ha]
    · rw [swapD_of_not (mt (same_above hS k).mpr ha), swapD_of_not ha]

theorem swapG_swap (d : Data) (G : Input → HashOutput) :
    swapG (swapD d G) (swapG d G) = G := by
  have hS := same_swap d G
  funext x
  by_cases hx : ∃ k, Above d k ∧ pt (hOf d) (d none) k = x
  · obtain ⟨k, ha, rfl⟩ := hx
    rw [same_pt hS k, swapG_pt ((same_above hS k).mp ha), swapD_of_above ha, same_pt hS k]
  · rw [swapG_of_not, swapG_of_not hx]
    rintro ⟨k, ha, hk⟩
    exact hx ⟨k, (same_above hS k).mpr ha, (same_pt hS k).trans hk⟩

/-- **The exchange**, an involution of the pairs of data and functions. -/
def swapE : Data × (Input → HashOutput) ≃ Data × (Input → HashOutput) :=
  Function.Involutive.toPerm (fun p ↦ (swapD p.1 p.2, swapG p.1 p.2)) fun p ↦
    Prod.ext (swapD_swap p.1 p.2) (swapG_swap p.1 p.2)

/-! ## The exchanged game -/

open Classical in
/-- The hidden game with the revealed inputs above the found counters answered by `G`, and the
unrevealed ones from the data. -/
def hidX (e : Data) : OvGame Input HashOutput Log Port Res where
  init := Log.empty
  ov := fun s x ↦ if hx : ∃ k, Above e k ∧ pt (hOf e) (e none) k = x then
      (if deps (Classical.choose hx) ⊆ rev e s then none else some (e (some (Classical.choose hx))))
    else (hidGame e).ov s x
  trans := (hidGame e).trans

theorem hidGame_ov_pt (d : Data) (s : Log) (k : Key) :
    (hidGame d).ov s (pt (hOf d) (d none) k) =
      if deps k ⊆ rev d s then some (d (some k)) else none := by
  simp only [hidGame]
  by_cases hr : deps k ⊆ rev d s
  · have hx : ∃ k', deps k' ⊆ rev d s ∧ pt (hOf d) (d none) k' = pt (hOf d) (d none) k := ⟨k, hr, rfl⟩
    rw [dite_eq_left hx, ite_eq_left hr, pt_inj d (Classical.choose_spec hx).2]
  · rw [ite_eq_right hr]
    refine dite_eq_right fun ⟨k', hr', hk'⟩ ↦ hr ?_
    rwa [pt_inj d hk'] at hr'

open Classical in
/-- **The exchange carries the hidden game's answers to the exchanged game's.** -/
theorem answer_swap (d : Data) (G : Input → HashOutput) (s : Log) (x : Input) :
    (hidGame d).answer s G x = (hidX (swapD d G)).answer s (swapG d G) x := by
  have hS := same_swap d G
  set d' := swapD d G
  unfold OvGame.answer
  by_cases hx : ∃ k, Above d k ∧ pt (hOf d) (d none) k = x
  · obtain ⟨k, ha, rfl⟩ := hx
    have hx' : ∃ k', Above d' k' ∧ pt (hOf d') (d' none) k' = pt (hOf d) (d none) k :=
      ⟨k, (same_above hS k).mp ha, (same_pt hS k).symm⟩
    have hck : Classical.choose hx' = k :=
      pt_inj d' ((Classical.choose_spec hx').2.trans (same_pt hS k))
    show _ = ((if hx : ∃ k', Above d' k' ∧ pt (hOf d') (d' none) k' = pt (hOf d) (d none) k then
      (if deps (Classical.choose hx) ⊆ rev d' s then none else some (d' (some (Classical.choose hx))))
      else (hidGame d').ov s (pt (hOf d) (d none) k))).getD (swapG d G (pt (hOf d) (d none) k))
    rw [dite_eq_left hx', hck, hidGame_ov_pt, ← same_rev hS s, swapG_pt ha]
    by_cases hr : deps k ⊆ rev d s
    · rw [ite_eq_left hr, ite_eq_left hr]
      rfl
    · rw [ite_eq_right hr, ite_eq_right hr]
      exact (swapD_of_above ha).symm
  · have hx' : ¬ ∃ k', Above d' k' ∧ pt (hOf d') (d' none) k' = x := by
      rintro ⟨k, ha, hk⟩
      exact hx ⟨k, (same_above hS k).mpr ha, (same_pt hS k).trans hk⟩
    show _ = ((if hx : ∃ k', Above d' k' ∧ pt (hOf d') (d' none) k' = x then
      (if deps (Classical.choose hx) ⊆ rev d' s then none else some (d' (some (Classical.choose hx))))
      else (hidGame d').ov s x)).getD (swapG d G x)
    have hov : (hidGame d).ov s x = (hidGame d').ov s x := by
      simp only [hidGame]
      refine dite_congr_choose (P := fun k ↦ deps k ⊆ rev d s ∧ pt (hOf d) (d none) k = x)
        (P' := fun k ↦ deps k ⊆ rev d' s ∧ pt (hOf d') (d' none) k = x) ?_ (fun k ↦ d (some k))
        (fun k ↦ d' (some k)) ?_ ?_
      · intro k
        rw [same_rev hS s, same_pt hS k]
      · intro k hk
        exact (swapD_of_not fun ha ↦ hx ⟨k, ha, hk.2⟩).symm
      · intro a b ha hb
        exact pt_inj d (ha.2.trans hb.2.symm)
    rw [dite_eq_right hx', swapG_of_not hx, hov]

/-! ## The bound -/

open Classical in
/-- `G` hits at an input the verifier read, in the exchanged game. -/
def evX (e : Data) (G : Input → HashOutput) (b : Bool × List HashInput) : Bool :=
  decide (∃ z ∈ outK b, good e z (G z))

/-- A read encoding collision is above the found counter. -/
theorem above_of_encAt {d : Data} {x : Input} (h : EncAt d x) :
    ∃ k, Above d k ∧ pt (hOf d) (d none) k = x ∧
      ∃ lay tree leaf c, k = .enc lay tree leaf c ∧
        truncateHash (hOf d k) = encTarget d lay tree leaf := by
  obtain ⟨lay, tree, leaf, cw, c, hf, hne, hx, ht⟩ := h
  have hlim : encodingAttemptLimit = 2 ^ counterBits := rfl
  obtain ⟨j, -, hj, hcw, hdec, hbelow, -⟩ := encH_spec (hOf d) lay tree leaf _ 0 cw hf
  have hjt : cw.1.toNat = j := by
    rw [hcw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hlim] at hj; omega)]
  have hv : TargetSum.Valid cw.2 := decodeDigest_valid hdec
  have hgt : cw.1.toNat < c.toNat := by
    rcases lt_trichotomy c.toNat cw.1.toNat with hlt | heq | hgt
    · have hb := hbelow c.toNat (Nat.zero_le _) (by omega)
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, ht, Completeness.decodeDigest_pack _ hv] at hb
      cases hb
    · exact absurd (BitVec.eq_of_toNat_eq heq) hne
    · exact hgt
  refine ⟨_, ⟨lay, tree, leaf, c, cw, rfl, hf, hgt⟩, hx, lay, tree, leaf, c, rfl, ?_⟩
  rw [ht]
  unfold encTarget wordH
  rw [hf]
  rfl

theorem good_same {d e : Data} (h : Same d e) {x : Input} {y : HashOutput} (hg : good d x y) :
    good e x y := by
  rcases hg with ⟨p, pa, pl, hx, hy⟩ | ⟨lay, tree, leaf, pa, pl, hx, hy⟩
  · exact Or.inl ⟨p, pa, pl, hx, hy.trans (congrArg truncateHash (h.off (.pos p) id))⟩
  · refine Or.inr ⟨lay, tree, leaf, pa, pl, hx, hy.trans ?_⟩
    unfold encTarget wordH
    rw [h.enc]

open Classical in
/-- The exchanged event: a hit stays a hit, and a read encoding collision becomes one. -/
theorem evHit_le_evX (d : Data) (G : Input → HashOutput) (b : Bool × List HashInput)
    (h : evHit d G b = true) : evX (swapD d G) (swapG d G) b = true := by
  have hS := same_swap d G
  obtain ⟨x, hx, he⟩ := evHit_iff.mp h
  unfold evX
  rw [decide_eq_true_iff]
  rcases he with ⟨hg, hnh⟩ | he
  · refine ⟨x, hx, ?_⟩
    rw [swapG_of_not fun ⟨k, _, hk⟩ ↦ hnh k hk]
    exact good_same hS hg
  · obtain ⟨k, ha, rfl, lay, tree, leaf, c, rfl, ht⟩ := above_of_encAt he
    refine ⟨_, hx, Or.inr ⟨lay, tree, leaf, param (hOf d),
      (dataOf (hOf d)).keyMessage lay tree leaf ++ bytesBE 4 c, rfl, ?_⟩⟩
    rw [swapG_pt ha, ht]
    unfold encTarget wordH
    rw [hS.enc]

open Classical in
/-- **Hits and read encoding collisions**, averaged over the data and `G`. -/
theorem avg_hit_le {A : QReg} (adv : Adversary A) {n : ℕ}
    (hadv : ∀ pk, (adv pk).IsTotalQueryBound n) (ρ : SubState A) :
    ∑ d, ∑ G, ((Fintype.card Data : ℝ≥0∞) * Fintype.card (Input → HashOutput))⁻¹ *
      OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦
        evHit d G (evalWithAnswerFn (hidAns d G s) (verifier p.2.2))) ≤
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 *
        (√(2 + 4 * (2 : ℝ)⁻¹ ^ 128) * (1 + n + verifyQueries : ℕ) + 2 * verifyQueries) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  set cD := (Fintype.card Data : ℝ≥0∞)
  set cG := (Fintype.card (Input → HashOutput) : ℝ≥0∞)
  set B := ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 128 *
      (√(2 + 4 * (2 : ℝ)⁻¹ ^ 128) * (1 + n + verifyQueries : ℕ) + 2 * verifyQueries) ^ 2) *
    ENNReal.ofReal ρ.matrix.trace.re
  set Φ : Data × (Input → HashOutput) → ℝ≥0∞ := fun p ↦ OvGame.sideW (hidX p.1) p.2 .instruments
    (withKey adv) ρ (fun q s ↦ evX p.1 p.2 (evalWithAnswerFn (QueryImpl.ofFn ((hidX p.1).answer s p.2))
      (verifier q.2.2)))
  have hinv : (cD * cG)⁻¹ = cD⁻¹ * cG⁻¹ :=
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))
  -- each term is at most the exchanged hit
  have hle : ∀ d G, OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦
      evHit d G (evalWithAnswerFn (hidAns d G s) (verifier p.2.2))) ≤ Φ (swapE (d, G)) := by
    intro d G
    have hS := same_swap d G
    have hans : ∀ s, hidAns d G s = QueryImpl.ofFn ((hidX (swapD d G)).answer s (swapG d G)) :=
      fun s ↦ congrArg QueryImpl.ofFn (funext (answer_swap d G s))
    simp only [hans]
    refine (OvGame.sideW_congr (g := hidGame d) (g' := hidX (swapD d G)) (answer_swap d G)
      (same_trans hS) rfl .instruments (withKey adv) ρ _).trans_le ?_
    exact OvGame.sideW_mono _ _ _ _ ρ fun p s hps ↦ evHit_le_evX d G _ hps
  -- the exchanged hits, for each data
  have hX : ∀ e, ∑ G, cG⁻¹ * Φ (e, G) ≤ B := by
    intro e
    have h := OvGame.search_withVerifier_le (hidX e) (good e) (2 ^ 128) (card_good_le e)
      (withKey adv) verifier outK verifyQueries card_outK_le (1 + n) verifyQueries
      (isTotalQueryBound_withKey hadv) isTotalQueryBound_verifier ρ
    have hc : ((2 ^ 128 : ℕ) : ℝ) / Fintype.card HashOutput = (2 : ℝ)⁻¹ ^ 128 := by
      rw [card_hashOutput]
      norm_num
    rw [hc] at h
    exact h
  calc ∑ d, ∑ G, (cD * cG)⁻¹ * OvGame.sideW (hidGame d) G .instruments (withKey adv) ρ (fun p s ↦
        evHit d G (evalWithAnswerFn (hidAns d G s) (verifier p.2.2)))
      ≤ ∑ d, ∑ G, (cD * cG)⁻¹ * Φ (swapE (d, G)) :=
        Finset.sum_le_sum fun d _ ↦ Finset.sum_le_sum fun G _ ↦ mul_le_mul_right (hle d G) _
    _ = ∑ p : Data × (Input → HashOutput), (cD * cG)⁻¹ * Φ (swapE p) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ p : Data × (Input → HashOutput), (cD * cG)⁻¹ * Φ p :=
        Equiv.sum_comp swapE fun p ↦ (cD * cG)⁻¹ * Φ p
    _ = ∑ e, cD⁻¹ * ∑ G, cG⁻¹ * Φ (e, G) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun e _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun G _ ↦ ?_
        rw [hinv]; ring
    _ ≤ ∑ _e : Data, cD⁻¹ * B := Finset.sum_le_sum fun e _ ↦ mul_le_mul_right (hX e) _
    _ = B := by
        rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
          one_mul]

end Qrom.Sphincs
