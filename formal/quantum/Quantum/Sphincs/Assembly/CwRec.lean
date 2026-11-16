module

public import Quantum.Xmss.Assembly.CwRec
public import Quantum.Sphincs.Assembly.CostRefined
public import Quantum.Sphincs.Assembly.TrialHit

@[expose] public section

/-!
# The codeword-recorded mass of leanSPHINCS's counter searches

PLACEHOLDER
-/

universe u v w

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest PublicParameter HashInput HashOutput Message)
open Quantum.Xmss (X Z blocks trunc128 out256 blocks_injective)
open Quantum.Xmss.Hybrid (LazyProg restrictTo totalWeight_le_totalWeight totalWeight_add_weight
  totalWeight_const_mul_weight setProj diagMass conjTranspose_setProj setProj_mul_self
  diagMass_mono diagMass_empty progUpdate hwProgKraus_ne_zero_snd uavg runtime2_branch)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT tmplLens readLift readLiftQ
  readLens revealThen progThen RevealVals hashTrial rdRoundU rdHU liftRead tmplSpec ModedP
  modedP_bind modedP₂_bind modedP_map modedP_act modeCmdOk modeCmdNx extWeight
  ofReal_sum_ite_eq_diagMass HitPred cwHit cwQOut cwRecHw cwFresh cwFresh_nonneg cwFresh_mono
  sum_pot_cw_le cB_out_le cB splitK actK tauK potential_setProj potential_zero
  potential_conj_kron NoBot decR_step_noBot decR_branch_apply cw_readKrausK_ne_zero
  cw_readKrausK'_ne_zero cw_readKrausH_ne_zero recKraus sum_recKraus recStep recStep_branch
  eq_of_recKraus_ne_zero cw_sum_pot_setProj_le cw_sum_pot_setProj_keep cw_potential_setProj_eq_dW
  totalWeight_le_modedP_inv forallQueries_noBot noBot_init cw_clsKraus_ne_zero
  splitK' actK' hwK'Count hwK'Count_progUpdate_le querySupportedOn_recStep_hw cwFresh_le_count
  cwFreshEps cwFreshEps_nonneg forallQueries_of_charge_step querySupportedOn_runtimeR_step
  forallQueries_and isChargeBound_mono_charge isChargeBound_portCharge_zero
  totalWeight_le_of_forallQueries querySupportedOn_traceRight extCls)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/- Membership in the concrete FORS opening's sets is otherwise decided by evaluating them. -/
attribute [local irreducible] forsNeed forsSlots

/-! ## The keys of the signatures and the values they sign -/

section keys

/-- **A key of the signatures**: `K_l(idx)` for some index. -/
def InRange (K : Key) : Prop :=
  ∃ (l : Layer) (idx : Index), keyOf l idx = K

theorem inRange_keyOf (l : Layer) (idx : Index) : InRange (keyOf l idx) :=
  ⟨l, idx, rfl⟩

theorem cwMsgPos_keyOf_zero (idx : Index) : msgPos (keyOf 0 idx) = .forsKey idx := by
  have hi : idx.val < 67108864 := idx.isLt
  change ValPos.forsKey (indexBelow 0 (treeOfIndex 0 idx) (leafOfIndex 0 idx)) = .forsKey idx
  refine congrArg ValPos.forsKey (Fin.ext ?_)
  change ((treeOfIndex 0 idx).val * 2 ^ 8 + (leafOfIndex 0 idx).val) % 2 ^ 26 = idx.val
  rw [treeOfIndex_zero, leafOfIndex_zero]
  change (idx.val / 256 * 256 + idx.val % 256) % 67108864 = idx.val
  omega

theorem cwMsgPos_keyOf_one (idx : Index) :
    msgPos (keyOf 1 idx) =
      tpos 0 ⟨idx.val / 256, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) idx.isLt⟩ 8 0 := by
  have hi : idx.val < 67108864 := idx.isLt
  change tpos 0 (indexBelow 1 (treeOfIndex 1 idx) (leafOfIndex 1 idx)) 8 0 = _
  refine congrArg (fun τ ↦ tpos 0 τ 8 0) (Fin.ext ?_)
  change (idx.val / 65536 * 256 + idx.val / 256 % 256) % 67108864 = idx.val / 256
  omega

theorem cwMsgPos_keyOf_two (idx : Index) :
    msgPos (keyOf 2 idx) =
      tpos 1 ⟨idx.val / 65536, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) idx.isLt⟩ 8 0 := by
  have hi : idx.val < 67108864 := idx.isLt
  change tpos 1 (indexBelow 2 (treeOfIndex 2 idx) (leafOfIndex 2 idx)) 8 0 = _
  refine congrArg (fun τ ↦ tpos 1 τ 8 0) (Fin.ext ?_)
  change (idx.val / 67108864 * 1024 + idx.val / 65536 % 1024) % 67108864 = idx.val / 65536
  omega

theorem keyOf_one_eq {i i' : Index} (h : i.val / 256 = i'.val / 256) : keyOf 1 i = keyOf 1 i' := by
  refine Prod.ext rfl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · change i.val / 65536 = i'.val / 65536
    omega
  · change i.val / 256 % 256 = i'.val / 256 % 256
    rw [h]

theorem keyOf_two_eq {i i' : Index} (h : i.val / 65536 = i'.val / 65536) :
    keyOf 2 i = keyOf 2 i' := by
  have hi : i.val < 67108864 := i.isLt
  have hi' : i'.val < 67108864 := i'.isLt
  refine Prod.ext rfl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · change i.val / 67108864 = i'.val / 67108864
    omega
  · change i.val / 65536 % 1024 = i'.val / 65536 % 1024
    rw [h]

theorem tpos_inj {l l' : Layer} {τ τ' : TreeIndex}
    (h : tpos l τ 8 0 = tpos l' τ' 8 0) : l = l' ∧ τ = τ' := by
  unfold tpos at h
  injection h with h1 h2
  exact ⟨h1, h2⟩

theorem layer_cases (l : Layer) : l = 0 ∨ l = 1 ∨ l = 2 := by
  fin_cases l
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- **Distinct keys of the signatures sign values at distinct positions.** -/
theorem msgPos_injOn {K K' : Key} (hK : InRange K) (hK' : InRange K')
    (h : msgPos K = msgPos K') : K = K' := by
  obtain ⟨l, i, rfl⟩ := hK
  obtain ⟨l', i', rfl⟩ := hK'
  rcases layer_cases l with rfl | rfl | rfl <;> rcases layer_cases l' with rfl | rfl | rfl
  · rw [cwMsgPos_keyOf_zero, cwMsgPos_keyOf_zero] at h
    cases h
    rfl
  · rw [cwMsgPos_keyOf_zero, cwMsgPos_keyOf_one] at h
    cases h
  · rw [cwMsgPos_keyOf_zero, cwMsgPos_keyOf_two] at h
    cases h
  · rw [cwMsgPos_keyOf_one, cwMsgPos_keyOf_zero] at h
    cases h
  · rw [cwMsgPos_keyOf_one, cwMsgPos_keyOf_one] at h
    exact keyOf_one_eq (congrArg Fin.val (tpos_inj h).2)
  · rw [cwMsgPos_keyOf_one, cwMsgPos_keyOf_two] at h
    exact absurd (tpos_inj h).1 (by decide)
  · rw [cwMsgPos_keyOf_two, cwMsgPos_keyOf_zero] at h
    cases h
  · rw [cwMsgPos_keyOf_two, cwMsgPos_keyOf_one] at h
    exact absurd (tpos_inj h).1 (by decide)
  · rw [cwMsgPos_keyOf_two, cwMsgPos_keyOf_two] at h
    exact keyOf_two_eq (congrArg Fin.val (tpos_inj h).2)

/-- The positions of a hypertree layer's tree `τ`: its chains and its nodes. -/
def LPos (l : Layer) (τ : TreeIndex) : ValPos → Prop
  | .chain l' τ' _ _ _ => l' = l ∧ τ' = τ
  | .tree l' τ' _ _ => l' = l ∧ τ' = τ
  | _ => False

/-- The positions of FORS instance `idx`. -/
def FPos (idx : Index) : ValPos → Prop
  | .forsSecret i _ _ => i = idx
  | .forsTree i _ _ _ => i = idx
  | .forsKey i => i = idx
  | _ => False

/-- A key of the signatures whose signed value is a position of the tree `(l, τ)`: the value is
the tree's root. -/
theorem msgPos_of_lPos {K : Key} (hK : InRange K) {l : Layer} {τ : TreeIndex}
    (h : LPos l τ (msgPos K)) : msgPos K = tpos l τ 8 0 := by
  obtain ⟨l', i, rfl⟩ := hK
  rcases layer_cases l' with rfl | rfl | rfl
  · rw [cwMsgPos_keyOf_zero] at h
    exact h.elim
  · rw [cwMsgPos_keyOf_one] at h ⊢
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
  · rw [cwMsgPos_keyOf_two] at h ⊢
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]

/-- A key of the signatures whose signed value is a position of FORS instance `idx`: the key is
`K_0(idx)`. -/
theorem eq_keyOf_of_fPos {K : Key} (hK : InRange K) {idx : Index} (h : FPos idx (msgPos K)) :
    K = keyOf 0 idx := by
  obtain ⟨l', i, rfl⟩ := hK
  rcases layer_cases l' with rfl | rfl | rfl
  · rw [cwMsgPos_keyOf_zero] at h
    change i = idx at h
    rw [h]
  · rw [cwMsgPos_keyOf_one] at h
    exact h.elim
  · rw [cwMsgPos_keyOf_two] at h
    exact h.elim

/-- **The positions a layer signature reveals lie in its tree.** -/
theorem lPos_of_mem_layerNeed {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding} :
    ∀ p ∈ layerNeed l τ e x, LPos l τ p := by
  intro p hp
  rcases mem_layerNeed hp with ⟨i, j, -, -, rfl⟩ | ⟨lev, a, rfl, -⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- **The positions a FORS opening reveals lie in its instance.** -/
theorem fPos_of_mem_forsNeed {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} :
    ∀ p ∈ forsNeed idx lv, FPos idx p := by
  intro p hp
  rcases mem_forsNeed hp with ⟨κ, rfl⟩ | rfl | ⟨κ, hgt, a, rfl, -⟩
  · rfl
  · rfl
  · rfl

theorem forsKey_mem_forsNeed (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    ValPos.forsKey idx ∈ forsNeed idx lv := by
  rw [forsNeed]
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  refine slotNeed_subset_needUnion (s := .forsRoots idx) ?_ (Finset.mem_insert_self _ _)
  rw [forsSlots]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem forsSecret_mem_forsNeed (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (κ : ForsTreeIndex) : ValPos.forsSecret idx κ (lv κ) ∈ forsNeed idx lv := by
  rw [forsNeed]
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem (fun κ ↦ ValPos.forsSecret idx κ (lv κ)) (Finset.mem_univ κ)))

theorem root_mem_layerNeed (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (x : Encoding)
    (he : e.val < 2 ^ layerHeight l) : tpos l τ (layerHeight l) 0 ∈ layerNeed l τ e x := by
  unfold layerNeed
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  have hh : 0 < layerHeight l := by unfold layerHeight; split <;> norm_num
  refine slotNeed_subset_needUnion (s := .node l τ (layerHeight l) (e.val >>> layerHeight l))
    ?_ ?_
  · simp only [layerSlots, List.mem_append, List.mem_cons, List.mem_map, List.mem_range]
    exact Or.inr (Or.inr ⟨layerHeight l - 1, by omega, by rw [Nat.sub_add_cancel hh]⟩)
  · have he' : e.val >>> layerHeight l = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt he]
    rw [he']
    simp [slotNeed]

end keys

/-! ## The trial blocks -/

section blk

/-- **The block of trial `j` of the search of key `K` on the value `m`** under `PK.seed = P`. -/
noncomputable def cwBlk (P : PublicParameter) (K : Key) (m : Digest) (j : ℕ) : X :=
  (blocks (encTrialIn P K m (BitVec.ofNat counterBits j))).getD 0 0

theorem blocks_encTrialIn (P : PublicParameter) (K : Key) (m : Digest) (c : EncodingCounter) :
    ∃ b, blocks (encTrialIn P K m c) = [b] := by
  refine List.length_eq_one_iff.mp ?_
  rw [Quantum.Xmss.length_blocks, encTrialIn, length_addressedHashInput]
  simp [HashSig.littleEndianBytes, bigEndianBytes]

theorem blocks_encTrialIn_eq (P : PublicParameter) (K : Key) (m : Digest) (j : ℕ) :
    blocks (encTrialIn P K m (BitVec.ofNat counterBits j)) = [cwBlk P K m j] := by
  obtain ⟨b, hb⟩ := blocks_encTrialIn P K m (BitVec.ofNat counterBits j)
  rw [cwBlk, hb]
  rfl

/-- A counter trial's input is the trial input of `encTrialIn`. -/
theorem trialInput_eq_encTrialIn (pub : Pub) (K : Key) (m : Digest) (j : ℕ) :
    trialInput pub K m j = encTrialIn pub.seed K m (BitVec.ofNat counterBits j) :=
  rfl

/-- **A trial block names its key, its value and its counter.** -/
theorem cwBlk_inj (P : PublicParameter) {K K' : Key} {m m' : Digest} {i j : ℕ}
    (hi : i < encodingAttemptLimit) (hj : j < encodingAttemptLimit)
    (h : cwBlk P K m i = cwBlk P K' m' j) : K = K' ∧ m = m' ∧ i = j := by
  have hb := blocks_encTrialIn_eq P K m i
  have hb' := blocks_encTrialIn_eq P K' m' j
  rw [h] at hb
  obtain ⟨ha, hp⟩ := addressedHashInput_injective P (blocks_injective (hb.trans hb'.symm))
  have hd := hashDomainFields_injOn (d := .encoding K.1 K.2.1 K.2.2)
    (d' := .encoding K'.1 K'.2.1 K'.2.2) trivial trivial ha
  injection hd with h1 h2 h3
  obtain ⟨hm, hc⟩ := List.append_inj hp (by simp [HashSig.littleEndianBytes])
  refine ⟨Prod.ext h1 (Prod.ext h2 h3), littleEndianBytes_injective 16 hm, ?_⟩
  have hn := congrArg BitVec.toNat (bigEndianBytes_injective 4 hc)
  simp only [BitVec.toNat_ofNat, counterBits] at hn
  have h32 : encodingAttemptLimit = 2 ^ 32 := rfl
  rwa [Nat.mod_eq_of_lt (h32 ▸ hi), Nat.mod_eq_of_lt (h32 ▸ hj)] at hn

/-- A trial block is a trial block. -/
theorem trialBlock_cwBlk (P : PublicParameter) (K : Key) (m : Digest) (j : ℕ) :
    TrialBlock (cwBlk P K m j) :=
  ⟨P, K, m, BitVec.ofNat counterBits j, blocks_encTrialIn_eq P K m j⟩

end blk

/-! ## The modes of the counter searches -/

section modes

/-- **The modes of the counter searches**: free; `K`'s value `m` disclosed, its search next; in the
search of `K` on `m` before trial `j`; after that trial's `k`-read with outcome `a`; after its
`k'`-read, with the rate `xi` after `π` and the `h`-cell `z` next. -/
inductive CwMode
  | free
  | pend (K : Key) (m : Digest)
  | grd (K : Key) (m : Digest) (j : ℕ)
  | afK (K : Key) (m : Digest) (j : ℕ) (a : Z)
  | afK' (K : Key) (m : Digest) (j : ℕ) (xi : X) (z : Z)

/-- A mode between trials. -/
def CwMode.Idle : CwMode → Prop
  | .free => True
  | .pend .. => True
  | .grd .. => True
  | _ => False

/-- The key of a reveal of the single value a key of the signatures signs (decided classically). -/
noncomputable def cwSingKey (T : Finset HPos) : Option Key :=
  @dite _ (∃ K, InRange K ∧ T = {.val (msgPos K)}) (Classical.propDecidable _)
    (fun h ↦ some h.choose) fun _ ↦ none

/-- The key of a reveal disclosing, among other coordinates, the value a key of the signatures
signs (decided classically). -/
noncomputable def cwDiscKey (T : Finset HPos) : Option Key :=
  @dite _ (∃ K, InRange K ∧ HPos.val (msgPos K) ∈ T ∧ T ≠ {.val (msgPos K)})
    (Classical.propDecidable _) (fun h ↦ some h.choose) fun _ ↦ none

theorem cwSingKey_spec {T : Finset HPos} {K : Key} (h : cwSingKey T = some K) :
    InRange K ∧ T = {.val (msgPos K)} := by
  unfold cwSingKey at h
  split_ifs at h with h'
  obtain rfl := Option.some.inj h
  exact h'.choose_spec

theorem cwSingKey_eq {K : Key} (hK : InRange K) : cwSingKey {.val (msgPos K)} = some K := by
  unfold cwSingKey
  split_ifs with h'
  · obtain ⟨hK', he⟩ := h'.choose_spec
    exact congrArg some (msgPos_injOn hK' hK (HPos.val.inj (Finset.singleton_injective he.symm)))
  · exact absurd ⟨K, hK, rfl⟩ h'

theorem cwSingKey_eq_none {T : Finset HPos} (h : ∀ K, InRange K → T ≠ {.val (msgPos K)}) :
    cwSingKey T = none := by
  unfold cwSingKey
  split_ifs with h'
  · exact absurd h'.choose_spec.2 (h _ h'.choose_spec.1)
  · rfl

theorem cwDiscKey_spec {T : Finset HPos} {K : Key} (h : cwDiscKey T = some K) :
    InRange K ∧ HPos.val (msgPos K) ∈ T := by
  unfold cwDiscKey at h
  split_ifs at h with h'
  obtain rfl := Option.some.inj h
  exact ⟨h'.choose_spec.1, h'.choose_spec.2.1⟩

theorem cwDiscKey_eq {T : Finset HPos} {K : Key} (hK : InRange K)
    (hm : HPos.val (msgPos K) ∈ T) (hT : T ≠ {.val (msgPos K)})
    (hu : ∀ K', InRange K' → HPos.val (msgPos K') ∈ T → K' = K) : cwDiscKey T = some K := by
  unfold cwDiscKey
  split_ifs with h'
  · exact congrArg some (hu _ h'.choose_spec.1 h'.choose_spec.2.1)
  · exact absurd ⟨K, hK, hm, hT⟩ h'

/-- The mode after a program: a disclosed key's search stays next. -/
def cwProgNx : CwMode → CwMode
  | .pend K m => .pend K m
  | _ => .free

theorem cwProgNx_idle (μ : CwMode) : (cwProgNx μ).Idle := by
  cases μ <;> trivial

/-- **The mode after a reveal of `T`**, from the values `val`: the reveal of the single value `K`
signs starts `K`'s search if `K`'s value was disclosed; a reveal disclosing the value `K` signs
among others makes `K`'s search next. -/
noncomputable def cwRevNx (μ : CwMode) (T : Finset HPos) (val : ValPos → Digest) : CwMode :=
  match cwSingKey T with
  | some K => match μ with
    | .pend K' _ => if K' = K then .grd K (val (msgPos K)) 0 else .free
    | _ => .free
  | none => match cwDiscKey T with
    | some K => .pend K (val (msgPos K))
    | none => .free

theorem cwRevNx_idle (μ : CwMode) (T : Finset HPos) (val : ValPos → Digest) :
    (cwRevNx μ T val).Idle := by
  unfold cwRevNx
  rcases cwSingKey T with _ | K
  · rcases cwDiscKey T with _ | K <;> trivial
  · rcases μ with _ | ⟨K', m⟩ | _ | _ | _
    all_goals try trivial
    dsimp only
    split_ifs <;> trivial

theorem cwRevNx_congr (μ : CwMode) (T : Finset HPos) {val val' : ValPos → Digest}
    (h : ∀ p, HPos.val p ∈ T → val p = val' p) : cwRevNx μ T val = cwRevNx μ T val' := by
  unfold cwRevNx
  rcases hs : cwSingKey T with _ | K
  · rcases hd : cwDiscKey T with _ | K
    · rfl
    · dsimp only
      rw [h _ (cwDiscKey_spec hd).2]
  · dsimp only
    have hm : HPos.val (msgPos K) ∈ T := by
      rw [(cwSingKey_spec hs).2]
      exact Finset.mem_singleton_self _
    rw [h _ hm]

/-- The reveal of the value of `K` from `K`'s pending mode starts its search. -/
theorem cwRevNx_sing {K : Key} (hK : InRange K) (m : Digest) (val : ValPos → Digest) :
    cwRevNx (.pend K m) {.val (msgPos K)} val = .grd K (val (msgPos K)) 0 := by
  unfold cwRevNx
  rw [cwSingKey_eq hK]
  exact ite_eq_left rfl

/-- A reveal disclosing the value of `K` among others makes `K`'s search next. -/
theorem cwRevNx_disc {T : Finset HPos} {K : Key} (hs : cwSingKey T = none)
    (hd : cwDiscKey T = some K) (μ : CwMode) (val : ValPos → Digest) :
    cwRevNx μ T val = .pend K (val (msgPos K)) := by
  unfold cwRevNx
  rw [hs, hd]

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter)

/-- The reads a mode allows: in a search before trial `j`, the `k`-read at the trial's block
keeping the memory; after it with outcome `a`, the `k'`-read at `π (x, a)` keeping the memory;
then the `h`-read at `z` with the trial's update `hu K x xi`. -/
noncomputable def cwRdOk {M' : Type} (hu : Key → X → X → M' → Option X → M') :
    CwMode → HwRead X Z M' → Prop
  | .grd K m j, .readK x u => j < encodingAttemptLimit ∧ x = cwBlk P K m j ∧ u = fun m _ ↦ m
  | .afK K m j a, .readK' y u => y = (π (cwBlk P K m j, a)).1 ∧ u = fun m _ ↦ m
  | .afK' K m j xi z, .readH z' u => z' = z ∧ u = hu K (cwBlk P K m j) xi
  | _, _ => False

/-- The mode after a read. -/
noncomputable def cwRdNx {M' : Type} : CwMode → (c : HwRead X Z M') → c.Result → CwMode
  | .grd K m j, .readK _ _, r => .afK K m j (r.1.getD 0)
  | .afK K m j a, .readK' _ _, r => .afK' K m j (π (cwBlk P K m j, a)).1
      ((π (cwBlk P K m j, a)).2 + r.1.getD 0)
  | .afK' K m j _ _, .readH _ _, _ => .grd K m (j + 1)
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 1's ports. -/
noncomputable def cwOkR {M : Type} (hu : Key → X → X → M → Option X → M) :
    CwMode → (hwReadSpec X Z M).Port → Prop
  | μ, .inl _ => μ.Idle
  | μ, .inr c => cwRdOk π P hu μ c

/-- The mode after a call of runtime 1. -/
noncomputable def cwNxR {M : Type} :
    CwMode → (i : (hwReadSpec X Z M).Port) → (hwReadSpec X Z M).Result i → CwMode
  | _, .inl _, _ => .free
  | μ, .inr c, r => cwRdNx π P μ c r

/-- The calls the modes allow, on the template's ports. -/
noncomputable def cwOkT {M : Type}
    (hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    CwMode → (SSpec M).Port → Prop
  | μ, .inl (.inl (.inr c)) => cwRdOk π P hu μ c.1
  | μ, _ => μ.Idle

/-- The mode after a call of the template. -/
noncomputable def cwNxT {M : Type} : CwMode → (i : (SSpec M).Port) → (SSpec M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => cwRdNx π P μ c.1 r
  | μ, .inl (.inr _), _ => cwProgNx μ
  | μ, .inr T, r => cwRevNx μ T (extendVals r.1)
  | _, _, _ => .free

/-- The calls the modes allow, on runtime 2's ports with record ports. -/
noncomputable def cwOkZ {M : Type}
    (hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M) :
    CwMode → (recHwSpec X Z HPos M).Port → Prop
  | μ, .inl (.inl (.inr c)) => cwRdOk π P hu μ c
  | μ, _ => μ.Idle

/-- The mode after a call of runtime 2 with record ports, at the hidden values `v`. -/
noncomputable def cwNxZ {M : Type} (v : (s : HPos) → XD s) :
    CwMode → (i : (recHwSpec X Z HPos M).Port) → (recHwSpec X Z HPos M).Result i → CwMode
  | μ, .inl (.inl (.inr c)), r => cwRdNx π P μ c r
  | μ, .inl (.inr _), _ => cwProgNx μ
  | μ, .inr T, _ => cwRevNx μ T (valsOf v)
  | _, _, _ => .free

/-- The update of a trial's `h`-read on the template's memory. -/
def cwLiftHu {M : Type} (hu : Key → X → X → M → Option X → M) :
    Key → X → X → Finset HPos × M → Option X → Finset HPos × M :=
  fun K b xi m o ↦ (m.1, hu K b xi m.2 o)

variable {M : Type} [Fintype M] [DecidableEq M]

/-! ### Runtime 1's searches -/

variable {π P}

omit [Fintype M] [DecidableEq M] in
theorem modedP_readCall {hu : Key → X → X → M → Option X → M} {μ : CwMode}
    {c : HwRead X Z M} (h : cwRdOk π P hu μ c) (B : QReg) :
    ModedP (L := LocalSig.instruments) (cwOkR π P hu) (cwNxR π P)
      (fun p μ' ↦ μ' = cwRdNx π P μ c p.2.2) μ (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

variable (π P) in
/-- A stateful program of runtime 1 that is moded from every state. -/
def CSMod (hu : Key → X → X → M → Option X → M) {B : QReg} {σ α : Type} (μ : CwMode)
    (F : α → CwMode → Prop) (x : StateT σ (QComp (hwReadSpec X Z M) B B) α) : Prop :=
  ∀ s, ModedP (L := LocalSig.instruments) (cwOkR π P hu) (cwNxR π P)
    (fun p μ' ↦ F p.2.2.1 μ') μ (x.run s)

section smod

variable {hu : Key → X → X → M → Option X → M} {B : QReg} {σ α β : Type}

omit [Fintype M] [DecidableEq M] in
theorem cSMod_bind {x : StateT σ (QComp (hwReadSpec X Z M) B B) α}
    {k : α → StateT σ (QComp (hwReadSpec X Z M) B B) β} {μ : CwMode} {F : α → CwMode → Prop}
    {G : β → CwMode → Prop} (hx : CSMod π P hu μ F x)
    (hk : ∀ a μ', F a μ' → CSMod π P hu μ' G (k a)) : CSMod π P hu μ G (x >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact modedP₂_bind (F := fun (q : α × σ) μ ↦ F q.1 μ) (F' := fun (q : β × σ) μ ↦ G q.1 μ) _ _
    (hx s) fun p μ' h ↦ hk p.1 μ' h p.2

omit [Fintype M] [DecidableEq M] in
theorem cSMod_pure (a : α) {F : α → CwMode → Prop} {μ : CwMode} (h : F a μ) :
    CSMod π P hu μ F (pure a : StateT σ (QComp (hwReadSpec X Z M) B B) α) := by
  intro s
  rw [StateT.run_pure]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem cSMod_map {x : StateT σ (QComp (hwReadSpec X Z M) B B) α} (g : α → β) {μ : CwMode}
    {F : β → CwMode → Prop} (hx : CSMod π P hu μ (fun a ↦ F (g a)) x) :
    CSMod π P hu μ F (g <$> x) := by
  intro s
  rw [StateT.run_map]
  exact modedP_map (F := fun q : β × σ ↦ F q.1) (fun p : α × σ ↦ (g p.1, p.2)) (hx s)

omit [Fintype M] [DecidableEq M] in
theorem cSMod_rdK {K : Key} {m : Digest} {j : ℕ} {x : X}
    (hj : j < encodingAttemptLimit) (hx : x = cwBlk P K m j) :
    CSMod π P hu (.grd K m j) (fun a (μ : CwMode) ↦ μ = .afK K m j a) (rdK (M := M) B x) :=
  fun s ↦ modedP₂_bind
    (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK K m j (r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK K m j q.1)
    (readCall (.readK x keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k x (r.1.getD 0)]))
    (modedP_readCall (μ := .grd K m j) (c := .readK x keepMem) ⟨hj, hx, rfl⟩ B)
    fun _ _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem cSMod_rdK' {K : Key} {m : Digest} {j : ℕ} {a : Z} {y : X}
    (hy : y = (π (cwBlk P K m j, a)).1) :
    CSMod π P hu (.afK K m j a) (fun c (μ : CwMode) ↦ μ = .afK' K m j
      (π (cwBlk P K m j, a)).1 ((π (cwBlk P K m j, a)).2 + c)) (rdK' (M := M) B y) :=
  fun s ↦ modedP₂_bind (F := fun r : Option Z × M ↦ fun (μ : CwMode) ↦ μ = .afK' K m j
      (π (cwBlk P K m j, a)).1 ((π (cwBlk P K m j, a)).2 + r.1.getD 0))
    (F' := fun q : Z × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .afK' K m j
      (π (cwBlk P K m j, a)).1 ((π (cwBlk P K m j, a)).2 + q.1))
    (readCall (.readK' y keepMem) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.k' y (r.1.getD 0)]))
    (modedP_readCall (μ := .afK K m j a) (c := .readK' y keepMem) ⟨hy, rfl⟩ B)
    fun _ _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem cSMod_rdHU {K : Key} {m : Digest} {j : ℕ} {xi : X} {z z' : Z}
    {u : M → Option X → M} (hz : z' = z) (hu' : u = hu K (cwBlk P K m j) xi) :
    CSMod π P hu (.afK' K m j xi z) (fun _ (μ : CwMode) ↦ μ = .grd K m (j + 1))
      (rdHU M B z' u) :=
  fun s ↦ modedP₂_bind (F := fun _ : Option X × M ↦ fun (μ : CwMode) ↦ μ = .grd K m (j + 1))
    (F' := fun _ : X × List (SpongeRead X Z) ↦ fun (μ : CwMode) ↦ μ = .grd K m (j + 1))
    (readCall (.readH z' u) B)
    (fun r ↦ QuantumComp₂.pure (r.1.getD 0, s ++ [SpongeRead.h z' (r.1.getD 0)]))
    (modedP_readCall (μ := .afK' K m j xi z) (c := .readH z' u) ⟨hz, hu'⟩ B)
    fun _ _ h ↦ h

end smod

omit [Fintype M] [DecidableEq M] in
/-- **A trial's round of reads.** -/
theorem cSMod_rdRoundU (upd : TrialUpd M) {B : QReg} {K : Key} {m : Digest} {j : ℕ}
    (hj : j < encodingAttemptLimit) {b : X} (hb : b = cwBlk P K m j) :
    CSMod π P upd (.grd K m j) (fun _ (μ : CwMode) ↦ μ = .grd K m (j + 1))
      (rdRoundU M (upd K) π B (0, 0) b) := by
  unfold rdRoundU
  refine cSMod_bind (cSMod_rdK hj (by simp [hb])) fun a μ ha ↦ ?_
  subst ha
  refine cSMod_bind (cSMod_rdK' (a := a) (by simp [hb])) fun c μ hc ↦ ?_
  subst hc
  refine cSMod_bind (cSMod_rdHU (by simp [hb]) (by simp [hb])) fun w μ hw ↦ ?_
  exact cSMod_pure _ hw

omit [Fintype M] [DecidableEq M] in
/-- **A trial's hash** of a one-block input whose block is the trial's. -/
theorem modedP_hashTrial (upd : TrialUpd M) {B : QReg} {K : Key} {m : Digest}
    {j : ℕ} (hj : j < encodingAttemptLimit) (input : HashInput)
    (hb : blocks input = [cwBlk P K m j]) :
    ModedP (L := LocalSig.instruments) (cwOkR π P upd) (cwNxR π P)
      (fun _ (μ : CwMode) ↦ μ = .grd K m (j + 1)) (.grd K m j)
      (hashTrial M (upd K) π B input) := by
  have hfold : CSMod π P upd (B := B) (.grd K m j)
      (fun _ (μ : CwMode) ↦ μ = .grd K m (j + 1))
      ((blocks input).foldlM (rdRoundU M (upd K) π B) (0, 0)) := by
    rw [hb]
    exact cSMod_bind (cSMod_rdRoundU upd hj rfl) fun s' μ h ↦ cSMod_pure s' h
  exact modedP_map (F := fun _ (μ : CwMode) ↦ μ = .grd K m (j + 1)) Prod.fst
    (cSMod_map (F := fun _ (μ : CwMode) ↦ μ = .grd K m (j + 1)) (out256 : X → HashOutput)
      (cSMod_map (F := fun _ (μ : CwMode) ↦ μ = .grd K m (j + 1)) (fun s : X × Z ↦ s.1)
        hfold) [])

omit [Fintype M] [DecidableEq M] in
/-- **The counter search** of key `K` on the value `m`, from its trial `c`, ends between
trials. -/
theorem modedP_grindK (upd : TrialUpd M) (pub : Pub) {B : QReg} (K : Key) (m : Digest) :
    ∀ n c, c + n ≤ encodingAttemptLimit →
      ModedP (L := LocalSig.instruments) (cwOkR pub.perm pub.seed upd)
      (cwNxR pub.perm pub.seed) (fun _ (μ : CwMode) ↦ μ.Idle) (.grd K m c)
      (grindK M upd pub B K m n c)
  | 0, _, _ => trivial
  | n + 1, c, hn => by
    rw [grindK]
    refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ = .grd K m (c + 1))
      (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _
      (modedP_hashTrial upd (by omega) _ (blocks_encTrialIn_eq pub.seed K m c))
      fun out μ hμ ↦ ?_
    subst hμ
    split
    · trivial
    · exact modedP_grindK upd pub K m n (c + 1) (by omega)

/-! ### Lifting the modes to the template and to runtime 2 -/

omit [Fintype M] [DecidableEq M] in
theorem cwRdOk_liftRead {hu : Key → X → X → M → Option X → M} {μ : CwMode}
    {c : HwRead X Z M} (h : cwRdOk π P hu μ c) :
    cwRdOk π P (cwLiftHu hu) μ (liftRead (S := HPos) c) := by
  rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z⟩ <;>
    rcases c with ⟨z', u⟩ | ⟨x', u⟩ | ⟨y, u⟩
  all_goals first
    | exact h
    | exact ⟨h.1, by rw [h.2]; try rfl⟩
    | exact ⟨h.1, h.2.1, by rw [h.2.2]⟩

omit [Fintype M] [DecidableEq M] in
/-- **Lifting runtime 1's moded programs to templates.** -/
theorem modedP_readLift {hu : Key → X → X → M → Option X → M} {Ω : QReg → Type} {A : QReg}
    {fin : (Σ u, Ω u) → CwMode → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec X Z M) Ω A) {μ : CwMode}
    (hy : ModedP (cwOkR π P hu) (cwNxR π P) fin μ y) :
    ModedP (cwOkT π P (cwLiftHu hu)) (cwNxT π P) fin μ (readLift goodAll y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨cwRdOk_liftRead hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
        rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z'⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

omit [Fintype M] [DecidableEq M] in
/-- A sponge program of runtime 1 is moded between trials. -/
theorem modedP_liftOrdinary {hu : Key → X → X → M → Option X → M} {Ω : QReg → Type}
    {A : QReg} (y : QuantumComp LocalSig.instruments (spongeSpec X Z) Ω A) :
    ∀ μ : CwMode, μ.Idle → ModedP (cwOkR π P hu) (cwNxR π P) (fun _ (μ : CwMode) ↦ μ.Idle) μ
      (y.liftOrdinary (t := hwReadCmdSpec X Z M)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun _ h ↦ h
  | liftBind _ c next ih =>
    intro μ hμ
    show ModedP _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ μ hμ⟩
    · exact ⟨hμ, fun b ↦ ih _ .free trivial⟩

omit [Fintype M] [DecidableEq M] in
theorem cwNxZ_rec_eq (v : (s : HPos) → XD s) (μ : CwMode) (T : Finset HPos)
    (m : Finset HPos × M) :
    cwNxZ (M := M) π P v μ (.inr T) m = cwNxT π P μ (.inr T) (restrictTo T v, m) :=
  cwRevNx_congr μ T fun _ hp ↦ (extendVals_restrictTo hp v).symm

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the modes.** -/
theorem modedP_realizeT {hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M}
    (v : (s : HPos) → XD s) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → CwMode → Prop} (y : QuantumComp L (SSpec M) Ω A)
    {μ : CwMode} (hy : ModedP (cwOkT π P hu) (cwNxT π P) fin μ y) :
    ModedP (cwOkZ π P hu) (cwNxZ π P v) fin μ (realizeT v y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (tmplLens v) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨_, _⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      have h := ih _ (hy.2 (ULift.up (restrictTo T v, b.down)))
      exact (congrArg (fun μ' ↦ ModedP (cwOkZ π P hu) (cwNxZ π P v) fin μ' _)
        (cwNxZ_rec_eq (π := π) (P := P) v μ T b.down)).mpr h

/-! ### The challenge prefix is moded -/

section trialPrefix

variable (π P) in
/-- A template moded between trials: from every mode between trials, it ends between trials. -/
def CIdle (hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M)
    {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (SSpec M) Ω A) : Prop :=
  ∀ μ : CwMode, μ.Idle → ModedP (cwOkT π P hu) (cwNxT π P) (fun _ (μ : CwMode) ↦ μ.Idle) μ y

variable (π P) in
/-- A template keeping a disclosed key's search next. -/
def CPend (hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M)
    {Ω : QReg → Type} {A : QReg} (y : QuantumComp LocalSig.instruments (SSpec M) Ω A) : Prop :=
  ∀ K m, ModedP (cwOkT π P hu) (cwNxT π P) (fun _ (μ : CwMode) ↦ μ = .pend K m) (.pend K m) y

variable {hu : Key → X → X → Finset HPos × M → Option X → Finset HPos × M}

omit [Fintype M] [DecidableEq M] in
theorem cIdle_bind {A B B' : QReg} {α β : Type} (x : QComp (SSpec M) A B α)
    (g : α → QComp (SSpec M) B B' β) (hx : CIdle π P hu x) (hg : ∀ a, CIdle π P hu (g a)) :
    CIdle π P hu (x.bind g) :=
  fun μ hμ ↦ modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Idle)
    (F' := fun _ (μ : CwMode) ↦ μ.Idle) x g (hx μ hμ) fun a μ' h ↦ hg a μ' h

omit [Fintype M] [DecidableEq M] in
theorem cPend_bind {A B B' : QReg} {α β : Type} (x : QComp (SSpec M) A B α)
    (g : α → QComp (SSpec M) B B' β) (hx : CPend π P hu x) (hg : ∀ a, CPend π P hu (g a)) :
    CPend π P hu (x.bind g) :=
  fun K m ↦ modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ = .pend K m)
    (F' := fun _ (μ : CwMode) ↦ μ = .pend K m) x g (hx K m) fun a _ h ↦ h ▸ hg a K m

omit [Fintype M] [DecidableEq M] in
theorem cIdle_pure {A : QReg} {α : Type} (a : α) :
    CIdle π P hu (QuantumComp₂.pure (L := LocalSig.instruments) (spec := SSpec M) (A := A) a) :=
  fun _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem cPend_pure {A : QReg} {α : Type} (a : α) :
    CPend π P hu (QuantumComp₂.pure (L := LocalSig.instruments) (spec := SSpec M) (A := A) a) :=
  fun _ _ ↦ rfl

omit [Fintype M] [DecidableEq M] in
theorem cIdle_act {A B : QReg} {α : Type} (p : SubInstrument A B α) :
    CIdle π P hu (QComp.act (spec := SSpec M) p) :=
  fun _ hμ ↦ ⟨trivial, fun _ ↦ hμ⟩

omit [Fintype M] [DecidableEq M] in
/-- **A reveal**, from a mode between trials: its continuation from the mode it leads to. -/
theorem modedP_revealThen {B B' : QReg} {α : Type} {fin : α → CwMode → Prop} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α) {μ : CwMode}
    (hμ : μ.Idle)
    (hk : ∀ r, ModedP (cwOkT π P hu) (cwNxT π P) (fun p μ ↦ fin p.2.2 μ)
      (cwRevNx μ T (extendVals r.1)) (k r)) :
    ModedP (cwOkT π P hu) (cwNxT π P) (fun p μ ↦ fin p.2.2 μ) μ (revealThen goodAll T k) := by
  refine ⟨hμ, fun b ↦ ?_⟩
  rw [show modeCmdNx (cwNxT (M := M) π P) (QuantumComp.Cmd.query (L := LocalSig.instruments)
    (.inr T) B _) μ b = cwRevNx μ T (extendVals b.down.1) from rfl]
  exact modedP₂_bind (F := fun _ (μ' : CwMode) ↦ μ' = cwRevNx μ T (extendVals b.down.1))
    (F' := fin) _ _ ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ h ▸ hk b.down

omit [Fintype M] [DecidableEq M] in
theorem cIdle_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α)
    (hk : ∀ r, CIdle π P hu (k r)) : CIdle π P hu (revealThen goodAll T k) :=
  fun μ hμ ↦ modedP_revealThen (fin := fun _ (μ : CwMode) ↦ μ.Idle) T k hμ
    fun r ↦ hk r _ (cwRevNx_idle μ T _)

omit [Fintype M] [DecidableEq M] in
theorem cIdle_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) (hk : CIdle π P hu k) : CIdle π P hu (progThen p hp k) :=
  fun μ hμ ↦ ⟨hμ, fun _ ↦ cIdle_bind _ _ (cIdle_act _) (fun _ ↦ hk) _ (cwProgNx_idle μ)⟩

omit [Fintype M] [DecidableEq M] in
theorem cPend_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) (hk : CPend π P hu k) : CPend π P hu (progThen p hp k) :=
  fun K m ↦ ⟨trivial, fun _ ↦ modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ = .pend K m)
    (F' := fun _ (μ : CwMode) ↦ μ = .pend K m) _ _ ⟨trivial, fun _ ↦ rfl⟩
    fun _ _ h ↦ h ▸ hk K m⟩

omit [Fintype M] [DecidableEq M] in
theorem cIdle_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    CIdle π P hu (progPorts M B ps) := by
  induction ps with
  | nil => exact cIdle_pure _
  | cons p ps ih => exact cIdle_progThen p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem cPend_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    CPend π P hu (progPorts M B ps) := by
  induction ps with
  | nil => exact cPend_pure _
  | cons p ps ih => exact cPend_progThen p trivial _ ih

omit [Fintype M] [DecidableEq M] in
theorem cIdle_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    CIdle π P hu (progSlots M pub B ss) := by
  induction ss with
  | nil => exact cIdle_pure _
  | cons s ss ih => exact cIdle_bind _ _ (cIdle_progPorts B _) fun _ ↦ ih

omit [Fintype M] [DecidableEq M] in
theorem cPend_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    CPend π P hu (progSlots M pub B ss) := by
  induction ss with
  | nil => exact cPend_pure _
  | cons s ss ih => exact cPend_bind _ _ (cPend_progPorts B _) fun _ ↦ ih

/-- The value a key of the signatures signs is at no chain position. -/
theorem msgPos_ne_chain {K : Key} (hK : InRange K) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (i : ChainIndex) (j : ℕ) : msgPos K ≠ cpos l τ e i j := by
  obtain ⟨l', idx, rfl⟩ := hK
  rcases layer_cases l' with rfl | rfl | rfl
  · rw [cwMsgPos_keyOf_zero]
    exact fun h ↦ by cases h
  · rw [cwMsgPos_keyOf_one]
    exact fun h ↦ by cases h
  · rw [cwMsgPos_keyOf_two]
    exact fun h ↦ by cases h

/-- The value a key of the signatures signs is at no FORS secret. -/
theorem msgPos_ne_forsSecret {K : Key} (hK : InRange K) (idx : Index) (κ : ForsTreeIndex)
    (s : ForsLeafIndex) : msgPos K ≠ .forsSecret idx κ s := by
  obtain ⟨l', i, rfl⟩ := hK
  rcases layer_cases l' with rfl | rfl | rfl
  · rw [cwMsgPos_keyOf_zero]
    exact fun h ↦ by cases h
  · rw [cwMsgPos_keyOf_one]
    exact fun h ↦ by cases h
  · rw [cwMsgPos_keyOf_two]
    exact fun h ↦ by cases h

/-- **The reveal of a FORS opening discloses the value `K_0(idx)` signs, and no other key's.** -/
theorem cwKeys_forsNeed (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    cwSingKey (valSet (forsNeed idx lv)) = none ∧
      cwDiscKey (valSet (forsNeed idx lv)) = some (keyOf 0 idx) := by
  have hsec : HPos.val (.forsSecret idx ⟨0, by decide⟩ (lv ⟨0, by decide⟩)) ∈
      valSet (forsNeed idx lv) :=
    val_mem_valSet.mpr (forsSecret_mem_forsNeed idx lv _)
  have hns : ∀ K, InRange K → valSet (forsNeed idx lv) ≠ {.val (msgPos K)} := fun K hK h ↦ by
    rw [h, Finset.mem_singleton] at hsec
    exact msgPos_ne_forsSecret hK idx _ _ (HPos.val.inj hsec).symm
  refine ⟨cwSingKey_eq_none hns, cwDiscKey_eq (inRange_keyOf 0 idx) ?_
    (hns _ (inRange_keyOf 0 idx)) fun K' hK' hm ↦ ?_⟩
  · rw [val_mem_valSet, cwMsgPos_keyOf_zero]
    exact forsKey_mem_forsNeed idx lv
  · exact eq_keyOf_of_fPos hK' (fPos_of_mem_forsNeed _ (val_mem_valSet.mp hm))

/-- The value `K_{l+1}(idx)` signs is the root of `K_l(idx)`'s tree. -/
theorem msgPos_keyOf_succ {l l' : Layer} (hl : l.val < 2) (hl' : l'.val = l.val + 1)
    (idx : Index) : msgPos (keyOf l' idx) = tpos l (treeOfIndex l idx) 8 0 := by
  have hi : idx.val < 67108864 := idx.isLt
  rcases layer_cases l with rfl | rfl | rfl
  · obtain rfl : l' = 1 := Fin.ext hl'
    rw [cwMsgPos_keyOf_one]
    refine congrArg (fun τ ↦ tpos 0 τ 8 0) (Fin.ext ?_)
    exact (treeOfIndex_zero idx).symm
  · obtain rfl : l' = 2 := Fin.ext hl'
    rw [cwMsgPos_keyOf_two]
    refine congrArg (fun τ ↦ tpos 1 τ 8 0) (Fin.ext ?_)
    change idx.val / 65536 = idx.val / 2 ^ (8 * 1 + 8)
    norm_num
  · exact absurd hl (by decide)

/-- **The reveal of a layer signature by `K_l(idx)` below the top discloses the value
`K_{l+1}(idx)` signs, and no other key's.** -/
theorem cwKeys_layerNeed {l l' : Layer} (hl : l.val < 2) (hl' : l'.val = l.val + 1)
    (idx : Index) (x : Encoding) :
    cwSingKey (valSet (layerNeed l (treeOfIndex l idx) (leafOfIndex l idx) x)) = none ∧
      cwDiscKey (valSet (layerNeed l (treeOfIndex l idx) (leafOfIndex l idx) x)) =
        some (keyOf l' idx) := by
  set T := valSet (layerNeed l (treeOfIndex l idx) (leafOfIndex l idx) x)
  have hch : HPos.val (cpos l (treeOfIndex l idx) (leafOfIndex l idx) ⟨0, by decide⟩
      (x ⟨0, by decide⟩).val) ∈ T :=
    val_mem_valSet.mpr (cpos_mem_layerNeed _ _ _ x _)
  have hns : ∀ K, InRange K → T ≠ {.val (msgPos K)} := fun K hK h ↦ by
    rw [h, Finset.mem_singleton] at hch
    exact msgPos_ne_chain hK _ _ _ _ _ (HPos.val.inj hch).symm
  have h8 : layerHeight l = 8 := by
    unfold layerHeight
    exact ite_eq_right (by omega)
  have hroot : HPos.val (msgPos (keyOf l' idx)) ∈ T := by
    rw [val_mem_valSet, msgPos_keyOf_succ hl hl', ← h8]
    exact root_mem_layerNeed _ _ _ x (leafOfIndex_lt l idx)
  refine ⟨cwSingKey_eq_none hns, cwDiscKey_eq (inRange_keyOf l' idx) hroot
    (hns _ (inRange_keyOf l' idx)) fun K' hK' hm ↦ ?_⟩
  refine msgPos_injOn hK' (inRange_keyOf l' idx) ?_
  rw [msgPos_keyOf_succ hl hl']
  exact msgPos_of_lPos hK' (lPos_of_mem_layerNeed _ (val_mem_valSet.mp hm))

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **The FORS opening of instance `idx`** ends with `K_0(idx)`'s search next. -/
theorem modedP_forsOpenT (pub : Pub) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) {μ : CwMode} (hμ : μ.Idle) :
    ModedP (cwOkT pub.perm pub.seed (cwLiftHu upd)) (cwNxT pub.perm pub.seed)
      (fun _ (μ : CwMode) ↦ ∃ m, μ = .pend (keyOf 0 idx) m) μ (forsOpenT M pub B idx lv) := by
  obtain ⟨hs, hd⟩ := cwKeys_forsNeed idx lv
  refine modedP_revealThen (fin := fun _ (μ : CwMode) ↦ ∃ m, μ = .pend (keyOf 0 idx) m) _ _ hμ
    fun r ↦ ?_
  rw [cwRevNx_disc hs hd]
  exact modedP₂_bind (F := fun _ (μ : CwMode) ↦
      μ = .pend (keyOf 0 idx) (extendVals r.1 (msgPos (keyOf 0 idx))))
    (F' := fun _ (μ : CwMode) ↦ ∃ m, μ = .pend (keyOf 0 idx) m) _ _
    (cPend_progSlots pub B _ _ _) fun _ _ h ↦ ⟨_, h⟩

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature** by a key of the signatures, from its search next: the reveal of its
value starts the search, which ends between trials; the continuation `k` from there. -/
theorem modedP_signLayerT_of (pub : Pub) (B : QReg) {K : Key} (hK : InRange K) (m : Digest)
    {fin : Option (LayerSignature K.1) → CwMode → Prop} (hnone : ∀ μ, μ.Idle → fin none μ)
    (hsome : ∀ (c : EncodingCounter) (x : Encoding) μ, μ.Idle →
      ModedP (cwOkT pub.perm pub.seed (cwLiftHu upd)) (cwNxT pub.perm pub.seed)
        (fun p μ ↦ fin p.2.2 μ) μ
        (revealThen goodAll (valSet (layerNeed K.1 K.2.1 K.2.2 x)) fun r ↦
          (progSlots M pub B (layerSlots K.1 K.2.1 K.2.2 x)).bind fun _ ↦
            QuantumComp₂.pure (some ⟨c, fun i ↦ extendVals r.1 (cpos K.1 K.2.1 K.2.2 i (x i).val),
              fun z ↦ extendVals r.1 (siblingPos K.1 K.2.1 K.2.2 z)⟩))) :
    ModedP (cwOkT pub.perm pub.seed (cwLiftHu upd)) (cwNxT pub.perm pub.seed)
      (fun p μ ↦ fin p.2.2 μ) (.pend K m) (signLayerT M upd pub B K) := by
  refine modedP_revealThen _ _ trivial fun r₀ ↦ ?_
  rw [cwRevNx_sing hK]
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Idle) _ _
    (modedP_readLift _ (modedP_grindK upd pub K _ _ _ (by omega))) fun g μ hμ ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · exact hnone μ hμ
  · exact hsome c x μ hμ

/-- The final modes of a layer signature below the top: when it signs, the next key's search
next; otherwise between trials. -/
def NextFin {α : Type} (K' : Key) : Option α → CwMode → Prop
  | some _, μ => ∃ m', μ = .pend K' m'
  | none, μ => μ.Idle

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature by `K_l(idx)` below the top** ends, when it signs, with `K_{l+1}(idx)`'s
search next. -/
theorem modedP_signLayerT_next (pub : Pub) (B : QReg) {l l' : Layer} (hl : l.val < 2)
    (hl' : l'.val = l.val + 1) (idx : Index) (m : Digest) :
    ModedP (cwOkT pub.perm pub.seed (cwLiftHu upd)) (cwNxT pub.perm pub.seed)
      (fun p μ ↦ NextFin (keyOf l' idx) p.2.2 μ) (.pend (keyOf l idx) m)
      (signLayerT M upd pub B (keyOf l idx)) := by
  refine modedP_signLayerT_of upd pub B (inRange_keyOf l idx) m (fin := NextFin (keyOf l' idx))
    (fun μ hμ ↦ hμ) fun c x μ hμ ↦ ?_
  obtain ⟨hs, hd⟩ := cwKeys_layerNeed hl hl' idx x
  refine modedP_revealThen (fin := NextFin (keyOf l' idx)) _ _ hμ fun r ↦ ?_
  rw [show cwRevNx μ (valSet (layerNeed (keyOf l idx).1 (keyOf l idx).2.1 (keyOf l idx).2.2 x))
    (extendVals r.1) = .pend (keyOf l' idx) (extendVals r.1 (msgPos (keyOf l' idx))) from
    cwRevNx_disc hs hd μ _]
  exact modedP₂_bind (F := fun _ (μ : CwMode) ↦
      μ = .pend (keyOf l' idx) (extendVals r.1 (msgPos (keyOf l' idx))))
    (F' := NextFin (keyOf l' idx)) _ _
    (cPend_progSlots pub B _ _ _) fun _ _ h ↦ ⟨_, h⟩

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature** by a key of the signatures, from its search next, ends between
trials. -/
theorem modedP_signLayerT_idle (pub : Pub) (B : QReg) {K : Key} (hK : InRange K) (m : Digest) :
    ModedP (cwOkT pub.perm pub.seed (cwLiftHu upd)) (cwNxT pub.perm pub.seed)
      (fun _ (μ : CwMode) ↦ μ.Idle) (.pend K m) (signLayerT M upd pub B K) :=
  modedP_signLayerT_of upd pub B hK m (fin := fun _ μ ↦ μ.Idle) (fun _ h ↦ h)
    fun _ _ μ hμ ↦ cIdle_revealThen _ _ (fun _ ↦ cIdle_bind _ _ (cIdle_progSlots pub B _)
      fun _ ↦ cIdle_pure _) μ hμ

omit [Fintype M] [DecidableEq M] in
/-- **A signature is moded between trials.** -/
theorem cIdle_signT (pol : DigestPolicy) (pub : Pub) (B : QReg) (msg : Message) :
    CIdle pub.perm pub.seed (cwLiftHu upd) (signT M upd pol pub B msg) := by
  intro μ hμ
  unfold signT
  refine modedP_revealThen (fin := fun _ (μ : CwMode) ↦ μ.Idle) _ _ hμ fun r₁ ↦
    modedP_revealThen (fin := fun _ (μ : CwMode) ↦ μ.Idle) _ _ (cwRevNx_idle _ _ _)
    fun r₂ ↦ ?_
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Idle) (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _
    (cIdle_progPorts B _ _ (cwRevNx_idle _ _ _)) fun _ μ₁ h₁ ↦ ?_
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ ∃ m, μ = .pend (keyOf 0 _) m)
    (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _ (modedP_forsOpenT upd pub B _ _ h₁) fun _ μ₂ h₂ ↦ ?_
  obtain ⟨m₂, rfl⟩ := h₂
  refine modedP₂_bind (F := NextFin (keyOf 1 _)) (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _
    (modedP_signLayerT_next upd pub B (l := 0) (l' := 1) (by decide) rfl _ m₂)
    fun s₀ μ₃ h₃ ↦ ?_
  rcases s₀ with _ | bottom
  · exact h₃
  obtain ⟨m₃, rfl⟩ := h₃
  refine modedP₂_bind (F := NextFin (keyOf 2 _)) (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _
    (modedP_signLayerT_next upd pub B (l := 1) (l' := 2) (by decide) rfl _ m₃)
    fun s₁ μ₄ h₄ ↦ ?_
  rcases s₁ with _ | middle
  · exact h₄
  obtain ⟨m₄, rfl⟩ := h₄
  refine modedP₂_bind (F := fun _ (μ : CwMode) ↦ μ.Idle) (F' := fun _ (μ : CwMode) ↦ μ.Idle) _ _
    (modedP_signLayerT_idle upd pub B (inRange_keyOf 2 _) m₄) fun s₂ μ₅ h₅ ↦ ?_
  rcases s₂ with _ | top
  · exact h₅
  · exact h₅

omit [Fintype M] [DecidableEq M] in
theorem cIdle_challengeT (pol : DigestPolicy) (pub : Pub) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    ∀ μ : CwMode, μ.Idle → ModedP (cwOkT pub.perm pub.seed (cwLiftHu upd))
      (cwNxT pub.perm pub.seed) (fun _ (μ : CwMode) ↦ μ.Idle) μ (challengeT M upd pol pub A c) := by
  intro μ hμ
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact modedP_readLift _ (modedP_liftOrdinary _ μ hμ)
  · exact modedP_readLift _ (modedP_liftOrdinary _ μ hμ)
  · exact modedP_bind (fin := fun _ (μ : CwMode) ↦ μ.Idle) _ _ (cIdle_bind _ _ (cIdle_act _)
      (fun _ ↦ cIdle_signT upd pol pub _ msg) μ hμ) fun _ _ _ h ↦ h

omit [Fintype M] [DecidableEq M] in
theorem modedP_cast {spec : QuantumOracleSpec.{0, 0}} {ok : CwMode → spec.Port → Prop}
    {nx : CwMode → (i : spec.Port) → spec.Result i → CwMode} {Ω : QReg → Type w}
    {fin : (Σ u, Ω u) → CwMode → Prop} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) (μ : CwMode) :
    ModedP ok nx fin μ (e ▸ y) ↔ ModedP ok nx fin μ y := by
  subst e
  rfl

omit [Fintype M] [DecidableEq M] in
/-- Substituting trees moded between trials. -/
theorem modedP_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments (SSpec M)))
    (hσ : ∀ A c, ∀ μ : CwMode, μ.Idle → ModedP (cwOkT π P hu) (cwNxT π P)
      (fun _ (μ : CwMode) ↦ μ.Idle) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ : CwMode, μ.Idle → ModedP (cwOkT π P hu) (cwNxT π P) (fun _ (μ : CwMode) ↦ μ.Idle) μ
      (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ h ↦ h
  | liftBind s c next ih =>
    intro μ hμ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ hμ) fun u ans μ' h ↦ (modedP_cast ans.2 _ _).mpr
      (ih ans.1 μ' h)

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix is moded**: its reads are the searches' trials. -/
theorem cIdle_prefixT (pol : DigestPolicy) (pub : Pub) (A : SAdversary) :
    CIdle pub.perm pub.seed (cwLiftHu upd) (prefixT M upd pol pub A) :=
  cIdle_revealThen _ _ fun _ ↦ cIdle_bind _ _
    (modedP_substitute _ (cIdle_challengeT upd pol pub) _) fun _ ↦ cIdle_pure _

omit [Fintype M] [DecidableEq M] in
/-- **The realized challenge prefix is moded**, from the free mode. -/
theorem modedP_prefixR' (pol : DigestPolicy) (pub : Pub) (A : SAdversary)
    (v : (s : HPos) → XD s) :
    ModedP (cwOkZ pub.perm pub.seed (cwLiftHu upd)) (cwNxZ pub.perm pub.seed v)
      (fun _ (μ : CwMode) ↦ μ.Idle) .free (realizeT v (prefixT M upd pol pub A)) :=
  modedP_realizeT v _ (cIdle_prefixT upd pol pub A .free trivial)

end trialPrefix

end modes

/-! ## The codeword-recorded mass as a diagonal mass -/

section mass

/-- **The codeword-recorded states per port**: at a trial's read port, CostRefined's `CwRec` at
its cell and trial; nothing at the other ports. -/
def cwSet : ∀ i : (recHwSpec X Z HPos Selections).Port,
    Set ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
  | .inl (.inl (.inr c)) => {q : Unit × HwReg X Z (Mem HPos) | IsTrial trialUpd c ∧
      CwRec (trialOf trialUpd c).1 (trialOf trialUpd c).2 q.2}
  | _ => ∅

/-- The codeword-recorded mass of a port is the diagonal mass of `cwSet` on positive semidefinite
inputs. -/
theorem cwWt_eq_diagMass (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ)
    (hσ : σ.PosSemidef) :
    extWeight (hwCost (cwRecW Prod.snd trialUpd) fun _ _ ↦ 0) i σ = diagMass (cwSet i) σ := by
  have h0 : ∀ (S : Set ((recHwSpec X Z HPos Selections).In i ×
      QReg.of (HwReg X Z (Mem HPos)))), S = ∅ → diagMass S σ = 0 := fun S hS ↦ by
    subst hS
    exact Finset.sum_eq_zero fun a _ ↦ Set.indicator_of_notMem (Set.notMem_empty a) _
  rcases i with ((p | c) | c) | T
  · exact (h0 _ rfl).symm
  · have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    show cwRecW Prod.snd trialUpd c σ = diagMass (cwSet (.inl (.inl (.inr c)))) σ
    by_cases ht : IsTrial trialUpd c
    · simp only [cwRecW, ht, ↓reduceIte]
      exact ofReal_sum_ite_eq_diagMass (n := Unit × HwReg X Z (Mem HPos))
        {q | IsTrial trialUpd c ∧ CwRec (trialOf trialUpd c).1 (trialOf trialUpd c).2 q.2}
        (fun q ↦ CwRec (trialOf trialUpd c).1 (trialOf trialUpd c).2 q.2)
        (fun _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨ht, h⟩⟩) σ hre
    · simp only [cwRecW, ht, ↓reduceIte]
      exact (Finset.sum_eq_zero fun q _ ↦ Set.indicator_of_notMem (fun h ↦ ht h.1) _).symm
  · exact (h0 _ rfl).symm
  · exact (h0 _ rfl).symm

/-- **The codeword-recorded mass of the prefix as a diagonal mass.** -/
theorem cwRecPre_eq_diag (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) :
    cwRecPre pol A p v = (runtimeR m0R).totalWeight .instruments (fun i ↦ diagMass (cwSet i))
      (prefixR pol A p v) initR :=
  le_antisymm
    (totalWeight_le_totalWeight _ _ (fun i σ hσ ↦ (cwWt_eq_diagMass i σ hσ).le) _
      initR_posSemidef)
    (totalWeight_le_totalWeight _ _ (fun i σ hσ ↦ (cwWt_eq_diagMass i σ hσ).ge) _
      initR_posSemidef)

end mass

/-! ## The codeword-recorded potentials of the searches -/

section main

/-- The key `K` is unselected. -/
def cwU (K : Key) (m : Mem HPos) : Prop :=
  m.2 K = none

/-- The codeword-recorded predicate of the key `K`: the `h`-cell not hardwired, the key
unselected, recorded with a value selecting it. -/
def cwHp (K : Key) : HitPred X Z (Mem HPos) :=
  fun xi z dh wm ↦ wm.1.1 z = none ∧ cwU K wm.2 ∧
    ∃ y, dh z = some y ∧ Codeword.Valid (trunc128 (xi + y))

/-- A recorded `h`-cell that is not hardwired. -/
def anyHp : HitPred X Z (Mem HPos) :=
  fun _ z dh wm ↦ wm.1.1 z = none ∧ ∃ y, dh z = some y

theorem cwHp_anyHp (K : Key) (xi : X) (z : Z) (dh : Database Z X) (wm : Hw X Z × Mem HPos)
    (h : cwHp K xi z dh wm) : anyHp xi z dh wm := by
  obtain ⟨h1, -, y, h3, -⟩ := h
  exact ⟨h1, y, h3⟩

/-- **Trial `j` already started**: its block is recorded or hardwired, the key unselected. -/
def cwTD (P : PublicParameter) (K : Key) (m : Digest) (j : ℕ) : Set (HwReg X Z (Mem HPos)) :=
  {s | (s.1.2.1 (cwBlk P K m j) ≠ none ∨ s.2.1.2.1 (cwBlk P K m j) ≠ none) ∧ cwU K s.2.2}

/-- The index of the potentials: a `k'`-read's outcome, or a trial with four copies. -/
abbrev CwJ : Type := Option (Option Z × Mem HPos) ⊕ (Fin encodingAttemptLimit × Fin 4)

/-- **The potentials of the search modes**: after a trial's `k`-read, the codeword-recorded
`h`-cell through each outcome of its `k'`-read; after its `k'`-read, the codeword-recorded `h`-cell;
in a search, four times each later trial already started; with `K`'s value disclosed and its search
next, four times each of its trials already started on the value `v (msgPos K)`. -/
noncomputable def cwKp (π : Equiv.Perm (X × Z)) (P : PublicParameter) (v : (s : HPos) → XD s) :
    CwMode → CwJ → Matrix (HwReg X Z (Mem HPos)) (HwReg X Z (Mem HPos)) ℂ
  | .afK K m j a, .inl (some r) =>
      setProj (cwHit (cwHp K) (π (cwBlk P K m j, a)).1
        ((π (cwBlk P K m j, a)).2 + r.1.getD 0)) *
        readKrausK' (π (cwBlk P K m j, a)).1 (fun m _ ↦ m) r
  | .afK' K _ _ xi z, .inl none => setProj (cwHit (cwHp K) xi z)
  | .pend K _, .inr i => setProj (cwTD P K (valsOf v (msgPos K)) i.1)
  | .grd K m j, .inr i => if j ≤ i.1.val then setProj (cwTD P K m i.1) else 0
  | .afK K m j _, .inr i => if j < i.1.val then setProj (cwTD P K m i.1) else 0
  | .afK' K m j _ _, .inr i => if j < i.1.val then setProj (cwTD P K m i.1) else 0
  | _, _ => 0

/-- A block of a counter trial of some key on some value under `PK.seed = P`. -/
def IsCwBlk (P : PublicParameter) (x : X) : Prop :=
  ∃ K m, ∃ j < encodingAttemptLimit, x = cwBlk P K m j

open scoped Classical in
/-- **The charge of a program**: a program of a trial block's `k`-cell, four times its weight. -/
noncomputable def cwProgCharge (P : PublicParameter) :
    HwProg X Z → Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ → ℝ≥0∞
  | .programK x _, σ =>
      if IsCwBlk P x then 4 * potential (setProj (Set.univ : Set (HwReg X Z (Mem HPos)))) σ
      else 0
  | _, _ => 0

/-- **The charge of a reveal disclosing the value `K` signs among others**: four times each trial
of `K` already started on the value `v (msgPos K)`. -/
noncomputable def cwDiscCharge (P : PublicParameter) (v : (s : HPos) → XD s) (T : Finset HPos)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  match cwSingKey T with
  | some _ => 0
  | none => match cwDiscKey T with
    | some K => ∑ i : Fin encodingAttemptLimit × Fin 4,
        diagMass {q : Unit × HwReg X Z (Mem HPos) | q.2 ∈ cwTD P K (valsOf v (msgPos K)) i.1} σ
    | none => 0

/-- **The charges**: at a `k`-read, its fresh part; at a program of a trial block's `k`-cell, four
times its weight; at a reveal disclosing the value a key signs among others, four times each trial
of that key already started. -/
noncomputable def cwCharge (π : Equiv.Perm (X × Z)) (P : PublicParameter)
    (v : (s : HPos) → XD s) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ → ℝ≥0∞
  | .inl (.inl (.inr (.readK x _))), σ => ENNReal.ofReal (∑ s, cwFresh anyHp π x s * (σ s s).re)
  | .inl (.inr c), σ => cwProgCharge P c σ
  | .inr T, σ => cwDiscCharge P v T σ
  | _, _ => 0

/-- The no-`⊥` invariant at a call, in the decompressed basis. -/
def CwInv (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ) : Prop :=
  QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z (Mem HPos) ↦ m.2)
    {s | NoBot s} (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z HPos Selections).In i)
      ((recHwSpec X Z HPos Selections).In i) ℂ) ⊗ₖ compressReg X Z (Mem HPos)) σ)

/-! ### Facts per port -/

theorem cwU_of_upd (K : Key) (x xi : X) (m : Mem HPos) (o : Option X)
    (h : cwU K (cwLiftHu cwUpd K x xi m o)) : cwU K m := by
  unfold cwU at h ⊢
  by_contra hm
  rcases o with _ | y
  · exact hm h
  · have he : cwUpd K x xi m.2 (some y) = m.2 := ite_eq_right hm
    exact hm (he ▸ h)

/-- **The codeword-recorded states are those whose recorded value moves the memory.** -/
theorem cwRec_iff (z : Z) (t : TrialPt) (s : HwReg X Z (Mem HPos)) :
    CwRec z t s ↔
      s.2.1.1 z = none ∧ ∃ y, s.1.1 z = some y ∧ trialUpd t s.2.2 (some y) ≠ s.2.2 := by
  constructor
  · rintro ⟨h1, h2, y, h3, h4⟩
    refine ⟨h1, y, h3, fun he ↦ ?_⟩
    have hs : cwUpd t.K t.x t.xi s.2.2.2 (some y) = s.2.2.2 := congrArg Prod.snd he
    rw [cwUpd_some_of_none _ _ _ h2] at hs
    have hn := (cwSel_eq_none_iff h2 t.x t.xi y).not.mpr (not_not.mpr h4)
    exact hn (by rw [hs]; exact h2)
  · rintro ⟨h1, y, h3, h4⟩
    have h2 : s.2.2.2 t.K = none := by
      by_contra hm
      exact h4 (Prod.ext rfl (ite_eq_right hm))
    refine ⟨h1, h2, y, h3, ?_⟩
    by_contra hv
    apply h4
    refine Prod.ext rfl ?_
    show cwUpd t.K t.x t.xi s.2.2.2 (some y) = s.2.2.2
    rw [cwUpd_some_of_none _ _ _ h2]
    exact ite_eq_right hv

/-- **The codeword-recorded mass of a trial's `h`-read** is at most the potential of its mode. -/
theorem diagMass_cwSet_readH_le (K : Key) (x xi : X) (z : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    diagMass (cwSet (.inl (.inl (.inr (.readH z (cwLiftHu cwUpd K x xi)))))) σ ≤
      potential (setProj (cwHit (cwHp K) xi z)) σ := by
  rw [potential_setProj _ hσ]
  refine diagMass_mono (fun q hq ↦ ?_) σ
  obtain ⟨ht, hc⟩ := hq
  have he := eq_readH_trialOf trialUpd ht
  set zt := trialOf trialUpd (.readH z (cwLiftHu cwUpd K x xi))
  obtain ⟨hz, hu⟩ := HwRead.readH.inj he
  obtain ⟨h1, y, h3, h4⟩ := (cwRec_iff _ _ _).1 hc
  rw [← hz] at h1 h3
  have h4' : cwLiftHu cwUpd K x xi q.2.2.2 (some y) ≠ q.2.2.2 := by
    rw [hu]
    exact h4
  exact (cwRec_iff z ⟨K, x, xi⟩ q.2).2 ⟨h1, y, h3, h4'⟩

theorem cwKp_free (π : Equiv.Perm (X × Z)) (P : PublicParameter) (v : (s : HPos) → XD s)
    (J : CwJ) : cwKp π P v .free J = 0 := by
  rcases J with (_ | _) | _ <;> rfl

theorem potential_ite_zero (c : Prop) [Decidable c]
    (K : Matrix (HwReg X Z (Mem HPos)) (HwReg X Z (Mem HPos)) ℂ)
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) :
    potential (if c then K else 0) σ = if c then potential K σ else 0 := by
  split_ifs
  · rfl
  · exact potential_zero σ

/-- The trial `j` term splits off the trials from `j` on. -/
theorem sum_le_split (f : Fin encodingAttemptLimit → ℝ≥0∞) {j : ℕ}
    (hj : j < encodingAttemptLimit) :
    ∑ i : Fin encodingAttemptLimit × Fin 4, (if j ≤ i.1.val then f i.1 else 0) =
      ∑ i : Fin encodingAttemptLimit × Fin 4, (if j < i.1.val then f i.1 else 0) +
        4 * f ⟨j, hj⟩ := by
  have hp : ∀ i : Fin encodingAttemptLimit, (if j ≤ i.val then f i else 0) =
      (if j < i.val then f i else 0) + if i = ⟨j, hj⟩ then f i else 0 := fun i ↦ by
    by_cases h1 : j < i.val
    · have h2 : i ≠ ⟨j, hj⟩ := fun h ↦ by rw [h] at h1; exact lt_irrefl _ h1
      rw [ite_eq_left h1.le, ite_eq_left h1, ite_eq_right h2, add_zero]
    · by_cases h3 : i = ⟨j, hj⟩
      · subst h3
        simp
      · have h4 : ¬ j ≤ i.val := fun h ↦ h3 (Fin.ext (le_antisymm (not_lt.mp h1) h))
        rw [ite_eq_right h4, ite_eq_right h1, ite_eq_right h3, add_zero]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hp, Finset.sum_add_distrib]
  norm_num

/-- The no-`⊥` invariant survives a read. -/
theorem cw_noBot_conj_read (c : HwRead X Z (Mem HPos)) (r : c.Result)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (h : QuerySupportedOn (fun m : Unit × HwReg X Z (Mem HPos) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Mem HPos)) σ)) :
    QuerySupportedOn (fun m : Unit × HwReg X Z (Mem HPos) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Mem HPos))
        (MatrixMap.conj (hwReadKraus c r) σ)) := by
  have hd := decR_step_noBot (S := HPos) m0R (.inl (.inl (.inr c))) r _ h
  set U : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ :=
    (1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Mem HPos)
  have hUh : Uᴴ = U := by
    simp only [U, conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressReg]
  have hUU : ∀ N : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ,
      U * (U * N) = N := fun N ↦ by
    rw [← Matrix.mul_assoc, show U * U = 1 by
      simp only [U, ← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self,
        one_kronecker_one], Matrix.one_mul]
  have he : MatrixMap.conj U (MatrixMap.conj (hwReadKraus c r) σ) =
      MatrixMap.conj (U * hwReadKraus c r * U) (MatrixMap.conj U σ) := by
    simp only [MatrixMap.conj_apply, conjTranspose_mul, hUh, Matrix.mul_assoc, hUU]
  rw [he]
  have hb := decR_branch_apply (S := HPos) (M := Selections) m0R (.inl (.inl (.inr c))) r _
    (runtime2_branch m0R (.inl (.inr c)) r) (MatrixMap.conj U σ)
  exact (congrArg (QuerySupportedOn (fun m : Unit × HwReg X Z (Mem HPos) ↦ m.2)
    {s | NoBot s}) hb).mp hd

/-- The register states of a trial already started, kept by a read of another `k`-cell. -/
theorem cwTD_keep_readK (P : PublicParameter) (K : Key) (m : Digest) {i : ℕ}
    {x : X} (hx : x ≠ cwBlk P K m i) (r : Option Z × Mem HPos)
    (s' a : Unit × HwReg X Z (Mem HPos))
    (h : hwReadKraus (.readK x fun m _ ↦ m) r s' a ≠ 0) :
    s'.2 ∈ cwTD P K m i ↔ a.2 ∈ cwTD P K m i := by
  obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
  obtain ⟨-, -, hk, hW, hm, hm'⟩ := cw_readKrausK_ne_zero x _ r hK
  have hmem : s'.2.2.2 = a.2.2.2 := by rw [hm', hm]
  simp only [cwTD, Set.mem_ofPred_eq, hk _ (Ne.symm hx), hW, hmem]

/-- The register states of a trial already started, kept by a read of a `k'`-cell. -/
theorem cwTD_keep_readK' (P : PublicParameter) (K : Key) (m : Digest) (i : ℕ)
    (y : X) (r : Option Z × Mem HPos) (s' a : Unit × HwReg X Z (Mem HPos))
    (h : hwReadKraus (.readK' y fun m _ ↦ m) r s' a ≠ 0) :
    s'.2 ∈ cwTD P K m i ↔ a.2 ∈ cwTD P K m i := by
  obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
  obtain ⟨-, hk, hW, hm, hm'⟩ := cw_readKrausK'_ne_zero y _ r hK
  have hmem : s'.2.2.2 = a.2.2.2 := by rw [hm', hm]
  simp only [cwTD, Set.mem_ofPred_eq, hk, hW, hmem]

/-- The register states of a trial already started, kept by a record port. -/
theorem cwTD_keep_rec (P : PublicParameter) (K : Key) (m : Digest) (i : ℕ)
    (T : Finset HPos) (mm : Mem HPos) (s' a : Unit × HwReg X Z (Mem HPos))
    (h : recKraus T mm s' a ≠ 0) :
    s'.2 ∈ cwTD P K m i ↔ a.2 ∈ cwTD P K m i := by
  have he := eq_of_recKraus_ne_zero (u := a.1) (u' := s'.1) (s := a.2) (s' := s'.2) h
  rw [he]
  rfl

/-- **A trial's `h`-read lowers the trials already started**: it can only select the key. -/
theorem sum_pot_cwTD_readH_le (P : PublicParameter) (K : Key) (m : Digest) (i : ℕ)
    (z : Z) (x xi : X)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ r : Option X × Mem HPos, potential (setProj (cwTD P K m i))
        (MatrixMap.conj (hwReadKraus (.readH z (cwLiftHu cwUpd K x xi)) r) σ) ≤
      potential (setProj (cwTD P K m i)) σ := by
  classical
  set u := cwLiftHu cwUpd K x xi
  refine cw_sum_pot_setProj_le (fun r ↦ hwReadKraus (.readH z u) r) (sum_hwReadKraus _) _ _
    (fun r ↦ if cwU K (u r.2 r.1) then 1 else 0) (fun r ↦ by split_ifs <;> norm_num)
    (fun r s' a h ↦ ?_) (fun r s' a b ha hb ↦ ?_) hσ
  · obtain ⟨-, hK⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) h
    obtain ⟨hk, hW, hm, hm'⟩ := cw_readKrausH_ne_zero z u r hK
    by_cases hc : cwU K (u r.2 r.1)
    · have hc' : cwU K a.2.2.2 := hm ▸ cwU_of_upd K x xi r.2 r.1 hc
      have hiff : s'.2 ∈ cwTD P K m i ↔ a.2 ∈ cwTD P K m i := by
        simp only [cwTD, Set.mem_ofPred_eq, hk, hW, hm', hm]
        rw [hm] at hc'
        simp only [hc, hc', and_true]
      rw [ite_eq_left hc, one_mul]
      by_cases ha : a.2 ∈ cwTD P K m i
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hiff.2 ha), Pi.one_apply,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (mt hiff.1 ha)]
    · rw [ite_eq_right hc, zero_mul]
      refine Set.indicator_of_notMem (fun hs ↦ hc ?_) _
      have := hs.2
      rwa [hm'] at this
  · obtain ⟨-, hKa⟩ := one_kronecker_ne_zero (a := a.1) (a' := s'.1) (b := a.2) (b' := s'.2) ha
    obtain ⟨-, hKb⟩ := one_kronecker_ne_zero (a := b.1) (a' := s'.1) (b := b.2) (b' := s'.2) hb
    obtain ⟨hka, hWa, hma, -⟩ := cw_readKrausH_ne_zero z u r hKa
    obtain ⟨hkb, hWb, hmb, -⟩ := cw_readKrausH_ne_zero z u r hKb
    have hiff : a.2 ∈ cwTD P K m i ↔ b.2 ∈ cwTD P K m i := by
      simp only [cwTD, Set.mem_ofPred_eq, ← hka, ← hkb, ← hWa, ← hWb, hma, hmb]
    by_cases ha' : a.2 ∈ cwTD P K m i
    · rw [Set.indicator_of_mem ha', Set.indicator_of_mem (hiff.1 ha'), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem ha', Set.indicator_of_notMem (mt hiff.2 ha')]

theorem cwRecHw_eq_indicator (P : PublicParameter) (K : Key) (m : Digest) (j : ℕ)
    (s : Unit × HwReg X Z (Mem HPos)) :
    cwRecHw (cwU K) (cwBlk P K m j) s = Set.indicator (cwTD P K m j) 1 s.2 := by
  classical
  unfold cwRecHw
  by_cases h : s.2 ∈ cwTD P K m j
  · rw [Set.indicator_of_mem h, Pi.one_apply]
    exact ite_eq_left h
  · rw [Set.indicator_of_notMem h]
    exact ite_eq_right h

theorem cw_potential_setProj_eq_sum (S : Set (HwReg X Z (Mem HPos)))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) :
    potential (setProj S) σ = ENNReal.ofReal (∑ s, (S.indicator 1 s.2 : ℝ) * (σ s s).re) :=
  cw_potential_setProj_eq_dW S σ

/-- A program changes the recorded `k`-cell `y` only by programming it. -/
theorem cw_progKraus_dbk (c : HwProg X Z) (r : c.Result) {s s' : HwReg X Z (Mem HPos)}
    (h : hwProgKraus c r ((), s') ((), s) ≠ 0) (y : X) (hy : ∀ w, c ≠ .programK y w) :
    s'.1.2.1 y = s.1.2.1 y := by
  rcases c with ⟨z, w⟩ | ⟨x, w⟩ | ⟨x, w⟩
  · simp only [hwProgKraus, programKrausH] at h
    obtain ⟨-, -, hR⟩ := cw_clsKraus_ne_zero (one_kronecker_ne_zero h).2
    rw [kroneckerMap_apply] at hR
    have h₂ := right_ne_zero_of_mul hR
    have he : s'.1.2 = s.1.2 := by
      by_contra hne
      exact h₂ (Matrix.one_apply_ne hne)
    rw [he]
  · simp only [hwProgKraus, programKrausK] at h
    obtain ⟨-, -, hR⟩ := cw_clsKraus_ne_zero (one_kronecker_ne_zero h).2
    rw [kroneckerMap_apply, kroneckerMap_apply] at hR
    have h₂ := left_ne_zero_of_mul (right_ne_zero_of_mul hR)
    have hyx : y ≠ x := fun e ↦ hy w (by rw [e])
    exact cellDiscard_apply_ne_zero h₂ y hyx
  · simp only [hwProgKraus, programKrausK'] at h
    obtain ⟨-, -, hR⟩ := cw_clsKraus_ne_zero (one_kronecker_ne_zero h).2
    rw [kroneckerMap_apply, kroneckerMap_apply] at hR
    have h₂ := left_ne_zero_of_mul (right_ne_zero_of_mul hR)
    have he : s'.1.2.1 = s.1.2.1 := by
      by_contra hne
      exact h₂ (Matrix.one_apply_ne hne)
    rw [he]

/-- The register states of a trial already started, kept by a program of another cell. -/
theorem cwTD_keep_prog (P : PublicParameter) (K : Key) (m : Digest) (i : ℕ) (c : HwProg X Z)
    (hc : ∀ w, c ≠ .programK (cwBlk P K m i) w) (r : c.Result)
    (s' a : Unit × HwReg X Z (Mem HPos)) (h : hwProgKraus c r s' a ≠ 0) :
    s'.2 ∈ cwTD P K m i ↔ a.2 ∈ cwTD P K m i := by
  have hs := hwProgKraus_ne_zero_snd c r (u := a.1) (u' := s'.1) (s := a.2) (s' := s'.2) h
  have hk := cw_progKraus_dbk c r (s := a.2) (s' := s'.2) h _ hc
  have hW : s'.2.2.1.2.1 (cwBlk P K m i) = a.2.2.1.2.1 (cwBlk P K m i) :=
    (congrArg (fun t : Hw X Z × Mem HPos ↦ t.1.2.1 (cwBlk P K m i)) hs).trans
      (progUpdate_k_of c _ _ hc)
  have hm : s'.2.2.2 = a.2.2.2 := by
    have h' := congrArg (fun t : Hw X Z × Mem HPos ↦ t.2) hs
    exact h'
  unfold cwTD
  simp only [Set.mem_ofPred_eq]
  rw [hk, hW, hm]

/-- A projector's potential is at most the full one. -/
theorem potential_setProj_le_univ (S : Set (HwReg X Z (Mem HPos)))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    potential (setProj S) σ ≤ potential (setProj (Set.univ : Set (HwReg X Z (Mem HPos)))) σ := by
  rw [potential_setProj _ hσ, potential_setProj _ hσ]
  exact diagMass_mono (fun q _ ↦ Set.mem_univ q.2) σ

/-- **A projector's potential after a program** is at most the full potential before. -/
theorem sum_pot_prog_le (c : HwProg X Z) (S : Set (HwReg X Z (Mem HPos)))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ r, potential (setProj S) (MatrixMap.conj (hwProgKraus c r) σ) ≤
      potential (setProj (Set.univ : Set (HwReg X Z (Mem HPos)))) σ :=
  (Finset.sum_le_sum fun _ _ ↦ potential_setProj_le_univ S (posSemidef_conj _ hσ)).trans
    (cw_sum_pot_setProj_keep (fun r ↦ hwProgKraus c r) (sum_hwProgKraus c) _
      (fun _ _ _ _ ↦ iff_of_true (Set.mem_univ _) (Set.mem_univ _)) hσ)

variable (π : Equiv.Perm (X × Z)) (P : PublicParameter) (v : (s : HPos) → XD s)

theorem cwKp_grd_sum (K : Key) (m : Digest) (j : ℕ)
    (τ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) :
    ∑ J, potential (cwKp π P v (.grd K m j) J) τ =
      ∑ i : Fin encodingAttemptLimit × Fin 4,
        (if j ≤ i.1.val then potential (setProj (cwTD P K m i.1)) τ else 0) := by
  rw [Fintype.sum_sum_type, Fintype.sum_option]
  simp only [cwKp, potential_zero, zero_add, Finset.sum_const_zero, potential_ite_zero]

theorem cwKp_pend_sum (K : Key) (m : Digest)
    (τ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) :
    ∑ J, potential (cwKp π P v (.pend K m) J) τ =
      ∑ i : Fin encodingAttemptLimit × Fin 4,
        potential (setProj (cwTD P K (valsOf v (msgPos K)) i.1)) τ := by
  rw [Fintype.sum_sum_type, Fintype.sum_option]
  simp only [cwKp, potential_zero, zero_add, Finset.sum_const_zero]

/-- **The step of a trial's `k`-read**: the potentials after it are at most those before plus its
fresh part. -/
theorem cw_step_readK (K : Key) (m : Digest) {j : ℕ} (hj : j < encodingAttemptLimit)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef)
    (hinv : QuerySupportedOn (fun m : Unit × HwReg X Z (Mem HPos) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Mem HPos)) σ)) :
    ∑ r : Option Z × Mem HPos, ∑ J, potential (cwKp π P v (.afK K m j (r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK (cwBlk P K m j) fun m _ ↦ m) r) σ) ≤
      ∑ J, potential (cwKp π P v (.grd K m j) J) σ +
        ENNReal.ofReal (∑ s, cwFresh anyHp π (cwBlk P K m j) s * (σ s s).re) := by
  set x := cwBlk P K m j with hx
  have hre : ∀ s, 0 ≤ (σ s s).re := fun s ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hL : ∀ r : Option Z × Mem HPos, ∑ J, potential (cwKp π P v (.afK K m j (r.1.getD 0)) J)
      (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) =
      ∑ r' : Option Z × Mem HPos, potential (setProj (cwHit (cwHp K) (π (x, r.1.getD 0)).1
          ((π (x, r.1.getD 0)).2 + r'.1.getD 0)) * readKrausK' (π (x, r.1.getD 0)).1
            (fun m _ ↦ m) r') (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) +
        ∑ i : Fin encodingAttemptLimit × Fin 4, (if j < i.1.val then
          potential (setProj (cwTD P K m i.1))
            (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) else 0) := fun r ↦ by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, zero_add, potential_ite_zero]
    rfl
  simp only [hL, cwKp_grd_sum, Finset.sum_add_distrib]
  rw [sum_le_split (fun i ↦ potential (setProj (cwTD P K m i)) σ) hj]
  have hnb : CellNoBot (splitK x) (actK x) σ := readNoBot_of_noBot (.readK x fun m _ ↦ m) hinv
  have hnb' : ∀ r : Option Z × Mem HPos, CellNoBot (splitK' (π (x, r.1.getD 0)).1)
      (actK' (π (x, r.1.getD 0)).1) (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) :=
    fun r ↦ readNoBot_of_noBot (.readK' (π (x, r.1.getD 0)).1 fun m _ ↦ m)
      (cw_noBot_conj_read (.readK x fun m _ ↦ m) r hinv)
  have h1 := sum_pot_cw_le (cwHp K) π x hσ hnb hnb'
  have hU : ∀ xi z dh wm, cwHp K xi z dh wm → cwU K wm.2 := fun _ _ _ _ h ↦ h.2.1
  have hpt : ∀ s, cB (splitK x) (actK x) (tauK x fun m _ ↦ m) (idxK x) (phiK x fun m _ ↦ m)
      (cwQOut (cwHp K) π x) s * (σ s s).re ≤
      4 * ((cwTD P K m j).indicator 1 s.2 * (σ s s).re) +
        cwFresh anyHp π x s * (σ s s).re := fun s ↦ by
    have hb := cB_out_le hU π x s
    have hf := cwFresh_mono (cwHp_anyHp K) π x s
    rw [cwRecHw_eq_indicator] at hb
    nlinarith [hre s]
  have h2 : ENNReal.ofReal (∑ s, cB (splitK x) (actK x) (tauK x fun m _ ↦ m) (idxK x)
      (phiK x fun m _ ↦ m) (cwQOut (cwHp K) π x) s * (σ s s).re) ≤
      4 * potential (setProj (cwTD P K m j)) σ +
        ENNReal.ofReal (∑ s, cwFresh anyHp π x s * (σ s s).re) := by
    rw [cw_potential_setProj_eq_sum]
    have hn1 : 0 ≤ ∑ s, ((cwTD P K m j).indicator 1 s.2 : ℝ) * (σ s s).re :=
      Finset.sum_nonneg fun s _ ↦ mul_nonneg (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
        (hre s)
    have hn2 : 0 ≤ ∑ s, cwFresh anyHp π x s * (σ s s).re :=
      Finset.sum_nonneg fun s _ ↦ mul_nonneg (cwFresh_nonneg _ _ _ _) (hre s)
    calc _ ≤ ENNReal.ofReal (4 * ∑ s, ((cwTD P K m j).indicator 1 s.2 : ℝ) * (σ s s).re +
          ∑ s, cwFresh anyHp π x s * (σ s s).re) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun s _ ↦ hpt s
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) hn2, ENNReal.ofReal_mul (by norm_num)]
          norm_num
  have h3 : ∑ r : Option Z × Mem HPos, ∑ i : Fin encodingAttemptLimit × Fin 4,
      (if j < i.1.val then potential (setProj (cwTD P K m i.1))
        (MatrixMap.conj (hwReadKraus (.readK x fun m _ ↦ m) r) σ) else 0) ≤
      ∑ i : Fin encodingAttemptLimit × Fin 4,
        (if j < i.1.val then potential (setProj (cwTD P K m i.1)) σ else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    by_cases hi : j < i.1.val
    · simp only [ite_eq_left hi]
      have hne : x ≠ cwBlk P K m i.1 := fun h ↦
        (Nat.ne_of_lt hi) (cwBlk_inj P hj i.1.isLt h).2.2
      exact cw_sum_pot_setProj_keep (fun r ↦ hwReadKraus (.readK x fun m _ ↦ m) r)
        (sum_hwReadKraus _) _ (cwTD_keep_readK P K m hne) hσ
    · simp only [ite_eq_right hi, Finset.sum_const_zero, le_refl]
  calc _ ≤ (4 * potential (setProj (cwTD P K m j)) σ +
        ENNReal.ofReal (∑ s, cwFresh anyHp π x s * (σ s s).re)) +
        ∑ i : Fin encodingAttemptLimit × Fin 4,
          (if j < i.1.val then potential (setProj (cwTD P K m i.1)) σ else 0) :=
        add_le_add (h1.trans h2) h3
    _ = _ := by ring

/-- **The step of a trial's `k'`-read**: the potentials move exactly. -/
theorem cw_step_readK' (K : Key) (m : Digest) (j : ℕ) (a : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑ r : Option Z × Mem HPos, ∑ J, potential (cwKp π P v (.afK' K m j
        (π (cwBlk P K m j, a)).1 ((π (cwBlk P K m j, a)).2 + r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK' (π (cwBlk P K m j, a)).1 fun m _ ↦ m) r) σ) ≤
      ∑ J, potential (cwKp π P v (.afK K m j a) J) σ := by
  set y := (π (cwBlk P K m j, a)).1
  have hL : ∀ r : Option Z × Mem HPos, ∑ J, potential (cwKp π P v (.afK' K m j y
      ((π (cwBlk P K m j, a)).2 + r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK' y fun m _ ↦ m) r) σ) =
      potential (setProj (cwHit (cwHp K) y ((π (cwBlk P K m j, a)).2 + r.1.getD 0)) *
        readKrausK' y (fun m _ ↦ m) r) σ +
        ∑ i : Fin encodingAttemptLimit × Fin 4, (if j < i.1.val then
          potential (setProj (cwTD P K m i.1))
            (MatrixMap.conj (hwReadKraus (.readK' y fun m _ ↦ m) r) σ) else 0) := fun r ↦ by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, Finset.sum_const_zero, add_zero, potential_ite_zero]
    rw [← potential_conj_kron]
    rfl
  have hR : ∑ J, potential (cwKp π P v (.afK K m j a) J) σ =
      ∑ r : Option Z × Mem HPos, potential (setProj (cwHit (cwHp K) y
        ((π (cwBlk P K m j, a)).2 + r.1.getD 0)) * readKrausK' y (fun m _ ↦ m) r) σ +
      ∑ i : Fin encodingAttemptLimit × Fin 4,
        (if j < i.1.val then potential (setProj (cwTD P K m i.1)) σ else 0) := by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, zero_add, potential_ite_zero]
    rfl
  simp only [hL, hR, Finset.sum_add_distrib]
  refine add_le_add le_rfl ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hi : j < i.1.val
  · simp only [ite_eq_left hi]
    exact cw_sum_pot_setProj_keep (fun r ↦ hwReadKraus (.readK' y fun m _ ↦ m) r)
      (sum_hwReadKraus _) _ (cwTD_keep_readK' P K m i.1 y) hσ
  · simp only [ite_eq_right hi, Finset.sum_const_zero, le_refl]

/-- **The step of a trial's `h`-read**: its codeword-recorded mass is paid by the potential of its
mode; the later trials can only lose their unselected key. -/
theorem cw_step_readH (K : Key) (m : Digest) (j : ℕ) (xi : X) (z : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    diagMass (cwSet (.inl (.inl (.inr (.readH z
        (cwLiftHu cwUpd K (cwBlk P K m j) xi)))))) σ +
      ∑ r : Option X × Mem HPos, ∑ J, potential (cwKp π P v (.grd K m (j + 1)) J)
        (MatrixMap.conj (hwReadKraus (.readH z
          (cwLiftHu cwUpd K (cwBlk P K m j) xi)) r) σ) ≤
      ∑ J, potential (cwKp π P v (.afK' K m j xi z) J) σ := by
  set u := cwLiftHu cwUpd K (cwBlk P K m j) xi
  have hL : ∀ r : Option X × Mem HPos, ∑ J, potential (cwKp π P v (.grd K m (j + 1)) J)
      (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) =
      ∑ i : Fin encodingAttemptLimit × Fin 4, (if j < i.1.val then
        potential (setProj (cwTD P K m i.1))
          (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) else 0) := fun r ↦ by
    rw [cwKp_grd_sum]
    simp only [Nat.succ_le_iff]
  have hR : ∑ J, potential (cwKp π P v (.afK' K m j xi z) J) σ =
      potential (setProj (cwHit (cwHp K) xi z)) σ +
      ∑ i : Fin encodingAttemptLimit × Fin 4,
        (if j < i.1.val then potential (setProj (cwTD P K m i.1)) σ else 0) := by
    rw [Fintype.sum_sum_type, Fintype.sum_option]
    simp only [cwKp, potential_zero, Finset.sum_const_zero, add_zero, potential_ite_zero]
  simp only [hL, hR]
  refine add_le_add (diagMass_cwSet_readH_le K _ xi z hσ) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hi : j < i.1.val
  · simp only [ite_eq_left hi]
    exact sum_pot_cwTD_readH_le P K m i.1 z _ xi hσ
  · simp only [ite_eq_right hi, Finset.sum_const_zero, le_refl]

/-- **The step of a reveal**: the reveal of the value `K` signs from `K`'s pending mode keeps its
potential; a reveal disclosing it among others is charged the trials already started. -/
theorem cw_step_rec (μ : CwMode) (T : Finset HPos)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' mm : Mem HPos, ∑ J, potential (cwKp π P v (cwRevNx μ T (valsOf v)) J)
        (MatrixMap.conj (recKraus (X := X) (Z := Z) T mm) σ) ≤
      ∑ J, potential (cwKp π P v μ J) σ + cwDiscCharge P v T σ := by
  rw [tsum_fintype]
  have hkeep : ∀ (K : Key) (m : Digest) (i : ℕ), ∑ mm : Mem HPos,
      potential (setProj (cwTD P K m i)) (MatrixMap.conj (recKraus (X := X) (Z := Z) T mm) σ) ≤
        potential (setProj (cwTD P K m i)) σ := fun K m i ↦
    cw_sum_pot_setProj_keep (fun mm ↦ recKraus (X := X) (Z := Z) T mm) (sum_recKraus T) _
      (cwTD_keep_rec P K m i T) hσ
  have hfree : ∀ mm : Mem HPos, ∑ J, potential (cwKp π P v .free J)
      (MatrixMap.conj (recKraus (X := X) (Z := Z) T mm) σ) = 0 := fun mm ↦
    Finset.sum_eq_zero fun J _ ↦ by rw [cwKp_free]; exact potential_zero _
  unfold cwRevNx cwDiscCharge
  rcases hs : cwSingKey T with _ | K
  · dsimp only
    rcases hd : cwDiscKey T with _ | K
    · simp only [hfree, Finset.sum_const_zero, zero_le]
    · simp only [cwKp_pend_sum]
      rw [Finset.sum_comm]
      refine le_trans (Finset.sum_le_sum fun i _ ↦ ?_) le_add_self
      rw [← potential_setProj _ hσ]
      exact hkeep K _ i.1
  · dsimp only
    rcases μ with _ | ⟨K', m'⟩ | _ | _ | _
    all_goals try (simp only [hfree, Finset.sum_const_zero, zero_le]; done)
    dsimp only
    split_ifs with hK
    · subst hK
      simp only [cwKp_grd_sum, Nat.zero_le, ↓reduceIte, cwKp_pend_sum]
      rw [Finset.sum_comm]
      exact le_trans (Finset.sum_le_sum fun i _ ↦ hkeep K' _ i.1) le_self_add
    · simp only [hfree, Finset.sum_const_zero, zero_le]

open scoped Classical in
/-- The trials of `K` on `m` with a given block: at most one. -/
theorem sum_ite_cwBlk_le (K : Key) (m : Digest) (x : X) (c : ℝ≥0∞) :
    ∑ i : Fin encodingAttemptLimit × Fin 4, (if x = cwBlk P K m i.1 then c else 0) ≤
      4 * if IsCwBlk P x then c else 0 := by
  by_cases hx : ∃ j : Fin encodingAttemptLimit, x = cwBlk P K m j
  · obtain ⟨j₀, hj₀⟩ := hx
    have hb : IsCwBlk P x := ⟨K, m, j₀.val, j₀.isLt, hj₀⟩
    have he : ∀ i : Fin encodingAttemptLimit × Fin 4,
        (if x = cwBlk P K m i.1 then c else 0) = if i.1 = j₀ then c else 0 := fun i ↦ by
      by_cases hi : i.1 = j₀
      · rw [ite_eq_left (by rw [hi]; exact hj₀), ite_eq_left hi]
      · refine (ite_eq_right fun h ↦ hi (Fin.ext ?_)).trans (ite_eq_right hi).symm
        exact (cwBlk_inj P j₀.isLt i.1.isLt (hj₀.symm.trans h)).2.2.symm
    rw [Finset.sum_congr rfl fun i _ ↦ he i,
      Fintype.sum_prod_type' (f := fun a (_ : Fin 4) ↦ if a = j₀ then c else 0)]
    have h4 : ∀ a : Fin encodingAttemptLimit, ∑ _b : Fin 4, (if a = j₀ then c else 0) =
        4 * if a = j₀ then c else 0 := fun a ↦ by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    rw [Finset.sum_congr rfl fun a _ ↦ h4 a, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ j₀,
      ite_eq_left (Finset.mem_univ _), ite_eq_left hb]
  · simp only [not_exists] at hx
    refine le_of_eq_of_le (Finset.sum_eq_zero fun i _ ↦ ite_eq_right (hx i.1)) zero_le

/-- **The step of a program**: a disclosed key's trials already started move only when the program
hardwires one of their blocks. -/
theorem cw_step_prog (μ : CwMode) (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' r, ∑ J, potential (cwKp π P v (cwProgNx μ) J) (MatrixMap.conj (hwProgKraus c r) σ) ≤
      ∑ J, potential (cwKp π P v μ J) σ + cwProgCharge P c σ := by
  classical
  rw [tsum_fintype]
  have hfree : ∀ r, ∑ J, potential (cwKp π P v .free J) (MatrixMap.conj (hwProgKraus c r) σ) =
      0 := fun r ↦ Finset.sum_eq_zero fun J _ ↦ by rw [cwKp_free]; exact potential_zero _
  rcases μ with _ | ⟨K, m⟩ | _ | _ | _
  all_goals try (simp only [cwProgNx, hfree, Finset.sum_const_zero, zero_le]; done)
  simp only [cwProgNx, cwKp_pend_sum]
  rw [Finset.sum_comm]
  set U := potential (setProj (Set.univ : Set (HwReg X Z (Mem HPos)))) σ
  have hi : ∀ i : Fin encodingAttemptLimit × Fin 4,
      ∑ r, potential (setProj (cwTD P K (valsOf v (msgPos K)) i.1))
        (MatrixMap.conj (hwProgKraus c r) σ) ≤
      potential (setProj (cwTD P K (valsOf v (msgPos K)) i.1)) σ +
        (if ∃ w, c = .programK (cwBlk P K (valsOf v (msgPos K)) i.1) w then U else 0) := by
    intro i
    split_ifs with hc
    · exact (sum_pot_prog_le c _ hσ).trans le_add_self
    · simp only [not_exists] at hc
      rw [add_zero]
      exact cw_sum_pot_setProj_keep (fun r ↦ hwProgKraus c r) (sum_hwProgKraus c) _
        (cwTD_keep_prog P K _ i.1 c hc) hσ
  refine (Finset.sum_le_sum fun i _ ↦ hi i).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add le_rfl ?_
  rcases c with ⟨z, w⟩ | ⟨x, w⟩ | ⟨x, w⟩
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun ⟨_, h⟩ ↦ by cases h)
      zero_le
  · have he : ∀ i : Fin encodingAttemptLimit × Fin 4,
        (if ∃ w', HwProg.programK x w = .programK (cwBlk P K (valsOf v (msgPos K)) i.1) w'
          then U else 0) = if x = cwBlk P K (valsOf v (msgPos K)) i.1 then U else 0 :=
      fun i ↦ if_congr ⟨fun ⟨_, h⟩ ↦ (HwProg.programK.inj h).1, fun h ↦ ⟨w, by rw [h]⟩⟩ rfl rfl
    simp only [he]
    refine (sum_ite_cwBlk_le P K _ x U).trans (le_of_eq ?_)
    simp only [cwProgCharge, mul_ite, mul_zero]
    rfl
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun ⟨_, h⟩ ↦ by cases h)
      zero_le

theorem cw_step_readK_t (K : Key) (m : Digest) {j : ℕ} (hj : j < encodingAttemptLimit)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef)
    (hinv : QuerySupportedOn (fun m : Unit × HwReg X Z (Mem HPos) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Mem HPos)) σ)) :
    ∑' r : Option Z × Mem HPos, ∑ J, potential (cwKp π P v (.afK K m j (r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK (cwBlk P K m j) fun m _ ↦ m) r) σ) ≤
      ∑ J, potential (cwKp π P v (.grd K m j) J) σ +
        ENNReal.ofReal (∑ s, cwFresh anyHp π (cwBlk P K m j) s * (σ s s).re) := by
  rw [tsum_fintype]
  exact cw_step_readK π P v K m hj hσ hinv

theorem cw_step_readK'_t (K : Key) (m : Digest) (j : ℕ) (a : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' r : Option Z × Mem HPos, ∑ J, potential (cwKp π P v (.afK' K m j
        (π (cwBlk P K m j, a)).1 ((π (cwBlk P K m j, a)).2 + r.1.getD 0)) J)
        (MatrixMap.conj (hwReadKraus (.readK' (π (cwBlk P K m j, a)).1 fun m _ ↦ m) r) σ) ≤
      ∑ J, potential (cwKp π P v (.afK K m j a) J) σ := by
  rw [tsum_fintype]
  exact cw_step_readK' π P v K m j a hσ

theorem cw_step_readH_t (K : Key) (m : Digest) (j : ℕ) (xi : X) (z : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef) :
    diagMass (cwSet (.inl (.inl (.inr (.readH z
        (cwLiftHu cwUpd K (cwBlk P K m j) xi)))))) σ +
      ∑' r : Option X × Mem HPos, ∑ J, potential (cwKp π P v (.grd K m (j + 1)) J)
        (MatrixMap.conj (hwReadKraus (.readH z
          (cwLiftHu cwUpd K (cwBlk P K m j) xi)) r) σ) ≤
      ∑ J, potential (cwKp π P v (.afK' K m j xi z) J) σ := by
  rw [tsum_fintype]
  exact cw_step_readH π P v K m j xi z hσ

theorem diagMass_cwSet_of_not_readH (i : (recHwSpec X Z HPos Selections).Port)
    (hi : ∀ z u, i ≠ .inl (.inl (.inr (.readH z u))))
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ) :
    diagMass (cwSet i) σ = 0 := by
  have h : cwSet i = ∅ := by
    rcases i with ((i | c) | c) | T
    · rfl
    · refine Set.eq_empty_of_forall_notMem fun q hq ↦ ?_
      obtain ⟨⟨zt, hzt⟩, -⟩ := hq
      exact hi zt.1 _ (by rw [hzt])
    · rfl
    · rfl
  rw [h, diagMass_empty]

/-- **The step condition of the search modes** on the no-`⊥` invariant: the codeword-recorded mass
of every allowed call plus the potentials after it is at most the potentials before plus the
charge. -/
theorem cw_step (μ : CwMode) (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ)
    (hσ : σ.PosSemidef) (hinv : CwInv i σ) (hok : cwOkZ π P (cwLiftHu cwUpd) μ i) :
    diagMass (cwSet i) σ + ∑' r, ∑ J, potential (cwKp π P v (cwNxZ π P v μ i r) J)
        (((runtimeR m0R).step i).branch r σ) ≤
      ∑ J, potential (cwKp π P v μ J) σ + cwCharge π P v i σ := by
  rcases i with ((i | c) | c) | T
  · rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
    refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.mpr fun r ↦ Finset.sum_eq_zero fun J _ ↦ ?_))
      zero_le
    rw [show cwKp π P v (cwNxZ π P v μ (.inl (.inl (.inl i))) r) J = 0 from cwKp_free π P v J]
    exact potential_zero _
  · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    simp only [hb]
    rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;>
      rcases μ with _ | ⟨K, m⟩ | ⟨K, m, j⟩ | ⟨K, m, j, a⟩ | ⟨K, m, j, xi, z'⟩
    all_goals try exact hok.elim
    · obtain ⟨rfl, rfl⟩ := hok
      exact (cw_step_readH_t π P v K m j xi z hσ).trans le_self_add
    · obtain ⟨hj, rfl, rfl⟩ := hok
      rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
      exact cw_step_readK_t π P v K m hj hσ hinv
    · obtain ⟨rfl, rfl⟩ := hok
      rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
      exact (cw_step_readK'_t π P v K m j a hσ).trans le_self_add
  · rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
    have hb : ∀ r, ((runtimeR m0R).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r) σ
    simp only [hb]
    exact cw_step_prog π P v μ c hσ
  · rw [diagMass_cwSet_of_not_readH _ (fun _ _ h ↦ by cases h), zero_add]
    exact cw_step_rec π P v μ T hσ

/-- **The codeword-recorded mass of the challenge prefix is at most its charges**: the fresh parts
of the trials' `k`-reads, the programs of trial blocks, and at each reveal disclosing the value a
key signs among others, four times the trials of its search already started (block recorded or
hardwired, key unselected). -/
theorem cwRecPre_le_charge (pol : DigestPolicy) (A : SAdversary) (p : Pub)
    (v : (s : HPos) → XD s) :
    cwRecPre pol A p v ≤ (runtimeR m0R).totalWeight .instruments (cwCharge p.perm p.seed v)
      (prefixR pol A p v) initR := by
  rw [cwRecPre_eq_diag]
  have h := totalWeight_le_modedP_inv (runtimeR m0R) .instruments (cwKp p.perm p.seed v)
    _ CwInv (fun _ _ _ h ↦ h) (fun i σ ↦ diagMass (cwSet i) σ) (cwCharge p.perm p.seed v)
    (fun μ i σ hσ hi hok ↦ cw_step p.perm p.seed v μ i σ hσ hi hok)
    (prefixR pol A p v) .free (modedP_prefixR' cwUpd pol p A v)
    initR_posSemidef (forallQueries_noBot m0R .instruments _
      (noBot_init m0R (SubState.basis ()).matrix))
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_eq_zero fun J _ ↦ ?_, zero_add]
  rw [cwKp_free]
  exact potential_zero _

end main

/-! ## The charges, split; the fresh parts along the prefix -/

section freshRun

/-- The fresh parts of the trials' `k`-reads. -/
noncomputable def cwFreshW (π : Equiv.Perm (X × Z)) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ → ℝ≥0∞
  | .inl (.inl (.inr (.readK x _))), σ => ENNReal.ofReal (∑ s, cwFresh anyHp π x s * (σ s s).re)
  | _, _ => 0

/-- The charges of the programs of trial blocks. -/
noncomputable def cwProgW (P : PublicParameter) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ → ℝ≥0∞
  | .inl (.inr c), σ => cwProgCharge P c σ
  | _, _ => 0

/-- **The charges at the reveals** disclosing the value a key signs among others. -/
noncomputable def cwRevW (P : PublicParameter) (v : (s : HPos) → XD s) :
    ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
        ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ → ℝ≥0∞
  | .inr T, σ => cwDiscCharge P v T σ
  | _, _ => 0

theorem cwCharge_le (π : Equiv.Perm (X × Z)) (P : PublicParameter) (v : (s : HPos) → XD s)
    (i : (recHwSpec X Z HPos Selections).Port)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos)))
      ((recHwSpec X Z HPos Selections).In i × QReg.of (HwReg X Z (Mem HPos))) ℂ) :
    cwCharge π P v i σ ≤ cwFreshW π i σ + cwProgW P i σ + cwRevW P v i σ := by
  rcases i with ((i | c) | c) | T
  · exact zero_le
  · rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩
    · exact zero_le
    · exact le_self_add.trans le_self_add
    · exact zero_le
  · exact le_add_self.trans le_self_add
  · exact le_add_self

/-- **Every port of `runtimeR` hardwires at most one more `k'`-cell.** -/
theorem querySupportedOn_runtimeR_step_hwK' (i : (recHwSpec X Z HPos Selections).Port)
    (r : (recHwSpec X Z HPos Selections).Result i) (t : ℕ)
    (σ : Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
      ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (recHwSpec X Z HPos Selections).In i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ hwK'Count q.2.2.1) (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (recHwSpec X Z HPos Selections).Out i ×
      (runtimeR (X := X) (Z := Z) m0R).D ↦ hwK'Count q.2.2.1) (Set.Iic (t + 1))
        (((runtimeR (X := X) (Z := Z) m0R).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · have hb : ((runtimeR m0R).step (.inl (.inl (.inl i)))).branch r σ =
        MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U i) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R i r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m0R i q.1 q'.1 q.2 q'.2 hK
    show hwK'Count q'.2.2.1 ≤ t + 1
    rw [he]
    exact (Set.mem_Iic.mp hq).trans (Nat.le_succ t)
  · have hb : ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
    have he := hwReadKraus_ne_zero_hw c r (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK
    show hwK'Count q'.2.2.1 ≤ t + 1
    rw [he]
    exact (Set.mem_Iic.mp hq).trans (Nat.le_succ t)
  · have hb : ((runtimeR m0R).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    refine QuerySupportedOn.conj hσ fun q' q hK hq ↦ ?_
    have he := hwProgKraus_ne_zero_snd c r (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK
    show hwK'Count q'.2.2.1 ≤ t + 1
    rw [he]
    exact (hwK'Count_progUpdate_le c _).trans (Nat.succ_le_succ (Set.mem_Iic.mp hq))
  · exact querySupportedOn_recStep_hw T r t σ hσ

/-- The initial state has no hardwired cell. -/
theorem querySupportedOn_initR_hwK' :
    QuerySupportedOn (fun m : QReg.of Unit × (runtimeR (X := X) (Z := Z) m0R).D ↦
      hwK'Count m.2.2.1) (Set.Iic 0) initR := by
  intro m m' hm
  change ((SubState.basis ()).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m0R) : HwReg X Z (Mem HPos))).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h
  split_ifs at h with he
  · have h0 : hwK'Count (hwEmpty X Z) = 0 := by
      simp [hwK'Count, hwEmpty]
    refine ⟨?_, ?_⟩
    · show hwK'Count m.2.2.1 ≤ 0
      rw [← he.1]
      exact h0.le
    · show hwK'Count m'.2.2.1 ≤ 0
      rw [← he.2]
      exact h0.le
  · exact absurd rfl h

/-- The fresh part at a `k`-read on states with at most `G` recorded and `G` hardwired cells. -/
theorem cwFresh_le_eps (π : Equiv.Perm (X × Z)) (x : X) {G : ℕ}
    (s : Unit × HwReg X Z (Mem HPos)) (hg : dbGrade s.2.1 ≤ G) (hh : hwK'Count s.2.2.1 ≤ G) :
    cwFresh anyHp π x s ≤ cwFreshEps G := by
  have h1 : s.2.1.1.size ≤ G := (le_max_left _ _).trans hg
  have h2 : s.2.1.2.2.size ≤ G := ((le_max_right _ _).trans (le_max_right _ _)).trans hg
  refine (cwFresh_le_count (fun _ _ _ _ h ↦ ?_) π x s).trans ?_
  · obtain ⟨-, y, hy⟩ := h
    rw [hy]
    rfl
  · unfold cwFreshEps
    have hN : (0 : ℝ) ≤ 2 / Fintype.card Z := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hN
    have h3 : (hwK'Count s.2.2.1 + s.2.1.2.2.size) * s.2.1.1.size ≤ (G + G) * G :=
      Nat.mul_le_mul (Nat.add_le_add hh h2) h1
    have h4 : (s.2.1.1.size : ℝ) ≤ G := by exact_mod_cast h1
    have h5 : (((hwK'Count s.2.2.1 + s.2.1.2.2.size) * s.2.1.1.size : ℕ) : ℝ) ≤
        ((G + G) * G : ℕ) := by exact_mod_cast h3
    linarith

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The fresh parts along the prefix**: at most `cwFreshEps (6q + clsCap)` per read call, at most
`clsCap` classical calls. -/
theorem totalWeight_cwFreshW_le (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    (runtimeR m0R).totalWeight .instruments (cwFreshW p.perm) (prefixR pol A p v) initR ≤
      ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap := by
  set G := 6 * q + clsCap
  set x := prefixR pol A p v
  set κ : (recHwSpec X Z HPos Selections).Port → ℕ := fun i ↦
    (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 0 else 1) +
      (if extCls X Z (Mem HPos) (recSpec HPos Selections) i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls X Z (Mem HPos) (recSpec HPos Selections) i = true <;> simp [h]
  have hx : IFreeM.IsChargeBound x (portCharge κ) G :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl)
      ((advCalls_prefixR hperm hsign pol p v).add (clsCalls_prefixR hperm hsign pol p v))
  have hg := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ dbGrade s.1) κ (fun _ ↦ 0)
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_step m0R i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments x hx (isChargeBound_portCharge_zero x)
    querySupportedOn_initR
  have hh := forallQueries_of_charge_step (runtimeR m0R) (fun s ↦ hwK'Count s.2.1) κ
    (fun _ ↦ 0) (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_step_hwK' i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) .instruments x hx (isChargeBound_portCharge_zero x)
    querySupportedOn_initR_hwK'
  have hle := totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
        (runtimeR (X := X) (Z := Z) m0R).D ↦ dbGrade m.2.1) (Set.Iic (0 + G)) σ ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i ×
        (runtimeR (X := X) (Z := Z) m0R).D ↦ hwK'Count m.2.2.1) (Set.Iic (0 + G)) σ)
    (fun i E σ h ↦ ⟨querySupportedOn_traceRight h.1.2, querySupportedOn_traceRight h.2.2⟩)
    (w := cwFreshW p.perm)
    (w' := fun i σ ↦ ENNReal.ofReal (cwFreshEps G) * extWeight (hwCost
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
    (fun i σ hσ hok ↦ ?_) x initR_posSemidef (forallQueries_and hg hh)
  · refine hle.trans ?_
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m0R) .instruments
      (ENNReal.ofReal (cwFreshEps G)) (extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
        fun _ σ ↦ ENNReal.ofReal σ.trace.re)) x initR)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (totalWeight_calls_le x (clsCalls_prefixR hperm hsign pol p v)) zero_le
  · rcases i with ((i | c) | c) | T
    · exact zero_le
    · rcases c with ⟨z, u⟩ | ⟨y, u⟩ | ⟨y, u⟩
      · exact zero_le
      · show ENNReal.ofReal (∑ s, cwFresh anyHp p.perm y s * (σ s s).re) ≤
          ENNReal.ofReal (cwFreshEps G) * ENNReal.ofReal σ.trace.re
        rw [← ENNReal.ofReal_mul (cwFreshEps_nonneg G)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Matrix.trace, Complex.re_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun s _ ↦ ?_
        have hre : 0 ≤ (σ s s).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
        by_cases h0 : σ s s = 0
        · exact le_of_eq_of_le (by rw [h0, Complex.zero_re, mul_zero])
            (mul_nonneg (cwFreshEps_nonneg G) hre)
        · have hb1 := (hok.1 s s h0).1
          have hb2 := (hok.2 s s h0).1
          simp only [Set.mem_Iic, zero_add] at hb1 hb2
          exact mul_le_mul_of_nonneg_right (cwFresh_le_eps p.perm y s hb1 hb2) hre
      · exact zero_le
    · exact zero_le
    · exact zero_le

/-- **The codeword-recorded mass at one datum**: the fresh parts, the programs of trial blocks and
the reveal charges. -/
theorem cwRecPre_le_rev (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s) :
    cwRecPre pol A p v ≤ ENNReal.ofReal (cwFreshEps (6 * q + clsCap)) * clsCap +
      (runtimeR m0R).totalWeight .instruments (cwProgW p.seed) (prefixR pol A p v) initR +
      (runtimeR m0R).totalWeight .instruments (cwRevW p.seed v) (prefixR pol A p v) initR := by
  refine (cwRecPre_le_charge pol A p v).trans ?_
  refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := fun i σ ↦ cwFreshW p.perm i σ + cwProgW p.seed i σ + cwRevW p.seed v i σ)
    (fun i σ _ ↦ cwCharge_le _ _ v i σ) _ initR_posSemidef).trans ?_
  refine le_of_eq_of_le ((totalWeight_add_weight (runtimeR m0R) .instruments
    (fun i σ ↦ cwFreshW p.perm i σ + cwProgW p.seed i σ) (cwRevW p.seed v) _ initR).trans
    (congrArg (· + _) (totalWeight_add_weight (runtimeR m0R) .instruments (cwFreshW p.perm)
      (cwProgW p.seed) _ initR))) ?_
  exact add_le_add (add_le_add (totalWeight_cwFreshW_le hperm hsign pol p v) le_rfl) le_rfl

end freshRun

end Quantum.Sphincs.Assembly

end
