module

public import Qrom.Sphincs.Game
public import Qrom.Presample
public import FORS.GraphView.Signer

@[expose] public section

/-!
# The honest positions of leanSPHINCS

Every input that key generation and the signer of any message hash, on any hash, is the input at a
position (`Qrom.Sphincs.Key`) computed from the values at earlier positions (`Qrom.Sphincs.input`):
`PK.seed` and `SK.prf`, every one-time and FORS secret, every node of the canonical graph (the
positions of `FORS.Security.Position`), every encoding counter of every one-time key on its honest
message, and the randomizer and the digest calls of every message. The values at the positions are
the data `h`; the honest structure is read from it (`Qrom.Sphincs.dataOf`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- A position of the honest computation. -/
inductive Key where
  | pkSeed
  | prf
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
  | fts (index : Index) (κ : FTree) (leaf : FLeaf)
  | pos (p : Position)
  | enc (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (counter : Counter)
  | rnd (m : Message)
  | dig (m : Message) (call : DigestCall)
deriving DecidableEq

/-- The positions as a sum of finite types. -/
def Key.equiv : Key ≃ Unit ⊕ Unit ⊕ (Layer × TreeIndex × LeafIndex × ChainIndex) ⊕
    (Index × FTree × FLeaf) ⊕ Position ⊕ (Layer × TreeIndex × LeafIndex × Counter) ⊕ Message ⊕
    (Message × DigestCall) where
  toFun
    | .pkSeed => .inl ()
    | .prf => .inr (.inl ())
    | .ots a b c d => .inr (.inr (.inl (a, b, c, d)))
    | .fts a b c => .inr (.inr (.inr (.inl (a, b, c))))
    | .pos p => .inr (.inr (.inr (.inr (.inl p))))
    | .enc a b c d => .inr (.inr (.inr (.inr (.inr (.inl (a, b, c, d))))))
    | .rnd m => .inr (.inr (.inr (.inr (.inr (.inr (.inl m))))))
    | .dig m c => .inr (.inr (.inr (.inr (.inr (.inr (.inr (m, c)))))))
  invFun
    | .inl () => .pkSeed
    | .inr (.inl ()) => .prf
    | .inr (.inr (.inl (a, b, c, d))) => .ots a b c d
    | .inr (.inr (.inr (.inl (a, b, c)))) => .fts a b c
    | .inr (.inr (.inr (.inr (.inl p)))) => .pos p
    | .inr (.inr (.inr (.inr (.inr (.inl (a, b, c, d)))))) => .enc a b c d
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl m)))))) => .rnd m
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (m, c))))))) => .dig m c
  left_inv k := by cases k <;> rfl
  right_inv x := by
    rcases x with ⟨⟩ | ⟨⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ | _ | ⟨_, _, _, _⟩ | _ | ⟨_, _⟩ <;> rfl

instance : Fintype Key := Fintype.ofEquiv _ Key.equiv.symm

/-! ## The honest values read from the data -/

variable (h : Key → HashOutput)

/-- `PK.seed`. -/
def param : PublicParameter := truncateHash (h .pkSeed)

/-- The one-time secrets. -/
def otsS : Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leaf c ↦ truncateHash (h (.ots lay tree leaf c))

/-- The FORS secrets. -/
def ftsS : ForsSecrets := fun index κ leaf ↦ truncateHash (h (.fts index κ leaf))

/-- The labels of the canonical graph. -/
def labelsOf : CanonicalGraphLabels := fun p ↦ h (.pos p)

/-- The public structure: the roots, paths and FORS keys. -/
def dataOf : PublicData := publicData (labelsOf h) fun _ ↦ 0

/-- The randomizer of a message. -/
def rndOf (m : Message) : Randomness := truncateHash (h (.rnd m))

/-! ## The inputs -/

/-- The input hashed at a position, from `SK.seed` and the values at earlier positions. -/
def input (seed : MasterSeed) : Key → HashInput
  | .pkSeed => keySeedInput seed 0
  | .prf => keySeedInput seed 1
  | .ots lay tree leaf c => keygenHashInput (param h) (.ots lay tree leaf c) seed
  | .fts index κ leaf => keygenHashInput (param h) (.fors index κ leaf) seed
  | .pos p => canonicalGraphInput (param h) (otsS h) (ftsS h) p (labelsOf h)
  | .enc lay tree leaf c => tweakableHashInput (param h) (.encoding lay tree leaf)
      ((dataOf h).keyMessage lay tree leaf ++ bytesBE 4 c)
  | .rnd m => randomizerHashInput (h .prf) (param h) m
  | .dig m call => messageDigestInput (param h) (dataOf h).root m (rndOf h m) call

/-! ## Lengths -/

theorem children_length_le (p : Position) : p.children.length ≤ 64 := by
  have hk := Params.forsTrees_le
  cases p with
  | leaf => exact le_of_eq (List.length_ofFn (f := fun chainIdx : ChainIndex ↦ _))
  | froots => simpa [Position.children] using hk
  | _ => simp only [Position.children]; (try split) <;> (try split) <;> simp

theorem canonicalGraphSlots_length_le (o : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (f : ForsSecrets) (labels : CanonicalGraphLabels) (p : Position) :
    (canonicalGraphSlots o f labels p).length ≤ 64 := by
  cases p <;> simp only [canonicalGraphSlots] <;> (try split) <;>
    simp only [List.length_map, List.length_singleton] <;>
    first | omega | exact children_length_le _

theorem flatMap_bytesLE_length (l : List (BitVec (8 * 16))) :
    (l.flatMap (bytesLE 16)).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, bytesLE_length, List.length_cons]
    ring

theorem input_length_le (seed : MasterSeed) (k : Key) : (input h seed k).length ≤ maxLen := by
  unfold maxLen
  cases k with
  | pkSeed => rw [input, keySeedInput_length]; omega
  | prf => rw [input, keySeedInput_length]; omega
  | ots => rw [input, keygenHashInput_length]; omega
  | fts => rw [input, keygenHashInput_length]; omega
  | pos p =>
    rw [input, canonicalGraphInput, tweakableHashInput_length]
    have hl : (List.flatMap (bytesLE 16) (canonicalGraphSlots (otsS h) (ftsS h) (labelsOf h) p)).length =
        16 * (canonicalGraphSlots (otsS h) (ftsS h) (labelsOf h) p).length :=
      flatMap_bytesLE_length _
    have := canonicalGraphSlots_length_le (otsS h) (ftsS h) (labelsOf h) p
    omega
  | enc lay tree leaf c =>
    have h4 : (bytesBE 4 c).length = 4 := bytesBE_length 4 c
    rw [input, tweakableHashInput_length, List.length_append, h4]
    have : ((dataOf h).keyMessage lay tree leaf).length = 16 := by
      unfold PublicData.keyMessage
      split <;> exact rootPayload_length _
    omega
  | rnd => rw [input, randomizerHashInput_length]; omega
  | dig => rw [input, messageDigestInput_length]; omega

/-- The input at a position, in the finite domain. -/
def pt (seed : MasterSeed) (k : Key) : Input := ⟨input h seed k, input_length_le h seed k⟩

/-! ## The order of the positions -/

/-- A bound on the depth of the canonical graph. -/
def maxDepth : ℕ := chainLength + 1 + maxLayerHeight + forsHeight + 1

theorem depth_le (p : Position) : p.depth ≤ maxDepth := by
  unfold maxDepth
  cases p with
  | chain _ _ _ _ step => simp only [Position.depth]; have := step.isLt; omega
  | leaf => simp only [Position.depth]; omega
  | node _ _ level _ => simp only [Position.depth]; have := level.isLt; omega
  | fleaf => simp only [Position.depth]; omega
  | fnode _ _ level _ => simp only [Position.depth]; have := level.isLt; omega
  | froots => simp only [Position.depth]; omega

/-- The rank of a position: every input reads values of positions of lower rank. -/
def rank : Key → ℕ
  | .pkSeed => 0
  | .prf => 0
  | .ots .. => 1
  | .fts .. => 1
  | .rnd _ => 1
  | .pos p => 2 + p.depth
  | .enc .. => 3 + maxDepth
  | .dig .. => 3 + maxDepth

/-- The positions ordered by rank, then by an enumeration. -/
instance : LinearOrder Key :=
  LinearOrder.lift' (fun k ↦ toLex (rank k, (Fintype.equivFin Key k : ℕ))) fun a b hab ↦ by
    have := congrArg (fun x ↦ (ofLex x).2) hab
    exact (Fintype.equivFin Key).injective (Fin.ext this)

theorem lt_of_rank_lt {a b : Key} (h : rank a < rank b) : a < b := by
  change toLex (rank a, (Fintype.equivFin Key a : ℕ)) < toLex (rank b, (Fintype.equivFin Key b : ℕ))
  exact Prod.Lex.lt_iff.mpr (Or.inl h)

/-- The input at a position reads only the values at positions of lower rank. -/
theorem input_congr (seed : MasterSeed) (k : Key) {h h' : Key → HashOutput}
    (H : ∀ k', rank k' < rank k → h k' = h' k') : input h seed k = input h' seed k := by
  have hp : 0 < rank k → param h = param h' := fun hk ↦ congrArg truncateHash (H .pkSeed hk)
  have hlab : 2 + maxDepth < rank k → labelsOf h = labelsOf h' := fun hk ↦ funext fun q ↦
    H (.pos q) (by have := depth_le q; show 2 + q.depth < rank k; omega)
  cases k with
  | pkSeed => rfl
  | prf => rfl
  | ots => simp only [input, hp (by simp [rank])]
  | fts => simp only [input, hp (by simp [rank])]
  | rnd m => simp only [input, hp (by simp [rank]), H .prf (by simp [rank])]
  | pos p =>
    have hots : otsS h = otsS h' := funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ funext fun _ ↦
      congrArg truncateHash (H (.ots _ _ _ _) (by simp only [rank]; omega))
    have hfts : ftsS h = ftsS h' := funext fun _ ↦ funext fun _ ↦ funext fun _ ↦
      congrArg truncateHash (H (.fts _ _ _) (by simp only [rank]; omega))
    simp only [input, hp (by simp [rank]), hots, hfts]
    exact canonicalGraphInput_congr _ _ _ p _ _ fun c hc ↦ congrArg truncateHash
      (H (.pos c) (by simp only [rank]; have := Position.depth_lt_of_mem_children hc; omega))
  | enc =>
    simp only [input, dataOf, hp (by simp [rank]), hlab (by simp [rank])]
  | dig m call =>
    have hr : rndOf h m = rndOf h' m :=
      congrArg truncateHash (H (.rnd m) (by simp only [rank]; omega))
    simp only [input, dataOf, hp (by simp [rank]), hlab (by simp [rank]), hr]

/-! ## Distinct positions read distinct inputs -/

section lengths

variable (seed : MasterSeed)

theorem length_input_pkSeed : (input h seed .pkSeed).length = 44 := keySeedInput_length _ _
theorem length_input_prf : (input h seed .prf).length = 44 := keySeedInput_length _ _
theorem length_input_ots (a b c d) : (input h seed (.ots a b c d)).length = 80 :=
  keygenHashInput_length _ _ _
theorem length_input_fts (a b c) : (input h seed (.fts a b c)).length = 80 :=
  keygenHashInput_length _ _ _
theorem length_input_pos (p : Position) : (input h seed (.pos p)).length =
    48 + 16 * (canonicalGraphSlots (otsS h) (ftsS h) (labelsOf h) p).length := by
  rw [input, canonicalGraphInput, tweakableHashInput_length]
  have hl : (List.flatMap (bytesLE 16) (canonicalGraphSlots (otsS h) (ftsS h) (labelsOf h) p)).length =
      16 * (canonicalGraphSlots (otsS h) (ftsS h) (labelsOf h) p).length :=
    flatMap_bytesLE_length _
  omega
theorem length_input_enc (a b c d) : (input h seed (.enc a b c d)).length = 68 := by
  have h4 : (bytesBE 4 d).length = 4 := bytesBE_length 4 d
  rw [input, tweakableHashInput_length, List.length_append, h4]
  have : ((dataOf h).keyMessage a b c).length = 16 := by
    unfold PublicData.keyMessage
    split <;> exact rootPayload_length _
  omega
theorem length_input_rnd (m) : (input h seed (.rnd m)).length = 93 := randomizerHashInput_length _ _ _
theorem length_input_dig (m c) : (input h seed (.dig m c)).length = 84 :=
  messageDigestInput_length _ _ _ _ _

end lengths

theorem input_injective (seed : MasterSeed) : Function.Injective (input h seed) := by
  intro k k' heq
  have hlen := congrArg List.length heq
  cases k <;> cases k' <;>
    simp only [length_input_pkSeed, length_input_prf, length_input_ots, length_input_fts,
      length_input_pos, length_input_enc, length_input_rnd, length_input_dig] at hlen <;>
    (try (exfalso; omega)) <;> simp only [input] at heq
  case pkSeed.pkSeed => rfl
  case prf.prf => rfl
  case pkSeed.prf => exact absurd (keySeedInput_injective (by norm_num) (by norm_num) heq).2 (by norm_num)
  case prf.pkSeed => exact absurd (keySeedInput_injective (by norm_num) (by norm_num) heq).2 (by norm_num)
  case ots.ots => obtain ⟨-, hd, -⟩ := keygenInput_injective heq; cases hd; rfl
  case ots.fts => obtain ⟨-, hd, -⟩ := keygenInput_injective heq; cases hd
  case fts.ots => obtain ⟨-, hd, -⟩ := keygenInput_injective heq; cases hd
  case fts.fts => obtain ⟨-, hd, -⟩ := keygenInput_injective heq; cases hd; rfl
  case ots.pos => exact absurd heq (keygenInput_ne_hashInput _ _ _ _ _ _)
  case fts.pos => exact absurd heq (keygenInput_ne_hashInput _ _ _ _ _ _)
  case pos.ots => exact absurd heq.symm (keygenInput_ne_hashInput _ _ _ _ _ _)
  case pos.fts => exact absurd heq.symm (keygenInput_ne_hashInput _ _ _ _ _ _)
  case pos.pos p q =>
    by_cases hne : p = q
    · rw [hne]
    · exact absurd heq (Position.input_separated _ hne _ _)
  case enc.enc a b c d a' b' c' d' =>
    obtain ⟨hf, -, hpay⟩ := tweakableInput_injective heq
    have hd := hashFields_injective (left := .encoding a b c) (right := .encoding a' b' c') trivial
      trivial hf
    cases hd
    have hc := bytesBE_injective (List.append_cancel_left hpay)
    rw [hc]
  case rnd.rnd => obtain ⟨-, -, hm⟩ := randomizerHashInput_injective heq; rw [hm]
  case dig.dig => obtain ⟨-, -, hm, -, hc⟩ := messageDigestInput_injective heq; rw [hm, hc]

/-- **The honest computation as a presampling procedure**, for `SK.seed`. -/
def proc (seed : MasterSeed) : Procedure Input HashOutput Key where
  pt h k := pt h seed k
  causal _ _ k hk := Subtype.ext (input_congr seed k fun k' hr ↦ hk k' (lt_of_rank_lt hr))
  distinct h _ _ hkk := input_injective h seed (congrArg Subtype.val hkk)

end Qrom.Sphincs
