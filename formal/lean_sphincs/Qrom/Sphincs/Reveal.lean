module

public import Qrom.Sphincs.Presampled

@[expose] public section

/-!
# What each honest input reads

The input at a position reads the data at the keys `deps k` and nothing else
(`Qrom.Sphincs.input_dep`), and holds at least the 128 low bits of the value at each of them
(`Qrom.Sphincs.input_embed`): two data giving the same input agree there. Different positions have
different inputs, on any two data (`Qrom.Sphincs.input_cross_injective`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Qrom.Sphincs

variable [Params]

/-! ## The positions of the public structure -/

/-- The position whose label is the root of the top tree. -/
def topRootPos : Position :=
  treePosition topLayer rootTree (layerHeight topLayer) (layerHeight_le _) ⟨0, Nat.two_pow_pos _⟩

/-- The position whose label is the message of the one-time key at leaf `leaf` of tree `tree` of
layer `lay`: the root of the tree below, or the FORS public key at the bottom layer. -/
def keyMsgPos (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Position :=
  if hbelow : lay.val + 1 < numLayers then
    treePosition ⟨lay.val + 1, hbelow⟩ (childTree lay tree leaf) (layerHeight ⟨lay.val + 1, hbelow⟩)
      (layerHeight_le _) ⟨0, Nat.two_pow_pos _⟩
  else .froots (childTree lay tree leaf)

theorem dataOf_root (h : Key → HashOutput) : (dataOf h).root = truncateHash (h (.pos topRootPos)) :=
  rfl

theorem dataOf_keyMessage (h : Key → HashOutput) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    (dataOf h).keyMessage lay tree leaf = rootPayload (truncateHash (h (.pos (keyMsgPos lay tree leaf)))) := by
  unfold PublicData.keyMessage keyMsgPos
  split <;> rfl

/-! ## The keys an input reads -/

/-- The secret a position's payload starts from, if any. -/
def secretDep : Position → Finset (Option Key)
  | .chain lay tree leaf chain step => if step.val = 0 then {some (.ots lay tree leaf chain)} else ∅
  | .fleaf index κ leaf => {some (.fts index κ leaf)}
  | _ => ∅

/-- The data keys the input at a position reads: `none` is `SK.seed`. -/
def deps : Key → Finset (Option Key)
  | .pkSeed => {none}
  | .prf => {none}
  | .ots .. => {none, some .pkSeed}
  | .fts .. => {none, some .pkSeed}
  | .pos p => insert (some .pkSeed) (secretDep p ∪ (p.children.map fun c ↦ some (.pos c)).toFinset)
  | .enc lay tree leaf _ => {some .pkSeed, some (.pos (keyMsgPos lay tree leaf))}
  | .rnd _ => {some .pkSeed, some .prf}
  | .dig m _ => {some .pkSeed, some (.pos topRootPos), some (.rnd m)}

/-- The honest values of the data. -/
abbrev hOf (d : Data) : Key → HashOutput := fun k ↦ d (some k)

/-- The input at a position on the data `d`. -/
abbrev inputD (d : Data) (k : Key) : HashInput := input (hOf d) (d none) k

theorem canonicalGraphSlots_congr (p : Position)
    {o o' : Layer → TreeIndex → LeafIndex → ChainIndex → Digest} {f f' : ForsSecrets}
    {l l' : CanonicalGraphLabels}
    (ho : ∀ lay tree leaf chain step, p = .chain lay tree leaf chain step → step.val = 0 →
      o lay tree leaf chain = o' lay tree leaf chain)
    (hf : ∀ index κ leaf, p = .fleaf index κ leaf → f index κ leaf = f' index κ leaf)
    (hl : ∀ c ∈ p.children, truncateHash (l c) = truncateHash (l' c)) :
    canonicalGraphSlots o f l p = canonicalGraphSlots o' f' l' p := by
  have hmap : p.children.map (fun c ↦ truncateHash (l c)) =
      p.children.map (fun c ↦ truncateHash (l' c)) := List.map_congr_left hl
  cases p with
  | chain lay tree leaf chain step =>
    simp only [canonicalGraphSlots]
    split_ifs with hs
    · rw [ho lay tree leaf chain step rfl hs]
    · exact hmap
  | fleaf index κ leaf =>
    simp only [canonicalGraphSlots]
    rw [hf index κ leaf rfl]
  | _ => exact hmap

theorem input_dep (k : Key) {d d' : Data} (H : ∀ q ∈ deps k, d q = d' q) :
    inputD d k = inputD d' k := by
  have hp : some Key.pkSeed ∈ deps k → param (hOf d) = param (hOf d') :=
    fun hm ↦ congrArg truncateHash (H _ hm)
  cases k with
  | pkSeed => simp only [inputD, input, H none (by simp [deps])]
  | prf => simp only [inputD, input, H none (by simp [deps])]
  | ots => simp only [inputD, input, H none (by simp [deps]), hp (by simp [deps])]
  | fts => simp only [inputD, input, H none (by simp [deps]), hp (by simp [deps])]
  | rnd m =>
    simp only [inputD, input, hp (by simp [deps])]
    rw [show hOf d .prf = hOf d' .prf from H _ (by simp [deps])]
  | dig m call =>
    simp only [inputD, input, hp (by simp [deps]), dataOf_root, rndOf]
    rw [show hOf d (.pos topRootPos) = hOf d' (.pos topRootPos) from H _ (by simp [deps]),
      show hOf d (.rnd m) = hOf d' (.rnd m) from H _ (by simp [deps])]
  | enc lay tree leaf c =>
    simp only [inputD, input, hp (by simp [deps]), dataOf_keyMessage]
    rw [show hOf d (.pos (keyMsgPos lay tree leaf)) = hOf d' (.pos (keyMsgPos lay tree leaf)) from
      H _ (by simp [deps])]
  | pos p =>
    simp only [inputD, input, canonicalGraphInput, hp (by simp [deps])]
    rw [show canonicalGraphSlots (otsS (hOf d)) (ftsS (hOf d)) (labelsOf (hOf d)) p =
        canonicalGraphSlots (otsS (hOf d')) (ftsS (hOf d')) (labelsOf (hOf d')) p from
      canonicalGraphSlots_congr p
      (fun lay tree leaf chain step hpe hs ↦ congrArg truncateHash (H _ (by
        subst hpe; simp [deps, secretDep, hs])))
      (fun index κ leaf hpe ↦ congrArg truncateHash (H _ (by subst hpe; simp [deps, secretDep])))
      (fun c hc ↦ congrArg truncateHash (H _ (by simp [deps, hc])))]

/-! ## Distinct positions, on any data -/

theorem input_cross_injective {d d' : Data} {k k' : Key} (heq : inputD d k = inputD d' k') :
    k = k' := by
  have hlen := congrArg List.length heq
  cases k <;> cases k' <;>
    simp only [inputD, length_input_pkSeed, length_input_prf, length_input_ots, length_input_fts,
      length_input_pos, length_input_enc, length_input_rnd, length_input_dig] at hlen <;>
    (try (exfalso; omega)) <;> simp only [inputD, input] at heq
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
    obtain ⟨hf, -, -⟩ := tweakableInput_injective heq
    rw [Position.fields_injective hf]
  case enc.enc a b c e a' b' c' e' =>
    obtain ⟨hf, -, hpay⟩ := tweakableInput_injective heq
    have hd := hashFields_injective (left := .encoding a b c) (right := .encoding a' b' c') trivial
      trivial hf
    cases hd
    have hl : ((dataOf (hOf d)).keyMessage a b c).length =
        ((dataOf (hOf d')).keyMessage a b c).length := by
      rw [dataOf_keyMessage, dataOf_keyMessage, rootPayload_length, rootPayload_length]
    have hc := bytesBE_injective (List.append_inj hpay hl).2
    rw [hc]
  case rnd.rnd => obtain ⟨-, -, hm⟩ := randomizerHashInput_injective heq; rw [hm]
  case dig.dig => obtain ⟨-, -, hm, -, hc⟩ := messageDigestInput_injective heq; rw [hm, hc]

/-! ## The input holds the values it reads -/

theorem flatMap_bytesLE16_inj {l l' : List (BitVec (8 * 16))} (hlen : l.length = l'.length)
    (h : l.flatMap (bytesLE 16) = l'.flatMap (bytesLE 16)) : l = l' := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a l ih => cases l' with
    | nil => simp at hlen
    | cons b l' =>
      simp only [List.flatMap_cons] at h
      obtain ⟨hab, htl⟩ := List.append_inj h (by rw [bytesLE_length, bytesLE_length])
      rw [bytesLE_injective hab, ih (by simpa using hlen) htl]

theorem slots_length (p : Position) (o o' : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (f f' : ForsSecrets) (l l' : CanonicalGraphLabels) :
    (canonicalGraphSlots o f l p).length = (canonicalGraphSlots o' f' l' p).length := by
  cases p <;> simp only [canonicalGraphSlots] <;> (try split_ifs) <;> simp

theorem input_embed {d d' : Data} {k : Key} (heq : inputD d k = inputD d' k) :
    ∀ q ∈ deps k, truncateHash (d q) = truncateHash (d' q) := by
  intro q hq
  cases k with
  | pkSeed =>
    simp only [deps, Finset.mem_singleton] at hq
    subst hq
    rw [(keySeedInput_injective (by norm_num) (by norm_num) heq).1]
  | prf =>
    simp only [deps, Finset.mem_singleton] at hq
    subst hq
    rw [(keySeedInput_injective (by norm_num) (by norm_num) heq).1]
  | ots =>
    obtain ⟨hp, -, hs⟩ := keygenInput_injective heq
    simp only [deps, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · rw [hs]
    · exact hp
  | fts =>
    obtain ⟨hp, -, hs⟩ := keygenInput_injective heq
    simp only [deps, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · rw [hs]
    · exact hp
  | rnd m =>
    obtain ⟨hprf, hp, -⟩ := randomizerHashInput_injective heq
    simp only [deps, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hp
    · exact congrArg truncateHash hprf
  | dig m call =>
    obtain ⟨hp, hroot, -, hR, -⟩ := messageDigestInput_injective heq
    simp only [deps, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hp
    · exact hroot
    · exact hR
  | enc lay tree leaf c =>
    obtain ⟨-, hp, hpay⟩ := tweakableInput_injective heq
    simp only [deps, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hp
    · have hl : ((dataOf (hOf d)).keyMessage lay tree leaf).length =
          ((dataOf (hOf d')).keyMessage lay tree leaf).length := by
        rw [dataOf_keyMessage, dataOf_keyMessage, rootPayload_length, rootPayload_length]
      have hm := (List.append_inj hpay hl).1
      rw [dataOf_keyMessage, dataOf_keyMessage] at hm
      exact bytesLE_injective hm
  | pos p =>
    obtain ⟨-, hp, hpay⟩ := tweakableInput_injective heq
    have hslots := flatMap_bytesLE16_inj (slots_length p _ _ _ _ _ _) hpay
    simp only [deps, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, List.mem_map] at hq
    rcases hq with rfl | hsec | ⟨c, hc, rfl⟩
    · exact hp
    · cases p with
      | chain lay tree leaf chain step =>
        simp only [secretDep] at hsec
        split_ifs at hsec with hs
        · simp only [Finset.mem_singleton] at hsec
          subst hsec
          simp only [canonicalGraphSlots, hs, ↓reduceIte, List.cons.injEq, and_true] at hslots
          exact hslots
        · simp at hsec
      | fleaf index κ leaf =>
        simp only [secretDep, Finset.mem_singleton] at hsec
        subst hsec
        simp only [canonicalGraphSlots, List.cons.injEq, and_true] at hslots
        exact hslots
      | _ => simp [secretDep] at hsec
    · have hmap : ∀ c ∈ p.children, truncateHash (labelsOf (hOf d) c) =
          truncateHash (labelsOf (hOf d') c) := by
        cases p with
        | chain lay tree leaf chain step =>
          intro c hc
          simp only [Position.children] at hc
          split_ifs at hc with hs
          · simp only [canonicalGraphSlots, show step.val ≠ 0 by omega, ↓reduceIte] at hslots
            exact List.map_inj_left.mp hslots c (by simp [Position.children, hs, hc])
          · simp at hc
        | fleaf => intro c hc; simp [Position.children] at hc
        | _ => exact List.map_inj_left.mp hslots
      exact hmap c hc

end Qrom.Sphincs
