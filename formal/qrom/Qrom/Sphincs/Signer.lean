module

public import Qrom.Sphincs.Reveal

@[expose] public section

/-!
# The signature read from the data

The signature of a message, on the hash that answers the honest positions with the data `h`, is an
explicit function of `h` (`Qrom.Sphincs.signH_eq`): the randomizer, the digest, the first valid
encoding counter of every layer's key, and the coordinates and labels it opens. It reads `h` only
at the keys `keysRead h m` (`Qrom.Sphincs.signExpl_local`), a set itself read on those keys
(`Qrom.Sphincs.keysRead_local`): the randomizer, the digest calls, every encoding counter of the
keys on the path, the opened FORS secrets, every label of the FORS trees and of the trees on the
path, and the chain coordinates the signature opens.
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Qrom.Sphincs

variable [Params] (h : Key → HashOutput)

/-- The first valid encoding counter of a key, read from the data. -/
def encH (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : ℕ → ℕ → Option (Counter × Encoding)
  | 0, _ => none
  | n + 1, c =>
    match TargetSum.decodeDigest (truncateHash (h (.enc lay tree leaf (BitVec.ofNat counterBits c)))) with
    | some w => some (BitVec.ofNat counterBits c, w)
    | none => encH lay tree leaf n (c + 1)

/-- The digest of a message, read from the data. -/
def digestH (m : Message) : MessageDigest := truncateMessageDigest fun call ↦ h (.dig m call)

/-- The signature of a message, read from the data. -/
def signExpl (m : Message) : Option Signature :=
  (Completeness.allSome fun lay ↦ encH h lay (treeIndexAt (digestIndex (digestH h m)) lay)
      (leafIndexAt (digestIndex (digestH h m)) lay) encodingAttemptLimit 0).map fun found ↦
    ⟨rndOf h m, assembledFors (dataOf h) (tableOf h) (digestIndex (digestH h m))
      (digestLeaves (digestH h m)),
      layerSignatures (dataOf h) (digestIndex (digestH h m)) found
        (assembledValues (tableOf h) (digestIndex (digestH h m)) found)⟩

variable (seed : MasterSeed)

theorem firstEncoding_ovFun (G : Input → HashOutput) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) : ∀ n c, Prefix.firstEncoding (QueryImpl.ofFn (ovFun seed h G)) (param h) lay
      tree leaf ((dataOf h).keyMessage lay tree leaf) n c = encH h lay tree leaf n c := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    have hv := ovFun_input seed h G (.enc lay tree leaf (BitVec.ofNat counterBits c))
    simp only [input] at hv
    simp only [Prefix.firstEncoding, encH, encode, evalWithAnswerFn_bind,
      Completeness.eval_tweakableHash, evalWithAnswerFn_pure, QueryImpl.ofFn_apply, hv, ih]
    cases TargetSum.decodeDigest (truncateHash (h (Key.enc lay tree leaf
      (BitVec.ofNat counterBits c)))) <;> rfl

theorem digest_ovFun (G : Input → HashOutput) (m : Message) :
    evalWithAnswerFn (QueryImpl.ofFn (ovFun seed h G))
      (messageDigest (param h) (dataOf h).root m (rndOf h m) : OracleComp HashSpec MessageDigest) =
      digestH h m := by
  have hv : ∀ call, ovFun seed h G (messageDigestInput (param h) (dataOf h).root m (rndOf h m) call) =
      h (.dig m call) := fun call ↦ ovFun_input seed h G (.dig m call)
  simp only [messageDigest, messageDigestCall, evalWithAnswerFn_bind, Completeness.eval_sequenceFin,
    Completeness.eval_oracleHash, evalWithAnswerFn_pure, QueryImpl.ofFn_apply, hv, digestH]

theorem signH_eq (m : Message) : signH seed h m = signExpl h m := by
  unfold signH assembled assembledEncodings signExpl
  rw [digest_ovFun]
  simp only [firstEncoding_ovFun]

/-! ## The keys a signature reads -/

/-- A position of the FORS trees of instance `index`. -/
def forsAt (index : Index) : Position → Prop
  | .fleaf i _ _ => i = index
  | .fnode i _ _ _ => i = index
  | .froots i => i = index
  | _ => False

/-- A position of a tree on the path of `index`: its leaves and nodes. -/
def treeAt (index : Index) : Position → Prop
  | .leaf lay tree _ => tree = treeIndexAt index lay
  | .node lay tree _ _ => tree = treeIndexAt index lay
  | _ => False

theorem digit_sub_lt (digit : Digit) : digit.val - 1 < chainLength - 1 := by
  have h4 : chainLength = 4 := rfl
  have : digit.val < chainLength := digit.isLt
  omega

/-- The key of the chain coordinate `digit` of a chain: the secret, or the step below it. -/
def chainKey (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (digit : Digit) :
    Option Key :=
  if digit.val = 0 then some (.ots lay tree leaf chain) else
    some (.pos (.chain lay tree leaf chain ⟨digit.val - 1, digit_sub_lt digit⟩))

/-- The chain coordinates a signature opens. -/
def chainKeys (m : Message) : Finset (Option Key) :=
  match Completeness.allSome fun lay ↦ encH h lay (treeIndexAt (digestIndex (digestH h m)) lay)
      (leafIndexAt (digestIndex (digestH h m)) lay) encodingAttemptLimit 0 with
  | none => ∅
  | some found => Finset.univ.image fun x : Layer × ChainIndex ↦
      chainKey x.1 (treeIndexAt (digestIndex (digestH h m)) x.1)
        (leafIndexAt (digestIndex (digestH h m)) x.1) x.2 ((found x.1).2 x.2)

open Classical in
/-- The keys the signature of `m` reads. -/
def keysRead (m : Message) : Finset (Option Key) :=
  insert (some (.rnd m)) (
    (Finset.univ.image fun call ↦ some (.dig m call)) ∪
    (Finset.univ.image fun x : Layer × Counter ↦ some (.enc x.1
      (treeIndexAt (digestIndex (digestH h m)) x.1) (leafIndexAt (digestIndex (digestH h m)) x.1) x.2)) ∪
    (Finset.univ.image fun κ ↦ some (.fts (digestIndex (digestH h m)) κ (digestLeaves (digestH h m) κ))) ∪
    (Finset.univ.image fun p : {p : Position // forsAt (digestIndex (digestH h m)) p ∨
      treeAt (digestIndex (digestH h m)) p} ↦ some (.pos p.1)) ∪
    chainKeys h m)

theorem encH_congr {h h' : Key → HashOutput} (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (H : ∀ c, h (.enc lay tree leaf c) = h' (.enc lay tree leaf c)) :
    ∀ n c, encH h lay tree leaf n c = encH h' lay tree leaf n c := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih => intro c; simp only [encH, H, ih]

theorem forsAt_forsPosition (index : Index) (κ : FTree) :
    ∀ l hl nd, forsAt index (forsPosition index κ l hl nd)
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem treeAt_treePosition (index : Index) (lay : Layer) :
    ∀ l hl idx, treeAt index (treePosition lay (treeIndexAt index lay) l hl idx)
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem forsPath_congr {h h' : Key → HashOutput} (index : Index)
    (H : ∀ p, forsAt index p → h (.pos p) = h' (.pos p)) (κ : FTree) (leaf : FLeaf) :
    (dataOf h).forsPath index κ leaf = (dataOf h').forsPath index κ leaf := by
  funext level
  simp only [dataOf, publicData, labelsOf]
  congr 1
  exact H _ (forsAt_forsPosition _ _ _ _ _)

theorem treePath_congr {h h' : Key → HashOutput} (index : Index)
    (H : ∀ p, treeAt index p → h (.pos p) = h' (.pos p)) (lay : Layer) :
    (dataOf h).treePath lay (treeIndexAt index lay) (leafIndexAt index lay) =
      (dataOf h').treePath lay (treeIndexAt index lay) (leafIndexAt index lay) := by
  funext level
  simp only [dataOf, publicData, labelsOf]
  congr 1
  exact H _ (treeAt_treePosition _ _ _ _ _)

/-- **The signature reads only its keys**, and those keys are read on themselves. -/
theorem signExpl_local {h h' : Key → HashOutput} {m : Message}
    (H : ∀ k, some k ∈ keysRead h m → h k = h' k) :
    signExpl h' m = signExpl h m ∧ keysRead h' m = keysRead h m := by
  have hdig : digestH h' m = digestH h m := by
    unfold digestH
    congr 1
    funext call
    exact (H _ (by simp [keysRead])).symm
  have hrnd : rndOf h' m = rndOf h m := congrArg truncateHash (H _ (by simp [keysRead])).symm
  set index := digestIndex (digestH h m) with hindex
  set leaves := digestLeaves (digestH h m) with hleaves
  have henc : ∀ lay, encH h' lay (treeIndexAt index lay) (leafIndexAt index lay) encodingAttemptLimit 0 =
      encH h lay (treeIndexAt index lay) (leafIndexAt index lay) encodingAttemptLimit 0 := fun lay ↦
    (encH_congr _ _ _ (fun c ↦ H _ (by simp [keysRead, ← hindex])) _ _).symm
  have hall : Completeness.allSome (fun lay ↦ encH h' lay (treeIndexAt index lay)
      (leafIndexAt index lay) encodingAttemptLimit 0) = Completeness.allSome (fun lay ↦ encH h lay
      (treeIndexAt index lay) (leafIndexAt index lay) encodingAttemptLimit 0) := by
    simp only [henc]
  have hfors : assembledFors (dataOf h') (tableOf h') index leaves =
      assembledFors (dataOf h) (tableOf h) index leaves := by
    funext κ
    simp only [assembledFors]
    rw [forsPath_congr index (fun p hp ↦ (H _ (by simp [keysRead, ← hindex, hp])).symm)]
    congr 1
    exact congrArg truncateHash (H _ (by simp [keysRead, ← hindex, ← hleaves])).symm
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
      rw [treePath_congr index (fun p hp ↦ (H _ (by simp [keysRead, ← hindex, hp])).symm)]
      congr 1
      funext chain
      simp only [assembledValues, tableOf, HiddenGraph.coordinates]
      have hk : chainKey lay (treeIndexAt index lay) (leafIndexAt index lay) chain
          ((found lay).2 chain) ∈ keysRead h m := by
        refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
        unfold chainKeys
        rw [← hindex, hres]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ (lay, chain))
      unfold chainKey at hk
      split_ifs at hk ⊢ with hz
      · exact congrArg truncateHash (H _ hk).symm
      · exact congrArg truncateHash (H _ hk).symm
  · unfold keysRead chainKeys
    rw [hdig, ← hindex, ← hleaves, hall]

end Qrom.Sphincs
