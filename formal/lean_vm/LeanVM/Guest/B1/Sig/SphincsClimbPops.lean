/-
  LeanVM.Guest.B1.Sig.SphincsClimbPops

  The witness-stream entries of `verify_sig_lean_sphincs`'s climbs (`lean_ethereum.py:4035-4055, 4106-4125`): a FORS tree pops its secret then each level's two children (`"sp_fors_nodes"`), a path each level's two children (`"siblings"`), the node and its sibling in the order of the leaf's bit.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundFors
public import LeanVM.Guest.B1.Sig.BlockPops
public import LeanVM.Guest.B1.Sig.PopsKit

/-!
# The climbs' pops

* `pairPop`, `climbPops`: a level's entry, the levels' entries from a node;
* `pairLevel_pops`: a level whose atoms hold pops its node and its sibling in the bit's order;
* `sForsLevels_pops`, `sForsTree_pops`, `sPath_pops`: from any valuation where their atoms hold, the climbs pop `climbPops` of the nodes `soundness` computes and the hinted siblings.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The entries -/

/-- A level's entry: the node `v` and its sibling `w`, in the order of the bit. -/
def pairPop (name : String) (bt : Bool) (v w : E) : Pop := (name, [(mPair bt v w).1, (mPair bt v w).2])

/-- The entries of levels `z ..< z + m` climbed from the node `v`, the parent of `v` at `z` being `node z v`. -/
def climbPops (name : String) (node : Nat → E → E) (bt : Nat → Bool) (sib : Nat → E) :
    Nat → Nat → E → List Pop
  | 0, _, _ => []
  | m + 1, z, v => pairPop name (bt z) v (sib z) :: climbPops name node bt sib m (z + 1) (node z v)

theorem climbPops_congr (name : String) (bt : Nat → Bool) {node node' : Nat → E → E} {sib sib' : Nat → E} :
    ∀ (m z : Nat) (v : E), (∀ j, z ≤ j → j < z + m → node j = node' j ∧ sib j = sib' j) →
      climbPops name node bt sib m z v = climbPops name node' bt sib' m z v
  | 0, _, _, _ => rfl
  | m + 1, z, v, h => by
      simp only [climbPops, (h z le_rfl (by omega)).1, (h z le_rfl (by omega)).2]
      rw [climbPops_congr name bt m (z + 1) _ fun j h1 h2 => h j (by omega) (by omega)]

/-- **The levels' entries**, level by level: level `z + j`'s node is `nIter` of the levels below. -/
theorem climbPops_eq (name : String) (node : Nat → E → E) (bt : Nat → Bool) (sib : Nat → E) :
    ∀ (m z : Nat) (v : E), climbPops name node bt sib m z v =
      (List.range m).map fun j => pairPop name (bt (z + j)) (nIter node z j v) (sib (z + j))
  | 0, _, _ => rfl
  | m + 1, z, v => by
      rw [climbPops, climbPops_eq name node bt sib m (z + 1), List.range_succ_eq_map, List.map_cons,
        List.map_map]
      simp only [Nat.add_zero, nIter, Function.comp_def, show ∀ j, z + 1 + j = z + (j + 1) from
        fun j => by omega]

/-! ## Blocks of atoms -/

/-- The witness hints of a block's atoms: their streams and destinations, in order. -/
def hintsOf : List Stmt → List (String × Dest)
  | [] => []
  | .atom (.hint (.witness s d)) :: ss => (s, d) :: hintsOf ss
  | _ :: ss => hintsOf ss

/-- **A block of atoms' entries are its witness hints'**, each its destination's words. -/
theorem atomsPops_eq_hintsOf (σ : Val) : ∀ ss : List Stmt,
    atomsPops rd σ ss = (hintsOf ss).map fun p => (p.1, p.2.words rd σ)
  | [] => rfl
  | .atom (.hint (.witness s d)) :: ss => by
      simp only [atomsPops, List.flatMap_cons, hintsOf, List.map_cons] at *
      rw [← atomsPops_eq_hintsOf σ ss]
      rfl
  | .atom (.hint (.bits ..)) :: ss | .atom (.hint (.bitsExp ..)) :: ss
  | .atom (.hint (.digitsExp ..)) :: ss | .atom (.hint (.windowsExp ..)) :: ss
  | .atom (.hint (.limbs ..)) :: ss | .atom (.hint (.log2Ceil ..)) :: ss
  | .atom (.hint (.inverse ..)) :: ss | .atom (.hint (.alloc ..)) :: ss
  | .atom (.hint (.allocDyn ..)) :: ss
  | .atom (.const ..) :: ss | .atom (.add ..) :: ss | .atom (.mul ..) :: ss | .atom (.copy ..) :: ss
  | .atom (.load ..) :: ss | .atom (.assertEq ..) :: ss | .atom (.assertNe ..) :: ss
  | .atom (.rangeCheck ..) :: ss | .atom (.assertInK ..) :: ss | .atom (.keccak ..) :: ss
  | .atom (.frameAddr ..) :: ss | .atom (.touch ..) :: ss
  | .ite .. :: ss | .match_ .. :: ss | .call .. :: ss | .callIf .. :: ss | .dispatch .. :: ss
  | .ret _ :: ss => by
      simp only [atomsPops, List.flatMap_cons, hintsOf] at *
      rw [← atomsPops_eq_hintsOf σ ss]
      rfl

/-- **A block of atoms pops its witness hints' words.** -/
theorem fallPops_hintsOf (σ : Val) {ss : List Stmt} (h : atomsOnly ss = true) :
    FallPops rd σ ss ((hintsOf ss).map fun p => (p.1, p.2.words rd σ)) := by
  rw [← atomsPops_eq_hintsOf]; exact fallPops_atoms σ h

/-! ## Blocks without hints -/

theorem sAddK_quiet (a : V) (k : Nat) (w : E) (x : Nat) : quiet (sAddK a k w x).1 = true := by
  unfold sAddK; split <;> rfl

theorem sBe16_quiet (val : Nat → V) (pos n x : Nat) : quiet (sBe16 val pos n x).1 = true := by
  unfold sBe16; split <;> rfl

theorem sForsAt_quiet (a1 : V) (val : Nat → V) (c z x : Nat) : quiet (sForsAt a1 val c z x).1 = true := by
  unfold sForsAt
  split_ifs <;> simp only [quiet_append, sAddK_quiet, sBe16_quiet] <;> rfl

theorem sPathAddr_quiet (val : Nat → V) (off z m x : Nat) : quiet (sPathAddr val off z m x).1 = true := by
  unfold sPathAddr
  split
  · rfl
  · simp only [quiet_append, sBe16_quiet]; rfl

theorem kNode_quiet (pad : Nat) (pp a0 adr k0 k1 : V) (y : Nat) : quiet (kNode pad pp a0 adr k0 k1 y).1 = true :=
  rfl

/-! ## A level -/

/-- **A level pops its node and its sibling**, in the order of the bit, when `is_child` holds. -/
theorem pairLevel_pops (name : String) {cur bit : V} {x : Nat} {A K : List Stmt} (hA : quiet A = true)
    (hK : quiet K = true) (hib : IsBit (σ bit))
    (hc : AtomsHold rd σ (isChildS cur (.n x) (.n (x + 1)) bit (x + 2))) {bt : Bool}
    (hd : decide (σ bit = 1) = bt) :
    FallPops rd σ ([hintW name [.n x, .n (x + 1)]] ++ isChildS cur (.n x) (.n (x + 1)) bit (x + 2) ++ A ++ K)
      [pairPop name bt (σ cur) (siblingOf σ bit x)] := by
  have e1 : σ (.n (x + 2)) = σ cur + σ (.n x) :=
    hc.atom (a := .add (.n (x + 2)) cur (.n x)) (by simp [isChildS, addS])
  have e2 : σ (.n (x + 3)) = σ (.n x) + σ (.n (x + 1)) :=
    hc.atom (a := .add (.n (x + 3)) (.n x) (.n (x + 1))) (by simp [isChildS, addS])
  have e3 : σ (.n (x + 2)) = σ bit * σ (.n (x + 3)) :=
    hc.atom (a := .mul (.n (x + 2)) bit (.n (x + 3))) (by simp [isChildS, mulS])
  have hpair := isChild_sound hib e1 e2 e3
  rw [hd] at hpair
  have hh : FallPops rd σ [hintW name [.n x, .n (x + 1)]] [(name, [σ (.n x), σ (.n (x + 1))])] :=
    FallPops.atom _
  have s : ∀ {α : Type} (p : α), [p] ++ [] ++ [] ++ [] = [p] := by intros; simp
  refine FallPops.congr_pops (((hh.append (fallPops_quiet σ rfl)).append (fallPops_quiet σ hA)).append
    (fallPops_quiet σ hK)) ?_
  rw [s, pairPop, ← hpair]

/-! ## FORS -/

/-- **A FORS tree's levels pop their children**, from any valuation where their atoms hold. -/
theorem sForsLevels_pops {pad : Nat} (hp : PadOK σ pad) {pp a0 a1 : V} {bit val : Nat → V}
    {c s : Nat} (hc : c < 24) (hs : s < 2 ^ 10)
    (hbit : ∀ z < 10, σ (bit (10 * c + z)) = if s.testBit z then 1 else 0)
    (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j s)) :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m ≤ 10 →
      AtomsHold rd σ (sForsLevels pad pp a0 a1 bit val c m z cur x).1 →
      FallPops rd σ (sForsLevels pad pp a0 a1 bit val c m z cur x).1
        (climbPops "sp_fors_nodes" (fNodeE (σ pp) (σ a0) (σ a1) c s (sForsSib σ bit c m z x)) s.testBit
          (sForsSib σ bit c m z x) m z (σ cur))
  | 0, _, _, _, _, _ => FallPops.nil
  | m + 1, z, cur, x, hm, hA => by
      rw [sForsLevels_succ] at hA ⊢
      have hL : AtomsHold rd σ (sForsLevel pad pp a0 a1 bit val c z cur x).1 := hA.left
      rw [sForsLevel_eq] at hL
      obtain ⟨hib, hd⟩ := bit_facts (hbit z (by omega))
      have hadr := sForsAt_sound (a1 := a1) (x := x + 4) hc (by omega) hs hval hL.left.right
      have hc' : AtomsHold rd σ (isChildS cur (.n x) (.n (x + 1)) (bit (10 * c + z)) (x + 2)) :=
        hL.left.left.sub fun t ht => List.mem_append_right _ ht
      have hlv := level_sound hp hib hc' hL.right
      have hnext := sForsAt_next a1 val c z x (by omega)
      have h1 := pairLevel_pops (rd := rd) "sp_fors_nodes" (sForsAt_quiet a1 val c (z + 1) (x + 4))
        (kNode_quiet pad pp a0 (sForsAt a1 val c (z + 1) (x + 4)).2.2 (.n x) (.n (x + 1))
          (sForsAt a1 val c (z + 1) (x + 4)).2.1) hib hc' hd
      have ih := sForsLevels_pops hp hc hs hbit hval m (z + 1) _ _ (by omega) hA.right
      have hfirst : σ (.n ((sForsAt a1 val c (z + 1) (x + 4)).2.1 + 4)) =
          fNodeE (σ pp) (σ a0) (σ a1) c s (sForsSib σ bit c (m + 1) z x) z (σ cur) := by
        rw [hlv, hd, hadr]
        simp [fNodeE, sForsSib]
      have hw : (sForsAt a1 val c (z + 1) (x + 4)).2.1 + 5 = x + forsLevelWidth c z := by
        rw [hnext]; unfold forsLevelWidth forsLevelW; omega
      rw [sForsLevel_eq]
      refine FallPops.congr_pops (h1.append ih) ?_
      rw [climbPops, ← hfirst, List.singleton_append, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · simp [sForsSib]
      · rw [hw]
        refine climbPops_congr _ _ m (z + 1) _ fun j hj1 _ => ⟨?_, ?_⟩
        · funext v; unfold fNodeE; simp only [sForsSib, show j ≠ z by omega, ite_false]
        · simp only [sForsSib, show j ≠ z by omega, ite_false]

/-- The siblings a FORS tree from base `b` hints, level by level. -/
abbrev sForsSibs (σ : Val) (bit : Nat → V) (c b : Nat) : Nat → E := sForsSib σ bit c 10 0 (b + forsLeafWidth c)

/-- **A FORS tree's entries**: its secret, then its levels' children, from its leaf `fLeafE`. -/
def forsTreePops (pp a0 A1 : E) (c s : Nat) (secret : E) (sib : Nat → E) : List Pop :=
  ("sp_fors_secrets", [secret]) ::
    climbPops "sp_fors_nodes" (fNodeE pp a0 A1 c s sib) s.testBit sib 10 0 (fLeafE pp a0 A1 c s secret)

/-- **FORS tree `c` pops its secret and its levels' children**, from any valuation where its atoms hold. -/
theorem sForsTree_pops {pad : Nat} (hp : PadOK σ pad) {pp a0 a1 : V} {bit val : Nat → V}
    {c s b : Nat} (hc : c < 24) (hs : s < 2 ^ 10)
    (hbit : ∀ z < 10, σ (bit (10 * c + z)) = if s.testBit z then 1 else 0)
    (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (fIdx c j s))
    (h : AtomsHold rd σ (sForsTree pad pp a0 a1 bit val c b).1) :
    FallPops rd σ (sForsTree pad pp a0 a1 bit val c b).1
      (forsTreePops (σ pp) (σ a0) (σ a1) c s (σ (.n b)) (sForsSibs σ bit c b)) := by
  simp only [sForsTree] at h ⊢
  have hy := sForsAt_leaf_next a1 val c b
  have hadr := sForsAt_sound (a1 := a1) (x := b + 1) hc (by norm_num) hs hval h.left.left.right
  have hk := k64_sound hp h.left.right
  have hlv := sForsLevels_pops hp hc hs hbit hval 10 0 _ _ (by norm_num) h.right
  have hw : (sForsAt a1 val c 0 (b + 1)).2.1 + 2 = b + forsLeafWidth c := by
    rw [hy]; unfold forsLeafWidth; omega
  rw [hw, hk, hadr] at hlv
  have hh : FallPops rd σ [hintW "sp_fors_secrets" [.n b]] [("sp_fors_secrets", [σ (.n b)])] := FallPops.atom _
  have s' : ∀ {α : Type} (p : α) (F : List α), [p] ++ [] ++ [] ++ F = p :: F := by intros; simp
  refine FallPops.congr_pops (((hh.append (fallPops_quiet σ (sForsAt_quiet ..))).append
    (fallPops_quiet σ rfl)).append hlv) ?_
  rw [s', forsTreePops]
  rfl

/-! ## A path -/

/-- **A path pops its levels' children**, from any valuation where its atoms hold. -/
theorem sPath_pops {pad : Nat} (hp : PadOK σ pad) {pp a0 : V} {bit val : Nat → V}
    {off e height : Nat} (hh : height ≤ 16) (he : e < 2 ^ height)
    (hbit : ∀ z < height, σ (bit (off + z)) = if e.testBit z then 1 else 0)
    (hval : ∀ z, z < height → σ (val (off + z)) = eOfNat (e >>> z)) :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m = height →
      AtomsHold rd σ (sPath pad pp a0 bit val off m z cur x).1 →
      FallPops rd σ (sPath pad pp a0 bit val off m z cur x).1
        (climbPops "siblings" (pNodeE (σ pp) (σ a0) e (sPathSib σ bit off m z x)) e.testBit
          (sPathSib σ bit off m z x) m z (σ cur))
  | 0, _, _, _, _, _ => FallPops.nil
  | m + 1, z, cur, x, hm, hA => by
      rw [sPath_succ] at hA ⊢
      obtain ⟨hib, hd⟩ := bit_facts (hbit z (by omega))
      have hadr := sPathAddr_sound (off := off) (x := x + 4) (by omega)
        (by rw [show z + 1 + m = height by omega]; exact he)
        (fun j _ hj => hval j (by omega)) hA.left.left.right
      have hk := hA.left.right
      have hc : AtomsHold rd σ (isChildS cur (.n x) (.n (x + 1)) (bit (off + z)) (x + 2)) :=
        hA.left.left.left.sub fun s hs => List.mem_append_right _ hs
      have hlv := level_sound hp hib hc hk
      have h1 := pairLevel_pops (rd := rd) "siblings" (sPathAddr_quiet val off z m (x + 4))
        (kNode_quiet pad pp a0 (sPathAddr val off z m (x + 4)).2.2 (.n x) (.n (x + 1))
          (sPathAddr val off z m (x + 4)).2.1) hib hc hd
      have ih := sPath_pops hp hh he hbit hval m (z + 1) _ _ (by omega) hA.right
      have hfirst : σ (.n ((sPathAddr val off z m (x + 4)).2.1 + 4)) =
          pNodeE (σ pp) (σ a0) e (sPathSib σ bit off (m + 1) z x) z (σ cur) := by
        rw [hlv, hd, hadr]
        simp [pNodeE, sPathSib]
      have hw : (sPathAddr val off z m (x + 4)).2.1 + 5 = x + pathWidth m := by
        rw [sPathAddr_next]; unfold pathWidth; split_ifs <;> omega
      refine FallPops.congr_pops (h1.append ih) ?_
      rw [climbPops, ← hfirst, List.singleton_append, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · simp [sPathSib]
      · rw [hw]
        refine climbPops_congr _ _ m (z + 1) _ fun j hj1 _ => ⟨?_, ?_⟩
        · funext v; unfold pNodeE; simp only [sPathSib, show j ≠ z by omega, ite_false]
        · simp only [sPathSib, show j ≠ z by omega, ite_false]

end
end LeanVM.Guest.B1.Sig
