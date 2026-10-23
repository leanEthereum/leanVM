/-
  LeanVM.Guest.B1.Da.Levels

  B1 for `da_levels` (11 specializations, G:3022-3031; TRIAGE #70) and its level loops: the
  internal levels of a Merkle tree whose leaves sit in memory.
-/

module

public import LeanVM.Guest.B1.Digest.Common
public import LeanVM.Spec.Da

/-!
# `da_levels__L{2^k}_L{k}`

The tree's `2^k` leaves sit at `tree`, two cells a node; level `l` lies at cell
`4·2^k - 4·2^(k-l)` (`lvOff`), and level `l`'s loop hashes each pair of its nodes into the next
level. The root is the specification's `LeanDa.treeRoot` of the leaves (`treeRoot_nodeD`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## Words of g-powers -/

/-- The words of `g^e` the trees' code holds, by exponent. -/
def gwTab : List (ℕ × ℕ) :=
  [(1, 2), (2, 4), (4, 16), (8, 256), (12, 4096), (16, 65536), (24, 16777216), (28, 268435456),
   (32, 4294967296), (48, 281474976710656), (56, 72057594037927936), (60, 1152921504606846976),
   (64, 27), (96, 115964116992), (112, 7599824371187712), (120, 1945555039024054272),
   (124, 12682136550675316763), (128, 325), (192, 7607), (224, 32671816220672),
   (240, 2141180147837960192), (248, 13186539708940812575), (252, 8070450532247933189),
   (256, 69649), (384, 22103317), (448, 476952263), (480, 2048494371338190848),
   (496, 13170495635268370703), (504, 14339461213564502026), (508, 8070450532517412884),
   (512, 4311744769), (768, 300171238899985), (896, 94597931458646037),
   (960, 2049660569696039367), (992, 13176250230020046863), (1008, 8198240175969533957),
   (1016, 14267404719021359371), (1020, 6917546619827130372), (1024, 281474976776218),
   (1536, 72058805673394458), (1792, 1156204715243055626), (1920, 6441720153044913022),
   (1984, 13176245770889490899), (2016, 14347467702602301457), (2032, 8204432621163905028),
   (2040, 15852670688780353547), (2044, 13835058062261485599), (2048, 111669150020),
   (3072, 98517633419844840), (3584, 1965051239618583364), (3840, 13302112368027285652),
   (3968, 16631350212487341976), (4032, 8198552921648688432), (4064, 14347462583001284619),
   (4080, 7868914448923099140), (4088, 3746994889972252943), (4092, 4611686018427392221)]

/-- The word of `g^e`. -/
def gw (e : ℕ) : ℕ := (gwTab.lookup e).getD 0

set_option maxRecDepth 100000 in
theorem gwTab_ok : (gwTab.all fun p => decide (K.ofBits p.2 = gpowK p.1)) = true := by decide +kernel

theorem lookup_ok : ∀ (l : List (ℕ × ℕ)), (l.all fun p => decide (K.ofBits p.2 = gpowK p.1)) = true →
    ∀ e w, l.lookup e = some w → K.ofBits w = gpowK e
  | [], _, _, _, h => by simp at h
  | p :: l, hall, e, w, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    unfold List.lookup at h
    split at h
    · rename_i he
      simp only [beq_iff_eq] at he
      cases h; rw [he]; exact hall.1
    · exact lookup_ok l hall.2 e w h

theorem gw_spec {e : ℕ} (h : (gwTab.lookup e).isSome = true) (he : e < 2 ^ 128) :
    word (gw e) 0 0 = gen ^ e := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  rw [word_eq_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq he, gw, hw, Option.getD_some]
  exact congrArg ofK (lookup_ok gwTab gwTab_ok e w hw)

/-! ## The templates -/

/-- The cell offset of level `l` of a tree of `2^k` leaves. -/
def lvOff (k l : ℕ) : ℕ := 4 * 2 ^ k - 4 * 2 ^ (k - l)

/-- The loops' names, by `k` then level. -/
def lvNames : List (List String) :=
  [[],
   ["__loop381"],
   ["__loop382", "__loop383"],
   ["__loop384", "__loop385", "__loop386"],
   ["__loop387", "__loop388", "__loop389", "__loop390"],
   ["__loop391", "__loop392", "__loop393", "__loop394", "__loop395"],
   ["__loop396", "__loop397", "__loop398", "__loop399", "__loop400", "__loop401"],
   ["__loop374", "__loop375", "__loop376", "__loop377", "__loop378", "__loop379", "__loop380"],
   ["__loop402", "__loop403", "__loop404", "__loop405", "__loop406", "__loop407", "__loop408",
    "__loop409"],
   ["__loop410", "__loop411", "__loop412", "__loop413", "__loop414", "__loop415", "__loop416",
    "__loop417", "__loop418"],
   ["__loop419", "__loop420", "__loop421", "__loop422", "__loop423", "__loop424", "__loop425",
    "__loop426", "__loop427", "__loop428"]]

/-- The name of level `l`'s loop. -/
def lvName (k l : ℕ) : String := (lvNames.getD k []).getD l ""

/-- The trees' names. -/
def dlNames : List String :=
  ["da_levels__L1_L0", "da_levels__L2_L1", "da_levels__L4_L2", "da_levels__L8_L3",
   "da_levels__L16_L4", "da_levels__L32_L5", "da_levels__L64_L6", "da_levels__L128_L7",
   "da_levels__L256_L8", "da_levels__L512_L9", "da_levels__L1024_L10"]

/-- The core index of the tree of `2^k` leaves. -/
def dlIdx : List ℕ := [537, 538, 539, 540, 541, 542, 543, 534, 544, 545, 546]

/-- The core index of level `l`'s loop. -/
def lvIdx (k l : ℕ) : ℕ := [0, 923, 924, 926, 929, 933, 938, 916, 944, 952, 961].getD k 0 + l

/-- Level `0`'s loop. -/
def lvBody0 (k : ℕ) : List Stmt :=
  ([.mul (.n 3) (.n 0) (.n 0), .mul (.n 4) (.n 3) (.n 3), .mul (.n 5) (.n 2) (.n 4),
    .const (.n 6) (word (gw (lvOff k 1)) 0 0), .mul (.n 7) (.n 2) (.n 6), .mul (.n 8) (.n 0) (.n 0),
    .mul (.n 9) (.n 7) (.n 8), .load (.n 10) (.n 5) 0, .load (.n 11) (.n 5) 1,
    .load (.n 12) (.n 5) 2, .load (.n 13) (.n 5) 3,
    .const (.n 14) (word 13503953895743350343 11912009169889063794 0),
    .const (.n 15) (word 11170449402626986623 6620516960021240235 0),
    .const (.n 16) (word 64 4294967295 0),
    .blake2s (.n 10) (.n 11) (.n 12) (.n 13) (.n 14) (.n 15) (.n 17) (.n 18) (.n 16),
    .load (.n 17) (.n 9) 0, .load (.n 18) (.n 9) 1, .const (.n 19) (word 2 0 0),
    .mul (.n 20) (.n 0) (.n 19), .add (.n 21) (.n 20) (.n 1), .const (.n 22) (word 2 0 0),
    .mul (.n 23) (.n 0) (.n 22)] : List Atom).map .atom ++
  [.callIf (.n 21) (lvName k 0) [.n 23, .n 1, .n 2], .ret []]

/-- Level `l ≥ 1`'s loop. -/
def lvBody (k l : ℕ) : List Stmt :=
  ([.const (.n 3) (word (gw (lvOff k l)) 0 0), .mul (.n 4) (.n 2) (.n 3), .mul (.n 5) (.n 0) (.n 0),
    .mul (.n 6) (.n 5) (.n 5), .mul (.n 7) (.n 4) (.n 6),
    .const (.n 8) (word (gw (lvOff k (l + 1))) 0 0), .mul (.n 9) (.n 2) (.n 8),
    .mul (.n 10) (.n 0) (.n 0), .mul (.n 11) (.n 9) (.n 10), .load (.n 12) (.n 7) 0,
    .load (.n 13) (.n 7) 1, .load (.n 14) (.n 7) 2, .load (.n 15) (.n 7) 3,
    .const (.n 16) (word 13503953895743350343 11912009169889063794 0),
    .const (.n 17) (word 11170449402626986623 6620516960021240235 0),
    .const (.n 18) (word 64 4294967295 0),
    .blake2s (.n 12) (.n 13) (.n 14) (.n 15) (.n 16) (.n 17) (.n 19) (.n 20) (.n 18),
    .load (.n 19) (.n 11) 0, .load (.n 20) (.n 11) 1, .const (.n 21) (word 2 0 0),
    .mul (.n 22) (.n 0) (.n 21), .add (.n 23) (.n 22) (.n 1), .const (.n 24) (word 2 0 0),
    .mul (.n 25) (.n 0) (.n 24)] : List Atom).map .atom ++
  [.callIf (.n 23) (lvName k l) [.n 25, .n 1, .n 2], .ret []]

/-- Level `l` of the tree's body: its loop's entry. -/
def dlBlk (k l : ℕ) : List Stmt :=
  [.atom (.const (.n (1 + 5 * l)) (word 1 0 0)),
   .atom (.const (.n (2 + 5 * l)) (word (gw (2 ^ (k - l - 1))) 0 0)),
   .atom (.add (.n (3 + 5 * l)) (.n (1 + 5 * l)) (.n (2 + 5 * l))),
   .atom (.const (.n (4 + 5 * l)) (word 1 0 0)),
   .atom (.const (.n (5 + 5 * l)) (word (gw (2 ^ (k - l - 1))) 0 0)),
   .callIf (.n (3 + 5 * l)) (lvName k l) [.n (4 + 5 * l), .n (5 + 5 * l), .n 0]]

/-- The tree's body. -/
def dlBody (k : ℕ) : List Stmt :=
  (List.range k).flatMap (dlBlk k) ++
  [.atom (.load (.n (1 + 5 * k)) (.n 0) (4 * 2 ^ k - 4)),
   .atom (.load (.n (2 + 5 * k)) (.n 0) (4 * 2 ^ k - 3)), .ret [.n (1 + 5 * k), .n (2 + 5 * k)]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem find_lv (k l : ℕ) (hk : k ≤ 10) (hl : l < k) :
    coreProgram.find? (lvName k l) =
      some ⟨lvName k l, [.n 0, .n 1, .n 2], if l = 0 then lvBody0 k else lvBody k l⟩ := by
  obtain ⟨j, hj⟩ : ∃ j, j = lvIdx k l := ⟨_, rfl⟩
  interval_cases k <;> interval_cases l
  all_goals exact Program.find?_of_indexOf? (j := j) (by subst hj; decide +kernel) (by subst hj; rfl)

set_option maxRecDepth 100000 in
theorem find_dl (k : ℕ) (hk : k ≤ 10) :
    coreProgram.find? (dlNames.getD k "") = some ⟨dlNames.getD k "", [.n 0], dlBody k⟩ := by
  obtain ⟨j, hj⟩ : ∃ j, j = dlIdx.getD k 0 := ⟨_, rfl⟩
  interval_cases k
  all_goals exact Program.find?_of_indexOf? (j := j) (by subst hj; decide +kernel) (by subst hj; rfl)

end
end LeanVM.Guest.B1.Digest
