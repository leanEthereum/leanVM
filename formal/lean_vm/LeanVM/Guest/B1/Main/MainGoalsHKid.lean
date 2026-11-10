/-
  LeanVM.Guest.B1.Main.MainGoalsHKid

  A child of `main`'s honest run as `__loop4` reads it (`hKid`): its counts, its base, its lists'
  digests, its DA digest, its deferred cells; and its statement's digest.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHBase
public import LeanVM.Guest.B1.Main.KidsAt
public import LeanVM.Protocol.Verifier.Load
public import LeanVM.Guest.AcceptableChild

/-!
# The honest children

`cellsBytes_claimCells`: a claim's four cells are its 64 bytes; so the claim lists' digests are
their cells' (`xmssList_cells`, `sphincsList_cells`).
`kid_segOf_sum`: the children's claim `base + j` is child `c`'s claim `j`. `hKid c`: child `c`'s
`KidH`, whose statement digest (`hKid_pi`) is the child's statement's.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (DeployedLimits)
open LeanVM.Guest.Hints (claimCells cellOfBytes cellsOfBytes)
open LeanVM.Guest.B1 (CompleteAtD Returns bufL)

@[expose] public section

/-! ## Cells of bytes -/

theorem cellBytes_cellOfBytes {b : List UInt8} (h : 16 ≤ b.length) :
    cellBytes (cellOfBytes b) = b.take 16 := by
  rw [cellBytes, cellOfBytes, ofLimbs_limb0, ofLimbs_limb1, kBytes_kOfBytes (by omega),
    kBytes_kOfBytes (by rw [List.length_drop]; omega)]
  exact (List.take_add (l := b) (i := 8) (j := 8)).symm

theorem length_claimBytes (r p : BitVec 128) (m : BitVec 256) : (claimBytesOf r p m).length = 64 := by
  simp [claimBytesOf, HashSig.littleEndianBytes]

theorem kid_claimCells_eq (r p : BitVec 128) (m : BitVec 256) :
    claimCells r p m = [cellOfBytes (claimBytesOf r p m), cellOfBytes ((claimBytesOf r p m).drop 16),
      cellOfBytes ((claimBytesOf r p m).drop 32), cellOfBytes ((claimBytesOf r p m).drop 48)] := by
  rw [claimCells, cellsOfBytes, length_claimBytes]
  rfl

theorem kid_length_claimCells (r p : BitVec 128) (m : BitVec 256) : (claimCells r p m).length = 4 := by
  rw [kid_claimCells_eq]; rfl

theorem take16_chain {b : List UInt8} (h : b.length = 64) :
    b.take 16 ++ ((b.drop 16).take 16 ++ ((b.drop 32).take 16 ++ (b.drop 48).take 16)) = b := by
  rw [List.take_of_length_le (l := b.drop 48) (by rw [List.length_drop]; omega),
    show b.drop 48 = (b.drop 32).drop 16 by rw [List.drop_drop], List.take_append_drop,
    show b.drop 32 = (b.drop 16).drop 16 by rw [List.drop_drop], List.take_append_drop,
    List.take_append_drop]

/-- **A claim's four cells are its 64 bytes.** -/
theorem cellsBytes_claimCells (r p : BitVec 128) (m : BitVec 256) :
    cellsBytes (claimCells r p m) = claimBytesOf r p m := by
  have hl := length_claimBytes r p m
  rw [kid_claimCells_eq]
  simp only [cellsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [cellBytes_cellOfBytes (by omega), cellBytes_cellOfBytes (by rw [List.length_drop]; omega),
    cellBytes_cellOfBytes (by rw [List.length_drop]; omega),
    cellBytes_cellOfBytes (by rw [List.length_drop]; omega)]
  exact take16_chain hl

/-! ## The lists' digests are their cells' -/

theorem xmssList_cells (l : List LeanXmssClaim) :
    claimListDigest xmssPublicKeyBytes l = keccak256 (cellsBytes (l.flatMap fun c => claimCells c.1.root c.1.parameter c.2)) := by
  unfold claimListDigest claimListPreimage
  congr 1
  simp only [cellsBytes, List.flatMap_assoc]
  congr 1
  funext c
  exact (cellsBytes_claimCells _ _ _).symm

theorem sphincsList_cells (l : List LeanSphincsClaim) :
    claimListDigest Sphincs.PublicKey.toBytes l =
      keccak256 (cellsBytes (l.flatMap fun c => claimCells c.1.publicSeed c.1.root c.2)) := by
  unfold claimListDigest claimListPreimage
  congr 1
  simp only [cellsBytes, List.flatMap_assoc]
  congr 1
  funext c
  exact (cellsBytes_claimCells _ _ _).symm

/-! ## Lists -/

/-- Entry `w·j + i` of a flattened list of `w`-entry lists. -/
theorem getD_flatMap_uniform {α : Type} {f : α → List E} {w : ℕ} :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = w) → ∀ j (hj : j < l.length), ∀ i < w,
      (l.flatMap f).getD (w * j + i) 0 = (f l[j]).getD i 0
  | [], _, j, hj, _, _ => absurd hj (by simp)
  | a :: l, hw, j, hj, i, hi => by
    rw [List.flatMap_cons]
    have ha := hw a List.mem_cons_self
    rcases j with _ | j
    · rw [Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
      rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [ha]; rw [Nat.mul_succ]; omega),
        ha, show w * (j + 1) + i - w = w * j + i by rw [Nat.mul_succ]; omega,
        ← List.getD_eq_getElem?_getD]
      exact getD_flatMap_uniform l (fun b hb => hw b (List.mem_cons_of_mem _ hb)) j
        (by simpa using hj) i hi

/-- **The children's claim `(sum of the first c lengths) + j`** is child `c`'s claim `j`. -/
theorem kid_segOf_sum : ∀ (ls : List ℕ) (c j : ℕ) (hc : c < ls.length), j < ls[c] →
    segOf ls ((ls.take c).sum + j) = (c, j)
  | [], _, _, hc, _ => absurd hc (by simp)
  | l :: ls, 0, j, _, hj => by
    simp only [List.take_zero, List.sum_nil, Nat.zero_add, segOf]
    split
    · rfl
    · rename_i h; exact absurd (by simpa using hj) h
  | l :: ls, c + 1, j, hc, hj => by
    have ih := kid_segOf_sum ls c j (by simpa using hc) (by simpa using hj)
    have e : (List.take (c + 1) (l :: ls)).sum + j = (ls.take c).sum + j + l := by
      simp only [List.take_succ_cons, List.sum_cons]; omega
    rw [e]
    simp only [segOf]
    split
    · omega
    · rw [show (ls.take c).sum + j + l - l = (ls.take c).sum + j by omega, ih]

/-! ## A child -/

variable (seed : Digest) (s : NodeStatement) (w : NodeWitness)

/-- **Child `c` of the honest run**, as `__loop4` reads it. -/
def hKid (c : ℕ) : KidH where
  ex := hEx w c
  es := hEs w c
  base := gen ^ hW s w c
  cx := (w.children.map fun ch => digestHalves (claimListDigest xmssPublicKeyBytes ch.statement.claims.xmss)).getD c (0, 0)
  cs := (w.children.map fun ch => digestHalves (claimListDigest Sphincs.PublicKey.toBytes ch.statement.claims.sphincs)).getD c
    (0, 0)
  da := (w.children.map fun ch => digestHalves ch.statement.claims.daDigest).getD c (0, 0)
  defer := (w.children.map fun ch => ch.statement.deferredClaim.cells).getD c []

variable {s w}

theorem getD_map_lt {α β : Type} (l : List α) (f : α → β) (x : β) {c : ℕ} (hc : c < l.length) :
    (l.map f).getD c x = f l[c] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map]

theorem hKid_ex {c : ℕ} (hc : c < w.children.length) :
    (hKid s w c).ex = w.children[c].statement.claims.xmss.length := getD_map_lt _ _ _ hc

theorem hKid_es {c : ℕ} (hc : c < w.children.length) :
    (hKid s w c).es = w.children[c].statement.claims.sphincs.length := getD_map_lt _ _ _ hc

theorem hKid_cx {c : ℕ} (hc : c < w.children.length) :
    (hKid s w c).cx = digestHalves (claimListDigest xmssPublicKeyBytes w.children[c].statement.claims.xmss) :=
  getD_map_lt _ _ _ hc

theorem hKid_cs {c : ℕ} (hc : c < w.children.length) :
    (hKid s w c).cs = digestHalves (claimListDigest Sphincs.PublicKey.toBytes w.children[c].statement.claims.sphincs) :=
  getD_map_lt _ _ _ hc

theorem hKid_da {c : ℕ} (hc : c < w.children.length) :
    (hKid s w c).da = digestHalves w.children[c].statement.claims.daDigest := getD_map_lt _ _ _ hc

theorem hKid_defer {c : ℕ} (hc : c < w.children.length) :
    (hKid s w c).defer = w.children[c].statement.deferredClaim.cells := getD_map_lt _ _ _ hc

/-- **Child `c`'s statement digest**, as `__loop4` computes it, is the child's statement's. -/
theorem hKid_pi {c : ℕ} (hc : c < w.children.length) :
    (hKid s w c).pi (digestHalves seed).1 (digestHalves seed).2 =
      digestHalves (statementDigest seed w.children[c].statement) := by
  unfold KidH.pi
  rw [hKid_cx hc, hKid_cs hc, hKid_da hc, hKid_defer hc,
    statementDigest_of_parts (digestBytes_eq_cells seed) (digestBytes_eq_cells _)
      (digestBytes_eq_cells _) (digestBytes_eq_cells _) rfl]

end
end LeanVM.Guest.B1.Main
