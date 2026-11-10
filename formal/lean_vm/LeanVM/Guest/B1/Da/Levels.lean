/-
  LeanVM.Guest.B1.Da.Levels

  `da_levels`' machinery: a level loop's step, the specializations' bodies, and the root of a
  tree built level by level.
-/

module

public import LeanVM.Guest.B1.Da.RowShape

/-!
# `da_levels` (G:4410-4418)

`da_levels(tree, n, log_n)` for `n = 2^k`: the nodes of level `lvl` (two cells each) sit at
`tree·g^(off k lvl)`, `off k lvl = 4·2^k - 4·2^(k - lvl)`, the leaves at level `0`. Level `lvl`'s
loop (`lvlOk`, one helper per `(k, lvl)`, `lvlTab`) hashes nodes `2p`, `2p + 1` into node `p` of
the next level for `p < 2^(k - lvl - 1)` (`LvlStep`, `lvl_step`), and the specialization's body
(`dlOk`) runs the `k` loops in order and returns the cells at `4·2^k - 4`, `4·2^k - 3`.
`levels_root`: the returned pair is `cellRoot k` of the leaves.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader} {σ : Val} {atoms : List Atom}

/-! ## Constants and pointers -/

/-- `c` is the constant `g^k` (its word evaluated in `K`). -/
def isConstPowAt (c : V) (k : ℕ) : Atom → Bool
  | .const d w => decide (d = c) && eEqb w (word (gpowK k).toBitVec.toNat 0 0)
  | _ => false

theorem ofBits_toNat' (a : K) : K.ofBits a.toBitVec.toNat = a := by
  simp [K.ofBits, BitVec.ofNat_toNat]

theorem constPow_sound {c : V} {k : ℕ} (h : atoms.any (isConstPowAt c k) = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) (hk : k < 2 ^ 64) : σ c = gen ^ k := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [isConstPowAt, Bool.false_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hp
  rename_i d w
  obtain ⟨hd, he⟩ := hp
  have e1 : σ d = w := ha
  rw [← hd, e1, eEqb_sound he, word_eOfNat, eOfNat, ofBits_toNat',
    gpowK_eq (by unfold u128Bound; omega), gen_pow_eq_ofK]

/-- `p = tree · g^k · x^e`, by its `MUL` factors. -/
def ptrOk (atoms : List Atom) (p tree x : V) (k e : ℕ) : Bool :=
  if k = 0 then (monoOf atoms 40 p).isPerm (tree :: List.replicate e x)
  else (monoOf atoms 40 p).any fun c =>
    atoms.any (isConstPowAt c k) && (monoOf atoms 40 p).isPerm (tree :: c :: List.replicate e x)

theorem ptr_sound {p tree x : V} {k e : ℕ} (h : ptrOk atoms p tree x k e = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) (hk : k < 2 ^ 64) :
    σ p = σ tree * gen ^ k * σ x ^ e := by
  unfold ptrOk at h
  split at h
  · rename_i hk0
    rw [mono_sound hat 40 p, (List.isPerm_iff.mp h).map σ |>.prod_eq, hk0]
    simp
  · obtain ⟨c, -, hc⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true] at hc
    rw [mono_sound hat 40 p, (List.isPerm_iff.mp hc.2).map σ |>.prod_eq]
    simp only [List.map_cons, List.prod_cons, List.map_replicate, List.prod_replicate,
      constPow_sound hc.1 hat hk]
    ring

/-! ## A level loop -/

/-- The level offsets: level `lvl`'s nodes of a tree over `2^k` leaves. -/
def off (k lvl : ℕ) : ℕ := 4 * 2 ^ k - 4 * 2 ^ (k - lvl)

/-- **A level loop's body, checked**: the four cells loaded through `tree·g^offA·x^4`, hashed,
the digest written through `tree·g^offB·x^2`. -/
def lvlOk (fn : Fn) (f : String) (offA offB : ℕ) : Bool :=
  let A := atomsIn (loopPre fn)
  let pa := if offA = 0 then 5 else 7
  let pb := if offA = 0 then 9 else 11
  let c0 := if offA = 0 then 10 else 12
  loopShapeF fn f && decide (fn.params.length = 3) &&
  (List.range 4).all (fun i => A.any (isLoadAt (.n (c0 + i)) (.n pa) i)) &&
  ptrOk A (.n pa) (.n 2) (.n 0) offA 4 && ptrOk A (.n pb) (.n 2) (.n 0) offB 2 &&
  pairHashOk A (.n c0) (.n (c0 + 1)) (.n (c0 + 2)) (.n (c0 + 3)) (.n pb)

/-- **One node of the next level**: the four cells at `tree·g^offA·x^4` read, canonical, and
their digest's cells at `tree·g^offB·x^2`. -/
def LvlStep (rd : Reader) (tree : E) (offA offB : ℕ) (x : E) : Prop :=
  (∀ i < 4, LoadHolds rd (tree * gen ^ offA * x ^ 4) i (memAt rd (tree * gen ^ offA * x ^ 4) i)) ∧
  LoadHolds rd (tree * gen ^ offB * x ^ 2) 0
    (nodeCells (memAt rd (tree * gen ^ offA * x ^ 4) 0, memAt rd (tree * gen ^ offA * x ^ 4) 1)
      (memAt rd (tree * gen ^ offA * x ^ 4) 2, memAt rd (tree * gen ^ offA * x ^ 4) 3)).1 ∧
  LoadHolds rd (tree * gen ^ offB * x ^ 2) 1
    (nodeCells (memAt rd (tree * gen ^ offA * x ^ 4) 0, memAt rd (tree * gen ^ offA * x ^ 4) 1)
      (memAt rd (tree * gen ^ offA * x ^ 4) 2, memAt rd (tree * gen ^ offA * x ^ 4) 3)).2

theorem lvl_step {f : String} {j offA offB : ℕ} (hidx : coreProgram.indexOf? f = some j)
    (hj : j < coreProgram.length) (hok : lvlOk (coreProgram.getD j default) f offA offB = true)
    (hA : offA < 2 ^ 64) (hB : offB < 2 ^ 64) {x : E} {ps : List E}
    (h : coreProgram.Rel rd f (x :: ps) []) :
    (∀ N tree, ps = [N, tree] → LvlStep rd tree offA offB x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []) := by
  have hf := find_of_idx hidx hj
  simp only [lvlOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨hshape, hlen⟩, hld⟩, hpa⟩, hpb⟩, hph⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N tree hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD j default).params = [V.n 0, V.n 1, V.n 2] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2⟩ := hps
  have ea := ptr_sound hpa hat hA
  have eb := ptr_sound hpb hat hB
  rw [h2, hx] at ea eb
  obtain ⟨h0, h1⟩ := pairHash_sound hph hat
  have hl : ∀ i < 4, LoadHolds rd (tree * gen ^ offA * x ^ 4) i
      (σ (.n ((if offA = 0 then 10 else 12) + i))) := fun i hi => by
    have := load_sound (hld i hi) hat
    rwa [ea] at this
  have hm : ∀ i < 4, memAt rd (tree * gen ^ offA * x ^ 4) i =
      σ (.n ((if offA = 0 then 10 else 12) + i)) := fun i hi => memAt_of_load (hl i hi)
  rw [eb] at h0 h1
  refine ⟨fun i hi => by rw [hm i hi]; exact hl i hi, ?_, ?_, ?_⟩
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append]
    rw [hm 0 (by omega), hm 1 (by omega), hm 2 (by omega), hm 3 (by omega)]
    exact hcan
  · rw [hm 0 (by omega), hm 1 (by omega), hm 2 (by omega), hm 3 (by omega)]
    exact h0
  · rw [hm 0 (by omega), hm 1 (by omega), hm 2 (by omega), hm 3 (by omega)]
    exact h1

/-! ## A specialization's body -/

/-- A body's block and returned values: the body is the block, then `ret vs`. -/
def splitRet (b : List Stmt) : Option (List Stmt × List V) :=
  match b.getLast? with
  | some (.ret vs) => some (b.dropLast, vs)
  | _ => none

theorem splitRet_eq {b P : List Stmt} {vs : List V} (h : splitRet b = some (P, vs)) :
    b = P ++ [Stmt.ret vs] := by
  unfold splitRet at h
  split at h
  · rename_i vs' hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (List.dropLast_append_getLast? _ hl).symm
  · exact absurd h (by simp)

/-- **A guarded loop on a constant bound** `g^k`: `callIf (1 + g^k) f [1, g^k, rest…]`. -/
def guardPowOk (P : List Stmt) (gc : V) (f : String) (one N : V) (rest : List V) (k : ℕ) : Bool :=
  P.any (stmtEqb · (.callIf gc f (one :: N :: rest))) &&
    (match addOf (atomsIn P) gc with
     | some (p, q) => (atomsIn P).any (isConstAt p 1 0) && (atomsIn P).any (isConstPowAt q k)
     | none => false) &&
    (atomsIn P).any (isConstAt one 1 0) && (atomsIn P).any (isConstPowAt N k)

theorem guardPow_sound {P : List Stmt} {gc : V} {f : String} {one N : V} {rest : List V} {k : ℕ}
    (h : guardPowOk P gc f one N rest k = true) {kret : List E → Prop}
    (hall : ∀ s ∈ P, Stmt.Holds (coreProgram.Rel rd) rd σ s True kret)
    (hk : k < 2 ^ 64) :
    1 + gen ^ k ≠ 0 → coreProgram.Rel rd f (1 :: gen ^ k :: rest.map σ) [] := by
  simp only [guardPowOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hc, ha⟩, h1⟩, hN⟩ := h
  have hat := atoms_of_flat hall
  have hcall := callIf_of_flat hall hc
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true] at ha
    intro hne
    have hgc : σ gc = 1 + gen ^ k := by
      rw [addOf_sound hpq hat, const_sound ha.1 hat, word_one, constPow_sound ha.2 hat hk]
    have := hcall.2 (by rw [hgc]; exact hne)
    rwa [List.map_cons, List.map_cons, const_sound h1 hat, word_one, constPow_sound hN hat hk]
      at this
  · exact absurd ha (by simp)

/-- **`da_levels__L{2^k}_L{k}`'s body, checked**, its level loops `loops`. -/
def dlOk (fn : Fn) (k : ℕ) (loops : List String) : Bool :=
  decide (fn.params = [.n 0]) && decide (loops.length = k) &&
  match splitRet fn.body with
  | some (P, vs) =>
    decide (vs = [.n (5 * k + 1), .n (5 * k + 2)]) && P.all Stmt.flat &&
    (List.range k).all (fun lvl => guardPowOk P (.n (5 * lvl + 3)) (loops.getD lvl "")
      (.n (5 * lvl + 4)) (.n (5 * lvl + 5)) [.n 0] (2 ^ (k - lvl - 1))) &&
    (atomsIn P).any (isLoadAt (.n (5 * k + 1)) (.n 0) (4 * 2 ^ k - 4)) &&
    (atomsIn P).any (isLoadAt (.n (5 * k + 2)) (.n 0) (4 * 2 ^ k - 3))
  | none => false

/-! ## The root of the levels -/

/-- Node `i` of level `lvl`: its two cells at `tree·g^(off k lvl + 2i)`. -/
noncomputable def node (rd : Reader) (tree : E) (k lvl i : ℕ) : E × E :=
  (memAt rd tree (off k lvl + 2 * i), memAt rd tree (off k lvl + 2 * i + 1))

theorem cellLevel_nodes {k j : ℕ} (hj : j < k) {rd : Reader} {tree : E}
    (h : ∀ p < 2 ^ (k - j - 1), node rd tree k (j + 1) p =
      nodeCells (node rd tree k j (2 * p)) (node rd tree k j (2 * p + 1))) :
    cellLevel ((List.range (2 ^ (k - j))).map (node rd tree k j)) =
      (List.range (2 ^ (k - (j + 1)))).map (node rd tree k (j + 1)) := by
  have e : 2 ^ (k - j) = 2 * 2 ^ (k - j - 1) := by
    rw [← pow_succ']; congr 1; omega
  unfold cellLevel
  rw [List.length_map, List.length_range, e, Nat.mul_div_cancel_left _ (by norm_num),
    show k - (j + 1) = k - j - 1 by omega]
  refine List.map_congr_left fun p hp => ?_
  have hp' := List.mem_range.mp hp
  rw [h p hp']
  congr 1
  · simp [List.getD_eq_getElem?_getD, show 2 * p < 2 * 2 ^ (k - j - 1) by omega]
  · simp [List.getD_eq_getElem?_getD, show 2 * p + 1 < 2 * 2 ^ (k - j - 1) by omega]

/-- **The root of the levels**: with every level's nodes the digests of the previous level's
pairs, the root over the leaves is the last level's node. -/
theorem levels_root {k : ℕ} {rd : Reader} {tree : E}
    (h : ∀ j < k, ∀ p < 2 ^ (k - j - 1), node rd tree k (j + 1) p =
      nodeCells (node rd tree k j (2 * p)) (node rd tree k j (2 * p + 1))) :
    cellRoot k ((List.range (2 ^ k)).map (node rd tree k 0)) = node rd tree k k 0 := by
  have key : ∀ j ≤ k, cellRoot k ((List.range (2 ^ k)).map (node rd tree k 0)) =
      cellRoot (k - j) ((List.range (2 ^ (k - j))).map (node rd tree k j)) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [ih (by omega), show k - j = (k - (j + 1)) + 1 by omega, cellRoot,
        show k - (j + 1) + 1 = k - j by omega, cellLevel_nodes (by omega) (h j (by omega))]
  rw [key k le_rfl, Nat.sub_self, pow_zero]
  rfl

end
end LeanVM.Guest.B1.Da
