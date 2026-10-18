/-
  LeanVM.Guest.B1.Digest.ClaimTail

  B1 for `claims_tail` (32 specializations; G:2747-2759; TRIAGE #61): the blocks a claim list's
  windows leave over.
-/

module

public import LeanVM.Guest.B1.Digest.Common

/-!
# `claims_tail__L{k}`

`claims_tail__L{k}(state_0, state_1, base, entries_ptr)`, `k < 32`: `k` claims read at
`entries_ptr`, four cells each, compressed in sequence from the state cells under the metadata
cells `base + E(64·(j + 1))`; it returns the state and the pointer past the claims,
`entries_ptr·g^(4k)`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The metadata cells of a run of non-final blocks after `base`. -/
def baseMd (base : E) (j : ℕ) : E := base + metadataCell (64 * (j + 1)) false

/-- **`claims_tail__L{k}`**: `k` claims at `ptr`, chained from the state under `baseMd base`; the
pointer past them. -/
def Meaning_claims_tail (k : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∃ s0 s1 base ptr o0 o1 p', args = [s0, s1, base, ptr] ∧ rets = [o0, o1, p'] ∧
    p' = ptr * gen ^ (4 * k) ∧ ∃ cs : List E, cs.length = 4 * k ∧ CellsAt rd ptr cs ∧
      ChainCells (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)

/-! ## The template -/

/-- `g^(4k)`, `k < 32`, as the 64-bit words the data holds. -/
def tailC : List ℕ :=
  [1, 16, 256, 4096, 65536, 1048576, 16777216, 268435456, 4294967296, 68719476736, 1099511627776,
   17592186044416, 281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976, 27,
   432, 6912, 110592, 1769472, 28311552, 452984832, 7247757312, 115964116992, 1855425871872,
   29686813949952, 474989023199232, 7599824371187712, 121597189939003392, 1945555039024054272,
   12682136550675316763]

theorem tailC_eq (k : ℕ) (hk : k < 32) : word (tailC.getD k 0) 0 0 = gen ^ (4 * k) := by
  rw [word_eq_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1
  interval_cases k <;> decide +kernel

/-- Block `j`: a claim read, its metadata cell, its compression. -/
def ctBlk (j : ℕ) : List Atom :=
  [.hint (.witness "claims" (.heap (.n 3) (4 * j) 4)),
   .load (.n (6 + 8 * j)) (.n 3) (4 * j), .load (.n (7 + 8 * j)) (.n 3) (4 * j + 1),
   .load (.n (8 + 8 * j)) (.n 3) (4 * j + 2), .load (.n (9 + 8 * j)) (.n 3) (4 * j + 3),
   .const (.n (10 + 8 * j)) (word (64 * (j + 1)) 0 0), .add (.n (11 + 8 * j)) (.n 2) (.n (10 + 8 * j)),
   .blake2s (.n (6 + 8 * j)) (.n (7 + 8 * j)) (.n (8 + 8 * j)) (.n (9 + 8 * j)) (.n (4 + 8 * j))
     (.n (5 + 8 * j)) (.n (4 + 8 * (j + 1))) (.n (5 + 8 * (j + 1))) (.n (11 + 8 * j))]

/-- `claims_tail__L{k}`'s body, `k ≥ 1`. -/
def ctBody (k : ℕ) : List Stmt :=
  (([.copy (.n 4) (.n 0), .copy (.n 5) (.n 1)] : List Atom) ++ (List.range k).flatMap ctBlk ++
    ([.copy (.n (6 + 8 * k)) (.n (4 + 8 * k)), .copy (.n (7 + 8 * k)) (.n (5 + 8 * k)),
      .const (.n (8 + 8 * k)) (word (tailC.getD k 0) 0 0), .mul (.n (9 + 8 * k)) (.n 3) (.n (8 + 8 * k))] :
      List Atom)).map .atom ++
  [.ret [.n (6 + 8 * k), .n (7 + 8 * k), .n (9 + 8 * k)]]

/-- `claims_tail__L0`'s body. -/
def ctBody0 : List Stmt :=
  ([.copy (.n 4) (.n 0), .copy (.n 5) (.n 1), .copy (.n 6) (.n 4), .copy (.n 7) (.n 5),
    .copy (.n 8) (.n 3)] : List Atom).map .atom ++ [.ret [.n 6, .n 7, .n 8]]

/-- The specializations' names, as `claim_list_digest` dispatches on them. -/
def ctNames : List String :=
  ["claims_tail__L0", "claims_tail__L1", "claims_tail__L2", "claims_tail__L3", "claims_tail__L4",
   "claims_tail__L5", "claims_tail__L6", "claims_tail__L7", "claims_tail__L8", "claims_tail__L9",
   "claims_tail__L10", "claims_tail__L11", "claims_tail__L12", "claims_tail__L13",
   "claims_tail__L14", "claims_tail__L15", "claims_tail__L16", "claims_tail__L17",
   "claims_tail__L18", "claims_tail__L19", "claims_tail__L20", "claims_tail__L21",
   "claims_tail__L22", "claims_tail__L23", "claims_tail__L24", "claims_tail__L25",
   "claims_tail__L26", "claims_tail__L27", "claims_tail__L28", "claims_tail__L29",
   "claims_tail__L30", "claims_tail__L31"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem find_claims_tail (k : ℕ) (hk : k < 32) :
    coreProgram.find? (ctNames.getD k "") =
      some ⟨ctNames.getD k "", [.n 0, .n 1, .n 2, .n 3], if k = 0 then ctBody0 else ctBody k⟩ := by
  obtain ⟨j, hj⟩ : ∃ j, j = 463 + k := ⟨_, rfl⟩
  interval_cases k
  all_goals exact Program.find?_of_indexOf? (j := j) (by subst hj; decide +kernel) (by subst hj; rfl)

/-! ## `claims_tail__L{k}`, `k ≥ 1` -/

section
variable (k : ℕ) (s0 s1 base ptr : E) (cs : List E) (h : Digest)

/-- The state after `j` blocks. -/
def ctS (j : ℕ) : E × E := digestScalars (chainRun h (blocksOf cs) (baseMd base) j)

/-- The honest values of `claims_tail__L{k}`. -/
def ctVals (i : ℕ) : E :=
  if i < 4 then [s0, s1, base, ptr].getD i 0 else
  if (i - 4) % 8 = 0 then (ctS base cs h ((i - 4) / 8)).1 else
  if (i - 4) % 8 = 1 then (ctS base cs h ((i - 4) / 8)).2 else
  if (i - 4) % 8 = 6 then word (64 * ((i - 4) / 8 + 1)) 0 0 else
  if (i - 4) % 8 = 7 then baseMd base ((i - 4) / 8) else
  if (i - 4) / 8 < k then cs.getD (4 * ((i - 4) / 8) + ((i - 4) % 8 - 2)) 0 else
  if (i - 4) % 8 = 2 then (ctS base cs h k).1 else
  if (i - 4) % 8 = 3 then (ctS base cs h k).2 else
  if (i - 4) % 8 = 4 then word (tailC.getD k 0) 0 0 else ptr * word (tailC.getD k 0) 0 0

theorem ctVals_st (j : ℕ) :
    ctVals k s0 s1 base ptr cs h (4 + 8 * j) = (ctS base cs h j).1 ∧
      ctVals k s0 s1 base ptr cs h (5 + 8 * j) = (ctS base cs h j).2 := by
  constructor
  · simp only [ctVals, show ¬(4 + 8 * j < 4) by omega, show (4 + 8 * j - 4) % 8 = 0 by omega,
      show (4 + 8 * j - 4) / 8 = j by omega, ↓reduceIte]
  · simp only [ctVals, show ¬(5 + 8 * j < 4) by omega, show (5 + 8 * j - 4) % 8 = 1 by omega,
      show (5 + 8 * j - 4) / 8 = j by omega, ↓reduceIte, one_ne_zero]

theorem ctVals_cell (j r : ℕ) (hj : j < k) (hr : r < 4) :
    ctVals k s0 s1 base ptr cs h (6 + 8 * j + r) = cs.getD (4 * j + r) 0 := by
  simp only [ctVals, show ¬(6 + 8 * j + r < 4) by omega, show (6 + 8 * j + r - 4) % 8 = r + 2 by omega,
    show (6 + 8 * j + r - 4) / 8 = j by omega, show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega,
    show r + 2 ≠ 6 by omega, show r + 2 ≠ 7 by omega, hj, ↓reduceIte, Nat.add_sub_cancel]

theorem ctVals_md (j : ℕ) :
    ctVals k s0 s1 base ptr cs h (10 + 8 * j) = word (64 * (j + 1)) 0 0 ∧
      ctVals k s0 s1 base ptr cs h (11 + 8 * j) = baseMd base j := by
  constructor
  · simp only [ctVals, show ¬(10 + 8 * j < 4) by omega, show (10 + 8 * j - 4) % 8 = 6 by omega,
      show (10 + 8 * j - 4) / 8 = j by omega, ↓reduceIte]
    simp
  · simp only [ctVals, show ¬(11 + 8 * j < 4) by omega, show (11 + 8 * j - 4) % 8 = 7 by omega,
      show (11 + 8 * j - 4) / 8 = j by omega, ↓reduceIte]
    simp

theorem ctVals_tail :
    ctVals k s0 s1 base ptr cs h (6 + 8 * k) = (ctS base cs h k).1 ∧
      ctVals k s0 s1 base ptr cs h (7 + 8 * k) = (ctS base cs h k).2 ∧
      ctVals k s0 s1 base ptr cs h (8 + 8 * k) = word (tailC.getD k 0) 0 0 ∧
      ctVals k s0 s1 base ptr cs h (9 + 8 * k) = ptr * word (tailC.getD k 0) 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [ctVals, show ¬(6 + 8 * k < 4) by omega, show ¬(7 + 8 * k < 4) by omega,
      show ¬(8 + 8 * k < 4) by omega, show ¬(9 + 8 * k < 4) by omega,
      show (6 + 8 * k - 4) % 8 = 2 by omega, show (7 + 8 * k - 4) % 8 = 3 by omega,
      show (8 + 8 * k - 4) % 8 = 4 by omega, show (9 + 8 * k - 4) % 8 = 5 by omega,
      show (6 + 8 * k - 4) / 8 = k by omega, show (7 + 8 * k - 4) / 8 = k by omega,
      show (8 + 8 * k - 4) / 8 = k by omega, show (9 + 8 * k - 4) / 8 = k by omega,
      lt_irrefl, ↓reduceIte]
    simp

end

theorem cs_getD' (b k : ℕ) (f : ℕ → E) (j r : ℕ) (hj : j < k) (hr : r < 4) :
    ((List.range (4 * k)).map (fun i => f (b + 8 * (i / 4) + i % 4))).getD (4 * j + r) 0 =
      f (b + 8 * j + r) := by
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  congr 2 <;> omega

theorem cs_getD (k : ℕ) (f : ℕ → E) (j r : ℕ) (hj : j < k) (hr : r < 4) :
    ((List.range (4 * k)).map (fun i => f (6 + 8 * (i / 4) + i % 4))).getD (4 * j + r) 0 =
      f (6 + 8 * j + r) := by
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  congr 2 <;> omega

theorem claims_tail_succ_iff (k : ℕ) (hk1 : 1 ≤ k) (hk : k < 32) (rd : Reader) (name : String)
    (args rets : List E) :
    Fn.Sem (coreProgram.Rel rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3], ctBody k⟩ args rets ↔
      Meaning_claims_tail k rd args rets := by
  simp only [Fn.Sem, ctBody, holdsList_atoms, holdsList_ret, List.forall_mem_append,
    forall_mem_flatMap_range, ctBlk, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff,
    and_true, true_and, List.map_cons, List.map_nil, Meaning_claims_tail]
  constructor
  · rintro ⟨σ, hp, ⟨⟨⟨h4, h5⟩, hblk⟩, h6, h7, h8, h9⟩, hr⟩
    set cs := (List.range (4 * k)).map (fun i => σ (.n (6 + 8 * (i / 4) + i % 4))) with hcsdef
    have hcs : ∀ j r, j < k → r < 4 → cs.getD (4 * j + r) 0 = σ (.n (6 + 8 * j + r)) :=
      cs_getD k (fun i => σ (.n i))
    have hch := chainCells_of_steps (n := k)
      (blocks := fun j => ![σ (.n (6 + 8 * j)), σ (.n (7 + 8 * j)), σ (.n (8 + 8 * j)),
        σ (.n (9 + 8 * j))]) (md := fun j => σ (.n (11 + 8 * j)))
      (st := fun j => (σ (.n (4 + 8 * j)), σ (.n (5 + 8 * j)))) (fun j hj => (hblk j hj).2.2.2.2.2.2)
    refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n (6 + 8 * k)), σ (.n (7 + 8 * k)),
      σ (.n (9 + 8 * k)), hp.symm, hr.symm, by rw [h9, h8, tailC_eq k hk], cs, by simp [cs], ?_, ?_⟩
    · intro i hi
      have hi' : i < 4 * k := by simpa [cs] using hi
      obtain ⟨j, r, hr4, rfl⟩ : ∃ j r, r < 4 ∧ i = 4 * j + r := ⟨i / 4, i % 4, by omega, by omega⟩
      rw [← List.getD_eq_getElem _ 0 hi, hcs j r (by omega) hr4]
      obtain ⟨l0, l1, l2, l3, -⟩ := hblk j (by omega)
      interval_cases r
      · simpa using l0
      · rw [show 6 + 8 * j + 1 = 7 + 8 * j by omega]; exact l1
      · rw [show 6 + 8 * j + 2 = 8 + 8 * j by omega]; exact l2
      · rw [show 6 + 8 * j + 3 = 9 + 8 * j by omega]; exact l3
    · rw [chainCells_congr (b' := fun j => ![σ (.n (6 + 8 * j)), σ (.n (7 + 8 * j)),
          σ (.n (8 + 8 * j)), σ (.n (9 + 8 * j))]) (md' := fun j => σ (.n (11 + 8 * j)))
          (fun j hj => ?_) (fun j hj => ?_)]
      · simp only [Nat.mul_zero, Nat.add_zero] at hch
        rw [← h4, ← h5, h6, h7]
        exact hch
      · have e0 := hcs j 0 hj (by omega)
        have e1 := hcs j 1 hj (by omega)
        have e2 := hcs j 2 hj (by omega)
        have e3 := hcs j 3 hj (by omega)
        rw [Nat.add_zero, Nat.add_zero] at e0
        rw [show 6 + 8 * j + 1 = 7 + 8 * j by omega] at e1
        rw [show 6 + 8 * j + 2 = 8 + 8 * j by omega] at e2
        rw [show 6 + 8 * j + 3 = 9 + 8 * j by omega] at e3
        simp only [blocksOf, e0, e1, e2, e3]
      · rw [baseMd, (hblk j hj).2.2.2.2.2.1, (hblk j hj).2.2.2.2.1, word_md]
  · rintro ⟨s0, s1, base, ptr, o0, o1, p', rfl, rfl, rfl, cs, hlen, hcells, hch⟩
    rcases hch with ⟨hk0, -⟩ | ⟨-, h, hst, hcan, hout⟩
    · omega
    have e := ctVals_st k s0 s1 base ptr cs h
    have ec := ctVals_cell k s0 s1 base ptr cs h
    have em := ctVals_md k s0 s1 base ptr cs h
    obtain ⟨t6, t7, t8, t9⟩ := ctVals_tail k s0 s1 base ptr cs h
    have hS0 : ctS base cs h 0 = (s0, s1) := by rw [ctS, chainRun, ← hst]
    refine ⟨fun v => ctVals k s0 s1 base ptr cs h v.idx, rfl,
      ⟨⟨⟨?_, ?_⟩, fun j hj => ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
    · show ctVals k s0 s1 base ptr cs h (4 + 8 * 0) = _
      rw [(e 0).1, hS0]; rfl
    · show ctVals k s0 s1 base ptr cs h (5 + 8 * 0) = _
      rw [(e 0).2, hS0]; rfl
    · dsimp only
      rw [show ctVals k s0 s1 base ptr cs h 3 = ptr from rfl]
      have l : ∀ r < 4, LoadHolds rd ptr (4 * j + r) (cs.getD (4 * j + r) 0) := fun r hr => by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact hcells _ (by omega)
      rw [show 6 + 8 * j = 6 + 8 * j + 0 by rfl, show 7 + 8 * j = 6 + 8 * j + 1 by omega,
        show 8 + 8 * j = 6 + 8 * j + 2 by omega, show 9 + 8 * j = 6 + 8 * j + 3 by omega,
        ec j 0 hj (by omega), ec j 1 hj (by omega), ec j 2 hj (by omega), ec j 3 hj (by omega),
        (em j).1, (em j).2, (e j).1, (e j).2, (e (j + 1)).1, (e (j + 1)).2]
      refine ⟨?_, l 1 (by omega), l 2 (by omega), l 3 (by omega), rfl, ?_, ?_⟩
      · simpa using l 0 (by omega)
      · show baseMd base j = base + word (64 * (j + 1)) 0 0
        rw [baseMd, word_md]
      · exact steps_of_chainCells hcan j hj
    · show ctVals k s0 s1 base ptr cs h (6 + 8 * k) = ctVals k s0 s1 base ptr cs h (4 + 8 * k)
      rw [t6, (e k).1]
    · show ctVals k s0 s1 base ptr cs h (7 + 8 * k) = ctVals k s0 s1 base ptr cs h (5 + 8 * k)
      rw [t7, (e k).2]
    · exact t8
    · show ctVals k s0 s1 base ptr cs h (9 + 8 * k) = ctVals k s0 s1 base ptr cs h 3 *
        ctVals k s0 s1 base ptr cs h (8 + 8 * k)
      rw [t9, t8]; rfl
    · show [ctVals k s0 s1 base ptr cs h (6 + 8 * k), ctVals k s0 s1 base ptr cs h (7 + 8 * k),
        ctVals k s0 s1 base ptr cs h (9 + 8 * k)] = _
      rw [t6, t7, t9, tailC_eq k hk, ctS, ← hout]

theorem claims_tail_zero_iff (rd : Reader) (name : String) (args rets : List E) :
    Fn.Sem (coreProgram.Rel rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3], ctBody0⟩ args rets ↔
      Meaning_claims_tail 0 rd args rets := by
  simp only [Fn.Sem, ctBody0, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  constructor
  · rintro ⟨σ, hp, h4, h5, h6, h7, h8, hr⟩
    refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 6), σ (.n 7), σ (.n 8), hp.symm, hr.symm,
      by rw [h8, Nat.mul_zero, pow_zero, mul_one], [], rfl, cellsAt_nil _ _, Or.inl ⟨rfl, ?_⟩⟩
    rw [h6, h7, h4, h5]
  · rintro ⟨s0, s1, base, ptr, o0, o1, p', rfl, rfl, hp', cs, -, -, hch⟩
    rcases hch with ⟨-, hout⟩ | ⟨h, -⟩
    · refine ⟨listVal [s0, s1, base, ptr, s0, s1, s0, s1, ptr], rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      simp only [Prod.mk.injEq] at hout
      show [s0, s1, ptr] = [o0, o1, p']
      rw [hout.1, hout.2, hp', Nat.mul_zero, pow_zero, mul_one]
    · omega

/-- **`claims_tail__L{k}`**, `k < 32`. -/
theorem claims_tail_iff (k : ℕ) (hk : k < 32) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (ctNames.getD k "") args rets ↔ Meaning_claims_tail k rd args rets := by
  rw [rel_of_find (find_claims_tail k hk)]
  rcases Nat.eq_zero_or_pos k with rfl | h
  · exact claims_tail_zero_iff rd _ args rets
  · simp only [show k ≠ 0 by omega, ↓reduceIte]
    exact claims_tail_succ_iff k h hk rd _ args rets

end
end LeanVM.Guest.B1.Digest
