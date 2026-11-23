/-
  LeanVM.Guest.B1.Digest.ClaimList

  B1 for `claim_list_digest` (TRIAGE #88) and `claim_list_chain`: the digest of a declared claim
  list, hashed 136 claims a loop frame, then seventeen, through a heap chain of sponge states.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListBig0
public import LeanVM.Guest.B1.Digest.ClaimListBig1
public import LeanVM.Guest.B1.Digest.ClaimListBig2
public import LeanVM.Guest.B1.Digest.ClaimListBig3
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_digest»
import LeanVM.Guest.Data.ValNames.«claim_list_chain»
import LeanVM.Guest.Data.ValNames.«claim_list_last__L»
import LeanVM.Guest.Data.ValNames.«claim_list_tail»
import LeanVM.Guest.B1.Common.Vc

/-!
# `claim_list_digest`

`claim_list_digest(entries, n_g)`: for `n_g = 1` the digest of the empty string; otherwise
`list_split` writes `n = 136 a + 17 b + c` and `claim_list_chain` hashes the claims: a heap chain
starts at the zero state (`zero_state`), the loop `claim_list_chain_loop0` absorbs big frame
`q < a` (544 cells, 64 blocks, `final=0`) from the state at `chain · g^(13q)` into the state at
`chain · g^(13(q + 1))`, the loop `claim_list_chain_loop1` then group `q < b` (68 cells, eight
blocks) from `mid = chain · g^(13a)` over the cells from `entries · g^(544a)` (one generic frame
loop: `grpOk`, `grp_step`, `frames_of_loop`), and `claim_list_last__L{c}` absorbs the last `4c`
cells with the padding from the state at `mid · g^(13b)` (`claimLast_sound`). By induction over the
frames (`groups_sound`), the digest is Keccak-256 of the `4n` cells' bytes
(`claim_list_chain_sound`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `claim_list_last__L{k}` -/

set_option maxRecDepth 100000 in
theorem cl_all : ∀ k < 17, clOk k (coreProgram.getD (idx% «claim_list_last__L0» + k) default) =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cl_idx : ∀ k < 17, coreProgram.indexOf? (clNames.getD k "") = some
    (idx% «claim_list_last__L0» + k) :=
  coreProgram_indexOf?_run (by decide +kernel)

/-- **`claim_list_last__L{k}`**: from a state at its first argument after whole blocks `pre`, it
returns the digest of `pre ++` the `4k` cells at its second. -/
theorem claimLast_sound {k : ℕ} (hk : k < 17) {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd (clNames.getD k "") args rets) :
    ∃ sp blk, args = [sp, blk] ∧ ∀ (n : ℕ) (pre : List UInt8), pre.length = rate * n →
      StateAt rd sp 0 (absorbChunks n zeroState pre) →
      ∃ cells : List E, cells.length = 4 * k ∧ ReadsAt rd blk cells ∧
        rets = digestCells (keccak256 (pre ++ cellsBytes cells)) := by
  have hf := find_of_idx (cl_idx k hk)
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem hf args rets).mp h
  have hok := cl_all k hk
  set f := coreProgram.getD (idx% «claim_list_last__L0» + k) default
  simp only [clOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  rw [hpar] at hp
  refine ⟨σ (V.n (valf% «claim_list_last» "state")), σ (V.n (valf% «claim_list_last» "blk")), by rw [← hp]; rfl, fun n pre hpre hS => ?_⟩
  split at hok
  · rename_i atoms r0 r1 hsb
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hc, hr⟩, hl⟩, hst⟩ := hok
    rw [splitBody_eq hsb, holdsList_atoms_ret] at hb
    obtain ⟨hat, hret⟩ := hb
    obtain ⟨hreads, hd⟩ := chain_final_mem hc rfl rfl hst hl hr hat hpre hS
    have hlen : ((clSpec k atoms).vals σ).length = 4 * k := by
      simp [ChainSpec.vals, clSpec]
    have htake : ((clSpec k atoms).vals σ).take ((clSpec k atoms).len / 16) =
        (clSpec k atoms).vals σ := by
      rw [List.take_of_length_le]
      rw [hlen]; simp only [clSpec]; omega
    rw [htake] at hd
    refine ⟨(clSpec k atoms).vals σ, hlen, hreads, ?_⟩
    rw [← hret, ← hd]
    rfl
  · exact absurd hok (by simp)

/-! ## `claim_list_tail` -/

theorem find_claim_list_tail : coreProgram.find? "claim_list_tail" = some fn% «claim_list_tail» :=
  coreProgram_find?_at (j := idx% «claim_list_tail») rfl

theorem claim_list_tail_shape : Fn.body fn% «claim_list_tail» =
    [.dispatch (.n (val% «claim_list_tail» "rest")) clNames [.n (val% «claim_list_tail» "state"), .n (val% «claim_list_tail» "blk")] [.n (val% «claim_list_tail» "d0"), .n (val% «claim_list_tail» "d1")], .atom (.copy (.n (val% «claim_list_tail» "s1#0")) (.n (val% «claim_list_tail» "d0"))),
      .atom (.copy (.n (val% «claim_list_tail» "s1#0[1]")) (.n (val% «claim_list_tail» "d1"))), .ret [.n (val% «claim_list_tail» "s1#0"), .n (val% «claim_list_tail» "s1#0[1]")]] :=
  stmtsEqb_sound (by decide +kernel)

theorem claim_list_tail_params : Fn.params fn% «claim_list_tail» = [.n (val% «claim_list_tail» "state"), .n (val% «claim_list_tail» "blk"), .n (val% «claim_list_tail» "rest")] := by
  decide +kernel

/-- **`claim_list_tail` is its dispatch** on `rest = g^j`, `j < 17`, to `claim_list_last__L{j}` (`vc`). -/
theorem tail_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "claim_list_tail" args rets ↔ ∃ sp blk j d0 d1, args = [sp, blk, ofK (addressOfIndex j)] ∧
      j < 17 ∧ rets = [d0, d1] ∧ coreProgram.Rel rd (clNames.getD j "") [sp, blk] [d0, d1] := by
  have hname : ∀ j (hj : j < clNames.length), clNames[j] = clNames.getD j "" :=
    fun j hj => by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [rel_iff_fnSem find_claim_list_tail]
  vc
  constructor
  · rintro ⟨sp, blk, x, rfl, d0, d1, ⟨j, hx, hj, hc⟩, rfl⟩
    exact ⟨sp, blk, j, d0, d1, by rw [hx], hj, rfl, by rw [← hname j hj]; exact hc⟩
  · rintro ⟨sp, blk, j, d0, d1, rfl, hj, rfl, hc⟩
    exact ⟨sp, blk, _, rfl, d0, d1, ⟨j, rfl, hj, by rw [← hname j hj] at hc; exact hc⟩, rfl⟩

/-- **`claim_list_tail` on `rest = g^j`, `j < 17`, is `claim_list_last__L{j}`.** -/
theorem tail_sound {rd : Reader} {args rets : List E} (h : coreProgram.Rel rd "claim_list_tail" args rets) :
    ∃ sp blk j, args = [sp, blk, ofK (addressOfIndex j)] ∧ j < 17 ∧
      coreProgram.Rel rd (clNames.getD j "") [sp, blk] rets := by
  obtain ⟨sp, blk, j, d0, d1, rfl, hj, rfl, hc⟩ := (tail_iff rd args rets).mp h
  exact ⟨sp, blk, j, rfl, hj, hc⟩

/-! ## The frame loops: `m` claims a frame -/

/-- **One frame of `m` claims, `nb` blocks**: from the state at `chain · x^13` after whole blocks
`pre`, the `4m` cells at `entries · x^(4m)` absorbed, the state written at
`chain · x^13 · g^13`. -/
def GroupStep (rd : Reader) (m nb : ℕ) (chain entries x : E) : Prop :=
  ∀ (n : ℕ) (pre : List UInt8), pre.length = rate * n →
    StateAt rd (chain * x ^ 13) 0 (absorbChunks n zeroState pre) →
    ∃ cells : List E, cells.length = 4 * m ∧ ReadsAt rd (entries * x ^ (4 * m)) cells ∧
      StateAt rd (chain * x ^ 13) 13 (absorbChunks (n + nb) zeroState (pre ++ cellsBytes cells))

theorem grp_step {rd : Reader} {f : String} {j m c0 st0 ep nb : ℕ}
    (hidx : coreProgram.indexOf? f = some j)
    (hok : grpOk (coreProgram.getD j default) f m c0 st0 ep = true)
    (hnb : (grpSpec m c0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    {x : E} {ps : List E} (h : coreProgram.Rel rd f (x :: ps) []) :
    (∀ N chain entries, ps = [N, chain, entries] → GroupStep rd m nb chain entries x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []) := by
  have hf := find_of_idx hidx
  simp only [grpOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hlen4⟩, hc⟩, hst⟩, hl⟩, hout⟩, hm9⟩, hmE⟩ := hok
  obtain ⟨σ, hx, hps, hat, hnext⟩ := loop_step hf hshape h
  refine ⟨fun N chain entries hNce n pre hpre hS => ?_, hnext⟩
  have hpar : (coreProgram.getD j default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    simp only [loopShape, Bool.and_eq_true, decide_eq_true_eq] at hshape
    rw [hshape.1.2, hlen4]; rfl
  rw [hpar, hNce] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, hchain, hentries⟩ := hps
  have h9 : σ (V.n 9) = chain * x ^ 13 := by rw [monoIs_sound hm9 hat, hchain, hx]
  have hE : σ (V.n ep) = entries * x ^ (4 * m) := by rw [monoIs_sound hmE hat, hentries, hx]
  rw [← h9] at hS
  obtain ⟨hreads, hS', -⟩ := chain_whole_mem hc rfl rfl hst hl hout hat hpre hS
  rw [hnb] at hS'
  refine ⟨(grpSpec m c0 st0 (loopAtoms (coreProgram.getD j default))).vals σ,
    by simp [ChainSpec.vals, grpSpec], by rwa [← hE], by rwa [← h9]⟩

set_option maxRecDepth 100000 in
theorem big_nb : (grpSpec 136 21 565 (loopAtoms (coreProgram.getD idx% «claim_list_chain_loop0»
    default))).nb = 64 := by
  decide +kernel

-- The big frame loop `claim_list_chain_loop0` (136 claims, 64 blocks): its head here, its sixteen
-- windows in
-- `ClaimListBig{q}`.
set_option maxRecDepth 100000 in
theorem big_head : grpHead (coreProgram.getD idx% «claim_list_chain_loop0» default)
    name% «claim_list_chain_loop0» 136 21 565 20 = true := by
  decide +kernel

theorem big_ok : grpOk (coreProgram.getD idx% «claim_list_chain_loop0» default)
    name% «claim_list_chain_loop0» 136 21 565 20 = true := by
  have hw : ∀ i < 16, bigWin i = true := by
    intro i hi
    interval_cases i
    exacts [bigWin_0, bigWin_1, bigWin_2, bigWin_3, bigWin_4, bigWin_5, bigWin_6, bigWin_7,
      bigWin_8, bigWin_9, bigWin_10, bigWin_11, bigWin_12, bigWin_13, bigWin_14, bigWin_15]
  simp only [bigWin, bigSpec, bigAtoms, Bool.and_eq_true] at hw
  exact grpOk_of_parts (w := 4) (W := 16) (v := 34) (U := 16) big_head (by rw [big_nb])
    (fun i hi => ChainSpec.blocksOk_of_from (hw i hi).1) (by norm_num)
    (fun i hi => loadsWin_of_from (hw i hi).2)

set_option maxRecDepth 100000 in
theorem big_idx : coreProgram.indexOf? name% «claim_list_chain_loop0» = some
    idx% «claim_list_chain_loop0» :=
  coreProgram_indexOf?_at (j := idx% «claim_list_chain_loop0») rfl


-- The group frame loop `claim_list_chain_loop1` (17 claims, 8 blocks).
set_option maxRecDepth 100000 in
theorem grp_ok : grpOk (coreProgram.getD idx% «claim_list_chain_loop1» default)
    name% «claim_list_chain_loop1» 17 18 86 17 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem grp_idx : coreProgram.indexOf? name% «claim_list_chain_loop1» = some
    idx% «claim_list_chain_loop1» :=
  coreProgram_indexOf?_at (j := idx% «claim_list_chain_loop1») rfl

set_option maxRecDepth 100000 in
theorem grp_nb : (grpSpec 17 18 86 (loopAtoms (coreProgram.getD idx% «claim_list_chain_loop1»
    default))).nb = 8 := by
  decide +kernel

theorem mono2Is_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x base y y' : V} {e e' : ℕ}
    (h : mono2Is atoms x base y e y' e' = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ x = σ base * σ y ^ e * σ y' ^ e' := by
  rw [mono_sound hat 40 x, (List.isPerm_iff.mp h).map σ |>.prod_eq]
  simp [mul_assoc]

/-! ## The frames, by induction -/

theorem gen_pow_pow (q e : ℕ) : (gen ^ q) ^ e = gen ^ (e * q) := by rw [← pow_mul, mul_comm]

/-- **The frames**: after `q ≤ a` frames of `m` claims (`nb` blocks each, `64 m = 136 nb`), the
state at `chain · g^(13q)` is the sponge after the `4mq` cells at `entries`. -/
theorem groups_sound {rd : Reader} {m nb : ℕ} (hmn : 64 * m = 136 * nb) {chain entries : E}
    {a n0 : ℕ} {pre : List UInt8} (hpre0 : pre.length = rate * n0)
    (h0 : StateAt rd chain 0 (absorbChunks n0 zeroState pre))
    (hstep : ∀ q < a, GroupStep rd m nb chain entries (gen ^ q)) :
    ∀ q ≤ a, ∃ cells : List E, cells.length = 4 * m * q ∧ ReadsAt rd entries cells ∧
      StateAt rd (chain * gen ^ (13 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre ++ cellsBytes cells)) := by
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨[], rfl, readsAt_nil _ _, ?_⟩
    simpa using h0
  | succ q ih =>
    intro hq
    obtain ⟨cells, hlen, hreads, hS⟩ := ih (by omega)
    have hpre : (pre ++ cellsBytes cells).length = rate * (n0 + nb * q) := by
      rw [List.length_append, length_cellsBytes, hlen, hpre0]
      show 136 * n0 + 16 * (4 * m * q) = 136 * (n0 + nb * q)
      have : 16 * (4 * m * q) = (64 * m) * q := by ring
      rw [this, hmn]; ring
    rw [show chain * gen ^ (13 * q) = chain * (gen ^ q) ^ 13 by rw [gen_pow_pow]] at hS
    obtain ⟨c2, hl2, hr2, hS2⟩ := hstep q (by omega) _ _ hpre hS
    refine ⟨cells ++ c2, by rw [List.length_append, hlen, hl2]; ring, ?_, ?_⟩
    · rw [readsAt_append, hlen]
      refine ⟨hreads, ?_⟩
      rwa [gen_pow_pow] at hr2
    · intro c
      have := hS2 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow] at this
      rw [loadHolds_mul_gen_pow, cellsBytes_append, ← List.append_assoc,
        show 13 * (q + 1) + (0 + c.val) = 13 * q + (13 + c.val) by ring,
        show n0 + nb * (q + 1) = n0 + nb * q + nb by ring]
      exact this

/-- **A loop of frames of `m` claims**: called as `callIf (1 + N) f [1, N, chain, entries]` with
`N = g^a`, `a < 2^34`, it gives every frame's step. -/
theorem frames_of_loop {rd : Reader} {f : String} {j m c0 st0 ep nb : ℕ}
    (hidx : coreProgram.indexOf? f = some j)
    (hok : grpOk (coreProgram.getD j default) f m c0 st0 ep = true)
    (hnb : (grpSpec m c0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    {N chain entries : E} {a : ℕ} (ha : a < 2 ^ 34) (hN : N = gen ^ a)
    (hloop : 1 + N ≠ 0 → coreProgram.Rel rd f [1, N, chain, entries] []) :
    ∀ q < a, GroupStep rd m nb chain entries (gen ^ q) :=
  loop_sound (f := f) (ps := [N, chain, entries]) (N := N)
    (B := GroupStep rd m nb chain entries) (by unfold ordG; omega) hN
    (fun x hx => by
      obtain ⟨h1, h2⟩ := grp_step hidx hok hnb hx
      exact ⟨h1 _ _ _ rfl, h2⟩)
    hloop

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `claim_list_chain` -/

theorem find_claim_list_chain : coreProgram.find? "claim_list_chain" = some fn% «claim_list_chain» :=
  coreProgram_find?_at (j := idx% «claim_list_chain») rfl

/-- `claim_list_chain`'s body before its `ret`. -/
noncomputable def chainFlat : List Stmt := (Fn.body fn% «claim_list_chain»).dropLast

set_option maxRecDepth 100000 in
theorem claim_list_chain_shape : Fn.body fn% «claim_list_chain» = chainFlat ++ [.ret [.n (val% «claim_list_chain» "s13#0"),
    .n (val% «claim_list_chain» "s13#0[1]")]] :=
  stmtsEqb_sound (by decide +kernel)

/-- The body: the zero state at `chain`, the big frames' loop, `mid = chain · bigs^13`,
`mid_entries = entries · bigs^544`, the groups' loop, `last = mid · groups^13`,
`blk = mid_entries · groups^68`, `claim_list_tail` on the rest. -/
noncomputable def chainBodyOk : Bool :=
  chainFlat.all Stmt.flat &&
  chainFlat.any (stmtEqb · (.callIf (.n (val% «claim_list_chain» "s2#1")) name% «claim_list_chain_loop0» [.n (val% «claim_list_chain» "s2#2"), .n (val% «claim_list_chain» "bigs"), .n (val% «claim_list_chain» "chain"),
      .n (val% «claim_list_chain» "entries_ptr")])) &&
  chainFlat.any (stmtEqb · (.callIf (.n (val% «claim_list_chain» "s5#1")) name% «claim_list_chain_loop1» [.n (val% «claim_list_chain» "s5#2"), .n (val% «claim_list_chain» "groups"), .n (val% «claim_list_chain» "mid"),
      .n (val% «claim_list_chain» "mid_entries")])) &&
  chainFlat.any (stmtEqb · (.call "claim_list_tail" [.n (val% «claim_list_chain» "last"), .n (val% «claim_list_chain» "d0~9"), .n (val% «claim_list_chain» "rest")] [.n (val% «claim_list_chain» "d0"), .n (val% «claim_list_chain» "d1")])) &&
  (atomsIn chainFlat).any (isConstAt (.n (val% «claim_list_chain» "s2#2")) 1 0) &&
  (atomsIn chainFlat).any (isAddAt (.n (val% «claim_list_chain» "s2#1")) (.n (val% «claim_list_chain» "s2#0")) (.n (val% «claim_list_chain» "bigs"))) &&
  (atomsIn chainFlat).any (isConstAt (.n (val% «claim_list_chain» "s2#0")) 1 0) &&
  (atomsIn chainFlat).any (isConstAt (.n (val% «claim_list_chain» "s5#2")) 1 0) &&
  (atomsIn chainFlat).any (isAddAt (.n (val% «claim_list_chain» "s5#1")) (.n (val% «claim_list_chain» "s5#0")) (.n (val% «claim_list_chain» "groups"))) &&
  (atomsIn chainFlat).any (isConstAt (.n (val% «claim_list_chain» "s5#0")) 1 0) &&
  (List.range 13).all (fun c => (atomsIn chainFlat).any (isLoadAt (.n ((val% «claim_list_chain» "s1.i0:zero_state.s0.u0.s0#0") + c)) (.n (val% «claim_list_chain» "chain")) c) &&
    (atomsIn chainFlat).any (isConstAt (.n ((val% «claim_list_chain» "s1.i0:zero_state.s0.u0.s0#0") + c)) 0 0)) &&
  monoIs (atomsIn chainFlat) (.n (val% «claim_list_chain» "mid")) (.n (val% «claim_list_chain» "chain")) (.n (val% «claim_list_chain» "bigs")) 13 &&
  monoIs (atomsIn chainFlat) (.n (val% «claim_list_chain» "mid_entries")) (.n (val% «claim_list_chain» "entries_ptr")) (.n (val% «claim_list_chain» "bigs")) 544 &&
  mono2Is (atomsIn chainFlat) (.n (val% «claim_list_chain» "last")) (.n (val% «claim_list_chain» "chain")) (.n (val% «claim_list_chain» "bigs")) 13 (.n (val% «claim_list_chain» "groups")) 13 &&
  mono2Is (atomsIn chainFlat) (.n (val% «claim_list_chain» "d0~9")) (.n (val% «claim_list_chain» "entries_ptr")) (.n (val% «claim_list_chain» "bigs")) 544 (.n (val% «claim_list_chain» "groups")) 68 &&
  (atomsIn chainFlat).any (isCopyAt (.n (val% «claim_list_chain» "s13#0")) (.n (val% «claim_list_chain» "d0"))) &&
  (atomsIn chainFlat).any (isCopyAt (.n (val% «claim_list_chain» "s13#0[1]")) (.n (val% «claim_list_chain» "d1")))

set_option maxRecDepth 100000 in
theorem chainBody_ok : chainBodyOk = true := by decide +kernel

/-- **`claim_list_chain`**: on `bigs = g^a`, `groups = g^b`, `rest = g^c`, `c < 17`, the digest of the
`4 (136a + 17b + c)` cells at `entries`. -/
theorem claim_list_chain_sound {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd "claim_list_chain" args rets) :
    ∃ entries ng bigs groups rest, args = [entries, ng, bigs, groups, rest] ∧
      ∀ a b c, a < 2 ^ 34 → b < 2 ^ 34 → c < 17 → bigs = gen ^ a → groups = gen ^ b → rest = gen ^ c →
        ∃ cells : List E, cells.length = 4 * (136 * a + 17 * b + c) ∧ ReadsAt rd entries cells ∧
          rets = digestCells (keccak256 (cellsBytes cells)) := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_claim_list_chain args rets).mp h
  refine ⟨σ (.n (val% «claim_list_chain» "entries_ptr")), σ (.n (val% «claim_list_chain» "n_g")), σ (.n (val% «claim_list_chain» "bigs")), σ (.n (val% «claim_list_chain» "groups")), σ (.n (val% «claim_list_chain» "rest")),
    by rw [← hp]; rfl, fun a b c ha hb' hc h23 h24 h25 => ?_⟩
  rw [claim_list_chain_shape, holdsList_append] at hb
  have hok := chainBody_ok
  simp only [chainBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfl, hlp⟩, hlp2⟩, hdis⟩, h50⟩, h49⟩, h48⟩, h70⟩, h69⟩, h68⟩,
    hzs⟩, hm56⟩, hm67⟩, hm76⟩, hm84⟩, hc10⟩, hc11⟩ := hok
  obtain ⟨hall, hret⟩ := holdsList_flat _ (List.all_eq_true.mpr hfl) _ _ hb
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  -- the zero state
  have h0 : StateAt rd (σ (.n (val% «claim_list_chain» "chain"))) 0 (absorbChunks 0 zeroState []) := by
    intro c
    have hl := load_sound (hzs c c.isLt).1 hat
    rw [const_sound (hzs c c.isLt).2 hat, word_zero] at hl
    rw [Nat.zero_add, absorbChunks, cellsOfState_zero]
    exact hl
  -- the big frames
  have hbig := frames_of_loop big_idx big_ok big_nb (chain := σ (.n (val% «claim_list_chain» "chain")))
    (entries := σ (.n (val% «claim_list_chain» "entries_ptr"))) ha h23 (fun hne => by
      have := (callIf_of_flat hall hlp).2
        (by rw [add_sound h49 hat, const_sound h48 hat, word_one]; exact hne)
      simpa [const_sound h50 hat, word_one] using this)
  obtain ⟨ca, hla, hra, hSa⟩ := groups_sound (by norm_num) (n0 := 0) (pre := []) rfl h0
    hbig a le_rfl
  -- the groups
  have h56 : σ (.n (val% «claim_list_chain» "mid")) = σ (.n (val% «claim_list_chain» "chain")) * gen ^ (13 * a) := by
    rw [monoIs_sound hm56 hat, h23, gen_pow_pow]
  have h67 : σ (.n (val% «claim_list_chain» "mid_entries")) = σ (.n (val% «claim_list_chain» "entries_ptr")) * gen ^ (544 * a) := by
    rw [monoIs_sound hm67 hat, h23, gen_pow_pow]
  have hgrp := frames_of_loop grp_idx grp_ok grp_nb (chain := σ (.n (val% «claim_list_chain» "mid")))
    (entries := σ (.n (val% «claim_list_chain» "mid_entries"))) hb' h24 (fun hne => by
      have := (callIf_of_flat hall hlp2).2
        (by rw [add_sound h69 hat, const_sound h68 hat, word_one]; exact hne)
      simpa [const_sound h70 hat, word_one] using this)
  have hpa : ([] ++ cellsBytes ca).length = rate * (0 + 64 * a) := by
    rw [List.nil_append, length_cellsBytes, hla]; show 16 * (4 * 136 * a) = 136 * (0 + 64 * a)
    ring
  obtain ⟨cb, hlb, hrb, hSb⟩ := groups_sound (by norm_num) hpa
    (by rw [h56]; exact hSa) hgrp b le_rfl
  -- the rest
  obtain ⟨sp0, blk0, j, hta, hj17, hcall⟩ := tail_sound (call_of_flat hall hdis)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hta
  obtain ⟨hsp0, hblk0, hsel⟩ := hta
  have hjc : j = c := by
    rw [h25, gen_pow_eq_ofK] at hsel
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hsel)).symm
  subst hjc
  obtain ⟨sp, blk, hargs, hlast⟩ := claimLast_sound hj17 hcall
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨hsp, hblk⟩ := hargs
  rw [← hsp0] at hsp
  rw [← hblk0] at hblk
  have h76 : σ (.n (val% «claim_list_chain» "last")) = σ (.n (val% «claim_list_chain» "mid")) * gen ^ (13 * b) := by
    rw [mono2Is_sound hm76 hat, h56, h23, h24]; simp only [gen_pow_pow]
  have h84 : σ (.n (val% «claim_list_chain» "d0~9")) = σ (.n (val% «claim_list_chain» "mid_entries")) * gen ^ (68 * b) := by
    rw [mono2Is_sound hm84 hat, h67, h23, h24]; simp only [gen_pow_pow]
  have hpre : ([] ++ cellsBytes ca ++ cellsBytes cb).length = rate * (0 + 64 * a + 8 * b) := by
    rw [List.length_append, List.nil_append, length_cellsBytes, length_cellsBytes, hla, hlb]
    show 16 * (4 * 136 * a) + 16 * (4 * 17 * b) = 136 * (0 + 64 * a + 8 * b)
    ring
  obtain ⟨cc, hlc, hrc, hd⟩ := hlast _ _ hpre (by rw [← hsp, h76]; exact hSb)
  refine ⟨ca ++ cb ++ cc, by rw [List.length_append, List.length_append, hla, hlb, hlc]; ring, ?_, ?_⟩
  · rw [readsAt_append, readsAt_append, List.length_append, hla, hlb]
    refine ⟨⟨hra, ?_⟩, ?_⟩
    · rw [show 4 * 136 * a = 544 * a by ring, ← h67]; exact hrb
    · rw [← hblk, h84, h67, mul_assoc, ← pow_add] at hrc
      rwa [show 4 * 136 * a + 4 * 17 * b = 544 * a + 68 * b by ring]
  · rw [← hret, copy_sound hc10 hat, copy_sound hc11 hat, cellsBytes_append, cellsBytes_append]
    simpa using hd

/-! ## `claim_list_digest` -/

/-- The branch of an empty list. -/
noncomputable def cl23Zero : List Stmt := match Fn.body fn% «claim_list_digest» with
  | [_, _, .ite _ z _, _, _, _, _] => z
  | _ => []

/-- The branch of a nonempty list. -/
noncomputable def cl23Else : List Stmt := match Fn.body fn% «claim_list_digest» with
  | [_, _, .ite _ _ n, _, _, _, _] => n
  | _ => []

set_option maxRecDepth 100000 in
theorem claim_list_digest_shape : Fn.body fn% «claim_list_digest» =
    [.atom (.const (.n (val% «claim_list_digest» "s1#0")) (word 1 0)), .atom (.add (.n (val% «claim_list_digest» "s1#1")) (.n (val% «claim_list_digest» "n_g")) (.n (val% «claim_list_digest» "s1#0"))),
     .ite (.n (val% «claim_list_digest» "s1#1")) cl23Zero cl23Else, .atom (.touch (.n (val% «claim_list_digest» "s2#0")) (.n (val% «claim_list_digest» "n_g"))), .atom (.copy (.n (val% «claim_list_digest» "s3#0")) (.n (val% «claim_list_digest» "digest[0]"))),
     .atom (.copy (.n (val% «claim_list_digest» "s3#0[1]")) (.n (val% «claim_list_digest» "digest[1]"))), .ret [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")]] :=
  stmtsEqb_sound (by decide +kernel)

/-- The empty list's chain: the empty message from the zero state. -/
noncomputable def czSpec : ChainSpec := ⟨[], 0, true, none, keccakBlocks (atomsIn cl23Zero)⟩

/-- The empty list's branch hashes the empty string into `.n 10`, `.n 11`. -/
noncomputable def czOk : Bool :=
  cl23Zero.all Stmt.flat && czSpec.check (atomsIn cl23Zero) &&
    decide (czSpec.outV (czSpec.nb - 1) 0 = V.n (val% «claim_list_digest» "digest[0]")) && decide (czSpec.outV (czSpec.nb - 1) 1 = V.n (val% «claim_list_digest» "digest[1]"))

/-- The nonempty list's branch: `list_split`, then `claim_list_chain` on its split, its digest copied. -/
noncomputable def ceOk : Bool :=
  cl23Else.all Stmt.flat &&
  cl23Else.any (stmtEqb · (.call "list_split" [.n (val% «claim_list_digest» "n_g")] [.n (val% «claim_list_digest» "bigs"), .n (val% «claim_list_digest» "groups"), .n (val% «claim_list_digest» "rest")])) &&
  cl23Else.any (stmtEqb · (.call "claim_list_chain" [.n (val% «claim_list_digest» "entries_ptr"), .n (val% «claim_list_digest» "n_g"), .n (val% «claim_list_digest» "bigs"), .n (val% «claim_list_digest» "groups"), .n (val% «claim_list_digest» "rest")]
    [.n (val% «claim_list_digest» "d0"), .n (val% «claim_list_digest» "d1")])) &&
  (atomsIn cl23Else).any (isCopyAt (.n (val% «claim_list_digest» "digest[0]")) (.n (val% «claim_list_digest» "d0"))) &&
  (atomsIn cl23Else).any (isCopyAt (.n (val% «claim_list_digest» "digest[1]")) (.n (val% «claim_list_digest» "d1")))

set_option maxRecDepth 100000 in
theorem cz_ok : czOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ce_ok : ceOk = true := by decide +kernel

/-- **`claim_list_digest` computes the digest of the claims.** -/
theorem claim_list_digest_sound : claim_list_digest_sound_Spec := by
  intro rd hm args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_claim_list_digest args rets).mp h
  have hp' : args = [σ (.n (val% «claim_list_digest» "entries_ptr")), σ (.n (val% «claim_list_digest» "n_g"))] := by rw [← hp]; rfl
  subst hp'
  rw [claim_list_digest_shape] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨c2, a3, -, hz, hnz⟩ := hb
  have hz1 := cz_ok
  have he1 := ce_ok
  simp only [czOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [ceOk, Bool.and_eq_true, List.all_eq_true] at he1
  obtain ⟨⟨⟨hzf, hzc⟩, hz10⟩, hz11⟩ := hz1
  obtain ⟨⟨⟨⟨hef, hls⟩, hcc⟩, hc10⟩, hc11⟩ := he1
  by_cases h3 : σ (.n (val% «claim_list_digest» "s1#1")) = 0
  · -- the empty list
    have hn1 : σ (.n (val% «claim_list_digest» "n_g")) = 1 := by
      rw [a3, c2, word_one] at h3; exact e_add_eq_zero_iff.mp h3
    obtain ⟨hall, -, h65, h66, hr⟩ := holdsList_flat _ hzf _ _ (hz h3)
    have hat := atoms_of_flat hall
    have hd := chain_final hzc rfl hat (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    rw [hz10, hz11, show List.take (czSpec.len / 16) (czSpec.vals σ) = [] by simp [czSpec],
      List.nil_append] at hd
    refine ⟨0, by norm_num, by rw [hn1, pow_zero], [], rfl, readsAt_nil _ _, ?_⟩
    rw [← hr, h65, h66, digestCells, ← hd]
  · -- a nonempty list
    obtain ⟨hall, -, h65, h66, hr⟩ := holdsList_flat _ (List.all_eq_true.mpr hef) _ _ (hnz h3)
    have hat := atoms_of_flat hall
    obtain ⟨a, ha, b, hb, c, hc, hn, habc⟩ :=
      list_split_sound rd hm _ _ (call_of_flat hall hls)
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at habc
    obtain ⟨h23, h24, h25⟩ := habc
    simp only [claimGroup, bigGroups] at hb hc
    obtain ⟨e0, n0, b0, g0, r0, hargs, hch⟩ := claim_list_chain_sound (call_of_flat hall hcc)
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs
    obtain ⟨he, -, hbg, hgr, hrs⟩ := hargs
    obtain ⟨cells, hlen, hreads, hd⟩ := hch a b c (by omega) (by omega) hc (by rw [← hbg, h23])
      (by rw [← hgr, h24]) (by rw [← hrs, h25])
    refine ⟨136 * a + 17 * b + c, by simp only [claimBig]; omega, by rw [hn], cells, hlen,
      by rw [he]; exact hreads, ?_⟩
    rw [← hr, h65, h66, copy_sound hc10 hat, copy_sound hc11 hat]
    simpa using hd

end
end LeanVM.Guest.B1.Digest
