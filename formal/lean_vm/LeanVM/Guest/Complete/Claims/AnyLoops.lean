module

public import LeanVM.Guest.Complete.Claims.AnyBody
public import LeanVM.Guest.Complete.Claims.Chain
public import LeanVM.Guest.Complete.Claims.KidPops
public import LeanVM.Guest.B1.VsC.LeafA
import LeanVM.Guest.ValRef

/-!
# `child_claim_list_any`'s callees, placed

`anyL_callAtA`: a frame loop of child claims (`child_claim_list_any_loop0`, `_loop1`: params
`[x, N, chain, entries, region, base, last]`, the block's `StackBuf` its frame's variables) entered
at `1` completes placed from its blocks (`any_core` at each counter, the records by
`recMem_group`), its loads the chain buffer's states, the records' marks and cells in the region.
`ccl_callAtA`: `child_claim_list_last__L{r}` a leaf placed from its valuation per memory
(`ccl_core`, `callAtA_leaf`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

theorem loadS_eq_stmtLoad (s : Stmt) : B1.Stmt.loadS s = stmtLoad? s := by
  cases s with
  | atom a => cases a <;> rfl
  | _ => rfl

theorem clU_big {a q : ℕ} (hq : q ≤ a) : clU a q = 8 * q := by
  unfold clU; rw [Nat.min_eq_left hq]; omega

theorem clU_grp (a q : ℕ) : clU a (a + q) = 8 * a + q := by
  unfold clU; rw [Nat.min_eq_right (by omega)]; omega

/-! ## The frame loops -/

set_option maxRecDepth 100000 in
theorem anyLoop0_facts : coreProgram.loop name% «child_claim_list_any_loop0» = true ∧
    (coreProgram.getD idx% «child_claim_list_any_loop0» default).params =
      [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
    (loopPre (coreProgram.getD idx% «child_claim_list_any_loop0» default)).all loopPlainHB = true ∧
    (loopPre (coreProgram.getD idx% «child_claim_list_any_loop0» default)).all noHeapHintC = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem anyLoop1_facts : coreProgram.loop name% «child_claim_list_any_loop1» = true ∧
    (coreProgram.getD idx% «child_claim_list_any_loop1» default).params =
      [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] ∧
    (loopPre (coreProgram.getD idx% «child_claim_list_any_loop1» default)).all loopPlainHB = true ∧
    (loopPre (coreProgram.getD idx% «child_claim_list_any_loop1» default)).all noHeapHintC = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any136_wits : (atomsIn (loopPre (coreProgram.getD idx% «child_claim_list_any_loop0» default))).flatMap atomWit =
    (List.range 136).map fun i => ("child_claim_index", Dest.stack [V.n (ccOV 22 i)]) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any17_wits : (atomsIn (loopPre (coreProgram.getD idx% «child_claim_list_any_loop1» default))).flatMap atomWit =
    (List.range 17).map fun i => ("child_claim_index", Dest.stack [V.n (ccOV 19 i)]) := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- **A frame loop of child claims entered at `1` completes placed**: `M` frames of `m` claims, the
states after each frame at `chain · g^(13q)`, the records' marks and cells in the region. -/
theorem anyL_callAtA {k : ℕ} {j : ℕ} {f : String} {m o0 p0 mk st0 nb : ℕ}
    (hf : coreProgram.find? f = some (coreProgram.getD j default)) (hlp : coreProgram.loop f = true)
    (hpl : (loopPre (coreProgram.getD j default)).all loopPlainHB = true)
    (hnh : (loopPre (coreProgram.getD j default)).all noHeapHintC = true)
    (hok : anyOk (coreProgram.getD j default) f m o0 p0 mk st0 = true)
    (hhd : anycHead (coreProgram.getD j default) f = true)
    (hedge : anycEdge (coreProgram.getD j default) m o0 p0 mk st0 = true)
    (hrecs : ∀ i < m, recW (ccOwn (loopAtoms (coreProgram.getD j default)) p0 i) (anyP mk) o0 i = true)
    (hnb : (anySpec m o0 st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    (hwit : (atomsIn (loopPre (coreProgram.getD j default))).flatMap atomWit =
      (List.range m).map fun i => ("child_claim_index", Dest.stack [V.n (ccOV o0 i)]))
    (h64 : 64 * m = 136 * nb) {base last : E} {chP eP rg L M n0 : ℕ} {pre0 : List UInt8}
    {o : ℕ → ℕ} {cells : List E} (hpre0 : pre0.length = rate * n0) (hl : 4 * m * M ≤ cells.length)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hM : M < 2 ^ 34) (hM0 : M ≠ 0)
    {R : ℕ → Prop} {Pre : Reader → Prop}
    (hmem : ∀ rd, LowDef k rd → Pre rd → (∀ q ≤ M, StateAt rd (gen ^ chP * gen ^ (13 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre0 ++ cellsBytes (cells.take (4 * m * q))))) ∧
      RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base (m * M) o cells ∧ BoundMem rd L)
    (hR1 : ∀ q < M, ∀ c < 26, R (chP + 13 * q + c)) (hR2 : ∀ i < m * M, R (rg + o i))
    (hR3 : ∀ i < m * M, ∀ c < 4, R (eP + 4 * o i + c)) (fp c : ℕ) (hfc : fp + lpBlk fs f M ≤ c) :
    CallAtA fs al cert k f [1, gen ^ M, gen ^ chP, gen ^ eP, gen ^ rg, base, last] [] R (fun _ => False)
      (fun _ => True) Pre (fun rd t => t.pops coreProgram rd = idxPops o 0 (m * M)) (lpBlk fs f M) fp c c := by
  have hshape : loopShapeF (coreProgram.getD j default) f = true := by
    simp only [anycHead, Bool.and_eq_true] at hhd; exact hhd.1.1.1.1
  have hpreA : ∀ s ∈ loopPre (coreProgram.getD j default), ∃ a, s = .atom a := by
    intro s hs
    have := List.all_eq_true.mp hpl s hs
    cases s with
    | atom a => exact ⟨a, rfl⟩
    | _ => simp [loopPlainHB] at this
  have h := loopFHP_callAtA (fs := fs) (al := al) (cert := cert) (k := k) hf hshape hlp hpl hM
    (ps := fun q => idxPops o (m * q) m)
    (rest := [gen ^ chP, gen ^ eP, gen ^ rg, base, last]) (R := R) (Pre := Pre) (fun q hq rd hlow hp => ?_)
    0 (Nat.pos_of_ne_zero hM0) fp c (by simpa using hfc)
  · rw [pow_zero, Nat.sub_zero] at h
    exact h.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h) fun rd t _ ht => by
      rw [ht, loopPopsFrom, Nat.sub_zero, idxPops_flatMap]
  obtain ⟨hS, hrec, hbd⟩ := hmem rd hlow hp
  have hmq : m * q + m ≤ m * M := by nlinarith
  have h1 : 4 * m * q ≤ cells.length := le_trans (by nlinarith) hl
  have h2 : 4 * m * q + 4 * m ≤ cells.length := le_trans (by nlinarith) hl
  have hpre : (pre0 ++ cellsBytes (cells.take (4 * m * q))).length = rate * (n0 + nb * q) := by
    rw [List.length_append, length_cellsBytes, List.length_take, Nat.min_eq_left h1, hpre0]
    show 136 * n0 + 16 * (4 * m * q) = 136 * (n0 + nb * q)
    have : 16 * (4 * m * q) = (64 * m) * q := by ring
    rw [this, h64]; ring
  have hS0 := hS q (by omega)
  have hS1 := hS (q + 1) (by omega)
  rw [show 4 * m * (q + 1) = 4 * m * q + 4 * m by ring, List.take_add, cellsBytes_append,
    ← List.append_assoc, show nb * (q + 1) = nb * q + nb by ring, ← Nat.add_assoc] at hS1
  have hr := recMem_group hrec (s := m * q) (k := m) hmq
  rw [show 4 * (m * q) = 4 * m * q by ring, show base * gen ^ (m * q) = base * (gen ^ q) ^ m by
    rw [gen_pow_pow]] at hr
  obtain ⟨σ, hp', hat, hload, hg⟩ := any_core hok hhd hedge hrecs hnb (x := gen ^ q) (N := gen ^ M)
    (chain := gen ^ chP) rfl rfl rfl rfl hpre (by rw [gen_pow_pow]; exact hS0)
    (cells := (cells.drop (4 * m * q)).take (4 * m))
    (by simp only [List.length_take, List.length_drop]; omega)
    hr hlast hL33 hbd (fun c => by
      have := hS1 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow]
      rw [loadHolds_mul_gen_pow, show 13 * (q + 1) + (0 + c.val) = 13 * q + (13 + c.val) by ring]
        at this
      exact this)
  refine ⟨σ, hp', fun s hs => ?_, fun q' hq' => ?_, fun A hA => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hpreA s hs
    exact hat a (cl_mem_atoms hs)
  · have hq'' : q' ∈ (loopPre (coreProgram.getD j default)).filterMap B1.Stmt.loadS := by
      obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp hq'
      exact List.mem_filterMap.mpr ⟨s, hs, by rw [loadS_eq_stmtLoad]; exact he⟩
    rcases hload q' hq'' with ⟨c, hc26, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, c, hc4, h⟩
    · exact ⟨_, h, hR1 q hq c hc26⟩
    · exact ⟨_, h, hR2 (m * q + i) (by omega)⟩
    · exact ⟨_, h, hR3 (m * q + i) (by omega) c hc4⟩
  · rw [heapHintAddrs_nil_of hnh] at hA
    exact absurd hA List.not_mem_nil
  · rw [blockPops_of_good hpreA hg hwit, idxPops]
    exact List.map_congr_left fun i _ => by rw [w_slot]

/-! ## The last group -/

set_option maxRecDepth 100000 in
/-- `child_claim_list_last__L{r}`'s witness hints: its claims' indices. -/
theorem ccl_wits_all : ∀ r < 17, decide ((cclAtoms r).flatMap atomWit =
    (List.range r).map fun i => ("child_claim_index", Dest.stack [V.n (ccOV 5 i)])) = true := by
  decide +kernel

theorem ccl_wits (r : ℕ) (hr : r < 17) : (cclAtoms r).flatMap atomWit =
    (List.range r).map fun i => ("child_claim_index", Dest.stack [V.n (ccOV 5 i)]) :=
  of_decide_eq_true (ccl_wits_all r hr)

set_option maxRecDepth 100000 in
theorem ccl_noHeap : ∀ r < 17, (cclAtoms r).all (fun a => (atomHeapDest? a).isNone) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_noAddr : ∀ r < 17,
    (cclAtoms r).all (fun a => match a with | .frameAddr .. => false | _ => true) = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
/-- **`child_claim_list_last__L{r}` completes placed**, a leaf at any frame and cursor: the state at
`g^sP`, the records' marks and cells in the region. -/
theorem ccl_callAtA {k r : ℕ} (hr : r < 17) {sP eP rg L n : ℕ} {marks last : E} {pre : List UInt8}
    {os : ℕ → ℕ} {cells : List E} (hpre : pre.length = rate * n) (hl : cells.length = 4 * r)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) {R : ℕ → Prop} {Pre : Reader → Prop}
    (hmem : ∀ rd, LowDef k rd → Pre rd → StateAt rd (gen ^ sP) 0 (absorbChunks n zeroState pre) ∧
      RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) marks r os cells ∧ BoundMem rd L)
    (hR1 : ∀ o < 13, R (sP + o)) (hR2 : ∀ j < r, R (rg + os j))
    (hR3 : ∀ j < r, ∀ c < 4, R (eP + 4 * os j + c)) (fp c : ℕ) :
    CallAtA fs al cert k (cclNames.getD r "") [gen ^ sP, gen ^ eP, gen ^ rg, marks, last]
      (digestCells (keccak256 (pre ++ cellsBytes cells))) R (fun _ => False) (fun _ => True) Pre
      (fun rd t => t.pops coreProgram rd = idxPops os 0 r) (fs (cclNames.getD r "")) fp c c := by
  have h := B1.VsC.callAtA_leaf (fs := fs) (al := al) (cert := cert) (k := k) (f := cclNames.getD r "")
    (args := [gen ^ sP, gen ^ eP, gen ^ rg, marks, last]) (rets := digestCells (keccak256 (pre ++ cellsBytes cells)))
    (R := R) (D := fun _ => False) (Out := fun _ => True) (Pre := Pre)
    (Post := fun rd t => t.pops coreProgram rd = idxPops os 0 r) (fp := fp) (c := c)
    [] [] (ccl_loop hr) ⟨by simp, List.Pairwise.nil⟩ (fun _ _ => trivial) (fun _ h => h.elim) (fun rd hlow _ hp => ?_)
  · simpa using h
  obtain ⟨hS, hrec, hbd⟩ := hmem rd hlow hp
  obtain ⟨vs, σ, hb, hpar, hat, hret, hload, hg⟩ := ccl_core hr rfl rfl rfl hpre hS hl hrec hlast hL33 hbd
  have hw : walk σ (coreProgram.getD (idx% «child_claim_list_last__L0» + r) default).body =
      .ret ((cclAtoms r).map Ev.atom) vs := by rw [hb, walk_atoms]
  refine ⟨σ, _, (cclAtoms r).map Ev.atom, vs, ccl_name hr, hpar, hw, hret,
    calls_atoms _, Memory.allocs_atoms σ (ccl_na hr), ⟨?_, fun q hq => ?_⟩, ?_, fun A hA => ?_, fun A hA => ?_, ?_⟩
  · rw [Memory.allocDsts_atoms (ccl_na hr)]; rfl
  · rw [B1.VsC.addrs_atoms _ (ccl_noAddr r hr)] at hq; exact absurd hq List.not_mem_nil
  · intro ev hev
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hev
    exact hat a ha
  · obtain ⟨d, p, off, ha, rfl⟩ := B1.VsC.mem_loadAddrs hA
    rcases hload (p, off) (List.mem_filterMap.mpr ⟨_, ha, rfl⟩) with ⟨o, ho, h⟩ | ⟨j, hj, h⟩ | ⟨j, hj, c', hc4, h⟩
    · exact ⟨_, h, Or.inr (hR1 o ho)⟩
    · exact ⟨_, h, Or.inr (hR2 j hj)⟩
    · exact ⟨_, h, Or.inr (hR3 j hj c' hc4)⟩
  · rw [B1.VsC.heapHintAddrs_atoms _ (ccl_noHeap r hr)] at hA; exact absurd hA List.not_mem_nil
  · rw [leaf_pops (ccl_name hr) hw, atomsPops_of_good hg (ccl_wits r hr), idxPops]
    exact List.map_congr_left fun i _ => by rw [w_slot, Nat.zero_add]

end
end LeanVM.Guest.Complete
