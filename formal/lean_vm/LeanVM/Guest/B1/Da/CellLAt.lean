/-
  LeanVM.Guest.B1.Da.CellLAt

  A blob's cell loop `da_verify_blob_loop0` placed by trees whose cell checks hold the honest symbols, so that it pops
  them: iteration by iteration, within its static bound.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.CellPlaced
public import LeanVM.Guest.B1.Da.DvHonest
public import LeanVM.Guest.B1.Da.LoopsComplete
public import LeanVM.Guest.B1.Da.WeightsAt
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_blob_loop0»
import LeanVM.Guest.StmtsAppend

/-!
# A blob's cell loop, popping its cells' symbols

Blob `i`'s region at `g^bb` (`regionCells syms z i`); the weights at `g^bw` (`wtsCells q`), column `h`'s expansion at
`g^(q h)` (`colRun z h`), its weights at `g^(q h + 128)`.

* `cellLNH`, `cellLFrom`: the loop's iterations of honest shape, cell `k`'s tree of `Tc k`;
* `cellL_stepLF`, `cellL_completeAtTB`: the loop from its first iteration within its static bound, its cells holding
  `syms i k`;
* `cellL_pops`: such a loop pops its cells' symbols in order.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Protocol.KeccakHash
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtDTB Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append iterK)

@[expose] public section

/-- The weights' pointers: column `h`'s weights at `g^(q h + 128)`. -/
def wtsCells (q : ℕ → ℕ) : List E := (List.range 128).map fun h => gen ^ (q h + 128)

theorem length_wtsCells (q : ℕ → ℕ) : (wtsCells q).length = 128 := by simp [wtsCells]

theorem gen_pow_add_ne {a b : ℕ} (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) :
    decide (gen ^ a + gen ^ b ≠ 0) = decide (a ≠ b) :=
  decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
    fun h he => h (gen_pow_inj' ha hb (e_add_eq_zero_iff.mp he))⟩

/-- `da_verify_blob_loop0`'s statements before its `ret`. -/
def cellLP : List Stmt := cellLPre ⧺ [.callIf (.n (val% «da_verify_blob_loop0» "s7#3")) name% «da_verify_blob_loop0» [.n (val% «da_verify_blob_loop0» "s7#5"), .n (val% «da_verify_blob_loop0» "weights"), .n (val% «da_verify_blob_loop0» "base")]]

theorem cellL_body_split : Fn.body (coreProgram.getD idx% «da_verify_blob_loop0» default) = cellLP ⧺ [.ret []] := by
  rw [dv_loops_body.2.2, cellLBody, cellLP, List.append_assoc]
  rfl

theorem cellLP_straight : cellLP.all Main.Stmt.straight = true := rfl

theorem cellL_loop : coreProgram.loop name% «da_verify_blob_loop0» = true := by
  rw [Program.loop_of_find? find_c]; decide +kernel

/-- An iteration's calls: the cell check, then the tail call, taken unless `k + 1 = 128`. -/
def cellLCalls (k : ℕ) : List Call :=
  [⟨"da_verify_cell", [.n (val% «da_verify_blob_loop0» "d0~4")], [.n (val% «da_verify_blob_loop0» "d0"), .n (val% «da_verify_blob_loop0» "d1"), .n (val% «da_verify_blob_loop0» "s")], true⟩] ++
    [⟨name% «da_verify_blob_loop0», [.n (val% «da_verify_blob_loop0» "s7#5"), .n (val% «da_verify_blob_loop0» "weights"), .n (val% «da_verify_blob_loop0» "base")], [], decide (k + 1 ≠ 128)⟩]

/-- **An iteration's honest shape**: at the counter `g^k`, its cell check by a tree of `Tc`, its tail call by a tree
of `Tt`. -/
def cellLNH (k : ℕ) (Tc Tt : Tree → Prop) : Tree → Prop :=
  NodeHonest coreProgram name% «da_verify_blob_loop0» (fun σ => σ (.n (val% «da_verify_blob_loop0» "xb")) = gen ^ k) (fun _ => cellLCalls k)
    (fun _ => []) [Tc, Tt]

/-- **`t` iterations from `k`**, the cell check of iteration `j` by a tree of `Tc j`. -/
def cellLFrom (Tc : ℕ → Tree → Prop) : ℕ → ℕ → Tree → Prop
  | 0, _ => fun _ => False
  | t + 1, k => cellLNH k (Tc k) (cellLFrom Tc t (k + 1))

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **One iteration of the cell loop, placed, its cell check holding the cell's symbols**: blob `i`'s cell `k`. -/
theorem cellL_stepLF {i k bb bw : ℕ} {q : ℕ → ℕ} {syms : ℕ → ℕ → List E} {z : E} {Lin : Layout} (hk : k < 128)
    (hsl : (syms i k).length = 128) (hBm : (bb, regionCells syms z i) ∈ Lin) (hWm : (bw, wtsCells q) ∈ Lin)
    (hCm : (q k, colRun z k) ∈ Lin) {Tt : Tree → Prop}
    (htail : k + 1 < 128 → PlacedLF fs cert 16 name% «da_verify_blob_loop0» Lin [gen ^ (k + 1), gen ^ bw, gen ^ bb] Tt) :
    PlacedLF fs cert 16 name% «da_verify_blob_loop0» Lin [gen ^ k, gen ^ bw, gen ^ bb]
      (cellLNH k (cellNH (syms i k)) Tt) := by
  obtain ⟨Bt', hRest⟩ := placedLF_tail (fs := fs) (cert := cert) (g := name% «da_verify_blob_loop0»)
    (last := k + 1 = 128) fun h' => htail (by omega)
  have hcell := cell_placedF (fs := fs) (cert := cert) (Lin := Lin) (b := q k + 128) (syms i k) (colWs z k) hsl
    (by simp [colWs]) (fun rd hm => colRun_reads hm z k hCm)
    (fun e he => by
      have := regionL_of_mem hCm (k := 128 + e) (by rw [length_colRun]; omega)
      rwa [← Nat.add_assoc] at this)
  refine ⟨fs name% «da_verify_blob_loop0» + Bt', fun fp cur hcur => ?_⟩
  obtain ⟨nc, hRc⟩ := hcell cur
  obtain ⟨nt, hlt, hRt⟩ := hRest (fp + fs name% «da_verify_blob_loop0») (cur + nc) (by omega)
  refine ⟨nc + nt, fun rd hlow hm => ?_⟩
  have hc := hRc rd hlow hm
  have ht := hRt rd hlow hm
  have hB := reads_of_memL hm hBm
  have hW := reads_of_memL hm hWm
  have hreg : ∀ {j : ℕ} {v : E}, j < 641 → (regionCells syms z i).getD j 0 = v → LoadHolds rd (gen ^ bb) j v :=
    fun hj hv => loadHolds_of_reads hB (by rw [length_regionCells]; exact hj) hv
  obtain ⟨hl1, hl2⟩ := regionCells_leaf (syms := syms) (z := z) (i := i) hk
  have h0 : LoadHolds rd (gen ^ bw * gen ^ k) 0 (gen ^ (q k + 128)) := by
    rw [loadHolds_mul_gen_pow]
    exact loadHolds_of_reads hW (by rw [length_wtsCells]; omega) (by
      simp [wtsCells, List.getD_eq_getElem?_getD, hk])
  have h2 : LoadHolds rd (gen ^ bb * gen ^ k) 512 (runSum syms z i k) := by
    rw [loadHolds_mul_gen_pow]
    exact hreg (by omega) (by rw [show k + 512 = 512 + k by ring, regionCells_sum (by omega)])
  have h3 : LoadHolds rd (gen ^ bb * gen ^ k) 513 (runSum syms z i k + cellDot syms z i k) := by
    rw [loadHolds_mul_gen_pow]
    exact hreg (by omega) (by rw [show k + 513 = 512 + (k + 1) by ring, regionCells_sum (by omega), runSum_succ])
  have h4 : LoadHolds rd (gen ^ bb * (gen ^ k * gen ^ k)) 0 (digestHalves (cellD syms i k)).1 := by
    rw [← pow_add, loadHolds_mul_gen_pow]
    exact hreg (by omega) (by rw [show k + k + 0 = 2 * k by ring, hl1])
  have h5 : LoadHolds rd (gen ^ bb * (gen ^ k * gen ^ k)) 1 (digestHalves (cellD syms i k)).2 := by
    rw [← pow_add, loadHolds_mul_gen_pow]
    exact hreg (by omega) (by rw [show k + k + 1 = 2 * k + 1 by ring, hl2])
  rw [cellRets_eq] at hc
  -- the path
  set σ := Val.ofArgs [gen ^ k, gen ^ bw, gen ^ bb, gen ^ bw * gen ^ k, gen ^ (q k + 128),
    (digestHalves (cellD syms i k)).1, (digestHalves (cellD syms i k)).2, cellDot syms z i k,
    gen ^ bb * gen ^ k, runSum syms z i k, runSum syms z i k + cellDot syms z i k, gen ^ k * gen ^ k,
    gen ^ bb * (gen ^ k * gen ^ k), word 2 0, gen ^ k * word 2 0, word 325 0, gen ^ k * word 2 0 + word 325 0,
    word 2 0, gen ^ k * word 2 0] with hσ
  have hw' := Main.walk_straight σ [] cellLP cellLP_straight
  rw [← cellL_body_split] at hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ cellLP_straight
  have h16 : σ (.n (val% «da_verify_blob_loop0» "s7#3")) = gen ^ (k + 1) + gen ^ 128 := by
    show gen ^ k * word 2 0 + word 325 0 = _
    rw [word_gen, gen_pow_mul_gen, word_g128]
  have htk : decide (σ (.n (val% «da_verify_blob_loop0» "s7#3")) ≠ 0) = decide (k + 1 ≠ 128) := by
    rw [h16]; exact gen_pow_add_ne (by omega) (by norm_num)
  have hcalls : calls (cellLP.flatMap (Main.slEvs σ)) = cellLCalls k := by
    rw [hpc, show cellLP.filterMap Main.Stmt.callS =
      [(none, "da_verify_cell", [.n (val% «da_verify_blob_loop0» "d0~4")], [.n (val% «da_verify_blob_loop0» "d0"), .n (val% «da_verify_blob_loop0» "d1"), .n (val% «da_verify_blob_loop0» "s")]),
        (some (.n (val% «da_verify_blob_loop0» "s7#3")), name% «da_verify_blob_loop0», [.n (val% «da_verify_blob_loop0» "s7#5"), .n (val% «da_verify_blob_loop0» "weights"), .n (val% «da_verify_blob_loop0» "base")], [])] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, htk, cellLCalls, List.cons_append, List.nil_append]
  have hal : allocs σ (cellLP.flatMap (Main.slEvs σ)) = [] := by
    rw [hpa, show cellLP.filterMap Main.Stmt.allocSz = [] from rfl]; rfl
  have hev : ∀ e ∈ cellLP.flatMap (Main.slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun s hs => ?_
    simp only [cellLP, cellLPre, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals simp only [SlOk, Atom.Holds, hσ, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero]
    exacts [h0, h2, h3, h4, h5, by rw [word_gen, gen_pow_mul_gen, word_g128]; exact gen_pow_add_isInK _ _]
  have hargs : [V.n (val% «da_verify_blob_loop0» "s7#5"), .n (val% «da_verify_blob_loop0» "weights"), .n (val% «da_verify_blob_loop0» "base")].map σ = [gen ^ (k + 1), gen ^ bw, gen ^ bb] := by
    show [gen ^ k * word 2 0, gen ^ bw, gen ^ bb] = _
    rw [word_gen, gen_pow_mul_gen]
  have hpar : (coreProgram.getD idx% «da_verify_blob_loop0» default).params = [.n (val% «da_verify_blob_loop0» "xb"), .n (val% «da_verify_blob_loop0» "weights"), .n (val% «da_verify_blob_loop0» "base")] :=
    dv_loops_shape.2.2
  have hreg' : ∀ {j : ℕ}, j < 641 → RegionL Lin (bb + j) := fun hj =>
    regionL_of_mem hBm (by rw [length_regionCells]; exact hj)
  have hrel := relAtInWT_of_walk_loop (P := coreProgram) (Ts := [cellNH (syms i k)]) (Tt := Tt) (fs := fs)
    (cert := cert) (σ := σ) (rd := rd) (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False)
    (Rt := RegionL Lin) (Dt := RegionL []) (fp := fp) (c := cur) (Bt := Bt') (m := nt) (N := nc)
    (args := [gen ^ k, gen ^ bw, gen ^ bb]) coreProgram_wf find_c cellL_loop
    (by rw [hpar]; rfl) hw' rfl hev (by rw [hcalls]; rfl)
    (by
      rw [hal, List.sum_nil, Nat.add_zero]
      by_cases hlast : k + 1 = 128
      · simpa [hlast] using ht
      · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte, List.map_nil, Nat.add_zero] at ht ⊢
        rw [hargs]; exact ht)
    (by rw [hal, hpd, show cellLP.filterMap Main.Stmt.allocSz = [] from rfl]; rfl)
    (fun q hq => by
      rw [hpad, show cellLP.filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    rfl
    (by
      rw [hal]
      refine ⟨nc, 0, RegionL Lin, fun _ => False, rfl, fun j hj => Or.inl (Or.inl hj), ?_,
        ⟨rfl, fun j hj => hj.elim⟩⟩
      simp only [ite_true, List.sum_nil, Nat.add_zero]
      exact relAtInT_dmono hc fun _ h => h.elim)
    (fun j hj => Or.inl hj)
    (fun A hA => by
      rw [B1.loadAddrs_straight σ _ cellLP_straight,
        show cellLP.filterMap B1.Stmt.loadS = [(.n (val% «da_verify_blob_loop0» "d0~3"), 0), (.n (val% «da_verify_blob_loop0» "chain"), 512), (.n (val% «da_verify_blob_loop0» "chain"), 513), (.n (val% «da_verify_blob_loop0» "leaf"), 0), (.n (val% «da_verify_blob_loop0» "leaf"), 1)]
          from rfl] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl | rfl
      · refine ⟨bw + k, ?_, Or.inr (Or.inl (regionL_of_mem hWm (by rw [length_wtsCells]; omega)))⟩
        show (gen ^ bw * gen ^ k).limb 0 * addressOfIndex 0 = _
        rw [← pow_add, limb0_gen_pow_mul, Nat.add_zero]
      · refine ⟨bb + (k + 512), ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ bb * gen ^ k).limb 0 * addressOfIndex 512 = _
        rw [← pow_add, limb0_gen_pow_mul]; ring_nf
      · refine ⟨bb + (k + 513), ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ bb * gen ^ k).limb 0 * addressOfIndex 513 = _
        rw [← pow_add, limb0_gen_pow_mul]; ring_nf
      · refine ⟨bb + 2 * k, ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ bb * (gen ^ k * gen ^ k)).limb 0 * addressOfIndex 0 = _
        rw [← pow_add, ← pow_add, limb0_gen_pow_mul]; ring_nf
      · refine ⟨bb + (2 * k + 1), ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ bb * (gen ^ k * gen ^ k)).limb 0 * addressOfIndex 1 = _
        rw [← pow_add, ← pow_add, limb0_gen_pow_mul]; ring_nf)
    (fun j hj => by obtain ⟨q, hq, -⟩ := hj; simp at hq)
  have h' := relAtInCT_nodeHonest (Q := fun σ => σ (.n (val% «da_verify_blob_loop0» "xb")) = gen ^ k)
    (cs := fun _ => cellLCalls k) (bs := fun _ => []) (Ts := [cellNH (syms i k), Tt]) hrel find_c hw' rfl
    (by rw [hcalls]) hal (by simp [cellLCalls])
  rw [hal] at h'
  simp only [List.sum_nil, Nat.zero_add] at h'
  exact h'

/-- **The cell loop, placed from its first iteration within its static bound**, its cell checks holding blob `i`'s
cells' symbols. -/
theorem cellL_completeAtTB {B : ℕ}
    (hT : TotalLeOn coreProgram fs name% «da_verify_blob_loop0» (fun a => a.getD 0 0 = 1) (fun _ => B))
    {i bb bw : ℕ} {q : ℕ → ℕ} {syms : ℕ → ℕ → List E} {z : E} {Lin : Layout}
    (hsl : ∀ k, (syms i k).length = 128) (hBm : (bb, regionCells syms z i) ∈ Lin) (hWm : (bw, wtsCells q) ∈ Lin)
    (hCm : ∀ k < 128, (q k, colRun z k) ∈ Lin) :
    CompleteAtDTB fs cert 16 name% «da_verify_blob_loop0» Lin [1, gen ^ bw, gen ^ bb]
      (Returns []) (cellLFrom (fun k => cellNH (syms i k)) 128 0) B := by
  have key : ∀ t k, k + t + 1 = 128 → PlacedLF fs cert 16 name% «da_verify_blob_loop0» Lin
      [gen ^ k, gen ^ bw, gen ^ bb] (cellLFrom (fun k => cellNH (syms i k)) (t + 1) k) := by
    intro t
    induction t with
    | zero =>
      exact fun k hk => cellL_stepLF (by omega) (hsl k) hBm hWm (hCm k (by omega)) fun h' => absurd h' (by omega)
    | succ t ih =>
      exact fun k hk => cellL_stepLF (by omega) (hsl k) hBm hWm (hCm k (by omega)) fun _ => ih (k + 1) (by omega)
  have h0 := (key 127 0 rfl).toF
  rw [pow_zero] at h0
  exact h0.toDTB fun rd t rets hn hv hb => hT rd t _ rets hn rfl hv hb

theorem cellL_body_mute : Stmt.muteList (fun _ => true)
    (coreProgram.getD idx% «da_verify_blob_loop0» default).body = true := by decide +kernel

/-- **An iteration of the cell loop pops its callees' entries**: its cell's, then the next iteration's. -/
theorem cellL_iter_pops {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E}
    (hv : (Memory.Tree.node name% «da_verify_blob_loop0» σ bufs kids).Valid coreProgram rd args rets) :
    (Memory.Tree.node name% «da_verify_blob_loop0» σ bufs kids).pops coreProgram rd =
      (Memory.Tree.popsKids coreProgram rd kids).flatten := by
  rw [Tree.pops_of_prefix hv find_c (List.nil_append _).symm (splicePops_nil rd σ) cellL_body_mute rfl,
    List.nil_append]

/-- **A cell loop whose cell checks hold `syms i k` pops them**, from iteration `k` to the last. -/
theorem cellL_pops {rd : Reader} {i : ℕ} {syms : ℕ → ℕ → List E} (hsl : ∀ k, (syms i k).length = 128) :
    ∀ n k (t : Memory.Tree) (args rets : List E), k + n = 128 → cellLFrom (fun j => cellNH (syms i j)) n k t →
      t.Valid coreProgram rd args rets →
      t.pops coreProgram rd = (List.range' k n).flatMap fun j => [("da_symbols", syms i j)]
  | 0, _, _, _, _, _, ht, _ => ht.elim
  | n + 1, k, t, args, rets, hkn, ht, hv => by
      obtain ⟨σ, ks, rfl, -, hc, -, hT⟩ := ht
      have hp := cellL_iter_pops hv
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := id hv
      rw [find_c] at hf
      cases hf
      rw [hc _ es vs find_c hw] at hkv
      obtain ⟨kc, kt, rfl⟩ : ∃ kc kt, ks = [kc, kt] := by
        match ks, kidsValid_len hkv with
        | [kc, kt], _ => exact ⟨kc, kt, rfl⟩
      obtain ⟨-, vc, -, vt, -⟩ := hkv
      obtain ⟨tc, tt, -⟩ := hT
      rw [hp]
      simp only [Memory.Tree.popsKids, List.flatten_cons, List.flatten_nil, List.append_nil]
      replace vc : kc.Valid coreProgram rd _ _ := vc
      rw [cellNH_pops (hsl k) (tc rfl) vc, List.range'_succ, List.flatMap_cons]
      by_cases hlast : k + 1 = 128
      · have hn : n = 0 := by omega
        subst hn
        rw [ite_eq_right (by simp [hlast])] at vt
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := vt
        simp [Memory.Tree.pops]
      · rw [ite_eq_left (by simp [hlast])] at vt
        rw [cellL_pops hsl n (k + 1) kt _ _ (by omega) (tt (by simp [hlast])) vt]

end
end LeanVM.Guest.B1.Da
