/-
  LeanVM.Guest.B1.Da.RowAtP

  A column's row loop `da_verify_column_loop0` placed by trees whose cell checks hold the honest symbols, so that it
  pops them: the cell check placed on its completing valuation (`da_verify_cell_complete_vals`), the loop iteration by
  iteration, within its static bound.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.DaPops
public import LeanVM.Guest.B1.Da.CellAtChk

/-!
# The row loop, popping its cells' symbols

* `PlacedF`, `PlacedLF`: placed at every frame pointer (a loop from an iteration on), no words of its own;
  `PlacedF.toDTB`: within the bound every valid tree of it meets.
* `cellNH syms`: a cell check's node holding `syms`; `cell_placedF`, `cellNH_pops`.
* `l21NH`, `l21From`: the row loop's iterations of honest shape, cell `j`'s tree of `Tc j`; `l21_stepLF`,
  `row_completeAtTB`: the loop from its first iteration within its static bound, its cells holding `syms j h`;
  `l21_pops`: such a loop pops its cells' symbols in order.
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

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-! ## Placed without words of its own -/

/-- **`f` placed at every frame pointer, no words of its own**, by a tree of `T`. -/
def PlacedF (k : ℕ) (f : String) (Lin : Layout) (args rets : List E) (T : Tree → Prop) : Prop :=
  ∀ fp, ∃ n, ∀ rd, LowDef k rd → MemL rd Lin →
    RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp n f args rets T

/-- **A loop helper placed from an iteration on, no words of its own**: its frames, `B` words, at any `fp`, the rest of
its subtree at any `c` past them. -/
def PlacedLF (k : ℕ) (f : String) (Lin : Layout) (args : List E) (T : Tree → Prop) : Prop :=
  ∃ B, ∀ fp c, fp + B ≤ c → ∃ n, ∀ rd, LowDef k rd → MemL rd Lin →
    RelAtInCT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c B n f args [] T

variable {fs cert}

theorem PlacedLF.toF {k : ℕ} {f : String} {Lin : Layout} {args : List E} {T : Tree → Prop}
    (h : PlacedLF fs cert k f Lin args T) : PlacedF fs cert k f Lin args [] T := fun fp =>
  let ⟨B, hB⟩ := h
  let ⟨n, hn⟩ := hB fp (fp + B) le_rfl
  ⟨B + n, fun rd hl hm => (hn rd hl hm).relAtInT⟩

/-- **Within the bound every valid tree meets.** -/
theorem PlacedF.toDTB {k : ℕ} {f : String} {Lin : Layout} {args rets : List E} {T : Tree → Prop} {B : ℕ}
    (h : PlacedF fs cert k f Lin args rets T)
    (hB : ∀ (rd : Reader) (t : Tree) (rets' : List E), t.name = f → t.Valid coreProgram rd args rets' →
      t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtDTB fs cert k f Lin args (Returns rets) T B := by
  intro fp
  classical
  obtain ⟨n, hn⟩ := h fp
  by_cases hex : ∃ rd, LowDef k rd ∧ MemL rd Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    obtain ⟨t, ⟨hnm, hv, hb, -, ht, -⟩, -⟩ := hn rd1 hl1 hL1
    exact ⟨n, [], rets, [], ht ▸ hB rd1 t rets hnm hv hb, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => hn rd hl (by simpa using hL)⟩
  · exact ⟨0, [], rets, [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- **The rest of a loop**: the next iteration's `PlacedLF`, or after the last a phantom of one frame. -/
theorem placedLF_tail {k : ℕ} {f g : String} {Lin : Layout} {args : List E} {T : Tree → Prop} {last : Prop}
    [Decidable last] (h : ¬ last → PlacedLF fs cert k f Lin args T) :
    ∃ Bt, ∀ fp c, fp + Bt ≤ c → ∃ nt, (last → Bt = fs g ∧ nt = 0) ∧ ∀ rd, LowDef k rd → MemL rd Lin →
      if decide (¬ last) = true then
        RelAtInCT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c Bt nt f args [] T
      else Bt = fs g ∧ nt = 0 := by
  by_cases hl : last
  · exact ⟨fs g, fun _ _ _ => ⟨0, fun _ => ⟨rfl, rfl⟩, fun _ _ _ => by simp [hl]⟩⟩
  · obtain ⟨B, hB⟩ := h hl
    refine ⟨B, fun fp c hc => ?_⟩
    obtain ⟨nt, hR⟩ := hB fp c hc
    refine ⟨nt, fun h' => absurd h' hl, fun rd hlw hm => ?_⟩
    simp only [hl, not_false_eq_true, decide_true, ↓reduceIte]
    exact hR rd hlw hm

/-! ## The cell check -/

/-- The symbols a cell check's valuation holds. -/
def cellQ (syms : List K) (σ : Val) : Prop := ∀ j < 256, σ (.n (j + 1)) = ofK (syms.getD j 0)

/-- **A cell check's node holding `syms`.** -/
def cellNH (syms : List K) (t : Tree) : Prop := ∃ σ ks, t = .node "da_verify_cell" σ [] ks ∧ cellQ syms σ

/-- **A cell check holding `syms` pops them.** -/
theorem cellNH_pops {syms : List K} (hsl : syms.length = 256) {t : Tree} (ht : cellNH syms t) {rd : Reader}
    {args rets : List E} (hv : t.Valid coreProgram rd args rets) :
    t.pops coreProgram rd = [("da_symbols", syms.map ofK)] := by
  obtain ⟨σ, ks, rfl, hq⟩ := ht
  rw [cell_pops hv, cellPop]
  refine congrArg (fun l => [(("da_symbols" : String), l)]) (List.ext_getElem (by simp [hsl]) fun j h1 h2 => ?_)
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  rw [hq j h1, List.getD_eq_getElem _ _ (by omega)]

/-- **The cell check placed on its completing valuation**: its weights `ws` at `g^b`, which `Lin` holds. -/
theorem cell_placedF {Lin : Layout} {b : ℕ} (syms : List K) (ws : List E) (hsl : syms.length = 256)
    (hwl : ws.length = 256) (hreads : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ b) ws)
    (hreg : ∀ e < 256, RegionL Lin (b + e)) :
    PlacedF fs cert 16 "da_verify_cell" Lin [gen ^ b] (cellRets syms ws) (cellNH syms) := by
  have hok := cellp_ok
  unfold cellPOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hbe, hflat⟩, hnd⟩, hni⟩, haddr⟩, halloc⟩, hcall⟩, hloads⟩ := hok
  have hb := stmtsEqb_sound hbe
  intro fp
  refine ⟨fs "da_verify_cell", fun rd _ hm => ?_⟩
  obtain ⟨σ, e0, hsym, hh⟩ := da_verify_cell_complete_vals rd (gen ^ b) syms ws hsl hwl (hreads rd hm)
  have hdo : ∀ s ∈ cellPre, B1.DispOk σ s := fun s hs => by
    have := List.all_eq_true.mp hnd s hs
    cases s with
    | dispatch => simp [noDispatch] at this
    | _ => trivial
  have hf := find_da_verify_cell
  have hpar := da_verify_cell_params
  have hmem : fn% «da_verify_cell» ∈ coreProgram := List.mem_of_find?_eq_some hf
  have hh1 := hh fun _ _ _ => True
  generalize fn% «da_verify_cell» = F at hf hpar hmem hh1 hb
  have hw := B1.walk_flat σ [.n 1740, .n 1741, .n 1742] cellPre hflat hdo
  rw [← hb] at hw
  have hsat := walk_sat (P := coreProgram) _ (coreProgram_wf _ hmem) hh1
  rw [hw] at hsat
  obtain ⟨i1, i2, i3, i4, i5⟩ := B1.flat_parts σ cellPre hflat
  have hal : allocs σ (cellPre.flatMap (B1.flEvs σ)) = [] := by rw [i2, halloc]; rfl
  have hcs : calls (cellPre.flatMap (B1.flEvs σ)) = [] := by
    rw [i4, show cellPre.filterMap (Stmt.callSF σ) = [] by
      rw [← hcall]
      refine List.filterMap_congr fun s hs => ?_
      have := List.all_eq_true.mp hnd s hs
      cases s with
      | dispatch => simp [noDispatch] at this
      | _ => rfl]
    rfl
  have hrel := relAtInWT_of_walk (P := coreProgram) (fs := fs)
    (cert := cert) (σ := σ) (rd := rd) (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0)
    (fp := fp) (args := [gen ^ b]) (rets := cellRets syms ws) coreProgram_wf hf (Or.inr hcs)
    (by rw [hpar]; simp [e0]) hw hsat.2 (fun e he => (hsat.1 e he).1)
    (by rw [hal, i1, halloc]; rfl) (by rw [i3, haddr]; simp) [] (by rw [hcs, hal]; exact ⟨rfl, fun _ h => h⟩)
    (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · obtain ⟨t, ⟨hn', hv', hb', hp', htt, hl', hd'⟩, ks, he, -⟩ := hrel
    rw [hal] at he
    exact ⟨t, ⟨hn', hv', hb', hp', by rw [htt, hal, List.sum_nil, Nat.add_zero, Nat.add_zero], hl', hd'⟩,
      σ, ks, he, hsym⟩
  · rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    have hq' := B1.filterMap_of_loadsEv hni hq
    rw [hloads] at hq'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq'
    have he' := List.mem_range.mp he
    exact ⟨b + e, by rw [e0, limb0_gen_pow_mul], Or.inr (Or.inl (hreg e he'))⟩

/-! ## The row loop -/

/-- `da_verify_column_loop0`'s statements before its `ret`. -/
def l21P : List Stmt :=
  l21Pre ++ [.callIf (.n 17) name% «da_verify_column_loop0» (.n 19 :: (List.range 5).map fun k => V.n (k + 1))]

theorem l21_body_split : Fn.body (coreProgram.getD idx% «da_verify_column_loop0» default) = l21P ++ [.ret []] := by
  rw [dv_loops_body.2.2.2, l21P, List.append_assoc]
  rfl

theorem l21P_straight : l21P.all Main.Stmt.straight = true := rfl

theorem l21_loop : coreProgram.loop name% «da_verify_column_loop0» = true := by
  rw [Program.loop_of_find? find_l21]; decide +kernel

/-- An iteration's calls: the cell check, then the tail call, taken unless `i + 1 = r`. -/
def l21Calls (i r : ℕ) : List Call :=
  [⟨"da_verify_cell", [.n 2], [.n 6, .n 7, .n 8], true⟩] ++
    [⟨name% «da_verify_column_loop0», .n 19 :: (List.range 5).map fun k => V.n (k + 1), [], decide (i + 1 ≠ r)⟩]

/-- **An iteration's honest shape**: at the counter `g^i`, its cell check by a tree of `Tc`, its tail call by a tree
of `Tt`. -/
def l21NH (i r : ℕ) (Tc Tt : Tree → Prop) : Tree → Prop :=
  NodeHonest coreProgram name% «da_verify_column_loop0» (fun σ => σ (.n 0) = gen ^ i) (fun _ => l21Calls i r)
    (fun _ => []) [Tc, Tt]

/-- **`t` iterations from `i`**, the cell check of iteration `j` by a tree of `Tc j`. -/
def l21From (r : ℕ) (Tc : ℕ → Tree → Prop) : ℕ → ℕ → Tree → Prop
  | 0, _ => fun _ => False
  | t + 1, i => l21NH i r (Tc i) (l21From r Tc t (i + 1))

theorem gen_pow_add_ne {a b : ℕ} (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) :
    decide (gen ^ a + gen ^ b ≠ 0) = decide (a ≠ b) :=
  decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
    fun h he => h (gen_pow_inj' ha hb (e_add_eq_zero_iff.mp he))⟩

/-- **One iteration of the row loop, placed, its cell check holding the cell's symbols**: blob `i`'s cell in column
`h`, the weights at `g^lb`. -/
theorem l21_stepLF {r h lb bb bR : ℕ} {syms : ℕ → ℕ → List K} {z : E} {Lin : Layout} {i : ℕ} (hi : i + 1 ≤ r)
    (hr : r ≤ 1024) (hh : h < 128) (hsl : ∀ i j, (syms i j).length = 256)
    (hBm : (bb, blobsCells r syms z) ∈ Lin) (hRm : (bR, rowbaseCells r bb) ∈ Lin)
    (hws : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ lb) (colWs z h)) (hwr : ∀ e < 256, RegionL Lin (lb + e))
    {Tt : Tree → Prop}
    (htail : i + 1 < r → PlacedLF fs cert 16 name% «da_verify_column_loop0» Lin
      [gen ^ (i + 1), gen ^ r, gen ^ lb, gen ^ bR, gen ^ h, gen ^ h * gen ^ h] Tt) :
    PlacedLF fs cert 16 name% «da_verify_column_loop0» Lin [gen ^ i, gen ^ r, gen ^ lb, gen ^ bR, gen ^ h, gen ^ h * gen ^ h]
      (l21NH i r (cellNH (syms i h)) Tt) := by
  obtain ⟨Bt', hRest⟩ := placedLF_tail (fs := fs) (cert := cert) (g := name% «da_verify_column_loop0»)
    (last := i + 1 = r) fun h' => htail (by omega)
  have hcell := cell_placedF (fs := fs) (cert := cert) (Lin := Lin) (b := lb) (syms i h) (colWs z h) (hsl i h)
    (by simp [colWs]) hws hwr
  refine ⟨fs name% «da_verify_column_loop0» + Bt', fun fp cur hcur => ?_⟩
  obtain ⟨nc, hRc⟩ := hcell cur
  obtain ⟨nt, hlt, hRt⟩ := hRest (fp + fs name% «da_verify_column_loop0») (cur + nc) (by omega)
  refine ⟨nc + nt, fun rd hlow hm => ?_⟩
  have hc := hRc rd hlow hm
  have ht := hRt rd hlow hm
  have hB := reads_of_memL hm hBm
  have hR := reads_of_memL hm hRm
  have hi' : i < r := by omega
  obtain ⟨hl1, hl2⟩ := regionCells_leaf (syms := syms) (z := z) (i := i) hh
  have h1 := hbase hR hi'
  have h2 : LoadHolds rd (gen ^ (bb + 641 * i) * gen ^ h) 512 (runSum syms z i h) := by
    rw [loadHolds_mul_gen_pow]
    exact hreg hB hi' (by omega) (by rw [show h + 512 = 512 + h by ring, regionCells_sum (by omega)])
  have h3 : LoadHolds rd (gen ^ (bb + 641 * i) * gen ^ h) 513 (runSum syms z i h + cellDot syms z i h) := by
    rw [loadHolds_mul_gen_pow]
    exact hreg hB hi' (by omega) (by
      rw [show h + 513 = 512 + (h + 1) by ring, regionCells_sum (by omega), runSum_succ])
  have h4 : LoadHolds rd (gen ^ (bb + 641 * i) * (gen ^ h * gen ^ h)) 0 (digestHalves (cellD syms i h)).1 := by
    rw [← pow_add, loadHolds_mul_gen_pow]
    exact hreg hB hi' (by omega) (by rw [show h + h + 0 = 2 * h by ring, hl1])
  have h5 : LoadHolds rd (gen ^ (bb + 641 * i) * (gen ^ h * gen ^ h)) 1 (digestHalves (cellD syms i h)).2 := by
    rw [← pow_add, loadHolds_mul_gen_pow]
    exact hreg hB hi' (by omega) (by rw [show h + h + 1 = 2 * h + 1 by ring, hl2])
  -- the path
  set σ := Val.ofArgs [gen ^ i, gen ^ r, gen ^ lb, gen ^ bR, gen ^ h, gen ^ h * gen ^ h,
    (digestHalves (cellD syms i h)).1, (digestHalves (cellD syms i h)).2, cellDot syms z i h,
    gen ^ bR * gen ^ i, gen ^ (bb + 641 * i), gen ^ (bb + 641 * i) * gen ^ h, runSum syms z i h,
    runSum syms z i h + cellDot syms z i h, gen ^ (bb + 641 * i) * (gen ^ h * gen ^ h),
    word 2 0, gen ^ i * word 2 0, gen ^ i * word 2 0 + gen ^ r, word 2 0, gen ^ i * word 2 0] with hσ
  have hw' := Main.walk_straight σ [] l21P l21P_straight
  rw [← l21_body_split] at hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ l21P_straight
  have h17 : σ (.n 17) = gen ^ (i + 1) + gen ^ r := by
    show gen ^ i * word 2 0 + gen ^ r = _
    rw [word_gen, gen_pow_mul_gen]
  have htk : decide (σ (.n 17) ≠ 0) = decide (i + 1 ≠ r) := by
    rw [h17]; exact gen_pow_add_ne (by omega) (by omega)
  have hcalls : calls (l21P.flatMap (Main.slEvs σ)) = l21Calls i r := by
    rw [hpc, show l21P.filterMap Main.Stmt.callS =
      [(none, "da_verify_cell", [.n 2], [.n 6, .n 7, .n 8]),
        (some (.n 17), name% «da_verify_column_loop0», .n 19 :: (List.range 5).map fun k => V.n (k + 1), [])]
      from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, htk, l21Calls, List.cons_append, List.nil_append]
  have hal : allocs σ (l21P.flatMap (Main.slEvs σ)) = [] := by
    rw [hpa, show l21P.filterMap Main.Stmt.allocSz = [] from rfl]; rfl
  have hev : ∀ e ∈ l21P.flatMap (Main.slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun s hs => ?_
    simp only [l21P, l21Pre, stepAtC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [SlOk, Atom.Holds, hσ, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero]
    exacts [h1, h2, h3, h4, h5, by rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _]
  have hargs : (.n 19 :: (List.range 5).map fun k => V.n (k + 1)).map σ =
      [gen ^ (i + 1), gen ^ r, gen ^ lb, gen ^ bR, gen ^ h, gen ^ h * gen ^ h] := by
    show [gen ^ i * word 2 0, gen ^ r, gen ^ lb, gen ^ bR, gen ^ h, gen ^ h * gen ^ h] = _
    rw [word_gen, gen_pow_mul_gen]
  have hpar : (coreProgram.getD idx% «da_verify_column_loop0» default).params = (List.range 6).map V.n :=
    params_of_shape dv_loops_shape.2.2.2.1 dv_loops_shape.2.2.2.2
  have hreg' : ∀ {k : ℕ}, k < 641 * r → RegionL Lin (bb + k) := fun hk =>
    regionL_of_mem hBm (by rw [length_blobsCells]; exact hk)
  have hrel := relAtInWT_of_walk_loop (P := coreProgram) (Ts := [cellNH (syms i h)]) (Tt := Tt) (fs := fs)
    (cert := cert) (σ := σ) (rd := rd) (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False)
    (Rt := RegionL Lin) (Dt := RegionL []) (fp := fp) (c := cur) (Bt := Bt') (m := nt) (N := nc)
    (args := [gen ^ i, gen ^ r, gen ^ lb, gen ^ bR, gen ^ h, gen ^ h * gen ^ h]) coreProgram_wf find_l21 l21_loop
    (by rw [hpar]; rfl) hw' rfl hev (by rw [hcalls]; rfl)
    (by
      rw [hal, List.sum_nil, Nat.add_zero]
      by_cases hlast : i + 1 = r
      · simpa [hlast] using ht
      · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
        rw [hargs]; exact ht)
    (by rw [hal, hpd, show l21P.filterMap Main.Stmt.allocSz = [] from rfl]; rfl)
    (fun q hq => by
      rw [hpad, show l21P.filterMap Main.Stmt.addrS = [] from rfl] at hq
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
      rw [B1.loadAddrs_straight σ _ l21P_straight,
        show l21P.filterMap B1.Stmt.loadS = [(.n 9, 0), (.n 11, 512), (.n 11, 513), (.n 14, 0), (.n 14, 1)]
          from rfl] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl | rfl
      · refine ⟨bR + i, ?_, Or.inr (Or.inl (regionL_of_mem hRm (by simp [rowbaseCells]; omega)))⟩
        show (gen ^ bR * gen ^ i).limb 0 * addressOfIndex 0 = _
        rw [← pow_add, limb0_gen_pow_mul, Nat.add_zero]
      · refine ⟨bb + (641 * i + h + 512), ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ (bb + 641 * i) * gen ^ h).limb 0 * addressOfIndex 512 = _
        rw [← pow_add, limb0_gen_pow_mul]; ring_nf
      · refine ⟨bb + (641 * i + h + 513), ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ (bb + 641 * i) * gen ^ h).limb 0 * addressOfIndex 513 = _
        rw [← pow_add, limb0_gen_pow_mul]; ring_nf
      · refine ⟨bb + (641 * i + 2 * h), ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ (bb + 641 * i) * (gen ^ h * gen ^ h)).limb 0 * addressOfIndex 0 = _
        rw [← pow_add, ← pow_add, limb0_gen_pow_mul]; ring_nf
      · refine ⟨bb + (641 * i + 2 * h + 1), ?_, Or.inr (Or.inl (hreg' (by omega)))⟩
        show (gen ^ (bb + 641 * i) * (gen ^ h * gen ^ h)).limb 0 * addressOfIndex 1 = _
        rw [← pow_add, ← pow_add, limb0_gen_pow_mul]; ring_nf)
    (fun j hj => by obtain ⟨q, hq, -⟩ := hj; simp at hq)
  have h' := relAtInCT_nodeHonest (Q := fun σ => σ (.n 0) = gen ^ i)
    (cs := fun _ => l21Calls i r) (bs := fun _ => []) (Ts := [cellNH (syms i h), Tt]) hrel find_l21 hw' rfl
    (by rw [hcalls]) hal (by simp [l21Calls])
  rw [hal] at h'
  simp only [List.sum_nil, Nat.zero_add] at h'
  exact h'

/-- **The row loop, placed from its first iteration within its static bound**, its cell checks holding the cells'
symbols: column `h` of the `r` blobs, the weights at `g^lb`. -/
theorem row_completeAtTB {SK : String → ℕ}
    (h21 : TotalLeOn coreProgram fs name% «da_verify_column_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «da_verify_column_loop0» + fs name% «da_verify_column_loop0»))
    {r h lb bb bR : ℕ} {syms : ℕ → ℕ → List K} {z : E} {Lin : Layout} (hr1 : 1 ≤ r) (hr : r ≤ 1024)
    (hh : h < 128) (hsl : ∀ i j, (syms i j).length = 256)
    (hBm : (bb, blobsCells r syms z) ∈ Lin) (hRm : (bR, rowbaseCells r bb) ∈ Lin)
    (hws : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ lb) (colWs z h)) (hwr : ∀ e < 256, RegionL Lin (lb + e)) :
    CompleteAtDTB fs cert 16 name% «da_verify_column_loop0» Lin [1, gen ^ r, gen ^ lb, gen ^ bR, gen ^ h, gen ^ h * gen ^ h]
      (Returns []) (l21From r (fun j => cellNH (syms j h)) r 0)
      (r * iterK fs SK name% «da_verify_column_loop0» + fs name% «da_verify_column_loop0») := by
  have key : ∀ t i, i + t + 1 = r → PlacedLF fs cert 16 name% «da_verify_column_loop0» Lin
      [gen ^ i, gen ^ r, gen ^ lb, gen ^ bR, gen ^ h, gen ^ h * gen ^ h] (l21From r (fun j => cellNH (syms j h)) (t + 1) i) := by
    intro t
    induction t with
    | zero => exact fun i hi => l21_stepLF (by omega) hr hh hsl hBm hRm hws hwr fun h' => absurd h' (by omega)
    | succ t ih => exact fun i hi => l21_stepLF (by omega) hr hh hsl hBm hRm hws hwr fun _ => ih (i + 1) (by omega)
  have h0 := (key (r - 1) 0 (by omega)).toF
  rw [show r - 1 + 1 = r by omega, pow_zero] at h0
  have hm : r < 2 ^ 64 - 1 := by omega
  exact h0.toDTB fun rd t rets hn hv hb => by
    have := h21 rd t _ rets hn (loopPre_gen (by omega) hm _) hv hb
    simpa [logG_gen_pow hm] using this

/-- **A row loop whose cell checks hold `syms j h` pops them**, from iteration `i` to the last. -/
theorem l21_pops {rd : Reader} {r h : ℕ} {syms : ℕ → ℕ → List K} (hsl : ∀ i j, (syms i j).length = 256) :
    ∀ n i (t : Tree) (args rets : List E), i + n = r → l21From r (fun j => cellNH (syms j h)) n i t →
      t.Valid coreProgram rd args rets →
      t.pops coreProgram rd = (List.range' i n).flatMap fun j => [("da_symbols", (syms j h).map ofK)]
  | 0, _, _, _, _, _, ht, _ => ht.elim
  | n + 1, i, t, args, rets, hin, ht, hv => by
      obtain ⟨σ, ks, rfl, -, hc, -, hT⟩ := ht
      have hp := row_pops hv
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := id hv
      rw [find_l21] at hf
      cases hf
      rw [hc _ es vs find_l21 hw] at hkv
      obtain ⟨kc, kt, rfl⟩ : ∃ kc kt, ks = [kc, kt] := by
        match ks, kidsValid_len hkv with
        | [kc, kt], _ => exact ⟨kc, kt, rfl⟩
      obtain ⟨-, vc, -, vt, -⟩ := hkv
      obtain ⟨tc, tt, -⟩ := hT
      rw [hp]
      simp only [Memory.Tree.popsKids, List.flatten_cons, List.flatten_nil, List.append_nil]
      replace vc : kc.Valid coreProgram rd _ _ := vc
      rw [cellNH_pops (hsl i h) (tc rfl) vc, List.range'_succ, List.flatMap_cons]
      by_cases hlast : i + 1 = r
      · have hn : n = 0 := by omega
        subst hn
        rw [ite_eq_right (by simp [hlast])] at vt
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := vt
        simp [Memory.Tree.pops]
      · rw [ite_eq_left (by simp [hlast])] at vt
        rw [l21_pops hsl n (i + 1) kt _ _ (by omega) (tt (by simp [hlast])) vt]

end
end LeanVM.Guest.B1.Da
