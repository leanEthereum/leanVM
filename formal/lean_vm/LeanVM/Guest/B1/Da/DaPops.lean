/-
  LeanVM.Guest.B1.Da.DaPops

  The witness-stream entries LeanDA's blob matrix check pops (`da_verify` and its callees, `lean_ethereum.py:4509-4591`) are the honest hint generator's (`Hints.daHints`), stream by stream, given what each column pops.
-/

module

public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.B1.Da.WitnessAtTB
public import LeanVM.Guest.B1.Da.CellComplete
public import LeanVM.Guest.B1.Da.DaMuteChk
public import LeanVM.Guest.Hints

/-!
# LeanDA's pops

`da_verify` pops its shape (`da_shape`) and its challenge (`da_challenge`), each cell check its `256` symbols (`da_symbols`); nothing else in its call tree pops.

* `kid_pops_mute`: every other callee of the check pops nothing, having no witness hint in its subtree (`noWitS`, `noWitS_of_callee`, `DaMuteChk`);
* `cell_pops`, `da_verify_cell_complete_pops`: a cell check pops the symbols its valuation holds, the honest ones on the completing valuation;
* `row_pops`, `col_pops`: an iteration of the row loop pops its cell's entries, then the next iteration's; a column pops its row loop's;
* `l18_pops`: the column loop pops its columns' entries in order;
* `dv_pops`: `da_verify` of honest shape pops its shape, its challenge, then its columns';
* `daPops_sameStreams`: those are `daHints`', stream by stream;
* `daHeapSizes_bufs`: the advised `HeapBuf` sizes are the honest tree's regions' and roots' buffers;
* `da_verify_complete_pops`: `da_verify` is complete by trees of honest shape exposing the hinted words (`dvNHz`), and such a tree whose columns pop their cells' honest symbols pops `daHints c w`, stream by stream.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Returns flatCalls)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Main (Layout MemL RegionL iterK)

@[expose] public section

theorem mkCall_f (σ : Val) (o : Option V) (f : String) (args rets : List V) : (Main.mkCall σ (o, f, args, rets)).f = f := by
  cases o <;> rfl

/-- A callee with no witness hint in its subtree pops nothing. -/
theorem kid_pops_mute {rd : Reader} {σ : Val} {c : Call} {k : Memory.Tree}
    (hk : if c.taken then k.Valid coreProgram rd (c.args.map σ) (c.rets.map σ)
      else (∃ f σ', k = .phantom f σ') ∧ Phantom coreProgram k (c.args.map σ))
    (hn : k.name = c.f) (hs : noWitS c.f = true) : k.pops coreProgram rd = [] := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at hk
    exact Tree.pops_mute noWitS_mute k hk (by rw [hn]; exact hs)
  · rw [ite_eq_right ht] at hk
    obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
    rw [Tree.pops]

/-! ## The cell check -/

/-- `da_verify_cell` pops its symbols first, then nothing, calling nothing. -/
noncomputable def cellShapeOk : Bool :=
  stmtsEqb ((Fn.body fn% «da_verify_cell»).take 1) [.atom symHint] &&
    Stmt.muteList (fun _ => false) ((Fn.body fn% «da_verify_cell»).drop 1)

theorem cell_shape_ok : cellShapeOk = true := by decide +kernel

/-- The entry of the cell check's hint on `σ`. -/
def cellPop (σ : Val) : Pop := ("da_symbols", (List.range 256).map fun j => σ (.n (j + 1)))

/-- **A cell check pops the symbols its valuation holds.** -/
theorem cell_pops {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E}
    (hv : (Memory.Tree.node "da_verify_cell" σ bufs kids).Valid coreProgram rd args rets) :
    (Memory.Tree.node "da_verify_cell" σ bufs kids).pops coreProgram rd = [cellPop σ] := by
  have h := cell_shape_ok
  simp only [cellShapeOk, Bool.and_eq_true] at h
  have hb : Fn.body fn% «da_verify_cell» = [.atom symHint] ++ (Fn.body fn% «da_verify_cell»).drop 1 := by
    rw [← stmtsEqb_sound h.1, List.take_append_drop]
  have ha : symHint.pops rd σ = [cellPop σ] := by simp [symHint, Atom.pops, Hint.pops, Dest.words, cellPop]
  have hx := FallPops.atom (rd := rd) (σ := σ) symHint
  rw [ha] at hx
  exact Tree.pops_of_prefix_leaf hv find_da_verify_cell hb hx h.2

/-- **`da_verify_cell` is complete, popping its symbols**: `da_verify_cell_complete_vals`'s valuation, and every valid call instance of it on that valuation pops `syms`. -/
theorem da_verify_cell_complete_pops (rd : Reader) (lv : E) (syms : List K) (ws : List E)
    (hsl : syms.length = LeanDa.cellSymbols) (hwl : ws.length = LeanDa.cellSymbols) (hreads : ReadsAt rd lv ws) :
    ∃ σ : Val, σ (.n 0) = lv ∧ (∀ C : CallRel,
      Stmt.HoldsList C rd σ (Fn.body fn% «da_verify_cell») False (fun rs => rs = cellRets syms ws)) ∧
      ∀ (bufs : List ℕ) (kids : List Memory.Tree) (args rets : List E),
        (Memory.Tree.node "da_verify_cell" σ bufs kids).Valid coreProgram rd args rets →
        (Memory.Tree.node "da_verify_cell" σ bufs kids).pops coreProgram rd = [("da_symbols", syms.map ofK)] := by
  obtain ⟨σ, e0, hs, h⟩ := da_verify_cell_complete_vals rd lv syms ws hsl hwl hreads
  refine ⟨σ, e0, h, fun bufs kids args rets hv => ?_⟩
  rw [cell_pops hv, cellPop]
  simp only [LeanDa.cellSymbols] at hsl
  refine congrArg (fun l => [(("da_symbols" : String), l)]) (List.ext_getElem (by simp [hsl]) fun j h1 h2 => ?_)
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  rw [hs j h1, List.getD_eq_getElem _ _ (by omega)]

/-! ## The loops and the column -/

theorem l18_body_mute : Stmt.muteList (fun _ => true) l18Body = true := by decide +kernel

theorem col_body_mute : Stmt.muteList (fun _ => true) (Fn.body fn% «da_verify_column») = true := by
  decide +kernel

theorem row_body_mute : Stmt.muteList (fun _ => true)
    (coreProgram.getD idx% «da_verify_column_loop0» default).body = true := by decide +kernel

theorem splicePops_nil (rd : Reader) (σ : Val) : SplicePops rd σ [] [] [] := ⟨[], rfl, rfl, rfl⟩

/-- **An iteration of the row loop pops its callees' entries**: its cell's, then the next iteration's. -/
theorem row_pops {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E}
    (hv : (Memory.Tree.node name% «da_verify_column_loop0» σ bufs kids).Valid coreProgram rd args rets) :
    (Memory.Tree.node name% «da_verify_column_loop0» σ bufs kids).pops coreProgram rd =
      (Memory.Tree.popsKids coreProgram rd kids).flatten := by
  rw [Tree.pops_of_prefix hv find_l21 (List.nil_append _).symm (splicePops_nil rd σ) row_body_mute rfl,
    List.nil_append]

/-- **A column of honest shape pops its row loop's entries.** -/
theorem col_pops {rd : Reader} {r : ℕ} {t : Memory.Tree} {args rets : List E} (ht : colNH r t)
    (hv : t.Valid coreProgram rd args rets) :
    ∃ σ bufs kx kr, t = .node "da_verify_column" σ bufs [kx, kr] ∧ t.pops coreProgram rd = kr.pops coreProgram rd := by
  obtain ⟨σ, ks, rfl, -, hc, -, -⟩ := ht
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := id hv
  rw [find_da_verify_column] at hf
  cases hf
  rw [hc _ es vs find_da_verify_column hw, col_flatCalls] at hkv
  obtain ⟨kx, kr, rfl⟩ : ∃ kx kr, ks = [kx, kr] := by
    match ks, kidsValid_len hkv with
    | [kx, kr], _ => exact ⟨kx, kr, rfl⟩
  obtain ⟨nx, vx, -, -, -⟩ := hkv
  refine ⟨σ, [], kx, kr, rfl, ?_⟩
  rw [Tree.pops_of_prefix hv find_da_verify_column (List.nil_append _).symm (splicePops_nil rd σ) col_body_mute rfl,
    kid_pops_mute vx nx (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify_column») (by decide +kernel))]
  simp [Memory.Tree.popsKids]

/-- **The column loop pops its columns' entries in order**, from iteration `k` to the last, when a column `j` of shape `Tc` pops `K j`. -/
theorem l18_pops {rd : Reader} {Tc : Memory.Tree → Prop} {K : ℕ → List Pop}
    (hK : ∀ j tc args rets, Tc tc → tc.Valid coreProgram rd args rets → args.head? = some (gen ^ j) → j < 128 →
      tc.pops coreProgram rd = K j) :
    ∀ n k (t : Memory.Tree) (args rets : List E), k + n = 128 → l18From Tc n k t →
      t.Valid coreProgram rd args rets → t.pops coreProgram rd = (List.range' k n).flatMap K
  | 0, _, _, _, _, _, h, _ => h.elim
  | n + 1, k, t, args, rets, hkn, ht, hv => by
      obtain ⟨σ, ks, rfl, hQ, hc, -, hT⟩ := ht
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := id hv
      rw [find_l18] at hf
      cases hf
      rw [hc _ es vs find_l18 hw] at hkv
      obtain ⟨kc, kt, rfl⟩ : ∃ kc kt, ks = [kc, kt] := by
        match ks, kidsValid_len hkv with
        | [kc, kt], _ => exact ⟨kc, kt, rfl⟩
      obtain ⟨-, vc, -, vt, -⟩ := hkv
      obtain ⟨tc, tt, -⟩ := hT
      rw [Tree.pops_of_prefix hv find_l18 (List.nil_append _).symm (splicePops_nil rd σ)
        (by rw [l18_body]; exact l18_body_mute) rfl]
      simp only [Memory.Tree.popsKids, List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append]
      replace vc : kc.Valid coreProgram rd _ _ := vc
      have hcK := hK k kc _ _ (tc rfl) vc (by show some (σ (.n 0)) = _; rw [hQ]) (by omega)
      rw [hcK, List.range'_succ, List.flatMap_cons]
      by_cases hlast : k + 1 = 128
      · have hn : n = 0 := by omega
        subst hn
        rw [ite_eq_right (by simp [hlast])] at vt
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := vt
        simp [Memory.Tree.pops]
      · rw [ite_eq_left (by simp [hlast])] at vt
        rw [l18_pops hK n (k + 1) kt _ _ (by omega) (tt (by simp [hlast])) vt]

/-! ## `da_verify` -/

/-- `da_verify`'s first statements: its shape's hint, the row shape, its challenge's hint. -/
def dvHead : List Stmt :=
  [.atom (.hint (.witness "da_shape" (.stack [.n 1, .n 2]))), .call "da_row_shape" [.n 1, .n 2, .n 0] [.n 3, .n 4],
    .atom (.hint (.witness "da_challenge" (.stack [.n 5])))]

/-- `da_verify` starts with `dvHead`, then pops nothing itself. -/
noncomputable def dvShapeOk : Bool :=
  stmtsEqb ((Fn.body fn% «da_verify»).take 3) dvHead && Stmt.muteList (fun _ => true) ((Fn.body fn% «da_verify»).drop 3)

theorem dv_shape_ok : dvShapeOk = true := by decide +kernel

theorem dvHead_pops (rd : Reader) (σ : Val) (k : List Pop) :
    SplicePops rd σ dvHead [k] (("da_shape", [σ (.n 1), σ (.n 2)]) :: (k ++ [("da_challenge", [σ (.n 5)])])) := by
  have h := (SplicePops.of_fallPops (rd := rd) (σ := σ)
    (FallPops.atom (.hint (.witness "da_shape" (.stack [.n 1, .n 2]))))).append
    ((SplicePops.call (rd := rd) (σ := σ) "da_row_shape" [.n 1, .n 2, .n 0] [.n 3, .n 4] k).append
      (SplicePops.of_fallPops (FallPops.atom (.hint (.witness "da_challenge" (.stack [.n 5]))))))
  simpa [dvHead, Atom.pops, Hint.pops, Dest.words] using h

/-- **`da_verify` of honest shape pops its shape and its challenge, then its column loop's entries.** -/
theorem dv_pops {rd : Reader} {r L : ℕ} {z : E} (hL : L ≤ 10) {t : Memory.Tree} {args rets : List E}
    (ht : dvNHz r L z t) (hv : t.Valid coreProgram rd args rets) :
    ∃ k3 args3, k3.Valid coreProgram rd args3 [] ∧ l18From (colNH r) 128 0 k3 ∧
      t.pops coreProgram rd = ("da_shape", [gen ^ r, gen ^ L]) :: ("da_challenge", [z]) :: k3.pops coreProgram rd := by
  obtain ⟨σ, ks, rfl, ⟨⟨s1, s2, -⟩, s5⟩, hc, -, hT⟩ := ht
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := id hv
  rw [find_da_verify] at hf
  cases hf
  have hlogL : logG (σ (.n 2)) = L := by rw [s2]; exact logG_gen_pow (by omega)
  rw [hc _ es vs find_da_verify hw, dv_flatCalls, hlogL] at hkv
  rw [dv_flatCalls, hlogL] at hT
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, rfl⟩ : ∃ k0 k1 k2 k3 k4 k5 k6, ks = [k0, k1, k2, k3, k4, k5, k6] := by
    match ks, kidsValid_len hkv with
    | [k0, k1, k2, k3, k4, k5, k6], _ => exact ⟨k0, k1, k2, k3, k4, k5, k6, rfl⟩
  obtain ⟨n0, v0, n1, v1, n2, v2, -, v3, n4, v4, n5, v5, n6, v6, -⟩ := hkv
  obtain ⟨-, -, -, t3, -⟩ := hT
  have e0 := kid_pops_mute v0 n0 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e1 := kid_pops_mute v1 n1 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e2 := kid_pops_mute v2 n2 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e4 := kid_pops_mute v4 n4 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e5 := kid_pops_mute v5 n5 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e6 := kid_pops_mute v6 n6 (by rw [mkCall_f, dlList_getD hL]; exact daLevels_noWit hL)
  have h := dv_shape_ok
  simp only [dvShapeOk, Bool.and_eq_true] at h
  have hb : Fn.body fn% «da_verify» = dvHead ++ (Fn.body fn% «da_verify»).drop 3 := by
    rw [← stmtsEqb_sound h.1, List.take_append_drop]
  replace v3 : k3.Valid coreProgram rd _ _ := v3
  refine ⟨k3, _, v3, t3 rfl, ?_⟩
  rw [Tree.pops_of_prefix hv find_da_verify hb (dvHead_pops rd σ (k0.pops coreProgram rd)) h.2 rfl, s1, s2, s5]
  simp [Memory.Tree.popsKids, e0, e1, e2, e4, e5, e6]

/-! ## Against the hints -/

/-- Column `h`'s entries: each row's cell `h`. -/
def daColPops (w : LeanVM.Da.MatrixWitness) (h : ℕ) : List Pop :=
  (List.range w.rows.length).map fun i => ("da_symbols", (wSyms w i h).map ofK)

theorem count_gen {n : ℕ} (h : n ≤ 1024) : Hints.count n = gen ^ n := by
  rw [Hints.count, gpowE, gpowK_eq (by unfold u128Bound; omega), gen_pow_eq_ofK]

/-- **The check's entries are `daHints`'**, stream by stream. -/
theorem daPops_sameStreams (c : LeanVM.Node.DaClaim) (w : LeanVM.Da.MatrixWitness) (hr : w.rows.length ≤ 1024)
    (hL : wLog w ≤ 10) :
    SameStreams (("da_shape", [gen ^ w.rows.length, gen ^ wLog w]) :: ("da_challenge", [c.membershipChallenge]) ::
      (List.range 128).flatMap (daColPops w)) (Hints.daHints c w) := by
  have e3 : (List.range LeanDa.cellsPerRow).flatMap (fun j => w.rows.map fun row =>
      (("da_symbols" : String), (LeanDa.listCell row j).map ofK)) = (List.range 128).flatMap (daColPops w) := by
    refine List.flatMap_congr fun j hj => List.ext_getElem (by simp [daColPops]) fun i h1 h2 => ?_
    have hj' : j < 128 := List.mem_range.mp hj
    simp only [List.length_map] at h1
    simp only [daColPops, List.getElem_map, List.getElem_range]
    rw [wSyms, ite_eq_left ⟨h1, hj'⟩, List.getD_eq_getElem _ _ h1]
  rw [Hints.daHints, count_gen hr, show LeanDa.logPaddedRowCount w.rows.length = wLog w from rfl, count_gen (by omega),
    e3]
  exact (sameStreams_append_comm (a := [("da_shape", [gen ^ w.rows.length, gen ^ wLog w])])
    (b := [("da_challenge", [c.membershipChallenge])]) (by simp)).append (SameStreams.refl _)

/-! ## The advised sizes -/

/-- **`da_verify`'s advised `HeapBuf` sizes** (`heap_sizes`, popped by the executor's `allocAdvice`, not by a `hint_witness`) are its honest tree's first and last buffers: the regions and the roots' tree. -/
theorem daHeapSizes_bufs {r L : ℕ} {z : E} {t : Memory.Tree} (ht : dvNHz r L z t) (hL : L = LeanDa.logPaddedRowCount r) :
    Hints.daHeapSizes r = [t.bufs.getD 0 0, t.bufs.getD 2 0] := by
  obtain ⟨σ, ks, rfl, -⟩ := ht
  subst hL
  simp [Hints.daHeapSizes, Memory.Tree.bufs, dvSizes, Nat.mul_comm]

variable {fs SB SK : String → ℕ} (cert : String → V → ℕ)

/-- **`da_verify` is complete, popping its hints**: for a witness opening `(root, z)`, `z` the claim's challenge, `da_verify` is complete by trees of its honest shape exposing its hinted words (`dvNHz`), and each such tree whose columns pop their cells' honest symbols (`daColPops`) pops `daHints c w`, stream by stream. -/
theorem da_verify_complete_pops (hrf : Lift.RunsFit fs cert) {w : LeanVM.Da.MatrixWitness} {c : LeanVM.Node.DaClaim}
    {root : LeanVM.Protocol.Digest} (hw : w.Opens root c.membershipChallenge) (s : ℕ) (hS : DvStaticB fs SB SK) :
    CompleteAtDTB fs cert 16 "da_verify" [(s + wLog w, [gen ^ 2 ^ wLog w])] [gen ^ s]
      (Returns (digestCells root ++ [c.membershipChallenge])) (dvNHz w.rows.length (wLog w) c.membershipChallenge)
      (dvB fs SB SK w.rows.length (wLog w)) ∧
    ∀ (rd : Reader) (t : Memory.Tree) (args rets : List E), dvNHz w.rows.length (wLog w) c.membershipChallenge t →
      t.Valid coreProgram rd args rets →
      (∀ h tc args' rets', colNH w.rows.length tc → tc.Valid coreProgram rd args' rets' →
        args'.head? = some (gen ^ h) → h < 128 → tc.pops coreProgram rd = daColPops w h) →
      SameStreams (t.pops coreProgram rd) (Hints.daHints c w) := by
  have hr1 := hw.1
  have hr : w.rows.length ≤ 1024 := hw.2.1
  have hL : 2 ^ wLog w = LeanDa.paddedRowCount w.rows.length := rfl
  have hL10 : wLog w ≤ 10 := by
    obtain ⟨hlo, hhi⟩ := nPad_bounds hr1
    have hlt : 2 ^ wLog w < 2 ^ 11 := by
      calc 2 ^ wLog w < 2 * w.rows.length := hL ▸ hhi
        _ ≤ 2 ^ 11 := by norm_num; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  refine ⟨?_, fun rd t args rets ht hv hK => ?_⟩
  · rw [opens_eq hw]
    refine (dv_completeAtB_z fs cert hrf hS.off hS.l17 hS.l19 hS.l20 hS.l21
      (by rw [← dlNames_bang hL10]; exact hS.dl _ hL10) hr1 hw.2.1 hL (wSyms_len hw) (wDot hw) s).mono ?_ fun _ h => h
    have := dvBs_le hS (r := w.rows.length) hL10
    unfold dvB
    omega
  · obtain ⟨k3, args3, v3, t3, e⟩ := dv_pops hL10 ht hv
    rw [e, l18_pops hK 128 0 k3 args3 [] rfl t3 v3]
    exact daPops_sameStreams c w hr hL10

end
end LeanVM.Guest.B1.Da
