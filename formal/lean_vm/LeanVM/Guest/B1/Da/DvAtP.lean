/-
  LeanVM.Guest.B1.Da.DvAtP

  `da_verify` placed on a witness by trees that pop the honest hints: its columns' row loops by trees whose cell checks
  hold the witness's symbols (`row_completeAtTB`), so every valid instance of the tree pops the shape, the challenge
  and the cells' symbols column by column.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.RowAtP

/-!
# `da_verify`, popping its hints

* `colPops r syms j`: column `j`'s entries; `colNHP r syms`: a column of honest shape whose valid instances at column
  `j` pop them; `colNHP_of_T`: column `h`'s tree whose row loop's cell checks hold `syms i h` is one.
* `daPopsW z w`: the check's entries on a witness; `da_verify_completeAtTBP`: `da_verify` complete within `dvB` by
  trees of its honest shape whose valid instances pop them.
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

/-- Column `j`'s entries: each blob's cell `j`. -/
def colPops (r : ℕ) (syms : ℕ → ℕ → List K) (j : ℕ) : List Pop :=
  (List.range' 0 r).flatMap fun i => [("da_symbols", (syms i j).map ofK)]

/-- **A column of honest shape popping its cells' symbols** at every valid instance of it at column `j`. -/
def colNHP (r : ℕ) (syms : ℕ → ℕ → List K) (tc : Tree) : Prop :=
  colNH r tc ∧ ∀ (rd : Reader) (j : ℕ) (args rets : List E), tc.Valid coreProgram rd args rets →
    args.head? = some (gen ^ j) → j < 128 → tc.pops coreProgram rd = colPops r syms j

theorem col_params_head : (fn% «da_verify_column»).params.head? = some (.n 0) := by decide +kernel

/-- **Column `h`'s tree, its row loop's cell checks holding `syms i h`, pops them.** -/
theorem colNHP_of_T {r h : ℕ} {syms : ℕ → ℕ → List K} (hr1 : 1 ≤ r) (hr : r ≤ 1024) (hh : h < 128)
    (hsl : ∀ i j, (syms i j).length = 256) {tc : Tree}
    (ht : colNHT r h (l21From r (fun j => cellNH (syms j h)) r 0) tc) : colNHP r syms tc := by
  refine ⟨colNH_of_T ht, fun rd j args rets hv hj hj128 => ?_⟩
  obtain ⟨σ', bufs', kx, kr, he, hpops⟩ := col_pops (colNH_of_T ht) hv
  obtain ⟨σ, ks, rfl, ⟨-, s0, s16⟩, hc, -, hT⟩ := ht
  obtain ⟨-, rfl, -, rfl⟩ := Memory.Tree.node.inj he
  obtain ⟨fn, hf, hp, es, vs, hw, -, -, hkv⟩ := id hv
  rw [find_da_verify_column] at hf
  cases hf
  have hjh : j = h := by
    have e : args.head? = some (σ (.n 0)) := by rw [← hp, List.head?_map, col_params_head]; rfl
    rw [e, s0, Option.some.injEq] at hj
    exact gen_pow_inj' (by omega) (by omega) hj.symm
  subst hjh
  rw [hc _ es vs find_da_verify_column hw, col_flatCalls] at hkv
  rw [col_flatCalls] at hT
  obtain ⟨-, -, -, vr, -⟩ := hkv
  obtain ⟨-, tr, -⟩ := hT
  have hne : (1 : E) + gen ^ r ≠ 0 := Digest.one_add_gen_pow_ne_zero (by omega) (by unfold ordG; omega)
  rw [ite_eq_left (by simp [Main.mkCall, s16, hne])] at vr
  rw [hpops, colPops, l21_pops hsl r 0 kr _ _ (by omega) (tr (by simp [Main.mkCall, s16, hne])) vr]

theorem l18From_mono {Tc Tc' : Tree → Prop} (h : ∀ t, Tc t → Tc' t) :
    ∀ n k t, l18From Tc n k t → l18From Tc' n k t
  | 0, _, _, ht => ht
  | n + 1, k, _, ht => nodeHonest_mono ht (.cons h (.cons (l18From_mono h n (k + 1)) .nil))

/-- The check's entries on a witness `w`, its challenge `z`: its shape, its challenge, its columns' cells. -/
def daPopsW (z : E) (w : LeanVM.Da.MatrixWitness) : List Pop :=
  ("da_shape", [gen ^ w.rows.length, gen ^ wLog w]) :: ("da_challenge", [z]) :: (List.range 128).flatMap (daColPops w)

theorem colPops_wSyms (w : LeanVM.Da.MatrixWitness) (j : ℕ) : colPops w.rows.length (wSyms w) j = daColPops w j := by
  rw [colPops, daColPops, ← List.range_eq_range']
  exact List.map_eq_flatMap.symm

variable {fs SB SK : String → ℕ} (cert : String → V → ℕ)

/-- **`da_verify` is complete, placed, on a witness opening `(root, z)`, by a tree of its honest shape whose valid
instances pop its hints**, within `dvB`. -/
theorem da_verify_completeAtTBP (hrf : Lift.RunsFit fs cert) {w : LeanVM.Da.MatrixWitness}
    {root : LeanVM.Protocol.Digest} {z : E} (hw : w.Opens root z) (s : ℕ) (hS : DvStaticB fs SB SK) :
    CompleteAtDTB fs cert 16 "da_verify" [(s + wLog w, [gen ^ 2 ^ wLog w])] [gen ^ s]
      (Returns (digestCells root ++ [z]))
      (fun t => dvNH w.rows.length (wLog w) t ∧ ∀ (rd : Reader) (args rets : List E),
        t.Valid coreProgram rd args rets → t.pops coreProgram rd = daPopsW z w)
      (dvB fs SB SK w.rows.length (wLog w)) := by
  have hr1 := hw.1
  have hr : w.rows.length ≤ 1024 := hw.2.1
  have hL : 2 ^ wLog w = LeanDa.paddedRowCount w.rows.length := rfl
  have hL10 : wLog w ≤ 10 := by
    obtain ⟨-, hhi⟩ := nPad_bounds hr1
    have hlt : 2 ^ wLog w < 2 ^ 11 := by
      calc 2 ^ wLog w < 2 * w.rows.length := hL ▸ hhi
        _ ≤ 2 ^ 11 := by norm_num; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  have hsl := wSyms_len hw
  rw [opens_eq hw]
  refine (dv_completeAtB_zC fs cert hrf hS.off hS.l17 hS.l19 hS.l20
    (by rw [← dlNames_bang hL10]; exact hS.dl _ hL10) hr1 hw.2.1 hL (wDot hw) s
    (Tc := colNHP w.rows.length (wSyms w)) fun bz bt bc bo bb k hk => ?_).mono ?_ fun t ht => ⟨dvNH_of_z (z := z) ?_, ?_⟩
  · refine (col_completeAtBT fs cert hrf hr1 hr hk fun c => row_completeAtTB (cert := cert) hS.l21 hr1 hr hk hsl
      List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
      (fun rd hm => colRun_reads hm z k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      fun e he => ?_).mono le_rfl fun _ h => colNHP_of_T hr1 hr hk hsl h
    have := regionL_of_mem (L := [(bb, blobsCells w.rows.length (wSyms w) z),
      (bb + 641 * w.rows.length, rowbaseCells w.rows.length bb), (c, colRun z k)]) (b := c) (xs := colRun z k) (k := 256 + e)
      (by simp) (by rw [length_colRun]; omega)
    rwa [← Nat.add_assoc] at this
  · have := dvBs_le hS (r := w.rows.length) hL10
    unfold dvB
    omega
  · obtain ⟨σ, ks, e, hQ, hc, hl, hk⟩ := ht
    exact ⟨σ, ks, e, hQ, hc, hl.trans (le_of_eq (by simp [dvTsC, dvTs])), kidsT_mono _ (dvTsC _) (dvTs _) _
      (.cons (fun _ h => h) (.cons (fun _ h => h) (.cons (fun _ h => h) (.cons (l18From_mono (fun _ h => h.1) 128 0)
        (.cons (fun _ h => h) (.cons (fun _ h => h) (.cons (fun _ h => h) .nil))))))) hk⟩
  · intro rd args rets hv
    obtain ⟨k3, args3, v3, t3, e⟩ := dv_pops hL10 ht hv
    rw [e, l18_pops (fun j tc args' rets' htc hv' hj hj' => htc.2 rd j args' rets' hv' hj hj') 128 0 k3 args3 [] rfl
      t3 v3, daPopsW, ← List.range_eq_range', funext (colPops_wSyms w)]

end
end LeanVM.Guest.B1.Da
