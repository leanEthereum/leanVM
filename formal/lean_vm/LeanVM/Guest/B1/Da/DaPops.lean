/-
  LeanVM.Guest.B1.Da.DaPops

  The witness-stream entries LeanDA's blob matrix check pops (`da_verify` and its callees, `lean_ethereum.py:4516-4600`)
  are the honest hint generator's (`Hints.daHints`), stream by stream.

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.B1.Da.DvAt
public import LeanVM.Guest.B1.Da.CellPops
public import LeanVM.Guest.B1.Da.DaMuteChk
public import LeanVM.Guest.B1.Da.Witness
public import LeanVM.Guest.Hints

/-!
# LeanDA's pops

`da_verify` pops its shape (`da_shape`) and its challenge (`da_challenge`), each cell check its `256` symbols
(`da_symbols`); nothing else in its call tree pops (`kid_pops_mute`).

* `blob_pops`: a blob of honest shape pops its cells' symbols in order (`blobPops`);
* `blobL_pops`: the blob loop pops its blobs' entries in order;
* `dv_pops`: `da_verify` of honest shape pops its shape, its challenge, then its blob loop's entries;
* `daPops_sameStreams`: those are `daHints`', stream by stream (blob by blob, `daSymPops`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (CompleteAtDTB Returns flatCalls)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Main (Layout MemL RegionL iterK)

@[expose] public section

/-! ## A blob and the blob loop -/

theorem blob_body_mute : Stmt.muteList (fun _ => true) (Fn.body fn% «da_verify_blob») = true := by decide +kernel

theorem blobL_body_mute : Stmt.muteList (fun _ => true)
    (coreProgram.getD idx% «da_verify_loop0» default).body = true := by decide +kernel

/-- Blob `i`'s entries: its cells' symbols. -/
def blobPops (syms : ℕ → ℕ → List K) (i : ℕ) : List Pop :=
  (List.range 128).map fun h => ("da_symbols", (syms i h).map ofK)

/-- **A blob of honest shape pops its cells' symbols.** -/
theorem blob_pops {fs SB SK : String → ℕ} {rd : Reader} {syms : ℕ → ℕ → List K} {i : ℕ}
    (hsl : ∀ k, (syms i k).length = 256) {t : Memory.Tree} {args rets : List E} (ht : blobNH fs SB SK syms i t)
    (hv : t.Valid coreProgram rd args rets) : t.pops coreProgram rd = blobPops syms i := by
  obtain ⟨σ, ks, rfl, -, hc, -, hT⟩ := ht
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := id hv
  rw [find_da_verify_blob] at hf
  cases hf
  rw [hc _ es vs find_da_verify_blob hw, blob_flatCalls] at hkv
  rw [blob_flatCalls] at hT
  obtain ⟨kc, kl, rfl⟩ : ∃ kc kl, ks = [kc, kl] := by
    match ks, kidsValid_len hkv with
    | [kc, kl], _ => exact ⟨kc, kl, rfl⟩
  obtain ⟨-, vc, nl, vl, -⟩ := hkv
  obtain ⟨tc, -, -⟩ := hT
  have el := kid_pops_mute vl nl (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify_blob») (by decide +kernel))
  rw [Tree.pops_of_prefix hv find_da_verify_blob (List.nil_append _).symm (splicePops_nil rd σ) blob_body_mute rfl]
  simp only [Memory.Tree.popsKids, List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append, el]
  replace vc : kc.Valid coreProgram rd _ _ := vc
  rw [cellL_pops hsl 128 0 kc _ _ rfl (tc rfl).2 vc, blobPops, List.range_eq_range', List.map_eq_flatMap]

/-- **The blob loop pops its blobs' entries in order**, from iteration `i` to the last, when blob `j`'s tree of shape
`Tb j` pops `K j`. -/
theorem blobL_pops {rd : Reader} {r : ℕ} {Tb : ℕ → Memory.Tree → Prop} {K : ℕ → List Pop}
    (hK : ∀ j tc args rets, j < r → Tb j tc → tc.Valid coreProgram rd args rets → tc.pops coreProgram rd = K j) :
    ∀ n i (t : Memory.Tree) (args rets : List E), i + n = r → blobLFrom r Tb n i t →
      t.Valid coreProgram rd args rets → t.pops coreProgram rd = (List.range' i n).flatMap K
  | 0, _, _, _, _, _, h, _ => h.elim
  | n + 1, i, t, args, rets, hin, ht, hv => by
      obtain ⟨σ, ks, rfl, -, hc, -, hT⟩ := ht
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := id hv
      rw [find_blobL] at hf
      cases hf
      rw [hc _ es vs find_blobL hw] at hkv
      obtain ⟨kc, kt, rfl⟩ : ∃ kc kt, ks = [kc, kt] := by
        match ks, kidsValid_len hkv with
        | [kc, kt], _ => exact ⟨kc, kt, rfl⟩
      obtain ⟨-, vc, -, vt, -⟩ := hkv
      obtain ⟨tc, tt, -⟩ := hT
      rw [Tree.pops_of_prefix hv find_blobL (List.nil_append _).symm (splicePops_nil rd σ) blobL_body_mute rfl]
      simp only [Memory.Tree.popsKids, List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append]
      replace vc : kc.Valid coreProgram rd _ _ := vc
      rw [hK i kc _ _ (by omega) (tc rfl) vc, List.range'_succ, List.flatMap_cons]
      by_cases hlast : i + 1 = r
      · have hn : n = 0 := by omega
        subst hn
        rw [ite_eq_right (by simp [hlast])] at vt
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := vt
        simp [Memory.Tree.pops]
      · rw [ite_eq_left (by simp [hlast])] at vt
        rw [blobL_pops hK n (i + 1) kt _ _ (by omega) (tt (by simp [hlast])) vt]

/-! ## `da_verify` -/

/-- `da_verify`'s first statements: its shape's hint, the shape's range check, the row shape, its challenge's hint. -/
def dvHead : List Stmt :=
  [.atom (.hint (.witness "da_shape" (.stack [.n 1, .n 2]))), .atom (.const (.n 3) (word 1024 0)),
    .atom (.rangeCheck (.n 2) (.n 4) (.n 5) (.n 6) (.n 3)), .call "da_row_shape" [.n 1, .n 2, .n 0] [.n 7, .n 8],
    .atom (.hint (.witness "da_challenge" (.stack [.n 9])))]

/-- `da_verify` starts with `dvHead`, then pops nothing itself. -/
noncomputable def dvShapeOk : Bool :=
  stmtsEqb ((Fn.body fn% «da_verify»).take 5) dvHead && Stmt.muteList (fun _ => true) ((Fn.body fn% «da_verify»).drop 5)

theorem dv_shape_ok : dvShapeOk = true := by decide +kernel

theorem dvHead_pops (rd : Reader) (σ : Val) (k : List Pop) :
    SplicePops rd σ dvHead [k] (("da_shape", [σ (.n 1), σ (.n 2)]) :: (k ++ [("da_challenge", [σ (.n 9)])])) := by
  have h := (SplicePops.of_fallPops (rd := rd) (σ := σ)
    (FallPops.atom (.hint (.witness "da_shape" (.stack [.n 1, .n 2]))))).append
    ((SplicePops.of_fallPops (FallPops.atom (.const (.n 3) (word 1024 0)))).append
    ((SplicePops.of_fallPops (FallPops.atom (.rangeCheck (.n 2) (.n 4) (.n 5) (.n 6) (.n 3)))).append
    ((SplicePops.call (rd := rd) (σ := σ) "da_row_shape" [.n 1, .n 2, .n 0] [.n 7, .n 8] k).append
      (SplicePops.of_fallPops (FallPops.atom (.hint (.witness "da_challenge" (.stack [.n 9]))))))))
  simpa [dvHead, Atom.pops, Hint.pops, Dest.words] using h

/-- **`da_verify` of honest shape pops its shape and its challenge, then its blob loop's entries.** -/
theorem dv_pops {rd : Reader} {r L : ℕ} {z : E} {Tb : Memory.Tree → Prop} (hr1 : 1 ≤ r) (hr : r ≤ 1024)
    (hL : L ≤ 10) {t : Memory.Tree} {args rets : List E} (ht : dvNHzC r L z Tb t)
    (hv : t.Valid coreProgram rd args rets) :
    ∃ k3 args3, k3.Valid coreProgram rd args3 [] ∧ Tb k3 ∧
      t.pops coreProgram rd = ("da_shape", [gen ^ r, gen ^ L]) :: ("da_challenge", [z]) :: k3.pops coreProgram rd := by
  obtain ⟨σ, ks, rfl, ⟨⟨s1, s2, -, s19, -⟩, s9⟩, hc, -, hT⟩ := ht
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := id hv
  rw [find_da_verify] at hf
  cases hf
  have hlogL : logG (σ (.n 2)) = L := by rw [s2]; exact logG_gen_pow (by omega)
  rw [hc _ es vs find_da_verify hw, dv_flatCalls, hlogL] at hkv
  rw [dv_flatCalls, hlogL] at hT
  obtain ⟨k0, k1, k2, k3, k4, rfl⟩ : ∃ k0 k1 k2 k3 k4, ks = [k0, k1, k2, k3, k4] := by
    match ks, kidsValid_len hkv with
    | [k0, k1, k2, k3, k4], _ => exact ⟨k0, k1, k2, k3, k4, rfl⟩
  obtain ⟨n0, v0, n1, v1, n2, v2, -, v3, n4, v4, -⟩ := hkv
  obtain ⟨-, -, -, t3, -⟩ := hT
  have hne : (1 : E) + gen ^ r ≠ 0 := one_add_gen_pow_ne_zero (by omega) (by unfold ordG; omega)
  have htk : (Main.mkCall σ (some (.n 19), name% «da_verify_loop0», [.n 20, .n 1, .n 14, .n 17], [])).taken = true := by
    simp [Main.mkCall, s19, hne]
  have e0 := kid_pops_mute v0 n0 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e1 := kid_pops_mute v1 n1 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e2 := kid_pops_mute v2 n2 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e4 := kid_pops_mute v4 n4 (by rw [mkCall_f]; exact rt_noWitS hL)
  have h := dv_shape_ok
  simp only [dvShapeOk, Bool.and_eq_true] at h
  have hb : Fn.body fn% «da_verify» = dvHead ++ (Fn.body fn% «da_verify»).drop 5 := by
    rw [← stmtsEqb_sound h.1, List.take_append_drop]
  rw [ite_eq_left htk] at v3
  replace v3 : k3.Valid coreProgram rd _ _ := v3
  refine ⟨k3, _, v3, t3 htk, ?_⟩
  rw [Tree.pops_of_prefix hv find_da_verify hb (dvHead_pops rd σ (k0.pops coreProgram rd)) h.2 rfl, s1, s2, s9]
  simp [Memory.Tree.popsKids, e0, e1, e2, e4]

/-! ## Against the hints -/

/-- The cells' entries on a witness, blob by blob. -/
def daSymPops (w : LeanVM.Da.MatrixWitness) : List Pop := (List.range w.rows.length).flatMap (blobPops (wSyms w))

theorem flatMap_eq_range {α β : Type} (d : α) (f : α → List β) :
    ∀ l : List α, l.flatMap f = (List.range l.length).flatMap fun i => f (l.getD i d)
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, flatMap_eq_range d f l, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp

theorem count_gen {n : ℕ} (h : n ≤ 1024) : Hints.count n = gen ^ n := by
  rw [Hints.count, gpowE, gpowK_eq (by unfold u128Bound; omega), gen_pow_eq_ofK]

/-- **The check's entries are `daHints`'**, stream by stream. -/
theorem daPops_sameStreams (c : LeanVM.Node.DaClaim) (w : LeanVM.Da.MatrixWitness) (hr : w.rows.length ≤ 1024)
    (hL : wLog w ≤ 10) :
    SameStreams (("da_shape", [gen ^ w.rows.length, gen ^ wLog w]) :: ("da_challenge", [c.membershipChallenge]) ::
      daSymPops w) (Hints.daHints c w) := by
  have e3 : w.rows.flatMap (fun row => (List.range LeanDa.cellsPerRow).map fun j =>
      (("da_symbols" : String), (LeanDa.listCell row j).map ofK)) = daSymPops w := by
    rw [flatMap_eq_range [] _ w.rows, daSymPops]
    refine List.flatMap_congr fun i hi => List.map_congr_left fun j hj => ?_
    rw [wSyms, ite_eq_left ⟨List.mem_range.mp hi, List.mem_range.mp hj⟩]
  rw [Hints.daHints, count_gen hr, show LeanDa.logPaddedRowCount w.rows.length = wLog w from rfl, count_gen (by omega),
    e3]
  exact (sameStreams_append_comm (a := [("da_shape", [gen ^ w.rows.length, gen ^ wLog w])])
    (b := [("da_challenge", [c.membershipChallenge])]) (by simp)).append (SameStreams.refl _)

end
end LeanVM.Guest.B1.Da
