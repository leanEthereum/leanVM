/-
  LeanVM.Guest.B1.Da.DaPops

  The witness-stream entries LeanDA's blob matrix check pops (`da_verify` and its callees)
  are the honest hint generator's (`Hints.daHints`), stream by stream.

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.B1.Da.DvAt
public import LeanVM.Guest.B1.Da.CellPops
public import LeanVM.Guest.B1.Da.Witness
public import LeanVM.Guest.Hints
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify»

/-!
# LeanDA's pops

`da_verify` pops its blob count (`da_n_blobs`) and its challenge (`da_challenge`), each cell check its `128` symbols
(`da_symbols`); nothing else in its call tree pops (`kid_pops_mute`).

* `blob_pops`: a blob of honest shape pops its cells' symbols in order (`blobPops`);
* `blobL_pops`: the blob loop pops its blobs' entries in order;
* `dv_pops`: `da_verify` of honest shape pops its blob count, its challenge, then its blob loop's entries;
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
def blobPops (syms : ℕ → ℕ → List E) (i : ℕ) : List Pop :=
  (List.range 128).map fun h => ("da_symbols", syms i h)

/-- **A blob of honest shape pops its cells' symbols.** -/
theorem blob_pops {fs SB SK : String → ℕ} {rd : Reader} {syms : ℕ → ℕ → List E} {i : ℕ}
    (hsl : ∀ k, (syms i k).length = 128) {t : Memory.Tree} {args rets : List E} (ht : blobNH fs SB SK syms i t)
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

/-- `da_verify`'s first statements: its blob count's hint, the padding rows' count, its challenge's hint. -/
def dvHead : List Stmt :=
  [.atom (.hint (.witness "da_n_blobs" (.stack [.n (val% «da_verify» "n_blob_g")]))), .call "da_padding" [.n (val% «da_verify» "n_blob_g")] [.n (val% «da_verify» "gap_g")],
    .atom (.hint (.witness "da_challenge" (.stack [.n (val% «da_verify» "z")])))]

/-- `da_verify` starts with `dvHead`, then pops nothing itself. -/
noncomputable def dvShapeOk : Bool :=
  stmtsEqb ((Fn.body fn% «da_verify»).take (pos% «da_verify» "zs")) dvHead && Stmt.muteList (fun _ => true) ((Fn.body fn% «da_verify»).drop (pos% «da_verify» "zs"))

theorem dv_shape_ok : dvShapeOk = true := by decide +kernel

theorem dvHead_pops (rd : Reader) (σ : Val) (k : List Pop) :
    SplicePops rd σ dvHead [k] (("da_n_blobs", [σ (.n (val% «da_verify» "n_blob_g"))]) :: (k ++ [("da_challenge", [σ (.n (val% «da_verify» "z"))])])) := by
  have h := (SplicePops.of_fallPops (rd := rd) (σ := σ)
    (FallPops.atom (.hint (.witness "da_n_blobs" (.stack [.n (val% «da_verify» "n_blob_g")]))))).append
    ((SplicePops.call (rd := rd) (σ := σ) "da_padding" [.n (val% «da_verify» "n_blob_g")] [.n (val% «da_verify» "gap_g")] k).append
      (SplicePops.of_fallPops (FallPops.atom (.hint (.witness "da_challenge" (.stack [.n (val% «da_verify» "z")]))))))
  simpa [dvHead, Atom.pops, Hint.pops, Dest.words] using h

/-- **`da_verify` of honest shape pops its blob count and its challenge, then its blob loop's entries.** -/
theorem dv_pops {rd : Reader} {r L : ℕ} {z : E} {Tb : Memory.Tree → Prop} (hr1 : 1 ≤ r) (hr : r ≤ 1024)
    {t : Memory.Tree} {args rets : List E} (ht : dvNHzC r L z Tb t)
    (hv : t.Valid coreProgram rd args rets) :
    ∃ k3 args3, k3.Valid coreProgram rd args3 [] ∧ Tb k3 ∧
      t.pops coreProgram rd = ("da_n_blobs", [gen ^ r]) :: ("da_challenge", [z]) :: k3.pops coreProgram rd := by
  obtain ⟨σ, ks, rfl, ⟨⟨s1, -, s12, -⟩, s3⟩, hc, -, hT⟩ := ht
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := id hv
  rw [find_da_verify] at hf
  cases hf
  rw [hc _ es vs find_da_verify hw, dv_flatCalls] at hkv
  rw [dv_flatCalls] at hT
  obtain ⟨k0, k1, k2, k3, k4, k5, rfl⟩ : ∃ k0 k1 k2 k3 k4 k5, ks = [k0, k1, k2, k3, k4, k5] := by
    match ks, kidsValid_len hkv with
    | [k0, k1, k2, k3, k4, k5], _ => exact ⟨k0, k1, k2, k3, k4, k5, rfl⟩
  obtain ⟨n0, v0, n1, v1, n2, v2, -, v3, n4, v4, n5, v5, -⟩ := hkv
  obtain ⟨-, -, -, t3, -⟩ := hT
  have hne : (1 : E) + gen ^ r ≠ 0 := one_add_gen_pow_ne_zero (by omega) (by unfold ordG; omega)
  have htk : (Main.mkCall σ (some (.n (val% «da_verify» "s6#1")), name% «da_verify_loop0», [.n (val% «da_verify» "s6#2"), .n (val% «da_verify» "n_blob_g"), .n (val% «da_verify» "weights"), .n (val% «da_verify» "roots")], [])).taken = true := by
    simp [Main.mkCall, s12, hne]
  have e0 := kid_pops_mute v0 n0 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e1 := kid_pops_mute v1 n1 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e2 := kid_pops_mute v2 n2 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e4 := kid_pops_mute v4 n4 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have e5 := kid_pops_mute v5 n5 (by rw [mkCall_f]; exact noWitS_of_callee (j := idx% «da_verify») (by decide +kernel))
  have h := dv_shape_ok
  simp only [dvShapeOk, Bool.and_eq_true] at h
  have hb : Fn.body fn% «da_verify» = dvHead ++ (Fn.body fn% «da_verify»).drop (pos% «da_verify» "zs") := by
    rw [← stmtsEqb_sound h.1, List.take_append_drop]
  rw [ite_eq_left htk] at v3
  replace v3 : k3.Valid coreProgram rd _ _ := v3
  refine ⟨k3, _, v3, t3 htk, ?_⟩
  rw [Tree.pops_of_prefix hv find_da_verify hb (dvHead_pops rd σ (k0.pops coreProgram rd)) h.2 rfl, s1, s3]
  simp [Memory.Tree.popsKids, e0, e1, e2, e4, e5]

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

theorem count_gen {n : ℕ} (_h : n ≤ 1024) : Hints.count n = gen ^ n := by
  rw [Hints.count, LeanVM.Protocol.Verifier.gpow]

/-- **The check's entries are `daHints`'**, stream by stream. -/
theorem daPops_sameStreams (c : LeanVM.Node.DaClaim) (w : LeanVM.Da.MatrixWitness) (hr : w.rows.length ≤ 1024) :
    SameStreams (("da_n_blobs", [gen ^ w.rows.length]) :: ("da_challenge", [c.membershipChallenge]) ::
      daSymPops w) (Hints.daHints c w) := by
  have e3 : w.rows.flatMap (fun row => (List.range LeanDa.cellsPerRow).map fun j =>
      (("da_symbols" : String), LeanDa.listCell row j)) = daSymPops w := by
    rw [flatMap_eq_range [] _ w.rows, daSymPops]
    refine List.flatMap_congr fun i hi => List.map_congr_left fun j hj => ?_
    rw [wSyms, ite_eq_left ⟨List.mem_range.mp hi, List.mem_range.mp hj⟩]
  rw [Hints.daHints, count_gen hr, e3]
  exact (sameStreams_append_comm (a := [("da_n_blobs", [gen ^ w.rows.length])])
    (b := [("da_challenge", [c.membershipChallenge])]) (by simp)).append (SameStreams.refl _)

end
end LeanVM.Guest.B1.Da
