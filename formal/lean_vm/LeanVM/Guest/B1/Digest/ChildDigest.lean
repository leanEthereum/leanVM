/-
  LeanVM.Guest.B1.Digest.ChildDigest

  B1 for `child_claim_list_digest` (G:4163-4184; TRIAGE #89): the digest of a child's claim list,
  rebuilt by either walk, the prover's hint `child_mono` choosing.
-/

module

public import LeanVM.Guest.B1.Digest.ChildMono

/-!
# `child_claim_list_digest`

`child_claim_list_digest(entries, region, base, limit, n_g)`: for `n_g = 1` the digest of the
empty string; otherwise `list_split` writes `n = 136 a + 17 b + c` and the hint `child_mono`
picks the walk: `g` the gap walk (`child_claim_list_mono_sound`: every claim marked `base`, the
slots strictly increasing), anything else the walk by hinted indices
(`child_claim_list_any_sound`: claim `j` marked `base · g^j`). Either gives `ChildListOut`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The branch of an empty list. -/
noncomputable def cc25Zero : List Stmt := match Fn.body Data.core24 with
  | [_, _, .ite _ z _, _, _, _] => z
  | _ => []

set_option maxRecDepth 100000 in
theorem core24_shape : Fn.body Data.core24 =
    [.atom (.const (.n 5) (word 1 0)), .atom (.add (.n 6) (.n 4) (.n 5)),
     .ite (.n 6) cc25Zero
      [.call "list_split" [.n 4] [.n 15, .n 16, .n 17],
       .atom (.hint (.witness "child_mono" (.stack [.n 18]))),
       .atom (.const (.n 19) (word 2 0)), .atom (.add (.n 20) (.n 18) (.n 19)),
       .ite (.n 20)
        [.call "child_claim_list_mono" [.n 0, .n 1, .n 2, .n 3, .n 15, .n 16, .n 17] [.n 21, .n 22],
         .atom (.copy (.n 13) (.n 21)), .atom (.copy (.n 14) (.n 22))]
        [.call "child_claim_list_any" [.n 0, .n 1, .n 2, .n 3, .n 15, .n 16, .n 17] [.n 23, .n 24],
         .atom (.copy (.n 13) (.n 23)), .atom (.copy (.n 14) (.n 24))]],
     .atom (.copy (.n 25) (.n 13)), .atom (.copy (.n 26) (.n 14)), .ret [.n 25, .n 26]] :=
  stmtsEqb_sound (by decide +kernel)

/-- The empty list's chain: the empty message from the zero state. -/
noncomputable def cc25ZSpec : ChainSpec := ⟨[], 0, true, none, keccakBlocks (atomsIn cc25Zero)⟩

/-- The empty list's branch hashes the empty string into `.n 13`, `.n 14`. -/
noncomputable def cc25ZOk : Bool :=
  cc25Zero.all Stmt.flat && cc25ZSpec.check (atomsIn cc25Zero) &&
    decide (cc25ZSpec.outV (cc25ZSpec.nb - 1) 0 = V.n 13) &&
    decide (cc25ZSpec.outV (cc25ZSpec.nb - 1) 1 = V.n 14)

set_option maxRecDepth 100000 in
theorem cc25z_ok : cc25ZOk = true := by decide +kernel

/-- The walk by hinted indices gives `ChildListOut` (marks `base · g^j`). -/
theorem childListOut_of_any {rd : Reader} {entries region base limit : E} {n : ℕ}
    {os : List ℕ} {cells : List E} {rets : List E}
    (h : ClaimsAt rd region limit entries base n os cells)
    (hr : rets = digestCells (keccak256 (cellsBytes cells))) :
    ChildListOut rd entries region base limit n rets := by
  obtain ⟨-, hl, hc⟩ := h
  refine ⟨false, fun j => os.getD j 0, cells, hl, fun h => absurd h (by simp),
    fun j hj => ?_, hr⟩
  obtain ⟨h1, h2, h3⟩ := hc j hj
  refine ⟨h1, by simpa using h2, fun c hcc => ?_⟩
  have := h3 c hcc
  rwa [getD_drop'] at this

/-- The gap walk gives `ChildListOut` (every mark `base`, the slots strictly increasing). -/
theorem childListOut_of_mono {rd : Reader} (hm : MemOk rd) {entries region base limit : E}
    {n : ℕ} (hn : n < 2 ^ 24) {os : List ℕ} {cells : List E} {O : ℕ} {rets : List E}
    (hlen : os.length = n) (hw : MonoWalk 0 os O) (hat : MonoAt rd region entries base os cells)
    (hr : rets = digestCells (keccak256 (cellsBytes cells)))
    (hb : ∃ e e', e < 2 ^ 32 ∧ e' < 2 ^ 32 ∧ region * gen ^ O = gen ^ e * region ∧
      limit = gen ^ (e + e')) :
    ChildListOut rd entries region base limit n rets := by
  have hs := monoSlots hm hw hat (by omega) hb
  subst hlen
  refine ⟨true, fun j => os.getD j 0, cells, by rw [hat.1],
    fun _ i j hij hj => hw.1 i j hij hj, fun j hj => ⟨hs j hj, ?_, (hat.2 j hj).2⟩, hr⟩
  simpa using (hat.2 j hj).1

/-- **`child_claim_list_digest` rebuilds a child's claim list at hinted slots, by either walk,
and computes its digest.** -/
theorem child_claim_list_digest_sound : child_claim_list_digest_sound_Spec := by
  intro rd hm args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_child_claim_list_digest args rets).mp h
  have hp' : args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
    rw [← hp]; rfl
  subst hp'
  rw [core24_shape] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨c5, a6, -, hz, hnz⟩ := hb
  by_cases h6 : σ (.n 6) = 0
  · -- the empty list
    have hz1 := cc25z_ok
    simp only [cc25ZOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
    obtain ⟨⟨⟨hzf, hzc⟩, hz13⟩, hz14⟩ := hz1
    have hn1 : σ (.n 4) = 1 := by
      rw [a6, c5, word_one] at h6; exact e_add_eq_zero_iff.mp h6
    obtain ⟨hall, h36, h37, hr⟩ := holdsList_flat _ hzf _ _ (hz h6)
    have hat := atoms_of_flat hall
    have hd := chain_final hzc rfl hat (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    rw [hz13, hz14, show List.take (cc25ZSpec.len / 16) (cc25ZSpec.vals σ) = [] by
      simp [cc25ZSpec], List.nil_append] at hd
    refine ⟨0, by norm_num, by rw [hn1, pow_zero], childListOut_of_any (os := []) (cells := [])
      ⟨rfl, rfl, fun j hj => absurd hj (by omega)⟩ ?_⟩
    rw [← hr, h36, h37, digestCells, ← hd]
  · -- a nonempty list
    obtain ⟨hsplit, -, c30, a31, -, hmono, hany⟩ := hnz h6
    obtain ⟨a, ha, b, hb, c, hc, hn, habc⟩ := list_split_sound rd hm _ _ hsplit
    simp only [List.cons.injEq, and_true] at habc
    obtain ⟨h26, h27, h28⟩ := habc
    simp only [maxKeys, claimGroup, bigGroups] at ha hb hc
    refine ⟨136 * a + 17 * b + c, by simp only [claimBig, maxKeys]; omega, by rw [hn], ?_⟩
    by_cases h31 : σ (.n 20) = 0
    · -- the gap walk
      obtain ⟨hcall, c13, c14, c36, c37, hr⟩ := hmono h31
      obtain ⟨entries, region, base, limit, bigs, groups, rest, hargs, hw⟩ :=
        child_claim_list_mono_sound hm hcall
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨he, hr', hb', hl, hbg, hgr, hrs⟩ := hargs
      obtain ⟨os, cells, O, hlen, hwk, hat, hd, hbd⟩ :=
        hw a b c (by omega) hb hc (by rw [← hbg, h26]) (by rw [← hgr, h27]) (by rw [← hrs, h28])
      rw [← he, ← hr', ← hb', ← hl] at *
      refine childListOut_of_mono hm (by omega) hlen hwk hat ?_ hbd
      rw [← hr, c36, c37, c13, c14, hd]
    · -- the walk by hinted indices
      obtain ⟨hcall, c13, c14, c36, c37, hr⟩ := hany h31
      obtain ⟨entries, region, base, limit, bigs, groups, rest, hargs, hw⟩ :=
        child_claim_list_any_sound hm hcall
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨he, hr', hb', hl, hbg, hgr, hrs⟩ := hargs
      obtain ⟨os, cells, hcl, hd⟩ :=
        hw a b c (by omega) hb hc (by rw [← hbg, h26]) (by rw [← hgr, h27]) (by rw [← hrs, h28])
      rw [← he, ← hr', ← hb', ← hl] at hcl
      refine childListOut_of_any hcl ?_
      rw [← hr, c36, c37, c13, c14, hd]

end
end LeanVM.Guest.B1.Digest
