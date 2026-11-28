/-
  LeanVM.Guest.B1.VsC.VsNatRg

  The ring switch's grind at the honest context: the guest's nonce permutation is the native verifier's, so its
  proof of work passes (`Bw3.hlow`).
-/

module

public import LeanVM.Guest.B1.VsC.VsNatKr
public import LeanVM.Guest.B1.VsC.SqueezeFwd
public import LeanVM.Guest.B1.VsC.VsOrcPh3Ctx

/-!
# The ring grind, natively

Statements `2929 ..< 2938` (`vsRingPreA`, `vsC`'s `2501 ..< 2510`, checked by the kernel): `verify_keccak`'s five
capacity returns copied, the stream's word at its cursor `w 2920` loaded, its tag, and the nonce's `KECCAK`.
**`VsCtx.ring_cells`**: at `D3.Ok.rvk`'s returns (`s'` with a full queue) and `rd0` reading `n` at the cursor, that
`KECCAK` writes the cells of `s'.nonceState n` (vsnat3's `vsFront_cells` pattern). **`VsCtx.hlow_nat`**: so
`natTail`'s `powOk Whir.batchGrindingBits` gives `Bw3.hlow`. `VsCtx.nonce_reads`: `rd0` reads `natTail`'s `n` at
`natBm + 144 + |xs|`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link

@[expose] public section

/-- Statements `2929 ..< 2938`: the capacity, the nonce and its permutation. -/
def vsRingPreA : List Atom :=
  [.copy (.n 2922) (.n 2915), .copy (.n 2923) (.n 2916), .copy (.n 2924) (.n 2917), .copy (.n 2925) (.n 2918),
    .copy (.n 2926) (.n 2919), .load (.n 2927) (.n 2920) 0, .copy (.n 2928) (.n 2927), .const (.n 2929) (word 0 4),
    .keccak [.n 2928, .n 2929, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 2922, .n 2923, .n 2924, .n 2925, .n 2926]
      [.n 2930, .n 2931, .n 2932, .n 2933, .n 2934, .n 2935, .n 2936, .n 2937, .n 2938, .n 2939, .n 2940, .n 2941,
        .n 2942] false false]

/-- An entry of a list, by its index (`VsNatFs`'s `mem_of_getElem?'`, which this module cannot import beside
`VsNatLk`). -/
theorem memIdx {l : List Atom} {a : Atom} (i : ℕ) (h : l[i]? = some a) : a ∈ l := by
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.mp h
  exact e ▸ List.getElem_mem hi

set_option maxRecDepth 200000 in
theorem vsRingPreA_eq : (vsC.drop 2501).take 9 = vsRingPreA.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

section
variable {x : VsCtx}

set_option maxRecDepth 100000 in
/-- **The ring grind's permutation, natively**: at `verify_keccak`'s returns from a sponge `s'` with a full queue,
and the stream's word `n` at its cursor, the nonce's `KECCAK` writes the cells of `s'.nonceState n`. -/
theorem VsCtx.ring_cells {s' : Fs} {bm nx : ℕ} {kw n : E} (hret : CausalRule x.ret)
    (rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets s' (ptrAt (bm + 144)) nx kw).getD j 0)
    (hpend : s'.pend.length = rateScalars) (hrd : ReadsAt x.rd0 (ptrAt (bm + 144 + nx)) [n]) :
    cells13 (([.n 2930, .n 2931, .n 2932, .n 2933, .n 2934, .n 2935, .n 2936, .n 2937, .n 2938, .n 2939, .n 2940,
      .n 2941, .n 2942] : List V).map (vsVal x.rd0 x.w x.args)) = cellsOfState (s'.nonceState n) false := by
  have ha : x.args.length = 6 := rfl
  set σ := vsVal x.rd0 x.w x.args with hσ
  have g : ∀ a ∈ vsRingPreA, Good x.rd0 vsSL x.w σ a := fun a h => by
    have := vsC_atoms_good (rd0 := x.rd0) (w := x.w) ha 2501 9
    rw [vsRingPreA_eq, atomsOf_map] at this
    exact this a h
  -- `verify_keccak`'s returns
  have r35 := vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC35_eq
  have ret : ∀ j < 6, σ (.n (2915 + j)) = (vkRets s' (ptrAt (bm + 144)) nx kw).getD j 0 := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with h | h | h | h | h | h <;> subst h
    · exact (r35 (.n 2915) (by simp)).trans (vsW_retC ha hret (i := 2915 + 0) (by decide) (rvk 0 (by norm_num)))
    · exact (r35 (.n 2916) (by simp)).trans (vsW_retC ha hret (i := 2915 + 1) (by decide) (rvk 1 (by norm_num)))
    · exact (r35 (.n 2917) (by simp)).trans (vsW_retC ha hret (i := 2915 + 2) (by decide) (rvk 2 (by norm_num)))
    · exact (r35 (.n 2918) (by simp)).trans (vsW_retC ha hret (i := 2915 + 3) (by decide) (rvk 3 (by norm_num)))
    · exact (r35 (.n 2919) (by simp)).trans (vsW_retC ha hret (i := 2915 + 4) (by decide) (rvk 4 (by norm_num)))
    · exact (r35 (.n 2920) (by simp)).trans (vsW_retC ha hret (i := 2915 + 5) (by decide) (rvk 5 (by norm_num)))
  have hcap : [σ (.n 2915), σ (.n 2916), σ (.n 2917), σ (.n 2918), σ (.n 2919)] = capOf s'.perm := by
    rw [ret 0 (by norm_num), ret 1 (by norm_num), ret 2 (by norm_num), ret 3 (by norm_num), ret 4 (by norm_num)]
    rfl
  have h2920 : σ (.n 2920) = ptrAt (bm + 144 + nx) := by
    rw [ret 5 (by norm_num)]
    show ptrAt (bm + 144) * gen ^ nx = _
    rw [ptrAt_mul_pow]
  -- the block
  have c2922 : σ (.n 2922) = σ (.n 2915) := g (.copy (.n 2922) (.n 2915)) (memIdx (l := vsRingPreA) 0 rfl)
  have c2923 : σ (.n 2923) = σ (.n 2916) := g (.copy (.n 2923) (.n 2916)) (memIdx (l := vsRingPreA) 1 rfl)
  have c2924 : σ (.n 2924) = σ (.n 2917) := g (.copy (.n 2924) (.n 2917)) (memIdx (l := vsRingPreA) 2 rfl)
  have c2925 : σ (.n 2925) = σ (.n 2918) := g (.copy (.n 2925) (.n 2918)) (memIdx (l := vsRingPreA) 3 rfl)
  have c2926 : σ (.n 2926) = σ (.n 2919) := g (.copy (.n 2926) (.n 2919)) (memIdx (l := vsRingPreA) 4 rfl)
  have hS : Atom.load (.n 2927) (.n 2920) 0 ∉ vsSL := fun h' => by
    have h := vsC36a_shape.2.2.2.2
    rw [List.contains_iff_mem.mpr h'] at h
    exact absurd h (by decide)
  have l2927 : σ (.n 2927) = n :=
    good_loadAt hS (g _ (memIdx (l := vsRingPreA) 5 rfl)) h2920 (by simp) hrd
  have c2928 : σ (.n 2928) = σ (.n 2927) := g (.copy (.n 2928) (.n 2927)) (memIdx (l := vsRingPreA) 6 rfl)
  have t2929 : σ (.n 2929) = word 0 4 := g (.const (.n 2929) (word 0 4)) (memIdx (l := vsRingPreA) 7 rfl)
  have k : (Atom.keccak [.n 2928, .n 2929, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 2922, .n 2923, .n 2924,
      .n 2925, .n 2926] [.n 2930, .n 2931, .n 2932, .n 2933, .n 2934, .n 2935, .n 2936, .n 2937, .n 2938, .n 2939,
      .n 2940, .n 2941, .n 2942] false false).Holds x.rd0 σ :=
    holds_of_good' (g _ (memIdx (l := vsRingPreA) 8 rfl)) rfl
  -- the seed's zeros
  have g0 : ∀ a ∈ vsW0, Good x.rd0 (storesOf 6 vsAf) x.w σ a := fun a h => vsW0_good ha h
  have z25 : σ (.n 25) = 0 := (g0 (.const (.n 25) (word 0 0)) (memIdx (l := vsW0) 19 rfl)).trans word_zero
  have z26 : σ (.n 26) = 0 := (g0 (.const (.n 26) (word 0 0)) (memIdx (l := vsW0) 20 rfl)).trans word_zero
  have z27 : σ (.n 27) = 0 := (g0 (.const (.n 27) (word 0 0)) (memIdx (l := vsW0) 21 rfl)).trans word_zero
  have z28 : σ (.n 28) = 0 := (g0 (.const (.n 28) (word 0 0)) (memIdx (l := vsW0) 22 rfl)).trans word_zero
  clear_value σ
  have habs : s'.absorb n dsPowNonce = ⟨capOf s'.perm, [(n, dsPowNonce)]⟩ := by simp [Fs.absorb, hpend]
  have hK := keccakA_fs (s := s'.absorb n dsPowNonce) k (by rw [habs]; simp) (by
    rw [habs, ← hcap]
    simp only [List.map_cons, List.map_nil, c2922, c2923, c2924, c2925, c2926, c2928, l2927, t2929, z25, z26, z27,
      z28]
    rfl)
  exact hK

/-- **`Bw3.hlow`, natively**: the ring grind's lane passes from `natTail`'s proof of work. -/
theorem VsCtx.hlow_nat {s' : Fs} {bm nx : ℕ} {kw n : E} (hret : CausalRule x.ret)
    (rvk : ∀ j < 7, ∀ σ, x.ret (2915 + j) σ = (vkRets s' (ptrAt (bm + 144)) nx kw).getD j 0)
    (hpend : s'.pend.length = rateScalars) (hrd : ReadsAt x.rd0 (ptrAt (bm + 144 + nx)) [n])
    (hpow : powOk Whir.batchGrindingBits (Keccak.lane (s'.nonceState n) 2) = true) :
    ((x.σ0 (.n 2931)).limb 0).lane.toNat % 2 ^ 13 = 0 := by
  have e : x.σ0 (.n 2931) = cellsOfState (s'.nonceState n) false 1 :=
    outs_eq (x.ring_cells hret rvk hpend hrd) 1 (by simp)
  rw [e, ← LeanVM.Guest.Value.Keccak.powLane_cells]
  rw [show Whir.batchGrindingBits = 13 from rfl, powOk, decide_eq_true_iff] at hpow
  exact hpow

/-- **The nonce's word in `rd0`**: `natTail`'s `n`, past the Keccak reduction's words from the packed message's
`144`. -/
theorem VsCtx.nonce_reads {L : LinkNat} {rest xs rest' : List E} {n : E} (hb : L.bits x.lay ≠ 0)
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest) (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream)
    (hm : L.msg.length = 144) (hr : rest = xs ++ n :: rest')
    (h0 : ReadsAt x.rd0 (ptrAt (x.base 18)) (x.bw.getD 18 [])) :
    ReadsAt x.rd0 (ptrAt (x.natBm L + 144 + xs.length)) [n] := by
  have hs := (x.sw_nat hb hw hb18 hm).2 (xs.length + 1) (by rw [hr]; simp)
  have e0 : ∀ ys : List E, (ys ++ n :: rest').take (ys.length + 1) = ys ++ [n] := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih => simp only [List.cons_append, List.length_cons, List.take_succ_cons, ih]
  have e : rest.take (xs.length + 1) = xs ++ [n] := by rw [hr]; exact e0 xs
  rw [e] at hs
  have hbm : x.base 18 ≤ x.natBm L := by simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]; omega
  have r := readsAt_slice h0 (x.natBm L - x.base 18 + 144) (xs.length + 1)
  have e1 : x.base 18 + (x.natBm L - x.base 18 + 144) = x.natBm L + 144 := by omega
  rw [e1] at r
  have r' : ReadsAt x.rd0 (ptrAt (x.natBm L + 144)) (xs ++ [n]) := by rw [← hs]; exact r
  have r2 := VsC.readsAt_drop (m := xs.length) r'
  simpa using r2

end

end
end LeanVM.Guest.B1.VsC
