/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.MonoReplay

  `child_claim_list_mono`'s walk at the node's own valuation: every record of its two frame loops
  holds the walk's pointers at an offset below the bound's exponent.
-/

module

public import LeanVM.Guest.CoreMode.Fam.MonoChain
public import LeanVM.Guest.B1.Digest.ChildMono
public import LeanVM.Guest.CoreMode.Fam.ResT
public import LeanVM.Guest.CoreMode.Fam.RefAll
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono»
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono_loop0»
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono_loop1»

/-!
# `child_claim_list_mono` at its own valuation

B1's `child_claim_list_mono_sound` goes through a fresh valuation, and so says nothing of the
node's chain pointer (an `allocDyn`). `mono_replay` walks the body at the node's own valuation:
the frame loops' counts `a`, `b` from their trees (`loopCount`: `a` frames within the node's
words, so `136 a + 17 b + c` stays below `2^28` and the walk's end `O ≤ (136 a + 17 b + c)·2^32`
does not wrap), the records at `chain · g^(15 q)` holding the pointers at offsets below the walk's
end (`monoFramesU`, `monoFrames_sound` keeping every record), and the end equal to the exponent
`e` of the bound (`region · g^O = g^e · region`, `region ≠ 0` where a claim is marked), below
`L = e + e'`, `limit = g^L`; and `region ≠ 0` once one of the counts is not `g^0`.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A record of the walk**: the pointers at `rec · g^13` and `rec · g^14`, at an offset `O ≤ L`. -/
def RecAt (rd : Reader) (rec region entries : E) (L : ℕ) : Prop :=
  ∃ O ≤ L, LoadHolds rd rec 13 (region * gen ^ O) ∧ LoadHolds rd rec 14 (entries * gen ^ (4 * O))

theorem RecAt.mono {rd : Reader} {rec region entries : E} {L L' : ℕ} (h : RecAt rd rec region entries L)
    (hL : L ≤ L') : RecAt rd rec region entries L' :=
  let ⟨O, hO, h13, h14⟩ := h
  ⟨O, le_trans hO hL, h13, h14⟩

/-- A pointer loaded through is nonzero. -/
theorem ne_zero_of_load {rd : Reader} (hm : MemOk rd) {p v : E} {o : ℕ} (h : LoadHolds rd p o v) : p ≠ 0 := by
  rw [← Nat.add_zero o, ← loadHolds_mul_gen_pow] at h
  obtain ⟨f, -, hf⟩ := load_gpow hm h
  rintro rfl
  rw [zero_mul] at hf
  exact pow_ne_zero f gen_ne_zero hf.symm

/-- **The frames of the walk, every record kept**: `monoFrames_sound`, and each record up to `q`
holds the pointers at an offset at most the walk's. -/
theorem monoFramesU {rd : Reader} {m nb : ℕ} (hmn : 64 * m = 136 * nb)
    {chain entries region mark : E} {a n0 O0 : ℕ} {pre : List UInt8}
    (hpre0 : pre.length = rate * n0) (h0 : StateAt rd chain 0 (absorbChunks n0 zeroState pre))
    (hc0 : LoadHolds rd chain 13 (region * gen ^ O0))
    (he0 : LoadHolds rd chain 14 (entries * gen ^ (4 * O0)))
    (hstep : ∀ q < a, MonoStep rd m nb chain mark (gen ^ q)) :
    ∀ q ≤ a, ∃ (os : List ℕ) (cells : List E) (O : ℕ), os.length = m * q ∧ MonoWalk O0 os O ∧
      MonoAt rd region entries mark os cells ∧ StateAt rd (chain * gen ^ (15 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre ++ cellsBytes cells)) ∧
      LoadHolds rd (chain * gen ^ (15 * q)) 13 (region * gen ^ O) ∧
      LoadHolds rd (chain * gen ^ (15 * q)) 14 (entries * gen ^ (4 * O)) ∧
      ∀ q' ≤ q, RecAt rd (chain * gen ^ (15 * q')) region entries O := by
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨[], [], O0, rfl, monoWalk_nil O0, monoAt_nil rd _ _ _,
      by simpa using h0, by simpa using hc0, by simpa using he0, fun q' hq' ↦ ?_⟩
    obtain rfl : q' = 0 := by omega
    exact ⟨O0, le_rfl, by simpa using hc0, by simpa using he0⟩
  | succ q ih =>
    intro hq
    obtain ⟨os, cells, O, hlen, hw, hat, hS, hc, he, hrec⟩ := ih (by omega)
    have hpre : (pre ++ cellsBytes cells).length = rate * (n0 + nb * q) := by
      rw [List.length_append, length_cellsBytes, hat.1, hlen, hpre0]
      show 136 * n0 + 16 * (4 * (m * q)) = 136 * (n0 + nb * q)
      have : 16 * (4 * (m * q)) = (64 * m) * q := by ring
      rw [this, hmn]; ring
    rw [show chain * gen ^ (15 * q) = chain * (gen ^ q) ^ 15 by rw [gen_pow_pow]] at hS hc he
    obtain ⟨os2, c2, O', hlen2, hw2, hat2, hS2, hc2, he2⟩ :=
      hstep q (by omega) region entries _ O _ hpre hS hc he
    rw [gen_pow_pow, loadHolds_mul_gen_pow] at hc2 he2
    have hc' : LoadHolds rd (chain * gen ^ (15 * (q + 1))) 13 (region * gen ^ O') := by
      rw [loadHolds_mul_gen_pow, show 15 * (q + 1) + 13 = 15 * q + 28 by ring]
      exact hc2
    have he' : LoadHolds rd (chain * gen ^ (15 * (q + 1))) 14 (entries * gen ^ (4 * O')) := by
      rw [loadHolds_mul_gen_pow, show 15 * (q + 1) + 14 = 15 * q + 29 by ring]
      exact he2
    refine ⟨os ++ os2, cells ++ c2, O', by rw [List.length_append, hlen, hlen2]; ring,
      monoWalk_append hw hw2, monoAt_append hat hat2, ?_, hc', he', fun q' hq' ↦ ?_⟩
    · intro c
      have := hS2 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow] at this
      rw [loadHolds_mul_gen_pow, cellsBytes_append, ← List.append_assoc,
        show 15 * (q + 1) + (0 + c.val) = 15 * q + (15 + c.val) by ring,
        show n0 + nb * (q + 1) = n0 + nb * q + nb by ring]
      exact this
    · rcases Nat.lt_or_ge q' (q + 1) with h | h
      · exact (hrec q' (by omega)).mono hw2.2.2.1
      · obtain rfl : q' = q + 1 := by omega
        exact ⟨O', le_rfl, hc', he'⟩

/-- **A frame loop's count from its tree**: called as `callIf (1 + N) f [1, N, chain, mark]`, its
tree within `T` words, `N = g^a` with `a` frames of `f` within `T`. -/
theorem loopCount {rd : Reader} {T : ℕ} {f : String} {j : ℕ} (hidx : coreProgram.indexOf? f = some j)
    (hl : (coreProgram.getD j default).loop = true) (hend : endOfFn (coreProgram.getD j default) = some none)
    (hpar : (coreProgram.getD j default).params = [.n 0, .n 1, .n 2, .n 3]) {N chain mark : E}
    (hcall : 1 + N ≠ 0 → KidRel coreProgram rd B2C.fs T f [1, N, chain, mark] []) :
    ∃ a, N = gen ^ a ∧ a * B2C.fs f ≤ T := by
  by_cases h0 : 1 + N = 0
  · exact ⟨0, by rw [pow_zero]; exact (e_add_eq_zero_iff.mp h0).symm, by simp⟩
  obtain ⟨t, hv, hn, htot⟩ := hcall h0
  have hf := find_of_idx hidx
  rcases t with ⟨f', σt, bufs, kids⟩ | ⟨f', σt⟩
  · simp only [Tree.name] at hn
    subst hn
    obtain ⟨-, e, he, hs, -⟩ := EndExec.progOk_guest.loop f' _ hf hl
    obtain rfl : e = none := Option.some.inj (he.symm.trans hend)
    obtain ⟨m, p0, prest, hps, -, hmf, hm⟩ := chainF fs_pos _ le_rfl hv hf hs
    obtain ⟨fn', hf', hp, -⟩ := hv
    obtain rfl := Option.some.inj (hf.symm.trans hf')
    rw [hpar] at hps hp
    obtain ⟨rfl, rfl⟩ := List.cons.inj hps
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
    obtain ⟨h1, hN, -⟩ := hp
    simp only [endVal, hpar, hN] at hm
    rw [h1, one_mul, ← gen_pow_eq_ofK] at hm
    exact ⟨m, hm.symm, by omega⟩
  · exact hv.elim

/-- **A frame loop entered runs**: its tree at counter `1` and end `g^a`, within `2^28` words,
makes `a ≥ 1` iterations. -/
theorem loop_pos {rd : Reader} {f : String} {j : ℕ} (hidx : coreProgram.indexOf? f = some j)
    (hl : (coreProgram.getD j default).loop = true) (hend : endOfFn (coreProgram.getD j default) = some none)
    (hpar : (coreProgram.getD j default).params = [.n 0, .n 1, .n 2, .n 3]) {σ : Val} {bufs : List ℕ}
    {kids : List Tree} {args rets : List E} (hv : (Memory.Tree.node f σ bufs kids).Valid coreProgram rd args rets)
    (htot : (Memory.Tree.node f σ bufs kids).total B2C.fs ≤ 2 ^ 28) (h0 : σ (.n 0) = 1) {a : ℕ}
    (ha : a < 2 ^ 32) (h1 : σ (.n 1) = gen ^ a) : 1 ≤ a := by
  have hf := find_of_idx hidx
  obtain ⟨-, e, he, hs, -⟩ := EndExec.progOk_guest.loop f _ hf hl
  obtain rfl : e = none := Option.some.inj (he.symm.trans hend)
  obtain ⟨m, p0, prest, hps, hm1, hmle, hm⟩ := chain fs_pos _ le_rfl hv hf hs
  rw [hpar] at hps
  obtain ⟨rfl, rfl⟩ := List.cons.inj hps
  simp only [endVal, hpar, h0, h1, one_mul, ← gen_pow_eq_ofK] at hm
  have := gen_pow_inj (by omega) (by omega) hm
  omega

theorem loop0_facts : (coreProgram.getD idx% «child_claim_list_mono_loop0» default).loop = true ∧
    endOfFn (coreProgram.getD idx% «child_claim_list_mono_loop0» default) = some none ∧
    (coreProgram.getD idx% «child_claim_list_mono_loop0» default).params = [.n (val% «child_claim_list_mono_loop0» "xq"), .n (val% «child_claim_list_mono_loop0» "bound"), .n (val% «child_claim_list_mono_loop0» "chain"), .n (val% «child_claim_list_mono_loop0» "base")] ∧
    512 ≤ B2C.fs name% «child_claim_list_mono_loop0» := by
  rw [B2C.fs, mono136_idx]
  decide +kernel

theorem loop1_facts : (coreProgram.getD idx% «child_claim_list_mono_loop1» default).loop = true ∧
    endOfFn (coreProgram.getD idx% «child_claim_list_mono_loop1» default) = some none ∧
    (coreProgram.getD idx% «child_claim_list_mono_loop1» default).params = [.n (val% «child_claim_list_mono_loop1» "xq"), .n (val% «child_claim_list_mono_loop1» "bound"), .n (val% «child_claim_list_mono_loop1» "mid"), .n (val% «child_claim_list_mono_loop1» "base")] ∧
    64 ≤ B2C.fs name% «child_claim_list_mono_loop1» := by
  rw [B2C.fs, mono17_idx]
  decide +kernel

/-- **`child_claim_list_mono` at its own valuation** `σ`, its calls as trees within `T ≤ 2^28`
words: the frame loops' counts `a`, `b`; the bound `limit = g^L`; the records of the big frames
from `chain = .n 16` and of the groups from `.n 39` (the last record `.n 49`) at offsets at most
`L`. -/
theorem mono_replay {rd : Reader} (hm : MemOk rd) {σ : Val} {T : ℕ} (hT : T ≤ 2 ^ 28) {rets : List E}
    (hb : Stmt.HoldsList (KidRel coreProgram rd B2C.fs T) rd σ (Fn.body fn% «child_claim_list_mono»)
      False (· = rets)) :
    ∃ a b L, σ (.n (val% «child_claim_list_mono» "bigs")) = gen ^ a ∧ σ (.n (val% «child_claim_list_mono» "groups")) = gen ^ b ∧ a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ L < 2 ^ 33 ∧
      σ (.n (val% «child_claim_list_mono» "limit_g")) = gen ^ L ∧ σ (.n (val% «child_claim_list_mono» "s4#2")) = 1 ∧ σ (.n (val% «child_claim_list_mono» "s6#2")) = 1 ∧ σ (.n (val% «child_claim_list_mono» "last")) = σ (.n (val% «child_claim_list_mono» "mid")) * gen ^ (15 * b) ∧
      (∀ q ≤ a, RecAt rd (σ (.n (val% «child_claim_list_mono» "chain")) * gen ^ (15 * q)) (σ (.n (val% «child_claim_list_mono» "region"))) (σ (.n (val% «child_claim_list_mono» "entries_ptr"))) L) ∧
      (∀ q ≤ b, RecAt rd (σ (.n (val% «child_claim_list_mono» "mid")) * gen ^ (15 * q)) (σ (.n (val% «child_claim_list_mono» "region"))) (σ (.n (val% «child_claim_list_mono» "entries_ptr"))) L) ∧
      (σ (.n (val% «child_claim_list_mono» "bigs")) ≠ 1 ∨ σ (.n (val% «child_claim_list_mono» "groups")) ≠ 1 ∨ σ (.n (val% «child_claim_list_mono» "rest")) ≠ 1 → σ (.n (val% «child_claim_list_mono» "region")) ≠ 0) := by
  rw [child_claim_list_mono_shape, holdsList_append] at hb
  have hok := monoBody_ok
  simp only [monoBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfl, hl19⟩, hl20⟩, hdis⟩, h32⟩, h31⟩, h30⟩, h42⟩, h41⟩, h40⟩, hzs⟩,
    hl1⟩, hl0⟩, hm39⟩, hm49⟩, -⟩, -⟩ := hok
  obtain ⟨hall, -⟩ := holdsList_flat _ (List.all_eq_true.mpr hfl) _ _ hb
  have hat := atoms_of_flat hall
  have hc32 : σ (.n (val% «child_claim_list_mono» "s4#2")) = 1 := by rw [const_sound h32 hat, word_one]
  have hc42 : σ (.n (val% «child_claim_list_mono» "s6#2")) = 1 := by rw [const_sound h42 hat, word_one]
  -- the zero record
  have h0 : StateAt rd (σ (.n (val% «child_claim_list_mono» "chain"))) 0 (absorbChunks 0 zeroState []) := by
    intro c
    have hl := load_sound (hzs c c.isLt).1 hat
    rw [const_sound (hzs c c.isLt).2 hat, word_zero] at hl
    rw [Nat.zero_add, absorbChunks, cellsOfState_zero]
    exact hl
  have hc0 : LoadHolds rd (σ (.n (val% «child_claim_list_mono» "chain"))) 13 (σ (.n (val% «child_claim_list_mono» "region")) * gen ^ 0) := by
    rw [pow_zero, mul_one]; exact load_sound hl1 hat
  have he0 : LoadHolds rd (σ (.n (val% «child_claim_list_mono» "chain"))) 14 (σ (.n (val% «child_claim_list_mono» "entries_ptr")) * gen ^ (4 * 0)) := by
    rw [mul_zero, pow_zero, mul_one]; exact load_sound hl0 hat
  -- the big frames
  have hcall19 : 1 + σ (.n (val% «child_claim_list_mono» "bigs")) ≠ 0 → KidRel coreProgram rd B2C.fs T name% «child_claim_list_mono_loop0»
      [1, σ (.n (val% «child_claim_list_mono» "bigs")), σ (.n (val% «child_claim_list_mono» "chain")), σ (.n (val% «child_claim_list_mono» "base"))] [] := fun hne ↦ by
    have := (callIf_of_flat hall hl19).2
      (by rw [add_sound h31 hat, const_sound h30 hat, word_one]; exact hne)
    simpa [hc32] using this
  obtain ⟨l0, e0, p0, f0⟩ := loop0_facts
  obtain ⟨a, h4, haf⟩ := loopCount mono136_idx l0 e0 p0 hcall19
  have ha : a ≤ 2 ^ 19 := by
    have : a * 512 ≤ 2 ^ 28 := le_trans (Nat.mul_le_mul_left a f0) (le_trans haf hT)
    omega
  have hbig := monoFrames_of_loop hm mono136_idx mono136_ok word_g136 word_g544
    mono136_nb (chain := σ (.n (val% «child_claim_list_mono» "chain"))) (mark := σ (.n (val% «child_claim_list_mono» "base"))) (by omega) h4 fun hne ↦ (hcall19 hne).rel
  obtain ⟨osa, ca, Oa, hla, hwa, hata, hSa, hca, hea, hreca⟩ :=
    monoFramesU (by norm_num) (n0 := 0) (pre := []) rfl h0 hc0 he0 hbig a le_rfl
  -- the groups
  have h39 : σ (.n (val% «child_claim_list_mono» "mid")) = σ (.n (val% «child_claim_list_mono» "chain")) * gen ^ (15 * a) := by
    rw [monoIs_sound hm39 hat, h4, gen_pow_pow]
  have hcall20 : 1 + σ (.n (val% «child_claim_list_mono» "groups")) ≠ 0 → KidRel coreProgram rd B2C.fs T name% «child_claim_list_mono_loop1»
      [1, σ (.n (val% «child_claim_list_mono» "groups")), σ (.n (val% «child_claim_list_mono» "mid")), σ (.n (val% «child_claim_list_mono» "base"))] [] := fun hne ↦ by
    have := (callIf_of_flat hall hl20).2
      (by rw [add_sound h41 hat, const_sound h40 hat, word_one]; exact hne)
    simpa [hc42] using this
  obtain ⟨l1, e1, p1, f1⟩ := loop1_facts
  obtain ⟨b, h5, hbf⟩ := loopCount mono17_idx l1 e1 p1 hcall20
  have hb' : b ≤ 2 ^ 22 := by
    have : b * 64 ≤ 2 ^ 28 := le_trans (Nat.mul_le_mul_left b f1) (le_trans hbf hT)
    omega
  have hgrp := monoFrames_of_loop hm mono17_idx mono17_ok word_g17 word_g68
    mono17_nb (chain := σ (.n (val% «child_claim_list_mono» "mid"))) (mark := σ (.n (val% «child_claim_list_mono» "base"))) (by omega) h5 fun hne ↦ (hcall20 hne).rel
  have hpa : ([] ++ cellsBytes ca).length = rate * (0 + 64 * a) := by
    rw [List.nil_append, length_cellsBytes, hata.1, hla]
    show 16 * (4 * (136 * a)) = 136 * (0 + 64 * a)
    ring
  obtain ⟨osb, cb, Ob, hlb, hwb, hatb, hSb, hcb, heb, hrecb⟩ :=
    monoFramesU (by norm_num) hpa (by rw [h39]; exact hSa) (by rw [h39]; exact hca)
      (by rw [h39]; exact hea) hgrp b le_rfl
  -- the rest
  obtain ⟨j, hj, hsel, hcall⟩ := dispatch_of_flat hall hdis
  have hj17 : j < 17 := hj
  rw [show mlNames[j] = mlNames.getD j "" by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl] at hcall
  obtain ⟨rec, reg, mk, lim, hargs, hlast⟩ := monoLast_sound hm hj17 (KidRel.rel hcall)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs
  obtain ⟨hrec, hreg, hmk, hlim⟩ := hargs
  have h49 : σ (.n (val% «child_claim_list_mono» "last")) = σ (.n (val% «child_claim_list_mono» "mid")) * gen ^ (15 * b) := by
    rw [mono2Is_sound hm49 hat, h39, h4, h5]; simp only [gen_pow_pow]
  have hpre : ([] ++ cellsBytes ca ++ cellsBytes cb).length = rate * (0 + 64 * a + 8 * b) := by
    rw [List.length_append, List.nil_append, length_cellsBytes, length_cellsBytes, hata.1, hla,
      hatb.1, hlb]
    show 16 * (4 * (136 * a)) + 16 * (4 * (17 * b)) = 136 * (0 + 64 * a + 8 * b)
    ring
  rw [← hreg, ← hmk] at hlast
  obtain ⟨osc, cc, Oc, hlc, hwc, hatc, -, e, e', he, he', hOc, hL⟩ := hlast (σ (.n (val% «child_claim_list_mono» "entries_ptr"))) _ Ob _ hpre
    (by rw [← hrec, h49]; exact hSb) (by rw [← hrec, h49]; exact hcb)
    (by rw [← hrec, h49]; exact heb)
  -- the walk's end is the bound's exponent
  have hw := monoWalk_append (monoWalk_append hwa hwb) hwc
  have hat' := monoAt_append (monoAt_append hata hatb) hatc
  have hlen : (osa ++ osb ++ osc).length < 2 ^ 28 := by
    rw [List.length_append, List.length_append, hla, hlb, hlc]; omega
  have hOc : Oc ≤ e := by
    rcases Nat.eq_zero_or_pos (osa ++ osb ++ osc).length with h0 | h0
    · have := hw.2.2.2; rw [h0] at this; omega
    · have hr0 := ne_zero_of_load hm (hat'.2 0 h0).1
      have hOb : Oc < 2 ^ 64 - 1 := by
        have := hw.2.2.2
        have : (osa ++ osb ++ osc).length * 2 ^ 32 ≤ 2 ^ 28 * 2 ^ 32 := Nat.mul_le_mul_right _ hlen.le
        omega
      rw [mul_comm (gen ^ e)] at hOc
      exact (gen_pow_inj hOb (by omega) (mul_left_cancel₀ hr0 hOc)).le
  have hab : Oa ≤ Oc := le_trans hwb.2.2.1 hwc.2.2.1
  -- a claim marked: the region nonzero
  have hreg : σ (.n (val% «child_claim_list_mono» "bigs")) ≠ 1 ∨ σ (.n (val% «child_claim_list_mono» "groups")) ≠ 1 ∨ σ (.n (val% «child_claim_list_mono» "rest")) ≠ 1 → σ (.n (val% «child_claim_list_mono» "region")) ≠ 0 := by
    intro h
    have h0 : 0 < (osa ++ osb ++ osc).length := by
      rw [List.length_append, List.length_append, hla, hlb, hlc]
      rcases h with h | h | h
      · have : a ≠ 0 := by rintro rfl; exact h (by rw [h4, pow_zero])
        omega
      · have : b ≠ 0 := by rintro rfl; exact h (by rw [h5, pow_zero])
        omega
      · have : j ≠ 0 := by rintro rfl; exact h (by rw [hsel, ← gen_pow_eq_ofK, pow_zero])
        omega
    exact ne_zero_of_load hm (hat'.2 0 h0).1
  refine ⟨a, b, e + e', h4, h5, by omega, by omega, by omega, by rw [hlim, hL], hc32, hc42, h49,
    fun q hq ↦ (hreca q hq).mono (by omega), fun q hq ↦ ?_, hreg⟩
  exact (hrecb q hq).mono (by have := hwc.2.2.1; omega)

end

end LeanVM.Guest.Res
