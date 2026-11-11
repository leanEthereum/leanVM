/-
  LeanVM.Guest.B1.Main.AggAbsorb

  `aggregate_claims`' absorbing loop (`__loop33`): one child's words absorbed into the batching's
  sponge, row by row.
-/

module

public import LeanVM.Guest.B1.Main.AggFs

/-!
# `__loop33`: the children's words

`aggregate_claims` (G:4670-4773) keeps the batching's sponge in rows of thirteen words (`absorb`,
`RowRel`: the capacity cells, then four waiting scalars' rate cells). Iteration `x = g^c`
(`__loop33`, core function `415`) writes the child's pointers `child_fresh·x^24`,
`child_carried·x^24` into the tables `lf`, `lc`, permutes row `c`, absorbs the child's `50` words
(its public input's two cells at `child_pi·x^2`, its fresh claim's `24` cells, its carried claim's
`24`) and two zeros in thirteen `KECCAK`s, and writes row `c + 1` (`l25_step`, `L25Step`).

Its body is checked by kernel evaluation (`l25Ok`): the `KECCAK` chain (`DupSpec.check`), the
row it reads and the row it writes, every word's source, and the pointers.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {rd : Reader} {σ : Val} {atoms : List Atom}

/-! ## Rows, read and written -/

/-- `v` is a copy of a value loaded through `p` at `o`. -/
def isCopyOfLoad (atoms : List Atom) (v p : V) (o : ℕ) : Atom → Bool
  | .copy d w => decide (d = v) && atoms.any (isLoadAt w p o)
  | _ => false

/-- `v` is loaded through `p` at `o`, or a copy of such a value. -/
def valIs (atoms : List Atom) (v p : V) (o : ℕ) : Bool :=
  atoms.any (isLoadAt v p o) || atoms.any (isCopyOfLoad atoms v p o)

theorem valIs_sound {v p : V} {o : ℕ} (h : valIs atoms v p o = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ v = memAt rd (σ p) o := by
  simp only [valIs, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (memAt_of_load (load_sound h hat)).symm
  · obtain ⟨a, hp, ha⟩ := any_holds h hat
    cases a <;> simp only [isCopyOfLoad, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hp
    obtain ⟨hd, hl⟩ := hp
    subst hd
    exact (show σ _ = σ _ from ha).trans (memAt_of_load (load_sound hl hat)).symm

/-- The thirteen values `ins` read the row at `p`: its rate cells `5 .. 12`, then its capacity
cells `0 .. 4`. -/
def rowInOk (atoms : List Atom) (p : V) (ins : List V) : Bool :=
  decide (ins.length = 13) &&
    (List.range 8).all (fun c => valIs atoms (ins.getD c default) p (5 + c)) &&
    (List.range 5).all fun i => valIs atoms (ins.getD (8 + i) default) p i

theorem rowIn_sound {p : V} {ins : List V} (h : rowInOk atoms p ins = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : ins.map σ = rowRate rd (σ p) ++ rowCap rd (σ p) := by
  simp only [rowInOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hl, hr⟩, hc⟩ := h
  have hR : (rowRate rd (σ p)).length = 8 := by simp [rowRate]
  refine list_eq_of_getD (n := 13) (by simp [hl]) (by simp [hR, rowCap]) fun c hc13 => ?_
  rw [DupSpec.getD_map_val ins c (by omega)]
  by_cases h8 : c < 8
  · rw [List.getD_append (rowRate rd (σ p)) (rowCap rd (σ p)) 0 c (by rw [hR]; exact h8),
      rowRate_getD _ _ c h8]
    exact valIs_sound (hr c h8) hat
  · obtain ⟨i, hi, rfl⟩ : ∃ i < 5, c = 8 + i := ⟨c - 8, by omega, by omega⟩
    rw [List.getD_append_right (rowRate rd (σ p)) (rowCap rd (σ p)) 0 (8 + i) (by rw [hR]; omega),
      hR, show 8 + i - 8 = i by omega, valIs_sound (hc i hi) hat]
    simp [rowCap, List.getD_eq_getElem?_getD, hi]

/-- The values `vs i`, `i < n`, written through `p` at `off + i`. -/
def storesOk (atoms : List Atom) (p : V) (off n : ℕ) (vs : ℕ → V) : Bool :=
  (List.range n).all fun i => atoms.any (isLoadAt (vs i) p (off + i))

theorem stores_sound {p : V} {off n : ℕ} {vs : ℕ → V} (h : storesOk atoms p off n vs = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : ∀ i < n, memAt rd (σ p * gen ^ off) i = σ (vs i) := by
  intro i hi
  simp only [storesOk, List.all_eq_true, List.mem_range] at h
  exact memAt_of_load ((loadHolds_mul_gen_pow rd _ off i _).mpr (load_sound (h i hi) hat))

theorem store_at {p : V} {v : V} {off k : ℕ} (h : atoms.any (isLoadAt v p (off + k)) = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) : memAt rd (σ p * gen ^ off) k = σ v :=
  memAt_of_load ((loadHolds_mul_gen_pow rd _ off k _).mpr (load_sound h hat))

/-- A row of four waiting scalars, from its words. -/
theorem rowRel_full {p : E} {ws : List E} (hws : ws.length = 4)
    (hpk : ∀ j < 4, PackOf (ws.getD j 0) (memAt rd p (5 + 2 * j)) (memAt rd p (6 + 2 * j))) :
    RowRel rd p ⟨rowCap rd p, ws.map (·, dsObserve)⟩ := by
  refine ⟨rfl, by simp [hws], fun k hk => ?_⟩
  have hk' : k < (ws.map (·, dsObserve)).length := by simp [hws]; exact hk
  split
  swap
  · exact absurd hk' (by assumption)
  refine ⟨by simp, ?_⟩
  have e : (ws.map (·, dsObserve))[k].1 = ws.getD k 0 := by
    rw [List.getElem_map, List.getD_eq_getElem _ _ (by omega : k < ws.length)]
  rw [e]
  exact hpk k hk

/-! ## The words of a chain -/

/-- The `fs_pack`s of a list of atoms: each packed value and its base. -/
def packsOf (atoms : List Atom) : List (V × ℕ) :=
  atoms.filterMap fun a => match a with
    | .hint (.limbs x (b :: _)) => some (x, b.idx)
    | _ => none

theorem DupSpec.wvals_eq (s : DupSpec) (σ : Val) :
    s.wvals σ = (List.range (4 * s.nb)).map fun w => σ (s.wV w) := by
  unfold DupSpec.wvals
  generalize s.nb = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih,
      show 4 * (n + 1) = 4 * n + 4 by ring, List.range_add, List.map_append, List.map_map]
    rfl

/-- The source of word `w` of a child: its public input's cells through `.n 59`, `.n 70`, its fresh
claim's through `.n 50`, its carried claim's through `.n 57`, then two zeros. -/
def l25Src (w : ℕ) : Option (V × ℕ) :=
  if w = 0 then some (.n 59, 0) else if w = 1 then some (.n 70, 1)
  else if w < 26 then some (.n 50, w - 2) else if w < 50 then some (.n 57, w - 26) else none

/-- `x` is loaded from its source, or is the constant zero. -/
def srcOk (atoms : List Atom) (x : V) : Option (V × ℕ) → Bool
  | some (p, o) => atoms.any (isLoadAt x p o)
  | none => atoms.any (isConstAt x 0 0)

theorem srcOk_some (atoms : List Atom) (x p : V) (o : ℕ) :
    srcOk atoms x (some (p, o)) = atoms.any (isLoadAt x p o) := rfl

theorem srcOk_none (atoms : List Atom) (x : V) :
    srcOk atoms x none = atoms.any (isConstAt x 0 0) := rfl

/-- Word `w` of the child at `x`. -/
noncomputable def l25Word (rd : Reader) (cpi cfresh ccarried x : E) (w : ℕ) : E :=
  if w < 2 then memAt rd (cpi * x ^ 2) w else if w < 26 then memAt rd (cfresh * x ^ 24) (w - 2)
  else if w < 50 then memAt rd (ccarried * x ^ 24) (w - 26) else 0

/-- The child's `52` words. -/
noncomputable def l25Words (rd : Reader) (cpi cfresh ccarried x : E) : List E :=
  (List.range 52).map (l25Word rd cpi cfresh ccarried x)

/-! ## The check -/

/-- **`__loop33`'s body, checked.** -/
def l25Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  let s : DupSpec := ⟨keccakBlocks A, packsOf A⟩
  loopShapeF fn "__loop33" && decide (fn.params.length = 8) && s.check A && decide (s.nb = 13) &&
  rowInOk A (.n 13) (s.ins 0) &&
  storesOk A (.n 13) 13 5 (fun i => (s.outs 12).getD (8 + i) default) &&
  (List.range 4).all (fun j => A.any (isLoadAt (.n (s.wB (48 + j) + 6)) (.n 13) (13 + (5 + 2 * j))) &&
    A.any (isLoadAt (.n (s.wB (48 + j) + 8)) (.n 13) (13 + (6 + 2 * j)))) &&
  (List.range 52).all (fun w => srcOk A (s.wV w) (l25Src w)) &&
  monoIs A (.n 13) (.n 2) (.n 0) 13 && monoIs A (.n 59) (.n 7) (.n 0) 2 &&
  monoIs A (.n 70) (.n 7) (.n 0) 2 && monoIs A (.n 50) (.n 3) (.n 0) 24 &&
  monoIs A (.n 57) (.n 5) (.n 0) 24 &&
  A.any (isLoadAt (.n 50) (.n 51) 0) && isMul A (.n 51) (.n 4) (.n 0) &&
  A.any (isLoadAt (.n 57) (.n 58) 0) && isMul A (.n 58) (.n 6) (.n 0)

set_option maxRecDepth 100000 in
theorem l25_ok : l25Ok (coreProgram.getD 401 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l25_idx : coreProgram.indexOf? "__loop33" = some 401 := by decide +kernel

/-! ## One child -/

/-- **Child `x`'s absorption**: its pointers in the tables `lf`, `lc`, and from a row of four
waiting scalars at `absorb·x^13`, the row after its words at `absorb·x^13·g^13`. -/
def L25Step (rd : Reader) (absorb cfresh lfT ccarried lcT cpi x : E) : Prop :=
  LoadHolds rd (lfT * x) 0 (cfresh * x ^ 24) ∧ LoadHolds rd (lcT * x) 0 (ccarried * x ^ 24) ∧
  ∀ st : Fs, st.pend.length = 4 → RowRel rd (absorb * x ^ 13) st →
    RowRel rd (absorb * x ^ 13 * gen ^ 13)
      (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)

theorem l25Src_lt2 {w : ℕ} (h : w < 2) : l25Src w = some (if w = 0 then V.n 59 else V.n 70, w) := by
  rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl <;> rfl

theorem l25Src_fresh {w : ℕ} (h1 : 2 ≤ w) (h2 : w < 26) : l25Src w = some (.n 50, w - 2) := by
  unfold l25Src
  split_ifs <;> first | rfl | (exfalso; omega)

theorem l25Src_carried {w : ℕ} (h1 : 26 ≤ w) (h2 : w < 50) : l25Src w = some (.n 57, w - 26) := by
  unfold l25Src
  split_ifs <;> first | rfl | (exfalso; omega)

theorem l25Src_pad {w : ℕ} (h1 : 50 ≤ w) : l25Src w = none := by
  unfold l25Src
  split_ifs <;> first | rfl | (exfalso; omega)

theorem l25_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop33" (x :: ps) []) :
    (∀ N absorb cfresh lfT ccarried lcT cpi, ps = [N, absorb, cfresh, lfT, ccarried, lcT, cpi] →
      L25Step rd absorb cfresh lfT ccarried lcT cpi x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop33" (x * gen :: ps) []) := by
  have hf := find_of_idx l25_idx (by rw [coreProgram_length]; omega)
  have hok := l25_ok
  simp only [l25Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hchk⟩, hnb⟩, hrin⟩, hcst⟩, hrst⟩, hsrc⟩, hm13⟩,
    hm59⟩, hm70⟩, hm50⟩, hm57⟩, hl50⟩, hm51⟩, hl57⟩, hm58⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N absorb cfresh lfT ccarried lcT cpi hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 401 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := hps
  have p13 : σ (.n 13) = absorb * x ^ 13 := by rw [monoIs_sound hm13 hat, h2, hx]
  have p59 : σ (.n 59) = cpi * x ^ 2 := by rw [monoIs_sound hm59 hat, h7, hx]
  have p70 : σ (.n 70) = cpi * x ^ 2 := by rw [monoIs_sound hm70 hat, h7, hx]
  have p50 : σ (.n 50) = cfresh * x ^ 24 := by rw [monoIs_sound hm50 hat, h3, hx]
  have p57 : σ (.n 57) = ccarried * x ^ 24 := by rw [monoIs_sound hm57 hat, h5, hx]
  refine ⟨?_, ?_, fun st hp hrow => ?_⟩
  · have := load_sound hl50 hat
    rwa [isMul_sound hm51 hat, h4, hx, p50] at this
  · have := load_sound hl57 hat
    rwa [isMul_sound hm58 hat, h6, hx, p57] at this
  -- the chain
  set A := atomsIn (loopPre (coreProgram.getD 401 default))
  set s : DupSpec := ⟨keccakBlocks A, packsOf A⟩
  obtain ⟨-, hwl, hK, hP, -⟩ := DupSpec.check_facts hchk hat
  have hin := rowIn_sound hrin hat
  rw [p13] at hin
  have hcan := (DupSpec.keccak_facts (hK 0 (by omega)).2.2 (hK 0 (by omega)).2.1).1
  rw [hin] at hcan
  have hperm := rowRel_perm hrow (fun c hc => hcan c (List.mem_append_left _ hc))
  rw [← hin] at hperm
  have hch := DupSpec.chain hchk hat st hp hperm
  -- the words
  have hw : s.wvals σ = l25Words rd cpi cfresh ccarried x := by
    rw [DupSpec.wvals_eq, hnb, l25Words]
    refine List.map_congr_left fun w hw => ?_
    have hw52 := List.mem_range.mp hw
    simp only [List.all_eq_true, List.mem_range] at hsrc
    have hs' := hsrc w hw52
    unfold l25Word
    by_cases ha : w < 2
    · rw [l25Src_lt2 ha, srcOk_some] at hs'
      have := memAt_of_load (load_sound hs' hat)
      rw [ite_pos' ha, ← this]
      rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
      · rw [ite_pos' rfl, p59]
      · rw [ite_neg' (show ¬ (1 = 0) by omega), p70]
    by_cases hb : w < 26
    · rw [l25Src_fresh (by omega) hb, srcOk_some] at hs'
      rw [ite_neg' ha, ite_pos' hb, ← p50]
      exact (memAt_of_load (load_sound hs' hat)).symm
    by_cases hc : w < 50
    · rw [l25Src_carried (by omega) hc, srcOk_some] at hs'
      rw [ite_neg' ha, ite_neg' hb, ite_pos' hc, ← p57]
      exact (memAt_of_load (load_sound hs' hat)).symm
    · rw [l25Src_pad (by omega), srcOk_none] at hs'
      rw [ite_neg' ha, ite_neg' hb, ite_neg' hc, const_sound hs' hat, word_zero]
  rw [← hw, hch, hnb]
  -- the row written
  have hcap : (List.range 5).map (fun i => σ ((s.outs (13 - 1)).getD (8 + i) default)) =
      rowCap rd (absorb * x ^ 13 * gen ^ 13) := by
    rw [rowCap, ← p13]
    refine List.map_congr_left fun i hi => ?_
    exact (stores_sound hcst hat i (List.mem_range.mp hi)).symm
  rw [hcap]
  refine rowRel_full (by simp [DupSpec.blk]) fun j hj => ?_
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hrst
  obtain ⟨r6, r8⟩ := hrst j hj
  rw [← p13, store_at r6 hat, store_at r8 hat]
  have hwj : (s.blk σ (13 - 1)).getD j 0 = σ (s.wV (48 + j)) := by
    simp [DupSpec.blk, List.getD_eq_getElem?_getD, hj]
  rw [hwj]
  exact packOf_of (hP (48 + j) (by rw [hwl, hnb]; omega))

end
end LeanVM.Guest.B1.Main
