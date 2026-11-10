/-
  LeanVM.Guest.B1.Main.AggSqueeze

  `aggregate_claims`' squeezing loop (`__loop34`: the lambdas and the batched claim) and its
  weighing loop (`__loop35`: the batched equality weight).
-/

module

public import LeanVM.Guest.B1.Main.AggAbsorb

/-!
# `__loop34` and `__loop35`

* `l26_step` (`__loop34`, core function `445`): iteration `x = g^c` reads record `c` of
  `bc_chain` (`chain·x^2`, two words: `λ`'s power `λ^(2c)` and the running claim), writes the
  power times `λ²` into word `2` (record `c + 1`'s power) and the running claim plus the power
  times `fresh[23] + λ · carried[23]` of the child's claims (through the pointer tables `lf`,
  `lc`) into word `3` (record `c + 1`'s claim) (`L26Step`).
* `l27_step` (`__loop35`, core function `447`): iteration `x = g^c` adds
  `p · (eq(fresh, r) + λ · eq(carried, r))` to the running weight `w[c]` into `w[c + 1]`, `p`
  record `c`'s power, `r = 1 + r1`, `r1` the `23` coordinates at `pt1` (`bc_point1 = 1 + bc_point`,
  `L27Step`); the equality polynomials are products `Π (p_j + r1_j) = Π (1 + p_j + r_j)` checked
  by evaluation (`eqChainOk`, `one_add_add_one_add`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

variable {rd : Reader} {σ : Val} {atoms : List Atom}

/-! ## Templates as atoms -/

/-- Every atom of `as` is in the list. -/
def allIn (atoms as : List Atom) : Bool := as.all fun a => atoms.any (atomEqb a)

theorem allIn_holds {as : List Atom} (h : allIn atoms as = true) (hat : ∀ a ∈ atoms, a.Holds rd σ)
    (C : CallRel) (kret : List E → Prop) : Stmt.HoldsList C rd σ (as.map Stmt.atom) True kret := by
  have hall : ∀ a ∈ as, a.Holds rd σ := by
    intro a ha
    simp only [allIn, List.all_eq_true] at h
    obtain ⟨a', ha', he⟩ := List.any_eq_true.mp (h a ha)
    rw [atomEqb_sound he]
    exact hat a' ha'
  have hA : AllAtoms (as.map Stmt.atom) := by
    intro s hs
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hs
    exact ⟨a, rfl⟩
  exact (holdsList_atoms hA True kret).mpr ⟨fun a ha => hall a (by
    obtain ⟨a', ha', he⟩ := List.mem_map.mp ha
    cases he
    exact ha'), trivial⟩

/-! ## `__loop34`: the powers of `λ` and the running claim -/

/-- **`__loop34`'s body, checked.** -/
def l26Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop34" && decide (fn.params.length = 7) &&
  isMul A (.n 7) (.n 0) (.n 0) && isMul A (.n 8) (.n 2) (.n 7) &&
  A.any (isLoadAt (.n 9) (.n 8) 0) &&
  isMul A (.n 10) (.n 3) (.n 0) && A.any (isLoadAt (.n 11) (.n 10) 0) &&
  isMul A (.n 12) (.n 4) (.n 0) && A.any (isLoadAt (.n 13) (.n 12) 0) &&
  isMul A (.n 14) (.n 9) (.n 5) && A.any (isLoadAt (.n 14) (.n 8) 2) &&
  A.any (isLoadAt (.n 15) (.n 8) 1) && A.any (isLoadAt (.n 16) (.n 11) 23) &&
  A.any (isLoadAt (.n 17) (.n 13) 23) && isMul A (.n 18) (.n 6) (.n 17) &&
  A.any (isAddAt (.n 19) (.n 16) (.n 18)) && isMul A (.n 20) (.n 9) (.n 19) &&
  A.any (isAddAt (.n 21) (.n 15) (.n 20)) && A.any (isLoadAt (.n 21) (.n 8) 3)

set_option maxRecDepth 100000 in
theorem l26_ok : l26Ok (coreProgram.getD 445 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l26_idx : coreProgram.indexOf? "__loop34" = some 445 := by decide +kernel

/-- **Child `x`'s record**: the record at `chain·x^2` holds `λ`'s power and the running claim;
the next record holds the power times `λ²` and the running claim plus the power times
`fresh[23] + λ · carried[23]` of the child's claims (through the pointer tables `lf`, `lc`). -/
def L26Step (rd : Reader) (chainT lfT lcT lamSq lam x : E) : Prop :=
  LoadHolds rd (chainT * x ^ 2) 2 (memAt rd (chainT * x ^ 2) 0 * lamSq) ∧
  LoadHolds rd (chainT * x ^ 2) 3 (memAt rd (chainT * x ^ 2) 1 +
    memAt rd (chainT * x ^ 2) 0 * (memAt rd (memAt rd (lfT * x) 0) 23 +
      lam * memAt rd (memAt rd (lcT * x) 0) 23))

theorem l26_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop34" (x :: ps) []) :
    (∀ N chainT lfT lcT lamSq lam, ps = [N, chainT, lfT, lcT, lamSq, lam] →
      L26Step rd chainT lfT lcT lamSq lam x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop34" (x * gen :: ps) []) := by
  have hf := find_of_idx l26_idx (by rw [coreProgram_length]; omega)
  have hok := l26_ok
  simp only [l26Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm7⟩, hm8⟩, hl9⟩, hm10⟩, hl11⟩, hm12⟩, hl13⟩, hm14⟩,
    hl14⟩, hl15⟩, hl16⟩, hl17⟩, hm18⟩, ha19⟩, hm20⟩, ha21⟩, hl21⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N chainT lfT lcT lamSq lam hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 445 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hps
  have p8 : σ (.n 8) = chainT * x ^ 2 := by
    rw [isMul_sound hm8 hat, isMul_sound hm7 hat, h2, hx, sq]
  have e9 := memAt_of_load (load_sound hl9 hat)
  have e11 := memAt_of_load (load_sound hl11 hat)
  have e13 := memAt_of_load (load_sound hl13 hat)
  have e15 := memAt_of_load (load_sound hl15 hat)
  have e16 := memAt_of_load (load_sound hl16 hat)
  have e17 := memAt_of_load (load_sound hl17 hat)
  rw [p8] at e9 e15
  rw [isMul_sound hm10 hat, h3, hx] at e11
  rw [isMul_sound hm12 hat, h4, hx] at e13
  refine ⟨?_, ?_⟩
  · have := load_sound hl14 hat
    rwa [p8, isMul_sound hm14 hat, h5, ← e9] at this
  · have := load_sound hl21 hat
    rwa [p8, add_sound ha21 hat, isMul_sound hm20 hat, add_sound ha19 hat, isMul_sound hm18 hat,
      h6, ← e9, ← e15, ← e16, ← e17, ← e11, ← e13] at this

/-! ## Equality weights -/

/-- In characteristic `2`, `(1 + a) + (1 + b) = a + b`: an equality factor against `1 + r` is
one `ADD`. -/
theorem one_add_add_one_add (a b : E) : 1 + a + (1 + b) = a + b := by
  linear_combination e_add_self 1

/-- `t = p[j] + r1[j]`, one `ADD` of loads through `pP`, `pR` (`r1` is `1 + r`: `bc_point1`). -/
def eqTermOk (A : List Atom) (t pP pR : V) (j : ℕ) : Bool :=
  match addOf A t with
  | some (pv, r) => A.any (isLoadAt pv pP j) && A.any (isLoadAt r pR j)
  | none => false

theorem eqTerm_sound {t pP pR : V} {j : ℕ} (h : eqTermOk atoms t pP pR j = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ t = memAt rd (σ pP) j + memAt rd (σ pR) j := by
  unfold eqTermOk at h
  split at h
  · rename_i pv r har
    simp only [Bool.and_eq_true] at h
    rw [addOf_sound har hat, memAt_of_load (load_sound h.1 hat),
      memAt_of_load (load_sound h.2 hat)]
  · exact absurd h (by simp)

/-- `out` is `Π_{j < n} (p[j] + r1[j])`, its factors through `MUL`s from the last, the first
factor alone. -/
def eqChainOk (A : List Atom) (pP pR : V) : ℕ → V → Bool
  | 0, _ => false
  | 1, t => eqTermOk A t pP pR 0
  | n + 2, out => match mulOf A out with
    | some (prev, t) => eqTermOk A t pP pR (n + 1) && eqChainOk A pP pR (n + 1) prev
    | none => false

theorem memRun_succ (rd : Reader) (p : E) (n : ℕ) :
    memRun rd p (n + 1) = memRun rd p n ++ [memAt rd p n] := by
  simp [memRun, List.range_succ]

theorem eqEval_snoc (l r : List E) (a b : E) (h : l.length = r.length) :
    eqEval (l ++ [a]) (r ++ [b]) = eqEval l r * (1 + a + b) := by
  rw [eqEval, eqEval, List.zipWith_append h, List.foldl_append]
  rfl

/-- **The chain is the equality polynomial** of the points at `pP` and `1 + r1`, `r1` at `pR`. -/
theorem eqChain_sound {pP pR : V} : ∀ {n : ℕ} {out : V}, eqChainOk atoms pP pR n out = true →
    (∀ a ∈ atoms, a.Holds rd σ) →
    σ out = eqEval (memRun rd (σ pP) n) ((memRun rd (σ pR) n).map (1 + ·))
  | 0, _, h, _ => absurd h (by simp [eqChainOk])
  | 1, t, h, hat => by
    rw [eqTerm_sound h hat]
    simp only [memRun, List.range_one, List.map_cons, List.map_nil, eqEval, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.foldl_cons, List.foldl_nil, one_mul, one_add_add_one_add]
  | n + 2, out, h, hat => by
    unfold eqChainOk at h
    split at h
    · rename_i prev t hm
      simp only [Bool.and_eq_true] at h
      rw [mulOf_sound hm hat, eqChain_sound h.2 hat, eqTerm_sound h.1 hat,
        memRun_succ rd _ (n + 1), memRun_succ rd _ (n + 1), List.map_append, List.map_singleton,
        eqEval_snoc _ _ _ _ (by simp), one_add_add_one_add]
    · exact absurd h (by simp)

/-- The point `r` from `r1 = 1 + r`, coordinatewise. -/
theorem map_one_add_memRun {p1 p : E} {n : ℕ} (h : ∀ k < n, memAt rd p1 k = 1 + memAt rd p k) :
    (memRun rd p1 n).map (1 + ·) = memRun rd p n := by
  simp only [memRun, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  rw [Function.comp_apply, h k (List.mem_range.mp hk), ← add_assoc, e_add_self, zero_add]

/-- `1 + ·` twice is the identity. -/
theorem map_one_add_twice (l : List E) : (l.map (1 + ·)).map (1 + ·) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun x _ => ?_
  rw [Function.comp_apply, ← add_assoc, e_add_self, zero_add, id]

/-! ## `__loop35`: the weights -/

/-- **`__loop35`'s body, checked.** -/
def l27Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn "__loop35" && decide (fn.params.length = 8) &&
  isMul A (.n 8) (.n 2) (.n 0) && A.any (isLoadAt (.n 9) (.n 8) 0) &&
  isMul A (.n 10) (.n 3) (.n 0) && A.any (isLoadAt (.n 11) (.n 10) 0) &&
  eqChainOk A (.n 9) (.n 4) 23 (.n 167) && eqChainOk A (.n 11) (.n 4) 23 (.n 170) &&
  isMul A (.n 171) (.n 0) (.n 0) && isMul A (.n 172) (.n 5) (.n 171) &&
  isMul A (.n 173) (.n 6) (.n 0) && A.any (isLoadAt (.n 174) (.n 173) 0) &&
  A.any (isLoadAt (.n 175) (.n 172) 0) && isMul A (.n 176) (.n 7) (.n 170) &&
  A.any (isAddAt (.n 177) (.n 167) (.n 176)) && isMul A (.n 178) (.n 175) (.n 177) &&
  A.any (isAddAt (.n 179) (.n 174) (.n 178)) && isMul A (.n 180) (.n 6) (.n 0) &&
  A.any (isLoadAt (.n 179) (.n 180) 1)

set_option maxRecDepth 100000 in
theorem l27_ok : l27Ok (coreProgram.getD 447 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l27_idx : coreProgram.indexOf? "__loop35" = some 447 := by decide +kernel

/-- **Child `x`'s weight**: `w[x·g] = w[x] + p · (eq(fresh, r) + λ · eq(carried, r))`, `p` the
power of `λ` at `chain·x^2`, the claims' points through the pointer tables, `r = 1 + r1`, `r1`
the 23 words at `pt1` (`bc_point1`). -/
def L27Step (rd : Reader) (lfT lcT pt1 chainT wT lam x : E) : Prop :=
  LoadHolds rd (wT * x) 1 (memAt rd (wT * x) 0 + memAt rd (chainT * x ^ 2) 0 *
    (eqEval (memRun rd (memAt rd (lfT * x) 0) 23) ((memRun rd pt1 23).map (1 + ·)) +
      lam * eqEval (memRun rd (memAt rd (lcT * x) 0) 23) ((memRun rd pt1 23).map (1 + ·))))

theorem l27_step {x : E} {ps : List E} (h : coreProgram.Rel rd "__loop35" (x :: ps) []) :
    (∀ N lfT lcT pt1 chainT wT lam, ps = [N, lfT, lcT, pt1, chainT, wT, lam] →
      L27Step rd lfT lcT pt1 chainT wT lam x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop35" (x * gen :: ps) []) := by
  have hf := find_of_idx l27_idx (by rw [coreProgram_length]; omega)
  have hok := l27_ok
  simp only [l27Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm8⟩, hl9⟩, hm10⟩, hl11⟩, he1⟩, he2⟩, hm171⟩, hm172⟩,
    hm173⟩, hl174⟩, hl175⟩, hm176⟩, ha177⟩, hm178⟩, ha179⟩, hm180⟩, hl179⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N lfT lcT pt1 chainT wT lam hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 447 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := hps
  have e9 := memAt_of_load (load_sound hl9 hat)
  have e11 := memAt_of_load (load_sound hl11 hat)
  rw [isMul_sound hm8 hat, h2, hx] at e9
  rw [isMul_sound hm10 hat, h3, hx] at e11
  have ef := eqChain_sound he1 hat
  have ec := eqChain_sound he2 hat
  rw [← e9, h4] at ef
  rw [← e11, h4] at ec
  have e174 := memAt_of_load (load_sound hl174 hat)
  have e175 := memAt_of_load (load_sound hl175 hat)
  have e179 := load_sound hl179 hat
  rw [isMul_sound hm173 hat, h6, hx] at e174
  rw [isMul_sound hm172 hat, isMul_sound hm171 hat, h5, hx, ← sq] at e175
  rw [isMul_sound hm180 hat, h6, hx] at e179
  unfold L27Step
  rw [add_sound ha179 hat, isMul_sound hm178 hat, add_sound ha177 hat, isMul_sound hm176 hat, h7,
    ← e174, ← e175, ef, ec] at e179
  exact e179

end
end LeanVM.Guest.B1.Main
