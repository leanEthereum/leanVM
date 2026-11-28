/-
  LeanVM.Guest.B1.Main.AggSqueeze

  `aggregate_claims`' loops after the absorption: the fresh claims' values folded at the column
  challenges (`aggregate_claims_loop1`), the lambdas and the batched claim (`aggregate_claims_loop2`),
  and the batched equality weight (`aggregate_claims_loop3`).
-/

module

public import LeanVM.Guest.B1.Main.AggAbsorb
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop1»
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop2»
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop3»
import LeanVM.Guest.B1.Common.Find

/-!
# `aggregate_claims_loop1`, `aggregate_claims_loop2` and `aggregate_claims_loop3`

* `a1_step` (`aggregate_claims_loop1`): iteration `x = g^c` writes at `fresh_val·x` the sum
  `Σ_{j < 36} eq_col[j] · fresh[19 + j]` of the child's fresh claim's values (through the pointer
  table `lf`) weighed by the column challenges' equality table `eq_col` (`A1Step`, `fvAcc`).
* `a2_step` (`aggregate_claims_loop2`): iteration `x = g^c` reads record `c` of `bc_chain`
  (`chain·x^2`: `λ`'s power `λ^(2c)` and the running claim), writes the power times `λ²` into word
  `2` and the running claim plus the power times `fresh_val[x] + λ · carried[25]` into word `3`
  (`A2Step`).
* `a3_step` (`aggregate_claims_loop3`): iteration `x = g^c` adds
  `p · (eq(fresh, r[..19]) · eq_cols + λ · eq(carried, r))` to the running weight, `p` record `c`'s
  power, `r = 1 + r1`, `r1` the `25` coordinates at `pt1` (`A3Step`); the equality polynomials are
  products `Π (p_j + r1_j) = Π (1 + p_j + r_j)` checked by evaluation (`eqChainOk`).
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

/-! ## `aggregate_claims_loop1`: the fresh claims' values at the column challenges -/

/-- `t = eq_col[j] · fresh[19 + j]`, one `MUL` of loads through `pE`, `pF`. -/
def fvTermOk (A : List Atom) (t pE pF : V) (j : ℕ) : Bool :=
  match mulOf A t with
  | some (a, b) => A.any (isLoadAt a pE j) && A.any (isLoadAt b pF (19 + j))
  | none => false

theorem fvTerm_sound {t pE pF : V} {j : ℕ} (h : fvTermOk atoms t pE pF j = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ t = memAt rd (σ pE) j * memAt rd (σ pF) (19 + j) := by
  unfold fvTermOk at h
  split at h
  · rename_i a b hm
    simp only [Bool.and_eq_true] at h
    rw [mulOf_sound hm hat, memAt_of_load (load_sound h.1 hat), memAt_of_load (load_sound h.2 hat)]
  · exact absurd h (by simp)

/-- `out` is `Σ_{j < n} eq_col[j] · fresh[19 + j]`, its terms through `ADD`s from the last, the
first term alone. -/
def fvChainOk (A : List Atom) (pE pF : V) : ℕ → V → Bool
  | 0, _ => false
  | 1, t => fvTermOk A t pE pF 0
  | n + 2, out => match addOf A out with
    | some (prev, t) => fvTermOk A t pE pF (n + 1) && fvChainOk A pE pF (n + 1) prev
    | none => false

/-- `Σ_{j < n} e[j] · f[19 + j]`. -/
noncomputable def fvAcc (rd : Reader) (e f : E) : ℕ → E
  | 0 => 0
  | n + 1 => fvAcc rd e f n + memAt rd e n * memAt rd f (19 + n)

theorem fvChain_sound {pE pF : V} : ∀ {n : ℕ} {out : V}, fvChainOk atoms pE pF n out = true →
    (∀ a ∈ atoms, a.Holds rd σ) → σ out = fvAcc rd (σ pE) (σ pF) n
  | 0, _, h, _ => absurd h (by simp [fvChainOk])
  | 1, t, h, hat => by
    rw [fvTerm_sound h hat, fvAcc, fvAcc, zero_add]
  | n + 2, out, h, hat => by
    unfold fvChainOk at h
    split at h
    · rename_i prev t hm
      simp only [Bool.and_eq_true] at h
      rw [addOf_sound hm hat, fvChain_sound h.2 hat, fvTerm_sound h.1 hat]
      rfl
    · exact absurd h (by simp)

/-- **`aggregate_claims_loop1`'s body, checked.** -/
def a1Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «aggregate_claims_loop1» && decide (fn.params.length = 5) &&
  isMul A (.n (val% «aggregate_claims_loop1» "fresh~0")) (.n (val% «aggregate_claims_loop1» "fresh_row")) (.n (val% «aggregate_claims_loop1» "xc")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop1» "fresh")) (.n (val% «aggregate_claims_loop1» "fresh~0")) 0) &&
  fvChainOk A (.n (val% «aggregate_claims_loop1» "eq_col")) (.n (val% «aggregate_claims_loop1» "fresh")) 36 (.n (val% «aggregate_claims_loop1» "fv@36")) &&
  isMul A (.n (val% «aggregate_claims_loop1» "s3#0")) (.n (val% «aggregate_claims_loop1» "fresh_val")) (.n (val% «aggregate_claims_loop1» "xc")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop1» "fv@36")) (.n (val% «aggregate_claims_loop1» "s3#0")) 0)

set_option maxRecDepth 100000 in
theorem a1_ok : a1Ok (coreProgram.getD idx% «aggregate_claims_loop1» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem a1_idx : coreProgram.indexOf? name% «aggregate_claims_loop1» = some
    idx% «aggregate_claims_loop1» :=
  coreProgram_indexOf?_at (j := idx% «aggregate_claims_loop1») rfl

/-- **Child `x`'s folded fresh value**: `fresh_val[x] = Σ_{j < 36} eq_col[j] · fresh[19 + j]`, the
child's fresh claim through the pointer table `lf`. -/
def A1Step (rd : Reader) (lfT eqc fvT x : E) : Prop :=
  LoadHolds rd (fvT * x) 0 (fvAcc rd eqc (memAt rd (lfT * x) 0) 36)

theorem a1_step {x : E} {ps : List E} (h : coreProgram.Rel rd name% «aggregate_claims_loop1» (x ::
    ps) []) :
    (∀ N lfT eqc fvT, ps = [N, lfT, eqc, fvT] → A1Step rd lfT eqc fvT x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd name% «aggregate_claims_loop1» (x * gen :: ps)
          []) := by
  have hf := find_of_idx a1_idx
  have hok := a1_ok
  simp only [a1Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm5⟩, hl6⟩, hfv⟩, hm150⟩, hl150⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N lfT eqc fvT hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD idx% «aggregate_claims_loop1» default).params =
      [V.n (val% «aggregate_claims_loop1» "xc"), V.n (val% «aggregate_claims_loop1» "bound"), V.n (val% «aggregate_claims_loop1» "fresh_row"), V.n (val% «aggregate_claims_loop1» "eq_col"), V.n (val% «aggregate_claims_loop1» "fresh_val")] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4⟩ := hps
  have e6 := memAt_of_load (load_sound hl6 hat)
  rw [isMul_sound hm5 hat, h2, hx] at e6
  have hv := fvChain_sound hfv hat
  rw [h3, ← e6] at hv
  have := load_sound hl150 hat
  rw [isMul_sound hm150 hat, h4, hx, hv] at this
  exact this

/-! ## `aggregate_claims_loop2`: the powers of `λ` and the running claim -/

/-- **`aggregate_claims_loop2`'s body, checked.** -/
def a2Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «aggregate_claims_loop2» && decide (fn.params.length = 8) &&
  isMul A (.n (val% «aggregate_claims_loop2» "row~0")) (.n (val% «aggregate_claims_loop2» "xc")) (.n (val% «aggregate_claims_loop2» "xc")) && isMul A (.n (val% «aggregate_claims_loop2» "row")) (.n (val% «aggregate_claims_loop2» "bc_chain")) (.n (val% «aggregate_claims_loop2» "row~0")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "lam_pow")) (.n (val% «aggregate_claims_loop2» "row")) 0) &&
  isMul A (.n (val% «aggregate_claims_loop2» "carried~0")) (.n (val% «aggregate_claims_loop2» "carried_row")) (.n (val% «aggregate_claims_loop2» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "carried")) (.n (val% «aggregate_claims_loop2» "carried~0")) 0) &&
  isMul A (.n (val% «aggregate_claims_loop2» "s5#0")) (.n (val% «aggregate_claims_loop2» "lam_pow")) (.n (val% «aggregate_claims_loop2» "lam_sq")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s5#0")) (.n (val% «aggregate_claims_loop2» "row")) 2) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s6#0")) (.n (val% «aggregate_claims_loop2» "row")) 1) &&
  isMul A (.n (val% «aggregate_claims_loop2» "s6#1")) (.n (val% «aggregate_claims_loop2» "fresh_val")) (.n (val% «aggregate_claims_loop2» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s6#2")) (.n (val% «aggregate_claims_loop2» "s6#1")) 0) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s6#3")) (.n (val% «aggregate_claims_loop2» "carried")) 25) && isMul A (.n (val% «aggregate_claims_loop2» "s6#4")) (.n (val% «aggregate_claims_loop2» "lam")) (.n (val% «aggregate_claims_loop2» "s6#3")) &&
  A.any (isAddAt (.n (val% «aggregate_claims_loop2» "s6#5")) (.n (val% «aggregate_claims_loop2» "s6#2")) (.n (val% «aggregate_claims_loop2» "s6#4"))) && isMul A (.n (val% «aggregate_claims_loop2» "s6#6")) (.n (val% «aggregate_claims_loop2» "lam_pow")) (.n (val% «aggregate_claims_loop2» "s6#5")) &&
  A.any (isAddAt (.n (val% «aggregate_claims_loop2» "s6#7")) (.n (val% «aggregate_claims_loop2» "s6#0")) (.n (val% «aggregate_claims_loop2» "s6#6"))) && A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s6#7")) (.n (val% «aggregate_claims_loop2» "row")) 3)

set_option maxRecDepth 100000 in
theorem a2_ok : a2Ok (coreProgram.getD idx% «aggregate_claims_loop2» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem a2_idx : coreProgram.indexOf? name% «aggregate_claims_loop2» = some
    idx% «aggregate_claims_loop2» :=
  coreProgram_indexOf?_at (j := idx% «aggregate_claims_loop2») rfl

/-- **Child `x`'s record**: the record at `chain·x^2` holds `λ`'s power and the running claim;
the next record holds the power times `λ²` and the running claim plus the power times
`fresh_val[x] + λ · carried[25]` (the carried claim through the pointer table `lc`). -/
def A2Step (rd : Reader) (chainT lcT lamSq fvT lam x : E) : Prop :=
  LoadHolds rd (chainT * x ^ 2) 2 (memAt rd (chainT * x ^ 2) 0 * lamSq) ∧
  LoadHolds rd (chainT * x ^ 2) 3 (memAt rd (chainT * x ^ 2) 1 +
    memAt rd (chainT * x ^ 2) 0 * (memAt rd (fvT * x) 0 +
      lam * memAt rd (memAt rd (lcT * x) 0) 25))

theorem a2_step {x : E} {ps : List E} (h : coreProgram.Rel rd name% «aggregate_claims_loop2» (x ::
    ps) []) :
    (∀ N chainT lfT lcT lamSq fvT lam, ps = [N, chainT, lfT, lcT, lamSq, fvT, lam] →
      A2Step rd chainT lcT lamSq fvT lam x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd name% «aggregate_claims_loop2» (x * gen :: ps)
          []) := by
  have hf := find_of_idx a2_idx
  have hok := a2_ok
  simp only [a2Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm7⟩, hm8⟩, hl9⟩, hm12⟩, hl13⟩, hm14⟩, hl14⟩, hl15⟩, hm16⟩, hl16⟩, hl17⟩, hm18⟩, ha19⟩, hm20⟩, ha21⟩, hl21⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N chainT lfT lcT lamSq fvT lam hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD idx% «aggregate_claims_loop2» default).params =
      [V.n (val% «aggregate_claims_loop2» "xc"), V.n (val% «aggregate_claims_loop2» "bound"), V.n (val% «aggregate_claims_loop2» "bc_chain"), V.n (val% «aggregate_claims_loop2» "fresh_row"), V.n (val% «aggregate_claims_loop2» "carried_row"), V.n (val% «aggregate_claims_loop2» "lam_sq"), V.n (val% «aggregate_claims_loop2» "fresh_val"), V.n (val% «aggregate_claims_loop2» "lam")] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, -, h4, h5, h6, h7⟩ := hps
  have p8 : σ (.n (val% «aggregate_claims_loop2» "row")) = chainT * x ^ 2 := by
    rw [isMul_sound hm8 hat, isMul_sound hm7 hat, h2, hx, sq]
  have e9 := memAt_of_load (load_sound hl9 hat)
  have e13 := memAt_of_load (load_sound hl13 hat)
  have e15 := memAt_of_load (load_sound hl15 hat)
  have e16 := memAt_of_load (load_sound hl16 hat)
  have e17 := memAt_of_load (load_sound hl17 hat)
  rw [p8] at e9 e15
  rw [isMul_sound hm12 hat, h4, hx] at e13
  rw [isMul_sound hm16 hat, h6, hx] at e16
  refine ⟨?_, ?_⟩
  · have := load_sound hl14 hat
    rwa [p8, isMul_sound hm14 hat, h5, ← e9] at this
  · have := load_sound hl21 hat
    rwa [p8, add_sound ha21 hat, isMul_sound hm20 hat, add_sound ha19 hat, isMul_sound hm18 hat,
      h7, ← e9, ← e15, ← e16, ← e17, ← e13] at this

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

/-! ## `aggregate_claims_loop3`: the weights -/

/-- **`aggregate_claims_loop3`'s body, checked.** -/
def a3Ok (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  loopShapeF fn name% «aggregate_claims_loop3» && decide (fn.params.length = 9) &&
  isMul A (.n (val% «aggregate_claims_loop3» "s0#0")) (.n (val% «aggregate_claims_loop3» "fresh_row")) (.n (val% «aggregate_claims_loop3» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop3» "fresh")) (.n (val% «aggregate_claims_loop3» "s0#0")) 0) &&
  isMul A (.n (val% «aggregate_claims_loop3» "s1#0")) (.n (val% «aggregate_claims_loop3» "carried_row")) (.n (val% «aggregate_claims_loop3» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop3» "carried")) (.n (val% «aggregate_claims_loop3» "s1#0")) 0) &&
  eqChainOk A (.n (val% «aggregate_claims_loop3» "fresh")) (.n (val% «aggregate_claims_loop3» "bc_point1")) 19 (.n (val% «aggregate_claims_loop3» "eq_fresh@19")) && eqChainOk A (.n (val% «aggregate_claims_loop3» "carried")) (.n (val% «aggregate_claims_loop3» "bc_point1")) 25 (.n (val% «aggregate_claims_loop3» "eq_carried@25")) &&
  isMul A (.n (val% «aggregate_claims_loop3» "s3#0")) (.n (val% «aggregate_claims_loop3» "xc")) (.n (val% «aggregate_claims_loop3» "xc")) && isMul A (.n (val% «aggregate_claims_loop3» "s3#1")) (.n (val% «aggregate_claims_loop3» "bc_chain")) (.n (val% «aggregate_claims_loop3» "s3#0")) &&
  isMul A (.n (val% «aggregate_claims_loop3» "s4#0")) (.n (val% «aggregate_claims_loop3» "bc_wsum")) (.n (val% «aggregate_claims_loop3» "xc")) && A.any (isLoadAt (.n (val% «aggregate_claims_loop3» "s4#1")) (.n (val% «aggregate_claims_loop3» "s4#0")) 0) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop3» "s4#2")) (.n (val% «aggregate_claims_loop3» "s3#1")) 0) &&
  isMul A (.n (val% «aggregate_claims_loop3» "s4#3")) (.n (val% «aggregate_claims_loop3» "eq_fresh@19")) (.n (val% «aggregate_claims_loop3» "eq_cols")) &&
  isMul A (.n (val% «aggregate_claims_loop3» "s4#4")) (.n (val% «aggregate_claims_loop3» "lam")) (.n (val% «aggregate_claims_loop3» "eq_carried@25")) &&
  A.any (isAddAt (.n (val% «aggregate_claims_loop3» "s4#5")) (.n (val% «aggregate_claims_loop3» "s4#3")) (.n (val% «aggregate_claims_loop3» "s4#4"))) && isMul A (.n (val% «aggregate_claims_loop3» "s4#6")) (.n (val% «aggregate_claims_loop3» "s4#2")) (.n (val% «aggregate_claims_loop3» "s4#5")) &&
  A.any (isAddAt (.n (val% «aggregate_claims_loop3» "s4#7")) (.n (val% «aggregate_claims_loop3» "s4#1")) (.n (val% «aggregate_claims_loop3» "s4#6"))) && isMul A (.n (val% «aggregate_claims_loop3» "s4#8")) (.n (val% «aggregate_claims_loop3» "bc_wsum")) (.n (val% «aggregate_claims_loop3» "xc")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop3» "s4#7")) (.n (val% «aggregate_claims_loop3» "s4#8")) 1)

set_option maxRecDepth 100000 in
theorem a3_ok : a3Ok (coreProgram.getD idx% «aggregate_claims_loop3» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem a3_idx : coreProgram.indexOf? name% «aggregate_claims_loop3» = some
    idx% «aggregate_claims_loop3» :=
  coreProgram_indexOf?_at (j := idx% «aggregate_claims_loop3») rfl

/-- **Child `x`'s weight**: `w[x·g] = w[x] + p · (eq(fresh, r[..19]) · eqc + λ · eq(carried, r))`,
`p` the power of `λ` at `chain·x^2`, the claims' points through the pointer tables, `r = 1 + r1`,
`r1` the `25` words at `pt1` (`bc_point1`), `eqc` the column factor. -/
def A3Step (rd : Reader) (lfT lcT pt1 chainT wT eqc lam x : E) : Prop :=
  LoadHolds rd (wT * x) 1 (memAt rd (wT * x) 0 + memAt rd (chainT * x ^ 2) 0 *
    (eqEval (memRun rd (memAt rd (lfT * x) 0) 19) ((memRun rd pt1 19).map (1 + ·)) * eqc +
      lam * eqEval (memRun rd (memAt rd (lcT * x) 0) 25) ((memRun rd pt1 25).map (1 + ·))))

theorem a3_step {x : E} {ps : List E} (h : coreProgram.Rel rd name% «aggregate_claims_loop3» (x ::
    ps) []) :
    (∀ N lfT lcT pt1 chainT wT eqc lam, ps = [N, lfT, lcT, pt1, chainT, wT, eqc, lam] →
      A3Step rd lfT lcT pt1 chainT wT eqc lam x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd name% «aggregate_claims_loop3» (x * gen :: ps)
          []) := by
  have hf := find_of_idx a3_idx
  have hok := a3_ok
  simp only [a3Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm9⟩, hl10⟩, hm11⟩, hl12⟩, he1⟩, he2⟩, hm168⟩, hm169⟩, hm170⟩, hl171⟩, hl172⟩, hm173⟩, hm174⟩, ha175⟩, hm176⟩, ha177⟩, hm178⟩, hl177⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N lfT lcT pt1 chainT wT eqc lam hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD idx% «aggregate_claims_loop3» default).params =
      [V.n (val% «aggregate_claims_loop3» "xc"), V.n (val% «aggregate_claims_loop3» "bound"), V.n (val% «aggregate_claims_loop3» "fresh_row"), V.n (val% «aggregate_claims_loop3» "carried_row"), V.n (val% «aggregate_claims_loop3» "bc_point1"), V.n (val% «aggregate_claims_loop3» "bc_chain"), V.n (val% «aggregate_claims_loop3» "bc_wsum"), V.n (val% «aggregate_claims_loop3» "eq_cols"), V.n (val% «aggregate_claims_loop3» "lam")] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8⟩ := hps
  have e10 := memAt_of_load (load_sound hl10 hat)
  have e12 := memAt_of_load (load_sound hl12 hat)
  rw [isMul_sound hm9 hat, h2, hx] at e10
  rw [isMul_sound hm11 hat, h3, hx] at e12
  have ef := eqChain_sound he1 hat
  have ec := eqChain_sound he2 hat
  rw [← e10, h4] at ef
  rw [← e12, h4] at ec
  have e171 := memAt_of_load (load_sound hl171 hat)
  have e172 := memAt_of_load (load_sound hl172 hat)
  have e177 := load_sound hl177 hat
  rw [isMul_sound hm170 hat, h6, hx] at e171
  rw [isMul_sound hm169 hat, isMul_sound hm168 hat, h5, hx, ← sq] at e172
  rw [isMul_sound hm178 hat, h6, hx] at e177
  unfold A3Step
  rw [add_sound ha177 hat, isMul_sound hm176 hat, add_sound ha175 hat, isMul_sound hm173 hat,
    isMul_sound hm174 hat, h7, h8, ← e171, ← e172, ef, ec] at e177
  exact e177

end
end LeanVM.Guest.B1.Main
