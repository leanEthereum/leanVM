/-
  LeanVM.Guest.B1.Main.Loops

  B1 for `main`'s loop helpers: the raw signatures (`__loop2`, `__loop3`) and the children
  (`__loop4`), each body checked by evaluation.
-/

module

public import LeanVM.Guest.B1.Main.Basic
public import LeanVM.Guest.B1.Digest.Loops

/-!
# `main`'s loops

Each helper's body (`loopPre`) is checked by evaluation (`l3Ok`, `l4Ok`, `l5Ok`), and its run at
`x` gives one iteration's facts (`LoopsC`: `RawXStepC`, `RawSStepC`, `KidStepC`) and the run at
`x·g` (`loop_stepF`).

* `__loop2` (G:4559-4568): a raw leanXMSS signature `i`: a slot `s` below the leanXMSS region,
  `cover[g^s] = g^i`, the leanXMSS segment (`verify_lean_xmss(lx_table · g^(4s), lx_tags)`,
  inline) on the signer `lx_table · g^(4s)` and the carried tags;
* `__loop3` (G:4569-4573): a raw leanSPHINCS signature `j`: a slot `s` below the leanSPHINCS
  region, `sp_cover[g^s] = n_raw_x · g^j` (`sp_cover = cover · lx_slots`),
  `verify_sig_lean_sphincs(ls_table · g^(4s), byte_bits)`;
* `__loop4` (G:4593-4617): child `c`, its DA digest hinted at `da_digests · c^2`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## Shared -/

/-- `P` holds the call `.call f args rets`. -/
def hasCall (P : List Stmt) (f : String) (args rets : List V) : Bool :=
  P.any (stmtEqb · (.call f args rets))

/-- `x = y · z`, by the first `MUL` into `x`. -/
def isMul (atoms : List Atom) (x y z : V) : Bool := decide (mulOf atoms x = some (y, z))

theorem isMul_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x y z : V}
    (h : isMul atoms x y z = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ x = σ y * σ z :=
  mulOf_sound (of_decide_eq_true h) hat

/-- **A guarded loop call** in a block: `callIf (1 + N) f [1, N, rest…]`, the two `1`s
constants. -/
def guardOk (P : List Stmt) (gc : V) (f : String) (one N : V) (rest : List V) : Bool :=
  P.any (stmtEqb · (.callIf gc f (one :: N :: rest))) &&
    (match addOf (atomsIn P) gc with
     | some (p, q) => (atomsIn P).any (isConstAt p 1 0) && decide (q = N)
     | none => false) &&
    (atomsIn P).any (isConstAt one 1 0)

theorem guard_sound {rd : Reader} {σ : Val} {P : List Stmt} {gc : V} {f : String} {one N : V}
    {rest : List V} (h : guardOk P gc f one N rest = true)
    (hall : ∀ s ∈ P, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = [])) :
    1 + σ N ≠ 0 → coreProgram.Rel rd f (1 :: σ N :: rest.map σ) [] := by
  simp only [guardOk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, ha⟩, h1⟩ := h
  have hat := atoms_of_flat hall
  have hcall := callIf_of_flat hall hc
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hp1, rfl⟩ := ha
    intro hne
    have hgc : σ gc = 1 + σ q := by rw [addOf_sound hpq hat, const_sound hp1 hat, word_one]
    have := hcall.2 (by rw [hgc]; exact hne)
    rwa [List.map_cons, List.map_cons, const_sound h1 hat, word_one] at this
  · exact absurd ha (by simp)

/-! ## `__loop2`: raw leanXMSS signatures -/

/-- `__loop2` with the leanXMSS segment cut out (`Sig.loop2_split`): its prelude (the slot `s`
hinted, range-checked below the region, `cover[g^s] = x`, the signer `lx_table · g^(4s)` at
`.n 65`), then its counter's self-call. -/
noncomputable def l2Fn : Fn := { Data.core36 with body := Sig.l2Pre ++ Sig.l2Post }

def l3Ok (fn : Fn) : Bool :=
  loopShapeF fn "__loop2" && decide (fn.params.length = 56) &&
    rcBoundOk (atomsIn (loopPre fn)) (.n 56) (.n 2) &&
    isMul (atomsIn (loopPre fn)) (.n 62) (.n 3) (.n 56) &&
    (atomsIn (loopPre fn)).any (isLoadAt (.n 0) (.n 62) 0) &&
    monoIs (atomsIn (loopPre fn)) (.n 65) (.n 4) (.n 56) 4

set_option maxRecDepth 100000 in
theorem l3_ok : l3Ok l2Fn = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l3_idx : coreProgram.indexOf? "__loop2" = some 36 := by decide +kernel

/-! ## `__loop3`: raw leanSPHINCS signatures -/

def l4Ok (fn : Fn) : Bool :=
  loopShapeF fn "__loop3" && decide (fn.params.length = 7) &&
    rcBoundOk (atomsIn (loopPre fn)) (.n 7) (.n 2) &&
    isMul (atomsIn (loopPre fn)) (.n 13) (.n 4) (.n 0) &&
    isMul (atomsIn (loopPre fn)) (.n 14) (.n 3) (.n 7) &&
    (atomsIn (loopPre fn)).any (isLoadAt (.n 13) (.n 14) 0) &&
    monoIs (atomsIn (loopPre fn)) (.n 17) (.n 5) (.n 7) 4 &&
    hasCall (loopPre fn) "verify_sig_lean_sphincs" [.n 17, .n 6] []

set_option maxRecDepth 100000 in
theorem l4_ok : l4Ok (coreProgram.getD 37 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l4_idx : coreProgram.indexOf? "__loop3" = some 37 := by decide +kernel

/-! ## A two-digest hash in a block -/

/-- The chain of `keccak([a, b], [c, d], out)`: four cells, `64` bytes, from the zero state. -/
def pairSpec (a b c d : V) (atoms : List Atom) : ChainSpec :=
  ⟨[some a, some b, some c, some d], 64, true, none, keccakBlocks atoms⟩

/-- `keccak([a, b], [c, d], out)` with the digest's two cells loaded into `p[0]`, `p[1]`. -/
def pairHashOk (atoms : List Atom) (a b c d p : V) : Bool :=
  (pairSpec a b c d atoms).check atoms &&
    atoms.any (isLoadAt ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 0) p 0) &&
    atoms.any (isLoadAt ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 1) p 1)

theorem pairHash_sound {rd : Reader} {σ : Val} {atoms : List Atom} {a b c d p : V}
    (h : pairHashOk atoms a b c d p = true) (hat : ∀ x ∈ atoms, x.Holds rd σ) :
    LoadHolds rd (σ p) 0 (digestHalves (keccak256 (cellsBytes [σ a, σ b, σ c, σ d]))).1 ∧
      LoadHolds rd (σ p) 1 (digestHalves (keccak256 (cellsBytes [σ a, σ b, σ c, σ d]))).2 := by
  simp only [pairHashOk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, h0⟩, h1⟩ := h
  have hd := chain_final hc rfl hat (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  have hv : ((pairSpec a b c d atoms).vals σ).take ((pairSpec a b c d atoms).len / 16) =
      [σ a, σ b, σ c, σ d] := by simp [pairSpec, ChainSpec.vals, srcVal]
  rw [hv, List.nil_append] at hd
  refine ⟨?_, ?_⟩
  · have := load_sound h0 hat
    rw [show ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 0) =
      ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) ((0 : Fin 13) : ℕ)) from rfl]
      at this
    rw [← hd]; exact this
  · have := load_sound h1 hat
    rw [show ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) 1) =
      ((pairSpec a b c d atoms).outV ((pairSpec a b c d atoms).nb - 1) ((1 : Fin 13) : ℕ)) from rfl]
      at this
    rw [← hd]; exact this

/-! ## `__loop4`: the children -/

def isLoad (atoms : List Atom) (x p : V) (o : ℕ) : Bool := atoms.any (isLoadAt x p o)

def l5Ok (fn : Fn) : Bool :=
  let P := loopPre fn
  let A := atomsIn P
  loopShapeF fn "__loop4" &&
  decide (fn.params.length = 16) &&
  isMul A (.n 16) (.n 2) (.n 0) &&
  isLoad A (.n 17) (.n 16) 0 &&
  rcConstOk A (.n 18) 9272771591053052074 &&
  rcConstOk A (.n 19) 9272771591053052074 &&
  isMul A (.n 28) (.n 18) (.n 19) &&
  hasCall P "child_claim_list_digest" [.n 3, .n 4, .n 17, .n 5, .n 18] [.n 29, .n 30] &&
  isMul A (.n 31) (.n 17) (.n 18) &&
  hasCall P "child_claim_list_digest" [.n 6, .n 7, .n 31, .n 8, .n 19] [.n 32, .n 33] &&
  monoIs A (.n 39) (.n 9) (.n 0) 24 &&
  monoIs A (.n 41) (.n 10) (.n 0) 2 &&
  isLoad A (.n 42) (.n 41) 0 &&
  isLoad A (.n 43) (.n 41) 1 &&
  hasCall P "statement_digest" [.n 11, .n 12, .n 29, .n 30, .n 32, .n 33, .n 42, .n 43, .n 39]
    [.n 44, .n 45] &&
  monoIs A (.n 47) (.n 13) (.n 0) 2 &&
  isLoad A (.n 44) (.n 47) 0 &&
  monoIs A (.n 48) (.n 13) (.n 0) 2 &&
  isLoad A (.n 45) (.n 48) 1 &&
  monoIs A (.n 54) (.n 15) (.n 0) 24 &&
  hasCall P "verify_sub" [.n 44, .n 45, .n 11, .n 12, .n 14, .n 54] [] &&
  isMul A (.n 55) (.n 17) (.n 28) &&
  isMul A (.n 56) (.n 2) (.n 0) &&
  isLoad A (.n 55) (.n 56) 1

set_option maxRecDepth 100000 in
theorem l5_ok : l5Ok (coreProgram.getD 38 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l5_idx : coreProgram.indexOf? "__loop4" = some 38 := by decide +kernel

end
end LeanVM.Guest.B1.Main
