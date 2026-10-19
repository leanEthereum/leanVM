/-
  LeanVM.Guest.B1.Tables.LoopSize

  Sizes of the valid trees of the terminal's and Flock's callees: the `mul_range` loops, the
  functions wrapping one, and the column selectors.
-/

module

public import LeanVM.Guest.B1.Tables.VtCSize
public import LeanVM.Guest.B1.Tables.TermAtBody
public import LeanVM.Guest.B1.Tables.FlockAt

/-!
# Callees' tree sizes

A `mul_range` loop whose body ends in the standard step (`loopTail`: `x·g + N`, `x·g`) run
from `g^j` to `g^m` is at most `(m - j) + 1` frames (`loopStd_total`); a function whose body
is straight-line with one conditional call is its frame and the callee's tree, or the callee's
frame when skipped (`wrap_total`); a function with no `HeapBuf` and no callee is its frame
(`leaf_total_of`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.VerifySub LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ}

/-- The step of a `mul_range` loop at `x = σ 0`, `N = σ 1`: `c = x·g + N`, `d = x·g`. -/
def loopTail (a b c a' d : ℕ) : List Stmt :=
  [.atom (.const (.n a) (word 2 0 0)), .atom (.mul (.n b) (.n 0) (.n a)),
    .atom (.add (.n c) (.n b) (.n 1)), .atom (.const (.n a') (word 2 0 0)),
    .atom (.mul (.n d) (.n 0) (.n a'))]

/-- **A `mul_range` loop's valid trees** from `g^j` to `g^m`: at most `m - j` frames and the
skipped tail's. -/
theorem loopStd_total {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre0 : List Stmt} {P : List V} {a b c a' d : ℕ} (hpar : fn.params = .n 0 :: .n 1 :: P)
    (hb : fn.body = (pre0 ++ loopTail a b c a' d) ++ [.callIf (.n c) f (.n d :: .n 1 :: P), .ret []])
    (hck : (pre0 ++ loopTail a b c a' d).all Main.Stmt.straight = true ∧
      (pre0 ++ loopTail a b c a' d).filterMap Main.Stmt.allocSz = [] ∧
      (pre0 ++ loopTail a b c a' d).filterMap Main.Stmt.callS = [])
    {rd : Reader} {j m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hj : j < m)
    (hn : t.name = f) (hv : t.Valid coreProgram rd (gen ^ j :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ (m - j) * fs f + fs f := by
  have := vtc_loop_total (fs := fs) hf hb hck.1 hck.2.1 rd m rest 0 ?_ (m - j) j t rets (by omega) hj
    hn hv hbo
  · simpa using this
  intro σ j' _ hp hes
  rw [hpar] at hp
  simp only [List.map_cons, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  have mem : ∀ s ∈ loopTail a b c a' d, s ∈ pre0 ++ loopTail a b c a' d :=
    fun s hs => List.mem_append_right _ hs
  have a1 := vtc_atom hes (mem (.atom (.const (.n a) (word 2 0 0))) (by simp [loopTail]))
  have a2 := vtc_atom hes (mem (.atom (.mul (.n b) (.n 0) (.n a))) (by simp [loopTail]))
  have a3 := vtc_atom hes (mem (.atom (.add (.n c) (.n b) (.n 1))) (by simp [loopTail]))
  have a4 := vtc_atom hes (mem (.atom (.const (.n a') (word 2 0 0))) (by simp [loopTail]))
  have a5 := vtc_atom hes (mem (.atom (.mul (.n d) (.n 0) (.n a'))) (by simp [loopTail]))
  simp only [Atom.Holds, word_gen] at a1 a2 a3 a4 a5
  refine ⟨by rw [a3, a2, a1, h0, h1], by simp [a5, a4, h0, h1, hr], fun kids hk _ => ?_⟩
  rw [hck.2.2] at hk
  match kids, hk with
  | [], _ => simp [Tree.totalKids]

/-- **A function calling one callee conditionally**: its frame and the callee's tree, or the
callee's frame when skipped. -/
theorem wrap_total {f g : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {pre : List Stmt}
    {c : V} {nxt : List V} (hb : fn.body = pre ++ [.callIf c g nxt, .ret []])
    (hck : pre.all Main.Stmt.straight = true ∧ pre.filterMap Main.Stmt.allocSz = [] ∧
      pre.filterMap Main.Stmt.callS = [])
    {rd : Reader} {args rets : List E} {t : Tree} (hn : t.name = f)
    (hv : t.Valid coreProgram rd args rets) (hbo : t.BufsOk coreProgram) {Kg : ℕ}
    (hk : ∀ σ : Val, fn.params.map σ = args → (∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd σ) →
      σ c ≠ 0 → ∀ (t' : Tree) (rets' : List E), t'.name = g →
        t'.Valid coreProgram rd (nxt.map σ) rets' → t'.BufsOk coreProgram → t'.total fs ≤ Kg) :
    t.total fs ≤ fs f + (fs g + Kg) := by
  have hb' : fn.body = (pre ++ [.callIf c g nxt]) ++ [.ret []] := by rw [hb, List.append_assoc]; rfl
  obtain ⟨σ, kids, ht, hp, hes, hkv, hbk⟩ := vtc_node (fs := fs) hf hb'
    (by simp [hck.1, Main.Stmt.straight]) (by simp [hck.2.1, Main.Stmt.allocSz]) hn hv hbo
  have hes' : ∀ e ∈ pre.flatMap (Main.slEvs σ), e.Holds rd σ := fun e he =>
    hes e (by rw [List.flatMap_append]; exact List.mem_append_left _ he)
  rw [List.filterMap_append, hck.2.2] at hkv
  simp only [Main.Stmt.callS, List.filterMap_cons, List.filterMap_nil, List.nil_append,
    List.map_cons, List.map_nil, Main.mkCall] at hkv
  match kids, hkv, hbk with
  | [kl], ⟨hnl, hvl, _⟩, ⟨hbl, _⟩ =>
    rw [ht]
    simp only [Tree.totalKids, Nat.add_zero]
    by_cases hz : σ c = 0
    · simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hvl
      obtain ⟨⟨g', σ', rfl⟩, -⟩ := hvl
      simp only [Tree.name] at hnl
      simp [Tree.total, hnl]
    · simp only [hz, ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hvl
      have := hk σ hp hes' hz kl _ hnl hvl hbl
      omega

/-- A body with no `HeapBuf` and no callee, ending in its `ret`. -/
def leafOk (body : List Stmt) : Bool :=
  match body.getLast? with
  | some (.ret _) => body.dropLast.all Main.Stmt.straight &&
      (body.dropLast.filterMap Main.Stmt.allocSz).isEmpty &&
      (body.dropLast.filterMap Main.Stmt.callS).isEmpty
  | _ => false

/-- **A function with no `HeapBuf` and no callee is its frame.** -/
theorem leaf_total_of {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (h : leafOk fn.body = true) {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid coreProgram rd args rets) (hbo : t.BufsOk coreProgram) : t.total fs = fs f := by
  unfold leafOk at h
  split at h
  · rename_i vs hl
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    have hb : fn.body = fn.body.dropLast ++ [.ret vs] := by
      rw [← List.dropLast_append_getLast? _ hl]; simp
    exact vtc_leaf_total hf hb h.1.1 h.1.2 h.2 hn hv hbo
  · exact absurd h (by simp)

/-! ## The loops -/

set_option maxRecDepth 100000 in
theorem l7_shape : Fn.body Data.core37 = ((Fn.body Data.core37).take 12 ++ loopTail 16 17 18 19 20) ++
    [.callIf (.n 18) "__loop7" [.n 20, .n 1, .n 2, .n 3, .n 4], .ret []] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l7_ck : ((Fn.body Data.core37).take 12 ++ loopTail 16 17 18 19 20).all Main.Stmt.straight = true ∧
    ((Fn.body Data.core37).take 12 ++ loopTail 16 17 18 19 20).filterMap Main.Stmt.allocSz = [] ∧
    ((Fn.body Data.core37).take 12 ++ loopTail 16 17 18 19 20).filterMap Main.Stmt.callS = [] := by
  decide +kernel

/-- **`__loop7`'s valid trees** from `g^j` to `g^m`. -/
theorem l7_total {rd : Reader} {j m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hj : j < m)
    (hn : t.name = "__loop7") (hv : t.Valid coreProgram rd (gen ^ j :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ (m - j) * fs "__loop7" + fs "__loop7" :=
  loopStd_total find_loop7 rfl l7_shape l7_ck hj hn hv hbo

set_option maxRecDepth 100000 in
theorem l8_shape : Fn.body Data.core38 = ((Fn.body Data.core38).take 332 ++ loopTail 273 274 275 276 277) ++
    [.callIf (.n 275) "__loop8" [.n 277, .n 1, .n 2, .n 3, .n 4], .ret []] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l8_ck : ((Fn.body Data.core38).take 332 ++ loopTail 273 274 275 276 277).all Main.Stmt.straight = true ∧
    ((Fn.body Data.core38).take 332 ++ loopTail 273 274 275 276 277).filterMap Main.Stmt.allocSz = [] ∧
    ((Fn.body Data.core38).take 332 ++ loopTail 273 274 275 276 277).filterMap Main.Stmt.callS = [] := by
  decide +kernel

/-- **`__loop8`'s valid trees** from `g^j` to `g^m`. -/
theorem l8_total {rd : Reader} {j m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hj : j < m)
    (hn : t.name = "__loop8") (hv : t.Valid coreProgram rd (gen ^ j :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ (m - j) * fs "__loop8" + fs "__loop8" :=
  loopStd_total find_loop8 rfl l8_shape l8_ck hj hn hv hbo

set_option maxRecDepth 100000 in
theorem l81_shape : Fn.body Data.core140 = ((Fn.body Data.core140).take 22 ++ loopTail 23 24 25 26 27) ++
    [.callIf (.n 25) "__loop81" [.n 27, .n 1, .n 2, .n 3], .ret []] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l81_ck : ((Fn.body Data.core140).take 22 ++ loopTail 23 24 25 26 27).all Main.Stmt.straight = true ∧
    ((Fn.body Data.core140).take 22 ++ loopTail 23 24 25 26 27).filterMap Main.Stmt.allocSz = [] ∧
    ((Fn.body Data.core140).take 22 ++ loopTail 23 24 25 26 27).filterMap Main.Stmt.callS = [] := by
  decide +kernel

/-- **`__loop81`'s valid trees** from `g^j` to `g^m`. -/
theorem l81_total {rd : Reader} {j m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hj : j < m)
    (hn : t.name = "__loop81") (hv : t.Valid coreProgram rd (gen ^ j :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ (m - j) * fs "__loop81" + fs "__loop81" :=
  loopStd_total find_loop81 rfl l81_shape l81_ck hj hn hv hbo

set_option maxRecDepth 100000 in
theorem l82_shape : Fn.body Data.core141 = ((Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72) ++
    [.callIf (.n 70) "__loop82" [.n 72, .n 1, .n 2, .n 3, .n 4], .ret []] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l82_ck : ((Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72).all Main.Stmt.straight = true ∧
    ((Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72).filterMap Main.Stmt.allocSz = [] ∧
    ((Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72).filterMap Main.Stmt.callS = [] := by
  decide +kernel

/-- **`__loop82`'s valid trees** from `g^j` to `g^m`. -/
theorem l82_total {rd : Reader} {j m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hj : j < m)
    (hn : t.name = "__loop82") (hv : t.Valid coreProgram rd (gen ^ j :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ (m - j) * fs "__loop82" + fs "__loop82" :=
  loopStd_total find_loop82 rfl l82_shape l82_ck hj hn hv hbo

set_option maxRecDepth 100000 in
theorem l83_shape : Fn.body Data.core142 = ((Fn.body Data.core142).take 9 ++ loopTail 12 13 14 15 16) ++
    [.callIf (.n 14) "__loop83" [.n 16, .n 1, .n 2, .n 3], .ret []] := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem l83_ck : ((Fn.body Data.core142).take 9 ++ loopTail 12 13 14 15 16).all Main.Stmt.straight = true ∧
    ((Fn.body Data.core142).take 9 ++ loopTail 12 13 14 15 16).filterMap Main.Stmt.allocSz = [] ∧
    ((Fn.body Data.core142).take 9 ++ loopTail 12 13 14 15 16).filterMap Main.Stmt.callS = [] := by
  decide +kernel

/-- **`__loop83`'s valid trees** from `g^j` to `g^m`. -/
theorem l83_total {rd : Reader} {j m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hj : j < m)
    (hn : t.name = "__loop83") (hv : t.Valid coreProgram rd (gen ^ j :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ (m - j) * fs "__loop83" + fs "__loop83" :=
  loopStd_total find_loop83 rfl l83_shape l83_ck hj hn hv hbo

/-! ## The wrappers and the column selectors -/

theorem eqpc_shape : Fn.body Data.core4 = (Fn.body Data.core4).take 4 ++
    [.callIf (.n 6) "__loop7" [.n 7, .n 4, .n 0, .n 2, .n 3], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem eqpc_ck : ((Fn.body Data.core4).take 4).all Main.Stmt.straight = true ∧
    ((Fn.body Data.core4).take 4).filterMap Main.Stmt.allocSz = [] ∧
    ((Fn.body Data.core4).take 4).filterMap Main.Stmt.callS = [] := by decide +kernel

/-- `eq_prefix_chain`'s bound: its frame and `__loop7` over at most 32 steps. -/
abbrev eqpcBound (fs : String → ℕ) : ℕ :=
  fs "eq_prefix_chain" + (fs "__loop7" + (32 * fs "__loop7" + fs "__loop7"))

/-- **`eq_prefix_chain`'s valid trees** on chains of at most 32 entries. -/
theorem eqpc_total {rd : Reader} {t : Tree} {rets : List E} {p s a b' : E} {m : ℕ} (hm : m ≤ 32)
    (hn : t.name = "eq_prefix_chain") (hv : t.Valid coreProgram rd [p, s, a, b', gen ^ m] rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ eqpcBound fs := by
  refine wrap_total find_eq_prefix_chain eqpc_shape eqpc_ck hn hv hbo
    fun σ hp hes hz t' rets' hn' hv' hbo' => ?_
  simp only [show Fn.params Data.core4 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, -, h2, h3, h4, -⟩ := hp
  have a5 := vtc_atom hes (List.mem_of_getElem? (l := (Fn.body Data.core4).take 4) (i := 1) rfl)
  have a6 := vtc_atom hes (List.mem_of_getElem? (l := (Fn.body Data.core4).take 4) (i := 2) rfl)
  have a7 := vtc_atom hes (List.mem_of_getElem? (l := (Fn.body Data.core4).take 4) (i := 3) rfl)
  simp only [Atom.Holds, word_one] at a5 a6 a7
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; apply hz; rw [a6, a5, h4, h, pow_zero]; exact e_add_self 1
    · exact h
  simp only [List.map_cons, List.map_nil, a7, h4, h0, h2, h3] at hv'
  rw [← pow_zero gen] at hv'
  have := l7_total (fs := fs) hm0 hn' hv' hbo'
  have : (m - 0) * fs "__loop7" ≤ 32 * fs "__loop7" := Nat.mul_le_mul_right _ (by omega)
  omega

theorem rs_shape : Fn.body Data.core5 = (Fn.body Data.core5).take 3 ++
    [.callIf (.n 5) "__loop8" [.n 6, .n 3, .n 1, .n 2, .n 0], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem rs_ck : ((Fn.body Data.core5).take 3).all Main.Stmt.straight = true ∧
    ((Fn.body Data.core5).take 3).filterMap Main.Stmt.allocSz = [] ∧
    ((Fn.body Data.core5).take 3).filterMap Main.Stmt.callS = [] := by decide +kernel

/-- `rs_eq_run`'s bound: its frame and `__loop8` over at most 32 steps. -/
abbrev rsBound (fs : String → ℕ) : ℕ :=
  fs "rs_eq_run" + (fs "__loop8" + (32 * fs "__loop8" + fs "__loop8"))

/-- **`rs_eq_run`'s valid trees** on runs of at most 32 rounds. -/
theorem rs_total {rd : Reader} {t : Tree} {rets : List E} {p z pt : E} {m : ℕ} (hm : m ≤ 32)
    (hn : t.name = "rs_eq_run") (hv : t.Valid coreProgram rd [p, z, pt, gen ^ m] rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ rsBound fs := by
  refine wrap_total find_rs_eq_run rs_shape rs_ck hn hv hbo
    fun σ hp hes hz t' rets' hn' hv' hbo' => ?_
  simp only [show Fn.params Data.core5 = [.n 0, .n 1, .n 2, .n 3] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, h2, h3, -⟩ := hp
  have a4 := vtc_atom hes (List.mem_of_getElem? (l := (Fn.body Data.core5).take 3) (i := 0) rfl)
  have a5 := vtc_atom hes (List.mem_of_getElem? (l := (Fn.body Data.core5).take 3) (i := 1) rfl)
  have a6 := vtc_atom hes (List.mem_of_getElem? (l := (Fn.body Data.core5).take 3) (i := 2) rfl)
  simp only [Atom.Holds, word_one] at a4 a5 a6
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; apply hz; rw [a5, a4, h3, h, pow_zero]; exact e_add_self 1
    · exact h
  simp only [List.map_cons, List.map_nil, a6, h3, h0, h1, h2] at hv'
  rw [← pow_zero gen] at hv'
  have := l8_total (fs := fs) hm0 hn' hv' hbo'
  have : (m - 0) * fs "__loop8" ≤ 32 * fs "__loop8" := Nat.mul_le_mul_right _ (by omega)
  omega

set_option maxRecDepth 100000 in
theorem cs_leafB : csNames.all (fun g => match coreProgram.find? g with
    | some fn => leafOk fn.body
    | none => false) = true := by decide +kernel

/-- **A column selector is its frame.** -/
theorem cs_total {g : String} (hg : g ∈ csNames) {rd : Reader} {t : Tree} {args rets : List E}
    (hn : t.name = g) (hv : t.Valid coreProgram rd args rets) (hbo : t.BufsOk coreProgram) :
    t.total fs = fs g := by
  have h := List.all_eq_true.mp cs_leafB g hg
  split at h
  · rename_i fn hf
    exact leaf_total_of hf h hn hv hbo
  · exact absurd h (by simp)

end
end LeanVM.Guest.B1
