/-
  LeanVM.Guest.B1.Tables.TermAtBody

  `check_opening_terminal`'s body, placed: its shape by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Tables.TermAtMem
public import LeanVM.Guest.B1.Tables.FlatAt

/-!
# The terminal's body, by kernel evaluation

Flat, no `frameAddr`, five `HeapBuf`s, its frames (three prefix chains, `__loop83`, the 92
selectors' dispatches, `rs_eq_run`), its loads, and its callees pure.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

/-- `PureIn` by evaluation. -/
noncomputable def pureCheck (S : List String) : Bool :=
  S.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList S fn.body
    | none => true

theorem pureIn_of_check {S : List String} (h : pureCheck S = true) : coreProgram.PureIn S := by
  intro g hg fn hfn
  have := List.all_eq_true.mp h g hg
  rw [hfn] at this
  exact this

set_option maxRecDepth 100000 in
theorem pure_eqpc : coreProgram.PureIn ["eq_prefix_chain", "__loop7"] :=
  pureIn_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
theorem pure_rs : coreProgram.PureIn ["rs_eq_run", "__loop8"] := pureIn_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
theorem pure_l83 : coreProgram.PureIn ["__loop83"] := pureIn_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
theorem pure_cs : coreProgram.PureIn csNames := pureIn_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
theorem term_not_loop : coreProgram.loop "check_opening_terminal" = false := by
  rw [Program.loop_of_find? find_check_opening_terminal]; decide +kernel

theorem term_body : Fn.body Data.core14 = tSegs.flatten ++ [.ret []] := core14_body

theorem term_flat : tSegs.flatten.all Stmt.flat = true := by decide +kernel

theorem term_addrs : tSegs.flatten.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem term_allocs : tSegs.flatten.filterMap Main.Stmt.allocSz =
    [(.n 17, .inl 35), (.n 19, .inl 35), (.n 21, .inl 35), (.n 25, .inl 35),
      (.n 1750, .inr (.n 1749))] := by decide +kernel

/-- A dispatch's selector and callees. -/
def Stmt.dispX : Stmt → Option (V × List String)
  | .dispatch x fs _ _ => some (x, fs)
  | _ => none

theorem term_disps : tSegs.flatten.filterMap Stmt.dispX =
    (List.range 92).map fun c => (.n (37 + 3 * c), csNames) := by decide +kernel

theorem callSF_nodisp (σ : Val) : ∀ l : List Stmt, l.all (fun s => (Stmt.dispX s).isNone) = true →
    l.filterMap (Stmt.callSF σ) = l.filterMap Main.Stmt.callS
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.filterMap_cons, List.filterMap_cons, callSF_nodisp σ l h.2]
    cases s <;> first | rfl | simp [Stmt.dispX] at h

theorem sel_calls (σ : Val) : ∀ n, ((List.range n).map selBlk).flatten.filterMap (Stmt.callSF σ) =
    (List.range n).map fun c =>
      (none, csNames.getD (logG (σ (.n (37 + 3 * c)))) "", [.n (36 + 3 * c), .n 13], [.n (selV c)])
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.filterMap_append, sel_calls σ n,
      List.map_append]
    simp [selBlk, List.filterMap_cons, List.filterMap_nil, Stmt.callSF, Main.Stmt.callS]

/-- **The terminal's frames**: the three prefix chains, `__loop83`, the 92 selectors, `rs_eq_run`. -/
theorem term_calls (σ : Val) : tSegs.flatten.filterMap (Stmt.callSF σ) =
    [(none, "eq_prefix_chain", [.n 17, .n 18, .n 0, .n 13, .n 3], []),
      (none, "eq_prefix_chain", [.n 19, .n 20, .n 1, .n 13, .n 4], []),
      (none, "eq_prefix_chain", [.n 21, .n 22, .n 1, .n 24, .n 6], []),
      (some (.n 32), "__loop83", [.n 33, .n 5, .n 25, .n 13], [])] ++
    (List.range 92).map (fun c =>
      (none, csNames.getD (logG (σ (.n (37 + 3 * c)))) "", [.n (36 + 3 * c), .n 13], [.n (selV c)])) ++
    [(none, "rs_eq_run", [.n 1750, .n 11, .n 13, .n 1816], [])] := by
  simp only [tSegs, List.flatten_cons, List.flatten_nil, List.append_nil, List.filterMap_append]
  rw [callSF_nodisp σ tPre (by decide +kernel), sel_calls σ 92,
    callSF_nodisp σ _ (by decide +kernel), callSF_nodisp σ tPostA (by decide +kernel),
    callSF_nodisp σ _ (by decide +kernel), callSF_nodisp σ tPostB (by decide +kernel),
    callSF_nodisp σ _ (by decide +kernel), callSF_nodisp σ tEnd (by decide +kernel)]
  have h1 : tPre.filterMap Main.Stmt.callS =
      [(none, "eq_prefix_chain", [.n 17, .n 18, .n 0, .n 13, .n 3], []),
        (none, "eq_prefix_chain", [.n 19, .n 20, .n 1, .n 13, .n 4], []),
        (none, "eq_prefix_chain", [.n 21, .n 22, .n 1, .n 24, .n 6], []),
        (some (.n 32), "__loop83", [.n 33, .n 5, .n 25, .n 13], [])] := by decide +kernel
  have h2 : ((List.range 112).map claimBlk).flatten.filterMap Main.Stmt.callS = [] := by decide +kernel
  have h3 : tPostA.filterMap Main.Stmt.callS = [] := by decide +kernel
  have h4 : ((List.range 64).map rinitBlk).flatten.filterMap Main.Stmt.callS = [] := by decide +kernel
  have h5 : tPostB.filterMap Main.Stmt.callS = [(none, "rs_eq_run", [.n 1750, .n 11, .n 13, .n 1816], [])] := by
    decide +kernel
  have h6 : ((List.range 64).map rsBlk).flatten.filterMap Main.Stmt.callS = [] := by decide +kernel
  have h7 : tEnd.filterMap Main.Stmt.callS = [] := by decide +kernel
  rw [h1, h2, h3, h4, h5, h6, h7]
  simp

/-- The terminal's loads through fixed values: the value, the offsets. -/
def termLoadT : List (ℕ × ℕ) :=
  [(13, 42), (25, 2), (34, 1), (9, 92), (10, 92), (7, 109), (8, 112), (12, 64), (1750, 64),
    (1825, 64)]

/-- A claim's load through its chain's pointer. -/
def claimPtr (j : ℕ) : ℕ :=
  if claimKind j = 2 then (qFacs (claimSlot j) 8 none (claimV.getD j 0 + 1)).2.2
  else claimV.getD j 0 + 1

def termLoadB (q : V × ℕ) : Bool :=
  termLoadT.any (fun t => q.1 == .n t.1 && decide (q.2 < t.2)) ||
    (List.range 112).any fun j => decide (claimKind j ≠ 3) && q.1 == .n (claimPtr j) && q.2 == 0

theorem term_loads : (tSegs.flatten.filterMap Stmt.loadS).all termLoadB = true := by decide +kernel

/-! ## What the segments compute -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem tpre_facts (h : Stmt.HoldsList C rd σ tPre True kret) :
    σ (.n 18) = word 1 0 0 ∧ σ (.n 20) = word 1 0 0 ∧ σ (.n 22) = word 1 0 0 ∧
      σ (.n 24) = σ (.n 13) * word 256 0 0 ∧ σ (.n 32) = word 2 0 0 + σ (.n 5) ∧
      σ (.n 33) = word 2 0 0 ∧ σ (.n 34) = σ (.n 25) * σ (.n 5) := by
  simp only [tPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true] at h
  obtain ⟨c18, -, c20, -, c22, c23, m24, -, c26, -, c27, a28, -, a30, -, c31, a32, c33, -, -, m34,
    -⟩ := h
  exact ⟨c18, c20, c22, by rw [m24, c23], by rw [a32, c31], c33, m34⟩

theorem tpostA_facts (h : Stmt.HoldsList C rd σ tPostA True kret) :
    σ (.n 1749) = sqI (σ (.n 6) * word 256 0 0 * word 2 0 0) 6 := by
  simp only [tPostA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨-, -, -, -, c1740, m1741, c1742, m1743, m1744, m1745, m1746, m1747, m1748, m1749⟩ := h
  rw [m1749, m1748, m1747, m1746, m1745, m1744, m1743, m1741, c1740, c1742]
  rfl

theorem tpostB_facts (h : Stmt.HoldsList C rd σ tPostB True kret) :
    σ (.n 1816) = σ (.n 6) * word 256 0 0 ∧
      σ (.n 1825) = σ (.n 1750) * sqI (σ (.n 6) * word 256 0 0) 6 := by
  simp only [tPostB, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    and_true] at h
  obtain ⟨c1815, m1816, -, c1817, m1818, m1819, m1820, m1821, m1822, m1823, m1824, m1825⟩ := h
  refine ⟨by rw [m1816, c1815], ?_⟩
  rw [m1825, m1824, m1823, m1822, m1821, m1820, m1819, m1818, c1817]
  rfl

/-- A claim's chain pointer: the chain's base times the claim's `g^len`, read at `cplen`. -/
theorem claim_ptr_facts {j : ℕ} (hk : claimKind j ≠ 3)
    (h : Stmt.HoldsList C rd σ (claimBlk j) True kret) :
    LoadHolds rd (σ (.n 7)) j (σ (.n (claimV.getD j 0))) ∧
      σ (.n (claimPtr j)) = σ (.n (if claimKind j = 0 then 17 else if claimKind j = 1 then 19 else 21)) *
        σ (.n (claimV.getD j 0)) := by
  by_cases h2 : claimKind j = 2
  · simp only [claimBlk, h2, ↓reduceIte, show (2 : ℕ) ≠ 3 from by decide] at h
    obtain ⟨lc, h⟩ := h
    simp only [List.append_eq] at h
    rw [holdsList_append, holdsList_noRet _ (qFacs_noRet _ _ _ _)] at h
    obtain ⟨-, h⟩ := h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
    obtain ⟨mu, -⟩ := h
    refine ⟨lc, ?_⟩
    simp only [claimPtr, h2, ↓reduceIte, show (2 : ℕ) ≠ 0 from by decide,
      show (2 : ℕ) ≠ 1 from by decide]
    exact mu
  · simp only [claimBlk, hk, h2, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
    obtain ⟨lc, m1, -⟩ := h
    refine ⟨lc, ?_⟩
    simp only [claimPtr, h2, ↓reduceIte]
    rw [m1]
    by_cases h0 : claimKind j = 0
    · simp [h0]
    · have h1 : claimKind j = 1 := by unfold claimKind at h0 h2 hk ⊢; split_ifs at * <;> omega
      simp [h1]

end

end
end LeanVM.Guest.B1
