/-
  LeanVM.Guest.B1.Place.LqProof

  `level_queries`' specializations: their walks and facts, for the placed proofs with pops (`LqProofP.lean`).
-/

module

public import LeanVM.Guest.B1.Place.Lq
public import LeanVM.Guest.B1.Place.LpProof
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.B1.Opening.QueriesFns
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Whir.OqKey
public import LeanVM.Guest.B1.Whir.DataSpec
public import LeanVM.Guest.B1.Whir.HelperAll
import LeanVM.Guest.StmtsAppend

/-!
# `level_queries`, placed

At every frame pointer, the specialization's walk is straight-line (the cap's and the flags' `HeapBuf`s, their
hints, `verify_merkle_cap`, `opening_queries`, `λ^q` by square and multiply). `LqFacts`: the facts an entry of
`lqTable` gives the placed proof (`LqProofP.lean`'s `lq_placedEP`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## The body -/

/-- The body before its `ret`. -/
abbrev lqPreB (q base folds leaf d cd mu nhs hbits fin : ℕ) : List Stmt :=
  lqBodyA q base folds leaf d cd mu nhs hbits fin

theorem lqBody_pre (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    lqBody q base folds leaf d cd mu nhs hbits fin =
      lqPreB q base folds leaf d cd mu nhs hbits fin ⧺
        [.ret [.n 19, .n 20, .n 21, .n (22 + osPowLen q)]] :=
  lqBody_split ..

theorem lqPreB_straight (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).all Main.Stmt.straight = true := by
  simp [lqBodyA, osHeap, os_powSteps_straight, Main.Stmt.straight]

theorem lqPreB_flat (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).all Whir.Stmt.flat = true :=
  lqBodyA_flat ..

theorem lq_pow_filterMap {β : Type} (f : Stmt → Option β) (hf : ∀ d a b, f (osMul d a b) = none)
    (ds : List Bool) (acc k : ℕ) : (osPowSteps 0 ds acc k).1.filterMap f = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro s hs
  obtain ⟨d, a, b, rfl⟩ := osPowSteps_mem_mul 0 ds acc k s hs
  exact hf d a b

theorem lqPreB_allocs (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).filterMap Main.Stmt.allocSz =
      [(.n 7, .inr (.n 6)), (.n 9, .inr (.n 8))] := by
  rw [lqPreB, lqBodyA, List.filterMap_append, List.filterMap_append,
    lq_pow_filterMap Main.Stmt.allocSz (fun _ _ _ ↦ rfl)]
  rfl

theorem lqPreB_addrs (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).filterMap Main.Stmt.addrS = [] := by
  rw [lqPreB, lqBodyA, List.filterMap_append, List.filterMap_append,
    lq_pow_filterMap Main.Stmt.addrS (fun _ _ _ ↦ rfl)]
  rfl

theorem lqPreB_calls (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).filterMap Main.Stmt.callS =
      [(none, "verify_merkle_cap__L" ++ natStr cd, [.n 7, .n 9], [.n 10, .n 11]),
        (none, oqName base folds leaf (d - cd) mu nhs hbits fin,
          [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17], [.n 18])] := by
  rw [lqPreB, lqBodyA, List.filterMap_append, List.filterMap_append,
    lq_pow_filterMap Main.Stmt.callS (fun _ _ _ ↦ rfl)]
  rfl

theorem lqPreB_loads (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).filterMap Stmt.loadS = [] := by
  rw [lqPreB, lqBodyA, List.filterMap_append, List.filterMap_append,
    lq_pow_filterMap Stmt.loadS (fun _ _ _ ↦ rfl)]
  rfl

/-- **`level_queries` ends with its returns**: it is no loop helper. -/
theorem lq_notLoop {q base folds leaf d cd mu nhs hbits fin : ℕ} {name : String} {fn : Fn}
    (hf : coreProgram.find? name = some fn)
    (hb : fn.body = lqBody q base folds leaf d cd mu nhs hbits fin) :
    coreProgram.loop name = false := by
  rw [Program.loop_of_find? hf, Fn.loop, hb, lqBody_pre]
  simp

/-! ## Placed -/

theorem lq_cap_lt {pd cd x e : ℕ} (hx : x < 2 ^ (pd + cd)) (he : e < 2) :
    2 * (2 ^ cd + x / 2 ^ pd) + e < 4 * 2 ^ cd := by
  have : x / 2 ^ pd < 2 ^ cd := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]; exact hx
  omega

theorem lq_flag_lt {pd cd x : ℕ} (hcd : 1 ≤ cd) (hx : x < 2 ^ (pd + cd)) :
    2 ^ (cd - 1) + x / 2 ^ (pd + 1) < 2 ^ cd := by
  have h2 : 2 ^ cd = 2 * 2 ^ (cd - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : x / 2 ^ (pd + 1) < 2 ^ (cd - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc x < 2 ^ (pd + cd) := hx
      _ = 2 ^ (cd - 1 + (pd + 1)) := by congr 1; omega
  omega

/-! ## Every specialization -/

/-- The facts an entry of `lqTable` gives `lq_placedEP`. -/
def LqFacts (q base folds leaf d cd mu nhs hbits fin : ℕ) : Prop :=
  (oqEntry (lqOqN base folds leaf d cd mu nhs hbits fin)).map (·.1) =
      some (lqOqN base folds leaf d cd mu nhs hbits fin) ∧
    oqCount (Whir.lqOdd q base) (lqOqS base folds leaf d cd mu nhs hbits fin).base (lqIters q base) = q ∧
    lqIters q base + 1 < ordG ∧ Whir.lqOdd q base ≤ (lqOqS base folds leaf d cd mu nhs hbits fin).base ∧
    1 ≤ cd ∧ cd ≤ 8 ∧ osKindOf ("verify_merkle_cap__L" ++ natStr cd) = some (.cap cd) ∧
    digitsVal (osPowDigits q) 1 = q

/-- `LqFacts` by numbers: the entry and shape of the numbers `k` (`Whir/OqKey`). -/
def LqFactsK (k : List ℕ) (q base cd : ℕ) : Prop :=
  (oqEntryK k).isSome ∧ oqCount (Whir.lqOdd q base) (oqShapeK k).oq.base (lqIters q base) = q ∧
    lqIters q base + 1 < ordG ∧ Whir.lqOdd q base ≤ (oqShapeK k).oq.base ∧
    1 ≤ cd ∧ cd ≤ 8 ∧ osKindOf ("verify_merkle_cap__L" ++ natStr cd) = some (.cap cd) ∧
    digitsVal (osPowDigits q) 1 = q

instance (k : List ℕ) (q base cd : ℕ) : Decidable (LqFactsK k q base cd) := by
  unfold LqFactsK; infer_instance

instance (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    Decidable (LqFacts q base folds leaf d cd mu nhs hbits fin) :=
  decidable_of_iff (LqFactsK (oqKey base folds leaf (d - cd) mu nhs hbits fin) q base cd) <| by
    unfold LqFacts LqFactsK lqOqS lqOqN
    rw [oqEntry_name_iff', oqShapeOf_oqName]

set_option maxRecDepth 100000 in
/-- **Every entry of `lqTable` has its facts**, by the kernel. -/
theorem lqTable_facts : ∀ e ∈ lqTable,
    LqFacts e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 := by
  decide +kernel

theorem oq_mem_of_entry {name : String} (h : (oqEntry name).map (·.1) = some name) :
    (name, oqLoopOf name, oqShapeOf name) ∈ openingQueriesLoops := by
  obtain ⟨e, hE, he1⟩ : ∃ e, oqEntry name = some e ∧ e.1 = name := by
    rcases hE : oqEntry name with _ | e
    · rw [hE] at h; simp at h
    · rw [hE] at h; simp at h; exact ⟨e, rfl, h⟩
  have heq : e = (name, oqLoopOf name, oqShapeOf name) := by
    obtain ⟨a, b, c⟩ := e
    simp only at he1
    simp [oqLoopOf, oqShapeOf, hE, he1]
  rw [← heq]
  exact List.mem_of_find?_eq_some hE

end
end LeanVM.Guest.B1
