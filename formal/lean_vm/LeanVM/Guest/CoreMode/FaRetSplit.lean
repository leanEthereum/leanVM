/-
  LeanVM.Guest.CoreMode.FaRetSplit

  `faRetOk` in chunks of offsets, each its own kernel evaluation, for a function whose frame run at its
  returns is longer than `core.py`'s `FA_RUN` values, checked `FA_B` values at a time.
-/

module

public import LeanVM.Guest.CoreMode.Core

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Bridge (stmtsOf)

@[expose] public section

/-- `faRetAt`'s check of a frame run's values `k ∈ [B·c, B·c + B)` only, and of its cells past the run at chunk `0`. -/
noncomputable def faRetAtC (X : Bridge.AlignCtx) (body : List Stmt) (fas : List (ℕ × ℕ)) (A : FSt) (B c : ℕ) :
    Stmt → Bool
  | .atom (.frameAddr p (r :: rs)) => ((List.range' (B * c) B).all fun k ↦ !decide (k < rs.length + 1) ||
      (!(match (r :: rs)[k]? with
        | some v => dstIn body v
        | none => false) || (A.w.get (X.locAt r.idx + k)).isSome)) &&
      (c != 0 || fas.all fun q ↦ !(decide (p = V.n q.1) && Nat.ble (rs.length + 1) q.2) ||
        (A.w.get (X.locAt r.idx + q.2)).isSome)
  | _ => true

/-- Each frame run of the statements has at most `n` values. -/
def runsLe (n : ℕ) (ss : List Stmt) : Bool := ss.all fun
  | .atom (.frameAddr _ (_ :: rs)) => decide (rs.length + 1 ≤ n)
  | _ => true

theorem faRetAt_of_chunks {X : Bridge.AlignCtx} {body : List Stmt} {fas : List (ℕ × ℕ)} {A : FSt} {B m : ℕ}
    {s : Stmt} (h0 : 0 < m) (hn : runsLe (B * m) [s] = true) (h : ∀ c < m, faRetAtC X body fas A B c s = true) :
    faRetAt X body fas A s = true := by
  cases s <;> try rfl
  rename_i a
  cases a <;> try rfl
  rename_i p l
  cases l
  · rfl
  rename_i r rs
  simp only [runsLe, List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at hn
  have hB : 0 < B := Nat.pos_of_ne_zero fun hB ↦ by rw [hB, Nat.zero_mul] at hn; omega
  simp only [faRetAt, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun k hk ↦ ?_, ?_⟩
  · have hc : k / B < m := Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hk hn)
    have := h (k / B) hc
    simp only [faRetAtC, Bool.and_eq_true, List.all_eq_true] at this
    have hhi := Nat.lt_div_mul_add (a := k) hB
    rw [Nat.mul_comm (k / B)] at hhi
    have := this.1 k (List.mem_range'_1.2 ⟨Nat.mul_div_le k B, hhi⟩)
    simpa [hk] using this
  · have := h 0 h0
    simp only [faRetAtC, Bool.and_eq_true, List.all_eq_true] at this
    simpa using this.2

/-- `faRetOk` with the frame runs' check at chunk `c` (`faRetAtC`). -/
noncomputable def faRetC (Cf : CFun) (code : List OffsetInstruction) (B c : ℕ) : Bool :=
  !faNeed Cf || (List.range code.length).all fun i ↦ match code[i]? with
    | some (.jump _ 0 1) => match retSt Cf.frame code i with
      | some A => (stmtsOf Cf.fn.body).all (faRetAtC Cf.X Cf.fn.body Cf.H.fas A B c)
      | none => false
    | _ => true

/-- **The frame run cells at every return**, its frame runs' values in chunks of `B`. -/
theorem faRetOk_of_kchunks {Cf : CFun} {code : List OffsetInstruction} (B m : ℕ) (h0 : 0 < m)
    (hn : runsLe (B * m) (stmtsOf Cf.fn.body) = true) (h : ∀ c < m, faRetC Cf code B c = true) :
    faRetOk Cf code = true := by
  unfold faRetOk
  cases hf : faNeed Cf
  · rfl
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range]
  intro i hi
  have hc : ∀ c < m, (match code[i]? with
      | some (.jump _ 0 1) => match retSt Cf.frame code i with
        | some A => (stmtsOf Cf.fn.body).all (faRetAtC Cf.X Cf.fn.body Cf.H.fas A B c)
        | none => false
      | _ => true) = true := fun c hc ↦ by
    have := h c hc
    simp only [faRetC, hf, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at this
    exact this i hi
  split
  · split
    · rename_i A _
      rw [List.all_eq_true]
      intro s hs
      refine faRetAt_of_chunks (B := B) h0 ?_ fun c hcm ↦ ?_
      · simp only [runsLe, List.all_eq_true] at hn ⊢
        intro x hx
        rw [List.mem_singleton.1 hx]
        exact hn s hs
      · have := hc c hcm
        simp only [*] at this
        exact List.all_eq_true.1 this s hs
    · have := hc 0 h0
      rename_i hr
      simp only [*] at this
      exact this
  · rfl

end

end LeanVM.Guest.CoreMode
