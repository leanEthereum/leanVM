/-
  LeanVM.Guest.CoreMode.FaRetSplit

  `faRetOk` in chunks of offsets, each its own kernel evaluation, for a function whose frame run at its
  returns is longer than `core.py`'s `FA_RUN` values, checked `FA_B` values at a time; and `faRetOkF`, the
  same check in one pass for the kernel.
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.TrieFacts

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Bridge (stmtsOf)
open LeanVM.Guest.Exec (Trie)

@[expose] public section

/-- `faRetAt`'s check of a frame run's values `k ∈ [B·c, B·c + B)` only, and of its cells past the run at chunk `0`. -/
noncomputable def faRetAtC (X : Bridge.AlignCtx) (body : List Stmt) (fas : List (ℕ × ℕ)) (A : FSt) (B c : ℕ) :
    Stmt → Bool
  | .atom (.frameAddr p (r :: rs)) => ((List.range' (B * c) B).all fun k ↦ !decide (k < rs.length + 1) ||
      (!(match (r :: rs)[k]? with
        | some v => dstIn body v
        | none => false) || A.hasW (X.locAt r.idx + k))) &&
      (c != 0 || fas.all fun q ↦ !(decide (p = V.n q.1) && Nat.ble (rs.length + 1) q.2) ||
        A.hasW (X.locAt r.idx + q.2))
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
      | some A => stmtsAll (faRetAtC Cf.X Cf.fn.body Cf.H.fas A B c) Cf.fn.body
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
        | some A => stmtsAll (faRetAtC Cf.X Cf.fn.body Cf.H.fas A B c) Cf.fn.body
        | none => false
      | _ => true) = true := fun c hc ↦ by
    have := h c hc
    simp only [faRetC, hf, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at this
    exact this i hi
  split
  · split
    · rename_i A _
      refine stmtsAll_of fun s hs ↦ faRetAt_of_chunks (B := B) h0 ?_ fun c hcm ↦ ?_
      · simp only [runsLe, List.all_eq_true] at hn ⊢
        intro x hx
        rw [List.mem_singleton.1 hx]
        exact hn s hs
      · have := hc c hcm
        simp only [*, stmtsAll_eq] at this
        exact List.all_eq_true.1 this s hs
    · have := hc 0 h0
      rename_i hr
      simp only [*] at this
      exact this
  · rfl

/-! ## In one pass

`faRetOk` reads the code by index at every offset and scans the body for each value of a frame run; `faRetOkF`
walks the code once for its returns (`retOffs`), and looks a value up among the body's defined values by number
(`dstT`). -/

/-- The offsets of the returns (`JUMP _ 0 1`) of `code`, from offset `i`. -/
def retOffs (i : ℕ) : List OffsetInstruction → List ℕ
  | [] => []
  | .jump _ od of :: code => bif Nat.beq od 0 && Nat.beq of 1 then i :: retOffs (i + 1) code else retOffs (i + 1) code
  | _ :: code => retOffs (i + 1) code

theorem mem_retOffs : ∀ (code : List OffsetInstruction) (i j a : ℕ), code[j]? = some (.jump a 0 1) →
    i + j ∈ retOffs i code
  | [], _, _, _, h => by simp at h
  | ins :: code, i, 0, a, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [retOffs]
  | ins :: code, i, j + 1, a, h => by
    simp only [List.getElem?_cons_succ] at h
    have ih := mem_retOffs code (i + 1) j a h
    rw [show i + (j + 1) = i + 1 + j by omega]
    cases ins <;> simp only [retOffs] <;> try exact ih
    cases (Nat.beq _ 0 && Nat.beq _ 1) <;> simp [ih]

/-- The numbers of the values an atom of the body defines, below the tries' depth, as a trie. -/
noncomputable def dstT (body : List Stmt) : Trie Unit :=
  keysT (((stmtsOf body).flatMap fun s ↦ match s with
    | .atom a => atomDst a
    | _ => []).filterMap vnum |>.filter fun k ↦ Nat.blt (k + 1) (2 ^ Exec.indexDepth)) .nil

/-- `dstIn body v`, by `v`'s number in `D` (`dstT body`) where it has one below the tries' depth. -/
noncomputable def dstInF (D : Trie Unit) (body : List Stmt) (v : V) : Bool :=
  match vnum v with
  | some k => bif Nat.blt (k + 1) (2 ^ Exec.indexDepth) then (Check.getF D k).isSome else dstIn body v
  | none => dstIn body v

theorem getF_keysT_of : ∀ (l : List ℕ) (t : Trie Unit) {k : ℕ}, (∀ n ∈ l, n + 1 < 2 ^ Exec.indexDepth) →
    (k ∈ l ∨ (Check.getF t k).isSome = true) → (Check.getF (keysT l t) k).isSome = true
  | [], _, _, _, h => by simpa [keysT] using h
  | n :: l, t, k, hl, h => by
    rw [keysT, Trie.seq_eq]
    refine getF_keysT_of l _ (fun m hm ↦ hl m (List.mem_cons_of_mem _ hm)) ?_
    have hn := hl n List.mem_cons_self
    rw [Check.getF_eq, Check.setF_eq, Check.get_set_eq () _ t n k hn, ← Check.getF_eq]
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (by simp)
      · exact Or.inl h
    · exact Or.inr (by split <;> simp [h])

theorem dstInF_of {body : List Stmt} {v : V} (h : dstIn body v = true) : dstInF (dstT body) body v = true := by
  unfold dstInF
  cases hv : vnum v with
  | none => exact h
  | some k =>
    simp only
    cases hk : Nat.blt (k + 1) (2 ^ Exec.indexDepth)
    · exact h
    · simp only [Bool.cond_true]
      refine getF_keysT_of _ _ (fun n hn ↦ ?_) (Or.inl ?_)
      · simpa using (List.mem_filter.1 hn).2
      · obtain ⟨s, hs, hsv⟩ := List.any_eq_true.1 h
        refine List.mem_filter.2 ⟨List.mem_filterMap.2 ⟨v, List.mem_flatMap.2 ⟨s, hs, ?_⟩, hv⟩, hk⟩
        cases s <;> simp_all

/-- `faRetAt`'s check of a frame run's values from `k` on, the run's cells from `c`. -/
noncomputable def runW (body : List Stmt) (D : Trie Unit) (A : FSt) (c : ℕ) : ℕ → List V → Bool
  | _, [] => true
  | k, v :: vs => (!dstInF D body v || A.hasW (c + k)) && runW body D A c (k + 1) vs

theorem runW_spec {body : List Stmt} {A : FSt} {c : ℕ} : ∀ (k : ℕ) (l : List V),
    runW body (dstT body) A c k l = true → ∀ j (hj : j < l.length),
      (!dstIn body l[j] || A.hasW (c + (k + j))) = true
  | _, [], _, j, hj => absurd hj (Nat.not_lt_zero _)
  | k, v :: vs, h, j, hj => by
    simp only [runW, Bool.and_eq_true] at h
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero]
      cases hd : dstIn body v
      · rfl
      · simpa [dstInF_of hd] using h.1
    | succ j =>
      simp only [List.getElem_cons_succ]
      rw [show k + (j + 1) = k + 1 + j by omega]
      exact runW_spec (k + 1) vs h.2 j (by simpa using hj)

/-- `faRetAt`, its frame run's values by `runW`. -/
noncomputable def faRetAtF (X : Bridge.AlignCtx) (body : List Stmt) (D : Trie Unit) (fas : List (ℕ × ℕ)) (A : FSt) :
    Stmt → Bool
  | .atom (.frameAddr p (r :: rs)) => runW body D A (X.locAt r.idx) 0 (r :: rs) &&
      fas.all fun q ↦ !(decide (p = V.n q.1) && Nat.ble (rs.length + 1) q.2) || A.hasW (X.locAt r.idx + q.2)
  | _ => true

theorem faRetAt_of_F {X : Bridge.AlignCtx} {body : List Stmt} {fas : List (ℕ × ℕ)} {A : FSt} {s : Stmt}
    (h : faRetAtF X body (dstT body) fas A s = true) : faRetAt X body fas A s = true := by
  cases s <;> try rfl
  rename_i a
  cases a <;> try rfl
  rename_i p l
  cases l
  · rfl
  rename_i r rs
  simp only [faRetAtF, Bool.and_eq_true] at h
  simp only [faRetAt, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun k hk ↦ ?_, List.all_eq_true.1 h.2⟩
  have := runW_spec 0 (r :: rs) h.1 k (by simpa using hk)
  rw [Nat.zero_add] at this
  rw [List.getElem?_eq_getElem (by simpa using hk)]
  exact this

/-- **`faRetOk` in one pass**: at each return (`retOffs`), the walk's state has the frame run cells (`faRetAtF`). -/
noncomputable def faRetOkF (Cf : CFun) (code : List OffsetInstruction) : Bool :=
  !faNeed Cf || (retOffs 0 code).all fun i ↦ match retSt Cf.frame code i with
    | some A => stmtsAll (faRetAtF Cf.X Cf.fn.body (dstT Cf.fn.body) Cf.H.fas A) Cf.fn.body
    | none => false

theorem faRetOk_of_F {Cf : CFun} {code : List OffsetInstruction} (h : faRetOkF Cf code = true) :
    faRetOk Cf code = true := by
  unfold faRetOk
  unfold faRetOkF at h
  cases hf : faNeed Cf
  · rfl
  simp only [hf, Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h ⊢
  intro i hi
  split
  · rename_i a hc
    have := h i (by simpa using mem_retOffs code 0 i a hc)
    split at this
    · rename_i A hA
      rw [hA]
      rw [stmtsAll_eq] at this
      exact stmtsAll_of fun s hs ↦ faRetAt_of_F (List.all_eq_true.1 this s hs)
    · exact absurd this Bool.false_ne_true
  · rfl

end

end LeanVM.Guest.CoreMode
