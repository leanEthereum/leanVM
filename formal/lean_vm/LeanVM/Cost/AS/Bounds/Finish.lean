module

public import LeanVM.Cost.AS.Bounds.Candidate
public import LeanVM.Cost.AS.Bounds.Budget
import all LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Cost.AS.Bounds.TraceShape
import all LeanVM.Protocol.Whir.Sound.DescentC
import all LeanVM.Protocol.Extraction.Fast.Transcript

/-!
# Bounds: the finish

The finish (`finishLC`) prices the transcript's index at the roots' longest lookup (one for every
root, `capOf_cost`), every root's word (`wordsPrice`), the descent across levels (`traceCostB`, at
words of at most `64` lanes: `size_wordsGo`), level 0's stack and the candidate execution:
**`finishL_cost`**, within `finishPrice`, the link's chunks' price at most `C`. A decoded trace is
small (`traceSmall_of_shape`).
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Verifier LeanVM.Extraction.AS LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Semantics LeanVM.Protocol.EndToEnd.Sound

public section

variable (P : MachineProgram)

attribute [local instance] lexOrd

/-! ## The words' widths -/

theorem size_laneRows (n i : ℕ) (lv : Array (List K)) (h w y : ℕ) (hlv : ∀ l ∈ lv, l.length ≤ w) :
    ((laneRows n i lv h w).getD y #[]).size ≤ w := by
  unfold laneRows
  rw [Array.getD]
  split
  · rename_i hy
    change ((Array.ofFn fun v : Fin n ↦ laneRow i lv h w v)[y]'hy).size ≤ w
    rw [Array.getElem_ofFn]
    unfold laneRow
    rw [List.size_toArray]
    exact (length_lanesOf_le i _).trans (length_leafAt_le lv h w y w hlv le_rfl)
  · simp

theorem size_wordArrOf (μ R : ℕ) (I : SortedMap (List UInt64 × ℕ) Hits)
    (i : ℕ) (x : LeanVM.Protocol.Digest × ℕ × ℕ) (y : ℕ) :
    ((wordArrOf μ R I i x).getD y #[]).size ≤ x.2.2 :=
  size_laneRows _ i (leavesAt I x) x.2.1 x.2.2 y fun l hl ↦
    (subtreeLeavesWith_mem_length _ _ _ _ l hl).le

theorem size_wordsGo (μ R : ℕ) (I : SortedMap (List UInt64 × ℕ) Hits) (Wd : ℕ) :
    ∀ (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)) (a : ℕ), (∀ x ∈ roots, x.2.2 ≤ Wd) →
      ∀ i y, (((wordsGo μ R I a roots).getD i #[]).getD y #[]).size ≤ Wd
  | [], _, _, i, y => by simp [wordsGo]
  | x :: xs, a, hx, i, y => by
    cases i with
    | zero =>
      simp only [wordsGo, List.getD_cons_zero]
      exact (size_wordArrOf μ R I a x y).trans (hx x List.mem_cons_self)
    | succ i =>
      simp only [wordsGo, List.getD_cons_succ]
      exact size_wordsGo μ R I Wd xs (a + 1) (fun z hz ↦ hx z (List.mem_cons_of_mem _ hz)) i y

/-! ## A decoded trace is small -/

theorem traceSmall_of_shape (logN : ℕ) (hN : logN ≤ 30) :
    ∀ (A : ℕ) (cfg : List Whir.Level) (tr : WhirTrace), TraceShape logN A cfg tr →
      (∀ lv ∈ cfg, lv.fold ≤ 6) → TraceSmall tr ∧ traceDepth tr + 1 ≤ cfg.length
  | _, [], tr, h, _ => by cases tr <;> simp [TraceShape] at h
  | A, [lv], .final rounds folded, h, hf => by
    have h6 := hf lv List.mem_cons_self
    have hp : 2 ^ (logN - (A + lv.fold)) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [TraceShape] at h
    refine ⟨⟨by omega, by omega⟩, by simp [traceDepth]⟩
  | A, [lv], .mid _ _ _, h, _ => by simp [TraceShape] at h
  | A, lv :: nx :: rest, .final _ _, h, _ => by simp [TraceShape] at h
  | A, lv :: nx :: rest, .mid rounds high tr, h, hf => by
    have h6 := hf lv List.mem_cons_self
    simp only [TraceShape] at h
    obtain ⟨ih1, ih2⟩ := traceSmall_of_shape logN hN (A + lv.fold) (nx :: rest) tr h.2.2
      fun l hl ↦ hf l (List.mem_cons_of_mem _ hl)
    refine ⟨⟨by omega, by omega, ih1⟩, ?_⟩
    simp only [traceDepth, List.length_cons] at ih2 ⊢
    omega

/-! ## The roots' longest lookup -/

theorem capOf_le (Wd : ℕ) : ∀ (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)),
    (∀ x ∈ roots, x.2.2 ≤ Wd) → capOf roots ≤ max 64 (8 * Wd)
  | [], _ => le_max_left _ _
  | x :: xs, h => by
    have := capOf_le Wd xs fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    have := h x List.mem_cons_self
    simp only [capOf]
    omega

/-- **The roots' longest lookup** (`capOf.c476`), which compiles the tail's lookup twice: at most
`60·2^n`, for `n` roots. -/
theorem capOf_cost (hP : Includes P Auto.LeanVM.Extraction.AS.capOf.c476.costDeps) :
    ∀ (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)), (∀ x ∈ roots, x.2.2 < 2 ^ 57) →
      machineCost P Auto.LeanVM.Extraction.AS.capOf.c476.costIdx [encodeValue roots] + 50 ≤
        60 * 2 ^ roots.length
  | [], _ => by rw [Auto.LeanVM.Extraction.AS.capOf.c476.costEq_nil P hP]; simp
  | x :: xs, h => by
    rw [Auto.LeanVM.Extraction.AS.capOf.c476.costEq_cons P hP]
    have ih := capOf_cost hP xs fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    have hx := h x List.mem_cons_self
    have hc := capOf_le (2 ^ 57) xs fun y hy ↦ (h y (List.mem_cons_of_mem _ hy)).le
    rw [limbs_of_lt (by omega : 8 * x.2.2 < 2 ^ 64), limbs_of_lt (by omega : x.2.2 < 2 ^ 64),
      limbs_of_lt (by omega : capOf xs < 2 ^ 64)]
    simp only [List.length_cons, max_self, pow_succ]
    split_ifs <;> omega

/-! ## The finish -/

/-- The price bound of the finish, the link's chunks' price at most `C`. -/
@[expose] def finishPrice (D Wl qn C : ℕ) (lay : LayoutLite) (ρ : ℕ) (tr : WhirTrace)
    (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)) : ℕ :=
  60 * 2 ^ roots.length + transcriptIndexPrice D (capOf roots) qn Wl +
    wordsPrice D Wl lay.stackLog ρ 0 roots + traceCostB lay.stackLog ρ 64 tr 0 +
    stackPrice lay.stackLog + (C + 720100 * 2 ^ 30 * 6 + 2 ^ 39) + 1000

/-- **The finish, priced.** -/
theorem finishL_cost (hP : Includes P finishLC.costDeps) (prog : Semantics.LeanIsaProgram)
    (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (D Wl : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ Wl) (hN : qs.length + 2 ≤ 2 ^ D)
    (lay : LayoutLite) (ρ : ℕ) (tr : WhirTrace) (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ))
    (hF : LayoutFacts lay) (h1 : 16 ≤ lay.stackLog) (h2 : lay.stackLog ≤ 30) (h3 : 1 ≤ ρ) (h4 : ρ ≤ 4)
    (hroots : RootsOk lay.stackLog ρ (roots.map Prod.snd)) (hs : TraceSmall tr)
    (hd : traceDepth tr < 2 ^ 40) (C : ℕ)
    (hC : machineCost P Auto.LeanVM.Protocol.EndToEnd.Sound.chunksL.c402.costIdx [encodeValue lay] ≤ C) :
    machineCost P finishLC.costIdx [encodeValue prog, encodeValue qs, encodeValue lay, encodeValue ρ,
      encodeValue tr, encodeValue roots] ≤ finishPrice D Wl qs.length C lay ρ tr roots := by
  rw [finishLC.costEq P hP]
  have hl : Protocol.EndToEnd.laneBits = 6 := rfl
  have hx : ∀ x ∈ roots, x.2.2 < 2 ^ 57 ∧ x.2.1 < 64 := fun x hx ↦ by
    have := hroots.2.1 x.2 (List.mem_map_of_mem hx)
    omega
  have hcap := capOf_le 64 roots fun x hx ↦ (hroots.2.1 x.2 (List.mem_map_of_mem hx)).2.2
  have c0 := capOf_cost P (by includes) roots fun x h ↦ (hx x h).1
  have c0' := transcriptIndex_cost P (by includes) D (capOf roots) Wl hW (by omega) qs hN
  have hlen : roots.length ≤ 6 := by simpa using hroots.1
  have c2 := wordsGoWorker_cost P (by includes) lay.stackLog ρ qs (capOf roots) D Wl (by omega) hW hN
    (by omega) (by omega) roots 0 hx (by omega)
  have c3 := descendTraceGo_cost P (by includes) lay.stackLog ρ
    (wordsGo lay.stackLog ρ (transcriptIndex qs (capOf roots)) 0 roots) 64 (by omega) (by omega)
    (size_wordsGo lay.stackLog ρ (transcriptIndex qs (capOf roots)) 64 roots 0 fun x hx ↦ by
      have := hroots.2.1 x.2 (List.mem_map_of_mem hx); omega) (by norm_num) tr 0 (by omega) hs
  have c4 := bind_le P (by includes) _ (.closure finishLC.lam0.costIdx [encodeValue prog, encodeValue lay])
    (fun T ↦ RunsApp.of_spec (finishLC.lam0.costSpec P (by includes) prog lay T))
    (descendTraceC lay.stackLog ρ (wordsGo lay.stackLog ρ (transcriptIndex qs (capOf roots)) 0 roots)
      tr 0) (stackPrice lay.stackLog + (C + 720100 * 2 ^ 30 * 6 + 2 ^ 39) + 30) (fun T hT ↦ by
      have hT1 := descendTraceC_fst _ _ _ tr 0 hs hT
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        finishLC.lam0.costEq P (by includes), hl, limbs_of_lt (by omega : T.1 < 2 ^ 64),
        limbs_of_lt (by norm_num : (6 : ℕ) < 2 ^ 64)]
      have c5 := stackA_cost P (by includes) lay.stackLog T.2 (by omega) (by omega)
      have c6 := candidateL_cost P (by includes) prog lay hF
        (⟨stackA lay.stackLog T.2⟩ : Protocol.Column lay.stackLog) C hC
      simp only [List.length_cons, List.length_nil]
      unfold stackPrice
      split_ifs <;> omega)
  unfold finishPrice transcriptIndexPrice
  omega

end

end LeanVM.Cost.Bounds.AS
