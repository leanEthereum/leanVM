module

public import LeanVM.Cost.AS.Bounds.Trace
public import LeanVM.Cost.AS.Bounds.Roots
public import LeanVM.Cost.AS.Bounds.Runner
public import LeanVM.Cost.AS.Bounds.Facts
public import LeanVM.Cost.AS.Top
public import LeanVM.Protocol.Extraction.AS.TraceShape
import all LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.Extraction.AS.TraceShape
import all LeanVM.Protocol.Whir.Sound.DescentC

/-!
# Bounds: the finish

The finish (`finishLC`) prices level 0's shape, every root's word (`wordsPrice`), the descent
across levels (`traceCostB`, at words of at most `128` lanes: `size_wordsGo`), level 0's stack
and the candidate run: **`finishL_cost`**, within `finishPrice`. A decoded trace is small
(`traceSmall_of_shape`).
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Verifier LeanVM.Extraction.AS LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Semantics

public section

variable (P : MachineProgram)

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

theorem size_wordArrOf (μ R : ℕ) (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (i : ℕ) (x : LeanVM.Protocol.Digest × ℕ × ℕ) (y : ℕ) :
    ((wordArrOf μ R qs i x).getD y #[]).size ≤ x.2.2 :=
  size_laneRows _ i (leavesAt qs x) x.2.1 x.2.2 y fun l hl ↦ (length_subtreeLeavesWith _ _ _ _ l hl).le

theorem size_wordsGo (μ R : ℕ) (qs : List (Common.PermutationQuery KeccakState × KeccakState)) (Wd : ℕ) :
    ∀ (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)) (a : ℕ), (∀ x ∈ roots, x.2.2 ≤ Wd) →
      ∀ i y, (((wordsGo μ R qs a roots).getD i #[]).getD y #[]).size ≤ Wd
  | [], _, _, i, y => by simp [wordsGo]
  | x :: xs, a, hx, i, y => by
    cases i with
    | zero =>
      simp only [wordsGo, List.getD_cons_zero]
      exact (size_wordArrOf μ R qs a x y).trans (hx x List.mem_cons_self)
    | succ i =>
      simp only [wordsGo, List.getD_cons_succ]
      exact size_wordsGo μ R qs Wd xs (a + 1) (fun z hz ↦ hx z (List.mem_cons_of_mem _ hz)) i y

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

/-! ## The finish -/

/-- The price bound of level 0's stack (`stackA_cost`). -/
@[expose] def stackPrice (μ : ℕ) : ℕ := μ * (174 * 2 ^ μ + 186944) + 90 * 2 ^ μ + 4000

/-- The price bound of the candidate run (`candidateRunner_cost`). -/
@[expose] def runnerPrice (lay : LayoutLite) (ℓ : ℕ) : ℕ :=
  (74 * lay.logMemory + 121) * 2 ^ lay.logMemory + (74 * ℓ + 121) * 2 ^ ℓ + 73 * ℓ + 357 +
    (runnerStepPrice lay.logMemory ℓ + 41) * stepCapLite lay + 45 * 2 ^ lay.logMemory + 1800

/-- The price bound of the finish. -/
@[expose] def finishPrice (D Wl qn ℓ : ℕ) (lay : LayoutLite) (ρ : ℕ) (tr : WhirTrace)
    (roots : List (LeanVM.Protocol.Digest × ℕ × ℕ)) : ℕ :=
  2 * (15 * (lay.stackLog + ρ + 0) + 20000) + wordsPrice D Wl qn lay.stackLog ρ 0 roots +
    traceCostB lay.stackLog ρ 128 tr 0 + stackPrice lay.stackLog + runnerPrice lay ℓ + 1000

/-- **The finish, priced.** -/
theorem finishL_cost (hP : Includes P finishLC.costDeps) (prog : Semantics.LeanIsaProgram)
    (input : PublicInput) (qs : List (Common.PermutationQuery KeccakState × KeccakState))
    (D Wl : ℕ) (hW : ∀ x, x ≤ 2 * 2 ^ D → limbCount x ≤ Wl) (hN : qs.length + 2 ≤ 2 ^ D)
    (b : Bool) (lay : LayoutLite) (ρ : ℕ) (tr : WhirTrace) (s : VerifierProgramState)
    (hF : LayoutFacts lay) (h1 : 16 ≤ lay.stackLog) (h2 : lay.stackLog ≤ 30) (h3 : 1 ≤ ρ) (h4 : ρ ≤ 4)
    (hroots : RootsOk (s.roots.map Prod.snd)) (hs : TraceSmall tr) (hd : traceDepth tr < 2 ^ 40) :
    machineCost P finishLC.costIdx [encodeValue prog, encodeValue input, encodeValue qs,
      encodeValue ((b, ((lay, ρ), tr)), s)] ≤
      finishPrice D Wl qs.length prog.logSize lay ρ tr s.roots := by
  rw [finishLC.costEq P hP]
  dsimp only
  have hl : Protocol.EndToEnd.laneBits = 6 := rfl
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := lvC_limbs lay.stackLog ρ 0
  have hx : ∀ x ∈ s.roots, 8 ≤ x.2.2 ∧ x.2.2 < 2 ^ 57 ∧ x.2.1 < 64 := fun x hx ↦ by
    have := hroots.2 x.2 (List.mem_map_of_mem hx)
    omega
  have hlen : s.roots.length ≤ 6 := by simpa using hroots.1
  have c1 := lvC_cost P (by includes) lay.stackLog ρ 0 (by omega) (by omega) (by omega)
  have c2 := wordsGoWorker_cost P (by includes) lay.stackLog ρ qs D Wl hW hN (by omega) (by omega)
    s.roots 0 hx (by omega)
  have c3 := descendTraceGo_cost P (by includes) lay.stackLog ρ
    (wordsGo lay.stackLog ρ qs 0 s.roots) 128 (by omega) (by omega)
    (size_wordsGo lay.stackLog ρ qs 128 s.roots 0 fun x hx ↦ by
      have := hroots.2 x.2 (List.mem_map_of_mem hx); omega) (by norm_num) tr 0 (by omega) hs
  have s1 : 1 <<< (lay.stackLog - 6) < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq, one_mul]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num : 2 ^ 24 < 2 ^ 64)
  have s2 : 2 ^ (lay.stackLog - 6) < 2 ^ 64 := by rwa [Nat.shiftLeft_eq, one_mul] at s1
  have s3 : 1 <<< ((lvC lay.stackLog ρ 0).1 + (lvC lay.stackLog ρ 0).2.1) < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq, one_mul]; omega
  rw [hl]
  simp (disch := omega) only [limbs_of_lt]
  split_ifs with g1 g2 g3
  · rw [Auto.Option.bind.c154.costEq P (by includes) _
      (fun T ↦ if T.1 = 6 then candidateRunner prog input lay (stackA lay.stackLog T.2) else none)
      _ (fun T ↦ RunsApp.of_spec (finishLC.lam0.costSpec P (by includes) prog input
        ((b, ((lay, ρ), tr)), s) T))]
    rcases hT : descendTraceC lay.stackLog ρ (wordsGo lay.stackLog ρ qs 0 s.roots) tr 0 with _ | T
    · simp only
      unfold finishPrice
      omega
    · simp only
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [finishLC.lam0.costEq P (by includes)]
      dsimp only
      have hT1 := descendTraceC_fst _ _ _ tr 0 hs hT
      rw [hl, limbs_of_lt (by omega : T.1 < 2 ^ 64), limbs_of_lt (by norm_num : (6 : ℕ) < 2 ^ 64)]
      have c4 := stackA_cost P (by includes) lay.stackLog T.2 (by omega) (by omega)
      have c5 := candidateRunner_cost P (by includes) prog input lay hF.logMemory_le hF.logBytecode_le
        hF.heights_le hF.heights_length hF.index_lt_word (stackA lay.stackLog T.2)
      split_ifs <;> (unfold finishPrice stackPrice runnerPrice; omega)
  all_goals unfold finishPrice; omega

end

end LeanVM.Cost.Bounds.AS
