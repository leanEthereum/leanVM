module

public import LeanVM.Guest.Complete.CallComplete
public import LeanVM.Guest.Memory.HintsIn

/-!
# Completeness of a call, placed by the aligned allocator

`CallCompletes` is layout-free: its tree's `HeapBuf` pointers and `frameAddr`s are whatever its
valuation picks, so it does not give what B2's completeness reads of `main`'s tree (`B2C.MainB1`:
`PlacedA`, `LoadsInA`, `HintsIn` at Hotwire's aligned layout). Pointers cannot be moved after
the fact (a counter `g^n` may equal an address, some buffers hold pointers), so the placement is
part of the statement, as the bus era's `CompleteAtDP` had it over the old allocator.

`CallAtA … R D Out Pre Post B fp c e`: the call placed with its frame at `fp` (its block `B`
words) and its other words from the cursor `c` to `e`, as `Tree.instsA` places it. Its own words
`W` lie in its frame past the header (`[fp + 2, fp + B)`) or in `[c, e)`, pairwise disjoint, `c ≤ e`, and
every memory holding them satisfies `Out` (what a caller and the later callees read of them). On
every memory defined on its first `2^k` words, holding `W` and satisfying `Pre`, the call has a
valid tree, its buffers its body's, of block `B` and end `e`, placed at `(fp, c)` (`PlacedA`),
its loads and heap hints in its subtree's data or the region `R` its caller hands it, its data
containing `D`, satisfying `Post`.

`CallCompletesA`: the block is fixed, and the call completes at every position whose cursor is
past its block (`fp + B ≤ c`), its end and claimed data a function of the position.

`CallAtA.toCallCompletes`-style forgetting: `CallCompletesA.toCallCompletes`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1

@[expose] public section

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ)

/-- Runs each within the frame part `[lo, hi)` or the cursor part `[c, e)`, pairwise disjoint. -/
def WordsInA (W : Words) (lo hi c e : ℕ) : Prop :=
  (∀ q ∈ W, (lo ≤ q.1 ∧ q.1 + q.2.length ≤ hi) ∨ (c ≤ q.1 ∧ q.1 + q.2.length ≤ e)) ∧
    W.Pairwise fun q q' => q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1

/-- **A call completes at a position, aligned**: frame `fp` of block `B`, cursor `c`, end `e`. -/
def CallAtA (k : ℕ) (f : String) (args rets : List E) (R D : ℕ → Prop) (Out Pre : Reader → Prop)
    (Post : Reader → Tree → Prop) (B fp c e : ℕ) : Prop :=
  ∃ W : Words, WordsInA W (fp + 2) (fp + B) c e ∧ c ≤ e ∧ (∀ rd, HoldsWords rd W → Out rd) ∧
    ∀ rd, LowDef k rd → HoldsWords rd W → Pre rd →
      ∃ t : Tree, t.name = f ∧ t.Valid coreProgram rd args rets ∧ t.BufsOk coreProgram ∧
        t.block fs coreProgram.loop = B ∧ t.endA fs coreProgram.loop al c = e ∧
        t.PlacedA coreProgram fs al cert (fp, c) ∧ t.LoadsInA coreProgram fs al cert R (fp, c) ∧
        t.HintsIn coreProgram fs al cert R (fp, c) ∧ (∀ i, D i → t.DataA coreProgram fs al cert (fp, c) i) ∧
        Post rd t

/-- **A call completes, aligned**: its block fixed, at every position past it. -/
def CallCompletesA (k : ℕ) (f : String) (args rets : List E) (R : ℕ → Prop) (D : ℕ → ℕ → ℕ → Prop)
    (Out Pre : Reader → Prop) (Post : Reader → Tree → Prop) : Prop :=
  ∃ B, ∀ fp c, fp + B ≤ c → ∃ e, CallAtA fs al cert k f args rets R (D fp c) Out Pre Post B fp c e

variable {fs al cert}

/-! ## Weakening -/

theorem CallAtA.mono {k : ℕ} {f : String} {args rets : List E} {R R' D D' : ℕ → Prop}
    {Out Out' Pre Pre' : Reader → Prop} {Post Post' : Reader → Tree → Prop} {B fp c e : ℕ}
    (h : CallAtA fs al cert k f args rets R D Out Pre Post B fp c e) (hR : ∀ i, R i → R' i)
    (hD : ∀ i, D' i → D i) (hO : ∀ rd, Out rd → Out' rd) (hP : ∀ rd, Pre' rd → Pre rd)
    (hQ : ∀ rd t, Pre' rd → Post rd t → Post' rd t) :
    CallAtA fs al cert k f args rets R' D' Out' Pre' Post' B fp c e := by
  obtain ⟨W, hW, hce, hO', hr⟩ := h
  refine ⟨W, hW, hce, fun rd hw => hO rd (hO' rd hw), fun rd hl hw hp => ?_⟩
  obtain ⟨t, hn, hv, hb, hB, he, hpl, hlo, hhi, hd, hq⟩ := hr rd hl hw (hP rd hp)
  exact ⟨t, hn, hv, hb, hB, he, hpl, loadsInA_mono t (fp, c) hR hlo, hintsIn_mono t (fp, c) hR hhi,
    fun i hi => hd i (hD i hi), hQ rd t hp hq⟩

/-! ## Forgetting the placement -/

theorem WordsInA.wordsIn {W : Words} {fp B c e : ℕ} (h : WordsInA W (fp + 2) (fp + B) c e) (hc : fp + B ≤ c) :
    WordsIn W fp (max e c - fp) :=
  ⟨fun q hq => by rcases h.1 q hq with h' | h' <;> omega, h.2⟩

/-- **The placed form gives the layout-free one.** -/
theorem CallCompletesA.toCallCompletes {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop}
    {D : ℕ → ℕ → ℕ → Prop} {Out Pre : Reader → Prop} {Post : Reader → Tree → Prop}
    (h : CallCompletesA fs al cert k f args rets R D Out Pre Post) : CallCompletes k f args rets Pre Post := by
  obtain ⟨B, hB⟩ := h
  intro b
  obtain ⟨e, W, hW, -, -, hr⟩ := hB b (b + B) le_rfl
  refine ⟨max e (b + B) - b, W, hW.wordsIn le_rfl, fun rd hl hw hp => ?_⟩
  obtain ⟨t, hn, hv, hb, -, -, -, -, -, -, hq⟩ := hr rd hl hw hp
  exact ⟨t, hn, hv, hb, hq⟩

end
end LeanVM.Guest.Complete
