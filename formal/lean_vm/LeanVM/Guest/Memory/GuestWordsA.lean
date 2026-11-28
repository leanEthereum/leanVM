/-
  LeanVM.Guest.Memory.GuestWordsA

  The guest's static certificates counting words on the aligned allocator (`Memory/GuestWordsA/`,
  written by `scripts/count/words.py`), checked by the kernel (`wa_checked`), and the bounds they
  give every valid tree of a certified function, at any frame sizes and aligned flags within the
  certificates' (`wa_cost_le_of_stat`, `wa_cost_le_of_loop`).
-/

module

public import LeanVM.Guest.Memory.GuestWordsA.All
public import LeanVM.Guest.Memory.FamilySound
public import LeanVM.Guest.Memory.WordsA

/-!
# The guest's words, certified

`waCertOf g`: the certificate of the core function `g`, by its index (`Data.wacertJ`); `.none` for
the functions whose words read a size or a loop's end from memory, and their callers
(`words.py --report`: `main`, `verify_sub`'s opening arms, the link's rounds, ...). `fsW`, `alW`: the
frame sizes (`main`'s with the jump table's slots) and the aligned flags the certificates were made at
(`walJ`: a function holding a `KECCAK`, or an arm of a `dispatch` with such an arm).

`wa_checked`: every function passes the static checker counting words at `fsPad fsW alW`, by the
kernel. So every valid tree of a certified function costs at most its certificate's bound
(`wa_cost_le_of_stat`, `wa_cost_le_of_loop`), at any frame sizes `fs ≤ fsW` and aligned flags
`al ≤ alW` (`cost_mono`), and its aligned words are at most that (`Memory/WordsA.lean`'s
`wordsA_le_cost`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The certificates counting aligned words, by name. -/
noncomputable def waCertOf (g : String) : Cert := Data.wacertJ (coreIdx g)

/-- The frame sizes the certificates were made at, by name. -/
noncomputable def fsW (g : String) : ℕ := Data.wfsJ (coreIdx g)

/-- The aligned flags the certificates were made at, by name. -/
noncomputable def alW (g : String) : Bool := Data.walJ (coreIdx g)

theorem waCertOf_of_idx {j : ℕ} {g : String} (h : (coreProgram[j]?).map Fn.name = some g) :
    waCertOf g = Data.wacertJ j := by
  rw [waCertOf, coreIdx_of_name h]

/-- **The guest's certificates counting aligned words check**, by the kernel. -/
theorem wa_checked : Checked coreProgram true waCertOf (fsPad fsW alW) :=
  checked_of_chkS wa_all fun j hj => by
    simp only [fsPad, fsW, alW, coreIdx_getElem hj, Data.waomegaJ]

mutual
/-- **The cost grows with the frame weights.** -/
theorem cost_mono {P : Core.Program} {α : Bool} {ω ω' : String → ℕ} (h : ∀ g, ω g ≤ ω' g) :
    ∀ t : Tree, t.cost P α ω ≤ t.cost P α ω'
  | .node f σ _ kids => by
      rw [Tree.cost, Tree.cost]
      have := costKids_mono (P := P) (α := α) h kids
      have := h f
      omega
  | .phantom f _ => by
      rw [Tree.cost, Tree.cost]
      split
      · exact h f
      · exact le_rfl

theorem costKids_mono {P : Core.Program} {α : Bool} {ω ω' : String → ℕ} (h : ∀ g, ω g ≤ ω' g) :
    ∀ ks : List Tree, Tree.costKids P α ω ks ≤ Tree.costKids P α ω' ks
  | [] => by rw [Tree.costKids, Tree.costKids]
  | k :: ks => by
      rw [Tree.costKids, Tree.costKids]
      exact Nat.add_le_add (cost_mono h k) (costKids_mono h ks)
end

/-- Frame sizes and aligned flags within the certificates' pad within their weights. -/
theorem fsPad_le {fs : String → ℕ} {al : String → Bool} (hfs : ∀ g, fs g ≤ fsW g)
    (hal : ∀ g, al g = true → alW g = true) (g : String) : fsPad fs al g ≤ fsPad fsW alW g := by
  unfold fsPad padOf
  have := hfs g
  by_cases h : al g = true
  · simp [h, hal g h]; omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; split <;> omega

variable {fs : String → ℕ} {al : String → Bool} {rd : Reader}

/-- **A certified function's cost**, at frame sizes and aligned flags within the certificates'. -/
theorem wa_cost_le_of_stat (hfs : ∀ g, fs g ≤ fsW g) (hal : ∀ g, al g = true → alW g = true)
    {f : String} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : waCertOf f = .stat pre b ks)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (hpre : ArgsPre pre args) :
    t.cost coreProgram true (fsPad fs al) ≤ b.eval args :=
  (cost_mono (fsPad_le hfs hal) t).trans
    (cost_le_of_stat wa_checked (fun _ h => h.elim) hcf hn hv hb hpre)

/-- **A certified loop's cost**: from `g^a` to `g^e`, `e - a` iterations and its last, untaken,
tail call's frame. -/
theorem wa_cost_le_of_loop (hfs : ∀ g, fs g ≤ fsW g) (hal : ∀ g, al g = true → alW g = true)
    {f : String} {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : waCertOf f = .loop endc pre b ks) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid coreProgram rd args rets) (hb : t.BufsOk coreProgram) {a e : ℕ}
    (ha : args.getD 0 0 = ofK (addressOfIndex a)) (he : endOf endc args = ofK (addressOfIndex e))
    (hae : a < e) (heo : e < 2 ^ 64 - 1) (hpre : ArgsPre pre args) :
    t.cost coreProgram true (fsPad fs al) ≤ (e - a) * b.eval args + fsPad fsW alW f :=
  (cost_mono (fsPad_le hfs hal) t).trans
    (by simpa using cost_le_of_loop wa_checked (fun _ h => h.elim) hcf hn hv hb ha he hae heo hpre)

/-- **The aligned words of a tree of a certified function.** -/
theorem wa_wordsA_le_of_stat (hfs : ∀ g, fs g ≤ fsW g) (hal : ∀ g, al g = true → alW g = true)
    (htl : ∀ f, fs (tailKey f) ≤ fs f) {lp : String → Bool}
    {f : String} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : waCertOf f = .stat pre b ks)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (hpre : ArgsPre pre args) :
    t.wordsA fs lp al ≤ b.eval args :=
  (wordsA_le_cost htl hb).trans (wa_cost_le_of_stat hfs hal hcf hn hv hb hpre)

end
end LeanVM.Guest.Memory
