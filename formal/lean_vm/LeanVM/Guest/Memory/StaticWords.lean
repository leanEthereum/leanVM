/-
  LeanVM.Guest.Memory.StaticWords

  The words of a call tree from the static checker counting words at the frame sizes, hand bounds
  for some functions taken as hypotheses.
-/

module

public import LeanVM.Guest.Memory.StaticSound

/-!
# Words from the checker

Counting words (`α = true`) at the frame sizes `fs`, a tree's cost is its words: each instance's
frame and the `HeapBuf`s its path allocates, each phantom's frame (`total_eq_cost`, given
`Tree.BufsOk`). So a certificate checked counting words at `fs` bounds the words
(`total_le_of_stat`, `total_le_of_loop`, `totalLe_of_stat`), the functions of a set `X` left to
hand bounds on their words (`HandOk`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {P : Core.Program} {fs : String → ℕ}

mutual
/-- **Counting words at the frame sizes, the cost is the words.** -/
theorem total_eq_cost : ∀ t : Tree, t.BufsOk P → t.total fs = t.cost P true fs
  | t@(.node f σ bufs kids), hb => by
      simp only [Tree.BufsOk] at hb
      obtain ⟨hbufs, hbk⟩ := hb
      rw [Tree.total, Tree.cost, ← hbufs, totalKids_eq_costKids kids hbk]
      simp only [↓reduceIte]
      omega
  | .phantom f _, _ => by rw [Tree.total, Tree.cost]; rfl

theorem totalKids_eq_costKids : ∀ ks : List Tree, Tree.BufsOkKids P ks →
    Tree.totalKids fs ks = Tree.costKids P true fs ks
  | [], _ => by rw [Tree.totalKids, Tree.costKids]
  | k :: ks, hb => by
      simp only [Tree.BufsOkKids] at hb
      rw [Tree.totalKids, Tree.costKids, total_eq_cost k hb.1, totalKids_eq_costKids ks hb.2]
end

variable {rd : Reader} {cert : String → Cert}

/-- **Hand bounds**: every valid tree of a function of `X` satisfies its certificate, in words. -/
def HandOk (P : Core.Program) (fs : String → ℕ) (cert : String → Cert) (X : String → Prop) : Prop :=
  ∀ f, X f → ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.Valid P rd args rets →
    t.BufsOk P → Bound P true cert fs t args

/-- A hand bound on the words of `f`'s trees, under its certificate's preconditions, is what
`HandOk` asks of a `stat` certificate. -/
theorem bound_of_total {f : String} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .stat pre b ks)
    (h : ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.Valid P rd args rets →
      t.BufsOk P → ArgsPre pre args → t.total fs ≤ b.eval args)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.Valid P rd args rets) (hb : t.BufsOk P) :
    Bound P true cert fs t args := by
  unfold Bound
  rw [hn, hcf]
  intro hpre
  rw [← total_eq_cost t hb]
  exact h rd t args rets hn hv hb hpre

/-- **A certificate checked counting words bounds the words**, under its preconditions. -/
theorem total_le_of_stat {X : String → Prop} (hchk : CheckedExcept P true cert fs X)
    (hX : HandOk P fs cert X) {f : String} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .stat pre b ks) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid P rd args rets) (hb : t.BufsOk P) (hpre : ArgsPre pre args) :
    t.total fs ≤ b.eval args := by
  rw [total_eq_cost t hb]
  exact cost_le_of_stat hchk (fun f hf => hX f hf rd) hcf hn hv hb hpre

/-- **A loop checked counting words**: from `g^a` to `g^e`, `e - a` times its iteration's
bound. -/
theorem total_le_of_loop {X : String → Prop} (hchk : CheckedExcept P true cert fs X)
    (hX : HandOk P fs cert X) {f : String} {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff}
    {ks : List (V × ℕ)} (hcf : cert f = .loop endc pre b ks) {t : Tree} {args rets : List E}
    (hn : t.name = f) (hv : t.Valid P rd args rets) (hb : t.BufsOk P) {a e : ℕ}
    (ha : args.getD 0 0 = ofK (gpow a)) (he : endOf endc args = ofK (gpow e)) (hae : a < e)
    (heo : e < 2 ^ 64 - 1) (hpre : ArgsPre pre args) : t.total fs ≤ (e - a) * b.eval args := by
  rw [total_eq_cost t hb]
  exact cost_le_of_loop hchk (fun f hf => hX f hf rd) hcf hn hv hb ha he hae heo hpre

/-- **A constant certificate checked counting words** is a `TotalLe`. -/
theorem totalLe_of_stat {X : String → Prop} (hchk : CheckedExcept P true cert fs X)
    (hX : HandOk P fs cert X) {f : String} {B : ℕ} {ks : List (V × ℕ)}
    (hcf : cert f = .stat [] ⟨B, []⟩ ks) : TotalLe P fs f fun _ => B :=
  fun _ _ _ _ hn hv hb => by
    have := total_le_of_stat hchk hX hcf hn hv hb (fun _ h => (List.not_mem_nil h).elim)
    simpa [Aff.eval] using this

end
end LeanVM.Guest.Memory
