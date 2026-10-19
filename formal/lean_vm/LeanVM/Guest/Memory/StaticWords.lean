/-
  LeanVM.Guest.Memory.StaticWords

  The words of a call tree from the static checker counting words: `total_le_cost`.
-/

module

public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.Memory.SizeTotal

/-!
# Words from the checker

Counting words (`α = true`), the checker bounds a tree's cost: its weight plus the `HeapBuf`s its
paths allocate. A tree's words (`Tree.total fs`) are its frames, its `HeapBuf`s and the frames of
its phantoms, the untaken `callIf`s'. With a weight `ω'` covering each function's frame and the
frames of all its `callIf` callees (`SkipLe`, from the syntax by `Stmt.blockSkips`), the words are
at most the cost (`total_le_cost`), so a certificate checked counting words at `ω'` bounds them
(`total_le_of_stat`, `total_le_of_loop`, `totalLe_of_stat`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

mutual
/-- The callees of a statement's `callIf`s. -/
def Stmt.skips : Stmt → List String
  | .ite _ z n => Stmt.blockSkips z ++ Stmt.blockSkips n
  | .match_ _ arms => Stmt.armsSkips arms
  | .callIf _ f _ => [f]
  | _ => []

/-- The callees of a block's `callIf`s. -/
def Stmt.blockSkips : List Stmt → List String
  | [] => []
  | s :: ss => Stmt.skips s ++ Stmt.blockSkips ss

/-- The callees of the arms' `callIf`s. -/
def Stmt.armsSkips : List (List Stmt) → List String
  | [] => []
  | a :: as => Stmt.blockSkips a ++ Stmt.armsSkips as
end

/-- **Each function's weight covers its frame and its `callIf` callees' frames.** -/
def SkipLe (P : Core.Program) (fs ω : String → ℕ) : Prop :=
  ∀ f fn, P.find? f = some fn → fs f + ((Stmt.blockSkips fn.body).map fs).sum ≤ ω f

section Skips

variable {fs : String → ℕ} {σ : Val}

theorem skipWords_append (cs cs' : List Call) :
    skipWords fs (cs ++ cs') = skipWords fs cs + skipWords fs cs' := by
  induction cs with
  | nil => simp [skipWords]
  | cons c cs ih => rw [List.cons_append, skipWords, skipWords, ih]; omega

/-- The frames of an outcome's untaken calls. -/
def Out.skipW (fs : String → ℕ) (o : Out) : ℕ := skipWords fs (calls o.evs)

theorem Out.skipW_seq (o k : Out) : (o.seq k).skipW fs ≤ o.skipW fs + k.skipW fs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> rcases k with es' | ⟨es', vs'⟩ | _ <;>
    simp [Out.seq, Out.pre, Out.skipW, Out.evs, calls_append, skipWords_append]

theorem Out.skipW_pre_inK (c : V) (o : Out) : (o.pre [.inK c]).skipW fs = o.skipW fs := by
  rcases o with es | ⟨es, vs⟩ | _ <;>
    simp [Out.pre, Out.skipW, Out.evs, calls, Ev.call?, List.filterMap_cons]

theorem pick_skipW {x : V} {args rets : List V} (gs : List String) (j : ℕ) :
    (pick σ x args rets j gs).skipW fs = 0 := by
  rcases pick_cases (σ := σ) (x := x) (a := args) (r := rets) gs j with h | ⟨g, -, h⟩ <;>
    rw [h] <;> simp [Out.skipW, Out.evs, calls, Ev.call?, skipWords]

mutual
/-- **A statement's path skips at most its `callIf` callees.** -/
theorem walk1_skips : ∀ s : Stmt, (walk1 σ s).skipW fs ≤ ((Stmt.skips s).map fs).sum
  | .atom a => by
      simp only [walk1, Out.skipW, Out.evs]
      rw [show calls [Ev.atom a] = [] from rfl, skipWords]; exact Nat.zero_le _
  | .ite c z n => by
      rw [walk1, Out.skipW_pre_inK]
      simp only [Stmt.skips, List.map_append, List.sum_append]
      split_ifs
      · exact (walk_skips z).trans (Nat.le_add_right _ _)
      · exact (walk_skips n).trans (Nat.le_add_left _ _)
  | .match_ x arms => by
      rw [walk1, Stmt.skips]
      exact walkArms_skips x arms 0
  | .call .. => by simp [walk1, Out.skipW, Out.evs, calls, Ev.call?, skipWords]
  | .callIf c f args => by
      rw [walk1]
      split_ifs <;> simp [Out.skipW, Out.evs, calls, Ev.call?, List.filterMap_cons, skipWords, Stmt.skips]
  | .dispatch x gs args rets => by rw [walk1, pick_skipW]; exact Nat.zero_le _
  | .ret _ => by simp [walk1, Out.skipW, Out.evs, calls, skipWords]

/-- **A block's path skips at most its `callIf` callees.** -/
theorem walk_skips : ∀ ss : List Stmt, (walk σ ss).skipW fs ≤ ((Stmt.blockSkips ss).map fs).sum
  | [] => by simp [walk, Out.skipW, Out.evs, calls, skipWords]
  | s :: ss => by
      rw [walk, Stmt.blockSkips, List.map_append, List.sum_append]
      exact (Out.skipW_seq _ _).trans (Nat.add_le_add (walk1_skips s) (walk_skips ss))

theorem walkArms_skips (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    (walkArms σ x j arms).skipW fs ≤ ((Stmt.armsSkips arms).map fs).sum
  | [], _ => by simp [walkArms, Out.skipW, Out.evs, calls, skipWords]
  | a :: as, j => by
      unfold walkArms
      rw [Stmt.armsSkips, List.map_append, List.sum_append]
      split_ifs
      · exact (walk_skips a).trans (Nat.le_add_right _ _)
      · exact (walkArms_skips x as (j + 1)).trans (Nat.le_add_left _ _)
end

end Skips

section Total

variable {P : Core.Program} {fs ω : String → ℕ} {rd : Reader}

mutual
/-- **The cost counting words bounds the words.** -/
theorem total_le_cost (hs : SkipLe P fs ω) :
    ∀ (t : Tree) {args rets : List E}, t.Valid P rd args rets → t.BufsOk P → t.total fs ≤ t.cost P true ω
  | .node f σ bufs kids, args, rets, hv, hb => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      simp only [Tree.BufsOk] at hb
      obtain ⟨hbufs, hbk⟩ := hb
      have he : (Tree.node f σ bufs kids).events P = es := by
        simp only [Tree.events, Tree.name, Tree.val, hf, hw]
      have hsk := walk_skips (σ := σ) (fs := fs) fn.body
      rw [hw] at hsk
      simp only [Out.skipW, Out.evs] at hsk
      have hl := hs f fn hf
      have hkk := totalKids_le_cost hs kids hk hbk
      rw [he] at hbufs
      rw [Tree.total, Tree.cost, he, hbufs]
      simp only [↓reduceIte]
      omega
  | .phantom .., _, _, hv, _ => hv.elim

theorem totalKids_le_cost (hs : SkipLe P fs ω) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValid P rd σ cs ks →
      Tree.BufsOkKids P ks → Tree.totalKids fs ks ≤ Tree.costKids P true ω ks + skipWords fs cs
  | [], _, [], _, _ => by simp only [Tree.totalKids, Tree.costKids, skipWords]; omega
  | [], _, _ :: _, hv, _ => hv.elim
  | _ :: _, _, [], hv, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hb => by
      obtain ⟨hn, hk, hv'⟩ := hv
      simp only [Tree.BufsOkKids] at hb
      have ih := totalKids_le_cost hs ks hv' hb.2
      rw [Tree.totalKids, Tree.costKids, skipWords]
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk ⊢
        have := total_le_cost hs k hk hb.1
        omega
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk ⊢
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        simp only [Tree.name] at hn
        rw [Tree.total, Tree.cost, hn]
        omega
end

variable {cert : String → Cert}

/-- **A certificate checked counting words bounds the words**, under its preconditions. -/
theorem total_le_of_stat (hchk : Checked P true cert ω) (hs : SkipLe P fs ω) {f : String}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : cert f = .stat pre b ks)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.Valid P rd args rets)
    (hb : t.BufsOk P) (hpre : ArgsPre pre args) : t.total fs ≤ b.eval args :=
  (total_le_cost hs t hv hb).trans (cost_le_of_stat hchk hcf hn hv hpre)

/-- **A loop checked counting words**: from `g^a` to `g^e`, `e - a` times its iteration's
bound. -/
theorem total_le_of_loop (hchk : Checked P true cert ω) (hs : SkipLe P fs ω) {f : String}
    {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .loop endc pre b ks) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid P rd args rets) (hb : t.BufsOk P) {a e : ℕ} (ha : args.getD 0 0 = ofK (gpow a))
    (he : endOf endc args = ofK (gpow e)) (hae : a < e) (heo : e < 2 ^ 64 - 1)
    (hpre : ArgsPre pre args) : t.total fs ≤ (e - a) * b.eval args :=
  (total_le_cost hs t hv hb).trans (cost_le_of_loop hchk hcf hn hv ha he hae heo hpre)

/-- **A constant certificate checked counting words** is a `TotalLe`. -/
theorem totalLe_of_stat (hchk : Checked P true cert ω) (hs : SkipLe P fs ω) {f : String} {B : ℕ}
    {ks : List (V × ℕ)} (hcf : cert f = .stat [] ⟨B, []⟩ ks) : TotalLe P fs f fun _ => B :=
  fun _ _ _ _ hn hv hb => by
    have := total_le_of_stat hchk hs hcf hn hv hb (fun _ h => (List.not_mem_nil h).elim)
    simpa [Aff.eval] using this

end Total

end
end LeanVM.Guest.Memory
