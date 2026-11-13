/-
  LeanVM.Guest.B1.Main.MainPopsKids

  `main`'s callees' entries from their trees' predicates and validity: an entered call's tree pops what its predicate says, a call not taken is a phantom popping `[]`.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestBR
public import LeanVM.Guest.B1.Main.MainPops
public import LeanVM.Guest.B1.Main.MainNoWit

/-!
# `main`'s callees' entries

* `PopsOf rd σ cs Ts pss`: each entered call's valid tree satisfying its predicate pops its entries, a skipped call's are `[]`; `popsKids_of_popsOf`: then the callees pop `pss`.
* `mainKidPopsR m q rd`: `mainKidPops` at `q`'s entries, a loop not entered popping `[]`, `exponent_tables` and `statement_digest` `[]` (no witness hint); `main_popsOf`: `main`'s calls at a valuation with its honest values pop them.
* `main_tree_popsR`: a valid node of `main` whose callees' trees satisfy `mTsR m (p.withPops q)` pops `mainOwnPops` at them.
* `mTsR_imp`, `kidsT_imp`: the predicates `p.withPops q` imply `p`'s.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **A call's entries**: its valid tree satisfying `T`, when entered, pops `p`; `p` is `[]` when skipped. -/
def PopOk (rd : Reader) (σ : Val) (c : Call) (T : Tree → Prop) (p : List Pop) : Prop :=
  (c.taken = true → ∀ t : Tree, t.name = c.f → t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ) → T t →
    t.pops coreProgram rd = p) ∧ (c.taken = false → p = [])

/-- **Each call's entries** (`PopOk`). -/
def PopsOf (rd : Reader) (σ : Val) : List Call → List (Tree → Prop) → List (List Pop) → Prop
  | c :: cs, T :: Ts, p :: pss => PopOk rd σ c T p ∧ PopsOf rd σ cs Ts pss
  | [], [], [] => True
  | _, _, _ => False

variable {rd : Reader} {σ : Val}

theorem PopsOf.append : ∀ {cs Ts pss cs' Ts' pss'}, PopsOf rd σ cs Ts pss → PopsOf rd σ cs' Ts' pss' →
    PopsOf rd σ (cs ++ cs') (Ts ++ Ts') (pss ++ pss')
  | [], [], [], _, _, _, _, h => h
  | _ :: _, _ :: _, _ :: _, _, _, _, ⟨h, hs⟩, h' => ⟨h, hs.append h'⟩
  | [], _ :: _, _, _, _, _, h, _ | [], [], _ :: _, _, _, _, h, _ | _ :: _, [], _, _, _, _, h, _
  | _ :: _, _ :: _, [], _, _, _, h, _ => h.elim

/-- **The callees pop their entries.** -/
theorem popsKids_of_popsOf : ∀ {cs : List Call} {Ts : List (Tree → Prop)} {pss : List (List Pop)} {ks : List Tree},
    Tree.KidsValid coreProgram rd σ cs ks → KidsT cs Ts ks → PopsOf rd σ cs Ts pss →
    Tree.popsKids coreProgram rd ks = pss
  | [], [], [], [], _, _, _ => by rw [Tree.popsKids]
  | c :: cs, T :: Ts, p :: pss, k :: ks, ⟨hn, hc, hv⟩, hT, ⟨⟨h1, h2⟩, ho⟩ => by
      rw [Tree.popsKids, popsKids_of_popsOf hv hT.2 ho]
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        rw [h1 ht k hn hc (hT.1 ht)]
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        rw [h2 (by simpa using ht), Tree.pops]
  | [], _, _, _ :: _, h, _, _ | _ :: _, _, _, [], h, _, _ => h.elim
  | [], _ :: _, _, [], _, _, h | [], [], _ :: _, [], _, _, h | _ :: _, [], _, _ :: _, _, _, h
  | _ :: _, _ :: _, [], _ :: _, _, _, h => h.elim

/-- `main`'s callees' entries at `q`'s, a loop not entered popping `[]`. -/
def mainKidPopsR (m : MainIn) (q : MainPops) (rd : Reader) : List (List Pop) :=
  mainKidPops m [] (q.px rd) (q.ps rd) (if m.nxd = 0 then [] else q.p0 rd) (if m.nsd = 0 then [] else q.p1 rd)
    (if m.nrx = 0 then [] else q.p2 rd) (if m.nrs = 0 then [] else q.p3 rd) (q.pd rd)
    (if m.nc = 0 then [] else q.p5 rd) (q.pa rd) []

theorem popOk_true {c : Call} {T : Tree → Prop} {p : List Pop} (hc : c.taken = true)
    (h : ∀ t : Tree, T t → t.pops coreProgram rd = p) : PopOk rd σ c T p :=
  ⟨fun _ t _ _ hT => h t hT, fun h' => by rw [hc] at h'; cases h'⟩

theorem popOk_noWit {c : Call} {T : Tree → Prop} (hg : NoWitG c.f) : PopOk rd σ c T [] :=
  ⟨fun _ _ hn hv _ => pops_nil_of_noWitness hg hv hn rd, fun _ => rfl⟩

/-- A loop entered when its count is not zero. -/
theorem popOk_loop {c : Call} {n : ℕ} {T : Tree → Prop} {p : List Pop} (hc : c.taken = decide (n ≠ 0))
    (h : ∀ t : Tree, T t → t.pops coreProgram rd = p) : PopOk rd σ c T (if n = 0 then [] else p) := by
  refine ⟨fun ht t _ _ hT => ?_, fun ht => ?_⟩
  · rw [hc, decide_eq_true_iff] at ht
    rw [ite_eq_right ht, h t hT]
  · rw [hc, decide_eq_false_iff_not, not_not] at ht
    rw [ite_eq_left ht]

/-- **`main`'s calls pop their entries**, at a valuation with `main`'s honest values. -/
theorem main_popsOf {m : MainIn} (hb : MainBounds (2 ^ 23) m) (hv : MVals rd σ m) (p : MainPreds) (q : MainPops) :
    PopsOf rd σ (mCalls σ m) ((fun _ => True) :: mTsR m (p.withPops q) rd) (mainKidPopsR m q rd) := by
  have := hb.xd
  have := hb.sd
  have := hb.rx
  have := hb.rs
  have := hb.nc
  have e0 := taken_eq (a := m.nxd) (by omega) hv.g61
  have e1 := taken_eq (a := m.nsd) (by omega) hv.g64
  have e2 := taken_eq (a := m.nrx) (by omega) hv.g377
  have e3 := taken_eq (a := m.nrs) (by omega) hv.g380
  have e5 := taken_eq (a := m.nc) (by omega) hv.g434
  unfold mCalls mTsR mainKidPopsR mainKidPops
  refine ⟨popOk_noWit exponent_tables_noWit, ?_⟩
  refine PopsOf.append (PopsOf.append (PopsOf.append (PopsOf.append ?_ ?_) ?_) ?_) ?_
  · exact ⟨popOk_true rfl fun _ h => h.2, popOk_true rfl fun _ h => h.2, popOk_loop e0 fun _ h => h, popOk_loop e1 fun _ h => h,
      popOk_loop e2 fun _ h => h, popOk_loop e3 fun _ h => h, trivial⟩
  · split
    · exact ⟨popOk_true rfl fun _ h => h.2, trivial⟩
    · trivial
  · exact ⟨popOk_loop e5 fun _ h => h.2, trivial⟩
  · split
    · trivial
    · exact ⟨popOk_true rfl fun _ h => h.2, trivial⟩
  · exact ⟨popOk_noWit statement_digest_noWit, trivial⟩

/-- **A valid node of `main` pops its entries**, its callees' trees satisfying `p.withPops q`. -/
theorem main_tree_popsR {m : MainIn} (hb : MainBounds (2 ^ 23) m) {bufs : List ℕ} {ks : List Tree}
    (hval : (Memory.Tree.node "main" σ bufs ks).Valid coreProgram rd [] []) (hv : MVals rd σ m) (p : MainPreds)
    (q : MainPops) (hT : KidsT (mCalls σ m) ((fun _ => True) :: mTsR m (p.withPops q) rd) ks)
    (hc : calls (mEvs σ) = mCalls σ m) :
    (Memory.Tree.node "main" σ bufs ks).pops coreProgram rd =
      mainOwnPops m [] (q.px rd) (q.ps rd) (if m.nxd = 0 then [] else q.p0 rd) (if m.nsd = 0 then [] else q.p1 rd)
        (if m.nrx = 0 then [] else q.p2 rd) (if m.nrs = 0 then [] else q.p3 rd) (q.pd rd)
        (if m.nc = 0 then [] else q.p5 rd) (q.pa rd) [] := by
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hval
  rw [find_main] at hf
  cases hf
  rw [walk_main σ] at hw
  cases hw
  rw [hc] at hkv
  exact main_pops hb.nd hb.nc hv (popsKids_of_popsOf hkv hT (main_popsOf hb hv p q))

/-! ## Forgetting the pops -/

theorem kidsT_imp : ∀ {cs : List Call} {Ts Ts' : List (Tree → Prop)} {ks : List Tree},
    KidsT cs Ts ks → List.Forall₂ (fun T T' => ∀ t, T t → T' t) Ts Ts' → KidsT cs Ts' ks
  | _ :: _, _ :: _, _ :: _, _ :: _, ⟨h, hs⟩, .cons hT hTs => ⟨fun ht => hT _ (h ht), kidsT_imp hs hTs⟩
  | _ :: _, _ :: _, _ :: _, [], _, _ => trivial
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], [], _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _, h => nomatch h
  | _ :: _, [], _ :: _, _, _, h => nomatch h

theorem forall₂_append {α β : Type} {R : α → β → Prop} : ∀ {a c : List α} {b d : List β},
    List.Forall₂ R a b → List.Forall₂ R c d → List.Forall₂ R (a ++ c) (b ++ d)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, .cons h hs, h' => .cons h (forall₂_append hs h')

/-- **`p.withPops q`'s predicates imply `p`'s**, on every memory. -/
theorem mTsR_imp (m : MainIn) (p : MainPreds) (q : MainPops) (rd : Reader) :
    List.Forall₂ (fun T T' => ∀ t, T t → T' t) ((fun _ => True) :: mTsR m (p.withPops q) rd)
      ((fun _ => True) :: mTs m p) := by
  refine .cons (fun _ h => h) ?_
  unfold mTsR mTs
  refine forall₂_append (forall₂_append (forall₂_append (forall₂_append ?_ ?_) ?_) ?_) ?_
  · exact .cons (fun _ h => h.1) (.cons (fun _ h => h.1) (.cons (fun _ _ => trivial) (.cons (fun _ _ => trivial)
      (.cons (fun _ _ => trivial) (.cons (fun _ _ => trivial) .nil)))))
  · split
    · exact .cons (fun _ h => h.1) .nil
    · exact .nil
  · exact .cons (fun _ h => h.1) .nil
  · split
    · exact .nil
    · exact .cons (fun _ h => h.1) .nil
  · exact .cons (fun _ _ => trivial) .nil

end
end LeanVM.Guest.B1.Main
