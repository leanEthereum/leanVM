/-
  LeanVM.Guest.B1.Main.MainHeap

  The advised sizes `main`'s tree pops: its own, its claim lists' digests', `da_verify`'s and each
  child's `verify_sub` call's, from its callees' trees' predicates and validity.
-/

module

public import LeanVM.Guest.B1.Main.MainPopsKids
public import LeanVM.Guest.B1.Main.L5Pops
public import LeanVM.Guest.B1.Main.MainHonestBudget
public import LeanVM.Guest.B1.Main.MainNoAdv

/-!
# The advised sizes of `main`'s tree

* `HeapsOf rd σ cs Ts hs`: each entered call's valid tree satisfying its predicate pops the advised sizes `hs`
  names, a skipped call's none; `heapPopsKids_of_heapsOf`: then the callees pop `hs`, in order.
* `clHonest_heap`, `dvNH_heap`: a claim list's digest and `da_verify` of honest shape pop their own advised sizes
  alone, their callees none.
* `l5From_heap`: the children loop's iterations pop each child's `verify_sub` call's advised sizes, in order, given
  those of its trees.
* `main_tree_heap`: a valid node of `main` whose callees' trees satisfy `mTs m p` pops its own advised sizes, then
  its claim lists' digests', `da_verify`'s and the children loop's.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest (valid_holds genMulOk genMul_sound isAddAt add_sound atomsIn atoms_of_flat
  holdsList_flat)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The callees' advised sizes -/

/-- **A call's advised sizes**: its valid tree satisfying `T`, when entered, pops `h`; `h` is `[]` when skipped. -/
def HeapOk (rd : Reader) (σ : Val) (c : Call) (T : Tree → Prop) (h : List (List E)) : Prop :=
  (c.taken = true → ∀ t : Tree, t.name = c.f → t.Valid coreProgram rd (c.args.map σ) (c.rets.map σ) → T t →
    t.heapPops heapSlots = h) ∧ (c.taken = false → h = [])

/-- **Each call's advised sizes** (`HeapOk`). -/
def HeapsOf (rd : Reader) (σ : Val) : List Call → List (Tree → Prop) → List (List (List E)) → Prop
  | c :: cs, T :: Ts, h :: hs => HeapOk rd σ c T h ∧ HeapsOf rd σ cs Ts hs
  | [], [], [] => True
  | _, _, _ => False

theorem HeapsOf.append : ∀ {cs Ts hs cs' Ts' hs'}, HeapsOf rd σ cs Ts hs → HeapsOf rd σ cs' Ts' hs' →
    HeapsOf rd σ (cs ++ cs') (Ts ++ Ts') (hs ++ hs')
  | [], [], [], _, _, _, _, h => h
  | _ :: _, _ :: _, _ :: _, _, _, _, ⟨h, hs⟩, h' => ⟨h, hs.append h'⟩
  | [], _ :: _, _, _, _, _, h, _ | [], [], _ :: _, _, _, _, h, _ | _ :: _, [], _, _, _, _, h, _
  | _ :: _, _ :: _, [], _, _, _, h, _ => h.elim

/-- **The callees pop their advised sizes**, in order. -/
theorem heapPopsKids_of_heapsOf : ∀ {cs : List Call} {Ts : List (Tree → Prop)} {hs : List (List (List E))}
    {ks : List Tree}, Tree.KidsValid coreProgram rd σ cs ks → KidsT cs Ts ks → HeapsOf rd σ cs Ts hs →
    Tree.heapPopsKids heapSlots ks = hs.flatten
  | [], [], [], [], _, _, _ => by rw [Tree.heapPopsKids]; rfl
  | c :: cs, T :: Ts, h :: hs, k :: ks, ⟨hn, hc, hv⟩, hT, ⟨⟨h1, h2⟩, ho⟩ => by
      rw [heapPopsKids_cons, heapPopsKids_of_heapsOf hv hT.2 ho, List.flatten_cons]
      congr 1
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact h1 ht k hn hc (hT.1 ht)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        rw [h2 (by simpa using ht), Tree.heapPops]
  | [], _, _, _ :: _, h, _, _ | _ :: _, _, _, [], h, _, _ => h.elim
  | [], _ :: _, _, [], _, _, h | [], [], _ :: _, [], _, _, h | _ :: _, [], _, _ :: _, _, _, h
  | _ :: _, _ :: _, [], _ :: _, _, _, h => h.elim

theorem heapOk_noAdv {c : Call} {T : Tree → Prop} (hg : NoAdvG c.f) : HeapOk rd σ c T [] :=
  ⟨fun _ _ hn hv _ => heapPops_noAdv (hn ▸ hg) hv, fun _ => rfl⟩

theorem heapOk_true {c : Call} {T : Tree → Prop} {h : List (List E)} (hc : c.taken = true)
    (H : ∀ t args rets, t.Valid coreProgram rd args rets → T t → t.heapPops heapSlots = h) : HeapOk rd σ c T h :=
  ⟨fun _ t _ hv hT => H t _ _ hv hT, fun h' => by rw [hc] at h'; cases h'⟩

/-! ## Claim lists' digests and `da_verify` -/

/-- **A claim list's digest of honest shape pops its chain buffer's size**, if any. -/
theorem clHonest_heap {n : ℕ} {t : Tree} {args rets : List E} (hv : t.Valid coreProgram rd args rets)
    (h : clHonest n t) : t.heapPops heapSlots = [advEntry (B1.Digest.clBufs n σ) 0] := by
  obtain ⟨σ', ks, rfl, -⟩ := h
  rw [heapPops_own cld_noAdvBut cld_name hv]
  rfl

/-- **`da_verify` of honest shape pops its advised buffer's size.** -/
theorem dvNH_heap {r L : ℕ} {t : Tree} {args rets : List E} (hv : t.Valid coreProgram rd args rets)
    (h : Da.dvNH r L t) : t.heapPops heapSlots = [advEntry (Da.dvSizes r L) 0] := by
  obtain ⟨σ', ks, rfl, -⟩ := h
  rw [heapPops_own dv_noAdvBut dv_name hv]
  rfl

/-! ## The children loop -/

/-- **The children loop's iterations pop each child's `verify_sub` call's advised sizes**, in order. -/
theorem l5From_heap {ex es : ℕ → ℕ} {Pxs Pss Pvs : ℕ → Tree → Prop} {vsH : ℕ → List (List E)}
    (hpv : ∀ c t, Pvs c t → t.heapPops heapSlots = vsH c) {nk : ℕ} {rest : List E} (hnk34 : nk < 2 ^ 34)
    (hnk : rest.getD 0 0 = gen ^ nk) :
    ∀ m c (t : Tree) (rets : List E), c + m = nk → t.Valid coreProgram rd (gen ^ c :: rest) rets →
      L5From ex es Pxs Pss Pvs m c t → t.heapPops heapSlots = (List.range' c m).flatMap vsH := by
  intro m
  induction m with
  | zero => intro _ _ _ _ _ h; exact h.elim
  | succ m ih =>
  intro c t rets hcm hv hL
  obtain ⟨σ, bufs, ks, rfl, -, -, hcl, hK⟩ := hL
  obtain ⟨fn0, hf0, hp0, hb⟩ := valid_holds hv
  rw [find_l5] at hf0
  obtain rfl := Option.some.inj hf0
  obtain ⟨fn', hf', -, es', vs, hw, -, -, hkv⟩ := hv
  rw [find_l5] at hf'
  obtain rfl := Option.some.inj hf'
  have hw' : walk σ (coreProgram.getD idx% «main_loop4» default).body = .ret (l5Evs σ) [] := by
    rw [l5_body, ← l5Body, l5Body_split]
    exact Main.walk_straight σ [] (l5Pre ++ [l5Tail]) l5Pre_straight
  rw [hw'] at hw
  cases hw
  rw [hcl] at hkv
  have hpar : ((List.range 16).map V.n).map σ = gen ^ c :: rest := by rw [← l5_params]; exact hp0
  have pr : ∀ i (hi : i < 16), σ (.n i) = (gen ^ c :: rest).getD i 0 := by
    intro i hi
    rw [← hpar, List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  have hrest : ((List.range 16).map V.n).tail.map σ = rest := by
    have := congrArg List.tail hpar
    rwa [← List.map_tail] at this
  have h0 : σ (.n 0) = gen ^ c := pr 0 (by omega)
  have h1 : σ (.n 1) = gen ^ nk := (pr 1 (by omega)).trans hnk
  rw [l5_body, holdsList_append] at hb
  obtain ⟨hflat, -, -, hg55, hg52, ha53⟩ := l5_chk
  obtain ⟨hall, -⟩ := holdsList_flat _ hflat _ _ hb
  have hat := atoms_of_flat hall
  have h55 : σ (.n 55) = gen ^ (c + 1) := by rw [genMul_sound hg55 hat, h0, pow_succ]
  have h53 : σ (.n 53) = gen ^ (c + 1) + gen ^ nk := by
    rw [add_sound ha53 hat, genMul_sound hg52 hat, h0, h1, pow_succ]
  obtain ⟨kx, ks', kst, kv, kt, rfl⟩ : ∃ kx ks' kst kv kt, ks = [kx, ks', kst, kv, kt] := by
    have := kidsValid_len hkv
    simp only [l5CallList, List.length_cons, List.length_nil] at this
    match ks, this with
    | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
  obtain ⟨hn1, hv1, hn2, hv2, hn3, hv3, -, -, -, hvt, -⟩ := hkv
  obtain ⟨-, -, -, hTv, hTt, -⟩ := hK
  have e1 := heapPops_kid_noAdv (c := ⟨"child_claim_list_digest", _, _, true⟩) hn1 cc_noAdv hv1
  have e2 := heapPops_kid_noAdv (c := ⟨"child_claim_list_digest", _, _, true⟩) hn2 cc_noAdv hv2
  have e3 := heapPops_kid_noAdv (c := ⟨"statement_digest", _, _, true⟩) hn3 statement_digest_noAdv hv3
  have e4 := hpv c kv (hTv rfl)
  have e5 : kt.heapPops heapSlots = (List.range' (c + 1) m).flatMap vsH := by
    by_cases h0' : σ (.n 53) = 0
    · have hcm' : c + 1 = nk := by
        rw [h53] at h0'
        exact Digest.gen_pow_inj' (by omega) hnk34 (e_add_eq_zero_iff.mp h0')
      rw [show m = 0 by omega, List.range'_zero, List.flatMap_nil]
      have : (decide (σ (.n 53) ≠ 0)) = false := by simpa using h0'
      simp only [this, Bool.false_eq_true, ↓reduceIte] at hvt
      obtain ⟨⟨g, σ', rfl⟩, -⟩ := hvt
      rw [Tree.heapPops]
    · have ht : (decide (σ (.n 53) ≠ 0)) = true := by simpa using h0'
      simp only [ht, ↓reduceIte] at hvt
      rw [l5_tail_args, h55, hrest] at hvt
      exact ih (c + 1) kt [] (by omega) hvt (hTt ht)
  rw [heapPops_node, heapPopsKids_cons, heapPopsKids_cons, heapPopsKids_cons, heapPopsKids_cons, heapPopsKids_cons,
    Tree.heapPopsKids, e1, e2, e3, e4, e5, List.range'_succ, List.flatMap_cons,
    show heapSlots name% «main_loop4» = [] by decide]
  simp

/-! ## `main` -/

/-- `main`'s callees' advised sizes, a loop not entered popping none. -/
def mainKidHeaps (m : MainIn) (Hx Hs Hd H5 : List (List E)) : List (List (List E)) :=
  [[], Hx, Hs, [], [], [], []] ++ (if m.nd = 1 then [Hd] else []) ++ [if m.nc = 0 then [] else H5] ++
    (if m.nc = 0 then [] else [[]]) ++ [[]]

theorem mCall5_args (σ : Val) :
    ([V.n 402, .n 6, .n 398, .n 31, .n 45, .n 22, .n 34, .n 46, .n 23, .n 395, .n 364, .n 26, .n 27, .n 383, .n 28,
      .n 389] : List V).map σ =
      σ (.n 402) :: ([V.n 6, .n 398, .n 31, .n 45, .n 22, .n 34, .n 46, .n 23, .n 395, .n 364, .n 26, .n 27, .n 383,
        .n 28, .n 389] : List V).map σ := rfl

/-- **`main`'s calls pop their advised sizes**, at a valuation with `main`'s honest values. -/
theorem main_heapsOf {m : MainIn} (hb : MainBounds (2 ^ 23) m) (hv : MVals rd σ m) (p : MainPreds)
    {Hx Hs Hd H5 : List (List E)}
    (hx : ∀ t args rets, t.Valid coreProgram rd args rets → p.Px t → t.heapPops heapSlots = Hx)
    (hs : ∀ t args rets, t.Valid coreProgram rd args rets → p.Ps t → t.heapPops heapSlots = Hs)
    (hd : m.nd = 1 → ∀ t args rets, t.Valid coreProgram rd args rets → p.Pd t → t.heapPops heapSlots = Hd)
    (h5 : ∀ t rest rets, rest.getD 0 0 = gen ^ m.nc → t.Valid coreProgram rd (gen ^ 0 :: rest) rets → p.T5 t →
      t.heapPops heapSlots = H5) :
    HeapsOf rd σ (mCalls σ m) ((fun _ => True) :: mTs m p) (mainKidHeaps m Hx Hs Hd H5) := by
  have := hb.nc
  have e5 := taken_eq (a := m.nc) (by omega) hv.g434
  unfold mCalls mTs mainKidHeaps
  refine ⟨heapOk_noAdv exponent_tables_noAdv, ?_⟩
  refine HeapsOf.append (HeapsOf.append (HeapsOf.append (HeapsOf.append ?_ ?_) ?_) ?_) ?_
  · exact ⟨heapOk_true rfl hx, heapOk_true rfl hs, heapOk_noAdv main_loop0_noAdv, heapOk_noAdv main_loop1_noAdv,
      heapOk_noAdv main_loop2_noAdv, heapOk_noAdv main_loop3_noAdv, trivial⟩
  · split
    · next h1 => exact ⟨heapOk_true rfl (hd h1), trivial⟩
    · trivial
  · refine ⟨⟨fun ht t _ htv hT => ?_, fun ht => ?_⟩, trivial⟩
    · have hnc : m.nc ≠ 0 := by
        have := e5 ▸ ht
        simpa using this
      rw [ite_eq_right hnc]
      have e0 : σ (.n 402) = gen ^ 0 := by rw [hv.g435, pow_zero]
      rw [mCall5_args, e0] at htv
      refine h5 t (([V.n 6, .n 398, .n 31, .n 45, .n 22, .n 34, .n 46, .n 23, .n 395, .n 364, .n 26, .n 27, .n 383,
        .n 28, .n 389] : List V).map σ) [] ?_ htv hT
      have h6 := hv.orc 6 (by simp)
      simp only [List.map_cons, List.getD_cons_zero]
      rw [h6]
      rfl
    · have : m.nc = 0 := by
        have := e5 ▸ ht
        simpa using this
      rw [ite_eq_left this]
  · split
    · trivial
    · exact ⟨heapOk_noAdv aggregate_claims_noAdv, trivial⟩
  · exact ⟨heapOk_noAdv statement_digest_noAdv, trivial⟩

/-- **A valid node of `main` pops its own advised sizes, then its callees'**: its claim lists' digests' `Hx`, `Hs`,
`da_verify`'s `Hd` when it checks a matrix, the children loop's `H5` when it has children. -/
theorem main_tree_heap {m : MainIn} (hb : MainBounds (2 ^ 23) m) {bufs : List ℕ} {ks : List Tree}
    (hval : (Memory.Tree.node "main" σ bufs ks).Valid coreProgram rd [] []) (hv : MVals rd σ m) (p : MainPreds)
    (hT : KidsT (mCalls σ m) ((fun _ => True) :: mTs m p) ks) (hc : calls (mEvs σ) = mCalls σ m)
    {Hx Hs Hd H5 : List (List E)}
    (hx : ∀ t args rets, t.Valid coreProgram rd args rets → p.Px t → t.heapPops heapSlots = Hx)
    (hs : ∀ t args rets, t.Valid coreProgram rd args rets → p.Ps t → t.heapPops heapSlots = Hs)
    (hd : m.nd = 1 → ∀ t args rets, t.Valid coreProgram rd args rets → p.Pd t → t.heapPops heapSlots = Hd)
    (h5 : ∀ t rest rets, rest.getD 0 0 = gen ^ m.nc → t.Valid coreProgram rd (gen ^ 0 :: rest) rets → p.T5 t →
      t.heapPops heapSlots = H5) :
    (Memory.Tree.node "main" σ bufs ks).heapPops heapSlots = (heapSlots "main").map (advEntry bufs) ++ Hx ++ Hs ++
      (if m.nd = 1 then Hd else []) ++ (if m.nc = 0 then [] else H5) := by
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hval
  rw [find_main] at hf
  cases hf
  rw [walk_main σ] at hw
  cases hw
  rw [hc] at hkv
  rw [heapPops_node, heapPopsKids_of_heapsOf hkv hT (main_heapsOf hb hv p hx hs hd h5), mainKidHeaps]
  split <;> split <;> simp

end

end LeanVM.Guest.B1.Main
