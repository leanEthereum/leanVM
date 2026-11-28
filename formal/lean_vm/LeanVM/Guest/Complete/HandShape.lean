/-
  LeanVM.Guest.Complete.HandShape

  The shape of `main`'s hand facts, for any node predicate: its callees but the children's loop satisfy it at every
  node from their paths (`main_kids_every`), and the children's loop is a `LoopRun` (`loopRun_of_valid`).
-/

module

public import LeanVM.Guest.Memory.HandNode
public import LeanVM.Guest.Exact.Every
public import LeanVM.Guest.Memory.Family
public import LeanVM.Guest.Memory.Restrict
public import LeanVM.Guest.Memory.SelArm
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.Value.Bits

/-!
# The shape of `main`'s hand facts

No function but `main` calls `da_verify` or the children's loop `__loop4_main`, which only `main` and itself call,
and none calls `main` (`calleesOff_ok`, by the kernel). So the functions off `main`'s node (`OffNode`) are
call-closed, and a node predicate `Q` that each of their paths satisfies holds at every node of their trees
(`offNode_everyIn`, `every_of_everyIn`). For `main`'s tree that is every callee but the loop, `da_verify`'s own node
given (`main_kids_every`).

The loop (`loopRun_of_valid`): a valid tree of `__loop4_main` is a `LoopRun` of any hand `h` and tail frame `w`, its
iterations' callees satisfying `Every Q`, its sum within `B x` for its counter `x` when each iteration's inner bound
plus the next one's `B` (or `w` at the last) is within `B` of its own counter.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## The functions off `main`'s node -/

/-- The functions off `main`'s node: all but `main`, `da_verify` and the children's loop. -/
def OffNode (g : String) : Prop := g ≠ "main" ∧ g ≠ "da_verify" ∧ g ≠ "__loop4_main"

/-- Function `fn`'s callees: never `main`; `da_verify` and the children's loop only from `main`, the loop also from
itself. -/
def calleesOff (_ : ℕ) (fn : Fn) : Bool :=
  (Stmt.blockCallees fn.body).all fun g => decide (g ≠ "main") &&
    (decide (fn.name = "main") || (decide (g ≠ "da_verify") &&
      (decide (g ≠ "__loop4_main") || decide (fn.name = "__loop4_main"))))

theorem calleesOff_0 : RangeOk calleesOff 0 200 := by unfold RangeOk; decide +kernel
theorem calleesOff_200 : RangeOk calleesOff 200 200 := by unfold RangeOk; decide +kernel
theorem calleesOff_400 : RangeOk calleesOff 400 200 := by unfold RangeOk; decide +kernel
theorem calleesOff_600 : RangeOk calleesOff 600 200 := by unfold RangeOk; decide +kernel
theorem calleesOff_800 : RangeOk calleesOff 800 200 := by unfold RangeOk; decide +kernel
theorem calleesOff_1000 : RangeOk calleesOff 1000 200 := by unfold RangeOk; decide +kernel
theorem calleesOff_1200 : RangeOk calleesOff 1200 200 := by unfold RangeOk; decide +kernel
theorem calleesOff_1400 : RangeOk calleesOff 1400 169 := by unfold RangeOk; decide +kernel

/-- **No function calls `main`, and only `main` (and the loop itself) calls `da_verify` or the loop**, by the
kernel. -/
theorem calleesOff_ok : RangeOk calleesOff 0 coreProgram.length := by
  rw [coreProgram_length]
  have h := ((((((calleesOff_0.append calleesOff_200).append calleesOff_400).append calleesOff_600).append
    calleesOff_800).append calleesOff_1000).append calleesOff_1200).append calleesOff_1400
  exact h

theorem calleesOff_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) :
    ∀ g ∈ Stmt.blockCallees fn.body, g ≠ "main" ∧
      (f = "main" ∨ (g ≠ "da_verify" ∧ (g ≠ "__loop4_main" ∨ f = "__loop4_main"))) := by
  obtain ⟨j, hj, hjf⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some h)
  have hn : fn.name = f := fn_name_of_find (P := coreProgram) h
  have hc := RangeOk.all calleesOff_ok hj
  rw [hjf] at hc
  intro g hg
  have := List.all_eq_true.mp hc g hg
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
  rw [hn] at this
  exact this

/-- **The functions off `main`'s node are call-closed**: a node predicate their paths satisfy holds on them. -/
theorem offNode_everyIn {rd : Reader} {Q : String → Val → Prop}
    (hQ : ∀ f, OffNode f → ∀ fn, coreProgram.find? f = some fn → ∀ σ es vs, walk σ fn.body = .ret es vs →
      (∀ e ∈ es, e.Holds rd σ) → Q f σ) : coreProgram.EveryIn rd Q OffNode := by
  intro f hf fn hfn
  refine ⟨fun g hg => ?_, hQ f hf fn hfn⟩
  obtain ⟨h1, h2⟩ := calleesOff_of_find hfn g hg
  obtain ⟨hm, -, hl⟩ := hf
  rcases h2 with h2 | ⟨h3, h4⟩
  · exact absurd h2 hm
  · exact ⟨h1, h3, h4.resolve_right hl⟩

/-- A function other than `main` and the loop calls only functions off `main`'s node. -/
theorem callees_offNode {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) (hm : f ≠ "main")
    (hl : f ≠ "__loop4_main") : ∀ g ∈ Stmt.blockCallees fn.body, OffNode g := by
  intro g hg
  obtain ⟨h1, h2⟩ := calleesOff_of_find h g hg
  rcases h2 with h2 | ⟨h3, h4⟩
  · exact absurd h2 hm
  · exact ⟨h1, h3, h4.resolve_right hl⟩

/-! ## Callee trees -/

variable {rd : Reader} {Q : String → Val → Prop}

/-- A callee of a node, entered or not: a phantom, or a valid tree. -/
theorem kidsValid_mem {P : Core.Program} {σ : Val} : ∀ {cs : List Call} {ks : List Memory.Tree},
    Memory.Tree.KidsValid P rd σ cs ks → ∀ k ∈ ks, ∃ c ∈ cs, k.name = c.f ∧
      ((∃ f σ', k = .phantom f σ') ∨ ∃ a r, k.Valid P rd a r)
  | [], [], _, k, hk => (List.not_mem_nil hk).elim
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
  | c :: cs, k' :: ks, ⟨hn, hc, hks⟩, k, hk => by
      rcases List.mem_cons.mp hk with rfl | hk
      · refine ⟨c, List.mem_cons_self, hn, ?_⟩
        by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc; exact Or.inr ⟨_, _, hc⟩
        · rw [ite_eq_right ht] at hc; exact Or.inl hc.1
      · obtain ⟨c', hc', h⟩ := kidsValid_mem hks k hk
        exact ⟨c', List.mem_cons_of_mem _ hc', h⟩

/-- **A valid node whose callees are off `main`'s node**, its own predicate given, satisfies `Every Q`. -/
theorem every_node_of (hS : coreProgram.EveryIn rd Q OffNode) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Memory.Tree} {a r : List E} (hv : (Memory.Tree.node f σ bufs kids).Valid coreProgram rd a r)
    (hc : ∀ fn, coreProgram.find? f = some fn → ∀ g ∈ Stmt.blockCallees fn.body, OffNode g) (hq : Q f σ) :
    (Memory.Tree.node f σ bufs kids).Every Q := by
  obtain ⟨fn, hf, _, es, vs, hw, _, _, hk⟩ := hv
  rw [Memory.Tree.every_node]
  exact ⟨hq, everyKids_of_everyIn hS kids σ (calls es) hk fun c hc' =>
    hc fn hf c.f (walk_callees (σ := σ) fn.body (by rw [hw]; exact hc'))⟩

/-- A callee off `main`'s node, entered or not, satisfies `Every Q`. -/
theorem every_of_kid (hS : coreProgram.EveryIn rd Q OffNode) {k : Memory.Tree}
    (h : (∃ f σ', k = .phantom f σ') ∨ ∃ a r, k.Valid coreProgram rd a r) (hn : OffNode k.name) : k.Every Q := by
  rcases h with ⟨f, σ', rfl⟩ | ⟨a, r, hv⟩
  · exact Memory.Tree.every_phantom
  · exact every_of_everyIn hS k hv hn

/-- **`main`'s callees but the children's loop satisfy `Every Q`**, given `Q` at `da_verify`'s own node. -/
theorem main_kids_every (hS : coreProgram.EveryIn rd Q OffNode) {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree}
    {a r : List E} (hv : (Memory.Tree.node "main" σ bufs kids).Valid coreProgram rd a r)
    (hda : ∀ σd bufsd kd, Memory.Tree.node "da_verify" σd bufsd kd ∈ kids → Q "da_verify" σd) :
    ∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every Q := by
  obtain ⟨fn, hf, _, es, vs, hw, _, _, hk⟩ := hv
  intro k hkm
  obtain ⟨c, hc, hn, hpv⟩ := kidsValid_mem hk k hkm
  have hcb : c.f ∈ Stmt.blockCallees fn.body := walk_callees (σ := σ) fn.body (by rw [hw]; exact hc)
  obtain ⟨h1, h2⟩ := calleesOff_of_find hf c.f hcb
  by_cases hl : c.f = "__loop4_main"
  · exact Or.inl (hn.trans hl)
  right
  by_cases hd : c.f = "da_verify"
  · rcases hpv with ⟨f, σ', rfl⟩ | ⟨a', r', hv'⟩
    · exact Memory.Tree.every_phantom
    · cases k with
      | phantom => exact hv'.elim
      | node f σd bufsd kd =>
          have hfd : f = "da_verify" := hn.trans hd
          subst hfd
          exact every_node_of hS hv' (fun fn' hf' => callees_offNode hf' (by decide) (by decide))
            (hda σd bufsd kd hkm)
  · exact every_of_kid hS hpv (hn ▸ ⟨h1, hd, hl⟩)

/-! ## The children's loop -/

/-- The callees of a block calling only functions off `main`'s node satisfy `Every Q`. -/
theorem kids_every_of_offNode (hS : coreProgram.EveryIn rd Q OffNode) {pre : List Stmt}
    (hpc : ∀ g ∈ Stmt.blockCallees pre, OffNode g) :
    ∀ σ es ks, walk σ pre = .fall es → HoldsAll rd σ es →
      Memory.Tree.KidsValid coreProgram rd σ (calls es) ks → ∀ k ∈ ks, k.Every Q := by
  intro σ es ks hw _ hk k hkm
  obtain ⟨c', hc', hn', hpv⟩ := kidsValid_mem hk k hkm
  exact every_of_kid hS hpv (hn' ▸ hpc c'.f (walk_callees (σ := σ) pre (by rw [hw]; exact hc')))

/-- **A valid tree of the children's loop is a `LoopRun`** of the hand `h` and the tail frame `w`, within `B` of its
counter, when each iteration whose arguments satisfy the invariant `Inv` has its inner bound plus the next counter's
`B` (`w` at the last) within its own counter's `B`, and passes `Inv` on. The loop's body is `pre ++ [callIf c loop (i' :: prest), ret []]`, its parameters `p0 :: prest`. -/
theorem loopRun_of_valid {fn : Fn}
    (hf : coreProgram.find? "__loop4_main" = some fn) {pre : List Stmt} {c i' p0 : V} {prest : List V}
    (hps : fn.params = p0 :: prest)
    (hbody : fn.body = pre ++ [.callIf c "__loop4_main" (i' :: prest), .ret []])
    (hnr : Stmt.noRetListS pre = true)
    (hkids : ∀ σ es ks, walk σ pre = .fall es → HoldsAll rd σ es →
      Memory.Tree.KidsValid coreProgram rd σ (calls es) ks → ∀ k ∈ ks, k.Every Q)
    (h : Hand) (w : ℕ) (B : E → ℕ) (Inv : List E → Prop)
    (hit : ∀ σ es, walk σ pre = .fall es → HoldsAll rd σ es → Inv (fn.params.map σ) →
      (∃ bufs kids a r, (Memory.Tree.node "__loop4_main" σ bufs kids).Valid coreProgram rd a r) →
      ArgsPre h.pre ((fn.params ++ h.vps).map σ) ∧
        h.b.eval ((fn.params ++ h.vps).map σ) + (if σ c = 0 then w else B (σ i')) ≤ B (σ p0) ∧
        (σ c ≠ 0 → Inv ((i' :: prest).map σ))) :
    ∀ n (t : Memory.Tree) {args rets : List E}, t.count ≤ n → t.Valid coreProgram rd args rets →
      t.name = "__loop4_main" → Inv args → ∃ S, LoopRun "__loop4_main" fn.params h w (fun k => k.Every Q) t S ∧
        S ≤ B (args.headD 0)
  | _, .phantom .., _, _, _, hv, _, _ => hv.elim
  | 0, .node .., _, _, hn, _, _, _ => by rw [Memory.Tree.count] at hn; omega
  | n + 1, .node f σ bufs kids, args, rets, hcnt, hv, hname, hinv => by
      simp only [Memory.Tree.name] at hname
      subst hname
      have hv0 := hv
      obtain ⟨fn', hf', hp, es, vs, hw, -, hes, hk⟩ := hv
      rw [hf] at hf'
      cases hf'
      rw [hbody, walk_append] at hw
      rcases walk_noRet (σ := σ) pre hnr with ⟨es1, hw1⟩ | hw1
      · rw [hw1] at hw
        have hwt : walk σ [.callIf c "__loop4_main" (i' :: prest), .ret []] =
            .ret [.inK c, if σ c = 0 then .skip "__loop4_main" (i' :: prest)
              else .call "__loop4_main" (i' :: prest) []] [] := by
          simp [walk, walk1, Out.seq, Out.pre]
        rw [hwt] at hw
        simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        have hes1 : HoldsAll rd σ es1 := fun e he => hes e (List.mem_append_left _ he)
        rw [calls_append] at hk
        obtain ⟨ks1, ks2, hks12, hk1, hk2⟩ := kidsValid_splitA hk
        have hcalls : calls [Ev.inK c, if σ c = 0 then .skip "__loop4_main" (i' :: prest)
            else .call "__loop4_main" (i' :: prest) []] =
              [⟨"__loop4_main", i' :: prest, [], !decide (σ c = 0)⟩] := by
          by_cases h0c : σ c = 0 <;> simp only [h0c, ↓reduceIte, decide_true, decide_false,
            Bool.not_true, Bool.not_false] <;> rfl
        rw [hcalls] at hk2
        match ks2, hk2 with
        | [tk], ⟨htn, htv, _⟩ =>
          subst hks12
          obtain ⟨hpre, hle, hnext⟩ := hit σ es1 hw1 hes1 (by rw [hp]; exact hinv) ⟨_, _, _, _, hv0⟩
          have hQk : ∀ k ∈ ks1, k.Every Q := hkids σ es1 ks1 hw1 hes1 hk1
          have hargs : args.headD 0 = σ p0 := by rw [← hp, hps]; rfl
          by_cases h0c : σ c = 0
          · simp only [h0c, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htv
            obtain ⟨⟨g', σ', rfl⟩, -⟩ := htv
            simp only [Memory.Tree.name] at htn
            subst htn
            refine ⟨_, LoopRun.step hQk hpre (LoopRun.last σ'), ?_⟩
            rw [ite_eq_left h0c] at hle
            rw [hargs]; exact hle
          · simp only [h0c, decide_false, Bool.not_false, ↓reduceIte] at htv
            have hc' : tk.count ≤ n := by
              have := countKids_le (ks := ks1 ++ [tk]) (k := tk) (by simp)
              rw [Memory.Tree.count] at hcnt
              omega
            obtain ⟨S, hrun, hS'⟩ := loopRun_of_valid hf hps hbody hnr hkids h w B Inv hit n tk hc' htv htn (hnext h0c)
            refine ⟨_, LoopRun.step hQk hpre hrun, ?_⟩
            rw [ite_eq_right h0c] at hle
            simp only [List.map_cons, List.headD_cons] at hS'
            rw [hargs]; omega
      · rw [hw1] at hw; simp [Out.seq] at hw

/-- The children's loop's bound from counter `x = g^j` to the end `g^n`: the iterations `j ..< n` at `cost`, then the
tail frame `w`. -/
noncomputable def loopB (n : ℕ) (cost : ℕ → ℕ) (w : ℕ) (x : E) : ℕ := (∑ m ∈ Finset.Ico (logG x) n, cost m) + w

/-- **The children's loop as a counted `LoopRun`**: entered at counter `g^j`, `j < n`, with end `g^n`, its run
sums within the iterations `j ..< n`'s costs plus the tail frame, when each valid iteration node at counter `g^j`,
`j < n`, has its hand's preconditions and its inner bound within `cost j`. -/
theorem loopRun_count {fn : Fn}
    (hf : coreProgram.find? "__loop4_main" = some fn) {pre : List Stmt} (hsh : loopShape fn none = some pre)
    (hkids : ∀ σ es ks, walk σ pre = .fall es → HoldsAll rd σ es →
      Memory.Tree.KidsValid coreProgram rd σ (calls es) ks → ∀ k ∈ ks, k.Every Q)
    (h : Hand) (w n : ℕ) (hn : n < 2 ^ 64 - 1) (cost : ℕ → ℕ)
    (hcost : ∀ σ, (∃ bufs kids a r, (Memory.Tree.node "__loop4_main" σ bufs kids).Valid coreProgram rd a r) → ∀ j < n,
      (fn.params.map σ).take 2 = [gen ^ j, gen ^ n] →
        ArgsPre h.pre ((fn.params ++ h.vps).map σ) ∧ h.b.eval ((fn.params ++ h.vps).map σ) ≤ cost j)
    (t : Memory.Tree) {args rets : List E} (hv : t.Valid coreProgram rd args rets) (hname : t.name = "__loop4_main")
    {j : ℕ} (hj : j < n) (hargs : args.take 2 = [gen ^ j, gen ^ n]) :
    ∃ S, LoopRun "__loop4_main" fn.params h w (fun k => k.Every Q) t S ∧
      S ≤ (∑ m ∈ Finset.Ico j n, cost m) + w := by
  obtain ⟨c, i', p0, prest, hps, hbody, hnr, hst, x, y, hadd, hxy⟩ := loopShape_spec hsh
  rw [fn_name_of_find (P := coreProgram) hf] at hbody
  have hg1 : gen = ofK (addressOfIndex 1) := by rw [← LeanVM.Guest.Value.gen_pow_eq_ofK, pow_one]
  -- the step and end variables, `σ c = σ s + σ e`
  obtain ⟨s, e, hse, hs, he⟩ : ∃ s e, (∀ σ : Val, σ c = σ x + σ y → σ c = σ s + σ e) ∧ isStep pre p0 s = true ∧
      isEnd pre prest.head? none e = true := by
    rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨x, y, fun _ h => h, h1, h2⟩
    · exact ⟨y, x, fun σ h => by rw [h, add_comm], h1, h2⟩
  have hhe : prest.head? = some e := by unfold isEnd at he; simpa using he
  obtain ⟨rest, rfl⟩ : ∃ rest, prest = e :: rest := by
    cases prest with
    | nil => simp at hhe
    | cons e' rest => simp only [List.head?_cons, Option.some.injEq] at hhe; exact ⟨rest, by rw [hhe]⟩
  have hlt : ∀ m ≤ n, logG (gen ^ m) = m := fun m hm => logG_gen_pow (by omega)
  let Inv : List E → Prop := fun a => ∃ j < n, a.take 2 = [gen ^ j, gen ^ n]
  have hit : ∀ σ es, walk σ pre = .fall es → HoldsAll rd σ es → Inv (fn.params.map σ) →
      (∃ bufs kids a r, (Memory.Tree.node "__loop4_main" σ bufs kids).Valid coreProgram rd a r) → ArgsPre h.pre ((fn.params ++ h.vps).map σ) ∧
        h.b.eval ((fn.params ++ h.vps).map σ) + (if σ c = 0 then w else loopB n cost w (σ i')) ≤
          loopB n cost w (σ p0) ∧ (σ c ≠ 0 → Inv ((i' :: e :: rest).map σ)) := by
    rintro σ es1 hw1 hes1 ⟨j, hj, ht⟩ hnode
    have ht' := ht
    rw [hps] at ht'
    simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at ht'
    obtain ⟨hp0, hen⟩ := ht'
    obtain ⟨hpre, hb⟩ := hcost σ hnode j hj ht
    have hsv : σ s = gen ^ (j + 1) := by rw [isStep_val hnr hw1 hes1 hs, hp0, ← hg1, pow_succ]
    have hiv : σ i' = gen ^ (j + 1) := by rw [isStep_val hnr hw1 hes1 hst, hp0, ← hg1, pow_succ]
    have hcv : σ c = σ s + σ e := hse σ (defAtom_holds hnr hw1 hes1 hadd)
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    have hsum : ∑ m ∈ Finset.Ico j n, cost m = cost j + ∑ m ∈ Finset.Ico (j + 1) n, cost m :=
      Finset.sum_eq_sum_Ico_succ_bot hj cost
    have hB0 : loopB n cost w (σ p0) = cost j + (∑ m ∈ Finset.Ico (j + 1) n, cost m) + w := by
      rw [loopB, hp0, hlt j hj.le, hsum]
    refine ⟨hpre, ?_, fun h0 => ?_⟩
    · by_cases h0 : σ c = 0
      · rw [ite_eq_left h0, hB0]
        have hjn : j + 1 = n := by
          refine LeanVM.Guest.Value.gen_pow_inj (by omega) (by omega) ?_
          rw [← hsv, ← hen]
          linear_combination (hcv.symm.trans h0) - σ e * h2
        rw [hjn, Finset.Ico_self, Finset.sum_empty]
        omega
      · rw [ite_eq_right h0, hB0, loopB, hiv]
        have hjn : j + 1 < n := by
          rcases Nat.lt_or_ge (j + 1) n with h | h
          · exact h
          · exfalso
            have : j + 1 = n := by omega
            apply h0
            rw [hcv, hsv, hen, this]
            linear_combination gen ^ n * h2
        rw [hlt (j + 1) hjn.le]
        omega
    · have hjn : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exact h
        · exfalso
          have : j + 1 = n := by omega
          apply h0
          rw [hcv, hsv, hen, this]
          linear_combination gen ^ n * h2
      exact ⟨j + 1, hjn, by simp only [List.map_cons, List.take_succ_cons, List.take_zero, hiv, hen]⟩
  obtain ⟨S, hrun, hS'⟩ := loopRun_of_valid hf hps hbody hnr hkids h w (loopB n cost w) Inv hit t.count t
    le_rfl hv hname ⟨j, hj, hargs⟩
  refine ⟨S, hrun, ?_⟩
  have ha0 : args.headD 0 = gen ^ j := by
    match args, hargs with
    | a :: _ :: _, h => simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at h; exact h.1
    | [a], h => simp at h
    | [], h => simp at h
  rw [ha0, loopB, hlt j hj.le] at hS'
  exact hS'

end
end LeanVM.Guest.Complete
