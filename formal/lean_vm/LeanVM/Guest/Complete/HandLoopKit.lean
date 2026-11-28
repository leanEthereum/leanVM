/-
  LeanVM.Guest.Complete.HandLoopKit

  Tools for the children's loop's hand facts: a stream's entries through the splice of a node's
  pops, pops bounded node by node, and a loop run with an invariant on the trees.
-/

module

public import LeanVM.Guest.Complete.HandShape
public import LeanVM.Guest.Budget.HandPops

/-!
# Tools for the loop

* `splice_append`, `mem_splice`, `streamOf_splice_own`: a node's pops (`splice`) of a path in two
  parts, an entry's source, and a stream's entries when no callee pops it.
* `pops_of_every`: a valid tree whose every node pops only entries in `S` itself (`OwnPops`) pops
  only entries in `S`.
* `loopRun_of_validT`: `loopRun_of_valid` with an invariant `J` on the iteration trees, which each
  iteration passes to its tail and which gives its callees' facts.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Budget
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## Splices -/

section Splice

variable {rd : Reader} {σ : Val}

theorem splice_append : ∀ (es es' : List Ev) (ks : List (List Pop)),
    splice rd σ (es ++ es') ks =
      splice rd σ es (ks.take (calls es).length) ++ splice rd σ es' (ks.drop (calls es).length)
  | [], es', ks => by simp [splice, calls]
  | .atom a :: es, es', ks => by
      have hc : calls (.atom a :: es) = calls es := rfl
      rw [List.cons_append, splice, splice, hc, splice_append es es' ks, List.append_assoc]
  | .inK x :: es, es', ks => by
      have hc : calls (.inK x :: es) = calls es := rfl
      rw [List.cons_append, splice, splice, hc, splice_append es es' ks]
  | .call f a r :: es, es', ks => by
      have hc : calls (.call f a r :: es) = ⟨f, a, r, true⟩ :: calls es := rfl
      rw [List.cons_append, splice, splice, hc, List.length_cons, splice_append es es' ks.tail]
      cases ks <;> simp [List.append_assoc]
  | .skip f a :: es, es', ks => by
      have hc : calls (.skip f a :: es) = ⟨f, a, [], false⟩ :: calls es := rfl
      rw [List.cons_append, splice, splice, hc, List.length_cons, splice_append es es' ks.tail]
      cases ks <;> simp [List.append_assoc]

/-- **An entry a node pops is its own or a callee's.** -/
theorem mem_splice : ∀ {es : List Ev} {ks : List (List Pop)} {p : Pop},
    p ∈ splice rd σ es ks → p ∈ evPops rd σ es ∨ ∃ k ∈ ks, p ∈ k
  | [], _, _, h => by simp [splice] at h
  | .atom a :: es, ks, p, h => by
      rw [splice, List.mem_append] at h
      rw [evPops_cons]
      rcases h with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · rcases mem_splice h with h | h
        · exact Or.inl (List.mem_append_right _ h)
        · exact Or.inr h
  | .inK _ :: es, ks, p, h => by
      rw [splice] at h
      rw [evPops_cons]
      rcases mem_splice h with h | h
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr h
  | .call .. :: es, ks, p, h => by
      rw [splice, List.mem_append] at h
      rw [evPops_cons]
      rcases h with h | h
      · cases ks with
        | nil => simp at h
        | cons k ks => exact Or.inr ⟨k, List.mem_cons_self, by simpa using h⟩
      · rcases mem_splice h with h | ⟨k, hk, hp⟩
        · exact Or.inl (List.mem_append_right _ h)
        · cases ks with
          | nil => simp at hk
          | cons k' ks => exact Or.inr ⟨k, List.mem_cons_of_mem _ (by simpa using hk), hp⟩
  | .skip .. :: es, ks, p, h => by
      rw [splice, List.mem_append] at h
      rw [evPops_cons]
      rcases h with h | h
      · cases ks with
        | nil => simp at h
        | cons k ks => exact Or.inr ⟨k, List.mem_cons_self, by simpa using h⟩
      · rcases mem_splice h with h | ⟨k, hk, hp⟩
        · exact Or.inl (List.mem_append_right _ h)
        · cases ks with
          | nil => simp at hk
          | cons k' ks => exact Or.inr ⟨k, List.mem_cons_of_mem _ (by simpa using hk), hp⟩

/-- A stream's entries, in order. -/
def streamOf (s : String) (ps : List Pop) : List Pop := ps.filter (·.1 == s)

theorem streamOf_append (s : String) (a b : List Pop) : streamOf s (a ++ b) = streamOf s a ++ streamOf s b :=
  List.filter_append a b

theorem streamOf_eq_nil {s : String} {l : List Pop} : streamOf s l = [] ↔ ∀ p ∈ l, p.1 ≠ s := by
  simp [streamOf, List.filter_eq_nil_iff]

/-- **A stream no callee pops is the node's own.** -/
theorem streamOf_splice_own (s : String) : ∀ (es : List Ev) (ks : List (List Pop)),
    (∀ k ∈ ks, streamOf s k = []) → streamOf s (splice rd σ es ks) = streamOf s (evPops rd σ es)
  | [], _, _ => by simp [splice, evPops, streamOf]
  | .atom a :: es, ks, h => by
      rw [splice, evPops_cons, streamOf_append, streamOf_append, streamOf_splice_own s es ks h]; rfl
  | .inK _ :: es, ks, h => by
      rw [splice, evPops_cons, streamOf_append, streamOf_splice_own s es ks h]; rfl
  | .call .. :: es, ks, h => by
      rw [splice, evPops_cons, streamOf_append, streamOf_append,
        streamOf_splice_own s es ks.tail fun k hk => h k (List.mem_of_mem_tail hk)]
      cases ks with
      | nil => rfl
      | cons k ks => rw [List.headD_cons, h k List.mem_cons_self]; rfl
  | .skip .. :: es, ks, h => by
      rw [splice, evPops_cons, streamOf_append, streamOf_append,
        streamOf_splice_own s es ks.tail fun k hk => h k (List.mem_of_mem_tail hk)]
      cases ks with
      | nil => rfl
      | cons k ks => rw [List.headD_cons, h k List.mem_cons_self]; rfl

end Splice

/-! ## Pops bounded node by node -/

section Pops

variable {P : Core.Program} {rd : Reader}

/-- The entries a node of `f` at `σ` pops itself are in `S`. -/
def OwnPops (P : Core.Program) (rd : Reader) (S : Pop → Prop) (f : String) (σ : Val) : Prop :=
  ∀ fn, P.find? f = some fn → ∀ es vs, walk σ fn.body = .ret es vs → ∀ p ∈ evPops rd σ es, S p

theorem popsKids_append : ∀ (a b : List Memory.Tree), Memory.Tree.popsKids P rd (a ++ b) = Memory.Tree.popsKids P rd a ++ Memory.Tree.popsKids P rd b
  | [], b => by rw [List.nil_append, Memory.Tree.popsKids, List.nil_append]
  | k :: a, b => by rw [List.cons_append, Memory.Tree.popsKids, Memory.Tree.popsKids, popsKids_append a b, List.cons_append]

mutual
/-- **A valid tree whose nodes pop only entries in `S` pops only entries in `S`.** -/
theorem pops_of_every {S : Pop → Prop} : ∀ (t : Memory.Tree) {args rets : List E}, t.Valid P rd args rets →
    t.Every (OwnPops P rd S) → ∀ p ∈ t.pops P rd, S p
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hE, p, hp => by
      rw [pops_node (rd := rd) (bufs := bufs) (kids := kids) hf hw] at hp
      rw [Memory.Tree.every_node] at hE
      rcases mem_splice hp with h | ⟨k, hk', hpk⟩
      · exact hE.1 fn hf es vs hw p h
      · exact popsKids_of_every σ kids (calls es) hk (Memory.Tree.everyKids_iff.mp hE.2) k hk' p hpk
  | .phantom .., _, _, h, _, _, _ => h.elim

/-- `pops_of_every` for the callees. -/
theorem popsKids_of_every {S : Pop → Prop} : ∀ (σ : Val) (ks : List Memory.Tree) (cs : List Call),
    Memory.Tree.KidsValid P rd σ cs ks → (∀ k ∈ ks, k.Every (OwnPops P rd S)) →
      ∀ k ∈ Memory.Tree.popsKids P rd ks, ∀ p ∈ k, S p
  | _, [], [], _, _, k, hk, _, _ => by rw [Memory.Tree.popsKids] at hk; simp at hk
  | σ, t :: ks, c :: cs, ⟨_, hc, hks⟩, hE, k, hk, p, hp => by
      rw [Memory.Tree.popsKids] at hk
      rcases List.mem_cons.mp hk with rfl | hk
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact pops_of_every t hc (hE t List.mem_cons_self) p hp
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          simp [Memory.Tree.pops] at hp
      · exact popsKids_of_every σ ks cs hks (fun t' ht' => hE t' (List.mem_cons_of_mem _ ht')) k hk p hp
  | _, _ :: _, [], h, _, _, _, _, _ => h.elim
end

end Pops

/-! ## A loop run with an invariant on the trees -/

variable {rd : Reader} {Q : String → Val → Prop}

/-- **A valid tree of the children's loop is a `LoopRun`** (`loopRun_of_valid`), with an invariant `J`
on the iteration trees beside `Inv` on their arguments: each iteration in `J` gives its callees' `Every Q`,
and passes `J` to its tail when that is valid. -/
theorem loopRun_of_validT {fn : Fn}
    (hf : coreProgram.find? "__loop4_main" = some fn) {pre : List Stmt} {c i' p0 : V} {prest : List V}
    (hps : fn.params = p0 :: prest)
    (hbody : fn.body = pre ++ [.callIf c "__loop4_main" (i' :: prest), .ret []])
    (hnr : Stmt.noRetListS pre = true)
    (h : Hand) (w : ℕ) (B : E → ℕ) (J : Memory.Tree → Prop) (Inv : List E → Prop)
    (hit : ∀ σ bufs ks1 tk es, J (.node "__loop4_main" σ bufs (ks1 ++ [tk])) → walk σ pre = .fall es →
      HoldsAll rd σ es → Memory.Tree.KidsValid coreProgram rd σ (calls es) ks1 → Inv (fn.params.map σ) →
      (∃ a r, (Memory.Tree.node "__loop4_main" σ bufs (ks1 ++ [tk])).Valid coreProgram rd a r) →
      (∀ k ∈ ks1, k.Every Q) ∧ ArgsPre h.pre ((fn.params ++ h.vps).map σ) ∧
        h.b.eval ((fn.params ++ h.vps).map σ) + (if σ c = 0 then w else B (σ i')) ≤ B (σ p0) ∧
        (σ c ≠ 0 → Inv ((i' :: prest).map σ)) ∧ ∀ a r, tk.Valid coreProgram rd a r → J tk) :
    ∀ n (t : Memory.Tree) {args rets : List E}, t.count ≤ n → t.Valid coreProgram rd args rets →
      t.name = "__loop4_main" → J t → Inv args → ∃ S, LoopRun "__loop4_main" fn.params h w (fun k => k.Every Q) t S ∧
        S ≤ B (args.headD 0)
  | _, .phantom .., _, _, _, hv, _, _, _ => hv.elim
  | 0, .node .., _, _, hn, _, _, _, _ => by rw [Memory.Tree.count] at hn; omega
  | n + 1, .node f σ bufs kids, args, rets, hcnt, hv, hname, hJ, hinv => by
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
          obtain ⟨hQk, hpre, hle, hnext, hJt⟩ := hit σ bufs ks1 tk es1 hJ hw1 hes1 hk1 (by rw [hp]; exact hinv)
            ⟨_, _, hv0⟩
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
            obtain ⟨S, hrun, hS'⟩ := loopRun_of_validT hf hps hbody hnr h w B J Inv hit n tk hc' htv htn
              (hJt _ _ htv) (hnext h0c)
            refine ⟨_, LoopRun.step hQk hpre hrun, ?_⟩
            rw [ite_eq_right h0c] at hle
            simp only [List.map_cons, List.headD_cons] at hS'
            rw [hargs]; omega
      · rw [hw1] at hw; simp [Out.seq] at hw

theorem loopRun_countT {fn : Fn}
    (hf : coreProgram.find? "__loop4_main" = some fn) {pre : List Stmt} (hsh : loopShape fn none = some pre)
    (J : Memory.Tree → Prop)
    (hkids : ∀ σ bufs ks1 tk es, J (.node "__loop4_main" σ bufs (ks1 ++ [tk])) → walk σ pre = .fall es →
      HoldsAll rd σ es → Memory.Tree.KidsValid coreProgram rd σ (calls es) ks1 →
      (∃ a r, (Memory.Tree.node "__loop4_main" σ bufs (ks1 ++ [tk])).Valid coreProgram rd a r) →
      (∀ k ∈ ks1, k.Every Q) ∧ ∀ a r, tk.Valid coreProgram rd a r → J tk)
    (h : Hand) (w n : ℕ) (hn : n < 2 ^ 64 - 1) (cost : ℕ → ℕ)
    (hcost : ∀ σ bufs kids, J (.node "__loop4_main" σ bufs kids) →
      (∃ a r, (Memory.Tree.node "__loop4_main" σ bufs kids).Valid coreProgram rd a r) → ∀ j < n,
      (fn.params.map σ).take 2 = [gen ^ j, gen ^ n] →
        ArgsPre h.pre ((fn.params ++ h.vps).map σ) ∧ h.b.eval ((fn.params ++ h.vps).map σ) ≤ cost j)
    (t : Memory.Tree) {args rets : List E} (hv : t.Valid coreProgram rd args rets) (hname : t.name = "__loop4_main")
    (hJ : J t) {j : ℕ} (hj : j < n) (hargs : args.take 2 = [gen ^ j, gen ^ n]) :
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
  have hit : ∀ σ bufs ks1 tk es, J (.node "__loop4_main" σ bufs (ks1 ++ [tk])) → walk σ pre = .fall es →
      HoldsAll rd σ es → Memory.Tree.KidsValid coreProgram rd σ (calls es) ks1 → Inv (fn.params.map σ) →
      (∃ a r, (Memory.Tree.node "__loop4_main" σ bufs (ks1 ++ [tk])).Valid coreProgram rd a r) →
      (∀ k ∈ ks1, k.Every Q) ∧ ArgsPre h.pre ((fn.params ++ h.vps).map σ) ∧
        h.b.eval ((fn.params ++ h.vps).map σ) + (if σ c = 0 then w else loopB n cost w (σ i')) ≤
          loopB n cost w (σ p0) ∧ (σ c ≠ 0 → Inv ((i' :: e :: rest).map σ)) ∧
          ∀ a r, tk.Valid coreProgram rd a r → J tk := by
    rintro σ bufs ks1 tk es1 hJn hw1 hes1 hk1 ⟨j, hj, ht⟩ hnode
    obtain ⟨hQk, hJt⟩ := hkids σ bufs ks1 tk es1 hJn hw1 hes1 hk1 hnode
    have ht' := ht
    rw [hps] at ht'
    simp only [List.map_cons, List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at ht'
    obtain ⟨hp0, hen⟩ := ht'
    obtain ⟨hpre, hb⟩ := hcost σ bufs _ hJn hnode j hj ht
    have hsv : σ s = gen ^ (j + 1) := by rw [isStep_val hnr hw1 hes1 hs, hp0, ← hg1, pow_succ]
    have hiv : σ i' = gen ^ (j + 1) := by rw [isStep_val hnr hw1 hes1 hst, hp0, ← hg1, pow_succ]
    have hcv : σ c = σ s + σ e := hse σ (defAtom_holds hnr hw1 hes1 hadd)
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    have hsum : ∑ m ∈ Finset.Ico j n, cost m = cost j + ∑ m ∈ Finset.Ico (j + 1) n, cost m :=
      Finset.sum_eq_sum_Ico_succ_bot hj cost
    have hB0 : loopB n cost w (σ p0) = cost j + (∑ m ∈ Finset.Ico (j + 1) n, cost m) + w := by
      rw [loopB, hp0, hlt j hj.le, hsum]
    refine ⟨hQk, hpre, ?_, fun h0 => ?_, hJt⟩
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
  obtain ⟨S, hrun, hS'⟩ := loopRun_of_validT hf hps hbody hnr h w (loopB n cost w) J Inv hit t.count t
    le_rfl hv hname hJ ⟨j, hj, hargs⟩
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
