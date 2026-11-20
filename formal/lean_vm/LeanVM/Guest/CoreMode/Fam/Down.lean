/-
  LeanVM.Guest.CoreMode.Fam.Down

  Facts carried down a valid tree, from each caller to its callees: an induction over the placed
  instances, the call sites of a body, and the atoms every returning path passes.
-/

module

public import LeanVM.Guest.CoreMode.Fam.SelDefs
public import LeanVM.Guest.Memory.SizeTotal

/-!
# Facts carried down a valid tree

`insts_down`: a property `Q` of the instances of a valid tree holds of all of them once it holds
of the root's and passes from each node to each of its callees (`KidStep`): the callee `J` at the
node's call `i` (`J.t` its `i`-th kid, `J.fp` its `i`-th callee frame, `J.hdr = H I i`), of the
call's callee, valid on the call's argument words when entered and a phantom when not.

`sitesB p body`: every call statement of a body (nested in branches and arms) satisfies `p` of its
callee, arguments and returns, so every call of a path does (`walk_sites`). `scanAt p body`: a
top-level atom satisfying `p` before any statement that can return, so on every returning path
(`scanAt_sound`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Call sites -/

/-- Every call site of a statement satisfies `p` (callee, arguments, returns), by the recursor
(which the kernel reduces faster than structural recursion). -/
noncomputable def sitesS (p : String → List V → List V → Bool) (s : Stmt) : Bool :=
  Stmt.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba) (fun f args rets => p f args rets)
    (fun _ f args => p f args []) (fun _ fs args rets => fs.all fun f => p f args rets) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) s

/-- Every call site of a block satisfies `p`. -/
noncomputable def sitesB (p : String → List V → List V → Bool) (ss : List Stmt) : Bool :=
  Stmt.rec_1 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba) (fun f args rets => p f args rets)
    (fun _ f args => p f args []) (fun _ fs args rets => fs.all fun f => p f args rets) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) ss

/-- Every call site of a list of arms satisfies `p`. -/
noncomputable def sitesA (p : String → List V → List V → Bool) (as : List (List Stmt)) : Bool :=
  Stmt.rec_2 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba) (fun f args rets => p f args rets)
    (fun _ f args => p f args []) (fun _ fs args rets => fs.all fun f => p f args rets) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) as

section

variable {σ : Val} {p : String → List V → List V → Bool}

theorem pick_sites {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ),
    gs.all (fun f => p f args rets) = true → ∀ c ∈ calls (pick σ x args rets j gs).evs, p c.f c.args c.rets = true
  | [], _, _, c, h => by simp [pick, Out.evs, calls] at h
  | g :: gs, j, hg, c, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hg
    unfold pick at h
    split_ifs at h
    · simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil, List.mem_cons,
        List.not_mem_nil, or_false] at h
      subst h; exact hg.1
    · exact pick_sites gs (j + 1) hg.2 c h

mutual
/-- **A statement's path calls only at its sites.** -/
theorem walk1_sites : ∀ (s : Stmt), sitesS p s = true → ∀ c ∈ calls (walk1 σ s).evs,
    p c.f c.args c.rets = true
  | .atom a, _, c, h => by simp [walk1, Out.evs, calls, Ev.call?] at h
  | .ite b z m, hs, c, h => by
    rw [walk1, Out.calls_pre_inK] at h
    replace hs : (sitesB p z && sitesB p m) = true := hs
    simp only [Bool.and_eq_true] at hs
    split_ifs at h
    · exact walk_sites z hs.1 c h
    · exact walk_sites m hs.2 c h
  | .match_ x arms, hs, c, h => by
    rw [walk1] at h
    exact walkArms_sites x arms 0 (show sitesA p arms = true from hs) c h
  | .call f args rets, hs, c, h => by
    simp only [walk1, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
      List.mem_cons, List.not_mem_nil, or_false] at h
    subst h; exact (show p f args rets = true from hs)
  | .callIf b f args, hs, c, h => by
    replace hs : p f args [] = true := hs
    rw [walk1] at h
    split_ifs at h <;>
      simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h <;>
      subst h <;> exact hs
  | .dispatch x gs args rets, hs, c, h => by
    rw [walk1] at h
    exact pick_sites gs 0 (show gs.all (fun f => p f args rets) = true from hs) c h
  | .ret _, _, c, h => by simp [walk1, Out.evs, calls] at h

/-- **A block's path calls only at its sites.** -/
theorem walk_sites : ∀ (ss : List Stmt), sitesB p ss = true → ∀ c ∈ calls (walk σ ss).evs,
    p c.f c.args c.rets = true
  | [], _, c, h => by simp [walk, Out.evs, calls] at h
  | s :: ss, hs, c, h => by
    rw [walk] at h
    replace hs : (sitesS p s && sitesB p ss) = true := hs
    simp only [Bool.and_eq_true] at hs
    rcases Out.calls_seq h with h | h
    · exact walk1_sites s hs.1 c h
    · exact walk_sites ss hs.2 c h

theorem walkArms_sites (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), sitesA p arms = true →
    ∀ c ∈ calls (walkArms σ x j arms).evs, p c.f c.args c.rets = true
  | [], _, _, c, h => by simp [walkArms, Out.evs, calls] at h
  | a :: as, j, hs, c, h => by
    unfold walkArms at h
    replace hs : (sitesB p a && sitesA p as) = true := hs
    simp only [Bool.and_eq_true] at hs
    split_ifs at h
    · exact walk_sites a hs.1 c h
    · exact walkArms_sites x as (j + 1) hs.2 c h
end

/-- The calls of a returning path satisfy `p`, every site of the body doing so. -/
theorem calls_sites {body : List Stmt} {es : List Ev} {vs : List V} (hs : sitesB p body = true)
    (hw : walk σ body = .ret es vs) : ∀ c ∈ calls es, p c.f c.args c.rets = true := by
  intro c hc
  exact walk_sites body hs c (by rw [hw]; exact hc)

end

/-! ## Top-level atoms -/

/-- **A top-level atom satisfying `p`**, every statement before it free of `ret`. -/
def scanAt (p : Atom → Bool) : List Stmt → Bool
  | [] => false
  | s :: ss => (match s with | .atom a => p a | _ => false) || (Memory.Stmt.noRet s && scanAt p ss)

/-- **A returning path passes a scanned atom.** -/
theorem scanAt_sound {σ : Val} {p : Atom → Bool} :
    ∀ {ss : List Stmt} {es : List Ev} {vs : List V}, scanAt p ss = true → walk σ ss = .ret es vs →
      ∃ a, p a = true ∧ Ev.atom a ∈ es
  | [], _, _, h, _ => by simp [scanAt] at h
  | s :: ss, es, vs, h, hw => by
    simp only [scanAt, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hn, h⟩
    · cases s with
      | atom a =>
        rw [walk] at hw
        simp only [walk1, Out.seq] at hw
        cases h2 : walk σ ss with
        | fall _ => rw [h2] at hw; simp [Out.pre] at hw
        | ret es2 vs2 =>
          rw [h2] at hw
          simp only [Out.pre, Out.ret.injEq] at hw
          exact ⟨a, h, by rw [← hw.1]; exact List.mem_cons_self⟩
        | stuck => rw [h2] at hw; simp [Out.pre] at hw
      | _ => simp at h
    · obtain ⟨es1, es2, -, h2, rfl⟩ := walk_cons_noRet hn hw
      obtain ⟨a, ha, he⟩ := scanAt_sound h h2
      exact ⟨a, ha, List.mem_append_right _ he⟩

/-! ## Down a valid tree -/

section

variable {P : Core.Program} {rd : Reader} {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E}

/-- An entered callee of a valid node's path is valid on its call's words. -/
theorem kidsValid_at {σ : Val} : ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ cs ks →
    ∀ {i : ℕ} {c : Call} {k : Tree}, cs[i]? = some c → ks[i]? = some k →
      k.name = c.f ∧ (c.taken = true → k.Valid P rd (c.args.map σ) (c.rets.map σ)) ∧
        (c.taken = false → ∃ f σ', k = .phantom f σ')
  | [], _, _, _, _, _, hc, _ => by simp at hc
  | _ :: _, [], h, _, _, _, _, _ => h.elim
  | c' :: cs, k' :: ks, h, 0, c, k, hc, hk => by
    obtain rfl := Option.some.inj hc
    obtain rfl := Option.some.inj hk
    obtain ⟨hn, hv, -⟩ := h
    refine ⟨hn, fun ht ↦ by rw [ite_eq_left ht] at hv; exact hv, fun ht ↦ ?_⟩
    rw [ht] at hv
    exact hv.1
  | c' :: cs, k' :: ks, h, i + 1, c, k, hc, hk => kidsValid_at h.2.2 (by simpa using hc) (by simpa using hk)

/-- A kid's instances are among its siblings'. -/
theorem insts_sub_instsKids (I : Inst) : ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (j i : ℕ) {k : Tree}
    {p : ℕ × ℕ}, ks[i]? = some k → ps[i]? = some p → ∀ J ∈ k.insts fs lp H p (H I (j + i)),
      J ∈ Tree.instsKids fs lp H I j ps ks
  | [], _, _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h, _, _ => by simp at h
  | k' :: ks, p' :: ps, j, 0, k, p, h, h', J, hJ => by
    obtain rfl := Option.some.inj h
    obtain rfl := Option.some.inj h'
    rw [instsKids_cons]
    exact List.mem_append_left _ (by simpa using hJ)
  | k' :: ks, p' :: ps, j, i + 1, k, p, h, h', J, hJ => by
    rw [instsKids_cons]
    exact List.mem_append_right _ (insts_sub_instsKids I ks ps (j + 1) i (by simpa using h)
      (by simpa using h') J (by rw [show j + 1 + i = j + (i + 1) by omega]; exact hJ))

/-- **A step down a valid tree**: `Q` passes from each node of `S` to each of its callees in `S`,
at its call, valid on the call's words when entered. -/
def KidStep (P : Core.Program) (rd : Reader) (H : Inst → ℕ → E × E) (S : List Inst) (Q : Inst → Prop) : Prop :=
  ∀ I ∈ S, ∀ f σ bufs kids, I.t = .node f σ bufs kids → ∀ fn, P.find? f = some fn → ∀ es vs,
    walk σ fn.body = .ret es vs → (∀ e ∈ es, e.Holds rd σ) → ∀ (i : ℕ) (c : Call) (J : Inst), (calls es)[i]? = some c →
    J ∈ S → kids[i]? = some J.t → I.kidFps[i]? = some J.fp → J.hdr = H I i → J.t.name = c.f →
    (c.taken = true → J.t.Valid P rd (c.args.map σ) (c.rets.map σ)) →
    (c.taken = false → ∃ g σ', J.t = .phantom g σ') → Q I → Q J

mutual
/-- **Down a valid tree**: `Q` of the root's instance and of each callee of an instance having it
gives `Q` of every instance. -/
theorem insts_down {S : List Inst} {Q : Inst → Prop} (hs : KidStep P rd H S Q) :
    ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E) {args rets : List E}, t.Valid P rd args rets →
      (∀ J ∈ t.insts fs lp H p hdr, J ∈ S) → (∀ J rest, t.insts fs lp H p hdr = J :: rest → Q J) →
      ∀ J ∈ t.insts fs lp H p hdr, Q J
  | .node f σ bufs kids, p, hdr, args, rets, hv, hS, h0, J, hJ => by
    rw [insts_node] at hS h0 hJ
    set ps := kidPos fs lp p f bufs (kids.map (Tree.sz fs lp)) with hps
    set I : Inst := ⟨.node f σ bufs kids, p.1, p.2, hdr, ps.map Prod.fst, bases p.2 bufs⟩ with hI
    have hQI : Q I := h0 _ _ rfl
    rcases List.mem_cons.mp hJ with rfl | hJ
    · exact hQI
    have hv' := hv
    obtain ⟨fn, hf, -, es, vs, hw, -, hh, hk⟩ := hv'
    refine instsKids_down hs I σ kids (calls es) 0 ps hk (fun J' hJ' ↦ hS J' (List.mem_cons_of_mem _ hJ'))
      (fun i k q c hk' hq hc J0 rest hJ0 ↦ ?_) J hJ
    obtain ⟨J1, rest1, he, ht, hfp, -, hh0⟩ := head_insts (fs := fs) (lp := lp) (H := H) k q (H I (0 + i))
    rw [he] at hJ0
    obtain ⟨rfl, -⟩ := List.cons.inj hJ0
    have hmem : J1 ∈ S := hS J1 (List.mem_cons_of_mem _
      (insts_sub_instsKids I kids ps 0 i hk' hq J1 (by rw [he]; exact List.mem_cons_self)))
    obtain ⟨hnm, hval, hph⟩ := kidsValid_at hk hc hk'
    refine hs I (hS I List.mem_cons_self) f σ bufs kids rfl fn hf es vs hw hh i c J1 hc hmem
      (by rw [ht]; exact hk') (by simp only [hI, List.getElem?_map, hq, hfp]; rfl)
      (by rw [hh0, Nat.zero_add]) (by rw [ht]; exact hnm) (fun ht' ↦ by rw [ht]; exact hval ht')
      (fun ht' ↦ by rw [ht]; exact hph ht') hQI
  | .phantom .., _, _, _, _, hv, _, _, _, _ => hv.elim

/-- `insts_down` for the callees of `I` from its `j`-th. -/
theorem instsKids_down {S : List Inst} {Q : Inst → Prop} (hs : KidStep P rd H S Q) (I : Inst) (σ : Val) :
    ∀ (ks : List Tree) (cs : List Call) (j : ℕ) (ps : List (ℕ × ℕ)), Tree.KidsValid P rd σ cs ks →
      (∀ J ∈ Tree.instsKids fs lp H I j ps ks, J ∈ S) →
      (∀ (i : ℕ) (k : Tree) (q : ℕ × ℕ) (c : Call), ks[i]? = some k → ps[i]? = some q → cs[i]? = some c →
        ∀ J rest, k.insts fs lp H q (H I (j + i)) = J :: rest → Q J) →
      ∀ J ∈ Tree.instsKids fs lp H I j ps ks, Q J
  | [], _, _, _, _, _, _, J, hJ => by rw [instsKids_nil] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, _, _, [], _, _, _, J, hJ => by rw [instsKids_nil_left] at hJ; exact absurd hJ List.not_mem_nil
  | _ :: _, [], _, _ :: _, hk, _, _, _, _ => hk.elim
  | k :: ks, c :: cs, j, q :: ps, hk, hS, h0, J, hJ => by
    rw [instsKids_cons] at hS hJ
    rcases List.mem_append.mp hJ with hJ | hJ
    · have hk0 := kidsValid_at (P := P) (rd := rd) hk (i := 0) rfl rfl
      have hh0 : ∀ J rest, k.insts fs lp H q (H I j) = J :: rest → Q J := fun J rest h ↦
        h0 0 k q c rfl rfl rfl J rest (by rw [Nat.add_zero]; exact h)
      cases ht : c.taken
      · obtain ⟨f', σ', rfl⟩ := hk0.2.2 ht
        rw [insts_phantom, List.mem_singleton] at hJ
        subst hJ
        exact hh0 _ _ insts_phantom
      · exact insts_down hs k q (H I j) (hk0.2.1 ht) (fun J' h ↦ hS J' (List.mem_append_left _ h)) hh0 J hJ
    · exact instsKids_down hs I σ ks cs (j + 1) ps hk.2.2 (fun J' h ↦ hS J' (List.mem_append_right _ h))
        (fun i k' q' c' h1 h2 h3 J' rest h ↦ h0 (i + 1) k' q' c' (by simpa using h1) (by simpa using h2)
          (by simpa using h3) J' rest (by rw [show j + (i + 1) = j + 1 + i by omega]; exact h)) J hJ
end

end

end

end LeanVM.Guest.Res
