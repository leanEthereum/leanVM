/-
  LeanVM.Guest.B1.Main.RelAtInE

  The placed relations by a tree whose pops are given and whose every node satisfies a predicate (`RelAtInPE`,
  `RelAtInCPE`, `KidsFromInPE`), their composition along a path (`relAtInPE_of_walk`, `relAtInPE_of_walk_loop`), and
  the same for any callees' predicates (`RelAtInT.every_of_walk`, `RelAtInCT.every_of_walk`).
-/

module

public import LeanVM.Guest.B1.Main.RelAtInP
public import LeanVM.Guest.Exact.Every

/-!
# Placed relations with their pops, every node satisfying `Q`

`RelAtInPE … Q … ps`, `RelAtInCPE … Q … ps`: `RelAtInP`, `RelAtInCP` by a tree also satisfying `Tree.Every Q`.
`KidsFromInPE`: `KidsFromInP`, each entered callee's tree satisfying `Every Q` too (a phantom does).

`relAtInPE_of_walk`, `relAtInPE_of_walk_loop`: `relAtInP_of_walk`, `relAtInP_of_walk_loop` with one more hypothesis,
the node's own `Q f σ` at the walk's valuation. `kidsT_every`: callees' trees satisfying `T ∧ Every Q` satisfy `T`, and
all of them, phantoms included, `Every Q`; `RelAtInT.every_of_walk`, `RelAtInCT.every_of_walk` turn `relAtInWT_of_walk`'s
and `relAtInWT_of_walk_loop`'s conclusions into a node satisfying `Every Q`. `RelAtInP.withEvery` adds `Every Q` to a
callee all of whose valid trees satisfy it.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`RelAtIn` by a tree popping `ps`, its every node satisfying `Q`.** -/
abbrev RelAtInPE (rd : Reader) (Q : String → Val → Prop) (R D : ℕ → Prop) (fp n : ℕ) (f : String)
    (args rets : List E) (ps : List Pop) : Prop :=
  RelAtInT P fs cert rd R D fp n f args rets fun t => t.pops P rd = ps ∧ t.Every Q

/-- **`RelAtInC` by a tree popping `ps`, its every node satisfying `Q`.** -/
abbrev RelAtInCPE (rd : Reader) (Q : String → Val → Prop) (R D : ℕ → Prop) (fp c B n : ℕ) (f : String)
    (args rets : List E) (ps : List Pop) : Prop :=
  RelAtInCT P fs cert rd R D fp c B n f args rets fun t => t.pops P rd = ps ∧ t.Every Q

/-- **`KidsFromInP`, each entered callee's tree satisfying `Every Q`.** -/
def KidsFromInPE (rd : Reader) (σ : Val) (Q : String → Val → Prop) (R : ℕ → Prop) :
    (ℕ → Prop) → List Call → List (List Pop) → ℕ → ℕ → (ℕ → Prop) → Prop
  | Dacc, [], [], _, n, Dend => n = 0 ∧ ∀ i, Dend i → Dacc i
  | Dacc, c :: cs, p :: pss, b, n, Dend => ∃ (m n' : ℕ) (Rk Dk : ℕ → Prop), n = m + n' ∧
      (∀ i, Rk i → R i ∨ Dacc i) ∧
      (if c.taken then RelAtInPE P fs cert rd Q Rk Dk b m c.f (c.args.map σ) (c.rets.map σ) p
        else m = fs c.f ∧ p = []) ∧
      KidsFromInPE rd σ Q R (fun i => Dacc i ∨ (c.taken = true ∧ Dk i)) cs pss (b + m) n' Dend
  | _, _, _, _, _, _ => False

variable {P fs cert} {rd : Reader} {σ : Val} {Q : String → Val → Prop}

/-! ## Forgetting -/

theorem RelAtInPE.toP {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E} {ps : List Pop}
    (h : RelAtInPE P fs cert rd Q R D fp n f args rets ps) : RelAtInP P fs cert rd R D fp n f args rets ps :=
  let ⟨t, ht, hp, _⟩ := h
  ⟨t, ht, hp⟩

theorem RelAtInCPE.toP {R D : ℕ → Prop} {fp c B n : ℕ} {f : String} {args rets : List E} {ps : List Pop}
    (h : RelAtInCPE P fs cert rd Q R D fp c B n f args rets ps) : RelAtInCP P fs cert rd R D fp c B n f args rets ps :=
  let ⟨t, ht, hp, _⟩ := h
  ⟨t, ht, hp⟩

/-- **A loop entered fresh**, with its pops and `Every Q`. -/
theorem RelAtInCPE.relAtInPE {R D : ℕ → Prop} {fp B n : ℕ} {f : String} {args rets : List E} {ps : List Pop}
    (h : RelAtInCPE P fs cert rd Q R D fp (fp + B) B n f args rets ps) :
    RelAtInPE P fs cert rd Q R D fp (B + n) f args rets ps :=
  RelAtInCT.relAtInT h

theorem KidsFromInPE.toP {R : ℕ → Prop} : ∀ {cs : List Call} {pss : List (List Pop)} {Dacc : ℕ → Prop} {b n : ℕ}
    {Dend : ℕ → Prop}, KidsFromInPE P fs cert rd σ Q R Dacc cs pss b n Dend →
    KidsFromInP P fs cert rd σ R Dacc cs pss b n Dend
  | [], [], _, _, _, _, h => h
  | c :: cs, p :: pss, _, _, _, _, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ => by
      refine ⟨m, n', Rk, Dk, hn, hR, ?_, hk.toP⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc ⊢; exact hc.toP
      · rw [ite_eq_right ht] at hc ⊢; exact hc
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h => h.elim

/-- `KidsFromInPE` is `KidsFromInT` by the trees popping the entries and satisfying `Every Q`, a skipped call's
entries `[]`. -/
theorem KidsFromInPE.toT {R : ℕ → Prop} : ∀ {cs : List Call} {pss : List (List Pop)} {Dacc : ℕ → Prop} {b n : ℕ}
    {Dend : ℕ → Prop}, KidsFromInPE P fs cert rd σ Q R Dacc cs pss b n Dend →
    KidsFromInT P fs cert rd σ R Dacc cs
      ((pss.map fun p t => t.pops P rd = p).map fun T t => T t ∧ t.Every Q) b n Dend ∧ KidsPopsOk cs pss
  | [], [], _, _, _, _, h => ⟨h, trivial⟩
  | c :: cs, p :: pss, _, _, _, _, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ => by
      obtain ⟨hk, ho⟩ := KidsFromInPE.toT hk
      refine ⟨⟨m, n', Rk, Dk, hn, hR, ?_, hk⟩, fun ht => ?_, ho⟩
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc ⊢; exact hc
        · rw [ite_eq_right ht] at hc ⊢; exact hc.1
      · rw [ht] at hc; exact hc.2
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h => h.elim

/-! ## Callees' trees -/

/-- **Callees' trees satisfying `T ∧ Every Q`** satisfy `T`, and every one, phantoms included, `Every Q`. -/
theorem kidsT_every : ∀ {cs : List Call} {Ts : List (Tree → Prop)} {ks : List Tree},
    Tree.KidsValid P rd σ cs ks → cs.length ≤ Ts.length →
    KidsT cs (Ts.map fun T t => T t ∧ t.Every Q) ks → KidsT cs Ts ks ∧ Tree.EveryKids Q ks
  | [], _, [], _, _, _ => ⟨by cases ‹List (Tree → Prop)› <;> trivial, by rw [Tree.EveryKids]; trivial⟩
  | c :: cs, T :: Ts, k :: ks, ⟨_, hc, hv⟩, hl, h => by
      rw [List.map_cons] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨hT, hE⟩ := kidsT_every hv (by simpa using hl) h2
      refine ⟨⟨fun ht => (h1 ht).1, hT⟩, ?_⟩
      rw [Tree.EveryKids]
      refine ⟨?_, hE⟩
      by_cases ht : c.taken = true
      · exact (h1 ht).2
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact Tree.every_phantom
  | _ :: _, [], _, _, hl, _ => absurd hl (by simp)
  | [], _, _ :: _, h, _, _ | _ :: _, _, [], h, _, _ => h.elim

/-- **`relAtInWT_of_walk`'s node satisfies `Every Q`**: its own `Q f σ`, its callees' trees `T ∧ Every Q`. -/
theorem RelAtInT.every_of_walk {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E} {fn : Fn}
    {es : List Ev} {vs : List V} {bufs : List ℕ} {Ts : List (Tree → Prop)} (hf : P.find? f = some fn)
    (hw : walk σ fn.body = .ret es vs) (hl : (calls es).length ≤ Ts.length) (hq : Q f σ)
    (h : RelAtInT P fs cert rd R D fp n f args rets fun t =>
      ∃ ks, t = .node f σ bufs ks ∧ KidsT (calls es) (Ts.map fun T t => T t ∧ t.Every Q) ks) :
    RelAtInT P fs cert rd R D fp n f args rets fun t =>
      (∃ ks, t = .node f σ bufs ks ∧ KidsT (calls es) Ts ks) ∧ t.Every Q := by
  obtain ⟨t, ht, ks, rfl, hT⟩ := h
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := ht.2.1
  rw [hf] at hf'; cases hf'
  rw [hw] at hw'; cases hw'
  obtain ⟨hT, hE⟩ := kidsT_every hkv hl hT
  exact ⟨_, ht, ⟨ks, rfl, hT⟩, Tree.every_node.mpr ⟨hq, hE⟩⟩

/-- **`relAtInWT_of_walk_loop`'s node satisfies `Every Q`**: its own `Q f σ`, its callees' trees `T ∧ Every Q`. -/
theorem RelAtInCT.every_of_walk {R D : ℕ → Prop} {fp c B n : ℕ} {f : String} {args rets : List E} {fn : Fn}
    {es : List Ev} {vs : List V} {bufs : List ℕ} {Ts : List (Tree → Prop)} (hf : P.find? f = some fn)
    (hw : walk σ fn.body = .ret es vs) (hl : (calls es).length ≤ Ts.length) (hq : Q f σ)
    (h : RelAtInCT P fs cert rd R D fp c B n f args rets fun t =>
      ∃ ks, t = .node f σ bufs ks ∧ KidsT (calls es) (Ts.map fun T t => T t ∧ t.Every Q) ks) :
    RelAtInCT P fs cert rd R D fp c B n f args rets fun t =>
      (∃ ks, t = .node f σ bufs ks ∧ KidsT (calls es) Ts ks) ∧ t.Every Q := by
  obtain ⟨t, ht, ks, rfl, hT⟩ := h
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := ht.2.1
  rw [hf] at hf'; cases hf'
  rw [hw] at hw'; cases hw'
  obtain ⟨hT, hE⟩ := kidsT_every hkv hl hT
  exact ⟨_, ht, ⟨ks, rfl, hT⟩, Tree.every_node.mpr ⟨hq, hE⟩⟩

/-! ## Free callees -/

/-- **A callee all of whose valid trees satisfy `Every Q`** gains it. -/
theorem RelAtInT.and_every {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E} {T : Tree → Prop}
    (h : RelAtInT P fs cert rd R D fp n f args rets T)
    (hQ : ∀ t : Tree, t.name = f → t.Valid P rd args rets → t.Every Q) :
    RelAtInT P fs cert rd R D fp n f args rets fun t => T t ∧ t.Every Q :=
  let ⟨t, ht, hT⟩ := h
  ⟨t, ht, hT, hQ t ht.1 ht.2.1⟩

theorem RelAtInCT.and_every {R D : ℕ → Prop} {fp c B n : ℕ} {f : String} {args rets : List E} {T : Tree → Prop}
    (h : RelAtInCT P fs cert rd R D fp c B n f args rets T)
    (hQ : ∀ t : Tree, t.name = f → t.Valid P rd args rets → t.Every Q) :
    RelAtInCT P fs cert rd R D fp c B n f args rets fun t => T t ∧ t.Every Q :=
  let ⟨t, ht, hT⟩ := h
  ⟨t, ht, hT, hQ t ht.1 ht.2.1⟩

theorem RelAtInP.withEvery {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E} {ps : List Pop}
    (h : RelAtInP P fs cert rd R D fp n f args rets ps)
    (hQ : ∀ t : Tree, t.name = f → t.Valid P rd args rets → t.Every Q) :
    RelAtInPE P fs cert rd Q R D fp n f args rets ps :=
  RelAtInT.and_every h hQ

theorem RelAtInCP.withEvery {R D : ℕ → Prop} {fp c B n : ℕ} {f : String} {args rets : List E} {ps : List Pop}
    (h : RelAtInCP P fs cert rd R D fp c B n f args rets ps)
    (hQ : ∀ t : Tree, t.name = f → t.Valid P rd args rets → t.Every Q) :
    RelAtInCPE P fs cert rd Q R D fp c B n f args rets ps :=
  RelAtInCT.and_every h hQ

/-! ## Composition -/

/-- **Composition with regions, pops and `Every Q`**: `relAtInP_of_walk`, the callees satisfying `Every Q` too, and
the node's own `Q f σ`. -/
theorem relAtInPE_of_walk (hP : P.Wf) {R D Dk : ℕ → Prop} {fp N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hl : P.loop f = false ∨ calls es = []) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b
        => ofK (addressOfIndex b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + cert f q.2)))
    {pss : List (List Pop)} {ps : List Pop}
    (hk : KidsFromInPE P fs cert rd σ Q (fun i => R i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
      (fun _ => False) (calls es) pss (fp + fs f + (allocs σ es).sum) N Dk)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ R i ∨ Dk i))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ Dk i)
    (hps : splice rd σ es pss = ps) (hq : Q f σ) :
    RelAtInPE P fs cert rd Q R D fp (fs f + (allocs σ es).sum + N) f args rets ps := by
  obtain ⟨hkT, ho⟩ := hk.toT
  obtain ⟨t, ht, ⟨ks, rfl, hT⟩, hE⟩ := RelAtInT.every_of_walk hf hw
    (by simp only [List.length_map]; exact ho.length.ge) hq
    (relAtInWT_of_walk hP hf hl hp hw hr hes hbuf haddr _ hkT hload hD)
  refine ⟨_, ht, ?_, hE⟩
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := ht.2.1
  rw [hf] at hf'; cases hf'
  rw [hw] at hw'; cases hw'
  rw [Tree.pops_node hf hw, popsKids_of_kidsT hkv hT ho, hps]

/-- **Composition with regions, pops and `Every Q`, a loop iteration**: `relAtInP_of_walk_loop`, the callees and the
tail call satisfying `Every Q` too, and the node's own `Q f σ`. -/
theorem relAtInPE_of_walk_loop (hP : P.Wf) {R D Dk Rt Dt : ℕ → Prop} {fp c Bt m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {ct : Call}
    {pss : List (List Pop)} {pt ps : List Pop}
    (hf : P.find? f = some fn) (hl : P.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hc : calls es = cs ++ [ct])
    (htail : if ct.taken then
        RelAtInCPE P fs cert rd Q Rt Dt (fp + fs f) (c + (allocs σ es).sum + N) Bt m ct.f
          (ct.args.map σ) (ct.rets.map σ) pt
      else Bt = fs ct.f ∧ m = 0 ∧ pt = [])
    (hbuf : (allocDsts es).map σ = (bases c (allocs σ es)).map fun b => ofK (addressOfIndex b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + cert f q.2)))
    (hk : KidsFromInPE P fs cert rd σ Q (fun i => R i ∨ ownData cert fp c f (allocs σ es) es i)
      (fun _ => False) cs pss (c + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp c f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (ct.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp c f (allocs σ es) es i ∨ Dk i ∨ (ct.taken = true ∧ Dt i))
    (hps : splice rd σ es (pss ++ [pt]) = ps) (hq : Q f σ) :
    RelAtInCPE P fs cert rd Q R D fp c (fs f + Bt) ((allocs σ es).sum + N + m) f args rets ps := by
  obtain ⟨hkT, ho⟩ := hk.toT
  have htail' : if ct.taken then
      RelAtInCT P fs cert rd Rt Dt (fp + fs f) (c + (allocs σ es).sum + N) Bt m ct.f (ct.args.map σ) (ct.rets.map σ)
        ((fun T t => T t ∧ t.Every Q) fun t => t.pops P rd = pt)
      else Bt = fs ct.f ∧ m = 0 := by
    by_cases ht : ct.taken = true
    · rw [ite_eq_left ht] at htail ⊢; exact htail
    · rw [ite_eq_right ht] at htail ⊢; exact ⟨htail.1, htail.2.1⟩
  have ho' : KidsPopsOk (cs ++ [ct]) (pss ++ [pt]) := ho.snoc fun ht => by
    rw [ht] at htail; exact htail.2.2
  have h := relAtInWT_of_walk_loop hP hf hl hp hw hr hes hc htail' hbuf haddr
    (by simp only [List.length_map]; exact ho.length) hkT hRt hload hD
  replace h : RelAtInCT P fs cert rd R D fp c (fs f + Bt) ((allocs σ es).sum + N + m) f args rets fun t =>
      ∃ ks, t = .node f σ (allocs σ es) ks ∧ KidsT (calls es)
        (((pss ++ [pt]).map fun p t => t.pops P rd = p).map fun T t => T t ∧ t.Every Q) ks := by
    simpa only [List.map_append, List.map_cons, List.map_nil] using h
  obtain ⟨t, ht, ⟨ks, rfl, hT⟩, hE⟩ := RelAtInCT.every_of_walk hf hw
    (by simp only [List.length_map]; rw [hc]; exact ho'.length.ge) hq h
  refine ⟨_, ht, ?_, hE⟩
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := ht.2.1
  rw [hf] at hf'; cases hf'
  rw [hw] at hw'; cases hw'
  rw [hc] at hT hkv
  rw [Tree.pops_node hf hw, popsKids_of_kidsT hkv hT ho', hps]

end
end LeanVM.Guest.Memory
