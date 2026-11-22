/-
  LeanVM.Guest.B1.Main.RelAtInP

  The placed relation by a tree whose pops are given (`RelAtInP`, `RelAtInCP`), the callees with theirs (`KidsFromInP`), and their composition along a path (`relAtInP_of_walk`, `relAtInP_of_walk_loop`).
-/

module

public import LeanVM.Guest.B1.Main.KidsT
public import LeanVM.Guest.B1.Sig.PopsKit

/-!
# Placed relations with their pops

`RelAtInP … ps`, `RelAtInCP … ps`: `RelAtIn`, `RelAtInC` by a tree popping `ps` on the reader in scope (`RelAtInT` with that predicate). `KidsFromInP … cs pss …`: `KidsFromIn`, one entry list per call, an entered callee's tree popping it, a skipped one's `[]` (a phantom pops nothing).

`relAtInP_of_walk`, `relAtInP_of_walk_loop`: `relAtIn_of_walk`, `relAtIn_of_walk_loop` with the callees' pops `pss` (and the tail call's `pt`), and the path's own entries with theirs spliced in, `splice rd σ es pss = ps`; `splice_of_body` gives that equation from a block's `SplicePops` and a return setting up no call.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`RelAtIn` by a tree popping `ps`.** -/
abbrev RelAtInP (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E) (ps : List Pop) :
    Prop :=
  RelAtInT P fs cert rd R D fp n f args rets fun t => t.pops P rd = ps

/-- **`RelAtInC` by a tree popping `ps`.** -/
abbrev RelAtInCP (rd : Reader) (R D : ℕ → Prop) (fp c B n : ℕ) (f : String) (args rets : List E)
    (ps : List Pop) : Prop :=
  RelAtInCT P fs cert rd R D fp c B n f args rets fun t => t.pops P rd = ps

/-- **`KidsFromIn`, each call's entries given**: an entered callee's tree pops them, a skipped one's are `[]`. -/
def KidsFromInP (rd : Reader) (σ : Val) (R : ℕ → Prop) :
    (ℕ → Prop) → List Call → List (List Pop) → ℕ → ℕ → (ℕ → Prop) → Prop
  | Dacc, [], [], _, n, Dend => n = 0 ∧ ∀ i, Dend i → Dacc i
  | Dacc, c :: cs, p :: pss, b, n, Dend => ∃ (m n' : ℕ) (Rk Dk : ℕ → Prop), n = m + n' ∧
      (∀ i, Rk i → R i ∨ Dacc i) ∧
      (if c.taken then RelAtInP P fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ) p
        else m = fs c.f ∧ p = []) ∧
      KidsFromInP rd σ R (fun i => Dacc i ∨ (c.taken = true ∧ Dk i)) cs pss (b + m) n' Dend
  | _, _, _, _, _, _ => False

/-- A skipped call's entries are `[]`. -/
def KidsPopsOk : List Call → List (List Pop) → Prop
  | c :: cs, p :: pss => (c.taken = false → p = []) ∧ KidsPopsOk cs pss
  | [], [] => True
  | _, _ => False

variable {P fs cert}

theorem KidsPopsOk.length : ∀ {cs : List Call} {pss : List (List Pop)}, KidsPopsOk cs pss → pss.length = cs.length
  | _ :: _, _ :: _, h => by rw [List.length_cons, List.length_cons, h.2.length]
  | [], [], _ => rfl

theorem KidsPopsOk.snoc {c : Call} {p : List Pop} (hp : c.taken = false → p = []) :
    ∀ {cs : List Call} {pss : List (List Pop)}, KidsPopsOk cs pss → KidsPopsOk (cs ++ [c]) (pss ++ [p])
  | _ :: _, _ :: _, h => ⟨h.1, h.2.snoc hp⟩
  | [], [], _ => ⟨hp, trivial⟩

theorem RelAtInP.relAtIn {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {ps : List Pop} (h : RelAtInP P fs cert rd R D fp n f args rets ps) : RelAtIn P fs cert rd R D fp n f args rets :=
  RelAtInT.relAtIn h

theorem RelAtInCP.relAtInC {rd : Reader} {R D : ℕ → Prop} {fp c B n : ℕ} {f : String} {args rets : List E}
    {ps : List Pop} (h : RelAtInCP P fs cert rd R D fp c B n f args rets ps) :
    RelAtInC P fs cert rd R D fp c B n f args rets :=
  RelAtInCT.relAtInC h

/-- **A loop entered fresh**, with its pops. -/
theorem RelAtInCP.relAtInP {rd : Reader} {R D : ℕ → Prop} {fp B n : ℕ} {f : String} {args rets : List E}
    {ps : List Pop} (h : RelAtInCP P fs cert rd R D fp (fp + B) B n f args rets ps) :
    RelAtInP P fs cert rd R D fp (B + n) f args rets ps :=
  RelAtInCT.relAtInT h

variable {rd : Reader} {σ : Val}

/-- `KidsFromInP` is `KidsFromInT` by the trees popping the entries, a skipped call's `[]`. -/
theorem KidsFromInP.toT {R : ℕ → Prop} : ∀ {cs : List Call} {pss : List (List Pop)} {Dacc : ℕ → Prop} {b n : ℕ}
    {Dend : ℕ → Prop}, KidsFromInP P fs cert rd σ R Dacc cs pss b n Dend →
    KidsFromInT P fs cert rd σ R Dacc cs (pss.map fun p t => t.pops P rd = p) b n Dend ∧ KidsPopsOk cs pss
  | [], [], _, _, _, _, h => ⟨h, trivial⟩
  | c :: cs, p :: pss, _, _, _, _, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ => by
      obtain ⟨hk, ho⟩ := KidsFromInP.toT hk
      refine ⟨⟨m, n', Rk, Dk, hn, hR, ?_, hk⟩, fun ht => ?_, ho⟩
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc ⊢; exact hc
        · rw [ite_eq_right ht] at hc ⊢; exact hc.1
      · rw [ht] at hc; exact hc.2
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h => h.elim

/-- **The callees' pops**: an entered one's tree pops its entries, a phantom `[]`. -/
theorem popsKids_of_kidsT : ∀ {cs : List Call} {pss : List (List Pop)} {ks : List Tree},
    Tree.KidsValid P rd σ cs ks → KidsT cs (pss.map fun p t => t.pops P rd = p) ks → KidsPopsOk cs pss →
    Tree.popsKids P rd ks = pss
  | [], [], [], _, _, _ => by rw [Tree.popsKids]
  | c :: cs, p :: pss, k :: ks, ⟨_, hc, hv⟩, hT, ho => by
      rw [List.map_cons] at hT
      rw [Tree.popsKids, popsKids_of_kidsT hv hT.2 ho.2]
      by_cases ht : c.taken = true
      · rw [hT.1 ht]
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        rw [ho.1 (by simpa using ht), Tree.pops]
  | [], _, _ :: _, h, _, _ | _ :: _, _, [], h, _, _ => h.elim
  | [], _ :: _, [], _, _, h | _ :: _, [], _ :: _, _, _, h => h.elim

/-- **The path's entries, the callees' spliced in**, from a block's `SplicePops` and a return setting up no call. -/
theorem splice_of_body {body xs ys : List Stmt} {ks : List (List Pop)} {p : List Pop} {es es' : List Ev}
    {vs vs' : List V} (hb : body = xs ++ ys) (hx : SplicePops rd σ xs ks p) (hy : walk σ ys = .ret es' vs')
    (hc : calls es' = []) (hw : walk σ body = .ret es vs) : splice rd σ es ks = p ++ evPops rd σ es' := by
  obtain ⟨es0, hw0, hc0, rfl⟩ := hx
  rw [hb, walk_append_fall' ys hw0, hy, Out.pre] at hw
  cases hw
  have e := splice_append (rd := rd) (σ := σ) es0 es' ks [] hc0
  rw [List.append_nil] at e
  rw [e, splice_nil_of_calls es' hc]

/-- **Composition with regions and pops**: `relAtIn_of_walk`, the callees popping `pss`, the path's entries with theirs
spliced in `ps`. -/
theorem relAtInP_of_walk (hP : P.Wf) {R D Dk : ℕ → Prop} {fp N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hl : P.loop f = false ∨ calls es = []) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b
        => ofK (addressOfIndex b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + cert f q.2)))
    {pss : List (List Pop)} {ps : List Pop}
    (hk : KidsFromInP P fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
      (fun _ => False) (calls es) pss (fp + fs f + (allocs σ es).sum) N Dk)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ R i ∨ Dk i))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ Dk i)
    (hps : splice rd σ es pss = ps) :
    RelAtInP P fs cert rd R D fp (fs f + (allocs σ es).sum + N) f args rets ps := by
  obtain ⟨hkT, ho⟩ := hk.toT
  obtain ⟨t, ht, ks, rfl, hT⟩ := relAtInWT_of_walk hP hf hl hp hw hr hes hbuf haddr _ hkT hload hD
  refine ⟨_, ht, ?_⟩
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := ht.2.1
  rw [hf] at hf'; cases hf'
  rw [hw] at hw'; cases hw'
  rw [Tree.pops_node hf hw, popsKids_of_kidsT hkv hT ho, hps]

/-- **Composition with regions and pops, a loop iteration**: `relAtIn_of_walk_loop`, the other callees popping `pss`,
the tail call `pt` (`[]` when not taken), the path's entries with theirs spliced in `ps`. -/
theorem relAtInP_of_walk_loop (hP : P.Wf) {R D Dk Rt Dt : ℕ → Prop} {fp c Bt m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {ct : Call}
    {pss : List (List Pop)} {pt ps : List Pop}
    (hf : P.find? f = some fn) (hl : P.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hc : calls es = cs ++ [ct])
    (htail : if ct.taken then
        RelAtInCP P fs cert rd Rt Dt (fp + fs f) (c + (allocs σ es).sum + N) Bt m ct.f
          (ct.args.map σ) (ct.rets.map σ) pt
      else Bt = fs ct.f ∧ m = 0 ∧ pt = [])
    (hbuf : (allocDsts es).map σ = (bases c (allocs σ es)).map fun b => ofK (addressOfIndex b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + cert f q.2)))
    (hk : KidsFromInP P fs cert rd σ (fun i => R i ∨ ownData cert fp c f (allocs σ es) es i)
      (fun _ => False) cs pss (c + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp c f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp c f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (ct.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp c f (allocs σ es) es i ∨ Dk i ∨ (ct.taken = true ∧ Dt i))
    (hps : splice rd σ es (pss ++ [pt]) = ps) :
    RelAtInCP P fs cert rd R D fp c (fs f + Bt) ((allocs σ es).sum + N + m) f args rets ps := by
  obtain ⟨hkT, ho⟩ := hk.toT
  have htail' : if ct.taken then
      RelAtInCT P fs cert rd Rt Dt (fp + fs f) (c + (allocs σ es).sum + N) Bt m ct.f (ct.args.map σ) (ct.rets.map σ)
        fun t => t.pops P rd = pt
      else Bt = fs ct.f ∧ m = 0 := by
    by_cases ht : ct.taken = true
    · rw [ite_eq_left ht] at htail ⊢; exact htail
    · rw [ite_eq_right ht] at htail ⊢; exact ⟨htail.1, htail.2.1⟩
  have ho' : KidsPopsOk (cs ++ [ct]) (pss ++ [pt]) := ho.snoc fun ht => by
    rw [ht] at htail; exact htail.2.2
  obtain ⟨t, ht, ks, rfl, hT⟩ := relAtInWT_of_walk_loop hP hf hl hp hw hr hes hc htail' hbuf haddr
    (by rw [List.length_map, ho.length]) hkT hRt hload hD
  refine ⟨_, ht, ?_⟩
  obtain ⟨fn', hf', -, es', vs', hw', -, -, hkv⟩ := ht.2.1
  rw [hf] at hf'; cases hf'
  rw [hw] at hw'; cases hw'
  rw [hc, ← List.map_singleton (f := fun p (t : Tree) => t.pops P rd = p), ← List.map_append] at hT
  rw [hc] at hkv
  rw [Tree.pops_node hf hw, popsKids_of_kidsT hkv hT ho', hps]

end
end LeanVM.Guest.Memory
