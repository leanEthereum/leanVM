/-
  LeanVM.Guest.B1.Main.KidsT

  The placed relation's composition with predicates on the callees' trees: a callee complete by
  a tree satisfying `T` puts a tree satisfying `T` among its caller's children.
-/

module

public import LeanVM.Guest.B1.Main.RelAtW
public import LeanVM.Guest.Memory.Uniform

/-!
# Callees' trees with predicates

`RelAtInT … T`: `RelAtIn` by a tree satisfying `T`. `KidsFromInT … Ts`: `KidsFromIn`, the `j`-th
entered callee by a tree satisfying `Ts[j]` (no constraint past `Ts`). `KidsT cs Ts ks`: the
entered callees' trees satisfy their predicates. `relAtInWT_of_walk`: `relAtIn_of_walk` (same
proof), its tree the node at the walk's valuation with children satisfying `KidsT`;
`relAtInWT_of_walk_loop` likewise for a loop helper (`relAtIn_of_walk_loop`), its tail call's tree
satisfying `Tt`.
`CompleteAtDT … T`: `CompleteAtD` by a tree satisfying `T`; `kidsFromInT_of_kidsDT`:
`kidsFromIn_of_kidsD` with the callees' predicates.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`RelAtIn` by a tree satisfying `T`.** -/
def RelAtInT (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E)
    (T : Tree → Prop) : Prop :=
  ∃ t : Tree, (t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧ t.Placed P fs cert fp ∧
    t.total fs = n ∧ t.LoadsIn P fs cert R fp ∧ ∀ i, D i → t.Data P fs cert fp i) ∧ T t

/-- **`KidsFromIn`, the entered callees by trees satisfying `Ts`.** -/
def KidsFromInT (rd : Reader) (σ : Val) (R : ℕ → Prop) :
    (ℕ → Prop) → List Call → List (Tree → Prop) → ℕ → ℕ → (ℕ → Prop) → Prop
  | Dacc, [], _, _, n, Dend => n = 0 ∧ ∀ i, Dend i → Dacc i
  | Dacc, c :: cs, Ts, b, n, Dend => ∃ (m n' : ℕ) (Rk Dk : ℕ → Prop), n = m + n' ∧
      (∀ i, Rk i → R i ∨ Dacc i) ∧
      (if c.taken then RelAtInT P fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ)
          (Ts.headD fun _ => True)
        else m = fs c.f) ∧
      KidsFromInT rd σ R (fun i => Dacc i ∨ (c.taken = true ∧ Dk i)) cs Ts.tail (b + m) n' Dend

/-- The entered callees' trees satisfy their predicates. -/
def KidsT : List Call → List (Tree → Prop) → List Tree → Prop
  | c :: cs, T :: Ts, k :: ks => (c.taken = true → T k) ∧ KidsT cs Ts ks
  | _, _, _ => True

variable {P fs cert}

theorem RelAtInT.relAtIn {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {T : Tree → Prop} (h : RelAtInT P fs cert rd R D fp n f args rets T) :
    RelAtIn P fs cert rd R D fp n f args rets :=
  let ⟨t, ht, _⟩ := h
  ⟨t, ht⟩

theorem RelAtIn.relAtInT {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtIn P fs cert rd R D fp n f args rets) :
    RelAtInT P fs cert rd R D fp n f args rets fun _ => True :=
  let ⟨t, ht⟩ := h
  ⟨t, ht, trivial⟩

variable {rd : Reader} {σ : Val}

/-- The callee of one frame, by a tree satisfying `T`. -/
theorem kid_ofInT {c : Call} {b m : ℕ} {Rk Dk : ℕ → Prop} {T : Tree → Prop}
    (hc : c.taken = false → P.Takes c.f c.args.length = true)
    (h : if c.taken then RelAtInT P fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ) T
      else m = fs c.f) :
    ∃ k : Tree, Tree.KidsValid P rd σ [c] [k] ∧ k.BufsOk P ∧ k.Placed P fs cert b ∧
      k.total fs = m ∧ k.LoadsIn P fs cert Rk b ∧ (c.taken = true → ∀ i, Dk i → k.Data P fs cert b i) ∧
      (c.taken = true → T k) := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at h
    obtain ⟨k, ⟨hn, hv, hb, hp, htot, hl, hd⟩, hT⟩ := h
    exact ⟨k, ⟨hn, by rw [ite_eq_left ht]; exact hv, trivial⟩, hb, hp, htot, hl, fun _ => hd,
      fun _ => hT⟩
  · rw [ite_eq_right ht] at h
    obtain ⟨k, hkv, hkb, hkp, hkt, hkl, hkd⟩ := kid_ofIn (P := P) (fs := fs) (cert := cert) (rd := rd)
      (σ := σ) (b := b) (m := m) (Rk := Rk) (Dk := Dk) hc (by rw [ite_eq_right ht]; exact h)
    exact ⟨k, hkv, hkb, hkp, hkt, hkl, hkd, fun h' => absurd h' ht⟩

/-- The callees of `KidsFromIn`, placed one after another from `b`. -/
theorem kids_of_kidsFromInT (R : ℕ → Prop) : ∀ (cs : List Call) (Ts : List (Tree → Prop)) (Dacc : ℕ → Prop) (b n : ℕ)
    (Dend : ℕ → Prop), (∀ c ∈ cs, c.taken = false → P.Takes c.f c.args.length = true) →
    KidsFromInT P fs cert rd σ R Dacc cs Ts b n Dend →
    ∃ ks : List Tree, Tree.KidsValid P rd σ cs ks ∧ KidsT cs Ts ks ∧ Tree.BufsOkKids P ks ∧
      Tree.PlacedKids P fs cert (bases b (ks.map (Tree.total fs))) ks ∧
      (ks.map (Tree.total fs)).sum = n ∧
      (∀ i, Dend i → Dacc i ∨ Tree.DataKids P fs cert (bases b (ks.map (Tree.total fs))) ks i) ∧
      ∀ Rp : ℕ → Prop, (∀ i, R i → Rp i) → (∀ i, Dacc i → Rp i) →
        (∀ i, Tree.DataKids P fs cert (bases b (ks.map (Tree.total fs))) ks i → Rp i) →
        Tree.LoadsInKids P fs cert Rp (bases b (ks.map (Tree.total fs))) ks
  | [], _, Dacc, _, n, Dend, _, h => by
      rw [KidsFromInT] at h
      refine ⟨[], by simp [Tree.KidsValid], trivial, by rw [Tree.BufsOkKids]; trivial, placedKids_nil,
        by simp [h.1], fun i hi => Or.inl (h.2 i hi), fun _ _ _ _ => loadsInKids_nil⟩
  | c :: cs, Ts, Dacc, b, n, Dend, hw, h => by
      rw [KidsFromInT] at h
      obtain ⟨m, n', Rk, Dk, rfl, hRk, hc, hcs⟩ := h
      obtain ⟨k, hkv, hkb, hkp, hkt, hkl, hkd, hkT⟩ := kid_ofInT (hw c List.mem_cons_self) hc
      obtain ⟨ks, hv, hT, hb, hp, hs, hd, hl⟩ := kids_of_kidsFromInT R cs Ts.tail _ (b + m) n' Dend
        (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) hcs
      have hpos : bases b ((k :: ks).map (Tree.total fs)) = b :: bases (b + m) (ks.map (Tree.total fs)) := by
        rw [List.map_cons, bases, hkt]
      refine ⟨k :: ks, ⟨hkv.1, hkv.2.1, hv⟩, ?_, by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, ?_, ?_, ?_, ?_⟩
      · cases Ts with
        | nil => trivial
        | cons T Ts => exact ⟨hkT, hT⟩
      · rw [hpos, placedKids_cons]; exact ⟨hkp, hp⟩
      · rw [List.map_cons, List.sum_cons, hkt, hs]
      · intro i hi
        rw [hpos, dataKids_cons]
        rcases hd i hi with (h | ⟨ht, h⟩) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (hkd ht i h))
        · exact Or.inr (Or.inr h)
      · intro Rp hR hD hK
        rw [hpos] at hK ⊢
        rw [loadsInKids_cons]
        refine ⟨loadsIn_mono k b (fun i hi => (hRk i hi).elim (hR i) (hD i)) hkl,
          hl Rp hR (fun i hi => ?_) (fun i hi => hK i (dataKids_cons.mpr (Or.inr hi)))⟩
        rcases hi with h | ⟨ht, h⟩
        · exact hD i h
        · exact hK i (dataKids_cons.mpr (Or.inl (hkd ht i h)))

/-- **Composition with regions, the callees' predicates exposed**: `relAtIn_of_walk`, by the node
at the walk's valuation, its children satisfying `KidsT`. -/
theorem relAtInWT_of_walk (hP : P.Wf) {R D Dk : ℕ → Prop} {fp N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hl : P.loop f = false ∨ calls es = []) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b
        => ofK (addressOfIndex b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + cert f q.2)))
    (Ts : List (Tree → Prop))
    (hk : KidsFromInT P fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
      (fun _ => False) (calls es) Ts (fp + fs f + (allocs σ es).sum) N Dk)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ R i ∨ Dk i))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ Dk i) :
    ∃ t : Tree, (t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧ t.Placed P fs cert fp ∧
      t.total fs = fs f + (allocs σ es).sum + N ∧ t.LoadsIn P fs cert R fp ∧
      ∀ i, D i → t.Data P fs cert fp i) ∧
      ∃ ks, t = .node f σ (allocs σ es) ks ∧ KidsT (calls es) Ts ks := by
  obtain ⟨ks, hkv, hkT, hkb, hkp, hks, hkd, hkl⟩ :=
    kids_of_kidsFromInT _ _ _ _ _ _ _ (takes_of_calls hP (List.mem_of_find?_eq_some hf) hw) hk
  have hl' : P.loop f = false ∨ ks.map (Tree.total fs) = [] := by
    rcases hl with hl | hl
    · exact Or.inl hl
    · rw [hl] at hkv
      cases ks with
      | nil => exact Or.inr rfl
      | cons _ _ => exact hkv.elim
  obtain ⟨hbb, hkpos⟩ := kidPos_not_loop (fs := fs) (fp := fp) (bufs := allocs σ es) hl'
  have hdata : ∀ i, (Tree.node f σ (allocs σ es) ks).Data P fs cert fp i ↔
      ownData cert fp (fp + fs f) f (allocs σ es) es i ∨
        Tree.DataKids P fs cert (bases (fp + fs f + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos]
  refine ⟨.node f σ (allocs σ es) ks, ⟨rfl, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_, ?_, ?_, ?_⟩,
    ks, rfl, hkT⟩
  · rw [Tree.BufsOk, events_node hf hw]
    exact ⟨rfl, hkb⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    exact ⟨⟨hbuf, haddr⟩, hkp⟩
  · rw [total_node, totalKids_eq_sum, hks]
    omega
  · rw [loadsIn_node, events_node hf hw, hkpos]
    refine ⟨fun A hA => ?_, hkl _ (fun i hi => ?_) (fun _ h => h.elim) (fun i hi => ?_)⟩
    · obtain ⟨i, hi, h⟩ := hload A hA
      refine ⟨i, hi, ?_⟩
      rw [hdata]
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact (hkd i h).elim (fun h => h.elim) fun h => Or.inl (Or.inr h)
    · rcases hi with h | h
      · exact Or.inr h
      · exact Or.inl ((hdata i).mpr (Or.inl h))
    · exact Or.inl ((hdata i).mpr (Or.inr hi))
  · intro i hi
    rw [hdata]
    rcases hD i hi with h | h
    · exact Or.inl h
    · exact (hkd i h).elim (fun h => h.elim) fun h => Or.inr h

theorem kidsValid_length : ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ cs ks →
    ks.length = cs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by rw [List.length_cons, List.length_cons, kidsValid_length h.2.2]
  | [], _ :: _, h => by simp [Tree.KidsValid] at h
  | _ :: _, [], h => by simp [Tree.KidsValid] at h

theorem kidsT_snoc {c : Call} {T : Tree → Prop} {k : Tree} : ∀ {cs : List Call}
    {Ts : List (Tree → Prop)} {ks : List Tree}, Ts.length = cs.length → ks.length = cs.length →
    KidsT cs Ts ks → (c.taken = true → T k) → KidsT (cs ++ [c]) (Ts ++ [T]) (ks ++ [k])
  | [], [], [], _, _, _, hc => ⟨hc, trivial⟩
  | [], [], _ :: _, _, h2, _, _ => by simp at h2
  | [], _ :: _, _, h1, _, _, _ => by simp at h1
  | _ :: _, [], _, h1, _, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, h2, _, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, h1, h2, h, hc =>
    ⟨h.1, kidsT_snoc (by simpa using h1) (by simpa using h2) h.2 hc⟩

/-- **Composition with regions, a loop helper, its callees' trees exposed**:
`relAtIn_of_walk_loop` by the node at the walk's valuation, its children satisfying
`KidsT (calls es) (Ts ++ [Tt])`: the other callees `Ts`, the tail call `Tt`. -/
theorem relAtInWT_of_walk_loop (hP : P.Wf) {R D Dk Rt Dt : ℕ → Prop} {fp m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {c : Call} {Ts : List (Tree → Prop)}
    {Tt : Tree → Prop}
    (hf : P.find? f = some fn) (hl : P.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAtInT P fs cert rd Rt Dt (fp + fs f) m c.f (c.args.map σ) (c.rets.map σ) Tt
      else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b
        => ofK (addressOfIndex b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + cert f q.2)))
    (hTs : Ts.length = cs.length)
    (hk : KidsFromInT P fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i)
      (fun _ => False) cs Ts (fp + fs f + m + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧
      (ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (c.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i ∨
      (c.taken = true ∧ Dt i)) :
    RelAtInT P fs cert rd R D fp (fs f + m + (allocs σ es).sum + N) f args rets
      (fun t => ∃ ks, t = .node f σ (allocs σ es) ks ∧ KidsT (calls es) (Ts ++ [Tt]) ks) := by
  have htk := takes_of_calls hP (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkTs, hkb, hkp, hks, hkd, hkl⟩ := kids_of_kidsFromInT _ _ _ _ _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  obtain ⟨k, hkv', hkb', hkp', hkt, hkl', hkd', hkT⟩ :=
    kid_ofInT (htk c (List.mem_append_right _ List.mem_cons_self)) htail
  have hns : (ks ++ [k]).map (Tree.total fs) = ks.map (Tree.total fs) ++ [m] := by
    rw [List.map_append, List.map_singleton, hkt]
  have hbb : bufBase fs P.loop fp f ((ks ++ [k]).map (Tree.total fs)) = fp + fs f + m := by
    rw [hns]; simp [bufBase, hl]
  have hkpos : kidPos fs P.loop fp f (allocs σ es) ((ks ++ [k]).map (Tree.total fs)) =
      bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs)) ++ [fp + fs f] := by
    rw [kidPos, ite_eq_left hl, hbb, hns, List.dropLast_concat, List.getLast?_concat]
    rfl
  have hlen : (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))).length = ks.length := by
    rw [length_bases, List.length_map]
  have hdata : ∀ i, (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i ↔
      ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨
        Tree.DataKids P fs cert (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i ∨
        k.Data P fs cert (fp + fs f) i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos, dataKids_append hlen, dataKids_cons]
    simp only [not_dataKids_nil, or_false]
  refine ⟨.node f σ (allocs σ es) (ks ++ [k]), ⟨rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, by rw [hc]; exact kidsValid_append hkv hkv'⟩, ?_, ?_, ?_, ?_, ?_⟩,
    ks ++ [k], rfl, by rw [hc]; exact kidsT_snoc hTs (kidsValid_length hkv) hkTs hkT⟩
  · rw [Tree.BufsOk, events_node hf hw]
    refine ⟨rfl, bufsOkKids_append hkb ?_⟩
    rw [Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hkb', trivial⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    refine ⟨⟨hbuf, haddr⟩, placedKids_append hlen hkp ?_⟩
    rw [placedKids_cons]
    exact ⟨hkp', placedKids_nil⟩
  · rw [total_node, totalKids_eq_sum, hns, List.sum_append, hks]
    simp only [List.sum_cons, List.sum_nil]
    omega
  · have hDk : ∀ i, Dk i → (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i := fun i h =>
      (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    have hDt : ∀ i, c.taken = true ∧ Dt i → (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i :=
      fun i h => (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))
    have hown : ∀ i, ownData cert fp (fp + fs f + m) f (allocs σ es) es i →
        (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i := fun i h => (hdata i).mpr (Or.inl h)
    rw [loadsIn_node, events_node hf hw, hkpos]
    refine ⟨fun A hA => ?_, loadsInKids_append hlen ?_ ?_⟩
    · obtain ⟨i, hi, h⟩ := hload A hA
      refine ⟨i, hi, ?_⟩
      rcases h with h | h | h | h
      · exact Or.inl (hown i h)
      · exact Or.inr h
      · exact Or.inl (hDk i h)
      · exact Or.inl (hDt i h)
    · exact hkl _ (fun i hi => hi.elim Or.inr fun h => Or.inl (hown i h)) (fun _ h => h.elim)
        (fun i hi => Or.inl ((hdata i).mpr (Or.inr (Or.inl hi))))
    · rw [loadsInKids_cons]
      refine ⟨loadsIn_mono k _ (fun i hi => ?_) hkl', loadsInKids_nil⟩
      rcases hRt i hi with h | h | h
      · exact Or.inr h
      · exact Or.inl (hown i h)
      · exact Or.inl (hDk i h)
  · intro i hi
    rcases hD i hi with h | h | h
    · exact (hdata i).mpr (Or.inl h)
    · exact (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    · exact (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))

end
end LeanVM.Guest.Memory

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`CompleteAtD` by a tree satisfying `T`.** -/
def CompleteAtDT (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (T : Tree → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets T

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem CompleteAtD.toT {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtD fs cert k f Lin args Out) :
    CompleteAtDT fs cert k f Lin args Out fun _ => True := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => (hr rd hl hm).relAtInT⟩

theorem CompleteAtDT.toD {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Tree → Prop} (h : CompleteAtDT fs cert k f Lin args Out T) :
    CompleteAtD fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => (hr rd hl hm).relAtIn⟩

/-- A completeness on memories defined below `2^k` holds on those defined below `2^k'`,
`k ≤ k'`. -/
theorem CompleteAtD.lowMono {k k' : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtD fs cert k f Lin args Out) (hk : k ≤ k') :
    CompleteAtD fs cert k' f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => hr rd (hl.mono hk) hm⟩

theorem CompleteAtDT.lowMono {k k' : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Tree → Prop} (h : CompleteAtDT fs cert k f Lin args Out T)
    (hk : k ≤ k') : CompleteAtDT fs cert k' f Lin args Out T := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => hr rd (hl.mono hk) hm⟩

/-- The entered callees are complete by trees satisfying their predicates. -/
def KidsDT (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : List Kid → List (Tree → Prop) → Prop
  | k :: ks, Ts => (k.taken = true → CompleteAtDT fs cert κ k.f k.Lin k.args k.Out
      (Ts.headD fun _ => True)) ∧ KidsDT fs cert κ ks Ts.tail
  | [], _ => True

theorem KidsDT.lowMono {κ κ' : ℕ} (hk : κ ≤ κ') : ∀ {ks : List Kid} {Ts : List (Tree → Prop)},
    KidsDT fs cert κ ks Ts → KidsDT fs cert κ' ks Ts
  | [], _, _ => trivial
  | _ :: _, _, ⟨h, hs⟩ => ⟨fun ht => (h ht).lowMono hk, hs.lowMono hk⟩

theorem kidsFromInT_dend {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (Dacc : ℕ → Prop) (b n : ℕ) {D D' : ℕ → Prop},
      (∀ i, D' i → D i) →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs Ts b n D →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs Ts b n D'
  | [], _, _, _, _, _, _, hD, ⟨hn, h⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: cs, _, _, _, _, _, _, hD, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, hR, hc, kidsFromInT_dend cs _ _ _ _ hD hk⟩

theorem kidsFromInT_of_kidsDT (κ : ℕ) : ∀ (ks : List Kid) (Ts : List (Tree → Prop)),
    KidsDT fs cert κ ks Ts → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      DisjL L ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInT coreProgram fs cert rd σ R Dacc cs Ts b N (fun i => Dacc i ∨ outRegion ks outs i)
  | [], _, _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, Ts, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hrel⟩ := hok.1 ht b
      obtain ⟨N, L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInT_of_kidsDT κ ks Ts.tail hok.2 (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_,
        disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            exact hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromInT_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨N, L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInT_of_kidsDT κ ks Ts.tail hok.2 (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · have ht' : k.taken = false := by simpa using ht
          rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInT_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

end
end LeanVM.Guest.B1
