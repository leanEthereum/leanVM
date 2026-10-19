/-
  LeanVM.Guest.B1.Main.WeightAt

  The placed relation by a tree within weights (`RelAtInW`), and its composition along a path and
  over a loop helper's iterations, as `RelAtIn`'s: the weights ride the completeness proofs, so a
  bound holds of the tree a completeness proof builds, whose hints are the honest ones.
-/

module

public import LeanVM.Guest.B1.Main.LoopAt
public import LeanVM.Guest.Memory.Size

/-!
# Placed relations within weights

A family of weights `w θ` (one per `θ : Θ`, e.g. per opcode). `RelAtInW … Bw` is `RelAtIn` by a
tree weighing at most `Bw θ` at every `w θ`. The callees of a path compose as `KidsFromIn`'s, each
entered one within its bound (`KidsFromInW`, `kids_of_kidsFromInW`); a node weighs its function's
weight and its callees' (`relAtInW_of_walk`, `relAtInW_of_walk_loop`). `CompleteAtW … B Bw` is
`CompleteAtB … B` by such trees: from `CompleteAtB` and a bound on every valid tree
(`CompleteAtB.toW`, `CompleteAtB.toW_weightLe`), or a weight within `α / 1000` times the words (`CompleteAtB.toW_tot`,
`WeightTot`). `kidsFromInW_of_kidsW`, `completeAt_loopW`, `loopStep_bufsW` are
`kidsFromIn_of_kidsB`, `completeAt_loop`, `loopStep_bufs` with the weights.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB Returns Kid CallsMatch
  OutsOk OutsIn RegionsOk outRegion kidsBound within_append kidsFromIn_dend)

@[expose] public section

/-- **Every valid tree of `f` weighs at most `α / 1000` times its words.** -/
def WeightTot (fs ω : String → ℕ) (f : String) (α : ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.Valid coreProgram rd args rets →
    t.BufsOk coreProgram → 1000 * t.weight ω ≤ α * t.total fs

theorem weightKids_append (ω : String → ℕ) : ∀ (k1 k2 : List Tree),
    Tree.weightKids ω (k1 ++ k2) = Tree.weightKids ω k1 + Tree.weightKids ω k2
  | [], _ => by simp [Tree.weightKids]
  | k :: k1, k2 => by
    simp only [List.cons_append, Tree.weightKids, weightKids_append ω k1 k2]; omega

variable (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type} (w : Θ → String → ℕ)

/-- **`RelAtIn` by a tree within the weights `Bw`.** -/
def RelAtInW (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E)
    (Bw : Θ → ℕ) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.Valid coreProgram rd args rets ∧ t.BufsOk coreProgram ∧
    t.Placed coreProgram fs cert fp ∧ t.total fs = n ∧ t.LoadsIn coreProgram fs cert R fp ∧
    (∀ i, D i → t.Data coreProgram fs cert fp i) ∧ ∀ θ, t.weight (w θ) ≤ Bw θ

/-- **`KidsFromIn` within weights**: each entered callee within its bound in `bws`. -/
def KidsFromInW (rd : Reader) (σ : Val) (R : ℕ → Prop) :
    (ℕ → Prop) → List Call → List (Θ → ℕ) → ℕ → ℕ → (ℕ → Prop) → Prop
  | Dacc, [], _, _, n, Dend => n = 0 ∧ ∀ i, Dend i → Dacc i
  | _, _ :: _, [], _, _, _ => False
  | Dacc, c :: cs, bw :: bws, b, n, Dend => ∃ (m n' : ℕ) (Rk Dk : ℕ → Prop), n = m + n' ∧
      (∀ i, Rk i → R i ∨ Dacc i) ∧
      (if c.taken then RelAtInW fs cert w rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ) bw
        else m = fs c.f) ∧
      KidsFromInW rd σ R (fun i => Dacc i ∨ (c.taken = true ∧ Dk i)) cs bws (b + m) n' Dend

/-- **`CompleteAtB` by trees within the weights `Bw`.** -/
def CompleteAtW (κ : ℕ) (f : String) (Lin : Layout) (args : List E) (Out : List E → Layout → Prop)
    (B : ℕ) (Bw : Θ → ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ n ≤ B ∧ ∀ rd, LowDef κ rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInW fs cert w rd (RegionL Lin) (RegionL Lout) fp n f args rets Bw

/-- **Callees within bounds and weights**: each entered one `CompleteAtW`, each one not entered
its frame within its bound. -/
def KidsW (κ : ℕ) : List Kid → List ℕ → List (Θ → ℕ) → Prop
  | k :: ks, B :: bs, Bw :: bws => (k.taken = true → CompleteAtW fs cert w κ k.f k.Lin k.args k.Out B Bw) ∧
      (k.taken = false → fs k.f ≤ B) ∧ KidsW κ ks bs bws
  | [], [], [] => True
  | _, _, _ => False

variable {fs cert w}

theorem RelAtInW.toRelAtIn {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw : Θ → ℕ} (h : RelAtInW fs cert w rd R D fp n f args rets Bw) :
    RelAtIn coreProgram fs cert rd R D fp n f args rets :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd, _⟩ := h
  ⟨t, hn, hv, hb, hp, ht, hl, hd⟩

theorem RelAtInW.dmono {rd : Reader} {R D D' : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw : Θ → ℕ} (h : RelAtInW fs cert w rd R D fp n f args rets Bw) (hD : ∀ i, D' i → D i) :
    RelAtInW fs cert w rd R D' fp n f args rets Bw :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd, hw⟩ := h
  ⟨t, hn, hv, hb, hp, ht, hl, fun i hi => hd i (hD i hi), hw⟩

theorem RelAtInW.wmono {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Bw Bw' : Θ → ℕ} (h : RelAtInW fs cert w rd R D fp n f args rets Bw) (hB : ∀ θ, Bw θ ≤ Bw' θ) :
    RelAtInW fs cert w rd R D fp n f args rets Bw' :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd, hw⟩ := h
  ⟨t, hn, hv, hb, hp, ht, hl, hd, fun θ => (hw θ).trans (hB θ)⟩

/-- A `RelAtIn` tree is within the bound every valid tree at its arguments is. -/
theorem relAtInW_of_valid {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String}
    {args rets : List E} {Bw : Θ → ℕ} (h : RelAtIn coreProgram fs cert rd R D fp n f args rets)
    (hw : ∀ θ (rd : Reader) (t : Tree) (rets : List E), t.name = f → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.weight (w θ) ≤ Bw θ) :
    RelAtInW fs cert w rd R D fp n f args rets Bw :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd⟩ := h
  ⟨t, hn, hv, hb, hp, ht, hl, hd, fun θ => hw θ rd t rets hn hv hb⟩

/-- A `RelAtIn` tree is within the bound every valid tree is. -/
theorem relAtInW_of_weightLe {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String}
    {args rets : List E} {Bf : Θ → List E → ℕ} (h : RelAtIn coreProgram fs cert rd R D fp n f args rets)
    (hw : ∀ θ, WeightLe coreProgram (w θ) f (Bf θ)) :
    RelAtInW fs cert w rd R D fp n f args rets fun θ => Bf θ args :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd⟩ := h
  ⟨t, hn, hv, hb, hp, ht, hl, hd, fun θ => hw θ rd t args rets hn hv hb⟩

/-- A `RelAtIn` tree of `n` words weighs at most `α / 1000` times `n`. -/
theorem relAtInW_of_tot {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String}
    {args rets : List E} {α : Θ → ℕ} (h : RelAtIn coreProgram fs cert rd R D fp n f args rets)
    (hw : ∀ θ, WeightTot fs (w θ) f (α θ)) :
    RelAtInW fs cert w rd R D fp n f args rets fun θ => α θ * n / 1000 :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd⟩ := h
  ⟨t, hn, hv, hb, hp, ht, hl, hd, fun θ => (Nat.le_div_iff_mul_le (by norm_num)).mpr
    (by have := hw θ rd t args rets hn hv hb; rw [ht] at this; linarith)⟩

theorem CompleteAtW.toB {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} (h : CompleteAtW fs cert w κ f Lin args Out B Bw) :
    CompleteAtB fs cert κ f Lin args Out B := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm => (hr rd hl hm).toRelAtIn⟩

theorem CompleteAtW.wmono {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw Bw' : Θ → ℕ} (h : CompleteAtW fs cert w κ f Lin args Out B Bw)
    (hB : ∀ θ, Bw θ ≤ Bw' θ) : CompleteAtW fs cert w κ f Lin args Out B Bw' := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm => (hr rd hl hm).wmono hB⟩

theorem CompleteAtB.toW {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ}
    (h : CompleteAtB fs cert κ f Lin args Out B)
    (hw : ∀ θ (rd : Reader) (t : Tree) (rets : List E), t.name = f → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.weight (w θ) ≤ Bw θ) :
    CompleteAtW fs cert w κ f Lin args Out B Bw := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm => relAtInW_of_valid (hr rd hl hm) hw⟩

theorem CompleteAtB.toW_weightLe {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bf : Θ → List E → ℕ}
    (h : CompleteAtB fs cert κ f Lin args Out B) (hw : ∀ θ, WeightLe coreProgram (w θ) f (Bf θ)) :
    CompleteAtW fs cert w κ f Lin args Out B fun θ => Bf θ args := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm => relAtInW_of_weightLe (hr rd hl hm) hw⟩

theorem CompleteAtB.toW_tot {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {α : Θ → ℕ}
    (h : CompleteAtB fs cert κ f Lin args Out B) (hw : ∀ θ, WeightTot fs (w θ) f (α θ)) :
    CompleteAtW fs cert w κ f Lin args Out B fun θ => α θ * B / 1000 := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    (relAtInW_of_tot (hr rd hl hm) hw).wmono fun _ => Nat.div_le_div_right (Nat.mul_le_mul_left _ hn)⟩

theorem KidsW.append {κ : ℕ} : ∀ {ks ks' : List Kid} {bs bs' : List ℕ} {bws bws' : List (Θ → ℕ)},
    KidsW fs cert w κ ks bs bws → KidsW fs cert w κ ks' bs' bws' →
      KidsW fs cert w κ (ks ++ ks') (bs ++ bs') (bws ++ bws')
  | [], _, [], _, [], _, _, h' => h'
  | _ :: _, _, _ :: _, _, _ :: _, _, ⟨h1, h2, h⟩, h' => ⟨h1, h2, KidsW.append h h'⟩
  | [], _, _ :: _, _, _, _, h, _ => h.elim
  | [], _, [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, _, _, h, _ => h.elim
  | _ :: _, _, _ :: _, _, [], _, h, _ => h.elim

/-! ## Composition -/

section Compose

variable {rd : Reader} {σ : Val}

/-- The callee of one frame, within its weights. -/
theorem kid_ofInW {c : Call} {b m : ℕ} {Rk Dk : ℕ → Prop} {bw : Θ → ℕ}
    (hc : c.taken = false → coreProgram.Takes c.f c.args.length = true)
    (h : if c.taken then RelAtInW fs cert w rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ) bw
      else m = fs c.f) :
    ∃ k : Tree, Tree.KidsValid coreProgram rd σ [c] [k] ∧ k.BufsOk coreProgram ∧
      k.Placed coreProgram fs cert b ∧ k.total fs = m ∧ k.LoadsIn coreProgram fs cert Rk b ∧
      (c.taken = true → ∀ i, Dk i → k.Data coreProgram fs cert b i) ∧ ∀ θ, k.weight (w θ) ≤ bw θ := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at h
    obtain ⟨k, hn, hv, hb, hp, htot, hl, hd, hw⟩ := h
    exact ⟨k, ⟨hn, by rw [ite_eq_left ht]; exact hv, trivial⟩, hb, hp, htot, hl, fun _ => hd, hw⟩
  · rw [ite_eq_right ht] at h
    obtain ⟨k, hkv, hkb, hkp, hkt, hkl, -⟩ := kid_ofIn (P := coreProgram) (fs := fs) (cert := cert)
      (rd := rd) (σ := σ) (b := b) (m := m) (Rk := Rk) (Dk := Dk) hc
      (show (if c.taken then RelAtIn coreProgram fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ)
        else m = fs c.f) by rw [ite_eq_right ht]; exact h)
    have hk := hkv.2.1
    rw [ite_eq_right ht] at hk
    obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
    exact ⟨_, hkv, hkb, hkp, hkt, hkl, fun h' => absurd h' ht, fun θ => by simp [Tree.weight]⟩

/-- **The callees of `KidsFromInW`**, as `kids_of_kidsFromIn`, within their weights. -/
theorem kids_of_kidsFromInW (R : ℕ → Prop) : ∀ (cs : List Call) (bws : List (Θ → ℕ))
    (Dacc : ℕ → Prop) (b n : ℕ) (Dend : ℕ → Prop),
    (∀ c ∈ cs, c.taken = false → coreProgram.Takes c.f c.args.length = true) →
    KidsFromInW fs cert w rd σ R Dacc cs bws b n Dend →
    ∃ ks : List Tree, Tree.KidsValid coreProgram rd σ cs ks ∧ Tree.BufsOkKids coreProgram ks ∧
      Tree.PlacedKids coreProgram fs cert (bases b (ks.map (Tree.total fs))) ks ∧
      (ks.map (Tree.total fs)).sum = n ∧
      (∀ i, Dend i → Dacc i ∨ Tree.DataKids coreProgram fs cert (bases b (ks.map (Tree.total fs))) ks i) ∧
      (∀ Rp : ℕ → Prop, (∀ i, R i → Rp i) → (∀ i, Dacc i → Rp i) →
        (∀ i, Tree.DataKids coreProgram fs cert (bases b (ks.map (Tree.total fs))) ks i → Rp i) →
        Tree.LoadsInKids coreProgram fs cert Rp (bases b (ks.map (Tree.total fs))) ks) ∧
      ∀ θ, Tree.weightKids (w θ) ks ≤ (bws.map (· θ)).sum
  | [], _, Dacc, _, n, Dend, _, h => by
      rw [KidsFromInW] at h
      refine ⟨[], by simp [Tree.KidsValid], by rw [Tree.BufsOkKids]; trivial, placedKids_nil,
        by simp [h.1], fun i hi => Or.inl (h.2 i hi), fun _ _ _ _ => loadsInKids_nil,
        fun θ => by simp [Tree.weightKids]⟩
  | _ :: _, [], _, _, _, _, _, h => by rw [KidsFromInW] at h; exact h.elim
  | c :: cs, bw :: bws, Dacc, b, n, Dend, hw, h => by
      rw [KidsFromInW] at h
      obtain ⟨m, n', Rk, Dk, rfl, hRk, hc, hcs⟩ := h
      obtain ⟨k, hkv, hkb, hkp, hkt, hkl, hkd, hkw⟩ := kid_ofInW (hw c List.mem_cons_self) hc
      obtain ⟨ks, hv, hb, hp, hs, hd, hl, hws⟩ := kids_of_kidsFromInW R cs bws _ (b + m) n' Dend
        (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) hcs
      have hpos : bases b ((k :: ks).map (Tree.total fs)) = b :: bases (b + m) (ks.map (Tree.total fs)) := by
        rw [List.map_cons, bases, hkt]
      refine ⟨k :: ks, ⟨hkv.1, hkv.2.1, hv⟩, by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, ?_, ?_, ?_, ?_, ?_⟩
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
      · intro θ
        have := hws θ
        have := hkw θ
        simp only [Tree.weightKids, List.map_cons, List.sum_cons]
        omega

/-- **`relAtIn_of_walk` within weights**: the node weighs its function's weight and its
callees'. -/
theorem relAtInW_of_walk {R D Dk : ℕ → Prop} {fp N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {bws : List (Θ → ℕ)}
    (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false ∨ calls es = []) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromInW fs cert w rd σ (fun i => R i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
      (fun _ => False) (calls es) bws (fp + fs f + (allocs σ es).sum) N Dk)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ R i ∨ Dk i))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ Dk i) :
    RelAtInW fs cert w rd R D fp (fs f + (allocs σ es).sum + N) f args rets
      fun θ => w θ f + (bws.map (· θ)).sum := by
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl, hkw⟩ :=
    kids_of_kidsFromInW _ _ _ _ _ _ _ (takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw) hk
  have hl' : coreProgram.loop f = false ∨ ks.map (Tree.total fs) = [] := by
    rcases hl with hl | hl
    · exact Or.inl hl
    · rw [hl] at hkv
      cases ks with
      | nil => exact Or.inr rfl
      | cons _ _ => exact hkv.elim
  obtain ⟨hbb, hkpos⟩ := kidPos_not_loop (P := coreProgram) (fs := fs) (fp := fp) (bufs := allocs σ es) hl'
  have hdata : ∀ i, (Memory.Tree.node f σ (allocs σ es) ks).Data coreProgram fs cert fp i ↔
      ownData cert fp (fp + fs f) f (allocs σ es) es i ∨
        Tree.DataKids coreProgram fs cert (bases (fp + fs f + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos]
  refine ⟨Memory.Tree.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_, ?_, ?_, ?_,
    fun θ => by have := hkw θ; simp only [Tree.weight]; omega⟩
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

/-- **`relAtIn_of_walk_loop` within weights**: the node weighs its function's weight, its
callees' and its tail's (`bt`, nothing for the frame not entered). -/
theorem relAtInW_of_walk_loop {R D Dk Rt Dt : ℕ → Prop} {fp m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {c : Call}
    {bws : List (Θ → ℕ)} {bt : Θ → ℕ}
    (hf : coreProgram.find? f = some fn) (hl : coreProgram.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAtInW fs cert w rd Rt Dt (fp + fs f) m c.f (c.args.map σ) (c.rets.map σ) bt
      else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromInW fs cert w rd σ (fun i => R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i)
      (fun _ => False) cs bws (fp + fs f + m + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (c.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i ∨
      (c.taken = true ∧ Dt i)) :
    RelAtInW fs cert w rd R D fp (fs f + m + (allocs σ es).sum + N) f args rets
      fun θ => w θ f + (bws.map (· θ)).sum + bt θ := by
  have htk := takes_of_calls coreProgram_wf (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl, hkw⟩ := kids_of_kidsFromInW _ _ _ _ _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  obtain ⟨k, hkv', hkb', hkp', hkt, hkl', hkd', hkw'⟩ :=
    kid_ofInW (htk c (List.mem_append_right _ List.mem_cons_self))
      (show if c.taken then RelAtInW fs cert w rd Rt Dt (fp + fs f) m c.f (c.args.map σ) (c.rets.map σ) bt
        else m = fs c.f from htail)
  have hns : (ks ++ [k]).map (Tree.total fs) = ks.map (Tree.total fs) ++ [m] := by
    rw [List.map_append, List.map_singleton, hkt]
  have hbb : bufBase fs coreProgram.loop fp f ((ks ++ [k]).map (Tree.total fs)) = fp + fs f + m := by
    rw [hns]; simp [bufBase, hl]
  have hkpos : kidPos fs coreProgram.loop fp f (allocs σ es) ((ks ++ [k]).map (Tree.total fs)) =
      bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs)) ++ [fp + fs f] := by
    rw [kidPos, ite_eq_left hl, hbb, hns, List.dropLast_concat, List.getLast?_concat]
    rfl
  have hlen : (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))).length = ks.length := by
    rw [length_bases, List.length_map]
  have hdata : ∀ i, (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i ↔
      ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨
        Tree.DataKids coreProgram fs cert (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i ∨
        k.Data coreProgram fs cert (fp + fs f) i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos, dataKids_append hlen, dataKids_cons]
    simp only [not_dataKids_nil, or_false]
  refine ⟨Memory.Tree.node f σ (allocs σ es) (ks ++ [k]), rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, by rw [hc]; exact kidsValid_append hkv hkv'⟩, ?_, ?_, ?_, ?_, ?_,
    fun θ => ?_⟩
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
  · have hDk : ∀ i, Dk i → (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i := fun i h =>
      (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    have hDt : ∀ i, c.taken = true ∧ Dt i → (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i :=
      fun i h => (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))
    have hown : ∀ i, ownData cert fp (fp + fs f + m) f (allocs σ es) es i →
        (Memory.Tree.node f σ (allocs σ es) (ks ++ [k])).Data coreProgram fs cert fp i := fun i h => (hdata i).mpr (Or.inl h)
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
  · have h1 := hkw θ
    have h2 := hkw' θ
    simp only [Tree.weight, weightKids_append, Tree.weightKids]
    omega

end Compose

end
end LeanVM.Guest.B1.Main
