/-
  LeanVM.Guest.B1.Main.WeightB

  Bounded trees within weights: a tree weighs at most its words at the same frame sizes, so a
  bound on the words of every valid tree, at every frame size, bounds the weight; and callees
  bounded by a function of the `Kid`.
-/

module

public import LeanVM.Guest.B1.Main.WeightLoop

/-!
# Bounded trees, within weights

`weight_le_total`: a tree weighs at most the words it allocates at `ω`, a phantom nothing and a
`HeapBuf` nothing. `CompleteAtB.toW_total` and `CompleteAtB.toW_memTot`: a `CompleteAtB` whose
valid trees allocate at most `Bw θ` words at the frame sizes `w θ` (on every memory holding
`Lin`, for the second) is `CompleteAtW` within `Bw`. `CompleteAtB.toWE`: at no weights at all
(`Θ := Empty`), every `CompleteAtB` is one. `kidsFromInW_of_kidsBW`: `kidsFromIn_of_kidsB` within
weights, a skipped callee weighing nothing (`kidsBoundW`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 (DisjL Within LowDef CompleteAtB Kid CallsMatch OutsOk OutsIn RegionsOk outRegion
  kidsBound)

@[expose] public section

mutual
/-- **A tree weighs at most its words** at the same frame sizes. -/
theorem weight_le_total (ω : String → ℕ) : ∀ t : Tree, t.weight ω ≤ t.total ω
  | .node f σ bufs kids => by
      rw [Tree.weight, total_node]
      have := weightKids_le_totalKids ω kids
      omega
  | .phantom .. => by simp [Tree.weight]

theorem weightKids_le_totalKids (ω : String → ℕ) : ∀ ks : List Tree,
    Tree.weightKids ω ks ≤ Tree.totalKids ω ks
  | [] => by simp [Tree.weightKids, Tree.totalKids]
  | k :: ks => by
      rw [Tree.weightKids, totalKids_cons]
      have := weight_le_total ω k
      have := weightKids_le_totalKids ω ks
      omega
end

variable {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}

/-- **Every `CompleteAtB` is `CompleteAtW` at no weights.** -/
theorem CompleteAtB.toWE {w : Empty → String → ℕ} {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Empty → ℕ} (h : CompleteAtB fs cert κ f Lin args Out B) :
    CompleteAtW fs cert w κ f Lin args Out B Bw :=
  CompleteAtB.toW h fun θ => θ.elim

/-- **A `CompleteAtB` within the words of its valid trees** at the frame sizes `w θ`. -/
theorem CompleteAtB.toW_total {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} (h : CompleteAtB fs cert κ f Lin args Out B)
    (hT : ∀ θ (rd : Reader) (t : Tree) (rets : List E), t.name = f → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.total (w θ) ≤ Bw θ) :
    CompleteAtW fs cert w κ f Lin args Out B Bw :=
  CompleteAtB.toW h fun θ rd t rets hn hv hb => (weight_le_total _ t).trans (hT θ rd t rets hn hv hb)

/-- **A `CompleteAtB` within the words of its valid trees on the memories holding `Lin`.** -/
theorem CompleteAtB.toW_memTot {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} (h : CompleteAtB fs cert κ f Lin args Out B)
    (hT : ∀ θ (rd : Reader), MemL rd Lin → ∀ (t : Tree) (rets : List E), t.name = f →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → t.total (w θ) ≤ Bw θ) :
    CompleteAtW fs cert w κ f Lin args Out B Bw := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, a, b, c, d, e, f', g⟩ := hr rd hl hm
    ⟨t, a, b, c, d, e, f', g, fun θ => (weight_le_total _ t).trans
      (hT θ rd (memL_append.mp hm).2 t rets a b c)⟩⟩

theorem CompleteAtW.bmono {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B B' : ℕ} {Bw : Θ → ℕ} (h : CompleteAtW fs cert w κ f Lin args Out B Bw)
    (hB : B ≤ B') : CompleteAtW fs cert w κ f Lin args Out B' Bw := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn.trans hB, hr⟩

/-- The callees' weights: an entered one's `bdw`, a skipped one nothing. -/
def kidsBoundW (bdw : Kid → Θ → ℕ) (ks : List Kid) (θ : Θ) : ℕ :=
  (ks.map fun k => if k.taken = true then bdw k θ else 0).sum

theorem kidsBoundW_le_kidsBound (bdw : Kid → Θ → ℕ) (θ : Θ) (ω : String → ℕ) (bd : Kid → ℕ)
    (h : ∀ k, bdw k θ ≤ bd k) (ks : List Kid) : kidsBoundW bdw ks θ ≤ kidsBound ω bd ks := by
  unfold kidsBoundW kidsBound
  refine List.sum_le_sum fun k _ => ?_
  split
  · exact h k
  · exact Nat.zero_le _

/-- The callees' weights, one per callee. -/
def kidsWs (bdw : Kid → Θ → ℕ) (ks : List Kid) : List (Θ → ℕ) :=
  ks.map fun k θ => if k.taken = true then bdw k θ else 0

theorem kidsWs_sum (bdw : Kid → Θ → ℕ) (ks : List Kid) (θ : Θ) :
    ((kidsWs bdw ks).map (· θ)).sum = kidsBoundW bdw ks θ := by
  simp only [kidsWs, kidsBoundW, List.map_map, Function.comp_def]

theorem kidsW_of (κ : ℕ) (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) : ∀ ks : List Kid,
    (∀ k ∈ ks, k.taken = true → CompleteAtW fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k)) →
    KidsW fs cert w κ ks (ks.map fun k => if k.taken = true then bd k else fs k.f) (kidsWs bdw ks)
  | [], _ => trivial
  | k :: ks, h => by
      refine ⟨fun ht => ?_, fun ht => ?_, kidsW_of κ bd bdw ks fun k' hk' => h k' (by simp [hk'])⟩
      · simp only [ht, ↓reduceIte]
        exact (h k (by simp) ht).wmono fun θ => by simp
      · simp [ht]

theorem kidsWs_length (bdw : Kid → Θ → ℕ) (ks : List Kid) : (kidsWs bdw ks).length = ks.length := by
  simp [kidsWs]

theorem callsMatch_length {σ : Val} : ∀ {cs : List Call} {ks : List Kid} {outs : List (List E × Layout)},
    CallsMatch σ cs ks outs → cs.length = ks.length
  | [], [], [], _ => rfl
  | _ :: _, _ :: _, _ :: _, ⟨_, _, _, h⟩ => by simp [callsMatch_length h]
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | [], [], _ :: _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-- **`kidsFromIn_append` within weights**, the weights of the first callees one per callee. -/
theorem kidsFromInW_append {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs1 cs2 : List Call) (bws1 bws2 : List (Θ → ℕ)) (Dacc : ℕ → Prop) (b n1 n2 : ℕ) (D1 D : ℕ → Prop),
      bws1.length = cs1.length →
      KidsFromInW fs cert w rd σ R Dacc cs1 bws1 b n1 D1 →
      (∀ Dacc' : ℕ → Prop, (∀ i, D1 i → Dacc' i) →
        KidsFromInW fs cert w rd σ R Dacc' cs2 bws2 (b + n1) n2 D) →
      KidsFromInW fs cert w rd σ R Dacc (cs1 ++ cs2) (bws1 ++ bws2) b (n1 + n2) D
  | [], cs2, [], bws2, Dacc, b, n1, n2, D1, D, _, ⟨hn, hD⟩, h2 => by
    subst hn; simpa using h2 Dacc hD
  | [], _, _ :: _, _, _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: _, _, [], _, _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: cs1, cs2, _ :: bws1, bws2, Dacc, b, n1, n2, D1, D, hl, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩, h2 =>
    ⟨m, n' + n2, Rk, Dk, by omega, hR, hc,
      kidsFromInW_append cs1 cs2 bws1 bws2 _ (b + m) n' n2 D1 D (by simpa using hl) hk fun Dacc' h => by
        rw [show b + m + n' = b + n1 by omega]; exact h2 Dacc' h⟩

/-- **`kidsFromIn_of_kidsB` within weights**: each entered callee within `bdw`. -/
theorem kidsFromInW_of_kidsBW (κ : ℕ) (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (ks : List Kid)
    (hok : ∀ k ∈ ks, k.taken = true → CompleteAtW fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      DisjL L ∧ N ≤ kidsBound fs bd ks ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInW fs cert w rd σ R Dacc cs (kidsWs bdw ks) b N (fun i => Dacc i ∨ outRegion ks outs i) :=
  kidsFromInW_of_kidsW κ ks _ _ (kidsW_of κ bd bdw ks hok) b

end
end LeanVM.Guest.B1.Main
