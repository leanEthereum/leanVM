/-
  LeanVM.Guest.B1.Merkle.CapPops

  The witness-stream entries `verify_merkle_cap` and `level_queries` pop: none for the former; the cap and its flags (`merkle_caps`, `merkle_cap_active`) for the latter, then its callees'.
-/

module

public import LeanVM.Guest.B1.Opening.WalkPops
public import LeanVM.Guest.B1.Merkle.Cap
public import LeanVM.Guest.B1.Whir.HelperT

/-!
# A level's cap pops

* `mc_node_pops`: a call instance of `verify_merkle_cap` pops nothing, whatever its valuation;
* `capPops`: the cap's `4·2^cd` cells and the flags' `2^cd`, read through their pointers;
* `lq_node_pops`: a call instance of `level_queries` pops `capPops`, then its two callees' entries.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- A branch both of whose sides are atoms without witness hints pops nothing. -/
theorem fallPops_ite_noWit {c : V} {z n : List Stmt} (hz : noWit z = true) (hn : noWit n = true) :
    FallPops rd σ [.ite c z n] [] :=
  FallPops.ite (by split; exacts [fallPops_noWit σ hz, fallPops_noWit σ hn])

theorem mcNode_fallPops (L k b : ℕ) : FallPops rd σ (mcNode L k b) [] := by
  unfold mcNode
  refine fallPops_eq ((FallPops.atom _).append (fallPops_ite_noWit (by split <;> rfl) rfl)) rfl

theorem fallPops_flatten_map_nil {α : Type} {f : α → List Stmt} :
    ∀ {l : List α}, (∀ a ∈ l, FallPops rd σ (f a) []) → FallPops rd σ (l.map f).flatten []
  | [], _ => FallPops.nil
  | a :: l, h => by
    rw [List.map_cons, List.flatten_cons]
    exact fallPops_eq ((h a (by simp)).append (fallPops_flatten_map_nil fun b hb => h b (by simp [hb]))) rfl

/-- **`verify_merkle_cap` pops nothing.** -/
theorem mc_node_pops {P : Core.Program} {name : String} {fn : Fn} (hf : P.find? name = some fn) {L : ℕ}
    (hb : fn.body = mcBody L) (τ : Val) (bufs : List ℕ) (kids : List Tree) :
    (Memory.Tree.node name τ bufs kids).pops P rd = [] := by
  have hx : FallPops rd τ (((List.range (4 * L - 2)).map fun i ↦ [.atom (.load (.n (i + 2)) (.n 0) (i + 2))]).flatten ++
      [.atom (.const (.n (mcP L)) (word 1 0)), .atom (.const (.n (mcP L + 1)) (word 0 0)),
        .atom (.const (.n (mcP L + 2)) (word 0 0)), .atom (.const (.n (mcP L + 3)) (word 0 0)),
        .atom (.const (.n (mcP L + 4)) (word 0 0)), .atom (.const (.n (mcP L + 5)) w63),
        keccakA (mcIns L 1 (mcP L + 5)) (mcOuts 1)] ++
      ((List.range (L - 2)).map fun j ↦ mcNode L (j + 2) (mcBase L (j + 2))).flatten ++
      [.atom (.copy (.n (mcBase L L)) (.n 2)), .atom (.copy (.n (mcBase L L + 1)) (.n 3))]) [] :=
    fallPops_eq ((((fallPops_noWit τ (noWit_flatten_map fun _ _ => rfl)).append (fallPops_noWit τ rfl)).append
      (fallPops_flatten_map_nil fun _ _ => mcNode_fallPops _ _ _)).append (fallPops_noWit τ rfl)) rfl
  obtain ⟨es, hw, hc, hp⟩ := retPops_of_fallPops (vs := [.n (mcBase L L), .n (mcBase L L + 1)]) hx
  rw [Tree.pops_node hf (by rw [hb, mcBody]; simpa [List.append_assoc] using hw)]
  have := splice_append_of_calls_nil (rd := rd) (σ := τ) (es := es) [] (Tree.popsKids P rd kids) hc
  rw [List.append_nil] at this
  rw [this, hp]
  simp [splice]

/-! ## `level_queries` -/

theorem osPowSteps_noWit (x : ℕ) : ∀ (ds : List Bool) (acc k : ℕ), noWit (osPowSteps x ds acc k).1 = true
  | [], _, _ => rfl
  | d :: ds, acc, k => by
    unfold osPowSteps
    split
    · show noWit ([osMul k acc acc, osMul (k + 1) k x] ++ _) = true
      rw [noWit_append, osPowSteps_noWit x ds]; rfl
    · show noWit ([osMul k acc acc] ++ _) = true
      rw [noWit_append, osPowSteps_noWit x ds]; rfl

/-- **The cap's and the flags' entries**: `4·2^cd` cells at the cap's pointer `.n 7`, `2^cd` at the flags' `.n 9`. -/
def capPops (rd : Reader) (σ : Val) (cd : ℕ) : List Pop :=
  [("merkle_caps", Dest.words rd σ (.heap (.n 7) 0 (4 * 2 ^ cd))),
    ("merkle_cap_active", Dest.words rd σ (.heap (.n 9) 0 (2 ^ cd)))]

/-- **`level_queries` pops the cap and its flags, then its callees' entries** (`verify_merkle_cap`'s, `opening_queries`'). -/
theorem lq_node_pops {P : Core.Program} {name : String} {fn : Fn} (hf : P.find? name = some fn)
    {q base folds leaf d cd mu nhs hbits fin : ℕ} (hb : fn.body = lqBody q base folds leaf d cd mu nhs hbits fin)
    (τ : Val) (bufs : List ℕ) {kids : List Tree} {kc ko : List Pop} (hk : Tree.popsKids P rd kids = [kc, ko]) :
    (Memory.Tree.node name τ bufs kids).pops P rd = capPops rd τ cd ++ kc ++ ko := by
  have hx : SplicePops rd τ (osHeap (4 * 2 ^ cd) 6 ++
      [.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))] ++
      osHeap (2 ^ cd) 8 ++
      [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd))))] ++
      [.call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11]] ++
      [osCst 12 (gw (if base = 1 then q / 2 else q))] ++
      [.call (oqName q base folds leaf d cd mu nhs hbits fin) [.n 7, .n 9, .n 1, .n 2, .n 3, .n 4, .n 5, .n 12]
        [.n 13]] ++
      ([osCp 14 10, osCp 15 11, osCp 16 13] ++ (osPowSteps 0 (osPowDigits q) 0 17).1 ++
        [osCp (17 + osPowLen q) (osPowSteps 0 (osPowDigits q) 0 17).2]))
      (Tree.popsKids P rd kids) (capPops rd τ cd ++ kc ++ ko) := by
    rw [hk]
    have h : SplicePops rd τ (((((((osHeap (4 * 2 ^ cd) 6 ++
        [.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))]) ++
        osHeap (2 ^ cd) 8) ++ [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd))))]) ++
        [.call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11]]) ++
        [osCst 12 (gw (if base = 1 then q / 2 else q))]) ++
        [.call (oqName q base folds leaf d cd mu nhs hbits fin) [.n 7, .n 9, .n 1, .n 2, .n 3, .n 4, .n 5, .n 12]
          [.n 13]]) ++
        ([osCp 14 10, osCp 15 11, osCp 16 13] ++ (osPowSteps 0 (osPowDigits q) 0 17).1 ++
          [osCp (17 + osPowLen q) (osPowSteps 0 (osPowDigits q) 0 17).2]))
        ([] ++ [] ++ [] ++ [] ++ [kc] ++ [] ++ [ko] ++ [])
        ([] ++ [("merkle_caps", Dest.words rd τ (.heap (.n 7) 0 (4 * 2 ^ cd)))] ++ [] ++
          [("merkle_cap_active", Dest.words rd τ (.heap (.n 9) 0 (2 ^ cd)))] ++ kc ++ [] ++ ko ++ []) :=
      (((((((SplicePops.of_fallPops (fallPops_noWit τ rfl)).append (SplicePops.of_fallPops (FallPops.atom _))).append
        (SplicePops.of_fallPops (fallPops_noWit τ rfl))).append (SplicePops.of_fallPops (FallPops.atom _))).append
        (SplicePops.call _ _ _ kc)).append (SplicePops.of_fallPops (fallPops_noWit τ rfl))).append
        (SplicePops.call _ _ _ ko)).append (SplicePops.of_fallPops (fallPops_noWit τ (by
          rw [noWit_append, noWit_append, osPowSteps_noWit]; rfl)))
    have h' := SplicePops.congr_pops (SplicePops.congr_ks h (ks' := [kc, ko]) (by simp))
      (q := capPops rd τ cd ++ kc ++ ko) (by simp [capPops])
    simpa only [List.append_assoc] using h'
  obtain ⟨es, -, he⟩ := Tree.pops_of_splice (bufs := bufs) hf (ys := [.ret [.n 14, .n 15, .n 16,
      .n (17 + osPowLen q)]])
    (by rw [hb, lqBody]; simp [List.append_assoc]) hx (es := []) (vs := [.n 14, .n 15, .n 16, .n (17 + osPowLen q)])
    (by simp [walk, walk1, Out.seq]) rfl
  rw [he]; simp [evPops]

end
end LeanVM.Guest.B1
