/-
  LeanVM.Guest.B1.Main.L5Pops

  The entries every valid tree of `main`'s children loop (`main_loop4`) of the honest shape pops: per child, its counts (`child_meta`), its two claim lists' digests', its deferred claim (`child_defer`) and DA digest (`child_da`) as the memory holds them, `verify_sub`'s.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T
public import LeanVM.Guest.B1.Main.MainPops
public import LeanVM.Guest.B1.Main.MainNoWit
public import LeanVM.Guest.B1.Digest.ClaimListPops

/-!
# The children loop's pops

* `l5Seg`: child `c`'s entries, its callees' given;
* `l5_popS`, `l5_chk`: `main_loop4`'s body's skeleton of entries and the products its proof reads, by the kernel;
* `l5From_pops`: a valid tree of `L5From` (`main_loop4` from child `c` to the count `nk`), its callees' predicates giving their entries, pops each child's `l5Seg` in order.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest (valid_holds words_heap monoIs monoIs_sound genMulOk genMul_sound isAddAt add_sound
  atomsIn atoms_of_flat holdsList_flat)

@[expose] public section

variable {rd : Reader}

/-- **Child `c`'s entries in `main_loop4`**: its counts, its claim lists' digests' `px`, `ps`, its deferred claim and DA
digest, `verify_sub`'s `pv`. -/
def l5Seg (ex es : ℕ) (px ps : List Pop) (defer : List E) (da : E × E) (pv : List Pop) : List Pop :=
  ("child_meta", [gen ^ ex, gen ^ es]) :: (px ++ ps ++ [("child_defer", defer), ("child_da", [da.1, da.2])] ++ pv)

theorem l5_popS : (l5Pre ++ [l5Tail]).filterMap Stmt.popS = [some ("child_meta", .stack [.n 18, .n 19]), none, none,
    some ("child_defer", .heap (.n 33) 0 24), some ("child_da", .heap (.n 35) 0 2), none, none, none] := by
  decide +kernel

theorem l5_chk : l5Pre.all Digest.Stmt.flat = true ∧ monoIs (atomsIn l5Pre) (.n 33) (.n 9) (.n 0) 24 = true ∧
    monoIs (atomsIn l5Pre) (.n 35) (.n 10) (.n 0) 2 = true ∧ genMulOk (atomsIn l5Pre) (.n 55) (.n 0) = true ∧
    genMulOk (atomsIn l5Pre) (.n 52) (.n 0) = true ∧ (atomsIn l5Pre).any (isAddAt (.n 53) (.n 52) (.n 1)) = true := by
  decide +kernel

/-- A heap destination through `g^a` of a run the memory holds reads the run. -/
theorem words_of_reads (σ : Val) {p : V} {a : ℕ} (hp : σ p = gen ^ a) {L : List E} (h : ReadsAt rd (gen ^ a) L) :
    Dest.words rd σ (.heap p 0 L.length) = L := by
  rw [words_heap σ hp]
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, Nat.zero_add]
  obtain ⟨-, hl⟩ := h k h2
  rw [gen_pow_eq_ofK, addr_ofK] at hl
  rw [hl]
  rfl

theorem l5_tail_args (σ : Val) : ([V.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12,
    .n 13, .n 14, .n 15] : List V).map σ = σ (.n 55) :: ((List.range 16).map V.n).tail.map σ := rfl

/-- **A valid tree of `main_loop4` from child `c`** (`L5From`), its callees' predicates giving their entries `px`,
`ps`, `pv`, the deferred claims and DA digests in memory: it pops each child's `l5Seg` up to the count `nk`. -/
theorem l5From_pops {ex es : ℕ → ℕ} {Pxs Pss Pvs : ℕ → Tree → Prop} {px ps pv : ℕ → List Pop}
    {defer : ℕ → List E} {da : ℕ → E × E}
    (hpx : ∀ c t, Pxs c t → t.pops coreProgram rd = px c) (hps : ∀ c t, Pss c t → t.pops coreProgram rd = ps c)
    (hpv : ∀ c t, Pvs c t → t.pops coreProgram rd = pv c)
    {nk Cr D : ℕ} {rest : List E} (hnk34 : nk < 2 ^ 34) (hnk : rest.getD 0 0 = gen ^ nk)
    (hCr : rest.getD 8 0 = gen ^ Cr) (hD : rest.getD 9 0 = gen ^ D)
    (hmem : ∀ c < nk, (defer c).length = 24 ∧ ReadsAt rd (gen ^ (Cr + 24 * c)) (defer c) ∧
      LoadHolds rd (gen ^ D) (2 * c) (da c).1 ∧ LoadHolds rd (gen ^ D) (2 * c + 1) (da c).2) :
    ∀ m c (t : Tree) (rets : List E), c + m = nk → t.Valid coreProgram rd (gen ^ c :: rest) rets →
      L5From ex es Pxs Pss Pvs m c t →
      t.pops coreProgram rd = (List.range' c m).flatMap fun c =>
        l5Seg (ex c) (es c) (px c) (ps c) (defer c) (da c) (pv c) := by
  intro m
  induction m with
  | zero => intro _ _ _ _ _ h; exact h.elim
  | succ m ih =>
  intro c t rets hcm hv hL
  obtain ⟨σ, bufs, ks, rfl, h18, h19, hcl, hK⟩ := hL
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
  -- the valuation
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
  have h9 : σ (.n 9) = gen ^ Cr := (pr 9 (by omega)).trans hCr
  have h10 : σ (.n 10) = gen ^ D := (pr 10 (by omega)).trans hD
  rw [l5_body, holdsList_append] at hb
  obtain ⟨hflat, hm33, hm35, hg55, hg52, ha53⟩ := l5_chk
  obtain ⟨hall, -⟩ := holdsList_flat _ hflat _ _ hb
  have hat := atoms_of_flat hall
  have h33 : σ (.n 33) = gen ^ (Cr + 24 * c) := by
    rw [monoIs_sound hm33 hat, h9, h0, ← pow_mul, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have h35 : σ (.n 35) = gen ^ (D + 2 * c) := by
    rw [monoIs_sound hm35 hat, h10, h0, ← pow_mul, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have h55 : σ (.n 55) = gen ^ (c + 1) := by rw [genMul_sound hg55 hat, h0, pow_succ]
  have h53 : σ (.n 53) = gen ^ (c + 1) + gen ^ nk := by
    rw [add_sound ha53 hat, genMul_sound hg52 hat, h0, h1, pow_succ]
  obtain ⟨hdl, hdef, hd0, hd1⟩ := hmem c (by omega)
  have hda : ReadsAt rd (gen ^ (D + 2 * c)) [(da c).1, (da c).2] := by
    intro k hk
    rw [pow_add, loadHolds_mul_gen_pow]
    match k, hk with
    | 0, _ => exact hd0
    | 1, _ => exact hd1
  -- the callees
  obtain ⟨kx, ks', kst, kv, kt, rfl⟩ : ∃ kx ks' kst kv kt, ks = [kx, ks', kst, kv, kt] := by
    have := kidsValid_len hkv
    simp only [l5CallList, List.length_cons, List.length_nil] at this
    match ks, this with
    | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩
  obtain ⟨-, -, -, -, hn3, hv3, -, -, -, hvt, -⟩ := hkv
  obtain ⟨hTx, hTs, -, hTv, hTt, -⟩ := hK
  have px' := hpx c kx (hTx rfl)
  have ps' := hps c ks' (hTs rfl)
  have pv' := hpv c kv (hTv rfl)
  have pst : kst.pops coreProgram rd = [] := pops_nil_of_noWitness statement_digest_noWit
    (show kst.Valid coreProgram rd _ _ from hv3) hn3 rd
  have pt : kt.pops coreProgram rd = (List.range' (c + 1) m).flatMap fun c =>
      l5Seg (ex c) (es c) (px c) (ps c) (defer c) (da c) (pv c) := by
    by_cases h0' : σ (.n 53) = 0
    · have hcm' : c + 1 = nk := by
        rw [h53] at h0'
        exact Digest.gen_pow_inj' (by omega) hnk34 (e_add_eq_zero_iff.mp h0')
      rw [show m = 0 by omega, List.range'_zero, List.flatMap_nil]
      have : (decide (σ (.n 53) ≠ 0)) = false := by simpa using h0'
      simp only [this, Bool.false_eq_true, ↓reduceIte] at hvt
      obtain ⟨⟨g, σ', rfl⟩, -⟩ := hvt
      rfl
    · have ht : (decide (σ (.n 53) ≠ 0)) = true := by simpa using h0'
      simp only [ht, ↓reduceIte] at hvt
      rw [l5_tail_args, h55, hrest] at hvt
      exact ih (c + 1) kt [] (by omega) hvt (hTt ht)
  rw [Tree.pops_node (find_l5) hw', l5Evs, splice_straight _ l5Pre_straight, l5_popS]
  simp only [spliceS, Tree.popsKids, List.headD_cons, List.tail_cons]
  rw [px', ps', pst, pv', pt, List.range'_succ, List.flatMap_cons, l5Seg]
  have w1 : Dest.words rd σ (.stack [.n 18, .n 19]) = [gen ^ ex c, gen ^ es c] := by
    show [σ (.n 18), σ (.n 19)] = _
    rw [h18, h19]
  have w2 : Dest.words rd σ (.heap (.n 33) 0 24) = defer c := by
    rw [← hdl]; exact words_of_reads σ h33 hdef
  have w3 : Dest.words rd σ (.heap (.n 35) 0 2) = [(da c).1, (da c).2] :=
    words_of_reads σ h35 hda
  rw [w1, w2, w3]
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

end
end LeanVM.Guest.B1.Main
