/-
  LeanVM.Guest.B1.Main.DupPops

  `main_loop0` and `main_loop1` (route S): every valid tree pops, iteration by iteration, the four words its heap hint reads at the claim table; on a memory holding `main`'s words those are the duplicate claims' cells.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsF
public import LeanVM.Guest.B1.Main.MainGoalsHKid
public import LeanVM.Guest.B1.Main.RawAtSP
public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.B1.Main.MainGoalsG

/-!
# The duplicate claims' loops, their pops

* `mfPop rd a b j`: iteration `j`'s entry, the four words at `a · (b·g^j)^4`;
* `mf_pops`: a valid tree of a function of `main_loop0`'s body from the counter `g^j` pops iterations `j ..< n`' entries;
* `mfL1_pops`, `mfL2_pops`: on a memory holding `main`'s words, every valid tree of `main_loop0` (`main_loop1`) at `main`'s arguments pops the duplicate leanXMSS (leanSPHINCS) claims' cells.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (claimCells)
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Da (limb0_gen_pow_mul)

@[expose] public section

/-- `main_loop0`'s and `main_loop1`'s atoms. -/
def mfA : List Stmt :=
  [.atom (.mul (.n 4) (.n 3) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)), .atom (.mul (.n 6) (.n 5) (.n 5)),
    .atom (.mul (.n 7) (.n 2) (.n 6)), .atom (.hint (.witness "dup_claims" (.heap (.n 7) 0 4))),
    .atom (.const (.n 8) (word 2 0)), .atom (.mul (.n 9) (.n 0) (.n 8)), .atom (.add (.n 10) (.n 9) (.n 1)),
    .atom (.const (.n 11) (word 2 0)), .atom (.mul (.n 12) (.n 0) (.n 11))]

/-- The body of `main_loop0` (`f` its name) before its return. -/
def mfPre (f : String) : List Stmt := mfA ++ [.callIf (.n 10) f [.n 12, .n 1, .n 2, .n 3]]

theorem mfL1_body : (coreProgram.getD idx% «main_loop0» default).body = mfPre name% «main_loop0» ++ [.ret []] := by
  rw [show (coreProgram.getD idx% «main_loop0» default).body = core% «main_loop0» body from rfl,
    core_eq% «main_loop0» body]
  rfl

theorem mfL2_body : (coreProgram.getD idx% «main_loop1» default).body = mfPre name% «main_loop1» ++ [.ret []] := by
  rw [show (coreProgram.getD idx% «main_loop1» default).body = core% «main_loop1» body from rfl,
    core_eq% «main_loop1» body]
  rfl

theorem mfL1_params : (coreProgram.getD idx% «main_loop0» default).params = [.n 0, .n 1, .n 2, .n 3] := rfl
theorem mfL2_params : (coreProgram.getD idx% «main_loop1» default).params = [.n 0, .n 1, .n 2, .n 3] := rfl

/-- **Iteration `j`'s entry**: the four words at `a · (b·g^j)^4`. -/
def mfPop (rd : Reader) (a b : E) (j : ℕ) : Pop :=
  ("dup_claims", (List.range 4).map fun k =>
    (rd ((a * (b * gen ^ j * (b * gen ^ j) * (b * gen ^ j * (b * gen ^ j)))).limb 0 * addressOfIndex (0 + k))).getD 0)

theorem mfPre_straight (f : String) : (mfPre f).all Main.Stmt.straight = true := rfl
theorem mfA_atoms : Sig.atomsOnly mfA = true := rfl

/-- **A valid tree of a function of `main_loop0`'s body**, from the counter `g^j` below `n`, pops iterations
`j ..< n`' entries. -/
theorem mf_pops {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3]) (hb : fn.body = mfPre f ++ [.ret []]) {n : ℕ} (hn : n < 2 ^ 34)
    (rd : Reader) (a b : E) :
    ∀ m j, j + m = n → 0 < m → ∀ (t : Tree) rets, t.name = f → t.Valid coreProgram rd [gen ^ j, gen ^ n, a, b] rets →
      t.pops coreProgram rd = (List.range' j m).map (mfPop rd a b) := by
  intro m
  induction m with
  | zero => intro j _ h; exact absurd h (Nat.lt_irrefl 0)
  | succ m ih =>
    intro j hjm _ t rets htn hv
    obtain ⟨f', σ, bufs, kids, rfl⟩ : ∃ f' σ bufs kids, t = .node f' σ bufs kids := by
      cases t with
      | node f' σ bufs kids => exact ⟨f', σ, bufs, kids, rfl⟩
      | phantom => exact hv.elim
    have htn' : f = f' := htn.symm
    subst htn'
    obtain ⟨fn', hf', hpar, es, vs, hw, -, hev, hkv⟩ := id hv
    rw [hf] at hf'
    cases hf'
    rw [hp] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨h0, h1, h2, h3⟩ := hpar
    have hws := Main.walk_straight σ [] (mfPre f) (mfPre_straight f)
    rw [← hb, hw] at hws
    obtain ⟨rfl, -⟩ := Out.ret.inj hws
    have hA : ∀ x, Stmt.atom x ∈ mfA → x.Holds rd σ := fun x hx =>
      hev (.atom x) (List.mem_flatMap.mpr ⟨.atom x, List.mem_append_left _ hx, List.mem_singleton_self _⟩)
    have h4 : σ (.n 4) = σ (.n 3) * σ (.n 0) := hA (.mul (.n 4) (.n 3) (.n 0)) (by simp [mfA])
    have h5 : σ (.n 5) = σ (.n 4) * σ (.n 4) := hA (.mul (.n 5) (.n 4) (.n 4)) (by simp [mfA])
    have h6 : σ (.n 6) = σ (.n 5) * σ (.n 5) := hA (.mul (.n 6) (.n 5) (.n 5)) (by simp [mfA])
    have h7 : σ (.n 7) = σ (.n 2) * σ (.n 6) := hA (.mul (.n 7) (.n 2) (.n 6)) (by simp [mfA])
    have h8 : σ (.n 8) = word 2 0 := hA (.const (.n 8) (word 2 0)) (by simp [mfA])
    have h9 : σ (.n 9) = σ (.n 0) * σ (.n 8) := hA (.mul (.n 9) (.n 0) (.n 8)) (by simp [mfA])
    have h10 : σ (.n 10) = σ (.n 9) + σ (.n 1) := hA (.add (.n 10) (.n 9) (.n 1)) (by simp [mfA])
    have h11 : σ (.n 11) = word 2 0 := hA (.const (.n 11) (word 2 0)) (by simp [mfA])
    have h12 : σ (.n 12) = σ (.n 0) * σ (.n 11) := hA (.mul (.n 12) (.n 0) (.n 11)) (by simp [mfA])
    have hcalls : calls ((mfPre f).flatMap (slEvs σ)) =
        [⟨f, [.n 12, .n 1, .n 2, .n 3], [], decide (σ (.n 10) ≠ 0)⟩] := by
      rw [(Main.straight_parts σ _ (mfPre_straight f)).2.2.2]
      rfl
    rw [hcalls] at hkv
    obtain ⟨k, rfl⟩ : ∃ k, kids = [k] := by
      match kids, hkv with
      | [k], _ => exact ⟨k, rfl⟩
    obtain ⟨hkn, hk, -⟩ := hkv
    have hsp : SplicePops rd σ (mfPre f) [k.pops coreProgram rd]
        (Sig.atomsPops rd σ mfA ++ k.pops coreProgram rd) :=
      (SplicePops.of_fallPops (Sig.fallPops_atoms σ mfA_atoms)).append (splicePops_callIf _ _ _ _)
    have e := Tree.pops_of_prefix (ks' := []) hv hf hb hsp rfl (by rw [Tree.popsKids, Tree.popsKids]; rfl)
    rw [List.flatten_nil, List.append_nil] at e
    rw [e, List.range'_succ, List.map_cons]
    have hσ7 : σ (.n 7) = a * (b * gen ^ j * (b * gen ^ j) * (b * gen ^ j * (b * gen ^ j))) := by
      rw [h7, h6, h5, h4, h0, h2, h3]
    have hpop : Sig.atomsPops rd σ mfA = [mfPop rd a b j] := by
      show [("dup_claims", (List.range 4).map fun k => (rd ((σ (.n 7)).limb 0 * addressOfIndex (0 + k))).getD 0)] = _
      rw [hσ7]
      rfl
    rw [hpop, List.singleton_append]
    refine congrArg (mfPop rd a b j :: ·) ?_
    have htk : decide (σ (.n 10) ≠ 0) = decide (j + 1 ≠ n) := by
      rw [h10, h9, h8, h0, h1]
      exact guard_taken hn (by omega)
    rw [htk] at hk
    rcases m with _ | m
    · have hn' : j + 1 = n := by omega
      simp only [hn', ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at hk
      obtain ⟨⟨f'', σ', rfl⟩, -⟩ := hk
      rw [Tree.pops]
      rfl
    · have hn' : j + 1 ≠ n := by omega
      simp only [hn', ne_eq, not_false_eq_true, decide_true, ↓reduceIte] at hk
      have ha : ([.n 12, .n 1, .n 2, .n 3] : List V).map σ = [gen ^ (j + 1), gen ^ n, a, b] := by
        simp only [List.map_cons, List.map_nil, h12, h11, h0, h1, h2, h3, word_gen, gen_pow_mul_gen]
      rw [ha] at hk
      exact ih (j + 1) (by omega) (by omega) k _ hkn hk

/-! ## Against the claim tables -/

theorem length_flatMap_four {α : Type} {cells : α → List E} (hc : ∀ x, (cells x).length = 4) :
    ∀ l : List α, (l.flatMap cells).length = 4 * l.length
  | [] => rfl
  | x :: l => by rw [List.flatMap_cons, List.length_append, hc, length_flatMap_four hc l, List.length_cons]; ring

/-- **The entries read off a claim table**: the table at `g^P` holding the cells of `L ++ D`, iterations `0 ..< |D|`
from `b = g^|L|` read `D`'s cells. -/
theorem mfPops_table {α : Type} {cells : α → List E} (hc : ∀ x, (cells x).length = 4) {L D : List α} {rd : Reader}
    {P : ℕ} (hR : ReadsAt rd (gen ^ P) ((L ++ D).flatMap cells)) :
    (List.range' 0 D.length).map (mfPop rd (gen ^ P) (gen ^ L.length)) = D.map fun c => ("dup_claims", cells c) := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.length_map, List.length_range'] at h1
  rw [List.getElem_map, List.getElem_range', List.getElem_map, mfPop, Nat.one_mul, Nat.zero_add]
  refine congrArg (Prod.mk "dup_claims") (List.ext_getElem (by simp [hc]) fun k k1 k2 => ?_)
  simp only [List.length_map, List.length_range] at k1
  rw [List.getElem_map, List.getElem_range]
  have hidx : 4 * (L.length + j) + k < ((L ++ D).flatMap cells).length := by
    rw [length_flatMap_four hc, List.length_append]
    omega
  have hld := (hR _ hidx).2
  rw [limb0_gen_pow_mul] at hld
  rw [← pow_add, gen4, ← pow_add, limb0_gen_pow_mul, Nat.zero_add, Nat.add_assoc, hld, Option.getD_some]
  have hu := getD_flatMap_uniform (f := cells) (w := 4) (L ++ D) (fun a _ => hc a) (L.length + j)
    (by rw [List.length_append]; omega) k k1
  rw [List.getD_eq_getElem _ _ hidx, List.getD_eq_getElem _ _ (by rw [hc]; exact k1)] at hu
  rw [hu]
  congr 2
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

variable {fs : String → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-- **`main_loop0` pops the duplicate leanXMSS claims' cells** on a memory holding `main`'s words. -/
theorem mfL1_pops (hl : GuestLimits s w) (hn : (hm fs fp seed s w).nxd ≠ 0) {rd : Reader}
    (hL : MemL rd (hLmain fs fp seed s w)) (t : Tree) (rets : List E) (htn : t.name = name% «main_loop0»)
    (hv : t.Valid coreProgram rd
      [1, gen ^ (hm fs fp seed s w).nxd, (hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx] rets) :
    t.pops coreProgram rd =
      (xPlan s w).duplicates.map fun c ↦ ("dup_claims", claimCells c.1.root c.1.parameter c.2) := by
  have hb := regions_lt hl
  have ed : (hm fs fp seed s w).nxd = (xPlan s w).duplicates.length := rfl
  have hX : rX s w = s.claims.xmss.length + (xPlan s w).duplicates.length := rfl
  have hv' : t.Valid coreProgram rd [gen ^ 0, gen ^ (xPlan s w).duplicates.length, gen ^ mfB fs fp seed s w 0,
      gen ^ s.claims.xmss.length] rets := by
    rw [pow_zero]; exact hv
  rw [mf_pops (Digest.find_of_idx mfL1_idx) mfL1_params mfL1_body (n := (xPlan s w).duplicates.length) (by omega) rd
    (gen ^ mfB fs fp seed s w 0) (gen ^ s.claims.xmss.length) (xPlan s w).duplicates.length 0 (by omega) (by omega) t rets
    htn hv']
  have hR := mf_reads fs fp seed s w hL (i := 0) (by omega)
  unfold hOwn at hR
  rw [List.getD_cons_zero] at hR
  have hc : ∀ c : LeanXmssClaim, (claimCells c.1.root c.1.parameter c.2).length = 4 := fun c =>
    mf_claimCells_length _ _ _
  exact mfPops_table hc hR

/-- **`main_loop1` pops the duplicate leanSPHINCS claims' cells** on a memory holding `main`'s words. -/
theorem mfL2_pops (hl : GuestLimits s w) (hn : (hm fs fp seed s w).nsd ≠ 0) {rd : Reader}
    (hL : MemL rd (hLmain fs fp seed s w)) (t : Tree) (rets : List E) (htn : t.name = name% «main_loop1»)
    (hv : t.Valid coreProgram rd
      [1, gen ^ (hm fs fp seed s w).nsd, (hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls] rets) :
    t.pops coreProgram rd =
      (sPlan s w).duplicates.map fun c ↦ ("dup_claims", claimCells c.1.publicSeed c.1.root c.2) := by
  have hb := regions_lt hl
  have ed : (hm fs fp seed s w).nsd = (sPlan s w).duplicates.length := rfl
  have hY : rY s w = s.claims.sphincs.length + (sPlan s w).duplicates.length := rfl
  have hv' : t.Valid coreProgram rd [gen ^ 0, gen ^ (sPlan s w).duplicates.length, gen ^ mfB fs fp seed s w 1,
      gen ^ s.claims.sphincs.length] rets := by
    rw [pow_zero]; exact hv
  rw [mf_pops (Digest.find_of_idx mfL2_idx) mfL2_params mfL2_body (n := (sPlan s w).duplicates.length) (by omega) rd
    (gen ^ mfB fs fp seed s w 1) (gen ^ s.claims.sphincs.length) (sPlan s w).duplicates.length 0 (by omega) (by omega) t rets
    htn hv']
  have hR := mf_reads fs fp seed s w hL (i := 1) (by omega)
  unfold hOwn at hR
  rw [List.getD_cons_succ, List.getD_cons_zero] at hR
  have hc : ∀ c : LeanSphincsClaim, (claimCells c.1.publicSeed c.1.root c.2).length = 4 := fun c =>
    mf_claimCells_length _ _ _
  exact mfPops_table hc hR

end
end LeanVM.Guest.B1.Main
