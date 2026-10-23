/-
  LeanVM.Guest.B1.Main.HonestChild

  A child's iteration on `main`'s honest words: its claim lists read at their slots and marking
  them, its DA roots, its deferred cells, its public input and its proof's run (`ChildWordsOk`).
-/

module

public import LeanVM.Guest.B1.Main.HonestMain

/-!
# A child, honestly

Child `c`'s claims are its region's writers from `hrx + Σ_{c' < c} n_x(c')` on (`writersX_child`),
numbered from `hbase c` (`gX_child`): each marks its slot with its number and the slot holds its
cells, so `child_claim_list_digest`'s precondition holds at the claims' slots (`hon_ccx`,
`hon_ccs`); its DA claims likewise for `cover_da_root` (`hon_childCov`). `hon_child`: the whole
`ChildWordsOk`, its proof's run given (`VsGood`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct)
open LeanVM.Guest.End (Limits coverage)
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Digest (SquaresAt CellsAt)

@[expose] public section

theorem getD_flatMap_const {β γ : Type} (f : γ → List β) (m : ℕ) (hf : ∀ a, (f a).length = m)
    (d : β) : ∀ (l : List γ) (i k : ℕ) (hi : i < l.length), k < m →
      (l.flatMap f).getD (m * i + k) d = (f (l[i]'hi)).getD k d
  | [], _, _, h, _ => absurd h (by simp)
  | a :: l, 0, k, _, hk => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hf]; omega)]
    simp [List.getD_eq_getElem?_getD]
  | a :: l, i + 1, k, hi, hk => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hf]; nlinarith), hf,
      show m * (i + 1) + k - m = m * i + k by rw [Nat.mul_succ]; omega, ← List.getD_eq_getElem?_getD,
      getD_flatMap_const f m hf d l i k (by simpa using hi) hk]
    simp

variable (fs : String → ℕ) {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
  {rd : Reader}

theorem list4 {l : List E} (h : l.length = 4) : [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] = l := by
  match l, h with
  | [_, _, _, _], _ => rfl

theorem hon_child_eq {c : ℕ} (hc : c < w.children.length) :
    (honestWords seed s w).child c = childWordsOf seed w.children[c] (hbase s w c) := by
  simp [honestWords, hc]

theorem sum_take_lt {γ : Type} (g : γ → ℕ) (L : List γ) {c : ℕ} (hc : c < L.length) :
    ((L.take c).map g).sum + g L[c] ≤ (L.map g).sum := by
  rw [← sum_take_succ g L c hc]; exact sum_take_map_le g L (c + 1)

/-! ## The claim lists -/

theorem hon_ccx (hlim : Limits s w) {c : ℕ} (hc : c < w.children.length)
    (hL : MemL rd (mainIn fs fp (honestWords seed s w))) :
    CclPreAt (fun j => (planX s w).1.getD (hrx s w + ((w.children.take c).map cnx).sum + j) 0)
      (w.children[c].statement.claims.xmss.flatMap xCellsOf) rd
      [mainPtr fs fp (honestWords seed s w) 1, mainPtr fs fp (honestWords seed s w) 4,
        gen ^ hbase s w c, 1, gen ^ s.claims.xmss.length * gen ^ (planX s w).2.length,
        gen ^ cnx w.children[c], ofK (gpow (mainExpBase fs fp (honestWords seed s w) + 34))]
      [(digestScalars (xmssListDigest w.children[c].statement.claims.xmss)).1,
        (digestScalars (xmssListDigest w.children[c].statement.claims.xmss)).2] := by
  have ht := honest_total (seed := seed) hlim
  simp only [MainWords.total, honestWords] at ht
  have hl := (hlim.lists _ (List.getElem_mem hc)).1
  have hlen := writersX_length hlim
  rw [writersX_len] at hlen
  have hsum := sum_take_lt cnx w.children hc
  refine ⟨squaresAt_of_mainIn fs hL, ⟨_, by omega, (pow_add _ _ _).symm⟩, cnx w.children[c], hl, rfl,
    length_flatMap_const _ 4 _ fun x _ => xCellsOf_length x, fun j hj => ?_, xCellsOf_canonical _, ?_⟩
  · have hr : hrx s w + ((w.children.take c).map cnx).sum + j < (writersX s w).length := by
      rw [writersX_len]; omega
    obtain ⟨hs, hm⟩ := hon_markX fs (seed := seed) (fp := fp) hr
    rw [gX_child hc hj] at hm
    refine ⟨⟨s.claims.xmss.length + (planX s w).2.length, by omega, (pow_add _ _ _).symm, hs⟩, ?_, ?_⟩
    · rw [one_mul, loadHolds_mul_gen_pow, Nat.add_zero, ← pow_add]
      exact hm.load hL
    · have he := hon_xEntry fs hL hr ((writersX_child (s := s) hc hj).trans (List.getElem?_eq_getElem hj))
      have g : ∀ k < 4, (w.children[c].statement.claims.xmss.flatMap xCellsOf).getD (4 * j + k) 0 =
          (xCellsOf (w.children[c].statement.claims.xmss[j]'hj)).getD k 0 := fun k hk =>
        getD_flatMap_four _ xCellsOf_length 0 _ j k hj hk
      have g0 : (w.children[c].statement.claims.xmss.flatMap xCellsOf).getD (4 * j) 0 =
          (xCellsOf (w.children[c].statement.claims.xmss[j]'hj)).getD 0 0 := by simpa using g 0 (by omega)
      rw [g0, g 1 (by omega), g 2 (by omega), g 3 (by omega), ← list4 (xCellsOf_length _)]
      exact he
  · rw [xCellsOf_bytes]; rfl

theorem hon_ccs (hlim : Limits s w) {c : ℕ} (hc : c < w.children.length)
    (hL : MemL rd (mainIn fs fp (honestWords seed s w))) :
    CclPreAt (fun j => (planS s w).1.getD (hrs s w + ((w.children.take c).map cns).sum + j) 0)
      (w.children[c].statement.claims.sphincs.flatMap sCellsOf) rd
      [mainPtr fs fp (honestWords seed s w) 2, mainPtr fs fp (honestWords seed s w) 4,
        gen ^ hbase s w c * gen ^ cnx w.children[c],
        gen ^ s.claims.xmss.length * gen ^ (planX s w).2.length,
        gen ^ s.claims.sphincs.length * gen ^ (planS s w).2.length,
        gen ^ cns w.children[c], ofK (gpow (mainExpBase fs fp (honestWords seed s w) + 34))]
      [(digestScalars (sphincsListDigest w.children[c].statement.claims.sphincs)).1,
        (digestScalars (sphincsListDigest w.children[c].statement.claims.sphincs)).2] := by
  have ht := honest_total (seed := seed) hlim
  simp only [MainWords.total, honestWords] at ht
  have hl := (hlim.lists _ (List.getElem_mem hc)).2
  have hlen := writersS_length hlim
  rw [writersS_len] at hlen
  have hsum := sum_take_lt cns w.children hc
  refine ⟨squaresAt_of_mainIn fs hL, ⟨_, by omega, (pow_add _ _ _).symm⟩, cns w.children[c], hl, rfl,
    length_flatMap_const _ 4 _ fun x _ => sCellsOf_length x, fun j hj => ?_, sCellsOf_canonical _, ?_⟩
  · have hr : hrs s w + ((w.children.take c).map cns).sum + j < (writersS s w).length := by
      rw [writersS_len]; omega
    obtain ⟨hs, hm⟩ := hon_markS fs (seed := seed) (fp := fp) hr
    rw [gS_child hc hj] at hm
    refine ⟨⟨s.claims.sphincs.length + (planS s w).2.length, by omega, (pow_add _ _ _).symm, hs⟩, ?_, ?_⟩
    · rw [← pow_add, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero, ← pow_add, ← pow_add]
      exact hm.load hL
    · have he := hon_sEntry fs hL hr ((writersS_child (s := s) hc hj).trans (List.getElem?_eq_getElem hj))
      have g : ∀ k < 4, (w.children[c].statement.claims.sphincs.flatMap sCellsOf).getD (4 * j + k) 0 =
          (sCellsOf (w.children[c].statement.claims.sphincs[j]'hj)).getD k 0 := fun k hk =>
        getD_flatMap_four _ sCellsOf_length 0 _ j k hj hk
      have g0 : (w.children[c].statement.claims.sphincs.flatMap sCellsOf).getD (4 * j) 0 =
          (sCellsOf (w.children[c].statement.claims.sphincs[j]'hj)).getD 0 0 := by simpa using g 0 (by omega)
      rw [g0, g 1 (by omega), g 2 (by omega), g 3 (by omega), ← list4 (sCellsOf_length _)]
      exact he
  · rw [sCellsOf_bytes]; rfl

/-! ## The DA roots -/

theorem hon_childCov (hlim : Limits s w) {c : ℕ} (hc : c < w.children.length)
    (hL : MemL rd (mainIn fs fp (honestWords seed s w))) {k : ℕ}
    (hk : k < w.children[c].statement.claims.da.length) :
    CoverPreAt ((planD s w).1.getD (hrd s w + ((w.children.take c).map cnda).sum + k) 0) rd
      [mainPtr fs fp (honestWords seed s w) 0,
      mainPtr fs fp (honestWords seed s w) 4 * (gen ^ s.claims.xmss.length * gen ^ (planX s w).2.length *
        (gen ^ s.claims.sphincs.length * gen ^ (planS s w).2.length)),
      gen ^ s.claims.da.length * gen ^ (planD s w).2.length,
      gen ^ hbase s w c * (gen ^ cnx w.children[c] * gen ^ cns w.children[c]) * gen ^ k]
      (daCellsOf (w.children[c].statement.claims.da[k]'hk)) := by
  have hsum := sum_take_lt cnda w.children hc
  have hr : hrd s w + ((w.children.take c).map cnda).sum + k < (writersD s w).length := by
    have : cnda w.children[c] = w.children[c].statement.claims.da.length := rfl
    rw [writersD_len]; omega
  obtain ⟨hs, hm⟩ := hon_markD fs (seed := seed) (fp := fp) hr
  rw [gD_child hc hk] at hm
  have hdau := honest_dau hlim
  have he := hon_dEntry fs hL hr ((writersD_child (s := s) hc hk).trans (List.getElem?_eq_getElem hk))
  refine ⟨s.claims.da.length + (planD s w).2.length, by omega, hs, (pow_add _ _ _).symm, ?_, he⟩
  have hv : gen ^ (hbase s w c + (cnx w.children[c] + cns w.children[c]) + k) =
      gen ^ hbase s w c * (gen ^ cnx w.children[c] * gen ^ cns w.children[c]) * gen ^ k := by ring
  rw [hv] at hm
  exact loadHolds_cover (hm.load hL)

/-! ## The whole iteration -/

theorem getElem?_flatMap_mem {γ : Type} (f : γ → List E) (m : ℕ) : ∀ (l : List γ),
    (∀ a ∈ l, (f a).length = m) → ∀ (i k : ℕ) (a : γ), l[i]? = some a → k < m →
      (l.flatMap f)[m * i + k]? = (f a)[k]?
  | [], _, i, k, a, h, _ => by simp at h
  | b :: l, hf, 0, k, a, h, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
      List.getElem?_append_left (by rw [hf _ List.mem_cons_self]; exact hk)]
  | b :: l, hf, i + 1, k, a, h, hk => by
    have hb := hf b List.mem_cons_self
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [hb]; nlinarith), hb,
      show m * (i + 1) + k - m = m * i + k by rw [Nat.mul_succ]; omega]
    exact getElem?_flatMap_mem f m l (fun x hx => hf x (List.mem_cons_of_mem _ hx)) i k a
      (by simpa using h) hk

theorem getElem_of_getD {β : Type} {l : List β} {d : β} {k : ℕ} (hk : k < l.length) :
    l[k] = l.getD k d := (List.getD_eq_getElem _ _ hk).symm

theorem hon_child {κ : ℕ} {VsGood : VerifySub.VsData → Prop} {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22) (hlim : Limits s w)
    (hshp : ∀ c ∈ w.children, c.statement.defer.Shaped bytecode)
    (hfr : ∀ c ∈ w.children, FreshShaped c.fresh)
    (hvs : ∀ c ∈ w.children, ∃ D : VerifySub.VsData, VsGood D ∧ D.pi = statementDigest seed c.statement ∧
      D.seed = seed ∧ D.fresh = c.fresh)
    {c : ℕ} (hc : c < w.children.length) :
    ChildWordsOk κ VsGood (mainIn fs fp (honestWords seed s w))
      (mainBase fs fp (honestWords seed s w) 8) (mainBase fs fp (honestWords seed s w) 5)
      (mainPtr fs fp (honestWords seed s w) 1) (mainPtr fs fp (honestWords seed s w) 4)
      (gen ^ (honestWords seed s w).dx * gen ^ (honestWords seed s w).ux)
      (ofK (gpow (mainExpBase fs fp (honestWords seed s w) + 34))) (mainPtr fs fp (honestWords seed s w) 2)
      (gen ^ (honestWords seed s w).ds * gen ^ (honestWords seed s w).us)
      (mainPtr fs fp (honestWords seed s w) 7) (mainPtr fs fp (honestWords seed s w) 0)
      (mainPtr fs fp (honestWords seed s w) 4 * (gen ^ (honestWords seed s w).dx *
        gen ^ (honestWords seed s w).ux * (gen ^ (honestWords seed s w).ds * gen ^ (honestWords seed s w).us)))
      (gen ^ (honestWords seed s w).da * gen ^ (honestWords seed s w).ud)
      (digestScalars (honestWords seed s w).seed).1 (digestScalars (honestWords seed s w).seed).2
      (ofK (gpow (mainExpBase fs fp (honestWords seed s w)))) (mainPtr fs fp (honestWords seed s w) 6)
      (honestWords seed s w).seed c ((honestWords seed s w).child c) := by
  rw [hon_child_eq hc]
  have hmem := List.getElem_mem hc
  obtain ⟨D, hg, hpi, hseed, hfresh⟩ := hvs _ hmem
  have hnc := hlim.children
  have hfl : (fixedCells w.children[c].fresh).length = 106 := fixedCells_length (hfr _ hmem)
  have hfrl : (w.children.flatMap fun c => fixedCells c.fresh).length = 106 * w.children.length :=
    length_flatMap_const _ 106 _ fun x hx => fixedCells_length (hfr x hx)
  refine
    { base := hon_written fs (seed := seed) (s := s) (w := w) c (by omega)
      next := ?_
      nx := (hlim.lists _ hmem).1
      ns := (hlim.lists _ hmem).2
      nda := hlim.daRoots.2 _ hmem
      ccx := ⟨_, _, length_flatMap_const _ 4 _ fun c _ => xCellsOf_length c, fun rd _ hL => hon_ccx fs hlim hc hL⟩
      ccs := ⟨_, _, length_flatMap_const _ 4 _ fun c _ => sCellsOf_length c, fun rd _ hL => hon_ccs fs hlim hc hL⟩
      sig := hon_sig _ _
      cov := ⟨_, fun k hk rd _ hL => hon_childCov fs hlim hc hL hk⟩
      defer := fun rd hL => ?_
      dlen := defer_cells_length hb (hshp _ hmem)
      seed := rfl
      pd := statementDigest_eq seed _
      pi0 := ?_
      pi1 := ?_
      vs := ⟨D, mainExpBase fs fp (honestWords seed s w), mainExpBase fs fp (honestWords seed s w) + 34,
        mainBase fs fp (honestWords seed s w) 6 + 106 * c, hg, hpi, hseed, rfl, rfl,
        ofK_gpow_mul_gen _ _, ?_⟩ }
  · have := hon_written fs (fp := fp) (seed := seed) (s := s) (w := w) (c + 1) (by omega)
    have hv : gen ^ hbase s w (c + 1) = gen ^ hbase s w c *
        (gen ^ cnx w.children[c] * gen ^ cns w.children[c]) * gen ^ cnda w.children[c] := by
      rw [hbase_succ hc, cnw]; ring
    rw [hv] at this
    exact this
  · have h7 : ReadsAt rd (mainPtr fs fp (honestWords seed s w) 7)
        (w.children.flatMap fun c => c.statement.defer.cells) := mainIn_reads hL 7 (by omega)
    exact readsAt_flatMap_of (w := 53) w.children
      (fun x hx => defer_cells_length hb (hshp x hx)) h7 c hc
  · refine cellL_of_getD (mainIn_mem 5 (by omega)) (2 * c) ?_ ?_
    · simp only [MainWords.bufs, honestWords, List.getD_cons_succ, List.getD_cons_zero]
      rw [length_flatMap_const _ 2 _ fun _ _ => rfl]; omega
    · simp only [MainWords.bufs, honestWords, List.getD_cons_succ, List.getD_cons_zero]
      rw [show 2 * c = 2 * c + 0 from rfl, getD_flatMap_const _ 2 (fun _ => rfl) 0 _ c 0 hc (by omega)]
      rfl
  · refine cellL_of_getD (mainIn_mem 5 (by omega)) (2 * c + 1) ?_ ?_
    · simp only [MainWords.bufs, honestWords, List.getD_cons_succ, List.getD_cons_zero]
      rw [length_flatMap_const _ 2 _ fun _ _ => rfl]; omega
    · simp only [MainWords.bufs, honestWords, List.getD_cons_succ, List.getD_cons_zero]
      rw [getD_flatMap_const _ 2 (fun _ => rfl) 0 _ c 1 hc (by omega)]
      rfl
  · refine SubL.append (SubL.of_mem fun q hq => List.mem_append_right _ ?_) ?_
    · simp only [VerifySub.expL, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · rw [hfresh]
      have hlen : 106 * c + (fixedCells w.children[c].fresh).length ≤
          (w.children.flatMap fun c => fixedCells c.fresh).length := by rw [hfl, hfrl]; nlinarith
      refine SubL.run (ys := w.children.flatMap fun c => fixedCells c.fresh)
        (mainIn_mem 6 (by omega)) hlen fun k hk => ?_
      have hk' : k < 106 := by rw [hfl] at hk; exact hk
      have := getElem?_flatMap_mem (fun c : Child => fixedCells c.fresh) 106 w.children
        (fun x hx => fixedCells_length (hfr x hx)) c k _ (List.getElem?_eq_getElem hc) hk'
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hk] at this
      exact (Option.some.inj this).symm

end
end LeanVM.Guest.B1.Main
