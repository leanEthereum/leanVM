/-
  LeanVM.Guest.B1.VerifySub.H.Fits

  `verify_sub` on an honest child: its own buffers fit their sizes, and `verify_tables`,
  `verify_keccak` and the terminal read slices of the caller's words, of the own buffers and of
  the results of the callees before them.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Regions
public import LeanVM.Guest.B1.VerifySub.H.TermC
public import LeanVM.Guest.B1.VerifySub.H.KFacts
public import LeanVM.Guest.B1.VerifySub.H.Vt

/-!
# The own buffers' sizes, the last callees' regions

`ChildSegs.ownW_fits`: the own buffers' honest words fit `vsSizes d` (the stream within
`childStreamCap`). `subOf_sub`: a slice of a slice. `kid10_lin_sub`: `verify_tables` reads the
caller's words, the own buffers and the GKR leaves `verify_bus_gkr` returned (`VbgOut`).
`kid11_lin_sub`: `verify_keccak` reads the caller's words and the own buffers (the output lanes
in the stream). `kid15_lin_sub`: the terminal, entered, reads them and `certify_placement`'s and
`open_stacked`'s returned buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- A slice of a slice. -/
theorem subOf_sub {L : Main.Layout} {b : ℕ} {xs : List E} (h : SubOf L (b, xs)) (off : ℕ)
    (ys : List E) (hl : off + ys.length ≤ xs.length) (hy : ys = (xs.drop off).take ys.length) :
    SubOf L (b + off, ys) := by
  obtain ⟨q', hq', o, e1, e2, e3⟩ := h
  simp only at e1 e2 e3
  have e4 : ys = ((q'.2.drop o).drop off).take ys.length := by
    conv_lhs => rw [hy]
    rw [e3, List.drop_take, List.take_take, min_eq_left (by omega)]
  refine ⟨q', hq', o + off, ?_, ?_, ?_⟩
  · show b + off = q'.1 + (o + off); omega
  · show o + off + ys.length ≤ q'.2.length; omega
  · show ys = (q'.2.drop (o + off)).take ys.length
    conv_lhs => rw [e4]
    rw [List.drop_drop, Nat.add_comm]

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

theorem ctab_length : S.ctab.length = 64 := by
  rw [ChildSegs.ctab, ringCoefficients_length (by simp [S.rchs_length, ringMapWidth])
    (by simp [S.rchs_length, ringMapWidth])]

theorem zvW_length (hbl : bytecode.length = 2 ^ 23) :
    (zvW S.kOut.point S.kc.2.1).length = qkeccakVarsCap + (S.τ + 6) := by
  obtain ⟨-, h22, -, -, -, hopl, hkpl, -⟩ := S.keccak_facts hbl
  simp only [zvW, List.length_append, List.length_replicate, hopl, hkpl, qkeccakVarsCap]
  omega

/-- **The own buffers fit their sizes.** -/
theorem ownW_fits (hbl : bytecode.length = 2 ^ 23)
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap) :
    List.Forall₂ (fun c s ↦ c.length ≤ s) S.ownW (vsSizes S.d) := by
  obtain ⟨hok, -, -, -⟩ := S.H_run hbl
  obtain ⟨-, h22, -, -, -, -, -, hsl⟩ := S.keccak_facts hbl
  obtain ⟨-, -, -, -, hpl, -⟩ := S.gkr_inv hbl
  have hnT := S.nT_le hbl
  have hzl := S.zvW_length hbl
  have hμ : S.μs ≤ 28 := S.hmu28
  simp only [ChildSegs.ownW, vsSizes, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
  refine ⟨?_, ?_, by simp [S.hrowsL], ?_, ?_, hpl.le, by rw [S.oodZ_length]; exact hμ, by simp,
    (S.wb_length hbl).le, ?_, S.slots_length.le, by rw [hzl]; simp only [qkeccakVarsCap]; omega,
    hsl.le, S.rchs_length.le, S.ctab_length.le⟩
  · simp [Tables.VtHonest.poolW, Tables.VtHonest.pcW, hok.hx4]
  · simp only [vsStreamW, List.length_append, List.length_replicate, Coverage.childStreamCap]
      at hst ⊢
    omega
  · simp [vsDimsW, heights_length6 S.rowsN S.hrowsL, ChildSegs.hs]
  · simp [vsKbW, heights_length6 S.rowsN S.hrowsL, ChildSegs.hs]
  · rw [S.chiW_length]; omega

/-- `dims_g`'s words as `verify_tables` reads them. -/
theorem dimsW_eq (hbl : bytecode.length = 2 ^ 23) : S.H.dimsW = vsDimsW S.logMem S.hs := by
  have ht : Tables.vtTauList S.H.τ = S.hs := by
    apply List.ext_getElem (by simp [Tables.vtTauList, heights_length6 S.rowsN S.hrowsL,
      ChildSegs.hs])
    intro t h1 h2
    simp only [Tables.vtTauList, List.getElem_map, List.getElem_range]
    rw [← List.getD_eq_getElem _ 0 h2]
    rfl
  rw [Tables.VtHonest.dimsW, vsDimsW, ht, S.hs_count hbl]
  rfl

end ChildSegs

/-- **`verify_tables` reads the caller's words, the own buffers and the GKR leaves**
`verify_bus_gkr` returned. -/
theorem kid10_lin_sub {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (b : ℕ) {sqE : ℕ} {Lin : Main.Layout}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (pv : List (List E × Main.Layout))
    (h9 : Tables.VbgOut S.s4.cap (ptr (ChildSegs.cG (bases b (vsSizes S.d))) * gen ^ S.xsG.length)
      S.rG.2.2 (pv.getD 9 ([], [])).1 (pv.getD 9 ([], [])).2) :
    ∀ q ∈ ((S.kids (bases b (vsSizes S.d)) sqE).getD 10 noKid pv).Lin,
      SubOf Lin q ∨ SubOf (bufL b (vsSizes S.d) S.ownW) q ∨ q ∈ (pv.getD 9 ([], [])).2 := by
  set bs := bases b (vsSizes S.d)
  have own : ∀ i < 15, SubOf (bufL b (vsSizes S.d) S.ownW) (vb bs i, S.ownW.getD i []) :=
    fun i hi ↦ S.sub_own b hi
  obtain ⟨-, hcur, -, -⟩ := S.H_run hbl
  obtain ⟨-, -, hc5, -⟩ := S.gkr_inv hbl
  have hleaves : (S.leavesB pv, S.rG.2.2) ∈ (pv.getD 9 ([], [])).2 := by
    obtain ⟨e, he, hm⟩ := h9
    have hex : ∃ b', (ChildSegs.gkRes pv).1.getD 6 0 = ptr b' ∧
        (b', S.rG.2.2) ∈ (ChildSegs.gkRes pv).2 := by
      refine ⟨e, ?_, hm⟩
      show (pv.getD 9 ([], [])).1.getD 6 0 = _
      rw [he, List.getD_append_right _ _ _ _ (by rw [hc5]; omega), hc5]
      rfl
    unfold ChildSegs.leavesB
    split
    · rename_i h'; exact (Classical.choose_spec h').2
    · exact absurd hex ‹_›
  intro q hq
  simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, Tables.VtHonest.linL,
    ChildSegs.vtB, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← hcur]; exact Or.inr (Or.inl (S.sub_xsT b hbl))
  · exact Or.inr (Or.inl (own 5 (by norm_num)))
  · rw [S.dimsW_eq hbl]; exact Or.inr (Or.inl (own 3 (by norm_num)))
  · exact Or.inr (Or.inl (own 2 (by norm_num)))
  · exact Or.inl (subOf_expTableWordsW hexp)
  · exact Or.inr (Or.inl (own 8 (by norm_num)))
  · exact Or.inr (Or.inl (own 0 (by norm_num)))
  · exact Or.inr (Or.inl (own 9 (by norm_num)))
  · exact Or.inr (Or.inr hleaves)
  · exact Or.inr (Or.inl (own 10 (by norm_num)))

/-- **`verify_keccak` reads the caller's words and the own buffers.** -/
theorem kid11_lin_sub {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (b : ℕ) {sqE : ℕ} {Lin : Main.Layout}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (pv : List (List E × Main.Layout)) :
    ∀ q ∈ ((S.kids (bases b (vsSizes S.d)) sqE).getD 11 noKid pv).Lin,
      SubOf Lin q ∨ SubOf (bufL b (vsSizes S.d) S.ownW) q := by
  set bs := bases b (vsSizes S.d)
  have own : ∀ i < 15, SubOf (bufL b (vsSizes S.d) S.ownW) (vb bs i, S.ownW.getD i []) :=
    fun i hi ↦ S.sub_own b hi
  obtain ⟨hlo, hlen⟩ := S.outs_stream hbl
  obtain ⟨-, h22, -, hol, -, hopl, -⟩ := S.keccak_facts hbl
  have hzl := S.zvW_length hbl
  have hz : SubOf (bufL b (vsSizes S.d) S.ownW) (vb bs 11, zvW S.kOut.point S.kc.2.1) :=
    own 11 (by norm_num)
  have hpre : zvW S.kOut.point S.kc.2.1 = S.kOut.point ++
      (List.replicate (qkeccakVarsCap - S.kOut.point.length) 0 ++ S.kc.2.1) := by
    rw [zvW, List.append_assoc]
  have hl39 : (S.kOut.point ++ List.replicate (qkeccakVarsCap - S.kOut.point.length) 0).length =
      qkeccakVarsCap := by
    rw [List.length_append, List.length_replicate, hopl]
    simp only [qkeccakVarsCap]
    omega
  have hk : (zvW S.kOut.point S.kc.2.1).drop qkeccakVarsCap = S.kc.2.1 := by
    rw [zvW]
    exact List.drop_left' hl39
  have hop : SubOf (bufL b (vsSizes S.d) S.ownW) (vb bs 11, S.kOut.point) := by
    have := subOf_sub hz 0 S.kOut.point (by rw [hzl, hopl]; simp only [qkeccakVarsCap]; omega)
      (by rw [List.drop_zero, hpre, List.take_left])
    rwa [Nat.add_zero] at this
  have hkpl := (S.keccak_facts hbl).2.2.2.2.2.2.1
  have hkp : SubOf (bufL b (vsSizes S.d) S.ownW) (vb bs 11 + qkeccakVarsCap, S.kc.2.1) :=
    subOf_sub hz qkeccakVarsCap S.kc.2.1 (by rw [hzl]; omega) (by rw [hk, List.take_length])
  intro q hq
  simp only [ChildSegs.kids, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (S.sub_xsK b hbl)
  · exact Or.inr (own 9 (by norm_num))
  · have := subOf_sub (S.sub_xsT b hbl) (14 + 3 * S.nT + 101) S.outs
      (by rw [hol, hlen]; omega) (by rw [hol]; exact hlo)
    rw [show S.cT bs + (14 + 3 * S.nT + 101) = S.cL bs by
      simp only [ChildSegs.cL, ChildSegs.cE]; omega] at this
    exact Or.inr this
  · exact Or.inr hop
  · exact Or.inr hkp
  · exact Or.inr (own 12 (by norm_num))
  · exact Or.inl (subOf_winTab hexp)

/-- **The terminal, entered, reads the caller's words, the own buffers and the buffers
`certify_placement` and `open_stacked` returned.** -/
theorem kid15_lin_sub {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (b : ℕ) {sqE : ℕ} {Lin : Main.Layout}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (pv : List (List E × Main.Layout)) :
    ∀ q ∈ ((S.kids (bases b (vsSizes S.d)) sqE).getD 15 noKid pv).Lin,
      SubOf Lin q ∨ SubOf (bufL b (vsSizes S.d) S.ownW) q ∨ q ∈ (pv.getD 3 ([], [])).2 ∨
        q ∈ (pv.getD 14 ([], [])).2 := by
  set bs := bases b (vsSizes S.d)
  have own : ∀ i < 15, SubOf (bufL b (vsSizes S.d) S.ownW) (vb bs i, S.ownW.getD i []) :=
    fun i hi ↦ S.sub_own b hi
  intro q hq
  by_cases hok : S.termOk pv
  · have hq' : q ∈ (ChildSegs.cpRes pv).2 ++ (ChildSegs.osRes pv).2 ++ S.termLin bs sqE := by
      have e : ((S.kids bs sqE).getD 15 noKid pv).Lin =
          (ChildSegs.cpRes pv).2 ++ (ChildSegs.osRes pv).2 ++ S.termLin bs sqE := by
        show @ite _ _ (Classical.propDecidable _) _ _ = _
        rw [@ite_pos' _ _ (Classical.propDecidable _) _ _ hok]
      rw [← e]; exact hq
    simp only [List.mem_append] at hq'
    rcases hq' with (h | h) | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · simp only [ChildSegs.termLin, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (own 5 (by norm_num)))
      · exact Or.inr (Or.inl (own 9 (by norm_num)))
      · have := own 4 (by norm_num)
        rw [show S.ownW.getD 4 [] = vsKbW S.logMem S.hs from rfl, S.kbW_eq hbl] at this
        exact Or.inr (Or.inl this)
      · exact Or.inl (subOf_self (hexp _ List.mem_cons_self))
      · exact Or.inr (Or.inl (own 11 (by norm_num)))
      · exact Or.inr (Or.inl (own 14 (by norm_num)))
      · exact Or.inr (Or.inl (own 6 (by norm_num)))
  · have e : ((S.kids bs sqE).getD 15 noKid pv).Lin = [] := by
      show @ite _ _ (Classical.propDecidable _) _ _ = _
      rw [@ite_neg' _ _ (Classical.propDecidable _) _ _ hok]
    rw [e] at hq
    simp at hq

end
end LeanVM.Guest.B1.VerifySub
