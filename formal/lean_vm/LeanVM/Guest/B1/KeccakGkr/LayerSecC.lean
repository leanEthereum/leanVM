/-
  LeanVM.Guest.B1.KeccakGkr.LayerSecC

  `keccak_layer`'s tail (G:2641-2669): the final check, the squeeze of `β`, the next claim's
  record, the return.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Flips

/-!
# The tail

`tailT_holds`: from the local point (its lane weights `f` and its words at `loc`), `t`'s words
packed, and the capacity after the local rounds, the tail's statements give the final check, the
squeeze of `β` after `t`, the next claim's value, point, local point, lanes (`lanesOut`) and slices
(`eqKernel` of the local point's first six coordinates), and the return: the capacity after `β`
and the cursor past `t`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The next claim's lanes. -/
theorem lanesOutT_holds {beta lp B : ℕ} {f : ℕ → ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (lanesOutT beta f lp B) next kret) :
    (∀ i < 25, σ (.n (B + 4 * i + 3)) = σ (.n (f i)) + σ (.n beta) *
        (σ (.n (f ((i % 5 + 4) % 5 + 5 * (i / 5)))) + σ (.n beta) *
          σ (.n (f ((i % 5 + 3) % 5 + 5 * (i / 5))))) ∧
      LoadHolds rd (σ (.n lp)) i (σ (.n (B + 4 * i + 3)))) ∧ next := by
  rw [lanesOutT, holdsList_range_flatten _ _ (fun _ ↦ rfl)] at h
  refine ⟨fun i hi ↦ ?_, h.2⟩
  have hi' := h.1 i hi
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hi'
  obtain ⟨e0, e1, e2, e3, l⟩ := hi'
  exact ⟨by rw [e3, e2, e1, e0], l⟩

theorem word_2p36 : word 68719476736 0 = gen ^ 36 := by
  rw [show (68719476736 : ℕ) = 2 ^ 36 from rfl]; exact word_two_pow (by decide)

theorem lflipBlk_noRet (lp : V) (sl : ℕ → ℕ) (top top1 i b : ℕ) (s : Stmt) :
    Stmt.noRetList (lflipT lp sl top top1 i b ++ [s]) = Stmt.noRetList [s] := by
  rw [noRetList_append]
  unfold lflipT
  split
  · rfl
  · rw [noRetList_append, noRetList_flatten_map _ (fun k ↦ rfl)]
    rfl

/-- **The tail** (G:2763-2824). -/
theorem tailT_holds {o W wv : ℕ} {locPt : List E} (hlocL : locPt.length = 11)
    (hloc : ReadsAt rd (σ (.n (o + 748))) locPt)
    (hf : ∀ i < 25, σ (.n (laneW o i)) = eqAt (locPt.drop 6) i)
    (p1 : FsPackOk σ (.n (o + 1112)) (o + 1112 + 1) dsObserve)
    (p2 : FsPackOk σ (.n (o + 1115)) (o + 1115 + 1) dsObserve)
    (p3 : FsPackOk σ (.n (o + 1118)) (o + 1118 + 1) dsObserve)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (tailT o W wv) next kret) :
      σ (.n (o + 747)) * σ (.n wv) * (σ (.n (o + 625)) * σ (.n (o + 1112)) +
        (σ (.n (o + 625)) + σ (.n (o + 1115))) * σ (.n (o + 1118))) = σ (.n (o + 1111)) ∧
      ((⟨(cap5 (o + 1098)).map σ, []⟩ : Fs).absorbAll
        [σ (.n (o + 1112)), σ (.n (o + 1115)), σ (.n (o + 1118))] dsObserve).squeeze =
        (σ (.n (W + 22)), ⟨(cap5 (W + 17)).map σ, []⟩) ∧
      LoadHolds rd (σ (.n 12)) 0 (σ (.n (o + 1112)) + σ (.n (W + 22)) *
        (σ (.n (o + 1115)) + σ (.n (W + 22)) * σ (.n (o + 1118)))) ∧
      LoadHolds rd (σ (.n 12)) 2 (σ (.n (o + 719))) ∧
      LoadHolds rd (σ (.n 12)) 4 (σ (.n (o + 748))) ∧
      LoadHolds rd (σ (.n 12)) 3 (σ (.n (W + 27))) ∧
      ReadsAt rd (σ (.n (W + 27))) (lanesOut locPt (σ (.n (W + 22)))) ∧
      LoadHolds rd (σ (.n 12)) 5 (σ (.n (topV W + 3))) ∧
      ReadsAt rd (σ (.n (topV W + 3)))
        (flipsOf (laterWeights (lanesOut locPt (σ (.n (W + 22)))) (eqKernel (locPt.take 6)))) ∧
      kret ((cap5 (W + 17)).map σ ++ [σ (.n (o + 745)) * gen ^ 36]) := by
  simp only [tailT, holdsList_append, List.append_assoc, holds_challengeT] at h
  simp only [Stmt.HoldsList, Stmt.Holds, keccakA] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, heq, z0, z1, hk, hch, h⟩ := h
  obtain ⟨o1, o2, o3, o4, lo0, lo2, lo4, -, h⟩ := h
  simp only [Atom.Holds] at e0 e1 e2 e3 e4 e5 e6 heq z0 z1 o1 o2 o3 o4 lo0 lo2 lo4
  obtain ⟨hl, h⟩ := lanesOutT_holds h
  obtain ⟨lo3, h⟩ := h
  simp only [Atom.Holds] at lo3
  obtain ⟨⟨rs, hrsL, hrs, hent⟩, h⟩ := eqfT_holds (by omega) (by omega) (by decide) (by decide) h
  obtain ⟨ltop, c1, etop, -, h⟩ := h
  simp only [Atom.Holds] at ltop c1 etop
  rw [lflipsT, holdsList_range_flatten _ _ (fun i ↦ by rw [lflipBlk_noRet]; rfl)] at h
  obtain ⟨hfl, lo5, h⟩ := h
  simp only [Atom.Holds] at lo5
  rw [holdsList_map_atoms] at h
  obtain ⟨hcp, c0', c1', c2', hret⟩ := h
  simp only [Atom.Holds] at hcp c0' c1' c2'
  have hsq := sq3_atoms (a := o + 1112) (o := W + 9) (cap := (cap5 (o + 1098)).map σ) p1
    (by simpa [Nat.add_assoc] using p2) (by simpa [Nat.add_assoc] using p3)
    (by simpa [cap5, Nat.add_assoc] using hk) (by simpa [Nat.add_assoc] using hch)
    (by rw [z0, word_zero]) (by rw [z1, word_zero]) rfl
  simp only [Nat.add_assoc, Nat.reduceAdd] at hsq
  have hrs5 : rs = locPt.take 5 := by
    apply List.ext_getElem (by simp [hrsL, hlocL])
    intro k h1 h2
    have := hloc k (by omega)
    simp only [Nat.zero_add] at hrs
    rw [List.getElem_take]
    exact loadHolds_unique (hrs k h1) this
  have htop : σ (.n (topV W)) = locPt.getD 5 0 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique ltop (hloc 5 (by omega))
  have hlanes : ReadsAt rd (σ (.n (W + 27))) (lanesOut locPt (σ (.n (W + 22)))) := by
    intro k hk
    simp only [lanesOut, List.length_map, List.length_range] at hk
    have := (hl k hk).2
    rw [(hl k hk).1, hf k hk, hf ((k % 5 + 4) % 5 + 5 * (k / 5)) (by omega),
      hf ((k % 5 + 3) % 5 + 5 * (k / 5)) (by omega)] at this
    simp only [lanesOut, List.getElem_map, List.getElem_range]
    exact this
  refine ⟨?_, ?_, ?_, lo2, lo4, lo3, hlanes, lo5, ?_, ?_⟩
  · rw [← eq_of_add_eq_zero' heq, e6, e5, e4, e3, e2, e1, e0]
  · refine Prod.ext hsq.1.symm ?_
    have hs : ∀ s : Fs, s.squeeze.2 = ⟨s.squeeze.2.cap, []⟩ := fun _ ↦ rfl
    rw [hs, ← hsq.2]
    rfl
  · rw [o4, o3, o2, o1] at lo0
    exact lo0
  · intro i hi
    simp only [flipsOf, List.length_map, List.length_range] at hi
    have hb := hfl i hi
    rw [holdsList_append] at hb
    obtain ⟨hv, hst⟩ := lflipT_holds (lanesOut_length _ _) hlanes hb
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hst
    simp only [flipsOf, List.getElem_map, List.getElem_range]
    rw [laterWeights_flip _ _ (by simp [hlocL]) hi]
    convert hst.1 using 1
    rw [hv]
    refine congrArg List.sum (List.map_congr_left fun o ho ↦ ?_)
    have h64 := (flipOffs_lt i o ho).2
    rw [hent _ (Nat.mod_lt _ (by norm_num)), hrs5, List.take_take, show min 5 6 = 5 from rfl]
    congr 2
    simp only [topOf]
    rw [List.getD_eq_getElem _ _ (by simp [hlocL]), List.getElem_take,
      ← List.getD_eq_getElem _ 0 (by omega), ← htop]
    split
    · rfl
    · rw [etop, c1, word_one]
  · have h0 : σ (.n (topV W + 305)) = σ (.n (W + 17)) := by simpa using hcp 0 (by omega)
    have h1 : σ (.n (topV W + 306)) = σ (.n (W + 18)) := by simpa [Nat.add_assoc] using hcp 1 (by omega)
    have h2 : σ (.n (topV W + 307)) = σ (.n (W + 19)) := by simpa [Nat.add_assoc] using hcp 2 (by omega)
    have h3 : σ (.n (topV W + 308)) = σ (.n (W + 20)) := by simpa [Nat.add_assoc] using hcp 3 (by omega)
    have h4 : σ (.n (topV W + 309)) = σ (.n (W + 21)) := by simpa [Nat.add_assoc] using hcp 4 (by omega)
    convert hret using 1
    simp only [cap5, List.map_cons, List.map_nil, List.cons_append, List.nil_append, c2', c1', c0',
      word_2p36, h0, h1, h2, h3, h4, Nat.add_assoc, Nat.reduceAdd]

end
end LeanVM.Guest.B1.VerifySub
