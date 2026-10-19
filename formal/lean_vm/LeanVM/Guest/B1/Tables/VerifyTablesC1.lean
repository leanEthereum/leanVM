/-
  LeanVM.Guest.B1.Tables.VerifyTablesC1

  `verify_tables`' completeness: the prelude (the arguments' copies, `sort_order`,
  `block_side_tab`, `block_off_g`) and `idxc_tab`.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesC0
public import LeanVM.Guest.B1.Tables.VerifyTablesFront

/-!
# The prelude and `idxc_tab`, forward

`vt_c_pre`: statements `0 ..< 213` (values `19 ..< 129`) on the three `HeapBuf` pointers, the side
table's stores against a memory holding it. `vt_c_idxc`: statements `1505 ..< 1574` (values
`1817 ..< 1852`), `INDEX_MLE_FACTORS` stored at the hinted pointer.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## The prelude -/

/-- Block `b`'s side, stored. -/
def vtSideI (b : ℕ) : List FItem :=
  [.atom (.const (.n (26 + b)) (word (vtBlockSide b) 0 0)), .atom (.load (.n (26 + b)) (.n 25) b)]

/-- The prelude's items. -/
def vtItPre : List FItem :=
  [.atom (.copy (.n 19) (.n 0)), .atom (.copy (.n 20) (.n 1)), .atom (.copy (.n 21) (.n 16)),
    .atom (.copy (.n 22) (.n 17)), .atom (.copy (.n 23) (.n 18)), .hint (.alloc (.n 24) 102),
    .hint (.witness "sort_order" (.heap (.n 24) 0 102)), .hint (.alloc (.n 25) 102)] ++
  (List.range 102).flatMap vtSideI ++ [.hint (.alloc (.n 128) 102)]

set_option maxRecDepth 100000 in
theorem vtItPre_eq : vtItPre.flatMap FItem.stmts = vtPre.take 213 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vtItPre_ok : fOkI 19 129 [] vtItPre = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtItPre_obs : iObs 19 [] vtItPre =
    (List.range 102).map fun b => .ob (.holds (.load (.n (26 + b)) (.n 25) b)) :=
  listEqb_sound iobEqb_sound (by decide +kernel)

/-- The prelude's definitions. -/
def vtPreEq : List FEq :=
  [.def (.copy (.n 19) (.n 0)), .def (.copy (.n 20) (.n 1)), .def (.copy (.n 21) (.n 16)),
    .def (.copy (.n 22) (.n 17)), .def (.copy (.n 23) (.n 18)), .item (.hint (.alloc (.n 24) 102)),
    .item (.hint (.alloc (.n 25) 102)), .item (.hint (.alloc (.n 128) 102))]

set_option maxRecDepth 100000 in
theorem vtItPre_eqsB : vtPreEq.all (fun e => (fEqs 19 [] vtItPre).any (feqEqb e)) &&
    (List.range 102).all (fun b => (fEqs 19 [] vtItPre).any
      (feqEqb (.def (.const (.n (26 + b)) (word (vtBlockSide b) 0 0))))) = true := by
  decide +kernel

/-- The prelude's oracle: the three pointers. -/
noncomputable def vtHvPre (p24 p25 p128 : E) (k : ℕ) : E :=
  if k = 24 then p24 else if k = 25 then p25 else if k = 128 then p128 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The prelude completes**: the arguments copied, the three pointers hinted, the sides stored. -/
theorem vt_c_pre {rd : Reader} {σ : Val} {p24 p25 p128 : E}
    (hside : ∀ b < 102, LoadHolds rd p25 b (word (vtBlockSide b) 0 0)) :
    Completes (coreProgram.Rel rd) rd 19 129 (vtPre.take 213) σ (fun σ' =>
      σ' (.n 19) = σ (.n 0) ∧ σ' (.n 20) = σ (.n 1) ∧ σ' (.n 21) = σ (.n 16) ∧
        σ' (.n 22) = σ (.n 17) ∧ σ' (.n 23) = σ (.n 18) ∧ σ' (.n 24) = p24 ∧ σ' (.n 25) = p25 ∧
        σ' (.n 128) = p128) := by
  rw [← vtItPre_eq]
  set hv := vtHvPre p24 p25 p128
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) hv vtItPre vtItPre_ok σ
  generalize hσf : fRunI rd 19 hv [] σ vtItPre = σf at Cm
  have hf : ∀ v, fRunI rd 19 hv [] σ vtItPre v = σf v := fun v => by rw [hσf]
  have E := fRunI_eqs rd hv σf vtItPre [] σ vtItPre_ok hf
  have FR : ∀ k < 19, σf (.n k) = σ (.n k) := fun k hk =>
    fRunI_eq_of_def rd hv vtItPre_ok hf (by simp [fDef, vNum, hk])
  have hB := vtItPre_eqsB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hB
  have Ed := fun e (he : e ∈ vtPreEq) => E e (mem_of_any feqEqb_sound (hB.1 e he))
  have Ec := fun b (hb : b ∈ List.range 102) => E _ (mem_of_any feqEqb_sound (hB.2 b hb))
  simp only [vtPreEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Ed
  obtain ⟨c19, c20, c21, c22, c23, a24, a25, a128⟩ := Ed
  have ptr := fun (it : FItem) (hit : FEq.Holds rd hv σf (.item it)) (v : ℕ) (hs : it.sets = [.n v]) =>
    hit 0 (by rw [hs]; simp) (by rw [FItem.vals_length, hs]; simp)
  have q24 := a24 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
  have q25 := a25 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
  have q128 := a128 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
  simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons, List.map_nil] at q24 q25 q128
  have e25 : σf (.n 25) = p25 := by rw [q25]; simp [hv, vtHvPre]
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [vtItPre_obs]
    intro o ho
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ho
    have hcb : σf (.n (26 + b)) = word (vtBlockSide b) 0 0 := Ec b hb
    show LoadHolds rd (σf (.n 25)) b (σf (.n (26 + b)))
    rw [e25, hcb]; exact hside b (List.mem_range.mp hb)
  · intro σ' h; rw [h]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, e25, ?_⟩
    · have : σf (.n 19) = σf (.n 0) := c19; rw [this, FR 0 (by omega)]
    · have : σf (.n 20) = σf (.n 1) := c20; rw [this, FR 1 (by omega)]
    · have : σf (.n 21) = σf (.n 16) := c21; rw [this, FR 16 (by omega)]
    · have : σf (.n 22) = σf (.n 17) := c22; rw [this, FR 17 (by omega)]
    · have : σf (.n 23) = σf (.n 18) := c23; rw [this, FR 18 (by omega)]
    · rw [q24]; simp [hv, vtHvPre]
    · rw [q128]; simp [hv, vtHvPre]

/-! ## `idxc_tab` -/

/-- Factor `t`, stored. -/
def vtIdxcI (t : ℕ) : List FItem :=
  [.atom (.const (.n (1818 + t)) (word (kToNat (1 + gpowK (2 ^ t))) 0 0)),
    .atom (.load (.n (1818 + t)) (.n 1817) t)]

/-- `idxc_tab`'s items. -/
def vtItIdxc : List FItem := .hint (.alloc (.n 1817) 34) :: (List.range 34).flatMap vtIdxcI

set_option maxRecDepth 100000 in
theorem vtItIdxc_eq : vtItIdxc.flatMap FItem.stmts = (vtPre.drop 1505).take 69 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vtItIdxc_ok : fOkI 1817 1852 [] vtItIdxc = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtItIdxc_obs : iObs 1817 [] vtItIdxc =
    (List.range 34).map fun t => .ob (.holds (.load (.n (1818 + t)) (.n 1817) t)) :=
  listEqb_sound iobEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem vtItIdxc_eqsB : (fEqs 1817 [] vtItIdxc).any (feqEqb (.item (.hint (.alloc (.n 1817) 34)))) &&
    (List.range 34).all (fun t => (fEqs 1817 [] vtItIdxc).any
      (feqEqb (.def (.const (.n (1818 + t)) (word (kToNat (1 + gpowK (2 ^ t))) 0 0))))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **`idxc_tab` completes** at the hinted pointer, on a memory holding the factors there. -/
theorem vt_c_idxc {rd : Reader} {σ : Val} {p : E}
    (hidx : ∀ t < 34, LoadHolds rd p t (1 + gen ^ 2 ^ t)) :
    Completes (coreProgram.Rel rd) rd 1817 1852 ((vtPre.drop 1505).take 69) σ (fun σ' =>
      σ' (.n 1817) = p) := by
  rw [← vtItIdxc_eq]
  set hv : ℕ → E := fun _ => p
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) hv vtItIdxc vtItIdxc_ok σ
  generalize hσf : fRunI rd 1817 hv [] σ vtItIdxc = σf at Cm
  have hf : ∀ v, fRunI rd 1817 hv [] σ vtItIdxc v = σf v := fun v => by rw [hσf]
  have E := fRunI_eqs rd hv σf vtItIdxc [] σ vtItIdxc_ok hf
  have hB := vtItIdxc_eqsB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hB
  have qp := E _ (mem_of_any feqEqb_sound hB.1) 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
  simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons, List.map_nil] at qp
  have Ec := fun t (ht : t ∈ List.range 34) => E _ (mem_of_any feqEqb_sound (hB.2 t ht))
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [vtItIdxc_obs]
    intro o ho
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ho
    have hc : σf (.n (1818 + t)) = word (kToNat (1 + gpowK (2 ^ t))) 0 0 := Ec t ht
    show LoadHolds rd (σf (.n 1817)) t (σf (.n (1818 + t)))
    have ht' := List.mem_range.mp ht
    rw [qp, hc, word_ofK, ofBits_kToNat, ofK_add', ofK_one,
      gpowK_eq (by unfold u128Bound; exact Nat.pow_lt_pow_right (by decide) (by omega)), ← gen_pow_eq_ofK]
    exact hidx t ht'
  · intro σ' h; rw [h]
    exact qp

end
end LeanVM.Guest.B1.VerifySub
