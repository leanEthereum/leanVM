/-
  LeanVM.Guest.B1.Sig.SpWotsPops

  The witness-stream entries `sp_wots` (`lean_ethereum.py:4072-4102`) pops on its completing valuation: each digit group's word (`"digits"`), then the starts of the chains its arm walks (`"chain_starts"`).
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsCompleteStmt
public import LeanVM.Guest.B1.Sig.BlockPops
public import LeanVM.Guest.B1.Sig.PopsKit

/-!
# `sp_wots`'s pops

* `groupD_pops`: a digit group pops its digit word, then the starts of the chains of the arm it takes;
* `spGroupPops`, `spPopsT`, `spPreT_pops`: the template's body before its return pops its 22 groups' entries, from any valuation holding the groups' words and starts (`SpGP`);
* `sp_wots_complete_cells_pops`, `sp_wots_complete_pops`: `sp_wots` completes on a valuation whose path pops `spWotsPops digest values`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## A group -/

/-- **A digit group pops its digit word, then the starts of the chains of the arm `k` it takes.** -/
theorem groupD_pops {W : WotsT} (hW : StepQuiet W) {first n : Nat} (hn : n ≤ 3) {fold : Bool}
    {prodIn encIn : V} {d : Nat} {pre : List Stmt} (hpre : quiet pre = true) {b : Nat} {σ : Val} {k : Nat}
    (hk : k < 4 ^ n) (hx : σ (.n d) = ofK (addressOfIndex k)) :
    FallPops rd σ (groupD W first n fold prodIn encIn d pre b).1
      (("digits", [σ (.n d)]) :: (List.range n).map fun t => startPop (σ (armStart W (slotsT W fold b) fold k
        (armBase W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) 0 k (b + 6))
          t))) := by
  have h64 : 4 ^ n ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn
  set arms := armsT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) (4 ^ n) 0
    (b + 6) with harms
  have hl : k < arms.1.length := by rw [harms, armsT_length]; exact hk
  have hm := FallPops.match_ (rd := rd) (x := .n d) hl (by norm_num at h64; omega) hx
    (p := (List.range n).map fun t => startPop (σ (armStart W (slotsT W fold b) fold k
        (armBase W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) 0 k (b + 6))
          t))) (by
      simp only [harms, armsT_getElem, Nat.zero_add]
      exact armT_pops hW σ _ _ _ _ _ _ _ _ _ _)
  have hh : FallPops rd σ [hintW "digits" [.n d]] [("digits", [σ (.n d)])] := FallPops.atom _
  have e : (groupD W first n fold prodIn encIn d pre b).1 = [hintW "digits" [.n d]] ++
      (rangeS (.n d) (word (2 ^ (4 ^ n - 1)) 0) (d + 1) ++ (pre ++ ([cst (b + 5) closeLane] ++
        [.match_ (.n d) arms.1]))) := by
    simp only [groupD, groupArmsT, harms, List.cons_append, List.nil_append, List.append_assoc]
  have s : ∀ {α : Type} (x : α) (F : List α), [x] ++ ([] ++ ([] ++ ([] ++ F))) = x :: F := by
    intros; simp only [List.nil_append, List.singleton_append]
  rw [e]
  exact FallPops.congr_pops (hh.append ((fallPops_quiet σ rfl).append ((fallPops_quiet σ hpre).append
    ((fallPops_quiet σ rfl).append hm)))) (s _ _)

theorem spW_quiet : StepQuiet spW := fun i s _ _ _ => by
  simp only [spW, spWp]
  split <;> rfl

/-- Group `q`'s entries: its digit word, then its chains' starts. -/
def spGroupPops (d : Nat → Nat) (vals : Nat → E) (q : Nat) : List Pop :=
  ("digits", [ofK (addressOfIndex (spK d q))]) :: (List.range (spN q)).map fun t => startPop (vals (3 * q + t))

theorem spPre_quiet (fold : Bool) (B : Nat) : quiet (spPre fold B) = true := by
  cases fold <;> rfl

/-- **Group `q` pops its entries** from any valuation holding its word and starts. -/
theorem spGroupP_pops {d : Nat → Nat} {vals : Nat → E} {q : Nat} {σ : Val} (h : SpGP d vals q σ) :
    FallPops rd σ (spGroupT (3 * q) (spN q) (q == 0) (spState q).1 (spState q).2.1 (spState q).2.2).1
      (spGroupPops d vals q) := by
  have hg := groupD_pops (rd := rd) spW_quiet (first := 3 * q) (spN_le q) (fold := q == 0)
    (prodIn := (spState q).1) (encIn := (spState q).2.1) (d := (spState q).2.2)
    (spPre_quiet (q == 0) (spState q).2.2) (b := spL (q == 0) (spState q).2.2) (spK_lt d q) h.1
  refine FallPops.congr_pops hg ?_
  rw [h.1]
  refine congrArg _ (List.map_congr_left fun t ht => congrArg startPop ?_)
  exact h.2 t (List.mem_range.mp ht)

/-- **Groups `p ..< p + m` pop their entries.** -/
theorem spGL_pops (d : Nat → Nat) (vals : Nat → E) {σ : Val} :
    ∀ m p, (∀ q, p ≤ q → q < p + m → SpGP d vals q σ) →
      FallPops rd σ (spGL p m) ((List.range m).flatMap fun j => spGroupPops d vals (p + j))
  | 0, _, _ => FallPops.nil
  | m + 1, p, h => by
      rw [spGL, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_zero]
      refine (spGroupP_pops (h p le_rfl (by omega))).append ?_
      refine FallPops.congr_pops (spGL_pops d vals m (p + 1) fun q h1 h2 => h q (by omega) (by omega)) ?_
      exact List.flatMap_congr fun j _ => by rw [show p + 1 + j = p + (j + 1) by omega]

/-! ## The body -/

/-- The template's entries: its 22 groups'. -/
def spPopsT (d : Nat → Nat) (vals : Nat → E) : List Pop := (List.range 22).flatMap (spGroupPops d vals)

/-- The template's body before its return. -/
def spPreT : List Stmt :=
  spCopies ++ (spPowers ++ (spGs.1 ++ (spLast.1 ++ (spChecks ++
    (spLeafK.1 ++ [copyS (.n spLeafK.2.1) (.n spLeafK.2.2)])))))

theorem spBodyT_ret : spBodyT = spPreT ++ [.ret [.n spLeafK.2.1]] := by
  rw [spBodyT_parts, spPreT]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- **The template's body before its return pops its groups' entries**, from any valuation holding them. -/
theorem spPreT_pops {d : Nat → Nat} {vals : Nat → E} {σ : Val} (h : ∀ q < 22, SpGP d vals q σ) :
    FallPops rd σ spPreT (spPopsT d vals) := by
  have hg := spGL_pops (rd := rd) d vals 22 0 fun q _ hq => h q hq
  simp only [Nat.zero_add] at hg
  rw [spGL_full] at hg
  have e : spPreT = spCopies ++ (spPowers ++ ((spGs.1 ++ spLast.1) ++ (spChecks ++
      (spLeafK.1 ++ [copyS (.n spLeafK.2.1) (.n spLeafK.2.2)])))) := by
    simp only [spPreT, List.append_assoc]
  have s : ∀ {α : Type} (F : List α), [] ++ ([] ++ (F ++ ([] ++ ([] ++ [])))) = F := by
    intros; simp only [List.nil_append, List.append_nil]
  rw [e]
  exact FallPops.congr_pops ((fallPops_quiet σ rfl).append ((fallPops_quiet σ rfl).append (hg.append
    ((fallPops_quiet σ rfl).append ((fallPops_quiet σ (kMsg_quiet _ _ _ _ _ _ _)).append
      (fallPops_quiet σ rfl)))))) (s _)

/-! ## In the guest's numbering -/

theorem mem_valsList_append_left {xs ys : List Stmt} {v : V} (h : v ∈ Stmt.valsList xs) :
    v ∈ Stmt.valsList (xs ++ ys) := by
  rw [valsList_append]; exact List.mem_append_left _ h

/-- **`sp_wots` is complete, popping its groups' entries**: `sp_wots_complete_cells`, and on the completing valuation its path returns setting up no call and popping `spPopsT d vals`. -/
theorem sp_wots_complete_cells_pops {pp a0 a1 : E} {d : Nat → Nat} (hd : ∀ i, d i < 4)
    (hsum : ∑ i ∈ Finset.range 64, d i = 128) {vals : Nat → E} (hm : MemOK rd 64) :
    ∃ σ : Val, σ (.n 0) = pp ∧ σ (.n 1) = a0 ∧ σ (.n 2) = a1 ∧ σ (.n 3) = eOfNat128 (spX d 64) ∧
      Stmt.HoldsList C rd σ (Fn.«sp_wots».core).body False (fun rs => rs = [spLeafCell pp a0 a1 d vals]) ∧
      ∃ es vs, walk σ (Fn.«sp_wots».core).body = .ret es vs ∧ calls es = [] ∧ evPops rd σ es = spPopsT d vals := by
  obtain ⟨σ', h0, h1, h2, h3, hgp, hh⟩ :=
    sp_wots_completeT_vals (C := C) (pp := pp) (a0 := a0) (a1 := a1) (vals := vals) hd hsum hm
  have e : ∀ j ≤ 29, (σ' ∘ spUn) (.n j) = σ' (.n j) := fun j hj => by
    simp [spUn, spRi_small hj, V.n]
  refine ⟨σ' ∘ spUn, by rw [e 0 (by norm_num), h0], by rw [e 1 (by norm_num), h1],
    by rw [e 2 (by norm_num), h2], by rw [e 3 (by norm_num), h3], ?_, ?_⟩
  · rw [spBody_eq, spBody, Stmt.holdsList_rename]
    refine (holdsList_congr spBodyT (fun v hv => ?_) _ _).mpr hh
    simp only [Function.comp_apply, spUn_spRen v hv]
  · have hp := spPreT_pops (rd := rd) hgp
    have hp' : FallPops rd ((σ' ∘ spUn) ∘ spRen) spPreT (spPopsT d vals) := hp.congr fun v hv => by
      have hv' : v ∈ Stmt.valsList spBodyT := by rw [spBodyT_ret]; exact mem_valsList_append_left hv
      simp only [Function.comp_apply, spUn_spRen v hv']
    obtain ⟨es, hw, hc, hps⟩ := retPops_of_fallPops (vs := [spRen (.n spLeafK.2.1)]) (FallPops.rename spRen hp')
    refine ⟨es, [spRen (.n spLeafK.2.1)], ?_, hc, hps⟩
    rw [spBody_eq, spBody, spBodyT_ret, renameList_append]
    exact hw

/-! ## Against the statement -/

/-- **`sp_wots`'s entries** for a digest and chain values: each group's word of the digest's `base_2b` digits, then its chains' values. -/
def spWotsPops (digest : HashSig.Digest) (values : Sphincs.ChainIndex → HashSig.Digest) : List Pop :=
  spPopsT (spDigitsOf digest) (spValsOf values)

/-- **`sp_wots` is complete, popping its entries**: `sp_wots_complete_Spec`, and on the completing valuation its path returns setting up no call and popping `spWotsPops digest values`. -/
theorem sp_wots_complete_pops (C : CallRel) (rd : Reader) (publicSeed : HashSig.PublicParameter)
    (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex) (digest : HashSig.Digest)
    (values : Sphincs.ChainIndex → HashSig.Digest) (hm : MemOK rd 64)
    (hT : Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits digest)) :
    ∃ σ : Val, σ (.n 0) = cellOf128 publicSeed ∧
      (σ (.n 1), σ (.n 2)) = keyAdrsCells layer.val tree.val leaf.val ∧
      σ (.n 3) = cellOf128 digest ∧
      Stmt.HoldsList C rd σ (Fn.«sp_wots».core).body False
        (fun rs => rs = [cellOf128 (wotsLeafOf publicSeed layer tree leaf digest values)]) ∧
      ∃ es vs, walk σ (Fn.«sp_wots».core).body = .ret es vs ∧ calls es = [] ∧
        evPops rd σ es = spWotsPops digest values := by
  have hpk : keyAdrsCells layer.val tree.val leaf.val =
      (adrsCell0 layer.val tree.val, adrsCell1 0 leaf.val 0 0) := rfl
  obtain ⟨σ, h0, h1, h2, h3, hh, hp⟩ := sp_wots_complete_cells_pops (C := C) (rd := rd)
    (pp := cellOf128 publicSeed) (a0 := adrsCell0 layer.val tree.val) (a1 := adrsCell1 0 leaf.val 0 0)
    (vals := spValsOf values) (spDigitsOf_lt digest) (spDigitsOf_sum hT) hm
  have hleaf : spLeafCell (cellOf128 publicSeed) (adrsCell0 layer.val tree.val)
      (adrsCell1 0 leaf.val 0 0) (spDigitsOf digest) (spValsOf values) =
      cellOf128 (wotsLeafOf publicSeed layer tree leaf digest values) := by
    have e := wotsLeafOf_cells (cellOf128 publicSeed) layer tree leaf digest (spDigitsOf digest)
      (spValsOf values) (spDigitsOf_eq digest)
    have ev : (fun i : Sphincs.ChainIndex => cellVal (spValsOf values i.val)) = values := by
      funext i
      have hi : i.val < 64 := i.isLt
      simp only [spValsOf, hi, ↓reduceDIte]
      exact cellVal_cellOf128 _
    rw [ev, cellVal_cellOf128] at e
    rw [e]
    exact (cellOf128_cellVal _).symm
  refine ⟨σ, h0, by rw [hpk, h1, h2], by rw [h3, spX_digest]; exact (cellOf128_eq_eOfNat128' digest).symm,
    by rw [← hleaf]; exact hh, hp⟩

end
end LeanVM.Guest.B1.Sig
