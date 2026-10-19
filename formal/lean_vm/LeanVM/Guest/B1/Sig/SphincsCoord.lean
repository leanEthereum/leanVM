/-
  LeanVM.Guest.B1.Sig.SphincsCoord

  One coordinate of the leanSPHINCS forest in `verify_sig_lean_sphincs` (G:2555-2580): the tree's
  leaf and both sub-trees' keys hinted in the exponent and dispatched, the forest keys, the folds
  and the super-child, sound for `coordRecover`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsKey
public import LeanVM.Guest.B1.Sig.SphincsFold

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The forest keys are sound under the call relation `C`. -/
def FkSound (C : CallRel) (rd : Reader) : Prop :=
  ∀ t < 256, ∀ args rets, C (fkNames.getD t "") args rets → Meaning_sp_forest_key t rd args rets

theorem fkSound_rel : FkSound (coreProgram.Rel rd) rd := fun _ ht _ _ h => sp_forest_key_sound ht h

set_option maxRecDepth 10000 in
theorem fkNames_length : fkNames.length = 256 := rfl

theorem holdsList_cons_dispatch (x : V) (fs : List String) (args rets : List V) (ss : List Stmt) (next : Prop)
    (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsList C rd σ (.dispatch x fs args rets :: ss) next kret ↔
      (∃ (j : Nat) (h : j < fs.length), σ x = ofK (gpow j) ∧ C fs[j] (args.map σ) (rets.map σ)) ∧
        Stmt.HoldsList C rd σ ss next kret := Iff.rfl

/-! ## A sub-tree -/

/-- **A sub-tree is sound**: the forest key of codeword `t` at the key's address, folded up two
levels at key `a`, lands in the output the key's top bit names; the codeword's cell is `t`; the
bound gains the key's field. -/
theorem sSub_sound (hfk : FkSound C rd) {σ : Val} (hmd : σ (.n 3) = mdw 64 true) {c j : Nat} {subAt bound : V}
    {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (sSub c j subAt bound b).1 next kret) :
    (∃ t < 256, ∃ a < 8, ∃ vals sibs : Nat → E, σ (.n (b + 1)) = word (a * 2 ^ 40) 0 0 ∧
      σ (sSub c j subAt bound b).2.2.1 = word t 0 0 ∧
      σ ((sSub c j subAt bound b).2.2.2.1 (2 * (a / 4))) =
        mFold (σ (.n 1)) (foldAddr σ subAt subFoldT a) (fun l => a.testBit l) sibs 2 0
          (fkLeaf t (σ (.n 1)) (σ subAt + word (a * 2 ^ 40) 0 0) vals) ∧
      σ (sSub c j subAt bound b).2.2.2.2 = σ bound + lit (a * 2 ^ (58 + 3 * (2 * c + j)))) ∧ next := by
  simp only [sSub, hintW, rangeS, cst, addS, List.cons_append, List.nil_append, holdsList_cons_atom,
    Atom.Holds, true_and] at h
  obtain ⟨-, -, -, -, hadd, h⟩ := h
  obtain ⟨⟨t, ht, -, hC⟩, h⟩ := (holdsList_cons_dispatch _ _ _ _ _ _ _ _).mp h
  rw [fkNames_length] at ht
  obtain ⟨ka, pp, hargs, vals, hrets⟩ := hfk t ht _ _ (by rw [List.getD_eq_getElem _ _ (by rw [fkNames_length]; exact ht)]; exact hC)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs hrets
  obtain ⟨a, ha, -, ⟨sibs, hs⟩, h1, h2, h⟩ := spMatch_sound hmd (by decide) h
  simp only [holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
  obtain ⟨hb, hn⟩ := h
  refine ⟨⟨t, ht, a, ha, vals, sibs, h1, hrets.2, ?_, ?_⟩, hn⟩
  · have e : a / 2 ^ (subFoldT.height - 1) = a / 4 := rfl
    rw [e] at hs
    refine hs.trans ?_
    rw [hrets.1, ← hargs.1, ← hargs.2, hadd, h1]
    rfl
  · exact hb.trans (by rw [h2])

/-! ## Addresses -/

theorem sp_add_word {k q B : Nat} (hB : B < 2 ^ k) : eOfNat B + word (2 ^ k * q) 0 0 = eOfNat (2 ^ k * q + B) := by
  rw [word_eq_eOfNat, add_comm, eOfNat_add_of_lt hB]

theorem sp_addrNat {tag step hi lo : Nat} (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 24) (ht : tag < 32) (hs : step < 8) :
    addrNat tag step hi lo = lo + 2 ^ 32 * hi + 2 ^ 56 * (tag + 32 * step) := by
  simp only [addrNat, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hs]

/-- The address of a node of the forest: instance `idx`, the packed position from bit 32. -/
def fpos (index c s j a : Nat) : Nat := index + 2 ^ 32 * (c + 8 * s + 128 * j + 256 * a)

theorem fpos_lt {index c s j a : Nat} (hi : index < 2 ^ 26) (hc : c < 8) (hs : s < 16) (hj : j < 2) (ha : a < 8) :
    fpos index c s j a < 2 ^ 43 := by
  unfold fpos; omega

theorem sp_tweak_fchain (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) (j : Sphincs.SubIdx)
    (a : Sphincs.ChildIdx) (i : Sphincs.FChain) (t : Sphincs.FStep) :
    Sphincs.tweakBytes (.fchain index c s j a i t) =
      cellBytes (eOfNat (addrNat 15 t.val (Sphincs.chainSlot c s j a i) index.val)) := by
  rw [← sTweak]; rfl

theorem sp_tweak_childLeaf (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) (j : Sphincs.SubIdx)
    (a : Sphincs.ChildIdx) :
    Sphincs.tweakBytes (.childLeaf index c s j a) =
      cellBytes (eOfNat (addrNat 16 0 (Sphincs.childSlot c s j a) index.val)) := by
  rw [← sTweak]; rfl

theorem sp_tweak_subNode (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) (j : Sphincs.SubIdx)
    (l : Fin Sphincs.subHeight) (node : Sphincs.ChildIdx) :
    Sphincs.tweakBytes (.subNode index c s j l node) =
      cellBytes (eOfNat (addrNat 17 0 (Sphincs.subSlot c s j + 256 * (l.val + 1) + 1024 * node.val) index.val)) := by
  rw [← sTweak]; rfl

theorem sp_tweak_superChild (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) :
    Sphincs.tweakBytes (.superChild index c s) = cellBytes (eOfNat (addrNat 18 0 (c.val + 8 * s.val) index.val)) := by
  rw [← sTweak]; rfl

theorem sp_tweak_topNode (index : Sphincs.Index) (c : Sphincs.Coord) (l : Fin Sphincs.topHeight)
    (node : Sphincs.SuperIdx) :
    Sphincs.tweakBytes (.topNode index c l node) =
      cellBytes (eOfNat (addrNat 19 0 (c.val + 8 * (l.val + 1) + 64 * node.val) index.val)) := by
  rw [← sTweak]; rfl

theorem sp_add_eOfNat {k q B : Nat} (hB : B < 2 ^ k) : eOfNat B + eOfNat (2 ^ k * q) = eOfNat (2 ^ k * q + B) := by
  rw [add_comm, eOfNat_add_of_lt hB]

/-- The bounds of a forest position. -/
theorem fbounds (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) (j : Sphincs.SubIdx)
    (a : Sphincs.ChildIdx) : index.val < 2 ^ 26 ∧ c.val < 8 ∧ s.val < 16 ∧ j.val < 2 ∧ a.val < 8 :=
  ⟨index.isLt, c.isLt, s.isLt, j.isLt, a.isLt⟩

/-- A forest chain step's address. -/
theorem fchain_addr (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) (j : Sphincs.SubIdx)
    (a : Sphincs.ChildIdx) (i : Sphincs.FChain) (t : Sphincs.FStep) :
    cellBytes (eOfNat (fpos index.val c.val s.val j.val a.val) + eOfNat (tw 15 + i.val * 2 ^ 43 + t.val * stepMul)) =
      Sphincs.tweakBytes (.fchain index c s j a i t) := by
  obtain ⟨hi, hc, hs, hj, ha⟩ := fbounds index c s j a
  have hi6 : i.val < 6 := i.isLt
  have ht4 : t.val < 4 := t.isLt
  rw [sp_tweak_fchain, show tw 15 + i.val * 2 ^ 43 + t.val * stepMul =
      2 ^ 43 * (i.val + 2 ^ 13 * 15 + 2 ^ 18 * t.val) by simp only [tw, stepMul]; ring,
    sp_add_eOfNat (fpos_lt hi hc hs hj ha)]
  congr 2
  rw [sp_addrNat (by omega) (by simp only [Sphincs.chainSlot, Sphincs.childSlot, Sphincs.subSlot]; omega) (by omega)
    (by omega)]
  simp only [fpos, Sphincs.chainSlot, Sphincs.childSlot, Sphincs.subSlot]
  ring

/-- A child leaf's address. -/
theorem childLeaf_addr (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) (j : Sphincs.SubIdx)
    (a : Sphincs.ChildIdx) :
    cellBytes (eOfNat (fpos index.val c.val s.val j.val a.val) + eOfNat (tw 16)) =
      Sphincs.tweakBytes (.childLeaf index c s j a) := by
  obtain ⟨hi, hc, hs, hj, ha⟩ := fbounds index c s j a
  rw [sp_tweak_childLeaf, show tw 16 = 2 ^ 43 * (2 ^ 13 * 16) by simp only [tw]; ring,
    sp_add_eOfNat (fpos_lt hi hc hs hj ha)]
  congr 2
  rw [sp_addrNat (by omega) (by simp only [Sphincs.childSlot, Sphincs.subSlot]; omega) (by omega) (by omega)]
  simp only [fpos, Sphincs.childSlot, Sphincs.subSlot]
  ring

/-- A sub-tree node's address. -/
theorem subNode_addr (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) (j : Sphincs.SubIdx)
    (a : Sphincs.ChildIdx) (l : Fin Sphincs.subHeight) (node : Sphincs.ChildIdx)
    (hn : node.val = a.val / 2 ^ (l.val + 1)) :
    cellBytes (eOfNat (fpos index.val c.val s.val j.val 0) + word (subFoldT.addr a.val l.val) 0 0) =
      Sphincs.tweakBytes (.subNode index c s j l node) := by
  obtain ⟨hi, hc, hs, hj, ha⟩ := fbounds index c s j a
  have hl : l.val < 3 := l.isLt
  have hnode : node.val < 8 := node.isLt
  rw [sp_tweak_subNode, show subFoldT.addr a.val l.val =
      2 ^ 40 * (l.val + 1 + 4 * (a.val / 2 ^ (l.val + 1)) + 2 ^ 16 * 17) by
      simp only [subFoldT, Fold.addr, tw, hiMul]; ring,
    sp_add_word (by unfold fpos; omega)]
  congr 2
  rw [sp_addrNat (by omega) (by simp only [Sphincs.subSlot]; omega) (by omega) (by omega)]
  simp only [fpos, Sphincs.subSlot, hn]
  ring

/-- A super-child's address. -/
theorem superChild_addr (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) :
    cellBytes (eOfNat (fpos index.val c.val s.val 0 0) + word (tw 18) 0 0) =
      Sphincs.tweakBytes (.superChild index c s) := by
  obtain ⟨hi, hc, hs, -, -⟩ := fbounds index c s 0 0
  rw [sp_tweak_superChild, show tw 18 = 2 ^ 39 * (2 ^ 17 * 18) by simp only [tw]; ring,
    sp_add_word (by unfold fpos; omega)]
  congr 2
  rw [sp_addrNat (by omega) (by omega) (by omega) (by omega)]
  simp only [fpos]
  ring

/-- A top-tree node's address. -/
theorem topNode_addr (index : Sphincs.Index) (c : Sphincs.Coord) (s : Sphincs.SuperIdx) (l : Fin Sphincs.topHeight)
    (node : Sphincs.SuperIdx) (hn : node.val = s.val / 2 ^ (l.val + 1)) :
    cellBytes (eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr s.val l.val) 0 0) =
      Sphincs.tweakBytes (.topNode index c l node) := by
  obtain ⟨hi, hc, hs, -, -⟩ := fbounds index c s 0 0
  have hl : l.val < 4 := l.isLt
  have hnode : node.val < 16 := node.isLt
  rw [sp_tweak_topNode, show topFoldT.addr s.val l.val =
      2 ^ 35 * (l.val + 1 + 8 * (s.val / 2 ^ (l.val + 1)) + 2 ^ 21 * 19) by
      simp only [topFoldT, Fold.addr, tw, hiMul]; ring,
    sp_add_word (by unfold fpos; omega)]
  congr 2
  rw [sp_addrNat (by omega) (by omega) (by omega) (by omega)]
  simp only [fpos, hn]
  ring

/-! ## A coordinate in the scheme -/

section Scheme

open Sphincs Sphincs.Concrete

variable {inst : HasQuery Sphincs.HashSpec Id}

theorem sCoordRecover_id (P : PublicParameter) (index : Index) (c : Coord) (mark : CoordMark)
    (opening : CoordOpening) :
    @coordRecover Id _ inst P index c mark opening =
      orderTops (mark.super.val.testBit (topHeight - 1))
        (@topFold Id _ inst P index c mark.super opening.top (topHeight - 1)
          (@superHash Id _ inst P index c mark.super fun j =>
            orderTops ((mark.child j).val.testBit (subHeight - 1))
              (@subFold Id _ inst P index c mark.super j (mark.child j) (opening.sub j).path (subHeight - 1)
                (@childRecover Id _ inst P index c mark.super j (mark.child j) (lut (mark.word j))
                  (opening.sub j).values))
              ((opening.sub j).path subTopLevel)))
        (opening.top topTopLevel) := by
  rw [coordRecover.eq_def]
  simp only [bind, pure, sSequenceFin_id]

theorem orderTops_sv (bit : Bool) (x y : E) : orderTops bit (sv x) (sv y) = if bit then (sv y, sv x) else (sv x, sv y) := rfl

theorem testBit_top {a k : Nat} (ha : a < 2 ^ (k + 1)) : a.testBit k = decide (a / 2 ^ k = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have : a / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (by rw [pow_succ] at ha; exact ha)
  generalize a / 2 ^ k = q at this ⊢
  congr 1
  apply propext
  constructor <;> intro h <;> omega

/-- The chains of a forest key are the scheme's at the codeword's deficits. -/
theorem fkLeaf_eq (t : LutIdx) (pp ka : E) (vals : Nat → E) :
    fkLeaf t.val pp ka vals = (hcell (pp :: (ka + eOfNat (tw 16)) :: (List.range 6).map (fEnds pp ka (lut t) vals))).1 := by
  have e : (List.range 6).map (fun k => fChain pp ka k (4 - spCode t.val k) (vals k) (spCode t.val k)) =
      (List.range 6).map (fEnds pp ka (lut t) vals) := List.map_congr_left fun k hk => by
    rw [List.mem_range] at hk
    have hk' : (⟨k % 6, Nat.mod_lt _ (by norm_num)⟩ : FChain) = ⟨k, hk⟩ := Fin.ext (Nat.mod_eq_of_lt hk)
    rw [fEnds, hk', ← spCode_lut t.isLt ⟨k, hk⟩]
  rw [fkLeaf, e]

/-- **A sub-tree's two top nodes in the scheme**: the forest key folded two levels, and the other top
node, in the order of the key's top bit. -/
theorem sp_subTops (hq : SQ inst) {pp : E} (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
    (t : LutIdx) (vals sibs : Nat → E) {x y : E}
    (hx : (if a.val / 4 = 0 then x else y) =
      mFold pp (fun l => eOfNat (fpos index.val c.val s.val j.val 0) + word (subFoldT.addr a.val l) 0 0)
        (fun l => a.val.testBit l) sibs 2 0 (fkLeaf t.val pp (eOfNat (fpos index.val c.val s.val j.val a.val)) vals))
    (hy : (if a.val / 4 = 0 then y else x) = sibs 2) :
    orderTops (a.val.testBit (subHeight - 1))
      (@subFold Id _ inst (spp pp) index c s j a (fun l => sv (sibs l.val)) (subHeight - 1)
        (@childRecover Id _ inst (spp pp) index c s j a (lut t) (fun i => sv (vals i.val))))
      (sv (sibs 2)) = (sv x, sv y) := by
  rw [sChildRecover_cells hq (ka := eOfNat (fpos index.val c.val s.val j.val a.val)) (lut t) vals
      (fchain_addr index c s j a) (childLeaf_addr index c s j a), ← fkLeaf_eq,
    sSubFold_cells hq (A := fun l => eOfNat (fpos index.val c.val s.val j.val 0) + word (subFoldT.addr a.val l) 0 0)
      (fun l node hn => subNode_addr index c s j a l node hn) sibs (subHeight - 1) (by decide),
    show subHeight - 1 = 2 from rfl, ← hx, ← hy, orderTops_sv, testBit_top (show a.val < 2 ^ (2 + 1) from a.isLt)]
  have ha : a.val / 4 = 0 ∨ a.val / 4 = 1 := by have := a.isLt; simp only [subHeight] at this; omega
  rcases ha with h | h <;> simp [h]

/-- **A coordinate's two top nodes in the scheme.** -/
theorem sp_topTops (hq : SQ inst) {pp : E} (index : Index) (c : Coord) (s : SuperIdx) (tsibs : Nat → E) {x y sup : E}
    (hx : (if s.val / 8 = 0 then x else y) =
      mFold pp (fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr s.val l) 0 0)
        (fun l => s.val.testBit l) tsibs 3 0 sup)
    (hy : (if s.val / 8 = 0 then y else x) = tsibs 3) :
    orderTops (s.val.testBit (topHeight - 1))
      (@topFold Id _ inst (spp pp) index c s (fun l => sv (tsibs l.val)) (topHeight - 1) (sv sup))
      (sv (tsibs 3)) = (sv x, sv y) := by
  rw [sTopFold_cells hq (A := fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr s.val l) 0 0)
      (fun l node hn => topNode_addr index c s l node hn) tsibs (topHeight - 1) (by decide),
    show topHeight - 1 = 3 from rfl, ← hx, ← hy, orderTops_sv, testBit_top (show s.val < 2 ^ (3 + 1) from s.isLt)]
  have hs : s.val / 8 = 0 ∨ s.val / 8 = 1 := by have := s.isLt; simp only [topHeight] at this; omega
  rcases hs with h | h <;> simp [h]

end Scheme

/-! ## A coordinate -/

/-- Coordinate `c` after its tree's address `treeAt`, from base `b0`. -/
def sCoordT (c : Nat) (bound treeAt : V) (b0 : Nat) : List Stmt × Nat × (V × V) × (V × V) × V :=
  let leafAt := V.n (b0 + 6)
  let s0 := sSub c 0 leafAt bound (b0 + 7)
  let b1 := s0.2.1
  let s1 := sSub c 1 (.n (b1 + 1)) s0.2.2.2.2 (b1 + 2)
  let f := s1.2.1
  let sub0 := s0.2.2.2.1
  let sub1 := s1.2.2.2.1
  let arms := spArms (.n 1) (.n 3) treeAt (.n (f + 10)) topFoldT (spOut topFoldT (f + 12)) (.n (b0 + 1))
    (spRet2 topFoldT (f + 12)) (fun s => word (s * 2 ^ 35) 0 0) (fun s => lit (s * 2 ^ (26 + 4 * c))) 16 0 (f + 12)
  ([hintW "sp_leaves" [.n b0, .n (b0 + 1)]] ++ rangeS (.n b0) 16 (b0 + 2) ++
    [addS leafAt treeAt (.n (b0 + 1))] ++ s0.1 ++ [cst b1 (word (2 ^ 39) 0 0), addS (.n (b1 + 1)) leafAt (.n b1)] ++
    s1.1 ++ [cst f (word (tw 18) 0 0), addS (.n (f + 1)) leafAt (.n f)] ++ ivs (f + 2) ++
    [cst (f + 4) (mdw 64 false),
      b2s (.n 1) (.n (f + 1)) (sub0 0) (sub0 2) (.n (f + 2)) (.n (f + 3)) (.n (f + 5)) (.n (f + 6)) (.n (f + 4)),
      cst (f + 7) (word 0 0 0), cst (f + 8) (word 0 0 0), cst (f + 9) (mdw 96 true),
      b2s (sub1 0) (sub1 2) (.n (f + 7)) (.n (f + 8)) (.n (f + 5)) (.n (f + 6)) (.n (f + 10)) (.n (f + 11)) (.n (f + 9)),
      .match_ (.n b0) arms.1, addS (.n arms.2) s1.2.2.2.2 (spRet2 topFoldT (f + 12))], arms.2 + 1,
    (s0.2.2.1, s1.2.2.1), (spOut topFoldT (f + 12) 0, spOut topFoldT (f + 12) 2), .n arms.2)

theorem sCoord_eq (c : Nat) (bound : V) (b : Nat) :
    sCoord c bound b =
      ((if c = 0 then [] else [cst b (word (c * hiMul) 0 0), addS (.n (b + 1)) (.n 142) (.n b)]) ++
        (sCoordT c bound (if c = 0 then .n 142 else .n (b + 1)) (if c = 0 then b else b + 2)).1,
        (sCoordT c bound (if c = 0 then .n 142 else .n (b + 1)) (if c = 0 then b else b + 2)).2) := by
  simp only [sCoord, sCoordT, List.append_assoc]

/-- The tree's address of coordinate `c`. -/
theorem sPre_sound {σ : Val} {index c b : Nat} (hi : index < 2 ^ 26) (hc : c < 8) (hidx : σ (.n 142) = eOfNat index)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (if c = 0 then [] else [cst b (word (c * hiMul) 0 0), addS (.n (b + 1)) (.n 142) (.n b)])
      next kret) :
    σ (if c = 0 then .n 142 else .n (b + 1)) = eOfNat (fpos index c 0 0 0) ∧ next := by
  by_cases h0 : c = 0
  · subst h0
    simp only [↓reduceIte, holdsList_nil] at h ⊢
    exact ⟨by rw [hidx]; simp [fpos], h⟩
  · simp only [h0, ↓reduceIte, cst, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h ⊢
    obtain ⟨h1, h2, hn⟩ := h
    refine ⟨?_, hn⟩
    rw [h2, h1, hidx, show c * hiMul = 2 ^ 32 * c by simp only [hiMul]; ring, sp_add_word (by omega)]
    simp only [fpos]
    ring_nf

section Scheme

open Sphincs Sphincs.Concrete

variable {inst : HasQuery Sphincs.HashSpec Id}

/-- **A coordinate is sound** (after its tree's address): the scheme's two top nodes of the mark
and the opening it reads land in its outputs, the codeword cells are the mark's, and the bound
gains the mark's fields. -/
theorem sCoordT_sound (hq : SQ inst) (hfk : FkSound C rd) {σ : Val} (hmd : σ (.n 3) = mdw 64 true)
    (index : Index) (c : Coord) {bound treeAt : V} {b0 : Nat}
    (htree : σ treeAt = eOfNat (fpos index.val c.val 0 0 0)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (sCoordT c.val bound treeAt b0).1 next kret) :
    (∃ (mark : CoordMark) (opening : CoordOpening),
      @coordRecover Id _ inst (spp (σ (.n 1))) index c mark opening =
        (sv (σ (sCoordT c.val bound treeAt b0).2.2.2.1.1), sv (σ (sCoordT c.val bound treeAt b0).2.2.2.1.2)) ∧
      σ (sCoordT c.val bound treeAt b0).2.2.1.1 = word (mark.word 0).val 0 0 ∧
      σ (sCoordT c.val bound treeAt b0).2.2.1.2 = word (mark.word 1).val 0 0 ∧
      σ (sCoordT c.val bound treeAt b0).2.2.2.2 = σ bound + lit ((mark.child 0).val * 2 ^ (58 + 3 * (2 * c.val))) +
        lit ((mark.child 1).val * 2 ^ (58 + 3 * (2 * c.val + 1))) + lit (mark.super.val * 2 ^ (26 + 4 * c.val))) ∧
      next := by
  simp only [sCoordT] at h ⊢
  simp only [List.append_assoc, List.cons_append, List.nil_append, holdsList_append, hintW, rangeS, cst,
    addS, ivs, b2s, holdsList_cons_atom, Atom.Holds, true_and] at h
  obtain ⟨-, -, hleaf, h⟩ := h
  obtain ⟨⟨t0, ht0, a0, ha0, vals0, sibs0, hk0, hw0, ho0, hb0⟩, h⟩ := sSub_sound hfk hmd h
  obtain ⟨hb1, hsub1, h⟩ := h
  obtain ⟨⟨t1, ht1, a1, ha1, vals1, sibs1, hk1, hw1, ho1, hb1'⟩, h⟩ := sSub_sound hfk hmd h
  obtain ⟨hf0, hf1, hiv0, hiv1, hmd4, hc1, h7, h8, hmd9, hc2, h⟩ := h
  obtain ⟨s, hs, -, ⟨tsibs, hts⟩, hr1, hr2, h⟩ := spMatch_sound hmd (by decide) h
  simp only [holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
  obtain ⟨hbound, hn⟩ := h
  generalize sSub c.val 0 (.n (b0 + 6)) bound (b0 + 7) = S0 at *
  generalize sSub c.val 1 (.n (S0.2.1 + 1)) S0.2.2.2.2 (S0.2.1 + 2) = S1 at *
  -- the scheme's indices
  have hi := index.isLt
  have hc := c.isLt
  simp only [totalHeight, forestCoords] at hi hc
  let sF : SuperIdx := ⟨s, hs⟩
  let a0F : ChildIdx := ⟨a0, ha0⟩
  let a1F : ChildIdx := ⟨a1, ha1⟩
  let t0F : LutIdx := ⟨t0, ht0⟩
  let t1F : LutIdx := ⟨t1, ht1⟩
  -- the addresses
  have hLeaf : σ (.n (b0 + 6)) = eOfNat (fpos index.val c.val s 0 0) := by
    rw [hleaf, htree, hr1, show s * 2 ^ 35 = 2 ^ 35 * s by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hSub1 : σ (.n (S0.2.1 + 1)) = eOfNat (fpos index.val c.val s 1 0) := by
    rw [hsub1, hLeaf, hb1, show (2 : Nat) ^ 39 = 2 ^ 39 * 1 by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hKey0 : σ (.n (b0 + 6)) + word (a0 * 2 ^ 40) 0 0 = eOfNat (fpos index.val c.val s 0 a0) := by
    rw [hLeaf, show a0 * 2 ^ 40 = 2 ^ 40 * a0 by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hKey1 : σ (.n (S0.2.1 + 1)) + word (a1 * 2 ^ 40) 0 0 = eOfNat (fpos index.val c.val s 1 a1) := by
    rw [hSub1, show a1 * 2 ^ 40 = 2 ^ 40 * a1 by ring, sp_add_word (by unfold fpos; omega)]
    congr 1; unfold fpos; ring
  have hA0 : foldAddr σ (.n (b0 + 6)) subFoldT a0 =
      fun l => eOfNat (fpos index.val c.val s 0 0) + word (subFoldT.addr a0 l) 0 0 := by
    funext l; rw [foldAddr, hLeaf]
  have hA1 : foldAddr σ (.n (S0.2.1 + 1)) subFoldT a1 =
      fun l => eOfNat (fpos index.val c.val s 1 0) + word (subFoldT.addr a1 l) 0 0 := by
    funext l; rw [foldAddr, hSub1]
  have hAT : foldAddr σ treeAt topFoldT s = fun l => eOfNat (fpos index.val c.val 0 0 0) + word (topFoldT.addr s l) 0 0 := by
    funext l; rw [foldAddr, htree]
  rw [hKey0, hA0] at ho0
  rw [hKey1, hA1] at ho1
  rw [hAT, show s / 2 ^ (topFoldT.height - 1) = s / 8 from rfl] at hts
  -- the super-child
  have hiv1' : σ (.n (S1.2.1 + 3)) = iv1 := hiv1
  rw [hiv0, hiv1', hmd4] at hc1
  rw [h7, h8, hmd9, word_zero] at hc2
  have hr32 : ([σ (S1.2.2.2.1 0), σ (S1.2.2.2.1 2)].flatMap cellBytes).length = 32 := by
    rw [length_flatMap_cellBytes']; rfl
  have hc2' : CompressCells ![σ (S1.2.2.2.1 0), σ (S1.2.2.2.1 2), 0, 0] (σ (.n (S1.2.1 + 5)))
      (σ (.n (S1.2.1 + 6))) (σ (.n (S1.2.1 + 10))) (σ (.n (S1.2.1 + 11)))
      (mdw (64 + ([σ (S1.2.2.2.1 0), σ (S1.2.2.2.1 2)].flatMap cellBytes).length) true) := by rw [hr32]; exact hc2
  obtain ⟨-, -, -, hsup⟩ := (compress_two_iff (blockBytes_two _ _) (by rw [hr32]; omega) (by rw [hr32]; omega)).mp
    ⟨hc1, hc2'⟩
  have hsup' : σ (.n (S1.2.1 + 10)) = (hcell [σ (.n 1), eOfNat (fpos index.val c.val s 0 0) + word (tw 18) 0 0,
      σ (S0.2.2.2.1 0), σ (S0.2.2.2.1 2), σ (S1.2.2.2.1 0), σ (S1.2.2.2.1 2)]).1 := by
    refine (congrArg Prod.fst hsup).trans ?_
    rw [blockBytes_four, hcell, ← List.flatMap_append, hf1, hLeaf, hf0]
    rfl
  -- the mark and the opening
  let sib0 : Nat → E := fun l => if l = 2 then σ (S0.2.2.2.1 (2 - 2 * (a0 / 4))) else sibs0 l
  let sib1 : Nat → E := fun l => if l = 2 then σ (S1.2.2.2.1 (2 - 2 * (a1 / 4))) else sibs1 l
  let tsib : Nat → E := fun l => if l = 3 then σ (spOut topFoldT (S1.2.1 + 12) (2 - 2 * (s / 8))) else tsibs l
  let mark : CoordMark := ⟨sF, ![a0F, a1F], ![t0F, t1F]⟩
  let opening : CoordOpening :=
    ⟨![⟨fun i => sv (vals0 i.val), fun l => sv (sib0 l.val)⟩, ⟨fun i => sv (vals1 i.val), fun l => sv (sib1 l.val)⟩],
      fun l => sv (tsib l.val)⟩
  have ha0' : a0 / 4 = 0 ∨ a0 / 4 = 1 := by omega
  have ha1' : a1 / 4 = 0 ∨ a1 / 4 = 1 := by omega
  have hs' : s / 8 = 0 ∨ s / 8 = 1 := by omega
  have hsub : (fun j : SubIdx => orderTops ((mark.child j).val.testBit (subHeight - 1))
      (@subFold Id _ inst (spp (σ (.n 1))) index c mark.super j (mark.child j) (opening.sub j).path (subHeight - 1)
        (@childRecover Id _ inst (spp (σ (.n 1))) index c mark.super j (mark.child j) (lut (mark.word j))
          (opening.sub j).values))
      ((opening.sub j).path subTopLevel)) =
      fun j => if j = 0 then (sv (σ (S0.2.2.2.1 0)), sv (σ (S0.2.2.2.1 2)))
        else (sv (σ (S1.2.2.2.1 0)), sv (σ (S1.2.2.2.1 2))) := by
    funext j
    fin_cases j
    · refine sp_subTops hq index c sF 0 a0F t0F vals0 sib0 ?_ ?_
      · refine (?_ : _ = _).trans (ho0.trans (mFold_congr _ _ _ 2 0
          (fun l _ hl => by simp only [sib0, show l ≠ 2 by omega, ↓reduceIte]) _))
        rcases ha0' with h | h <;> simp [h, a0F]
      · rcases ha0' with h | h <;> simp [sib0, h, a0F]
    · refine sp_subTops hq index c sF 1 a1F t1F vals1 sib1 ?_ ?_
      · refine (?_ : _ = _).trans (ho1.trans (mFold_congr _ _ _ 2 0
          (fun l _ hl => by simp only [sib1, show l ≠ 2 by omega, ↓reduceIte]) _))
        rcases ha1' with h | h <;> simp [h, a1F]
      · rcases ha1' with h | h <;> simp [sib1, h, a1F]
  refine ⟨⟨mark, opening, ?_, hw0, hw1, ?_⟩, hn⟩
  · rw [sCoordRecover_id, hsub, sSuperHash_cells hq (superChild_addr index c sF), ← hsup']
    refine sp_topTops hq index c sF tsib ?_ ?_
    · refine (?_ : _ = _).trans (hts.trans (mFold_congr _ _ _ 3 0
        (fun l _ hl => by simp only [tsib, show l ≠ 3 by omega, ↓reduceIte]) _))
      rcases hs' with h | h <;> simp [h, sF]
    · rcases hs' with h | h <;> simp [tsib, h, sF]
  · rw [hbound, hb1', hb0, hr2]
    rfl

/-- **A coordinate is sound.** -/
theorem sCoord_sound (hq : SQ inst) (hfk : FkSound C rd) {σ : Val} (hmd : σ (.n 3) = mdw 64 true)
    (index : Index) (c : Coord) (hidx : σ (.n 142) = eOfNat index.val) {bound : V} {b : Nat} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (sCoord c.val bound b).1 next kret) :
    (∃ (mark : CoordMark) (opening : CoordOpening),
      @coordRecover Id _ inst (spp (σ (.n 1))) index c mark opening =
        (sv (σ (sCoord c.val bound b).2.2.2.1.1), sv (σ (sCoord c.val bound b).2.2.2.1.2)) ∧
      σ (sCoord c.val bound b).2.2.1.1 = word (mark.word 0).val 0 0 ∧
      σ (sCoord c.val bound b).2.2.1.2 = word (mark.word 1).val 0 0 ∧
      σ (sCoord c.val bound b).2.2.2.2 = σ bound + lit ((mark.child 0).val * 2 ^ (58 + 3 * (2 * c.val))) +
        lit ((mark.child 1).val * 2 ^ (58 + 3 * (2 * c.val + 1))) + lit (mark.super.val * 2 ^ (26 + 4 * c.val))) ∧
      next := by
  rw [sCoord_eq] at h ⊢
  rw [holdsList_append] at h
  obtain ⟨htree, h⟩ := sPre_sound index.isLt c.isLt hidx h
  exact sCoordT_sound hq hfk hmd index c htree h

/-- What coordinate `c` of a mark weighs in the digest's second cell. -/
def coordWeight (c : Nat) (mark : CoordMark) : E :=
  lit ((mark.child 0).val * 2 ^ (58 + 3 * (2 * c))) + lit ((mark.child 1).val * 2 ^ (58 + 3 * (2 * c + 1))) +
    lit (mark.super.val * 2 ^ (26 + 4 * c))

/-- **The coordinates are sound.** -/
theorem sCoords_sound (hq : SQ inst) (hfk : FkSound C rd) {σ : Val} (hmd : σ (.n 3) = mdw 64 true)
    (index : Index) (hidx : σ (.n 142) = eOfNat index.val) :
    ∀ (m c : Nat) (bound : V) (b : Nat) {next : Prop} {kret : List E → Prop} (_ : c + m ≤ 8),
      Stmt.HoldsList C rd σ (sCoords m c bound b).1 next kret →
      (∃ (marks : Nat → CoordMark) (openings : Nat → CoordOpening),
        (∀ r (hr : r < m),
          @coordRecover Id _ inst (spp (σ (.n 1))) index ⟨c + r, by simp only [forestCoords]; omega⟩
              (marks (c + r)) (openings (c + r)) =
            (sv (σ ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).1),
              sv (σ ((sCoords m c bound b).2.2.2.1.getD r (.n 0, .n 0)).2)) ∧
          σ ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).1 = word ((marks (c + r)).word 0).val 0 0 ∧
          σ ((sCoords m c bound b).2.2.1.getD r (.n 0, .n 0)).2 = word ((marks (c + r)).word 1).val 0 0) ∧
        σ (sCoords m c bound b).2.2.2.2 = σ bound + ∑ r ∈ Finset.range m, coordWeight (c + r) (marks (c + r))) ∧
      next
  | 0, _, bound, _, _, _, _, h => ⟨⟨fun _ => ⟨0, fun _ => 0, fun _ => 0⟩, fun _ => ⟨fun _ => ⟨fun _ => 0, fun _ => 0⟩,
      fun _ => 0⟩, fun _ h => absurd h (by omega), by simp [sCoords]⟩, h⟩
  | m + 1, c, bound, b, next, kret, hcm, h => by
      simp only [sCoords, holdsList_append] at h ⊢
      obtain ⟨⟨mark, opening, hrec, hw0, hw1, hb⟩, h⟩ :=
        sCoord_sound hq hfk hmd index ⟨c, by simp only [forestCoords]; omega⟩ hidx h
      obtain ⟨⟨marks, openings, hr, hbs⟩, hn⟩ := sCoords_sound hq hfk hmd index hidx m (c + 1) _ _ (by omega) h
      refine ⟨⟨fun k => if k = c then mark else marks k, fun k => if k = c then opening else openings k,
        fun r hr' => ?_, ?_⟩, hn⟩
      · rcases r with _ | r
        · simp only [Nat.add_zero, ↓reduceIte, List.getD_cons_zero]
          exact ⟨hrec, hw0, hw1⟩
        · have := hr r (by omega)
          simp only [List.getD_cons_succ, show c + (r + 1) ≠ c by omega, ↓reduceIte]
          have hF : (⟨c + (r + 1), by simp only [forestCoords]; omega⟩ : Coord) =
              ⟨c + 1 + r, by simp only [forestCoords]; omega⟩ := Fin.ext (by simp only; omega)
          rw [hF, show c + (r + 1) = c + 1 + r by omega]
          exact this
      · have hsum : ∑ r ∈ Finset.range m, coordWeight (c + (r + 1))
            ((fun k => if k = c then mark else marks k) (c + (r + 1))) =
            ∑ r ∈ Finset.range m, coordWeight (c + 1 + r) (marks (c + 1 + r)) :=
          Finset.sum_congr rfl fun r _ => by
            simp only [show c + (r + 1) = c + 1 + r by omega, show c + 1 + r ≠ c by omega, ↓reduceIte]
        rw [hbs, hb, Finset.sum_range_succ', hsum]
        simp only [Nat.add_zero, ↓reduceIte]
        rw [coordWeight]
        abel

end Scheme

end
end LeanVM.Guest.B1.Sig
