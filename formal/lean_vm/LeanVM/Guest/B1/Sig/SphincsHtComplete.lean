/-
  LeanVM.Guest.B1.Sig.SphincsHtComplete

  A layer of `verify_sig_lean_sphincs` (`sp_layer`, `lean_ethereum.py:4129-4140`) is complete: its counter hinted as `BE_32(N)`'s marks and read, then the layer.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsCompleteBlocks
public import LeanVM.Guest.B1.Sig.KMsgComplete

/-!
# A layer, complete

Layer `l` of the body (`sLayerAt l (sA0Of l) (sA1Of l) (sSignedOf l)`, from `sLayerBase l`) is the
counter's four marks hinted (`sp_counter`), read by `sp_from_bytes` (`CounterCompletes`) into
`sCtrOf l`, then `sHtLayer` (`HtLayerCompletes`). `sLayerAt_complete`: with the marks of
`BE_32(N)`, the call relation holding of `sp_wots` on the encoding of `N` and a leaf `lv`, the
layer reaches `pFold` of `pNodeE` from `lv`, and its bytes are read through the byte table.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- What layer `l` signs: the FORS key, then the root of the layer below. -/
def sSignedOf (l : Nat) : V := if l = 0 then sForsPk else if l = 1 then sLayerB.2.2 else sLayerM.2.2

/-- Layer `l` of the body. -/
def sLayerBlk (l : Nat) : List Stmt × Nat × V := sLayerAt l (sA0Of l) (sA1Of l) (sSignedOf l)

theorem sLayerBlk_eq : sLayerBlk 0 = sLayerB ∧ sLayerBlk 1 = sLayerM ∧ sLayerBlk 2 = sLayerT :=
  ⟨rfl, rfl, rfl⟩

/-- Layer `l`'s counter. -/
def sCtrBlock (l : Nat) : List Stmt × Nat × V := sFromMarks (sLayerBase l) 4 (sLayerBase l + 4)

theorem sCtrBlock_out (l : Nat) :
    (sCtrBlock l).2.2 = sCtrOf l ∧ (sCtrBlock l).2.1 = sLayerBase l + 37 := by
  constructor <;> rfl

/-- Layer `l` after its counter. -/
def sHtBlock (l : Nat) : List Stmt × Nat × V :=
  sHtLayer sPad sPP (sA0Of l) (sA1Of l) (sSignedOf l) (sCtrOf l) sLeafBit sLVal (sOffOf l)
    (sHeightOf l) (sLayerBase l + 37)

theorem sLayerBlk_split (l : Nat) :
    sLayerBlk l = ([hintW "sp_counter" (runV (sLayerBase l) 4)] ++ ((sCtrBlock l).1 ++ (sHtBlock l).1),
      (sHtBlock l).2.1, (sHtBlock l).2.2) := by
  simp only [sLayerBlk, sLayerAt, sHtBlock, sCtrBlock, List.append_assoc]
  rfl

/-- The shapes of the three layers: their values, their ends, the bases of what they read. -/
structure LayerShape (l : Nat) : Prop where
  ctr_nb : NumBelow (sLayerBase l + 37) (Stmt.valsList (sCtrBlock l).1)
  ht_nb : NumBelow (sHtBlock l).2.1 (Stmt.valsList (sHtBlock l).1)
  ht_le : sLayerBase l + 37 ≤ (sHtBlock l).2.1
  ht_ptrs : loadPtrs (sHtBlock l).1 = []
  ctr_ptrs : ∀ q ∈ loadPtrs (sCtrBlock l).1, q ∈ (List.range 4).map (fbPtr (sLayerBase l + 4))
  a0 : NBv (sLayerBase l) (sA0Of l)
  a1 : NBv (sLayerBase l) (sA1Of l)
  signed : NBv (sLayerBase l) (sSignedOf l)
  pad : sPad + 5 ≤ sLayerBase l
  two : 2 ≤ sLayerBase l
  digest : 1372 ≤ sLayerBase l

theorem layerShape_zero : LayerShape 0 :=
  ⟨numBelow_of_all (by decide +kernel), numBelow_of_all (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel, ⟨1379, by decide, rfl⟩, ⟨1381, by decide, rfl⟩,
    ⟨5248, by decide, rfl⟩, by decide, by decide, by decide⟩

theorem layerShape_one : LayerShape 1 :=
  ⟨numBelow_of_all (by decide +kernel), numBelow_of_all (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel, ⟨5404, by decide, rfl⟩, ⟨5406, by decide, rfl⟩,
    ⟨(sLayerB.2.2).idx, by decide +kernel, by decide +kernel⟩, by decide, by decide, by decide⟩

theorem layerShape_two : LayerShape 2 :=
  ⟨numBelow_of_all (by decide +kernel), numBelow_of_all (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel, ⟨5561, by decide, rfl⟩, ⟨5560, by decide, rfl⟩,
    ⟨(sLayerM.2.2).idx, by decide +kernel, by decide +kernel⟩, by decide, by decide, by decide⟩

theorem layerShape {l : Nat} (hl : l < 3) : LayerShape l := by
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
  · exact layerShape_zero
  · exact layerShape_one
  · exact layerShape_two

/-- **Layer `l` completes**: its counter hinted as the marks of `BE_32(N)`, the call relation
holding of `sp_wots` on the encoding of `N` and a leaf `lv`, the leaf `e` read off the digest's
bits and shifts, any siblings: the layer's root is `pFold` of `pNodeE` from
`lv`, and its bytes are the table's. -/
theorem sLayerBlk_complete (hB : SphincsBlocksComplete) (hm : MemOK rd 256) {bb : E}
    (hbb : ByteBits rd bb) {l : Nat} (hl : l < 3) {N : Nat} (hN : N < 2 ^ 32) {lv : E} {e : Nat}
    {sib : Nat → E} (σ : Val) (h1 : σ (.n 1) = bb) (hp : PadOK σ sPad)
    (hcall : C "sp_wots" [σ sPP, σ (sA0Of l), σ (sA1Of l),
      encDigestCell (σ sPP) (σ (sA0Of l)) (σ (sA1Of l) + lit (7 * 2 ^ 24)) (σ (sSignedOf l))
        (eOfNat (beWordAt 0 N))] [lv])
    (he : e < 2 ^ sHeightOf l)
    (hbit : ∀ z < sHeightOf l, σ (sLeafBit (sOffOf l + z)) = if e.testBit z then 1 else 0)
    (hval : ∀ z < sHeightOf l, σ (sLVal (sOffOf l + z)) = eOfNat (e >>> z)) :
    Completes C rd (sLayerBase l) (sLayerBlk l).2.1 (sLayerBlk l).1 σ (fun σ' =>
      σ' (sLayerBlk l).2.2 = pFold (pNodeE (σ sPP) (σ (sA0Of l)) e sib) (sHeightOf l) lv ∧
        TablePtrs bb σ' (sLayerBlk l).1) := by
  have S := layerShape hl
  rw [sLayerBlk_split]
  dsimp only
  have hB0 : sLayerBase l + 4 ≤ sLayerBase l + 37 := by omega
  refine Completes.append (m := sLayerBase l + 4) (by omega) (by have := S.ht_le; omega)
    (by rw [valsList_hint]; exact fun v hv => runV_nb (le_refl _) v hv)
    (hintRun_complete σ "sp_counter" (sLayerBase l) 4
      fun k => ofK (addressOfIndex (beWordAt 0 N / 256 ^ k % 256)))
    (fun σ1 he1 hm1 => ?_)
  have t1 : ∀ k < sLayerBase l, σ1 (.n k) = σ (.n k) := fun k hk => he1.apply (Or.inl hk)
  refine Completes.append (m := sLayerBase l + 37)
    (P := fun σ' => σ' (sCtrBlock l).2.2 = eOfNat (beWordAt 0 N % 256 ^ 4) ∧
      ∀ k ≤ 4 - 1, BytePtr bb (σ' (.n (fbPtr (sLayerBase l + 4) k))))
    hB0 S.ht_le S.ctr_nb
    (sFromMarks_complete (C := C) hm hbb (b := sLayerBase l) (n := 4) (x := sLayerBase l + 4)
      (X := beWordAt 0 N) (by norm_num) (by norm_num) σ1 (by omega) le_rfl hm1
      (by rw [t1 1 (by have := S.digest; omega)]; exact h1))
    (fun σ2 he2 hP2 => ?_)
  obtain ⟨hctr, hptr⟩ := hP2
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (beWordAt_zero_lt N) (by norm_num))] at hctr
  have t2 : ∀ k < sLayerBase l, σ2 (.n k) = σ (.n k) := fun k hk => by
    rw [he2.apply (Or.inl (by omega)), t1 k hk]
  have tv : ∀ v : V, NBv (sLayerBase l) v → σ2 v = σ v := fun v ⟨k, hk, ek⟩ => by rw [ek]; exact t2 k hk
  have hpp' : σ2 sPP = σ sPP := tv sPP ⟨2, by have := S.digest; omega, rfl⟩
  have ha0 := tv _ S.a0
  have ha1 := tv _ S.a1
  have hsg := tv _ S.signed
  rw [(sCtrBlock_out l).1] at hctr
  have hL := hB.layer C rd σ2 l (sA0Of l) (sA1Of l) (sSignedOf l) (sCtrOf l) (sLayerBase l + 37) lv e sib
    hl (by have := S.digest; omega) (S.a0.mono' (by omega)) (S.a1.mono' (by omega))
    (S.signed.mono' (by omega)) ⟨sLayerBase l + 36, by omega, rfl⟩
    (hp.congr (b := sLayerBase l) S.pad fun j hj => (t2 j hj).symm) ⟨N, hN, hctr⟩
    (by rw [hpp', ha0, ha1, hsg, hctr]; exact hcall) he
    (fun z hz => by
      obtain ⟨k, hk, ek⟩ := sLeafBit_lt (b := sOffOf l + z) (sOff_lt hl hz)
      rw [ek, t2 k (by have := S.digest; omega), ← ek]; exact hbit z hz)
    (fun z hz => by
      obtain ⟨k, hk, ek⟩ := sLVal_below (sOffOf l + z)
      rw [ek, t2 k (by have := S.digest; omega), ← ek]; exact hval z hz)
  obtain ⟨σ3, he3, hp3, hh3⟩ := hL
  refine ⟨σ3, he3, ⟨hp3.trans (by rw [hpp', ha0]), ?_⟩, hh3⟩
  refine TablePtrs.append (TablePtrs.nil_of rfl) (TablePtrs.append ?_ (TablePtrs.nil_of S.ht_ptrs))
  intro q hq
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp (S.ctr_ptrs q hq)
  have hk4 := List.mem_range.mp hk
  rw [he3.apply (Or.inl (by simp only [fbPtr]; split <;> omega))]
  exact hptr k (by omega)

end
end LeanVM.Guest.B1.Sig
