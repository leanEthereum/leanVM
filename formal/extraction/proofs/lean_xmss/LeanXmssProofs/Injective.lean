import LeanXmssProofs.Common

/-!
# Distinct Rust inputs are distinct statement inputs

`toPublicKey`, `toMessage` and `toSignature` (`Defs.lean`, `Keccak256Proofs.Defs`) lose nothing:
each is injective. The theorem about `verify` does not use this; it is what makes "the statement's
verdict on the values the arguments stand for" a statement about every Rust input separately.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation LeanXmss
open lean_xmss
open Keccak256Proofs

namespace LeanXmssProofs

theorem toPublicKey_inj {a b : scheme.LeanXmssPublicKey} (h : toPublicKey a = toPublicKey b) :
    a = b := by
  obtain ⟨ra, pa⟩ := a
  obtain ⟨rb, pb⟩ := b
  injection h with h1 h2
  obtain rfl : ra = rb := toDigest_inj h1
  obtain rfl : pa = pb := toDigest_inj h2
  rfl

/-- Arrays of digests that stand for the same statement digests at every index are equal. -/
theorem digests_inj {N : Std.Usize} {a b : Array (Array Std.U8 16#usize) N}
    (h : ∀ i < N.val, toDigest a.val[i]! = toDigest b.val[i]!) : a = b := by
  have ha : a.val.length = N.val := by simp
  have hb : b.val.length = N.val := by simp
  apply (Array.eq_iff a b).mpr
  apply List.ext_getElem (by rw [ha, hb])
  intro i h1 h2
  have := toDigest_inj (h i (by omega))
  rwa [getElem!_pos a.val i h1, getElem!_pos b.val i h2] at this

theorem toLayerSignature_inj {a b : scheme.LayerSignature}
    (h : toLayerSignature a = toLayerSignature b) : a = b := by
  obtain ⟨ra, ca, pa⟩ := a
  obtain ⟨rb, cb, pb⟩ := b
  injection h with hr hc hp
  obtain rfl : ra = rb := toDigest_inj hr
  obtain rfl : ca = cb := digests_inj (fun i hi => congrFun hc ⟨i, hi⟩)
  obtain rfl : pa = pb := digests_inj (fun i hi => congrFun hp ⟨i, hi⟩)
  rfl

theorem toSignature_inj {a b : scheme.LeanXmssSignature} (h : toSignature a = toSignature b) :
    a = b := by
  obtain ⟨ia, ba, ta⟩ := a
  obtain ⟨ib, bb, tb⟩ := b
  injection h with hi hl
  obtain rfl : ia = ib := (UScalar.eq_equiv _ _).2 (congrArg Fin.val hi)
  obtain rfl : ba = bb := toLayerSignature_inj (congrFun hl bottomLayer)
  obtain rfl : ta = tb := toLayerSignature_inj (congrFun hl topLayer)
  rfl

end LeanXmssProofs
