import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.IdealStatement

/-!
# The byte encoding is injective

Domain separation is what keeps a query from bearing on two structural positions at once, and it
rests on the tweak bytes determining the position. That in turn rests on the fixed-width
little-endian encoding being injective, which is what this module proves.
-/

namespace SphincsSecurity

theorem bytesLE_injective {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

theorem bytesLE_length (n : Nat) (x : BitVec (8 * n)) : (bytesLE n x).length = n := by
  simp [bytesLE]

/-- A bit vector determines the natural it encodes, below the wrap. -/
theorem ofNat_inj_of_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

theorem fieldBytes_injective {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) : t1 = t2 := by
  obtain ⟨tag1, layer1, reserved1, tree1, position1, index1⟩ := t1
  obtain ⟨tag2, layer2, reserved2, tree2, position2, index2⟩ := t2
  simp only [fieldBytes] at h
  obtain ⟨h, hindex⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, htree⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hposition⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hreserved⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨htag, hlayer⟩ := List.append_inj' h (by simp [bytesLE_length])
  have htag := List.append_right_injective [protocolDomainSep] htag
  simp only [bytesLE_injective htag, bytesLE_injective hlayer, bytesLE_injective hreserved, bytesLE_injective htree,
    bytesLE_injective hposition, bytesLE_injective hindex]

theorem tweakBytes_eq_iff {d1 d2 : HashDomain} :
    tweakBytes d1 = tweakBytes d2 ↔ hashDomainFields d1 = hashDomainFields d2 :=
  ⟨fun h => fieldBytes_injective h, fun h => by rw [tweakBytes, tweakBytes, h]⟩

private theorem layer_le : numLayers ≤ 2 ^ 8 := by decide
private theorem tree_le : 2 ^ 32 ≤ 2 ^ 32 := le_rfl
private theorem leaf_le : 2 ^ maxLayerHeight ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by decide)
private theorem ftsTree_le : ftsTrees - 1 ≤ 2 ^ 8 := by decide
private theorem ftsLeaf_le : 2 ^ ftsTreeHeight ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by decide)

/-- Every field a tweak carries is below the width that encodes it. The `Fin`-valued ones are by
construction; the two tree recursions take their level and node as naturals, so those are the only
positions that need saying, and honest use keeps them far below `2^32`. -/
def HashDomain.InRange : HashDomain → Prop
  | .node _ _ level nodeIdx => level < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
  | .ftsNode _ _ level nodeIdx => level < 2 ^ 32 ∧ nodeIdx < 2 ^ 32
  | _ => True

theorem fin_of_ofNat_eq {w n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ w)
    (h : BitVec.ofNat w a.val = BitVec.ofNat w b.val) : a = b :=
  Fin.ext (ofNat_inj_of_lt (Nat.lt_of_lt_of_le a.isLt hn) (Nat.lt_of_lt_of_le b.isLt hn) h)

theorem fts_index_eq {a b : Index}
    (hhigh : BitVec.ofNat 8 (a.val / 2 ^ 32) = BitVec.ofNat 8 (b.val / 2 ^ 32))
    (hlow : BitVec.ofNat 32 a.val = BitVec.ofNat 32 b.val) : a = b := by
  have ha : a.val / 2 ^ 32 < 2 ^ 8 := by
    have := a.isLt
    norm_num [totalHeight] at *
    omega
  have hb : b.val / 2 ^ 32 < 2 ^ 8 := by
    have := b.isLt
    norm_num [totalHeight] at *
    omega
  have hdiv := ofNat_inj_of_lt ha hb hhigh
  have hmod := congrArg BitVec.toNat hlow
  simp only [BitVec.toNat_ofNat] at hmod
  exact Fin.ext (by omega)

/-- **Domain separation.** A tweak names one structural position: two in-range domains with the same
tweak bytes are the same domain. This is what stops one query from bearing on two positions, and so
what keeps an inversion at `2^-n` per query with no multi-target factor. -/
theorem tweakBytes_injective {d1 d2 : HashDomain} (h1 : d1.InRange) (h2 : d2.InRange)
    (h : tweakBytes d1 = tweakBytes d2) : d1 = d2 := by
  rw [tweakBytes_eq_iff] at h
  cases d1 <;> cases d2 <;>
    simp_all [hashDomainFields, tweakFields, ftsTweakFields, HashDomain.InRange, TweakFields.mk.injEq]
  case chain.chain lay1 tree1 leaf1 i1 s1 lay2 tree2 leaf2 i2 s2 =>
    obtain ⟨hl, ht, hp, hlf⟩ := h
    have hpos := ofNat_inj_of_lt (OtsCode.chainTweakPosition_lt i1 s1) (OtsCode.chainTweakPosition_lt i2 s2) hp
    obtain ⟨hi, hs⟩ := OtsCode.chainTweakPosition_injective hpos
    exact ⟨fin_of_ofNat_eq layer_le hl, fin_of_ofNat_eq leaf_le hlf, hi, hs⟩
  case leaf.leaf => exact ⟨fin_of_ofNat_eq layer_le h.1,
      fin_of_ofNat_eq leaf_le h.2.2⟩
  case node.node lay1 tree1 level1 nodeIdx1 lay2 tree2 level2 nodeIdx2 =>
    exact ⟨fin_of_ofNat_eq layer_le h.1,
      ofNat_inj_of_lt h1.1 h2.1 h.2.2.1, ofNat_inj_of_lt h1.2 h2.2 h.2.2.2⟩
  case encoding.encoding => exact ⟨fin_of_ofNat_eq layer_le h.1,
      fin_of_ofNat_eq leaf_le h.2.2⟩
  case ftsLeaf.ftsLeaf => exact ⟨fts_index_eq h.2.1 h.2.2.1, fin_of_ofNat_eq ftsTree_le h.1,
      fin_of_ofNat_eq ftsLeaf_le h.2.2.2⟩
  case ftsNode.ftsNode =>
    exact ⟨fts_index_eq h.2.1 h.2.2.1, fin_of_ofNat_eq ftsTree_le h.1,
      ofNat_inj_of_lt h1.1 h2.1 h.2.2.2.1, ofNat_inj_of_lt h1.2 h2.2 h.2.2.2.2⟩
  case ftsRoots.ftsRoots => exact fts_index_eq h.1 h.2

theorem tweakBytes_length (domain : HashDomain) : (tweakBytes domain).length = 16 := by
  simp [tweakBytes, fieldBytes, bytesLE_length]

/-- What the reduction reads off a query: the tweak is a fixed-length prefix of the hashed input, so
the input determines both the position it names and the payload. -/
theorem tweakableHashInput_injective (parameter : PublicParameter) {d1 d2 : HashDomain}
    (h1 : d1.InRange) (h2 : d2.InRange) {payload1 payload2 : HashInput}
    (h : tweakableHashInput parameter d1 payload1 = tweakableHashInput parameter d2 payload2) :
    d1 = d2 ∧ payload1 = payload2 := by
  simp only [tweakableHashInput] at h
  obtain ⟨hprefix, hpayload⟩ := List.append_inj h (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact ⟨tweakBytes_injective h1 h2 htweak, hpayload⟩

theorem tweakableHashInput_ne_message (parameter : PublicParameter) (domain : HashDomain)
    (hdomain : domain ≠ .message) (payload messagePayload : HashInput) :
    tweakableHashInput parameter domain payload ≠
      tweakableHashInput parameter .message messagePayload := by
  intro hinput
  simp only [tweakableHashInput] at hinput
  obtain ⟨hprefix, _⟩ := List.append_inj hinput
    (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  apply hdomain
  cases domain <;>
    simp_all [tweakBytes_eq_iff, hashDomainFields, tweakFields, ftsTweakFields, TweakFields.mk.injEq]

/-! ### Payloads

A node's payload is its two children, a leaf's is its `v` chain endpoints, and a few-time key's is
its `k-1` roots. Each is injective, which is what lets the extraction argument descend: if an
adversary's payload hashes to an honest value, either it *is* the honest payload, and then its parts
are the honest parts, or the hash was hit. -/

theorem digestBytes_injective {x y : Digest} (h : Concrete.digestBytes x = Concrete.digestBytes y) :
    x = y :=
  bytesLE_injective h

theorem digestBytes_length (x : Digest) : (Concrete.digestBytes x).length = 16 :=
  bytesLE_length 16 x

theorem nodePayload_injective {left right left' right' : Digest}
    (h : Concrete.nodePayload left right = Concrete.nodePayload left' right') :
    left = left' ∧ right = right' := by
  obtain ⟨hleft, hright⟩ := List.append_inj h (by simp [bytesLE_length])
  exact ⟨digestBytes_injective hleft, digestBytes_injective hright⟩

/-- A concatenation of fixed-length blocks determines the blocks. -/
theorem flatMap_ofFn_injective {α β : Type} (g : α → List β) (len : Nat)
    (hlen : ∀ a, (g a).length = len) (hinj : ∀ a b, g a = g b → a = b) :
    ∀ {n : Nat} {f f' : Fin n → α},
      (List.ofFn f).flatMap g = (List.ofFn f').flatMap g → f = f' := by
  intro n
  induction n with
  | zero => intro f f' _; funext i; exact i.elim0
  | succ n ih =>
      intro f f' h
      simp only [List.ofFn_succ, List.flatMap_cons] at h
      obtain ⟨hhead, htail⟩ := List.append_inj h (by rw [hlen, hlen])
      have hzero := hinj _ _ hhead
      have hsucc := ih htail
      funext i
      cases i using Fin.cases with
      | zero => exact hzero
      | succ j => exact congrFun hsucc j

/-- A one-time signature's payload is its `v` endpoints, and the concatenation determines them. -/
theorem leafPayload_injective {endpoints endpoints' : ChainIndex → Digest}
    (h : Concrete.leafPayload endpoints = Concrete.leafPayload endpoints') :
    endpoints = endpoints' :=
  flatMap_ofFn_injective Concrete.digestBytes 16 digestBytes_length
    (fun _ _ => digestBytes_injective) h

/-- A few-time public key's payload is its `k - 1` roots. -/
theorem ftsRootsPayload_injective {roots roots' : FtsTree → Digest}
    (h : Concrete.ftsRootsPayload roots = Concrete.ftsRootsPayload roots') : roots = roots' :=
  flatMap_ofFn_injective Concrete.digestBytes 16 digestBytes_length
    (fun _ _ => digestBytes_injective) h

end SphincsSecurity
