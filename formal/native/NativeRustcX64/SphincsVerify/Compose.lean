module

public import NativeRustcX64.SphincsVerify.Basic

/-!
# `sphincs_verify` from its regions

The regions' statements (`ParseSpec`, ..., `TreeSpec`) compose: from the entry the machine
inevitably returns `sphincsVerify` of the input words (`run_correct`). The layers' loop is an
induction on the layers left (`layers_correct`): a layer without a codeword returns `0`, as
`layersFrom` gives `none` (`resultFrom_none`); otherwise the next layer's message is the layer's
root (`resultFrom_some`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs

public section

namespace Run

variable (r : Run)

theorem range'_cons {l : Nat} (hl : l < 3) :
    List.range' l (3 - l) = l :: List.range' (l + 1) (3 - (l + 1)) := by
  rw [show 3 - l = (3 - (l + 1)) + 1 by omega]
  rfl

/-- A layer without a codeword: verification is `false`. -/
theorem resultFrom_none {l : Nat} {s : List UInt8} (hl : l < 3)
    (h : encode r.seed (r.key l) s (r.layerSig l).counter = none) : r.resultFrom l s = false := by
  have h' : encode r.seed (OtsKey.ofIndex l r.idx) s (r.sig.layers.getD l ⟨0, []⟩).counter =
    none := h
  unfold resultFrom
  rw [range'_cons hl]
  simp only [layersFrom, wotsLeaf, h']

/-- A layer with the codeword `x`: verification goes on from the next layer, its message the
layer's root. -/
theorem resultFrom_some {l : Nat} {s x : List UInt8} (hl : l < 3)
    (h : encode r.seed (r.key l) s (r.layerSig l).counter = some x) :
    r.resultFrom l s = r.resultFrom (l + 1) (r.layerRoot l (r.chainEnds l x)) := by
  have h' : encode r.seed (OtsKey.ofIndex l r.idx) s (r.sig.layers.getD l ⟨0, []⟩).counter =
    some x := h
  unfold resultFrom
  rw [range'_cons hl]
  simp only [layersFrom, wotsLeaf, h']
  rfl

/-- After the last layer: the comparison with `PK.root`. -/
theorem resultFrom_three (s : List UInt8) : r.resultFrom 3 s = (s == r.pk.root) := rfl

/-- Verification is the layers' from the FORS key. -/
theorem sphincsVerify_eq : sphincsVerify r.w = r.resultFrom 0 r.forsPk := by
  have hL : layersFrom (PublicKey.fromBytes (pkBytes r.w)).pkSeed
      (messageDigest (PublicKey.fromBytes (pkBytes r.w)) (Signature.fromBytes (sigBytes r.w)).randomizer
        (messageBytes r.w)).1 (Signature.fromBytes (sigBytes r.w)) [0, 1, 2]
      (forsRecover (PublicKey.fromBytes (pkBytes r.w)).pkSeed
        (messageDigest (PublicKey.fromBytes (pkBytes r.w))
          (Signature.fromBytes (sigBytes r.w)).randomizer (messageBytes r.w)).1
        (messageDigest (PublicKey.fromBytes (pkBytes r.w))
          (Signature.fromBytes (sigBytes r.w)).randomizer (messageBytes r.w)).2
        (Signature.fromBytes (sigBytes r.w)).fors) =
      layersFrom r.seed r.idx r.sig (List.range' 0 (3 - 0)) r.forsPk := rfl
  unfold sphincsVerify verify resultFrom
  rw [hL]
  cases layersFrom r.seed r.idx r.sig (List.range' 0 (3 - 0)) r.forsPk <;> rfl

end Run

variable [Host]

/-- A region's conclusion at a state with its pc. -/
theorem at_pc {r : Run} {j : Nat} {P : MachineData → Prop} {Q : MachineState → Prop}
    (h : ∀ m, P m → Eventually (step1 Host.exe) Q ⟨m, r.pc j⟩) :
    ∀ st : MachineState, st.pc = r.pc j ∧ P st.data → Eventually (step1 Host.exe) Q st := by
  rintro ⟨m, pc⟩ ⟨hpc, hm⟩
  cases hpc
  exact h m hm

/-- **The layers' loop**: from layer `l`'s state with message `s`, the machine inevitably returns
what verification gives from layer `l` on. -/
theorem layers_correct (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) (he : EncodeSpec) (hch : ChainsSpec) (ht : TreeSpec) :
    ∀ n l s m, l + n = 3 → r.AtLayer l s m →
      Eventually (step1 Host.exe) (r.Done (r.resultFrom l s)) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b104Offset⟩ := by
  intro n
  induction n with
  | zero =>
    intro l s m hn h
    exact absurd h.1 (by omega)
  | succ n ih =>
    intro l s m hn h
    have hl : l < 3 := h.1
    refine Eventually.bind (he l s r hp hc hpre m h) fun st hst ↦ ?_
    rcases hst with ⟨hnone, hdone⟩ | ⟨x, hx, hpc, hch'⟩
    · rw [r.resultFrom_none hl hnone]
      exact .done _ hdone
    rw [r.resultFrom_some hl hx]
    have hev := Eventually.bind (at_pc (hch l x r hp hc hpre) st ⟨hpc, hch'⟩) fun st' hst' ↦
      at_pc (ht l (r.chainEnds l x) r hp hc hpre) st' hst'
    by_cases h2 : l = 2
    · subst h2
      refine Eventually.mono hev fun st'' h ↦ ?_
      simp only [↓reduceIte] at h
      rwa [r.resultFrom_three]
    · refine Eventually.bind hev fun st'' h ↦ ?_
      simp only [h2, ↓reduceIte] at h
      exact at_pc (fun m hm ↦ ih (l + 1) _ m (by omega) hm) st'' h

/-- **`sphincs_verify` from its regions**: from the entry the machine inevitably returns
`sphincsVerify` of the input words. -/
theorem run_correct (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees)
    (hpre : r.Pre) (h1 : ParseSpec) (h2 : DigestSpec) (h3 : ForsSpec) (h4 : ForsKeySpec)
    (he : EncodeSpec) (hch : ChainsSpec) (ht : TreeSpec) :
    Eventually (step1 Host.exe) (r.Done (sphincsVerify r.w))
      ⟨r.m0, Host.addrOf r.k⟩ := by
  have e1 := h1 r hp hc hpre r.m0 rfl
  rw [Sphincs.SphincsVerify.b0Offset, Nat.add_zero] at e1
  refine Eventually.bind e1 (at_pc fun m hm ↦ ?_)
  refine Eventually.bind (h2 r hp hc hpre m hm) (at_pc fun m hm ↦ ?_)
  refine Eventually.bind (h3 r hp hc hpre m hm) (at_pc fun m hm ↦ ?_)
  refine Eventually.bind (h4 r hp hc hpre m hm) (at_pc fun m hm ↦ ?_)
  rw [r.sphincsVerify_eq]
  exact layers_correct r hp hc hpre he hch ht 3 0 _ m rfl hm

end

end NativeRustcX64.SphincsVerifyProof
