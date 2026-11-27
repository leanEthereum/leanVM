module

public import NativeRustcArm.SphincsVerify.Basic

/-!
# `sphincs_verify` from its regions

The regions' statements (`ParseSpec`, ..., `TreeSpec`) compose: from the entry the machine
inevitably returns `sphincsVerifyBytes` of the raw input bytes (`run_correct`). The layers' loop is
an induction on the layers left (`layers_correct`): a layer without a codeword returns `0`, as
`layersFrom` gives `none` (`resultFrom_none`); otherwise the next layer's message is the layer's
root (`resultFrom_some`).
-/

namespace NativeRustcArm.SphincsVerifyProof

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
theorem sphincsVerifyBytes_eq :
    sphincsVerifyBytes r.pkBytes r.msgBytes r.sigBytes = r.resultFrom 0 r.forsPk := by
  have hL : layersFrom (PublicKey.fromBytes r.pkBytes).pkSeed
      (messageDigest (PublicKey.fromBytes r.pkBytes) (Signature.fromBytes r.sigBytes).randomizer
        r.msgBytes).1 (Signature.fromBytes r.sigBytes) [0, 1, 2]
      (forsRecover (PublicKey.fromBytes r.pkBytes).pkSeed
        (messageDigest (PublicKey.fromBytes r.pkBytes)
          (Signature.fromBytes r.sigBytes).randomizer r.msgBytes).1
        (messageDigest (PublicKey.fromBytes r.pkBytes)
          (Signature.fromBytes r.sigBytes).randomizer r.msgBytes).2
        (Signature.fromBytes r.sigBytes).fors) =
      layersFrom r.seed r.idx r.sig (List.range' 0 (3 - 0)) r.forsPk := rfl
  unfold sphincsVerifyBytes verify resultFrom
  rw [hL]
  cases layersFrom r.seed r.idx r.sig (List.range' 0 (3 - 0)) r.forsPk <;> rfl

end Run

variable [ElfHost]

/-- A region's conclusion at a state with its pc. -/
theorem at_pc {r : Run} {j : Nat} {P : MachineData → Prop} {Q : MachineState → Prop}
    (h : ∀ m, P m → Eventually (elfStep1 ElfHost.exe) Q ⟨m, r.pc j⟩) :
    ∀ st : MachineState, st.pc = r.pc j ∧ P st.data → Eventually (elfStep1 ElfHost.exe) Q st := by
  rintro ⟨m, pc⟩ ⟨hpc, hm⟩
  cases hpc
  exact h m hm

/-- The parse from its head and its tail. -/
theorem parseSpec_of (hh : ParseHeadSpec) (ht : ParseTailSpec) : ParseSpec := by
  intro r hp hc hpre m hm
  exact Eventually.bind_elf (hh r hp hc hpre m hm) (at_pc fun m' hm' ↦ ht r hp hc hpre m' hm')

/-- **The layers' loop**: from layer `l`'s state with message `s`, the machine inevitably returns
what verification gives from layer `l` on. -/
theorem layers_correct (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees)
    (hpre : r.Pre) (he : EncodeSpec) (hch : ChainsSpec) (ht : TreeSpec) :
    ∀ n l s m, l + n = 3 → r.AtLayer l s m →
      Eventually (elfStep1 ElfHost.exe) (r.Done (r.resultFrom l s))
        ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b92Offset⟩ := by
  intro n
  induction n with
  | zero =>
    intro l s m hn h
    exact absurd h.1 (by omega)
  | succ n ih =>
    intro l s m hn h
    have hl : l < 3 := h.1
    refine Eventually.bind_elf (he l s r hp hc hpre m h) fun st hst ↦ ?_
    rcases hst with ⟨hnone, hdone⟩ | ⟨x, hx, hpc, hch'⟩
    · rw [r.resultFrom_none hl hnone]
      exact .done _ hdone
    rw [r.resultFrom_some hl hx]
    have hev := Eventually.bind_elf (at_pc (hch l x r hp hc hpre) st ⟨hpc, hch'⟩) fun st' hst' ↦
      at_pc (ht l (r.chainEnds l x) r hp hc hpre) st' hst'
    by_cases h2 : l = 2
    · subst h2
      refine Eventually.mono_elf hev fun st'' h ↦ ?_
      simp only [↓reduceIte] at h
      rwa [r.resultFrom_three]
    · refine Eventually.bind_elf hev fun st'' h ↦ ?_
      simp only [h2, ↓reduceIte] at h
      exact at_pc (fun m hm ↦ ih (l + 1) _ m (by omega) hm) st'' h

/-- **`sphincs_verify` from its regions**: from the entry the machine inevitably returns
`sphincsVerifyBytes` of the raw input bytes. -/
theorem run_correct (r : Run) (hp : PlacedIn Sphincs.SphincsVerify.code r.sec r.k) (hc : Callees)
    (hpre : r.Pre) (h1 : ParseSpec) (h2 : DigestSpec) (h3 : ForsSpec) (h4 : ForsKeySpec)
    (he : EncodeSpec) (hch : ChainsSpec) (ht : TreeSpec) :
    Eventually (elfStep1 ElfHost.exe) (r.Done (sphincsVerifyBytes r.pkBytes r.msgBytes r.sigBytes))
      ⟨r.m0, ElfHost.addrOf r.sec r.k⟩ := by
  have e1 := h1 r hp hc hpre r.m0 rfl
  rw [Sphincs.SphincsVerify.b0Offset, Nat.add_zero] at e1
  refine Eventually.bind_elf e1 (at_pc fun m hm ↦ ?_)
  refine Eventually.bind_elf (h2 r hp hc hpre m hm) (at_pc fun m hm ↦ ?_)
  refine Eventually.bind_elf (h3 r hp hc hpre m hm) (at_pc fun m hm ↦ ?_)
  refine Eventually.bind_elf (h4 r hp hc hpre m hm) (at_pc fun m hm ↦ ?_)
  rw [r.sphincsVerifyBytes_eq]
  exact layers_correct r hp hc hpre he hch ht 3 0 _ m rfl hm

end

end NativeRustcArm.SphincsVerifyProof
