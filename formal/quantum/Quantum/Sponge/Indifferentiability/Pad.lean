module

public import Quantum.Sponge.Indifferentiability.Fix
public import Quantum.Xmss.Keccak
public import Quantum.Qrom.Model

@[expose] public section

/-!
# The sponge's random oracle from the hash's (padding and truncation)

The indifferentiability route ends in a random oracle `f' : Msg X 9 → X` on padded block lists
(`X` the Keccak rate); the QROM proofs use a random function `H : HashDomain → HashOutput` on byte
strings of at most `maxLen = 1088` bytes. Keccak-256 of a string `s` is `out256` of the sponge on
`blocks s` (`Quantum.Xmss.keccakHash_eq_spongeHash`), which has at most `1088 / 136 + 1 = 9` blocks.

* Generic (`simOracle`): an oracle `f'` on messages `M` from `H : D → Y` and a private `Q : M → X`,
  with `X ≃+ Yb × R` and `Y ≃ Yb`: on a message with a preimage `x` under `pre`, the `Yb` part is
  `H x` and the `R` part is `Q`'s; elsewhere `Q` plus `H x0`. The pair `(f', junk)` is a bijective
  image of `(H, Q)` (`simEquiv`), so under uniform `H`, `Q` the oracle `f'` is uniform and its
  `Yb` parts at preimages are `H` (`sum_simOracle_joint`, `sum_simOracle`, `simOracle_fst`).
* Keccak (`keccakSim`): `M = Msg KeccakRate 9`, `pre` the code of the string a list pads
  (`padPre`), `padMsg x` the padded blocks of the string of a code. For every string `s` with code
  `x`, `out256 (keccakSim H Q ⟨blocks s, _⟩) = H x` (`out256_keccakSim`): the ideal sponge hashes
  as `H`.
-/

namespace Quantum.Sponge

section law

variable {D M X Y Yb R : Type} [AddCommGroup X] [AddCommGroup Yb] [AddCommGroup R]
  (sp : X ≃+ Yb × R) (conv : Y ≃ Yb) (pre : M → Option D) (x0 : D)

/-- The input of `H` a message's simulation reads: its preimage, else `x0`. -/
def preD (m : M) : D :=
  (pre m).getD x0

/-- The private part of the simulated oracle: on messages with a preimage only `Q`'s `R` part,
elsewhere all of `Q`. -/
def privPart (Q : M → X) (m : M) : X :=
  if (pre m).isSome then sp.symm (0, (sp (Q m)).2) else Q m

/-- **The simulated oracle**: the private part plus `H` of the read input in the `Yb` part. -/
def simOracle (H : D → Y) (Q : M → X) (m : M) : X :=
  privPart sp pre Q m + sp.symm (conv (H (preD pre x0 m)), 0)

variable {sp conv pre x0}

theorem sp_simOracle_of_some {H : D → Y} {Q : M → X} {m : M} {x : D} (h : pre m = some x) :
    sp (simOracle sp conv pre x0 H Q m) = (conv (H x), (sp (Q m)).2) := by
  simp [simOracle, privPart, preD, h]

theorem simOracle_of_none {H : D → Y} {Q : M → X} {m : M} (h : pre m = none) :
    simOracle sp conv pre x0 H Q m = Q m + sp.symm (conv (H x0), 0) := by
  simp [simOracle, privPart, preD, h]

/-- At a message with preimage `x`, the simulated oracle's `Yb` part is `H x`. -/
theorem simOracle_fst {H : D → Y} {Q : M → X} {m : M} {x : D} (h : pre m = some x) :
    conv.symm (sp (simOracle sp conv pre x0 H Q m)).1 = H x := by
  rw [sp_simOracle_of_some h, Equiv.symm_apply_apply]

variable (sp conv pre x0) [DecidableEq D] (pad : D → M)

/-- The randomness the simulated oracle forgets: `Q`'s `Yb` parts at preimages, `H` elsewhere. -/
def simJunk (H : D → Y) (Q : M → X) (x : D) : Y :=
  if pre (pad x) = some x then conv.symm (sp (Q (pad x))).1 else H x

/-- `H` from the oracle and the junk. -/
def unH (f : M → X) (J : D → Y) (x : D) : Y :=
  if pre (pad x) = some x then conv.symm (sp (f (pad x))).1 else J x

/-- `Q` from the oracle and the junk. -/
def unQ (f : M → X) (J : D → Y) (m : M) : X :=
  match pre m with
  | some x => sp.symm (conv (J x), (sp (f m)).2)
  | none => f m - sp.symm (conv (unH sp conv pre pad f J x0), 0)

variable {pad}

theorem unH_simOracle (H : D → Y) (Q : M → X) :
    unH sp conv pre pad (simOracle sp conv pre x0 H Q) (simJunk sp conv pre pad H Q) = H := by
  funext x
  by_cases hc : pre (pad x) = some x
  · rw [unH, ite_eq_left hc, simOracle_fst hc]
  · rw [unH, ite_eq_right hc, simJunk, ite_eq_right hc]

theorem unQ_simOracle (hpre : ∀ m x, pre m = some x → pad x = m) (H : D → Y) (Q : M → X) :
    unQ sp conv pre x0 pad (simOracle sp conv pre x0 H Q) (simJunk sp conv pre pad H Q) = Q := by
  funext m
  rw [unQ]
  split
  · next x hm =>
    have hx := hpre m x hm
    rw [simJunk, ite_eq_left (hx ▸ hm), hx, Equiv.apply_symm_apply, sp_simOracle_of_some hm]
    exact sp.symm_apply_apply (Q m)
  · next hm =>
    rw [unH_simOracle sp conv pre x0, simOracle_of_none hm, add_sub_cancel_right]

theorem simOracle_unQ (hpre : ∀ m x, pre m = some x → pad x = m) (f : M → X) (J : D → Y) :
    simOracle sp conv pre x0 (unH sp conv pre pad f J) (unQ sp conv pre x0 pad f J) = f := by
  funext m
  cases hm : pre m with
  | none =>
    rw [simOracle_of_none hm, unQ, hm]
    exact sub_add_cancel _ _
  | some x =>
    have hx := hpre m x hm
    refine sp.injective ?_
    rw [sp_simOracle_of_some hm, unH, ite_eq_left (hx ▸ hm), hx, Equiv.apply_symm_apply, unQ, hm]
    simp

theorem simJunk_unQ (f : M → X) (J : D → Y) :
    simJunk sp conv pre pad (unH sp conv pre pad f J) (unQ sp conv pre x0 pad f J) = J := by
  funext x
  by_cases hc : pre (pad x) = some x
  · rw [simJunk, ite_eq_left hc, unQ, hc]
    simp
  · rw [simJunk, ite_eq_right hc, unH, ite_eq_right hc]

/-- The simulation as a bijection `(H, Q) ↦ (f', junk)`. -/
def simEquiv (hpre : ∀ m x, pre m = some x → pad x = m) : (D → Y) × (M → X) ≃ (M → X) × (D → Y)
    where
  toFun p := (simOracle sp conv pre x0 p.1 p.2, simJunk sp conv pre pad p.1 p.2)
  invFun q := (unH sp conv pre pad q.1 q.2, unQ sp conv pre x0 pad q.1 q.2)
  left_inv p := Prod.ext (unH_simOracle sp conv pre x0 p.1 p.2)
    (unQ_simOracle sp conv pre x0 hpre p.1 p.2)
  right_inv q := Prod.ext (simOracle_unQ sp conv pre x0 hpre q.1 q.2)
    (simJunk_unQ sp conv pre x0 q.1 q.2)

variable [Fintype D] [Fintype M] [DecidableEq M] [Fintype X] [Fintype Y]

/-- **The simulation is perfect, jointly with `H`**: under uniform `H`, `Q`, the pair
`(H, simOracle H Q)` has the law of `(unH f J, f)` under uniform `f`, `J`; `unH f J` is `Yb` of `f`
at every padding of a preimage. -/
theorem sum_simOracle_joint (hpre : ∀ m x, pre m = some x → pad x = m) {β : Type*}
    [AddCommMonoid β] (F : (D → Y) → (M → X) → β) :
    ∑ H, ∑ Q, F H (simOracle sp conv pre x0 H Q) = ∑ f, ∑ J, F (unH sp conv pre pad f J) f := by
  rw [← Fintype.sum_prod_type' (fun H Q ↦ F H (simOracle sp conv pre x0 H Q)),
    ← Fintype.sum_prod_type' (fun f J ↦ F (unH sp conv pre pad f J) f)]
  refine Fintype.sum_equiv (simEquiv sp conv pre x0 hpre) _ _ fun p ↦ ?_
  change _ = F (unH sp conv pre pad (simOracle sp conv pre x0 p.1 p.2)
    (simJunk sp conv pre pad p.1 p.2)) (simOracle sp conv pre x0 p.1 p.2)
  rw [unH_simOracle sp conv pre x0]

/-- **The simulated oracle is uniform**. -/
theorem sum_simOracle (hpre : ∀ m x, pre m = some x → pad x = m) {β : Type*} [AddCommMonoid β]
    (F : (M → X) → β) :
    ∑ H, ∑ Q, F (simOracle sp conv pre x0 H Q) = Fintype.card (D → Y) • ∑ f, F f := by
  rw [sum_simOracle_joint sp conv pre x0 hpre fun _ f ↦ F f, Finset.smul_sum]
  simp

end law

/-! ## Keccak's padding -/

section keccak

open HashSig Quantum.Qrom

/-- The rate split into its 256 output bits and the other 832, additively. -/
def rateSplit : KeccakRate ≃+ (Fin 256 → ZMod 2) × (Fin 832 → ZMod 2) where
  toFun x := (fun j ↦ x (Fin.castAdd 832 j), fun j ↦ x (Fin.natAdd 256 j))
  invFun p := (Fin.append p.1 p.2 : Fin (256 + 832) → ZMod 2)
  left_inv x := Fin.append_castAdd_natAdd
  right_inv p := by simp
  map_add' _ _ := rfl

theorem out256_eq_rateSplit (x : KeccakRate) :
    Xmss.out256 x = (Xmss.bitsEquiv 256).symm (rateSplit x).1 :=
  rfl

theorem length_decodeInput (x : HashDomain) : (decodeInput x).length = x.1 := by
  simp [decodeInput]

/-- The padded blocks of the string of a code. -/
def padMsg (x : HashDomain) : Msg KeccakRate 9 :=
  ⟨Xmss.blocks (decodeInput x), by
    rw [← List.length_pos_iff, Xmss.length_blocks]
    omega, by
    have : (x.1 : ℕ) < 1089 := x.1.isLt
    rw [Xmss.length_blocks, length_decodeInput]
    omega⟩

open Classical in
/-- The code of the string whose padded blocks a list is, if any. -/
noncomputable def padPre (m : Msg KeccakRate 9) : Option HashDomain :=
  if h : ∃ s : HashInput, s.length ≤ maxLen ∧ Xmss.blocks s = m.1 then encodeInput h.choose
  else none

theorem padMsg_of_padPre {m : Msg KeccakRate 9} {x : HashDomain} (h : padPre m = some x) :
    padMsg x = m := by
  rw [padPre] at h
  split_ifs at h with hs
  refine Subtype.ext ?_
  change Xmss.blocks (decodeInput x) = m.1
  rw [decodeInput_of_encodeInput_eq_some h, hs.choose_spec.2]

theorem padMsg_val {s : HashInput} {x : HashDomain} (h : encodeInput s = some x) :
    (padMsg x).1 = Xmss.blocks s := by
  change Xmss.blocks (decodeInput x) = _
  rw [decodeInput_of_encodeInput_eq_some h]

/-- The code of a string is the preimage of its padded blocks. -/
theorem padPre_padMsg {s : HashInput} {x : HashDomain} (h : encodeInput s = some x) :
    padPre (padMsg x) = some x := by
  have hl : s.length ≤ maxLen := isSome_encodeInput_iff.1 (by rw [h]; rfl)
  have hs : ∃ s' : HashInput, s'.length ≤ maxLen ∧ Xmss.blocks s' = (padMsg x).1 :=
    ⟨s, hl, (padMsg_val h).symm⟩
  rw [padPre, dite_eq_left hs, Xmss.blocks_injective (hs.choose_spec.2.trans (padMsg_val h)), h]

/-- **The sponge's oracle from `H`** and a private oracle `Q`. -/
noncomputable def keccakSim (H : HashDomain → HashOutput) (Q : Msg KeccakRate 9 → KeccakRate) :
    Msg KeccakRate 9 → KeccakRate :=
  simOracle rateSplit (Xmss.bitsEquiv 256) padPre 0 H Q

/-- **The ideal sponge hashes as `H`**: on the padded blocks of a string with code `x`, the
first 256 bits of the simulated oracle are `H x`. -/
theorem out256_keccakSim {s : HashInput} {x : HashDomain} (h : encodeInput s = some x)
    (H : HashDomain → HashOutput) (Q : Msg KeccakRate 9 → KeccakRate) :
    Xmss.out256 (keccakSim H Q ⟨Xmss.blocks s, (padMsg_val h) ▸ (padMsg x).2⟩) = H x := by
  rw [out256_eq_rateSplit, keccakSim]
  refine simOracle_fst ?_
  rw [← padPre_padMsg h]
  exact congrArg padPre (Subtype.ext (padMsg_val h).symm)

/-- **The simulated sponge oracle is perfect, jointly with `H`**. -/
theorem sum_keccakSim_joint {β : Type*} [AddCommMonoid β]
    (F : (HashDomain → HashOutput) → (Msg KeccakRate 9 → KeccakRate) → β) :
    ∑ H, ∑ Q, F H (keccakSim H Q) =
      ∑ f, ∑ J, F (unH rateSplit (Xmss.bitsEquiv 256) padPre padMsg f J) f :=
  sum_simOracle_joint rateSplit (Xmss.bitsEquiv 256) padPre 0 (fun _ _ ↦ padMsg_of_padPre) F

/-- **The simulated sponge oracle is uniform**. -/
theorem sum_keccakSim {β : Type*} [AddCommMonoid β] (F : (Msg KeccakRate 9 → KeccakRate) → β) :
    ∑ H, ∑ Q, F (keccakSim H Q) = Fintype.card (HashDomain → HashOutput) • ∑ f, F f :=
  sum_simOracle rateSplit (Xmss.bitsEquiv 256) padPre 0 (fun _ _ ↦ padMsg_of_padPre) F

end keccak

end Quantum.Sponge

end
