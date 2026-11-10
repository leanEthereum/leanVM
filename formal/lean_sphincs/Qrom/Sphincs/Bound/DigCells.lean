module

public import Qrom.Sphincs.Bound.LamCov

@[expose] public section

/-!
# The digest calls as one cell

A digest input is an 80-byte prefix (the randomizer, `PK.seed`, `PK.root` and the message) and the
4 bytes of its call. Grouping the inputs of that shape by prefix (`Qrom.Sphincs.cellOf`) makes the
digest calls of one message and randomizer the components of one cell, and every input of another
shape a cell alone. The games
answer the calls of a cell together: the hidden game overrides one call of a prefix exactly when it
overrides all of them (`Qrom.Sphincs.hidGame_ov_whole`), so its overrides are those of a game on
cells (`Qrom.Sphincs.cellOv_spec`).

A cell value is then a whole digest, and the fraction of the digests that presampled digests `δ`
cover is at most `∑_t c_t^k / (2^h 2^(k a))`, with `c_t` the number of them at the index `t`
(`Qrom.Sphincs.sbF_le`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-! ## Cells -/

/-- The cells: a digest prefix, or an input alone. -/
abbrev Cell := Input ⊕ Input

/-- The bytes of a digest call. -/
def callBytes (c : DigestCall) : HashInput := bytesBE 4 (BitVec.ofNat 32 c.val)

theorem callBytes_length (c : DigestCall) : (callBytes c).length = 4 := bytesBE_length _ _

theorem callBytes_inj {c c' : DigestCall} (h : callBytes c = callBytes c') : c = c' :=
  Fin.ext (ofNat_inj_of_lt (digestCall_lt c) (digestCall_lt c') (bytesBE_injective h))

/-- The 80-byte prefix of a digest input. -/
def digPrefix (pa : PublicParameter) (root : Digest) (m : Message) (R : Randomness) : HashInput :=
  bytesLE 16 R ++ bytesLE 16 pa ++ bytesLE 16 root ++ bytesLE 32 m

theorem messageDigestInput_split (pa : PublicParameter) (root : Digest) (m : Message) (R : Randomness)
    (c : DigestCall) : messageDigestInput pa root m R c = digPrefix pa root m R ++ callBytes c := rfl

theorem digPrefix_length (pa : PublicParameter) (root : Digest) (m : Message) (R : Randomness) :
    (digPrefix pa root m R).length = 80 := by
  have h := messageDigestInput_length pa root m R firstCall
  rw [messageDigestInput_split, List.length_append, callBytes_length] at h
  omega

/-- `x` has the shape of the call `c` of a digest input. -/
def IsDig (x : Input) (c : DigestCall) : Prop := x.1.length = 84 ∧ x.1.drop 80 = callBytes c

theorem isDig_unique {x : Input} {c c' : DigestCall} (h : IsDig x c) (h' : IsDig x c') : c = c' :=
  callBytes_inj (h.2.symm.trans h'.2)

/-- The first 80 bytes of an input. -/
def pre (x : Input) : Input := ⟨x.1.take 80, (List.length_take_le _ _).trans (by unfold maxLen; omega)⟩

/-- The input of the call `c` of the prefix `p`. -/
def cellIn (p : Input) (c : DigestCall) : Input :=
  ⟨p.1.take 80 ++ callBytes c, by
    rw [List.length_append, callBytes_length]
    have := List.length_take_le 80 p.1
    unfold maxLen
    omega⟩

open Classical in
/-- The cell of an input and its component. -/
def cellOf (x : Input) : Cell × DigestCall :=
  if h : ∃ c, IsDig x c then (.inl (pre x), Classical.choose h) else (.inr x, firstCall)

theorem cellOf_of_isDig {x : Input} {c : DigestCall} (h : IsDig x c) : cellOf x = (.inl (pre x), c) := by
  have hex : ∃ c, IsDig x c := ⟨c, h⟩
  rw [cellOf, dite_eq_left hex, isDig_unique (Classical.choose_spec hex) h]

theorem cellOf_of_not {x : Input} (h : ¬ ∃ c, IsDig x c) : cellOf x = (.inr x, firstCall) := by
  rw [cellOf, dite_eq_right h]

theorem eq_cellIn_of_isDig {x : Input} {c : DigestCall} (h : IsDig x c) : x = cellIn (pre x) c := by
  apply Subtype.ext
  show x.1 = (x.1.take 80).take 80 ++ callBytes c
  rw [List.take_take, min_self, ← h.2, List.take_append_drop]

theorem cellOf_injective : Function.Injective cellOf := by
  intro x y hxy
  by_cases hx : ∃ c, IsDig x c <;> by_cases hy : ∃ c, IsDig y c
  · obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hy
    rw [cellOf_of_isDig hc, cellOf_of_isDig hc'] at hxy
    simp only [Prod.mk.injEq, Sum.inl.injEq] at hxy
    obtain ⟨hp, rfl⟩ := hxy
    rw [eq_cellIn_of_isDig hc, eq_cellIn_of_isDig hc', hp]
  · obtain ⟨c, hc⟩ := hx
    rw [cellOf_of_isDig hc, cellOf_of_not hy] at hxy
    simp at hxy
  · obtain ⟨c, hc⟩ := hy
    rw [cellOf_of_not hx, cellOf_of_isDig hc] at hxy
    simp at hxy
  · rw [cellOf_of_not hx, cellOf_of_not hy] at hxy
    simpa using hxy

theorem length_pre_of_isDig {x : Input} {c : DigestCall} (h : IsDig x c) : (pre x).1.length = 80 := by
  show (x.1.take 80).length = 80
  rw [List.length_take, h.1]
  rfl

theorem isDig_digestInputX (d : Data) (m : Message) (R : Randomness) (c : DigestCall) :
    IsDig (digestInputX d m R c) c := by
  refine ⟨messageDigestInput_length _ _ _ _ _, ?_⟩
  show (messageDigestInput _ _ m R c).drop 80 = callBytes c
  rw [messageDigestInput_split, List.drop_left' (digPrefix_length _ _ _ _)]

theorem pre_digestInputX (d : Data) (m : Message) (R : Randomness) (c : DigestCall) :
    (pre (digestInputX d m R c)).1 = digPrefix (param (hOf d)) (dataOf (hOf d)).root m R := by
  show (messageDigestInput _ _ m R c).take 80 = _
  rw [messageDigestInput_split, List.take_left' (digPrefix_length _ _ _ _)]

/-! ## Overrides of whole cells -/

open Classical in
/-- The overrides on cells: a digest prefix is overridden when all its calls are. -/
def cellOv (ov : Input → Option HashOutput) : Cell → Option DigV
  | .inl p => if p.1.length = 80 ∧ ∀ c, (ov (cellIn p c)).isSome then
      some fun c ↦ (ov (cellIn p c)).getD 0 else none
  | .inr x => (ov x).map fun y _ ↦ y

theorem cellOv_spec (ov : Input → Option HashOutput)
    (hwhole : ∀ p : Input, p.1.length = 80 → ∀ c c', (ov (cellIn p c)).isSome → (ov (cellIn p c')).isSome)
    (x : Input) : ov x = (cellOv ov (cellOf x).1).map fun v ↦ v (cellOf x).2 := by
  by_cases hx : ∃ c, IsDig x c
  · obtain ⟨c, hc⟩ := hx
    have hl := length_pre_of_isDig hc
    have he := eq_cellIn_of_isDig hc
    rw [cellOf_of_isDig hc]
    simp only [cellOv]
    cases hv : ov x with
    | none =>
      rw [ite_eq_right fun h ↦ by have := h.2 c; rw [← he, hv] at this; simp at this]
      rfl
    | some y =>
      have hall : ∀ c', (ov (cellIn (pre x) c')).isSome := fun c' ↦
        hwhole _ hl c c' (by rw [← he, hv]; rfl)
      rw [ite_eq_left ⟨hl, hall⟩]
      simp only [Option.map_some]
      rw [← he, hv]
      rfl
  · rw [cellOf_of_not hx]
    simp only [cellOv, Option.map_map]
    cases ov x <;> rfl

theorem hidGame_ov_isSome {d : Data} {s : Log} {x : Input} :
    ((hidGame d).ov s x).isSome ↔ ∃ k, deps k ⊆ rev d s ∧ pt (hOf d) (d none) k = x := by
  simp only [hidGame]
  split_ifs with hx
  · simp only [Option.isSome_some, true_iff]
    exact hx
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact hx

/-- An honest input of a call of a prefix is a digest call of one message. -/
theorem eq_dig_of_pt {d : Data} {k : Key} {p : Input} {c : DigestCall} (hp : p.1.length = 80)
    (h : pt (hOf d) (d none) k = cellIn p c) :
    ∃ m, k = .dig m c ∧ ∀ c', pt (hOf d) (d none) (.dig m c') = cellIn p c' := by
  have hv := congrArg Subtype.val h
  have hlen := congrArg List.length hv
  have hc : (cellIn p c).1.length = 84 := by
    show (p.1.take 80 ++ callBytes c).length = 84
    rw [List.length_append, callBytes_length, List.length_take, hp]
    rfl
  have hE : (pt (hOf d) (d none) k).1.length = (input (hOf d) (d none) k).length := rfl
  rw [hc, hE] at hlen
  cases k with
  | pkSeed => rw [length_input_pkSeed (hOf d) (d none)] at hlen; omega
  | prf => rw [length_input_prf (hOf d) (d none)] at hlen; omega
  | ots a b c' e => rw [length_input_ots (hOf d) (d none) a b c' e] at hlen; omega
  | fts a b c' => rw [length_input_fts (hOf d) (d none) a b c'] at hlen; omega
  | pos q => rw [length_input_pos (hOf d) (d none) q] at hlen; omega
  | enc a b c' e => rw [length_input_enc (hOf d) (d none) a b c' e] at hlen; omega
  | rnd m => rw [length_input_rnd (hOf d) (d none) m] at hlen; omega
  | dig m c₀ =>
    have hv' : digPrefix (param (hOf d)) (dataOf (hOf d)).root m (rndOf (hOf d) m) ++ callBytes c₀ =
        p.1.take 80 ++ callBytes c := hv
    obtain ⟨hpre, hcall⟩ := List.append_inj hv' (by rw [digPrefix_length, List.length_take, hp]; rfl)
    refine ⟨m, by rw [callBytes_inj hcall], fun c' ↦ Subtype.ext ?_⟩
    show digPrefix (param (hOf d)) (dataOf (hOf d)).root m (rndOf (hOf d) m) ++ callBytes c' =
      p.1.take 80 ++ callBytes c'
    rw [hpre]

/-- **The hidden game overrides whole cells.** -/
theorem hidGame_ov_whole (d : Data) (s : Log) (p : Input) (hp : p.1.length = 80) (c c' : DigestCall)
    (h : ((hidGame d).ov s (cellIn p c)).isSome) : ((hidGame d).ov s (cellIn p c')).isSome := by
  obtain ⟨k, hk, hpt⟩ := hidGame_ov_isSome.mp h
  obtain ⟨m, rfl, hall⟩ := eq_dig_of_pt hp hpt
  exact hidGame_ov_isSome.mpr ⟨.dig m c', by simpa [deps] using hk, hall c'⟩

theorem gB_ov (r : Data) (δ : Fin signatureLimit → DigV) (s : Log) :
    (gB r δ).ov s = (hidGame (withDig r (dgOf δ (sig s)))).ov s := rfl

theorem gB_ov_spec (r : Data) (δ : Fin signatureLimit → DigV) (s : Log) (x : Input) :
    (gB r δ).ov s x = (cellOv ((gB r δ).ov s) (cellOf x).1).map fun v ↦ v (cellOf x).2 := by
  rw [gB_ov]
  exact cellOv_spec _ (fun p hp c c' h ↦ hidGame_ov_whole (withDig r (dgOf δ (sig s))) s p hp c c' h) x

/-! ## The covered digests -/

open Classical in
/-- The number of digests the presampled digests cover. -/
def sbF (δ : Fin signatureLimit → DigV) : ℕ :=
  (Finset.univ.filter fun v : DigV ↦ Covered (leavesAll δ) (fullDigestView (truncateMessageDigest v))).card

open Classical in
theorem sbF_le (δ : Fin signatureLimit → DigV) :
    (sbF δ : ℝ) / Fintype.card DigV ≤
      ∑ t, (cnt δ t : ℝ) ^ forsTrees / (Fintype.card Index * Fintype.card (FTree → FLeaf)) := by
  have hv := card_view_filter (Covered (leavesAll δ))
  have hc : (Finset.univ.filter (Covered (leavesAll δ))).card ≤ ∑ t, cnt δ t ^ forsTrees := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    calc ∑ y : FTree → FLeaf, (if Covered (leavesAll δ) (t, y) then 1 else 0)
        = (Fintype.piFinset (leavesAll δ t)).card := by
          rw [← Finset.card_filter]
          congr 1
          ext y
          rw [Finset.mem_filter, Fintype.mem_piFinset]
          exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩
      _ ≤ ∏ _κ : FTree, cnt δ t := by
          rw [Fintype.card_piFinset]
          exact Finset.prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _) fun κ _ ↦ card_leavesAll_le δ t κ
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hD : (0 : ℝ) < Fintype.card DigV := Nat.cast_pos.mpr Fintype.card_pos
  have hI : (0 : ℝ) < Fintype.card Index := Nat.cast_pos.mpr Fintype.card_pos
  have hF : (0 : ℝ) < Fintype.card (FTree → FLeaf) := Nat.cast_pos.mpr Fintype.card_pos
  have hv' : (sbF δ : ℝ) * (Fintype.card Index * Fintype.card (FTree → FLeaf)) =
      Fintype.card DigV * (Finset.univ.filter (Covered (leavesAll δ))).card := by
    have := congrArg (Nat.cast : ℕ → ℝ) hv
    push_cast [Fintype.card_prod] at this
    rw [sbF]
    convert this using 2
  rw [← Finset.sum_div, div_le_div_iff₀ hD (mul_pos hI hF), hv']
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hD.le

end Qrom.Sphincs
