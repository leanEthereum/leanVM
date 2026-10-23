/-
  LeanVM.Protocol.Blake2sCircuit

  The BLAKE2s compression circuit of leanVM's Flock argument, as a product-gate circuit on a
  block of `2 ^ 14` positions, with its soundness against the compression function `compress`
  and its boundedness.
-/

module

public import LeanVM.Spec.Verifier
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Protocol.Blake2sHash
public import LeanVM.Parameters.Field
public import LeanVM.Protocol.ToArkLib.Flock.Words
public import LeanVM.Semantics.Lemmas

/-!
# The BLAKE2s compression circuit

Transcribed from leanVM at pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`crates/flock/src/hash.rs:40-63` (layout), `:141-160` (positions and gadget offsets) and
`:293-356` (`forward_walk`), with the adder rows of `crates/flock/src/gf2.rs`, cross-checked row
for row against `python-verifier/verifier.py:1179-1288` (`blake2s_row_values`) by the digest
test. The specification fixes the constant at position `512` and the row of each kind of wire
(`doc/leanvm/body/c-flock-protocol.tex:22-28`, `:205-215`: a product `(u, u')`, a committed XOR
`(S_w, 1)`, a source `(w, 1)`, an empty position zero), which `rowOf` implements; it does not
fix the circuit or its other positions.

The block of `2 ^ 14` bits (`hash.rs:41-53`):

* `0 … 255`: the chaining value `h`, eight words; `256 … 511`: the output, eight words;
  `512`: the constant `1`; `640 … 1151`: the message, sixteen words; `1152`, `1184`: the
  counter's low and high words; `1216`, `1248`: the two flag words. All of them but the output
  and the constant are inputs.
* `1280 … 15999`: the products of the 80 mixing steps, 184 each: the three-operand adder
  `a + b + m_x` (61), the adder `c + d_1` (31), the three-operand adder `a_1 + b_1 + m_y` (61),
  the adder `c_1 + d_2` (31), each adder's carries as in `ToArkLib/Flock/Words.lean`.
* Every other position is padding, with the zero row.

No intermediate word is committed: XORs and rotations are substituted into their consumers, and
the output rows are `(out bit, 1)`. `compressW` is `compress` with the word operations replaced
by the gadgets, so `sound_compressW` follows the specification step by step.

* `blake2sCircuit`, `bounded_blake2s` (from the gate-count contracts, without evaluating the
  circuit: exactly `14720` gates from `1280`).
* `blake2s_sound`, `blake2s_sound_words`: a Boolean block satisfying the circuit's R1CS over a
  nontrivial ring of characteristic two, with `1` at the constant position, carries at its output
  positions the compression of the words it carries at its input positions.
* `blake2s_complete`: the trace of any input satisfies the R1CS, holds `1` at the constant, keeps
  its inputs, and so carries the compression of the input words at its output positions.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics ProductCircuit ProductCircuit.Start

@[expose] public section

namespace Blake2sCircuit

/-! ## The layout -/

/-- The block's log-size, `14`. -/
abbrev m : ℕ := Flock.kSkip + Flock.kIn

/-- The first message position. -/
abbrev msgBase : ℕ := 640

/-- The counter's low word. -/
abbrev counterLo : ℕ := 1152

/-- The counter's high word. -/
abbrev counterHi : ℕ := 1184

/-- The last-block flag word. -/
abbrev finalFlag : ℕ := 1216

/-- The last-node flag word. -/
abbrev lastNodeFlag : ℕ := 1248

/-- The first gate position. -/
abbrev gateBase : ℕ := 1280

/-- Chaining-value word `w`, at `32 w`. -/
def cvW (w : ℕ) : Word m := inW (32 * w)

/-- Message word `w`, at `640 + 32 w`. -/
def msgW (w : ℕ) : Word m := inW (msgBase + 32 * w)

/-- Output word `w`, at `256 + 32 w`. -/
def outW (w : ℕ) : Word m := inW (256 + 32 * w)

/-! ## The gadgets -/

/-- The mixing function `G`, mirroring `Blake2s.mix`. -/
def gW (v : Vector (Word m) 16) (a b c d : Fin 16) (mx my : Word m) :
    Builder m (Vector (Word m) 16) := do
  let a1 ← add3W v[a] v[b] mx
  let d1 := rotrW (xorW v[d] a1) 16
  let c1 ← addW v[c] d1
  let b1 := rotrW (xorW v[b] c1) 12
  let a2 ← add3W a1 b1 my
  let d2 := rotrW (xorW d1 a2) 8
  let c2 ← addW c1 d2
  let b2 := rotrW (xorW b1 c2) 7
  pure ((((v.set a a2).set b b2).set c c2).set d d2)

/-- One round, mirroring `Blake2s.round`. -/
def roundW (v m' : Vector (Word m) 16) (s : Vector (Fin 16) 16) :
    Builder m (Vector (Word m) 16) := do
  let v ← gW v 0 4 8 12 m'[s[0]] m'[s[1]]
  let v ← gW v 1 5 9 13 m'[s[2]] m'[s[3]]
  let v ← gW v 2 6 10 14 m'[s[4]] m'[s[5]]
  let v ← gW v 3 7 11 15 m'[s[6]] m'[s[7]]
  let v ← gW v 0 5 10 15 m'[s[8]] m'[s[9]]
  let v ← gW v 1 6 11 12 m'[s[10]] m'[s[11]]
  let v ← gW v 2 7 8 13 m'[s[12]] m'[s[13]]
  gW v 3 4 9 14 m'[s[14]] m'[s[15]]

/-- The initial working vector, mirroring `Blake2s.initialState`: `h`, `iv[0..4]`, and
`iv[4..8]` XOR the counter's two words and the two flag words. -/
def initW : Vector (Word m) 16 :=
  Vector.ofFn fun w : Fin 16 ↦
    if w.val < 8 then cvW w
    else if w.val < 12 then litW Flock.constPos iv[w.val - 8]
    else xorW (litW Flock.constPos iv[w.val - 8]) (inW (counterLo + 32 * (w.val - 12)))

/-- The compression's output words, mirroring `compress`. -/
def compressW : Builder m (Vector (Word m) 8) := do
  let msg : Vector (Word m) 16 := Vector.ofFn fun w ↦ msgW w
  let v ← sigma.foldlM (fun v s ↦ roundW v msg s) initW
  pure (Vector.ofFn fun w : Fin 8 ↦ xorW (xorW v[w] v[w.val + 8]) (cvW w))

/-! ## The circuit -/

/-- The input positions: `0 … 255` and `640 … 1279`. -/
def inputs : Form m := BitVec.ofNat _ (2 ^ 256 - 1) ||| (BitVec.ofNat _ (2 ^ 640 - 1) <<< 640)

/-- The output rows `(out bit, 1)` at `256 + 32 w + i`. -/
def outRows (outs : Vector (Word m) 8) : List (Pos m × Gate m) :=
  (List.finRange 8).flatMap fun w ↦
    (List.finRange 32).map fun i ↦
      (pos (256 + 32 * w.val + i.val), ⟨outs[w][i], Form.var Flock.constPos⟩)

/-- The BLAKE2s compression circuit: the product gates from `1280`, then the output rows.
Irreducible, so that no unification evaluates it. -/
@[irreducible] def blake2sCircuit : ProductCircuit m :=
  let r := compressW.run ⟨gateBase, #[]⟩
  { cpos := Flock.constPos, inputs := inputs, gates := r.2.gates ++ (outRows r.1).toArray }

theorem blake2sCircuit_cpos : blake2sCircuit.cpos = Flock.constPos := by
  unfold blake2sCircuit; rfl

theorem blake2sCircuit_inputs : blake2sCircuit.inputs = inputs := by
  unfold blake2sCircuit; rfl

theorem blake2sCircuit_gates : blake2sCircuit.gates =
    (compressW.run ⟨gateBase, #[]⟩).2.gates ++
      (outRows (compressW.run ⟨gateBase, #[]⟩).1).toArray := by
  unfold blake2sCircuit; rfl

theorem getLsbD_inputs (j : ℕ) :
    inputs.getLsbD j = decide (j < 256 ∨ (640 ≤ j ∧ j < 1280)) := by
  have h2 : 2 ^ m = 16384 := rfl
  rw [inputs, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one,
    Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, h2]
  omega

/-! ## Soundness -/

section Soundness

variable {w : Pos m → Bool}

private theorem sound_gW {v : Vector (Word m) 16} {vu : Vector UInt32 16} (a b c d : Fin 16)
    {mx my : Word m} {mxu myu : UInt32} (hv : ∀ j : Fin 16, Den w v[j] vu[j]) (hmx : Den w mx mxu)
    (hmy : Den w my myu) :
    Sound w (gW v a b c d mx my)
      (fun v' ↦ ∀ j : Fin 16, Den w v'[j] (Blake2s.mix vu a b c d mxu myu)[j]) := by
  unfold gW Blake2s.mix
  refine sound_bind (sound_add3W (hv a) (hv b) hmx) (fun _ ↦ ?_) fun a1 ha1 ↦ ?_
  · exact grows_bind (grows_addW _ _) fun _ ↦ grows_bind (grows_add3W _ _ _) fun _ ↦
      grows_bind (grows_addW _ _) fun _ ↦ grows_pure _
  have hd1 := den_rotrW (den_xorW (hv d) ha1) (n := 16) (by decide)
  refine sound_bind (sound_addW (hv c) hd1) (fun _ ↦ ?_) fun c1 hc1 ↦ ?_
  · exact grows_bind (grows_add3W _ _ _) fun _ ↦ grows_bind (grows_addW _ _) fun _ ↦ grows_pure _
  have hb1 := den_rotrW (den_xorW (hv b) hc1) (n := 12) (by decide)
  refine sound_bind (sound_add3W ha1 hb1 hmy) (fun _ ↦ ?_) fun a2 ha2 ↦ ?_
  · exact grows_bind (grows_addW _ _) fun _ ↦ grows_pure _
  have hd2 := den_rotrW (den_xorW hd1 ha2) (n := 8) (by decide)
  refine sound_bind (sound_addW hc1 hd2) (fun _ ↦ grows_pure _) fun c2 hc2 ↦ ?_
  have hb2 := den_rotrW (den_xorW hb1 hc2) (n := 7) (by decide)
  refine sound_pure fun j ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_set]
  split_ifs
  · exact hd2
  · exact hc2
  · exact hb2
  · exact ha2
  · exact hv j

private theorem grows_gW (v : Vector (Word m) 16) (a b c d : Fin 16) (mx my : Word m) :
    Grows (gW v a b c d mx my) := by
  unfold gW
  exact grows_bind (grows_add3W _ _ _) fun _ ↦ grows_bind (grows_addW _ _) fun _ ↦
    grows_bind (grows_add3W _ _ _) fun _ ↦ grows_bind (grows_addW _ _) fun _ ↦ grows_pure _

-- From here on the gadgets are opaque to unification: a failed match against an unfolded
-- gadget would evaluate its loops.
attribute [local irreducible] gW addW add3W

/-- Discharges `Grows` for chains of `gW` calls. -/
local macro "grows_gW_chain" : tactic =>
  `(tactic| repeat' (first | refine grows_bind (grows_gW _ _ _ _ _ _ _) fun _ ↦ ?_ |
    exact grows_gW _ _ _ _ _ _ _))

private theorem grows_roundW (v m' : Vector (Word m) 16) (s : Vector (Fin 16) 16) :
    Grows (roundW v m' s) := by
  unfold roundW
  grows_gW_chain

private theorem sound_roundW {v m' : Vector (Word m) 16} {vu mu : Vector UInt32 16}
    (s : Vector (Fin 16) 16) (hv : ∀ j : Fin 16, Den w v[j] vu[j])
    (hm : ∀ j : Fin 16, Den w m'[j] mu[j]) :
    Sound w (roundW v m' s) (fun v' ↦ ∀ j : Fin 16, Den w v'[j] (Blake2s.round vu mu s)[j]) := by
  unfold roundW Blake2s.round
  refine sound_bind (sound_gW 0 4 8 12 hv (hm _) (hm _)) (fun _ ↦ by grows_gW_chain) fun v1 h1 ↦ ?_
  refine sound_bind (sound_gW 1 5 9 13 h1 (hm _) (hm _)) (fun _ ↦ by grows_gW_chain) fun v2 h2 ↦ ?_
  refine sound_bind (sound_gW 2 6 10 14 h2 (hm _) (hm _)) (fun _ ↦ by grows_gW_chain) fun v3 h3 ↦ ?_
  refine sound_bind (sound_gW 3 7 11 15 h3 (hm _) (hm _)) (fun _ ↦ by grows_gW_chain) fun v4 h4 ↦ ?_
  refine sound_bind (sound_gW 0 5 10 15 h4 (hm _) (hm _)) (fun _ ↦ by grows_gW_chain) fun v5 h5 ↦ ?_
  refine sound_bind (sound_gW 1 6 11 12 h5 (hm _) (hm _)) (fun _ ↦ by grows_gW_chain) fun v6 h6 ↦ ?_
  refine sound_bind (sound_gW 2 7 8 13 h6 (hm _) (hm _)) (fun _ ↦ by grows_gW_chain) fun v7 h7 ↦ ?_
  exact sound_gW 3 4 9 14 h7 (hm _) (hm _)

attribute [local irreducible] roundW

private theorem grows_rounds (msg : Vector (Word m) 16) (l : List (Vector (Fin 16) 16))
    (v : Vector (Word m) 16) : Grows (l.foldlM (fun v s ↦ roundW v msg s) v) := by
  induction l generalizing v with
  | nil => exact grows_pure _
  | cons s l ih => rw [List.foldlM_cons]; exact grows_bind (grows_roundW _ _ _) ih

private theorem sound_rounds {msg : Vector (Word m) 16} {mu : Vector UInt32 16}
    (hm : ∀ j : Fin 16, Den w msg[j] mu[j]) (l : List (Vector (Fin 16) 16))
    (v : Vector (Word m) 16) (vu : Vector UInt32 16) (hv : ∀ j : Fin 16, Den w v[j] vu[j]) :
    Sound w (l.foldlM (fun v s ↦ roundW v msg s) v)
      (fun v' ↦ ∀ j : Fin 16, Den w v'[j] (l.foldl (fun v s ↦ Blake2s.round v mu s) vu)[j]) := by
  induction l generalizing v vu with
  | nil => exact sound_pure hv
  | cons s l ih =>
    rw [List.foldlM_cons, List.foldl_cons]
    exact sound_bind (sound_roundW s hv hm) (grows_rounds msg l) fun v' hv' ↦ ih v' _ hv'

/-- The initial working vector denotes `initialState`, given the input words and the
constant. -/
private theorem den_initW {h : Vector UInt32 8} {t : UInt64} {f0 f1 : UInt32}
    (hh : ∀ k : Fin 8, Den w (cvW k) h[k]) (ht0 : Den w (inW counterLo) t.toUInt32)
    (ht1 : Den w (inW counterHi) (t >>> 32).toUInt32) (hf0 : Den w (inW finalFlag) f0)
    (hf1 : Den w (inW lastNodeFlag) f1) (hc : w Flock.constPos = true) :
    ∀ j : Fin 16, Den w initW[j] (Blake2s.initialState h t f0 f1)[j] := by
  intro j
  fin_cases j <;> simp only [initW, Blake2s.initialState, Fin.getElem_fin, Vector.getElem_ofFn,
    Vector.getElem_set] <;> simp
  · exact den_congr (hh 0) (Vector.getElem_append_left (by decide)).symm
  · exact den_congr (hh 1) (Vector.getElem_append_left (by decide)).symm
  · exact den_congr (hh 2) (Vector.getElem_append_left (by decide)).symm
  · exact den_congr (hh 3) (Vector.getElem_append_left (by decide)).symm
  · exact den_congr (hh 4) (Vector.getElem_append_left (by decide)).symm
  · exact den_congr (hh 5) (Vector.getElem_append_left (by decide)).symm
  · exact den_congr (hh 6) (Vector.getElem_append_left (by decide)).symm
  · exact den_congr (hh 7) (Vector.getElem_append_left (by decide)).symm
  · exact den_congr (den_litW hc _)
      (by rw [Vector.getElem_append_right (by decide) (by decide)]; rfl)
  · exact den_congr (den_litW hc _)
      (by rw [Vector.getElem_append_right (by decide) (by decide)])
  · exact den_congr (den_litW hc _)
      (by rw [Vector.getElem_append_right (by decide) (by decide)])
  · exact den_congr (den_litW hc _)
      (by rw [Vector.getElem_append_right (by decide) (by decide)])
  · exact den_congr (den_xorW (den_litW hc _) ht0)
      (by rw [Vector.getElem_append_right (by decide) (by decide)])
  · exact den_congr (den_xorW (den_litW hc _) ht1)
      (by rw [Vector.getElem_append_right (by decide) (by decide)])
  · exact den_congr (den_xorW (den_litW hc _) hf0)
      (by rw [Vector.getElem_append_right (by decide) (by decide)])
  · exact den_congr (den_xorW (den_litW hc _) hf1)
      (by rw [Vector.getElem_append_right (by decide) (by decide)])

/-- An output word of `compress`: `h[k] ^ v[k] ^ v[k + 8]` for the final working vector `v`. -/
private theorem compress_getElem (h : Vector UInt32 8) (msg : Vector UInt32 16) (t : UInt64)
    (f0 f1 : UInt32) (k : Fin 8) :
    (compress h msg t f0 f1)[k] =
      h[k] ^^^
      (sigma.foldl (fun v s ↦ Blake2s.round v msg s) (Blake2s.initialState h t f0 f1))[k.1] ^^^
      (sigma.foldl (fun v s ↦ Blake2s.round v msg s)
        (Blake2s.initialState h t f0 f1))[k.1 + 8] := by
  fin_cases k <;> rfl

/-- The compression gadget is sound: if its gates hold, its eight output words denote the
compression of the words at the input positions. -/
private theorem sound_compressW {h : Vector UInt32 8} {msg : Vector UInt32 16} {t : UInt64}
    {f0 f1 : UInt32} (hh : ∀ k : Fin 8, Den w (cvW k) h[k])
    (hm : ∀ k : Fin 16, Den w (msgW k) msg[k])
    (ht0 : Den w (inW counterLo) t.toUInt32) (ht1 : Den w (inW counterHi) (t >>> 32).toUInt32)
    (hf0 : Den w (inW finalFlag) f0) (hf1 : Den w (inW lastNodeFlag) f1)
    (hc : w Flock.constPos = true) :
    Sound w compressW (fun out ↦ ∀ k : Fin 8, Den w out[k] (compress h msg t f0 f1)[k]) := by
  unfold compressW
  dsimp only
  rw [← Vector.foldlM_toList]
  have hmsg : ∀ k : Fin 16, Den w (Vector.ofFn fun k : Fin 16 ↦ msgW k)[k] msg[k] := fun k ↦ by
    rw [Fin.getElem_fin, Vector.getElem_ofFn]
    exact hm k
  refine sound_bind (sound_rounds hmsg sigma.toList initW _
    (den_initW hh ht0 ht1 hf0 hf1 hc)) (fun _ ↦ grows_pure _) fun v hv ↦ sound_pure ?_
  intro k
  rw [Vector.foldl_toList] at hv
  rw [Fin.getElem_fin, Vector.getElem_ofFn, compress_getElem]
  refine den_congr (den_xorW (den_xorW (hv ⟨k, by omega⟩) (hv ⟨k + 8, by omega⟩)) (hh k)) ?_
  simp only [Fin.getElem_fin]
  rw [UInt32.xor_comm, UInt32.xor_assoc]

end Soundness

/-! ## Boundedness -/

private theorem constPos_val : (Flock.constPos : ℕ) = 512 := rfl

/-- No position from `1280` on is an input or the constant. -/
theorem fresh_from_gateBase (j : ℕ) (hj : 1280 ≤ j) :
    (inputs ||| Form.var Flock.constPos).getLsbD j = false := by
  rw [BitVec.getLsbD_or, getLsbD_inputs, getLsbD_var, constPos_val, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, decide_eq_false_iff_not]
  omega

/-- The start: the inputs and the constant are available, gates from `1280`. -/
def start : Start m where
  avail := inputs ||| Form.var Flock.constPos
  base := gateBase
  fresh := fresh_from_gateBase

private theorem start_avail (j : ℕ) :
    start.avail.getLsbD j = decide (j < 256 ∨ j = 512 ∨ (640 ≤ j ∧ j < 1280)) := by
  rw [start, BitVec.getLsbD_or, getLsbD_inputs, getLsbD_var, constPos_val, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

private theorem start_availAt (n j : ℕ) :
    start.AvailAt n j = true ↔ j < 256 ∨ j = 512 ∨ (640 ≤ j ∧ j < 1280) ∨ (1280 ≤ j ∧ j < n) := by
  rw [availAt_iff, start_avail, decide_eq_true_iff]
  show _ ∨ (1280 ≤ j ∧ j < n) ↔ _
  omega

private theorem subW_inW_start {b : ℕ} (hb : b + 32 ≤ 256 ∨ (640 ≤ b ∧ b + 32 ≤ 1280)) (n : ℕ) :
    start.SubW (inW b) n :=
  subW_inW (by show b + 32 ≤ 16384; omega)
    (fun i hi ↦ by rw [start_avail, decide_eq_true_iff]; omega) n

/-- Every word of a vector reads only positions available at `n`. -/
private def SubV {k : ℕ} (v : Vector (Word m) k) (n : ℕ) : Prop := ∀ j : Fin k, start.SubW v[j] n

private theorem SubV.mono {k : ℕ} {v : Vector (Word m) k} {n n' : ℕ} (h : SubV v n) (hn : n ≤ n') :
    SubV v n' := fun j ↦ (h j).mono hn

private theorem SubV.set {v : Vector (Word m) 16} {n : ℕ} (hv : SubV v n) (a : Fin 16) {x : Word m}
    (hx : start.SubW x n) : SubV (v.set a x) n := by
  intro j
  simp only [Fin.getElem_fin, Vector.getElem_set]
  split_ifs
  · exact hx
  · exact hv j

private theorem ok_gW {n₀ : ℕ} {v : Vector (Word m) 16} (a b c d : Fin 16) {mx my : Word m}
    (hv : SubV v n₀) (hmx : start.SubW mx n₀) (hmy : start.SubW my n₀) :
    start.Ok n₀ (gW v a b c d mx my) 184 SubV := by
  unfold gW
  refine ok_bind (ok_add3W (hv a) (hv b) hmx) (by omega) fun a1 n₁ hn₁ ha1 ↦ ?_
  have hd1 := subW_rotrW (subW_xorW ((hv d).mono hn₁) ha1) 16
  refine ok_bind (ok_addW ((hv c).mono hn₁) hd1) (by omega) fun c1 n₂ hn₂ hc1 ↦ ?_
  have hb1 := subW_rotrW (subW_xorW ((hv b).mono (by omega)) hc1) 12
  refine ok_bind (ok_add3W (ha1.mono hn₂) hb1 (hmy.mono (by omega))) (by omega)
    fun a2 n₃ hn₃ ha2 ↦ ?_
  have hd2 := subW_rotrW (subW_xorW (hd1.mono (by omega)) ha2) 8
  refine ok_bind (ok_addW (hc1.mono hn₃) hd2) (by omega) fun c2 n₄ hn₄ hc2 ↦ ?_
  have hb2 := subW_rotrW (subW_xorW (hb1.mono (by omega)) hc2) 7
  refine ok_pure (fun n hn ↦ ?_) (by omega)
  exact ((((hv.mono (by omega)).set a ((ha2.mono hn₄).mono hn)).set b (hb2.mono hn)).set c
    ((hc2.mono hn))).set d ((hd2.mono hn₄).mono hn)

attribute [local irreducible] gW

private theorem ok_roundW {n₀ : ℕ} {v m' : Vector (Word m) 16} (s : Vector (Fin 16) 16)
    (hv : SubV v n₀)
    (hm : SubV m' n₀) : start.Ok n₀ (roundW v m' s) 1472 SubV := by
  unfold roundW
  refine ok_bind (ok_gW 0 4 8 12 hv (hm _) (hm _)) (by omega) fun v1 n1 h1 hv1 ↦ ?_
  have hm1 := hm.mono h1
  refine ok_bind (ok_gW 1 5 9 13 hv1 (hm1 _) (hm1 _)) (by omega) fun v2 n2 h2 hv2 ↦ ?_
  have hm2 := hm1.mono h2
  refine ok_bind (ok_gW 2 6 10 14 hv2 (hm2 _) (hm2 _)) (by omega) fun v3 n3 h3 hv3 ↦ ?_
  have hm3 := hm2.mono h3
  refine ok_bind (ok_gW 3 7 11 15 hv3 (hm3 _) (hm3 _)) (by omega) fun v4 n4 h4 hv4 ↦ ?_
  have hm4 := hm3.mono h4
  refine ok_bind (ok_gW 0 5 10 15 hv4 (hm4 _) (hm4 _)) (by omega) fun v5 n5 h5 hv5 ↦ ?_
  have hm5 := hm4.mono h5
  refine ok_bind (ok_gW 1 6 11 12 hv5 (hm5 _) (hm5 _)) (by omega) fun v6 n6 h6 hv6 ↦ ?_
  have hm6 := hm5.mono h6
  refine ok_bind (ok_gW 2 7 8 13 hv6 (hm6 _) (hm6 _)) (by omega) fun v7 n7 h7 hv7 ↦ ?_
  have hm7 := hm6.mono h7
  exact (ok_gW 3 4 9 14 hv7 (hm7 _) (hm7 _)).cast (by omega)

attribute [local irreducible] roundW

private theorem ok_rounds (msg : Vector (Word m) 16) (l : List (Vector (Fin 16) 16)) :
    ∀ (v : Vector (Word m) 16) (n₀ : ℕ), SubV v n₀ → SubV msg n₀ →
      start.Ok n₀ (l.foldlM (fun v s ↦ roundW v msg s) v) (1472 * l.length) SubV := by
  induction l with
  | nil =>
    intro v n₀ hv _
    rw [List.foldlM_nil]
    exact ok_pure (fun n hn ↦ hv.mono hn) (by simp)
  | cons s l ih =>
    intro v n₀ hv hm
    rw [List.foldlM_cons]
    exact ok_bind (ok_roundW s hv hm) (by simp only [List.length_cons]; omega)
      fun v' n₁ hn₁ hv' ↦
        (ih v' n₁ hv' (hm.mono hn₁)).cast (by simp only [List.length_cons]; omega)

private theorem subV_initW : SubV initW gateBase := by
  intro j
  rw [initW, Fin.getElem_fin, Vector.getElem_ofFn]
  have hc : start.avail.getLsbD Flock.constPos = true := by
    rw [start_avail, constPos_val]; decide
  split_ifs with h h'
  · exact subW_inW_start (by omega) _
  · exact subW_litW hc _ _
  · exact subW_xorW (subW_litW hc _ _) (subW_inW_start (by simp only [counterLo]; omega) _)

private theorem subV_msg : SubV (Vector.ofFn fun w : Fin 16 ↦ msgW w) gateBase := by
  intro j
  rw [Fin.getElem_fin, Vector.getElem_ofFn]
  exact subW_inW_start (by simp only [msgBase]; omega) _

/-- The compression records exactly `14720` gates from `1280`, keeps the schedule bounded, and
its output words read only available positions. -/
private theorem ok_compressW : start.Ok gateBase compressW 14720 SubV := by
  unfold compressW
  dsimp only
  rw [← Vector.foldlM_toList]
  refine ok_bind (ok_rounds _ sigma.toList initW gateBase subV_initW subV_msg)
    (by rw [Vector.length_toList]) fun v _ _ hv ↦ ok_pure (fun n hn w ↦ ?_)
      (by rw [Vector.length_toList])
  rw [Fin.getElem_fin, Vector.getElem_ofFn]
  exact subW_xorW (subW_xorW ((hv ⟨w, by omega⟩).mono hn) ((hv ⟨w + 8, by omega⟩).mono hn))
    (subW_inW_start (by omega) _)

/-- The product gates occupy exactly `[1280, 16000)`. -/
theorem compressW_next : (compressW.run ⟨gateBase, #[]⟩).2.next = 16000 :=
  (ok_compressW ⟨gateBase, #[]⟩ inv_init le_rfl (by decide)).2.1

private theorem pos_out_val (w : Fin 8) (i : Fin 32) :
    ((pos (256 + 32 * w.val + i.val) : Pos m) : ℕ) = 256 + 32 * w.val + i.val :=
  pos_val (by have := w.isLt; have := i.isLt; show _ < 16384; omega)

private theorem mem_outRows {outs : Vector (Word m) 8} {kg : Pos m × Gate m}
    (h : kg ∈ outRows outs) :
    ∃ (w : Fin 8) (i : Fin 32),
      kg = (pos (256 + 32 * w.val + i.val), ⟨outs[w][i], Form.var Flock.constPos⟩) := by
  unfold outRows at h
  simp only [List.mem_flatMap, List.mem_finRange, List.mem_map, true_and] at h
  obtain ⟨w, i, rfl⟩ := h
  exact ⟨w, i, rfl⟩

private theorem nodup_outRows (outs : Vector (Word m) 8) : ((outRows outs).map Prod.fst).Nodup := by
  unfold outRows
  rw [List.map_flatMap, List.nodup_flatMap]
  simp only [List.map_map]
  refine ⟨fun w _ ↦ (List.nodup_finRange 32).map fun i i' h ↦ ?_,
    (List.pairwise_lt_finRange 8).imp fun {w w'} hw ↦ ?_⟩
  · have := congrArg Fin.val h
    simp only [Function.comp_apply, pos_out_val] at this
    exact Fin.ext (by omega)
  · rw [Function.onFun, List.disjoint_left]
    intro p hp hp'
    simp only [List.mem_map, List.mem_finRange, true_and, Function.comp_apply] at hp hp'
    obtain ⟨i, rfl⟩ := hp
    obtain ⟨i', he⟩ := hp'
    have := congrArg Fin.val he
    rw [pos_out_val, pos_out_val] at this
    have : (w : ℕ) < w' := hw
    have := i.isLt
    have := i'.isLt
    omega

/-- The output rows read only the final availability, at the fresh positions `256 … 511`. -/
private theorem boundedFrom_outRows (r : Vector (Word m) 8 × BuildState m) (hinv : start.Inv r.2)
    (hout : SubV r.1 r.2.next) :
    BoundedFrom (availAfter start.avail r.2.gates.toList) (outRows r.1) := by
  have hc : start.avail.getLsbD Flock.constPos = true := by
    rw [start_avail, constPos_val]; decide
  refine boundedFrom_of_nodup _ _ (fun kg hkg ↦ ?_) (fun kg hkg ↦ ?_) (nodup_outRows _)
  · obtain ⟨w, i, rfl⟩ := mem_outRows hkg
    exact ⟨sub_of_subN hinv.avail (hout w i), sub_of_subN hinv.avail (subN_start hc _)⟩
  · obtain ⟨w, i, rfl⟩ := mem_outRows hkg
    rw [hinv.avail, pos_out_val, Bool.eq_false_iff, ne_eq, start_availAt]
    have := w.isLt
    have := i.isLt
    omega

private theorem toList_append_toArray {α : Type} (A : Array α) (l : List α) :
    (A ++ l.toArray).toList = A.toList ++ l := by
  simp

/-- The BLAKE2s circuit is bounded: every gate reads only inputs, the constant and earlier
gates, at a fresh position. Proved from the gate-count contracts, without evaluating the
circuit. -/
theorem bounded_blake2s : blake2sCircuit.Bounded := by
  have hok := ok_compressW ⟨gateBase, #[]⟩ inv_init le_rfl (by decide)
  rw [Bounded, blake2sCircuit_inputs, blake2sCircuit_cpos, blake2sCircuit_gates,
    toList_append_toArray, boundedFrom_append]
  exact ⟨hok.1.bounded, boundedFrom_outRows _ hok.1 hok.2.2⟩

/-! ## Soundness of the circuit -/

/-- Soundness of the BLAKE2s circuit: in a Boolean block satisfying its R1CS over a nontrivial
ring of characteristic two, with `1` at the constant position, the output positions carry the
compression of the words at the input positions. -/
theorem blake2s_sound {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (z : Pos m → Bool)
    (hz : (blake2sCircuit.toBlockR1CS R).Holds (liftBlock R z)) (h1 : z Flock.constPos = true)
    {h : Vector UInt32 8} {msg : Vector UInt32 16} {t : UInt64} {f0 f1 : UInt32}
    (hh : ∀ k : Fin 8, Den z (cvW k) h[k]) (hm : ∀ k : Fin 16, Den z (msgW k) msg[k])
    (ht0 : Den z (inW counterLo) t.toUInt32) (ht1 : Den z (inW counterHi) (t >>> 32).toUInt32)
    (hf0 : Den z (inW finalFlag) f0) (hf1 : Den z (inW lastNodeFlag) f1) :
    ∀ k : Fin 8, Den z (outW k) (compress h msg t f0 f1)[k] := by
  have hg := gates_of_holds bounded_blake2s z hz
  have hsound := sound_compressW hh hm ht0 ht1 hf0 hf1 h1 ⟨gateBase, #[]⟩
  rw [blake2sCircuit_gates] at hg
  generalize compressW.run ⟨gateBase, #[]⟩ = r at hg hsound
  have hout := hsound fun kg hkg ↦ hg kg (Array.mem_append_left _ hkg)
  intro k i
  have hmem : (pos (256 + 32 * k.val + i.val),
      (⟨r.1[k][i], Form.var Flock.constPos⟩ : Gate m)) ∈ outRows r.1 :=
    List.mem_flatMap.mpr ⟨k, List.mem_finRange k, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩
  have hrow := hg _ (Array.mem_append_right _ (List.mem_toArray.mpr hmem))
  dsimp only at hrow
  rw [outW, inW, Fin.getElem_fin, Vector.getElem_ofFn, eval_var, hrow, eval_var, h1,
    Bool.and_true]
  exact hout k i

/-- Soundness, in words: a satisfying block's output words are the compression of its input
words. -/
theorem blake2s_sound_words {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]
    (z : Pos m → Bool) (hz : (blake2sCircuit.toBlockR1CS R).Holds (liftBlock R z))
    (h1 : z Flock.constPos = true) (k : Fin 8) :
    readWord z (256 + 32 * k) =
      (compress (Vector.ofFn fun j : Fin 8 ↦ readWord z (32 * j))
        (Vector.ofFn fun j : Fin 16 ↦ readWord z (msgBase + 32 * j))
        ((readWord z counterLo).toUInt64 ||| ((readWord z counterHi).toUInt64 <<< 32))
        (readWord z finalFlag) (readWord z lastNodeFlag))[k] := by
  refine den_unique (den_readWord z _) (blake2s_sound z hz h1 (fun j ↦ ?_) (fun j ↦ ?_) ?_ ?_
    (den_readWord z _) (den_readWord z _) k)
  · simp only [Fin.getElem_fin, Vector.getElem_ofFn]; exact den_readWord z _
  · simp only [Fin.getElem_fin, Vector.getElem_ofFn]; exact den_readWord z _
  · refine den_congr (den_readWord z _) ?_
    apply UInt32.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  · refine den_congr (den_readWord z _) ?_
    apply UInt32.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi, show 32 + i < 64 by omega, show i < 64 by omega]

/-- The word a block holds depends only on its positions. -/
theorem readWord_congr {z z' : Pos m → Bool} {b : ℕ}
    (h : ∀ i < 32, z (pos (b + i)) = z' (pos (b + i))) :
    readWord z b = readWord z' b := by
  unfold readWord
  congr 2
  funext i
  exact h i i.isLt

/-- The trace keeps every input position. -/
theorem traceF_inputs (inp : Pos m → Bool) {j : Pos m} (hj : inputs.getLsbD j = true) :
    blake2sCircuit.traceF inp j = inp j := by
  refine traceF_input bounded_blake2s inp (by rw [blake2sCircuit_inputs]; exact hj) ?_
  rintro rfl
  rw [blake2sCircuit_cpos, getLsbD_inputs] at hj
  exact absurd (of_decide_eq_true hj) (by decide)

/-- Completeness of the BLAKE2s circuit: over a nontrivial ring of characteristic two, the trace of
any input satisfies the circuit's R1CS, holds `1` at the constant position, keeps its inputs, and
carries at its output positions the compression of the input words. -/
theorem blake2s_complete {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R] (inp : Pos m → Bool) :
    (blake2sCircuit.toBlockR1CS R).Holds (liftBlock R (blake2sCircuit.traceF inp)) ∧
      blake2sCircuit.traceF inp Flock.constPos = true ∧
      (∀ j : Pos m, inputs.getLsbD j = true → blake2sCircuit.traceF inp j = inp j) ∧
      ∀ k : Fin 8, readWord (blake2sCircuit.traceF inp) (256 + 32 * k) =
        (compress (Vector.ofFn fun j : Fin 8 ↦ readWord inp (32 * j))
          (Vector.ofFn fun j : Fin 16 ↦ readWord inp (msgBase + 32 * j))
          ((readWord inp counterLo).toUInt64 ||| ((readWord inp counterHi).toUInt64 <<< 32))
          (readWord inp finalFlag) (readWord inp lastNodeFlag))[k] := by
  have hs := trace_satisfies (R := R) bounded_blake2s inp
  have h1 : blake2sCircuit.traceF inp Flock.constPos = true := by
    rw [← blake2sCircuit_cpos]; exact traceF_cpos bounded_blake2s inp
  have hin : ∀ b, (∀ i < 32, inputs.getLsbD (b + i) = true) → b + 32 ≤ 2 ^ m →
      readWord (blake2sCircuit.traceF inp) b = readWord inp b := fun b hb hm ↦
    readWord_congr fun i hi ↦ traceF_inputs inp (by rw [pos_val (by omega)]; exact hb i hi)
  have hi : ∀ b, (b + 32 ≤ 256 ∨ (640 ≤ b ∧ b + 32 ≤ 1280)) →
      ∀ i < 32, inputs.getLsbD (b + i) = true :=
    fun b hb i hi ↦ by rw [getLsbD_inputs]; exact decide_eq_true (by omega)
  refine ⟨hs.1, h1, fun j hj ↦ traceF_inputs inp hj, fun k ↦ ?_⟩
  rw [blake2s_sound_words _ hs.1 h1 k]
  have e : ∀ b, (b + 32 ≤ 256 ∨ (640 ≤ b ∧ b + 32 ≤ 1280)) →
      readWord (blake2sCircuit.traceF inp) b = readWord inp b := fun b hb ↦
    hin b (hi b hb) (by show b + 32 ≤ 16384; omega)
  congr 1
  rw [e counterLo (by simp only [counterLo]; omega), e counterHi (by simp only [counterHi]; omega),
    e finalFlag (by simp only [finalFlag]; omega),
    e lastNodeFlag (by simp only [lastNodeFlag]; omega)]
  congr 1
  · exact Vector.ext fun j hj ↦ by simp only [Vector.getElem_ofFn]; exact e _ (by omega)
  · exact Vector.ext fun j hj ↦ by
      simp only [Vector.getElem_ofFn]; exact e _ (by simp only [msgBase]; omega)

end Blake2sCircuit

end
end LeanVM.Protocol
