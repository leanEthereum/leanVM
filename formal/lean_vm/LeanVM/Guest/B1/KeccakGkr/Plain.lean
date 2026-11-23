/-
  LeanVM.Guest.B1.KeccakGkr.Plain

  B1 of `keccak_plain_rounds`: its two specializations compute plain sumcheck rounds of degree
  two on the carried sponge.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Interface
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_plain_rounds__L4_L1»
import LeanVM.Guest.Data.ValNames.«keccak_plain_rounds__L6_L0»

/-!
# `keccak_plain_rounds`

`keccak_plain_rounds(fs0..fs4, p0, p1, cursor, value, point, tabs, n, k0)`: its
specializations `__L6_L0` (`fn% «keccak_plain_rounds__L6_L0»`) and `__L4_L1` (`fn%
«keccak_plain_rounds__L4_L1»`) copy the capacity, run `n` rounds, each a template `plainRoundT`
(`c₀`, `c₂` read and packed by `fs_next`, one `KECCAK` atom on the waiting scalars' rate cells and
the capacity, the round's grind of `0` bits, `challenge_from_state`, the challenge
stored at `point[i]`, the claim `c₀ + c·((claim + c₂) + c·c₂)`), and return the last capacity,
the cursor `·g^(2n)` and the claim. The bodies are the templates by kernel evaluation
(`stmtsEqb_sound`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## A round -/

/-- One plain round at index `i`: `c₀` read into `a`, `c₂` into `a + 3` (`fs_next`), the
statements `mid` (constants), the `KECCAK` atom on `ins` writing `o .. o + 12`,
the challenge its output `o` (`challenge_from_state`), then the claim from `vIn`:
`o + 13 = vIn + c₂`, the challenge stored at `pt[i]`, `o + 17 = c₀ + c·(o + 13 + c·c₂)`. -/
def plainRoundT (cur pt vIn : V) (ins : List V) (mid : List Stmt) (i a o : ℕ) : List Stmt :=
  fsNextT cur (2 * i) a ++ fsNextT cur (2 * i + 1) (a + 3) ++ mid ++
    [keccakA ins ((List.range 13).map fun k ↦ .n (o + k))] ++
    [.atom (.add (.n (o + 13)) vIn (.n (a + 3))), .atom (.load (.n o) pt i),
      .atom (.mul (.n (o + 14)) (.n o) (.n (a + 3))),
      .atom (.add (.n (o + 15)) (.n (o + 13)) (.n (o + 14))),
      .atom (.mul (.n (o + 16)) (.n o) (.n (o + 15))),
      .atom (.add (.n (o + 17)) (.n a) (.n (o + 16)))]

/-- What a round's statements ask of a valuation. -/
structure PlainRoundOk (rd : Reader) (σ : Val) (cur pt vIn : V) (ins : List V) (i a o : ℕ) :
    Prop where
  ld0 : LoadHolds rd (σ cur) (2 * i) (σ (.n a))
  pk0 : FsPackOk σ (.n a) (a + 1) dsObserve
  ld2 : LoadHolds rd (σ cur) (2 * i + 1) (σ (.n (a + 3)))
  pk2 : FsPackOk σ (.n (a + 3)) (a + 3 + 1) dsObserve
  kc : (Atom.keccak ins ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ
  st : LoadHolds rd (σ pt) i (σ (.n o))
  v : σ (.n (o + 17)) =
    σ (.n a) + σ (.n o) * ((σ vIn + σ (.n (a + 3))) + σ (.n o) * σ (.n (a + 3)))

theorem holds_plainRoundT {cur pt vIn : V} {ins : List V} {mid : List Stmt} {i a o : ℕ}
    {kret : List E → Prop} (hmid : Stmt.noRetList mid = true) {next : Prop}
    (h : Stmt.HoldsList C rd σ (plainRoundT cur pt vIn ins mid i a o) next kret) :
    (PlainRoundOk rd σ cur pt vIn ins i a o ∧ Stmt.HoldsList C rd σ mid True kret) ∧ next := by
  simp only [plainRoundT, holdsList_append, holds_fsNextT] at h
  obtain ⟨⟨l0, p0⟩, ⟨l2, p2⟩, h⟩ := h
  obtain ⟨hm, h⟩ := (holdsList_noRet mid hmid _ _).mp h
  simp only [keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨kc, e20, st, e21, e22, e23, e24, hn⟩ := h
  refine ⟨⟨⟨l0, p0, l2, p2, kc, st, ?_⟩, hm⟩, hn⟩
  rw [e24, e23, e22, e21, e20]

/-! ## A round on the carried sponge -/

theorem range13_map (f : ℕ → V) :
    (List.range 13).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12] :=
  rfl

/-- The sponge of a plain round: `c₀`, `c₂` absorbed after the waiting scalars, squeezed. -/
def plainSq (s : Fs) (c0 c2 : E) : E × Fs := ((s.absorb c0 dsObserve).absorb c2 dsObserve).squeeze

/-- **A round with nothing waiting**: the atom reads `c₀`'s and `c₂`'s rate cells, four zero
cells and the capacity; the challenge `o` and the outputs `o + 8 .. o + 12` are the
squeeze's. -/
theorem plain_round_sq0 {cur pt vIn : V} {zs capV : List V} {i a o : ℕ} {cap : List E}
    (h : PlainRoundOk rd σ cur pt vIn ([.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV)
      i a o)
    (hz : zs.map σ = [0, 0, 0, 0]) (hc : capV.map σ = cap) :
    σ (.n o) = (plainSq ⟨cap, []⟩ (σ (.n a)) (σ (.n (a + 3)))).1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        (plainSq ⟨cap, []⟩ (σ (.n a)) (σ (.n (a + 3)))).2.cap := by
  have s0 := fsNext_scalar h.pk0
  have s2 := fsNext_scalar h.pk2
  have habs : ((⟨cap, []⟩ : Fs).absorb (σ (.n a)) dsObserve).absorb (σ (.n (a + 3))) dsObserve =
      ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩ := rfl
  have hin : ([V.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV).map σ =
      rateOf [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)] ++ cap := by
    rw [rateOf_two, ← s0, ← s2, List.map_append, List.map_append, hz, hc]
    rfl
  have := squeeze_atom (s := ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩) h.kc hin
    (b := o) rfl
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [plainSq, habs]
  exact ⟨this.1, this.2⟩

/-- **A round with one scalar `w` waiting**, its rate cells `p0`, `p1`: the atom reads them,
`c₀`'s and `c₂`'s rate cells, two zero cells and the capacity. -/
theorem plain_round_sq1 {cur pt vIn p0 p1 : V} {zs capV : List V} {i a o : ℕ} {cap : List E} {w : E}
    (h : PlainRoundOk rd σ cur pt vIn
      ([p0, p1, .n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV) i a o)
    (hp : (σ p0, σ p1) = Keccak.scalarCells w dsObserve)
    (hz : zs.map σ = [0, 0]) (hc : capV.map σ = cap) :
    σ (.n o) = (plainSq ⟨cap, [(w, dsObserve)]⟩ (σ (.n a)) (σ (.n (a + 3)))).1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        (plainSq ⟨cap, [(w, dsObserve)]⟩ (σ (.n a)) (σ (.n (a + 3)))).2.cap := by
  have s0 := fsNext_scalar h.pk0
  have s2 := fsNext_scalar h.pk2
  have habs : ((⟨cap, [(w, dsObserve)]⟩ : Fs).absorb (σ (.n a)) dsObserve).absorb
      (σ (.n (a + 3))) dsObserve =
      ⟨cap, [(w, dsObserve), (σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩ := rfl
  have hin : ([p0, p1, .n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV).map σ =
      rateOf [(w, dsObserve), (σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)] ++ cap := by
    rw [rateOf_three, ← hp, ← s0, ← s2, List.map_append, List.map_append, hz, hc]
    rfl
  have := squeeze_atom (s := ⟨cap, [(w, dsObserve), (σ (.n a), dsObserve),
    (σ (.n (a + 3)), dsObserve)]⟩) h.kc hin (b := o) rfl
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [plainSq, habs]
  exact ⟨this.1, this.2⟩

/-- `plainRun`'s first round, from the facts of its squeeze. -/
theorem plainRun_step {c0 c2 v v' ch : E} {s : Fs} {cap' : List E} {rest : List (E × E)}
    (hch : (plainSq s c0 c2).1 = ch) (hcap : (plainSq s c0 c2).2.cap = cap')
    (hv : c0 + ch * ((v + c2) + ch * c2) = v') :
    plainRun ((c0, c2) :: rest) v s =
      (ch :: (plainRun rest v' ⟨cap', []⟩).1, (plainRun rest v' ⟨cap', []⟩).2) := by
  have e : (plainSq s c0 c2).2 = ⟨cap', []⟩ := by rw [← hcap]; rfl
  simp only [plainRun]
  rw [← plainSq, e, hch, hv]

/-! ## The two specializations -/

theorem word_4096 : word 4096 0 = gen ^ (2 * 6) := by
  rw [show (4096 : ℕ) = 2 ^ (2 * 6) from rfl]; exact word_two_pow (by decide)

theorem word_256 : word 256 0 = gen ^ (2 * 4) := by
  rw [show (256 : ℕ) = 2 ^ (2 * 4) from rfl]; exact word_two_pow (by decide)

/-- The capacity cells from `b`. -/
def capV (b : ℕ) : List V := [.n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4)]

/-- The cells a round's atom reads with nothing waiting: `c₀`'s, `c₂`'s, the zeros, the
capacity from `cb`. -/
def plainIns0 (a : ℕ) (zs : List V) (cb : ℕ) : List V :=
  [.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV cb

/-- The four zero cells of `__L6_L0` (and the constant `1` before them). -/
def plainMid60 : List Stmt :=
  [.atom (.const (.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0")) (word 1 0)), .atom (.const (.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) (word 0 0)),
    .atom (.const (.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) (word 0 0)), .atom (.const (.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) (word 0 0)),
    .atom (.const (.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) (word 0 0))]

/-- `keccak_plain_rounds__L6_L0`'s body. -/
def plain60T : List Stmt :=
  [.atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "sp[0]")) (.n (val% «keccak_plain_rounds__L6_L0» "fs0"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "sp[1]")) (.n (val% «keccak_plain_rounds__L6_L0» "fs1"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "sp[2]")) (.n (val% «keccak_plain_rounds__L6_L0» "fs2"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "sp[3]")) (.n (val% «keccak_plain_rounds__L6_L0» "fs3"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "sp[4]")) (.n (val% «keccak_plain_rounds__L6_L0» "fs4")))] ++
  plainRoundT (.n (val% «keccak_plain_rounds__L6_L0» "cursor")) (.n (val% «keccak_plain_rounds__L6_L0» "point")) (.n (val% «keccak_plain_rounds__L6_L0» "value@1")) (plainIns0 16 [.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 11) plainMid60 0 16 27 ++
  plainRoundT (.n (val% «keccak_plain_rounds__L6_L0» "cursor")) (.n (val% «keccak_plain_rounds__L6_L0» "point")) (.n (val% «keccak_plain_rounds__L6_L0» "value@2")) (plainIns0 45 [.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 35) [] 1 45 51 ++
  plainRoundT (.n (val% «keccak_plain_rounds__L6_L0» "cursor")) (.n (val% «keccak_plain_rounds__L6_L0» "point")) (.n (val% «keccak_plain_rounds__L6_L0» "value@3")) (plainIns0 69 [.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 59) [] 2 69 75 ++
  plainRoundT (.n (val% «keccak_plain_rounds__L6_L0» "cursor")) (.n (val% «keccak_plain_rounds__L6_L0» "point")) (.n (val% «keccak_plain_rounds__L6_L0» "value@4")) (plainIns0 93 [.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 83) [] 3 93 99 ++
  plainRoundT (.n (val% «keccak_plain_rounds__L6_L0» "cursor")) (.n (val% «keccak_plain_rounds__L6_L0» "point")) (.n (val% «keccak_plain_rounds__L6_L0» "value@5")) (plainIns0 117 [.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 107) [] 4 117 123 ++
  plainRoundT (.n (val% «keccak_plain_rounds__L6_L0» "cursor")) (.n (val% «keccak_plain_rounds__L6_L0» "point")) (.n (val% «keccak_plain_rounds__L6_L0» "value@6")) (plainIns0 141 [.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 131) [] 5 141 147 ++
  [.atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "s2#0")) (.n (val% «keccak_plain_rounds__L6_L0» "nxt[8]@6"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "s2#0[1]")) (.n (val% «keccak_plain_rounds__L6_L0» "nxt[9]@6"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "s2#0[2]")) (.n (val% «keccak_plain_rounds__L6_L0» "nxt[10]@6"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "s2#0[3]")) (.n (val% «keccak_plain_rounds__L6_L0» "nxt[11]@6"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "s2#0[4]")) (.n (val% «keccak_plain_rounds__L6_L0» "nxt[12]@6"))),
    .atom (.const (.n (val% «keccak_plain_rounds__L6_L0» "s2#1")) (word 4096 0)), .atom (.mul (.n (val% «keccak_plain_rounds__L6_L0» "s2#2")) (.n (val% «keccak_plain_rounds__L6_L0» "cursor")) (.n (val% «keccak_plain_rounds__L6_L0» "s2#1"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "s2#0[5]")) (.n (val% «keccak_plain_rounds__L6_L0» "s2#2"))), .atom (.copy (.n (val% «keccak_plain_rounds__L6_L0» "s2#0[6]")) (.n (val% «keccak_plain_rounds__L6_L0» "value@7"))),
    .ret [.n (val% «keccak_plain_rounds__L6_L0» "s2#0"), .n (val% «keccak_plain_rounds__L6_L0» "s2#0[1]"), .n (val% «keccak_plain_rounds__L6_L0» "s2#0[2]"), .n (val% «keccak_plain_rounds__L6_L0» "s2#0[3]"), .n (val% «keccak_plain_rounds__L6_L0» "s2#0[4]"), .n (val% «keccak_plain_rounds__L6_L0» "s2#0[5]"), .n (val% «keccak_plain_rounds__L6_L0» "s2#0[6]")]]

theorem body60 : (fn% «keccak_plain_rounds__L6_L0»).body = plain60T :=
  stmtsEqb_sound (by decide +kernel)

/-- The two zero cells of `__L4_L1`'s first round. -/
def plainMid41a : List Stmt :=
  [.atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "rate[6]")) (word 0 0)), .atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "rate[7]")) (word 0 0))]

/-- The four zero cells of `__L4_L1`'s later rounds (and the constant `1` before them). -/
def plainMid41b : List Stmt :=
  [.atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0")) (word 1 0)), .atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) (word 0 0)),
    .atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) (word 0 0)), .atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) (word 0 0)),
    .atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) (word 0 0))]

/-- `keccak_plain_rounds__L4_L1`'s body. -/
def plain41T : List Stmt :=
  [.atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[0]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs0"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[1]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs1"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[2]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs2"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[3]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs3"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "sp[4]")) (.n (val% «keccak_plain_rounds__L4_L1» "fs4"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "rate[0]@1")) (.n (val% «keccak_plain_rounds__L4_L1» "p0"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "rate[1]@1")) (.n (val% «keccak_plain_rounds__L4_L1» "p1")))] ++
  plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@1"))
    ([.n (val% «keccak_plain_rounds__L4_L1» "rate[0]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[1]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[2]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[3]@1"), .n (val% «keccak_plain_rounds__L4_L1» "rate[4]"), .n (val% «keccak_plain_rounds__L4_L1» "rate[5]")] ++ [.n (val% «keccak_plain_rounds__L4_L1» "rate[6]"), .n (val% «keccak_plain_rounds__L4_L1» "rate[7]")] ++ capV 11) plainMid41a 0 18 26 ++
  plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@2")) (plainIns0 44 [.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 34) plainMid41b 1 44 55 ++
  plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@3")) (plainIns0 73 [.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 63) [] 2 73 79 ++
  plainRoundT (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "point")) (.n (val% «keccak_plain_rounds__L4_L1» "value@4")) (plainIns0 97 [.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] 87) [] 3 97 103 ++
  [.atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@4"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[1]")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@4"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[2]")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@4"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[3]")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@4"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[4]")) (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@4"))),
    .atom (.const (.n (val% «keccak_plain_rounds__L4_L1» "s2#1")) (word 256 0)), .atom (.mul (.n (val% «keccak_plain_rounds__L4_L1» "s2#2")) (.n (val% «keccak_plain_rounds__L4_L1» "cursor")) (.n (val% «keccak_plain_rounds__L4_L1» "s2#1"))),
    .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[5]")) (.n (val% «keccak_plain_rounds__L4_L1» "s2#2"))), .atom (.copy (.n (val% «keccak_plain_rounds__L4_L1» "s2#0[6]")) (.n (val% «keccak_plain_rounds__L4_L1» "value@5"))),
    .ret [.n (val% «keccak_plain_rounds__L4_L1» "s2#0"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[4]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[5]"), .n (val% «keccak_plain_rounds__L4_L1» "s2#0[6]")]]

theorem body41 : (fn% «keccak_plain_rounds__L4_L1»).body = plain41T :=
  stmtsEqb_sound (by decide +kernel)

theorem find_plain60 : coreProgram.find? "keccak_plain_rounds__L6_L0" = some
    fn% «keccak_plain_rounds__L6_L0» :=
  coreProgram_find?_at (j := idx% «keccak_plain_rounds__L6_L0») rfl

theorem plain60_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "keccak_plain_rounds__L6_L0" args rets) :
    MeaningPlainRounds 6 0 rd args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_plain60 args rets).mp h
  rw [body60] at hb
  simp only [core_eq% «keccak_plain_rounds__L6_L0», List.map_cons, List.map_nil] at hpar hb
  subst hpar
  simp only [plain60T, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨e11, e12, e13, e14, e15, hb⟩ := hb
  obtain ⟨⟨r0, m0⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r1, m1⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r2, m2⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r3, m3⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r4, m4⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r5, m5⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨e165, e166, e167, e168, e169, e170, e171, e172, e173, hret⟩ := hb
  simp only [plainMid60, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at m0
  obtain ⟨-, m23, m24, m25, m26⟩ := m0
  have hz : [V.n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L6_L0» "s1.u0.s1.t.s0.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, m23, m24, m25, m26, word_zero]
  have q0 := plain_round_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L6_L0» "fs0")), σ (.n (val% «keccak_plain_rounds__L6_L0» "fs1")), σ (.n (val% «keccak_plain_rounds__L6_L0» "fs2")), σ (.n (val% «keccak_plain_rounds__L6_L0» "fs3")), σ (.n (val% «keccak_plain_rounds__L6_L0» "fs4"))]) r0 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd, e11, e12, e13, e14, e15])
  have v0 := r0.v
  simp only [Nat.reduceAdd] at q0 v0
  have q1 := plain_round_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[8]@1")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[9]@1")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[10]@1")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[11]@1")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[12]@1"))]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v1 := r1.v
  simp only [Nat.reduceAdd] at q1 v1
  have q2 := plain_round_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[8]@2")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[9]@2")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[10]@2")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[11]@2")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[12]@2"))]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v2 := r2.v
  simp only [Nat.reduceAdd] at q2 v2
  have q3 := plain_round_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[8]@3")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[9]@3")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[10]@3")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[11]@3")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[12]@3"))]) r3 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v3 := r3.v
  simp only [Nat.reduceAdd] at q3 v3
  have q4 := plain_round_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[8]@4")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[9]@4")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[10]@4")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[11]@4")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[12]@4"))])
    r4 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v4 := r4.v
  simp only [Nat.reduceAdd] at q4 v4
  have q5 := plain_round_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[8]@5")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[9]@5")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[10]@5")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[11]@5")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[12]@5"))])
    r5 hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have v5 := r5.v
  simp only [Nat.reduceAdd] at q5 v5
  have hrun : plainRun [(σ (.n (val% «keccak_plain_rounds__L6_L0» "x@1")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@2"))), (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@3")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@4"))), (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@5")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@6"))),
      (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@7")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@8"))), (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@9")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@10"))), (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@11")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@12")))] (σ (.n (val% «keccak_plain_rounds__L6_L0» "value@1")))
      ⟨[σ (.n (val% «keccak_plain_rounds__L6_L0» "fs0")), σ (.n (val% «keccak_plain_rounds__L6_L0» "fs1")), σ (.n (val% «keccak_plain_rounds__L6_L0» "fs2")), σ (.n (val% «keccak_plain_rounds__L6_L0» "fs3")), σ (.n (val% «keccak_plain_rounds__L6_L0» "fs4"))], []⟩ =
      ([σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[0]@1")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[0]@2")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[0]@3")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[0]@4")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[0]@5")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[0]@6"))], σ (.n (val% «keccak_plain_rounds__L6_L0» "value@7")),
        ⟨[σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[8]@6")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[9]@6")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[10]@6")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[11]@6")), σ (.n (val% «keccak_plain_rounds__L6_L0» "nxt[12]@6"))], []⟩) := by
    rw [plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm,
      plainRun_step q4.1.symm q4.2.symm v4.symm, plainRun_step q5.1.symm q5.2.symm v5.symm]
    rfl
  refine ⟨[(σ (.n (val% «keccak_plain_rounds__L6_L0» "x@1")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@2"))), (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@3")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@4"))),
    (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@5")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@6"))), (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@7")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@8"))), (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@9")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@10"))),
    (σ (.n (val% «keccak_plain_rounds__L6_L0» "x@11")), σ (.n (val% «keccak_plain_rounds__L6_L0» "x@12")))], rfl, ?_, fun w _ => ?_⟩
  · intro k hk
    simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
      List.append_nil, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact r0.ld0
    · exact r0.ld2
    · exact r1.ld0
    · exact r1.ld2
    · exact r2.ld0
    · exact r2.ld2
    · exact r3.ld0
    · exact r3.ld2
    · exact r4.ld0
    · exact r4.ld2
    · exact r5.ld0
    · exact r5.ld2
  · simp only [plainStart, show ¬ (0 : ℕ) = 1 by decide, ↓reduceIte, hrun]
    refine ⟨?_, ?_⟩
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact r0.st
      · exact r1.st
      · exact r2.st
      · exact r3.st
      · exact r4.st
      · exact r5.st
    · rw [← hret]
      simp only [List.map_cons, List.map_nil, e165, e166, e167, e168, e169, e172, e171, e170, e173,
        List.cons_append, List.nil_append, word_4096]

theorem find_plain41 : coreProgram.find? "keccak_plain_rounds__L4_L1" = some
    fn% «keccak_plain_rounds__L4_L1» :=
  coreProgram_find?_at (j := idx% «keccak_plain_rounds__L4_L1») rfl

theorem plain41_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "keccak_plain_rounds__L4_L1" args rets) :
    MeaningPlainRounds 4 1 rd args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_plain41 args rets).mp h
  rw [body41] at hb
  simp only [core_eq% «keccak_plain_rounds__L4_L1», List.map_cons, List.map_nil] at hpar hb
  subst hpar
  simp only [plain41T, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨e11, e12, e13, e14, e15, e16, e17, hb⟩ := hb
  obtain ⟨⟨r0, m0⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r1, m1⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r2, -⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨⟨r3, -⟩, hb⟩ := holds_plainRoundT rfl hb
  obtain ⟨e121, e122, e123, e124, e125, e126, e127, e128, e129, hret⟩ := hb
  simp only [plainMid41a, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at m0
  simp only [plainMid41b, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at m1
  obtain ⟨m24, m25⟩ := m0
  obtain ⟨-, m51, m52, m53, m54⟩ := m1
  have hz0 : [V.n (val% «keccak_plain_rounds__L4_L1» "rate[6]"), .n (val% «keccak_plain_rounds__L4_L1» "rate[7]")].map σ = [0, 0] := by
    simp only [List.map_cons, List.map_nil, m24, m25, word_zero]
  have hz : [V.n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «keccak_plain_rounds__L4_L1» "s1.u1.s1.e.s2.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, m51, m52, m53, m54, word_zero]
  have v0 := r0.v
  have v1 := r1.v
  have v2 := r2.v
  have v3 := r3.v
  simp only [Nat.reduceAdd] at v0 v1 v2 v3
  refine ⟨[(σ (.n (val% «keccak_plain_rounds__L4_L1» "x@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "x@2"))), (σ (.n (val% «keccak_plain_rounds__L4_L1» "x@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "x@4"))),
    (σ (.n (val% «keccak_plain_rounds__L4_L1» "x@5")), σ (.n (val% «keccak_plain_rounds__L4_L1» "x@6"))), (σ (.n (val% «keccak_plain_rounds__L4_L1» "x@7")), σ (.n (val% «keccak_plain_rounds__L4_L1» "x@8")))], rfl, ?_, fun w hw => ?_⟩
  · intro k hk
    simp only [List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
      List.append_nil, List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact r0.ld0
    · exact r0.ld2
    · exact r1.ld0
    · exact r1.ld2
    · exact r2.ld0
    · exact r2.ld2
    · exact r3.ld0
    · exact r3.ld2
  have hp : (σ (.n (val% «keccak_plain_rounds__L4_L1» "rate[0]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "rate[1]@1"))) = Keccak.scalarCells w dsObserve := by
    rw [e16, e17]; exact hw rfl
  have q0 := plain_round_sq1 (cap := [σ (.n (val% «keccak_plain_rounds__L4_L1» "fs0")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs4"))]) r0 hp hz0
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd, e11, e12, e13, e14, e15])
  have q1 := plain_round_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@1"))]) r1 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q2 := plain_round_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@2"))]) r2 hz
    (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  have q3 := plain_round_sq0 (cap := [σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@3"))]) r3
    hz (by simp only [capV, List.map_cons, List.map_nil, Nat.reduceAdd])
  simp only [Nat.reduceAdd] at q0 q1 q2 q3
  have hrun : plainRun [(σ (.n (val% «keccak_plain_rounds__L4_L1» "x@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "x@2"))), (σ (.n (val% «keccak_plain_rounds__L4_L1» "x@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "x@4"))), (σ (.n (val% «keccak_plain_rounds__L4_L1» "x@5")), σ (.n (val% «keccak_plain_rounds__L4_L1» "x@6"))),
      (σ (.n (val% «keccak_plain_rounds__L4_L1» "x@7")), σ (.n (val% «keccak_plain_rounds__L4_L1» "x@8")))] (σ (.n (val% «keccak_plain_rounds__L4_L1» "value@1")))
      ⟨[σ (.n (val% «keccak_plain_rounds__L4_L1» "fs0")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "fs4"))], [(w, dsObserve)]⟩ =
      ([σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@1")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@2")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@3")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[0]@4"))], σ (.n (val% «keccak_plain_rounds__L4_L1» "value@5")),
        ⟨[σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[8]@4")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[9]@4")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[10]@4")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[11]@4")), σ (.n (val% «keccak_plain_rounds__L4_L1» "nxt[12]@4"))], []⟩) := by
    rw [plainRun_step q0.1.symm q0.2.symm v0.symm, plainRun_step q1.1.symm q1.2.symm v1.symm,
      plainRun_step q2.1.symm q2.2.symm v2.symm, plainRun_step q3.1.symm q3.2.symm v3.symm]
    rfl
  simp only [plainStart, ↓reduceIte, hrun]
  refine ⟨?_, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact r0.st
    · exact r1.st
    · exact r2.st
    · exact r3.st
  · rw [← hret]
    simp only [List.map_cons, List.map_nil, e121, e122, e123, e124, e125, e128, e127, e126, e129,
      List.cons_append, List.nil_append, word_256]

/-- **`keccak_plain_rounds`' two specializations compute their meanings.** -/
theorem keccak_plain_rounds_holds : keccak_plain_rounds_Spec := by
  intro k0 hk rd args rets h
  interval_cases k0
  · exact plain60_sound rd args rets h
  · exact plain41_sound rd args rets h

end
end LeanVM.Guest.B1.VerifySub
