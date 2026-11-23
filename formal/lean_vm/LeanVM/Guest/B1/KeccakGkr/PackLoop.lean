/-
  LeanVM.Guest.B1.KeccakGkr.PackLoop

  B1 of the pack rounds' loop helpers (`keccak_layer__L1_loop0` .. `keccak_layer__L0_loop1`, two per
  `keccak_layer` specialization): eight equality-mode rounds an iteration, then one an iteration,
  from one round record to the next.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Plain
public import LeanVM.Guest.B1.KeccakGkr.LayerSpec
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L_loop0»
import LeanVM.Guest.Data.ValNames.«keccak_layer__L_loop1»

/-!
# The pack rounds' loops (`keccak_layer`)

`for xs in mul_range(1, step_g)` in `keccak_layer` is lowered to a helper of parameters
`[xs, step_g, rounds, prev_point, point, tabs]` (`fn% «keccak_layer__L1_loop0»`, `fn%
«keccak_layer__L0_loop0»`: the same body but for the self-call's name, `pack8T`). At `x = g^j` it
reads the record `rounds·x`, the eight coordinates `prev_point[8j ..]` (`prev_point·x⁸`), runs eight
equality-mode rounds (`eqRound`, a round each `packRoundT`), stores their challenges at `point[8j
..]` and writes the record `rounds·x·g` (`Pack8Step`). `for x1 in mul_range(1, rem_g)` (`fn%
«keccak_layer__L1_loop1»`, `fn% «keccak_layer__L0_loop1»`, `packRemT`, parameters `[x1, rem_g,
rounds, prev_point, tabs, point]`) runs one round an iteration on `rounds·g^⌊y/8⌋`,
`prev_point·g^(8⌊y/8⌋)`, `point·g^(8⌊y/8⌋)` (`PackRemStep`). Every grind of these rounds is of `0`
bits: `tabs` is passed along, never read.

`EqChain`: rounds chained by `eqRound`, which `packRunF` runs (`packRunF_of_chain`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Two words absorbed and a squeeze -/

/-- **A squeeze of two read words**: `c₁`'s and `c₂`'s `fs_next` cells (`a + 1`, `a + 2`,
`a + 4`, `a + 5`), four zeros and the capacity in one `KECCAK` atom: the challenge its output
`o` (`challenge_from_state`) and the outputs `o + 8 .. o + 12` are
`(⟨cap, []⟩.absorbAll [c₁, c₂]).squeeze`'s. -/
theorem sq2_atoms {a o : ℕ} {zs capV : List V} {cap : List E}
    (p1 : FsPackOk σ (.n a) (a + 1) dsObserve) (p2 : FsPackOk σ (.n (a + 3)) (a + 3 + 1) dsObserve)
    (hk : (Atom.keccak ([V.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV)
      ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ)
    (hz : zs.map σ = [0, 0, 0, 0])
    (hc : capV.map σ = cap) :
    σ (.n o) = ((⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3))] dsObserve).squeeze.1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        ((⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3))] dsObserve).squeeze.2.cap := by
  have s0 := fsNext_scalar p1
  have s2 := fsNext_scalar p2
  have habs : (⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 3))] dsObserve =
      ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩ := rfl
  have hin : ([V.n (a + 1), .n (a + 2), .n (a + 4), .n (a + 5)] ++ zs ++ capV).map σ =
      rateOf [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)] ++ cap := by
    rw [rateOf_two, ← s0, ← s2, List.map_append, List.map_append, hz, hc]
    rfl
  have := squeeze_atom (s := ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 3)), dsObserve)]⟩) hk hin
    (b := o) rfl
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [habs]
  exact ⟨this.1, this.2⟩

/-! ## Rounds chained -/

/-- The capacity cells from `b`. -/
def cap5 (b : ℕ) : List V := [.n b, .n (b + 1), .n (b + 2), .n (b + 3), .n (b + 4)]

/-- Rounds chained by `eqRound`: from the normalized claim `cl` and capacity `cap`, the coordinates `rs` and messages `ms` give the challenges `chs`, final claim `cl'` and capacity `cap'`. -/
def EqChain : List E → List (E × E) → E → List E → List E → E → List E → Prop
  | [], [], cl, cap, chs, cl', cap' => chs = [] ∧ cl' = cl ∧ cap' = cap
  | r :: rs, (g1, g2) :: ms, cl, cap, chs, cl', cap' =>
      ∃ (ch cl1 : E) (cap1 chs' : List E),
        eqRound ⟨cap, []⟩ g1 g2 r cl = (ch, cl1, ⟨cap1, []⟩) ∧ chs = ch :: chs' ∧
          EqChain rs ms cl1 cap1 chs' cl' cap'
  | _, _, _, _, _, _, _ => False

/-- A round of `packRunF` is `eqRound`. -/
theorem packRunF_cons (r g1 g2 v : E) (rs : List E) (ms : List (E × E)) (s : Fs) :
    packRunF (r :: rs) ((g1, g2) :: ms) v s =
      (((packRunF rs ms (eqRound s g1 g2 r v).2.1 (eqRound s g1 g2 r v).2.2).1.1,
        (eqRound s g1 g2 r v).1 ::
          (packRunF rs ms (eqRound s g1 g2 r v).2.1 (eqRound s g1 g2 r v).2.2).1.2),
        (packRunF rs ms (eqRound s g1 g2 r v).2.1 (eqRound s g1 g2 r v).2.2).2) := by
  have e : polyEval [v + r * sumE [g1, g2], g1, g2]
      (s.absorbAll [g1, g2] dsObserve).squeeze.1 = (eqRound s g1 g2 r v).2.1 := by
    simp only [eqRound, polyEval, sumE, List.foldl, List.foldr]
    ring
  simp only [packRunF]
  rw [e]
  rfl

/-- `packRunF` runs a chain. -/
theorem packRunF_of_chain : ∀ (rs : List E) (ms : List (E × E)) (cl : E) (cap chs : List E)
    (cl' : E) (cap' : List E), EqChain rs ms cl cap chs cl' cap' →
    packRunF rs ms cl ⟨cap, []⟩ = ((cl', chs), ⟨cap', []⟩)
  | [], [], _, _, _, _, _, h => by
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | r :: rs, (g1, g2) :: ms, cl, cap, chs, cl', cap', h => by
    obtain ⟨ch, cl1, cap1, chs', he, rfl, hc⟩ := h
    rw [packRunF_cons, he]
    simp only
    rw [packRunF_of_chain rs ms cl1 cap1 chs' cl' cap' hc]
  | [], _ :: _, _, _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, _, _, h => h.elim

theorem packEqChain_length : ∀ {rs : List E} {ms : List (E × E)} {cl : E} {cap chs : List E}
    {cl' : E} {cap' : List E}, EqChain rs ms cl cap chs cl' cap' →
    ms.length = rs.length ∧ chs.length = rs.length
  | [], [], _, _, _, _, _, h => by obtain ⟨rfl, -⟩ := h; simp
  | _ :: _, (_, _) :: _, _, _, _, _, _, h => by
    obtain ⟨_, _, _, _, -, rfl, hc⟩ := h
    have := packEqChain_length hc
    simp [this.1, this.2]
  | [], _ :: _, _, _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, _, _, h => h.elim

/-! ## A round of the eight-round loop -/

/-- Round `q` reads its coordinate and two coefficients, squeezes the challenge and stores the next normalized claim. -/
def packRoundT (pp cu pt : V) (q b c : ℕ) (pre : List Stmt) (zs cap : List V) (cl : V) :
    List Stmt :=
  [.atom (.load (.n b) pp q)] ++ fsNextT cu (2 * q) (b + 1) ++ fsNextT cu (2 * q + 1) (b + 4) ++
    pre ++
  [keccakA ([.n (b + 2), .n (b + 3), .n (b + 5), .n (b + 6)] ++ zs ++ cap)
    ((List.range 13).map fun k ↦ .n (c + k))] ++
  [.atom (.load (.n c) pt q), .atom (.add (.n (c + 13)) (.n b) (.n c)),
    .atom (.mul (.n (c + 14)) (.n (c + 13)) (.n (b + 1))),
    .atom (.add (.n (c + 15)) cl (.n (c + 14))),
    .atom (.mul (.n (c + 16)) (.n c) (.n c)),
    .atom (.add (.n (c + 17)) (.n b) (.n (c + 16))),
    .atom (.mul (.n (c + 18)) (.n (c + 17)) (.n (b + 4))),
    .atom (.add (.n (c + 19)) (.n (c + 15)) (.n (c + 18)))]

theorem fsNextT_atoms (cu : V) (off b : ℕ) : AllAtoms (fsNextT cu off b) := by
  intro s hs
  simp only [fsNextT, fsPackT, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem challengeT_atoms (s0 : V) (b : ℕ) : AllAtoms (challengeT s0 b) := by
  intro s hs
  simp only [challengeT, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl
  exact ⟨_, rfl⟩

theorem fsNextT_facts {cu : V} {off b : ℕ} (H : ∀ a, Stmt.atom a ∈ fsNextT cu off b → a.Holds rd σ) :
    LoadHolds rd (σ cu) off (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve :=
  ((holds_fsNextT (C := fun _ _ _ ↦ True) cu off b True (fun _ ↦ False)).1
    ((holdsList_atoms (fsNextT_atoms cu off b) True _).2 ⟨H, trivial⟩)).1

theorem challengeT_facts {s0 : V} {b : ℕ}
    (H : ∀ a, Stmt.atom a ∈ challengeT s0 b → a.Holds rd σ) : ChallengeOk σ s0 b :=
  ((holds_challengeT (C := fun _ _ _ ↦ True) s0 b True (fun _ ↦ False)).1
    ((holdsList_atoms (challengeT_atoms s0 b) True _).2 ⟨H, trivial⟩)).1

/-- **A round's facts**: the coordinate and the two words read, and `eqRound` of them on the
capacity: the challenge (stored at `pt[q]`), the normalized claim and the capacity after. -/
theorem packRound_facts {pp cu pt : V} {q b c : ℕ} {pre : List Stmt} {zs cap : List V} {cl : V}
    (H : ∀ a, Stmt.atom a ∈ packRoundT pp cu pt q b c pre zs cap cl → a.Holds rd σ)
    (hz : zs.map σ = [0, 0, 0, 0]) :
    LoadHolds rd (σ pp) q (σ (.n b)) ∧ LoadHolds rd (σ cu) (2 * q) (σ (.n (b + 1))) ∧
      LoadHolds rd (σ cu) (2 * q + 1) (σ (.n (b + 4))) ∧ LoadHolds rd (σ pt) q (σ (.n c)) ∧
      eqRound ⟨cap.map σ, []⟩ (σ (.n (b + 1))) (σ (.n (b + 4))) (σ (.n b)) (σ cl) =
        (σ (.n c), σ (.n (c + 19)), ⟨(cap5 (c + 8)).map σ, []⟩) := by
  have m1 : ∀ a, Stmt.atom a ∈ fsNextT cu (2 * q) (b + 1) → a.Holds rd σ := fun a ha ↦
    H a (by simp only [packRoundT, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ha)))))
  have m2 : ∀ a, Stmt.atom a ∈ fsNextT cu (2 * q + 1) (b + 4) → a.Holds rd σ := fun a ha ↦
    H a (by simp only [packRoundT, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr ha))))
  have hk : (Atom.keccak ([V.n (b + 2), .n (b + 3), .n (b + 5), .n (b + 6)] ++ zs ++ cap)
      ((List.range 13).map fun k ↦ .n (c + k)) false false).Holds rd σ :=
    H _ (by simp [packRoundT, keccakA])
  have l0 : LoadHolds rd (σ pp) q (σ (.n b)) := H (.load (.n b) pp q) (by simp [packRoundT])
  obtain ⟨l1, p1⟩ := fsNextT_facts m1
  obtain ⟨l2, p2⟩ := fsNextT_facts m2
  have q0 := sq2_atoms (a := b + 1) (o := c) (zs := zs) (capV := cap) (cap := cap.map σ) p1 p2
    (by simpa [Nat.add_assoc] using hk) hz rfl
  have l3 : LoadHolds rd (σ pt) q (σ (.n c)) := H (.load (.n c) pt q) (by simp [packRoundT])
  have e14 : σ (.n (c + 13)) = σ (.n b) + σ (.n c) := H (.add (.n (c + 13)) (.n b) (.n c)) (by simp [packRoundT])
  have e17 : σ (.n (c + 14)) = σ (.n (c + 13)) * σ (.n (b + 1)) := H (.mul (.n (c + 14)) (.n (c + 13)) (.n (b + 1))) (by simp [packRoundT])
  have e18 : σ (.n (c + 15)) = σ cl + σ (.n (c + 14)) := H (.add (.n (c + 15)) cl (.n (c + 14))) (by simp [packRoundT])
  have e19 : σ (.n (c + 16)) = σ (.n c) * σ (.n c) := H (.mul (.n (c + 16)) (.n c) (.n c)) (by simp [packRoundT])
  have e20 : σ (.n (c + 17)) = σ (.n b) + σ (.n (c + 16)) := H (.add (.n (c + 17)) (.n b) (.n (c + 16))) (by simp [packRoundT])
  have e21 : σ (.n (c + 18)) = σ (.n (c + 17)) * σ (.n (b + 4)) := H (.mul (.n (c + 18)) (.n (c + 17)) (.n (b + 4))) (by simp [packRoundT])
  have e22 : σ (.n (c + 19)) = σ (.n (c + 15)) + σ (.n (c + 18)) := H (.add (.n (c + 19)) (.n (c + 15)) (.n (c + 18))) (by simp [packRoundT])
  have hsq : ((⟨cap.map σ, []⟩ : Fs).absorbAll [σ (.n (b + 1)), σ (.n (b + 4))] dsObserve).squeeze =
      (σ (.n c), ⟨(cap5 (c + 8)).map σ, []⟩) := by
    refine Prod.ext q0.1.symm ?_
    have h2 := q0.2
    simp only [cap5, List.map_cons, List.map_nil, Nat.add_assoc, Nat.reduceAdd] at h2 ⊢
    rw [h2]
    rfl
  refine ⟨l0, l1, l2, l3, ?_⟩
  simp only [eqRound]
  rw [hsq]
  simp only [Prod.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  rw [e22, e21, e20, e19, e18, e17, e14]

/-! ## The eight-round loop -/

/-- Round `q`'s permutation outputs. -/
def pkC (q : ℕ) : ℕ := 34 + 27 * q

/-- Round `q`'s first value. -/
def pkB (q : ℕ) : ℕ := if q = 0 then 22 else 27 + 27 * q

/-- The capacity cells round `q` reads. -/
def pkCap (q : ℕ) : List V := if q = 0 then cap5 15 else cap5 (pkC (q - 1) + 8)

/-- The claim round `q` reads. -/
def pkCl (q : ℕ) : ℕ := if q = 0 then 21 else pkC (q - 1) + 19

/-- The zero cells (and a one) round `0` sets. -/
def pkPre (q : ℕ) : List Stmt :=
  if q = 0 then
    [.atom (.const (.n (valf% «keccak_layer» «_loop0» "s6.u0.s4.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0")) (word 1 0)), .atom (.const (.n (valf% «keccak_layer» «_loop0» "s6.u0.s4.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) (word 0 0)),
      .atom (.const (.n (valf% «keccak_layer» «_loop0» "s6.u0.s4.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) (word 0 0)), .atom (.const (.n (valf% «keccak_layer» «_loop0» "s6.u0.s4.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) (word 0 0)),
      .atom (.const (.n (valf% «keccak_layer» «_loop0» "s6.u0.s4.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) (word 0 0))]
  else []

/-- The zero cells. -/
def pkZs : List V := [.n (valf% «keccak_layer» «_loop0» "s6.u0.s4.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (valf% «keccak_layer» «_loop0» "s6.u0.s4.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (valf% «keccak_layer» «_loop0» "s6.u0.s4.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (valf% «keccak_layer» «_loop0» "s6.u0.s4.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")]

/-- Round `q` of the eight-round loop. -/
def pkRound (q : ℕ) : List Stmt :=
  packRoundT (.n (valf% «keccak_layer» «_loop0» "pp")) (.n (valf% «keccak_layer» «_loop0» "cur_i")) (.n (valf% «keccak_layer» «_loop0» "pt")) q (pkB q) (pkC q) (pkPre q) pkZs (pkCap q) (.n (pkCl q))

/-- The loop body's head: `rd = rounds·x`, `pp = prev_point·x⁸`, `pt = point·x⁸`, the record read. -/
def pk8Head : List Stmt :=
  [.atom (.mul (.n (valf% «keccak_layer» «_loop0» "rd")) (.n (valf% «keccak_layer» «_loop0» "rounds")) (.n (valf% «keccak_layer» «_loop0» "xs"))), .atom (.mul (.n (valf% «keccak_layer» «_loop0» "pp~0")) (.n (valf% «keccak_layer» «_loop0» "xs")) (.n (valf% «keccak_layer» «_loop0» "xs"))),
    .atom (.mul (.n (valf% «keccak_layer» «_loop0» "pp~1")) (.n (valf% «keccak_layer» «_loop0» "pp~0")) (.n (valf% «keccak_layer» «_loop0» "pp~0"))), .atom (.mul (.n (valf% «keccak_layer» «_loop0» "pp~2")) (.n (valf% «keccak_layer» «_loop0» "pp~1")) (.n (valf% «keccak_layer» «_loop0» "pp~1"))),
    .atom (.mul (.n (valf% «keccak_layer» «_loop0» "pp")) (.n (valf% «keccak_layer» «_loop0» "prev_point")) (.n (valf% «keccak_layer» «_loop0» "pp~2"))), .atom (.mul (.n (valf% «keccak_layer» «_loop0» "pt~0")) (.n (valf% «keccak_layer» «_loop0» "xs")) (.n (valf% «keccak_layer» «_loop0» "xs"))),
    .atom (.mul (.n (valf% «keccak_layer» «_loop0» "pt~1")) (.n (valf% «keccak_layer» «_loop0» "pt~0")) (.n (valf% «keccak_layer» «_loop0» "pt~0"))), .atom (.mul (.n (valf% «keccak_layer» «_loop0» "pt~2")) (.n (valf% «keccak_layer» «_loop0» "pt~1")) (.n (valf% «keccak_layer» «_loop0» "pt~1"))),
    .atom (.mul (.n (valf% «keccak_layer» «_loop0» "pt")) (.n (valf% «keccak_layer» «_loop0» "point")) (.n (valf% «keccak_layer» «_loop0» "pt~2"))),
    .atom (.load (.n (valf% «keccak_layer» «_loop0» "sp[0]")) (.n (valf% «keccak_layer» «_loop0» "rd")) 0), .atom (.load (.n (valf% «keccak_layer» «_loop0» "sp[1]")) (.n (valf% «keccak_layer» «_loop0» "rd")) 11), .atom (.load (.n (valf% «keccak_layer» «_loop0» "sp[2]")) (.n (valf% «keccak_layer» «_loop0» "rd")) 22),
    .atom (.load (.n (valf% «keccak_layer» «_loop0» "sp[3]")) (.n (valf% «keccak_layer» «_loop0» "rd")) 33), .atom (.load (.n (valf% «keccak_layer» «_loop0» "sp[4]")) (.n (valf% «keccak_layer» «_loop0» "rd")) 44), .atom (.load (.n (valf% «keccak_layer» «_loop0» "cur_i")) (.n (valf% «keccak_layer» «_loop0» "rd")) 55),
    .atom (.load (.n (valf% «keccak_layer» «_loop0» "run@1")) (.n (valf% «keccak_layer» «_loop0» "rd")) 66)]

/-- The eight rounds. -/
def pk8Rounds : List Stmt := ((List.range 8).map pkRound).flatten

/-- The next record written, the counter's step. -/
def pk8Tail : List Stmt :=
  [.atom (.load (.n (valf% «keccak_layer» «_loop0» "nxt[8]@8")) (.n (valf% «keccak_layer» «_loop0» "rd")) 1), .atom (.load (.n (valf% «keccak_layer» «_loop0» "nxt[9]@8")) (.n (valf% «keccak_layer» «_loop0» "rd")) 12),
    .atom (.load (.n (valf% «keccak_layer» «_loop0» "nxt[10]@8")) (.n (valf% «keccak_layer» «_loop0» "rd")) 23), .atom (.load (.n (valf% «keccak_layer» «_loop0» "nxt[11]@8")) (.n (valf% «keccak_layer» «_loop0» "rd")) 34),
    .atom (.load (.n (valf% «keccak_layer» «_loop0» "nxt[12]@8")) (.n (valf% «keccak_layer» «_loop0» "rd")) 45),
    .atom (.const (.n (valf% «keccak_layer» «_loop0» "s9#0")) (word 65536 0)), .atom (.mul (.n (valf% «keccak_layer» «_loop0» "s9#1")) (.n (valf% «keccak_layer» «_loop0» "cur_i")) (.n (valf% «keccak_layer» «_loop0» "s9#0"))),
    .atom (.load (.n (valf% «keccak_layer» «_loop0» "s9#1")) (.n (valf% «keccak_layer» «_loop0» "rd")) 56), .atom (.load (.n (valf% «keccak_layer» «_loop0» "run@9")) (.n (valf% «keccak_layer» «_loop0» "rd")) 67),
    .atom (.const (.n (valf% «keccak_layer» «_loop0» "s12#0")) (word 2 0)), .atom (.mul (.n (valf% «keccak_layer» «_loop0» "s12#1")) (.n (valf% «keccak_layer» «_loop0» "xs")) (.n (valf% «keccak_layer» «_loop0» "s12#0"))),
    .atom (.add (.n (valf% «keccak_layer» «_loop0» "s12#2")) (.n (valf% «keccak_layer» «_loop0» "s12#1")) (.n (valf% «keccak_layer» «_loop0» "bound"))), .atom (.const (.n (valf% «keccak_layer» «_loop0» "s12#3")) (word 2 0)),
    .atom (.mul (.n (valf% «keccak_layer» «_loop0» "s12#4")) (.n (valf% «keccak_layer» «_loop0» "xs")) (.n (valf% «keccak_layer» «_loop0» "s12#3")))]

/-- The loop body's atoms. -/
def pack8Pre : List Stmt := pk8Head ++ pk8Rounds ++ pk8Tail

theorem pack8Pre_atoms : pack8Pre.all isAtom = true := by decide +kernel

/-- The loop body, the self-call named `name`. -/
def pack8T (name : String) : List Stmt :=
  pack8Pre ++ [.callIf (.n (valf% «keccak_layer» «_loop0» "s12#2")) name [.n (valf% «keccak_layer» «_loop0» "s12#4"), .n (valf% «keccak_layer» «_loop0» "bound"), .n (valf% «keccak_layer» «_loop0» "rounds"), .n (valf% «keccak_layer» «_loop0» "prev_point"), .n (valf% «keccak_layer» «_loop0» "point"), .n (valf% «keccak_layer» «_loop0» "tabs")], .ret []]

/-- The remainder loop's atoms: one round on the record `rounds·x`. -/
def packRemPre : List Stmt :=
  [.atom (.mul (.n (valf% «keccak_layer» «_loop1» "rd")) (.n (valf% «keccak_layer» «_loop1» "rem_rounds")) (.n (valf% «keccak_layer» «_loop1» "x1"))),
    .atom (.mul (.n (valf% «keccak_layer» «_loop1» "r_eq~0")) (.n (valf% «keccak_layer» «_loop1» "rem_prev")) (.n (valf% «keccak_layer» «_loop1» "x1"))),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "r_eq")) (.n (valf% «keccak_layer» «_loop1» "r_eq~0")) 0),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "sp[0]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 0),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "sp[1]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 11),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "sp[2]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 22),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "sp[3]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 33),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "sp[4]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 44),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "cur_i")) (.n (valf% «keccak_layer» «_loop1» "rd")) 55),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "x@1")) (.n (valf% «keccak_layer» «_loop1» "cur_i")) 0),
    .atom (.copy (.n (valf% «keccak_layer» «_loop1» "rate[0]")) (.n (valf% «keccak_layer» «_loop1» "x@1"))),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "rate[1]")) (word 0 1)),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "x@2")) (.n (valf% «keccak_layer» «_loop1» "cur_i")) 1),
    .atom (.copy (.n (valf% «keccak_layer» «_loop1» "rate[2]")) (.n (valf% «keccak_layer» «_loop1» "x@2"))),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "rate[3]")) (word 0 1)),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0")) (word 1 0)),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) (word 0 0)),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) (word 0 0)),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) (word 0 0)),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) (word 0 0)),
    .atom (.keccak [.n (valf% «keccak_layer» «_loop1» "rate[0]"), .n (valf% «keccak_layer» «_loop1» "rate[1]"), .n (valf% «keccak_layer» «_loop1» "rate[2]"), .n (valf% «keccak_layer» «_loop1» "rate[3]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]"), .n (valf% «keccak_layer» «_loop1» "sp[0]"), .n (valf% «keccak_layer» «_loop1» "sp[1]"), .n (valf% «keccak_layer» «_loop1» "sp[2]"), .n (valf% «keccak_layer» «_loop1» "sp[3]"), .n (valf% «keccak_layer» «_loop1» "sp[4]")] [.n (valf% «keccak_layer» «_loop1» "nxt[0]"), .n (valf% «keccak_layer» «_loop1» "nxt[1]"), .n (valf% «keccak_layer» «_loop1» "nxt[2]"), .n (valf% «keccak_layer» «_loop1» "nxt[3]"), .n (valf% «keccak_layer» «_loop1» "nxt[4]"), .n (valf% «keccak_layer» «_loop1» "nxt[5]"), .n (valf% «keccak_layer» «_loop1» "nxt[6]"), .n (valf% «keccak_layer» «_loop1» "nxt[7]"), .n (valf% «keccak_layer» «_loop1» "nxt[8]"), .n (valf% «keccak_layer» «_loop1» "nxt[9]"), .n (valf% «keccak_layer» «_loop1» "nxt[10]"), .n (valf% «keccak_layer» «_loop1» "nxt[11]"), .n (valf% «keccak_layer» «_loop1» "nxt[12]")] false false),
    .atom (.mul (.n (valf% «keccak_layer» «_loop1» "s8#0")) (.n (valf% «keccak_layer» «_loop1» "rem_point")) (.n (valf% «keccak_layer» «_loop1» "x1"))),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "nxt[0]")) (.n (valf% «keccak_layer» «_loop1» "s8#0")) 0),
    .atom (.add (.n (valf% «keccak_layer» «_loop1» "gap")) (.n (valf% «keccak_layer» «_loop1» "r_eq")) (.n (valf% «keccak_layer» «_loop1» "nxt[0]"))),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "nxt[8]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 1),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "nxt[9]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 12),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "nxt[10]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 23),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "nxt[11]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 34),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "nxt[12]")) (.n (valf% «keccak_layer» «_loop1» "rd")) 45),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "s12#0")) (word 4 0)),
    .atom (.mul (.n (valf% «keccak_layer» «_loop1» "s12#1")) (.n (valf% «keccak_layer» «_loop1» "cur_i")) (.n (valf% «keccak_layer» «_loop1» "s12#0"))),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "s12#1")) (.n (valf% «keccak_layer» «_loop1» "rd")) 56),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "s13#0")) (.n (valf% «keccak_layer» «_loop1» "rd")) 66),
    .atom (.mul (.n (valf% «keccak_layer» «_loop1» "s13#1")) (.n (valf% «keccak_layer» «_loop1» "gap")) (.n (valf% «keccak_layer» «_loop1» "x@1"))),
    .atom (.add (.n (valf% «keccak_layer» «_loop1» "s13#2")) (.n (valf% «keccak_layer» «_loop1» "s13#0")) (.n (valf% «keccak_layer» «_loop1» "s13#1"))),
    .atom (.mul (.n (valf% «keccak_layer» «_loop1» "s13#3")) (.n (valf% «keccak_layer» «_loop1» "nxt[0]")) (.n (valf% «keccak_layer» «_loop1» "nxt[0]"))),
    .atom (.add (.n (valf% «keccak_layer» «_loop1» "s13#4")) (.n (valf% «keccak_layer» «_loop1» "r_eq")) (.n (valf% «keccak_layer» «_loop1» "s13#3"))),
    .atom (.mul (.n (valf% «keccak_layer» «_loop1» "s13#5")) (.n (valf% «keccak_layer» «_loop1» "s13#4")) (.n (valf% «keccak_layer» «_loop1» "x@2"))),
    .atom (.add (.n (valf% «keccak_layer» «_loop1» "s13#6")) (.n (valf% «keccak_layer» «_loop1» "s13#2")) (.n (valf% «keccak_layer» «_loop1» "s13#5"))),
    .atom (.load (.n (valf% «keccak_layer» «_loop1» "s13#6")) (.n (valf% «keccak_layer» «_loop1» "rd")) 67),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "s15#0")) (word 2 0)),
    .atom (.mul (.n (valf% «keccak_layer» «_loop1» "s15#1")) (.n (valf% «keccak_layer» «_loop1» "x1")) (.n (valf% «keccak_layer» «_loop1» "s15#0"))),
    .atom (.add (.n (valf% «keccak_layer» «_loop1» "s15#2")) (.n (valf% «keccak_layer» «_loop1» "s15#1")) (.n (valf% «keccak_layer» «_loop1» "bound"))),
    .atom (.const (.n (valf% «keccak_layer» «_loop1» "s15#3")) (word 2 0)),
    .atom (.mul (.n (valf% «keccak_layer» «_loop1» "s15#4")) (.n (valf% «keccak_layer» «_loop1» "x1")) (.n (valf% «keccak_layer» «_loop1» "s15#3")))]

theorem packRemPre_atoms : packRemPre.all isAtom = true := by decide +kernel

/-- The remainder loop's body, the self-call named `name`. -/
def packRemT (name : String) : List Stmt :=
  packRemPre ++ [.callIf (.n (valf% «keccak_layer» «_loop1» "s15#2")) name [.n (valf% «keccak_layer» «_loop1» "s15#4"), .n (valf% «keccak_layer» «_loop1» "bound"), .n (valf% «keccak_layer» «_loop1» "rem_rounds"), .n (valf% «keccak_layer» «_loop1» "rem_prev"), .n (valf% «keccak_layer» «_loop1» "tabs"), .n (valf% «keccak_layer» «_loop1» "rem_point")], .ret []]

/-- The two helpers' names, by `keccak_layer` specialization: the eight-round loop. -/
def packLoopName : ℕ → String
  | 1 => name% «keccak_layer__L1_loop0»
  | _ => name% «keccak_layer__L0_loop0»

/-- The remainder loop. -/
def remLoopName : ℕ → String
  | 1 => name% «keccak_layer__L1_loop1»
  | _ => name% «keccak_layer__L0_loop1»

theorem pack8_body456 : (fn% «keccak_layer__L1_loop0»).body = pack8T name% «keccak_layer__L1_loop0»
    := stmtsEqb_sound (by decide +kernel)
theorem pack8_body458 : (fn% «keccak_layer__L0_loop0»).body = pack8T name% «keccak_layer__L0_loop0»
    := stmtsEqb_sound (by decide +kernel)
theorem packRem_body457 : (fn% «keccak_layer__L1_loop1»).body = packRemT
    name% «keccak_layer__L1_loop1» :=
  stmtsEqb_sound (by decide +kernel)
theorem packRem_body459 : (fn% «keccak_layer__L0_loop1»).body = packRemT
    name% «keccak_layer__L0_loop1» :=
  stmtsEqb_sound (by decide +kernel)

theorem find_pack8_456 : coreProgram.find? name% «keccak_layer__L1_loop0» = some
    fn% «keccak_layer__L1_loop0» :=
  coreProgram_find?_at (j := idx% «keccak_layer__L1_loop0») rfl
theorem find_packRem_457 : coreProgram.find? name% «keccak_layer__L1_loop1» = some
    fn% «keccak_layer__L1_loop1» :=
  coreProgram_find?_at (j := idx% «keccak_layer__L1_loop1») rfl
theorem find_pack8_458 : coreProgram.find? name% «keccak_layer__L0_loop0» = some
    fn% «keccak_layer__L0_loop0» :=
  coreProgram_find?_at (j := idx% «keccak_layer__L0_loop0») rfl
theorem find_packRem_459 : coreProgram.find? name% «keccak_layer__L0_loop1» = some
    fn% «keccak_layer__L0_loop1» :=
  coreProgram_find?_at (j := idx% «keccak_layer__L0_loop1») rfl

/-- The loops' parameters: `[x, bound, rounds, prev_point, point, tabs]` for the eight-round
loop, `[x, bound, rounds, prev_point, tabs, point]` for the remainder loop. -/
def loopParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]

theorem find_pack8 {first : ℕ} (hf : first < 2) :
    ∃ fn, coreProgram.find? (packLoopName first) = some fn ∧ fn.body = pack8T (packLoopName first) ∧
      fn.params = loopParams := by
  interval_cases first
  · exact ⟨_, find_pack8_458, pack8_body458, rfl⟩
  · exact ⟨_, find_pack8_456, pack8_body456, rfl⟩

theorem find_packRem {first : ℕ} (hf : first < 2) :
    ∃ fn, coreProgram.find? (remLoopName first) = some fn ∧ fn.body = packRemT (remLoopName first) ∧
      fn.params = loopParams := by
  interval_cases first
  · exact ⟨_, find_packRem_459, packRem_body459, rfl⟩
  · exact ⟨_, find_packRem_457, packRem_body457, rfl⟩

/-! ## The steps -/

/-- An iteration of the eight-round loop at `x`: the record `rounds·x` holds a capacity, cursor and normalized claim. The eight coordinates and sixteen message words run eight rounds, storing their challenges and the next record. -/
def Pack8Step (rd : Reader) (rec pp pt x : E) : Prop :=
  ∃ (cap : List E) (cur claim : E) (rs : List E) (ms : List (E × E)) (chs : List E)
    (claim' : E) (cap' : List E),
    RoundRec rd (rec * x) 0 cap cur claim ∧ rs.length = 8 ∧ ReadsAt rd (pp * x ^ 8) rs ∧
      ReadsAt rd cur (ms.flatMap fun m ↦ [m.1, m.2]) ∧
      EqChain rs ms claim cap chs claim' cap' ∧ ReadsAt rd (pt * x ^ 8) chs ∧
      RoundRec rd (rec * x) 1 cap' (cur * gen ^ 16) claim'

/-- An iteration of the remainder loop at `x`: one round, on the coordinate at `prev_point·x`, its challenge at `point·x`. -/
def PackRemStep (rd : Reader) (rec pp pt x : E) : Prop :=
  ∃ (cap : List E) (cur claim r g1 g2 : E),
    RoundRec rd (rec * x) 0 cap cur claim ∧ LoadHolds rd (pp * x) 0 r ∧
      ReadsAt rd cur [g1, g2] ∧
      let o := eqRound ⟨cap, []⟩ g1 g2 r claim
      LoadHolds rd (pt * x) 0 o.1 ∧ RoundRec rd (rec * x) 1 o.2.2.cap (cur * gen ^ 2) o.2.1

theorem word_16 : word 16 0 = gen ^ 4 := by
  rw [show (16 : ℕ) = 2 ^ 4 from rfl]; exact word_two_pow (by decide)

/-! ## Chains over a range -/

/-- **A chain over a range of rounds**: rounds `k .. k + n` chained by `eqRound`. -/
theorem eqChain_range (R G1 G2 CH CL : ℕ → E) (CAP : ℕ → List E) :
    ∀ n k, (∀ q < n, eqRound ⟨CAP (k + q), []⟩ (G1 (k + q)) (G2 (k + q)) (R (k + q)) (CL (k + q))
      = (CH (k + q), CL (k + q + 1), ⟨CAP (k + q + 1), []⟩)) →
    EqChain ((List.range' k n).map R) ((List.range' k n).map fun q ↦ (G1 q, G2 q)) (CL k)
      (CAP k) ((List.range' k n).map CH) (CL (k + n)) (CAP (k + n))
  | 0, k, _ => by simp [EqChain]
  | n + 1, k, h => by
    simp only [List.range'_succ, List.map_cons]
    refine ⟨CH k, CL (k + 1), CAP (k + 1), _, by simpa using h 0 (by omega), rfl, ?_⟩
    have := eqChain_range R G1 G2 CH CL CAP n (k + 1) fun q hq ↦ by
      have := h (q + 1) (by omega)
      rwa [show k + (q + 1) = k + 1 + q by omega] at this
    rwa [show k + 1 + n = k + (n + 1) by omega] at this

/-- Pairs read in order from `p`. -/
theorem readsAt_pairs {p : E} : ∀ (ms : List (E × E)) (o : ℕ),
    (∀ q < ms.length, LoadHolds rd p (o + 2 * q) (ms.getD q (0, 0)).1 ∧
      LoadHolds rd p (o + 2 * q + 1) (ms.getD q (0, 0)).2) →
    ReadsAt rd (p * gen ^ o) (ms.flatMap fun m ↦ [m.1, m.2])
  | [], _, _ => readsAt_nil _ _
  | (g1, g2) :: ms, o, h => by
    have ih := readsAt_pairs ms (o + 2) fun q hq ↦ by
      have := h (q + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at this
      rw [show o + 2 + 2 * q = o + 2 * (q + 1) by ring]
      exact this
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero] at h0
    rw [List.flatMap_cons, show [(g1, g2).1, (g1, g2).2] = [g1, g2] from rfl, List.cons_append,
      List.cons_append, List.nil_append]
    intro k hk
    rcases k with _ | _ | k
    · simpa [loadHolds_mul_gen_pow] using h0.1
    · simpa [loadHolds_mul_gen_pow] using h0.2
    · have := ih k (by simpa using hk)
      rw [loadHolds_mul_gen_pow] at this ⊢
      simpa [show o + 2 + k = o + (k + 2) by ring] using this

theorem gen_pow_eight_of (x a b c : E) (ha : a = x * x) (hb : b = a * a) (hc : c = b * b) :
    c = x ^ 8 := by
  subst ha hb hc; ring

/-! ## The eight-round step -/

theorem pk8_mem_round {q : ℕ} (hq : q < 8) {a : Atom} (ha : Stmt.atom a ∈ pkRound q) :
    Stmt.atom a ∈ pack8Pre :=
  List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatten.2 ⟨pkRound q, List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩, ha⟩))

set_option maxRecDepth 20000 in
/-- **The eight-round loop's step**: at depth `d + 1` and `x`, an iteration's meaning, and the
call at `x·g` one level shallower unless `x·g = step_g`. -/
theorem pack8_step {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = pack8T name) (hp : fn.params = loopParams) (d : ℕ)
    (x hg rec pp pt tb : E) (h : coreProgram.relN rd (d + 1) name [x, hg, rec, pp, pt, tb] []) :
    Pack8Step rd rec pp pt x ∧
      (x * gen + hg ≠ 0 → coreProgram.relN rd d name [x * gen, hg, rec, pp, pt, tb] []) := by
  obtain ⟨fn', hf', σ, hpar, hbody⟩ := h
  rw [hf] at hf'
  cases hf'
  rw [hp] at hpar
  simp only [loopParams, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, pack8T, holdsList_append] at hbody
  obtain ⟨H, hc⟩ := (holdsList_atoms (allAtoms_of_all pack8Pre_atoms) _ _).1 hbody
  simp only [Stmt.HoldsList, Stmt.Holds] at hc
  obtain ⟨-, hcall, -⟩ := hc
  have HH : ∀ a, Stmt.atom a ∈ pk8Head → a.Holds rd σ := fun a ha ↦
    H a (List.mem_append_left _ (List.mem_append_left _ ha))
  have HT : ∀ a, Stmt.atom a ∈ pk8Tail → a.Holds rd σ := fun a ha ↦
    H a (List.mem_append_right _ ha)
  have HR : ∀ q < 8, ∀ a, Stmt.atom a ∈ pkRound q → a.Holds rd σ := fun q hq a ha ↦
    H a (pk8_mem_round hq ha)
  simp only [pk8Head, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Atom.Holds,
    Stmt.atom.injEq, forall_eq] at HH
  obtain ⟨e6, e7, e8, e9, e10, e11, e12, e13, e14, L15, L16, L17, L18, L19, L20, L21⟩ := HH
  simp only [pk8Tail, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Atom.Holds,
    Stmt.atom.injEq, forall_eq] at HT
  obtain ⟨S267, S268, S269, S270, S271, e284, e285, S285, S282, e286, e287, e288, e289,
    e290⟩ := HT
  have hz : pkZs.map σ = [0, 0, 0, 0] := by
    have z : ∀ v ∈ [30, 31, 32, 33], σ (.n v) = 0 := by
      intro v hv
      have := HR 0 (by omega) (.const (.n v) (word 0 0)) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl <;> simp [pkRound, packRoundT, pkPre])
      simpa [Atom.Holds, word_zero] using this
    simp [pkZs, z 30 (by simp), z 31 (by simp), z 32 (by simp), z 33 (by simp)]
  have F := fun q (hq : q < 8) ↦ packRound_facts (HR q hq) hz
  have hx8 : σ (.n (valf% «keccak_layer» «_loop0» "pp~2")) = σ (.n (valf% «keccak_layer» «_loop0» "xs")) ^ 8 := gen_pow_eight_of _ _ _ _ e7 e8 e9
  have hx12 : σ (.n (valf% «keccak_layer» «_loop0» "pt~2")) = σ (.n (valf% «keccak_layer» «_loop0» "xs")) ^ 8 := gen_pow_eight_of _ _ _ _ e11 e12 e13
  let R : ℕ → E := fun q ↦ σ (.n (pkB q))
  let G1 : ℕ → E := fun q ↦ σ (.n (pkB q + 1))
  let G2 : ℕ → E := fun q ↦ σ (.n (pkB q + 4))
  let CH : ℕ → E := fun q ↦ σ (.n (pkC q))
  let CL : ℕ → E := fun q ↦ σ (.n (pkCl q))
  let CAP : ℕ → List E := fun q ↦ (pkCap q).map σ
  have hch := eqChain_range R G1 G2 CH CL CAP 8 0 fun q hq ↦ by
    have := (F q hq).2.2.2.2
    simp only [Nat.zero_add]
    simpa [R, G1, G2, CH, CL, CAP, pkCl, pkCap, pkRound] using this
  refine ⟨⟨CAP 0, σ (.n (valf% «keccak_layer» «_loop0» "cur_i")), CL 0, (List.range' 0 8).map R,
    (List.range' 0 8).map fun q ↦ (G1 q, G2 q), (List.range' 0 8).map CH, CL 8, CAP 8,
    ?_, by simp, ?_, ?_, hch, ?_, ?_⟩, ?_⟩
  · rw [← e6]
    exact ⟨capAt_five L15 L16 L17 L18 L19, L20, L21⟩
  · intro k hk
    simp only [List.length_map, List.length_range'] at hk
    have := (F k hk).1
    rw [e10, hx8] at this
    simpa [R] using this
  · have := readsAt_pairs (rd := rd) (p := σ (.n (valf% «keccak_layer» «_loop0» "cur_i"))) ((List.range' 0 8).map fun q ↦ (G1 q, G2 q)) 0
      fun q hq ↦ by
        simp only [List.length_map, List.length_range'] at hq
        have h1 := (F q hq).2.1
        have h2 := (F q hq).2.2.1
        simp only [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range' hq, Option.map_some, Option.getD_some, G1, G2]
        exact ⟨by simpa using h1, by simpa using h2⟩
    simpa using this
  · intro k hk
    simp only [List.length_map, List.length_range'] at hk
    have := (F k hk).2.2.2.1
    rw [e14, hx12] at this
    simpa [CH] using this
  · rw [← e6]
    refine ⟨capAt_five ?_ ?_ ?_ ?_ ?_, ?_, ?_⟩
    · simpa [CAP, pkCap, pkC, cap5] using S267
    · simpa [CAP, pkCap, pkC, cap5] using S268
    · simpa [CAP, pkCap, pkC, cap5] using S269
    · simpa [CAP, pkCap, pkC, cap5] using S270
    · simpa [CAP, pkCap, pkC, cap5] using S271
    · rw [e285, e284, show (65536 : ℕ) = 2 ^ 16 from rfl, word_two_pow (by decide)] at S285
      simpa [krCap] using S285
    · simpa [CL, pkCl, pkC, krCap] using S282
  · intro hne
    have e : σ (.n (valf% «keccak_layer» «_loop0» "s12#2")) = σ (.n (valf% «keccak_layer» «_loop0» "xs")) * gen + σ (.n (valf% «keccak_layer» «_loop0» "bound")) := by rw [e288, e287, e286, word_gen]
    have e' : σ (.n (valf% «keccak_layer» «_loop0» "s12#4")) = σ (.n (valf% «keccak_layer» «_loop0» "xs")) * gen := by rw [e290, e289, word_gen]
    have := hcall (by rw [e]; exact hne)
    simpa [e'] using this

set_option maxRecDepth 20000 in
/-- **The remainder loop's step**: at depth `d + 1` and `x`, an iteration's meaning, and the call
at `x·g` one level shallower unless `x·g = rem_g`. -/
theorem packRem_step {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = packRemT name) (hp : fn.params = loopParams) (d : ℕ)
    (x hg rec pp tb pt : E) (h : coreProgram.relN rd (d + 1) name [x, hg, rec, pp, tb, pt] []) :
    PackRemStep rd rec pp pt x ∧
      (x * gen + hg ≠ 0 → coreProgram.relN rd d name [x * gen, hg, rec, pp, tb, pt] []) := by
  obtain ⟨fn', hf', σ, hpar, hbody⟩ := h
  rw [hf] at hf'
  cases hf'
  rw [hp] at hpar
  simp only [loopParams, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, packRemT, holdsList_append] at hbody
  obtain ⟨H, hc⟩ := (holdsList_atoms (allAtoms_of_all packRemPre_atoms) _ _).1 hbody
  simp only [Stmt.HoldsList, Stmt.Holds] at hc
  obtain ⟨-, hcall, -⟩ := hc
  simp only [packRemPre, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Atom.Holds,
    Stmt.atom.injEq, forall_eq] at H
  obtain ⟨e6, e7, L8_7_0, L9_6_0, L10_6_16, L11_6_32, L12_6_48, L13_6_64, L14_6_80, L15_14_0, e16,
    e17, L18_14_1, e19, e20, e21, e22, e23, e24, e25, hk, e40, L39_40_0, e41,
    L34_6_1, L35_6_17, L36_6_33, L37_6_49, L38_6_65, e44, e45, L45_6_81, L46_6_96, e47, e48, e49,
    e50, e51, e52, L53_6_97, e56, e57, e58, e59, e60⟩ := H
  have hz : [V.n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, e22, e23, e24, e25, word_zero]
  have q0 := sq2_atoms (rd := rd) (a := 15) (o := 26) (zs := [.n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (valf% «keccak_layer» «_loop1» "s7.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")])
    (capV := [.n (valf% «keccak_layer» «_loop1» "sp[0]"), .n (valf% «keccak_layer» «_loop1» "sp[1]"), .n (valf% «keccak_layer» «_loop1» "sp[2]"), .n (valf% «keccak_layer» «_loop1» "sp[3]"), .n (valf% «keccak_layer» «_loop1» "sp[4]")])
    (cap := [σ (.n (valf% «keccak_layer» «_loop1» "sp[0]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[1]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[2]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[3]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[4]"))])
    ⟨e16, e17⟩ ⟨e19, e20⟩ hk hz rfl
  simp only [Nat.reduceAdd] at q0
  refine ⟨⟨[σ (.n (valf% «keccak_layer» «_loop1» "sp[0]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[1]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[2]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[3]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[4]"))], σ (.n (valf% «keccak_layer» «_loop1» "cur_i")), σ (.n (valf% «keccak_layer» «_loop1» "s13#0")),
    σ (.n (valf% «keccak_layer» «_loop1» "r_eq")), σ (.n (valf% «keccak_layer» «_loop1» "x@1")), σ (.n (valf% «keccak_layer» «_loop1» "x@2")), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← e6]
    exact ⟨capAt_five L9_6_0 L10_6_16 L11_6_32 L12_6_48 L13_6_64, L14_6_80, L46_6_96⟩
  · rw [← e7]; exact L8_7_0
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact L15_14_0
    · exact L18_14_1
  · have hsq : ((⟨[σ (.n (valf% «keccak_layer» «_loop1» "sp[0]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[1]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[2]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[3]")), σ (.n (valf% «keccak_layer» «_loop1» "sp[4]"))], []⟩ : Fs).absorbAll
        [σ (.n (valf% «keccak_layer» «_loop1» "x@1")), σ (.n (valf% «keccak_layer» «_loop1» "x@2"))] dsObserve).squeeze =
        (σ (.n (valf% «keccak_layer» «_loop1» "nxt[0]")), ⟨[σ (.n (valf% «keccak_layer» «_loop1» "nxt[8]")), σ (.n (valf% «keccak_layer» «_loop1» "nxt[9]")), σ (.n (valf% «keccak_layer» «_loop1» "nxt[10]")), σ (.n (valf% «keccak_layer» «_loop1» "nxt[11]")), σ (.n (valf% «keccak_layer» «_loop1» "nxt[12]"))], []⟩) := by
      refine Prod.ext q0.1.symm ?_
      rw [q0.2]
      rfl
    simp only [eqRound]
    rw [hsq]
    refine ⟨by rw [← e40]; exact L39_40_0, ?_⟩
    rw [← e6]
    simp only [RoundRec, krCap, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨capAt_five L34_6_1 L35_6_17 L36_6_33 L37_6_49 L38_6_65, ?_, ?_⟩
    · rw [e45, e44, show (4 : ℕ) = 2 ^ 2 from rfl, word_two_pow (by decide)] at L45_6_81
      exact L45_6_81
    · simp only [e52, e51, e50, e49, e48, e47, e41] at L53_6_97
      exact L53_6_97
  · intro hne
    have e : σ (.n (valf% «keccak_layer» «_loop1» "s15#2")) = σ (.n (valf% «keccak_layer» «_loop1» "x1")) * gen + σ (.n (valf% «keccak_layer» «_loop1» "bound")) := by rw [e58, e57, e56, word_gen]
    have e' : σ (.n (valf% «keccak_layer» «_loop1» "s15#4")) = σ (.n (valf% «keccak_layer» «_loop1» "x1")) * gen := by rw [e60, e59, word_gen]
    have := hcall (by rw [e]; exact hne)
    simpa [e'] using this

end
end LeanVM.Guest.B1.VerifySub
