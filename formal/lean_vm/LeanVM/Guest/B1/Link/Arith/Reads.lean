/-
  LeanVM.Guest.B1.Link.Arith.Reads

  The link section's reads are the Statement's values (`readsOfFacts`), from its callees'
  meanings, its own atoms and the transcript.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Calls
import LeanVM.Guest.B1.Link.IndexMle
import LeanVM.Guest.Value.Bits
import Mathlib.Tactic.IntervalCases

/-!
# The section's reads

* the challenge buffer: `θ_0` stored at `chal[0]`, the packed squeeze's cells at `chal·g`
  (`squeeze_packed_sound`, the drawn challenges its first `linkDrawn`); `τ` at `chal·g^89`, `ζ` at
  `τ·g^(n_rows)` (`drawnAt`);
* `slot` and `eq_q`: the section's inline `eqtree`s (`slotSeg`, `eqqSeg`, `eqtreeAt_sound`);
* `table_point`'s returns (`tablePoint_forms`), the corners (`one_plus_suffixes_sound`),
  `state_ends`' and `index_side`'s returns and `below` (`linkEqAt_*`, `sideFold_eq`, `belowE`);
* the rest from the transcript's values.

The `let`s of `tailLets` sliced from the challenges are computed by the kernel at challenges
written `θ_0`, then `88` entries, then a rest (`letsR_*`), as in `Arith/Row.lean`.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Guest.B1.Link LeanVM.Guest.B1 LeanVM.Guest.Value

@[expose] public section

/-! ## Words -/

theorem rdw_of_load {rd : Reader} {p : E} {k : ℕ} {w : E} (h : LoadHolds rd p k w) : rdw rd p k = w := by
  rw [rdw, h.2, Option.getD_some]

theorem rdw_mul_gen_pow (rd : Reader) (p : E) (j k : ℕ) : rdw rd (p * gen ^ j) k = rdw rd p (j + k) := by
  rw [rdw, rdw, Value.gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc, addressOfIndex, addressOfIndex, ← pow_add]

theorem word_g88 : word 452984832 0 = gen ^ 88 := by
  rw [← gpow, ← gpowE_eq_gpow (by decide)]
  decide +kernel

theorem word_g26 : word 67108864 0 = gen ^ 26 := word_two_pow (a := 26) (by norm_num)

theorem word_g1 : word 2 0 = gen ^ 1 := by rw [pow_one]; exact word_gen

/-! ## The section's atoms and `eqtree`s -/

theorem linkAtom {rd : Reader} {σ : Val} (hA : ∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ) {i : ℕ}
    {a : Atom} (h : atomAt linkSec i a = true) : a.Holds rd σ :=
  hA a (mem_of_atomAt h)

theorem seg_mem {ss : List Stmt} {i : ℕ} {t : List Stmt} (h : stmtsEqb ((ss.drop i).take t.length) t = true)
    {a : Atom} (ha : Stmt.atom a ∈ t) : Stmt.atom a ∈ ss := by
  rw [← stmtsEqb_sound h] at ha
  exact List.mem_of_mem_drop (List.mem_of_mem_take ha)

/-- `eqtree(alpha, slot, 4)`, inline. -/
theorem slotSeg : stmtsEqb ((linkSec.drop 99).take (eqtreeAt (.n 10) (.n 11) 50 0 696 4).length)
    (eqtreeAt (.n 10) (.n 11) 50 0 696 4) = true := by decide +kernel

/-- `eqtree(q_point, eq_q, 6)`, inline. -/
theorem eqqSeg : stmtsEqb ((linkSec.drop 483).take (eqtreeAt (.n 16) (.n 17) 0 0 1078 6).length)
    (eqtreeAt (.n 16) (.n 17) 0 0 1078 6) = true := by decide +kernel

/-! ## `linkTail`'s slices at `θ_0`, `88` entries `f`, a rest -/

section Lets

variable (lm lb : ℕ) (bc : List K) (rows : List ℕ) (pl : List (Option Placement)) (sl : ℕ)
  (hts : List ℕ) (chunks : Chunks) (theta0 : E) (f : ℕ → E) (rest r : List E) (m1 : E)
  (fresh : List E) (split : Split) (qPoint : List E)

/-- The `let`s at challenges `θ_0`, `88` entries `f`, a rest. -/
abbrev letsR : TailLets :=
  tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 ((List.range 88).map f ++ rest) r m1 fresh
    split qPoint

theorem letsR_theta : (letsR lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh split qPoint).theta =
    theta0 :: (List.range 5).map f := by kernel_eq

theorem letsR_slot : (letsR lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh split qPoint).slot =
    eqKernel ((List.range 4).map fun i ↦ f (49 + i)) := by kernel_eq

theorem letsR_tau : (letsR lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh split qPoint).tau =
    rest.take (hts.foldl max 0) := by kernel_eq

theorem letsR_zeta : (letsR lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh split qPoint).zeta =
    (rest.drop (hts.foldl max 0)).take chunks.width := by kernel_eq

theorem letsR_nu : (letsR lm lb bc rows pl sl hts chunks theta0 f rest r m1 fresh split qPoint).nu =
    ((rest.drop (hts.foldl max 0)).drop chunks.width).take chunks.d := by kernel_eq

end Lets

/-! ## The drawn challenges' words -/

theorem linkDrawn_eq (lm lb : ℕ) (bc : List K) (rows : List ℕ) (pl : List (Option Placement)) (sl : ℕ)
    (hts : List ℕ) (chunks : Chunks) :
    linkDrawn (layoutOf lm lb bc rows pl sl hts) chunks =
      88 + hts.foldl max 0 + chunks.width + ((Chunks.new chunks.width).map Chunks.d).getD 0 := by
  have h1 : (tables.map (·.links.memory.length)).sum = 39 := by decide +kernel
  have h2 : (tables.map fun x ↦ x.links.pointers.length).sum = 33 := by decide +kernel
  simp only [linkDrawn, packedChallenges, linkRows, h1, h2, nTables, bytecodeSlotBits]

/-! ## The `let`s, in terms of the challenges -/

section LetsD

variable {lm lb : ℕ} {bc : List K} {rows : List ℕ} {pl : List (Option Placement)} {sl : ℕ}
  {hts : List ℕ} {chunks : Chunks} {theta0 : E} {drawn r : List E} {m1 : E} {fresh : List E}
  {split : Split} {qPoint : List E}

theorem lets_theta (hd : 88 ≤ drawn.length) :
    (tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh split qPoint).theta =
      theta0 :: (List.range 5).map (drawn.getD · 0) := by
  conv_lhs => rw [list_canon drawn 88 hd]
  exact letsR_theta ..

theorem lets_slot (hd : 88 ≤ drawn.length) :
    (tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh split qPoint).slot =
      eqKernel ((List.range 4).map fun i ↦ drawn.getD (49 + i) 0) := by
  conv_lhs => rw [list_canon drawn 88 hd]
  exact letsR_slot ..

theorem lets_tau (hd : 88 ≤ drawn.length) :
    (tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh split qPoint).tau =
      (drawn.drop 88).take (hts.foldl max 0) := by
  conv_lhs => rw [list_canon drawn 88 hd]
  exact letsR_tau ..

theorem lets_zeta (hd : 88 ≤ drawn.length) :
    (tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh split qPoint).zeta =
      ((drawn.drop 88).drop (hts.foldl max 0)).take chunks.width := by
  conv_lhs => rw [list_canon drawn 88 hd]
  exact letsR_zeta ..

theorem lets_nu (hd : 88 ≤ drawn.length) :
    (tailLets (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh split qPoint).nu =
      (((drawn.drop 88).drop (hts.foldl max 0)).drop chunks.width).take chunks.d := by
  conv_lhs => rw [list_canon drawn 88 hd]
  exact letsR_nu ..

end LetsD

/-! ## From the facts -/

theorem readsAt_ext {rd : Reader} {p : E} {xs : List E} {n : ℕ} {f : ℕ → E} (hx : ReadsAt rd p xs)
    (hl : xs.length = n) (hf : ∀ i < n, LoadHolds rd p i (f i)) : xs = (List.range n).map f := by
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range]
  exact loadHolds_unique (hx i h1) (hf i (by omega))

theorem getD_eq_getElem' {l : List E} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

section Facts

variable {rd : Reader} {σ : Val} {lm lb : ℕ} {bc : List K} {rows : List ℕ}
  {pl : List (Option Placement)} {sl : ℕ} {hts : List ℕ} {chunks : Chunks} {theta0 : E}
  {drawn r : List E} {m1 : E} {fresh splitv chi qPoint message : List E} {p : ℕ}
  (hA : ∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ)
  (F : LinkFacts rd σ (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh splitv chi
    qPoint message p)

include F in
/-- The drawn challenges are the words at `chal·g`. -/
theorem drawnAt : ∀ j < linkDrawn (layoutOf lm lb bc rows pl sl hts) chunks,
    LoadHolds rd (σ (.n 679)) j (drawn.getD j 0) := by
  have hm := squeeze_packed_sound rd _ _ F.squeeze
  simp only [MeaningSP] at hm
  obtain ⟨p', hp', hcg, hreads, -⟩ := hm
  have hpp : p' = p := gen_pow_inj (by omega) (by have := F.countLt; omega) (hcg.symm.trans F.count)
  subst hpp
  intro j hj
  have hl := pkSqueeze_length p' [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579)]
  have hj8 : j < 8 * p' := lt_of_lt_of_le hj F.drawnLe
  rw [F.drawnEq, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj,
    List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact hreads j (by omega)

theorem drawn_len_ge : 88 + hts.foldl max 0 + chunks.width ≤
    linkDrawn (layoutOf lm lb bc rows pl sl hts) chunks := by
  rw [linkDrawn_eq]; omega

include hA F in
/-- The challenge buffer: `θ_0`, then the drawn challenges. -/
theorem chalAt : ∀ k < 89, LoadHolds rd (σ (.n 10)) k ((theta0 :: drawn).getD k 0) := by
  intro k hk
  rcases k with _ | j
  · have h := linkAtom hA (i := 84) (a := .load (.n 573) (.n 10) 0) (by decide +kernel)
    rw [← F.theta]; exact h
  · have h678 : σ (.n 678) = word 2 0 :=
      linkAtom hA (i := 85) (a := .const (.n 678) (word 2 0)) (by decide +kernel)
    have h679 : σ (.n 679) = σ (.n 10) * σ (.n 678) :=
      linkAtom hA (i := 86) (a := .mul (.n 679) (.n 10) (.n 678)) (by decide +kernel)
    have hlen := drawn_len_ge (lm := lm) (lb := lb) (bc := bc) (rows := rows) (pl := pl) (sl := sl)
      (hts := hts) (chunks := chunks)
    have hd := drawnAt F j (by omega)
    rw [h679, h678, word_g1, loadHolds_mul_gen_pow] at hd
    simpa [Nat.add_comm] using hd

end Facts

section Tables

variable {rd : Reader} {σ : Val} {lm lb : ℕ} {bc : List K} {rows : List ℕ}
  {pl : List (Option Placement)} {sl : ℕ} {hts : List ℕ} {chunks : Chunks} {theta0 : E}
  {drawn r : List E} {m1 : E} {fresh splitv chi qPoint message : List E} {p : ℕ}
  (hA : ∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ)
  (F : LinkFacts rd σ (layoutOf lm lb bc rows pl sl hts) chunks theta0 drawn r m1 fresh splitv chi
    qPoint message p)

include hA F in
/-- Table `t`'s pointers: `theta[t]`, `τ` at `chal·g^89`, the row bits, the corner. -/
theorem tableAtoms (t : ℕ) (ht : t < 6) :
    LoadHolds rd (σ (.n 10)) t (σ (.n (tpThetaVn.getD t 0))) ∧
      σ (.n (tpTauVn.getD t 0)) = σ (.n 679) * gen ^ 88 ∧
      σ (.n (tpBitsVn.getD t 0)) = σ (.n (bitsVn.getD t 0)) ∧
      σ (.n (cornerVn.getD t 0)) = σ (.n 18) * σ (.n (115 + t)) := by
  interval_cases t
  · have hθ : LoadHolds rd (σ (.n 10)) 0 (σ (.n 1293)) :=
      linkAtom hA (i := 817) (a := .load (.n 1293) (.n 10) 0) (by decide +kernel)
    have hc : σ (.n 1294) = word 452984832 0 :=
      linkAtom hA (i := 818) (a := .const (.n 1294) (word 452984832 0)) (by decide +kernel)
    have hm : σ (.n 1295) = σ (.n 679) * σ (.n 1294) :=
      linkAtom hA (i := 819) (a := .mul (.n 1295) (.n 679) (.n 1294)) (by decide +kernel)
    have hk : σ (.n 1299) = σ (.n 18) * σ (.n 115) :=
      linkAtom hA (i := 821) (a := .mul (.n 1299) (.n 18) (.n 115)) (by decide +kernel)
    exact ⟨hθ, by show σ (.n 1295) = _; rw [hm, hc, word_g88], rfl, hk⟩
  · have hθ : LoadHolds rd (σ (.n 10)) 1 (σ (.n 1403)) :=
      linkAtom hA (i := 925) (a := .load (.n 1403) (.n 10) 1) (by decide +kernel)
    have hc : σ (.n 1404) = word 452984832 0 :=
      linkAtom hA (i := 926) (a := .const (.n 1404) (word 452984832 0)) (by decide +kernel)
    have hm : σ (.n 1405) = σ (.n 679) * σ (.n 1404) :=
      linkAtom hA (i := 927) (a := .mul (.n 1405) (.n 679) (.n 1404)) (by decide +kernel)
    have hk : σ (.n 1411) = σ (.n 18) * σ (.n 116) :=
      linkAtom hA (i := 931) (a := .mul (.n 1411) (.n 18) (.n 116)) (by decide +kernel)
    have hbc : σ (.n 1406) = word 67108864 0 :=
      linkAtom hA (i := 928) (a := .const (.n 1406) (word 67108864 0)) (by decide +kernel)
    have hbm : σ (.n 1407) = σ (.n 7) * σ (.n 1406) :=
      linkAtom hA (i := 929) (a := .mul (.n 1407) (.n 7) (.n 1406)) (by decide +kernel)
    have hp := F.bitsPtr 0 (by norm_num)
    exact ⟨hθ, by show σ (.n 1405) = _; rw [hm, hc, word_g88],
      by show σ (.n 1407) = σ (.n 159); rw [hbm, hbc]; exact hp.symm, hk⟩
  · have hθ : LoadHolds rd (σ (.n 10)) 2 (σ (.n 1524)) :=
      linkAtom hA (i := 1044) (a := .load (.n 1524) (.n 10) 2) (by decide +kernel)
    have hc : σ (.n 1525) = word 452984832 0 :=
      linkAtom hA (i := 1045) (a := .const (.n 1525) (word 452984832 0)) (by decide +kernel)
    have hm : σ (.n 1526) = σ (.n 679) * σ (.n 1525) :=
      linkAtom hA (i := 1046) (a := .mul (.n 1526) (.n 679) (.n 1525)) (by decide +kernel)
    have hk : σ (.n 1532) = σ (.n 18) * σ (.n 117) :=
      linkAtom hA (i := 1050) (a := .mul (.n 1532) (.n 18) (.n 117)) (by decide +kernel)
    have hbc : σ (.n 1527) = word 67108864 0 :=
      linkAtom hA (i := 1047) (a := .const (.n 1527) (word 67108864 0)) (by decide +kernel)
    have hbm : σ (.n 1528) = σ (.n 159) * σ (.n 1527) :=
      linkAtom hA (i := 1048) (a := .mul (.n 1528) (.n 159) (.n 1527)) (by decide +kernel)
    have hp := F.bitsPtr 1 (by norm_num)
    exact ⟨hθ, by show σ (.n 1526) = _; rw [hm, hc, word_g88],
      by show σ (.n 1528) = σ (.n 175); rw [hbm, hbc]; exact hp.symm, hk⟩
  · have hθ : LoadHolds rd (σ (.n 10)) 3 (σ (.n 1607)) :=
      linkAtom hA (i := 1125) (a := .load (.n 1607) (.n 10) 3) (by decide +kernel)
    have hc : σ (.n 1608) = word 452984832 0 :=
      linkAtom hA (i := 1126) (a := .const (.n 1608) (word 452984832 0)) (by decide +kernel)
    have hm : σ (.n 1609) = σ (.n 679) * σ (.n 1608) :=
      linkAtom hA (i := 1127) (a := .mul (.n 1609) (.n 679) (.n 1608)) (by decide +kernel)
    have hk : σ (.n 1615) = σ (.n 18) * σ (.n 118) :=
      linkAtom hA (i := 1131) (a := .mul (.n 1615) (.n 18) (.n 118)) (by decide +kernel)
    have hbc : σ (.n 1610) = word 67108864 0 :=
      linkAtom hA (i := 1128) (a := .const (.n 1610) (word 67108864 0)) (by decide +kernel)
    have hbm : σ (.n 1611) = σ (.n 175) * σ (.n 1610) :=
      linkAtom hA (i := 1129) (a := .mul (.n 1611) (.n 175) (.n 1610)) (by decide +kernel)
    have hp := F.bitsPtr 2 (by norm_num)
    exact ⟨hθ, by show σ (.n 1609) = _; rw [hm, hc, word_g88],
      by show σ (.n 1611) = σ (.n 191); rw [hbm, hbc]; exact hp.symm, hk⟩
  · have hθ : LoadHolds rd (σ (.n 10)) 4 (σ (.n 1734)) :=
      linkAtom hA (i := 1250) (a := .load (.n 1734) (.n 10) 4) (by decide +kernel)
    have hc : σ (.n 1735) = word 452984832 0 :=
      linkAtom hA (i := 1251) (a := .const (.n 1735) (word 452984832 0)) (by decide +kernel)
    have hm : σ (.n 1736) = σ (.n 679) * σ (.n 1735) :=
      linkAtom hA (i := 1252) (a := .mul (.n 1736) (.n 679) (.n 1735)) (by decide +kernel)
    have hk : σ (.n 1742) = σ (.n 18) * σ (.n 119) :=
      linkAtom hA (i := 1256) (a := .mul (.n 1742) (.n 18) (.n 119)) (by decide +kernel)
    have hbc : σ (.n 1737) = word 67108864 0 :=
      linkAtom hA (i := 1253) (a := .const (.n 1737) (word 67108864 0)) (by decide +kernel)
    have hbm : σ (.n 1738) = σ (.n 191) * σ (.n 1737) :=
      linkAtom hA (i := 1254) (a := .mul (.n 1738) (.n 191) (.n 1737)) (by decide +kernel)
    have hp := F.bitsPtr 3 (by norm_num)
    exact ⟨hθ, by show σ (.n 1736) = _; rw [hm, hc, word_g88],
      by show σ (.n 1738) = σ (.n 207); rw [hbm, hbc]; exact hp.symm, hk⟩
  · have hθ : LoadHolds rd (σ (.n 10)) 5 (σ (.n 1880)) :=
      linkAtom hA (i := 1394) (a := .load (.n 1880) (.n 10) 5) (by decide +kernel)
    have hc : σ (.n 1881) = word 452984832 0 :=
      linkAtom hA (i := 1395) (a := .const (.n 1881) (word 452984832 0)) (by decide +kernel)
    have hm : σ (.n 1882) = σ (.n 679) * σ (.n 1881) :=
      linkAtom hA (i := 1396) (a := .mul (.n 1882) (.n 679) (.n 1881)) (by decide +kernel)
    have hk : σ (.n 1888) = σ (.n 18) * σ (.n 120) :=
      linkAtom hA (i := 1400) (a := .mul (.n 1888) (.n 18) (.n 120)) (by decide +kernel)
    have hbc : σ (.n 1883) = word 67108864 0 :=
      linkAtom hA (i := 1397) (a := .const (.n 1883) (word 67108864 0)) (by decide +kernel)
    have hbm : σ (.n 1884) = σ (.n 207) * σ (.n 1883) :=
      linkAtom hA (i := 1398) (a := .mul (.n 1884) (.n 207) (.n 1883)) (by decide +kernel)
    have hp := F.bitsPtr 4 (by norm_num)
    exact ⟨hθ, by show σ (.n 1882) = _; rw [hm, hc, word_g88],
      by show σ (.n 1884) = σ (.n 223); rw [hbm, hbc]; exact hp.symm, hk⟩

include hA in
/-- `ζ` at `τ·g^(n_rows)`, `ν` at `ζ·g^w`. -/
theorem zetaAtoms : σ (.n 694) = σ (.n 679) * σ (.n 692) * σ (.n 408) ∧ σ (.n 692) = word 452984832 0 ∧
    σ (.n 695) = σ (.n 694) * σ (.n 409) := by
  have h692 : σ (.n 692) = word 452984832 0 :=
    linkAtom hA (i := 95) (a := .const (.n 692) (word 452984832 0)) (by decide +kernel)
  have h693 : σ (.n 693) = σ (.n 679) * σ (.n 692) :=
    linkAtom hA (i := 96) (a := .mul (.n 693) (.n 679) (.n 692)) (by decide +kernel)
  have h694 : σ (.n 694) = σ (.n 693) * σ (.n 408) :=
    linkAtom hA (i := 97) (a := .mul (.n 694) (.n 693) (.n 408)) (by decide +kernel)
  have h695 : σ (.n 695) = σ (.n 694) * σ (.n 409) :=
    linkAtom hA (i := 98) (a := .mul (.n 695) (.n 694) (.n 409)) (by decide +kernel)
  exact ⟨by rw [h694, h693], h692, h695⟩

include hA F in
/-- `ζ`'s words: the drawn challenges from `88 + n_rows`. -/
theorem zetaAt : ∀ i < chunks.width,
    LoadHolds rd (σ (.n 694)) i (drawn.getD (88 + hts.foldl max 0 + i) 0) := by
  intro i hi
  obtain ⟨h694, h692, -⟩ := zetaAtoms hA
  have hlen := drawn_len_ge (lm := lm) (lb := lb) (bc := bc) (rows := rows) (pl := pl) (sl := sl)
    (hts := hts) (chunks := chunks)
  have hd := drawnAt F (88 + hts.foldl max 0 + i) (by omega)
  rw [h694, h692, word_g88, F.gN, mul_assoc, ← pow_add, loadHolds_mul_gen_pow]
  simpa [linkRows, Nat.add_assoc] using hd

end Tables

/-! ## Slices -/

theorem dt_eq (l : List E) (a w : ℕ) (h : a + w ≤ l.length) :
    (l.drop a).take w = (List.range w).map fun i ↦ l.getD (a + i) 0 := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 ↦ ?_
  simp only [List.length_map, List.length_range] at h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [getD_eq_getElem' (by omega)]

theorem ddt_eq (l : List E) (a b w : ℕ) (h : a + b + w ≤ l.length) :
    ((l.drop a).drop b).take w = (List.range w).map fun i ↦ l.getD (a + b + i) 0 := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 ↦ ?_
  simp only [List.length_map, List.length_range] at h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [getD_eq_getElem' (by omega)]
  congr 1; omega

theorem getD_cons_succ' (x : E) (l : List E) (k : ℕ) : (x :: l).getD (k + 1) 0 = l.getD k 0 := rfl

theorem slot_mem {a : Atom} (ha : Stmt.atom a ∈ eqtreeAt (.n 10) (.n 11) 50 0 696 4) :
    Stmt.atom a ∈ linkSec := seg_mem slotSeg ha

theorem eqq_mem {a : Atom} (ha : Stmt.atom a ∈ eqtreeAt (.n 16) (.n 17) 0 0 1078 6) :
    Stmt.atom a ∈ linkSec := seg_mem eqqSeg ha

/-- `slot`: `eq(α, ·)` of the four challenges from `chal[50]`. -/
theorem slotAt {rd : Reader} {σ : Val} (hA : ∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ) {rs : List E}
    (hrs : rs.length = 4) (hpt : ∀ t < 4, LoadHolds rd (σ (.n 10)) (50 + t) (rs.getD t 0)) :
    ∀ k < 16, LoadHolds rd (σ (.n 11)) (14 + k) ((eqKernel rs).getD k 0) := by
  intro k hk
  have := eqtreeAt_sound (rd := rd) (σ := σ) (p := .n 10) (o := .n 11) (po := 50) (oo := 0)
    (b := 696) (n := 4) (by norm_num) (fun a ha ↦ hA a (slot_mem ha)) hrs hpt 4 (by norm_num) le_rfl k hk
  rwa [List.take_of_length_le (by omega), show 0 + (2 ^ 4 - 2 + k) = 14 + k by omega] at this

/-- `eq_q`: `eq(q_point, ·)`. -/
theorem eqqAt {rd : Reader} {σ : Val} (hA : ∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ) {qs : List E}
    (hqs : qs.length = 6) (hpt : ∀ t < 6, LoadHolds rd (σ (.n 16)) (0 + t) (qs.getD t 0)) :
    ∀ q < 64, LoadHolds rd (σ (.n 17)) (62 + q) ((eqKernel qs).getD q 0) := by
  intro q hq
  have := eqtreeAt_sound (rd := rd) (σ := σ) (p := .n 16) (o := .n 17) (po := 0) (oo := 0)
    (b := 1078) (n := 6) (by norm_num) (fun a ha ↦ hA a (eqq_mem ha)) hqs hpt 6 (by norm_num) le_rfl q hq
  rwa [List.take_of_length_le (by omega), show 0 + (2 ^ 6 - 2 + q) = 62 + q by omega] at this

/-! ## The reads -/

/-- **The section's reads are the Statement's values.** -/
theorem readsOfFacts : ReadsOfFacts := by
  intro rd σ layout chunks theta0 drawn r m1 fresh splitv chi qPoint message p hA hs hlb F
  obtain ⟨htab, hd, -, -, hq, -⟩ := hs
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab hlb
  subst htab hlb
  change LinkFacts rd σ (layoutOf lm 19 bc rows pl sl hts) chunks theta0 drawn r m1 fresh splitv chi
    qPoint message p at F
  change IRReads rd σ (tailIn (layoutOf lm 19 bc rows pl sl hts) chunks theta0 drawn r m1 fresh splitv
    chi qPoint message)
  have hd' : 88 ≤ drawn.length := hd
  have hq6 : qPoint.length = 6 := hq
  have hdl : drawn.length = linkDrawn (layoutOf lm 19 bc rows pl sl hts) chunks := by
    rw [F.drawnEq, List.length_take, pkSqueeze_length]
    exact Nat.min_eq_left F.drawnLe
  have hlen := drawn_len_ge (lm := lm) (lb := 19) (bc := bc) (rows := rows) (pl := pl) (sl := sl)
    (hts := hts) (chunks := chunks)
  have hchal := chalAt hA F
  have hw1 := F.widthGe
  have hw2 := F.widthLe
  have hnR : hts.foldl max 0 ≤ 24 := F.rowsLe
  -- `ζ`
  have hzeta : (tailLets (layoutOf lm 19 bc rows pl sl hts) chunks theta0 drawn r m1 fresh
      (Split.ofColumns tables splitv) qPoint).zeta =
      (List.range chunks.width).map fun i ↦ drawn.getD (88 + hts.foldl max 0 + i) 0 := by
    rw [lets_zeta hd', ddt_eq _ _ _ _ (by omega)]
  -- `state_ends`
  have hse := state_ends_sound chunks.width hw1 hw2 rd _ _ F.stateEnds
  simp only [MeaningStateEnds] at hse
  obtain ⟨zs, cs, hzl, hcl, hrz, hrc, hse⟩ := hse
  have hzs : zs = (List.range chunks.width).map fun i ↦ drawn.getD (88 + hts.foldl max 0 + i) 0 :=
    readsAt_ext hrz hzl (zetaAt hA F)
  have hcs : cs = bitsE (linkCycles (layoutOf lm 19 bc rows pl sl hts)) chunks.width :=
    readsAt_unique hrc F.cycleBits (by rw [hcl, bitsE_length])
  simp only [List.cons.injEq, and_true] at hse
  -- `index_side`
  have his := index_side_sound index_mle_holds chunks.width hw1 hw2 rd _ _ F.indexSide
  simp only [MeaningIndexSide] at his
  obtain ⟨rs, zs', hrl, hzl', hrr, hrz', hbelow, his⟩ := his
  have hrs : rs = r := readsAt_unique hrr F.point (hrl.trans F.pointLen.symm)
  have hzs' : zs' = zs := readsAt_unique hrz' hrz (hzl'.trans hzl.symm)
  subst rs zs'
  simp only [List.cons.injEq, and_true] at his
  -- the corners
  have hops := one_plus_suffixes_sound (hts.foldl max 0) (by omega) rd _ _ F.suffixes
  simp only [MeaningOnePlusSuffixes] at hops
  obtain ⟨⟨as, hasl, hras, hcorner⟩, -⟩ := hops
  have has : as = chi := readsAt_unique hras F.rowPoint (hasl.trans F.rowPointLen.symm)
  subst as
  have h801 : σ (.n 801) = σ (.n 13) * σ (.n 101) :=
    linkAtom hA (i := 213) (a := .mul (.n 801) (.n 13) (.n 101)) (by decide +kernel)
  set L := tailLets (layoutOf lm 19 bc rows pl sl hts) chunks theta0 drawn r m1 fresh
    (Split.ofColumns tables splitv) qPoint with hL
  have htab : ∀ t < 6,
      σ (.n (omegaVn.getD t 0)) = omegaAt (L.theta.getD t 0) (L.tau.take (hts.getD t 0))
        (chi.take (hts.getD t 0)) (rows.getD t 0) ∧
      σ (.n (omegaVn.getD t 0 + 1)) = lessThan (chi.take (hts.getD t 0)) (rows.getD t 0) ∧
      σ (.n (omegaVn.getD t 0 + 2)) = eqEval (L.tau.take (hts.getD t 0)) (chi.take (hts.getD t 0)) := by
    intro t ht
    obtain ⟨hθ, htau, hbits, -⟩ := tableAtoms hA F t ht
    have hh : hts.getD t 0 ≤ hts.foldl max 0 := F.heightsLe t ht
    have htp := table_point_sound (hts.getD t 0) (by omega) rd _ _ (F.tablePoint t ht)
    simp only [MeaningTablePoint] at htp
    obtain ⟨ts, xs, cs, top, htl, hxl, hcl', hrts, hrxs, hrcs, htop, hret⟩ := htp
    rw [htau] at hrts
    rw [hbits] at hrcs htop
    have hts' : ts = L.tau.take (hts.getD t 0) := by
      rw [hL, lets_tau hd', List.take_take, Nat.min_eq_left hh, dt_eq _ _ _ (by omega)]
      exact readsAt_ext hrts htl fun i hi ↦ by
        rw [loadHolds_mul_gen_pow]; exact drawnAt F (88 + i) (by omega)
    have hcl2 : chi.length = hts.foldl max 0 := F.rowPointLen
    have hxs' : xs = chi.take (hts.getD t 0) := by
      rw [← List.drop_zero (l := chi), dt_eq _ _ _ (by omega)]
      exact readsAt_ext hrxs hxl fun i hi ↦ by
        rw [Nat.zero_add, getD_eq_getElem' (by omega)]; exact F.rowPoint i (by omega)
    have hcs' : cs = cbitsE (rows.getD t 0) (hts.getD t 0) :=
      readsAt_unique hrcs (F.rowBits t ht).1 (by rw [hcl', cbitsE_length])
    have htop' : top = bitE (rows.getD t 0) (hts.getD t 0) := loadHolds_unique htop (F.rowBits t ht).2
    have hθ' : σ (.n (tpThetaVn.getD t 0)) = L.theta.getD t 0 := by
      rw [loadHolds_unique hθ (hchal t (by omega)), hL, lets_theta hd']
      rcases t with _ | j
      · rfl
      · rw [getD_cons_succ', getD_cons_succ', getD_range_map _ (by omega)]
    subst ts xs cs top
    simp only [List.cons.injEq, and_true] at hret
    obtain ⟨f1, f2, f3⟩ := tablePoint_forms (σ (.n (tpThetaVn.getD t 0))) (L.tau.take (hts.getD t 0))
      (chi.take (hts.getD t 0)) (rows.getD t 0) (hts.getD t 0) htl hxl (F.tableRowsLe t ht)
    refine ⟨?_, ?_, ?_⟩
    · rw [hret.1, f1, hθ']
    · rw [hret.2.1, f2]
    · rw [hret.2.2, f3]
  refine
    { chal := fun k hk ↦ rdw_of_load (hchal k hk)
      slot := ?_
      sent := F.messageAt
      splitv := F.splitAt
      eqQ := ?_
      omega := fun t ht ↦ (htab t ht).1
      act := fun t ht ↦ (htab t ht).2.1
      eqTau := fun t ht ↦ (htab t ht).2.2
      corner := ?_
      jump := ?_
      e0 := ?_
      ec := ?_
      idx := his.1
      eqzr := ?_
      shz := ?_
      belowMem := ?_
      belowBc := ?_
      eq0R := ?_
      m1 := F.memTerm
      cert := ?_ }
  · -- `slot`: the inline `eqtree(alpha, slot, 4)`
    intro k hk
    have h := slotAt hA (rs := (List.range 4).map fun i ↦ drawn.getD (49 + i) 0)
      (by rw [List.length_map, List.length_range]) (fun t ht ↦ by
        rw [getD_range_map _ ht]
        have h := hchal (50 + t) (by omega)
        have e : (theta0 :: drawn).getD (50 + t) 0 = drawn.getD (49 + t) 0 := by
          rw [show 50 + t = (49 + t) + 1 by omega]; rfl
        rwa [e] at h) k hk
    show rdw rd (σ (.n 11)) (14 + k) = (tailLets (layoutOf lm 19 bc rows pl sl hts) chunks theta0 drawn r m1
      fresh (Split.ofColumns tables splitv) qPoint).slot.getD k 0
    rw [lets_slot hd']
    exact rdw_of_load h
  · -- `eq_q`: the inline `eqtree(q_point, eq_q, 6)`
    intro q hq'
    exact rdw_of_load (eqqAt hA hq6 (fun t ht ↦ by
      rw [getD_eq_getElem' (by omega), Nat.zero_add]; exact F.qPointAt t (by omega)) q hq')
  · -- the corners
    intro t ht
    obtain ⟨-, -, -, hcor⟩ := tableAtoms hA F t ht
    have hh : hts.getD t 0 ≤ hts.foldl max 0 := F.heightsLe t ht
    show rdw rd (σ (.n (cornerVn.getD t 0))) 0 = prodE ((chi.drop (hts.getD t 0)).map (1 + ·))
    rw [hcor, show σ (.n (115 + t)) = gen ^ hts.getD t 0 from F.gH t ht, rdw_mul_gen_pow, Nat.add_zero]
    exact rdw_of_load (hcorner _ hh)
  · intro k hk
    show σ (.n (783 + k)) = (fresh.drop 1).getD k 0
    rw [F.freshEq]
    interval_cases k <;> rfl
  · show σ (.n 752) = linkEqAt L.zeta 0
    rw [hse.1, hzeta, ← hzs, linkEqAt_zero_eq]
  · show σ (.n 753) = linkEqAt L.zeta (linkCycles (layoutOf lm 19 bc rows pl sl hts))
    rw [hse.2, hzeta, ← hzs, hcs, linkEqAt_eq_endsProd, hzl]
  · show σ (.n 798) = eqEval L.zeta r
    rw [his.2.1, hzeta, ← hzs]
    exact (sideFold_eq zs r).1
  · show σ (.n 799) = linkShiftEq L.zeta r
    rw [his.2.2, hzeta, ← hzs]
    exact (sideFold_eq zs r).2
  · show rdw rd (σ (.n 801)) 0 = prodE ((r.drop (min lm chunks.width)).map (1 + ·))
    rw [h801, show σ (.n 101) = gen ^ lm from F.gMem, rdw_mul_gen_pow, Nat.add_zero,
      Nat.min_eq_left F.logMemoryLe]
    exact rdw_of_load (hbelow lm F.logMemoryLe)
  · show rdw rd (σ (.n 13)) 19 = prodE ((r.drop (min 19 chunks.width)).map (1 + ·))
    rw [Nat.min_eq_left hw1]
    exact rdw_of_load (hbelow 19 hw1)
  · show rdw rd (σ (.n 13)) 0 = prodE ((r.drop (min 0 chunks.width)).map (1 + ·))
    rw [Nat.zero_min]
    exact rdw_of_load (hbelow 0 (Nat.zero_le _))
  · show σ (.n 782) = fresh.getD 0 0
    rw [F.freshEq]
    rfl

end

end LeanVM.Guest.B1.Link.Arith
