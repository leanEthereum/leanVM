/-
  LeanVM.Guest.B1.VerifySub.PhLinkFacts

  From `verify_sub`'s run: the link section's atoms hold, and the facts `readsOfFacts` and
  `terminalOfFacts` read (`LinkFacts`, `TerminalFacts`, `TailShape`) hold at the transcript's
  values.
-/

module

public import LeanVM.Guest.B1.VerifySub.Flat
public import LeanVM.Guest.B1.VerifySub.PhLinkShape
public import LeanVM.Guest.B1.Link.Arith.Calls
public import LeanVM.Guest.B1.Link.Arith.Reads
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»
import LeanVM.Guest.CoreLemmas
import Mathlib.Tactic.IntervalCases

/-!
# The link section's facts, from the run

`vsLinkFactsOfRun`: from a run (`VsRun`), its shape (`ShapeOk`, `PhLinkShape.lean`) at the chunking
`c` of its pointer width, the packed squeeze's count `g^p` with
`linkDrawn ≤ 8 p`, and the words at `r_pt`, `chi`, `q_point` and the row side's cursor, the link
section's atoms hold, and `TailShape`, `LinkFacts` and `TerminalFacts` hold at the transcript's
values: `θ_0 = σ573`, the drawn challenges the squeeze's first `linkDrawn` cells, `m1 = σ779`, the
fresh coefficients `σ782 .. σ786`, the split values the `36` words at `splitv`, the claim `σ1077`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Guest.B1.Link LeanVM.Guest.B1.Link.Arith

@[expose] public section

/-- **The link section's facts, from the run.** -/
def VsLinkFactsOfRun : Prop :=
  ∀ (bytecode : List K) {κ : ℕ} (L : MemoryImage κ) (C : CallRel) (V : FrameMap) (σ : Val)
    (rets : List E) (c : Chunks) (p : ℕ) (r chi qPoint message : List E),
    VsRun bytecode L C V σ rets → ShapeOk bytecode L.read σ →
    Chunks.new (linkWidth (vsLayout bytecode σ)) = some c →
    σ (.n 645) = gen ^ p → p < 64 → linkDrawn (vsLayout bytecode σ) c ≤ 8 * p →
    ReadsAt L.read (σ (.n 12)) r → r.length = linkWidth (vsLayout bytecode σ) →
    ReadsAt L.read (σ (.n 15)) chi → chi.length = linkRows (vsLayout bytecode σ) →
    ReadsAt L.read (σ (.n 16)) qPoint → qPoint.length = 6 →
    ReadsAt L.read (σ (.n 1076)) message → message.length = 144 →
    let layout := vsLayout bytecode σ
    let drawn := ((pkSqueeze p [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579)]).1).take
      (linkDrawn layout c)
    let fresh := [σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785), σ (.n 786)]
    let splitv := wordsAt L.read (σ (.n 14)) 36
    (∀ a, Stmt.atom a ∈ linkSec → a.Holds L.read σ) ∧
      TailShape layout drawn fresh splitv qPoint message ∧
      LinkFacts L.read σ layout c (σ (.n 573)) drawn r (σ (.n 779)) fresh splitv chi qPoint message p ∧
      TerminalFacts L.read σ c message (σ (.n 1077))

/-! ## Dispatches and selectors -/

section

variable {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {Vm : FrameMap} {σ : Val}
  {rets : List E}

/-- A dispatch of the body at the selector `g^j`: its `j`-th callee's relation. -/
theorem disp_rel (R : VsRun bytecode L C Vm σ rets) {x : ℕ} {fs : List String} {args rs : List V}
    (hm : membB (.dispatch (.n x) fs args rs) vsPre = true) (hfs : fs.length ≤ 64) {j : ℕ}
    (hj : j < fs.length) (hx : σ (.n x) = gen ^ j) :
    coreProgram.Rel L.read (fs.getD j "") (args.map σ) (rs.map σ) := by
  have h := R.dispatch hm
  simp only [Stmt.Holds, and_true] at h
  obtain ⟨j', hj', hx', hc⟩ := h
  rw [hx, ← gen_pow_eq_ofK] at hx'
  obtain rfl : j = j' := gen_pow_inj (by omega) (by omega) hx'
  rw [List.getD_eq_getElem _ _ hj']
  exact R.hle _ _ _ hc

end

/-- `g^-19`, as the data writes it. -/
theorem word_ginv19_mul : word 10248187242686185485 0 * gen ^ 19 = 1 := by
  rw [show gen ^ 19 = ofK (K.ofBits 524288) by rw [← word_two_pow (a := 19) (by decide)]; exact word_eOfNat _,
    show word 10248187242686185485 0 = ofK (K.ofBits 10248187242686185485) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 10248187242686185485 * K.ofBits 524288 = 1 by decide +kernel, ofK_one]

/-- A pointer width's selector, `g_w·g^-19 = g^(w - 19)`. -/
theorem sel19 {σ : Val} {x k : ℕ} {w : ℕ} (hw : 19 ≤ w) (h409 : σ (.n 409) = gen ^ w)
    (hk : σ (.n k) = word 10248187242686185485 0) (hm : σ (.n x) = σ (.n 409) * σ (.n k)) :
    σ (.n x) = gen ^ (w - 19) := by
  rw [hm, h409, hk, show gen ^ w = gen ^ (w - 19) * gen ^ 19 by rw [← pow_add, Nat.sub_add_cancel hw],
    mul_assoc, mul_comm (gen ^ 19), word_ginv19_mul, mul_one]

theorem seNames_length : seNames.length = 6 := rfl
theorem isNames_length : isNames.length = 6 := rfl
theorem ltNames_length : ltNames.length = 6 := rfl
theorem tpNames_length : tpNames.length = 25 := rfl
theorem opsNames_length : opsNames.length = 41 := rfl

theorem readsAt_take {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) (n : ℕ) :
    ReadsAt rd p (l.take n) := fun k hk ↦ by
  simp only [List.length_take] at hk
  rw [List.getElem_take]
  exact h k (by omega)

theorem bitsE_take (n w v : ℕ) (h : w ≤ v) : bitsE n w = (bitsE n v).take w := by
  simp only [bitsE, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem linkDrawn_ge {layout : Layout} (h : layout.tables = tables) (c : Chunks) :
    88 ≤ linkDrawn layout c := by
  have h1 : (tables.map (·.links.memory.length)).sum = 39 := by decide +kernel
  have h2 : (tables.map fun x ↦ x.links.pointers.length).sum = 33 := by decide +kernel
  simp only [linkDrawn, packedChallenges, h, h1, h2, nTables, bytecodeSlotBits]
  omega

theorem tailNValues_le {layout : Layout} (h : layout.tables = tables) : tailNValues layout ≤ 144 := by
  unfold tailNValues
  rw [h]
  decide +kernel

theorem splitColumns_len : (splitColumns tables).length = 36 := by decide +kernel

/-! ## The facts -/

theorem vsLinkFactsOfRun : VsLinkFactsOfRun := by
  intro bytecode κ L C V σ rets c p r chi qPoint message R S hc hp hp64 hpd hr hrl hchi hchil hq hql
    hm hml layout drawn fresh splitv
  have hsec : (vsPre.drop 487).take 2419 = linkSec := stmtsEqb_sound (by decide +kernel)
  have hA : ∀ a, Stmt.atom a ∈ linkSec → a.Holds L.read σ := fun a ha ↦ R.atom_in hsec ha
  have hcw : c.width = linkWidth layout := chunks_width hc
  have hgD : σ (.n 484) = gen ^ c.d := by
    obtain ⟨c', hc', hd'⟩ := S.chunks
    rw [hc] at hc'
    rw [hd', Option.some.inj hc']
  have hgMem : σ (.n 101) = gen ^ layout.logMemory := R.sizesOk.logMem
  have hw1 : 19 ≤ linkWidth layout := S.widthGe
  have hw2 : linkWidth layout ≤ 24 := S.widthLe
  have hdl : drawn.length = linkDrawn layout c := by
    show (List.take _ _).length = _
    rw [List.length_take, pkSqueeze_length]
    exact Nat.min_eq_left hpd
  have h750 : σ (.n 750) = word 10248187242686185485 0 := R.atom (a := .const (.n 750) (word 10248187242686185485 0)) (by decide +kernel)
  have h751 : σ (.n 751) = σ (.n 409) * σ (.n 750) := R.atom (a := .mul (.n 751) (.n 409) (.n 750)) (by decide +kernel)
  have h795 : σ (.n 795) = word 10248187242686185485 0 := R.atom (a := .const (.n 795) (word 10248187242686185485 0)) (by decide +kernel)
  have h796 : σ (.n 796) = σ (.n 409) * σ (.n 795) := R.atom (a := .mul (.n 796) (.n 409) (.n 795)) (by decide +kernel)
  have h2892 : σ (.n 2892) = word 10248187242686185485 0 := R.atom (a := .const (.n 2892) (word 10248187242686185485 0)) (by decide +kernel)
  have h2893 : σ (.n 2893) = σ (.n 409) * σ (.n 2892) := R.atom (a := .mul (.n 2893) (.n 409) (.n 2892)) (by decide +kernel)
  have hs751 := sel19 hw1 S.gW h750 h751
  have hs796 := sel19 hw1 S.gW h795 h796
  have hs2893 := sel19 hw1 S.gW h2892 h2893
  refine ⟨hA, ⟨S.tablesEq, by rw [hdl]; exact linkDrawn_ge S.tablesEq c, rfl,
    by rw [wordsAt_length, splitColumns_len], hql, by rw [hml]; exact tailNValues_le S.tablesEq⟩, ?_, ?_⟩
  · refine
      { widthGe := by rw [hcw]; exact hw1
        widthLe := by rw [hcw]; exact hw2
        heightsLe := S.heightsLe
        rowsLe := S.rowsLe
        logMemoryLe := by rw [hcw]; exact S.logMemoryLe
        tableRowsLe := S.tableRowsLe
        gN := S.gN
        gW := by rw [hcw]; exact S.gW
        gMem := hgMem
        gH := S.gH
        bitsPtr := S.bitsPtr
        rowBits := S.rowBits
        cycleBits := by rw [hcw, bitsE_take _ _ 24 hw2]; exact readsAt_take S.cycleBits _
        squeeze := R.hle _ _ _ (R.call (f := "squeeze_packed")
          (args := [.n 575, .n 576, .n 577, .n 578, .n 579, .n 679, .n 645])
          (rs := [.n 680, .n 681, .n 682, .n 683, .n 684]) (by decide +kernel))
        stateEnds := by
          rw [hcw]
          exact disp_rel R (x := 751) (fs := seNames) (args := [.n 694, .n 8]) (rs := [.n 752, .n 753])
            (by decide +kernel) (by decide) (by rw [seNames_length]; omega) hs751
        indexSide := by
          rw [hcw]
          exact disp_rel R (x := 796) (fs := isNames) (args := [.n 12, .n 694, .n 13])
            (rs := [.n 797, .n 798, .n 799]) (by decide +kernel) (by decide) (by rw [isNames_length]; omega) hs796
        tablePoint := by
          intro t ht
          have hh : layout.tableLogHeights.getD t 0 ≤ 24 := (S.heightsLe t ht).trans S.rowsLe
          interval_cases t
          · exact disp_rel R (x := 115) (fs := tpNames) (args := [.n 1293, .n 1295, .n 15, .n 7])
              (rs := [.n 1296, .n 1297, .n 1298]) (by decide +kernel) (by decide) (by rw [tpNames_length]; omega)
              (S.gH 0 (by norm_num))
          · exact disp_rel R (x := 116) (fs := tpNames) (args := [.n 1403, .n 1405, .n 15, .n 1407])
              (rs := [.n 1408, .n 1409, .n 1410]) (by decide +kernel) (by decide) (by rw [tpNames_length]; omega)
              (S.gH 1 (by norm_num))
          · exact disp_rel R (x := 117) (fs := tpNames) (args := [.n 1524, .n 1526, .n 15, .n 1528])
              (rs := [.n 1529, .n 1530, .n 1531]) (by decide +kernel) (by decide) (by rw [tpNames_length]; omega)
              (S.gH 2 (by norm_num))
          · exact disp_rel R (x := 118) (fs := tpNames) (args := [.n 1607, .n 1609, .n 15, .n 1611])
              (rs := [.n 1612, .n 1613, .n 1614]) (by decide +kernel) (by decide) (by rw [tpNames_length]; omega)
              (S.gH 3 (by norm_num))
          · exact disp_rel R (x := 119) (fs := tpNames) (args := [.n 1734, .n 1736, .n 15, .n 1738])
              (rs := [.n 1739, .n 1740, .n 1741]) (by decide +kernel) (by decide) (by rw [tpNames_length]; omega)
              (S.gH 4 (by norm_num))
          · exact disp_rel R (x := 120) (fs := tpNames) (args := [.n 1880, .n 1882, .n 15, .n 1884])
              (rs := [.n 1885, .n 1886, .n 1887]) (by decide +kernel) (by decide) (by rw [tpNames_length]; omega)
              (S.gH 5 (by norm_num))
        suffixes := disp_rel R (x := 408) (fs := opsNames) (args := [.n 18, .n 15]) (rs := [.n 1286])
          (by decide +kernel) (by decide) (by rw [opsNames_length]; have : linkRows layout ≤ 24 := S.rowsLe; omega) S.gN
        theta := rfl
        count := hp
        countLt := hp64
        drawnEq := rfl
        drawnLe := hpd
        point := hr
        pointLen := by rw [hrl, hcw]
        memTerm := rdw_of_load (R.load (d := 779) (p := 772) (off := 0) (by decide +kernel))
        freshEq := rfl
        rowPoint := hchi
        rowPointLen := hchil
        qPointAt := hq
        splitAt := fun k hk ↦ by
          show rdw L.read (σ (.n 14)) k = (wordsAt L.read (σ (.n 14)) 36).getD k 0
          rw [wordsAt, getD_range_map _ hk]
          rfl
        messageAt := fun k hk ↦ by
          rw [getD_eq_getElem' (by omega)]
          exact rdw_of_load (hm k (by omega)) }
  · refine
      { chunksEq := by rw [hcw]; exact hc
        terminal := by
          rw [hcw]
          exact disp_rel R (x := 2893) (fs := ltNames)
            (args := [.n 12, .n 1076, .n 2846, .n 19, .n 2891, .n 695, .n 2890, .n 1077]) (rs := [.n 2894])
            (by decide +kernel) (by decide) (by rw [ltNames_length]; omega) hs2893
        claimEq := rfl
        messageLen := hml
        slices := fun k hk ↦ by
          rw [getD_eq_getElem' (by omega)]
          exact hm (80 + k) (by omega) }

end

end LeanVM.Guest.B1.VerifySub
