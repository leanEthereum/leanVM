/-
  LeanVM.Guest.B1.VerifySub.PhLinkSpine

  `verify_sub`'s link section, its transcript: the moves of `verify_link` (`linkSkeleton`) from
  the words the section reads, against its callees' meanings.
-/

module

public import LeanVM.Guest.B1.VerifySub.PhLinkShape
public import LeanVM.Guest.B1.VerifySub.PhLinkRun
public import LeanVM.Guest.B1.VerifySub.PhOodRingGrind
public import LeanVM.Guest.B1.VerifySub.Keccak
public import LeanVM.Guest.B1.Fs.MessageComplete
public import LeanVM.Guest.B1.Link.RowSide
public import LeanVM.Guest.B1.Link.RoundsMain
public import LeanVM.Guest.B1.Link.PackedMessage
public import LeanVM.Guest.B1.Link.Arith.Check
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»
import Mathlib.Tactic.IntervalCases

/-!
# The link's transcript

The section's statements that move the transcript, as templates checked by the kernel: the
out-of-domain value's message with the link grind's nonce (`vsLkOmT`, `485 .. 487`), the inline
`grind_check` of `LINK_GRIND_BITS = 2` (`488 .. 536`), the packed count's `vanish` check and
`squeeze_packed` (`vsLkVanishT`, `537 .. 574`), `link_rounds` over the index point, `m1` and the
fresh coefficients' permutation (`vsLkIdxT`, `684 .. 695`), the `link_row_side` dispatch
(`vsLkRowT`, `963 .. 969`), `packed_message` (`vsLkMsgT`, `1303`).

`linkTailR_eq`: `linkTail`, its `let`s named (`linkTailR`), is the packed read, the terminal
check `tailLast = claim` and the end `lkEnd`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Link LeanVM.Guest.B1.Link LeanVM.Guest.B1.Link.Arith

@[expose] public section

/-- `verify_sub`'s statements 485 to 487. -/
def vsLkOmT : List Stmt := (
  .atom (.const (.n 571) (word 2048 0)) ::
  .atom (.mul (.n 572) (.n 55) (.n 571)) ::
  .call "opening_message__L1_L1" [.n 566, .n 567, .n 568, .n 569, .n 570, .n 572, .n 23] [.n 573, .n 574, .n 575, .n 576, .n 577, .n 578, .n 579, .n 580] ::
  [])

theorem vsLkOmT_eq : (vsPre.drop 485).take 3 = vsLkOmT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 537 to 574. -/
def vsLkVanishT : List Stmt := (
  .atom (.load (.n 645) (.n 9) 3) ::
  .atom (.mul (.n 646) (.n 645) (.n 645)) ::
  .atom (.mul (.n 647) (.n 646) (.n 646)) ::
  .atom (.mul (.n 648) (.n 647) (.n 647)) ::
  .atom (.const (.n 649) (word 452984832 0)) ::
  .atom (.mul (.n 650) (.n 408) (.n 649)) ::
  .atom (.mul (.n 651) (.n 650) (.n 409)) ::
  .atom (.mul (.n 652) (.n 651) (.n 484)) ::
  .atom (.mul (.n 648) (.n 653) (.n 652)) ::
  .atom (.const (.n 654) (word 1 0)) ::
  .atom (.add (.n 655) (.n 653) (.n 654)) ::
  .atom (.const (.n 656) (word 2 0)) ::
  .atom (.add (.n 657) (.n 653) (.n 656)) ::
  .atom (.mul (.n 658) (.n 655) (.n 657)) ::
  .atom (.const (.n 659) (word 4 0)) ::
  .atom (.add (.n 660) (.n 653) (.n 659)) ::
  .atom (.mul (.n 661) (.n 658) (.n 660)) ::
  .atom (.const (.n 662) (word 8 0)) ::
  .atom (.add (.n 663) (.n 653) (.n 662)) ::
  .atom (.mul (.n 664) (.n 661) (.n 663)) ::
  .atom (.const (.n 665) (word 16 0)) ::
  .atom (.add (.n 666) (.n 653) (.n 665)) ::
  .atom (.mul (.n 667) (.n 664) (.n 666)) ::
  .atom (.const (.n 668) (word 32 0)) ::
  .atom (.add (.n 669) (.n 653) (.n 668)) ::
  .atom (.mul (.n 670) (.n 667) (.n 669)) ::
  .atom (.const (.n 671) (word 64 0)) ::
  .atom (.add (.n 672) (.n 653) (.n 671)) ::
  .atom (.mul (.n 673) (.n 670) (.n 672)) ::
  .atom (.const (.n 674) (word 128 0)) ::
  .atom (.add (.n 675) (.n 653) (.n 674)) ::
  .atom (.mul (.n 676) (.n 673) (.n 675)) ::
  .atom (.const (.n 677) (word 0 0)) ::
  .atom (.assertEq (.n 676) (.n 677)) ::
  .atom (.load (.n 573) (.n 10) 0) ::
  .atom (.const (.n 678) (word 2 0)) ::
  .atom (.mul (.n 679) (.n 10) (.n 678)) ::
  .call "squeeze_packed" [.n 575, .n 576, .n 577, .n 578, .n 579, .n 679, .n 645] [.n 680, .n 681, .n 682, .n 683, .n 684] ::
  [])

theorem vsLkVanishT_eq : (vsPre.drop 537).take 38 = vsLkVanishT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 684 to 695. -/
def vsLkIdxT : List Stmt := (
  .atom (.const (.n 765) (word 365917469723852800 0)) ::
  .atom (.mul (.n 766) (.n 4) (.n 765)) ::
  .call "link_rounds__L1_L0" [.n 680, .n 681, .n 682, .n 683, .n 684, .n 580, .n 764, .n 12, .n 409, .n 766] [.n 767, .n 768, .n 769, .n 770, .n 771, .n 772, .n 773] ::
  .atom (.copy (.n 774) (.n 767)) ::
  .atom (.copy (.n 775) (.n 768)) ::
  .atom (.copy (.n 776) (.n 769)) ::
  .atom (.copy (.n 777) (.n 770)) ::
  .atom (.copy (.n 778) (.n 771)) ::
  .atom (.load (.n 779) (.n 772) 0) ::
  .atom (.copy (.n 780) (.n 779)) ::
  .atom (.const (.n 781) (word 0 1)) ::
  .atom (.keccak [.n 780, .n 781, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 774, .n 775, .n 776, .n 777, .n 778] [.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792, .n 793, .n 794] false false) ::
  [])

theorem vsLkIdxT_eq : (vsPre.drop 684).take 12 = vsLkIdxT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 963 to 969. -/
def vsLkRowT : List Stmt := (
  .atom (.const (.n 1065) (word 2 0)) ::
  .atom (.mul (.n 1066) (.n 772) (.n 1065)) ::
  .atom (.const (.n 1067) (word 365917469723852800 0)) ::
  .atom (.mul (.n 1068) (.n 4) (.n 1067)) ::
  .atom (.const (.n 1069) (word 2017612633061982209 0)) ::
  .atom (.mul (.n 1070) (.n 484) (.n 1069)) ::
  .dispatch (.n 1070) ["link_row_side__L6", "link_row_side__L7", "link_row_side__L8", "link_row_side__L9"] [.n 790, .n 791, .n 792, .n 793, .n 794, .n 1066, .n 773, .n 15, .n 16, .n 408, .n 1068] [.n 1071, .n 1072, .n 1073, .n 1074, .n 1075, .n 1076, .n 1077] ::
  [])

theorem vsLkRowT_eq : (vsPre.drop 963).take 7 = vsLkRowT := stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 1303 to 1303. -/
def vsLkMsgT : List Stmt := (
  .call "packed_message__L144" [.n 1071, .n 1072, .n 1073, .n 1074, .n 1075, .n 1076] [.n 1287, .n 1288, .n 1289, .n 1290, .n 1291, .n 1292] ::
  [])

theorem vsLkMsgT_eq : (vsPre.drop 1303).take 1 = vsLkMsgT := stmtsEqb_sound (by decide +kernel)

theorem vsLkGrindT_eq : (vsPre.drop 488).take 49 = gcInlineAt 2 581 178 (.n 574) (.n 4) :=
  stmtsEqb_sound (by decide +kernel)

/-- `verify_sub`'s statements 19 to 22: the zero cells. -/
def vsZeroT : List Stmt :=
  [.atom (.const (.n 25) (word 0 0)), .atom (.const (.n 26) (word 0 0)),
    .atom (.const (.n 27) (word 0 0)), .atom (.const (.n 28) (word 0 0))]

theorem vsZeroT_eq : (vsPre.drop 19).take 4 = vsZeroT := stmtsEqb_sound (by decide +kernel)

/-! ## Constants -/

theorem winv6_mul : word 2017612633061982209 0 * gen ^ 6 = 1 := by
  rw [show gen ^ 6 = ofK (K.ofBits 64) by
      rw [← word_two_pow (a := 6) (by decide)]; exact word_eOfNat _,
    show word 2017612633061982209 0 = ofK (K.ofBits 2017612633061982209) from word_eOfNat _,
    ← ofK_mul, show K.ofBits 2017612633061982209 * K.ofBits 64 = 1 by decide +kernel, ofK_one]

set_option maxRecDepth 100000 in
theorem word_g144 : word 21299200 0 = gen ^ 144 := by
  rw [← gpow, ← gpowE_eq_gpow (by decide)]
  decide +kernel

/-! ## `linkTail`, as a read, a check and an end -/

section Tail

variable (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E) (m1 : E)
  (fresh : List E) (split : Split) (chi qPoint message : List E) (claim : E)

/-- The summand `linkTail` checks against the claim (`TailCheck`'s left side). -/
def tailLast : E :=
  let L := tailLets layout chunks theta0 drawn r m1 fresh split qPoint
  let maxShift := layout.tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  let nValues := tailNValues layout
  let slices := message.drop nValues
  let rowSide := tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message
  let functionals := Functionals.new chunks r maxShift
  let values := functionals.values chunks slices
  let eq0Q := prodE (qPoint.map (1 + ·))
  let certs := L.nu.map fun n ↦ L.cert * rowSide.certWeight * n
  functionals.summand rowSide.coef rowSide.shifts values certs + eq0Q * rowSide.base

/-- The `LinkEnd` `linkTail` returns. -/
def lkEnd : LinkEnd :=
  let L := tailLets layout chunks theta0 drawn r m1 fresh split qPoint
  let nValues := tailNValues layout
  let slices := message.drop nValues
  let rowSide := tailRowSide layout chunks theta0 drawn r m1 fresh split chi qPoint message
  { memoryPoint := r.take layout.logMemory
    memoryScales := (L.belowMem, eY * L.belowMem)
    memoryValue := m1
    columns := rowSide.columns
    ring := ⟨rowSide.pieces, slices⟩
    bytecodePoint := r.take layout.logBytecode }

theorem tailCheck_iff :
    TailCheck layout chunks theta0 drawn r m1 fresh split chi qPoint message claim ↔
      tailLast layout chunks theta0 drawn r m1 fresh split chi qPoint message = claim := Iff.rfl

theorem linkTailR_eq :
    linkTailR layout chunks theta0 drawn r m1 fresh split chi qPoint claim =
      (VerifierProgram.readScalarsPacked (tailNValues layout + kBits) >>= fun message ↦
        VerifierProgram.require
            (tailLast layout chunks theta0 drawn r m1 fresh split chi qPoint message = claim) >>=
          fun _ ↦ pure (lkEnd layout chunks theta0 drawn r m1 fresh split chi qPoint message)) := rfl

end Tail

theorem tailNValues_tables {layout : Layout} (h : layout.tables = tables) : tailNValues layout = 80 := by
  unfold tailNValues
  simp only [h]
  decide +kernel

/-- **`linkTail` runs** on the message, when its check passes. -/
theorem runsTo_linkTail {layout : Layout} (htab : layout.tables = tables) (chunks : Chunks) (theta0 : E)
    (drawn r : List E) (m1 : E) (fresh : List E) (split : Split) (chi qPoint : List E) (claim : E)
    (cap message : List E) (hl : message.length = 144)
    (h : TailCheck layout chunks theta0 drawn r m1 fresh split chi qPoint message claim) :
    RunsTo (linkTail layout chunks theta0 drawn r m1 fresh split chi qPoint claim) ⟨cap, []⟩ message
      (lkEnd layout chunks theta0 drawn r m1 fresh split chi qPoint message)
      ⟨pkAbsorb 18 message cap, []⟩ := by
  rw [linkTailEq, linkTailR_eq, tailNValues_tables htab, show 80 + kBits = 8 * 18 from rfl]
  have h1 := runsTo_readPacked cap message (b := 18) hl
  have h2 := (lkRunsTo_require ((tailCheck_iff ..).mp h) ⟨pkAbsorb 18 message cap, []⟩).bind
    (f := fun _ ↦ pure (lkEnd layout chunks theta0 drawn r m1 fresh split chi qPoint message))
    (runsTo_ret _ _)
  have h3 := RunsTo.bind (f := fun message ↦ VerifierProgram.require
      (tailLast layout chunks theta0 drawn r m1 fresh split chi qPoint message = claim) >>=
        fun _ ↦ pure (lkEnd layout chunks theta0 drawn r m1 fresh split chi qPoint message)) h1 h2
  exact RunsTo.of_eq h3 rfl (by simp) rfl rfl

/-! ## The front: the link grind, `θ_0`, the drawn challenges -/

/-- The challenges the link draws after `θ_0`: the first `linkDrawn` cells of `p` permutations. -/
def lkDrawn (bytecode : List K) (σ : Val) (c : Chunks) (p : ℕ) : List E :=
  ((pkSqueeze p [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579)]).1).take
    (linkDrawn (vsLayout bytecode σ) c)

theorem pow8 (x : E) (p : ℕ) (h : x = gen ^ p) : x * x * (x * x) * (x * x * (x * x)) = gen ^ (8 * p) := by
  rw [h, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring

/-- One of eight factors `x + g^j` vanishes. -/
theorem vanish_of {x : E} {a1 a2 a3 a4 a5 a6 a7 a8 : E}
    (e1 : a1 = x + 1) (e2 : a2 = x + gen ^ 1) (e3 : a3 = x + gen ^ 2) (e4 : a4 = x + gen ^ 3)
    (e5 : a5 = x + gen ^ 4) (e6 : a6 = x + gen ^ 5) (e7 : a7 = x + gen ^ 6) (e8 : a8 = x + gen ^ 7)
    (h : a1 * a2 * a3 * a4 * a5 * a6 * a7 * a8 = 0) : ∃ j < 8, x = gen ^ j := by
  have z : ∀ {k : ℕ}, x + gen ^ k = 0 → x = gen ^ k := fun h ↦ eq_of_add_zero h
  rcases mul_zero_cases h with h | h
  · rcases mul_zero_cases h with h | h
    · rcases mul_zero_cases h with h | h
      · rcases mul_zero_cases h with h | h
        · rcases mul_zero_cases h with h | h
          · rcases mul_zero_cases h with h | h
            · rcases mul_zero_cases h with h | h
              · exact ⟨0, by norm_num, z (by rw [pow_zero, ← e1, h])⟩
              · exact ⟨1, by norm_num, z (by rw [← e2, h])⟩
            · exact ⟨2, by norm_num, z (by rw [← e3, h])⟩
          · exact ⟨3, by norm_num, z (by rw [← e4, h])⟩
        · exact ⟨4, by norm_num, z (by rw [← e5, h])⟩
      · exact ⟨5, by norm_num, z (by rw [← e6, h])⟩
    · exact ⟨6, by norm_num, z (by rw [← e7, h])⟩
  · exact ⟨7, by norm_num, z (by rw [← e8, h])⟩

theorem word_pow2 {a : ℕ} (h : a < 64) : word (2 ^ a) 0 = gen ^ a := word_two_pow h

set_option maxHeartbeats 1000000 in
/-- **The link's front**: the grind's nonce at `stream·g^12` passes on `vsF3`, its permutation
gives `θ_0 = σ573` and the capacity `σ575 ..`; `g^p` at `link_shape[3]` draws `linkDrawn`
challenges (`8 (p - 1) < linkDrawn ≤ 8 p`) by `squeeze_packed`, its capacity `σ680 ..`. -/
theorem VsRun.linkFront {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap}
    {σ : Val} {rets : List E} (R : VsRun bytecode L C V σ rets) {c : Chunks}
    (hc : Chunks.new (linkWidth (vsLayout bytecode σ)) = some c) :
    ∃ (nn : E) (p : ℕ), LoadHolds L.read (vsStream σ) 12 nn ∧ σ (.n 580) = vsStream σ * gen ^ 13 ∧
      σ (.n 645) = gen ^ p ∧ p < 64 ∧ 8 * p - 8 < linkDrawn (vsLayout bytecode σ) c ∧
      linkDrawn (vsLayout bytecode σ) c ≤ 8 * p ∧
      ReadsAt L.read (σ (.n 679)) (pkSqueeze p [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579)]).1 ∧
      [σ (.n 680), σ (.n 681), σ (.n 682), σ (.n 683), σ (.n 684)] =
        (pkSqueeze p [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579)]).2 ∧
      RunsToG (VerifierProgram.grindProofOfWork 2) (vsF3 L.read σ) [nn] ()
        [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579)] (σ (.n 573)) := by
  have Sh := R.shapeOk
  obtain ⟨-, hwin, h11⟩ := R.pre
  -- the message and the nonce
  have hO := R.slice vsLkOmT_eq
  simp only [vsLkOmT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hO
  obtain ⟨o571, o572, hom, -⟩ := hO
  have hM := (opening_message_holds (1, 1) (by decide) L.read _ _).mp (R.hle _ _ _ hom)
  simp only [MeaningOpeningMessage] at hM
  obtain ⟨vs, hvl, -, hvo, nn, hnn, hrets⟩ := hM
  obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
    match vs, hvl with
    | [v], _ => exact ⟨v, rfl⟩
  have e572 : σ (.n 572) = vsStream σ * gen ^ 11 := by
    rw [o572, o571, show (2048 : ℕ) = 2 ^ 11 from rfl, gen_word 11 (by decide)]
    rfl
  have hv : vsOodValue L.read σ = v := by
    have := wordsAt_eq hvo
    simp only [List.length_cons, List.length_nil] at this
    simp only [vsOodValue, this]
    rfl
  have hF3 : ((⟨[σ (.n 566), σ (.n 567), σ (.n 568), σ (.n 569), σ (.n 570)], []⟩ : Fs).absorbAll [v]
      dsObserve) = vsF3 L.read σ := by
    rw [absorbAll_short _ _ _ (by simp)]
    simp only [vsF3, hv]
    rfl
  simp only [omState, ↓reduceIte, hF3] at hrets
  set S := (vsF3 L.read σ).nonceState nn with hS
  simp only [capOf, List.cons_append, List.nil_append, List.cons.injEq] at hrets
  obtain ⟨r573, r574, r575, r576, r577, r578, r579, r580, -⟩ := hrets
  have hcap : [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579)] = capOf S := by
    rw [r575, r576, r577, r578, r579]; rfl
  -- the grind
  have hG := R.slice vsLkGrindT_eq
  obtain ⟨hpow, -⟩ := gcInlineAt_sound R.hκ h11 L (by decide) (winTabs_of_expWinTab hwin) hG
  have hok : (vsF3 L.read σ).GrindOk 2 nn :=
    (grindOk_iff (by decide) nn).mpr (by rw [← hS, ← r574]; exact hpow)
  have hrunG := runsToG_grind (by decide) (vsF3 L.read σ) nn (hok.resolve_left (by decide))
  rw [← hS, ← hcap, Keccak.challengeOf_cells, ← r573] at hrunG
  -- the count
  have hV := R.slice vsLkVanishT_eq
  simp only [vsLkVanishT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hV
  obtain ⟨-, v538, v539, v540, v541, v542, v543, v544, v545, v546, v547, v548, v549, v550, v551, v552,
    v553, v554, v555, v556, v557, v558, v559, v560, v561, v562, v563, v564, v565, v566, v567, v568, v569,
    v570, -, -, -, hsq, -⟩ := hV
  have M := Link.squeeze_packed_sound L.read _ _ (R.hle _ _ _ hsq)
  simp only [Link.MeaningSP] at M
  obtain ⟨p, hp, hcg, hread, hret⟩ := M
  have hj : ∃ j < 8, σ (.n 653) = gen ^ j := by
    have h0 : σ (.n 676) = 0 := by rw [eq_of_add_zero v570, v569, word_zero]
    rw [v568, v565, v562, v559, v556, v553, v550] at h0
    refine vanish_of (by rw [v547, v546, word_one]) (by rw [v549, v548, ← word_pow2 (by norm_num)]; rfl)
      (by rw [v552, v551, ← word_pow2 (by norm_num)]; rfl) (by rw [v555, v554, ← word_pow2 (by norm_num)]; rfl)
      (by rw [v558, v557, ← word_pow2 (by norm_num)]; rfl) (by rw [v561, v560, ← word_pow2 (by norm_num)]; rfl)
      (by rw [v564, v563, ← word_pow2 (by norm_num)]; rfl) (by rw [v567, v566, ← word_pow2 (by norm_num)]; rfl) h0
  obtain ⟨j, hj8, x653⟩ := hj
  have hcw := chunks_width hc
  have hcdle : 6 ≤ c.d ∧ c.d ≤ 9 := by
    have hall : ∀ w, 19 ≤ w → w ≤ 24 →
        ((Chunks.new w).map Chunks.d).all (fun x ↦ decide (6 ≤ x ∧ x ≤ 9)) = true := by
      intro w h1 h2; interval_cases w <;> decide +kernel
    have := hall _ Sh.widthGe Sh.widthLe
    rw [hc] at this
    simpa using this
  obtain ⟨c', hc', hcd⟩ := Sh.chunks
  rw [hc] at hc'
  obtain rfl : c = c' := Option.some.inj hc'
  have hN : linkDrawn (vsLayout bytecode σ) c = 88 + linkRows (vsLayout bytecode σ) + linkWidth
      (vsLayout bytecode σ) + c.d := by
    rw [linkDrawn_tables Sh.tablesEq, hcw, hc]; rfl
  have h652 : σ (.n 652) = gen ^ linkDrawn (vsLayout bytecode σ) c := by
    rw [v544, v543, v542, v541, word_g88, Sh.gN, Sh.gW, hcd, hN, ← pow_add, ← pow_add, ← pow_add]
    congr 1; ring
  have h8 : gen ^ (8 * p) = gen ^ (j + linkDrawn (vsLayout bytecode σ) c) := by
    rw [← pow8 _ p hcg, ← v538, ← v539, ← v540, v545, x653, h652, pow_add]
  have hrw := Sh.rowsLe
  have hww := Sh.widthLe
  have e8 := Digest.gen_pow_inj' (by omega) (by omega) h8
  refine ⟨nn, p, ?_, ?_, hcg, hp, by omega, by omega, hread, hret, hrunG⟩
  · have := (loadHolds_mul_gen_pow _ _ _ _ _).mp (e572 ▸ hnn trivial)
    simpa using this
  · rw [r580, e572, mul_assoc, ← pow_add]

/-! ## The index side's rounds, `m1`, the fresh coefficients -/

set_option maxHeartbeats 1000000 in
/-- **The index point**: `link_rounds` runs the index side's sum-check from the capacity
`σ680 ..` and the claim `σ764`, its challenges at `r_pt`, leaving the cursor `σ772` and the claim
`σ773`; `m1` is the word there, read, and the five fresh coefficients are cells `0 .. 4` of the
permutation taking it. -/
theorem VsRun.linkIdx {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap}
    {σ : Val} {rets : List E} (R : VsRun bytecode L C V σ rets) :
    ∃ (l : List (E × RSt)) (ws : List E), l.length = linkWidth (vsLayout bytecode σ) ∧
      ReadsAt L.read (σ (.n 12)) (l.map Prod.fst) ∧ ReadsAt L.read (σ (.n 580)) ws ∧
      σ (.n 772) = σ (.n 580) * gen ^ ws.length ∧
      RunsTo (sumcheck (σ (.n 764)) 3 (List.replicate (linkWidth (vsLayout bytecode σ)) none))
        ⟨[σ (.n 680), σ (.n 681), σ (.n 682), σ (.n 683), σ (.n 684)], []⟩ ws
        (l.map Prod.fst, σ (.n 773)) ⟨[σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)], []⟩ ∧
      LoadHolds L.read (σ (.n 772)) 0 (σ (.n 779)) ∧
      RunsTo (VerifierProgram.sampleChallengesPacked 5)
        ⟨[σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)], [(σ (.n 779), dsObserve)]⟩ []
        [σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785), σ (.n 786)]
        ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)], []⟩ := by
  have Sh := R.shapeOk
  have hI := R.slice vsLkIdxT_eq
  simp only [vsLkIdxT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hI
  obtain ⟨-, -, hlr, i3, i4, i5, i6, i7, i8, i9, i10, i11, -⟩ := hI
  simp only [Atom.Holds] at i3 i4 i5 i6 i7 i8 i9 i10
  have hZ := R.slice vsZeroT_eq
  simp only [vsZeroT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hZ
  obtain ⟨z25, z26, z27, z28, -⟩ := hZ
  -- the rounds
  have M := Link.link_rounds_L1_L0_sound L.read (fun h ↦ absurd rfl h) _ _ (R.hle _ _ _ hlr)
  simp only [Link.MeaningLR] at M
  obtain ⟨cnt, hcnt, hcg, hch⟩ := M
  obtain ⟨l, hll, hchain, hpt, hret⟩ := hch (fun h ↦ absurd rfl h)
  have hcw : cnt = linkWidth (vsLayout bytecode σ) := by
    have := Sh.widthLe
    exact Digest.gen_pow_inj' (by omega) (by omega) (hcg.symm.trans Sh.gW)
  obtain ⟨ws, hws, hcur, hrun⟩ := chain_runsTo gb2 hchain
  have h5 := chainLast_cap_length (rd := L.read) (nt := 1) (bits := 0) rfl hchain
  obtain ⟨a, b, c, d, e, u, v, hcells, hst⟩ := cells_eq_seven h5
  rw [hcells] at hret
  simp only [List.cons.injEq] at hret
  obtain ⟨ra, rb, rc, rd, re, ru, rv, -⟩ := hret
  rw [hst] at hcur hrun
  simp only at hcur hrun
  -- the fresh permutation
  set s1 : Fs := ⟨[σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)], [(σ (.n 779), dsObserve)]⟩
  have hK := keccakA_fs (s := s1) i11 (by simp [s1]) (by
    simp only [List.map_cons, List.map_nil, s1, i3, i4, i5, i6, i7, i9, i10, z25, z26, z27, z28]
    rfl)
  have hc : ∀ k : Fin 13, ∀ hk : k.val < 13,
      σ ([.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792,
        .n 793, .n 794] : List Core.V)[k.val] = cellsOfState s1.perm false k :=
    fun k hk ↦ outs_eq hK k (by simp)
  have hfr := runsTo_samplePacked5 s1
  have e1 : (List.range 5).map (Link.cellAt s1.perm) =
      [σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785), σ (.n 786)] := by
    have hcell : ∀ i (h : i < 13), Link.cellAt s1.perm i = cellsOfState s1.perm false ⟨i, h⟩ :=
      fun i h ↦ by simp [Link.cellAt, h]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append]
    rw [hcell 0 (by decide), hcell 1 (by decide), hcell 2 (by decide), hcell 3 (by decide),
      hcell 4 (by decide), ← hc ⟨0, by decide⟩ (by decide), ← hc ⟨1, by decide⟩ (by decide),
      ← hc ⟨2, by decide⟩ (by decide), ← hc ⟨3, by decide⟩ (by decide), ← hc ⟨4, by decide⟩ (by decide)]
    rfl
  have e2 : capOf s1.perm = [σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)] := by
    simp only [capOf]
    rw [← hc 8 (by decide), ← hc 9 (by decide), ← hc 10 (by decide), ← hc 11 (by decide),
      ← hc 12 (by decide)]
    rfl
  rw [e1, e2] at hfr
  refine ⟨l, ws, by rw [hll, hcw], hpt, hws, by rw [ru]; exact hcur, ?_, i8, hfr⟩
  rw [hll, hcw] at hrun
  rw [← ra, ← rb, ← rc, ← rd, ← re, ← rv] at hrun
  exact hrun

/-! ## The row side and the message -/

/-- **A `link_row_side` arm runs** the row and pointer-column sum-checks at `d`'s coefficients. -/
theorem rowSide_runs {rd : Reader} {nt1 b1 nt2 b2 d : ℕ} (h1 : nt1 = d + 1) (h2 : nt2 = d) (hd : 2 ≤ d)
    (g1 : grindingBits (nt1 + 1) = b1) (g2 : grindingBits (nt2 + 1) = b2)
    {f0 f1 f2 f3 f4 cur cl chi qp gn tabs : E} {rets : List E} (hw : WinTabs rd tabs)
    (hM : MeaningLRS nt1 b1 nt2 b2 rd [f0, f1, f2, f3, f4, cur, cl, chi, qp, gn, tabs] rets) :
    ∃ n < 64, gn = gen ^ n ∧ ∃ (l1 l2 : List (E × RSt)) (ws1 ws2 : List E),
      l1.length = n ∧ l2.length = 6 ∧ ReadsAt rd chi (l1.map Prod.fst) ∧
      ReadsAt rd qp (l2.map Prod.fst) ∧ ReadsAt rd cur ws1 ∧ ReadsAt rd (cur * gen ^ ws1.length) ws2 ∧
      rets = (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cells ∧
      (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cur =
        cur * gen ^ (ws1.length + ws2.length) ∧
      (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cap.length = 5 ∧
      RunsTo (sumcheck cl (roundCoefficients d).1 (List.replicate n none)) ⟨[f0, f1, f2, f3, f4], []⟩ ws1
        (l1.map Prod.fst, (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cl)
        ⟨(chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cap, []⟩ ∧
      RunsTo (sumcheck (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cl (roundCoefficients d).2
          (List.replicate 6 none))
        ⟨(chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cap, []⟩ ws2
        (l2.map Prod.fst, (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cl)
        ⟨(chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cap, []⟩ := by
  simp only [MeaningLRS] at hM
  obtain ⟨n, hn, hgn, hch⟩ := hM
  obtain ⟨l1, l2, hl1, hl2, hc1, hc2, hr1, hr2, hret⟩ := hch (fun _ ↦ hw)
  obtain ⟨ws1, hw1, hcur1, hrun1⟩ := chain_runsTo g1 hc1
  obtain ⟨ws2, hw2, hcur2, hrun2⟩ := chain_runsTo g2 hc2
  have e1 : (roundCoefficients d).1 = nt1 + 2 := by
    simp only [roundCoefficients, Nat.max_def]; split_ifs <;> omega
  have e2 : (roundCoefficients d).2 = nt2 + 2 := by
    simp only [roundCoefficients, Nat.max_def]; split_ifs <;> omega
  rw [e1, e2]
  refine ⟨n, hn, hgn, l1, l2, ws1, ws2, hl1, hl2, hr1, hr2, hw1, by rw [← hcur1]; exact hw2, hret,
    by rw [hcur2, hcur1, mul_assoc, ← pow_add], chainLast_cap_length (chainLast_cap_length rfl hc1) hc2,
    by rw [← hl1]; exact hrun1, by rw [← hl2]; exact hrun2⟩

theorem rowArms {d : ℕ} (h : d - 6 < 4) (h6 : 6 ≤ d) :
    d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega

set_option maxHeartbeats 1000000 in
/-- **The row side**: `link_row_side` at the chunks' `d` runs the row sum-check over
`linkRows` variables, its challenges at `chi`, then the pointer columns' over six at `q_point`,
from the fresh permutation's capacity, the cursor past `m1` and the claim `σ773`; it leaves the
capacity `σ1071 ..`, the cursor `σ1076` and the claim `σ1077`. -/
theorem VsRun.linkRow {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap}
    {σ : Val} {rets : List E} (R : VsRun bytecode L C V σ rets) {c : Chunks}
    (hc : Chunks.new (linkWidth (vsLayout bytecode σ)) = some c) :
    ∃ (l1 l2 : List (E × RSt)) (ws1 ws2 : List E) (cl1 : E) (cap1 : List E),
      l1.length = linkRows (vsLayout bytecode σ) ∧ l2.length = 6 ∧
      ReadsAt L.read (σ (.n 15)) (l1.map Prod.fst) ∧ ReadsAt L.read (σ (.n 16)) (l2.map Prod.fst) ∧
      ReadsAt L.read (σ (.n 772) * gen) ws1 ∧ ReadsAt L.read (σ (.n 772) * gen * gen ^ ws1.length) ws2 ∧
      σ (.n 1076) = σ (.n 772) * gen * gen ^ (ws1.length + ws2.length) ∧
      RunsTo (sumcheck (σ (.n 773)) (roundCoefficients c.d).1
          (List.replicate (linkRows (vsLayout bytecode σ)) none))
        ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)], []⟩ ws1 (l1.map Prod.fst, cl1)
        ⟨cap1, []⟩ ∧
      RunsTo (sumcheck cl1 (roundCoefficients c.d).2 (List.replicate 6 none)) ⟨cap1, []⟩ ws2
        (l2.map Prod.fst, σ (.n 1077))
        ⟨[σ (.n 1071), σ (.n 1072), σ (.n 1073), σ (.n 1074), σ (.n 1075)], []⟩ := by
  have Sh := R.shapeOk
  obtain ⟨-, hwin, h11⟩ := R.pre
  have hgc : GcSound1 L.read := gcSound1_image R.hκ h11 L
  obtain ⟨c', hc', hcd⟩ := Sh.chunks
  rw [hc] at hc'
  obtain rfl : c = c' := Option.some.inj hc'
  have hcdle : 6 ≤ c.d ∧ c.d ≤ 9 := by
    have hall : ∀ w, 19 ≤ w → w ≤ 24 →
        ((Chunks.new w).map Chunks.d).all (fun x ↦ decide (6 ≤ x ∧ x ≤ 9)) = true := by
      intro w h1 h2; interval_cases w <;> decide +kernel
    have := hall _ Sh.widthGe Sh.widthLe
    rw [hc] at this
    simpa using this
  have hW := R.slice vsLkRowT_eq
  simp only [vsLkRowT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hW
  obtain ⟨w0, w1, w2, w3, w4, w5, ⟨j, hj, hsel, hcall⟩, -⟩ := hW
  have hj4 : j < 4 := by simpa using hj
  have hjd : c.d = j + 6 := by
    have h1070 : σ (.n 1070) = gen ^ j := by rw [hsel, gen_pow_eq_ofK]
    have : gen ^ c.d = gen ^ (j + 6) := by
      rw [← hcd, pow_add, ← h1070, w5, w4, mul_assoc, winv6_mul, mul_one]
    exact Digest.gen_pow_inj' (by omega) (by omega) this
  have hwt : WinTabs L.read (σ (.n 1068)) := by
    rw [w3, w2, word_winTab]; exact winTabs_of_expWinTab hwin
  have hcur : σ (.n 1066) = σ (.n 772) * gen := by rw [w1, w0, word_gen]
  have hRS : ∃ n < 64, σ (.n 408) = gen ^ n ∧ ∃ (l1 l2 : List (E × RSt)) (ws1 ws2 : List E),
      l1.length = n ∧ l2.length = 6 ∧ ReadsAt L.read (σ (.n 15)) (l1.map Prod.fst) ∧
      ReadsAt L.read (σ (.n 16)) (l2.map Prod.fst) ∧ ReadsAt L.read (σ (.n 1066)) ws1 ∧
      ReadsAt L.read (σ (.n 1066) * gen ^ ws1.length) ws2 ∧
      [σ (.n 1071), σ (.n 1072), σ (.n 1073), σ (.n 1074), σ (.n 1075), σ (.n 1076), σ (.n 1077)] =
        (chainLast (chainLast ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)],
          σ (.n 1066), σ (.n 773)⟩ l1) l2).cells ∧
      (chainLast (chainLast ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)],
          σ (.n 1066), σ (.n 773)⟩ l1) l2).cur = σ (.n 1066) * gen ^ (ws1.length + ws2.length) ∧
      (chainLast (chainLast ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)],
          σ (.n 1066), σ (.n 773)⟩ l1) l2).cap.length = 5 ∧
      RunsTo (sumcheck (σ (.n 773)) (roundCoefficients c.d).1 (List.replicate n none))
        ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)], []⟩ ws1
        (l1.map Prod.fst, (chainLast ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)],
          σ (.n 1066), σ (.n 773)⟩ l1).cl)
        ⟨(chainLast ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)],
          σ (.n 1066), σ (.n 773)⟩ l1).cap, []⟩ ∧
      RunsTo (sumcheck (chainLast ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)],
          σ (.n 1066), σ (.n 773)⟩ l1).cl (roundCoefficients c.d).2 (List.replicate 6 none))
        ⟨(chainLast ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)],
          σ (.n 1066), σ (.n 773)⟩ l1).cap, []⟩ ws2
        (l2.map Prod.fst, (chainLast (chainLast ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793),
          σ (.n 794)], σ (.n 1066), σ (.n 773)⟩ l1) l2).cl)
        ⟨(chainLast (chainLast ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)],
          σ (.n 1066), σ (.n 773)⟩ l1) l2).cap, []⟩ := by
    interval_cases j
    · exact rowSide_runs (nt1 := 7) (nt2 := 6) (by omega) (by omega) (by omega) gb8 gb7 hwt
        (link_row_side_L6_sound L.read hgc _ _ (R.hle _ _ _ hcall))
    · exact rowSide_runs (nt1 := 8) (nt2 := 7) (by omega) (by omega) (by omega) gb9 gb8 hwt
        (link_row_side_L7_sound L.read hgc _ _ (R.hle _ _ _ hcall))
    · exact rowSide_runs (nt1 := 9) (nt2 := 8) (by omega) (by omega) (by omega) gb10 gb9 hwt
        (link_row_side_L8_sound L.read hgc _ _ (R.hle _ _ _ hcall))
    · exact rowSide_runs (nt1 := 10) (nt2 := 9) (by omega) (by omega) (by omega) gb11 gb10 hwt
        (link_row_side_L9_sound L.read hgc _ _ (R.hle _ _ _ hcall))
  obtain ⟨n, hn, hgn, l1, l2, ws1, ws2, hl1, hl2, hr1, hr2, hw1, hw2, hret, hcur2, h5, hrun1, hrun2⟩ := hRS
  have hnr : n = linkRows (vsLayout bytecode σ) := by
    have := Sh.rowsLe
    exact Digest.gen_pow_inj' (by omega) (by omega) (hgn.symm.trans Sh.gN)
  subst hnr
  obtain ⟨a, b, c0, d0, e, u, v, hcells, hst⟩ := cells_eq_seven h5
  rw [hcells] at hret
  simp only [List.cons.injEq] at hret
  obtain ⟨ra, rb, rc, rd, re, ru, rv, -⟩ := hret
  rw [hst] at hcur2 hrun2
  simp only at hcur2 hrun2
  rw [← ra, ← rb, ← rc, ← rd, ← re, ← rv] at hrun2
  refine ⟨l1, l2, ws1, ws2, _, _, hl1, hl2, hr1, hr2, by rw [← hcur]; exact hw1, by rw [← hcur]; exact hw2,
    by rw [ru, hcur2, hcur], hrun1, hrun2⟩

/-- **The message**: `packed_message` reads the `144` words at `σ1076` in eight-word permutations
of the capacity `σ1071 ..`, its squeeze the public input's challenge `σ1287` and the capacity
`σ1288 ..`. -/
theorem VsRun.linkMsg {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap}
    {σ : Val} {rets : List E} (R : VsRun bytecode L C V σ rets) :
    ∃ message : List E, message.length = 144 ∧ ReadsAt L.read (σ (.n 1076)) message ∧
      (⟨pkAbsorb 18 message [σ (.n 1071), σ (.n 1072), σ (.n 1073), σ (.n 1074), σ (.n 1075)], []⟩ :
        Fs).squeeze = (σ (.n 1287), ⟨[σ (.n 1288), σ (.n 1289), σ (.n 1290), σ (.n 1291), σ (.n 1292)], []⟩) := by
  have hM := R.slice vsLkMsgT_eq
  simp only [vsLkMsgT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hM
  have M := packed_message_sound L.read _ _ (R.hle _ _ _ hM.1)
  simp only [MeaningPM] at M
  obtain ⟨xs, hxl, hxr, hret⟩ := M
  refine ⟨xs, hxl, hxr, ?_⟩
  simp only [List.cons.injEq] at hret
  obtain ⟨e0, hcap⟩ := hret
  rw [Prod.ext_iff]
  refine ⟨e0.symm, ?_⟩
  simp only [Fs.squeeze] at hcap ⊢
  rw [hcap]

/-! ## `verify_link`, run -/

theorem readsAt_app {rd : Reader} {p q : E} {l1 l2 : List E} (h1 : ReadsAt rd p l1)
    (hq : q = p * gen ^ l1.length) (h2 : ReadsAt rd q l2) : ReadsAt rd p (l1 ++ l2) :=
  readsAt_append_shift h1 (hq ▸ h2)

theorem lkReadsAt_prefix {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) (n : ℕ) :
    ReadsAt rd p (l.take n) := by
  intro k hk
  rw [List.getElem_take]
  exact h k (by simp at hk; omega)

theorem lkSplitColumns_length : (splitColumns tables).length = 36 := by decide +kernel

set_option maxHeartbeats 2000000 in
/-- **The link's run**: the section's words from `stream·g^12` run `verifyLink` with the fresh
claim's split from `vsF3`, to `lkEnd` at the transcript's values and the capacity after the
message, when the index side's claim and the terminal check are the Statement's. -/
theorem VsRun.linkRun {bytecode : List K} {κ : ℕ} {L : MemoryImage κ} {C : CallRel} {V : FrameMap}
    {σ : Val} {rets : List E} (R : VsRun bytecode L C V σ rets) :
    ∃ (c : Chunks) (p : ℕ) (r chi qPoint message : List E),
      Chunks.new (linkWidth (vsLayout bytecode σ)) = some c ∧ σ (.n 645) = gen ^ p ∧ p < 64 ∧
      linkDrawn (vsLayout bytecode σ) c ≤ 8 * p ∧
      ReadsAt L.read (σ (.n 12)) r ∧ r.length = linkWidth (vsLayout bytecode σ) ∧
      ReadsAt L.read (σ (.n 15)) chi ∧ chi.length = linkRows (vsLayout bytecode σ) ∧
      ReadsAt L.read (σ (.n 16)) qPoint ∧ qPoint.length = 6 ∧
      ReadsAt L.read (σ (.n 1076)) message ∧ message.length = 144 ∧
      (⟨pkAbsorb 18 message [σ (.n 1071), σ (.n 1072), σ (.n 1073), σ (.n 1074), σ (.n 1075)], []⟩ :
        Fs).squeeze = (σ (.n 1287), ⟨[σ (.n 1288), σ (.n 1289), σ (.n 1290), σ (.n 1291), σ (.n 1292)], []⟩) ∧
      (σ (.n 764) = indexClaim (vsLayout bytecode σ) c (lkDrawn bytecode σ c p) →
        TailCheck (vsLayout bytecode σ) c (σ (.n 573)) (lkDrawn bytecode σ c p) r (σ (.n 779))
          [σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785), σ (.n 786)]
          (Split.ofColumns tables (vsFresh L.read σ).values) chi qPoint message (σ (.n 1077)) →
        ∃ xs : List E, ReadsAt L.read (vsStream σ * gen ^ 12) xs ∧
          σ (.n 1076) * gen ^ 144 = vsStream σ * gen ^ (12 + xs.length) ∧
          RunsTo (verifyLink (freshSplit (vsFresh L.read σ)) (vsLayout bytecode σ)) (vsF3 L.read σ) xs
            (lkEnd (vsLayout bytecode σ) c (σ (.n 573)) (lkDrawn bytecode σ c p) r (σ (.n 779))
              [σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785), σ (.n 786)]
              (Split.ofColumns tables (vsFresh L.read σ).values) chi qPoint message)
            ⟨pkAbsorb 18 message [σ (.n 1071), σ (.n 1072), σ (.n 1073), σ (.n 1074), σ (.n 1075)], []⟩) := by
  have Sh := R.shapeOk
  obtain ⟨c, hc, -⟩ := Sh.chunks
  have hcw := chunks_width hc
  obtain ⟨nn, p, hnn, h580, hcg, hp, hd1, hd2, -, hret, hG⟩ := R.linkFront hc
  obtain ⟨l, ws, hll, hr, hws, h772, hidx, hm1, hfr⟩ := R.linkIdx
  obtain ⟨l1, l2, ws1, ws2, cl1, cap1, hl1, hl2, hc1, hc2, hw1, hw2, h1076, hrun1, hrun2⟩ := R.linkRow hc
  obtain ⟨message, hml, hmr, hsq⟩ := R.linkMsg
  refine ⟨c, p, l.map Prod.fst, l1.map Prod.fst, l2.map Prod.fst, message, hc, hcg, hp, hd2, hr,
    by simp [hll], hc1, by simp [hl1], hc2, by simp [hl2], hmr, hml, hsq, fun hclaim htail ↦ ?_⟩
  -- the moves
  have hdraw := runsTo_samplePacked [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579)] hd1 hd2
  rw [← hret] at hdraw
  rw [hclaim, ← hcw] at hidx
  have hm1r : RunsTo VerifierProgram.readScalar
      ⟨[σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)], []⟩ [σ (.n 779)] (σ (.n 779))
      ⟨[σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)], [(σ (.n 779), dsObserve)]⟩ :=
    RunsTo.of_eq (runsTo_readE _ _) rfl rfl rfl (by simp [Fs.absorb, rateScalars])
  have hpt : ((l.map Prod.fst).take (vsLayout bytecode σ).logBytecode) = (vsFresh L.read σ).point := by
    have h19 := Sh.widthGe
    rw [Sh.logBc]
    have := wordsAt_eq (lkReadsAt_prefix hr 19)
    rw [List.length_take, List.length_map, hll, min_eq_left h19] at this
    exact this.symm
  have hsplit : RunsTo (freshSplit (vsFresh L.read σ) (vsLayout bytecode σ).bytecode
      ((l.map Prod.fst).take (vsLayout bytecode σ).logBytecode) (pcSlots (vsLayout bytecode σ).tables))
      ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)], []⟩ []
      (Split.ofColumns tables (vsFresh L.read σ).values)
      ⟨[σ (.n 790), σ (.n 791), σ (.n 792), σ (.n 793), σ (.n 794)], []⟩ := by
    unfold freshSplit
    refine RunsTo.of_eq ((lkRunsTo_require ⟨hpt, by simp [vsFresh, wordsAt_length, lkSplitColumns_length]⟩
      _).bind (f := fun _ ↦ pure (Split.ofColumns tables (vsFresh L.read σ).values)) (runsTo_ret _ _))
      rfl rfl rfl rfl
  have htl := runsTo_linkTail Sh.tablesEq c (σ (.n 573)) (lkDrawn bytecode σ c p) (l.map Prod.fst)
    (σ (.n 779)) [σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785), σ (.n 786)]
    (Split.ofColumns tables (vsFresh L.read σ).values) (l1.map Prod.fst) (l2.map Prod.fst) (σ (.n 1077))
    [σ (.n 1071), σ (.n 1072), σ (.n 1073), σ (.n 1074), σ (.n 1075)] message hml htail
  have hrow : RunsTo (linkRowPhase (freshSplit (vsFresh L.read σ)) (vsLayout bytecode σ) c (σ (.n 573))
      (lkDrawn bytecode σ c p) (l.map Prod.fst) (σ (.n 773)))
      ⟨[σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)], []⟩ (σ (.n 779) :: (ws1 ++ (ws2 ++ message)))
      (lkEnd (vsLayout bytecode σ) c (σ (.n 573)) (lkDrawn bytecode σ c p) (l.map Prod.fst) (σ (.n 779))
        [σ (.n 782), σ (.n 783), σ (.n 784), σ (.n 785), σ (.n 786)]
        (Split.ofColumns tables (vsFresh L.read σ).values) (l1.map Prod.fst) (l2.map Prod.fst) message)
      ⟨pkAbsorb 18 message [σ (.n 1071), σ (.n 1072), σ (.n 1073), σ (.n 1074), σ (.n 1075)], []⟩ := by
    unfold linkRowPhase
    rw [linkQVars_tables Sh.tablesEq]
    refine RunsTo.of_eq (xs := [σ (.n 779)] ++ ([] ++ ([] ++ (ws1 ++ (ws2 ++ message))))) ?_ rfl
      (by simp) rfl rfl
    refine RunsTo.bind (ys := [] ++ ([] ++ (ws1 ++ (ws2 ++ message)))) hm1r ?_
    refine RunsTo.bind (ys := [] ++ (ws1 ++ (ws2 ++ message))) hfr ?_
    refine RunsTo.bind (ys := ws1 ++ (ws2 ++ message)) hsplit ?_
    refine RunsTo.bind (ys := ws2 ++ message) hrun1 ?_
    refine RunsTo.bind (ys := message) hrun2 ?_
    exact htl
  refine ⟨nn :: (ws ++ (σ (.n 779) :: (ws1 ++ (ws2 ++ message)))), ?_, ?_, ?_⟩
  · refine readsAt_app (q := σ (.n 580)) (l1 := [nn]) (fun k hk ↦ ?_)
      (by rw [h580, List.length_singleton, pow_one, mul_assoc, ← pow_succ]) ?_
    · obtain rfl : k = 0 := by simp at hk; omega
      exact (loadHolds_mul_gen_pow _ _ _ _ _).mpr hnn
    refine readsAt_app (q := σ (.n 772)) hws h772 ?_
    refine readsAt_app (q := σ (.n 772) * gen) (l1 := [σ (.n 779)]) (fun k hk ↦ ?_)
      (by rw [List.length_singleton, pow_one]) ?_
    · obtain rfl : k = 0 := by simp at hk; omega
      exact hm1
    refine readsAt_app hw1 rfl ?_
    refine readsAt_app (q := σ (.n 1076)) hw2 (by rw [h1076, pow_add]; ring) hmr
  · rw [h1076, h772, h580]
    simp only [List.length_cons, List.length_append, hml]
    ring
  · rw [verifyLink_eq_linkSkeleton, linkSkeleton, hc]
    refine RunsTo.of_eq (xs := [] ++ ([nn] ++ ([] ++ ([] ++ (ws ++ (σ (.n 779) :: (ws1 ++ (ws2 ++
      message)))))))) ?_ rfl (by simp) rfl rfl
    refine RunsTo.bind (lkRunsTo_liftOption c _) ?_
    have hgb : grindingBits (max (linkRows (vsLayout bytecode σ) + 3 + bytecodeSlotBits) (c.width + 1)) = 2 := by
      rw [hcw]; exact linkGrind_bits Sh.rowsLe Sh.widthGe Sh.widthLe
    show RunsTo (VerifierProgram.grindProofOfWork (grindingBits (max (linkRows (vsLayout bytecode σ) + 3 +
      bytecodeSlotBits) (c.width + 1))) >>= _) _ _ _ _
    rw [hgb]
    refine RunsToG.bindFrom (ys := [] ++ ([] ++ (ws ++ (σ (.n 779) :: (ws1 ++ (ws2 ++ message)))))) hG ?_
    refine RunsFromG.bind (ys := [] ++ (ws ++ (σ (.n 779) :: (ws1 ++ (ws2 ++ message))))) (runsFromG_sample _ _) ?_
    refine RunsTo.bind (ys := ws ++ (σ (.n 779) :: (ws1 ++ (ws2 ++ message)))) hdraw ?_
    refine RunsTo.bind (ys := σ (.n 779) :: (ws1 ++ (ws2 ++ message))) hidx ?_
    exact hrow

end
end LeanVM.Guest.B1.VerifySub
