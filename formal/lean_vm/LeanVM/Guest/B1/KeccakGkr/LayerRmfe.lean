/-
  LeanVM.Guest.B1.KeccakGkr.LayerRmfe

  The instance weights in `keccak_layer`: the powers of `s`, the RMFE embeddings
  evaluated at `s` as products of small factors, their sum, and their stores in the next claim.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Mask
public import LeanVM.Protocol.Keccak.LayerSum
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# The instance weights

The two specializations of `keccak_layer` share this block up to an offset `o` of their values
(`LayOff`: `0` for `__L0`, `20` for `__L1`; `s` the value `o + 531`, `out` the parameter `12`): the powers `s^0 .. s^5`, the eight factors
(`KECCAK_FAC_START`, `KECCAK_FAC_IDX`), their products (`KECCAK_EMB_A`, `KECCAK_EMB_B`), the
embeddings stored (`KECCAK_EMB_OUT`) and summed. Its values are binary polynomials in `s` (`Mask`); by
kernel evaluation (`rmfeCheck`) the sixteen stored at `out[6 + i]` are the embeddings
`RMFE_EMBED[i]` and the one stored at `out[1]` their sum, which `rmfeBlock_holds` turns into
`keccakInstanceWeights s` and its sum.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The block from `s = o + 531` (`o` the specialization's offset). -/
def rmfeBlockT (o : ℕ) : List Stmt :=
  [.atom (.const (.n (o + 544)) (word 1 0)),
    .atom (.copy (.n (o + 545)) (.n (o + 531))),
    .atom (.mul (.n (o + 546)) (.n (o + 545)) (.n (o + 531))),
    .atom (.mul (.n (o + 547)) (.n (o + 546)) (.n (o + 531))),
    .atom (.mul (.n (o + 548)) (.n (o + 547)) (.n (o + 531))),
    .atom (.mul (.n (o + 549)) (.n (o + 548)) (.n (o + 531))),
    .atom (.copy (.n (o + 550)) (.n (o + 545))),
    .atom (.add (.n (o + 551)) (.n (o + 544)) (.n (o + 545))),
    .atom (.copy (.n (o + 552)) (.n (o + 551))),
    .atom (.add (.n (o + 553)) (.n (o + 544)) (.n (o + 545))),
    .atom (.add (.n (o + 554)) (.n (o + 553)) (.n (o + 546))),
    .atom (.copy (.n (o + 555)) (.n (o + 554))),
    .atom (.add (.n (o + 556)) (.n (o + 544)) (.n (o + 545))),
    .atom (.add (.n (o + 557)) (.n (o + 556)) (.n (o + 547))),
    .atom (.copy (.n (o + 558)) (.n (o + 557))),
    .atom (.add (.n (o + 559)) (.n (o + 544)) (.n (o + 546))),
    .atom (.add (.n (o + 560)) (.n (o + 559)) (.n (o + 547))),
    .atom (.copy (.n (o + 561)) (.n (o + 560))),
    .atom (.add (.n (o + 562)) (.n (o + 544)) (.n (o + 546))),
    .atom (.add (.n (o + 563)) (.n (o + 562)) (.n (o + 549))),
    .atom (.copy (.n (o + 564)) (.n (o + 563))),
    .atom (.add (.n (o + 565)) (.n (o + 544)) (.n (o + 547))),
    .atom (.add (.n (o + 566)) (.n (o + 565)) (.n (o + 549))),
    .atom (.copy (.n (o + 567)) (.n (o + 566))),
    .atom (.add (.n (o + 568)) (.n (o + 544)) (.n (o + 545))),
    .atom (.add (.n (o + 569)) (.n (o + 568)) (.n (o + 546))),
    .atom (.add (.n (o + 570)) (.n (o + 569)) (.n (o + 547))),
    .atom (.add (.n (o + 571)) (.n (o + 570)) (.n (o + 549))),
    .atom (.copy (.n (o + 572)) (.n (o + 571))),
    .atom (.mul (.n (o + 573)) (.n (o + 550)) (.n (o + 552))),
    .atom (.mul (.n (o + 574)) (.n (o + 558)) (.n (o + 561))),
    .atom (.mul (.n (o + 575)) (.n (o + 564)) (.n (o + 573))),
    .atom (.mul (.n (o + 576)) (.n (o + 567)) (.n (o + 572))),
    .atom (.mul (.n (o + 577)) (.n (o + 552)) (.n (o + 574))),
    .atom (.mul (.n (o + 578)) (.n (o + 550)) (.n (o + 575))),
    .atom (.mul (.n (o + 579)) (.n (o + 574)) (.n (o + 576))),
    .atom (.mul (.n (o + 580)) (.n (o + 577)) (.n (o + 578))),
    .atom (.mul (.n (o + 581)) (.n (o + 558)) (.n (o + 576))),
    .atom (.mul (.n (o + 582)) (.n (o + 550)) (.n (o + 567))),
    .atom (.mul (.n (o + 583)) (.n (o + 550)) (.n (o + 579))),
    .atom (.mul (.n (o + 584)) (.n (o + 552)) (.n (o + 561))),
    .atom (.mul (.n (o + 585)) (.n (o + 552)) (.n (o + 572))),
    .atom (.mul (.n (o + 586)) (.n (o + 555)) (.n (o + 575))),
    .atom (.mul (.n (o + 587)) (.n (o + 576)) (.n (o + 584))),
    .atom (.mul (.n (o + 588)) (.n (o + 580)) (.n (o + 582))),
    .atom (.mul (.n (o + 589)) (.n (o + 550)) (.n (o + 588))),
    .atom (.mul (.n (o + 590)) (.n (o + 552)) (.n (o + 575))),
    .atom (.mul (.n (o + 591)) (.n (o + 552)) (.n (o + 588))),
    .atom (.mul (.n (o + 592)) (.n (o + 564)) (.n (o + 576))),
    .atom (.mul (.n (o + 593)) (.n (o + 564)) (.n (o + 583))),
    .atom (.mul (.n (o + 594)) (.n (o + 567)) (.n (o + 574))),
    .atom (.mul (.n (o + 595)) (.n (o + 572)) (.n (o + 580))),
    .atom (.mul (.n (o + 596)) (.n (o + 573)) (.n (o + 577))),
    .atom (.mul (.n (o + 597)) (.n (o + 573)) (.n (o + 579))),
    .atom (.mul (.n (o + 598)) (.n (o + 573)) (.n (o + 583))),
    .atom (.mul (.n (o + 599)) (.n (o + 575)) (.n (o + 577))),
    .atom (.mul (.n (o + 600)) (.n (o + 575)) (.n (o + 579))),
    .atom (.mul (.n (o + 601)) (.n (o + 575)) (.n (o + 581))),
    .atom (.mul (.n (o + 602)) (.n (o + 577)) (.n (o + 592))),
    .atom (.mul (.n (o + 603)) (.n (o + 578)) (.n (o + 587))),
    .atom (.mul (.n (o + 604)) (.n (o + 580)) (.n (o + 585))),
    .atom (.mul (.n (o + 605)) (.n (o + 581)) (.n (o + 586))),
    .atom (.mul (.n (o + 606)) (.n (o + 581)) (.n (o + 596))),
    .atom (.mul (.n (o + 607)) (.n (o + 585)) (.n (o + 599))),
    .atom (.mul (.n (o + 608)) (.n (o + 586)) (.n (o + 594))),
    .atom (.mul (.n (o + 609)) (.n (o + 587)) (.n (o + 590))),
    .atom (.load (.n (o + 602)) (.n (valf% «keccak_layer» "out")) 6),
    .atom (.load (.n (o + 593)) (.n (valf% «keccak_layer» "out")) 7),
    .atom (.add (.n (o + 610)) (.n (o + 602)) (.n (o + 593))),
    .atom (.load (.n (o + 609)) (.n (valf% «keccak_layer» "out")) 8),
    .atom (.add (.n (o + 611)) (.n (o + 610)) (.n (o + 609))),
    .atom (.load (.n (o + 603)) (.n (valf% «keccak_layer» "out")) 9),
    .atom (.add (.n (o + 612)) (.n (o + 611)) (.n (o + 603))),
    .atom (.load (.n (o + 605)) (.n (valf% «keccak_layer» "out")) 10),
    .atom (.add (.n (o + 613)) (.n (o + 612)) (.n (o + 605))),
    .atom (.load (.n (o + 601)) (.n (valf% «keccak_layer» "out")) 11),
    .atom (.add (.n (o + 614)) (.n (o + 613)) (.n (o + 601))),
    .atom (.load (.n (o + 597)) (.n (valf% «keccak_layer» "out")) 12),
    .atom (.add (.n (o + 615)) (.n (o + 614)) (.n (o + 597))),
    .atom (.load (.n (o + 606)) (.n (valf% «keccak_layer» "out")) 13),
    .atom (.add (.n (o + 616)) (.n (o + 615)) (.n (o + 606))),
    .atom (.load (.n (o + 598)) (.n (valf% «keccak_layer» "out")) 14),
    .atom (.add (.n (o + 617)) (.n (o + 616)) (.n (o + 598))),
    .atom (.load (.n (o + 607)) (.n (valf% «keccak_layer» "out")) 15),
    .atom (.add (.n (o + 618)) (.n (o + 617)) (.n (o + 607))),
    .atom (.load (.n (o + 595)) (.n (valf% «keccak_layer» "out")) 16),
    .atom (.add (.n (o + 619)) (.n (o + 618)) (.n (o + 595))),
    .atom (.load (.n (o + 604)) (.n (valf% «keccak_layer» "out")) 17),
    .atom (.add (.n (o + 620)) (.n (o + 619)) (.n (o + 604))),
    .atom (.load (.n (o + 591)) (.n (valf% «keccak_layer» "out")) 18),
    .atom (.add (.n (o + 621)) (.n (o + 620)) (.n (o + 591))),
    .atom (.load (.n (o + 589)) (.n (valf% «keccak_layer» "out")) 19),
    .atom (.add (.n (o + 622)) (.n (o + 621)) (.n (o + 589))),
    .atom (.load (.n (o + 608)) (.n (valf% «keccak_layer» "out")) 20),
    .atom (.add (.n (o + 623)) (.n (o + 622)) (.n (o + 608))),
    .atom (.load (.n (o + 600)) (.n (valf% «keccak_layer» "out")) 21),
    .atom (.add (.n (o + 624)) (.n (o + 623)) (.n (o + 600))),
    .atom (.load (.n (o + 624)) (.n (valf% «keccak_layer» "out")) 1)]


/-- The values stored at `out[6 + i]`. -/
def rmfeStores : List ℕ :=
  [602, 593, 609, 603, 605, 601, 597, 606, 598, 607, 595, 604, 591, 589, 608, 600]

/-- The sum of the embeddings, as a mask. -/
def embedXor : ℕ := embedLit.foldl (· ^^^ ·) 0

/-- The offsets of `keccak_layer`'s two specializations past `s`: `0` (`__L0`), `20` (`__L1`). -/
def LayOff (o : ℕ) : Prop := o = 1 ∨ o = 21

/-- The block's masks, checked. -/
def rmfeCheck (o : ℕ) : Bool :=
  match maskRun (.n (o + 531)) [(.n (o + 531), 2)] (rmfeBlockT o) with
  | some st => (List.range 16).all (fun i ↦ st.lookup (.n (o + rmfeStores.getD i 0)) ==
      some (embedLit.getD i 0)) && st.lookup (.n (o + 624)) == some embedXor
  | none => false

theorem rmfeCheck_true {o : ℕ} (ho : LayOff o) : rmfeCheck o = true := by
  rcases ho with rfl | rfl <;> decide +kernel

theorem rmfeBlock_atoms (o : ℕ) : (rmfeBlockT o).all isAtom = true := rfl

theorem rmfeBlock_stores {o : ℕ} (ho : LayOff o) : ∀ i < 16, (rmfeBlockT o).any (fun s ↦ stmtEqb s
    (.atom (.load (.n (o + rmfeStores.getD i 0)) (.n (valf% «keccak_layer» "out")) (6 + i)))) = true := by
  rcases ho with rfl | rfl <;> decide +kernel

theorem rmfeBlock_kappa {o : ℕ} (ho : LayOff o) :
    (rmfeBlockT o).any (fun s ↦ stmtEqb s (.atom (.load (.n (o + 624)) (.n (valf% «keccak_layer» "out")) 1))) = true := by
  rcases ho with rfl | rfl <;> decide +kernel

/-! ## The weights as masks -/

theorem pe_zero (x : E) : pe 0 x = 0 := by simp [pe]

theorem pe_two (x : E) : pe 2 x = x := by
  rw [show (2 : ℕ) = 1 <<< 1 from rfl, pe_shl 1 (by norm_num), pe_one, mul_one]

theorem pe_of_lt (m : ℕ) (hm : m < 2 ^ 24) (x : E) :
    pe m x = ∑ b ∈ range 24, if m.testBit b then x ^ b else 0 := by
  unfold pe
  refine (Finset.sum_subset (fun b hb ↦ by simp at hb ⊢; omega) fun b _ hb ↦ ?_).symm
  have h24 : 24 ≤ b := by simpa using hb
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) h24))]
  simp

theorem embedLit_lt : ∀ e ∈ embedLit, e < 2 ^ 24 := by decide +kernel

/-- The instance weights at `s` are the embeddings' masks at `s`. -/
theorem keccakInstanceWeights_pe (s : E) :
    keccakInstanceWeights s = embedLit.map (fun e ↦ pe e s) := by
  simp only [keccakInstanceWeights]
  rw [rmfeEmbed_eq]
  refine List.map_congr_left fun e he ↦ ?_
  rw [sumE_filterMap_range, show embedBits = 24 from rfl, pe_of_lt e (embedLit_lt e he)]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [powers_getD s (Finset.mem_range.1 hb)]

theorem keccakInstanceWeights_getD_pe (s : E) {i : ℕ} (hi : i < 16) :
    (keccakInstanceWeights s).getD i 0 = pe (embedLit.getD i 0) s := by
  have hl : i < embedLit.length := hi
  rw [keccakInstanceWeights_pe, List.getD_eq_getElem _ _ (by simpa using hl),
    List.getD_eq_getElem _ _ hl, List.getElem_map]

theorem pe_foldl_xor (x : E) :
    ∀ (l : List ℕ) (a : ℕ), pe (l.foldl (· ^^^ ·) a) x = pe a x + (l.map (pe · x)).sum
  | [], a => by simp
  | e :: l, a => by
    rw [List.foldl_cons, pe_foldl_xor x l, pe_xor, List.map_cons, List.sum_cons, add_assoc]

theorem sumE_keccakInstanceWeights (s : E) :
    sumE (keccakInstanceWeights s) = pe embedXor s := by
  rw [keccakInstanceWeights_pe, LeanVM.Protocol.KeccakGkr.sumE_eq_sum, embedXor, pe_foldl_xor,
    pe_zero, zero_add]

/-- **The instance weights, stored**: if the block holds, the next
claim's record holds `keccakInstanceWeights s` at `out[6 + i]` and their sum at `out[1]`. -/
theorem rmfeBlock_holds {o : ℕ} (ho : LayOff o) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (rmfeBlockT o) next kret) :
    (∀ i < 16, LoadHolds rd (σ (.n (valf% «keccak_layer» "out"))) (6 + i)
      ((keccakInstanceWeights (σ (.n (o + 531)))).getD i 0)) ∧
    LoadHolds rd (σ (.n (valf% «keccak_layer» "out"))) 1 (sumE (keccakInstanceWeights (σ (.n (o + 531))))) := by
  have hc := rmfeCheck_true ho
  unfold rmfeCheck at hc
  split at hc
  · rename_i st hst
    have hok0 : MaskOk σ (σ (.n (o + 531))) [(.n (o + 531), 2)] := by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact (pe_two _).symm
    obtain ⟨hok, -⟩ := maskRun_sound hst hok0 h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
    obtain ⟨hst16, hk⟩ := hc
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · have hl := atom_of_block (rmfeBlock_atoms o) h _ (rmfeBlock_stores ho i hi)
      simp only [Atom.Holds] at hl
      rwa [hok.lookup (hst16 i hi), ← keccakInstanceWeights_getD_pe _ hi] at hl
    · have hl := atom_of_block (rmfeBlock_atoms o) h _ (rmfeBlock_kappa ho)
      simp only [Atom.Holds] at hl
      rwa [hok.lookup hk, ← sumE_keccakInstanceWeights] at hl
  · cases hc

end
end LeanVM.Guest.B1.VerifySub
