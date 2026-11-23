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
  [.atom (.const (.n (o + 608)) (word 1 0)),
    .atom (.copy (.n (o + 609)) (.n (o + 531))),
    .atom (.mul (.n (o + 610)) (.n (o + 609)) (.n (o + 531))),
    .atom (.mul (.n (o + 611)) (.n (o + 610)) (.n (o + 531))),
    .atom (.mul (.n (o + 612)) (.n (o + 611)) (.n (o + 531))),
    .atom (.mul (.n (o + 613)) (.n (o + 612)) (.n (o + 531))),
    .atom (.copy (.n (o + 614)) (.n (o + 609))),
    .atom (.add (.n (o + 615)) (.n (o + 608)) (.n (o + 609))),
    .atom (.copy (.n (o + 616)) (.n (o + 615))),
    .atom (.add (.n (o + 617)) (.n (o + 608)) (.n (o + 609))),
    .atom (.add (.n (o + 618)) (.n (o + 617)) (.n (o + 610))),
    .atom (.copy (.n (o + 619)) (.n (o + 618))),
    .atom (.add (.n (o + 620)) (.n (o + 608)) (.n (o + 609))),
    .atom (.add (.n (o + 621)) (.n (o + 620)) (.n (o + 611))),
    .atom (.copy (.n (o + 622)) (.n (o + 621))),
    .atom (.add (.n (o + 623)) (.n (o + 608)) (.n (o + 610))),
    .atom (.add (.n (o + 624)) (.n (o + 623)) (.n (o + 611))),
    .atom (.copy (.n (o + 625)) (.n (o + 624))),
    .atom (.add (.n (o + 626)) (.n (o + 608)) (.n (o + 610))),
    .atom (.add (.n (o + 627)) (.n (o + 626)) (.n (o + 613))),
    .atom (.copy (.n (o + 628)) (.n (o + 627))),
    .atom (.add (.n (o + 629)) (.n (o + 608)) (.n (o + 611))),
    .atom (.add (.n (o + 630)) (.n (o + 629)) (.n (o + 613))),
    .atom (.copy (.n (o + 631)) (.n (o + 630))),
    .atom (.add (.n (o + 632)) (.n (o + 608)) (.n (o + 609))),
    .atom (.add (.n (o + 633)) (.n (o + 632)) (.n (o + 610))),
    .atom (.add (.n (o + 634)) (.n (o + 633)) (.n (o + 611))),
    .atom (.add (.n (o + 635)) (.n (o + 634)) (.n (o + 613))),
    .atom (.copy (.n (o + 636)) (.n (o + 635))),
    .atom (.mul (.n (o + 637)) (.n (o + 614)) (.n (o + 616))),
    .atom (.mul (.n (o + 638)) (.n (o + 622)) (.n (o + 625))),
    .atom (.mul (.n (o + 639)) (.n (o + 628)) (.n (o + 637))),
    .atom (.mul (.n (o + 640)) (.n (o + 631)) (.n (o + 636))),
    .atom (.mul (.n (o + 641)) (.n (o + 616)) (.n (o + 638))),
    .atom (.mul (.n (o + 642)) (.n (o + 614)) (.n (o + 639))),
    .atom (.mul (.n (o + 643)) (.n (o + 638)) (.n (o + 640))),
    .atom (.mul (.n (o + 644)) (.n (o + 641)) (.n (o + 642))),
    .atom (.mul (.n (o + 645)) (.n (o + 622)) (.n (o + 640))),
    .atom (.mul (.n (o + 646)) (.n (o + 614)) (.n (o + 631))),
    .atom (.mul (.n (o + 647)) (.n (o + 614)) (.n (o + 643))),
    .atom (.mul (.n (o + 648)) (.n (o + 616)) (.n (o + 625))),
    .atom (.mul (.n (o + 649)) (.n (o + 616)) (.n (o + 636))),
    .atom (.mul (.n (o + 650)) (.n (o + 619)) (.n (o + 639))),
    .atom (.mul (.n (o + 651)) (.n (o + 640)) (.n (o + 648))),
    .atom (.mul (.n (o + 652)) (.n (o + 644)) (.n (o + 646))),
    .atom (.mul (.n (o + 653)) (.n (o + 614)) (.n (o + 652))),
    .atom (.mul (.n (o + 654)) (.n (o + 616)) (.n (o + 639))),
    .atom (.mul (.n (o + 655)) (.n (o + 616)) (.n (o + 652))),
    .atom (.mul (.n (o + 656)) (.n (o + 628)) (.n (o + 640))),
    .atom (.mul (.n (o + 657)) (.n (o + 628)) (.n (o + 647))),
    .atom (.mul (.n (o + 658)) (.n (o + 631)) (.n (o + 638))),
    .atom (.mul (.n (o + 659)) (.n (o + 636)) (.n (o + 644))),
    .atom (.mul (.n (o + 660)) (.n (o + 637)) (.n (o + 641))),
    .atom (.mul (.n (o + 661)) (.n (o + 637)) (.n (o + 643))),
    .atom (.mul (.n (o + 662)) (.n (o + 637)) (.n (o + 647))),
    .atom (.mul (.n (o + 663)) (.n (o + 639)) (.n (o + 641))),
    .atom (.mul (.n (o + 664)) (.n (o + 639)) (.n (o + 643))),
    .atom (.mul (.n (o + 665)) (.n (o + 639)) (.n (o + 645))),
    .atom (.mul (.n (o + 666)) (.n (o + 641)) (.n (o + 656))),
    .atom (.mul (.n (o + 667)) (.n (o + 642)) (.n (o + 651))),
    .atom (.mul (.n (o + 668)) (.n (o + 644)) (.n (o + 649))),
    .atom (.mul (.n (o + 669)) (.n (o + 645)) (.n (o + 650))),
    .atom (.mul (.n (o + 670)) (.n (o + 645)) (.n (o + 660))),
    .atom (.mul (.n (o + 671)) (.n (o + 649)) (.n (o + 663))),
    .atom (.mul (.n (o + 672)) (.n (o + 650)) (.n (o + 658))),
    .atom (.mul (.n (o + 673)) (.n (o + 651)) (.n (o + 654))),
    .atom (.load (.n (o + 666)) (.n (valf% «keccak_layer» "out")) 6),
    .atom (.load (.n (o + 657)) (.n (valf% «keccak_layer» "out")) 7),
    .atom (.add (.n (o + 674)) (.n (o + 666)) (.n (o + 657))),
    .atom (.load (.n (o + 673)) (.n (valf% «keccak_layer» "out")) 8),
    .atom (.add (.n (o + 675)) (.n (o + 674)) (.n (o + 673))),
    .atom (.load (.n (o + 667)) (.n (valf% «keccak_layer» "out")) 9),
    .atom (.add (.n (o + 676)) (.n (o + 675)) (.n (o + 667))),
    .atom (.load (.n (o + 669)) (.n (valf% «keccak_layer» "out")) 10),
    .atom (.add (.n (o + 677)) (.n (o + 676)) (.n (o + 669))),
    .atom (.load (.n (o + 665)) (.n (valf% «keccak_layer» "out")) 11),
    .atom (.add (.n (o + 678)) (.n (o + 677)) (.n (o + 665))),
    .atom (.load (.n (o + 661)) (.n (valf% «keccak_layer» "out")) 12),
    .atom (.add (.n (o + 679)) (.n (o + 678)) (.n (o + 661))),
    .atom (.load (.n (o + 670)) (.n (valf% «keccak_layer» "out")) 13),
    .atom (.add (.n (o + 680)) (.n (o + 679)) (.n (o + 670))),
    .atom (.load (.n (o + 662)) (.n (valf% «keccak_layer» "out")) 14),
    .atom (.add (.n (o + 681)) (.n (o + 680)) (.n (o + 662))),
    .atom (.load (.n (o + 671)) (.n (valf% «keccak_layer» "out")) 15),
    .atom (.add (.n (o + 682)) (.n (o + 681)) (.n (o + 671))),
    .atom (.load (.n (o + 659)) (.n (valf% «keccak_layer» "out")) 16),
    .atom (.add (.n (o + 683)) (.n (o + 682)) (.n (o + 659))),
    .atom (.load (.n (o + 668)) (.n (valf% «keccak_layer» "out")) 17),
    .atom (.add (.n (o + 684)) (.n (o + 683)) (.n (o + 668))),
    .atom (.load (.n (o + 655)) (.n (valf% «keccak_layer» "out")) 18),
    .atom (.add (.n (o + 685)) (.n (o + 684)) (.n (o + 655))),
    .atom (.load (.n (o + 653)) (.n (valf% «keccak_layer» "out")) 19),
    .atom (.add (.n (o + 686)) (.n (o + 685)) (.n (o + 653))),
    .atom (.load (.n (o + 672)) (.n (valf% «keccak_layer» "out")) 20),
    .atom (.add (.n (o + 687)) (.n (o + 686)) (.n (o + 672))),
    .atom (.load (.n (o + 664)) (.n (valf% «keccak_layer» "out")) 21),
    .atom (.add (.n (o + 688)) (.n (o + 687)) (.n (o + 664))),
    .atom (.load (.n (o + 688)) (.n (valf% «keccak_layer» "out")) 1)]


/-- The values stored at `out[6 + i]`. -/
def rmfeStores : List ℕ :=
  [666, 657, 673, 667, 669, 665, 661, 670, 662, 671, 659, 668, 655, 653, 672, 664]

/-- The sum of the embeddings, as a mask. -/
def embedXor : ℕ := embedLit.foldl (· ^^^ ·) 0

/-- The offsets of `keccak_layer`'s two specializations past `s`: `0` (`__L0`), `20` (`__L1`). -/
def LayOff (o : ℕ) : Prop := o = 1 ∨ o = 21

/-- The block's masks, checked. -/
def rmfeCheck (o : ℕ) : Bool :=
  match maskRun (.n (o + 531)) [(.n (o + 531), 2)] (rmfeBlockT o) with
  | some st => (List.range 16).all (fun i ↦ st.lookup (.n (o + rmfeStores.getD i 0)) ==
      some (embedLit.getD i 0)) && st.lookup (.n (o + 688)) == some embedXor
  | none => false

theorem rmfeCheck_true {o : ℕ} (ho : LayOff o) : rmfeCheck o = true := by
  rcases ho with rfl | rfl <;> decide +kernel

theorem rmfeBlock_atoms (o : ℕ) : (rmfeBlockT o).all isAtom = true := rfl

theorem rmfeBlock_stores {o : ℕ} (ho : LayOff o) : ∀ i < 16, (rmfeBlockT o).any (fun s ↦ stmtEqb s
    (.atom (.load (.n (o + rmfeStores.getD i 0)) (.n (valf% «keccak_layer» "out")) (6 + i)))) = true := by
  rcases ho with rfl | rfl <;> decide +kernel

theorem rmfeBlock_kappa {o : ℕ} (ho : LayOff o) :
    (rmfeBlockT o).any (fun s ↦ stmtEqb s (.atom (.load (.n (o + 688)) (.n (valf% «keccak_layer» "out")) 1))) = true := by
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
