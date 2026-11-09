/-
  LeanVM.Guest.B1.KeccakGkr.LayerRmfe

  The instance weights in `keccak_layer` (G:2729-2748): the powers of `s`, the RMFE embeddings
  evaluated at `s` as products of small factors, their sum, and their stores in the next claim.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Mask
public import LeanVM.Protocol.Keccak.LayerSum

/-!
# The instance weights

The two specializations of `keccak_layer` share this block (statements `675 .. 772`, `s` the
value `877`, `out` the parameter `12`): the powers `s^0 .. s^5`, the eight factors
(`KECCAK_FAC_START`, `KECCAK_FAC_IDX`), their products (`KECCAK_EMB_A`, `KECCAK_EMB_B`), the
embeddings stored (`KECCAK_EMB_OUT`) and summed. Its values are binary polynomials in `s` (`Mask`); by
kernel evaluation (`rmfeCheck`) the sixteen stored at `out[6 + i]` are the embeddings
`RMFE_EMBED[i]` and the one stored at `out[1]` their sum, which `rmfeBlock_holds` turns into
`keccakInstanceWeights s` (V:1960) and its sum.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- The block, `keccak_layer`'s statements `675 .. 772`. -/
def rmfeBlockT : List Stmt :=
  [.atom (.const (.n 878) (word 1 0 0)),
    .atom (.copy (.n 879) (.n 877)),
    .atom (.mul (.n 880) (.n 879) (.n 877)),
    .atom (.mul (.n 881) (.n 880) (.n 877)),
    .atom (.mul (.n 882) (.n 881) (.n 877)),
    .atom (.mul (.n 883) (.n 882) (.n 877)),
    .atom (.copy (.n 884) (.n 879)),
    .atom (.add (.n 885) (.n 878) (.n 879)),
    .atom (.copy (.n 886) (.n 885)),
    .atom (.add (.n 887) (.n 878) (.n 879)),
    .atom (.add (.n 888) (.n 887) (.n 880)),
    .atom (.copy (.n 889) (.n 888)),
    .atom (.add (.n 890) (.n 878) (.n 879)),
    .atom (.add (.n 891) (.n 890) (.n 881)),
    .atom (.copy (.n 892) (.n 891)),
    .atom (.add (.n 893) (.n 878) (.n 880)),
    .atom (.add (.n 894) (.n 893) (.n 881)),
    .atom (.copy (.n 895) (.n 894)),
    .atom (.add (.n 896) (.n 878) (.n 880)),
    .atom (.add (.n 897) (.n 896) (.n 883)),
    .atom (.copy (.n 898) (.n 897)),
    .atom (.add (.n 899) (.n 878) (.n 881)),
    .atom (.add (.n 900) (.n 899) (.n 883)),
    .atom (.copy (.n 901) (.n 900)),
    .atom (.add (.n 902) (.n 878) (.n 879)),
    .atom (.add (.n 903) (.n 902) (.n 880)),
    .atom (.add (.n 904) (.n 903) (.n 881)),
    .atom (.add (.n 905) (.n 904) (.n 883)),
    .atom (.copy (.n 906) (.n 905)),
    .atom (.mul (.n 907) (.n 884) (.n 886)),
    .atom (.mul (.n 908) (.n 892) (.n 895)),
    .atom (.mul (.n 909) (.n 898) (.n 907)),
    .atom (.mul (.n 910) (.n 901) (.n 906)),
    .atom (.mul (.n 911) (.n 886) (.n 908)),
    .atom (.mul (.n 912) (.n 884) (.n 909)),
    .atom (.mul (.n 913) (.n 908) (.n 910)),
    .atom (.mul (.n 914) (.n 911) (.n 912)),
    .atom (.mul (.n 915) (.n 892) (.n 910)),
    .atom (.mul (.n 916) (.n 884) (.n 901)),
    .atom (.mul (.n 917) (.n 884) (.n 913)),
    .atom (.mul (.n 918) (.n 886) (.n 895)),
    .atom (.mul (.n 919) (.n 886) (.n 906)),
    .atom (.mul (.n 920) (.n 889) (.n 909)),
    .atom (.mul (.n 921) (.n 910) (.n 918)),
    .atom (.mul (.n 922) (.n 914) (.n 916)),
    .atom (.mul (.n 923) (.n 884) (.n 922)),
    .atom (.mul (.n 924) (.n 886) (.n 909)),
    .atom (.mul (.n 925) (.n 886) (.n 922)),
    .atom (.mul (.n 926) (.n 898) (.n 910)),
    .atom (.mul (.n 927) (.n 898) (.n 917)),
    .atom (.mul (.n 928) (.n 901) (.n 908)),
    .atom (.mul (.n 929) (.n 906) (.n 914)),
    .atom (.mul (.n 930) (.n 907) (.n 911)),
    .atom (.mul (.n 931) (.n 907) (.n 913)),
    .atom (.mul (.n 932) (.n 907) (.n 917)),
    .atom (.mul (.n 933) (.n 909) (.n 911)),
    .atom (.mul (.n 934) (.n 909) (.n 913)),
    .atom (.mul (.n 935) (.n 909) (.n 915)),
    .atom (.mul (.n 936) (.n 911) (.n 926)),
    .atom (.mul (.n 937) (.n 912) (.n 921)),
    .atom (.mul (.n 938) (.n 914) (.n 919)),
    .atom (.mul (.n 939) (.n 915) (.n 920)),
    .atom (.mul (.n 940) (.n 915) (.n 930)),
    .atom (.mul (.n 941) (.n 919) (.n 933)),
    .atom (.mul (.n 942) (.n 920) (.n 928)),
    .atom (.mul (.n 943) (.n 921) (.n 924)),
    .atom (.load (.n 936) (.n 12) 6),
    .atom (.load (.n 927) (.n 12) 7),
    .atom (.add (.n 944) (.n 936) (.n 927)),
    .atom (.load (.n 943) (.n 12) 8),
    .atom (.add (.n 945) (.n 944) (.n 943)),
    .atom (.load (.n 937) (.n 12) 9),
    .atom (.add (.n 946) (.n 945) (.n 937)),
    .atom (.load (.n 939) (.n 12) 10),
    .atom (.add (.n 947) (.n 946) (.n 939)),
    .atom (.load (.n 935) (.n 12) 11),
    .atom (.add (.n 948) (.n 947) (.n 935)),
    .atom (.load (.n 931) (.n 12) 12),
    .atom (.add (.n 949) (.n 948) (.n 931)),
    .atom (.load (.n 940) (.n 12) 13),
    .atom (.add (.n 950) (.n 949) (.n 940)),
    .atom (.load (.n 932) (.n 12) 14),
    .atom (.add (.n 951) (.n 950) (.n 932)),
    .atom (.load (.n 941) (.n 12) 15),
    .atom (.add (.n 952) (.n 951) (.n 941)),
    .atom (.load (.n 929) (.n 12) 16),
    .atom (.add (.n 953) (.n 952) (.n 929)),
    .atom (.load (.n 938) (.n 12) 17),
    .atom (.add (.n 954) (.n 953) (.n 938)),
    .atom (.load (.n 925) (.n 12) 18),
    .atom (.add (.n 955) (.n 954) (.n 925)),
    .atom (.load (.n 923) (.n 12) 19),
    .atom (.add (.n 956) (.n 955) (.n 923)),
    .atom (.load (.n 942) (.n 12) 20),
    .atom (.add (.n 957) (.n 956) (.n 942)),
    .atom (.load (.n 934) (.n 12) 21),
    .atom (.add (.n 958) (.n 957) (.n 934)),
    .atom (.load (.n 958) (.n 12) 1)]


/-- The values stored at `out[6 + i]`. -/
def rmfeStores : List ℕ :=
  [936, 927, 943, 937, 939, 935, 931, 940, 932, 941, 929, 938, 925, 923, 942, 934]

/-- The sum of the embeddings, as a mask. -/
def embedXor : ℕ := embedLit.foldl (· ^^^ ·) 0

/-- The block's masks, checked. -/
def rmfeCheck : Bool :=
  match maskRun (.n 877) [(.n 877, 2)] rmfeBlockT with
  | some st => (List.range 16).all (fun i ↦ st.lookup (.n (rmfeStores.getD i 0)) ==
      some (embedLit.getD i 0)) && st.lookup (.n 958) == some embedXor
  | none => false

theorem rmfeCheck_true : rmfeCheck = true := by decide +kernel

theorem rmfeBlock_atoms : rmfeBlockT.all isAtom = true := by decide +kernel

theorem rmfeBlock_stores : ∀ i < 16, rmfeBlockT.any (fun s ↦ stmtEqb s
    (.atom (.load (.n (rmfeStores.getD i 0)) (.n 12) (6 + i)))) = true := by decide +kernel

theorem rmfeBlock_kappa : rmfeBlockT.any (fun s ↦ stmtEqb s (.atom (.load (.n 958) (.n 12) 1))) =
    true := by decide +kernel

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

/-- **The instance weights, stored** (G:2511-2610 against V:1960): if the block holds, the next
claim's record holds `keccakInstanceWeights s` at `out[6 + i]` and their sum at `out[1]`. -/
theorem rmfeBlock_holds {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ rmfeBlockT next kret) :
    (∀ i < 16, LoadHolds rd (σ (.n 12)) (6 + i)
      ((keccakInstanceWeights (σ (.n 877))).getD i 0)) ∧
    LoadHolds rd (σ (.n 12)) 1 (sumE (keccakInstanceWeights (σ (.n 877)))) := by
  have hc := rmfeCheck_true
  unfold rmfeCheck at hc
  split at hc
  · rename_i st hst
    have hok0 : MaskOk σ (σ (.n 877)) [(.n 877, 2)] := by
      intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact (pe_two _).symm
    obtain ⟨hok, -⟩ := maskRun_sound hst hok0 h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
    obtain ⟨hst16, hk⟩ := hc
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · have hl := atom_of_block rmfeBlock_atoms h _ (rmfeBlock_stores i hi)
      simp only [Atom.Holds] at hl
      rwa [hok.lookup (hst16 i hi), ← keccakInstanceWeights_getD_pe _ hi] at hl
    · have hl := atom_of_block rmfeBlock_atoms h _ rmfeBlock_kappa
      simp only [Atom.Holds] at hl
      rwa [hok.lookup hk, ← sumE_keccakInstanceWeights] at hl
  · cases hc

end
end LeanVM.Guest.B1.VerifySub
