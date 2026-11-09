/-
  LeanVM.Guest.B1.Da.DualMath

  The dual codeword the guest builds (`da_vector`), as arithmetic on words: `Ŵ_j` at the basis
  elements as literals, `Ŵ_j` at any point as their sum over its bits (`wK`), and the dual
  codeword's entries as the product of the factors `1 + z^(2^j) Ŵ_j(x)` (`dualAt`).
-/

module

public import LeanDa.Subspace

/-!
# The dual codeword, on words

The guest program builds the dual codeword `L(x) = ∏_(j < 14) (1 + z^(2^j) Ŵ_j(x))` of a
challenge `z` (`da_vector`, `lean_ethereum.py:4421-4485` at leanVM `40f877dc`) from constants
that are sums of `Ŵ_j` at basis elements (`DA_VHAT`, `DA_VHAT_COLUMN`,
`aggregation/placeholders.rs:845-864`). Here:

* `rowWords`, `omegaWords`: `W_j` and `Ŵ_j` at `e_j … e_14` as words; `subspaceRow_words`:
  LeanDA's `subspaceRow` is `rowWords` (kernel evaluation, one row from the last);
  `wHat_basis`: `Ŵ_j(e_(j+k))` is `omegaWords`' entry (`Ŵ_j = W_j / W_j(e_j)`, checked by
  multiplication, no inverse evaluated).
* `wK j b`: `Ŵ_j` at point `b`, the sum over the bits `c` of `b` of `omegaK j c`
  (`wHat_point_eq_wK`).
* `dualAt z b`: the product of the factors; `dualAt_eq`: it is `LeanDa.dualCodewordAt z b`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters

@[expose] public section

/-! ## `W_j` and `Ŵ_j` at the basis -/

/-- `W_j` at `e_j … e_14` (`LeanDa.subspaceRow j`), as words, `j ≤ 14`. -/
def rowWords : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384],
    [6, 20, 72, 272, 1056, 4160, 16512, 65792, 262656, 1049600, 4196352, 16781312, 67117056, 268451840],
    [360, 4592, 67424, 1055936, 16806272, 268550912, 4295427584, 68721314816, 1099518973952, 17592215416832, 281475094175744, 4503600097181696, 72057595917074432],
    [18245760, 4319836928, 1099910667776, 281481375194112, 72057696337049600, 1636483952667, 26182527417088, 418915553820672, 6702629731926016, 107242090889936896, 1715901248742227968, 9014799494681460763],
    [78274681211224091, 1687463513465815067, 8988296383555312369, 14393933788395009471, 7906007890015401141, 15781322294011423466, 12813109461703663119, 1994160189539999749, 12275766169714957820, 9318856278138094875, 176229507072594925],
    [8244804748658156366, 6964524709014517257, 578243005985270896, 17277335748864455019, 18053493123004363615, 10607133894588926735, 17771630945875104135, 266999502398134886, 7901597046524247948, 599988404761654045],
    [8749050644146709186, 3762997275846411469, 11907229328435556158, 4555794481886719399, 7622730220496178298, 14880951363819466616, 8278445872699611729, 5443067111753567332, 6564153150106746978],
    [1085473640648473244, 13257388749725124263, 8640965300599897156, 4260877643451432541, 13939281692944205708, 1226547897764449325, 7799250065211332859, 10952656440188270193],
    [7640059558905957125, 15245751680780821412, 143612520775495321, 11567511995096082708, 3961294767110061651, 15102218351729071184, 15120760296663629047],
    [15191009085390685913, 10195376274664516890, 16509755171424326081, 16029578439158647856, 12437422469226935224, 4967066667814387433],
    [7878391778441664005, 3025435752272433020, 3577674312705047675, 4943399500596486068, 3688776378962563934],
    [15027479999479429674, 16383687819482525314, 13559777212733457364, 14978689530819424709],
    [45258276057990961, 18395008089186019805, 7259194857137784930],
    [4327488829911782419, 12491284962065956391],
    [436120406283855025]]

/-- `Ŵ_j` at `e_j … e_14` (`LeanDa.subspaceEvaluations j`), as words, `j < 14`. -/
def omegaWords : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384],
    [1, 6, 28, 120, 496, 2016, 8128, 32640, 130816, 523776, 2096128, 8386560, 33550336, 134209536],
    [1, 22, 380, 6072, 96880, 1548512, 24777152, 396452736, 6343345920, 101493476864, 1623894465536, 25982304925696, 415716882542592],
    [1, 278, 71548, 18312120, 4687839856, 1200088273120, 307222578655680, 78648980444062592, 1687394915039069979, 7697984633618339057, 15329193679826184270, 13563848713073753244],
    [1, 65814, 4313257852, 282673648724920, 78556165118804587, 1615241704258849297, 9062579267945766542, 13745958506209089452, 7134958990657035894, 2139914792680233373, 6167318088647702568],
    [1, 4295033110, 282673290876775, 78274714194178377, 1686429987210079355, 8093902837644929116, 2422540277288827463, 13196406910240451480, 13213593128912166904, 3668356571201410070],
    [1, 4295033101, 282626045512904, 75731904430919377, 921200596245996688, 14970031326078462060, 17572184006332843942, 31130361615557857, 12848484449566071747],
    [1, 4295032904, 281788514129824, 20362858032959473, 6333143277032856037, 15889496096340495536, 18389557790574996782, 18043989520406123418],
    [1, 4294971481, 17970429743721, 1230839726621911816, 14460140448413987329, 16729653553120207151, 9535639316610554448],
    [1, 16781656, 72340238454070065, 5285358749914120329, 12692627785335414101, 3354021532151090965],
    [1, 281474993557826, 1177972821613886597, 15149451407579695255, 5133604927441220030],
    [1, 281586662707206, 794529912925087409, 8657422631621425818],
    [1, 281586662645178, 477400160501157490],
    [1, 281590962936042]]

/-- Row `j` of `rowWords`, in `K`. -/
def rowK (j : ℕ) : List K := (rowWords.getD j []).map K.ofBits

/-- One step of `LeanDa.subspaceRow`. -/
def rowStep (previous : List K) : List K :=
  (previous.drop 1).map fun value ↦ value * (value + previous.headD 0)

set_option maxRecDepth 10000 in
theorem rowK_zero : rowK 0 = (List.range LeanDa.logM).map fun j ↦ K.ofBits (2 ^ j) := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem rowK_step : ∀ j < 14, rowStep (rowK j) = rowK (j + 1) := by decide +kernel

/-- **LeanDA's `subspaceRow` is `rowWords`.** -/
theorem subspaceRow_words : ∀ {j : ℕ}, j ≤ 14 → LeanDa.subspaceRow j = rowK j
  | 0, _ => by rw [rowK_zero]; rfl
  | j + 1, hj => by
    rw [← rowK_step j (by omega), ← subspaceRow_words (j := j) (by omega)]
    rfl

set_option maxRecDepth 10000 in
/-- `omegaWords` times the row's head is the row: `Ŵ_j(e_(j+k)) · W_j(e_j) = W_j(e_(j+k))`. -/
theorem omega_mul_head : ∀ j < 14, ∀ k < 15 - j,
    K.ofBits ((omegaWords.getD j []).getD k 0) * (rowK j).headD 0 = (rowK j).getD k 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem rowK_head_ne : ∀ j < 14, (rowK j).headD 0 ≠ 0 := by decide +kernel

set_option maxRecDepth 10000 in
theorem length_rowK : ∀ j < 15, (rowK j).length = 15 - j := by decide +kernel

/-- **`Ŵ_j(e_(j+k))` is `omegaWords`' entry.** -/
theorem wHat_basis {j k : ℕ} (hj : j < 14) (hk : k < 15 - j) :
    LeanDa.wHat j (LeanDa.point (2 ^ (j + k))) = K.ofBits ((omegaWords.getD j []).getD k 0) := by
  have hr := LeanDa.subspaceRow_eq (i := j) (by omega)
  rw [subspaceRow_words (by omega)] at hr
  have hrow : ∀ i < 15 - j, (rowK j).getD i 0 = LeanDa.wSub j (LeanDa.point (2 ^ (j + i))) := by
    intro i hi
    rw [hr, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  have h0 : (rowK j).headD 0 = LeanDa.wSub j (LeanDa.point (2 ^ j)) := by
    have := hrow 0 (by omega)
    rw [add_zero] at this
    rw [← this]
    cases h : rowK j with
    | nil => have := length_rowK j (by omega); rw [h] at this; simp at this; omega
    | cons a l => rfl
  rw [LeanDa.wHat_eq j (by omega), ← hrow k hk, ← h0, ← omega_mul_head j hj k hk,
    mul_assoc, mul_inv_cancel₀ (rowK_head_ne j hj), mul_one]

/-! ## `Ŵ_j` at a point -/

/-- `Ŵ_j(e_c)`: zero below `j`, else `omegaWords`' entry. -/
def omegaK (j c : ℕ) : K := if c < j then 0 else K.ofBits ((omegaWords.getD j []).getD (c - j) 0)

/-- **`Ŵ_j` at point `b < 2^15`**: the sum over the bits `c` of `b` of `Ŵ_j(e_c)`. -/
def wK (j b : ℕ) : K := ((List.range 15).map fun c ↦ if b.testBit c then omegaK j c else 0).sum

theorem sum_map_filter {M : Type*} [AddCommMonoid M] (p : ℕ → Bool) (f : ℕ → M) :
    ∀ l : List ℕ, ((l.filter p).map f).sum = (l.map fun c ↦ if p c then f c else 0).sum
  | [] => rfl
  | c :: l => by
    by_cases h : p c <;> simp [h, sum_map_filter p f l]

theorem wHat_basis_omegaK {j c : ℕ} (hj : j < 14) (hc : c < 15) :
    LeanDa.wHat j (LeanDa.point (2 ^ c)) = omegaK j c := by
  unfold omegaK
  split_ifs with h
  · exact LeanDa.wHat_two_pow_of_lt (by omega) h
  · have := wHat_basis (j := j) (k := c - j) hj (by omega)
    rwa [show j + (c - j) = c by omega] at this

/-- **`Ŵ_j` at a point is `wK`.** -/
theorem wHat_point_eq_wK {j b : ℕ} (hj : j < 14) (hb : b < 2 ^ 15) :
    LeanDa.wHat j (LeanDa.point b) = wK j b := by
  rw [LeanDa.wHat_point_eq_sum j hb, sum_map_filter, wK]
  refine congrArg _ (List.map_congr_left fun c hc ↦ ?_)
  rw [wHat_basis_omegaK hj (List.mem_range.mp hc)]

/-! ## The dual codeword -/

/-- **The dual codeword's entry `b`**: `∏_(j < 14) (1 + z^(2^j) Ŵ_j(b))`, `Ŵ_j` as `wK`. -/
def dualAt (z : E) (b : ℕ) : E := ((List.range 14).map fun j ↦ 1 + z ^ 2 ^ j * ofK (wK j b)).prod

/-- **`dualAt` is the statement's dual codeword.** -/
theorem dualAt_eq (z : E) (b : Fin (2 ^ 15)) : dualAt z b = LeanDa.dualCodewordAt z b := by
  rw [dualAt, LeanDa.prod_map_range, LeanDa.dualCodewordAt,
    ← Fin.prod_univ_eq_prod_range (fun j ↦ 1 + z ^ 2 ^ j * ofK (wK j b)) 14]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [LeanDa.normW_eval, wHat_point_eq_wK j.2 b.2]
  rfl

end
end LeanVM.Guest.B1.Da
