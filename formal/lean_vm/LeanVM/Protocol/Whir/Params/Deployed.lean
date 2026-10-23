/-
  LeanVM.Protocol.Whir.Params.Deployed

  Level codes for every admissible WHIR ladder of the deployed opening, with the certificate that
  their group escapes are at most `2^-128`: a table of Johnson slacks and square-root brackets,
  checked by kernel evaluation.
-/

module

public import LeanVM.Protocol.Whir.Params.Check

/-!
# The deployed codes and their escape bound

For each of the 56 admissible pairs `(μ, R)` (`LeanVM.Parameters.Whir.Admissible`, leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`), `certTable` gives one `Cert` per level of the ladder
`ladder μ R`: the level's `κ` and `R`, its Johnson slack `η = e / 2^22`, and the bracket
`s / 2^40 ≤ √ρ₋ ≤ (s + 1) / 2^40`. The slacks were chosen offline, per level, to balance the fold
group's exception count (decreasing in `η`) against the query group's
`((A − 1)/n)^t` (increasing in `η`), by `scripts/whir-params/gen.py`. The table is untrusted
data: `shapeOK_all` checks it by kernel evaluation.

* `deployedCodes μ R`: the codes of the levels.
* `deployed_spec_hyps`: **for every admissible `(μ, R)` with ladder `config`**, the hypotheses
  of `whirSpec` and `stackedSpec` about the codes: level 0 has `κ = μ − laneBits` and rate `R`,
  `LadderArith μ (deployedCodes μ R) 0 0 config`, and `whirEps (deployedCodes μ R) config ≤ 2^-128`;
  moreover `listMax ≤ 2^18` at level 0, which bounds `eBatch`.
* `exists_codes`: the existential form.

The certified bound is `B = 128`, and the margin is thin: the weakest shape is `(μ, R) = (15, 2)`
(about `2^-128.16`, level 0's query group, its fold group at about `2^-128.27`), where
`shapeOK 129 15 2` fails (see the tests).

The fold group is the one `LeanVM.Protocol.Whir.Sound.eFold` proves, with the row-union factor:
`(2·listMax + 2^(ℓ−1)·mcaMax)/|E|`. Annex B at this pin states the smaller `2L/|E| + ε`
(`lem:fold-list`, citing Jo, ePrint 2026/891, Thm 4.4), and the deployed query counts were
derived under it (`b977f5fa`, 25 of the 56 shapes lowered by one to three queries). The table
certifies the lowered counts under the larger, proved bound; the Annex's bound is not used.
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.EndToEnd

@[expose] public section

/-- The certificates `(κ, R, e, s)` of the levels, indexed by `R − 1`, then `μ − 15`, then the
level. -/
def certTable : List (List (List (ℕ × ℕ × ℕ × ℕ))) :=
  [
    -- rate exponent 1, stack sizes 15 to 28
    [
      [(9, 1, 34, 776712506778), (5, 4, 12, 270548850458)],
      [(10, 1, 45, 777092410204), (6, 4, 19, 272721968504), (2, 7, 7, 84163826697)],
      [(11, 1, 55, 777282292286), (7, 4, 21, 273802059735), (3, 7, 10, 90907322834)],
      [(12, 1, 68, 777377215934), (8, 4, 25, 274340510717), (4, 7, 19, 94098018870)],
      [(13, 1, 85, 777424673412), (9, 4, 31, 274609340287), (5, 7, 20, 95653463400)],
      [(14, 1, 107, 777448401065), (10, 4, 39, 274743656431), (6, 7, 23, 96421776654),
        (2, 10, 21, 29756406294)],
      [(15, 1, 134, 777460264620), (11, 4, 49, 274810789885), (7, 7, 27, 96803646571),
        (3, 10, 15, 32140592218)],
      [(16, 1, 189, 777466196329), (12, 4, 61, 274844350463), (8, 7, 34, 96994017741),
        (4, 10, 46, 33268673619)],
      [(17, 1, 237, 777469162167), (13, 4, 76, 274861129215), (9, 7, 42, 97089063347),
        (5, 10, 51, 33818606307)],
      [(18, 1, 298, 777470645082), (14, 4, 96, 274869518207), (10, 7, 52, 97136551275),
        (6, 10, 60, 34090246063), (2, 13, 25, 10520478337)],
      [(19, 1, 375, 777471386538), (15, 4, 121, 274873712607), (11, 7, 65, 97160286535),
        (7, 10, 74, 34225257466), (3, 13, 21, 11363415354)],
      [(20, 1, 471, 777471757266), (16, 4, 152, 274875809783), (12, 7, 82, 97172151991),
        (8, 10, 91, 34292563839), (4, 13, 95, 11762252358)],
      [(21, 1, 663, 777471942630), (17, 4, 191, 274876858365), (13, 7, 103, 97178084176),
        (9, 10, 114, 34326167535), (5, 13, 109, 11956682925)],
      [(22, 1, 832, 777472035311), (18, 4, 240, 274877382655), (14, 7, 129, 97181050133),
        (10, 10, 142, 34342957053), (6, 13, 130, 12052722081), (2, 16, 42, 3719550786)]],
    -- rate exponent 2, stack sizes 15 to 28
    [
      [(9, 2, 34, 549218680575), (5, 5, 19, 191306926801)],
      [(10, 2, 52, 549487312863), (6, 5, 22, 192843553308), (2, 8, 14, 59512812588)],
      [(11, 2, 65, 549621579771), (7, 5, 25, 193607293142), (3, 8, 22, 64281184436)],
      [(12, 2, 81, 549688700927), (8, 5, 31, 193988035482), (4, 8, 20, 66537347239)],
      [(13, 2, 102, 549722258431), (9, 5, 38, 194178126694), (5, 8, 22, 67637212614)],
      [(14, 2, 128, 549739036415), (10, 5, 48, 194273102551), (6, 8, 25, 68180492126),
        (2, 11, 21, 21040956674)],
      [(15, 2, 161, 549747425215), (11, 5, 60, 194320573071), (7, 8, 30, 68450514933),
        (3, 11, 16, 22726830708)],
      [(16, 2, 203, 549751619567), (12, 5, 75, 194344303983), (8, 8, 37, 68585127679),
        (4, 11, 56, 23524504717)],
      [(17, 2, 255, 549753716731), (13, 5, 94, 194356168353), (9, 8, 46, 68652335071),
        (5, 11, 63, 23913365850)],
      [(18, 2, 321, 549754765310), (14, 5, 118, 194362100266), (10, 8, 58, 68685914107),
        (6, 11, 75, 24105444163), (2, 14, 37, 7439101573)],
      [(19, 2, 404, 549755289599), (15, 5, 149, 194365066155), (11, 8, 72, 68702697471),
        (7, 11, 92, 24200911642), (3, 14, 32, 8035148054)],
      [(20, 2, 508, 549755551743), (16, 5, 187, 194366549082), (12, 8, 91, 68711087615),
        (8, 11, 114, 24248504435), (4, 14, 33, 8317168404)],
      [(21, 2, 639, 549755682815), (17, 5, 236, 194367290541), (13, 8, 114, 68715282303),
        (9, 11, 142, 24272265836), (5, 14, 39, 8454651576)],
      [(22, 2, 802, 549755748351), (18, 5, 296, 194367661270), (14, 8, 144, 68717379551),
        (10, 11, 178, 24284137818), (6, 14, 47, 8522561515), (2, 17, 32, 2630119584)]],
    -- rate exponent 3, stack sizes 15 to 28
    [
      [(9, 3, 51, 388356253389), (5, 6, 15, 135274425229)],
      [(10, 3, 63, 388546205102), (6, 6, 16, 136360984252), (2, 9, 13, 42081913348)],
      [(11, 3, 79, 388641146143), (7, 6, 20, 136901029867), (3, 9, 25, 45453661417)],
      [(12, 3, 99, 388688607967), (8, 6, 48, 137170255358), (4, 9, 24, 47049009435)],
      [(13, 3, 124, 388712336706), (9, 6, 59, 137304670143), (5, 9, 26, 47826731700)],
      [(14, 3, 156, 388724200532), (10, 6, 74, 137371828215), (6, 9, 31, 48210888327),
        (2, 12, 13, 14878203147)],
      [(15, 3, 196, 388730132310), (11, 6, 93, 137405394942), (7, 9, 37, 48401823285),
        (3, 12, 42, 16070296109)],
      [(16, 3, 247, 388733098164), (12, 6, 117, 137422175231), (8, 9, 46, 48497008870),
        (4, 12, 43, 16634336809)],
      [(17, 3, 311, 388734581083), (13, 6, 147, 137430564607), (9, 9, 58, 48544531673),
        (5, 12, 49, 16909303153)],
      [(18, 3, 391, 388735322541), (14, 6, 184, 137434759103), (10, 9, 72, 48568275637),
        (6, 12, 59, 17045123031), (2, 15, 44, 5260239168)],
      [(19, 3, 492, 388735693269), (15, 6, 232, 137436856303), (11, 9, 90, 48580143267),
        (7, 12, 73, 17112628733), (3, 15, 39, 5681707677)],
      [(20, 3, 618, 388735878633), (16, 6, 292, 137437904891), (12, 9, 114, 48586075995),
        (8, 12, 90, 17146281919), (4, 15, 41, 5881126179)],
      [(21, 3, 776, 388735971315), (17, 6, 367, 137438429182), (13, 9, 143, 48589042088),
        (9, 12, 113, 17163083767), (5, 15, 48, 5978341462)],
      [(22, 3, 975, 388736017655), (18, 6, 461, 137438691327), (14, 9, 179, 48590525066),
        (10, 12, 141, 17171478526), (6, 15, 58, 6026361040), (2, 18, 148, 1859775393)]],
    -- rate exponent 4, stack sizes 15 to 28
    [
      [(9, 4, 49, 274609340287), (5, 7, 20, 95653463400)],
      [(10, 4, 61, 274743656431), (6, 7, 23, 96421776654), (2, 10, 21, 29756406294)],
      [(11, 4, 77, 274810789885), (7, 7, 27, 96803646571), (3, 10, 15, 32140592218)],
      [(12, 4, 96, 274844350463), (8, 7, 34, 96994017741), (4, 10, 46, 33268673619)],
      [(13, 4, 121, 274861129215), (9, 7, 42, 97089063347), (5, 10, 51, 33818606307)],
      [(14, 4, 152, 274869518207), (10, 7, 52, 97136551275), (6, 10, 60, 34090246063),
        (2, 13, 25, 10520478337)],
      [(15, 4, 191, 274873712607), (11, 7, 65, 97160286535), (7, 10, 74, 34225257466),
        (3, 13, 21, 11363415354)],
      [(16, 4, 240, 274875809783), (12, 7, 82, 97172151991), (8, 10, 91, 34292563839),
        (4, 13, 95, 11762252358)],
      [(17, 4, 303, 274876858365), (13, 7, 103, 97178084176), (9, 10, 114, 34326167535),
        (5, 13, 109, 11956682925)],
      [(18, 4, 381, 274877382655), (14, 7, 129, 97181050133), (10, 10, 142, 34342957053),
        (6, 13, 130, 12052722081), (2, 16, 42, 3719550786)],
      [(19, 4, 478, 274877644799), (15, 7, 163, 97182533077), (11, 10, 179, 34351348735),
        (7, 13, 161, 12100455821), (3, 16, 38, 4017574027)],
      [(20, 4, 602, 274877775871), (16, 7, 204, 97183274541), (12, 10, 224, 34355543807),
        (8, 13, 198, 12124252217), (4, 16, 41, 4158584202)],
      [(21, 4, 756, 274877841407), (17, 7, 257, 97183645270), (13, 10, 282, 34357641151),
        (9, 13, 247, 12136132918), (5, 16, 288, 4227325788)],
      [(22, 4, 949, 274877874175), (18, 7, 323, 97183830635), (14, 10, 353, 34358689775),
        (10, 13, 309, 12142068909), (6, 16, 339, 4261280757), (2, 19, 81, 1315059792)]]]

/-- The certificate of level `i` of the ladder `(μ, R)` (the default certificate off the table). -/
def certOf (μ R i : ℕ) : Cert :=
  match ((certTable.getD (R - 1) []).getD (μ - 15) []).getD i (1, 1, 2 ^ 20, 2 ^ 39) with
  | (κ, R', e, s) => ⟨κ, R', e, s⟩

/-- **The codes of the deployed ladder `(μ, R)`.** -/
noncomputable def deployedCodes (μ R : ℕ) : ℕ → LevelCode := codesOf (certOf μ R)

/-- The check of a shape at `2^-B`: the ladder against its certificates, level 0's `κ` and rate,
its fold `laneBits`, and its list bound at most `2^18`. -/
def shapeOK (B μ R : ℕ) : Bool :=
  match Whir.ladder μ R with
  | some config => chkLevels B μ (certOf μ R) 0 0 config &&
      decide ((certOf μ R 0).κ = μ - laneBits ∧ (certOf μ R 0).R = R ∧
        (certOf μ R 0).listHi ≤ 2 ^ 18 ∧ (config.head?.map (·.fold)) = some laneBits)
  | none => false

/-- Every admissible shape checks at `2^-128` (kernel evaluation). -/
theorem shapeOK_all : ∀ μ < 29, ∀ R < 5, Whir.Admissible μ R → shapeOK 128 μ R = true := by
  decide +kernel

/-- **The hypotheses of `whirSpec` and `stackedSpec` about the codes**, for every admissible
shape: level 0 folds `laneBits` variables at `κ = μ − laneBits` and rate `R`, the ladder
arithmetic holds, every group escapes with probability at most `2^-128`, and level 0's list
bound is at most `2^18`. -/
theorem deployed_spec_hyps {μ R : ℕ} (h : Whir.Admissible μ R) {level : Whir.Level}
    {rest : List Whir.Level} (hc : deriveConfig μ R = some (level :: rest)) :
    level.fold = laneBits ∧ laneBits ≤ μ ∧ (deployedCodes μ R 0).κ = μ - laneBits ∧
      (deployedCodes μ R 0).R = R ∧ (deployedCodes μ R 0).listMax ≤ 2 ^ 18 ∧
      LadderArith μ (deployedCodes μ R) 0 0 (level :: rest) ∧
      whirEps (deployedCodes μ R) (level :: rest) ≤ (2 : ENNReal)⁻¹ ^ 128 := by
  have hc' : Whir.ladder μ R = some (level :: rest) := hc
  have hok := shapeOK_all μ (by have := h.2.1; unfold Whir.maxLogStack at this; omega) R
    (by have := h.2.2.2; unfold Whir.maxLogInvRate at this; omega) h
  rw [shapeOK, hc'] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hchk, hd⟩ := hok
  obtain ⟨hκ, hR, hL, hf⟩ := of_decide_eq_true hd
  have h0 := chkLevels_head hchk
  have hsound := chkLevels_sound (by norm_num) (by norm_num) _ 0 0 hchk
  have hμ : laneBits ≤ μ := by
    have := h.1
    unfold Whir.minLogStack at this
    unfold laneBits
    omega
  refine ⟨by simpa using hf, hμ, ?_, ?_, ?_, hsound.1, hsound.2⟩
  · rw [deployedCodes, codesOf, mkCode_eq h0]; exact hκ
  · rw [deployedCodes, codesOf, mkCode_eq h0]; exact hR
  · rw [deployedCodes, codesOf, mkCode_eq h0]; exact (Cert.listMax_le h0).trans hL

/-- **Codes with escapes at most `2^-128` exist for every admissible shape.** -/
theorem exists_codes {μ R : ℕ} (h : Whir.Admissible μ R) {config : List Whir.Level}
    (hc : deriveConfig μ R = some config) :
    ∃ codes : ℕ → LevelCode, LadderArith μ codes 0 0 config ∧
      whirEps codes config ≤ (2 : ENNReal)⁻¹ ^ 128 := by
  obtain ⟨level, rest, rfl⟩ : ∃ level rest, config = level :: rest := by
    have := Whir.ladder_length h config hc
    match config, this with
    | level :: rest, _ => exact ⟨level, rest, rfl⟩
  obtain ⟨-, -, -, -, -, hA, hε⟩ := deployed_spec_hyps h hc
  exact ⟨_, hA, hε⟩

end
end LeanVM.Protocol.Whir.Params
