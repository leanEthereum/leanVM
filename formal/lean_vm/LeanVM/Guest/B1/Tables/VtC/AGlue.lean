/-
  LeanVM.Guest.B1.Tables.VtC.AGlue

  What the honest valuation's equations give between `verify_tables`' ranges: the pull side's
  selectors, `ξ`'s powers, the GKR leaf values read, the sponge after the evaluations.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup
public import LeanVM.Guest.B1.Tables.VtC.FFinal
public import LeanVM.Guest.B1.Tables.VtC.FData

/-!
# Between the ranges

`vt_pull_good`: the pull side's selectors are the push side's. `vt_xi_good`: `ξ`'s powers.
`vt_leaves_good`: the three GKR leaf values are `gkr_leaves`' words. `vt_evalFs_good`: the
sponge after the `153` evaluations is the last permutation's capacity with the last evaluation
waiting, its rate cells `σ4688`, `σ4689`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

set_option maxRecDepth 10000 in
/-- **The pull side's selectors are the push side's**, honestly. -/
theorem vt_pull_good (hl : args.length = 20) : VtPullSelsH (vtσ rd w args) := by
  have g1334 := (vt_goodL (rd := rd) (w := w) hl 1182 [.atom (.copy (.n 1152) (.n 859))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1336 := (vt_goodL (rd := rd) (w := w) hl 1184 [.atom (.copy (.n 1154) (.n 864))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1338 := (vt_goodL (rd := rd) (w := w) hl 1186 [.atom (.copy (.n 1156) (.n 869))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1340 := (vt_goodL (rd := rd) (w := w) hl 1188 [.atom (.copy (.n 1158) (.n 874))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1342 := (vt_goodL (rd := rd) (w := w) hl 1190 [.atom (.copy (.n 1160) (.n 879))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1344 := (vt_goodL (rd := rd) (w := w) hl 1192 [.atom (.copy (.n 1162) (.n 884))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1346 := (vt_goodL (rd := rd) (w := w) hl 1194 [.atom (.copy (.n 1164) (.n 889))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1348 := (vt_goodL (rd := rd) (w := w) hl 1196 [.atom (.copy (.n 1166) (.n 894))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1350 := (vt_goodL (rd := rd) (w := w) hl 1198 [.atom (.copy (.n 1168) (.n 899))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1352 := (vt_goodL (rd := rd) (w := w) hl 1200 [.atom (.copy (.n 1170) (.n 904))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1354 := (vt_goodL (rd := rd) (w := w) hl 1202 [.atom (.copy (.n 1172) (.n 909))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1356 := (vt_goodL (rd := rd) (w := w) hl 1204 [.atom (.copy (.n 1174) (.n 914))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1358 := (vt_goodL (rd := rd) (w := w) hl 1206 [.atom (.copy (.n 1176) (.n 919))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1360 := (vt_goodL (rd := rd) (w := w) hl 1208 [.atom (.copy (.n 1178) (.n 924))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1362 := (vt_goodL (rd := rd) (w := w) hl 1210 [.atom (.copy (.n 1180) (.n 929))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1364 := (vt_goodL (rd := rd) (w := w) hl 1212 [.atom (.copy (.n 1182) (.n 934))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1366 := (vt_goodL (rd := rd) (w := w) hl 1214 [.atom (.copy (.n 1184) (.n 939))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1368 := (vt_goodL (rd := rd) (w := w) hl 1216 [.atom (.copy (.n 1186) (.n 944))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1370 := (vt_goodL (rd := rd) (w := w) hl 1218 [.atom (.copy (.n 1188) (.n 949))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1372 := (vt_goodL (rd := rd) (w := w) hl 1220 [.atom (.copy (.n 1190) (.n 954))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1374 := (vt_goodL (rd := rd) (w := w) hl 1222 [.atom (.copy (.n 1192) (.n 959))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1376 := (vt_goodL (rd := rd) (w := w) hl 1224 [.atom (.copy (.n 1194) (.n 964))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1378 := (vt_goodL (rd := rd) (w := w) hl 1226 [.atom (.copy (.n 1196) (.n 969))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1380 := (vt_goodL (rd := rd) (w := w) hl 1228 [.atom (.copy (.n 1198) (.n 974))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1382 := (vt_goodL (rd := rd) (w := w) hl 1230 [.atom (.copy (.n 1200) (.n 979))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1384 := (vt_goodL (rd := rd) (w := w) hl 1232 [.atom (.copy (.n 1202) (.n 984))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1386 := (vt_goodL (rd := rd) (w := w) hl 1234 [.atom (.copy (.n 1204) (.n 989))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1388 := (vt_goodL (rd := rd) (w := w) hl 1236 [.atom (.copy (.n 1206) (.n 994))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1390 := (vt_goodL (rd := rd) (w := w) hl 1238 [.atom (.copy (.n 1208) (.n 999))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1392 := (vt_goodL (rd := rd) (w := w) hl 1240 [.atom (.copy (.n 1210) (.n 1004))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1394 := (vt_goodL (rd := rd) (w := w) hl 1242 [.atom (.copy (.n 1212) (.n 1009))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1396 := (vt_goodL (rd := rd) (w := w) hl 1244 [.atom (.copy (.n 1214) (.n 1014))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1398 := (vt_goodL (rd := rd) (w := w) hl 1246 [.atom (.copy (.n 1216) (.n 1019))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1400 := (vt_goodL (rd := rd) (w := w) hl 1248 [.atom (.copy (.n 1218) (.n 1024))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1402 := (vt_goodL (rd := rd) (w := w) hl 1250 [.atom (.copy (.n 1220) (.n 1029))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1404 := (vt_goodL (rd := rd) (w := w) hl 1252 [.atom (.copy (.n 1222) (.n 1034))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1406 := (vt_goodL (rd := rd) (w := w) hl 1254 [.atom (.copy (.n 1224) (.n 1039))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1408 := (vt_goodL (rd := rd) (w := w) hl 1256 [.atom (.copy (.n 1226) (.n 1044))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1410 := (vt_goodL (rd := rd) (w := w) hl 1258 [.atom (.copy (.n 1228) (.n 1049))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1412 := (vt_goodL (rd := rd) (w := w) hl 1260 [.atom (.copy (.n 1230) (.n 1054))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1414 := (vt_goodL (rd := rd) (w := w) hl 1262 [.atom (.copy (.n 1232) (.n 1059))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1416 := (vt_goodL (rd := rd) (w := w) hl 1264 [.atom (.copy (.n 1234) (.n 1064))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1418 := (vt_goodL (rd := rd) (w := w) hl 1266 [.atom (.copy (.n 1236) (.n 1069))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1420 := (vt_goodL (rd := rd) (w := w) hl 1268 [.atom (.copy (.n 1238) (.n 1074))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1422 := (vt_goodL (rd := rd) (w := w) hl 1270 [.atom (.copy (.n 1240) (.n 1079))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1424 := (vt_goodL (rd := rd) (w := w) hl 1272 [.atom (.copy (.n 1242) (.n 1084))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1426 := (vt_goodL (rd := rd) (w := w) hl 1274 [.atom (.copy (.n 1244) (.n 1089))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1428 := (vt_goodL (rd := rd) (w := w) hl 1276 [.atom (.copy (.n 1246) (.n 1094))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1430 := (vt_goodL (rd := rd) (w := w) hl 1278 [.atom (.copy (.n 1248) (.n 1099))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1432 := (vt_goodL (rd := rd) (w := w) hl 1280 [.atom (.copy (.n 1250) (.n 1104))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1434 := (vt_goodL (rd := rd) (w := w) hl 1282 [.atom (.copy (.n 1252) (.n 1109))] (by rw [vtPre_drop]; decide +kernel)).1
  generalize vtσ rd w args = σ at g1334 g1336 g1338 g1340 g1342 g1344 g1346 g1348 g1350 g1352 g1354 g1356 g1358 g1360 g1362 g1364 g1366 g1368 g1370 g1372 g1374 g1376 g1378 g1380 g1382 g1384 g1386 g1388 g1390 g1392 g1394 g1396 g1398 g1400 g1402 g1404 g1406 g1408 g1410 g1412 g1414 g1416 g1418 g1420 g1422 g1424 g1426 g1428 g1430 g1432 g1434 ⊢
  simp only [GoodS, fixNe, Good] at g1334 g1336 g1338 g1340 g1342 g1344 g1346 g1348 g1350 g1352 g1354 g1356 g1358 g1360 g1362 g1364 g1366 g1368 g1370 g1372 g1374 g1376 g1378 g1380 g1382 g1384 g1386 g1388 g1390 g1392 g1394 g1396 g1398 g1400 g1402 g1404 g1406 g1408 g1410 g1412 g1414 g1416 g1418 g1420 g1422 g1424 g1426 g1428 g1430 g1432 g1434
  simp only [VtPullSelsH, g1334, g1336, g1338, g1340, g1342, g1344, g1346, g1348, g1350, g1352, g1354, g1356, g1358, g1360, g1362, g1364, g1366, g1368, g1370, g1372, g1374, g1376, g1378, g1380, g1382, g1384, g1386, g1388, g1390, g1392, g1394, g1396, g1398, g1400, g1402, g1404, g1406, g1408, g1410, g1412, g1414, g1416, g1418, g1420, g1422, g1424, g1426, g1428, g1430, g1432, g1434, and_self]

/-- **`ξ`'s powers**, honestly. -/
theorem vt_xi_good (hl : args.length = 20) :
    vtσ rd w args (.n 2263) = 1 ∧ vtσ rd w args (.n 2264) = vtσ rd w args (.n 2250) ∧
      vtσ rd w args (.n 2265) = vtσ rd w args (.n 2250) ^ 2 ∧
      vtσ rd w args (.n 2266) = vtσ rd w args (.n 2250) ^ 3 ∧
      vtσ rd w args (.n 2267) = vtσ rd w args (.n 2250) ^ 4 := by
  have g := vt_goodL (rd := rd) (w := w) hl 2273 [.atom (.const (.n 2263) (word 1 0)),
    .atom (.mul (.n 2264) (.n 2263) (.n 2250)), .atom (.mul (.n 2265) (.n 2264) (.n 2250)),
    .atom (.mul (.n 2266) (.n 2265) (.n 2250)), .atom (.mul (.n 2267) (.n 2266) (.n 2250))]
    (by rw [vtPre_drop]; decide +kernel)
  generalize vtσ rd w args = σ at g ⊢
  simp only [GoodL, GoodS, fixNe, Good, Nat.reduceLT, and_self, ↓reduceIte, and_true] at g
  obtain ⟨g0, g1, g2, g3, g4⟩ := g
  rw [tb_word_one] at g0
  refine ⟨g0, ?_, ?_, ?_, ?_⟩
  · rw [g1, g0, one_mul]
  · rw [g2, g1, g0, one_mul, sq]
  · rw [g3, g2, g1, g0, one_mul]; ring
  · rw [g4, g3, g2, g1, g0, one_mul]; ring

/-- **The GKR leaf values** are read from `gkr_leaves` (`args 17`). -/
theorem vt_leaves_good (hl : args.length = 20) {leaves : List E} (hll : leaves.length = 3)
    (h : TbReadsAt rd (args.getD 17 0) leaves) :
    vtσ rd w args (.n 2094) = leaves.getD 0 0 ∧ vtσ rd w args (.n 2140) = leaves.getD 1 0 ∧
      vtσ rd w args (.n 2195) = leaves.getD 2 0 := by
  have hp : vtσ rd w args (.n 17) = args.getD 17 0 := vt_param hl (by norm_num)
  have rd0 := vt_read (rd := rd) (w := w) hl 2129 (d := .n 2094) (p := .n 17) (off := 0)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  have rd1 := vt_read (rd := rd) (w := w) hl 2175 (d := .n 2140) (p := .n 17) (off := 1)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  have rd2 := vt_read (rd := rd) (w := w) hl 2230 (d := .n 2195) (p := .n 17) (off := 2)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  rw [hp] at rd0 rd1 rd2
  have l0 := h 0 (by omega)
  have l1 := h 1 (by omega)
  have l2 := h 2 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [rd0, rdAt, l0.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]
  · rw [rd1, rdAt, l1.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]
  · rw [rd2, rdAt, l2.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]

theorem vtPermCap_38 : vtPermCap 38 = [.n 4334, .n 4335, .n 4336, .n 4337, .n 4338] := by
  decide +kernel

theorem vtEvB_152 : vtEvB 152 = 4339 := by decide +kernel

/-- **The sponge after the evaluations**, from the evaluations' sponge facts: the last
permutation's capacity and the last evaluation waiting, its rate cells `σ4688`, `σ4689`. -/
theorem vt_evalFs_good (hl : args.length = 20)
    (hF : ∀ j < 38, (⟨vtCapV (vtσ rd w args) 0, []⟩ : Fs).absorbAll
        ((vtEvs (vtσ rd w args)).take (4 * (j + 1))) dsObserve =
      ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
      vtCapV (vtσ rd w args) (j + 1) = capOf (Fs.perm ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩)) :
    rateOf (vtEvalFs (vtσ rd w args)).pend =
        [vtσ rd w args (.n 4340), vtσ rd w args (.n 4341), 0, 0, 0, 0, 0, 0] ∧
      (vtEvalFs (vtσ rd w args)).cap = [vtσ rd w args (.n 4334), vtσ rd w args (.n 4335),
        vtσ rd w args (.n 4336), vtσ rd w args (.n 4337), vtσ rd w args (.n 4338)] := by
  have g := vt_goodL (rd := rd) (w := w) hl 3904 [.atom (.copy (.n 4340) (.n 4339)),
    .atom (.const (.n 4341) (word 0 1))] (by rw [vtPre_drop]; decide +kernel)
  generalize vtσ rd w args = σ at g hF ⊢
  simp only [GoodL, GoodS, fixNe, Good, and_true] at g
  obtain ⟨g0, g1⟩ := g
  obtain ⟨h37, hp37⟩ := hF 37 (by norm_num)
  have hr : vtEvs σ = (List.range 152).map (fun k ↦ σ (.n (vtEvB k))) ++
      [σ (.n (vtEvB 152))] := by
    show (List.range (152 + 1)).map _ = _
    rw [List.range_succ, List.map_append, List.map_singleton]
  have ht : (vtEvs σ).take (4 * (37 + 1)) = (List.range 152).map fun k ↦ σ (.n (vtEvB k)) := by
    rw [hr, List.take_left' (by simp)]
  rw [ht] at h37
  have hE : vtEvalFs σ = ⟨vtCapV σ 38, [(σ (.n (vtEvB 152)), dsObserve)]⟩ := by
    rw [vtEvalFs, hr, fs_absorbAll_append, h37, tb_absorbAll_full' _ (by simp [vtEvs]) _
      (by simp) (by simp), ← hp37]
    rfl
  rw [hE, rateOf_eq_cells _ (by simp), vtEvB_152]
  refine ⟨?_, ?_⟩
  · simp only [pendCells, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons,
      List.length_nil, Keccak.scalarCells, g0, g1]
    rfl
  · simp [vtCapV, vtPermCap_38]

end

end
end LeanVM.Guest.B1.Tables
