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
  have g1334 := (vt_goodL (rd := rd) (w := w) hl 1242 [.atom (.copy (.n 1200) (.n 907))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1336 := (vt_goodL (rd := rd) (w := w) hl 1244 [.atom (.copy (.n 1202) (.n 912))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1338 := (vt_goodL (rd := rd) (w := w) hl 1246 [.atom (.copy (.n 1204) (.n 917))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1340 := (vt_goodL (rd := rd) (w := w) hl 1248 [.atom (.copy (.n 1206) (.n 922))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1342 := (vt_goodL (rd := rd) (w := w) hl 1250 [.atom (.copy (.n 1208) (.n 927))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1344 := (vt_goodL (rd := rd) (w := w) hl 1252 [.atom (.copy (.n 1210) (.n 932))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1346 := (vt_goodL (rd := rd) (w := w) hl 1254 [.atom (.copy (.n 1212) (.n 937))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1348 := (vt_goodL (rd := rd) (w := w) hl 1256 [.atom (.copy (.n 1214) (.n 942))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1350 := (vt_goodL (rd := rd) (w := w) hl 1258 [.atom (.copy (.n 1216) (.n 947))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1352 := (vt_goodL (rd := rd) (w := w) hl 1260 [.atom (.copy (.n 1218) (.n 952))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1354 := (vt_goodL (rd := rd) (w := w) hl 1262 [.atom (.copy (.n 1220) (.n 957))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1356 := (vt_goodL (rd := rd) (w := w) hl 1264 [.atom (.copy (.n 1222) (.n 962))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1358 := (vt_goodL (rd := rd) (w := w) hl 1266 [.atom (.copy (.n 1224) (.n 967))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1360 := (vt_goodL (rd := rd) (w := w) hl 1268 [.atom (.copy (.n 1226) (.n 972))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1362 := (vt_goodL (rd := rd) (w := w) hl 1270 [.atom (.copy (.n 1228) (.n 977))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1364 := (vt_goodL (rd := rd) (w := w) hl 1272 [.atom (.copy (.n 1230) (.n 982))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1366 := (vt_goodL (rd := rd) (w := w) hl 1274 [.atom (.copy (.n 1232) (.n 987))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1368 := (vt_goodL (rd := rd) (w := w) hl 1276 [.atom (.copy (.n 1234) (.n 992))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1370 := (vt_goodL (rd := rd) (w := w) hl 1278 [.atom (.copy (.n 1236) (.n 997))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1372 := (vt_goodL (rd := rd) (w := w) hl 1280 [.atom (.copy (.n 1238) (.n 1002))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1374 := (vt_goodL (rd := rd) (w := w) hl 1282 [.atom (.copy (.n 1240) (.n 1007))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1376 := (vt_goodL (rd := rd) (w := w) hl 1284 [.atom (.copy (.n 1242) (.n 1012))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1378 := (vt_goodL (rd := rd) (w := w) hl 1286 [.atom (.copy (.n 1244) (.n 1017))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1380 := (vt_goodL (rd := rd) (w := w) hl 1288 [.atom (.copy (.n 1246) (.n 1022))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1382 := (vt_goodL (rd := rd) (w := w) hl 1290 [.atom (.copy (.n 1248) (.n 1027))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1384 := (vt_goodL (rd := rd) (w := w) hl 1292 [.atom (.copy (.n 1250) (.n 1032))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1386 := (vt_goodL (rd := rd) (w := w) hl 1294 [.atom (.copy (.n 1252) (.n 1037))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1388 := (vt_goodL (rd := rd) (w := w) hl 1296 [.atom (.copy (.n 1254) (.n 1042))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1390 := (vt_goodL (rd := rd) (w := w) hl 1298 [.atom (.copy (.n 1256) (.n 1047))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1392 := (vt_goodL (rd := rd) (w := w) hl 1300 [.atom (.copy (.n 1258) (.n 1052))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1394 := (vt_goodL (rd := rd) (w := w) hl 1302 [.atom (.copy (.n 1260) (.n 1057))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1396 := (vt_goodL (rd := rd) (w := w) hl 1304 [.atom (.copy (.n 1262) (.n 1062))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1398 := (vt_goodL (rd := rd) (w := w) hl 1306 [.atom (.copy (.n 1264) (.n 1067))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1400 := (vt_goodL (rd := rd) (w := w) hl 1308 [.atom (.copy (.n 1266) (.n 1072))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1402 := (vt_goodL (rd := rd) (w := w) hl 1310 [.atom (.copy (.n 1268) (.n 1077))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1404 := (vt_goodL (rd := rd) (w := w) hl 1312 [.atom (.copy (.n 1270) (.n 1082))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1406 := (vt_goodL (rd := rd) (w := w) hl 1314 [.atom (.copy (.n 1272) (.n 1087))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1408 := (vt_goodL (rd := rd) (w := w) hl 1316 [.atom (.copy (.n 1274) (.n 1092))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1410 := (vt_goodL (rd := rd) (w := w) hl 1318 [.atom (.copy (.n 1276) (.n 1097))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1412 := (vt_goodL (rd := rd) (w := w) hl 1320 [.atom (.copy (.n 1278) (.n 1102))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1414 := (vt_goodL (rd := rd) (w := w) hl 1322 [.atom (.copy (.n 1280) (.n 1107))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1416 := (vt_goodL (rd := rd) (w := w) hl 1324 [.atom (.copy (.n 1282) (.n 1112))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1418 := (vt_goodL (rd := rd) (w := w) hl 1326 [.atom (.copy (.n 1284) (.n 1117))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1420 := (vt_goodL (rd := rd) (w := w) hl 1328 [.atom (.copy (.n 1286) (.n 1122))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1422 := (vt_goodL (rd := rd) (w := w) hl 1330 [.atom (.copy (.n 1288) (.n 1127))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1424 := (vt_goodL (rd := rd) (w := w) hl 1332 [.atom (.copy (.n 1290) (.n 1132))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1426 := (vt_goodL (rd := rd) (w := w) hl 1334 [.atom (.copy (.n 1292) (.n 1137))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1428 := (vt_goodL (rd := rd) (w := w) hl 1336 [.atom (.copy (.n 1294) (.n 1142))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1430 := (vt_goodL (rd := rd) (w := w) hl 1338 [.atom (.copy (.n 1296) (.n 1147))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1432 := (vt_goodL (rd := rd) (w := w) hl 1340 [.atom (.copy (.n 1298) (.n 1152))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1434 := (vt_goodL (rd := rd) (w := w) hl 1342 [.atom (.copy (.n 1300) (.n 1157))] (by rw [vtPre_drop]; decide +kernel)).1
  generalize vtσ rd w args = σ at g1334 g1336 g1338 g1340 g1342 g1344 g1346 g1348 g1350 g1352 g1354 g1356 g1358 g1360 g1362 g1364 g1366 g1368 g1370 g1372 g1374 g1376 g1378 g1380 g1382 g1384 g1386 g1388 g1390 g1392 g1394 g1396 g1398 g1400 g1402 g1404 g1406 g1408 g1410 g1412 g1414 g1416 g1418 g1420 g1422 g1424 g1426 g1428 g1430 g1432 g1434 ⊢
  simp only [GoodS, fixNe, Good] at g1334 g1336 g1338 g1340 g1342 g1344 g1346 g1348 g1350 g1352 g1354 g1356 g1358 g1360 g1362 g1364 g1366 g1368 g1370 g1372 g1374 g1376 g1378 g1380 g1382 g1384 g1386 g1388 g1390 g1392 g1394 g1396 g1398 g1400 g1402 g1404 g1406 g1408 g1410 g1412 g1414 g1416 g1418 g1420 g1422 g1424 g1426 g1428 g1430 g1432 g1434
  simp only [VtPullSelsH, g1334, g1336, g1338, g1340, g1342, g1344, g1346, g1348, g1350, g1352, g1354, g1356, g1358, g1360, g1362, g1364, g1366, g1368, g1370, g1372, g1374, g1376, g1378, g1380, g1382, g1384, g1386, g1388, g1390, g1392, g1394, g1396, g1398, g1400, g1402, g1404, g1406, g1408, g1410, g1412, g1414, g1416, g1418, g1420, g1422, g1424, g1426, g1428, g1430, g1432, g1434, and_self]

/-- **`ξ`'s powers**, honestly. -/
theorem vt_xi_good (hl : args.length = 20) :
    vtσ rd w args (.n 2311) = 1 ∧ vtσ rd w args (.n 2312) = vtσ rd w args (.n 2298) ∧
      vtσ rd w args (.n 2313) = vtσ rd w args (.n 2298) ^ 2 ∧
      vtσ rd w args (.n 2314) = vtσ rd w args (.n 2298) ^ 3 ∧
      vtσ rd w args (.n 2315) = vtσ rd w args (.n 2298) ^ 4 := by
  have g := vt_goodL (rd := rd) (w := w) hl 2333 [.atom (.const (.n 2311) (word 1 0)),
    .atom (.mul (.n 2312) (.n 2311) (.n 2298)), .atom (.mul (.n 2313) (.n 2312) (.n 2298)),
    .atom (.mul (.n 2314) (.n 2313) (.n 2298)), .atom (.mul (.n 2315) (.n 2314) (.n 2298))]
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
    vtσ rd w args (.n 2142) = leaves.getD 0 0 ∧ vtσ rd w args (.n 2188) = leaves.getD 1 0 ∧
      vtσ rd w args (.n 2243) = leaves.getD 2 0 := by
  have hp : vtσ rd w args (.n 17) = args.getD 17 0 := vt_param hl (by norm_num)
  have rd0 := vt_read (rd := rd) (w := w) hl 2189 (d := .n 2142) (p := .n 17) (off := 0)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  have rd1 := vt_read (rd := rd) (w := w) hl 2235 (d := .n 2188) (p := .n 17) (off := 1)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  have rd2 := vt_read (rd := rd) (w := w) hl 2290 (d := .n 2243) (p := .n 17) (off := 2)
    (by rw [vtPre_drop]; decide +kernel) (by decide)
  rw [hp] at rd0 rd1 rd2
  have l0 := h 0 (by omega)
  have l1 := h 1 (by omega)
  have l2 := h 2 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [rd0, rdAt, l0.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]
  · rw [rd1, rdAt, l1.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]
  · rw [rd2, rdAt, l2.2, Option.getD_some, List.getD_eq_getElem _ _ (by omega)]

theorem vtPermCap_38 : vtPermCap 38 = [.n 4382, .n 4383, .n 4384, .n 4385, .n 4386] := by
  decide +kernel

theorem vtEvB_152 : vtEvB 152 = 4387 := by decide +kernel

/-- **The sponge after the evaluations**, from the evaluations' sponge facts: the last
permutation's capacity and the last evaluation waiting, its rate cells `σ4388`, `σ4389`. -/
theorem vt_evalFs_good (hl : args.length = 20)
    (hF : ∀ j < 38, (⟨vtCapV (vtσ rd w args) 0, []⟩ : Fs).absorbAll
        ((vtEvs (vtσ rd w args)).take (4 * (j + 1))) dsObserve =
      ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
      vtCapV (vtσ rd w args) (j + 1) = capOf (Fs.perm ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩)) :
    rateOf (vtEvalFs (vtσ rd w args)).pend =
        [vtσ rd w args (.n 4388), vtσ rd w args (.n 4389), 0, 0, 0, 0, 0, 0] ∧
      (vtEvalFs (vtσ rd w args)).cap = [vtσ rd w args (.n 4382), vtσ rd w args (.n 4383),
        vtσ rd w args (.n 4384), vtσ rd w args (.n 4385), vtσ rd w args (.n 4386)] := by
  have g := vt_goodL (rd := rd) (w := w) hl 3964 [.atom (.copy (.n 4388) (.n 4387)),
    .atom (.const (.n 4389) (word 0 1))] (by rw [vtPre_drop]; decide +kernel)
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
