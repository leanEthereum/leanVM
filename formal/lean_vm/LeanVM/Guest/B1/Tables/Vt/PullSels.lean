/-
  LeanVM.Guest.B1.Tables.Vt.PullSels

  The pull side's table block selectors are the push side's, copied.

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vtPullSels0 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1335), σ (.n 1337), σ (.n 1339), σ (.n 1341), σ (.n 1343)] =
      [σ (.n 858), σ (.n 863), σ (.n 868), σ (.n 873), σ (.n 878)] := by
  have a1376 := h.atomAt 1376 (.copy (.n 1335) (.n 858)) (by decide +kernel)
  have a1378 := h.atomAt 1378 (.copy (.n 1337) (.n 863)) (by decide +kernel)
  have a1380 := h.atomAt 1380 (.copy (.n 1339) (.n 868)) (by decide +kernel)
  have a1382 := h.atomAt 1382 (.copy (.n 1341) (.n 873)) (by decide +kernel)
  have a1384 := h.atomAt 1384 (.copy (.n 1343) (.n 878)) (by decide +kernel)
  simp only [Atom.Holds] at a1376 a1378 a1380 a1382 a1384
  rw [a1376, a1378, a1380, a1382, a1384]

theorem vtPullSels1 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1345), σ (.n 1347), σ (.n 1349), σ (.n 1351), σ (.n 1353)] =
      [σ (.n 887), σ (.n 896), σ (.n 905), σ (.n 914), σ (.n 923)] := by
  have a1386 := h.atomAt 1386 (.copy (.n 1345) (.n 887)) (by decide +kernel)
  have a1388 := h.atomAt 1388 (.copy (.n 1347) (.n 896)) (by decide +kernel)
  have a1390 := h.atomAt 1390 (.copy (.n 1349) (.n 905)) (by decide +kernel)
  have a1392 := h.atomAt 1392 (.copy (.n 1351) (.n 914)) (by decide +kernel)
  have a1394 := h.atomAt 1394 (.copy (.n 1353) (.n 923)) (by decide +kernel)
  simp only [Atom.Holds] at a1386 a1388 a1390 a1392 a1394
  rw [a1386, a1388, a1390, a1392, a1394]

theorem vtPullSels2 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1355), σ (.n 1357), σ (.n 1359)] =
      [σ (.n 932), σ (.n 941), σ (.n 950)] := by
  have a1396 := h.atomAt 1396 (.copy (.n 1355) (.n 932)) (by decide +kernel)
  have a1398 := h.atomAt 1398 (.copy (.n 1357) (.n 941)) (by decide +kernel)
  have a1400 := h.atomAt 1400 (.copy (.n 1359) (.n 950)) (by decide +kernel)
  simp only [Atom.Holds] at a1396 a1398 a1400
  rw [a1396, a1398, a1400]

theorem vtPullSels3 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1361), σ (.n 1363), σ (.n 1365), σ (.n 1367), σ (.n 1369)] =
      [σ (.n 959), σ (.n 968), σ (.n 977), σ (.n 986), σ (.n 995)] := by
  have a1402 := h.atomAt 1402 (.copy (.n 1361) (.n 959)) (by decide +kernel)
  have a1404 := h.atomAt 1404 (.copy (.n 1363) (.n 968)) (by decide +kernel)
  have a1406 := h.atomAt 1406 (.copy (.n 1365) (.n 977)) (by decide +kernel)
  have a1408 := h.atomAt 1408 (.copy (.n 1367) (.n 986)) (by decide +kernel)
  have a1410 := h.atomAt 1410 (.copy (.n 1369) (.n 995)) (by decide +kernel)
  simp only [Atom.Holds] at a1402 a1404 a1406 a1408 a1410
  rw [a1402, a1404, a1406, a1408, a1410]

theorem vtPullSels4 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1371), σ (.n 1373), σ (.n 1375), σ (.n 1377), σ (.n 1379)] =
      [σ (.n 1004), σ (.n 1013), σ (.n 1022), σ (.n 1031), σ (.n 1040)] := by
  have a1412 := h.atomAt 1412 (.copy (.n 1371) (.n 1004)) (by decide +kernel)
  have a1414 := h.atomAt 1414 (.copy (.n 1373) (.n 1013)) (by decide +kernel)
  have a1416 := h.atomAt 1416 (.copy (.n 1375) (.n 1022)) (by decide +kernel)
  have a1418 := h.atomAt 1418 (.copy (.n 1377) (.n 1031)) (by decide +kernel)
  have a1420 := h.atomAt 1420 (.copy (.n 1379) (.n 1040)) (by decide +kernel)
  simp only [Atom.Holds] at a1412 a1414 a1416 a1418 a1420
  rw [a1412, a1414, a1416, a1418, a1420]

theorem vtPullSels5 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1381), σ (.n 1383), σ (.n 1385), σ (.n 1387), σ (.n 1389), σ (.n 1391), σ (.n 1393), σ (.n 1395), σ (.n 1397), σ (.n 1399), σ (.n 1401), σ (.n 1403), σ (.n 1405), σ (.n 1407), σ (.n 1409), σ (.n 1411), σ (.n 1413), σ (.n 1415), σ (.n 1417), σ (.n 1419), σ (.n 1421), σ (.n 1423), σ (.n 1425), σ (.n 1427), σ (.n 1429), σ (.n 1431), σ (.n 1433), σ (.n 1435)] =
      [σ (.n 1049), σ (.n 1058), σ (.n 1067), σ (.n 1076), σ (.n 1085), σ (.n 1094), σ (.n 1103), σ (.n 1112), σ (.n 1121), σ (.n 1130), σ (.n 1139), σ (.n 1148), σ (.n 1157), σ (.n 1166), σ (.n 1175), σ (.n 1184), σ (.n 1193), σ (.n 1202), σ (.n 1211), σ (.n 1220), σ (.n 1229), σ (.n 1238), σ (.n 1247), σ (.n 1256), σ (.n 1265), σ (.n 1274), σ (.n 1283), σ (.n 1292)] := by
  have a1422 := h.atomAt 1422 (.copy (.n 1381) (.n 1049)) (by decide +kernel)
  have a1424 := h.atomAt 1424 (.copy (.n 1383) (.n 1058)) (by decide +kernel)
  have a1426 := h.atomAt 1426 (.copy (.n 1385) (.n 1067)) (by decide +kernel)
  have a1428 := h.atomAt 1428 (.copy (.n 1387) (.n 1076)) (by decide +kernel)
  have a1430 := h.atomAt 1430 (.copy (.n 1389) (.n 1085)) (by decide +kernel)
  have a1432 := h.atomAt 1432 (.copy (.n 1391) (.n 1094)) (by decide +kernel)
  have a1434 := h.atomAt 1434 (.copy (.n 1393) (.n 1103)) (by decide +kernel)
  have a1436 := h.atomAt 1436 (.copy (.n 1395) (.n 1112)) (by decide +kernel)
  have a1438 := h.atomAt 1438 (.copy (.n 1397) (.n 1121)) (by decide +kernel)
  have a1440 := h.atomAt 1440 (.copy (.n 1399) (.n 1130)) (by decide +kernel)
  have a1442 := h.atomAt 1442 (.copy (.n 1401) (.n 1139)) (by decide +kernel)
  have a1444 := h.atomAt 1444 (.copy (.n 1403) (.n 1148)) (by decide +kernel)
  have a1446 := h.atomAt 1446 (.copy (.n 1405) (.n 1157)) (by decide +kernel)
  have a1448 := h.atomAt 1448 (.copy (.n 1407) (.n 1166)) (by decide +kernel)
  have a1450 := h.atomAt 1450 (.copy (.n 1409) (.n 1175)) (by decide +kernel)
  have a1452 := h.atomAt 1452 (.copy (.n 1411) (.n 1184)) (by decide +kernel)
  have a1454 := h.atomAt 1454 (.copy (.n 1413) (.n 1193)) (by decide +kernel)
  have a1456 := h.atomAt 1456 (.copy (.n 1415) (.n 1202)) (by decide +kernel)
  have a1458 := h.atomAt 1458 (.copy (.n 1417) (.n 1211)) (by decide +kernel)
  have a1460 := h.atomAt 1460 (.copy (.n 1419) (.n 1220)) (by decide +kernel)
  have a1462 := h.atomAt 1462 (.copy (.n 1421) (.n 1229)) (by decide +kernel)
  have a1464 := h.atomAt 1464 (.copy (.n 1423) (.n 1238)) (by decide +kernel)
  have a1466 := h.atomAt 1466 (.copy (.n 1425) (.n 1247)) (by decide +kernel)
  have a1468 := h.atomAt 1468 (.copy (.n 1427) (.n 1256)) (by decide +kernel)
  have a1470 := h.atomAt 1470 (.copy (.n 1429) (.n 1265)) (by decide +kernel)
  have a1472 := h.atomAt 1472 (.copy (.n 1431) (.n 1274)) (by decide +kernel)
  have a1474 := h.atomAt 1474 (.copy (.n 1433) (.n 1283)) (by decide +kernel)
  have a1476 := h.atomAt 1476 (.copy (.n 1435) (.n 1292)) (by decide +kernel)
  simp only [Atom.Holds] at a1422 a1424 a1426 a1428 a1430 a1432 a1434 a1436 a1438 a1440 a1442 a1444 a1446 a1448 a1450 a1452 a1454 a1456 a1458 a1460 a1462 a1464 a1466 a1468 a1470 a1472 a1474 a1476
  rw [a1422, a1424, a1426, a1428, a1430, a1432, a1434, a1436, a1438, a1440, a1442, a1444, a1446, a1448, a1450, a1452, a1454, a1456, a1458, a1460, a1462, a1464, a1466, a1468, a1470, a1472, a1474, a1476]

end
end LeanVM.Guest.B1.Tables
