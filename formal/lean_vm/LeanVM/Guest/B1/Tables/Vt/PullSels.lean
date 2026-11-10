/-
  LeanVM.Guest.B1.Tables.Vt.PullSels

  The pull side's table block selectors are the push side's, copied.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vtPullSels0 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1334), σ (.n 1336), σ (.n 1338), σ (.n 1340), σ (.n 1342)] =
      [σ (.n 857), σ (.n 862), σ (.n 867), σ (.n 872), σ (.n 877)] := by
  have a1376 := h.atomAt 1376 (.copy (.n 1334) (.n 857)) (by decide +kernel)
  have a1378 := h.atomAt 1378 (.copy (.n 1336) (.n 862)) (by decide +kernel)
  have a1380 := h.atomAt 1380 (.copy (.n 1338) (.n 867)) (by decide +kernel)
  have a1382 := h.atomAt 1382 (.copy (.n 1340) (.n 872)) (by decide +kernel)
  have a1384 := h.atomAt 1384 (.copy (.n 1342) (.n 877)) (by decide +kernel)
  simp only [Atom.Holds] at a1376 a1378 a1380 a1382 a1384
  rw [a1376, a1378, a1380, a1382, a1384]

theorem vtPullSels1 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1344), σ (.n 1346), σ (.n 1348), σ (.n 1350), σ (.n 1352)] =
      [σ (.n 886), σ (.n 895), σ (.n 904), σ (.n 913), σ (.n 922)] := by
  have a1386 := h.atomAt 1386 (.copy (.n 1344) (.n 886)) (by decide +kernel)
  have a1388 := h.atomAt 1388 (.copy (.n 1346) (.n 895)) (by decide +kernel)
  have a1390 := h.atomAt 1390 (.copy (.n 1348) (.n 904)) (by decide +kernel)
  have a1392 := h.atomAt 1392 (.copy (.n 1350) (.n 913)) (by decide +kernel)
  have a1394 := h.atomAt 1394 (.copy (.n 1352) (.n 922)) (by decide +kernel)
  simp only [Atom.Holds] at a1386 a1388 a1390 a1392 a1394
  rw [a1386, a1388, a1390, a1392, a1394]

theorem vtPullSels2 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1354), σ (.n 1356), σ (.n 1358)] =
      [σ (.n 931), σ (.n 940), σ (.n 949)] := by
  have a1396 := h.atomAt 1396 (.copy (.n 1354) (.n 931)) (by decide +kernel)
  have a1398 := h.atomAt 1398 (.copy (.n 1356) (.n 940)) (by decide +kernel)
  have a1400 := h.atomAt 1400 (.copy (.n 1358) (.n 949)) (by decide +kernel)
  simp only [Atom.Holds] at a1396 a1398 a1400
  rw [a1396, a1398, a1400]

theorem vtPullSels3 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1360), σ (.n 1362), σ (.n 1364), σ (.n 1366), σ (.n 1368)] =
      [σ (.n 958), σ (.n 967), σ (.n 976), σ (.n 985), σ (.n 994)] := by
  have a1402 := h.atomAt 1402 (.copy (.n 1360) (.n 958)) (by decide +kernel)
  have a1404 := h.atomAt 1404 (.copy (.n 1362) (.n 967)) (by decide +kernel)
  have a1406 := h.atomAt 1406 (.copy (.n 1364) (.n 976)) (by decide +kernel)
  have a1408 := h.atomAt 1408 (.copy (.n 1366) (.n 985)) (by decide +kernel)
  have a1410 := h.atomAt 1410 (.copy (.n 1368) (.n 994)) (by decide +kernel)
  simp only [Atom.Holds] at a1402 a1404 a1406 a1408 a1410
  rw [a1402, a1404, a1406, a1408, a1410]

theorem vtPullSels4 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1370), σ (.n 1372), σ (.n 1374), σ (.n 1376), σ (.n 1378)] =
      [σ (.n 1003), σ (.n 1012), σ (.n 1021), σ (.n 1030), σ (.n 1039)] := by
  have a1412 := h.atomAt 1412 (.copy (.n 1370) (.n 1003)) (by decide +kernel)
  have a1414 := h.atomAt 1414 (.copy (.n 1372) (.n 1012)) (by decide +kernel)
  have a1416 := h.atomAt 1416 (.copy (.n 1374) (.n 1021)) (by decide +kernel)
  have a1418 := h.atomAt 1418 (.copy (.n 1376) (.n 1030)) (by decide +kernel)
  have a1420 := h.atomAt 1420 (.copy (.n 1378) (.n 1039)) (by decide +kernel)
  simp only [Atom.Holds] at a1412 a1414 a1416 a1418 a1420
  rw [a1412, a1414, a1416, a1418, a1420]

theorem vtPullSels5 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1380), σ (.n 1382), σ (.n 1384), σ (.n 1386), σ (.n 1388), σ (.n 1390), σ (.n 1392), σ (.n 1394), σ (.n 1396), σ (.n 1398), σ (.n 1400), σ (.n 1402), σ (.n 1404), σ (.n 1406), σ (.n 1408), σ (.n 1410), σ (.n 1412), σ (.n 1414), σ (.n 1416), σ (.n 1418), σ (.n 1420), σ (.n 1422), σ (.n 1424), σ (.n 1426), σ (.n 1428), σ (.n 1430), σ (.n 1432), σ (.n 1434)] =
      [σ (.n 1048), σ (.n 1057), σ (.n 1066), σ (.n 1075), σ (.n 1084), σ (.n 1093), σ (.n 1102), σ (.n 1111), σ (.n 1120), σ (.n 1129), σ (.n 1138), σ (.n 1147), σ (.n 1156), σ (.n 1165), σ (.n 1174), σ (.n 1183), σ (.n 1192), σ (.n 1201), σ (.n 1210), σ (.n 1219), σ (.n 1228), σ (.n 1237), σ (.n 1246), σ (.n 1255), σ (.n 1264), σ (.n 1273), σ (.n 1282), σ (.n 1291)] := by
  have a1422 := h.atomAt 1422 (.copy (.n 1380) (.n 1048)) (by decide +kernel)
  have a1424 := h.atomAt 1424 (.copy (.n 1382) (.n 1057)) (by decide +kernel)
  have a1426 := h.atomAt 1426 (.copy (.n 1384) (.n 1066)) (by decide +kernel)
  have a1428 := h.atomAt 1428 (.copy (.n 1386) (.n 1075)) (by decide +kernel)
  have a1430 := h.atomAt 1430 (.copy (.n 1388) (.n 1084)) (by decide +kernel)
  have a1432 := h.atomAt 1432 (.copy (.n 1390) (.n 1093)) (by decide +kernel)
  have a1434 := h.atomAt 1434 (.copy (.n 1392) (.n 1102)) (by decide +kernel)
  have a1436 := h.atomAt 1436 (.copy (.n 1394) (.n 1111)) (by decide +kernel)
  have a1438 := h.atomAt 1438 (.copy (.n 1396) (.n 1120)) (by decide +kernel)
  have a1440 := h.atomAt 1440 (.copy (.n 1398) (.n 1129)) (by decide +kernel)
  have a1442 := h.atomAt 1442 (.copy (.n 1400) (.n 1138)) (by decide +kernel)
  have a1444 := h.atomAt 1444 (.copy (.n 1402) (.n 1147)) (by decide +kernel)
  have a1446 := h.atomAt 1446 (.copy (.n 1404) (.n 1156)) (by decide +kernel)
  have a1448 := h.atomAt 1448 (.copy (.n 1406) (.n 1165)) (by decide +kernel)
  have a1450 := h.atomAt 1450 (.copy (.n 1408) (.n 1174)) (by decide +kernel)
  have a1452 := h.atomAt 1452 (.copy (.n 1410) (.n 1183)) (by decide +kernel)
  have a1454 := h.atomAt 1454 (.copy (.n 1412) (.n 1192)) (by decide +kernel)
  have a1456 := h.atomAt 1456 (.copy (.n 1414) (.n 1201)) (by decide +kernel)
  have a1458 := h.atomAt 1458 (.copy (.n 1416) (.n 1210)) (by decide +kernel)
  have a1460 := h.atomAt 1460 (.copy (.n 1418) (.n 1219)) (by decide +kernel)
  have a1462 := h.atomAt 1462 (.copy (.n 1420) (.n 1228)) (by decide +kernel)
  have a1464 := h.atomAt 1464 (.copy (.n 1422) (.n 1237)) (by decide +kernel)
  have a1466 := h.atomAt 1466 (.copy (.n 1424) (.n 1246)) (by decide +kernel)
  have a1468 := h.atomAt 1468 (.copy (.n 1426) (.n 1255)) (by decide +kernel)
  have a1470 := h.atomAt 1470 (.copy (.n 1428) (.n 1264)) (by decide +kernel)
  have a1472 := h.atomAt 1472 (.copy (.n 1430) (.n 1273)) (by decide +kernel)
  have a1474 := h.atomAt 1474 (.copy (.n 1432) (.n 1282)) (by decide +kernel)
  have a1476 := h.atomAt 1476 (.copy (.n 1434) (.n 1291)) (by decide +kernel)
  simp only [Atom.Holds] at a1422 a1424 a1426 a1428 a1430 a1432 a1434 a1436 a1438 a1440 a1442 a1444 a1446 a1448 a1450 a1452 a1454 a1456 a1458 a1460 a1462 a1464 a1466 a1468 a1470 a1472 a1474 a1476
  rw [a1422, a1424, a1426, a1428, a1430, a1432, a1434, a1436, a1438, a1440, a1442, a1444, a1446, a1448, a1450, a1452, a1454, a1456, a1458, a1460, a1462, a1464, a1466, a1468, a1470, a1472, a1474, a1476]

end
end LeanVM.Guest.B1.Tables
