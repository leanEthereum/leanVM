/-
  LeanVM.Guest.B1.Tables.VtC.BGlueGen

  `verify_tables`' bus sides between the selectors and the stream reads, slice by slice
  (generated: scripts/b1c-vt/genbglue.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BGlue
public import LeanVM.Guest.B1.Tables.Vt.SelFw

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
theorem vtB_glue_769 (hl : args.length = 20)  :
    ∀ s ∈ (vtPre.drop 769).take 3, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  exact vt_blockR hl 769 3 [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))

set_option maxRecDepth 100000 in
theorem vtB_glue_784 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i))  :
    ∀ s ∈ (vtPre.drop 784).take 10, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 784 10 [
    .atom (.load (.n 797) (.n 13) 0),
    .atom (.load (.n 798) (.n 13) 1),
    .atom (.load (.n 800) (.n 13) 2)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact (vt_readAt hl 784 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 785 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 787 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_807 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h810 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.dispatch (.n 29) vtImNames [.n 8] [.n 824]))
    (h811 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 824) (.n 781) 1))) :
    ∀ s ∈ (vtPre.drop 807).take 10, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 807 10 [
    .atom (.load (.n 821) (.n 13) 0),
    .dispatch (.n 29) vtImNames [.n 8] [.n 824],
    .atom (.load (.n 824) (.n 781) 1),
    .atom (.load (.n 825) (.n 13) 1),
    .atom (.load (.n 828) (.n 13) 2)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact (vt_readAt hl 807 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact h810
  · exact h811
  · exact (vt_readAt hl 812 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 815 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_826 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h826 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 830) (.n 15) 0))) :
    ∀ s ∈ (vtPre.drop 826).take 4, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 826 4 [
    .atom (.load (.n 830) (.n 15) 0),
    .atom (.load (.n 840) (.n 13) 3)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h826
  · exact (vt_readAt hl 827 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_839 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h839 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 843) (.n 15) 1))) :
    ∀ s ∈ (vtPre.drop 839).take 4, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 839 4 [
    .atom (.load (.n 843) (.n 15) 1),
    .atom (.load (.n 853) (.n 13) 4)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h839
  · exact (vt_readAt hl 840 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_852 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h852 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 856) (.n 15) 2))) :
    ∀ s ∈ (vtPre.drop 852).take 12, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 852 12 [
    .atom (.load (.n 856) (.n 15) 2),
    .atom (.load (.n 866) (.n 13) 5)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h852
  · exact (vt_readAt hl 853 (by decide +kernel) (by decide +kernel) (hw 5 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_877 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h880 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.dispatch (.n 876) vtImNames [.n 8] [.n 894]))
    (h881 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 894) (.n 781) 2))) :
    ∀ s ∈ (vtPre.drop 877).take 66, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 877 66 [
    .atom (.load (.n 891) (.n 13) 0),
    .dispatch (.n 876) vtImNames [.n 8] [.n 894],
    .atom (.load (.n 894) (.n 781) 2),
    .atom (.load (.n 895) (.n 13) 1),
    .atom (.load (.n 898) (.n 13) 2),
    .atom (.load (.n 900) (.n 13) 3),
    .atom (.load (.n 904) (.n 13) 4),
    .atom (.load (.n 908) (.n 13) 5),
    .atom (.load (.n 912) (.n 13) 6),
    .atom (.load (.n 916) (.n 13) 7),
    .atom (.load (.n 920) (.n 13) 8),
    .atom (.load (.n 924) (.n 13) 9),
    .atom (.load (.n 928) (.n 13) 10),
    .atom (.load (.n 932) (.n 13) 11),
    .atom (.load (.n 936) (.n 13) 12),
    .atom (.load (.n 940) (.n 13) 13),
    .atom (.load (.n 944) (.n 13) 14),
    .atom (.load (.n 948) (.n 13) 15)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (vt_readAt hl 877 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact h880
  · exact h881
  · exact (vt_readAt hl 882 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 885 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 887 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 891 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 895 (by decide +kernel) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vt_readAt hl 899 (by decide +kernel) (by decide +kernel) (hw 6 (by norm_num))).2
  · exact (vt_readAt hl 903 (by decide +kernel) (by decide +kernel) (hw 7 (by norm_num))).2
  · exact (vt_readAt hl 907 (by decide +kernel) (by decide +kernel) (hw 8 (by norm_num))).2
  · exact (vt_readAt hl 911 (by decide +kernel) (by decide +kernel) (hw 9 (by norm_num))).2
  · exact (vt_readAt hl 915 (by decide +kernel) (by decide +kernel) (hw 10 (by norm_num))).2
  · exact (vt_readAt hl 919 (by decide +kernel) (by decide +kernel) (hw 11 (by norm_num))).2
  · exact (vt_readAt hl 923 (by decide +kernel) (by decide +kernel) (hw 12 (by norm_num))).2
  · exact (vt_readAt hl 927 (by decide +kernel) (by decide +kernel) (hw 13 (by norm_num))).2
  · exact (vt_readAt hl 931 (by decide +kernel) (by decide +kernel) (hw 14 (by norm_num))).2
  · exact (vt_readAt hl 935 (by decide +kernel) (by decide +kernel) (hw 15 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_1433 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) {Q : ℕ → E}
    (hidx : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 781)) i (Q i))  :
    ∀ s ∈ (vtPre.drop 1433).take 448, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 1433 448 [
    .atom (.load (.n 1395) (.n 13) 0),
    .atom (.load (.n 1398) (.n 13) 0),
    .atom (.load (.n 1402) (.n 13) 3),
    .atom (.load (.n 1406) (.n 13) 0),
    .atom (.load (.n 1412) (.n 13) 0),
    .atom (.load (.n 1418) (.n 13) 0),
    .atom (.load (.n 1425) (.n 13) 0),
    .atom (.load (.n 1428) (.n 13) 0),
    .atom (.load (.n 1432) (.n 13) 3),
    .atom (.load (.n 1438) (.n 13) 0),
    .atom (.load (.n 1444) (.n 13) 0),
    .atom (.load (.n 1450) (.n 13) 0),
    .atom (.load (.n 1458) (.n 13) 0),
    .atom (.load (.n 1461) (.n 13) 0),
    .atom (.load (.n 1465) (.n 13) 3),
    .atom (.load (.n 1471) (.n 13) 0),
    .atom (.load (.n 1479) (.n 13) 0),
    .atom (.load (.n 1482) (.n 13) 0),
    .atom (.load (.n 1486) (.n 13) 3),
    .atom (.load (.n 1492) (.n 13) 0),
    .atom (.load (.n 1498) (.n 13) 0),
    .atom (.load (.n 1504) (.n 13) 0),
    .atom (.load (.n 1512) (.n 13) 0),
    .atom (.load (.n 1515) (.n 13) 0),
    .atom (.load (.n 1519) (.n 13) 3),
    .atom (.load (.n 1525) (.n 13) 0),
    .atom (.load (.n 1531) (.n 13) 0),
    .atom (.load (.n 1537) (.n 13) 0),
    .atom (.load (.n 1545) (.n 13) 0),
    .atom (.load (.n 1548) (.n 13) 0),
    .atom (.load (.n 1552) (.n 13) 3),
    .atom (.load (.n 1558) (.n 13) 0),
    .atom (.load (.n 1564) (.n 13) 0),
    .atom (.load (.n 1570) (.n 13) 0),
    .atom (.load (.n 1576) (.n 13) 0),
    .atom (.load (.n 1582) (.n 13) 0),
    .atom (.load (.n 1588) (.n 13) 0),
    .atom (.load (.n 1594) (.n 13) 0),
    .atom (.load (.n 1600) (.n 13) 0),
    .atom (.load (.n 1606) (.n 13) 0),
    .atom (.load (.n 1612) (.n 13) 0),
    .atom (.load (.n 1618) (.n 13) 0),
    .atom (.load (.n 1624) (.n 13) 0),
    .atom (.load (.n 1630) (.n 13) 0),
    .atom (.load (.n 1636) (.n 13) 0),
    .atom (.load (.n 1640) (.n 13) 3),
    .atom (.load (.n 1644) (.n 13) 4),
    .atom (.load (.n 1650) (.n 13) 0),
    .atom (.load (.n 1654) (.n 13) 3),
    .atom (.load (.n 1658) (.n 13) 4),
    .atom (.load (.n 1664) (.n 13) 0),
    .atom (.load (.n 1668) (.n 13) 3),
    .atom (.load (.n 1672) (.n 13) 4),
    .atom (.load (.n 1678) (.n 13) 0),
    .atom (.load (.n 1682) (.n 13) 3),
    .atom (.load (.n 1686) (.n 13) 4),
    .atom (.load (.n 1692) (.n 13) 0),
    .atom (.load (.n 1696) (.n 13) 3),
    .atom (.load (.n 1700) (.n 13) 4),
    .atom (.load (.n 1706) (.n 13) 0),
    .atom (.load (.n 1710) (.n 13) 3),
    .atom (.load (.n 1714) (.n 13) 4),
    .atom (.load (.n 1720) (.n 13) 0),
    .atom (.load (.n 1724) (.n 13) 3),
    .atom (.load (.n 1728) (.n 13) 4),
    .atom (.load (.n 1734) (.n 13) 0),
    .atom (.load (.n 1738) (.n 13) 3),
    .atom (.load (.n 1742) (.n 13) 4),
    .atom (.load (.n 1748) (.n 13) 0),
    .atom (.load (.n 1752) (.n 13) 3),
    .atom (.load (.n 1758) (.n 13) 0),
    .atom (.load (.n 1762) (.n 13) 3),
    .atom (.load (.n 1766) (.n 13) 4),
    .atom (.load (.n 1772) (.n 13) 0),
    .atom (.load (.n 1776) (.n 13) 3),
    .atom (.load (.n 1780) (.n 13) 4),
    .atom (.load (.n 1786) (.n 13) 0),
    .atom (.load (.n 1790) (.n 13) 3),
    .atom (.load (.n 1794) (.n 13) 4),
    .atom (.load (.n 1800) (.n 13) 0),
    .atom (.load (.n 1804) (.n 13) 3),
    .atom (.load (.n 1808) (.n 13) 4),
    .atom (.load (.n 1822) (.n 13) 0),
    .atom (.load (.n 1823) (.n 13) 1),
    .atom (.load (.n 1827) (.n 13) 2),
    .atom (.load (.n 1836) (.n 13) 0),
    .atom (.load (.n 1839) (.n 781) 1),
    .atom (.load (.n 1840) (.n 13) 1)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (vt_readAt hl 1433 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1436 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1440 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1444 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1450 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1456 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1463 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1466 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1470 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1476 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1482 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1488 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1496 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1499 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1503 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1509 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1517 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1520 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1524 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1530 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1536 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1542 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1550 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1553 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1557 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1563 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1569 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1575 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1583 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1586 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1590 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1596 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1602 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1608 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1614 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1620 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1626 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1632 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1638 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1644 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1650 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1656 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1662 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1668 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1674 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1678 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1682 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1688 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1692 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1696 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1702 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1706 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1710 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1716 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1720 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1724 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1730 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1734 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1738 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1744 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1748 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1752 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1758 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1762 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1766 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1772 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1776 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1780 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1786 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1790 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1796 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1800 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1804 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1810 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1814 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1818 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1824 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1828 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1832 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1838 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1842 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1846 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1860 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1861 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 1865 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 1874 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1877 (by decide +kernel) (by decide +kernel) (hidx 1 (by norm_num))).2
  · exact (vt_readAt hl 1878 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_1890 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) {P : ℕ → E}
    (hpool : ∀ i < 5, LoadHolds rd (vtσ rd wo args (.n 15)) i (P i)) {Q : ℕ → E}
    (hidx : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 781)) i (Q i)) 
    (h1890 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1843) (.n 15) 3)))
    (h1923 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.keccak [.n 837, .n 839, .n 850, .n 852, .n 863, .n 865, .n 1850, .n 1852, .n 20, .n 21, .n 22, .n 23, .n 24] [.n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 1891, .n 1892, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897] false false))) :
    ∀ s ∈ (vtPre.drop 1890).take 34, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 1890 34 [
    .atom (.load (.n 1843) (.n 15) 3),
    .atom (.load (.n 1853) (.n 13) 2),
    .atom (.load (.n 1856) (.n 15) 0),
    .atom (.load (.n 1857) (.n 13) 3),
    .atom (.load (.n 1860) (.n 15) 1),
    .atom (.load (.n 1861) (.n 13) 4),
    .atom (.load (.n 1864) (.n 15) 2),
    .atom (.load (.n 1865) (.n 13) 5),
    .atom (.load (.n 1878) (.n 13) 0),
    .atom (.load (.n 1881) (.n 781) 2),
    .atom (.load (.n 1882) (.n 13) 1),
    .atom (.keccak [.n 837, .n 839, .n 850, .n 852, .n 863, .n 865, .n 1850, .n 1852, .n 20, .n 21, .n 22, .n 23, .n 24] [.n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 1891, .n 1892, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897] false false)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1890
  · exact (vt_readAt hl 1891 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 1894 (by decide +kernel) (by decide +kernel) (hpool 0 (by norm_num))).2
  · exact (vt_readAt hl 1895 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1898 (by decide +kernel) (by decide +kernel) (hpool 1 (by norm_num))).2
  · exact (vt_readAt hl 1899 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1902 (by decide +kernel) (by decide +kernel) (hpool 2 (by norm_num))).2
  · exact (vt_readAt hl 1903 (by decide +kernel) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vt_readAt hl 1916 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1919 (by decide +kernel) (by decide +kernel) (hidx 2 (by norm_num))).2
  · exact (vt_readAt hl 1920 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact h1923

set_option maxRecDepth 100000 in
theorem vtB_glue_1933 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) 
    (h1933 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1898) (.n 15) 4))) :
    ∀ s ∈ (vtPre.drop 1933).take 167, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 1933 167 [
    .atom (.load (.n 1898) (.n 15) 4),
    .atom (.load (.n 1908) (.n 13) 2),
    .atom (.load (.n 1911) (.n 13) 3),
    .atom (.load (.n 1915) (.n 13) 4),
    .atom (.load (.n 1919) (.n 13) 5),
    .atom (.load (.n 1923) (.n 13) 6),
    .atom (.load (.n 1927) (.n 13) 7),
    .atom (.load (.n 1931) (.n 13) 8),
    .atom (.load (.n 1935) (.n 13) 9),
    .atom (.load (.n 1939) (.n 13) 10),
    .atom (.load (.n 1943) (.n 13) 11),
    .atom (.load (.n 1947) (.n 13) 12),
    .atom (.load (.n 1951) (.n 13) 13),
    .atom (.load (.n 1955) (.n 13) 14),
    .atom (.load (.n 1959) (.n 13) 15)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1933
  · exact (vt_readAt hl 1934 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 1937 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1941 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1945 (by decide +kernel) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vt_readAt hl 1949 (by decide +kernel) (by decide +kernel) (hw 6 (by norm_num))).2
  · exact (vt_readAt hl 1953 (by decide +kernel) (by decide +kernel) (hw 7 (by norm_num))).2
  · exact (vt_readAt hl 1957 (by decide +kernel) (by decide +kernel) (hw 8 (by norm_num))).2
  · exact (vt_readAt hl 1961 (by decide +kernel) (by decide +kernel) (hw 9 (by norm_num))).2
  · exact (vt_readAt hl 1965 (by decide +kernel) (by decide +kernel) (hw 10 (by norm_num))).2
  · exact (vt_readAt hl 1969 (by decide +kernel) (by decide +kernel) (hw 11 (by norm_num))).2
  · exact (vt_readAt hl 1973 (by decide +kernel) (by decide +kernel) (hw 12 (by norm_num))).2
  · exact (vt_readAt hl 1977 (by decide +kernel) (by decide +kernel) (hw 13 (by norm_num))).2
  · exact (vt_readAt hl 1981 (by decide +kernel) (by decide +kernel) (hw 14 (by norm_num))).2
  · exact (vt_readAt hl 1985 (by decide +kernel) (by decide +kernel) (hw 15 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_2533 (hl : args.length = 20)  :
    ∀ s ∈ (vtPre.drop 2533).take 56, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  exact vt_blockR hl 2533 56 [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))

end

end
end LeanVM.Guest.B1.Tables
