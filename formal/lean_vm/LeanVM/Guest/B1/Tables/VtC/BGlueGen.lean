/-
  LeanVM.Guest.B1.Tables.VtC.BGlueGen

  `verify_tables`' bus sides outside the selectors, slice by slice (generated:
  scripts/b1c-vt/genbglue.py).

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
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
theorem vtB_glue_765 (hl : args.length = 20)  :
    ∀ s ∈ (vtPre.drop 765).take 1, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  exact vt_blockR hl 765 1 [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))

set_option maxRecDepth 100000 in
theorem vtB_glue_778 (hl : args.length = 20)  :
    ∀ s ∈ (vtPre.drop 778).take 3, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  exact vt_blockR hl 778 3 [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))

set_option maxRecDepth 100000 in
theorem vtB_glue_794 (hl : args.length = 20) {C : ℕ → E}
    (hcur : ∀ i < 7, LoadHolds rd (vtσ rd wo args (.n 5)) i (C i)) 
    (h795 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.dispatch (.n 26) vtImNames [.n 8] [.n 809]))
    (h797 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 809) (.n 777) 1)))
    (h802 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 812) (.n 15) 0)))
    (h807 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 816) (.n 15) 1))) :
    ∀ s ∈ (vtPre.drop 794).take 17, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 794 17 [
    .dispatch (.n 26) vtImNames [.n 8] [.n 809],
    .atom (.load (.n 809) (.n 777) 1),
    .atom (.load (.n 812) (.n 5) 0),
    .atom (.load (.n 812) (.n 15) 0),
    .atom (.load (.n 816) (.n 5) 1),
    .atom (.load (.n 816) (.n 15) 1)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h795
  · exact h797
  · exact (vt_readAt hl 799 (by decide +kernel) (by decide +kernel) (hcur 0 (by norm_num))).2
  · exact h802
  · exact (vt_readAt hl 804 (by decide +kernel) (by decide +kernel) (hcur 1 (by norm_num))).2
  · exact h807

set_option maxRecDepth 100000 in
theorem vtB_glue_824 (hl : args.length = 20) 
    (h825 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.dispatch (.n 821) vtImNames [.n 8] [.n 837]))
    (h827 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 837) (.n 777) 2))) :
    ∀ s ∈ (vtPre.drop 824).take 18, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 824 18 [
    .dispatch (.n 821) vtImNames [.n 8] [.n 837],
    .atom (.load (.n 837) (.n 777) 2)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact h825
  · exact h827

set_option maxRecDepth 100000 in
theorem vtB_glue_1332 (hl : args.length = 20) {P : ℕ → E}
    (hpool : ∀ i < 4, LoadHolds rd (vtσ rd wo args (.n 15)) i (P i)) {Q : ℕ → E}
    (hidx : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 777)) i (Q i)) {C : ℕ → E}
    (hcur : ∀ i < 7, LoadHolds rd (vtσ rd wo args (.n 5)) i (C i)) 
    (h1345 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1302) (.n 15) 2)))
    (h1360 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1316) (.n 15) 3))) :
    ∀ s ∈ (vtPre.drop 1332).take 147, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 1332 147 [
    .atom (.load (.n 1301) (.n 777) 1),
    .atom (.load (.n 1302) (.n 5) 2),
    .atom (.load (.n 1302) (.n 15) 2),
    .atom (.load (.n 1306) (.n 15) 0),
    .atom (.load (.n 1308) (.n 15) 1),
    .atom (.load (.n 1315) (.n 777) 2),
    .atom (.load (.n 1316) (.n 5) 3),
    .atom (.load (.n 1316) (.n 15) 3)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (vt_readAt hl 1341 (by decide +kernel) (by decide +kernel) (hidx 1 (by norm_num))).2
  · exact (vt_readAt hl 1342 (by decide +kernel) (by decide +kernel) (hcur 2 (by norm_num))).2
  · exact h1345
  · exact (vt_readAt hl 1347 (by decide +kernel) (by decide +kernel) (hpool 0 (by norm_num))).2
  · exact (vt_readAt hl 1349 (by decide +kernel) (by decide +kernel) (hpool 1 (by norm_num))).2
  · exact (vt_readAt hl 1356 (by decide +kernel) (by decide +kernel) (hidx 2 (by norm_num))).2
  · exact (vt_readAt hl 1357 (by decide +kernel) (by decide +kernel) (hcur 3 (by norm_num))).2
  · exact h1360

set_option maxRecDepth 100000 in
theorem vtB_glue_1912 (hl : args.length = 20) {C : ℕ → E}
    (hcur : ∀ i < 7, LoadHolds rd (vtσ rd wo args (.n 5)) i (C i))  :
    ∀ s ∈ (vtPre.drop 1912).take 14, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 1912 14 [
    .atom (.keccak [.n 813, .n 814, .n 817, .n 818, .n 1303, .n 1304, .n 1317, .n 1318, .n 20, .n 21, .n 22, .n 23, .n 24] [.n 1827, .n 1828, .n 1829, .n 1830, .n 1831, .n 1832, .n 1833, .n 1834, .n 1835, .n 1836, .n 1837, .n 1838, .n 1839] false false),
    .atom (.load (.n 1840) (.n 5) 4),
    .atom (.load (.n 1844) (.n 5) 5),
    .atom (.load (.n 1848) (.n 5) 6)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact vtB_keccakAt hl 1914 (by decide +kernel)
  · exact (vt_readAt hl 1915 (by decide +kernel) (by decide +kernel) (hcur 4 (by norm_num))).2
  · exact (vt_readAt hl 1919 (by decide +kernel) (by decide +kernel) (hcur 5 (by norm_num))).2
  · exact (vt_readAt hl 1923 (by decide +kernel) (by decide +kernel) (hcur 6 (by norm_num))).2

set_option maxRecDepth 100000 in
theorem vtB_glue_1926 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) {T : ℕ → E}
    (hpt : ∀ i < 4, LoadHolds rd (vtσ rd wo args (.n 19)) i (T i)) 
    (h1931 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1867) (.n 19) 0)))
    (h1940 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.call "opening_tail_round" [.n 1862, .n 1863, .n 1864, .n 1865, .n 1866, .n 1875, .n 1873, .n 18] [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882, .n 1883]))
    (h1941 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1883) (.n 19) 1)))
    (h1942 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.call "opening_tail_round" [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882, .n 18] [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 1891]))
    (h1943 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1891) (.n 19) 2)))
    (h1944 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.call "opening_tail_round" [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 18] [.n 1892, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897, .n 1898, .n 1899]))
    (h1945 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1899) (.n 19) 3)))
    (h1951 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 1905) (.n 1897) 0)))
    (h2020 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.assertEq (.n 1898) (.n 1973)))) :
    ∀ s ∈ (vtPre.drop 1926).take 95, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 1926 95 [
    .atom (.keccak [.n 1841, .n 1842, .n 1845, .n 1846, .n 1849, .n 1850, .n 1852, .n 1853, .n 1835, .n 1836, .n 1837, .n 1838, .n 1839] [.n 1854, .n 1855, .n 1856, .n 1857, .n 1858, .n 1859, .n 1860, .n 1861, .n 1862, .n 1863, .n 1864, .n 1865, .n 1866] false false),
    .atom (.load (.n 1867) (.n 19) 0),
    .call "opening_tail_round" [.n 1862, .n 1863, .n 1864, .n 1865, .n 1866, .n 1875, .n 1873, .n 18] [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882, .n 1883],
    .atom (.load (.n 1883) (.n 19) 1),
    .call "opening_tail_round" [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882, .n 18] [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 1891],
    .atom (.load (.n 1891) (.n 19) 2),
    .call "opening_tail_round" [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 18] [.n 1892, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897, .n 1898, .n 1899],
    .atom (.load (.n 1899) (.n 19) 3),
    .atom (.load (.n 1905) (.n 1897) 0),
    .atom (.load (.n 1908) (.n 19) 0),
    .atom (.load (.n 1909) (.n 13) 0),
    .atom (.load (.n 1910) (.n 13) 1),
    .atom (.load (.n 1914) (.n 13) 2),
    .atom (.load (.n 1915) (.n 13) 3),
    .atom (.load (.n 1919) (.n 13) 4),
    .atom (.load (.n 1920) (.n 13) 5),
    .atom (.load (.n 1924) (.n 13) 6),
    .atom (.load (.n 1925) (.n 13) 7),
    .atom (.load (.n 1929) (.n 13) 8),
    .atom (.load (.n 1930) (.n 13) 9),
    .atom (.load (.n 1934) (.n 13) 10),
    .atom (.load (.n 1935) (.n 13) 11),
    .atom (.load (.n 1939) (.n 13) 12),
    .atom (.load (.n 1940) (.n 13) 13),
    .atom (.load (.n 1944) (.n 13) 14),
    .atom (.load (.n 1945) (.n 13) 15),
    .atom (.load (.n 1949) (.n 19) 1),
    .atom (.load (.n 1962) (.n 19) 2),
    .atom (.load (.n 1969) (.n 19) 3),
    .atom (.assertEq (.n 1898) (.n 1973))] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vtB_keccakAt hl 1929 (by decide +kernel)
  · exact h1931
  · exact h1940
  · exact h1941
  · exact h1942
  · exact h1943
  · exact h1944
  · exact h1945
  · exact h1951
  · exact (vt_readAt hl 1954 (by decide +kernel) (by decide +kernel) (hpt 0 (by norm_num))).2
  · exact (vt_readAt hl 1955 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 1956 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 1960 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 1961 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 1965 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 1966 (by decide +kernel) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vt_readAt hl 1970 (by decide +kernel) (by decide +kernel) (hw 6 (by norm_num))).2
  · exact (vt_readAt hl 1971 (by decide +kernel) (by decide +kernel) (hw 7 (by norm_num))).2
  · exact (vt_readAt hl 1975 (by decide +kernel) (by decide +kernel) (hw 8 (by norm_num))).2
  · exact (vt_readAt hl 1976 (by decide +kernel) (by decide +kernel) (hw 9 (by norm_num))).2
  · exact (vt_readAt hl 1980 (by decide +kernel) (by decide +kernel) (hw 10 (by norm_num))).2
  · exact (vt_readAt hl 1981 (by decide +kernel) (by decide +kernel) (hw 11 (by norm_num))).2
  · exact (vt_readAt hl 1985 (by decide +kernel) (by decide +kernel) (hw 12 (by norm_num))).2
  · exact (vt_readAt hl 1986 (by decide +kernel) (by decide +kernel) (hw 13 (by norm_num))).2
  · exact (vt_readAt hl 1990 (by decide +kernel) (by decide +kernel) (hw 14 (by norm_num))).2
  · exact (vt_readAt hl 1991 (by decide +kernel) (by decide +kernel) (hw 15 (by norm_num))).2
  · exact (vt_readAt hl 1995 (by decide +kernel) (by decide +kernel) (hpt 1 (by norm_num))).2
  · exact (vt_readAt hl 2008 (by decide +kernel) (by decide +kernel) (hpt 2 (by norm_num))).2
  · exact (vt_readAt hl 2015 (by decide +kernel) (by decide +kernel) (hpt 3 (by norm_num))).2
  · exact h2020

set_option maxRecDepth 100000 in
theorem vtB_glue_2021 (hl : args.length = 20) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 13)) i (W i)) {G : ℕ → E}
    (hleaves : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 17)) i (G i))  :
    ∀ s ∈ (vtPre.drop 2021).take 572, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vt_blockR hl 2021 572 [
    .atom (.load (.n 1976) (.n 13) 0),
    .atom (.load (.n 1978) (.n 13) 1),
    .atom (.load (.n 1981) (.n 13) 2),
    .atom (.load (.n 1986) (.n 13) 0),
    .atom (.load (.n 1988) (.n 13) 1),
    .atom (.load (.n 1991) (.n 13) 2),
    .atom (.load (.n 1994) (.n 13) 3),
    .atom (.load (.n 1997) (.n 13) 4),
    .atom (.load (.n 2003) (.n 13) 0),
    .atom (.load (.n 2005) (.n 13) 1),
    .atom (.load (.n 2008) (.n 13) 2),
    .atom (.load (.n 2016) (.n 13) 0),
    .atom (.load (.n 2019) (.n 13) 0),
    .atom (.load (.n 2023) (.n 13) 3),
    .atom (.load (.n 2027) (.n 13) 0),
    .atom (.load (.n 2033) (.n 13) 0),
    .atom (.load (.n 2039) (.n 13) 0),
    .atom (.load (.n 2046) (.n 13) 0),
    .atom (.load (.n 2049) (.n 13) 0),
    .atom (.load (.n 2053) (.n 13) 3),
    .atom (.load (.n 2059) (.n 13) 0),
    .atom (.load (.n 2065) (.n 13) 0),
    .atom (.load (.n 2071) (.n 13) 0),
    .atom (.load (.n 2079) (.n 13) 0),
    .atom (.load (.n 2082) (.n 13) 0),
    .atom (.load (.n 2086) (.n 13) 3),
    .atom (.load (.n 2092) (.n 13) 0),
    .atom (.load (.n 2100) (.n 13) 0),
    .atom (.load (.n 2103) (.n 13) 0),
    .atom (.load (.n 2107) (.n 13) 3),
    .atom (.load (.n 2113) (.n 13) 0),
    .atom (.load (.n 2119) (.n 13) 0),
    .atom (.load (.n 2125) (.n 13) 0),
    .atom (.load (.n 2133) (.n 13) 0),
    .atom (.load (.n 2136) (.n 13) 0),
    .atom (.load (.n 2140) (.n 13) 3),
    .atom (.load (.n 2146) (.n 13) 0),
    .atom (.load (.n 2152) (.n 13) 0),
    .atom (.load (.n 2158) (.n 13) 0),
    .atom (.load (.n 2166) (.n 13) 0),
    .atom (.load (.n 2169) (.n 13) 0),
    .atom (.load (.n 2173) (.n 13) 3),
    .atom (.load (.n 2179) (.n 13) 0),
    .atom (.load (.n 2185) (.n 13) 0),
    .atom (.load (.n 2191) (.n 13) 0),
    .atom (.load (.n 2197) (.n 13) 0),
    .atom (.load (.n 2203) (.n 13) 0),
    .atom (.load (.n 2209) (.n 13) 0),
    .atom (.load (.n 2215) (.n 13) 0),
    .atom (.load (.n 2221) (.n 13) 0),
    .atom (.load (.n 2227) (.n 13) 0),
    .atom (.load (.n 2233) (.n 13) 0),
    .atom (.load (.n 2239) (.n 13) 0),
    .atom (.load (.n 2245) (.n 13) 0),
    .atom (.load (.n 2251) (.n 13) 0),
    .atom (.load (.n 2257) (.n 13) 0),
    .atom (.load (.n 2261) (.n 13) 3),
    .atom (.load (.n 2265) (.n 13) 4),
    .atom (.load (.n 2271) (.n 13) 0),
    .atom (.load (.n 2275) (.n 13) 3),
    .atom (.load (.n 2279) (.n 13) 4),
    .atom (.load (.n 2285) (.n 13) 0),
    .atom (.load (.n 2289) (.n 13) 3),
    .atom (.load (.n 2293) (.n 13) 4),
    .atom (.load (.n 2299) (.n 13) 0),
    .atom (.load (.n 2303) (.n 13) 3),
    .atom (.load (.n 2307) (.n 13) 4),
    .atom (.load (.n 2313) (.n 13) 0),
    .atom (.load (.n 2317) (.n 13) 3),
    .atom (.load (.n 2321) (.n 13) 4),
    .atom (.load (.n 2327) (.n 13) 0),
    .atom (.load (.n 2331) (.n 13) 3),
    .atom (.load (.n 2335) (.n 13) 4),
    .atom (.load (.n 2341) (.n 13) 0),
    .atom (.load (.n 2345) (.n 13) 3),
    .atom (.load (.n 2349) (.n 13) 4),
    .atom (.load (.n 2355) (.n 13) 0),
    .atom (.load (.n 2359) (.n 13) 3),
    .atom (.load (.n 2363) (.n 13) 4),
    .atom (.load (.n 2369) (.n 13) 0),
    .atom (.load (.n 2373) (.n 13) 3),
    .atom (.load (.n 2379) (.n 13) 0),
    .atom (.load (.n 2383) (.n 13) 3),
    .atom (.load (.n 2387) (.n 13) 4),
    .atom (.load (.n 2393) (.n 13) 0),
    .atom (.load (.n 2397) (.n 13) 3),
    .atom (.load (.n 2401) (.n 13) 4),
    .atom (.load (.n 2407) (.n 13) 0),
    .atom (.load (.n 2411) (.n 13) 3),
    .atom (.load (.n 2415) (.n 13) 4),
    .atom (.load (.n 2421) (.n 13) 0),
    .atom (.load (.n 2425) (.n 13) 3),
    .atom (.load (.n 2429) (.n 13) 4),
    .atom (.load (.n 2441) (.n 17) 0),
    .atom (.load (.n 2443) (.n 13) 0),
    .atom (.load (.n 2445) (.n 13) 1),
    .atom (.load (.n 2448) (.n 13) 2),
    .atom (.load (.n 2453) (.n 13) 0),
    .atom (.load (.n 2455) (.n 13) 1),
    .atom (.load (.n 2458) (.n 13) 2),
    .atom (.load (.n 2461) (.n 13) 3),
    .atom (.load (.n 2464) (.n 13) 4),
    .atom (.load (.n 2470) (.n 13) 0),
    .atom (.load (.n 2472) (.n 13) 1),
    .atom (.load (.n 2475) (.n 13) 2),
    .atom (.load (.n 2487) (.n 17) 1),
    .atom (.load (.n 2542) (.n 17) 2)] (by decide +kernel) ?_
  intro s hs _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (vt_readAt hl 2023 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2025 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 2028 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 2033 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2035 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 2038 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 2041 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2044 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2050 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2052 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 2055 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 2063 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2066 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2070 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2074 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2080 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2086 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2093 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2096 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2100 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2106 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2112 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2118 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2126 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2129 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2133 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2139 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2147 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2150 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2154 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2160 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2166 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2172 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2180 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2183 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2187 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2193 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2199 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2205 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2213 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2216 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2220 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2226 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2232 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2238 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2244 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2250 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2256 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2262 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2268 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2274 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2280 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2286 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2292 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2298 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2304 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2308 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2312 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2318 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2322 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2326 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2332 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2336 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2340 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2346 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2350 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2354 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2360 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2364 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2368 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2374 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2378 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2382 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2388 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2392 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2396 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2402 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2406 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2410 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2416 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2420 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2426 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2430 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2434 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2440 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2444 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2448 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2454 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2458 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2462 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2468 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2472 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2476 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2488 (by decide +kernel) (by decide +kernel) (hleaves 0 (by norm_num))).2
  · exact (vt_readAt hl 2490 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2492 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 2495 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 2500 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2502 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 2505 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 2508 (by decide +kernel) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vt_readAt hl 2511 (by decide +kernel) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vt_readAt hl 2517 (by decide +kernel) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vt_readAt hl 2519 (by decide +kernel) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vt_readAt hl 2522 (by decide +kernel) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vt_readAt hl 2534 (by decide +kernel) (by decide +kernel) (hleaves 1 (by norm_num))).2
  · exact (vt_readAt hl 2589 (by decide +kernel) (by decide +kernel) (hleaves 2 (by norm_num))).2

end

end
end LeanVM.Guest.B1.Tables
