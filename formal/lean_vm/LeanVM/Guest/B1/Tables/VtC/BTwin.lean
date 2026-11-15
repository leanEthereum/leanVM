/-
  LeanVM.Guest.B1.Tables.VtC.BTwin

  The soundness's algebra of the bus sides, replayed on `VtP` (generated:
  scripts/b1c-vt/genbtwin.py from Vt/{PushFw,PushPad,PullTotal,PullSels,CountTotal}.lean).

  Do not edit: `scripts/b1c-vt/all.py` writes it (`regen-guest.sh`, step `vt`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BBase
public import LeanVM.Guest.B1.Tables.Vt.AsmTotals

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The push side's framework accumulator.** -/
theorem vtP_push_fw {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2016) = σ (.n 791) * (σ (.n 14) + (W 0 + W 1 + W 2)) +
      σ (.n 808) * (σ (.n 14) + (W 0 * gen + W 1 * σ (.n 811) + W 2 + W 3 * σ (.n 816) +
        W 4 * σ (.n 820))) +
      σ (.n 836) * (σ (.n 14) + (W 0 * gen ^ 2 + W 1 * σ (.n 839) + W 2)) +
      σ (.n 1294) * σ (.n 1844) := by
  have a778 := h.atomAt 778 (.const (.n 792) (word 1 0)) (by decide +kernel)
  have a779 := h.atomAt 779 (.const (.n 793) (word 1 0)) (by decide +kernel)
  have a780 := h.atomAt 780 (.const (.n 794) (word 1 0)) (by decide +kernel)
  have a794 := h.atomAt 794 (.const (.n 809) (word 2 0)) (by decide +kernel)
  have a798 := h.atomAt 798 (.const (.n 812) (word 1 0)) (by decide +kernel)
  have a824 := h.atomAt 824 (.const (.n 837) (word 4 0)) (by decide +kernel)
  have a828 := h.atomAt 828 (.const (.n 840) (word 1 0)) (by decide +kernel)
  have a2023 := h.atomAt 2023 (.load (.n 1977) (.n 13) 0) (by decide +kernel)
  have e2023 := tb_loadHolds_unique a2023 (hw 0 (by norm_num))
  have a2024 := h.atomAt 2024 (.mul (.n 1978) (.n 1977) (.n 792)) (by decide +kernel)
  have a2025 := h.atomAt 2025 (.load (.n 1979) (.n 13) 1) (by decide +kernel)
  have e2025 := tb_loadHolds_unique a2025 (hw 1 (by norm_num))
  have a2026 := h.atomAt 2026 (.mul (.n 1980) (.n 1979) (.n 793)) (by decide +kernel)
  have a2027 := h.atomAt 2027 (.add (.n 1981) (.n 1978) (.n 1980)) (by decide +kernel)
  have a2028 := h.atomAt 2028 (.load (.n 1982) (.n 13) 2) (by decide +kernel)
  have e2028 := tb_loadHolds_unique a2028 (hw 2 (by norm_num))
  have a2029 := h.atomAt 2029 (.mul (.n 1983) (.n 1982) (.n 794)) (by decide +kernel)
  have a2030 := h.atomAt 2030 (.add (.n 1984) (.n 1981) (.n 1983)) (by decide +kernel)
  have a2031 := h.atomAt 2031 (.add (.n 1985) (.n 14) (.n 1984)) (by decide +kernel)
  have a2032 := h.atomAt 2032 (.mul (.n 1986) (.n 791) (.n 1985)) (by decide +kernel)
  have a2033 := h.atomAt 2033 (.load (.n 1987) (.n 13) 0) (by decide +kernel)
  have e2033 := tb_loadHolds_unique a2033 (hw 0 (by norm_num))
  have a2034 := h.atomAt 2034 (.mul (.n 1988) (.n 1987) (.n 809)) (by decide +kernel)
  have a2035 := h.atomAt 2035 (.load (.n 1989) (.n 13) 1) (by decide +kernel)
  have e2035 := tb_loadHolds_unique a2035 (hw 1 (by norm_num))
  have a2036 := h.atomAt 2036 (.mul (.n 1990) (.n 1989) (.n 811)) (by decide +kernel)
  have a2037 := h.atomAt 2037 (.add (.n 1991) (.n 1988) (.n 1990)) (by decide +kernel)
  have a2038 := h.atomAt 2038 (.load (.n 1992) (.n 13) 2) (by decide +kernel)
  have e2038 := tb_loadHolds_unique a2038 (hw 2 (by norm_num))
  have a2039 := h.atomAt 2039 (.mul (.n 1993) (.n 1992) (.n 812)) (by decide +kernel)
  have a2040 := h.atomAt 2040 (.add (.n 1994) (.n 1991) (.n 1993)) (by decide +kernel)
  have a2041 := h.atomAt 2041 (.load (.n 1995) (.n 13) 3) (by decide +kernel)
  have e2041 := tb_loadHolds_unique a2041 (hw 3 (by norm_num))
  have a2042 := h.atomAt 2042 (.mul (.n 1996) (.n 1995) (.n 816)) (by decide +kernel)
  have a2043 := h.atomAt 2043 (.add (.n 1997) (.n 1994) (.n 1996)) (by decide +kernel)
  have a2044 := h.atomAt 2044 (.load (.n 1998) (.n 13) 4) (by decide +kernel)
  have e2044 := tb_loadHolds_unique a2044 (hw 4 (by norm_num))
  have a2045 := h.atomAt 2045 (.mul (.n 1999) (.n 1998) (.n 820)) (by decide +kernel)
  have a2046 := h.atomAt 2046 (.add (.n 2000) (.n 1997) (.n 1999)) (by decide +kernel)
  have a2047 := h.atomAt 2047 (.add (.n 2001) (.n 14) (.n 2000)) (by decide +kernel)
  have a2048 := h.atomAt 2048 (.mul (.n 2002) (.n 808) (.n 2001)) (by decide +kernel)
  have a2049 := h.atomAt 2049 (.add (.n 2003) (.n 1986) (.n 2002)) (by decide +kernel)
  have a2050 := h.atomAt 2050 (.load (.n 2004) (.n 13) 0) (by decide +kernel)
  have e2050 := tb_loadHolds_unique a2050 (hw 0 (by norm_num))
  have a2051 := h.atomAt 2051 (.mul (.n 2005) (.n 2004) (.n 837)) (by decide +kernel)
  have a2052 := h.atomAt 2052 (.load (.n 2006) (.n 13) 1) (by decide +kernel)
  have e2052 := tb_loadHolds_unique a2052 (hw 1 (by norm_num))
  have a2053 := h.atomAt 2053 (.mul (.n 2007) (.n 2006) (.n 839)) (by decide +kernel)
  have a2054 := h.atomAt 2054 (.add (.n 2008) (.n 2005) (.n 2007)) (by decide +kernel)
  have a2055 := h.atomAt 2055 (.load (.n 2009) (.n 13) 2) (by decide +kernel)
  have e2055 := tb_loadHolds_unique a2055 (hw 2 (by norm_num))
  have a2056 := h.atomAt 2056 (.mul (.n 2010) (.n 2009) (.n 840)) (by decide +kernel)
  have a2057 := h.atomAt 2057 (.add (.n 2011) (.n 2008) (.n 2010)) (by decide +kernel)
  have a2058 := h.atomAt 2058 (.add (.n 2012) (.n 14) (.n 2011)) (by decide +kernel)
  have a2059 := h.atomAt 2059 (.mul (.n 2013) (.n 836) (.n 2012)) (by decide +kernel)
  have a2060 := h.atomAt 2060 (.add (.n 2014) (.n 2003) (.n 2013)) (by decide +kernel)
  have a2061 := h.atomAt 2061 (.mul (.n 2015) (.n 1294) (.n 1844)) (by decide +kernel)
  have a2062 := h.atomAt 2062 (.add (.n 2016) (.n 2014) (.n 2015)) (by decide +kernel)
  simp only [Atom.Holds] at a778 a779 a780 a794 a798 a824 a828 a2024 a2026 a2027
  simp only [Atom.Holds] at a2029 a2030 a2031 a2032 a2034 a2036 a2037 a2039 a2040 a2042
  simp only [Atom.Holds] at a2043 a2045 a2046 a2047 a2048 a2049 a2051 a2053 a2054 a2056
  simp only [Atom.Holds] at a2057 a2058 a2059 a2060 a2061 a2062
  simp only [a778, a779, a780, a794, a798, a824, a828, e2023, a2024, e2025, a2026, a2027, e2028,
    a2029, a2030, a2031, a2032, e2033, a2034, e2035, a2036, a2037, e2038, a2039, a2040, e2041,
    a2042, a2043, e2044, a2045, a2046, a2047, a2048, a2049, e2050, a2051, e2052, a2053, a2054,
    e2055, a2056, a2057, a2058, a2059, a2060, a2061, a2062]
  simp only [tb_word_one, tb_word_gen, vt_word4]
  ring

set_option maxRecDepth 100000 in
theorem vtP_pushPadT0 {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2045) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 1976)) vtPushPadData 0 := by
  have a2063 := h.atomAt 2063 (.load (.n 2017) (.n 13) 0) (by decide +kernel)
  have e2063 := tb_loadHolds_unique a2063 (hw 0 (by norm_num))
  have a2064 := h.atomAt 2064 (.add (.n 2018) (.n 1976) (.n 2017)) (by decide +kernel)
  have a2065 := h.atomAt 2065 (.mul (.n 2019) (.n 858) (.n 2018)) (by decide +kernel)
  have a2066 := h.atomAt 2066 (.load (.n 2020) (.n 13) 0) (by decide +kernel)
  have e2066 := tb_loadHolds_unique a2066 (hw 0 (by norm_num))
  have a2067 := h.atomAt 2067 (.const (.n 2021) (word 4 0)) (by decide +kernel)
  have a2068 := h.atomAt 2068 (.mul (.n 2022) (.n 2020) (.n 2021)) (by decide +kernel)
  have a2069 := h.atomAt 2069 (.add (.n 2023) (.n 1976) (.n 2022)) (by decide +kernel)
  have a2070 := h.atomAt 2070 (.load (.n 2024) (.n 13) 3) (by decide +kernel)
  have e2070 := tb_loadHolds_unique a2070 (hw 3 (by norm_num))
  have a2071 := h.atomAt 2071 (.add (.n 2025) (.n 2023) (.n 2024)) (by decide +kernel)
  have a2072 := h.atomAt 2072 (.mul (.n 2026) (.n 863) (.n 2025)) (by decide +kernel)
  have a2073 := h.atomAt 2073 (.add (.n 2027) (.n 2019) (.n 2026)) (by decide +kernel)
  have a2074 := h.atomAt 2074 (.load (.n 2028) (.n 13) 0) (by decide +kernel)
  have e2074 := tb_loadHolds_unique a2074 (hw 0 (by norm_num))
  have a2075 := h.atomAt 2075 (.const (.n 2029) (word 2 0)) (by decide +kernel)
  have a2076 := h.atomAt 2076 (.mul (.n 2030) (.n 2028) (.n 2029)) (by decide +kernel)
  have a2077 := h.atomAt 2077 (.add (.n 2031) (.n 1976) (.n 2030)) (by decide +kernel)
  have a2078 := h.atomAt 2078 (.mul (.n 2032) (.n 868) (.n 2031)) (by decide +kernel)
  have a2079 := h.atomAt 2079 (.add (.n 2033) (.n 2027) (.n 2032)) (by decide +kernel)
  have a2080 := h.atomAt 2080 (.load (.n 2034) (.n 13) 0) (by decide +kernel)
  have e2080 := tb_loadHolds_unique a2080 (hw 0 (by norm_num))
  have a2081 := h.atomAt 2081 (.const (.n 2035) (word 2 0)) (by decide +kernel)
  have a2082 := h.atomAt 2082 (.mul (.n 2036) (.n 2034) (.n 2035)) (by decide +kernel)
  have a2083 := h.atomAt 2083 (.add (.n 2037) (.n 1976) (.n 2036)) (by decide +kernel)
  have a2084 := h.atomAt 2084 (.mul (.n 2038) (.n 873) (.n 2037)) (by decide +kernel)
  have a2085 := h.atomAt 2085 (.add (.n 2039) (.n 2033) (.n 2038)) (by decide +kernel)
  have a2086 := h.atomAt 2086 (.load (.n 2040) (.n 13) 0) (by decide +kernel)
  have e2086 := tb_loadHolds_unique a2086 (hw 0 (by norm_num))
  have a2087 := h.atomAt 2087 (.const (.n 2041) (word 2 0)) (by decide +kernel)
  have a2088 := h.atomAt 2088 (.mul (.n 2042) (.n 2040) (.n 2041)) (by decide +kernel)
  have a2089 := h.atomAt 2089 (.add (.n 2043) (.n 1976) (.n 2042)) (by decide +kernel)
  have a2090 := h.atomAt 2090 (.mul (.n 2044) (.n 878) (.n 2043)) (by decide +kernel)
  have a2091 := h.atomAt 2091 (.add (.n 2045) (.n 2039) (.n 2044)) (by decide +kernel)
  simp only [Atom.Holds] at a2064 a2065 a2067 a2068 a2069 a2071 a2072 a2073 a2075 a2076
  simp only [Atom.Holds] at a2077 a2078 a2079 a2081 a2082 a2083 a2084 a2085 a2087 a2088
  simp only [Atom.Holds] at a2089 a2090 a2091
  simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    tb_word_one, mul_one, add_zero]
  simp only [e2063, a2064, a2065, e2066, a2067, a2068, a2069, e2070, a2071, a2072, a2073, e2074,
    a2075, a2076, a2077, a2078, a2079, e2080, a2081, a2082, a2083, a2084, a2085, e2086, a2087,
    a2088, a2089, a2090, a2091]
  ring

set_option maxRecDepth 100000 in
theorem vtP_pushPadT1 {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2077) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 1976)) vtPushPadData 1 := by
  have a2093 := h.atomAt 2093 (.load (.n 2047) (.n 13) 0) (by decide +kernel)
  have e2093 := tb_loadHolds_unique a2093 (hw 0 (by norm_num))
  have a2094 := h.atomAt 2094 (.add (.n 2048) (.n 1976) (.n 2047)) (by decide +kernel)
  have a2095 := h.atomAt 2095 (.mul (.n 2049) (.n 887) (.n 2048)) (by decide +kernel)
  have a2096 := h.atomAt 2096 (.load (.n 2050) (.n 13) 0) (by decide +kernel)
  have e2096 := tb_loadHolds_unique a2096 (hw 0 (by norm_num))
  have a2097 := h.atomAt 2097 (.const (.n 2051) (word 4 0)) (by decide +kernel)
  have a2098 := h.atomAt 2098 (.mul (.n 2052) (.n 2050) (.n 2051)) (by decide +kernel)
  have a2099 := h.atomAt 2099 (.add (.n 2053) (.n 1976) (.n 2052)) (by decide +kernel)
  have a2100 := h.atomAt 2100 (.load (.n 2054) (.n 13) 3) (by decide +kernel)
  have e2100 := tb_loadHolds_unique a2100 (hw 3 (by norm_num))
  have a2101 := h.atomAt 2101 (.const (.n 2055) (word 2 0)) (by decide +kernel)
  have a2102 := h.atomAt 2102 (.mul (.n 2056) (.n 2054) (.n 2055)) (by decide +kernel)
  have a2103 := h.atomAt 2103 (.add (.n 2057) (.n 2053) (.n 2056)) (by decide +kernel)
  have a2104 := h.atomAt 2104 (.mul (.n 2058) (.n 896) (.n 2057)) (by decide +kernel)
  have a2105 := h.atomAt 2105 (.add (.n 2059) (.n 2049) (.n 2058)) (by decide +kernel)
  have a2106 := h.atomAt 2106 (.load (.n 2060) (.n 13) 0) (by decide +kernel)
  have e2106 := tb_loadHolds_unique a2106 (hw 0 (by norm_num))
  have a2107 := h.atomAt 2107 (.const (.n 2061) (word 2 0)) (by decide +kernel)
  have a2108 := h.atomAt 2108 (.mul (.n 2062) (.n 2060) (.n 2061)) (by decide +kernel)
  have a2109 := h.atomAt 2109 (.add (.n 2063) (.n 1976) (.n 2062)) (by decide +kernel)
  have a2110 := h.atomAt 2110 (.mul (.n 2064) (.n 905) (.n 2063)) (by decide +kernel)
  have a2111 := h.atomAt 2111 (.add (.n 2065) (.n 2059) (.n 2064)) (by decide +kernel)
  have a2112 := h.atomAt 2112 (.load (.n 2066) (.n 13) 0) (by decide +kernel)
  have e2112 := tb_loadHolds_unique a2112 (hw 0 (by norm_num))
  have a2113 := h.atomAt 2113 (.const (.n 2067) (word 2 0)) (by decide +kernel)
  have a2114 := h.atomAt 2114 (.mul (.n 2068) (.n 2066) (.n 2067)) (by decide +kernel)
  have a2115 := h.atomAt 2115 (.add (.n 2069) (.n 1976) (.n 2068)) (by decide +kernel)
  have a2116 := h.atomAt 2116 (.mul (.n 2070) (.n 914) (.n 2069)) (by decide +kernel)
  have a2117 := h.atomAt 2117 (.add (.n 2071) (.n 2065) (.n 2070)) (by decide +kernel)
  have a2118 := h.atomAt 2118 (.load (.n 2072) (.n 13) 0) (by decide +kernel)
  have e2118 := tb_loadHolds_unique a2118 (hw 0 (by norm_num))
  have a2119 := h.atomAt 2119 (.const (.n 2073) (word 2 0)) (by decide +kernel)
  have a2120 := h.atomAt 2120 (.mul (.n 2074) (.n 2072) (.n 2073)) (by decide +kernel)
  have a2121 := h.atomAt 2121 (.add (.n 2075) (.n 1976) (.n 2074)) (by decide +kernel)
  have a2122 := h.atomAt 2122 (.mul (.n 2076) (.n 923) (.n 2075)) (by decide +kernel)
  have a2123 := h.atomAt 2123 (.add (.n 2077) (.n 2071) (.n 2076)) (by decide +kernel)
  simp only [Atom.Holds] at a2094 a2095 a2097 a2098 a2099 a2101 a2102 a2103 a2104 a2105
  simp only [Atom.Holds] at a2107 a2108 a2109 a2110 a2111 a2113 a2114 a2115 a2116 a2117
  simp only [Atom.Holds] at a2119 a2120 a2121 a2122 a2123
  simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    tb_word_one, mul_one, add_zero]
  simp only [e2093, a2094, a2095, e2096, a2097, a2098, a2099, e2100, a2101, a2102, a2103, a2104,
    a2105, e2106, a2107, a2108, a2109, a2110, a2111, e2112, a2113, a2114, a2115, a2116, a2117,
    e2118, a2119, a2120, a2121, a2122, a2123]
  ring

set_option maxRecDepth 100000 in
theorem vtP_pushPadT2 {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2098) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 1976)) vtPushPadData 2 := by
  have a2126 := h.atomAt 2126 (.load (.n 2080) (.n 13) 0) (by decide +kernel)
  have e2126 := tb_loadHolds_unique a2126 (hw 0 (by norm_num))
  have a2127 := h.atomAt 2127 (.add (.n 2081) (.n 1976) (.n 2080)) (by decide +kernel)
  have a2128 := h.atomAt 2128 (.mul (.n 2082) (.n 932) (.n 2081)) (by decide +kernel)
  have a2129 := h.atomAt 2129 (.load (.n 2083) (.n 13) 0) (by decide +kernel)
  have e2129 := tb_loadHolds_unique a2129 (hw 0 (by norm_num))
  have a2130 := h.atomAt 2130 (.const (.n 2084) (word 4 0)) (by decide +kernel)
  have a2131 := h.atomAt 2131 (.mul (.n 2085) (.n 2083) (.n 2084)) (by decide +kernel)
  have a2132 := h.atomAt 2132 (.add (.n 2086) (.n 1976) (.n 2085)) (by decide +kernel)
  have a2133 := h.atomAt 2133 (.load (.n 2087) (.n 13) 3) (by decide +kernel)
  have e2133 := tb_loadHolds_unique a2133 (hw 3 (by norm_num))
  have a2134 := h.atomAt 2134 (.const (.n 2088) (word 4 0)) (by decide +kernel)
  have a2135 := h.atomAt 2135 (.mul (.n 2089) (.n 2087) (.n 2088)) (by decide +kernel)
  have a2136 := h.atomAt 2136 (.add (.n 2090) (.n 2086) (.n 2089)) (by decide +kernel)
  have a2137 := h.atomAt 2137 (.mul (.n 2091) (.n 941) (.n 2090)) (by decide +kernel)
  have a2138 := h.atomAt 2138 (.add (.n 2092) (.n 2082) (.n 2091)) (by decide +kernel)
  have a2139 := h.atomAt 2139 (.load (.n 2093) (.n 13) 0) (by decide +kernel)
  have e2139 := tb_loadHolds_unique a2139 (hw 0 (by norm_num))
  have a2140 := h.atomAt 2140 (.const (.n 2094) (word 2 0)) (by decide +kernel)
  have a2141 := h.atomAt 2141 (.mul (.n 2095) (.n 2093) (.n 2094)) (by decide +kernel)
  have a2142 := h.atomAt 2142 (.add (.n 2096) (.n 1976) (.n 2095)) (by decide +kernel)
  have a2143 := h.atomAt 2143 (.mul (.n 2097) (.n 950) (.n 2096)) (by decide +kernel)
  have a2144 := h.atomAt 2144 (.add (.n 2098) (.n 2092) (.n 2097)) (by decide +kernel)
  simp only [Atom.Holds] at a2127 a2128 a2130 a2131 a2132 a2134 a2135 a2136 a2137 a2138
  simp only [Atom.Holds] at a2140 a2141 a2142 a2143 a2144
  simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    tb_word_one, mul_one, add_zero]
  simp only [e2126, a2127, a2128, e2129, a2130, a2131, a2132, e2133, a2134, a2135, a2136, a2137,
    a2138, e2139, a2140, a2141, a2142, a2143, a2144]
  ring

set_option maxRecDepth 100000 in
theorem vtP_pushPadT3 {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2131) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 1976)) vtPushPadData 3 := by
  have a2147 := h.atomAt 2147 (.load (.n 2101) (.n 13) 0) (by decide +kernel)
  have e2147 := tb_loadHolds_unique a2147 (hw 0 (by norm_num))
  have a2148 := h.atomAt 2148 (.add (.n 2102) (.n 1976) (.n 2101)) (by decide +kernel)
  have a2149 := h.atomAt 2149 (.mul (.n 2103) (.n 959) (.n 2102)) (by decide +kernel)
  have a2150 := h.atomAt 2150 (.load (.n 2104) (.n 13) 0) (by decide +kernel)
  have e2150 := tb_loadHolds_unique a2150 (hw 0 (by norm_num))
  have a2151 := h.atomAt 2151 (.const (.n 2105) (word 4 0)) (by decide +kernel)
  have a2152 := h.atomAt 2152 (.mul (.n 2106) (.n 2104) (.n 2105)) (by decide +kernel)
  have a2153 := h.atomAt 2153 (.add (.n 2107) (.n 1976) (.n 2106)) (by decide +kernel)
  have a2154 := h.atomAt 2154 (.load (.n 2108) (.n 13) 3) (by decide +kernel)
  have e2154 := tb_loadHolds_unique a2154 (hw 3 (by norm_num))
  have a2155 := h.atomAt 2155 (.const (.n 2109) (word 8 0)) (by decide +kernel)
  have a2156 := h.atomAt 2156 (.mul (.n 2110) (.n 2108) (.n 2109)) (by decide +kernel)
  have a2157 := h.atomAt 2157 (.add (.n 2111) (.n 2107) (.n 2110)) (by decide +kernel)
  have a2158 := h.atomAt 2158 (.mul (.n 2112) (.n 968) (.n 2111)) (by decide +kernel)
  have a2159 := h.atomAt 2159 (.add (.n 2113) (.n 2103) (.n 2112)) (by decide +kernel)
  have a2160 := h.atomAt 2160 (.load (.n 2114) (.n 13) 0) (by decide +kernel)
  have e2160 := tb_loadHolds_unique a2160 (hw 0 (by norm_num))
  have a2161 := h.atomAt 2161 (.const (.n 2115) (word 2 0)) (by decide +kernel)
  have a2162 := h.atomAt 2162 (.mul (.n 2116) (.n 2114) (.n 2115)) (by decide +kernel)
  have a2163 := h.atomAt 2163 (.add (.n 2117) (.n 1976) (.n 2116)) (by decide +kernel)
  have a2164 := h.atomAt 2164 (.mul (.n 2118) (.n 977) (.n 2117)) (by decide +kernel)
  have a2165 := h.atomAt 2165 (.add (.n 2119) (.n 2113) (.n 2118)) (by decide +kernel)
  have a2166 := h.atomAt 2166 (.load (.n 2120) (.n 13) 0) (by decide +kernel)
  have e2166 := tb_loadHolds_unique a2166 (hw 0 (by norm_num))
  have a2167 := h.atomAt 2167 (.const (.n 2121) (word 2 0)) (by decide +kernel)
  have a2168 := h.atomAt 2168 (.mul (.n 2122) (.n 2120) (.n 2121)) (by decide +kernel)
  have a2169 := h.atomAt 2169 (.add (.n 2123) (.n 1976) (.n 2122)) (by decide +kernel)
  have a2170 := h.atomAt 2170 (.mul (.n 2124) (.n 986) (.n 2123)) (by decide +kernel)
  have a2171 := h.atomAt 2171 (.add (.n 2125) (.n 2119) (.n 2124)) (by decide +kernel)
  have a2172 := h.atomAt 2172 (.load (.n 2126) (.n 13) 0) (by decide +kernel)
  have e2172 := tb_loadHolds_unique a2172 (hw 0 (by norm_num))
  have a2173 := h.atomAt 2173 (.const (.n 2127) (word 2 0)) (by decide +kernel)
  have a2174 := h.atomAt 2174 (.mul (.n 2128) (.n 2126) (.n 2127)) (by decide +kernel)
  have a2175 := h.atomAt 2175 (.add (.n 2129) (.n 1976) (.n 2128)) (by decide +kernel)
  have a2176 := h.atomAt 2176 (.mul (.n 2130) (.n 995) (.n 2129)) (by decide +kernel)
  have a2177 := h.atomAt 2177 (.add (.n 2131) (.n 2125) (.n 2130)) (by decide +kernel)
  simp only [Atom.Holds] at a2148 a2149 a2151 a2152 a2153 a2155 a2156 a2157 a2158 a2159
  simp only [Atom.Holds] at a2161 a2162 a2163 a2164 a2165 a2167 a2168 a2169 a2170 a2171
  simp only [Atom.Holds] at a2173 a2174 a2175 a2176 a2177
  simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    tb_word_one, mul_one, add_zero]
  simp only [e2147, a2148, a2149, e2150, a2151, a2152, a2153, e2154, a2155, a2156, a2157, a2158,
    a2159, e2160, a2161, a2162, a2163, a2164, a2165, e2166, a2167, a2168, a2169, a2170, a2171,
    e2172, a2173, a2174, a2175, a2176, a2177]
  ring

set_option maxRecDepth 100000 in
theorem vtP_pushPadT4 {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2164) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 1976)) vtPushPadData 4 := by
  have a2180 := h.atomAt 2180 (.load (.n 2134) (.n 13) 0) (by decide +kernel)
  have e2180 := tb_loadHolds_unique a2180 (hw 0 (by norm_num))
  have a2181 := h.atomAt 2181 (.add (.n 2135) (.n 1976) (.n 2134)) (by decide +kernel)
  have a2182 := h.atomAt 2182 (.mul (.n 2136) (.n 1004) (.n 2135)) (by decide +kernel)
  have a2183 := h.atomAt 2183 (.load (.n 2137) (.n 13) 0) (by decide +kernel)
  have e2183 := tb_loadHolds_unique a2183 (hw 0 (by norm_num))
  have a2184 := h.atomAt 2184 (.const (.n 2138) (word 4 0)) (by decide +kernel)
  have a2185 := h.atomAt 2185 (.mul (.n 2139) (.n 2137) (.n 2138)) (by decide +kernel)
  have a2186 := h.atomAt 2186 (.add (.n 2140) (.n 1976) (.n 2139)) (by decide +kernel)
  have a2187 := h.atomAt 2187 (.load (.n 2141) (.n 13) 3) (by decide +kernel)
  have e2187 := tb_loadHolds_unique a2187 (hw 3 (by norm_num))
  have a2188 := h.atomAt 2188 (.const (.n 2142) (word 16 0)) (by decide +kernel)
  have a2189 := h.atomAt 2189 (.mul (.n 2143) (.n 2141) (.n 2142)) (by decide +kernel)
  have a2190 := h.atomAt 2190 (.add (.n 2144) (.n 2140) (.n 2143)) (by decide +kernel)
  have a2191 := h.atomAt 2191 (.mul (.n 2145) (.n 1013) (.n 2144)) (by decide +kernel)
  have a2192 := h.atomAt 2192 (.add (.n 2146) (.n 2136) (.n 2145)) (by decide +kernel)
  have a2193 := h.atomAt 2193 (.load (.n 2147) (.n 13) 0) (by decide +kernel)
  have e2193 := tb_loadHolds_unique a2193 (hw 0 (by norm_num))
  have a2194 := h.atomAt 2194 (.const (.n 2148) (word 2 0)) (by decide +kernel)
  have a2195 := h.atomAt 2195 (.mul (.n 2149) (.n 2147) (.n 2148)) (by decide +kernel)
  have a2196 := h.atomAt 2196 (.add (.n 2150) (.n 1976) (.n 2149)) (by decide +kernel)
  have a2197 := h.atomAt 2197 (.mul (.n 2151) (.n 1022) (.n 2150)) (by decide +kernel)
  have a2198 := h.atomAt 2198 (.add (.n 2152) (.n 2146) (.n 2151)) (by decide +kernel)
  have a2199 := h.atomAt 2199 (.load (.n 2153) (.n 13) 0) (by decide +kernel)
  have e2199 := tb_loadHolds_unique a2199 (hw 0 (by norm_num))
  have a2200 := h.atomAt 2200 (.const (.n 2154) (word 2 0)) (by decide +kernel)
  have a2201 := h.atomAt 2201 (.mul (.n 2155) (.n 2153) (.n 2154)) (by decide +kernel)
  have a2202 := h.atomAt 2202 (.add (.n 2156) (.n 1976) (.n 2155)) (by decide +kernel)
  have a2203 := h.atomAt 2203 (.mul (.n 2157) (.n 1031) (.n 2156)) (by decide +kernel)
  have a2204 := h.atomAt 2204 (.add (.n 2158) (.n 2152) (.n 2157)) (by decide +kernel)
  have a2205 := h.atomAt 2205 (.load (.n 2159) (.n 13) 0) (by decide +kernel)
  have e2205 := tb_loadHolds_unique a2205 (hw 0 (by norm_num))
  have a2206 := h.atomAt 2206 (.const (.n 2160) (word 2 0)) (by decide +kernel)
  have a2207 := h.atomAt 2207 (.mul (.n 2161) (.n 2159) (.n 2160)) (by decide +kernel)
  have a2208 := h.atomAt 2208 (.add (.n 2162) (.n 1976) (.n 2161)) (by decide +kernel)
  have a2209 := h.atomAt 2209 (.mul (.n 2163) (.n 1040) (.n 2162)) (by decide +kernel)
  have a2210 := h.atomAt 2210 (.add (.n 2164) (.n 2158) (.n 2163)) (by decide +kernel)
  simp only [Atom.Holds] at a2181 a2182 a2184 a2185 a2186 a2188 a2189 a2190 a2191 a2192
  simp only [Atom.Holds] at a2194 a2195 a2196 a2197 a2198 a2200 a2201 a2202 a2203 a2204
  simp only [Atom.Holds] at a2206 a2207 a2208 a2209 a2210
  simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    tb_word_one, mul_one, add_zero]
  simp only [e2180, a2181, a2182, e2183, a2184, a2185, a2186, e2187, a2188, a2189, a2190, a2191,
    a2192, e2193, a2194, a2195, a2196, a2197, a2198, e2199, a2200, a2201, a2202, a2203, a2204,
    e2205, a2206, a2207, a2208, a2209, a2210]
  ring

set_option maxRecDepth 100000 in
theorem vtP_pushPadT5 {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2435) = vtPadTable (fun c ↦ σ (.n c)) W (σ (.n 1976)) vtPushPadData 5 := by
  have a2213 := h.atomAt 2213 (.load (.n 2167) (.n 13) 0) (by decide +kernel)
  have e2213 := tb_loadHolds_unique a2213 (hw 0 (by norm_num))
  have a2214 := h.atomAt 2214 (.add (.n 2168) (.n 1976) (.n 2167)) (by decide +kernel)
  have a2215 := h.atomAt 2215 (.mul (.n 2169) (.n 1049) (.n 2168)) (by decide +kernel)
  have a2216 := h.atomAt 2216 (.load (.n 2170) (.n 13) 0) (by decide +kernel)
  have e2216 := tb_loadHolds_unique a2216 (hw 0 (by norm_num))
  have a2217 := h.atomAt 2217 (.const (.n 2171) (word 4 0)) (by decide +kernel)
  have a2218 := h.atomAt 2218 (.mul (.n 2172) (.n 2170) (.n 2171)) (by decide +kernel)
  have a2219 := h.atomAt 2219 (.add (.n 2173) (.n 1976) (.n 2172)) (by decide +kernel)
  have a2220 := h.atomAt 2220 (.load (.n 2174) (.n 13) 3) (by decide +kernel)
  have e2220 := tb_loadHolds_unique a2220 (hw 3 (by norm_num))
  have a2221 := h.atomAt 2221 (.const (.n 2175) (word 32 0)) (by decide +kernel)
  have a2222 := h.atomAt 2222 (.mul (.n 2176) (.n 2174) (.n 2175)) (by decide +kernel)
  have a2223 := h.atomAt 2223 (.add (.n 2177) (.n 2173) (.n 2176)) (by decide +kernel)
  have a2224 := h.atomAt 2224 (.mul (.n 2178) (.n 1058) (.n 2177)) (by decide +kernel)
  have a2225 := h.atomAt 2225 (.add (.n 2179) (.n 2169) (.n 2178)) (by decide +kernel)
  have a2226 := h.atomAt 2226 (.load (.n 2180) (.n 13) 0) (by decide +kernel)
  have e2226 := tb_loadHolds_unique a2226 (hw 0 (by norm_num))
  have a2227 := h.atomAt 2227 (.const (.n 2181) (word 2 0)) (by decide +kernel)
  have a2228 := h.atomAt 2228 (.mul (.n 2182) (.n 2180) (.n 2181)) (by decide +kernel)
  have a2229 := h.atomAt 2229 (.add (.n 2183) (.n 1976) (.n 2182)) (by decide +kernel)
  have a2230 := h.atomAt 2230 (.mul (.n 2184) (.n 1067) (.n 2183)) (by decide +kernel)
  have a2231 := h.atomAt 2231 (.add (.n 2185) (.n 2179) (.n 2184)) (by decide +kernel)
  have a2232 := h.atomAt 2232 (.load (.n 2186) (.n 13) 0) (by decide +kernel)
  have e2232 := tb_loadHolds_unique a2232 (hw 0 (by norm_num))
  have a2233 := h.atomAt 2233 (.const (.n 2187) (word 2 0)) (by decide +kernel)
  have a2234 := h.atomAt 2234 (.mul (.n 2188) (.n 2186) (.n 2187)) (by decide +kernel)
  have a2235 := h.atomAt 2235 (.add (.n 2189) (.n 1976) (.n 2188)) (by decide +kernel)
  have a2236 := h.atomAt 2236 (.mul (.n 2190) (.n 1076) (.n 2189)) (by decide +kernel)
  have a2237 := h.atomAt 2237 (.add (.n 2191) (.n 2185) (.n 2190)) (by decide +kernel)
  have a2238 := h.atomAt 2238 (.load (.n 2192) (.n 13) 0) (by decide +kernel)
  have e2238 := tb_loadHolds_unique a2238 (hw 0 (by norm_num))
  have a2239 := h.atomAt 2239 (.const (.n 2193) (word 2 0)) (by decide +kernel)
  have a2240 := h.atomAt 2240 (.mul (.n 2194) (.n 2192) (.n 2193)) (by decide +kernel)
  have a2241 := h.atomAt 2241 (.add (.n 2195) (.n 1976) (.n 2194)) (by decide +kernel)
  have a2242 := h.atomAt 2242 (.mul (.n 2196) (.n 1085) (.n 2195)) (by decide +kernel)
  have a2243 := h.atomAt 2243 (.add (.n 2197) (.n 2191) (.n 2196)) (by decide +kernel)
  have a2244 := h.atomAt 2244 (.load (.n 2198) (.n 13) 0) (by decide +kernel)
  have e2244 := tb_loadHolds_unique a2244 (hw 0 (by norm_num))
  have a2245 := h.atomAt 2245 (.const (.n 2199) (word 2 0)) (by decide +kernel)
  have a2246 := h.atomAt 2246 (.mul (.n 2200) (.n 2198) (.n 2199)) (by decide +kernel)
  have a2247 := h.atomAt 2247 (.add (.n 2201) (.n 1976) (.n 2200)) (by decide +kernel)
  have a2248 := h.atomAt 2248 (.mul (.n 2202) (.n 1094) (.n 2201)) (by decide +kernel)
  have a2249 := h.atomAt 2249 (.add (.n 2203) (.n 2197) (.n 2202)) (by decide +kernel)
  have a2250 := h.atomAt 2250 (.load (.n 2204) (.n 13) 0) (by decide +kernel)
  have e2250 := tb_loadHolds_unique a2250 (hw 0 (by norm_num))
  have a2251 := h.atomAt 2251 (.const (.n 2205) (word 2 0)) (by decide +kernel)
  have a2252 := h.atomAt 2252 (.mul (.n 2206) (.n 2204) (.n 2205)) (by decide +kernel)
  have a2253 := h.atomAt 2253 (.add (.n 2207) (.n 1976) (.n 2206)) (by decide +kernel)
  have a2254 := h.atomAt 2254 (.mul (.n 2208) (.n 1103) (.n 2207)) (by decide +kernel)
  have a2255 := h.atomAt 2255 (.add (.n 2209) (.n 2203) (.n 2208)) (by decide +kernel)
  have a2256 := h.atomAt 2256 (.load (.n 2210) (.n 13) 0) (by decide +kernel)
  have e2256 := tb_loadHolds_unique a2256 (hw 0 (by norm_num))
  have a2257 := h.atomAt 2257 (.const (.n 2211) (word 2 0)) (by decide +kernel)
  have a2258 := h.atomAt 2258 (.mul (.n 2212) (.n 2210) (.n 2211)) (by decide +kernel)
  have a2259 := h.atomAt 2259 (.add (.n 2213) (.n 1976) (.n 2212)) (by decide +kernel)
  have a2260 := h.atomAt 2260 (.mul (.n 2214) (.n 1112) (.n 2213)) (by decide +kernel)
  have a2261 := h.atomAt 2261 (.add (.n 2215) (.n 2209) (.n 2214)) (by decide +kernel)
  have a2262 := h.atomAt 2262 (.load (.n 2216) (.n 13) 0) (by decide +kernel)
  have e2262 := tb_loadHolds_unique a2262 (hw 0 (by norm_num))
  have a2263 := h.atomAt 2263 (.const (.n 2217) (word 2 0)) (by decide +kernel)
  have a2264 := h.atomAt 2264 (.mul (.n 2218) (.n 2216) (.n 2217)) (by decide +kernel)
  have a2265 := h.atomAt 2265 (.add (.n 2219) (.n 1976) (.n 2218)) (by decide +kernel)
  have a2266 := h.atomAt 2266 (.mul (.n 2220) (.n 1121) (.n 2219)) (by decide +kernel)
  have a2267 := h.atomAt 2267 (.add (.n 2221) (.n 2215) (.n 2220)) (by decide +kernel)
  have a2268 := h.atomAt 2268 (.load (.n 2222) (.n 13) 0) (by decide +kernel)
  have e2268 := tb_loadHolds_unique a2268 (hw 0 (by norm_num))
  have a2269 := h.atomAt 2269 (.const (.n 2223) (word 2 0)) (by decide +kernel)
  have a2270 := h.atomAt 2270 (.mul (.n 2224) (.n 2222) (.n 2223)) (by decide +kernel)
  have a2271 := h.atomAt 2271 (.add (.n 2225) (.n 1976) (.n 2224)) (by decide +kernel)
  have a2272 := h.atomAt 2272 (.mul (.n 2226) (.n 1130) (.n 2225)) (by decide +kernel)
  have a2273 := h.atomAt 2273 (.add (.n 2227) (.n 2221) (.n 2226)) (by decide +kernel)
  have a2274 := h.atomAt 2274 (.load (.n 2228) (.n 13) 0) (by decide +kernel)
  have e2274 := tb_loadHolds_unique a2274 (hw 0 (by norm_num))
  have a2275 := h.atomAt 2275 (.const (.n 2229) (word 2 0)) (by decide +kernel)
  have a2276 := h.atomAt 2276 (.mul (.n 2230) (.n 2228) (.n 2229)) (by decide +kernel)
  have a2277 := h.atomAt 2277 (.add (.n 2231) (.n 1976) (.n 2230)) (by decide +kernel)
  have a2278 := h.atomAt 2278 (.mul (.n 2232) (.n 1139) (.n 2231)) (by decide +kernel)
  have a2279 := h.atomAt 2279 (.add (.n 2233) (.n 2227) (.n 2232)) (by decide +kernel)
  have a2280 := h.atomAt 2280 (.load (.n 2234) (.n 13) 0) (by decide +kernel)
  have e2280 := tb_loadHolds_unique a2280 (hw 0 (by norm_num))
  have a2281 := h.atomAt 2281 (.const (.n 2235) (word 2 0)) (by decide +kernel)
  have a2282 := h.atomAt 2282 (.mul (.n 2236) (.n 2234) (.n 2235)) (by decide +kernel)
  have a2283 := h.atomAt 2283 (.add (.n 2237) (.n 1976) (.n 2236)) (by decide +kernel)
  have a2284 := h.atomAt 2284 (.mul (.n 2238) (.n 1148) (.n 2237)) (by decide +kernel)
  have a2285 := h.atomAt 2285 (.add (.n 2239) (.n 2233) (.n 2238)) (by decide +kernel)
  have a2286 := h.atomAt 2286 (.load (.n 2240) (.n 13) 0) (by decide +kernel)
  have e2286 := tb_loadHolds_unique a2286 (hw 0 (by norm_num))
  have a2287 := h.atomAt 2287 (.const (.n 2241) (word 2 0)) (by decide +kernel)
  have a2288 := h.atomAt 2288 (.mul (.n 2242) (.n 2240) (.n 2241)) (by decide +kernel)
  have a2289 := h.atomAt 2289 (.add (.n 2243) (.n 1976) (.n 2242)) (by decide +kernel)
  have a2290 := h.atomAt 2290 (.mul (.n 2244) (.n 1157) (.n 2243)) (by decide +kernel)
  have a2291 := h.atomAt 2291 (.add (.n 2245) (.n 2239) (.n 2244)) (by decide +kernel)
  have a2292 := h.atomAt 2292 (.load (.n 2246) (.n 13) 0) (by decide +kernel)
  have e2292 := tb_loadHolds_unique a2292 (hw 0 (by norm_num))
  have a2293 := h.atomAt 2293 (.const (.n 2247) (word 2 0)) (by decide +kernel)
  have a2294 := h.atomAt 2294 (.mul (.n 2248) (.n 2246) (.n 2247)) (by decide +kernel)
  have a2295 := h.atomAt 2295 (.add (.n 2249) (.n 1976) (.n 2248)) (by decide +kernel)
  have a2296 := h.atomAt 2296 (.mul (.n 2250) (.n 1166) (.n 2249)) (by decide +kernel)
  have a2297 := h.atomAt 2297 (.add (.n 2251) (.n 2245) (.n 2250)) (by decide +kernel)
  have a2298 := h.atomAt 2298 (.load (.n 2252) (.n 13) 0) (by decide +kernel)
  have e2298 := tb_loadHolds_unique a2298 (hw 0 (by norm_num))
  have a2299 := h.atomAt 2299 (.const (.n 2253) (word 2 0)) (by decide +kernel)
  have a2300 := h.atomAt 2300 (.mul (.n 2254) (.n 2252) (.n 2253)) (by decide +kernel)
  have a2301 := h.atomAt 2301 (.add (.n 2255) (.n 1976) (.n 2254)) (by decide +kernel)
  have a2302 := h.atomAt 2302 (.mul (.n 2256) (.n 1175) (.n 2255)) (by decide +kernel)
  have a2303 := h.atomAt 2303 (.add (.n 2257) (.n 2251) (.n 2256)) (by decide +kernel)
  have a2304 := h.atomAt 2304 (.load (.n 2258) (.n 13) 0) (by decide +kernel)
  have e2304 := tb_loadHolds_unique a2304 (hw 0 (by norm_num))
  have a2305 := h.atomAt 2305 (.const (.n 2259) (word 2 0)) (by decide +kernel)
  have a2306 := h.atomAt 2306 (.mul (.n 2260) (.n 2258) (.n 2259)) (by decide +kernel)
  have a2307 := h.atomAt 2307 (.add (.n 2261) (.n 1976) (.n 2260)) (by decide +kernel)
  have a2308 := h.atomAt 2308 (.load (.n 2262) (.n 13) 3) (by decide +kernel)
  have e2308 := tb_loadHolds_unique a2308 (hw 3 (by norm_num))
  have a2309 := h.atomAt 2309 (.const (.n 2263) (word 17376452488221285863 0)) (by decide +kernel)
  have a2310 := h.atomAt 2310 (.mul (.n 2264) (.n 2262) (.n 2263)) (by decide +kernel)
  have a2311 := h.atomAt 2311 (.add (.n 2265) (.n 2261) (.n 2264)) (by decide +kernel)
  have a2312 := h.atomAt 2312 (.load (.n 2266) (.n 13) 4) (by decide +kernel)
  have e2312 := tb_loadHolds_unique a2312 (hw 4 (by norm_num))
  have a2313 := h.atomAt 2313 (.const (.n 2267) (word 9571781953733019530 0)) (by decide +kernel)
  have a2314 := h.atomAt 2314 (.mul (.n 2268) (.n 2266) (.n 2267)) (by decide +kernel)
  have a2315 := h.atomAt 2315 (.add (.n 2269) (.n 2265) (.n 2268)) (by decide +kernel)
  have a2316 := h.atomAt 2316 (.mul (.n 2270) (.n 1184) (.n 2269)) (by decide +kernel)
  have a2317 := h.atomAt 2317 (.add (.n 2271) (.n 2257) (.n 2270)) (by decide +kernel)
  have a2318 := h.atomAt 2318 (.load (.n 2272) (.n 13) 0) (by decide +kernel)
  have e2318 := tb_loadHolds_unique a2318 (hw 0 (by norm_num))
  have a2319 := h.atomAt 2319 (.const (.n 2273) (word 2 0)) (by decide +kernel)
  have a2320 := h.atomAt 2320 (.mul (.n 2274) (.n 2272) (.n 2273)) (by decide +kernel)
  have a2321 := h.atomAt 2321 (.add (.n 2275) (.n 1976) (.n 2274)) (by decide +kernel)
  have a2322 := h.atomAt 2322 (.load (.n 2276) (.n 13) 3) (by decide +kernel)
  have e2322 := tb_loadHolds_unique a2322 (hw 3 (by norm_num))
  have a2323 := h.atomAt 2323 (.const (.n 2277) (word 15391093639620504046 0)) (by decide +kernel)
  have a2324 := h.atomAt 2324 (.mul (.n 2278) (.n 2276) (.n 2277)) (by decide +kernel)
  have a2325 := h.atomAt 2325 (.add (.n 2279) (.n 2275) (.n 2278)) (by decide +kernel)
  have a2326 := h.atomAt 2326 (.load (.n 2280) (.n 13) 4) (by decide +kernel)
  have e2326 := tb_loadHolds_unique a2326 (hw 4 (by norm_num))
  have a2327 := h.atomAt 2327 (.const (.n 2281) (word 13624874521033984333 0)) (by decide +kernel)
  have a2328 := h.atomAt 2328 (.mul (.n 2282) (.n 2280) (.n 2281)) (by decide +kernel)
  have a2329 := h.atomAt 2329 (.add (.n 2283) (.n 2279) (.n 2282)) (by decide +kernel)
  have a2330 := h.atomAt 2330 (.mul (.n 2284) (.n 1193) (.n 2283)) (by decide +kernel)
  have a2331 := h.atomAt 2331 (.add (.n 2285) (.n 2271) (.n 2284)) (by decide +kernel)
  have a2332 := h.atomAt 2332 (.load (.n 2286) (.n 13) 0) (by decide +kernel)
  have e2332 := tb_loadHolds_unique a2332 (hw 0 (by norm_num))
  have a2333 := h.atomAt 2333 (.const (.n 2287) (word 2 0)) (by decide +kernel)
  have a2334 := h.atomAt 2334 (.mul (.n 2288) (.n 2286) (.n 2287)) (by decide +kernel)
  have a2335 := h.atomAt 2335 (.add (.n 2289) (.n 1976) (.n 2288)) (by decide +kernel)
  have a2336 := h.atomAt 2336 (.load (.n 2290) (.n 13) 3) (by decide +kernel)
  have e2336 := tb_loadHolds_unique a2336 (hw 3 (by norm_num))
  have a2337 := h.atomAt 2337 (.const (.n 2291) (word 10027350355371872343 0)) (by decide +kernel)
  have a2338 := h.atomAt 2338 (.mul (.n 2292) (.n 2290) (.n 2291)) (by decide +kernel)
  have a2339 := h.atomAt 2339 (.add (.n 2293) (.n 2289) (.n 2292)) (by decide +kernel)
  have a2340 := h.atomAt 2340 (.load (.n 2294) (.n 13) 4) (by decide +kernel)
  have e2340 := tb_loadHolds_unique a2340 (hw 4 (by norm_num))
  have a2341 := h.atomAt 2341 (.const (.n 2295) (word 18417369716475457492 0)) (by decide +kernel)
  have a2342 := h.atomAt 2342 (.mul (.n 2296) (.n 2294) (.n 2295)) (by decide +kernel)
  have a2343 := h.atomAt 2343 (.add (.n 2297) (.n 2293) (.n 2296)) (by decide +kernel)
  have a2344 := h.atomAt 2344 (.mul (.n 2298) (.n 1202) (.n 2297)) (by decide +kernel)
  have a2345 := h.atomAt 2345 (.add (.n 2299) (.n 2285) (.n 2298)) (by decide +kernel)
  have a2346 := h.atomAt 2346 (.load (.n 2300) (.n 13) 0) (by decide +kernel)
  have e2346 := tb_loadHolds_unique a2346 (hw 0 (by norm_num))
  have a2347 := h.atomAt 2347 (.const (.n 2301) (word 2 0)) (by decide +kernel)
  have a2348 := h.atomAt 2348 (.mul (.n 2302) (.n 2300) (.n 2301)) (by decide +kernel)
  have a2349 := h.atomAt 2349 (.add (.n 2303) (.n 1976) (.n 2302)) (by decide +kernel)
  have a2350 := h.atomAt 2350 (.load (.n 2304) (.n 13) 3) (by decide +kernel)
  have e2350 := tb_loadHolds_unique a2350 (hw 3 (by norm_num))
  have a2351 := h.atomAt 2351 (.const (.n 2305) (word 10448040663659726788 0)) (by decide +kernel)
  have a2352 := h.atomAt 2352 (.mul (.n 2306) (.n 2304) (.n 2305)) (by decide +kernel)
  have a2353 := h.atomAt 2353 (.add (.n 2307) (.n 2303) (.n 2306)) (by decide +kernel)
  have a2354 := h.atomAt 2354 (.load (.n 2308) (.n 13) 4) (by decide +kernel)
  have e2354 := tb_loadHolds_unique a2354 (hw 4 (by norm_num))
  have a2355 := h.atomAt 2355 (.const (.n 2309) (word 10113917136857017974 0)) (by decide +kernel)
  have a2356 := h.atomAt 2356 (.mul (.n 2310) (.n 2308) (.n 2309)) (by decide +kernel)
  have a2357 := h.atomAt 2357 (.add (.n 2311) (.n 2307) (.n 2310)) (by decide +kernel)
  have a2358 := h.atomAt 2358 (.mul (.n 2312) (.n 1211) (.n 2311)) (by decide +kernel)
  have a2359 := h.atomAt 2359 (.add (.n 2313) (.n 2299) (.n 2312)) (by decide +kernel)
  have a2360 := h.atomAt 2360 (.load (.n 2314) (.n 13) 0) (by decide +kernel)
  have e2360 := tb_loadHolds_unique a2360 (hw 0 (by norm_num))
  have a2361 := h.atomAt 2361 (.const (.n 2315) (word 2 0)) (by decide +kernel)
  have a2362 := h.atomAt 2362 (.mul (.n 2316) (.n 2314) (.n 2315)) (by decide +kernel)
  have a2363 := h.atomAt 2363 (.add (.n 2317) (.n 1976) (.n 2316)) (by decide +kernel)
  have a2364 := h.atomAt 2364 (.load (.n 2318) (.n 13) 3) (by decide +kernel)
  have e2364 := tb_loadHolds_unique a2364 (hw 3 (by norm_num))
  have a2365 := h.atomAt 2365 (.const (.n 2319) (word 12479658147685402012 0)) (by decide +kernel)
  have a2366 := h.atomAt 2366 (.mul (.n 2320) (.n 2318) (.n 2319)) (by decide +kernel)
  have a2367 := h.atomAt 2367 (.add (.n 2321) (.n 2317) (.n 2320)) (by decide +kernel)
  have a2368 := h.atomAt 2368 (.load (.n 2322) (.n 13) 4) (by decide +kernel)
  have e2368 := tb_loadHolds_unique a2368 (hw 4 (by norm_num))
  have a2369 := h.atomAt 2369 (.const (.n 2323) (word 3500241080921619556 0)) (by decide +kernel)
  have a2370 := h.atomAt 2370 (.mul (.n 2324) (.n 2322) (.n 2323)) (by decide +kernel)
  have a2371 := h.atomAt 2371 (.add (.n 2325) (.n 2321) (.n 2324)) (by decide +kernel)
  have a2372 := h.atomAt 2372 (.mul (.n 2326) (.n 1220) (.n 2325)) (by decide +kernel)
  have a2373 := h.atomAt 2373 (.add (.n 2327) (.n 2313) (.n 2326)) (by decide +kernel)
  have a2374 := h.atomAt 2374 (.load (.n 2328) (.n 13) 0) (by decide +kernel)
  have e2374 := tb_loadHolds_unique a2374 (hw 0 (by norm_num))
  have a2375 := h.atomAt 2375 (.const (.n 2329) (word 2 0)) (by decide +kernel)
  have a2376 := h.atomAt 2376 (.mul (.n 2330) (.n 2328) (.n 2329)) (by decide +kernel)
  have a2377 := h.atomAt 2377 (.add (.n 2331) (.n 1976) (.n 2330)) (by decide +kernel)
  have a2378 := h.atomAt 2378 (.load (.n 2332) (.n 13) 3) (by decide +kernel)
  have e2378 := tb_loadHolds_unique a2378 (hw 3 (by norm_num))
  have a2379 := h.atomAt 2379 (.const (.n 2333) (word 16959053435453822517 0)) (by decide +kernel)
  have a2380 := h.atomAt 2380 (.mul (.n 2334) (.n 2332) (.n 2333)) (by decide +kernel)
  have a2381 := h.atomAt 2381 (.add (.n 2335) (.n 2331) (.n 2334)) (by decide +kernel)
  have a2382 := h.atomAt 2382 (.load (.n 2336) (.n 13) 4) (by decide +kernel)
  have e2382 := tb_loadHolds_unique a2382 (hw 4 (by norm_num))
  have a2383 := h.atomAt 2383 (.const (.n 2337) (word 12224711289652453635 0)) (by decide +kernel)
  have a2384 := h.atomAt 2384 (.mul (.n 2338) (.n 2336) (.n 2337)) (by decide +kernel)
  have a2385 := h.atomAt 2385 (.add (.n 2339) (.n 2335) (.n 2338)) (by decide +kernel)
  have a2386 := h.atomAt 2386 (.mul (.n 2340) (.n 1229) (.n 2339)) (by decide +kernel)
  have a2387 := h.atomAt 2387 (.add (.n 2341) (.n 2327) (.n 2340)) (by decide +kernel)
  have a2388 := h.atomAt 2388 (.load (.n 2342) (.n 13) 0) (by decide +kernel)
  have e2388 := tb_loadHolds_unique a2388 (hw 0 (by norm_num))
  have a2389 := h.atomAt 2389 (.const (.n 2343) (word 2 0)) (by decide +kernel)
  have a2390 := h.atomAt 2390 (.mul (.n 2344) (.n 2342) (.n 2343)) (by decide +kernel)
  have a2391 := h.atomAt 2391 (.add (.n 2345) (.n 1976) (.n 2344)) (by decide +kernel)
  have a2392 := h.atomAt 2392 (.load (.n 2346) (.n 13) 3) (by decide +kernel)
  have e2392 := tb_loadHolds_unique a2392 (hw 3 (by norm_num))
  have a2393 := h.atomAt 2393 (.const (.n 2347) (word 9342009439668884831 0)) (by decide +kernel)
  have a2394 := h.atomAt 2394 (.mul (.n 2348) (.n 2346) (.n 2347)) (by decide +kernel)
  have a2395 := h.atomAt 2395 (.add (.n 2349) (.n 2345) (.n 2348)) (by decide +kernel)
  have a2396 := h.atomAt 2396 (.load (.n 2350) (.n 13) 4) (by decide +kernel)
  have e2396 := tb_loadHolds_unique a2396 (hw 4 (by norm_num))
  have a2397 := h.atomAt 2397 (.const (.n 2351) (word 4879704952849025062 0)) (by decide +kernel)
  have a2398 := h.atomAt 2398 (.mul (.n 2352) (.n 2350) (.n 2351)) (by decide +kernel)
  have a2399 := h.atomAt 2399 (.add (.n 2353) (.n 2349) (.n 2352)) (by decide +kernel)
  have a2400 := h.atomAt 2400 (.mul (.n 2354) (.n 1238) (.n 2353)) (by decide +kernel)
  have a2401 := h.atomAt 2401 (.add (.n 2355) (.n 2341) (.n 2354)) (by decide +kernel)
  have a2402 := h.atomAt 2402 (.load (.n 2356) (.n 13) 0) (by decide +kernel)
  have e2402 := tb_loadHolds_unique a2402 (hw 0 (by norm_num))
  have a2403 := h.atomAt 2403 (.const (.n 2357) (word 2 0)) (by decide +kernel)
  have a2404 := h.atomAt 2404 (.mul (.n 2358) (.n 2356) (.n 2357)) (by decide +kernel)
  have a2405 := h.atomAt 2405 (.add (.n 2359) (.n 1976) (.n 2358)) (by decide +kernel)
  have a2406 := h.atomAt 2406 (.load (.n 2360) (.n 13) 3) (by decide +kernel)
  have e2406 := tb_loadHolds_unique a2406 (hw 3 (by norm_num))
  have a2407 := h.atomAt 2407 (.const (.n 2361) (word 140226327413610143 0)) (by decide +kernel)
  have a2408 := h.atomAt 2408 (.mul (.n 2362) (.n 2360) (.n 2361)) (by decide +kernel)
  have a2409 := h.atomAt 2409 (.add (.n 2363) (.n 2359) (.n 2362)) (by decide +kernel)
  have a2410 := h.atomAt 2410 (.load (.n 2364) (.n 13) 4) (by decide +kernel)
  have e2410 := tb_loadHolds_unique a2410 (hw 4 (by norm_num))
  have a2411 := h.atomAt 2411 (.const (.n 2365) (word 424854978622500449 0)) (by decide +kernel)
  have a2412 := h.atomAt 2412 (.mul (.n 2366) (.n 2364) (.n 2365)) (by decide +kernel)
  have a2413 := h.atomAt 2413 (.add (.n 2367) (.n 2363) (.n 2366)) (by decide +kernel)
  have a2414 := h.atomAt 2414 (.mul (.n 2368) (.n 1247) (.n 2367)) (by decide +kernel)
  have a2415 := h.atomAt 2415 (.add (.n 2369) (.n 2355) (.n 2368)) (by decide +kernel)
  have a2416 := h.atomAt 2416 (.load (.n 2370) (.n 13) 0) (by decide +kernel)
  have e2416 := tb_loadHolds_unique a2416 (hw 0 (by norm_num))
  have a2417 := h.atomAt 2417 (.const (.n 2371) (word 2 0)) (by decide +kernel)
  have a2418 := h.atomAt 2418 (.mul (.n 2372) (.n 2370) (.n 2371)) (by decide +kernel)
  have a2419 := h.atomAt 2419 (.add (.n 2373) (.n 1976) (.n 2372)) (by decide +kernel)
  have a2420 := h.atomAt 2420 (.load (.n 2374) (.n 13) 3) (by decide +kernel)
  have e2420 := tb_loadHolds_unique a2420 (hw 3 (by norm_num))
  have a2421 := h.atomAt 2421 (.const (.n 2375) (word 7259519967065370866 0)) (by decide +kernel)
  have a2422 := h.atomAt 2422 (.mul (.n 2376) (.n 2374) (.n 2375)) (by decide +kernel)
  have a2423 := h.atomAt 2423 (.add (.n 2377) (.n 2373) (.n 2376)) (by decide +kernel)
  have a2424 := h.atomAt 2424 (.mul (.n 2378) (.n 1256) (.n 2377)) (by decide +kernel)
  have a2425 := h.atomAt 2425 (.add (.n 2379) (.n 2369) (.n 2378)) (by decide +kernel)
  have a2426 := h.atomAt 2426 (.load (.n 2380) (.n 13) 0) (by decide +kernel)
  have e2426 := tb_loadHolds_unique a2426 (hw 0 (by norm_num))
  have a2427 := h.atomAt 2427 (.const (.n 2381) (word 2 0)) (by decide +kernel)
  have a2428 := h.atomAt 2428 (.mul (.n 2382) (.n 2380) (.n 2381)) (by decide +kernel)
  have a2429 := h.atomAt 2429 (.add (.n 2383) (.n 1976) (.n 2382)) (by decide +kernel)
  have a2430 := h.atomAt 2430 (.load (.n 2384) (.n 13) 3) (by decide +kernel)
  have e2430 := tb_loadHolds_unique a2430 (hw 3 (by norm_num))
  have a2431 := h.atomAt 2431 (.const (.n 2385) (word 7004910057750291985 0)) (by decide +kernel)
  have a2432 := h.atomAt 2432 (.mul (.n 2386) (.n 2384) (.n 2385)) (by decide +kernel)
  have a2433 := h.atomAt 2433 (.add (.n 2387) (.n 2383) (.n 2386)) (by decide +kernel)
  have a2434 := h.atomAt 2434 (.load (.n 2388) (.n 13) 4) (by decide +kernel)
  have e2434 := tb_loadHolds_unique a2434 (hw 4 (by norm_num))
  have a2435 := h.atomAt 2435 (.const (.n 2389) (word 13293599522548616907 0)) (by decide +kernel)
  have a2436 := h.atomAt 2436 (.mul (.n 2390) (.n 2388) (.n 2389)) (by decide +kernel)
  have a2437 := h.atomAt 2437 (.add (.n 2391) (.n 2387) (.n 2390)) (by decide +kernel)
  have a2438 := h.atomAt 2438 (.mul (.n 2392) (.n 1265) (.n 2391)) (by decide +kernel)
  have a2439 := h.atomAt 2439 (.add (.n 2393) (.n 2379) (.n 2392)) (by decide +kernel)
  have a2440 := h.atomAt 2440 (.load (.n 2394) (.n 13) 0) (by decide +kernel)
  have e2440 := tb_loadHolds_unique a2440 (hw 0 (by norm_num))
  have a2441 := h.atomAt 2441 (.const (.n 2395) (word 2 0)) (by decide +kernel)
  have a2442 := h.atomAt 2442 (.mul (.n 2396) (.n 2394) (.n 2395)) (by decide +kernel)
  have a2443 := h.atomAt 2443 (.add (.n 2397) (.n 1976) (.n 2396)) (by decide +kernel)
  have a2444 := h.atomAt 2444 (.load (.n 2398) (.n 13) 3) (by decide +kernel)
  have e2444 := tb_loadHolds_unique a2444 (hw 3 (by norm_num))
  have a2445 := h.atomAt 2445 (.const (.n 2399) (word 10105770293752443592 0)) (by decide +kernel)
  have a2446 := h.atomAt 2446 (.mul (.n 2400) (.n 2398) (.n 2399)) (by decide +kernel)
  have a2447 := h.atomAt 2447 (.add (.n 2401) (.n 2397) (.n 2400)) (by decide +kernel)
  have a2448 := h.atomAt 2448 (.load (.n 2402) (.n 13) 4) (by decide +kernel)
  have e2448 := tb_loadHolds_unique a2448 (hw 4 (by norm_num))
  have a2449 := h.atomAt 2449 (.const (.n 2403) (word 10668034807192757780 0)) (by decide +kernel)
  have a2450 := h.atomAt 2450 (.mul (.n 2404) (.n 2402) (.n 2403)) (by decide +kernel)
  have a2451 := h.atomAt 2451 (.add (.n 2405) (.n 2401) (.n 2404)) (by decide +kernel)
  have a2452 := h.atomAt 2452 (.mul (.n 2406) (.n 1274) (.n 2405)) (by decide +kernel)
  have a2453 := h.atomAt 2453 (.add (.n 2407) (.n 2393) (.n 2406)) (by decide +kernel)
  have a2454 := h.atomAt 2454 (.load (.n 2408) (.n 13) 0) (by decide +kernel)
  have e2454 := tb_loadHolds_unique a2454 (hw 0 (by norm_num))
  have a2455 := h.atomAt 2455 (.const (.n 2409) (word 2 0)) (by decide +kernel)
  have a2456 := h.atomAt 2456 (.mul (.n 2410) (.n 2408) (.n 2409)) (by decide +kernel)
  have a2457 := h.atomAt 2457 (.add (.n 2411) (.n 1976) (.n 2410)) (by decide +kernel)
  have a2458 := h.atomAt 2458 (.load (.n 2412) (.n 13) 3) (by decide +kernel)
  have e2458 := tb_loadHolds_unique a2458 (hw 3 (by norm_num))
  have a2459 := h.atomAt 2459 (.const (.n 2413) (word 1747952066141424100 0)) (by decide +kernel)
  have a2460 := h.atomAt 2460 (.mul (.n 2414) (.n 2412) (.n 2413)) (by decide +kernel)
  have a2461 := h.atomAt 2461 (.add (.n 2415) (.n 2411) (.n 2414)) (by decide +kernel)
  have a2462 := h.atomAt 2462 (.load (.n 2416) (.n 13) 4) (by decide +kernel)
  have e2462 := tb_loadHolds_unique a2462 (hw 4 (by norm_num))
  have a2463 := h.atomAt 2463 (.const (.n 2417) (word 1654286879329379778 0)) (by decide +kernel)
  have a2464 := h.atomAt 2464 (.mul (.n 2418) (.n 2416) (.n 2417)) (by decide +kernel)
  have a2465 := h.atomAt 2465 (.add (.n 2419) (.n 2415) (.n 2418)) (by decide +kernel)
  have a2466 := h.atomAt 2466 (.mul (.n 2420) (.n 1283) (.n 2419)) (by decide +kernel)
  have a2467 := h.atomAt 2467 (.add (.n 2421) (.n 2407) (.n 2420)) (by decide +kernel)
  have a2468 := h.atomAt 2468 (.load (.n 2422) (.n 13) 0) (by decide +kernel)
  have e2468 := tb_loadHolds_unique a2468 (hw 0 (by norm_num))
  have a2469 := h.atomAt 2469 (.const (.n 2423) (word 2 0)) (by decide +kernel)
  have a2470 := h.atomAt 2470 (.mul (.n 2424) (.n 2422) (.n 2423)) (by decide +kernel)
  have a2471 := h.atomAt 2471 (.add (.n 2425) (.n 1976) (.n 2424)) (by decide +kernel)
  have a2472 := h.atomAt 2472 (.load (.n 2426) (.n 13) 3) (by decide +kernel)
  have e2472 := tb_loadHolds_unique a2472 (hw 3 (by norm_num))
  have a2473 := h.atomAt 2473 (.const (.n 2427) (word 8500057116360352059 0)) (by decide +kernel)
  have a2474 := h.atomAt 2474 (.mul (.n 2428) (.n 2426) (.n 2427)) (by decide +kernel)
  have a2475 := h.atomAt 2475 (.add (.n 2429) (.n 2425) (.n 2428)) (by decide +kernel)
  have a2476 := h.atomAt 2476 (.load (.n 2430) (.n 13) 4) (by decide +kernel)
  have e2476 := tb_loadHolds_unique a2476 (hw 4 (by norm_num))
  have a2477 := h.atomAt 2477 (.const (.n 2431) (word 16929593379567477321 0)) (by decide +kernel)
  have a2478 := h.atomAt 2478 (.mul (.n 2432) (.n 2430) (.n 2431)) (by decide +kernel)
  have a2479 := h.atomAt 2479 (.add (.n 2433) (.n 2429) (.n 2432)) (by decide +kernel)
  have a2480 := h.atomAt 2480 (.mul (.n 2434) (.n 1292) (.n 2433)) (by decide +kernel)
  have a2481 := h.atomAt 2481 (.add (.n 2435) (.n 2421) (.n 2434)) (by decide +kernel)
  simp only [Atom.Holds] at a2214 a2215 a2217 a2218 a2219 a2221 a2222 a2223 a2224 a2225
  simp only [Atom.Holds] at a2227 a2228 a2229 a2230 a2231 a2233 a2234 a2235 a2236 a2237
  simp only [Atom.Holds] at a2239 a2240 a2241 a2242 a2243 a2245 a2246 a2247 a2248 a2249
  simp only [Atom.Holds] at a2251 a2252 a2253 a2254 a2255 a2257 a2258 a2259 a2260 a2261
  simp only [Atom.Holds] at a2263 a2264 a2265 a2266 a2267 a2269 a2270 a2271 a2272 a2273
  simp only [Atom.Holds] at a2275 a2276 a2277 a2278 a2279 a2281 a2282 a2283 a2284 a2285
  simp only [Atom.Holds] at a2287 a2288 a2289 a2290 a2291 a2293 a2294 a2295 a2296 a2297
  simp only [Atom.Holds] at a2299 a2300 a2301 a2302 a2303 a2305 a2306 a2307 a2309 a2310
  simp only [Atom.Holds] at a2311 a2313 a2314 a2315 a2316 a2317 a2319 a2320 a2321 a2323
  simp only [Atom.Holds] at a2324 a2325 a2327 a2328 a2329 a2330 a2331 a2333 a2334 a2335
  simp only [Atom.Holds] at a2337 a2338 a2339 a2341 a2342 a2343 a2344 a2345 a2347 a2348
  simp only [Atom.Holds] at a2349 a2351 a2352 a2353 a2355 a2356 a2357 a2358 a2359 a2361
  simp only [Atom.Holds] at a2362 a2363 a2365 a2366 a2367 a2369 a2370 a2371 a2372 a2373
  simp only [Atom.Holds] at a2375 a2376 a2377 a2379 a2380 a2381 a2383 a2384 a2385 a2386
  simp only [Atom.Holds] at a2387 a2389 a2390 a2391 a2393 a2394 a2395 a2397 a2398 a2399
  simp only [Atom.Holds] at a2400 a2401 a2403 a2404 a2405 a2407 a2408 a2409 a2411 a2412
  simp only [Atom.Holds] at a2413 a2414 a2415 a2417 a2418 a2419 a2421 a2422 a2423 a2424
  simp only [Atom.Holds] at a2425 a2427 a2428 a2429 a2431 a2432 a2433 a2435 a2436 a2437
  simp only [Atom.Holds] at a2438 a2439 a2441 a2442 a2443 a2445 a2446 a2447 a2449 a2450
  simp only [Atom.Holds] at a2451 a2452 a2453 a2455 a2456 a2457 a2459 a2460 a2461 a2463
  simp only [Atom.Holds] at a2464 a2465 a2466 a2467 a2469 a2470 a2471 a2473 a2474 a2475
  simp only [Atom.Holds] at a2477 a2478 a2479 a2480 a2481
  simp (config := { decide := true }) only [vtPadTable, vtPushPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    tb_word_one, mul_one, add_zero]
  simp only [e2213, a2214, a2215, e2216, a2217, a2218, a2219, e2220, a2221, a2222, a2223, a2224,
    a2225, e2226, a2227, a2228, a2229, a2230, a2231, e2232, a2233, a2234, a2235, a2236, a2237,
    e2238, a2239, a2240, a2241, a2242, a2243, e2244, a2245, a2246, a2247, a2248, a2249, e2250,
    a2251, a2252, a2253, a2254, a2255, e2256, a2257, a2258, a2259, a2260, a2261, e2262, a2263,
    a2264, a2265, a2266, a2267, e2268, a2269, a2270, a2271, a2272, a2273, e2274, a2275, a2276,
    a2277, a2278, a2279, e2280, a2281, a2282, a2283, a2284, a2285, e2286, a2287, a2288, a2289,
    a2290, a2291, e2292, a2293, a2294, a2295, a2296, a2297, e2298, a2299, a2300, a2301, a2302,
    a2303, e2304, a2305, a2306, a2307, e2308, a2309, a2310, a2311, e2312, a2313, a2314, a2315,
    a2316, a2317, e2318, a2319, a2320, a2321, e2322, a2323, a2324, a2325, e2326, a2327, a2328,
    a2329, a2330, a2331, e2332, a2333, a2334, a2335, e2336, a2337, a2338, a2339, e2340, a2341,
    a2342, a2343, a2344, a2345, e2346, a2347, a2348, a2349, e2350, a2351, a2352, a2353, e2354,
    a2355, a2356, a2357, a2358, a2359, e2360, a2361, a2362, a2363, e2364, a2365, a2366, a2367,
    e2368, a2369, a2370, a2371, a2372, a2373, e2374, a2375, a2376, a2377, e2378, a2379, a2380,
    a2381, e2382, a2383, a2384, a2385, a2386, a2387, e2388, a2389, a2390, a2391, e2392, a2393,
    a2394, a2395, e2396, a2397, a2398, a2399, a2400, a2401, e2402, a2403, a2404, a2405, e2406,
    a2407, a2408, a2409, e2410, a2411, a2412, a2413, a2414, a2415, e2416, a2417, a2418, a2419,
    e2420, a2421, a2422, a2423, a2424, a2425, e2426, a2427, a2428, a2429, e2430, a2431, a2432,
    a2433, e2434, a2435, a2436, a2437, a2438, a2439, e2440, a2441, a2442, a2443, e2444, a2445,
    a2446, a2447, e2448, a2449, a2450, a2451, a2452, a2453, e2454, a2455, a2456, a2457, e2458,
    a2459, a2460, a2461, e2462, a2463, a2464, a2465, a2466, a2467, e2468, a2469, a2470, a2471,
    e2472, a2473, a2474, a2475, e2476, a2477, a2478, a2479, a2480, a2481]
  ring

set_option maxRecDepth 100000 in
/-- **The push side's padding sum.** -/
theorem vtP_push_pad {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2437) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W (σ (.n 1976))
      vtPushPadData := by
  have a2092 := h.atomAt 2092 (.mul (.n 2046) (.n 584) (.n 2045)) (by decide +kernel)
  have a2124 := h.atomAt 2124 (.mul (.n 2078) (.n 597) (.n 2077)) (by decide +kernel)
  have a2125 := h.atomAt 2125 (.add (.n 2079) (.n 2046) (.n 2078)) (by decide +kernel)
  have a2145 := h.atomAt 2145 (.mul (.n 2099) (.n 610) (.n 2098)) (by decide +kernel)
  have a2146 := h.atomAt 2146 (.add (.n 2100) (.n 2079) (.n 2099)) (by decide +kernel)
  have a2178 := h.atomAt 2178 (.mul (.n 2132) (.n 623) (.n 2131)) (by decide +kernel)
  have a2179 := h.atomAt 2179 (.add (.n 2133) (.n 2100) (.n 2132)) (by decide +kernel)
  have a2211 := h.atomAt 2211 (.mul (.n 2165) (.n 636) (.n 2164)) (by decide +kernel)
  have a2212 := h.atomAt 2212 (.add (.n 2166) (.n 2133) (.n 2165)) (by decide +kernel)
  have a2482 := h.atomAt 2482 (.mul (.n 2436) (.n 649) (.n 2435)) (by decide +kernel)
  have a2483 := h.atomAt 2483 (.add (.n 2437) (.n 2166) (.n 2436)) (by decide +kernel)
  simp only [Atom.Holds] at a2092 a2124 a2125 a2145 a2146 a2178 a2179 a2211 a2212 a2482
  simp only [Atom.Holds] at a2483
  simp only [a2092, a2124, a2125, a2145, a2146, a2178, a2179, a2211, a2212, a2482, a2483]
  simp only [vtPadSum, vtPadV]
  rw [← vtP_pushPadT0 h hw, ← vtP_pushPadT1 h hw, ← vtP_pushPadT2 h hw, ← vtP_pushPadT3 h hw,
    ← vtP_pushPadT4 h hw, ← vtP_pushPadT5 h hw]

/-- **The push side's total.** -/
theorem vtP_push_total {rd : Reader} {σ : Val} (h : VtP rd σ) :
    σ (.n 2443) = σ (.n 2016) + σ (.n 2437) + (1 + σ (.n 1293)) + σ (.n 2442) := by
  have a2484 := h.atomAt 2484 (.add (.n 2438) (.n 2016) (.n 2437)) (by decide +kernel)
  have a2485 := h.atomAt 2485 (.const (.n 2439) (word 1 0)) (by decide +kernel)
  have a2486 := h.atomAt 2486 (.add (.n 2440) (.n 2439) (.n 1293)) (by decide +kernel)
  have a2487 := h.atomAt 2487 (.add (.n 2441) (.n 2438) (.n 2440)) (by decide +kernel)
  have a2489 := h.atomAt 2489 (.add (.n 2443) (.n 2441) (.n 2442)) (by decide +kernel)
  simp only [Atom.Holds] at a2484 a2485 a2486 a2487 a2489
  rw [a2489, a2487, a2486, a2485, a2484, tb_word_one]

/-- `push_padding`'s selector sum is the running sum's copy. -/
theorem vtP_push_sel {rd : Reader} {σ : Val} (h : VtP rd σ) : σ (.n 1293) = σ (.n 1291) := by
  have a := h.atomAt 1332 (.copy (.n 1293) (.n 1291)) (by decide +kernel)
  simpa only [Atom.Holds] using a

set_option maxRecDepth 100000 in
/-- **The pull side's framework accumulator.** -/
theorem vtP_pull_fw {rd : Reader} {σ : Val} (h : VtP rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2483) = σ (.n 1295) * (σ (.n 14) + (W 0 + W 1 * vtWFinalPc + W 2)) +
      σ (.n 1300) * (σ (.n 14) + (W 0 * gen + W 1 * σ (.n 1302) + W 2 * σ (.n 1306) +
        W 3 * σ (.n 1308) + W 4 * σ (.n 1310))) +
      σ (.n 1314) * (σ (.n 14) + (W 0 * gen ^ 2 + W 1 * σ (.n 1316) + W 2 * σ (.n 1320))) +
      σ (.n 1437) * σ (.n 1844) := by
  have a1335 := h.atomAt 1335 (.const (.n 1296) (word 1 0)) (by decide +kernel)
  have a1336 := h.atomAt 1336 (.const (.n 1297) (word 12261764870545049476 0)) (by decide +kernel)
  have a1337 := h.atomAt 1337 (.const (.n 1298) (word 1 0)) (by decide +kernel)
  have a1340 := h.atomAt 1340 (.const (.n 1301) (word 2 0)) (by decide +kernel)
  have a1355 := h.atomAt 1355 (.const (.n 1315) (word 4 0)) (by decide +kernel)
  have a2490 := h.atomAt 2490 (.load (.n 2444) (.n 13) 0) (by decide +kernel)
  have e2490 := tb_loadHolds_unique a2490 (hw 0 (by norm_num))
  have a2491 := h.atomAt 2491 (.mul (.n 2445) (.n 2444) (.n 1296)) (by decide +kernel)
  have a2492 := h.atomAt 2492 (.load (.n 2446) (.n 13) 1) (by decide +kernel)
  have e2492 := tb_loadHolds_unique a2492 (hw 1 (by norm_num))
  have a2493 := h.atomAt 2493 (.mul (.n 2447) (.n 2446) (.n 1297)) (by decide +kernel)
  have a2494 := h.atomAt 2494 (.add (.n 2448) (.n 2445) (.n 2447)) (by decide +kernel)
  have a2495 := h.atomAt 2495 (.load (.n 2449) (.n 13) 2) (by decide +kernel)
  have e2495 := tb_loadHolds_unique a2495 (hw 2 (by norm_num))
  have a2496 := h.atomAt 2496 (.mul (.n 2450) (.n 2449) (.n 1298)) (by decide +kernel)
  have a2497 := h.atomAt 2497 (.add (.n 2451) (.n 2448) (.n 2450)) (by decide +kernel)
  have a2498 := h.atomAt 2498 (.add (.n 2452) (.n 14) (.n 2451)) (by decide +kernel)
  have a2499 := h.atomAt 2499 (.mul (.n 2453) (.n 1295) (.n 2452)) (by decide +kernel)
  have a2500 := h.atomAt 2500 (.load (.n 2454) (.n 13) 0) (by decide +kernel)
  have e2500 := tb_loadHolds_unique a2500 (hw 0 (by norm_num))
  have a2501 := h.atomAt 2501 (.mul (.n 2455) (.n 2454) (.n 1301)) (by decide +kernel)
  have a2502 := h.atomAt 2502 (.load (.n 2456) (.n 13) 1) (by decide +kernel)
  have e2502 := tb_loadHolds_unique a2502 (hw 1 (by norm_num))
  have a2503 := h.atomAt 2503 (.mul (.n 2457) (.n 2456) (.n 1302)) (by decide +kernel)
  have a2504 := h.atomAt 2504 (.add (.n 2458) (.n 2455) (.n 2457)) (by decide +kernel)
  have a2505 := h.atomAt 2505 (.load (.n 2459) (.n 13) 2) (by decide +kernel)
  have e2505 := tb_loadHolds_unique a2505 (hw 2 (by norm_num))
  have a2506 := h.atomAt 2506 (.mul (.n 2460) (.n 2459) (.n 1306)) (by decide +kernel)
  have a2507 := h.atomAt 2507 (.add (.n 2461) (.n 2458) (.n 2460)) (by decide +kernel)
  have a2508 := h.atomAt 2508 (.load (.n 2462) (.n 13) 3) (by decide +kernel)
  have e2508 := tb_loadHolds_unique a2508 (hw 3 (by norm_num))
  have a2509 := h.atomAt 2509 (.mul (.n 2463) (.n 2462) (.n 1308)) (by decide +kernel)
  have a2510 := h.atomAt 2510 (.add (.n 2464) (.n 2461) (.n 2463)) (by decide +kernel)
  have a2511 := h.atomAt 2511 (.load (.n 2465) (.n 13) 4) (by decide +kernel)
  have e2511 := tb_loadHolds_unique a2511 (hw 4 (by norm_num))
  have a2512 := h.atomAt 2512 (.mul (.n 2466) (.n 2465) (.n 1310)) (by decide +kernel)
  have a2513 := h.atomAt 2513 (.add (.n 2467) (.n 2464) (.n 2466)) (by decide +kernel)
  have a2514 := h.atomAt 2514 (.add (.n 2468) (.n 14) (.n 2467)) (by decide +kernel)
  have a2515 := h.atomAt 2515 (.mul (.n 2469) (.n 1300) (.n 2468)) (by decide +kernel)
  have a2516 := h.atomAt 2516 (.add (.n 2470) (.n 2453) (.n 2469)) (by decide +kernel)
  have a2517 := h.atomAt 2517 (.load (.n 2471) (.n 13) 0) (by decide +kernel)
  have e2517 := tb_loadHolds_unique a2517 (hw 0 (by norm_num))
  have a2518 := h.atomAt 2518 (.mul (.n 2472) (.n 2471) (.n 1315)) (by decide +kernel)
  have a2519 := h.atomAt 2519 (.load (.n 2473) (.n 13) 1) (by decide +kernel)
  have e2519 := tb_loadHolds_unique a2519 (hw 1 (by norm_num))
  have a2520 := h.atomAt 2520 (.mul (.n 2474) (.n 2473) (.n 1316)) (by decide +kernel)
  have a2521 := h.atomAt 2521 (.add (.n 2475) (.n 2472) (.n 2474)) (by decide +kernel)
  have a2522 := h.atomAt 2522 (.load (.n 2476) (.n 13) 2) (by decide +kernel)
  have e2522 := tb_loadHolds_unique a2522 (hw 2 (by norm_num))
  have a2523 := h.atomAt 2523 (.mul (.n 2477) (.n 2476) (.n 1320)) (by decide +kernel)
  have a2524 := h.atomAt 2524 (.add (.n 2478) (.n 2475) (.n 2477)) (by decide +kernel)
  have a2525 := h.atomAt 2525 (.add (.n 2479) (.n 14) (.n 2478)) (by decide +kernel)
  have a2526 := h.atomAt 2526 (.mul (.n 2480) (.n 1314) (.n 2479)) (by decide +kernel)
  have a2527 := h.atomAt 2527 (.add (.n 2481) (.n 2470) (.n 2480)) (by decide +kernel)
  have a2528 := h.atomAt 2528 (.mul (.n 2482) (.n 1437) (.n 1844)) (by decide +kernel)
  have a2529 := h.atomAt 2529 (.add (.n 2483) (.n 2481) (.n 2482)) (by decide +kernel)
  simp only [Atom.Holds] at a1335 a1336 a1337 a1340 a1355 a2491 a2493 a2494 a2496 a2497
  simp only [Atom.Holds] at a2498 a2499 a2501 a2503 a2504 a2506 a2507 a2509 a2510 a2512
  simp only [Atom.Holds] at a2513 a2514 a2515 a2516 a2518 a2520 a2521 a2523 a2524 a2525
  simp only [Atom.Holds] at a2526 a2527 a2528 a2529
  simp only [a1335, a1336, a1337, a1340, a1355, e2490, a2491, e2492, a2493, a2494, e2495, a2496,
    a2497, a2498, a2499, e2500, a2501, e2502, a2503, a2504, e2505, a2506, a2507, e2508, a2509,
    a2510, e2511, a2512, a2513, a2514, a2515, a2516, e2517, a2518, e2519, a2520, a2521, e2522,
    a2523, a2524, a2525, a2526, a2527, a2528, a2529]
  simp only [tb_word_one, tb_word_gen, vt_word4]
  ring

set_option maxRecDepth 100000 in
/-- **The pull side's selector sum: the push blocks' copies.** -/
theorem vtP_pull_sel {rd : Reader} {σ : Val} (h : VtP rd σ) :
    σ (.n 1436) = σ (.n 791) + σ (.n 808) + σ (.n 836) +
      (vtPushPadData.map fun x ↦ σ (.n x.2.2.1)).sum := by
  have a1338 := h.atomAt 1338 (.add (.n 1299) (.n 791) (.n 808)) (by decide +kernel)
  have a1353 := h.atomAt 1353 (.add (.n 1313) (.n 1299) (.n 836)) (by decide +kernel)
  have a1375 := h.atomAt 1375 (.add (.n 1334) (.n 1313) (.n 858)) (by decide +kernel)
  have a1377 := h.atomAt 1377 (.add (.n 1336) (.n 1334) (.n 863)) (by decide +kernel)
  have a1379 := h.atomAt 1379 (.add (.n 1338) (.n 1336) (.n 868)) (by decide +kernel)
  have a1381 := h.atomAt 1381 (.add (.n 1340) (.n 1338) (.n 873)) (by decide +kernel)
  have a1383 := h.atomAt 1383 (.add (.n 1342) (.n 1340) (.n 878)) (by decide +kernel)
  have a1385 := h.atomAt 1385 (.add (.n 1344) (.n 1342) (.n 887)) (by decide +kernel)
  have a1387 := h.atomAt 1387 (.add (.n 1346) (.n 1344) (.n 896)) (by decide +kernel)
  have a1389 := h.atomAt 1389 (.add (.n 1348) (.n 1346) (.n 905)) (by decide +kernel)
  have a1391 := h.atomAt 1391 (.add (.n 1350) (.n 1348) (.n 914)) (by decide +kernel)
  have a1393 := h.atomAt 1393 (.add (.n 1352) (.n 1350) (.n 923)) (by decide +kernel)
  have a1395 := h.atomAt 1395 (.add (.n 1354) (.n 1352) (.n 932)) (by decide +kernel)
  have a1397 := h.atomAt 1397 (.add (.n 1356) (.n 1354) (.n 941)) (by decide +kernel)
  have a1399 := h.atomAt 1399 (.add (.n 1358) (.n 1356) (.n 950)) (by decide +kernel)
  have a1401 := h.atomAt 1401 (.add (.n 1360) (.n 1358) (.n 959)) (by decide +kernel)
  have a1403 := h.atomAt 1403 (.add (.n 1362) (.n 1360) (.n 968)) (by decide +kernel)
  have a1405 := h.atomAt 1405 (.add (.n 1364) (.n 1362) (.n 977)) (by decide +kernel)
  have a1407 := h.atomAt 1407 (.add (.n 1366) (.n 1364) (.n 986)) (by decide +kernel)
  have a1409 := h.atomAt 1409 (.add (.n 1368) (.n 1366) (.n 995)) (by decide +kernel)
  have a1411 := h.atomAt 1411 (.add (.n 1370) (.n 1368) (.n 1004)) (by decide +kernel)
  have a1413 := h.atomAt 1413 (.add (.n 1372) (.n 1370) (.n 1013)) (by decide +kernel)
  have a1415 := h.atomAt 1415 (.add (.n 1374) (.n 1372) (.n 1022)) (by decide +kernel)
  have a1417 := h.atomAt 1417 (.add (.n 1376) (.n 1374) (.n 1031)) (by decide +kernel)
  have a1419 := h.atomAt 1419 (.add (.n 1378) (.n 1376) (.n 1040)) (by decide +kernel)
  have a1421 := h.atomAt 1421 (.add (.n 1380) (.n 1378) (.n 1049)) (by decide +kernel)
  have a1423 := h.atomAt 1423 (.add (.n 1382) (.n 1380) (.n 1058)) (by decide +kernel)
  have a1425 := h.atomAt 1425 (.add (.n 1384) (.n 1382) (.n 1067)) (by decide +kernel)
  have a1427 := h.atomAt 1427 (.add (.n 1386) (.n 1384) (.n 1076)) (by decide +kernel)
  have a1429 := h.atomAt 1429 (.add (.n 1388) (.n 1386) (.n 1085)) (by decide +kernel)
  have a1431 := h.atomAt 1431 (.add (.n 1390) (.n 1388) (.n 1094)) (by decide +kernel)
  have a1433 := h.atomAt 1433 (.add (.n 1392) (.n 1390) (.n 1103)) (by decide +kernel)
  have a1435 := h.atomAt 1435 (.add (.n 1394) (.n 1392) (.n 1112)) (by decide +kernel)
  have a1437 := h.atomAt 1437 (.add (.n 1396) (.n 1394) (.n 1121)) (by decide +kernel)
  have a1439 := h.atomAt 1439 (.add (.n 1398) (.n 1396) (.n 1130)) (by decide +kernel)
  have a1441 := h.atomAt 1441 (.add (.n 1400) (.n 1398) (.n 1139)) (by decide +kernel)
  have a1443 := h.atomAt 1443 (.add (.n 1402) (.n 1400) (.n 1148)) (by decide +kernel)
  have a1445 := h.atomAt 1445 (.add (.n 1404) (.n 1402) (.n 1157)) (by decide +kernel)
  have a1447 := h.atomAt 1447 (.add (.n 1406) (.n 1404) (.n 1166)) (by decide +kernel)
  have a1449 := h.atomAt 1449 (.add (.n 1408) (.n 1406) (.n 1175)) (by decide +kernel)
  have a1451 := h.atomAt 1451 (.add (.n 1410) (.n 1408) (.n 1184)) (by decide +kernel)
  have a1453 := h.atomAt 1453 (.add (.n 1412) (.n 1410) (.n 1193)) (by decide +kernel)
  have a1455 := h.atomAt 1455 (.add (.n 1414) (.n 1412) (.n 1202)) (by decide +kernel)
  have a1457 := h.atomAt 1457 (.add (.n 1416) (.n 1414) (.n 1211)) (by decide +kernel)
  have a1459 := h.atomAt 1459 (.add (.n 1418) (.n 1416) (.n 1220)) (by decide +kernel)
  have a1461 := h.atomAt 1461 (.add (.n 1420) (.n 1418) (.n 1229)) (by decide +kernel)
  have a1463 := h.atomAt 1463 (.add (.n 1422) (.n 1420) (.n 1238)) (by decide +kernel)
  have a1465 := h.atomAt 1465 (.add (.n 1424) (.n 1422) (.n 1247)) (by decide +kernel)
  have a1467 := h.atomAt 1467 (.add (.n 1426) (.n 1424) (.n 1256)) (by decide +kernel)
  have a1469 := h.atomAt 1469 (.add (.n 1428) (.n 1426) (.n 1265)) (by decide +kernel)
  have a1471 := h.atomAt 1471 (.add (.n 1430) (.n 1428) (.n 1274)) (by decide +kernel)
  have a1473 := h.atomAt 1473 (.add (.n 1432) (.n 1430) (.n 1283)) (by decide +kernel)
  have a1475 := h.atomAt 1475 (.add (.n 1434) (.n 1432) (.n 1292)) (by decide +kernel)
  have a1477 := h.atomAt 1477 (.copy (.n 1436) (.n 1434)) (by decide +kernel)
  simp only [Atom.Holds] at a1338 a1353 a1375 a1377 a1379 a1381 a1383 a1385 a1387 a1389
  simp only [Atom.Holds] at a1391 a1393 a1395 a1397 a1399 a1401 a1403 a1405 a1407 a1409
  simp only [Atom.Holds] at a1411 a1413 a1415 a1417 a1419 a1421 a1423 a1425 a1427 a1429
  simp only [Atom.Holds] at a1431 a1433 a1435 a1437 a1439 a1441 a1443 a1445 a1447 a1449
  simp only [Atom.Holds] at a1451 a1453 a1455 a1457 a1459 a1461 a1463 a1465 a1467 a1469
  simp only [Atom.Holds] at a1471 a1473 a1475 a1477
  simp only [a1338, a1353, a1375, a1377, a1379, a1381, a1383, a1385, a1387, a1389, a1391, a1393,
    a1395, a1397, a1399, a1401, a1403, a1405, a1407, a1409, a1411, a1413, a1415, a1417, a1419,
    a1421, a1423, a1425, a1427, a1429, a1431, a1433, a1435, a1437, a1439, a1441, a1443, a1445,
    a1447, a1449, a1451, a1453, a1455, a1457, a1459, a1461, a1463, a1465, a1467, a1469, a1471,
    a1473, a1475, a1477]
  simp only [vtPushPadData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- **The pull side's total.** -/
theorem vtP_pull_total {rd : Reader} {σ : Val} (h : VtP rd σ) :
    σ (.n 2489) = σ (.n 2483) + σ (.n 2437) + (1 + σ (.n 1436)) + σ (.n 2488) := by
  have a2530 := h.atomAt 2530 (.add (.n 2484) (.n 2483) (.n 2437)) (by decide +kernel)
  have a2531 := h.atomAt 2531 (.const (.n 2485) (word 1 0)) (by decide +kernel)
  have a2532 := h.atomAt 2532 (.add (.n 2486) (.n 2485) (.n 1436)) (by decide +kernel)
  have a2533 := h.atomAt 2533 (.add (.n 2487) (.n 2484) (.n 2486)) (by decide +kernel)
  have a2535 := h.atomAt 2535 (.add (.n 2489) (.n 2487) (.n 2488)) (by decide +kernel)
  simp only [Atom.Holds] at a2530 a2531 a2532 a2533 a2535
  rw [a2535, a2533, a2532, a2531, a2530, tb_word_one]

theorem vtPPullSels0 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 1335), σ (.n 1337), σ (.n 1339), σ (.n 1341), σ (.n 1343)] =
      [σ (.n 858), σ (.n 863), σ (.n 868), σ (.n 873), σ (.n 878)] := by
  have a1376 := h.atomAt 1376 (.copy (.n 1335) (.n 858)) (by decide +kernel)
  have a1378 := h.atomAt 1378 (.copy (.n 1337) (.n 863)) (by decide +kernel)
  have a1380 := h.atomAt 1380 (.copy (.n 1339) (.n 868)) (by decide +kernel)
  have a1382 := h.atomAt 1382 (.copy (.n 1341) (.n 873)) (by decide +kernel)
  have a1384 := h.atomAt 1384 (.copy (.n 1343) (.n 878)) (by decide +kernel)
  simp only [Atom.Holds] at a1376 a1378 a1380 a1382 a1384
  rw [a1376, a1378, a1380, a1382, a1384]

theorem vtPPullSels1 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 1345), σ (.n 1347), σ (.n 1349), σ (.n 1351), σ (.n 1353)] =
      [σ (.n 887), σ (.n 896), σ (.n 905), σ (.n 914), σ (.n 923)] := by
  have a1386 := h.atomAt 1386 (.copy (.n 1345) (.n 887)) (by decide +kernel)
  have a1388 := h.atomAt 1388 (.copy (.n 1347) (.n 896)) (by decide +kernel)
  have a1390 := h.atomAt 1390 (.copy (.n 1349) (.n 905)) (by decide +kernel)
  have a1392 := h.atomAt 1392 (.copy (.n 1351) (.n 914)) (by decide +kernel)
  have a1394 := h.atomAt 1394 (.copy (.n 1353) (.n 923)) (by decide +kernel)
  simp only [Atom.Holds] at a1386 a1388 a1390 a1392 a1394
  rw [a1386, a1388, a1390, a1392, a1394]

theorem vtPPullSels2 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 1355), σ (.n 1357), σ (.n 1359)] =
      [σ (.n 932), σ (.n 941), σ (.n 950)] := by
  have a1396 := h.atomAt 1396 (.copy (.n 1355) (.n 932)) (by decide +kernel)
  have a1398 := h.atomAt 1398 (.copy (.n 1357) (.n 941)) (by decide +kernel)
  have a1400 := h.atomAt 1400 (.copy (.n 1359) (.n 950)) (by decide +kernel)
  simp only [Atom.Holds] at a1396 a1398 a1400
  rw [a1396, a1398, a1400]

theorem vtPPullSels3 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 1361), σ (.n 1363), σ (.n 1365), σ (.n 1367), σ (.n 1369)] =
      [σ (.n 959), σ (.n 968), σ (.n 977), σ (.n 986), σ (.n 995)] := by
  have a1402 := h.atomAt 1402 (.copy (.n 1361) (.n 959)) (by decide +kernel)
  have a1404 := h.atomAt 1404 (.copy (.n 1363) (.n 968)) (by decide +kernel)
  have a1406 := h.atomAt 1406 (.copy (.n 1365) (.n 977)) (by decide +kernel)
  have a1408 := h.atomAt 1408 (.copy (.n 1367) (.n 986)) (by decide +kernel)
  have a1410 := h.atomAt 1410 (.copy (.n 1369) (.n 995)) (by decide +kernel)
  simp only [Atom.Holds] at a1402 a1404 a1406 a1408 a1410
  rw [a1402, a1404, a1406, a1408, a1410]

theorem vtPPullSels4 {rd : Reader} {σ : Val} (h : VtP rd σ) :
    [σ (.n 1371), σ (.n 1373), σ (.n 1375), σ (.n 1377), σ (.n 1379)] =
      [σ (.n 1004), σ (.n 1013), σ (.n 1022), σ (.n 1031), σ (.n 1040)] := by
  have a1412 := h.atomAt 1412 (.copy (.n 1371) (.n 1004)) (by decide +kernel)
  have a1414 := h.atomAt 1414 (.copy (.n 1373) (.n 1013)) (by decide +kernel)
  have a1416 := h.atomAt 1416 (.copy (.n 1375) (.n 1022)) (by decide +kernel)
  have a1418 := h.atomAt 1418 (.copy (.n 1377) (.n 1031)) (by decide +kernel)
  have a1420 := h.atomAt 1420 (.copy (.n 1379) (.n 1040)) (by decide +kernel)
  simp only [Atom.Holds] at a1412 a1414 a1416 a1418 a1420
  rw [a1412, a1414, a1416, a1418, a1420]

theorem vtPPullSels5 {rd : Reader} {σ : Val} (h : VtP rd σ) :
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

set_option maxRecDepth 100000 in
theorem vtP_countPadT0 {rd : Reader} {σ : Val} (h : VtP rd σ) (W : ℕ → E) :
    σ (.n 2492) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 0 := by
  have a2536 := h.atomAt 2536 (.add (.n 2490) (.n 1441) (.n 1446)) (by decide +kernel)
  have a2537 := h.atomAt 2537 (.add (.n 2491) (.n 2490) (.n 1451)) (by decide +kernel)
  have a2538 := h.atomAt 2538 (.add (.n 2492) (.n 2491) (.n 1456)) (by decide +kernel)
  simp only [Atom.Holds] at a2536 a2537 a2538
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2536, a2537, a2538]
  ring

set_option maxRecDepth 100000 in
theorem vtP_countPadT1 {rd : Reader} {σ : Val} (h : VtP rd σ) (W : ℕ → E) :
    σ (.n 2496) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 1 := by
  have a2540 := h.atomAt 2540 (.add (.n 2494) (.n 1465) (.n 1474)) (by decide +kernel)
  have a2541 := h.atomAt 2541 (.add (.n 2495) (.n 2494) (.n 1483)) (by decide +kernel)
  have a2542 := h.atomAt 2542 (.add (.n 2496) (.n 2495) (.n 1492)) (by decide +kernel)
  simp only [Atom.Holds] at a2540 a2541 a2542
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2540, a2541, a2542]
  ring

set_option maxRecDepth 100000 in
theorem vtP_countPadT2 {rd : Reader} {σ : Val} (h : VtP rd σ) (W : ℕ → E) :
    σ (.n 2499) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 2 := by
  have a2545 := h.atomAt 2545 (.add (.n 2499) (.n 1501) (.n 1510)) (by decide +kernel)
  simp only [Atom.Holds] at a2545
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2545]

set_option maxRecDepth 100000 in
theorem vtP_countPadT3 {rd : Reader} {σ : Val} (h : VtP rd σ) (W : ℕ → E) :
    σ (.n 2504) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 3 := by
  have a2548 := h.atomAt 2548 (.add (.n 2502) (.n 1519) (.n 1528)) (by decide +kernel)
  have a2549 := h.atomAt 2549 (.add (.n 2503) (.n 2502) (.n 1537)) (by decide +kernel)
  have a2550 := h.atomAt 2550 (.add (.n 2504) (.n 2503) (.n 1546)) (by decide +kernel)
  simp only [Atom.Holds] at a2548 a2549 a2550
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2548, a2549, a2550]
  ring

set_option maxRecDepth 100000 in
theorem vtP_countPadT4 {rd : Reader} {σ : Val} (h : VtP rd σ) (W : ℕ → E) :
    σ (.n 2509) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 4 := by
  have a2553 := h.atomAt 2553 (.add (.n 2507) (.n 1555) (.n 1564)) (by decide +kernel)
  have a2554 := h.atomAt 2554 (.add (.n 2508) (.n 2507) (.n 1573)) (by decide +kernel)
  have a2555 := h.atomAt 2555 (.add (.n 2509) (.n 2508) (.n 1582)) (by decide +kernel)
  simp only [Atom.Holds] at a2553 a2554 a2555
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2553, a2554, a2555]
  ring

set_option maxRecDepth 100000 in
theorem vtP_countPadT5 {rd : Reader} {σ : Val} (h : VtP rd σ) (W : ℕ → E) :
    σ (.n 2537) = vtPadTable (fun c ↦ σ (.n c)) W 1 vtCountPadData 5 := by
  have a2558 := h.atomAt 2558 (.add (.n 2512) (.n 1591) (.n 1600)) (by decide +kernel)
  have a2559 := h.atomAt 2559 (.add (.n 2513) (.n 2512) (.n 1609)) (by decide +kernel)
  have a2560 := h.atomAt 2560 (.add (.n 2514) (.n 2513) (.n 1618)) (by decide +kernel)
  have a2561 := h.atomAt 2561 (.add (.n 2515) (.n 2514) (.n 1627)) (by decide +kernel)
  have a2562 := h.atomAt 2562 (.add (.n 2516) (.n 2515) (.n 1636)) (by decide +kernel)
  have a2563 := h.atomAt 2563 (.add (.n 2517) (.n 2516) (.n 1645)) (by decide +kernel)
  have a2564 := h.atomAt 2564 (.add (.n 2518) (.n 2517) (.n 1654)) (by decide +kernel)
  have a2565 := h.atomAt 2565 (.add (.n 2519) (.n 2518) (.n 1663)) (by decide +kernel)
  have a2566 := h.atomAt 2566 (.add (.n 2520) (.n 2519) (.n 1672)) (by decide +kernel)
  have a2567 := h.atomAt 2567 (.add (.n 2521) (.n 2520) (.n 1681)) (by decide +kernel)
  have a2568 := h.atomAt 2568 (.add (.n 2522) (.n 2521) (.n 1690)) (by decide +kernel)
  have a2569 := h.atomAt 2569 (.add (.n 2523) (.n 2522) (.n 1699)) (by decide +kernel)
  have a2570 := h.atomAt 2570 (.add (.n 2524) (.n 2523) (.n 1708)) (by decide +kernel)
  have a2571 := h.atomAt 2571 (.add (.n 2525) (.n 2524) (.n 1717)) (by decide +kernel)
  have a2572 := h.atomAt 2572 (.add (.n 2526) (.n 2525) (.n 1726)) (by decide +kernel)
  have a2573 := h.atomAt 2573 (.add (.n 2527) (.n 2526) (.n 1735)) (by decide +kernel)
  have a2574 := h.atomAt 2574 (.add (.n 2528) (.n 2527) (.n 1744)) (by decide +kernel)
  have a2575 := h.atomAt 2575 (.add (.n 2529) (.n 2528) (.n 1753)) (by decide +kernel)
  have a2576 := h.atomAt 2576 (.add (.n 2530) (.n 2529) (.n 1762)) (by decide +kernel)
  have a2577 := h.atomAt 2577 (.add (.n 2531) (.n 2530) (.n 1771)) (by decide +kernel)
  have a2578 := h.atomAt 2578 (.add (.n 2532) (.n 2531) (.n 1780)) (by decide +kernel)
  have a2579 := h.atomAt 2579 (.add (.n 2533) (.n 2532) (.n 1789)) (by decide +kernel)
  have a2580 := h.atomAt 2580 (.add (.n 2534) (.n 2533) (.n 1798)) (by decide +kernel)
  have a2581 := h.atomAt 2581 (.add (.n 2535) (.n 2534) (.n 1807)) (by decide +kernel)
  have a2582 := h.atomAt 2582 (.add (.n 2536) (.n 2535) (.n 1816)) (by decide +kernel)
  have a2583 := h.atomAt 2583 (.add (.n 2537) (.n 2536) (.n 1825)) (by decide +kernel)
  simp only [Atom.Holds] at a2558 a2559 a2560 a2561 a2562 a2563 a2564 a2565 a2566 a2567
  simp only [Atom.Holds] at a2568 a2569 a2570 a2571 a2572 a2573 a2574 a2575 a2576 a2577
  simp only [Atom.Holds] at a2578 a2579 a2580 a2581 a2582 a2583
  simp (config := { decide := true }) only [vtPadTable, vtCountPadData, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte,
    mul_one, add_zero]
  simp only [a2558, a2559, a2560, a2561, a2562, a2563, a2564, a2565, a2566, a2567, a2568, a2569,
    a2570, a2571, a2572, a2573, a2574, a2575, a2576, a2577, a2578, a2579, a2580, a2581, a2582,
    a2583]
  ring

set_option maxRecDepth 100000 in
/-- **The count side's padding sum.** -/
theorem vtP_count_pad {rd : Reader} {σ : Val} (h : VtP rd σ) (W : ℕ → E) :
    σ (.n 2539) = vtPadSum (fun c ↦ σ (.n c)) (fun t ↦ σ (.n (vtPadV t))) W 1 vtCountPadData := by
  have a2539 := h.atomAt 2539 (.mul (.n 2493) (.n 584) (.n 2492)) (by decide +kernel)
  have a2543 := h.atomAt 2543 (.mul (.n 2497) (.n 597) (.n 2496)) (by decide +kernel)
  have a2544 := h.atomAt 2544 (.add (.n 2498) (.n 2493) (.n 2497)) (by decide +kernel)
  have a2546 := h.atomAt 2546 (.mul (.n 2500) (.n 610) (.n 2499)) (by decide +kernel)
  have a2547 := h.atomAt 2547 (.add (.n 2501) (.n 2498) (.n 2500)) (by decide +kernel)
  have a2551 := h.atomAt 2551 (.mul (.n 2505) (.n 623) (.n 2504)) (by decide +kernel)
  have a2552 := h.atomAt 2552 (.add (.n 2506) (.n 2501) (.n 2505)) (by decide +kernel)
  have a2556 := h.atomAt 2556 (.mul (.n 2510) (.n 636) (.n 2509)) (by decide +kernel)
  have a2557 := h.atomAt 2557 (.add (.n 2511) (.n 2506) (.n 2510)) (by decide +kernel)
  have a2584 := h.atomAt 2584 (.mul (.n 2538) (.n 649) (.n 2537)) (by decide +kernel)
  have a2585 := h.atomAt 2585 (.add (.n 2539) (.n 2511) (.n 2538)) (by decide +kernel)
  simp only [Atom.Holds] at a2539 a2543 a2544 a2546 a2547 a2551 a2552 a2556 a2557 a2584
  simp only [Atom.Holds] at a2585
  simp only [a2539, a2543, a2544, a2546, a2547, a2551, a2552, a2556, a2557, a2584, a2585]
  simp only [vtPadSum, vtPadV]
  rw [← vtP_countPadT0 h W, ← vtP_countPadT1 h W, ← vtP_countPadT2 h W, ← vtP_countPadT3 h W,
    ← vtP_countPadT4 h W, ← vtP_countPadT5 h W]

/-- **The count side's total.** -/
theorem vtP_count_total {rd : Reader} {σ : Val} (h : VtP rd σ) :
    σ (.n 2544) = σ (.n 2539) + (1 + σ (.n 1826)) + σ (.n 2543) := by
  have a2586 := h.atomAt 2586 (.const (.n 2540) (word 1 0)) (by decide +kernel)
  have a2587 := h.atomAt 2587 (.add (.n 2541) (.n 2540) (.n 1826)) (by decide +kernel)
  have a2588 := h.atomAt 2588 (.add (.n 2542) (.n 2539) (.n 2541)) (by decide +kernel)
  have a2590 := h.atomAt 2590 (.add (.n 2544) (.n 2542) (.n 2543)) (by decide +kernel)
  simp only [Atom.Holds] at a2586 a2587 a2588 a2590
  rw [a2590, a2588, a2587, a2586, tb_word_one]

/-- The count side's selector sum is the running sum's copy. -/
theorem vtP_count_sel {rd : Reader} {σ : Val} (h : VtP rd σ) : σ (.n 1826) = σ (.n 1824) := by
  have a := h.atomAt 1912 (.copy (.n 1826) (.n 1824)) (by decide +kernel)
  simpa only [Atom.Holds] using a

end
end LeanVM.Guest.B1.Tables
