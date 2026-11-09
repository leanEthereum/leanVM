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
    [σ (.n 1968), σ (.n 1970), σ (.n 1972), σ (.n 1974), σ (.n 1976)] =
      [σ (.n 960), σ (.n 965), σ (.n 970), σ (.n 975), σ (.n 980)] := by
  have a1994 := h.atomAt 1994 (.copy (.n 1968) (.n 960)) (by decide +kernel)
  have a1996 := h.atomAt 1996 (.copy (.n 1970) (.n 965)) (by decide +kernel)
  have a1998 := h.atomAt 1998 (.copy (.n 1972) (.n 970)) (by decide +kernel)
  have a2000 := h.atomAt 2000 (.copy (.n 1974) (.n 975)) (by decide +kernel)
  have a2002 := h.atomAt 2002 (.copy (.n 1976) (.n 980)) (by decide +kernel)
  simp only [Atom.Holds] at a1994 a1996 a1998 a2000 a2002
  rw [a1994, a1996, a1998, a2000, a2002]

theorem vtPullSels1 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1978), σ (.n 1980), σ (.n 1982), σ (.n 1984), σ (.n 1986)] =
      [σ (.n 989), σ (.n 998), σ (.n 1007), σ (.n 1016), σ (.n 1025)] := by
  have a2004 := h.atomAt 2004 (.copy (.n 1978) (.n 989)) (by decide +kernel)
  have a2006 := h.atomAt 2006 (.copy (.n 1980) (.n 998)) (by decide +kernel)
  have a2008 := h.atomAt 2008 (.copy (.n 1982) (.n 1007)) (by decide +kernel)
  have a2010 := h.atomAt 2010 (.copy (.n 1984) (.n 1016)) (by decide +kernel)
  have a2012 := h.atomAt 2012 (.copy (.n 1986) (.n 1025)) (by decide +kernel)
  simp only [Atom.Holds] at a2004 a2006 a2008 a2010 a2012
  rw [a2004, a2006, a2008, a2010, a2012]

theorem vtPullSels2 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1988), σ (.n 1990), σ (.n 1992)] =
      [σ (.n 1034), σ (.n 1043), σ (.n 1052)] := by
  have a2014 := h.atomAt 2014 (.copy (.n 1988) (.n 1034)) (by decide +kernel)
  have a2016 := h.atomAt 2016 (.copy (.n 1990) (.n 1043)) (by decide +kernel)
  have a2018 := h.atomAt 2018 (.copy (.n 1992) (.n 1052)) (by decide +kernel)
  simp only [Atom.Holds] at a2014 a2016 a2018
  rw [a2014, a2016, a2018]

theorem vtPullSels3 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1994), σ (.n 1996), σ (.n 1998), σ (.n 2000), σ (.n 2002)] =
      [σ (.n 1061), σ (.n 1070), σ (.n 1079), σ (.n 1088), σ (.n 1097)] := by
  have a2020 := h.atomAt 2020 (.copy (.n 1994) (.n 1061)) (by decide +kernel)
  have a2022 := h.atomAt 2022 (.copy (.n 1996) (.n 1070)) (by decide +kernel)
  have a2024 := h.atomAt 2024 (.copy (.n 1998) (.n 1079)) (by decide +kernel)
  have a2026 := h.atomAt 2026 (.copy (.n 2000) (.n 1088)) (by decide +kernel)
  have a2028 := h.atomAt 2028 (.copy (.n 2002) (.n 1097)) (by decide +kernel)
  simp only [Atom.Holds] at a2020 a2022 a2024 a2026 a2028
  rw [a2020, a2022, a2024, a2026, a2028]

theorem vtPullSels4 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 2004), σ (.n 2006), σ (.n 2008), σ (.n 2010), σ (.n 2012)] =
      [σ (.n 1106), σ (.n 1115), σ (.n 1124), σ (.n 1133), σ (.n 1142)] := by
  have a2030 := h.atomAt 2030 (.copy (.n 2004) (.n 1106)) (by decide +kernel)
  have a2032 := h.atomAt 2032 (.copy (.n 2006) (.n 1115)) (by decide +kernel)
  have a2034 := h.atomAt 2034 (.copy (.n 2008) (.n 1124)) (by decide +kernel)
  have a2036 := h.atomAt 2036 (.copy (.n 2010) (.n 1133)) (by decide +kernel)
  have a2038 := h.atomAt 2038 (.copy (.n 2012) (.n 1142)) (by decide +kernel)
  simp only [Atom.Holds] at a2030 a2032 a2034 a2036 a2038
  rw [a2030, a2032, a2034, a2036, a2038]

theorem vtPullSels5 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 2014), σ (.n 2016), σ (.n 2018), σ (.n 2020), σ (.n 2022), σ (.n 2024), σ (.n 2026), σ (.n 2028), σ (.n 2030), σ (.n 2032), σ (.n 2034), σ (.n 2036), σ (.n 2038), σ (.n 2040), σ (.n 2042), σ (.n 2044), σ (.n 2046), σ (.n 2048), σ (.n 2050), σ (.n 2052), σ (.n 2054), σ (.n 2056), σ (.n 2058), σ (.n 2060), σ (.n 2062), σ (.n 2064), σ (.n 2066), σ (.n 2068)] =
      [σ (.n 1151), σ (.n 1160), σ (.n 1169), σ (.n 1178), σ (.n 1187), σ (.n 1196), σ (.n 1205), σ (.n 1214), σ (.n 1223), σ (.n 1232), σ (.n 1241), σ (.n 1250), σ (.n 1259), σ (.n 1268), σ (.n 1277), σ (.n 1286), σ (.n 1295), σ (.n 1304), σ (.n 1313), σ (.n 1322), σ (.n 1331), σ (.n 1340), σ (.n 1349), σ (.n 1358), σ (.n 1367), σ (.n 1376), σ (.n 1385), σ (.n 1394)] := by
  have a2040 := h.atomAt 2040 (.copy (.n 2014) (.n 1151)) (by decide +kernel)
  have a2042 := h.atomAt 2042 (.copy (.n 2016) (.n 1160)) (by decide +kernel)
  have a2044 := h.atomAt 2044 (.copy (.n 2018) (.n 1169)) (by decide +kernel)
  have a2046 := h.atomAt 2046 (.copy (.n 2020) (.n 1178)) (by decide +kernel)
  have a2048 := h.atomAt 2048 (.copy (.n 2022) (.n 1187)) (by decide +kernel)
  have a2050 := h.atomAt 2050 (.copy (.n 2024) (.n 1196)) (by decide +kernel)
  have a2052 := h.atomAt 2052 (.copy (.n 2026) (.n 1205)) (by decide +kernel)
  have a2054 := h.atomAt 2054 (.copy (.n 2028) (.n 1214)) (by decide +kernel)
  have a2056 := h.atomAt 2056 (.copy (.n 2030) (.n 1223)) (by decide +kernel)
  have a2058 := h.atomAt 2058 (.copy (.n 2032) (.n 1232)) (by decide +kernel)
  have a2060 := h.atomAt 2060 (.copy (.n 2034) (.n 1241)) (by decide +kernel)
  have a2062 := h.atomAt 2062 (.copy (.n 2036) (.n 1250)) (by decide +kernel)
  have a2064 := h.atomAt 2064 (.copy (.n 2038) (.n 1259)) (by decide +kernel)
  have a2066 := h.atomAt 2066 (.copy (.n 2040) (.n 1268)) (by decide +kernel)
  have a2068 := h.atomAt 2068 (.copy (.n 2042) (.n 1277)) (by decide +kernel)
  have a2070 := h.atomAt 2070 (.copy (.n 2044) (.n 1286)) (by decide +kernel)
  have a2072 := h.atomAt 2072 (.copy (.n 2046) (.n 1295)) (by decide +kernel)
  have a2074 := h.atomAt 2074 (.copy (.n 2048) (.n 1304)) (by decide +kernel)
  have a2076 := h.atomAt 2076 (.copy (.n 2050) (.n 1313)) (by decide +kernel)
  have a2078 := h.atomAt 2078 (.copy (.n 2052) (.n 1322)) (by decide +kernel)
  have a2080 := h.atomAt 2080 (.copy (.n 2054) (.n 1331)) (by decide +kernel)
  have a2082 := h.atomAt 2082 (.copy (.n 2056) (.n 1340)) (by decide +kernel)
  have a2084 := h.atomAt 2084 (.copy (.n 2058) (.n 1349)) (by decide +kernel)
  have a2086 := h.atomAt 2086 (.copy (.n 2060) (.n 1358)) (by decide +kernel)
  have a2088 := h.atomAt 2088 (.copy (.n 2062) (.n 1367)) (by decide +kernel)
  have a2090 := h.atomAt 2090 (.copy (.n 2064) (.n 1376)) (by decide +kernel)
  have a2092 := h.atomAt 2092 (.copy (.n 2066) (.n 1385)) (by decide +kernel)
  have a2094 := h.atomAt 2094 (.copy (.n 2068) (.n 1394)) (by decide +kernel)
  simp only [Atom.Holds] at a2040 a2042 a2044 a2046 a2048 a2050 a2052 a2054 a2056 a2058 a2060 a2062 a2064 a2066 a2068 a2070 a2072 a2074 a2076 a2078 a2080 a2082 a2084 a2086 a2088 a2090 a2092 a2094
  rw [a2040, a2042, a2044, a2046, a2048, a2050, a2052, a2054, a2056, a2058, a2060, a2062, a2064, a2066, a2068, a2070, a2072, a2074, a2076, a2078, a2080, a2082, a2084, a2086, a2088, a2090, a2092, a2094]

end
end LeanVM.Guest.B1.Tables
