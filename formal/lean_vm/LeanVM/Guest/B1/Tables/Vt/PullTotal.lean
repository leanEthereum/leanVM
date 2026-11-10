/-
  LeanVM.Guest.B1.Tables.Vt.PullTotal

  `verify_tables`' pull side total: its framework blocks' fingerprints (with the final memory and
  bytecode counts), the push side's padding sum, the selector sum and the GKR pull value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PushFw

/-!
# The pull side's total (G:2228-2230, 2318-2322)

The pull side's blocks mirror the push side's: their eq weights are the push blocks' copies, and
their padding sum is the push side's. `vt_pull_total`: `bus_table_total[PULL]`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `g^(2^19 - 1)`, the final `pc`, as the data writes it. -/
abbrev vtWFinalPc : E := word 12261764870545049476 0

set_option maxRecDepth 100000 in
/-- **The pull side's total.** -/
theorem vt_pull_total {rd : Reader} {σ : Val} (h : VtH rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2073) = σ (.n 796) * (σ (.n 14) + (W 0 + W 1 * vtWFinalPc + W 2)) +
      σ (.n 820) * (σ (.n 14) + (W 0 * gen + W 1 * σ (.n 1839) + W 2 * σ (.n 1843) +
        W 3 * σ (.n 1856) + W 4 * σ (.n 1860) + W 5 * σ (.n 1864))) +
      σ (.n 890) * (σ (.n 14) + (W 0 * gen ^ 2 + W 1 * σ (.n 1881) + W 2 * σ (.n 1898) +
        σ (.n 581))) + σ (.n 1815) +
      (1 + (σ (.n 796) + σ (.n 820) + σ (.n 890) +
        (vtPushPadData.map fun x ↦ σ (.n x.2.2.1)).sum)) + σ (.n 26) := by
  have a3914 := h.atomAt 1860 (.load (.n 1822) (.n 13) 0) (by decide +kernel)
  have a3915 := h.atomAt 1861 (.load (.n 1823) (.n 13) 1) (by decide +kernel)
  have a3916 := h.atomAt 1862 (.const (.n 1824) (word 12261764870545049476 0)) (by decide +kernel)
  have a3917 := h.atomAt 1863 (.mul (.n 1825) (.n 1823) (.n 1824)) (by decide +kernel)
  have a3918 := h.atomAt 1864 (.add (.n 1826) (.n 1822) (.n 1825)) (by decide +kernel)
  have a3919 := h.atomAt 1865 (.load (.n 1827) (.n 13) 2) (by decide +kernel)
  have a3920 := h.atomAt 1866 (.add (.n 1828) (.n 1826) (.n 1827)) (by decide +kernel)
  have a3921 := h.atomAt 1867 (.const (.n 1829) (word 0 0)) (by decide +kernel)
  have a3922 := h.atomAt 1868 (.mul (.n 1830) (.n 1829) (.n 581)) (by decide +kernel)
  have a3923 := h.atomAt 1869 (.add (.n 1831) (.n 1828) (.n 1830)) (by decide +kernel)
  have a3924 := h.atomAt 1870 (.add (.n 1832) (.n 14) (.n 1831)) (by decide +kernel)
  have a3925 := h.atomAt 1871 (.mul (.n 1833) (.n 796) (.n 1832)) (by decide +kernel)
  have a3929 := h.atomAt 1872 (.add (.n 1834) (.n 796) (.n 820)) (by decide +kernel)
  have a3931 := h.atomAt 1874 (.load (.n 1836) (.n 13) 0) (by decide +kernel)
  have a3932 := h.atomAt 1875 (.const (.n 1837) (word 2 0)) (by decide +kernel)
  have a3933 := h.atomAt 1876 (.mul (.n 1838) (.n 1836) (.n 1837)) (by decide +kernel)
  have a3935 := h.atomAt 1878 (.load (.n 1840) (.n 13) 1) (by decide +kernel)
  have a3936 := h.atomAt 1879 (.mul (.n 1841) (.n 1840) (.n 1839)) (by decide +kernel)
  have a3937 := h.atomAt 1880 (.add (.n 1842) (.n 1838) (.n 1841)) (by decide +kernel)
  have a3949 := h.atomAt 1891 (.load (.n 1853) (.n 13) 2) (by decide +kernel)
  have a3950 := h.atomAt 1892 (.mul (.n 1854) (.n 1853) (.n 1843)) (by decide +kernel)
  have a3951 := h.atomAt 1893 (.add (.n 1855) (.n 1842) (.n 1854)) (by decide +kernel)
  have a3953 := h.atomAt 1895 (.load (.n 1857) (.n 13) 3) (by decide +kernel)
  have a3954 := h.atomAt 1896 (.mul (.n 1858) (.n 1857) (.n 1856)) (by decide +kernel)
  have a3955 := h.atomAt 1897 (.add (.n 1859) (.n 1855) (.n 1858)) (by decide +kernel)
  have a3957 := h.atomAt 1899 (.load (.n 1861) (.n 13) 4) (by decide +kernel)
  have a3958 := h.atomAt 1900 (.mul (.n 1862) (.n 1861) (.n 1860)) (by decide +kernel)
  have a3959 := h.atomAt 1901 (.add (.n 1863) (.n 1859) (.n 1862)) (by decide +kernel)
  have a3961 := h.atomAt 1903 (.load (.n 1865) (.n 13) 5) (by decide +kernel)
  have a3962 := h.atomAt 1904 (.mul (.n 1866) (.n 1865) (.n 1864)) (by decide +kernel)
  have a3963 := h.atomAt 1905 (.add (.n 1867) (.n 1863) (.n 1866)) (by decide +kernel)
  have a3964 := h.atomAt 1906 (.const (.n 1868) (word 0 0)) (by decide +kernel)
  have a3965 := h.atomAt 1907 (.mul (.n 1869) (.n 1868) (.n 581)) (by decide +kernel)
  have a3966 := h.atomAt 1908 (.add (.n 1870) (.n 1867) (.n 1869)) (by decide +kernel)
  have a3967 := h.atomAt 1909 (.add (.n 1871) (.n 14) (.n 1870)) (by decide +kernel)
  have a3968 := h.atomAt 1910 (.mul (.n 1872) (.n 820) (.n 1871)) (by decide +kernel)
  have a3969 := h.atomAt 1911 (.add (.n 1873) (.n 1833) (.n 1872)) (by decide +kernel)
  have a3973 := h.atomAt 1914 (.add (.n 1876) (.n 1834) (.n 890)) (by decide +kernel)
  have a3975 := h.atomAt 1916 (.load (.n 1878) (.n 13) 0) (by decide +kernel)
  have a3976 := h.atomAt 1917 (.const (.n 1879) (word 4 0)) (by decide +kernel)
  have a3977 := h.atomAt 1918 (.mul (.n 1880) (.n 1878) (.n 1879)) (by decide +kernel)
  have a3979 := h.atomAt 1920 (.load (.n 1882) (.n 13) 1) (by decide +kernel)
  have a3980 := h.atomAt 1921 (.mul (.n 1883) (.n 1882) (.n 1881)) (by decide +kernel)
  have a3981 := h.atomAt 1922 (.add (.n 1884) (.n 1880) (.n 1883)) (by decide +kernel)
  have a3994 := h.atomAt 1934 (.load (.n 1908) (.n 13) 2) (by decide +kernel)
  have a3995 := h.atomAt 1935 (.mul (.n 1909) (.n 1908) (.n 1898)) (by decide +kernel)
  have a3996 := h.atomAt 1936 (.add (.n 1910) (.n 1884) (.n 1909)) (by decide +kernel)
  have a3997 := h.atomAt 1937 (.load (.n 1911) (.n 13) 3) (by decide +kernel)
  have a3998 := h.atomAt 1938 (.const (.n 1912) (word 0 0)) (by decide +kernel)
  have a3999 := h.atomAt 1939 (.mul (.n 1913) (.n 1911) (.n 1912)) (by decide +kernel)
  have a4000 := h.atomAt 1940 (.add (.n 1914) (.n 1910) (.n 1913)) (by decide +kernel)
  have a4001 := h.atomAt 1941 (.load (.n 1915) (.n 13) 4) (by decide +kernel)
  have a4002 := h.atomAt 1942 (.const (.n 1916) (word 0 0)) (by decide +kernel)
  have a4003 := h.atomAt 1943 (.mul (.n 1917) (.n 1915) (.n 1916)) (by decide +kernel)
  have a4004 := h.atomAt 1944 (.add (.n 1918) (.n 1914) (.n 1917)) (by decide +kernel)
  have a4005 := h.atomAt 1945 (.load (.n 1919) (.n 13) 5) (by decide +kernel)
  have a4006 := h.atomAt 1946 (.const (.n 1920) (word 0 0)) (by decide +kernel)
  have a4007 := h.atomAt 1947 (.mul (.n 1921) (.n 1919) (.n 1920)) (by decide +kernel)
  have a4008 := h.atomAt 1948 (.add (.n 1922) (.n 1918) (.n 1921)) (by decide +kernel)
  have a4009 := h.atomAt 1949 (.load (.n 1923) (.n 13) 6) (by decide +kernel)
  have a4010 := h.atomAt 1950 (.const (.n 1924) (word 0 0)) (by decide +kernel)
  have a4011 := h.atomAt 1951 (.mul (.n 1925) (.n 1923) (.n 1924)) (by decide +kernel)
  have a4012 := h.atomAt 1952 (.add (.n 1926) (.n 1922) (.n 1925)) (by decide +kernel)
  have a4013 := h.atomAt 1953 (.load (.n 1927) (.n 13) 7) (by decide +kernel)
  have a4014 := h.atomAt 1954 (.const (.n 1928) (word 0 0)) (by decide +kernel)
  have a4015 := h.atomAt 1955 (.mul (.n 1929) (.n 1927) (.n 1928)) (by decide +kernel)
  have a4016 := h.atomAt 1956 (.add (.n 1930) (.n 1926) (.n 1929)) (by decide +kernel)
  have a4017 := h.atomAt 1957 (.load (.n 1931) (.n 13) 8) (by decide +kernel)
  have a4018 := h.atomAt 1958 (.const (.n 1932) (word 0 0)) (by decide +kernel)
  have a4019 := h.atomAt 1959 (.mul (.n 1933) (.n 1931) (.n 1932)) (by decide +kernel)
  have a4020 := h.atomAt 1960 (.add (.n 1934) (.n 1930) (.n 1933)) (by decide +kernel)
  have a4021 := h.atomAt 1961 (.load (.n 1935) (.n 13) 9) (by decide +kernel)
  have a4022 := h.atomAt 1962 (.const (.n 1936) (word 0 0)) (by decide +kernel)
  have a4023 := h.atomAt 1963 (.mul (.n 1937) (.n 1935) (.n 1936)) (by decide +kernel)
  have a4024 := h.atomAt 1964 (.add (.n 1938) (.n 1934) (.n 1937)) (by decide +kernel)
  have a4025 := h.atomAt 1965 (.load (.n 1939) (.n 13) 10) (by decide +kernel)
  have a4026 := h.atomAt 1966 (.const (.n 1940) (word 0 0)) (by decide +kernel)
  have a4027 := h.atomAt 1967 (.mul (.n 1941) (.n 1939) (.n 1940)) (by decide +kernel)
  have a4028 := h.atomAt 1968 (.add (.n 1942) (.n 1938) (.n 1941)) (by decide +kernel)
  have a4029 := h.atomAt 1969 (.load (.n 1943) (.n 13) 11) (by decide +kernel)
  have a4030 := h.atomAt 1970 (.const (.n 1944) (word 0 0)) (by decide +kernel)
  have a4031 := h.atomAt 1971 (.mul (.n 1945) (.n 1943) (.n 1944)) (by decide +kernel)
  have a4032 := h.atomAt 1972 (.add (.n 1946) (.n 1942) (.n 1945)) (by decide +kernel)
  have a4033 := h.atomAt 1973 (.load (.n 1947) (.n 13) 12) (by decide +kernel)
  have a4034 := h.atomAt 1974 (.const (.n 1948) (word 0 0)) (by decide +kernel)
  have a4035 := h.atomAt 1975 (.mul (.n 1949) (.n 1947) (.n 1948)) (by decide +kernel)
  have a4036 := h.atomAt 1976 (.add (.n 1950) (.n 1946) (.n 1949)) (by decide +kernel)
  have a4037 := h.atomAt 1977 (.load (.n 1951) (.n 13) 13) (by decide +kernel)
  have c1978 := h.atomAt 1978 (.const (.n 1952) (word 0 0)) (by decide +kernel)
  have c1979 := h.atomAt 1979 (.mul (.n 1953) (.n 1951) (.n 1952)) (by decide +kernel)
  have c1980 := h.atomAt 1980 (.add (.n 1954) (.n 1950) (.n 1953)) (by decide +kernel)
  have c1982 := h.atomAt 1982 (.const (.n 1956) (word 0 0)) (by decide +kernel)
  have c1983 := h.atomAt 1983 (.mul (.n 1957) (.n 1955) (.n 1956)) (by decide +kernel)
  have c1984 := h.atomAt 1984 (.add (.n 1958) (.n 1954) (.n 1957)) (by decide +kernel)
  have a4038 := h.atomAt 1986 (.const (.n 1960) (word 0 0)) (by decide +kernel)
  have a4039 := h.atomAt 1987 (.mul (.n 1961) (.n 1959) (.n 1960)) (by decide +kernel)
  have a4040 := h.atomAt 1988 (.add (.n 1962) (.n 1958) (.n 1961)) (by decide +kernel)
  have a4041 := h.atomAt 1989 (.add (.n 1963) (.n 1962) (.n 581)) (by decide +kernel)
  have a4042 := h.atomAt 1990 (.add (.n 1964) (.n 14) (.n 1963)) (by decide +kernel)
  have a4043 := h.atomAt 1991 (.mul (.n 1965) (.n 890) (.n 1964)) (by decide +kernel)
  have a4044 := h.atomAt 1992 (.add (.n 1966) (.n 1873) (.n 1965)) (by decide +kernel)
  have a4048 := h.atomAt 1993 (.add (.n 1967) (.n 1876) (.n 960)) (by decide +kernel)
  have a4053 := h.atomAt 1995 (.add (.n 1969) (.n 1967) (.n 965)) (by decide +kernel)
  have a4058 := h.atomAt 1997 (.add (.n 1971) (.n 1969) (.n 970)) (by decide +kernel)
  have a4063 := h.atomAt 1999 (.add (.n 1973) (.n 1971) (.n 975)) (by decide +kernel)
  have a4068 := h.atomAt 2001 (.add (.n 1975) (.n 1973) (.n 980)) (by decide +kernel)
  have a4073 := h.atomAt 2003 (.add (.n 1977) (.n 1975) (.n 989)) (by decide +kernel)
  have a4078 := h.atomAt 2005 (.add (.n 1979) (.n 1977) (.n 998)) (by decide +kernel)
  have a4083 := h.atomAt 2007 (.add (.n 1981) (.n 1979) (.n 1007)) (by decide +kernel)
  have a4088 := h.atomAt 2009 (.add (.n 1983) (.n 1981) (.n 1016)) (by decide +kernel)
  have a4093 := h.atomAt 2011 (.add (.n 1985) (.n 1983) (.n 1025)) (by decide +kernel)
  have a4098 := h.atomAt 2013 (.add (.n 1987) (.n 1985) (.n 1034)) (by decide +kernel)
  have a4103 := h.atomAt 2015 (.add (.n 1989) (.n 1987) (.n 1043)) (by decide +kernel)
  have a4108 := h.atomAt 2017 (.add (.n 1991) (.n 1989) (.n 1052)) (by decide +kernel)
  have a4113 := h.atomAt 2019 (.add (.n 1993) (.n 1991) (.n 1061)) (by decide +kernel)
  have a4118 := h.atomAt 2021 (.add (.n 1995) (.n 1993) (.n 1070)) (by decide +kernel)
  have a4123 := h.atomAt 2023 (.add (.n 1997) (.n 1995) (.n 1079)) (by decide +kernel)
  have a4128 := h.atomAt 2025 (.add (.n 1999) (.n 1997) (.n 1088)) (by decide +kernel)
  have a4133 := h.atomAt 2027 (.add (.n 2001) (.n 1999) (.n 1097)) (by decide +kernel)
  have a4138 := h.atomAt 2029 (.add (.n 2003) (.n 2001) (.n 1106)) (by decide +kernel)
  have a4143 := h.atomAt 2031 (.add (.n 2005) (.n 2003) (.n 1115)) (by decide +kernel)
  have a4148 := h.atomAt 2033 (.add (.n 2007) (.n 2005) (.n 1124)) (by decide +kernel)
  have a4153 := h.atomAt 2035 (.add (.n 2009) (.n 2007) (.n 1133)) (by decide +kernel)
  have a4158 := h.atomAt 2037 (.add (.n 2011) (.n 2009) (.n 1142)) (by decide +kernel)
  have a4163 := h.atomAt 2039 (.add (.n 2013) (.n 2011) (.n 1151)) (by decide +kernel)
  have a4168 := h.atomAt 2041 (.add (.n 2015) (.n 2013) (.n 1160)) (by decide +kernel)
  have a4173 := h.atomAt 2043 (.add (.n 2017) (.n 2015) (.n 1169)) (by decide +kernel)
  have a4178 := h.atomAt 2045 (.add (.n 2019) (.n 2017) (.n 1178)) (by decide +kernel)
  have a4183 := h.atomAt 2047 (.add (.n 2021) (.n 2019) (.n 1187)) (by decide +kernel)
  have a4188 := h.atomAt 2049 (.add (.n 2023) (.n 2021) (.n 1196)) (by decide +kernel)
  have a4193 := h.atomAt 2051 (.add (.n 2025) (.n 2023) (.n 1205)) (by decide +kernel)
  have a4198 := h.atomAt 2053 (.add (.n 2027) (.n 2025) (.n 1214)) (by decide +kernel)
  have a4203 := h.atomAt 2055 (.add (.n 2029) (.n 2027) (.n 1223)) (by decide +kernel)
  have a4208 := h.atomAt 2057 (.add (.n 2031) (.n 2029) (.n 1232)) (by decide +kernel)
  have a4213 := h.atomAt 2059 (.add (.n 2033) (.n 2031) (.n 1241)) (by decide +kernel)
  have a4218 := h.atomAt 2061 (.add (.n 2035) (.n 2033) (.n 1250)) (by decide +kernel)
  have a4223 := h.atomAt 2063 (.add (.n 2037) (.n 2035) (.n 1259)) (by decide +kernel)
  have a4228 := h.atomAt 2065 (.add (.n 2039) (.n 2037) (.n 1268)) (by decide +kernel)
  have a4233 := h.atomAt 2067 (.add (.n 2041) (.n 2039) (.n 1277)) (by decide +kernel)
  have a4238 := h.atomAt 2069 (.add (.n 2043) (.n 2041) (.n 1286)) (by decide +kernel)
  have a4243 := h.atomAt 2071 (.add (.n 2045) (.n 2043) (.n 1295)) (by decide +kernel)
  have a4248 := h.atomAt 2073 (.add (.n 2047) (.n 2045) (.n 1304)) (by decide +kernel)
  have a4253 := h.atomAt 2075 (.add (.n 2049) (.n 2047) (.n 1313)) (by decide +kernel)
  have a4258 := h.atomAt 2077 (.add (.n 2051) (.n 2049) (.n 1322)) (by decide +kernel)
  have a4263 := h.atomAt 2079 (.add (.n 2053) (.n 2051) (.n 1331)) (by decide +kernel)
  have a4268 := h.atomAt 2081 (.add (.n 2055) (.n 2053) (.n 1340)) (by decide +kernel)
  have a4273 := h.atomAt 2083 (.add (.n 2057) (.n 2055) (.n 1349)) (by decide +kernel)
  have a4278 := h.atomAt 2085 (.add (.n 2059) (.n 2057) (.n 1358)) (by decide +kernel)
  have a4283 := h.atomAt 2087 (.add (.n 2061) (.n 2059) (.n 1367)) (by decide +kernel)
  have a4288 := h.atomAt 2089 (.add (.n 2063) (.n 2061) (.n 1376)) (by decide +kernel)
  have a4293 := h.atomAt 2091 (.add (.n 2065) (.n 2063) (.n 1385)) (by decide +kernel)
  have a4298 := h.atomAt 2093 (.add (.n 2067) (.n 2065) (.n 1394)) (by decide +kernel)
  have a4300 := h.atomAt 2095 (.add (.n 2069) (.n 1966) (.n 1815)) (by decide +kernel)
  have a4301 := h.atomAt 2096 (.const (.n 2070) (word 1 0)) (by decide +kernel)
  have a4302 := h.atomAt 2097 (.add (.n 2071) (.n 2070) (.n 2067)) (by decide +kernel)
  have a4303 := h.atomAt 2098 (.add (.n 2072) (.n 2069) (.n 2071)) (by decide +kernel)
  have a4304 := h.atomAt 2099 (.add (.n 2073) (.n 2072) (.n 26)) (by decide +kernel)
  have e3914 := tb_loadHolds_unique a3914 (hw 0 (by norm_num))
  have e3915 := tb_loadHolds_unique a3915 (hw 1 (by norm_num))
  have e3919 := tb_loadHolds_unique a3919 (hw 2 (by norm_num))
  have e3931 := tb_loadHolds_unique a3931 (hw 0 (by norm_num))
  have e3935 := tb_loadHolds_unique a3935 (hw 1 (by norm_num))
  have e3949 := tb_loadHolds_unique a3949 (hw 2 (by norm_num))
  have e3953 := tb_loadHolds_unique a3953 (hw 3 (by norm_num))
  have e3957 := tb_loadHolds_unique a3957 (hw 4 (by norm_num))
  have e3961 := tb_loadHolds_unique a3961 (hw 5 (by norm_num))
  have e3975 := tb_loadHolds_unique a3975 (hw 0 (by norm_num))
  have e3979 := tb_loadHolds_unique a3979 (hw 1 (by norm_num))
  have e3994 := tb_loadHolds_unique a3994 (hw 2 (by norm_num))
  have e3997 := tb_loadHolds_unique a3997 (hw 3 (by norm_num))
  have e4001 := tb_loadHolds_unique a4001 (hw 4 (by norm_num))
  have e4005 := tb_loadHolds_unique a4005 (hw 5 (by norm_num))
  have e4009 := tb_loadHolds_unique a4009 (hw 6 (by norm_num))
  have e4013 := tb_loadHolds_unique a4013 (hw 7 (by norm_num))
  have e4017 := tb_loadHolds_unique a4017 (hw 8 (by norm_num))
  have e4021 := tb_loadHolds_unique a4021 (hw 9 (by norm_num))
  have e4025 := tb_loadHolds_unique a4025 (hw 10 (by norm_num))
  have e4029 := tb_loadHolds_unique a4029 (hw 11 (by norm_num))
  have e4033 := tb_loadHolds_unique a4033 (hw 12 (by norm_num))
  have e4037 := tb_loadHolds_unique a4037 (hw 13 (by norm_num))
  simp only [Atom.Holds] at a3916 a3917 a3918 a3920 a3921 a3922 a3923 a3924 a3925 a3929
  simp only [Atom.Holds] at a3932 a3933 a3936 a3937 a3950 a3951 a3954 a3955 a3958 a3959
  simp only [Atom.Holds] at a3962 a3963 a3964 a3965 a3966 a3967 a3968 a3969 a3973 a3976
  simp only [Atom.Holds] at a3977 a3980 a3981 a3995 a3996 a3998 a3999 a4000 a4002 a4003
  simp only [Atom.Holds] at a4004 a4006 a4007 a4008 a4010 a4011 a4012 a4014 a4015 a4016
  simp only [Atom.Holds] at a4018 a4019 a4020 a4022 a4023 a4024 a4026 a4027 a4028 a4030
  simp only [Atom.Holds] at a4031 a4032 a4034 a4035 a4036 a4038 a4039 a4040 a4041 a4042
  simp only [Atom.Holds] at c1978 c1979 c1980 c1982 c1983 c1984
  simp only [Atom.Holds] at a4043 a4044 a4048 a4053 a4058 a4063 a4068 a4073 a4078 a4083
  simp only [Atom.Holds] at a4088 a4093 a4098 a4103 a4108 a4113 a4118 a4123 a4128 a4133
  simp only [Atom.Holds] at a4138 a4143 a4148 a4153 a4158 a4163 a4168 a4173 a4178 a4183
  simp only [Atom.Holds] at a4188 a4193 a4198 a4203 a4208 a4213 a4218 a4223 a4228 a4233
  simp only [Atom.Holds] at a4238 a4243 a4248 a4253 a4258 a4263 a4268 a4273 a4278 a4283
  simp only [Atom.Holds] at a4288 a4293 a4298 a4300 a4301 a4302 a4303 a4304
  simp only [e3914, e3915, a3916, a3917, a3918, e3919, a3920, a3921, a3922, a3923, a3924, a3925, a3929,
    e3931, a3932, a3933, e3935, a3936, a3937, e3949, a3950, a3951, e3953, a3954, a3955, e3957,
    a3958, a3959, e3961, a3962, a3963, a3964, a3965, a3966, a3967, a3968, a3969, a3973, e3975,
    a3976, a3977, e3979, a3980, a3981, e3994, a3995, a3996, e3997, a3998, a3999, a4000, e4001,
    a4002, a4003, a4004, e4005, a4006, a4007, a4008, e4009, a4010, a4011, a4012, e4013, a4014,
    a4015, a4016, e4017, a4018, a4019, a4020, e4021, a4022, a4023, a4024, e4025, a4026, a4027,
    a4028, e4029, a4030, a4031, a4032, e4033, a4034, a4035, a4036, e4037, a4038, a4039, a4040,
    c1984, c1983, c1982, c1980, c1979, c1978,
    a4041, a4042, a4043, a4044, a4048, a4053, a4058, a4063, a4068, a4073, a4078, a4083, a4088,
    a4093, a4098, a4103, a4108, a4113, a4118, a4123, a4128, a4133, a4138, a4143, a4148, a4153,
    a4158, a4163, a4168, a4173, a4178, a4183, a4188, a4193, a4198, a4203, a4208, a4213, a4218,
    a4223, a4228, a4233, a4238, a4243, a4248, a4253, a4258, a4263, a4268, a4273, a4278, a4283,
    a4288, a4293, a4298, a4300, a4301, a4302, a4303, a4304]
  simp only [vtPushPadData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [tb_word_zero, tb_word_one, tb_word_gen, show (4 : ℕ) = 2 ^ 2 by norm_num,
    tb_word_two_pow (by norm_num)]
  ring

end
end LeanVM.Guest.B1.Tables
