/-
  LeanVM.Guest.B1.Tables.Vt.BcShare

  `verify_tables`' bytecode share: the slot sumcheck's four rounds, its point in `bc_point`, the
  bytecode's value read after it, and the closing check against the slot weights' fold.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Fresh
public import LeanVM.Guest.B1.Fs.TailRound
public import LeanVM.Guest.B1.Gkr.Spec
public import LeanVM.Protocol.EndToEnd.Complete.BusShare

/-!
# The bytecode share (G:2421-2468)

After the framework's four words, the share `S` and the first round's `c0`, `c2` ride the stream
(`vt_fresh`); the first round's challenge is squeezed after them, its claim
`c0 + r (S + (1 + r) c2)` computed in place, and the three other rounds are `opening_tail_round`
calls. Each challenge is stored in `bc_point`. The bytecode's value is then read, and the last
claim checked against `fp_w` folded at the four challenges (`multilinearEval`) times the value.

`vt_bc`: from the sponge after the framework's words, `bytecodeShare` reads `S`, `c0`, `c2`, the
three rounds' six words and the value, and returns the share, the point and the value, leaving the
value waiting on the last round's capacity.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (multilinearEval_eq_dot)

@[expose] public section

/-- A plain round of `sumcheck _ 3` on the carried capacity, then the rounds after it. -/
theorem vt_tail_cons (cap : List E) (c0 c2 claim : E) {rest : List (Option E)} {ys pt : List E}
    {fin : E} {s2 : Fs}
    (h2 : RunsTo (sumcheck (c0 + ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1 *
        (claim + (1 + ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1) * c2)) 3 rest)
      ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.2 ys (pt, fin) s2) :
    RunsTo (sumcheck claim 3 (none :: rest)) ⟨cap, []⟩ ([c0, c2] ++ ys)
      (((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1 :: pt, fin) s2 := by
  rw [tail_eval] at h2
  exact runsTo_sumcheck_cons (runsTo_roundPolyNone ⟨cap, []⟩ claim c0 [c2] 3 rfl (by decide)) h2

/-- `opening_tail_round`'s returns, by its meaning. -/
theorem vt_otr {rd : Reader} {f0 f1 f2 f3 f4 cur claim tabs : E} {rets : List E}
    (h : coreProgram.Rel rd "opening_tail_round" [f0, f1, f2, f3, f4, cur, claim, tabs] rets) :
    ∃ c0 c2 : E, ReadsAt rd cur [c0, c2] ∧
      rets = ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.2.cap ++
        [cur * gen ^ 2, c0 + ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll [c0, c2]
          dsObserve).squeeze.1 * (claim + (1 + ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll
          [c0, c2] dsObserve).squeeze.1) * c2),
          ((⟨[f0, f1, f2, f3, f4], []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1] :=
  (opening_tail_round_holds rd _ _).mp h

/-- An eight-word return split as five capacity cells and three words. -/
theorem vt_split8 {a0 a1 a2 a3 a4 a5 a6 a7 p q r : E} {C : List E} (hC : C.length = 5)
    (h : [a0, a1, a2, a3, a4, a5, a6, a7] = C ++ [p, q, r]) :
    [a0, a1, a2, a3, a4] = C ∧ a5 = p ∧ a6 = q ∧ a7 = r := by
  match C, hC with
  | [c0, c1, c2, c3, c4], _ =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := h
    subst h0 h1 h2 h3 h4
    exact ⟨rfl, h5, h6, h7⟩

/-- A list of length `16` is its sixteen entries. -/
theorem vt_list16 (w : List E) (hw : w.length = 16) :
    w = (List.range 16).map fun i ↦ w.getD i 0 := by
  apply List.ext_getElem (by simp [hw])
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

set_option maxRecDepth 10000 in
/-- **The bytecode share.** -/
theorem vt_bc {rd : Reader} {σ : Val} (h : VtH rd σ) {weights : List E}
    (hwl : weights.length = 16) (hW : TbReadsAt rd (σ (.n 13)) weights) (low : List E) :
    ∃ ys : List E, ys.length = 6 ∧ TbReadsAt rd (σ (.n 5) * gen ^ 7) (ys ++ [σ (.n 1905)]) ∧
      TbReadsAt rd (σ (.n 19)) [σ (.n 1867), σ (.n 1883), σ (.n 1891), σ (.n 1899)] ∧
      σ (.n 1897) = σ (.n 5) * gen ^ 7 * gen ^ 6 ∧
      [σ (.n 1900), σ (.n 1901), σ (.n 1902), σ (.n 1903), σ (.n 1904)] =
        [σ (.n 1892), σ (.n 1893), σ (.n 1894), σ (.n 1895), σ (.n 1896)] ∧
      σ (.n 1906) = σ (.n 1905) ∧
      RunsTo (bytecodeShare weights low)
        ((⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorbAll
          [σ (.n 812), σ (.n 816), σ (.n 1302), σ (.n 1316)] dsObserve)
        ([σ (.n 1840), σ (.n 1844), σ (.n 1848)] ++ ys ++ [σ (.n 1905)])
        (σ (.n 1840), low ++ [σ (.n 1867), σ (.n 1883), σ (.n 1891), σ (.n 1899)], σ (.n 1905))
        ((⟨[σ (.n 1892), σ (.n 1893), σ (.n 1894), σ (.n 1895), σ (.n 1896)], []⟩ : Fs).absorb
          (σ (.n 1905)) dsObserve) := by
  obtain ⟨-, hr0, hcap0, d43, d47, d51⟩ := vt_fresh h
  have s0 := h.atomAt 1931 (.load (.n 1867) (.n 19) 0) (by decide +kernel)
  have a1932 := h.atomAt 1932 (.const (.n 1868) (word 1 0)) (by decide +kernel)
  have a1933 := h.atomAt 1933 (.add (.n 1869) (.n 1868) (.n 1867)) (by decide +kernel)
  have a1934 := h.atomAt 1934 (.mul (.n 1870) (.n 1869) (.n 1851)) (by decide +kernel)
  have a1935 := h.atomAt 1935 (.add (.n 1871) (.n 1843) (.n 1870)) (by decide +kernel)
  have a1936 := h.atomAt 1936 (.mul (.n 1872) (.n 1867) (.n 1871)) (by decide +kernel)
  have a1937 := h.atomAt 1937 (.add (.n 1873) (.n 1847) (.n 1872)) (by decide +kernel)
  have a1938 := h.atomAt 1938 (.const (.n 1874) (word 128 0)) (by decide +kernel)
  have a1939 := h.atomAt 1939 (.mul (.n 1875) (.n 5) (.n 1874)) (by decide +kernel)
  have k1 := h.callAt 1940 "opening_tail_round" [.n 1862, .n 1863, .n 1864, .n 1865, .n 1866,
    .n 1875, .n 1873, .n 18] [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880, .n 1881, .n 1882,
    .n 1883] (by decide +kernel)
  have s1 := h.atomAt 1941 (.load (.n 1883) (.n 19) 1) (by decide +kernel)
  have k2 := h.callAt 1942 "opening_tail_round" [.n 1876, .n 1877, .n 1878, .n 1879, .n 1880,
    .n 1881, .n 1882, .n 18] [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890,
    .n 1891] (by decide +kernel)
  have s2 := h.atomAt 1943 (.load (.n 1891) (.n 19) 2) (by decide +kernel)
  have k3 := h.callAt 1944 "opening_tail_round" [.n 1884, .n 1885, .n 1886, .n 1887, .n 1888,
    .n 1889, .n 1890, .n 18] [.n 1892, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897, .n 1898,
    .n 1899] (by decide +kernel)
  have s3 := h.atomAt 1945 (.load (.n 1899) (.n 19) 3) (by decide +kernel)
  have c0 := h.atomAt 1946 (.copy (.n 1900) (.n 1892)) (by decide +kernel)
  have c1 := h.atomAt 1947 (.copy (.n 1901) (.n 1893)) (by decide +kernel)
  have c2 := h.atomAt 1948 (.copy (.n 1902) (.n 1894)) (by decide +kernel)
  have c3 := h.atomAt 1949 (.copy (.n 1903) (.n 1895)) (by decide +kernel)
  have c4 := h.atomAt 1950 (.copy (.n 1904) (.n 1896)) (by decide +kernel)
  have lv := h.atomAt 1951 (.load (.n 1905) (.n 1897) 0) (by decide +kernel)
  have cv := h.atomAt 1952 (.copy (.n 1906) (.n 1905)) (by decide +kernel)
  -- the fold of `fp_w`
  have l0 := h.atomAt 1954 (.load (.n 1908) (.n 19) 0) (by decide +kernel)
  have w0 := h.atomAt 1955 (.load (.n 1909) (.n 13) 0) (by decide +kernel)
  have w1 := h.atomAt 1956 (.load (.n 1910) (.n 13) 1) (by decide +kernel)
  have a1957 := h.atomAt 1957 (.add (.n 1911) (.n 1909) (.n 1910)) (by decide +kernel)
  have a1958 := h.atomAt 1958 (.mul (.n 1912) (.n 1908) (.n 1911)) (by decide +kernel)
  have a1959 := h.atomAt 1959 (.add (.n 1913) (.n 1909) (.n 1912)) (by decide +kernel)
  have w2 := h.atomAt 1960 (.load (.n 1914) (.n 13) 2) (by decide +kernel)
  have w3 := h.atomAt 1961 (.load (.n 1915) (.n 13) 3) (by decide +kernel)
  have a1962 := h.atomAt 1962 (.add (.n 1916) (.n 1914) (.n 1915)) (by decide +kernel)
  have a1963 := h.atomAt 1963 (.mul (.n 1917) (.n 1908) (.n 1916)) (by decide +kernel)
  have a1964 := h.atomAt 1964 (.add (.n 1918) (.n 1914) (.n 1917)) (by decide +kernel)
  have w4 := h.atomAt 1965 (.load (.n 1919) (.n 13) 4) (by decide +kernel)
  have w5 := h.atomAt 1966 (.load (.n 1920) (.n 13) 5) (by decide +kernel)
  have a1967 := h.atomAt 1967 (.add (.n 1921) (.n 1919) (.n 1920)) (by decide +kernel)
  have a1968 := h.atomAt 1968 (.mul (.n 1922) (.n 1908) (.n 1921)) (by decide +kernel)
  have a1969 := h.atomAt 1969 (.add (.n 1923) (.n 1919) (.n 1922)) (by decide +kernel)
  have w6 := h.atomAt 1970 (.load (.n 1924) (.n 13) 6) (by decide +kernel)
  have w7 := h.atomAt 1971 (.load (.n 1925) (.n 13) 7) (by decide +kernel)
  have a1972 := h.atomAt 1972 (.add (.n 1926) (.n 1924) (.n 1925)) (by decide +kernel)
  have a1973 := h.atomAt 1973 (.mul (.n 1927) (.n 1908) (.n 1926)) (by decide +kernel)
  have a1974 := h.atomAt 1974 (.add (.n 1928) (.n 1924) (.n 1927)) (by decide +kernel)
  have w8 := h.atomAt 1975 (.load (.n 1929) (.n 13) 8) (by decide +kernel)
  have w9 := h.atomAt 1976 (.load (.n 1930) (.n 13) 9) (by decide +kernel)
  have a1977 := h.atomAt 1977 (.add (.n 1931) (.n 1929) (.n 1930)) (by decide +kernel)
  have a1978 := h.atomAt 1978 (.mul (.n 1932) (.n 1908) (.n 1931)) (by decide +kernel)
  have a1979 := h.atomAt 1979 (.add (.n 1933) (.n 1929) (.n 1932)) (by decide +kernel)
  have w10 := h.atomAt 1980 (.load (.n 1934) (.n 13) 10) (by decide +kernel)
  have w11 := h.atomAt 1981 (.load (.n 1935) (.n 13) 11) (by decide +kernel)
  have a1982 := h.atomAt 1982 (.add (.n 1936) (.n 1934) (.n 1935)) (by decide +kernel)
  have a1983 := h.atomAt 1983 (.mul (.n 1937) (.n 1908) (.n 1936)) (by decide +kernel)
  have a1984 := h.atomAt 1984 (.add (.n 1938) (.n 1934) (.n 1937)) (by decide +kernel)
  have w12 := h.atomAt 1985 (.load (.n 1939) (.n 13) 12) (by decide +kernel)
  have w13 := h.atomAt 1986 (.load (.n 1940) (.n 13) 13) (by decide +kernel)
  have a1987 := h.atomAt 1987 (.add (.n 1941) (.n 1939) (.n 1940)) (by decide +kernel)
  have a1988 := h.atomAt 1988 (.mul (.n 1942) (.n 1908) (.n 1941)) (by decide +kernel)
  have a1989 := h.atomAt 1989 (.add (.n 1943) (.n 1939) (.n 1942)) (by decide +kernel)
  have w14 := h.atomAt 1990 (.load (.n 1944) (.n 13) 14) (by decide +kernel)
  have w15 := h.atomAt 1991 (.load (.n 1945) (.n 13) 15) (by decide +kernel)
  have a1992 := h.atomAt 1992 (.add (.n 1946) (.n 1944) (.n 1945)) (by decide +kernel)
  have a1993 := h.atomAt 1993 (.mul (.n 1947) (.n 1908) (.n 1946)) (by decide +kernel)
  have a1994 := h.atomAt 1994 (.add (.n 1948) (.n 1944) (.n 1947)) (by decide +kernel)
  have l1 := h.atomAt 1995 (.load (.n 1949) (.n 19) 1) (by decide +kernel)
  have a1996 := h.atomAt 1996 (.add (.n 1950) (.n 1913) (.n 1918)) (by decide +kernel)
  have a1997 := h.atomAt 1997 (.mul (.n 1951) (.n 1949) (.n 1950)) (by decide +kernel)
  have a1998 := h.atomAt 1998 (.add (.n 1952) (.n 1913) (.n 1951)) (by decide +kernel)
  have a1999 := h.atomAt 1999 (.add (.n 1953) (.n 1923) (.n 1928)) (by decide +kernel)
  have a2000 := h.atomAt 2000 (.mul (.n 1954) (.n 1949) (.n 1953)) (by decide +kernel)
  have a2001 := h.atomAt 2001 (.add (.n 1955) (.n 1923) (.n 1954)) (by decide +kernel)
  have a2002 := h.atomAt 2002 (.add (.n 1956) (.n 1933) (.n 1938)) (by decide +kernel)
  have a2003 := h.atomAt 2003 (.mul (.n 1957) (.n 1949) (.n 1956)) (by decide +kernel)
  have a2004 := h.atomAt 2004 (.add (.n 1958) (.n 1933) (.n 1957)) (by decide +kernel)
  have a2005 := h.atomAt 2005 (.add (.n 1959) (.n 1943) (.n 1948)) (by decide +kernel)
  have a2006 := h.atomAt 2006 (.mul (.n 1960) (.n 1949) (.n 1959)) (by decide +kernel)
  have a2007 := h.atomAt 2007 (.add (.n 1961) (.n 1943) (.n 1960)) (by decide +kernel)
  have l2 := h.atomAt 2008 (.load (.n 1962) (.n 19) 2) (by decide +kernel)
  have a2009 := h.atomAt 2009 (.add (.n 1963) (.n 1952) (.n 1955)) (by decide +kernel)
  have a2010 := h.atomAt 2010 (.mul (.n 1964) (.n 1962) (.n 1963)) (by decide +kernel)
  have a2011 := h.atomAt 2011 (.add (.n 1965) (.n 1952) (.n 1964)) (by decide +kernel)
  have a2012 := h.atomAt 2012 (.add (.n 1966) (.n 1958) (.n 1961)) (by decide +kernel)
  have a2013 := h.atomAt 2013 (.mul (.n 1967) (.n 1962) (.n 1966)) (by decide +kernel)
  have a2014 := h.atomAt 2014 (.add (.n 1968) (.n 1958) (.n 1967)) (by decide +kernel)
  have l3 := h.atomAt 2015 (.load (.n 1969) (.n 19) 3) (by decide +kernel)
  have a2016 := h.atomAt 2016 (.add (.n 1970) (.n 1965) (.n 1968)) (by decide +kernel)
  have a2017 := h.atomAt 2017 (.mul (.n 1971) (.n 1969) (.n 1970)) (by decide +kernel)
  have a2018 := h.atomAt 2018 (.add (.n 1972) (.n 1965) (.n 1971)) (by decide +kernel)
  have a2019 := h.atomAt 2019 (.mul (.n 1973) (.n 1972) (.n 1905)) (by decide +kernel)
  have a2020 := h.atomAt 2020 (.assertEq (.n 1898) (.n 1973)) (by decide +kernel)
  simp only [Atom.Holds] at s0 a1932 a1933 a1934 a1935 a1936 a1937 a1938 a1939 s1 s2 s3
  simp only [Atom.Holds] at c0 c1 c2 c3 c4 lv cv l0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12
  simp only [Atom.Holds] at w13 w14 w15 l1 l2 l3 a2020
  simp only [Atom.Holds] at a1957 a1958 a1959 a1962 a1963 a1964 a1967 a1968 a1969 a1972 a1973
  simp only [Atom.Holds] at a1974 a1977 a1978 a1979 a1982 a1983 a1984 a1987 a1988 a1989 a1992
  simp only [Atom.Holds] at a1993 a1994 a1996 a1997 a1998 a1999 a2000 a2001 a2002 a2003 a2004
  simp only [Atom.Holds] at a2005 a2006 a2007 a2009 a2010 a2011 a2012 a2013 a2014 a2016 a2017
  simp only [Atom.Holds] at a2018 a2019
  simp only [List.map_cons, List.map_nil] at k1 k2 k3
  -- the three tail rounds
  obtain ⟨x0, x1, hx01, e1⟩ := vt_otr k1
  obtain ⟨x2, x3, hx23, e2⟩ := vt_otr k2
  obtain ⟨x4, x5, hx45, e3⟩ := vt_otr k3
  obtain ⟨q1, u1, v1, r1⟩ := vt_split8 (by rfl) e1
  obtain ⟨q2, u2, v2, r2⟩ := vt_split8 (by rfl) e2
  obtain ⟨q3, u3, v3, r3⟩ := vt_split8 (by rfl) e3
  -- the sponge before the share, and after its first round
  set F0 : Fs := (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorbAll
    [σ (.n 812), σ (.n 816), σ (.n 1302), σ (.n 1316)] dsObserve with hF0
  have hF : ((F0.absorb (σ (.n 1840)) dsObserve).absorb (σ (.n 1844)) dsObserve).absorbAll
      [σ (.n 1848)] dsObserve = vtFreshFs σ := by
    simp only [hF0, vtFreshFs, vtFreshWords, Fs.absorbAll, List.foldl_cons, List.foldl_nil]
  have hF2 : (vtFreshFs σ).squeeze.2 =
      ⟨[σ (.n 1862), σ (.n 1863), σ (.n 1864), σ (.n 1865), σ (.n 1866)], []⟩ := by
    rw [show (vtFreshFs σ).squeeze.2 = ⟨(vtFreshFs σ).squeeze.2.cap, []⟩ from rfl, ← hcap0]
    rfl
  -- the claims
  have hw128 : σ (.n 1874) = gen ^ 7 := by
    rw [a1938, show (128 : ℕ) = 2 ^ 7 by norm_num, tb_word_two_pow (by norm_num)]
  have hc1 : σ (.n 1873) = σ (.n 1844) + σ (.n 1867) * (σ (.n 1840) + (1 + σ (.n 1867)) *
      σ (.n 1848)) := by
    rw [a1937, a1936, a1935, a1934, a1933, a1932, tb_word_one, d43, d47, d51]
  have hfin : σ (.n 1898) = dot (eqKernel [σ (.n 1867), σ (.n 1883), σ (.n 1891), σ (.n 1899)])
      weights * σ (.n 1905) := by
    have hl0 := tb_loadHolds_unique l0 s0
    have hl1 := tb_loadHolds_unique l1 s1
    have hl2 := tb_loadHolds_unique l2 s2
    have hl3 := tb_loadHolds_unique l3 s3
    have hw : ∀ i (hi : i < 16), LoadHolds rd (σ (.n 13)) i (weights.getD i 0) := fun i hi ↦ by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hW i (by omega)
    have ew := fun {i : ℕ} {v : E} (hi : i < 16) (hv : LoadHolds rd (σ (.n 13)) i v) ↦
      tb_loadHolds_unique hv (hw i hi)
    have e1972 : σ (.n 1972) = multilinearEval ((List.range 16).map fun i ↦ weights.getD i 0)
        [σ (.n 1867), σ (.n 1883), σ (.n 1891), σ (.n 1899)] := by
      rw [a2018, a2017, a2016, a2011, a2010, a2009, a2014, a2013, a2012, a1998, a1997, a1996,
        a2001, a2000, a1999, a2004, a2003, a2002, a2007, a2006, a2005, a1959, a1958, a1957,
        a1964, a1963, a1962, a1969, a1968, a1967, a1974, a1973, a1972, a1979, a1978, a1977,
        a1984, a1983, a1982, a1989, a1988, a1987, a1994, a1993, a1992, hl0, hl1, hl2, hl3,
        ew (by norm_num) w0, ew (by norm_num) w1, ew (by norm_num) w2, ew (by norm_num) w3,
        ew (by norm_num) w4, ew (by norm_num) w5, ew (by norm_num) w6, ew (by norm_num) w7,
        ew (by norm_num) w8, ew (by norm_num) w9, ew (by norm_num) w10, ew (by norm_num) w11,
        ew (by norm_num) w12, ew (by norm_num) w13, ew (by norm_num) w14, ew (by norm_num) w15]
      simp only [multilinearEval, List.range_succ, List.range_zero,
        List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.foldl_cons,
        List.foldl_nil, foldPairs, List.headD_cons]
      ring
    rw [e_add_eq_zero_iff.mp a2020, a2019, e1972, ← vt_list16 weights hwl,
      multilinearEval_eq_dot weights _ hwl rfl]
  -- the run
  have sq : ∀ s : Fs, s.squeeze.2 = ⟨s.squeeze.2.cap, []⟩ := fun s ↦ rfl
  have hR4 := runsTo_sumcheck_nil
    (⟨[σ (.n 1892), σ (.n 1893), σ (.n 1894), σ (.n 1895), σ (.n 1896)], []⟩ : Fs)
    (σ (.n 1898)) 3
  have hR3 := vt_tail_cons [σ (.n 1884), σ (.n 1885), σ (.n 1886), σ (.n 1887), σ (.n 1888)]
    x4 x5 (σ (.n 1890)) (rest := []) (ys := []) (pt := []) (fin := σ (.n 1898))
    (s2 := ⟨[σ (.n 1892), σ (.n 1893), σ (.n 1894), σ (.n 1895), σ (.n 1896)], []⟩)
    (by rw [← v3, sq, ← q3]; exact hR4)
  have hR2 := vt_tail_cons [σ (.n 1876), σ (.n 1877), σ (.n 1878), σ (.n 1879), σ (.n 1880)]
    x2 x3 (σ (.n 1882)) (by rw [← v2, sq, ← q2]; exact hR3)
  have hR1 := vt_tail_cons [σ (.n 1862), σ (.n 1863), σ (.n 1864), σ (.n 1865), σ (.n 1866)]
    x0 x1 (σ (.n 1873)) (by rw [← v1, sq, ← q1]; exact hR2)
  rw [← r1, ← r2, ← r3] at hR1
  have hR0 := runsTo_sumcheck_cons
    (runsTo_roundPolyNone (F0.absorb (σ (.n 1840)) dsObserve) (σ (.n 1840)) (σ (.n 1844))
      [σ (.n 1848)] 3 rfl (by decide))
    (by rw [hF, hF2, ← tail_eval, ← hr0, ← hc1]; exact hR1)
  rw [hF, ← hr0] at hR0
  have hS := runsTo_readE F0 (σ (.n 1840))
  have hv := runsTo_readE
    (⟨[σ (.n 1892), σ (.n 1893), σ (.n 1894), σ (.n 1895), σ (.n 1896)], []⟩ : Fs) (σ (.n 1905))
  have hq := tb_runsTo_require hfin
    ((⟨[σ (.n 1892), σ (.n 1893), σ (.n 1894), σ (.n 1895), σ (.n 1896)], []⟩ : Fs).absorb
      (σ (.n 1905)) dsObserve)
  -- the reads
  have hp1 : σ (.n 1875) = σ (.n 5) * gen ^ 7 := by rw [a1939, hw128]
  have hrd : TbReadsAt rd (σ (.n 5) * gen ^ 7) ([x0, x1] ++ ([x2, x3] ++ ([x4, x5] ++
      [σ (.n 1905)]))) := by
    have r01 : TbReadsAt rd (σ (.n 5) * gen ^ 7) [x0, x1] := fun k hk ↦ by
      have := hx01 k hk; rwa [hp1] at this
    have r23 : TbReadsAt rd (σ (.n 5) * gen ^ 7 * gen ^ 2) [x2, x3] := fun k hk ↦ by
      have := hx23 k hk; rwa [u1, hp1] at this
    have r45 : TbReadsAt rd (σ (.n 5) * gen ^ 7 * gen ^ 2 * gen ^ 2) [x4, x5] := fun k hk ↦ by
      have := hx45 k hk; rwa [u2, u1, hp1] at this
    have rv : TbReadsAt rd (σ (.n 5) * gen ^ 7 * gen ^ 2 * gen ^ 2 * gen ^ 2) [σ (.n 1905)] := by
      rw [tbReadsAt_singleton, ← hp1, ← u1, ← u2, ← u3]; exact lv
    exact tbReadsAt_append.mpr ⟨r01, tbReadsAt_append.mpr ⟨r23, tbReadsAt_append.mpr ⟨r45, rv⟩⟩⟩
  refine ⟨[x0, x1, x2, x3, x4, x5], rfl, by simpa using hrd, ?_, ?_, ?_, cv, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact s0
    · exact s1
    · exact s2
    · exact s3
  · rw [u3, u2, u1, hp1, mul_assoc, mul_assoc, ← pow_add, ← pow_add]
  · rw [c0, c1, c2, c3, c4]
  · rw [show [σ (.n 1840), σ (.n 1844), σ (.n 1848)] ++ [x0, x1, x2, x3, x4, x5] ++ [σ (.n 1905)] =
        [σ (.n 1840)] ++ (([σ (.n 1844), σ (.n 1848)] ++ ([x0, x1] ++ ([x2, x3] ++ ([x4, x5] ++
          [])))) ++ ([σ (.n 1905)] ++ ([] ++ []))) by simp]
    unfold bytecodeShare
    exact hS.bind (hR0.bind (hv.bind (hq.bind (runsTo_ret _ _))))

end
end LeanVM.Guest.B1.Tables
