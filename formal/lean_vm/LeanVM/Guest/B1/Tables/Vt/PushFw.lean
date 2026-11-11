/-
  LeanVM.Guest.B1.Tables.Vt.PushFw

  `verify_tables`' push side's framework blocks: their fingerprints' accumulator and the
  bytecode share's public term.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.PushPad

/-!
# The push side's framework blocks (G:2517-2530)

`vt_push_fw`: the accumulator after the state, memory and bytecode blocks is
`Σ_f eq_f·(β + Σ_i w_i·coord_i)`, the bytecode block's public slots left out, plus
`public_eq·S`. The framework blocks' coordinate values are the first loop's (`coord_vals`): constants, the index
extensions and the stream words.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vt_word4 : word 4 0 = gen ^ 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)]

set_option maxRecDepth 100000 in
/-- **The push side's framework accumulator.** -/
theorem vt_push_fw {rd : Reader} {σ : Val} (h : VtH rd σ) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (W i)) :
    σ (.n 2015) = σ (.n 790) * (σ (.n 14) + (W 0 + W 1 + W 2)) +
      σ (.n 807) * (σ (.n 14) + (W 0 * gen + W 1 * σ (.n 810) + W 2 + W 3 * σ (.n 815) +
        W 4 * σ (.n 819))) +
      σ (.n 835) * (σ (.n 14) + (W 0 * gen ^ 2 + W 1 * σ (.n 838) + W 2)) +
      σ (.n 1293) * σ (.n 1843) := by
  have a778 := h.atomAt 778 (.const (.n 791) (word 1 0)) (by decide +kernel)
  have a779 := h.atomAt 779 (.const (.n 792) (word 1 0)) (by decide +kernel)
  have a780 := h.atomAt 780 (.const (.n 793) (word 1 0)) (by decide +kernel)
  have a794 := h.atomAt 794 (.const (.n 808) (word 2 0)) (by decide +kernel)
  have a798 := h.atomAt 798 (.const (.n 811) (word 1 0)) (by decide +kernel)
  have a824 := h.atomAt 824 (.const (.n 836) (word 4 0)) (by decide +kernel)
  have a828 := h.atomAt 828 (.const (.n 839) (word 1 0)) (by decide +kernel)
  have a2023 := h.atomAt 2023 (.load (.n 1976) (.n 13) 0) (by decide +kernel)
  have e2023 := tb_loadHolds_unique a2023 (hw 0 (by norm_num))
  have a2024 := h.atomAt 2024 (.mul (.n 1977) (.n 1976) (.n 791)) (by decide +kernel)
  have a2025 := h.atomAt 2025 (.load (.n 1978) (.n 13) 1) (by decide +kernel)
  have e2025 := tb_loadHolds_unique a2025 (hw 1 (by norm_num))
  have a2026 := h.atomAt 2026 (.mul (.n 1979) (.n 1978) (.n 792)) (by decide +kernel)
  have a2027 := h.atomAt 2027 (.add (.n 1980) (.n 1977) (.n 1979)) (by decide +kernel)
  have a2028 := h.atomAt 2028 (.load (.n 1981) (.n 13) 2) (by decide +kernel)
  have e2028 := tb_loadHolds_unique a2028 (hw 2 (by norm_num))
  have a2029 := h.atomAt 2029 (.mul (.n 1982) (.n 1981) (.n 793)) (by decide +kernel)
  have a2030 := h.atomAt 2030 (.add (.n 1983) (.n 1980) (.n 1982)) (by decide +kernel)
  have a2031 := h.atomAt 2031 (.add (.n 1984) (.n 14) (.n 1983)) (by decide +kernel)
  have a2032 := h.atomAt 2032 (.mul (.n 1985) (.n 790) (.n 1984)) (by decide +kernel)
  have a2033 := h.atomAt 2033 (.load (.n 1986) (.n 13) 0) (by decide +kernel)
  have e2033 := tb_loadHolds_unique a2033 (hw 0 (by norm_num))
  have a2034 := h.atomAt 2034 (.mul (.n 1987) (.n 1986) (.n 808)) (by decide +kernel)
  have a2035 := h.atomAt 2035 (.load (.n 1988) (.n 13) 1) (by decide +kernel)
  have e2035 := tb_loadHolds_unique a2035 (hw 1 (by norm_num))
  have a2036 := h.atomAt 2036 (.mul (.n 1989) (.n 1988) (.n 810)) (by decide +kernel)
  have a2037 := h.atomAt 2037 (.add (.n 1990) (.n 1987) (.n 1989)) (by decide +kernel)
  have a2038 := h.atomAt 2038 (.load (.n 1991) (.n 13) 2) (by decide +kernel)
  have e2038 := tb_loadHolds_unique a2038 (hw 2 (by norm_num))
  have a2039 := h.atomAt 2039 (.mul (.n 1992) (.n 1991) (.n 811)) (by decide +kernel)
  have a2040 := h.atomAt 2040 (.add (.n 1993) (.n 1990) (.n 1992)) (by decide +kernel)
  have a2041 := h.atomAt 2041 (.load (.n 1994) (.n 13) 3) (by decide +kernel)
  have e2041 := tb_loadHolds_unique a2041 (hw 3 (by norm_num))
  have a2042 := h.atomAt 2042 (.mul (.n 1995) (.n 1994) (.n 815)) (by decide +kernel)
  have a2043 := h.atomAt 2043 (.add (.n 1996) (.n 1993) (.n 1995)) (by decide +kernel)
  have a2044 := h.atomAt 2044 (.load (.n 1997) (.n 13) 4) (by decide +kernel)
  have e2044 := tb_loadHolds_unique a2044 (hw 4 (by norm_num))
  have a2045 := h.atomAt 2045 (.mul (.n 1998) (.n 1997) (.n 819)) (by decide +kernel)
  have a2046 := h.atomAt 2046 (.add (.n 1999) (.n 1996) (.n 1998)) (by decide +kernel)
  have a2047 := h.atomAt 2047 (.add (.n 2000) (.n 14) (.n 1999)) (by decide +kernel)
  have a2048 := h.atomAt 2048 (.mul (.n 2001) (.n 807) (.n 2000)) (by decide +kernel)
  have a2049 := h.atomAt 2049 (.add (.n 2002) (.n 1985) (.n 2001)) (by decide +kernel)
  have a2050 := h.atomAt 2050 (.load (.n 2003) (.n 13) 0) (by decide +kernel)
  have e2050 := tb_loadHolds_unique a2050 (hw 0 (by norm_num))
  have a2051 := h.atomAt 2051 (.mul (.n 2004) (.n 2003) (.n 836)) (by decide +kernel)
  have a2052 := h.atomAt 2052 (.load (.n 2005) (.n 13) 1) (by decide +kernel)
  have e2052 := tb_loadHolds_unique a2052 (hw 1 (by norm_num))
  have a2053 := h.atomAt 2053 (.mul (.n 2006) (.n 2005) (.n 838)) (by decide +kernel)
  have a2054 := h.atomAt 2054 (.add (.n 2007) (.n 2004) (.n 2006)) (by decide +kernel)
  have a2055 := h.atomAt 2055 (.load (.n 2008) (.n 13) 2) (by decide +kernel)
  have e2055 := tb_loadHolds_unique a2055 (hw 2 (by norm_num))
  have a2056 := h.atomAt 2056 (.mul (.n 2009) (.n 2008) (.n 839)) (by decide +kernel)
  have a2057 := h.atomAt 2057 (.add (.n 2010) (.n 2007) (.n 2009)) (by decide +kernel)
  have a2058 := h.atomAt 2058 (.add (.n 2011) (.n 14) (.n 2010)) (by decide +kernel)
  have a2059 := h.atomAt 2059 (.mul (.n 2012) (.n 835) (.n 2011)) (by decide +kernel)
  have a2060 := h.atomAt 2060 (.add (.n 2013) (.n 2002) (.n 2012)) (by decide +kernel)
  have a2061 := h.atomAt 2061 (.mul (.n 2014) (.n 1293) (.n 1843)) (by decide +kernel)
  have a2062 := h.atomAt 2062 (.add (.n 2015) (.n 2013) (.n 2014)) (by decide +kernel)
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

end
end LeanVM.Guest.B1.Tables
