/-
  LeanVM.Guest.B1.VsC.Oq.LqChecks

  The kernel's facts about each `level_queries` specialization's template.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.VmcA
public import LeanVM.Guest.B1.Whir.LqSound
public import LeanVM.Guest.B1.Whir.OqKey
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.Exact.Atoms

/-!
# `level_queries`' templates, checked

`lqChecks q base folds leaf d cd mu nhs hbits fin`: the forward checker passes on its body, the
body but its return is straight, no atom needs a side condition or is a computed hint, `λ^q`'s
digits are `q`'s, its `opening_queries` entry exists, its cap depth is deployed (`2 ..= 8`) and
below its depth, `1 ≤ q < 2^20`. `lq_checks`: every `lqTable` entry, one `decide +kernel` each.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The facts each `level_queries` specialization's proof reads of its template. -/
def lqChecks (q base folds leaf d cd mu nhs hbits fin : ℕ) : Bool :=
  (chk 6 (lqBody q base folds leaf d cd mu nhs hbits fin)).isSome &&
    (lqBodyA q base folds leaf d cd mu nhs hbits fin).all Stmt.straight &&
    Stmt.atomsAll (fun a => !needsSide a && !isComputed a) (lqBody q base folds leaf d cd mu nhs hbits fin) &&
    decide (digitsVal (osPowDigits q) 1 = q) &&
    (oqEntryK (oqKey base folds leaf (d - cd) mu nhs hbits fin)).isSome &&
    decide (("verify_merkle_cap__L" ++ natStr cd, cd) ∈ merkleCapNames) &&
    decide (cd ≤ d ∧ 1 ≤ q ∧ q < 2 ^ 20 ∧ base ≤ 1)

theorem lq_checks_0 : lqChecks 230 1 6 32 11 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_1 : lqChecks 112 1 6 32 12 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_2 : lqChecks 74 1 6 32 13 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_3 : lqChecks 56 1 6 32 14 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_4 : lqChecks 60 0 4 16 10 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_5 : lqChecks 47 0 4 16 11 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_6 : lqChecks 39 0 4 16 12 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_7 : lqChecks 33 0 4 16 13 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_8 : lqChecks 42 0 4 16 9 3 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_9 : lqChecks 35 0 4 16 10 4 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_10 : lqChecks 30 0 4 16 11 5 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_11 : lqChecks 27 0 4 16 12 6 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_12 : lqChecks 225 1 6 32 12 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_13 : lqChecks 111 1 6 32 13 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_14 : lqChecks 74 1 6 32 14 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_15 : lqChecks 55 1 6 32 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_16 : lqChecks 58 0 4 16 11 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_17 : lqChecks 46 0 4 16 12 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_18 : lqChecks 38 0 4 16 13 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_19 : lqChecks 32 0 4 16 14 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_20 : lqChecks 38 0 4 16 10 4 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_21 : lqChecks 32 0 4 16 11 5 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_22 : lqChecks 28 0 4 16 12 6 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_23 : lqChecks 25 0 4 16 13 7 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_24 : lqChecks 222 1 6 32 13 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_25 : lqChecks 110 1 6 32 14 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_26 : lqChecks 73 1 6 32 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_27 : lqChecks 55 1 6 32 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_28 : lqChecks 57 0 4 16 12 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_29 : lqChecks 45 0 4 16 13 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_30 : lqChecks 37 0 4 16 14 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_31 : lqChecks 32 0 4 16 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_32 : lqChecks 35 0 4 16 11 5 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_33 : lqChecks 31 0 4 16 12 6 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_34 : lqChecks 27 0 4 16 13 7 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_35 : lqChecks 24 0 4 16 14 2 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_36 : lqChecks 220 1 6 32 14 8 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_37 : lqChecks 110 1 6 32 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_38 : lqChecks 73 1 6 32 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_39 : lqChecks 55 1 6 32 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_40 : lqChecks 56 0 4 16 13 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_41 : lqChecks 45 0 4 16 14 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_42 : lqChecks 37 0 4 16 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_43 : lqChecks 32 0 4 16 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_44 : lqChecks 34 0 4 16 12 6 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_45 : lqChecks 29 0 4 16 13 7 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_46 : lqChecks 26 0 4 16 14 2 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_47 : lqChecks 23 0 4 16 15 3 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_48 : lqChecks 219 1 6 32 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_49 : lqChecks 109 1 6 32 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_50 : lqChecks 73 1 6 32 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_51 : lqChecks 55 1 6 32 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_52 : lqChecks 55 0 4 16 14 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_53 : lqChecks 44 0 4 16 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_54 : lqChecks 37 0 4 16 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_55 : lqChecks 32 0 4 16 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_56 : lqChecks 29 0 4 16 14 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_57 : lqChecks 25 0 4 16 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_58 : lqChecks 23 0 4 16 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_59 : lqChecks 24 0 4 16 13 7 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_60 : lqChecks 22 0 4 16 14 2 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_61 : lqChecks 20 0 4 16 15 3 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_62 : lqChecks 218 1 6 32 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_63 : lqChecks 109 1 6 32 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_64 : lqChecks 73 1 6 32 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_65 : lqChecks 55 1 6 32 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_66 : lqChecks 55 0 4 16 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_67 : lqChecks 44 0 4 16 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_68 : lqChecks 37 0 4 16 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_69 : lqChecks 32 0 4 16 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_70 : lqChecks 28 0 4 16 15 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_71 : lqChecks 25 0 4 16 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_72 : lqChecks 23 0 4 16 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_73 : lqChecks 23 0 4 16 14 2 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_74 : lqChecks 20 0 4 16 15 3 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_75 : lqChecks 19 0 4 16 16 4 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_76 : lqChecks 218 1 6 32 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_77 : lqChecks 109 1 6 32 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_78 : lqChecks 73 1 6 32 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_79 : lqChecks 55 1 6 32 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_80 : lqChecks 55 0 4 16 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_81 : lqChecks 44 0 4 16 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_82 : lqChecks 37 0 4 16 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_83 : lqChecks 32 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_84 : lqChecks 28 0 4 16 16 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_85 : lqChecks 25 0 4 16 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_86 : lqChecks 23 0 4 16 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_87 : lqChecks 22 0 4 16 15 3 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_88 : lqChecks 20 0 4 16 16 4 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_89 : lqChecks 18 0 4 16 17 5 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_90 : lqChecks 218 1 6 32 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_91 : lqChecks 109 1 6 32 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_92 : lqChecks 73 1 6 32 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_93 : lqChecks 55 1 6 32 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_94 : lqChecks 55 0 4 16 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_95 : lqChecks 44 0 4 16 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_96 : lqChecks 37 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_97 : lqChecks 32 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_98 : lqChecks 28 0 4 16 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_99 : lqChecks 25 0 4 16 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_100 : lqChecks 23 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_101 : lqChecks 21 0 4 16 16 4 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_102 : lqChecks 19 0 4 16 17 5 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_103 : lqChecks 18 0 4 16 18 6 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_104 : lqChecks 218 1 6 32 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_105 : lqChecks 109 1 6 32 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_106 : lqChecks 73 1 6 32 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_107 : lqChecks 55 1 6 32 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_108 : lqChecks 55 0 4 16 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_109 : lqChecks 44 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_110 : lqChecks 37 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_111 : lqChecks 32 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_112 : lqChecks 28 0 4 16 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_113 : lqChecks 25 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_114 : lqChecks 23 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_115 : lqChecks 21 0 4 16 17 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_116 : lqChecks 19 0 4 16 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_117 : lqChecks 18 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_118 : lqChecks 18 0 4 16 16 4 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_119 : lqChecks 17 0 4 16 17 5 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_120 : lqChecks 16 0 4 16 18 6 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_121 : lqChecks 218 1 6 32 20 8 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_122 : lqChecks 109 1 6 32 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_123 : lqChecks 73 1 6 32 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_124 : lqChecks 55 1 6 32 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_125 : lqChecks 55 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_126 : lqChecks 44 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_127 : lqChecks 37 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_128 : lqChecks 32 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_129 : lqChecks 28 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_130 : lqChecks 25 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_131 : lqChecks 23 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_132 : lqChecks 21 0 4 16 18 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_133 : lqChecks 19 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_134 : lqChecks 18 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_135 : lqChecks 17 0 4 16 17 5 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_136 : lqChecks 16 0 4 16 18 6 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_137 : lqChecks 15 0 4 16 19 7 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_138 : lqChecks 218 1 6 32 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_139 : lqChecks 109 1 6 32 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_140 : lqChecks 73 1 6 32 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_141 : lqChecks 55 1 6 32 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_142 : lqChecks 55 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_143 : lqChecks 44 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_144 : lqChecks 37 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_145 : lqChecks 32 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_146 : lqChecks 28 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_147 : lqChecks 25 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_148 : lqChecks 23 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_149 : lqChecks 21 0 4 16 19 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_150 : lqChecks 19 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_151 : lqChecks 18 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_152 : lqChecks 17 0 4 16 18 6 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_153 : lqChecks 16 0 4 16 19 7 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_154 : lqChecks 15 0 4 16 20 2 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_155 : lqChecks 218 1 6 32 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_156 : lqChecks 109 1 6 32 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_157 : lqChecks 73 1 6 32 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_158 : lqChecks 55 1 6 32 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_159 : lqChecks 55 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_160 : lqChecks 44 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_161 : lqChecks 37 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_162 : lqChecks 32 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_163 : lqChecks 28 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_164 : lqChecks 25 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_165 : lqChecks 23 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_166 : lqChecks 21 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_167 : lqChecks 19 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_168 : lqChecks 18 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_169 : lqChecks 17 0 4 16 19 7 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_170 : lqChecks 16 0 4 16 20 2 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_171 : lqChecks 15 0 4 16 21 3 5 36 6 1 = true := by
  decide +kernel

theorem lq_checks_172 : lqChecks 218 1 6 32 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_173 : lqChecks 109 1 6 32 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_174 : lqChecks 73 1 6 32 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_175 : lqChecks 55 1 6 32 26 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_176 : lqChecks 55 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_177 : lqChecks 44 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_178 : lqChecks 37 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_179 : lqChecks 32 0 4 16 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_180 : lqChecks 28 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_181 : lqChecks 25 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_182 : lqChecks 23 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_183 : lqChecks 21 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_184 : lqChecks 19 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_185 : lqChecks 18 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_186 : lqChecks 17 0 4 16 20 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_187 : lqChecks 16 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_188 : lqChecks 15 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_189 : lqChecks 15 0 4 16 19 7 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_190 : lqChecks 15 0 4 16 20 2 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_191 : lqChecks 14 0 4 16 21 3 2 8 3 1 = true := by
  decide +kernel

theorem lq_checks_192 : lqChecks 218 1 6 32 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_193 : lqChecks 109 1 6 32 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_194 : lqChecks 73 1 6 32 26 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_195 : lqChecks 55 1 6 32 27 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_196 : lqChecks 55 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_197 : lqChecks 44 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_198 : lqChecks 37 0 4 16 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_199 : lqChecks 32 0 4 16 26 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_200 : lqChecks 28 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_201 : lqChecks 25 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_202 : lqChecks 23 0 4 16 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_203 : lqChecks 21 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_204 : lqChecks 19 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_205 : lqChecks 18 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_206 : lqChecks 17 0 4 16 21 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_207 : lqChecks 16 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_208 : lqChecks 16 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_209 : lqChecks 15 0 4 16 20 2 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_210 : lqChecks 14 0 4 16 21 3 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_211 : lqChecks 14 0 4 16 22 4 3 12 4 1 = true := by
  decide +kernel

theorem lq_checks_212 : lqChecks 218 1 6 32 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_213 : lqChecks 109 1 6 32 26 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_214 : lqChecks 73 1 6 32 27 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_215 : lqChecks 55 1 6 32 28 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_216 : lqChecks 55 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_217 : lqChecks 44 0 4 16 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_218 : lqChecks 37 0 4 16 26 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_219 : lqChecks 32 0 4 16 27 3 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_220 : lqChecks 28 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_221 : lqChecks 25 0 4 16 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_222 : lqChecks 23 0 4 16 26 2 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_223 : lqChecks 21 0 4 16 23 5 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_224 : lqChecks 19 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_225 : lqChecks 18 0 4 16 25 7 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_226 : lqChecks 17 0 4 16 22 4 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_227 : lqChecks 16 0 4 16 24 6 0 0 0 0 = true := by
  decide +kernel

theorem lq_checks_228 : lqChecks 15 0 4 16 21 3 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_229 : lqChecks 15 0 4 16 22 4 4 20 5 1 = true := by
  decide +kernel

theorem lq_checks_230 : lqChecks 14 0 4 16 23 5 4 20 5 1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem lq_checks : ∀ e ∈ lqTable, lqChecks e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
    e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 = true :=
  List.forall_mem_cons.2 ⟨lq_checks_0,
  List.forall_mem_cons.2 ⟨lq_checks_1,
  List.forall_mem_cons.2 ⟨lq_checks_2,
  List.forall_mem_cons.2 ⟨lq_checks_3,
  List.forall_mem_cons.2 ⟨lq_checks_4,
  List.forall_mem_cons.2 ⟨lq_checks_5,
  List.forall_mem_cons.2 ⟨lq_checks_6,
  List.forall_mem_cons.2 ⟨lq_checks_7,
  List.forall_mem_cons.2 ⟨lq_checks_8,
  List.forall_mem_cons.2 ⟨lq_checks_9,
  List.forall_mem_cons.2 ⟨lq_checks_10,
  List.forall_mem_cons.2 ⟨lq_checks_11,
  List.forall_mem_cons.2 ⟨lq_checks_12,
  List.forall_mem_cons.2 ⟨lq_checks_13,
  List.forall_mem_cons.2 ⟨lq_checks_14,
  List.forall_mem_cons.2 ⟨lq_checks_15,
  List.forall_mem_cons.2 ⟨lq_checks_16,
  List.forall_mem_cons.2 ⟨lq_checks_17,
  List.forall_mem_cons.2 ⟨lq_checks_18,
  List.forall_mem_cons.2 ⟨lq_checks_19,
  List.forall_mem_cons.2 ⟨lq_checks_20,
  List.forall_mem_cons.2 ⟨lq_checks_21,
  List.forall_mem_cons.2 ⟨lq_checks_22,
  List.forall_mem_cons.2 ⟨lq_checks_23,
  List.forall_mem_cons.2 ⟨lq_checks_24,
  List.forall_mem_cons.2 ⟨lq_checks_25,
  List.forall_mem_cons.2 ⟨lq_checks_26,
  List.forall_mem_cons.2 ⟨lq_checks_27,
  List.forall_mem_cons.2 ⟨lq_checks_28,
  List.forall_mem_cons.2 ⟨lq_checks_29,
  List.forall_mem_cons.2 ⟨lq_checks_30,
  List.forall_mem_cons.2 ⟨lq_checks_31,
  List.forall_mem_cons.2 ⟨lq_checks_32,
  List.forall_mem_cons.2 ⟨lq_checks_33,
  List.forall_mem_cons.2 ⟨lq_checks_34,
  List.forall_mem_cons.2 ⟨lq_checks_35,
  List.forall_mem_cons.2 ⟨lq_checks_36,
  List.forall_mem_cons.2 ⟨lq_checks_37,
  List.forall_mem_cons.2 ⟨lq_checks_38,
  List.forall_mem_cons.2 ⟨lq_checks_39,
  List.forall_mem_cons.2 ⟨lq_checks_40,
  List.forall_mem_cons.2 ⟨lq_checks_41,
  List.forall_mem_cons.2 ⟨lq_checks_42,
  List.forall_mem_cons.2 ⟨lq_checks_43,
  List.forall_mem_cons.2 ⟨lq_checks_44,
  List.forall_mem_cons.2 ⟨lq_checks_45,
  List.forall_mem_cons.2 ⟨lq_checks_46,
  List.forall_mem_cons.2 ⟨lq_checks_47,
  List.forall_mem_cons.2 ⟨lq_checks_48,
  List.forall_mem_cons.2 ⟨lq_checks_49,
  List.forall_mem_cons.2 ⟨lq_checks_50,
  List.forall_mem_cons.2 ⟨lq_checks_51,
  List.forall_mem_cons.2 ⟨lq_checks_52,
  List.forall_mem_cons.2 ⟨lq_checks_53,
  List.forall_mem_cons.2 ⟨lq_checks_54,
  List.forall_mem_cons.2 ⟨lq_checks_55,
  List.forall_mem_cons.2 ⟨lq_checks_56,
  List.forall_mem_cons.2 ⟨lq_checks_57,
  List.forall_mem_cons.2 ⟨lq_checks_58,
  List.forall_mem_cons.2 ⟨lq_checks_59,
  List.forall_mem_cons.2 ⟨lq_checks_60,
  List.forall_mem_cons.2 ⟨lq_checks_61,
  List.forall_mem_cons.2 ⟨lq_checks_62,
  List.forall_mem_cons.2 ⟨lq_checks_63,
  List.forall_mem_cons.2 ⟨lq_checks_64,
  List.forall_mem_cons.2 ⟨lq_checks_65,
  List.forall_mem_cons.2 ⟨lq_checks_66,
  List.forall_mem_cons.2 ⟨lq_checks_67,
  List.forall_mem_cons.2 ⟨lq_checks_68,
  List.forall_mem_cons.2 ⟨lq_checks_69,
  List.forall_mem_cons.2 ⟨lq_checks_70,
  List.forall_mem_cons.2 ⟨lq_checks_71,
  List.forall_mem_cons.2 ⟨lq_checks_72,
  List.forall_mem_cons.2 ⟨lq_checks_73,
  List.forall_mem_cons.2 ⟨lq_checks_74,
  List.forall_mem_cons.2 ⟨lq_checks_75,
  List.forall_mem_cons.2 ⟨lq_checks_76,
  List.forall_mem_cons.2 ⟨lq_checks_77,
  List.forall_mem_cons.2 ⟨lq_checks_78,
  List.forall_mem_cons.2 ⟨lq_checks_79,
  List.forall_mem_cons.2 ⟨lq_checks_80,
  List.forall_mem_cons.2 ⟨lq_checks_81,
  List.forall_mem_cons.2 ⟨lq_checks_82,
  List.forall_mem_cons.2 ⟨lq_checks_83,
  List.forall_mem_cons.2 ⟨lq_checks_84,
  List.forall_mem_cons.2 ⟨lq_checks_85,
  List.forall_mem_cons.2 ⟨lq_checks_86,
  List.forall_mem_cons.2 ⟨lq_checks_87,
  List.forall_mem_cons.2 ⟨lq_checks_88,
  List.forall_mem_cons.2 ⟨lq_checks_89,
  List.forall_mem_cons.2 ⟨lq_checks_90,
  List.forall_mem_cons.2 ⟨lq_checks_91,
  List.forall_mem_cons.2 ⟨lq_checks_92,
  List.forall_mem_cons.2 ⟨lq_checks_93,
  List.forall_mem_cons.2 ⟨lq_checks_94,
  List.forall_mem_cons.2 ⟨lq_checks_95,
  List.forall_mem_cons.2 ⟨lq_checks_96,
  List.forall_mem_cons.2 ⟨lq_checks_97,
  List.forall_mem_cons.2 ⟨lq_checks_98,
  List.forall_mem_cons.2 ⟨lq_checks_99,
  List.forall_mem_cons.2 ⟨lq_checks_100,
  List.forall_mem_cons.2 ⟨lq_checks_101,
  List.forall_mem_cons.2 ⟨lq_checks_102,
  List.forall_mem_cons.2 ⟨lq_checks_103,
  List.forall_mem_cons.2 ⟨lq_checks_104,
  List.forall_mem_cons.2 ⟨lq_checks_105,
  List.forall_mem_cons.2 ⟨lq_checks_106,
  List.forall_mem_cons.2 ⟨lq_checks_107,
  List.forall_mem_cons.2 ⟨lq_checks_108,
  List.forall_mem_cons.2 ⟨lq_checks_109,
  List.forall_mem_cons.2 ⟨lq_checks_110,
  List.forall_mem_cons.2 ⟨lq_checks_111,
  List.forall_mem_cons.2 ⟨lq_checks_112,
  List.forall_mem_cons.2 ⟨lq_checks_113,
  List.forall_mem_cons.2 ⟨lq_checks_114,
  List.forall_mem_cons.2 ⟨lq_checks_115,
  List.forall_mem_cons.2 ⟨lq_checks_116,
  List.forall_mem_cons.2 ⟨lq_checks_117,
  List.forall_mem_cons.2 ⟨lq_checks_118,
  List.forall_mem_cons.2 ⟨lq_checks_119,
  List.forall_mem_cons.2 ⟨lq_checks_120,
  List.forall_mem_cons.2 ⟨lq_checks_121,
  List.forall_mem_cons.2 ⟨lq_checks_122,
  List.forall_mem_cons.2 ⟨lq_checks_123,
  List.forall_mem_cons.2 ⟨lq_checks_124,
  List.forall_mem_cons.2 ⟨lq_checks_125,
  List.forall_mem_cons.2 ⟨lq_checks_126,
  List.forall_mem_cons.2 ⟨lq_checks_127,
  List.forall_mem_cons.2 ⟨lq_checks_128,
  List.forall_mem_cons.2 ⟨lq_checks_129,
  List.forall_mem_cons.2 ⟨lq_checks_130,
  List.forall_mem_cons.2 ⟨lq_checks_131,
  List.forall_mem_cons.2 ⟨lq_checks_132,
  List.forall_mem_cons.2 ⟨lq_checks_133,
  List.forall_mem_cons.2 ⟨lq_checks_134,
  List.forall_mem_cons.2 ⟨lq_checks_135,
  List.forall_mem_cons.2 ⟨lq_checks_136,
  List.forall_mem_cons.2 ⟨lq_checks_137,
  List.forall_mem_cons.2 ⟨lq_checks_138,
  List.forall_mem_cons.2 ⟨lq_checks_139,
  List.forall_mem_cons.2 ⟨lq_checks_140,
  List.forall_mem_cons.2 ⟨lq_checks_141,
  List.forall_mem_cons.2 ⟨lq_checks_142,
  List.forall_mem_cons.2 ⟨lq_checks_143,
  List.forall_mem_cons.2 ⟨lq_checks_144,
  List.forall_mem_cons.2 ⟨lq_checks_145,
  List.forall_mem_cons.2 ⟨lq_checks_146,
  List.forall_mem_cons.2 ⟨lq_checks_147,
  List.forall_mem_cons.2 ⟨lq_checks_148,
  List.forall_mem_cons.2 ⟨lq_checks_149,
  List.forall_mem_cons.2 ⟨lq_checks_150,
  List.forall_mem_cons.2 ⟨lq_checks_151,
  List.forall_mem_cons.2 ⟨lq_checks_152,
  List.forall_mem_cons.2 ⟨lq_checks_153,
  List.forall_mem_cons.2 ⟨lq_checks_154,
  List.forall_mem_cons.2 ⟨lq_checks_155,
  List.forall_mem_cons.2 ⟨lq_checks_156,
  List.forall_mem_cons.2 ⟨lq_checks_157,
  List.forall_mem_cons.2 ⟨lq_checks_158,
  List.forall_mem_cons.2 ⟨lq_checks_159,
  List.forall_mem_cons.2 ⟨lq_checks_160,
  List.forall_mem_cons.2 ⟨lq_checks_161,
  List.forall_mem_cons.2 ⟨lq_checks_162,
  List.forall_mem_cons.2 ⟨lq_checks_163,
  List.forall_mem_cons.2 ⟨lq_checks_164,
  List.forall_mem_cons.2 ⟨lq_checks_165,
  List.forall_mem_cons.2 ⟨lq_checks_166,
  List.forall_mem_cons.2 ⟨lq_checks_167,
  List.forall_mem_cons.2 ⟨lq_checks_168,
  List.forall_mem_cons.2 ⟨lq_checks_169,
  List.forall_mem_cons.2 ⟨lq_checks_170,
  List.forall_mem_cons.2 ⟨lq_checks_171,
  List.forall_mem_cons.2 ⟨lq_checks_172,
  List.forall_mem_cons.2 ⟨lq_checks_173,
  List.forall_mem_cons.2 ⟨lq_checks_174,
  List.forall_mem_cons.2 ⟨lq_checks_175,
  List.forall_mem_cons.2 ⟨lq_checks_176,
  List.forall_mem_cons.2 ⟨lq_checks_177,
  List.forall_mem_cons.2 ⟨lq_checks_178,
  List.forall_mem_cons.2 ⟨lq_checks_179,
  List.forall_mem_cons.2 ⟨lq_checks_180,
  List.forall_mem_cons.2 ⟨lq_checks_181,
  List.forall_mem_cons.2 ⟨lq_checks_182,
  List.forall_mem_cons.2 ⟨lq_checks_183,
  List.forall_mem_cons.2 ⟨lq_checks_184,
  List.forall_mem_cons.2 ⟨lq_checks_185,
  List.forall_mem_cons.2 ⟨lq_checks_186,
  List.forall_mem_cons.2 ⟨lq_checks_187,
  List.forall_mem_cons.2 ⟨lq_checks_188,
  List.forall_mem_cons.2 ⟨lq_checks_189,
  List.forall_mem_cons.2 ⟨lq_checks_190,
  List.forall_mem_cons.2 ⟨lq_checks_191,
  List.forall_mem_cons.2 ⟨lq_checks_192,
  List.forall_mem_cons.2 ⟨lq_checks_193,
  List.forall_mem_cons.2 ⟨lq_checks_194,
  List.forall_mem_cons.2 ⟨lq_checks_195,
  List.forall_mem_cons.2 ⟨lq_checks_196,
  List.forall_mem_cons.2 ⟨lq_checks_197,
  List.forall_mem_cons.2 ⟨lq_checks_198,
  List.forall_mem_cons.2 ⟨lq_checks_199,
  List.forall_mem_cons.2 ⟨lq_checks_200,
  List.forall_mem_cons.2 ⟨lq_checks_201,
  List.forall_mem_cons.2 ⟨lq_checks_202,
  List.forall_mem_cons.2 ⟨lq_checks_203,
  List.forall_mem_cons.2 ⟨lq_checks_204,
  List.forall_mem_cons.2 ⟨lq_checks_205,
  List.forall_mem_cons.2 ⟨lq_checks_206,
  List.forall_mem_cons.2 ⟨lq_checks_207,
  List.forall_mem_cons.2 ⟨lq_checks_208,
  List.forall_mem_cons.2 ⟨lq_checks_209,
  List.forall_mem_cons.2 ⟨lq_checks_210,
  List.forall_mem_cons.2 ⟨lq_checks_211,
  List.forall_mem_cons.2 ⟨lq_checks_212,
  List.forall_mem_cons.2 ⟨lq_checks_213,
  List.forall_mem_cons.2 ⟨lq_checks_214,
  List.forall_mem_cons.2 ⟨lq_checks_215,
  List.forall_mem_cons.2 ⟨lq_checks_216,
  List.forall_mem_cons.2 ⟨lq_checks_217,
  List.forall_mem_cons.2 ⟨lq_checks_218,
  List.forall_mem_cons.2 ⟨lq_checks_219,
  List.forall_mem_cons.2 ⟨lq_checks_220,
  List.forall_mem_cons.2 ⟨lq_checks_221,
  List.forall_mem_cons.2 ⟨lq_checks_222,
  List.forall_mem_cons.2 ⟨lq_checks_223,
  List.forall_mem_cons.2 ⟨lq_checks_224,
  List.forall_mem_cons.2 ⟨lq_checks_225,
  List.forall_mem_cons.2 ⟨lq_checks_226,
  List.forall_mem_cons.2 ⟨lq_checks_227,
  List.forall_mem_cons.2 ⟨lq_checks_228,
  List.forall_mem_cons.2 ⟨lq_checks_229,
  List.forall_mem_cons.2 ⟨lq_checks_230,
  List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end
end LeanVM.Guest.B1.VsC
