/-
  LeanVM.Guest.B1.Tables.VtC.AGlue

  What the honest valuation's equations give between `verify_tables`' ranges: the sponge after
  the framework words, `ξ`'s powers, the pull side's selectors.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup
public import LeanVM.Guest.B1.Tables.VtC.FFinal
public import LeanVM.Guest.B1.Tables.Vt.Fresh
public import LeanVM.Guest.B1.Tables.VtC.FData

/-!
# Between the ranges

`pack_good`: an `fs_pack` template whose hint is the honest one (the word's limbs) packs the
word's two rate cells, both canonical. `vt_fresh_good`: the sponge after the five framework words
is the five capacity cells the first permutation writes and the last word waiting, its rate cells
`σ1897`, `σ1899`, all canonical. `vt_xi_good`: `ξ`'s powers. `vt_pull_good`: the pull side's
selectors are the push side's.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- **An honest `fs_pack`** packs the word's rate cells, canonical. -/
theorem pack_good {σ : Val} {x : V} {b t : ℕ}
    (hl : σ (.n (b + 2)) = limbAt (σ x) 2) (h3 : σ (.n (b + 3)) = word t 0 0)
    (h4 : σ (.n (b + 4)) = word 0 0 1)
    (h5 : σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n (b + 2)))
    (h6 : σ (.n (b + 6)) = σ x + σ (.n (b + 5))) (h7 : σ (.n (b + 7)) = word 0 t 0)
    (h8 : σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7))) :
    σ (.n (b + 6)) = (Keccak.scalarCells (σ x) t).1 ∧
      σ (.n (b + 8)) = (Keccak.scalarCells (σ x) t).2 ∧
      IsCanonical128 (σ (.n (b + 6))) ∧ IsCanonical128 (σ (.n (b + 8))) := by
  have hl' : σ (.n (b + 2)) = ofK ((σ x).limb 2) := by rw [hl]; rfl
  have hok : FsPackOk σ x b t := ⟨h3, by rw [hl']; exact ofK_isInK _,
    by rw [h3, word_eOfNat]; exact eOfNat_isInK _, h4, h5, h6, h7, h8⟩
  have hcan : IsCanonical128 (σ (.n (b + 6))) := by
    rw [h6, h5, h4, hl', word_yy, top_pin_eq]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have e := Prod.ext_iff.mp (fsPackT_cells hok hcan)
  obtain ⟨c1, c2⟩ := scalarCells_canonical (σ x) t
  have e1 : σ (.n (b + 6)) = (Keccak.scalarCells (σ x) t).1 := e.1
  have e2 : σ (.n (b + 8)) = (Keccak.scalarCells (σ x) t).2 := e.2
  exact ⟨e1, e2, by rw [e1]; exact c1, by rw [e2]; exact c2⟩

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **A framework word's `fs_next`, honestly**: its two rate cells, canonical. -/
theorem vt_next_good (hl : args.length = 20) (cur : V) (pos k b : ℕ)
    (heq : tbStmtsEqb (fsNextT cur k b) ((vtPre.drop pos).take (fsNextT cur k b).length) =
      true) :
    vtσ rd w args (.n (b + 7)) = (Keccak.scalarCells (vtσ rd w args (.n b)) dsObserve).1 ∧
      vtσ rd w args (.n (b + 9)) = (Keccak.scalarCells (vtσ rd w args (.n b)) dsObserve).2 ∧
      IsCanonical128 (vtσ rd w args (.n (b + 7))) ∧ IsCanonical128 (vtσ rd w args (.n (b + 9))) := by
  have g := vt_goodL (rd := rd) (w := w) hl pos _ heq
  generalize vtσ rd w args = σ at g ⊢
  simp only [fsNextT, fsPackT, GoodL, GoodS, fixNe, Good, List.length_cons, List.length_nil,
    and_true] at g
  obtain ⟨-, gl, g3, -, g4, g5, g6, g7, g8⟩ := g
  have hl2 : σ (.n (b + 1 + 2)) = limbAt (σ (.n b)) 2 := gl 2 (by norm_num)
  have h5 : σ (.n (b + 1 + 5)) = σ (.n (b + 1 + 4)) * σ (.n (b + 1 + 2)) := by
    split_ifs at g5 with hc
    · exact g5
    · exact absurd ⟨by omega, by omega⟩ hc
  have := pack_good (σ := σ) (x := .n b) (b := b + 1) (t := dsObserve) hl2 g3 g4 h5 g6 g7 g8
  rwa [show b + 1 + 6 = b + 7 by omega, show b + 1 + 8 = b + 9 by omega] at this

theorem canon_zero' : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

theorem good_keccak_cells {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {ins : List V}
    {b : ℕ} (h : Good rd S w σ (.keccak ins (lyOuts b) false false)) :
    ∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
  obtain ⟨-, -, hc⟩ := good_keccak13 h (by simp [lyOuts])
  intro k hk
  have := hc ⟨k, hk⟩
  simpa [cells13, lyOuts, List.getD_eq_getElem?_getD, hk, permOf] using this

set_option maxRecDepth 10000 in
/-- **The sponge after the framework words**, honestly: the first permutation's capacity and the
last word waiting, its rate cells canonical, the capacity canonical. -/
theorem vt_fresh_good (hl : args.length = 20) :
    vtFreshFs (vtσ rd w args) = ⟨(lyCap 1885).map (vtσ rd w args),
        [(vtσ rd w args (.n 1898), dsObserve)]⟩ ∧
      rateOf [(vtσ rd w args (.n 1898), dsObserve)] =
        [vtσ rd w args (.n 1905), vtσ rd w args (.n 1907), 0, 0, 0, 0, 0, 0] ∧
      AllCanonical ([vtσ rd w args (.n 1905), vtσ rd w args (.n 1907), 0, 0, 0, 0, 0, 0] ++
        (lyCap 1885).map (vtσ rd w args)) := by
  have p0 := vt_next_good (rd := rd) (w := w) hl (.n 5) 817 0 830 (by rw [vtPre_drop]; decide +kernel)
  have p1 := vt_next_good (rd := rd) (w := w) hl (.n 5) 830 1 843 (by rw [vtPre_drop]; decide +kernel)
  have p2 := vt_next_good (rd := rd) (w := w) hl (.n 5) 843 2 856 (by rw [vtPre_drop]; decide +kernel)
  have p3 := vt_next_good (rd := rd) (w := w) hl (.n 5) 1881 3 1843 (by rw [vtPre_drop]; decide +kernel)
  have p4 := vt_next_good (rd := rd) (w := w) hl (.n 5) 1924 4 1898 (by rw [vtPre_drop]; decide +kernel)
  have gc := vt_goodL (rd := rd) (w := w) hl 0 [.atom (.copy (.n 20) (.n 0)),
    .atom (.copy (.n 21) (.n 1)), .atom (.copy (.n 22) (.n 2)), .atom (.copy (.n 23) (.n 3)),
    .atom (.copy (.n 24) (.n 4))] (by rw [vtPre_drop]; decide +kernel)
  have gk := (vt_goodL (rd := rd) (w := w) hl 1923 [.atom (.keccak [.n 837, .n 839, .n 850,
    .n 852, .n 863, .n 865, .n 1850, .n 1852, .n 20, .n 21, .n 22, .n 23, .n 24] (lyOuts 1885)
    false false)] (by rw [vtPre_drop]; decide +kernel)).1
  generalize vtσ rd w args = σ at p0 p1 p2 p3 p4 gc gk ⊢
  simp only [GoodL, GoodS, fixNe, Good, and_true] at gc
  obtain ⟨c20, c21, c22, c23, c24⟩ := gc
  have hk := good_keccak_cells (rd := rd) (S := vtSL) (w := w) gk
  simp only [Nat.reduceAdd] at p0 p1 p2 p3 p4
  set S4 : Fs := ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 830), dsObserve),
    (σ (.n 843), dsObserve), (σ (.n 856), dsObserve), (σ (.n 1843), dsObserve)]⟩ with hS4d
  have hS4 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorbAll
      [σ (.n 830), σ (.n 843), σ (.n 856), σ (.n 1843)] dsObserve = S4 := by
    rw [absorbAll_short _ _ _ (by simp)]; rfl
  have hin1 : ([.n 837, .n 839, .n 850, .n 852, .n 863, .n 865, .n 1850, .n 1852, .n 20,
      .n 21, .n 22, .n 23, .n 24] : List V).map σ = rateOf S4.pend ++ S4.cap := by
    rw [rateOf_eq_cells _ (by simp [hS4d])]
    simp only [hS4d, List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      p0.1, p0.2.1, p1.1, p1.2.1, p2.1, p2.2.1, p3.1, p3.2.1, c20, c21, c22, c23, c24]
    rfl
  rw [hin1] at hk
  have hcap : (lyCap 1885).map σ = capOf S4.perm := by
    have e : (lyCap 1885).map σ =
        [σ (.n 1893), σ (.n 1894), σ (.n 1895), σ (.n 1896), σ (.n 1897)] := rfl
    have h8 : σ (.n 1893) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 8 :=
      hk 8 (by norm_num)
    have h9 : σ (.n 1894) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 9 :=
      hk 9 (by norm_num)
    have h10 : σ (.n 1895) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 10 :=
      hk 10 (by norm_num)
    have h11 : σ (.n 1896) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 11 :=
      hk 11 (by norm_num)
    have h12 : σ (.n 1897) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 12 :=
      hk 12 (by norm_num)
    rw [e, h8, h9, h10, h11, h12]
    rfl
  have hS5 : vtFreshFs σ = ⟨(lyCap 1885).map σ, [(σ (.n 1898), dsObserve)]⟩ := by
    have hsplit : vtFreshWords σ = [σ (.n 830), σ (.n 843), σ (.n 856), σ (.n 1843)] ++
        [σ (.n 1898)] := rfl
    rw [vtFreshFs, hsplit, vt_absorbAll_append, hS4, hcap]
    simp [Fs.absorbAll, Fs.absorb, rateScalars, hS4d]
  have hr : rateOf [(σ (.n 1898), dsObserve)] =
      [σ (.n 1905), σ (.n 1907), 0, 0, 0, 0, 0, 0] := by
    rw [rateOf_eq_cells _ (by simp)]
    simp [pendCells, p4.1, p4.2.1]
  refine ⟨hS5, hr, ?_⟩
  intro c hc
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hc
  · exact p4.2.2.1
  · exact p4.2.2.2
  all_goals try exact canon_zero'
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
  simp only [lyCap, List.mem_map, List.mem_range] at hv
  obtain ⟨k, hk5, rfl⟩ := hv
  have := hk (8 + k) (by omega)
  rw [show 1885 + 8 + k = 1885 + (8 + k) by omega, this]
  exact canon_cellsOfState _ _ _

set_option maxRecDepth 10000 in
/-- **The pull side's selectors are the push side's**, honestly. -/
theorem vt_pull_good (hl : args.length = 20) : VtPullSelsH (vtσ rd w args) := by
  have g1978 := (vt_goodL (rd := rd) (w := w) hl 1994 [.atom (.copy (.n 1968) (.n 960))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1980 := (vt_goodL (rd := rd) (w := w) hl 1996 [.atom (.copy (.n 1970) (.n 965))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1982 := (vt_goodL (rd := rd) (w := w) hl 1998 [.atom (.copy (.n 1972) (.n 970))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1984 := (vt_goodL (rd := rd) (w := w) hl 2000 [.atom (.copy (.n 1974) (.n 975))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1986 := (vt_goodL (rd := rd) (w := w) hl 2002 [.atom (.copy (.n 1976) (.n 980))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1988 := (vt_goodL (rd := rd) (w := w) hl 2004 [.atom (.copy (.n 1978) (.n 989))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1990 := (vt_goodL (rd := rd) (w := w) hl 2006 [.atom (.copy (.n 1980) (.n 998))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1992 := (vt_goodL (rd := rd) (w := w) hl 2008 [.atom (.copy (.n 1982) (.n 1007))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1994 := (vt_goodL (rd := rd) (w := w) hl 2010 [.atom (.copy (.n 1984) (.n 1016))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1996 := (vt_goodL (rd := rd) (w := w) hl 2012 [.atom (.copy (.n 1986) (.n 1025))] (by rw [vtPre_drop]; decide +kernel)).1
  have g1998 := (vt_goodL (rd := rd) (w := w) hl 2014 [.atom (.copy (.n 1988) (.n 1034))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2000 := (vt_goodL (rd := rd) (w := w) hl 2016 [.atom (.copy (.n 1990) (.n 1043))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2002 := (vt_goodL (rd := rd) (w := w) hl 2018 [.atom (.copy (.n 1992) (.n 1052))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2004 := (vt_goodL (rd := rd) (w := w) hl 2020 [.atom (.copy (.n 1994) (.n 1061))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2006 := (vt_goodL (rd := rd) (w := w) hl 2022 [.atom (.copy (.n 1996) (.n 1070))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2008 := (vt_goodL (rd := rd) (w := w) hl 2024 [.atom (.copy (.n 1998) (.n 1079))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2010 := (vt_goodL (rd := rd) (w := w) hl 2026 [.atom (.copy (.n 2000) (.n 1088))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2012 := (vt_goodL (rd := rd) (w := w) hl 2028 [.atom (.copy (.n 2002) (.n 1097))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2014 := (vt_goodL (rd := rd) (w := w) hl 2030 [.atom (.copy (.n 2004) (.n 1106))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2016 := (vt_goodL (rd := rd) (w := w) hl 2032 [.atom (.copy (.n 2006) (.n 1115))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2018 := (vt_goodL (rd := rd) (w := w) hl 2034 [.atom (.copy (.n 2008) (.n 1124))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2020 := (vt_goodL (rd := rd) (w := w) hl 2036 [.atom (.copy (.n 2010) (.n 1133))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2022 := (vt_goodL (rd := rd) (w := w) hl 2038 [.atom (.copy (.n 2012) (.n 1142))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2024 := (vt_goodL (rd := rd) (w := w) hl 2040 [.atom (.copy (.n 2014) (.n 1151))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2026 := (vt_goodL (rd := rd) (w := w) hl 2042 [.atom (.copy (.n 2016) (.n 1160))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2028 := (vt_goodL (rd := rd) (w := w) hl 2044 [.atom (.copy (.n 2018) (.n 1169))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2030 := (vt_goodL (rd := rd) (w := w) hl 2046 [.atom (.copy (.n 2020) (.n 1178))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2032 := (vt_goodL (rd := rd) (w := w) hl 2048 [.atom (.copy (.n 2022) (.n 1187))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2034 := (vt_goodL (rd := rd) (w := w) hl 2050 [.atom (.copy (.n 2024) (.n 1196))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2036 := (vt_goodL (rd := rd) (w := w) hl 2052 [.atom (.copy (.n 2026) (.n 1205))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2038 := (vt_goodL (rd := rd) (w := w) hl 2054 [.atom (.copy (.n 2028) (.n 1214))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2040 := (vt_goodL (rd := rd) (w := w) hl 2056 [.atom (.copy (.n 2030) (.n 1223))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2042 := (vt_goodL (rd := rd) (w := w) hl 2058 [.atom (.copy (.n 2032) (.n 1232))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2044 := (vt_goodL (rd := rd) (w := w) hl 2060 [.atom (.copy (.n 2034) (.n 1241))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2046 := (vt_goodL (rd := rd) (w := w) hl 2062 [.atom (.copy (.n 2036) (.n 1250))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2048 := (vt_goodL (rd := rd) (w := w) hl 2064 [.atom (.copy (.n 2038) (.n 1259))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2050 := (vt_goodL (rd := rd) (w := w) hl 2066 [.atom (.copy (.n 2040) (.n 1268))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2052 := (vt_goodL (rd := rd) (w := w) hl 2068 [.atom (.copy (.n 2042) (.n 1277))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2054 := (vt_goodL (rd := rd) (w := w) hl 2070 [.atom (.copy (.n 2044) (.n 1286))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2056 := (vt_goodL (rd := rd) (w := w) hl 2072 [.atom (.copy (.n 2046) (.n 1295))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2058 := (vt_goodL (rd := rd) (w := w) hl 2074 [.atom (.copy (.n 2048) (.n 1304))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2060 := (vt_goodL (rd := rd) (w := w) hl 2076 [.atom (.copy (.n 2050) (.n 1313))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2062 := (vt_goodL (rd := rd) (w := w) hl 2078 [.atom (.copy (.n 2052) (.n 1322))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2064 := (vt_goodL (rd := rd) (w := w) hl 2080 [.atom (.copy (.n 2054) (.n 1331))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2066 := (vt_goodL (rd := rd) (w := w) hl 2082 [.atom (.copy (.n 2056) (.n 1340))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2068 := (vt_goodL (rd := rd) (w := w) hl 2084 [.atom (.copy (.n 2058) (.n 1349))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2070 := (vt_goodL (rd := rd) (w := w) hl 2086 [.atom (.copy (.n 2060) (.n 1358))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2072 := (vt_goodL (rd := rd) (w := w) hl 2088 [.atom (.copy (.n 2062) (.n 1367))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2074 := (vt_goodL (rd := rd) (w := w) hl 2090 [.atom (.copy (.n 2064) (.n 1376))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2076 := (vt_goodL (rd := rd) (w := w) hl 2092 [.atom (.copy (.n 2066) (.n 1385))] (by rw [vtPre_drop]; decide +kernel)).1
  have g2078 := (vt_goodL (rd := rd) (w := w) hl 2094 [.atom (.copy (.n 2068) (.n 1394))] (by rw [vtPre_drop]; decide +kernel)).1
  generalize vtσ rd w args = σ at g1978 g1980 g1982 g1984 g1986 g1988 g1990 g1992 g1994 g1996 g1998 g2000 g2002 g2004 g2006 g2008 g2010 g2012 g2014 g2016 g2018 g2020 g2022 g2024 g2026 g2028 g2030 g2032 g2034 g2036 g2038 g2040 g2042 g2044 g2046 g2048 g2050 g2052 g2054 g2056 g2058 g2060 g2062 g2064 g2066 g2068 g2070 g2072 g2074 g2076 g2078 ⊢
  simp only [GoodS, fixNe, Good] at g1978 g1980 g1982 g1984 g1986 g1988 g1990 g1992 g1994 g1996 g1998 g2000 g2002 g2004 g2006 g2008 g2010 g2012 g2014 g2016 g2018 g2020 g2022 g2024 g2026 g2028 g2030 g2032 g2034 g2036 g2038 g2040 g2042 g2044 g2046 g2048 g2050 g2052 g2054 g2056 g2058 g2060 g2062 g2064 g2066 g2068 g2070 g2072 g2074 g2076 g2078
  simp only [VtPullSelsH, g1978, g1980, g1982, g1984, g1986, g1988, g1990, g1992, g1994, g1996, g1998, g2000, g2002, g2004, g2006, g2008, g2010, g2012, g2014, g2016, g2018, g2020, g2022, g2024, g2026, g2028, g2030, g2032, g2034, g2036, g2038, g2040, g2042, g2044, g2046, g2048, g2050, g2052, g2054, g2056, g2058, g2060, g2062, g2064, g2066, g2068, g2070, g2072, g2074, g2076, g2078, and_self]

/-- **`ξ`'s powers**, honestly. -/
theorem vt_xi_good (hl : args.length = 20) :
    vtσ rd w args (.n 2589) = 1 ∧ vtσ rd w args (.n 2590) = vtσ rd w args (.n 2588) ∧
      vtσ rd w args (.n 2591) = vtσ rd w args (.n 2588) ^ 2 ∧
      vtσ rd w args (.n 2592) = vtσ rd w args (.n 2588) ^ 3 ∧
      vtσ rd w args (.n 2593) = vtσ rd w args (.n 2588) ^ 4 := by
  have g := vt_goodL (rd := rd) (w := w) hl 2636 [.atom (.const (.n 2589) (word 1 0 0)),
    .atom (.mul (.n 2590) (.n 2589) (.n 2588)), .atom (.mul (.n 2591) (.n 2590) (.n 2588)),
    .atom (.mul (.n 2592) (.n 2591) (.n 2588)), .atom (.mul (.n 2593) (.n 2592) (.n 2588))]
    (by rw [vtPre_drop]; decide +kernel)
  generalize vtσ rd w args = σ at g ⊢
  simp only [GoodL, GoodS, fixNe, Good, Nat.reduceLT, and_self, ↓reduceIte, and_true] at g
  obtain ⟨g0, g1, g2, g3, g4⟩ := g
  rw [tb_word_one] at g0
  refine ⟨g0, ?_, ?_, ?_, ?_⟩
  · rw [g1, g0, one_mul]
  · rw [g2, g1, g0, one_mul, sq]
  · rw [g3, g2, g1, g0, one_mul]; ring
  · rw [g4, g3, g2, g1, g0, one_mul]; ring

theorem vtPermCap_39 : vtPermCap 39 = [.n 5700, .n 5701, .n 5702, .n 5703, .n 5704] := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- **The sponge after the evaluations**, from the evaluations' sponge facts: the last
permutation's capacity and the last three evaluations waiting, their rate cells canonical. -/
theorem vt_evalFs_good (hl : args.length = 20)
    (hF : ∀ j < 39, (⟨vtCapV (vtσ rd w args) 0, []⟩ : Fs).absorbAll
        ((vtEvs (vtσ rd w args)).take (4 * (j + 1))) dsObserve =
      ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
      vtCapV (vtσ rd w args) (j + 1) = capOf (Fs.perm ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩)) :
    vtEvalFs (vtσ rd w args) = ⟨vtCapV (vtσ rd w args) 39,
        [(vtσ rd w args (.n 5705), dsObserve), (vtσ rd w args (.n 5716), dsObserve),
          (vtσ rd w args (.n 5727), dsObserve)]⟩ ∧
      rateOf (vtEvalFs (vtσ rd w args)).pend =
        [vtσ rd w args (.n 5712), vtσ rd w args (.n 5714), vtσ rd w args (.n 5723),
          vtσ rd w args (.n 5725), vtσ rd w args (.n 5734), vtσ rd w args (.n 5736), 0, 0] ∧
      (vtEvalFs (vtσ rd w args)).cap = [vtσ rd w args (.n 5700), vtσ rd w args (.n 5701),
        vtσ rd w args (.n 5702), vtσ rd w args (.n 5703), vtσ rd w args (.n 5704)] ∧
      AllCanonical (rateOf (vtEvalFs (vtσ rd w args)).pend ++ (vtEvalFs (vtσ rd w args)).cap) := by
  have p0 := vt_next_good (rd := rd) (w := w) hl (.n 2625) 5138 156 5705
    (by rw [vtPre_drop]; decide +kernel)
  have p1 := vt_next_good (rd := rd) (w := w) hl (.n 2625) 5148 157 5716
    (by rw [vtPre_drop]; decide +kernel)
  have p2 := vt_next_good (rd := rd) (w := w) hl (.n 2625) 5158 158 5727
    (by rw [vtPre_drop]; decide +kernel)
  generalize vtσ rd w args = σ at hF p0 p1 p2 ⊢
  have he0 : vtEvB 156 = 5705 := by decide
  have he1 : vtEvB 157 = 5716 := by decide
  have he2 : vtEvB 158 = 5727 := by decide
  obtain ⟨h38, hp38⟩ := hF 38 (by norm_num)
  have hr : vtEvs σ = (List.range 156).map (fun k ↦ σ (.n (vtEvB k))) ++
      [σ (.n (vtEvB 156)), σ (.n (vtEvB 157)), σ (.n (vtEvB 158))] := by
    show (List.range (156 + 1 + 1 + 1)).map _ = _
    rw [List.range_succ, List.range_succ, List.range_succ]
    simp only [List.map_append, List.append_assoc, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append]
  have ht : (vtEvs σ).take (4 * (38 + 1)) = (List.range 156).map fun k ↦ σ (.n (vtEvB k)) := by
    rw [hr, List.take_left' (by simp)]
  rw [ht] at h38
  have hS : vtEvalFs σ = ⟨vtCapV σ 39, [(σ (.n 5705), dsObserve), (σ (.n 5716), dsObserve),
      (σ (.n 5727), dsObserve)]⟩ := by
    rw [vtEvalFs, hr, fs_absorbAll_append, h38, tb_absorbAll_full' _ (by simp [vtEvs]) _
      (by simp) (by simp), ← hp38, he0, he1, he2]
    rfl
  have hcap : vtCapV σ 39 = [σ (.n 5700), σ (.n 5701), σ (.n 5702), σ (.n 5703), σ (.n 5704)] := by
    simp [vtCapV, vtPermCap_39]
  have hrate : rateOf [(σ (.n 5705), dsObserve), (σ (.n 5716), dsObserve),
      (σ (.n 5727), dsObserve)] =
      [σ (.n 5712), σ (.n 5714), σ (.n 5723), σ (.n 5725), σ (.n 5734), σ (.n 5736), 0, 0] := by
    rw [rateOf_eq_cells _ (by simp)]
    simp [pendCells, p0.1, p0.2.1, p1.1, p1.2.1, p2.1, p2.2.1]
  refine ⟨hS, by rw [hS]; exact hrate, by rw [hS]; exact hcap, ?_⟩
  rw [hS]
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · rw [hrate] at hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact p0.2.2.1
    · exact p0.2.2.2
    · exact p1.2.2.1
    · exact p1.2.2.2
    · exact p2.2.2.1
    · exact p2.2.2.2
    all_goals exact canon_zero'
  · rw [hp38] at hc
    simp only [capOf, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact canon_cellsOfState _ _ _

end

end
end LeanVM.Guest.B1.Tables
